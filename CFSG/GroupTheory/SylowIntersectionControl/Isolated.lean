module

public import Mathlib.GroupTheory.IsSubnormal
public import CFSG.GroupTheory.SylowIntersectionControl.Defs
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import CFSG.Assembly.Subnormal
import CFSG.GroupTheory.ComponentCovering
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools CFSG.ClassicalInvolution.GlaubermanAut
open scoped Pointwise

variable {G : Type*} [Group G] {p : ℕ}

@[expose] def IsPIsolatedOver (p : ℕ) (K H : Subgroup G) : Prop :=
  ∃ S T : Subgroup G, IsSylowOf p S K ∧ IsSylowOf p T K ∧
    ¬ Relation.EqvGen (fun A B : Subgroup G => IsSylowOf p A K ∧ IsSylowOf p B K ∧ H < A ⊓ B)
      S T

private theorem lt_of_eq_inf_of_ne [Finite G] [Fact p.Prime] {H S T : Subgroup G}
    (hH : H = S ⊓ T) (hST : S ≠ T) (hS : IsSylowOf p S ⊤) (hT : IsSylowOf p T ⊤) :
    H < S ∧ H < T := by
  have hHS : H ≤ S := hH.le.trans inf_le_left
  have hHT : H ≤ T := hH.le.trans inf_le_right
  constructor
  · refine lt_of_le_of_ne hHS ?_
    intro hEq
    have hSTle : S ≤ T := by
      rw [← hEq, hH]
      exact inf_le_right
    exact hST (IsSylowOf.eq_of_le hS hSTle le_top hT.isPGroup).symm
  · refine lt_of_le_of_ne hHT ?_
    intro hEq
    have hTSle : T ≤ S := by
      rw [← hEq, hH]
      exact inf_le_left
    exact hST (IsSylowOf.eq_of_le hT hTSle le_top hS.isPGroup)

private theorem lt_inf_of_dvd_relIndex [Finite G] [Fact p.Prime] {H N A : Subgroup G}
    (hAN : IsSylowOf p (A ⊓ N) N) (hHA : H ≤ A) (hHN : H ≤ N)
    (hp : p ∣ H.relIndex N) : H < A ⊓ N := by
  refine lt_of_le_of_ne (le_inf hHA hHN) ?_
  intro heq
  exact (isSylowOf_iff.mp hAN).2.2 (heq ▸ hp)

private theorem chain_of_reflTransGen {𝓕 : Set (Subgroup G)} {N H : Subgroup G}
    (hH : ∀ A : Subgroup G, IsSylowOf p A N → H < A)
    (step : ∀ S' T' : Subgroup G, IsSylowOf p S' ⊤ → IsSylowOf p T' ⊤ → H ≤ S' ⊓ T' →
      (H < S' ⊓ T' ∨ S' = T') → Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) S' T') :
    ∀ (A B : Subgroup G),
      Relation.ReflTransGen (fun A B : Subgroup G =>
        IsSylowOf p A N ∧ IsSylowOf p B N ∧ H < A ⊓ B) A B →
      IsSylowOf p A N → IsSylowOf p B N →
      ∀ (Ahat Bhat : Subgroup G), IsSylowOf p Ahat ⊤ → IsSylowOf p Bhat ⊤ → A ≤ Ahat →
        B ≤ Bhat → Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) Ahat Bhat := by
  intro A B h
  induction h with
  | refl =>
      intro hA _ Ahat Bhat hAhat hBhat hAAhat hBBhat
      have hlt : H < Ahat ⊓ Bhat := lt_of_lt_of_le (hH _ hA) (le_inf hAAhat hBBhat)
      exact step Ahat Bhat hAhat hBhat hlt.le (Or.inl hlt)
  | @tail b c hprev hstep ih =>
      intro hA hB Ahat Bhat hAhat hBhat hAAhat hBBhat
      obtain ⟨hbN, -, hltbc⟩ := hstep
      obtain ⟨bhat, hbbhat, hbhat⟩ := exists_isSylowOf_ge hbN.isPGroup le_top
      have hlt : H < bhat ⊓ Bhat :=
        lt_of_lt_of_le hltbc (le_inf (inf_le_left.trans hbbhat) (inf_le_right.trans hBBhat))
      exact (ih hA hbN Ahat bhat hAhat hbhat hAAhat hbbhat).trans
        (step bhat Bhat hbhat hBhat hlt.le (Or.inl hlt))

private theorem lt_of_isSylowOf_normalizer [Finite G] [Fact p.Prime] {H : Subgroup G}
    (hHp : IsPGroup p H) {P : Subgroup G}
    (hP : IsSylowOf p P (normalizer (H : Set G))) (hHltP : H < P) :
    ∀ A : Subgroup G, IsSylowOf p A (normalizer (H : Set G)) → H < A := by
  intro A hA
  have hHA : H ≤ A := by
    have hs : IsSylowOf p (A ⊓ H) H := hA.inf_of_le_normalizer (N := H) le_normalizer le_rfl
    have heq : H = A ⊓ H := IsSylowOf.eq_of_le hs inf_le_right le_rfl hHp
    rw [heq]
    exact inf_le_left
  refine lt_of_le_of_ne hHA ?_
  intro heq
  have hcard : Nat.card H = Nat.card P := by
    rw [heq, IsSylowOf.card_eq hA, IsSylowOf.card_eq hP]
  exact (ne_of_lt (Subgroup.card_lt_of_lt hHltP)) hcard

private theorem chain_of_eqvGen [Finite G] [Fact p.Prime] {𝓕 : Set (Subgroup G)} {H : Subgroup G}
    (hlarger : ∀ S' T' : Subgroup G, IsSylowOf p S' ⊤ → IsSylowOf p T' ⊤ → H ≤ S' ⊓ T' →
      (H < S' ⊓ T' ∨ S' = T') → Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) S' T')
    (hH : ∀ A : Subgroup G, IsSylowOf p A (normalizer (H : Set G)) → H < A)
    {Q R : Subgroup G} (hQ : IsSylowOf p Q ⊤) (hR : IsSylowOf p R ⊤)
    (hP₁ : IsSylowOf p (Q ⊓ normalizer (H : Set G)) (normalizer (H : Set G)))
    (hP₂ : IsSylowOf p (R ⊓ normalizer (H : Set G)) (normalizer (H : Set G)))
    (heqv : Relation.EqvGen (fun A B : Subgroup G =>
      IsSylowOf p A (normalizer (H : Set G)) ∧
        IsSylowOf p B (normalizer (H : Set G)) ∧ H < A ⊓ B)
      (Q ⊓ normalizer (H : Set G)) (R ⊓ normalizer (H : Set G))) :
    Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) Q R := by
  let rel : Subgroup G → Subgroup G → Prop := fun A B =>
    IsSylowOf p A (normalizer (H : Set G)) ∧
      IsSylowOf p B (normalizer (H : Set G)) ∧ H < A ⊓ B
  have hsymm : Std.Symm rel :=
    ⟨fun A B hh => ⟨hh.2.1, hh.1, by rw [inf_comm]; exact hh.2.2⟩⟩
  have hEqvRT : Relation.ReflTransGen rel (Q ⊓ normalizer (H : Set G))
      (R ⊓ normalizer (H : Set G)) :=
    @Relation.EqvGen.eqvGen_eq_reflTransGen (Subgroup G) rel hsymm ▸ heqv
  exact chain_of_reflTransGen hH hlarger (Q ⊓ normalizer (H : Set G))
    (R ⊓ normalizer (H : Set G)) hEqvRT hP₁ hP₂ Q R hQ hR inf_le_left inf_le_left

private theorem exists_link_through_member [Finite G] [Fact p.Prime] {𝓕 : Set (Subgroup G)}
    {H N X A B : Subgroup G} (hHN : H ≤ N) (hNX : N ≤ X) (hXmem : X ∈ 𝓕)
    (hHA : H ≤ A) (hHB : H ≤ B)
    (hAN : IsSylowOf p A N) (hBN : IsSylowOf p B N) :
    ∃ U V : Subgroup G, IsSylowOf p U ⊤ ∧ IsSylowOf p V ⊤ ∧ A ≤ U ∧ B ≤ V ∧
      SylowConjLink p 𝓕 ⊤ H U V := by
  obtain ⟨U', hAU', hU'⟩ := exists_isSylowOf_ge hAN.isPGroup (hAN.le.trans hNX)
  obtain ⟨V'', hBV'', hV''⟩ := exists_isSylowOf_ge hBN.isPGroup (hBN.le.trans hNX)
  obtain ⟨U, hU'U, hU⟩ := exists_isSylowOf_ge hU'.isPGroup le_top
  obtain ⟨k, hkX, hk⟩ := hU'.exists_mem_conj hV''
  set V : Subgroup G := U.map (MulAut.conj k).toMonoidHom with hVdef
  have hV : IsSylowOf p V ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · simpa only [hVdef] using hU.isPGroup.map (MulAut.conj k).toMonoidHom
    · rw [Subgroup.relIndex_top_right, hVdef,
        Subgroup.index_map_of_bijective (MulAut.conj k).bijective]
      have hnot := (isSylowOf_iff.mp hU).2.2
      rwa [Subgroup.relIndex_top_right] at hnot
  have hV''V : V'' ≤ V := by
    intro y hy
    rw [hVdef, Subgroup.mem_map]
    refine ⟨k⁻¹ * y * k, hU'U ((hk y).mp hy), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hUX : U ⊓ X = U' :=
    IsSylowOf.eq_of_le hU' (le_inf hU'U hU'.le) inf_le_right hU.isPGroup.to_inf_left
  have hVX : V ⊓ X = V'' :=
    IsSylowOf.eq_of_le hV'' (le_inf hV''V hV''.le) inf_le_right hV.isPGroup.to_inf_left
  refine ⟨U, V, hU, hV, hAU'.trans hU'U, hBV''.trans hV''V, ?_⟩
  refine ⟨hU, hV, X, ⟨hXmem, by rw [hUX]; exact hU'⟩,
    ⟨hXmem, by rw [hVX]; exact hV''⟩, ?_, k, hkX, hVdef⟩
  exact le_inf (le_inf (hHA.trans (hAU'.trans hU'U)) (hHB.trans (hBV''.trans hV''V)))
    (hHN.trans hNX)

private theorem chain_via_isolated [Finite G] [Fact p.Prime] {𝓕 : Set (Subgroup G)}
    {H N X Q R : Subgroup G}
    (hlarger : ∀ S' T' : Subgroup G, IsSylowOf p S' ⊤ → IsSylowOf p T' ⊤ → H ≤ S' ⊓ T' →
      (H < S' ⊓ T' ∨ S' = T') → Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) S' T')
    (hHN : H ≤ N) (hNnorm : N ≤ normalizer (H : Set G))
    (hNsub : (N.subgroupOf (normalizer (H : Set G))).IsSubnormal)
    (hpdiv : p ∣ H.relIndex N) (hXmem : X ∈ 𝓕) (hNX : N ≤ X)
    (hQ : IsSylowOf p Q ⊤) (hR : IsSylowOf p R ⊤)
    (hP₁ : IsSylowOf p (Q ⊓ normalizer (H : Set G)) (normalizer (H : Set G)))
    (hP₂ : IsSylowOf p (R ⊓ normalizer (H : Set G)) (normalizer (H : Set G)))
    (hHltP₁ : H < Q ⊓ normalizer (H : Set G)) (hHltP₂ : H < R ⊓ normalizer (H : Set G)) :
    Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) Q R := by
  have hNsubOpen : CFSG.Open.IsSubnormal N (normalizer (H : Set G)) :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hNnorm).2 hNsub
  have hQN : IsSylowOf p (Q ⊓ N) N := by
    have h := CFSG.ABGLocalTools.IsSylowOf.inf_of_isSubnormal hP₁ hNsubOpen
    rwa [inf_assoc, inf_eq_right.mpr hNnorm] at h
  have hRN : IsSylowOf p (R ⊓ N) N := by
    have h := CFSG.ABGLocalTools.IsSylowOf.inf_of_isSubnormal hP₂ hNsubOpen
    rwa [inf_assoc, inf_eq_right.mpr hNnorm] at h
  have hHltQN : H < Q ⊓ N :=
    lt_inf_of_dvd_relIndex hQN (hHltP₁.le.trans inf_le_left) hHN hpdiv
  have hHltRN : H < R ⊓ N :=
    lt_inf_of_dvd_relIndex hRN (hHltP₂.le.trans inf_le_left) hHN hpdiv
  obtain ⟨U, V, hU, hV, hQNU, hRNV, hlink⟩ :=
    exists_link_through_member hHN hNX hXmem hHltQN.le hHltRN.le hQN hRN
  have hHltQU : H < Q ⊓ U := lt_of_lt_of_le hHltQN (le_inf inf_le_left hQNU)
  have hHltVR : H < V ⊓ R := lt_of_lt_of_le hHltRN (le_inf hRNV inf_le_left)
  exact (hlarger Q U hQ hU hHltQU.le (Or.inl hHltQU)).trans
    ((Relation.ReflTransGen.single hlink).trans (hlarger V R hV hR hHltVR.le (Or.inl hHltVR)))

private theorem reflTransGen_of_lt_inf [Finite G] [Fact p.Prime] {𝓕 : Set (Subgroup G)}
    {H : Subgroup G}
    (ih : ∀ S' T' : Subgroup G, Nat.card H < Nat.card ↥(S' ⊓ T') →
      IsSylowOf p S' ⊤ → IsSylowOf p T' ⊤ → S' ⊓ T' ≠ ⊥ →
      Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ (S' ⊓ T')) S' T')
    (hHbot : H ≠ ⊥) :
    ∀ S' T' : Subgroup G, IsSylowOf p S' ⊤ → IsSylowOf p T' ⊤ → H ≤ S' ⊓ T' →
      (H < S' ⊓ T' ∨ S' = T') → Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) S' T' := by
  intro S' T' hS' hT' hle hcase
  rcases hcase with hlt | hEq
  · have hne : S' ⊓ T' ≠ ⊥ := fun hbot => hHbot (le_bot_iff.mp (hbot ▸ hle))
    exact Relation.ReflTransGen.mono (fun _ _ hab => SylowConjLink.mono hle hab) S' T'
      (ih S' T' (Subgroup.card_lt_of_lt hlt) hS' hT' hne)
  · rw [hEq]

private theorem reduce_step [Finite G] [Fact p.Prime] {𝓕 : Set (Subgroup G)} {H S T : Subgroup G}
    (hH : H = S ⊓ T) (hST : S ≠ T) (hS : IsSylowOf p S ⊤) (hT : IsSylowOf p T ⊤)
    (hlarger : ∀ S' T' : Subgroup G, IsSylowOf p S' ⊤ → IsSylowOf p T' ⊤ → H ≤ S' ⊓ T' →
      (H < S' ⊓ T' ∨ S' = T') → Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) S' T') :
    ∃ Q R : Subgroup G, IsSylowOf p Q ⊤ ∧ IsSylowOf p R ⊤ ∧
      Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) S Q ∧
      Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) R T ∧
      (Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) Q R ∨
        (IsSylowOf p (Q ⊓ normalizer (H : Set G)) (normalizer (H : Set G)) ∧
          IsSylowOf p (R ⊓ normalizer (H : Set G)) (normalizer (H : Set G)) ∧
          H < Q ⊓ normalizer (H : Set G) ∧ H < R ⊓ normalizer (H : Set G))) := by
  obtain ⟨hHS, hHT⟩ := lt_of_eq_inf_of_ne hH hST hS hT
  have hHSnorm : H < S ⊓ normalizer (H : Set G) :=
    lt_inf_normalizer_of_isPGroup hS.isPGroup hHS
  have hHTnorm : H < T ⊓ normalizer (H : Set G) :=
    lt_inf_normalizer_of_isPGroup hT.isPGroup hHT
  obtain ⟨P₁, hNSP₁, hP₁⟩ := exists_isSylowOf_ge hS.isPGroup.to_inf_left inf_le_right
  obtain ⟨P₂, hNTP₂, hP₂⟩ := exists_isSylowOf_ge hT.isPGroup.to_inf_left inf_le_right
  obtain ⟨Q, hP₁Q, hQ⟩ := exists_isSylowOf_ge hP₁.isPGroup le_top
  obtain ⟨R, hP₂R, hR⟩ := exists_isSylowOf_ge hP₂.isPGroup le_top
  have hHltSQ : H < S ⊓ Q := lt_of_lt_of_le hHSnorm (le_inf inf_le_left (hNSP₁.trans hP₁Q))
  have hHltTR : H < T ⊓ R := lt_of_lt_of_le hHTnorm (le_inf inf_le_left (hNTP₂.trans hP₂R))
  have hSQ : Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) S Q :=
    hlarger S Q hS hQ hHltSQ.le (Or.inl hHltSQ)
  have hRT : Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ H) R T := by
    have hlt : H < R ⊓ T := by rwa [inf_comm]
    exact hlarger R T hR hT hlt.le (Or.inl hlt)
  have hQP₁ : Q ⊓ normalizer (H : Set G) = P₁ :=
    IsSylowOf.eq_of_le hP₁ (le_inf hP₁Q hP₁.le) inf_le_right hQ.isPGroup.to_inf_left
  have hRP₂ : R ⊓ normalizer (H : Set G) = P₂ :=
    IsSylowOf.eq_of_le hP₂ (le_inf hP₂R hP₂.le) inf_le_right hR.isPGroup.to_inf_left
  have hHltP₁ : H < P₁ := lt_of_lt_of_le hHSnorm hNSP₁
  have hHltP₂ : H < P₂ := lt_of_lt_of_le hHTnorm hNTP₂
  refine ⟨Q, R, hQ, hR, hSQ, hRT, ?_⟩
  by_cases hQR : Q = R
  · exact Or.inl (hQR ▸ Relation.ReflTransGen.refl)
  by_cases hltQR : H < Q ⊓ R
  · exact Or.inl (hlarger Q R hQ hR hltQR.le (Or.inl hltQR))
  exact Or.inr ⟨hQP₁ ▸ hP₁, hRP₂ ▸ hP₂, hQP₁ ▸ hHltP₁, hRP₂ ▸ hHltP₂⟩

theorem controlsSylowIntersections_of_isPIsolatedOver [Finite G] [Fact p.Prime]
    {𝓕 : Set (Subgroup G)}
    (h : ∀ H : Subgroup G, H ≠ ⊥ → IsPGroup p H →
      IsPIsolatedOver p (normalizer (H : Set G)) H →
      ∃ N : Subgroup G, H ≤ N ∧ N ≤ normalizer (H : Set G) ∧
        (N.subgroupOf (normalizer (H : Set G))).IsSubnormal ∧
        p ∣ H.relIndex N ∧ ∃ X ∈ 𝓕, N ≤ X) :
    ControlsSylowIntersections p 𝓕 ⊤ := by
  classical
  have key : ∀ n, ∀ S T : Subgroup G, Nat.card G - Nat.card ↥(S ⊓ T) = n →
      IsSylowOf p S ⊤ → IsSylowOf p T ⊤ → S ⊓ T ≠ ⊥ →
      Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ (S ⊓ T)) S T := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S T hn hS hT hHbot
      rcases eq_or_ne S T with rfl | hST
      · exact Relation.ReflTransGen.refl
      set H : Subgroup G := S ⊓ T with hHdef
      have hHbot' : H ≠ ⊥ := by rwa [hHdef]
      have hHp : IsPGroup p H := by rw [hHdef]; exact hS.isPGroup.to_inf_left
      have ih' : ∀ S' T' : Subgroup G, Nat.card H < Nat.card ↥(S' ⊓ T') →
          IsSylowOf p S' ⊤ → IsSylowOf p T' ⊤ → S' ⊓ T' ≠ ⊥ →
          Relation.ReflTransGen (SylowConjLink p 𝓕 ⊤ (S' ⊓ T')) S' T' := by
        intro S' T' hcard hS' hT' hne
        have hltn : Nat.card G - Nat.card ↥(S' ⊓ T') < n := by
          rw [← hn, hHdef]
          exact Nat.sub_lt_sub_left
            (lt_of_lt_of_le hcard (Subgroup.card_le_card_group (H := S' ⊓ T'))) hcard
        exact ih _ hltn S' T' rfl hS' hT' hne
      have hlarger := reflTransGen_of_lt_inf ih' hHbot'
      obtain ⟨Q, R, hQ, hR, hSQ, hRT, hcase⟩ := reduce_step hHdef hST hS hT hlarger
      rcases hcase with hQR | ⟨hP₁, hP₂, hHltP₁, hHltP₂⟩
      · exact hSQ.trans (hQR.trans hRT)
      by_cases hIso : IsPIsolatedOver p (normalizer (H : Set G)) H
      · obtain ⟨N, hHN, hNnorm, hNsub, hpdiv, X, hXmem, hNX⟩ := h H hHbot' hHp hIso
        exact hSQ.trans ((chain_via_isolated hlarger hHN hNnorm hNsub hpdiv hXmem hNX hQ hR hP₁
          hP₂ hHltP₁ hHltP₂).trans hRT)
      · have hHlt := lt_of_isSylowOf_normalizer hHp hP₁ hHltP₁
        have heqv : Relation.EqvGen (fun A B : Subgroup G =>
            IsSylowOf p A (normalizer (H : Set G)) ∧
              IsSylowOf p B (normalizer (H : Set G)) ∧ H < A ⊓ B)
            (Q ⊓ normalizer (H : Set G)) (R ⊓ normalizer (H : Set G)) := by
          by_contra hc
          exact hIso ⟨_, _, hP₁, hP₂, hc⟩
        exact hSQ.trans ((chain_of_eqvGen hlarger hHlt hQ hR hP₁ hP₂ heqv).trans hRT)
  intro S T hS hT _ hHbot
  exact key (Nat.card G - Nat.card ↥(S ⊓ T)) S T rfl hS hT hHbot

end CFSG.GroupTheory
