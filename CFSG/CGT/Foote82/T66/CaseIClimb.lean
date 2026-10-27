module

public import CFSG.CGT.Foote82.T66.Cited
public import CFSG.CGT.Foote82.T66.Inherit
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
import CFSG.LocalAnalysis.GLTheoremB.I2810.AltDegree
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129j
import CFSG.Quasithin.Background.G11Basic
public import CFSG.CGT.Foote82.T66.Prop35

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

namespace CaseIClimbAux
open scoped commutatorElement

section Groups

variable {Γ : Type*} [Group Γ]

private theorem not_mem_of_orderOf_eq_two {K : Subgroup Γ} {r : Γ} (hr : orderOf r = 2)
    (hK : Odd (Nat.card K)) : r ∉ K := by
  intro hrK
  have h := Subgroup.orderOf_dvd_natCard K hrK
  rw [hr] at h
  exact Nat.not_even_iff_odd.2 hK (even_iff_two_dvd.2 h)

private theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [hp] at hcomm
    exact eq_top_iff.mpr hcomm

private theorem isQuasisimple_of_isSimpleGroup {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hnc : ∃ a b : Q, a * b ≠ b * a) : Open.IsQuasisimple Q := by
  obtain ⟨a, b, hab⟩ := hnc
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      apply hab
      have hc : ⁅a, b⁆ ∈ commutator Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

private theorem isQuasisimple_native {Q : Type*} [Group Q] (h : Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q h⟩

private theorem nontrivial_of_isQuasisimple {Q : Type*} [Group Q] (hQ : Open.IsQuasisimple Q) :
    Nontrivial Q := by
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  obtain ⟨x, y, hxy⟩ := hsimple.exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨a, b, fun hab => hxy (by rw [hab])⟩

private theorem perfect_ne_bot {L : Subgroup Γ} (hq : Open.IsQuasisimple ↥L) :
    ⁅L, L⁆ = L ∧ L ≠ ⊥ := by
  haveI : Nontrivial ↥L := nontrivial_of_isQuasisimple hq
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.2 hq.1
  exact ⟨Subgroup.isPerfect_iff.1 inferInstance, (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance⟩

private theorem eq_of_perfect_le {L L₀ N : Subgroup Γ} (hL₀ : Open.IsQuasisimple ↥L₀)
    (hperf : ⁅L, L⁆ = L) (hLne : L ≠ ⊥) (hLN : L ≤ N) (hNL₀ : N ≤ L₀)
    (hnorm : ∀ g ∈ L₀, ∀ x ∈ N, g * x * g⁻¹ ∈ N) : N = L₀ := by
  have hN' : (N.subgroupOf L₀).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hnorm g g.2 x hx⟩
  rcases normal_eq_top_or_le_center hL₀ hN' with h | h
  · refine le_antisymm hNL₀ fun x hx => ?_
    have : (⟨x, hx⟩ : ↥L₀) ∈ N.subgroupOf L₀ := h ▸ Subgroup.mem_top _
    exact this
  · exfalso
    apply hLne
    have hcomm : ⁅L, L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb' : (⟨b, hNL₀ (hLN hb)⟩ : ↥L₀) ∈ Subgroup.center ↥L₀ :=
        h (Subgroup.mem_subgroupOf.2 (hLN hb))
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hb' ⟨a, hNL₀ (hLN ha)⟩)).symm
    rw [← hperf, hcomm]

private theorem isQuasisimple_alt {n : ℕ} (hn : 5 ≤ n) :
    Open.IsQuasisimple ↥(alternatingGroup (Fin n)) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  refine isQuasisimple_of_isSimpleGroup hs ?_
  by_contra hc
  push Not at hc
  obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : ↥(alternatingGroup (Fin n)))).1
    hs.toNontrivial
  have h1 : a ∈ Subgroup.center ↥(alternatingGroup (Fin n)) :=
    Subgroup.mem_center_iff.2 fun g => hc g a
  rw [alternatingGroup.center_eq_bot (by simpa using (by omega : 4 ≤ n))] at h1
  exact ha (Subgroup.mem_bot.1 h1)

private theorem card_alt {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem isQuasisimple_omegaMinusTwo :
    Open.IsQuasisimple ↥(CFSG.RankThree.PartTwo.omegaMinusTwo 2) := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨hsimple, -, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (K := ZMod 2) (n := 3) (Or.inr rfl) hirr
  push Not at hna
  exact Open.IsQuasisimple.of_mulEquiv
    (MulEquiv.refl _ : ↥(CFSG.RankThree.PartTwo.omegaMinusTwo 2) ≃*
      ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)))
    (isQuasisimple_of_isSimpleGroup hsimple hna)

private theorem card_omegaMinusTwo :
    Nat.card ↥(CFSG.RankThree.PartTwo.omegaMinusTwo 2) = 25920 :=
  (Nat.card_congr (MulEquiv.refl _ : ↥(CFSG.RankThree.PartTwo.omegaMinusTwo 2) ≃*
      ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1))).toEquiv).trans
    CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltDegree.card_omegaMinusSix.2

private theorem le_normalizer_map_subtype' {H : Subgroup Γ} (N : Subgroup ↥H) [N.Normal] :
    H ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup Γ) : Set Γ) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, Subgroup.Normal.conj_mem inferInstance k hk ⟨h, hh⟩, rfl⟩
  · rintro ⟨k, hk, hkg⟩
    refine ⟨⟨h, hh⟩⁻¹ * k * ⟨h, hh⟩, ?_, ?_⟩
    · have := Subgroup.Normal.conj_mem (inferInstance : N.Normal) k hk ⟨h, hh⟩⁻¹
      simpa using this
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hkg ⊢
      rw [hkg]
      group

end Groups

private theorem exists_altOn {Γ : Type} [Group Γ] {Hb E Rb Lb : Subgroup Γ} {M : ℕ}
    (hM : 7 ≤ M) (φ : ↥E ≃* alternatingGroup (Fin M)) (hEH : E ≤ Hb)
    (hnorm : Hb ≤ Subgroup.normalizer (E : Set Γ)) (hRb : IsPGroup 2 ↥Rb) (hRbH : Rb ≤ Hb)
    (hLb : IsComponentOf Lb (Hb ⊓ Subgroup.centralizer (Rb : Set Γ))) (hLbE : Lb ≤ E) :
    ∃ F : Set (Fin M), 5 ≤ F.ncard ∧
      (Lb.subgroupOf E).map ((alternatingGroup (Fin M)).subtype.comp φ.toMonoidHom) =
        altOn F := by
  classical
  obtain ⟨ρ, hρ⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129j.exists_perm_implementer
    (by omega) (by omega) φ hnorm
  set φ' : ↥E →* Equiv.Perm (Fin M) :=
    (alternatingGroup (Fin M)).subtype.comp φ.toMonoidHom with hφ'
  have hφ'inj : Function.Injective φ' := Subtype.val_injective.comp φ.injective
  have hφ'apply : ∀ e : ↥E, φ' e = ((φ e : alternatingGroup (Fin M)) : Equiv.Perm (Fin M)) :=
    fun e => rfl
  set R' : Subgroup (Equiv.Perm (Fin M)) := (Rb.subgroupOf Hb).map ρ with hR'
  have hR'2 : IsPGroup 2 ↥R' :=
    (IsPGroup.of_equiv hRb (Subgroup.subgroupOfEquivOfLe hRbH).symm).map ρ
  have key : ∀ (r : ↥Hb) (e : ↥E),
      ((r : Γ) * e = e * r ↔ ρ r * φ' e = φ' e * ρ r) := by
    intro r e
    have hy : (r : Γ) * e * (r : Γ)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.1 (hnorm r.2) e).1 e.2
    have h := hρ r e ⟨_, hy⟩ rfl
    rw [← hφ'apply, ← hφ'apply] at h
    constructor
    · intro hc
      have hye : (⟨_, hy⟩ : ↥E) = e := Subtype.ext (by
        show (r : Γ) * e * (r : Γ)⁻¹ = e
        rw [hc, mul_inv_cancel_right])
      rw [hye] at h
      calc ρ r * φ' e = (ρ r * φ' e * (ρ r)⁻¹) * ρ r := by group
        _ = φ' e * ρ r := by rw [← h]
    · intro hc
      have h2 : φ' ⟨_, hy⟩ = φ' e := by rw [h, hc, mul_inv_cancel_right]
      have h3 : (r : Γ) * e * (r : Γ)⁻¹ = e := congrArg Subtype.val (hφ'inj h2)
      calc (r : Γ) * e = ((r : Γ) * e * (r : Γ)⁻¹) * r := by group
        _ = e * r := by rw [h3]
  set X : Subgroup (Equiv.Perm (Fin M)) :=
    alternatingGroup (Fin M) ⊓ Subgroup.centralizer (R' : Set (Equiv.Perm (Fin M))) with hX
  have hXeq : ((E ⊓ Subgroup.centralizer (Rb : Set Γ)).subgroupOf E).map φ' = X := by
    ext σ
    constructor
    · rintro ⟨e, he, rfl⟩
      refine ⟨(φ e).2, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      have hr' : (r : Γ) ∈ Rb := hr
      have hc : (r : Γ) * e = e * r := Subgroup.mem_centralizer_iff.1 he.2 r hr'
      exact (key r e).1 hc
    · rintro ⟨hσA, hσC⟩
      refine ⟨φ.symm ⟨σ, hσA⟩, ⟨(φ.symm ⟨σ, hσA⟩).2, Subgroup.mem_centralizer_iff.2 ?_⟩, ?_⟩
      · intro g hg
        have h1 : φ' (φ.symm ⟨σ, hσA⟩) = σ := by rw [hφ'apply, MulEquiv.apply_symm_apply]
        have h2 : ρ ⟨g, hRbH hg⟩ * σ = σ * ρ ⟨g, hRbH hg⟩ :=
          Subgroup.mem_centralizer_iff.1 hσC _ ⟨⟨g, hRbH hg⟩, hg, rfl⟩
        rw [← h1] at h2
        exact (key ⟨g, hRbH hg⟩ _).2 h2
      · rw [hφ'apply, MulEquiv.apply_symm_apply]
  set K : Subgroup (Equiv.Perm (Fin M)) := (Lb.subgroupOf E).map φ' with hK
  have hLbs : Lb ≤ E ⊓ Subgroup.centralizer (Rb : Set Γ) :=
    le_inf hLbE (hLb.1.trans inf_le_right)
  have hsub1 : IsSubnormal Lb (E ⊓ Subgroup.centralizer (Rb : Set Γ)) := by
    have := hLb.2.1.inf_of_le (inf_le_inf_right _ hEH)
    rwa [inf_eq_left.2 hLbs] at this
  have hKX : IsComponentOf K X := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hXeq]
      exact Subgroup.map_mono (Subgroup.comap_mono hLbs)
    · rw [← hXeq]
      exact (hsub1.comap E.subtype).map φ'
    · have e1 : ↥K ≃* ↥(Lb.subgroupOf E) :=
        ((Lb.subgroupOf E).equivMapOfInjective φ' hφ'inj).symm
      exact Open.IsQuasisimple.of_mulEquiv (e1.trans (Subgroup.subgroupOfEquivOfLe hLbE))
        hLb.2.2
  obtain ⟨h5, hKeq⟩ := eq_altOn_of_isComponentOf hR'2 le_rfl inf_le_right hKX
  exact ⟨{i | ∀ r ∈ R', r i = i}, by rw [← Nat.card_coe_set_eq]; exact h5, hKeq⟩

section Linear

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem add_self_eq_zero' (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

private theorem odd_nsmul_eq {k : ℕ} (hk : Odd k) (v : V) : k • v = v := by
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2), ZMod.natCast_eq_one_iff_odd.2 hk, one_smul]

private theorem mk_eq_mk_iff' {W₀ W₁ : Submodule (ZMod 2) V} {v v' : V} (hv : v ∈ W₁)
    (hv' : v' ∈ W₁) :
    (Submodule.Quotient.mk ⟨v, hv⟩ : Sect W₀ W₁) = Submodule.Quotient.mk ⟨v', hv'⟩ ↔
      v - v' ∈ W₀ := by
  rw [Submodule.Quotient.eq]
  rfl

private theorem sectHom_eq_one_iff' {H : Subgroup (GLV V)} {W₀ W₁ : Submodule (ZMod 2) V}
    (h₀ : Invariant H W₀) (h₁ : Invariant H W₁) (y : ↥H) :
    sectHom H h₀ h₁ y = 1 ↔ ∀ w ∈ W₁, (y : GLV V) w - w ∈ W₀ := by
  constructor
  · intro h w hw
    have h' := congrArg (fun f : GLV (Sect W₀ W₁) => f (Submodule.Quotient.mk ⟨w, hw⟩)) h
    simp only [sectHom_mk] at h'
    exact (mk_eq_mk_iff' (h₁ y y.2 w hw) hw).1 h'
  · intro h
    ext q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp only [sectHom_mk]
    exact (mk_eq_mk_iff' (h₁ y y.2 w w.2) w.2).2 (h w w.2)

private theorem mem_of_sub_mem {W₀ W₁ : Submodule (ZMod 2) V} {y : GLV V}
    (hy₁ : ∀ w ∈ W₁, y w ∈ W₁) (hyW : ∀ w ∈ W₁, y w - w ∈ W₀) (hodd : Odd (orderOf y))
    (u : V) (hv : y u - u ∈ W₁) : y u - u ∈ W₀ := by
  have hpow : ∀ i : ℕ, ∀ w ∈ W₁, (y ^ i) w ∈ W₁ ∧ (y ^ i) w - w ∈ W₀ := by
    intro i
    induction i with
    | zero => intro w hw; simp [hw]
    | succ i ih =>
      intro w hw
      obtain ⟨h1, h2⟩ := ih w hw
      rw [pow_succ', LinearEquiv.mul_apply]
      refine ⟨hy₁ _ h1, ?_⟩
      have e : y ((y ^ i) w) - w = (y ((y ^ i) w) - (y ^ i) w) + ((y ^ i) w - w) := by abel
      rw [e]
      exact W₀.add_mem (hyW _ h1) h2
  have htel : ∑ i ∈ Finset.range (orderOf y), (y ^ i) (y u - u) = 0 := by
    have e : ∀ i, (y ^ i) (y u - u) = (y ^ (i + 1)) u - (y ^ i) u := by
      intro i
      rw [map_sub, pow_succ, LinearEquiv.mul_apply]
    simp_rw [e]
    rw [Finset.sum_range_sub (fun i => (y ^ i) u), pow_orderOf_eq_one, pow_zero, sub_self]
  have hsum : ∑ i ∈ Finset.range (orderOf y), ((y ^ i) (y u - u) - (y u - u)) ∈ W₀ :=
    W₀.sum_mem fun i _ => (hpow i _ hv).2
  rw [Finset.sum_sub_distrib, htel, Finset.sum_const, Finset.card_range, odd_nsmul_eq hodd,
    zero_sub] at hsum
  exact W₀.neg_mem_iff.1 hsum

end Linear

section Modules

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem trivial_of_trivial {L L₀ : Subgroup (GLV V)} (hLL₀ : L ≤ L₀)
    (hL₀ : Open.IsQuasisimple ↥L₀) (hperf : ⁅L, L⁆ = L) (hLne : L ≠ ⊥)
    {J : Submodule (ZMod 2) V} (hJ : Invariant L₀ J) (htriv : ∀ l ∈ L, ∀ j ∈ J, l j = j) :
    ∀ x ∈ L₀, ∀ j ∈ J, x j = j := by
  have hN : centralizerOn L₀ J = L₀ := by
    refine eq_of_perfect_le hL₀ hperf hLne (fun l hl => ⟨hLL₀ hl, htriv l hl⟩)
      (fun x hx => hx.1) fun g hg x hx => ⟨L₀.mul_mem (L₀.mul_mem hg hx.1) (L₀.inv_mem hg),
        fun j hj => ?_⟩
    have h1 : g⁻¹ j ∈ J := hJ _ (L₀.inv_mem hg) j hj
    simp only [LinearEquiv.mul_apply]
    rw [hx.2 _ h1]
    simp
  intro x hx j hj
  have hx' : x ∈ centralizerOn L₀ J := by rw [hN]; exact hx
  exact hx'.2 j hj

private theorem commSpace_le_of_le {L L₀ : Subgroup (GLV V)} (hLL₀ : L ≤ L₀)
    (hL₀ : Open.IsQuasisimple ↥L₀) (hperf : ⁅L, L⁆ = L) (hLne : L ≠ ⊥)
    {J : Submodule (ZMod 2) V} (hJ : Invariant L₀ J) (hle : commSpace L ⊤ ≤ J) :
    commSpace L₀ ⊤ ≤ J := by
  let N : Subgroup (GLV V) :=
    { carrier := {x | x ∈ L₀ ∧ ∀ v : V, x v - v ∈ J}
      mul_mem' := fun {a b} ha hb => ⟨L₀.mul_mem ha.1 hb.1, fun v => by
        have e : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
          rw [LinearEquiv.mul_apply]; abel
        rw [e]
        exact J.add_mem (ha.2 _) (hb.2 v)⟩
      one_mem' := ⟨L₀.one_mem, fun v => by simp⟩
      inv_mem' := fun {a} ha => ⟨L₀.inv_mem ha.1, fun v => by
        have e : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by
          rw [show a (a⁻¹ v) = v by simp]; abel
        rw [e]
        exact J.neg_mem (ha.2 _)⟩ }
  have hN : N = L₀ := by
    refine eq_of_perfect_le hL₀ hperf hLne
      (fun l hl => ⟨hLL₀ hl, fun v => hle (sub_mem_commSpace hl Submodule.mem_top)⟩)
      (fun x hx => hx.1) fun g hg x hx => ⟨L₀.mul_mem (L₀.mul_mem hg hx.1) (L₀.inv_mem hg),
        fun v => ?_⟩
    have e : (g * x * g⁻¹) v - v = g (x (g⁻¹ v) - g⁻¹ v) := by
      simp only [LinearEquiv.mul_apply, map_sub]
      simp
    rw [e]
    exact hJ g hg _ (hx.2 _)
  refine commSpace_le_iff.2 fun x hx v _ => ?_
  have hx' : x ∈ N := by rw [hN]; exact hx
  exact hx'.2 v

private theorem eq_one_of_odd {L L₀ : Subgroup (GLV V)} {W₀ W₁ : Submodule (ZMod 2) V}
    (hLL₀ : L ≤ L₀) (hL₀ : Open.IsQuasisimple ↥L₀) (hperf : ⁅L, L⁆ = L) (hLne : L ≠ ⊥)
    (hirr : HasIrrTildeV L) (hW₁ : Invariant L W₁) (hLW : ∃ l ∈ L, ∃ w ∈ W₁, l w - w ∉ W₀)
    {y : GLV V} (hyL₀ : y ∈ L₀) (hyc : ∀ x ∈ L₀, y * x = x * y)
    (hy₁ : ∀ w ∈ W₁, y w ∈ W₁) (hyW : ∀ w ∈ W₁, y w - w ∈ W₀) (hodd : Odd (orderOf y)) :
    y = 1 := by
  let U : Submodule (ZMod 2) V := LinearMap.range ((y : V →ₗ[ZMod 2] V) - LinearMap.id)
  have hmemU : ∀ u : V, y u - u ∈ U := fun u => ⟨u, by simp⟩
  have hcomm : ∀ x ∈ L₀, ∀ v : V, x (y v) = y (x v) := fun x hx v => by
    have := congrArg (fun g : GLV V => g v) (hyc x hx)
    simp only [LinearEquiv.mul_apply] at this
    exact this.symm
  have hUinv : Invariant L₀ U := by
    rintro x hx _ ⟨v, rfl⟩
    refine ⟨x v, ?_⟩
    simp [hcomm x hx v]
  rcases trivial_or_commSpace_le hperf hirr (hUinv.mono hLL₀) with htriv | hle
  · have hyU := trivial_of_trivial hLL₀ hL₀ hperf hLne hUinv htriv y hyL₀
    have hy2 : y ^ 2 = 1 := by
      ext v
      have h := hyU _ (hmemU v)
      rw [map_sub] at h
      rw [pow_two, LinearEquiv.mul_apply, LinearEquiv.coe_one, id]
      have e1 : y (y v) = (y v + y v) - v := by rw [sub_eq_iff_eq_add.1 h]; abel
      rw [e1, add_self_eq_zero', zero_sub]
      exact neg_eq_iff_add_eq_zero.2 (add_self_eq_zero' v)
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    have h1 : orderOf y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.1 h1
  · exfalso
    obtain ⟨l, hl, w, hw, hlw⟩ := hLW
    obtain ⟨u, hu⟩ := hle (sub_mem_commSpace hl (Submodule.mem_top : w ∈ ⊤))
    have hu' : y u - u = l w - w := by simpa using hu
    have h2 : y u - u ∈ W₁ := by rw [hu']; exact W₁.sub_mem (hW₁ l hl w hw) hw
    exact hlw (hu' ▸ mem_of_sub_mem hy₁ hyW hodd u h2)

private theorem tilde_sect {L L₀ H : Subgroup (GLV V)} {W₀ W₁ : Submodule (ZMod 2) V}
    (hLL₀ : L ≤ L₀) (hL₀H : L₀ ≤ H) (hnorm : ∀ h ∈ H, ∀ x ∈ L₀, h * x * h⁻¹ ∈ L₀)
    (hL₀ : Open.IsQuasisimple ↥L₀) (hperf : ⁅L, L⁆ = L) (hLne : L ≠ ⊥) (hirr : HasIrrTildeV L)
    (h₀ : Invariant H W₀) (h₁ : Invariant H W₁) (hirrW : IrrSec H W₀ W₁)
    (hLW : ∃ l ∈ L, ∃ w ∈ W₁, l w - w ∉ W₀) :
    HasIrrTildeV L₀ ∧ commSpace L₀ ⊤ ≤ W₁ ∧
      (∀ u ∈ commSpace L₀ ⊤, u ∈ W₀ ↔ u ∈ fixedSpace L₀) ∧
      (∀ w ∈ W₁, ∃ u ∈ commSpace L₀ ⊤, w - u ∈ W₀) := by
  obtain ⟨hperf₀, -⟩ := perfect_ne_bot hL₀
  have hL₀L₀ : ∀ x ∈ L₀, ∀ y ∈ L₀, x * y * x⁻¹ ∈ L₀ := fun x hx y hy =>
    L₀.mul_mem (L₀.mul_mem hx hy) (L₀.inv_mem hx)
  have hUinv : Invariant L₀ (commSpace L₀ ⊤) := invariant_commSpace hL₀L₀ (invariant_top L₀)
  have hW₀L₀ : Invariant L₀ W₀ := h₀.mono hL₀H
  have hW₁L₀ : Invariant L₀ W₁ := h₁.mono hL₀H
  have hW01 : W₀ ≤ W₁ := hirrW.1.le
  have hirr₀ : HasIrrTildeV L₀ := by
    refine ⟨lt_of_le_of_ne inf_le_right fun heq => ?_, fun J hJ hJ1 hJ2 => ?_⟩
    · have hU : commSpace L₀ ⊤ ≤ fixedSpace L₀ := heq.ge.trans inf_le_left
      have h' : commSpace L ⊤ ≤ tildeVBot L :=
        le_inf ((commSpace_mono hLL₀ le_rfl).trans (hU.trans (fixedSpace_anti hLL₀))) le_rfl
      exact lt_irrefl _ (lt_of_lt_of_le hirr.1 h')
    · rcases trivial_or_commSpace_le hperf hirr (hJ.mono hLL₀) with ht | hle
      · left
        exact le_antisymm (fun j hj =>
          ⟨fun x hx => trivial_of_trivial hLL₀ hL₀ hperf hLne hJ ht x hx j hj, hJ2 hj⟩) hJ1
      · right
        exact le_antisymm hJ2 (commSpace_le_of_le hLL₀ hL₀ hperf hLne hJ hle)
  obtain ⟨l₀, hl₀, w₀, hw₀, hlw₀⟩ := hLW
  have hL₀W : ¬ ∀ x ∈ L₀, ∀ w ∈ W₁, x w - w ∈ W₀ := fun h => hlw₀ (h l₀ (hLL₀ hl₀) w₀ hw₀)
  have hJ1 : commSpace L₀ W₁ ⊔ W₀ = W₁ := by
    have hinv : Invariant H (commSpace L₀ W₁ ⊔ W₀) := (invariant_commSpace hnorm h₁).sup h₀
    rcases hirrW.2 _ hinv le_sup_right (sup_le (commSpace_le_of_invariant hW₁L₀) hW01) with h | h
    · exfalso
      exact hL₀W fun x hx w hw => h.le (le_sup_left (a := commSpace L₀ W₁) (b := W₀)
        (sub_mem_commSpace hx hw))
    · exact h
  have hJ2 : ∀ w ∈ W₁, (∀ x ∈ L₀, x w - w ∈ W₀) → w ∈ W₀ := by
    let J : Submodule (ZMod 2) V :=
      { carrier := {w | w ∈ W₁ ∧ ∀ x ∈ L₀, x w - w ∈ W₀}
        add_mem' := fun {a b} ha hb => ⟨W₁.add_mem ha.1 hb.1, fun x hx => by
          rw [map_add, show x a + x b - (a + b) = (x a - a) + (x b - b) by abel]
          exact W₀.add_mem (ha.2 x hx) (hb.2 x hx)⟩
        zero_mem' := ⟨W₁.zero_mem, fun x _ => by simp⟩
        smul_mem' := fun c a ha => ⟨W₁.smul_mem c ha.1, fun x hx => by
          rw [map_smul, ← smul_sub]
          exact W₀.smul_mem c (ha.2 x hx)⟩ }
    have hJinv : Invariant H J := by
      intro h hh w hw
      refine ⟨h₁ h hh w hw.1, fun x hx => ?_⟩
      have e : x (h w) - h w = h ((h⁻¹ * x * h) w - w) := by
        simp only [LinearEquiv.mul_apply, map_sub]
        simp
      rw [e]
      have hx' : h⁻¹ * x * h ∈ L₀ := by
        have := hnorm h⁻¹ (H.inv_mem hh) x hx
        simpa using this
      exact h₀ h hh _ (hw.2 _ hx')
    have hW₀J : W₀ ≤ J := fun w hw => ⟨hW01 hw, fun x hx => W₀.sub_mem (hW₀L₀ x hx w hw) hw⟩
    rcases hirrW.2 J hJinv hW₀J (fun w hw => hw.1) with h | h
    · intro w hw hfix
      have hwJ : w ∈ J := ⟨hw, hfix⟩
      rwa [h] at hwJ
    · exfalso
      exact hL₀W fun x hx w hw => (h.ge hw).2 x hx
  have hUW₁ : commSpace L₀ ⊤ ≤ W₁ := by
    rcases trivial_or_commSpace_le hperf₀ hirr₀ (hUinv.inf hW₁L₀) with ht | hle
    · exfalso
      apply hL₀W
      intro x hx w hw
      have hw' : w ∈ commSpace L₀ W₁ ⊔ W₀ := by rw [hJ1]; exact hw
      obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.1 hw'
      have hc' : x c = c :=
        ht x hx c ⟨commSpace_mono le_rfl le_top hc, commSpace_le_of_invariant hW₁L₀ hc⟩
      rw [map_add, hc', show c + x d - (c + d) = x d - d by abel]
      exact W₀.sub_mem (hW₀L₀ x hx d hd) hd
    · exact hle.trans inf_le_right
  have hUW₀ : ∀ u ∈ commSpace L₀ ⊤, u ∈ W₀ → u ∈ fixedSpace L₀ := by
    rcases trivial_or_commSpace_le hperf₀ hirr₀ (hUinv.inf hW₀L₀) with ht | hle
    · exact fun u hu hu0 x hx => ht x hx u ⟨hu, hu0⟩
    · exfalso
      have h1 : commSpace L₀ W₁ ≤ W₀ :=
        (commSpace_mono le_rfl le_top).trans (hle.trans inf_le_right)
      have h2 : W₁ ≤ W₀ := by rw [← hJ1]; exact sup_le h1 le_rfl
      exact lt_irrefl _ (lt_of_lt_of_le hirrW.1 h2)
  refine ⟨hirr₀, hUW₁, fun u hu => ⟨hUW₀ u hu, fun hfix => hJ2 u (hUW₁ hu) fun x hx => ?_⟩,
    fun w hw => ?_⟩
  · rw [hfix x hx, sub_self]
    exact W₀.zero_mem
  · have hw' : w ∈ commSpace L₀ W₁ ⊔ W₀ := by rw [hJ1]; exact hw
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.1 hw'
    exact ⟨c, commSpace_mono le_rfl le_top hc, by simpa using hd⟩

private theorem tildeVWitness_of_sect {L₀ H : Subgroup (GLV V)} {W₀ W₁ : Submodule (ZMod 2) V}
    (hL₀H : L₀ ≤ H) (h₀ : Invariant H W₀) (h₁ : Invariant H W₁)
    (hUW₁ : commSpace L₀ ⊤ ≤ W₁) (hUW₀ : ∀ u ∈ commSpace L₀ ⊤, u ∈ W₀ ↔ u ∈ fixedSpace L₀)
    (hsurj : ∀ w ∈ W₁, ∃ u ∈ commSpace L₀ ⊤, w - u ∈ W₀)
    {X M : Type} [Group X] [AddGroup M] (Rel : X → M → M → Prop)
    (α : ↥L₀ →* X) (hα : Function.Surjective α) (ψ : Sect W₀ W₁ →+ M)
    (hψ : Function.Bijective ψ)
    (hRel : ∀ (ℓ : ↥L₀) (q : Sect W₀ W₁),
      Rel (α ℓ) (ψ q) (ψ (sectHom H h₀ h₁ (Subgroup.inclusion hL₀H ℓ) q))) :
    TildeVWitness L₀ X M Rel := by
  let β₀ : ↥(commSpace L₀ ⊤) →ₗ[ZMod 2] Sect W₀ W₁ :=
    (W₀.comap W₁.subtype).mkQ ∘ₗ Submodule.inclusion hUW₁
  have hβ₀ : ∀ u : ↥(commSpace L₀ ⊤), β₀ u = Submodule.Quotient.mk ⟨u, hUW₁ u.2⟩ :=
    fun u => rfl
  refine ⟨α, hα, ψ.comp β₀.toAddMonoidHom, ?_, ?_, ?_⟩
  · refine hψ.2.comp fun q => ?_
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨u, hu, hwu⟩ := hsurj w w.2
    refine ⟨⟨u, hu⟩, ?_⟩
    show β₀ ⟨u, hu⟩ = _
    rw [hβ₀]
    exact (mk_eq_mk_iff' _ _).2 (by rw [← neg_sub]; exact W₀.neg_mem hwu)
  · ext u
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Submodule.mem_toAddSubgroup,
      Submodule.mem_comap, Submodule.subtype_apply]
    rw [map_eq_zero_iff ψ hψ.1]
    rw [show (β₀.toAddMonoidHom u) = β₀ u from rfl, hβ₀, Submodule.Quotient.mk_eq_zero]
    exact hUW₀ u u.2
  · intro ℓ w w' hw'
    have e : β₀ w' = sectHom H h₀ h₁ (Subgroup.inclusion hL₀H ℓ) (β₀ w) := by
      rw [hβ₀, hβ₀, sectHom_mk]
      congr 1
      exact Subtype.ext hw'
    show Rel (α ℓ) (ψ (β₀ w)) (ψ (β₀ w'))
    rw [e]
    exact hRel ℓ (β₀ w)

private theorem faithfulTildeV_of_sect {L₀ H : Subgroup (GLV V)} {W₀ W₁ : Submodule (ZMod 2) V}
    (hL₀H : L₀ ≤ H) (h₀ : Invariant H W₀) (h₁ : Invariant H W₁)
    (hUW₀ : ∀ u ∈ commSpace L₀ ⊤, u ∈ W₀ ↔ u ∈ fixedSpace L₀)
    (hsurj : ∀ w ∈ W₁, ∃ u ∈ commSpace L₀ ⊤, w - u ∈ W₀)
    (hker : ∀ x : ↥L₀, sectHom H h₀ h₁ (Subgroup.inclusion hL₀H x) = 1 → x = 1) :
    FaithfulTildeV L₀ := by
  intro ℓ hℓ hfix
  have h1 := hker ⟨ℓ, hℓ⟩ ((sectHom_eq_one_iff' h₀ h₁ _).2 fun w hw => ?_)
  · exact congrArg Subtype.val h1
  · obtain ⟨u, hu, hwu⟩ := hsurj w hw
    have h2 : ℓ u - u ∈ W₀ :=
      (hUW₀ _ (sub_mem_commSpace hℓ Submodule.mem_top)).2 (hfix u hu)
    have h3 : ℓ (w - u) - (w - u) ∈ W₀ := W₀.sub_mem (h₀ ℓ (hL₀H hℓ) _ hwu) hwu
    have e : ℓ w - w = (ℓ u - u) + (ℓ (w - u) - (w - u)) := by rw [map_sub]; abel
    show ℓ w - w ∈ W₀
    rw [e]
    exact W₀.add_mem h2 h3

end Modules

section Config

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem normalClosure_le_of_le' {Γ L K : Subgroup (GLV V)} (hΓ : Γ ≤ K) (hL : L ≤ K) :
    normalClosure Γ L ≤ K := by
  rw [normalClosure, Subgroup.closure_le]
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  exact K.mul_mem (K.mul_mem (hΓ hγ) (hL hl)) (K.inv_mem (hΓ hγ))

private theorem normalClosure_mono' {Γ Γ' L L' : Subgroup (GLV V)} (hΓ : Γ ≤ Γ') (hL : L ≤ L') :
    normalClosure Γ L ≤ normalClosure Γ' L' := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  exact ⟨γ, hΓ hγ, l, hL hl, rfl⟩

private theorem centralizer_zpowers' (r : GLV V) :
    Subgroup.centralizer ((Subgroup.zpowers r : Subgroup (GLV V)) : Set (GLV V)) =
      Subgroup.centralizer ({r} : Set (GLV V)) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private instance instFiniteSectClimb (W₀ W₁ : Submodule (ZMod 2) V) : Finite (Sect W₀ W₁) :=
  Module.finite_of_finite (ZMod 2)

end Config

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

open scoped commutatorElement in
theorem climbB (hSA : SchurAltLift) (hSU : SchurU42Lift) {G S L' R L : Subgroup (GLV V)}
    {r : GLV V} (h : Extremal G S L') (hcL : Conf66 G R L) (hfL : FaithfulTildeV L)
    (hrR : r ∈ R) (hrC : r ∈ Subgroup.centralizer (R : Set (GLV V))) (hr2 : orderOf r = 2) :
    ∃ L₀ : Subgroup (GLV V), L ≤ L₀ ∧
      IsComponentOf L₀ (G ⊓ Subgroup.centralizer ({r} : Set (GLV V))) ∧ HasIrrTildeV L₀ ∧
      FaithfulTildeV L₀ ∧ IsFPrimeModule L₀ ∧
      (L₀ = L ∨ (∃ n k : ℕ, 6 ≤ n ∧ 1 ≤ k ∧ Nonempty (↥L ≃* alternatingGroup (Fin n)) ∧
          Nonempty (↥L₀ ≃* alternatingGroup (Fin (n + 2 * k)))) ∨
        Nonempty (↥L₀ ≃* ↥(CFSG.RankThree.PartTwo.omegaMinusTwo 2))) := by
  have hs : Setup6 G R L := hcL.setup.toSetup6
  have hR : IsPGroup 2 R := hcL.setup.isPGroup
  have hRG : R ≤ G := hcL.setup.S_le
  have hcomp := hcL.setup.component
  have hrG : r ∈ G := hRG hrR
  set H₀ : Subgroup (GLV V) := G ⊓ Subgroup.centralizer ({r} : Set (GLV V)) with hH₀def
  have hH₀G : H₀ ≤ G := inf_le_left
  have hLH₀ : L ≤ H₀ := fun x hx => ⟨(hcomp.1 hx).1, Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 (hcomp.1 hx).2 r hrR).symm⟩
  have hRH₀ : R ≤ H₀ := fun x hx => ⟨hRG hx, Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 hrC x hx)⟩
  have hLR : L ⊔ R ≤ H₀ := sup_le hLH₀ hRH₀
  set L₀ : Subgroup (GLV V) := normalClosure (layerIn H₀) L with hL₀def
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (GLV V), H = L₀ ⊔ R := ⟨_, rfl⟩
  have hLL₀ : L ≤ L₀ := le_normalClosure _ _
  have hL₀H : L₀ ≤ H := by rw [hH]; exact le_sup_left
  have hLH : L ≤ H := hLL₀.trans hL₀H
  have hL₀H₀ : L₀ ≤ H₀ := normalClosure_le_of_le' (Subgroup.map_subtype_le _) hLH₀
  have hHH₀ : H ≤ H₀ := by rw [hH]; exact sup_le hL₀H₀ hRH₀
  obtain ⟨hLperf, hLne⟩ := perfect_ne_bot hcomp.2.2
  obtain ⟨W₀, W₁, h₀, h₁, hirr, hnt⟩ := exists_irrSec_nontrivial_of_perfect hLH hLperf hLne
  obtain ⟨hconf, hfaith, hinj⟩ :=
    hcL.conf66_sect hfL hs hH₀G hLR hH h₀ h₁ hirr hnt
  obtain ⟨-, hmapE, hcent⟩ := lemma63 hs hH₀G hLR hH h₀ h₁ hirr hnt
  have hEH : layerIn H = L₀ := layerIn_eq_normalClosure hs hH₀G hLR hH
  rw [hEH] at hmapE hcent
  set φH := sectHom H h₀ h₁ with hφH
  set Hb := φH.range with hHb
  set Lb := (L.subgroupOf H).map φH with hLb
  set Rb := (R.subgroupOf H).map φH with hRb
  have hLW : ∃ l ∈ L, ∃ w ∈ W₁, l w - w ∉ W₀ := by
    obtain ⟨l, hl1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hLne
    by_contra hcon
    push Not at hcon
    apply hl1
    have h1 := hinj ⟨l, hLH l.2⟩ l.2 ((sectHom_eq_one_iff' h₀ h₁ _).2 (hcon l l.2))
    exact Subtype.ext (congrArg (fun x : ↥H => (x : GLV V)) h1)
  have eLb : ↥L ≃* ↥Lb := by
    refine (Subgroup.subgroupOfEquivOfLe hLH).symm.trans
      (MulEquiv.ofBijective (φH.subgroupMap (L.subgroupOf H))
        ⟨?_, φH.subgroupMap_surjective _⟩)
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : φH x = 1 := congrArg Subtype.val hx
    exact Subtype.ext (hinj x x.2 h1)
  have hH₀ne : H₀ ≠ G := by
    intro heq
    refine not_mem_of_orderOf_eq_two hr2 h.setup.odd_card_center
      ⟨hrG, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have hg' : g ∈ H₀ := by rw [heq]; exact hg
    exact Subgroup.mem_centralizer_singleton_iff.1 hg'.2
  have hcard : Nat.card Hb < Nat.card G :=
    calc Nat.card Hb ≤ Nat.card H := Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd φH)
      _ ≤ Nat.card H₀ := Subgroup.card_le_of_le hHH₀
      _ < Nat.card G := Subgroup.card_lt_of_lt (lt_of_le_of_ne hH₀G hH₀ne)
  have hconcl : Concl66 Hb Lb := h.min _ Hb Rb Lb hcard hconf hfaith
  have hsb : Setup6Irr Hb Rb Lb := hconf.setup
  have hLbE : Lb ≤ layerIn Hb := hsb.toSetup6.le_layerIn
  have hLbq : Open.IsQuasisimple ↥Lb := hsb.component.2.2
  have hq : CFSG.IsQuasisimple ↥(layerIn Hb) := by
    rcases hconcl with h1 | ⟨n, k, hn, hk, -, φ, -, -⟩ | ⟨-, φ, -, -⟩
    · have he : layerIn Hb = Lb := le_antisymm ((Subgroup.map_subtype_le _).trans h1.ge) hLbE
      rw [he]
      exact isQuasisimple_native hLbq
    · exact isQuasisimple_native (Open.IsQuasisimple.of_mulEquiv φ (isQuasisimple_alt (by omega)))
    · exact isQuasisimple_native (Open.IsQuasisimple.of_mulEquiv φ isQuasisimple_omegaMinusTwo)
  have hL₀comp : IsComponentOf L₀ H₀ :=
    isComponentOf_normalClosure hs hH₀G hLR hH h₀ h₁ hirr hnt hq
  by_cases hL₀L : L₀ = L
  · exact ⟨L₀, hLL₀, hL₀comp, hL₀L ▸ hcL.setup.irrTilde, hL₀L ▸ hfL, hL₀L ▸ hcL.fmod,
      Or.inl hL₀L⟩
  have hL₀q : Open.IsQuasisimple ↥L₀ := hL₀comp.2.2
  obtain ⟨hL₀perf, -⟩ := perfect_ne_bot hL₀q
  have hL₀top : ⁅(⊤ : Subgroup ↥L₀), ⊤⁆ = ⊤ := hL₀q.1
  have hLlt : Nat.card L < Nat.card L₀ :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hLL₀ (Ne.symm hL₀L))
  have hL₀norm : ∀ x ∈ H, ∀ y ∈ L₀, x * y * x⁻¹ ∈ L₀ := by
    intro x hx y hy
    rw [← hEH] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_map_subtype' (CFSG.layer ↥H) hx) y).1 hy
  have hτmem : ∀ x : ↥L₀, φH (Subgroup.inclusion hL₀H x) ∈ layerIn Hb := fun x => by
    rw [← hmapE]
    exact ⟨Subgroup.inclusion hL₀H x, x.2, rfl⟩
  set τ : ↥L₀ →* ↥(layerIn Hb) :=
    (φH.comp (Subgroup.inclusion hL₀H)).codRestrict _ hτmem with hτdef
  have hτapply : ∀ x : ↥L₀,
      ((τ x : ↥(layerIn Hb)) : GLV (Sect W₀ W₁)) = φH (Subgroup.inclusion hL₀H x) :=
    fun x => rfl
  have hτsurj : Function.Surjective τ := by
    rintro ⟨e, he⟩
    rw [← hmapE] at he
    obtain ⟨y, hy, rfl⟩ := he
    exact ⟨⟨y, hy⟩, Subtype.ext rfl⟩
  have hτker : ∀ x : ↥L₀, τ x = 1 ↔ φH (Subgroup.inclusion hL₀H x) = 1 := fun x => by
    rw [← hτapply]
    exact ⟨fun h1 => by rw [h1]; rfl, fun h1 => Subtype.ext h1⟩
  have hτcent : τ.ker ≤ Subgroup.center ↥L₀ := by
    intro x hx
    have h2 := hcent (Subgroup.inclusion hL₀H x) x.2 ((hτker x).1 hx)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 g g.2)
  have hτ2 : IsPGroup 2 ↥τ.ker := by
    intro g
    set y : GLV V := ((g : ↥L₀) : GLV V) with hy
    have hgL₀ : y ∈ L₀ := (g : ↥L₀).2
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    refine ⟨a, ?_⟩
    have hgker : φH (Subgroup.inclusion hL₀H (g : ↥L₀)) = 1 := (hτker _).1 g.2
    have hzord : orderOf (y ^ 2 ^ a) = b := by
      rw [orderOf_pow_of_dvd (by positivity) (hab ▸ dvd_mul_right _ _), hab,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hz1 : y ^ 2 ^ a = 1 := by
      refine eq_one_of_odd hLL₀ hL₀q hLperf hLne hs.irrTilde (h₁.mono hLH) hLW
        (L₀.pow_mem hgL₀ _) (fun x hx => ?_) (fun w hw => h₁ _ (H.pow_mem (hL₀H hgL₀) _) w hw)
        (fun w hw => ?_) (hzord ▸ hb)
      · have hc : y * x = x * y := (congrArg Subtype.val
          (Subgroup.mem_center_iff.1 (hτcent g.2) ⟨x, hx⟩)).symm
        exact (Commute.pow_left hc _).eq
      · have hz : (⟨y ^ 2 ^ a, H.pow_mem (hL₀H hgL₀) _⟩ : ↥H) =
            (Subgroup.inclusion hL₀H (g : ↥L₀)) ^ 2 ^ a := Subtype.ext (by simp [hy])
        have h1 : φH ⟨y ^ 2 ^ a, H.pow_mem (hL₀H hgL₀) _⟩ = 1 := by
          rw [hz, map_pow, hgker, one_pow]
        exact (sectHom_eq_one_iff' h₀ h₁ _).1 h1 w hw
    apply Subtype.ext
    apply Subtype.ext
    simpa [hy] using hz1
  have hLmap : (L.subgroupOf L₀).map τ = Lb.subgroupOf (layerIn Hb) := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.inclusion hL₀H x, hx, rfl⟩
    · intro he
      obtain ⟨y, hy, hye⟩ := he
      refine ⟨⟨y, hLL₀ hy⟩, hy, Subtype.ext ?_⟩
      rw [hτapply]
      exact hye
  have hLτ : ∀ x ∈ L.subgroupOf L₀, τ x = 1 → x = 1 := by
    intro x hx h1
    have h2 := hinj (Subgroup.inclusion hL₀H x) hx ((hτker x).1 h1)
    exact Subtype.ext (congrArg (fun x : ↥H => (x : GLV V)) h2)
  obtain ⟨hirr₀, hUW₁, hUW₀, hsurjW⟩ :=
    tilde_sect hLL₀ hL₀H hL₀norm hL₀q hLperf hLne hs.irrTilde h₀ h₁ hirr hLW
  rcases hconcl with h1 | ⟨n, k, hn, hk, ⟨eL⟩, φ, ψ, hφψ⟩ | ⟨⟨eL⟩, φ, ψ, hφψ⟩
  ·
    exfalso
    apply hL₀L
    refine le_antisymm ?_ hLL₀
    have hdec : ∀ a ∈ L₀, ∃ l ∈ L, ∃ z ∈ L₀, a = l * z ∧ ∀ w ∈ L₀, z * w = w * z := by
      intro a ha
      have hmem : φH (Subgroup.inclusion hL₀H ⟨a, ha⟩) ∈ Lb := by
        rw [h1]
        exact ⟨_, rfl⟩
      obtain ⟨l, hl, hle⟩ := hmem
      set z : ↥H := l⁻¹ * Subgroup.inclusion hL₀H ⟨a, ha⟩ with hz
      have hz1 : φH z = 1 := by rw [hz, map_mul, map_inv, hle, inv_mul_cancel]
      have hzL₀ : (z : GLV V) ∈ L₀ := L₀.mul_mem (L₀.inv_mem (hLL₀ hl)) ha
      have hzc := hcent z hzL₀ hz1
      refine ⟨(l : GLV V), hl, (z : GLV V), hzL₀, ?_,
        fun w hw => (Subgroup.mem_centralizer_iff.1 hzc w hw).symm⟩
      simp [hz]
    rw [← hL₀perf, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨l₁, hl₁, z₁, hz₁, rfl, hc₁⟩ := hdec a ha
    obtain ⟨l₂, hl₂, z₂, hz₂, rfl, hc₂⟩ := hdec b hb
    have e1 : z₁ * (l₂ * z₂) = (l₂ * z₂) * z₁ := hc₁ _ (L₀.mul_mem (hLL₀ hl₂) hz₂)
    have e2 : z₂ * l₁⁻¹ = l₁⁻¹ * z₂ := hc₂ _ (L₀.inv_mem (hLL₀ hl₁))
    have e : ⁅l₁ * z₁, l₂ * z₂⁆ = ⁅l₁, l₂⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc l₁ * z₁ * (l₂ * z₂) * (l₁ * z₁)⁻¹ * (l₂ * z₂)⁻¹
          = l₁ * (z₁ * (l₂ * z₂)) * z₁⁻¹ * l₁⁻¹ * z₂⁻¹ * l₂⁻¹ := by group
        _ = l₁ * ((l₂ * z₂) * z₁) * z₁⁻¹ * l₁⁻¹ * z₂⁻¹ * l₂⁻¹ := by rw [e1]
        _ = l₁ * l₂ * (z₂ * l₁⁻¹) * z₂⁻¹ * l₂⁻¹ := by group
        _ = l₁ * l₂ * (l₁⁻¹ * z₂) * z₂⁻¹ * l₂⁻¹ := by rw [e2]
        _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by group
    rw [e, ← hLperf]
    exact Subgroup.commutator_mem_commutator hl₁ hl₂
  ·
    have hM8 : 8 ≤ (n + 2 * k) := by omega
    set φ' : ↥(layerIn Hb) →* Equiv.Perm (Fin (n + 2 * k)) :=
      (alternatingGroup (Fin (n + 2 * k))).subtype.comp φ.toMonoidHom with hφ'
    have hφ'inj : Function.Injective φ' := Subtype.val_injective.comp φ.injective
    set π : ↥L₀ →* Equiv.Perm (Fin (n + 2 * k)) := φ'.comp τ with hπ
    have hπker : π.ker = τ.ker := by
      ext x
      simp only [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply]
      exact ⟨fun h2 => hφ'inj (h2.trans (map_one φ').symm), fun h2 => by rw [h2, map_one]⟩
    have hπrange : π.range = alternatingGroup (Fin (n + 2 * k)) := by
      ext σ
      constructor
      · rintro ⟨x, rfl⟩
        exact (φ (τ x)).2
      · intro hσ
        obtain ⟨x, hx⟩ := hτsurj (φ.symm ⟨σ, hσ⟩)
        exact ⟨x, by simp [hπ, hφ', hx]⟩
    obtain ⟨F, hF5, hF⟩ := exists_altOn (by omega) φ (Subgroup.map_subtype_le _)
      (le_normalizer_map_subtype' (CFSG.layer ↥Hb)) hsb.isPGroup hsb.S_le hsb.component hLbE
    have hπL : (L.subgroupOf L₀).map π = altOn F := by
      rw [hπ, ← Subgroup.map_map, hLmap, hF]
    have hLinj : ∀ x ∈ L.subgroupOf L₀, π x = 1 → x = 1 := fun x hx hπx =>
      hLτ x hx (by rw [← MonoidHom.mem_ker, ← hπker]; exact hπx)
    have hker : π.ker = ⊥ := hSA ↥L₀ (n + 2 * k) hM8 π hπrange hL₀top (hπker ▸ hτcent) (hπker ▸ hτ2)
      (L.subgroupOf L₀) F (by omega) hπL hLinj
    have hτinj : Function.Injective τ := (MonoidHom.ker_eq_bot_iff τ).1 (hπker ▸ hker)
    have hτker1 : ∀ x : ↥L₀, φH (Subgroup.inclusion hL₀H x) = 1 → x = 1 := fun x hx =>
      hτinj (((hτker x).2 hx).trans (map_one τ).symm)
    have eL₀ : ↥L₀ ≃* alternatingGroup (Fin (n + 2 * k)) :=
      (MulEquiv.ofBijective τ ⟨hτinj, hτsurj⟩).trans φ
    have hcardL₀ : Nat.card ↥L₀ = (n + 2 * k).factorial / 2 :=
      (Nat.card_congr eL₀.toEquiv).trans (card_alt (by omega))
    have hfaith₀ : FaithfulTildeV L₀ := faithfulTildeV_of_sect hL₀H h₀ h₁ hUW₀ hsurjW hτker1
    have hfmod₀ : IsFPrimeModule L₀ := Or.inl ⟨n + 2 * k, by omega,
      tildeVWitness_of_sect hL₀H h₀ h₁ hUW₁ hUW₀ hsurjW _ (φ.toMonoidHom.comp τ)
        (φ.surjective.comp hτsurj) ψ.toAddMonoidHom ψ.bijective
        (fun ℓ q x hx => hφψ (τ ℓ) q x hx)⟩
    exact ⟨L₀, hLL₀, hL₀comp, hirr₀, hfaith₀, hfmod₀,
      Or.inr (Or.inl ⟨n, k, hn, hk, ⟨eLb.trans eL⟩, ⟨eL₀⟩⟩)⟩
  ·
    set π : ↥L₀ →* ↥(CFSG.RankThree.PartTwo.omegaMinusTwo 2) := φ.toMonoidHom.comp τ with hπ
    have hπker : π.ker = τ.ker := by
      ext x
      simp only [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply]
      exact ⟨fun h2 => φ.injective (h2.trans (map_one φ).symm), fun h2 => by rw [h2, map_one]⟩
    have hπsurj : Function.Surjective π := φ.surjective.comp hτsurj
    have hLπ : Nonempty (↥((L.subgroupOf L₀).map π) ≃* alternatingGroup (Fin 6)) := by
      rw [hπ, ← Subgroup.map_map, hLmap]
      exact ⟨((Lb.subgroupOf (layerIn Hb)).equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans
        ((Subgroup.subgroupOfEquivOfLe hLbE).trans eL)⟩
    have hLinj : ∀ x ∈ L.subgroupOf L₀, π x = 1 → x = 1 := fun x hx hπx =>
      hLτ x hx (by rw [← MonoidHom.mem_ker, ← hπker]; exact hπx)
    have hker : π.ker = ⊥ := hSU ↥L₀ π hπsurj hL₀top (hπker ▸ hτcent) (hπker ▸ hτ2)
      (L.subgroupOf L₀) hLπ hLinj
    have hτinj : Function.Injective τ := (MonoidHom.ker_eq_bot_iff τ).1 (hπker ▸ hker)
    have hτker1 : ∀ x : ↥L₀, φH (Subgroup.inclusion hL₀H x) = 1 → x = 1 := fun x hx =>
      hτinj (((hτker x).2 hx).trans (map_one τ).symm)
    have eL₀ : ↥L₀ ≃* ↥(CFSG.RankThree.PartTwo.omegaMinusTwo 2) :=
      (MulEquiv.ofBijective τ ⟨hτinj, hτsurj⟩).trans φ
    have hcardL₀ : Nat.card ↥L₀ = 25920 := (Nat.card_congr eL₀.toEquiv).trans card_omegaMinusTwo
    have hcardL : Nat.card ↥L = 360 :=
      (Nat.card_congr (eLb.trans eL).toEquiv).trans (by rw [card_alt (by norm_num)]; decide)
    have hfaith₀ : FaithfulTildeV L₀ := faithfulTildeV_of_sect hL₀H h₀ h₁ hUW₀ hsurjW hτker1
    have hfmod₀ : IsFPrimeModule L₀ := Or.inr (Or.inr (Or.inr (Or.inl
      (tildeVWitness_of_sect hL₀H h₀ h₁ hUW₁ hUW₀ hsurjW _ (φ.toMonoidHom.comp τ)
        (φ.surjective.comp hτsurj) ψ.toAddEquiv.toAddMonoidHom ψ.bijective
        (fun ℓ q => hφψ (τ ℓ) q)))))
    exact ⟨L₀, hLL₀, hL₀comp, hirr₀, hfaith₀, hfmod₀, Or.inr (Or.inr ⟨eL₀⟩)⟩

theorem isQuasisimple_altGroup {n : ℕ} (hn : 5 ≤ n) :
    Open.IsQuasisimple ↥(alternatingGroup (Fin n)) := isQuasisimple_alt hn

theorem card_altGroup {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := card_alt hn

theorem card_omegaMinusTwo_two :
    Nat.card ↥(CFSG.RankThree.PartTwo.omegaMinusTwo 2) = 25920 := card_omegaMinusTwo

theorem perfect_ne_bot_of_isQuasisimple {Γ : Type*} [Group Γ] {L : Subgroup Γ}
    (hq : Open.IsQuasisimple ↥L) : ⁅L, L⁆ = L ∧ L ≠ ⊥ := perfect_ne_bot hq

theorem eq_of_perfect_le_of_normalized {Γ : Type*} [Group Γ] {L L₀ N : Subgroup Γ}
    (hL₀ : Open.IsQuasisimple ↥L₀) (hperf : ⁅L, L⁆ = L) (hLne : L ≠ ⊥) (hLN : L ≤ N)
    (hNL₀ : N ≤ L₀) (hnorm : ∀ g ∈ L₀, ∀ x ∈ N, g * x * g⁻¹ ∈ N) : N = L₀ :=
  eq_of_perfect_le hL₀ hperf hLne hLN hNL₀ hnorm

theorem not_mem_of_orderOf_two {Γ : Type*} [Group Γ] {K : Subgroup Γ} {r : Γ}
    (hr : orderOf r = 2) (hK : Odd (Nat.card K)) : r ∉ K := not_mem_of_orderOf_eq_two hr hK

theorem normalClosure_le_of_le_of_le {Γ L K : Subgroup (GLV V)} (hΓ : Γ ≤ K) (hL : L ≤ K) :
    normalClosure Γ L ≤ K := normalClosure_le_of_le' hΓ hL

theorem normalClosure_mono_both {Γ Γ' L L' : Subgroup (GLV V)} (hΓ : Γ ≤ Γ') (hL : L ≤ L') :
    normalClosure Γ L ≤ normalClosure Γ' L' := normalClosure_mono' hΓ hL

theorem conj_mem_normalClosure {Γ L : Subgroup (GLV V)} {γ x : GLV V} (hγ : γ ∈ Γ)
    (hx : x ∈ normalClosure Γ L) : γ * x * γ⁻¹ ∈ normalClosure Γ L := by
  have hle : normalClosure Γ L ≤ (normalClosure Γ L).comap (MulAut.conj γ).toMonoidHom := by
    rw [normalClosure, Subgroup.closure_le]
    rintro _ ⟨γ', hγ', l, hl, rfl⟩
    refine Subgroup.subset_closure ⟨γ * γ', Γ.mul_mem hγ hγ', l, hl, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hle hx

theorem normalClosure_le_normalClosure {Γ L L' : Subgroup (GLV V)}
    (hL : L ≤ normalClosure Γ L') : normalClosure Γ L ≤ normalClosure Γ L' := by
  rw [normalClosure, Subgroup.closure_le]
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  exact conj_mem_normalClosure hγ (hL hl)

theorem normal_eq_top_or_le_center' {Q : Type*} [Group Q] (hQ : Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q :=
  normal_eq_top_or_le_center hQ hN

theorem isQuasisimple_native' {Q : Type*} [Group Q] (hQ : Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := isQuasisimple_native hQ

theorem exists_altOn_fix {Γ : Type} [Group Γ] {Hb E Lb : Subgroup Γ} {M : ℕ} {r : Γ}
    (hM : 7 ≤ M) (φ : ↥E ≃* alternatingGroup (Fin M)) (hEH : E ≤ Hb)
    (hnorm : Hb ≤ Subgroup.normalizer (E : Set Γ)) (hr : r * r = 1) (hrH : r ∈ Hb)
    (hLb : IsComponentOf Lb (Hb ⊓ Subgroup.centralizer ((Subgroup.zpowers r : Subgroup Γ) : Set Γ)))
    (hLbE : Lb ≤ E) :
    ∃ τ : Equiv.Perm (Fin M), τ * τ = 1 ∧ 5 ≤ Nat.card ↥({i | τ i = i} : Set (Fin M)) ∧
      (Lb.subgroupOf E).map ((alternatingGroup (Fin M)).subtype.comp φ.toMonoidHom) =
        altOn {i | τ i = i} := by
  classical
  set Rz : Subgroup Γ := Subgroup.zpowers r with hRzdef
  have hRz : IsPGroup 2 ↥Rz := by
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show r ^ ((2 : ℕ) : ℤ) = 1 by
      rw [zpow_natCast, sq, hr], one_zpow]
  have hRzH : Rz ≤ Hb := Subgroup.zpowers_le.2 hrH
  obtain ⟨ρ, hρ⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129j.exists_perm_implementer
    (by omega) (by omega) φ hnorm
  set φ' : ↥E →* Equiv.Perm (Fin M) :=
    (alternatingGroup (Fin M)).subtype.comp φ.toMonoidHom with hφ'
  have hφ'inj : Function.Injective φ' := Subtype.val_injective.comp φ.injective
  have hφ'apply : ∀ e : ↥E, φ' e = ((φ e : alternatingGroup (Fin M)) : Equiv.Perm (Fin M)) :=
    fun e => rfl
  set R' : Subgroup (Equiv.Perm (Fin M)) := (Rz.subgroupOf Hb).map ρ with hR'
  have hR'2 : IsPGroup 2 ↥R' :=
    (IsPGroup.of_equiv hRz (Subgroup.subgroupOfEquivOfLe hRzH).symm).map ρ
  have key : ∀ (r : ↥Hb) (e : ↥E),
      ((r : Γ) * e = e * r ↔ ρ r * φ' e = φ' e * ρ r) := by
    intro r e
    have hy : (r : Γ) * e * (r : Γ)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.1 (hnorm r.2) e).1 e.2
    have h := hρ r e ⟨_, hy⟩ rfl
    rw [← hφ'apply, ← hφ'apply] at h
    constructor
    · intro hc
      have hye : (⟨_, hy⟩ : ↥E) = e := Subtype.ext (by
        show (r : Γ) * e * (r : Γ)⁻¹ = e
        rw [hc, mul_inv_cancel_right])
      rw [hye] at h
      calc ρ r * φ' e = (ρ r * φ' e * (ρ r)⁻¹) * ρ r := by group
        _ = φ' e * ρ r := by rw [← h]
    · intro hc
      have h2 : φ' ⟨_, hy⟩ = φ' e := by rw [h, hc, mul_inv_cancel_right]
      have h3 : (r : Γ) * e * (r : Γ)⁻¹ = e := congrArg Subtype.val (hφ'inj h2)
      calc (r : Γ) * e = ((r : Γ) * e * (r : Γ)⁻¹) * r := by group
        _ = e * r := by rw [h3]
  set X : Subgroup (Equiv.Perm (Fin M)) :=
    alternatingGroup (Fin M) ⊓ Subgroup.centralizer (R' : Set (Equiv.Perm (Fin M))) with hX
  have hXeq : ((E ⊓ Subgroup.centralizer (Rz : Set Γ)).subgroupOf E).map φ' = X := by
    ext σ
    constructor
    · rintro ⟨e, he, rfl⟩
      refine ⟨(φ e).2, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      have hr' : (r : Γ) ∈ Rz := hr
      have hc : (r : Γ) * e = e * r := Subgroup.mem_centralizer_iff.1 he.2 r hr'
      exact (key r e).1 hc
    · rintro ⟨hσA, hσC⟩
      refine ⟨φ.symm ⟨σ, hσA⟩, ⟨(φ.symm ⟨σ, hσA⟩).2, Subgroup.mem_centralizer_iff.2 ?_⟩, ?_⟩
      · intro g hg
        have h1 : φ' (φ.symm ⟨σ, hσA⟩) = σ := by rw [hφ'apply, MulEquiv.apply_symm_apply]
        have h2 : ρ ⟨g, hRzH hg⟩ * σ = σ * ρ ⟨g, hRzH hg⟩ :=
          Subgroup.mem_centralizer_iff.1 hσC _ ⟨⟨g, hRzH hg⟩, hg, rfl⟩
        rw [← h1] at h2
        exact (key ⟨g, hRzH hg⟩ _).2 h2
      · rw [hφ'apply, MulEquiv.apply_symm_apply]
  set K : Subgroup (Equiv.Perm (Fin M)) := (Lb.subgroupOf E).map φ' with hK
  have hLbs : Lb ≤ E ⊓ Subgroup.centralizer (Rz : Set Γ) :=
    le_inf hLbE (hLb.1.trans inf_le_right)
  have hsub1 : IsSubnormal Lb (E ⊓ Subgroup.centralizer (Rz : Set Γ)) := by
    have := hLb.2.1.inf_of_le (inf_le_inf_right _ hEH)
    rwa [inf_eq_left.2 hLbs] at this
  have hKX : IsComponentOf K X := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hXeq]
      exact Subgroup.map_mono (Subgroup.comap_mono hLbs)
    · rw [← hXeq]
      exact (hsub1.comap E.subtype).map φ'
    · have e1 : ↥K ≃* ↥(Lb.subgroupOf E) :=
        ((Lb.subgroupOf E).equivMapOfInjective φ' hφ'inj).symm
      exact Open.IsQuasisimple.of_mulEquiv (e1.trans (Subgroup.subgroupOfEquivOfLe hLbE))
        hLb.2.2
  obtain ⟨h5, hKeq⟩ := eq_altOn_of_isComponentOf hR'2 le_rfl inf_le_right hKX
  have hFix : ({i | ∀ r ∈ R', r i = i} : Set (Fin M)) = {i | ρ ⟨r, hrH⟩ i = i} := by
    ext i
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hi
      exact hi _ ⟨⟨r, hrH⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers r), rfl⟩
    · intro hi x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : (y : Γ) ∈ Subgroup.zpowers r := Subgroup.mem_subgroupOf.1 hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy'
      have : y = ⟨r, hrH⟩ ^ k := Subtype.ext (by rw [← hk]; rfl)
      rw [this, map_zpow]
      exact (Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hi k)
  refine ⟨ρ ⟨r, hrH⟩, by
    rw [← map_mul, show (⟨r, hrH⟩ : ↥Hb) * ⟨r, hrH⟩ = 1 from Subtype.ext hr, map_one],
    by rw [← hFix]; exact h5, hKeq.trans (congrArg altOn hFix)⟩

theorem centralizer_zpowers_eq (r : GLV V) :
    Subgroup.centralizer ((Subgroup.zpowers r : Subgroup (GLV V)) : Set (GLV V)) =
      Subgroup.centralizer ({r} : Set (GLV V)) := centralizer_zpowers' r

end CaseIClimbAux

end CFSG.CGT.Foote82
