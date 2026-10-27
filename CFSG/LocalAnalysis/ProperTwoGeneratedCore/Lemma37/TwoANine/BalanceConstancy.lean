module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.BalanceSignalizer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_of_map_conj_eq {H : Subgroup X} {g : X}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set X) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← h]
    exact ⟨x, hx, rfl⟩
  · rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [(MulAut.conj g).injective hyx] at hy

omit [Finite X] in
theorem map_conj_eq_of_mem_normalizer {H : Subgroup X} {g : X} (hg : g ∈ normalizer (H : Set X)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  refine ⟨?_, fun hx => ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · refine (Subgroup.mem_normalizer_iff.mp hg _).mpr ?_
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]

section Lift

variable {b : X} (hb : orderOf b = 2) (hJ : IsTwoANine (EscapingQuotient b))
include hb hJ

omit hb hJ in
theorem card_escapingImage_of_card_eq {A : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hA : Nat.card A = 16) (hAb : A ≤ centralizer {b}) : Nat.card (escapingImage A b) = 16 := by
  rw [card_escapingImage_of_isPGroup (isPGroup_of_sq_eq_one hA2) hAb, hA]

theorem mem_of_le_centralizer_of_card_eq {A : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hA : Nat.card A = 16) (hAb : A ≤ centralizer {b}) : b ∈ A := by
  obtain ⟨c, hc, hcb⟩ := hJ.zbar_mem_of_card_eq (fun y hy => sq_eq_one_of_mem_escapingImage hA2 hy)
    (card_escapingImage_of_card_eq hA2 hA hAb)
  have hc2 : c ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hA2 _ (Subgroup.mem_subgroupOf.mp hc), OneMemClass.coe_one])
  rw [← hJ.eq_of_escapingMk_eq_zbar hb hc2 hcb]
  exact Subgroup.mem_subgroupOf.mp hc

theorem exists_le_of_le_isPGroup {A A' T : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hA : Nat.card A = 16) (hA'2 : ∀ x ∈ A', x ^ 2 = 1) (hA' : Nat.card A' = 16)
    (hT : IsPGroup 2 T) (hTb : T ≤ centralizer {b}) (hAT : A ≤ T) (hA'T : A' ≤ T) :
    ∃ V : Subgroup X, V ≤ A ∧ V ≤ A' ∧ b ∈ V ∧ Nat.card V = 4 := by
  have hsub : ∀ {B : Subgroup X}, B ≤ T → escapingImage B b ≤ escapingImage T b := fun hBT =>
    Subgroup.map_mono fun c hc => Subgroup.mem_subgroupOf.mpr (hBT (Subgroup.mem_subgroupOf.mp hc))
  obtain ⟨V₀, hV₀A, hV₀A', hzV₀, hV₀⟩ := hJ.exists_le_of_le_of_isPGroup
    (fun y hy => sq_eq_one_of_mem_escapingImage hA2 hy)
    (card_escapingImage_of_card_eq hA2 hA (hAT.trans hTb))
    (fun y hy => sq_eq_one_of_mem_escapingImage hA'2 hy)
    (card_escapingImage_of_card_eq hA'2 hA' (hA'T.trans hTb))
    (hT.comap_subtype.map _) (hsub hAT) (hsub hA'T)
  set P : Subgroup (centralizer ({b} : Set X)) :=
    V₀.comap (escapingMk b) ⊓ A.subgroupOf (centralizer {b}) with hP
  have hPT : ∀ {c}, c ∈ P → (c : X) ∈ T := fun hc => hAT (Subgroup.mem_subgroupOf.mp hc.2)
  have hPmap : P.map (escapingMk b) = V₀ := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_left) fun v hv => ?_
    obtain ⟨c, hc, rfl⟩ := hV₀A hv
    exact ⟨c, ⟨hv, hc⟩, rfl⟩
  refine ⟨P.map (centralizer ({b} : Set X)).subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hc.2
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨c', hc', hc'c⟩ := hV₀A' hc.1
    rw [← eq_of_escapingMk_eq_of_isPGroup hT (hA'T (Subgroup.mem_subgroupOf.mp hc')) (hPT hc)
      hc'c]
    exact Subgroup.mem_subgroupOf.mp hc'
  · refine ⟨escapingSelf b, ⟨?_, ?_⟩, rfl⟩
    · show escapingMk b (escapingSelf b) ∈ V₀
      rw [hJ.zbar_eq_escapingBar hb] at hzV₀
      exact hzV₀
    · exact Subgroup.mem_subgroupOf.mpr
        (mem_of_le_centralizer_of_card_eq hb hJ hA2 hA (hAT.trans hTb))
  · rw [Subgroup.card_map_of_injective (centralizer ({b} : Set X)).subtype_injective, ← hV₀,
      ← hPmap, card_map_mk_of_isPGroup (escaping_oddCore_odd b)]
    exact (hT.comap_subtype (K := centralizer {b})).to_le fun c hc => hPT hc

end Lift

theorem signalizerJoin_eq_of_le_isPGroup
    (hall : ∀ c : X, orderOf c = 2 → IsTwoANine (EscapingQuotient c)) {b : X}
    (hb : orderOf b = 2) {A A' T : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA : Nat.card A = 16)
    (hA'2 : ∀ x ∈ A', x ^ 2 = 1) (hA' : Nat.card A' = 16) (hT : IsPGroup 2 T)
    (hTb : T ≤ centralizer {b}) (hAT : A ≤ T) (hA'T : A' ≤ T) :
    signalizerJoin A = signalizerJoin A' := by
  obtain ⟨V, hVA, hVA', -, hV⟩ :=
    exists_le_of_le_isPGroup hb (hall b hb) hA2 hA hA'2 hA' hT hTb hAT hA'T
  exact signalizerJoin_eq_of_le_of_le hA2 (by rw [hA]; norm_num)
    (fun c hc hc1 => hall c (orderOf_eq_prime (hA2 c hc) hc1)) hA'2 (by rw [hA']; norm_num)
    (fun c hc hc1 => hall c (orderOf_eq_prime (hA'2 c hc) hc1)) hVA hVA' hV

theorem le_normalizer_signalizerJoin_of_le
    (hall : ∀ c : X, orderOf c = 2 → IsTwoANine (EscapingQuotient c)) {b : X}
    (hb : orderOf b = 2) {A T : Subgroup X} (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA : Nat.card A = 16)
    (hT : IsPGroup 2 T) (hTb : T ≤ centralizer {b}) (hAT : A ≤ T) :
    T ≤ normalizer (signalizerJoin A : Set X) := by
  intro s hs
  refine mem_normalizer_of_map_conj_eq ?_
  rw [map_conj_signalizerJoin]
  refine (signalizerJoin_eq_of_le_isPGroup hall hb hA2 hA ?_ ?_ hT hTb hAT ?_).symm
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hA2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, hA]
  · rintro _ ⟨x, hx, rfl⟩
    exact T.mul_mem (T.mul_mem hs (hAT hx)) (T.inv_mem hs)

omit [Finite X] in
theorem normalizer_le_normalizer_signalizerJoin (A : Subgroup X) :
    normalizer (A : Set X) ≤ normalizer (signalizerJoin A : Set X) := fun g hg =>
  mem_normalizer_of_map_conj_eq (by rw [map_conj_signalizerJoin, map_conj_eq_of_mem_normalizer hg])

omit [Finite X] in
theorem le_centralizer_of_isCentralInvolution {S : Subgroup X} {t : X}
    (ht : IsCentralInvolution S t) : S ≤ centralizer {t} := fun s hs =>
  Subgroup.mem_centralizer_singleton_iff.mpr (ht.2.2 s hs)

theorem exists_le_sylow_of_isCentralInvolution (S : Sylow 2 X) {t : X}
    (ht : IsCentralInvolution (S : Subgroup X) t) (hJ : IsTwoANine (EscapingQuotient t)) :
    ∃ A : Subgroup X, A ≤ S ∧ (∀ x ∈ A, x ^ 2 = 1) ∧ Nat.card A = 16 ∧ t ∈ A := by
  have hSt := le_centralizer_of_isCentralInvolution ht
  set S' : Subgroup (centralizer ({t} : Set X)) := (S : Subgroup X).subgroupOf (centralizer {t})
  have hS' : IsPGroup 2 S' := S.isPGroup'.comap_subtype
  obtain ⟨E, hES, hE2, hE⟩ := hJ.exists_le_sylow
    ((S.subtype hSt).mapSurjective (QuotientGroup.mk'_surjective _))
  rw [Sylow.coe_mapSurjective, Sylow.coe_subtype] at hES
  set P : Subgroup (centralizer ({t} : Set X)) := E.comap (escapingMk t) ⊓ S' with hP
  have hPmap : P.map (escapingMk t) = E := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_left) fun v hv => ?_
    obtain ⟨c, hc, rfl⟩ := hES hv
    exact ⟨c, ⟨hv, hc⟩, rfl⟩
  have hPS : ∀ {c}, c ∈ P → (c : X) ∈ (S : Subgroup X) := fun hc => Subgroup.mem_subgroupOf.mp hc.2
  have hA2 : ∀ x ∈ P.map (centralizer ({t} : Set X)).subtype, x ^ 2 = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    have h1 : escapingMk t (c ^ 2) = 1 := by rw [map_pow]; exact hE2 _ hc.1
    have h2 := eq_one_of_mem_of_isPGroup_of_odd hS' (escaping_oddCore_odd t)
      (S'.pow_mem hc.2 2) ((QuotientGroup.eq_one_iff _).mp h1)
    rw [← map_pow, h2, map_one]
  have hA : Nat.card (P.map (centralizer ({t} : Set X)).subtype) = 16 := by
    rw [Subgroup.card_map_of_injective (centralizer ({t} : Set X)).subtype_injective, ← hE, ← hPmap,
      card_map_mk_of_isPGroup (escaping_oddCore_odd t) (hS'.to_le inf_le_right)]
  have hAS : P.map (centralizer ({t} : Set X)).subtype ≤ S := by
    rintro _ ⟨c, hc, rfl⟩
    exact hPS hc
  exact ⟨_, hAS, hA2, hA,
    mem_of_le_centralizer_of_card_eq ht.2.1 hJ hA2 hA (hAS.trans hSt)⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
