module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Gen
public import CFSG.Sporadic.Co1Patterson.NativeSetting
public import CFSG.Sporadic.Co1Patterson.GenerationClasses

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

theorem card_lt_pow_of_dvd {X : Type} [Group X] [Finite X] {F : Subgroup X} (hF : IsPGroup 3 F)
    {n k : ℕ} (hdvd : Nat.card F ∣ n) (hk : ¬ 3 ^ k ∣ n) : Nat.card F < 3 ^ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hF
  rw [hm] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hkm : k ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 hlt
  exact hk ((pow_dvd_pow 3 hkm).trans hdvd)

theorem elemAbelian_subgroupOf {X : Type} [Group X] {p : ℕ} {F C : Subgroup X}
    (hF : IsElemAbelian p F) : IsElemAbelian p (F.subgroupOf C) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
  · exact comm_of_elemAbelian' hF (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2)
  · exact hF.2 _ (Subgroup.mem_subgroupOf.1 ha)

open CFSG.Sporadic.Co1Patterson CFSG.Blueprint


set_option maxRecDepth 100000 in
theorem twoLocalBoundPow_co1 : TwoLocalBoundPow 4 NativeSporadic.Co1 := by
  haveI : Finite NativeSporadic.Co1 := inferInstance
  have hcls₀ := exists_involution_classes (Y := NativeSporadic.Co1) (MulEquiv.refl NativeSporadic.Co1)
  obtain ⟨a, b, c, hcls, -, -, -, -, -, -, hCa, hCb, hCc⟩ := hcls₀
  have hcardconj : ∀ {x y : NativeSporadic.Co1}, IsConj x y →
      Nat.card (Subgroup.centralizer ({x} : Set NativeSporadic.Co1)) =
        Nat.card (Subgroup.centralizer ({y} : Set NativeSporadic.Co1)) := by
    intro x y h
    obtain ⟨g, rfl⟩ := isConj_iff.1 h
    rw [CFSG.Sporadic.Co1Block.card_centralizer_equiv (MulAut.conj g) x, MulAut.conj_apply]
  have haA : IsConj a aNC := by
    rcases hcls aNC orderOf_aNC with h | h | h
    · exact h
    · have := hcardconj h
      rw [hCb, card_centralizer_aNC] at this
      norm_num at this
    · have := hcardconj h
      rw [hCc, card_centralizer_aNC] at this
      norm_num at this
  set T := nativeTypeSystem
  have hT := typeSystem_data (k := 4) (by norm_num) (Subgroup.subtype_injective _) T
  have hTz : ((T.z : Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1)) : NativeSporadic.Co1) =
      aNC := rfl
  have dAa : ∀ F : Subgroup NativeSporadic.Co1,
      F ≤ Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1) → IsElemAbelian 3 F →
        Nat.card F ≤ 3 ^ 4 := by
    intro F hF hE
    have := hT.1 _ (elemAbelian_subgroupOf (C := Subgroup.centralizer ({aNC} : Set _)) hE)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv] at this
  have dAb : ∀ F : Subgroup NativeSporadic.Co1,
      F ≤ Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1) → IsElemAbelian 3 F →
        Nat.card F = 3 ^ 4 → ∀ u : NativeSporadic.Co1, orderOf u = 2 →
          u ∈ Subgroup.centralizer (F : Set NativeSporadic.Co1) → u * aNC = aNC * u → u = aNC := by
    intro F hF hE hFk u hu huF hua
    have huC : u ∈ Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1) :=
      Subgroup.mem_centralizer_singleton_iff.2 hua
    set u' : Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1) := ⟨u, huC⟩
    have hu2 : u' * u' = 1 := by
      apply Subtype.ext
      show u * u = 1
      have := pow_orderOf_eq_one u
      rw [hu, sq] at this
      exact this
    have huF' : ∀ f ∈ F.subgroupOf (Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1)),
        f * u' = u' * f := fun f hf =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.1 huF) _ (Subgroup.mem_subgroupOf.1 hf))
    have hcard : Nat.card (F.subgroupOf (Subgroup.centralizer ({aNC} : Set NativeSporadic.Co1))) =
        3 ^ 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv, hFk]
    rcases hT.2 _ (elemAbelian_subgroupOf hE) hcard u' hu2 huF' with h | h
    · exfalso
      have : u = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at hu
      exact absurd hu (by norm_num)
    · have := congrArg Subtype.val h
      rw [hTz] at this
      exact this
  have dsmall : ∀ t : NativeSporadic.Co1, ¬ 3 ^ 4 ∣ Nat.card (Subgroup.centralizer ({t} : Set _)) →
      ∀ F : Subgroup NativeSporadic.Co1, F ≤ Subgroup.centralizer ({t} : Set NativeSporadic.Co1) →
        IsElemAbelian 3 F → Nat.card F < 3 ^ 4 := fun t ht F hF hE =>
    card_lt_pow_of_dvd (isPGroup_of_elemAbelian3' hE) (Subgroup.card_dvd_of_le hF) ht
  have hdata : ∀ t : NativeSporadic.Co1, orderOf t = 2 →
      (∀ F : Subgroup NativeSporadic.Co1, F ≤ Subgroup.centralizer ({t} : Set NativeSporadic.Co1) →
        IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 4) ∧
      (∀ F : Subgroup NativeSporadic.Co1, F ≤ Subgroup.centralizer ({t} : Set NativeSporadic.Co1) →
        IsElemAbelian 3 F → Nat.card F = 3 ^ 4 → ∀ u : NativeSporadic.Co1, orderOf u = 2 →
          u ∈ Subgroup.centralizer (F : Set NativeSporadic.Co1) → u * t = t * u → u = t) := by
    intro t ht
    rcases hcls t ht with h | h | h
    · exact involution_data_of_conj_k 4 dAa dAb (haA.symm.trans h)
    · have h81 : ¬ 3 ^ 4 ∣ Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.Co1)) := by
        rw [← hcardconj h, hCb]
        norm_num
      exact ⟨fun F hF hE => (dsmall t h81 F hF hE).le,
        fun F hF hE hFk => absurd hFk (dsmall t h81 F hF hE).ne⟩
    · have h81 : ¬ 3 ^ 4 ∣ Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.Co1)) := by
        rw [← hcardconj h, hCc]
        norm_num
      exact ⟨fun F hF hE => (dsmall t h81 F hF hE).le,
        fun F hF hE hFk => absurd hFk (dsmall t h81 F hF hE).ne⟩
  intro R₀ E hR hR2 hEN hE
  exact card_le_of_involution_data_k 4 (fun t ht => (hdata t ht).1) (fun t ht => (hdata t ht).2)
    R₀ E hR hR2 hEN hE

set_option maxRecDepth 100000 in
theorem i1016Co1Fact_holds : I1016Co1Fact := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Co1
  have φ₁ : K ≃* NativeSporadic.Carrier .Co1 := e.trans b.symm
  have hC : TwoLocalBoundPow 4 (NativeSporadic.Carrier .Co1) := by
    unfold NativeSporadic.Carrier
    exact twoLocalBoundPow_co1
  have hK : TwoLocalBoundPow 4 K := twoLocalBoundPow_of_mulEquiv φ₁ hC
  exact CFSG.LocalAnalysis.GLTheoremA.glaTwoLocalRank_le_of_card_le Nat.prime_three
    fun R₀ E hR hR2 hEN hE => hK R₀ E hR hR2 hEN hE

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
