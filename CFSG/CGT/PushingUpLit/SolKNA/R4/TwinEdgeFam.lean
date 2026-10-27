module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeDefs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Generic CFSG.Blueprint

section FourGen

variable {A : Type} [Group A] [Finite A]

theorem exists_comap_socle (T : Subgroup A) [T.Normal] (hTs : IsSimpleGroup ↥T)
    (hTab : ∃ a b : ↥T, a * b ≠ b * a) (hTC : Subgroup.centralizer (T : Set A) = ⊥)
    {Y : Type} [Group Y] [Finite Y] (ι : Y →* A) (hι : Function.Injective ι) (hT : T ≤ ι.range) :
    ∃ T₁ : Subgroup Y, T₁.Normal ∧ Nonempty (↥T₁ ≃* ↥T) ∧
      Subgroup.centralizer (T₁ : Set Y) = ⊥ ∧ genFittingFStar Y = T₁ ∧
      Subgroup.center Y = ⊥ := by
  have hmap : (T.comap ι).map ι = T := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hT
  let e : ↥(T.comap ι) ≃* ↥T :=
    (Subgroup.equivMapOfInjective (T.comap ι) ι hι).trans (MulEquiv.subgroupCongr hmap)
  have hC : Subgroup.centralizer ((T.comap ι : Subgroup Y) : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : ι y ∈ Subgroup.centralizer (T : Set A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨s, hs⟩ := hT ha
      have hsT : s ∈ T.comap ι := by rw [Subgroup.mem_comap, hs]; exact ha
      have := Subgroup.mem_centralizer_iff.mp hy s hsT
      rw [← hs, ← map_mul, ← map_mul, this]
    rw [hTC, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact hι (by rw [this, map_one])
  haveI : IsSimpleGroup ↥(T.comap ι) := e.isSimpleGroup
  have hnab : ∃ a b : ↥(T.comap ι), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hTab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  refine ⟨T.comap ι, inferInstance, ⟨e⟩, hC, genFittingFStar_eq_of_normal_simple _ hnab hC, ?_⟩
  rw [eq_bot_iff]
  intro c hc
  have : c ∈ Subgroup.centralizer ((T.comap ι : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    exact (Subgroup.mem_center_iff.mp hc g)
  rw [hC] at this
  exact this

section Thm6Step


theorem cit3Below_mono_R {m n : ℕ} (h : m ≤ n) (hn : CIT3Below n) : CIT3Below m :=
  fun Y _ _ hY Λ hΛ => hn Y (lt_of_lt_of_le hY h) Λ hΛ

theorem twoSubgroupsFourGenerated_socle {r n : ℕ} (hr : 4 ≤ r) (hA : CIT3Below n)
    (hB : TightBelowR r n) (h6 : ∀ m, TightLargeEdgeSR r m) (T : Subgroup A) [T.Normal]
    (hTs : IsSimpleGroup ↥T) (hTab : ∃ a b : ↥T, a * b ≠ b * a)
    (hTC : Subgroup.centralizer (T : Set A) = ⊥) {Y : Type} [Group Y] [Finite Y]
    (hY : Nat.card Y < n) (ι : Y →* A) (hι : Function.Injective ι) (hT : T ≤ ι.range)
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t) (hc : TightClsR r Y R S t)
    (hnO : ¬ TightInO2 t) : TwoSubgroupsFourGenerated ↥T := by
  obtain ⟨T₁, hT₁n, ⟨e⟩, hC₁, hF, hZ⟩ := exists_comap_socle T hTs hTab hTC ι hι hT
  have hE : TightEdgeless R := by
    rcases (hB Y hY R S t hd hc).resolve_right (not_goodThreeElement_of_four_le hr hd hc.1) with
      h2 | ⟨he, -⟩ | ⟨he, -⟩ | h4
    · exact absurd h2 hnO
    · exact he
    · exact he
    · exact absurd h4 (not_tightE4_R hd hc hnO hZ)
  by_contra hne
  haveI : IsSimpleGroup ↥T₁ := e.isSimpleGroup
  have hF' : ↥(genFittingFStar Y) ≃* ↥T₁ := MulEquiv.subgroupCongr hF
  haveI : IsSimpleGroup ↥(genFittingFStar Y) := hF'.isSimpleGroup
  have hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hTab
    exact ⟨hF'.symm (e.symm a), hF'.symm (e.symm b), fun h => hab (by
      simpa using congrArg (fun x => e (hF' x)) h)⟩
  have hne' : ¬ TwoSubgroupsFourGenerated ↥(genFittingFStar Y) := fun h =>
    hne (twoSubgroupsFourGenerated_of_mulEquiv e (twoSubgroupsFourGenerated_of_mulEquiv hF' h))
  exact h6 (Nat.card Y) (cit3Below_mono_R hY.le hA)
    (fun Z _ _ hZ => hB Z (lt_of_lt_of_le hZ hY.le)) Y rfl hnab R S t hd hc hnO hne' hE

end Thm6Step

end FourGen

section Classify

variable {r : ℕ} {A : Type} [Group A] [Finite A]

theorem edgelessFamily_of_embedded (hr : 4 ≤ r) (hList : SmallListR) (hO : NoDatumOtherR r)
    (T : Subgroup A) [T.Normal] (hTs : IsSimpleGroup ↥T) (hTab : ∃ a b : ↥T, a * b ≠ b * a)
    (hTC : Subgroup.centralizer (T : Set A) = ⊥) (h4 : TwoSubgroupsFourGenerated ↥T)
    {Y : Type} [Group Y] [Finite Y] (ι : Y →* A) (hι : Function.Injective ι) (hT : T ≤ ι.range)
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t)
    (hc : TightClsR r Y R S t) : EdgelessFamily ↥T := by
  haveI := hTs
  obtain ⟨T₁, hT₁n, ⟨e⟩, hC₁, -, -⟩ := exists_comap_socle T hTs hTab hTC ι hι hT
  have hvac : OtherFamily ↥T → False := fun hOF =>
    hO hr ↥T hTab hOF Y T₁ ⟨e⟩ hC₁ (twoSubgroupsFourGenerated_of_mulEquiv e.symm h4) R S t hd hc.1
  rcases hList ↥T hTab h4 with hfam | hex
  · unfold SmallFamily at hfam
    rcases hfam with h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact (hvac (by unfold OtherFamily; tauto)).elim
    · exact (hvac (by unfold OtherFamily; tauto)).elim
    · exact (hvac (by unfold OtherFamily; tauto)).elim
    · exact (hvac (by unfold OtherFamily; tauto)).elim
    · exact (hvac (by unfold OtherFamily; tauto)).elim
    · exact (hvac (by unfold OtherFamily; tauto)).elim
    · exact (hvac (by unfold OtherFamily; tauto)).elim
    · exact (hvac (by unfold OtherFamily; tauto)).elim
    · exact (hvac (by unfold OtherFamily; tauto)).elim
    · exact Or.inl h
    · obtain ⟨p, f, hp, hp2, hf, hm⟩ := h
      by_cases h3 : p ^ f = 3
      · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
        have hq : LieModel ↥T .PSL 3 3 1 := Or.inl ⟨by decide, hm⟩
        exact (hvac (by unfold OtherFamily; tauto)).elim
      · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h3, hm⟩)
    · obtain ⟨p, f, hp, hp2, hf, hm⟩ := h
      by_cases h3 : p ^ f = 3
      · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
        have hq : LieModel ↥T .PSU 3 3 1 := Or.inl ⟨by decide, hm⟩
        exact (hvac (by unfold OtherFamily; tauto)).elim
      · exact Or.inr (Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩)
    · exact (hvac (by unfold OtherFamily; tauto)).elim
  · exact (hvac (Or.inr hex)).elim

end Classify

end CFSG.CGT.PushingUpLit.SolKNA.R4
