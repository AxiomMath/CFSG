module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.AlphaCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two

variable {X : Type} [Group X] [Finite X]

theorem alphaVanishes_of_local_inner (hZ : Subgroup.center X = ⊥)
    (hOut : ∀ α : MulAut X, ∃ g : X, α = MulAut.conj g) {D : Subgroup X}
    (H1 : ∀ b ∈ D, b ≠ 1 → ∀ x ∈ inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({b} : Set X)) ⊓ qRes b, ∀ y ∈ qRes b, x * y = y * x)
    (H2 : ∀ b ∈ D, b ≠ 1 → D ≤ Subgroup.zpowers b ⊔ qRes b) {b₁ : X} (hb₁ : b₁ ∈ D)
    (hb₁1 : b₁ ≠ 1)
    (H3 : ∀ g : X, (∀ q ∈ qRes b₁, g * q * g⁻¹ = q) → ¬ 3 ∣ orderOf g → g = 1) :
    AlphaVanishes X D := by
  intro Y hY
  have hinj := conj_injective_of_center hZ
  set B := (D.map (MulAut.conj : X →* MulAut X)).subgroupOf Y with hB
  have hJ : thetaJ 3 B = ⊥ := thetaJ_eq_bot_of_local hZ H1 H2 hY
  have hT : thetaT 3 B = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    have hbY : MulAut.conj b₁ ∈ Y := hY ⟨b₁, rfl⟩
    set b : Y := ⟨MulAut.conj b₁, hbY⟩ with hbdef
    have hbB : b ∈ B := Subgroup.mem_subgroupOf.mpr ⟨b₁, hb₁, rfl⟩
    have hb1 : b ≠ 1 := by
      intro h1
      apply hb₁1
      apply hinj
      rw [map_one]
      exact congrArg Subtype.val h1
    have htb : t ∈
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y)) := by
      have h1 := Subgroup.mem_iInf.mp ht b
      have h2 := Subgroup.mem_iInf.mp h1 hbB
      exact Subgroup.mem_iInf.mp h2 hb1
    have hfix := fixes_qRes hZ hY (b := b) (d := b₁) rfl (H1 b₁ hb₁ hb₁1) htb
    obtain ⟨g, hg⟩ := hOut (t : MulAut X)
    have hgq : ∀ q ∈ qRes b₁, g * q * g⁻¹ = q := by
      intro q hq
      have h1 := hfix q hq
      rw [hg] at h1
      simpa [MulAut.conj_apply] using h1
    have h3 : ¬ 3 ∣ orderOf g := by
      intro h3
      set U := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y)) with hU
      have h1 : orderOf (⟨t, htb⟩ : U) ∣ Nat.card U := orderOf_dvd_natCard _
      have e1 : orderOf g = orderOf (t : MulAut X) := by
        rw [hg]
        exact (orderOf_injective (MulAut.conj : X →* MulAut X) hinj g).symm
      have e2 : orderOf (t : MulAut X) = orderOf (⟨t, htb⟩ : U) := by
        rw [← Subgroup.orderOf_coe (⟨t, htb⟩ : U), Subgroup.orderOf_coe]
      have h4 : orderOf g ∣ Nat.card U := by
        rw [e1, e2]
        exact h1
      exact not_three_dvd_card_inSubgroup_theta (Subgroup.centralizer ({b} : Set Y))
        (h3.trans h4)
    have hg1 := H3 g hgq h3
    apply Subtype.ext
    rw [hg, hg1]
    simp
  rw [thetaAlpha, hJ, hT, sup_bot_eq]

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
