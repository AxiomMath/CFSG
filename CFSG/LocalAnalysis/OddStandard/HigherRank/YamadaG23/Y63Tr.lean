module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Reg

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable [Group Y63TG] {G : Type} [Group G] {P : Subgroup G}

@[expose] def y63Img (ψ : ↥P ≃* Y63TG) (H : Subgroup G) : Subgroup Y63TG :=
  (H.subgroupOf P).comap ψ.symm.toMonoidHom

theorem mem_y63Img (ψ : ↥P ≃* Y63TG) (H : Subgroup G) (x : Y63TG) :
    x ∈ y63Img ψ H ↔ ((ψ.symm x : ↥P) : G) ∈ H :=
  Iff.rfl

theorem y63Img_card (ψ : ↥P ≃* Y63TG) {H : Subgroup G} (hHP : H ≤ P) :
    Nat.card ↥(y63Img ψ H) = Nat.card ↥H := by
  refine Nat.card_congr
    { toFun := fun x => ⟨((ψ.symm x.1 : ↥P) : G), (mem_y63Img ψ H x.1).mp x.2⟩
      invFun := fun h => ⟨ψ ⟨h.1, hHP h.2⟩, by
        rw [mem_y63Img, ψ.symm_apply_apply]
        exact h.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun h => Subtype.ext (by simp) }

theorem y63Img_normal (ψ : ↥P ≃* Y63TG) {H : Subgroup G} (hHP : H ≤ P)
    (hPN : P ≤ normalizer (H : Set G)) : (y63Img ψ H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_y63Img] at hn ⊢
  have h := (Subgroup.mem_normalizer_iff.mp (hPN (ψ.symm g).2) _).mp hn
  simpa using h

theorem y63_decomp {S M : Subgroup G} (hSP : S ≤ P) (hMP : M ≤ P)
    (hPN : P ≤ normalizer (M : Set G)) (hSM : S ⊔ M = P) :
    ∀ x ∈ P, ∃ s ∈ S, ∃ m ∈ M, x = s * m := by
  intro x hx
  haveI : (M.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMP).mpr hPN
  have hsup : S.subgroupOf P ⊔ M.subgroupOf P = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hSP hMP, hSM, Subgroup.subgroupOf_self]
  have hx' : (⟨x, hx⟩ : ↥P) ∈ S.subgroupOf P ⊔ M.subgroupOf P := by
    rw [hsup]
    trivial
  obtain ⟨s', hs', m', hm', h⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  exact ⟨s', hs', m', hm', (congrArg Subtype.val h).symm⟩

theorem y63Img_sup (ψ : ↥P ≃* Y63TG) {S M : Subgroup G} (hSP : S ≤ P) (hMP : M ≤ P)
    (hPN : P ≤ normalizer (M : Set G)) (hSM : S ⊔ M = P) :
    y63Img ψ S ⊔ y63Img ψ M = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨s, hs, m, hm, h⟩ := y63_decomp hSP hMP hPN hSM (ψ.symm y : G) (ψ.symm y).2
  have hy : y = ψ ⟨s, hSP hs⟩ * ψ ⟨m, hMP hm⟩ := by
    rw [← map_mul]
    apply ψ.symm.injective
    rw [ψ.symm_apply_apply]
    exact Subtype.ext h
  rw [hy]
  refine Subgroup.mul_mem_sup ?_ ?_
  · rw [mem_y63Img, ψ.symm_apply_apply]
    exact hs
  · rw [mem_y63Img, ψ.symm_apply_apply]
    exact hm

theorem y63Img_exp (ψ : ↥P ≃* Y63TG) {M : Subgroup G} (h4 : ∀ m ∈ M, m ^ 4 = 1) :
    ∀ x ∈ y63Img ψ M, x ^ 4 = 1 := by
  intro x hx
  have h : (ψ.symm x) ^ 4 = 1 := Subtype.ext (by simpa using h4 _ ((mem_y63Img ψ M x).mp hx))
  calc x ^ 4 = ψ ((ψ.symm x) ^ 4) := by rw [map_pow, ψ.apply_symm_apply]
    _ = 1 := by rw [h, map_one]

theorem y63Img_comm (ψ : ↥P ≃* Y63TG) {M : Subgroup G}
    (hc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) :
    ∀ x ∈ y63Img ψ M, ∀ y ∈ y63Img ψ M, x * y = y * x := by
  intro x hx y hy
  have h : ψ.symm x * ψ.symm y = ψ.symm y * ψ.symm x :=
    Subtype.ext (hc _ ((mem_y63Img ψ M x).mp hx) _ ((mem_y63Img ψ M y).mp hy))
  apply ψ.symm.injective
  rw [map_mul, map_mul]
  exact h

theorem y63Img_omega (ψ : ↥P ≃* Y63TG) {S M : Subgroup G} (hΩ : omega1 M ≤ S)
    {x : Y63TG} (hx : x ∈ y63Img ψ M) (h2 : x * x = 1) : x ∈ y63Img ψ S := by
  rw [mem_y63Img]
  apply hΩ
  apply Subgroup.subset_closure
  refine ⟨(mem_y63Img ψ M x).mp hx, ?_⟩
  have h : ψ.symm x * ψ.symm x = 1 := by rw [← map_mul, h2, map_one]
  simpa [pow_two] using congrArg Subtype.val h

end CFSG.OddStandard.HigherRank.YamadaG23
