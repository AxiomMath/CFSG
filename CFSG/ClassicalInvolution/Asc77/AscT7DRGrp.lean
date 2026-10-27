module

public import CFSG.ClassicalInvolution.Asc77.AscT7C2RGen

public section

namespace CFSG.ClassicalInvolution.Asc77.T7DR

open CFSG.ClassicalInvolution.Asc77.T7C2

section Dihedral

variable {Q : Type*} [Group Q]

theorem genLE_two_of_two_involutions {x y : Q} (hx : x * x = 1) (hy : y * y = 1)
    (hgen : Subgroup.closure ({x, y} : Set Q) = ⊤) (B : Subgroup Q) : GenLE B 2 := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  set C : Subgroup Q := Subgroup.zpowers (x * y) with hC
  have hxu : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    rw [hxinv, mul_inv_rev, hyinv, hxinv]
    calc x * (x * y) * x = (x * x) * (y * x) := by group
      _ = y * x := by rw [hx, one_mul]
  have hyu : y * (x * y) * y⁻¹ = (x * y)⁻¹ := by
    rw [hyinv, mul_inv_rev, hyinv, hxinv]
    calc y * (x * y) * y = y * x * (y * y) := by group
      _ = y * x := by rw [hy, mul_one]
  have hconj : ∀ g : Q, g⁻¹ = g → g * (x * y) * g⁻¹ = (x * y)⁻¹ →
      g ∈ Subgroup.normalizer (C : Set Q) := by
    intro g hginv hg
    have key : ∀ k : ℤ, g * (x * y) ^ k * g⁻¹ = (x * y) ^ (-k) := by
      intro k
      rw [← conj_zpow, hg, inv_zpow, zpow_neg]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [key]
      exact Subgroup.zpow_mem_zpowers _ _
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hh' : h = (x * y) ^ (-k) := by
        calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
          _ = g⁻¹ * (x * y) ^ k * g := by rw [← hk]
          _ = g * (x * y) ^ k * g⁻¹ := by rw [hginv]
          _ = (x * y) ^ (-k) := key k
      rw [hh']
      exact Subgroup.zpow_mem_zpowers _ _
  have hN : Subgroup.normalizer (C : Set Q) = ⊤ := by
    apply top_le_iff.mp
    rw [← hgen, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact hconj g hxinv hxu
    · exact hconj g hyinv hyu
  have hCn : C.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  have hker : (QuotientGroup.mk' C).ker = C := QuotientGroup.ker_mk' _
  have h1 : GenLE (B ⊓ (QuotientGroup.mk' C).ker) 1 :=
    GenLE.of_le_zpowers (a := x * y) (fun z hz => by rw [← hC, ← hker]; exact hz.2)
  have hxy1 : QuotientGroup.mk' C x * QuotientGroup.mk' C y = 1 := by
    rw [← map_mul, ← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_zpowers _
  have hcyc : IsCyclic (Q ⧸ C) := by
    refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨QuotientGroup.mk' C y, ?_⟩
    rw [eq_top_iff]
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ Subgroup.closure ({x, y} : Set Q) := hgen ▸ Subgroup.mem_top g
    have hle : Subgroup.closure ({x, y} : Set Q) ≤
        (Subgroup.zpowers (QuotientGroup.mk' C y)).comap (QuotientGroup.mk' C) := by
      rw [Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | rfl
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        have : QuotientGroup.mk' C z = (QuotientGroup.mk' C y)⁻¹ := eq_inv_of_mul_eq_one_left hxy1
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
    exact hle hg
  have h2 : GenLE (B.map (QuotientGroup.mk' C)) 1 := GenLE.of_isCyclic _
  exact GenLE.of_ker (QuotientGroup.mk' C) B h1 h2

end Dihedral

section Four

variable {S : Type*} [Group S]

theorem genLE_two_of_closure_pair' {W : Subgroup S} {a b : S} (ha : a ∈ W)
    (hb : b ∈ W) (hab : a * b = b * a) (hgen : Subgroup.closure ({a, b} : Set S) = W)
    {B : Subgroup S} (hB : B ≤ W) : GenLE B 2 := by
  have hgen' : Subgroup.closure ({(⟨a, ha⟩ : ↥W), ⟨b, hb⟩} : Set ↥W) = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hgen
  have h2 := genLE_two_of_abelian (a := (⟨a, ha⟩ : ↥W)) (b := ⟨b, hb⟩) (Subtype.ext hab) hgen'
    (B.subgroupOf W)
  exact GenLE.of_subgroupOf hB h2

theorem genLE_four_of_normal_two_gen {W : Subgroup S} [W.Normal] {c d : S} (hc : c ∈ W)
    (hd : d ∈ W) (hcd : c * d = d * c) (hW : Subgroup.closure ({c, d} : Set S) = W) {x y : S}
    (hx : x * x ∈ W) (hy : y * y ∈ W)
    (hS : Subgroup.closure ((W : Set S) ∪ {x, y}) = ⊤) (H : Subgroup S) : GenLE H 4 := by
  have hker : (QuotientGroup.mk' W).ker = W := QuotientGroup.ker_mk' _
  have h1 : GenLE (H ⊓ (QuotientGroup.mk' W).ker) 2 :=
    genLE_two_of_closure_pair' hc hd hcd hW (by rw [hker]; exact inf_le_right)
  have hx1 : QuotientGroup.mk' W x * QuotientGroup.mk' W x = 1 := by
    rw [← map_mul, ← MonoidHom.mem_ker, hker]
    exact hx
  have hy1 : QuotientGroup.mk' W y * QuotientGroup.mk' W y = 1 := by
    rw [← map_mul, ← MonoidHom.mem_ker, hker]
    exact hy
  have hgen : Subgroup.closure ({QuotientGroup.mk' W x, QuotientGroup.mk' W y} :
      Set (S ⧸ W)) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ Subgroup.closure ((W : Set S) ∪ {x, y}) := hS ▸ Subgroup.mem_top g
    have hle : Subgroup.closure ((W : Set S) ∪ {x, y}) ≤
        (Subgroup.closure ({QuotientGroup.mk' W x, QuotientGroup.mk' W y} :
          Set (S ⧸ W))).comap (QuotientGroup.mk' W) := by
      rw [Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      rcases hz with hz | hz
      · have : QuotientGroup.mk' W z = 1 := by
          rw [← MonoidHom.mem_ker, hker]
          exact hz
        rw [this]
        exact Subgroup.one_mem _
      · rcases hz with rfl | hz
        · exact Subgroup.subset_closure (by simp)
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact Subgroup.subset_closure (by simp)
    exact hle hg
  have h2 : GenLE (H.map (QuotientGroup.mk' W)) 2 :=
    genLE_two_of_two_involutions hx1 hy1 hgen _
  exact GenLE.of_ker (QuotientGroup.mk' W) H h1 h2

end Four

section Omega5

variable {S : Type*} [Group S] [Finite S]

theorem normal_of_conj_gens {W : Subgroup S} {T : Set S} (hT : Subgroup.closure T = ⊤)
    (h : ∀ g ∈ T, ∀ w ∈ W, g * w * g⁻¹ ∈ W) : W.Normal := by
  have hN : Subgroup.normalizer (W : Set S) = ⊤ := by
    apply top_le_iff.mp
    rw [← hT, Subgroup.closure_le]
    intro g hg
    exact Subgroup.mem_normalizer_fintype (fun n hn => h g hg n hn)
  exact Subgroup.normalizer_eq_top_iff.mp hN

omit [Finite S] in
theorem conj_mem_closure_pair {g c d : S} (hc : g * c * g⁻¹ ∈ Subgroup.closure ({c, d} : Set S))
    (hd : g * d * g⁻¹ ∈ Subgroup.closure ({c, d} : Set S)) :
    ∀ w ∈ Subgroup.closure ({c, d} : Set S), g * w * g⁻¹ ∈ Subgroup.closure ({c, d} : Set S) := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact hc
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hd
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem genLE_four_of_omega5 {a b t : S} (hS : Subgroup.closure ({a, b, t} : Set S) = ⊤)
    (hbab : b * a * b⁻¹ = a⁻¹) (hb2 : ∃ k : ℤ, b * b = a ^ k) (ht2 : t * t = 1)
    (h5 : a * (t * a * t⁻¹) = (t * a * t⁻¹) * a) (h6 : b * (t * a * t⁻¹) = (t * a * t⁻¹) * b)
    (H : Subgroup S) : GenLE H 4 := by
  set a' : S := t * a * t⁻¹ with ha'
  set W : Subgroup S := Subgroup.closure ({a, a'} : Set S) with hW
  have haW : a ∈ W := Subgroup.subset_closure (by simp)
  have ha'W : a' ∈ W := Subgroup.subset_closure (by simp)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hnormal : W.Normal := by
    refine normal_of_conj_gens hS ?_
    intro g hg
    rcases hg with rfl | rfl | rfl
    · refine conj_mem_closure_pair ?_ ?_
      · simpa using haW
      · have : g * a' * g⁻¹ = a' := by
          calc g * a' * g⁻¹ = (g * a') * g⁻¹ := rfl
            _ = (a' * g) * g⁻¹ := by rw [h5]
            _ = a' := by group
        rw [this]
        exact ha'W
    · refine conj_mem_closure_pair ?_ ?_
      · rw [hbab]
        exact Subgroup.inv_mem _ haW
      · have : g * a' * g⁻¹ = a' := by
          calc g * a' * g⁻¹ = (g * a') * g⁻¹ := rfl
            _ = (a' * g) * g⁻¹ := by rw [h6]
            _ = a' := by group
        rw [this]
        exact ha'W
    · refine conj_mem_closure_pair ?_ ?_
      · exact ha'W
      · have : g * a' * g⁻¹ = a := by
          rw [ha', htinv]
          calc g * (g * a * g) * g = (g * g) * a * (g * g) := by group
            _ = a := by rw [ht2]; group
        rw [this]
        exact haW
  have hb2W : b * b ∈ W := by
    obtain ⟨k, hk⟩ := hb2
    rw [hk]
    exact Subgroup.zpow_mem _ haW k
  have ht2W : t * t ∈ W := by
    rw [ht2]
    exact Subgroup.one_mem _
  refine genLE_four_of_normal_two_gen haW ha'W h5 hW.symm hb2W ht2W ?_ H
  rw [eq_top_iff, ← hS, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl | rfl
  · exact Subgroup.subset_closure (Or.inl haW)
  · exact Subgroup.subset_closure (Or.inr (by simp))
  · exact Subgroup.subset_closure (Or.inr (by simp))

end Omega5

end CFSG.ClassicalInvolution.Asc77.T7DR
