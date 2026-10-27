module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRGrp

public section

namespace CFSG.ClassicalInvolution.Asc77.T7Q

open CFSG.ClassicalInvolution.Asc77.T7C2 CFSG.ClassicalInvolution.Asc77.T7DR

section Meta

variable {Q : Type*} [Group Q]

theorem mem_normalizer_zpowers {a g : Q} (h1 : g * a * g⁻¹ ∈ Subgroup.zpowers a)
    (h2 : g⁻¹ * a * g ∈ Subgroup.zpowers a) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have : g * a ^ k * g⁻¹ = (g * a * g⁻¹) ^ k := by rw [conj_zpow]
    rw [this]
    exact Subgroup.zpow_mem _ h1 k
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    have e : h = (g⁻¹ * a * g) ^ k := by
      have : (g⁻¹ * a * g) ^ k = g⁻¹ * a ^ k * g := by
        have := conj_zpow (a := g⁻¹) (b := a) (i := k)
        simpa using this
      rw [this, hk]
      group
    rw [e]
    exact Subgroup.zpow_mem _ h2 k

theorem genLE_two_of_gen_normalizes {a x : Q} (hgen : Subgroup.closure ({a, x} : Set Q) = ⊤)
    (hxa : x * a * x⁻¹ ∈ Subgroup.zpowers a) (hxa' : x⁻¹ * a * x ∈ Subgroup.zpowers a)
    (B : Subgroup Q) : GenLE B 2 := by
  set A : Subgroup Q := Subgroup.zpowers a with hA
  have hN : Subgroup.normalizer (A : Set Q) = ⊤ := by
    apply top_le_iff.mp
    rw [← hgen, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · refine mem_normalizer_zpowers ?_ ?_ <;>
        · have : g * g * g⁻¹ = g := by group
          have h2 : g⁻¹ * g * g = g := by group
          first | rw [this] | rw [h2]
          exact Subgroup.mem_zpowers g
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact mem_normalizer_zpowers hxa hxa'
  have hAn : A.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  have hker : (QuotientGroup.mk' A).ker = A := QuotientGroup.ker_mk' _
  have h1 : GenLE (B ⊓ (QuotientGroup.mk' A).ker) 1 :=
    GenLE.of_le_zpowers (a := a) (fun y hy => by rw [← hA, ← hker]; exact hy.2)
  have hcyc : IsCyclic (Q ⧸ A) := by
    refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨QuotientGroup.mk' A x, ?_⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hg : g ∈ Subgroup.closure ({a, x} : Set Q) := hgen ▸ Subgroup.mem_top g
    have hle : Subgroup.closure ({a, x} : Set Q) ≤
        (Subgroup.zpowers (QuotientGroup.mk' A x)).comap (QuotientGroup.mk' A) := by
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with hw | hw
      · have h0 : (QuotientGroup.mk' A) w = 1 := by
          rw [← MonoidHom.mem_ker, hker, hw]
          exact Subgroup.mem_zpowers a
        exact Subgroup.mem_comap.mpr (by rw [h0]; exact Subgroup.one_mem _)
      · rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
    exact hle hg
  have h2 : GenLE (B.map (QuotientGroup.mk' A)) 1 := GenLE.of_isCyclic _
  exact GenLE.of_ker (QuotientGroup.mk' A) B h1 h2

end Meta

section Sub

variable {S : Type*} [Group S]

theorem genLE_two_of_sub_normalizes {W : Subgroup S} {a x : S} (ha : a ∈ W) (hx : x ∈ W)
    (hgen : Subgroup.closure ({a, x} : Set S) = W)
    (hxa : x * a * x⁻¹ ∈ Subgroup.zpowers a) (hxa' : x⁻¹ * a * x ∈ Subgroup.zpowers a)
    {B : Subgroup S} (hB : B ≤ W) : GenLE B 2 := by
  have hgen' : Subgroup.closure ({(⟨a, ha⟩ : ↥W), ⟨x, hx⟩} : Set ↥W) = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hgen
  have hz : ∀ {c : S} (hc : c ∈ W) (hc' : c ∈ Subgroup.zpowers a),
      (⟨c, hc⟩ : ↥W) ∈ Subgroup.zpowers (⟨a, ha⟩ : ↥W) := by
    intro c hc hc'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
    exact ⟨k, Subtype.ext (by simp)⟩
  have h1 : (⟨x, hx⟩ : ↥W) * ⟨a, ha⟩ * (⟨x, hx⟩ : ↥W)⁻¹ ∈ Subgroup.zpowers (⟨a, ha⟩ : ↥W) := by
    have := hz (W.mul_mem (W.mul_mem hx ha) (W.inv_mem hx)) hxa
    exact this
  have h2 : (⟨x, hx⟩ : ↥W)⁻¹ * ⟨a, ha⟩ * (⟨x, hx⟩ : ↥W) ∈ Subgroup.zpowers (⟨a, ha⟩ : ↥W) := by
    have := hz (W.mul_mem (W.mul_mem (W.inv_mem hx) ha) hx) hxa'
    exact this
  have key := genLE_two_of_gen_normalizes hgen' h1 h2 (B.subgroupOf W)
  exact GenLE.of_subgroupOf hB key

end Sub

section Ext

variable {S : Type*} [Group S]

theorem genLE_four_of_ext {W : Subgroup S} [W.Normal] (hW : ∀ B : Subgroup S, B ≤ W → GenLE B 2)
    {y z : S} (hy : y * y ∈ W) (hz : z * z ∈ W)
    (hS : Subgroup.closure ((W : Set S) ∪ {y, z}) = ⊤) (H : Subgroup S) : GenLE H 4 := by
  have hker : (QuotientGroup.mk' W).ker = W := QuotientGroup.ker_mk' _
  have h1 : GenLE (H ⊓ (QuotientGroup.mk' W).ker) 2 :=
    hW _ (by rw [hker]; exact inf_le_right)
  have hy1 : QuotientGroup.mk' W y * QuotientGroup.mk' W y = 1 := by
    rw [← map_mul, ← MonoidHom.mem_ker, hker]
    exact hy
  have hz1 : QuotientGroup.mk' W z * QuotientGroup.mk' W z = 1 := by
    rw [← map_mul, ← MonoidHom.mem_ker, hker]
    exact hz
  have hgen : Subgroup.closure ({QuotientGroup.mk' W y, QuotientGroup.mk' W z} :
      Set (S ⧸ W)) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ Subgroup.closure ((W : Set S) ∪ {y, z}) := hS ▸ Subgroup.mem_top g
    have hle : Subgroup.closure ((W : Set S) ∪ {y, z}) ≤
        (Subgroup.closure ({QuotientGroup.mk' W y, QuotientGroup.mk' W z} :
          Set (S ⧸ W))).comap (QuotientGroup.mk' W) := by
      rw [Subgroup.closure_le]
      intro w hw
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      rcases hw with hw | hw
      · have : QuotientGroup.mk' W w = 1 := by
          rw [← MonoidHom.mem_ker, hker]
          exact hw
        rw [this]
        exact Subgroup.one_mem _
      · rcases hw with rfl | hw
        · exact Subgroup.subset_closure (by simp)
        · rw [Set.mem_singleton_iff] at hw
          rw [hw]
          exact Subgroup.subset_closure (by simp)
    exact hle hg
  have h2 : GenLE (H.map (QuotientGroup.mk' W)) 2 :=
    genLE_two_of_two_involutions hy1 hz1 hgen _
  exact GenLE.of_ker (QuotientGroup.mk' W) H h1 h2

end Ext

end CFSG.ClassicalInvolution.Asc77.T7Q
