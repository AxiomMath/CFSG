module

public import CFSG.GH74.Generic.S3.L3Cover

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

theorem exists_Iv_of_isClassicalSL2 {S G : Type*} [Group S] [Group G] {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (α : S →* G) (hker : α.ker ≤ Subgroup.center S)
    (hZ : ∀ k ∈ Subgroup.center S, k ^ 3 = 1) {y : G} (hy : y ∈ α.range) (hy2 : y * y = 1)
    (hy1 : y ≠ 1)
    (hcl : ∀ z : S, z * z = 1 → z ≠ 1 →
      ∃ L : Subgroup S, CFSG.ClassicalInvolution.IsClassicalSL2 F L z) :
    ∃ Iv : Subgroup G, Iv ≤ α.range ∧ y ∈ Iv ∧ Nonempty (SL(2, F) ≃* Iv) ∧
      (∀ g ∈ α.range, g * y = y * g → ∀ i ∈ Iv, g * i * g⁻¹ ∈ Iv) := by
  obtain ⟨z, hz2, hzy⟩ := CFSG.GH74.GLS.LU.exists_involution_lift α hker hZ hy hy2
  have hz1 : z ≠ 1 := fun h => hy1 (by rw [← hzy, h, map_one])
  obtain ⟨L, hL⟩ := hcl z hz2 hz1
  obtain ⟨e⟩ := hL.nonempty_mulEquiv
  have hinj : Function.Injective (α.domRestrict L) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hxL⟩ hx
    have hxk : x ∈ α.ker := hx
    have hxc : x ∈ Subgroup.center S := hker hxk
    have hcL : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_center_iff.mp hxc l)
    rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp
        ((CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e _).mp hcL) with h1 | h1
    · exact (map_eq_one_iff e e.injective).mp h1
    · have hord : orderOf (⟨x, hxL⟩ : L) = 2 :=
        (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e _).mpr
          (by rw [← h1]; simp)
      rw [Subgroup.orderOf_mk] at hord
      have hxz : x = z := hL.eq_of_orderOf_eq_two hodd hxL hord
      exfalso
      apply hy1
      rw [← hzy, ← hxz]
      exact hxk
  refine ⟨L.map α, Subgroup.map_le_range α L, ⟨z, hL.mem, hzy⟩, ?_, ?_⟩
  · exact ⟨e.symm.trans ((MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range L α)))⟩
  · intro g hg hgy i hi
    obtain ⟨g', rfl⟩ := hg
    obtain ⟨l, hl, rfl⟩ := hi
    have hc : g' * z = z * g' :=
      CFSG.GH74.GLS.LU.commute_of_involution_lift α hker hZ hz2 (g := g') (by rw [hzy]; exact hgy)
    have hgc : g' ∈ Subgroup.centralizer ({z} : Set S) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hc
    have hN := Subgroup.mem_normalizer_iff.mp (hL.centralizer_le_normalizer hgc) l
    exact ⟨g' * l * g'⁻¹, hN.mp hl, by simp⟩

section Linear

theorem exists_Iv_lin {G : Type*} [Group G] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {α : SL(3, F) →* G}
    (hker : α.ker ≤ Subgroup.center SL(3, F)) {y : G} (hy : y ∈ α.range) (hy2 : y * y = 1)
    (hy1 : y ≠ 1) :
    ∃ Iv : Subgroup G, Iv ≤ α.range ∧ y ∈ Iv ∧ Nonempty (SL(2, F) ≃* Iv) ∧
      (∀ g ∈ α.range, g * y = y * g → ∀ i ∈ Iv, g * i * g⁻¹ ∈ Iv) := by
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  exact exists_Iv_of_isClassicalSL2 hodd α hker CFSG.GH74.GLS.LU.center_pow_three hy hy2 hy1
    (fun _ hz2 hz1 =>
      ⟨_, (CFSG.GH74.GLS.LU.isLongRootSL2_of_involution h2 hz2 hz1).isClassicalSL2 h2⟩)

end Linear

section Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_Iv_uni (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {G : Type*} [Group G]
    {α : CFSG.ClassicalInvolution.Phan.Su K p f 3 →* G}
    (hker : α.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su K p f 3)) {y : G}
    (hy : y ∈ α.range) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ Iv : Subgroup G, Iv ≤ α.range ∧ y ∈ Iv ∧
      Nonempty (SL(2, ↥(CFSG.LieType.Steinberg.fixedSubfield K p f)) ≃* Iv) ∧
      (∀ g ∈ α.range, g * y = y * g → ∀ i ∈ Iv, g * i * g⁻¹ ∈ Iv) :=
  exists_Iv_of_isClassicalSL2 (CFSG.ClassicalInvolution.Models.odd_natCard_fixedSubfield hK hp) α
    hker (CFSG.GH74.GLS.LU.center_pow_three_su hK) hy hy2 hy1
    (fun _ hz2 hz1 => ⟨_,
      (CFSG.GH74.GLS.LU.isLongRootSU2_of_involution hK hp hz2 hz1).isClassicalSL2 hK hp⟩)

end Unitary

theorem exists_Iv (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    {Iw : Subgroup G} (hq : IsQuasisimple ↥Iw) (hodd : Odd (Nat.card ↥(center ↥Iw)))
    (hmodel : LieModel (↥Iw ⧸ center ↥Iw) t 3 p f) {y : G} (hy : y ∈ Iw) (hy2 : y * y = 1)
    (hy1 : y ≠ 1) :
    ∃ Iv : Subgroup G, Iv ≤ Iw ∧ y ∈ Iv ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (SL(2, F) ≃* Iv)) ∧
      (∀ g ∈ Iw, g * y = y * g → ∀ i ∈ Iv, g * i * g⁻¹ ∈ Iv) := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h5
    omega
  have hcov := b_L3_cover_of_griess hGA G p f hp hp2 h5 Iw hq hodd
  rcases ht with rfl | rfl
  · obtain ⟨α, hker, hrange⟩ := hcov.1 hmodel (GaloisField p f) inferInstance inferInstance
      (GaloisField.card p f hf)
    have hoddF : Odd (Nat.card (GaloisField p f)) := by
      rw [GaloisField.card p f hf]
      exact (hp.odd_of_ne_two hp2).pow
    obtain ⟨Iv, hle, hyIv, ⟨e⟩, hnorm⟩ :=
      exists_Iv_lin hoddF hker (by rw [hrange]; exact hy) hy2 hy1
    rw [hrange] at hle hnorm
    exact ⟨Iv, hle, hyIv, ⟨GaloisField p f, inferInstance, inferInstance,
      GaloisField.card p f hf, ⟨e⟩⟩, hnorm⟩
  · have hF₂ : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
      rw [GaloisField.card p (2 * f) (by omega), mul_comm, pow_mul]
    obtain ⟨α₀, hker₀, hrange₀⟩ := hcov.2 hmodel (GaloisField p (2 * f)) inferInstance
      inferInstance hF₂
    let eSU : CFSG.ClassicalInvolution.Phan.Su (GaloisField p (2 * f)) p f 3 ≃*
        ↥(StatedSU 3 (p ^ f) (GaloisField p (2 * f))) :=
      MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF₂ 3)
    obtain ⟨α, hker, hrange⟩ := exists_hom_of_mulEquiv eSU.symm α₀ hker₀
    have hrangeI : α.range = Iw := hrange.trans hrange₀
    obtain ⟨Iv, hle, hyIv, ⟨e⟩, hnorm⟩ :=
      exists_Iv_uni hF₂ hp2 hker (by rw [hrangeI]; exact hy) hy2 hy1
    rw [hrangeI] at hle hnorm
    exact ⟨Iv, hle, hyIv, ⟨_, inferInstance, inferInstance,
      CFSG.LieType.Steinberg.card_fixedSubfield hF₂, ⟨e⟩⟩, hnorm⟩

end CFSG.GH74.Generic.S3
