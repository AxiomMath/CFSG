module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.QM

open QuaternionGroup DihedralGroup

variable {N : ℕ} [NeZero N]

@[expose] def proj : QuaternionGroup N →* DihedralGroup N where
  toFun x := match x with
    | QuaternionGroup.a i => DihedralGroup.r (ZMod.castHom (dvd_mul_left N 2) (ZMod N) i)
    | QuaternionGroup.xa i => DihedralGroup.sr (ZMod.castHom (dvd_mul_left N 2) (ZMod N) i)
  map_one' := by
    show DihedralGroup.r (ZMod.castHom (dvd_mul_left N 2) (ZMod N) 0) = 1
    rw [map_zero]
    rfl
  map_mul' := by
    rintro (i | i) (j | j)
    · simp [map_add]
    · simp [map_sub]
    · simp [map_add]
    · simp [map_add, map_sub]

omit [NeZero N] in
theorem proj_a (i : ZMod (2 * N)) :
    proj (QuaternionGroup.a i) = DihedralGroup.r (ZMod.castHom (dvd_mul_left N 2) (ZMod N) i) :=
  rfl

omit [NeZero N] in
theorem proj_xa (i : ZMod (2 * N)) :
    proj (QuaternionGroup.xa i) = DihedralGroup.sr (ZMod.castHom (dvd_mul_left N 2) (ZMod N) i) :=
  rfl

theorem proj_surjective : Function.Surjective (proj (N := N)) := by
  rintro (j | j)
  · refine ⟨QuaternionGroup.a ((j.val : ℕ) : ZMod (2 * N)), ?_⟩
    rw [proj_a, map_natCast, ZMod.natCast_zmod_val]
  · refine ⟨QuaternionGroup.xa ((j.val : ℕ) : ZMod (2 * N)), ?_⟩
    rw [proj_xa, map_natCast, ZMod.natCast_zmod_val]

theorem card_ker : Nat.card (proj (N := N)).ker = 2 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (proj (N := N)).ker
  have hQ : Nat.card (QuaternionGroup N) = 4 * N := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective proj proj_surjective).toEquiv,
    DihedralGroup.nat_card, hQ] at h1
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h2 : 2 * N * 2 = 2 * N * Nat.card (proj (N := N)).ker := by rw [← h1]; ring
  exact (Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * N) h2).symm

theorem involution_mem_ker {z : QuaternionGroup N} (hz : orderOf z = 2) : proj z = 1 := by
  rcases z with i | i
  · have h2 : (QuaternionGroup.a i) * (QuaternionGroup.a i) = 1 := by
      have := pow_orderOf_eq_one (QuaternionGroup.a i)
      rwa [hz, pow_two] at this
    rw [QuaternionGroup.a_mul_a, QuaternionGroup.one_def] at h2
    have h3 : i + i = 0 := QuaternionGroup.a.inj h2
    have h4 : ((2 * N : ℕ) : ℕ) ∣ 2 * i.val := by
      have : ((2 * i.val : ℕ) : ZMod (2 * N)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
        rw [← h3]; push_cast; ring
      exact (ZMod.natCast_eq_zero_iff _ _).1 this
    have h5 : N ∣ i.val := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
    rw [proj_a, DihedralGroup.one_def]
    congr 1
    have : ((i.val : ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h5
    rw [← this, ← map_natCast (ZMod.castHom (dvd_mul_left N 2) (ZMod N)), ZMod.natCast_zmod_val]
  · exfalso
    rw [QuaternionGroup.orderOf_xa] at hz
    omega

theorem quot_equiv {G : Type*} [Group G] {P : Subgroup G} (e : ↥P ≃* QuaternionGroup N) {z : G}
    (hz : z ∈ P) (hz2 : orderOf z = 2) :
    ∃ _ : ((Subgroup.zpowers z).subgroupOf P).Normal,
      Nonempty ((↥P ⧸ (Subgroup.zpowers z).subgroupOf P) ≃* DihedralGroup N) := by
  have hzo : orderOf (⟨z, hz⟩ : ↥P) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz2
  have hz'o : orderOf (e ⟨z, hz⟩) = 2 := by simp [hzo]
  have hzker : (e ⟨z, hz⟩) ∈ (proj (N := N)).ker := involution_mem_ker hz'o
  have hker : Subgroup.zpowers (e ⟨z, hz⟩) = (proj (N := N)).ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.2 hzker
    · rw [card_ker, Nat.card_zpowers, hz'o]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥P →* DihedralGroup N, ∀ x, ψ x = proj (e x) :=
    ⟨proj.comp e.toMonoidHom, fun x => rfl⟩
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨q, hq⟩ := proj_surjective y
    exact ⟨e.symm q, by rw [hψ, MulEquiv.apply_symm_apply, hq]⟩
  have hψk : ψ.ker = (Subgroup.zpowers z).subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, hψ, Subgroup.mem_subgroupOf, ← MonoidHom.mem_ker, ← hker,
      Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      rw [← map_zpow] at hk
      have h2 := e.injective hk
      exact ⟨k, by simpa using congrArg Subtype.val h2⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← map_zpow]
      congr 1
      exact Subtype.ext (by simpa using hk)
  have hnorm : ((Subgroup.zpowers z).subgroupOf P).Normal := hψk ▸ MonoidHom.normal_ker ψ
  exact ⟨hnorm, ⟨(QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.QM
