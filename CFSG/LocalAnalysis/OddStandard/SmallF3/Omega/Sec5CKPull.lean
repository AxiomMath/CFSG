module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDPull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OStep1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Tab5Cov

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem sec5c_pull_equiv {φ : ↥L →* omegaGroup hQ} (hinj : Function.Injective φ)
    {B : Subgroup (OGroup Q)} (hB : B ≤ (sec5cdPhi φ).range) :
    Nonempty (↥(sec5cdPull φ B) ≃* ↥B) := by
  have hΦ := sec5cdPhi_injective hinj
  have h1 : (B.comap (sec5cdPhi φ)).map (sec5cdPhi φ) = B := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hB]
  unfold sec5cdPull
  exact ⟨(Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).symm.trans
    ((Subgroup.equivMapOfInjective _ (sec5cdPhi φ) hΦ).trans (MulEquiv.subgroupCongr h1))⟩

theorem sec5c_pair_pull {φ : ↥L →* omegaGroup hQ} (hinj : Function.Injective φ)
    (hsurj : Function.Surjective φ) {z : G} (hz : z ∈ L)
    (D : Om6Par Q (sec5cdPhi φ ⟨z, hz⟩)) :
    Sec5Pair (sec5cdPull φ D.L) (sec5cdPull φ D.R) z := by
  have hΦ := sec5cdPhi_injective hinj
  have hr := sec5cdPhi_range hsurj
  have hLle : D.L ≤ (sec5cdPhi φ).range := by
    rw [hr]
    exact (le_sup_left.trans D.le_omega_cent).trans inf_le_left
  have hRle : D.R ≤ (sec5cdPhi φ).range := by
    rw [hr]
    exact (le_sup_right.trans D.le_omega_cent).trans inf_le_left
  have hP := D.sec5Pair
  refine ⟨?_, ⟨?_⟩, ⟨?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨l₁, rfl, h₁⟩ := mem_sec5cdPull_iff.mp ha
    obtain ⟨l₂, rfl, h₂⟩ := mem_sec5cdPull_iff.mp hb
    have h := hP.comm _ h₁ _ h₂
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (hΦ h)
  · exact (sec5c_pull_equiv hinj hLle).some.trans hP.iso₁.some
  · exact (sec5c_pull_equiv hinj hRle).some.trans hP.iso₂.some
  · exact mem_sec5cdPull_iff.mpr ⟨⟨z, hz⟩, rfl, hP.z_mem₁⟩
  · exact mem_sec5cdPull_iff.mpr ⟨⟨z, hz⟩, rfl, hP.z_mem₂⟩
  · have h : sec5cdPhi φ (⟨z, hz⟩ * ⟨z, hz⟩) = sec5cdPhi φ 1 := by
      rw [map_mul, map_one]
      exact hP.z_sq
    exact congrArg Subtype.val (hΦ h)
  · intro h1
    apply hP.z_ne
    have h2 : (⟨z, hz⟩ : ↥L) = 1 := Subtype.ext h1
    rw [h2, map_one]

theorem sec5c_oddCoreIn_bot [Finite G] (hL : IsOm6Z2 L) {t : G} (ht2 : orderOf t = 2)
    (hct : centerIn L = zpowers t) : oddCoreIn L = ⊥ := by
  rw [← le_bot_iff]
  intro x hx
  have hxt : x ∈ zpowers t := by
    rw [← hct]
    exact sec5o_oddCoreIn_le_centerIn hL hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxt
  have htt : t ^ (2 : ℤ) = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2] at h
    exact_mod_cast h
  have hx2 : x * x = 1 := by
    rw [← hk, ← zpow_add, show k + k = 2 * k by ring, zpow_mul, htt, one_zpow]
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hx2)
  have hodd : Odd (orderOf x) := odd_orderOf_of_mem_oddCoreIn hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

theorem sec5c_finite_ogroup : Finite (OGroup Q) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e₁ e₂ he => LinearEquiv.ext (congrFun he))
  exact Finite.of_injective (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) Subtype.val_injective

theorem sec5c_cover_iso [Finite G] (hS : Asc82SchurU43) (hL : IsOm6Z2 L) (hodd : oddCoreIn L = ⊥) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate) (φ : ↥L →* omegaGroup hQ),
      IsCoverMap L φ ∧ Function.Injective φ ∧ Function.Surjective φ := by
  obtain ⟨V, _, _, _, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  have hker : CFSG.oddCore ↥L = ⊥ := by
    have h : (CFSG.oddCore ↥L).map L.subtype = ⊥ := hodd
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.oddCore ↥L) L.subtype_injective).mp h
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφ.ker_eq, hker]
  exact ⟨V, _, _, _, Q, hQ, φ, hφ, hinj, hφ.surjective⟩

theorem sec5c_mem_of_isI4PlusIn {z : G} (hz : IsI4PlusIn L z) : z ∈ L := by
  obtain ⟨-, K, hzK, hKle, -, -⟩ := id hz
  exact (Subgroup.mem_inf.mp (hKle hzK)).1

theorem sec5c_z_model [Finite G] {φ : ↥L →* omegaGroup hQ} (hL : IsOm6Z2 L) (hφ : IsCoverMap L φ)
    {z : G} (hz : IsI4PlusIn L z) (hzL : z ∈ L) :
    sec5cdPhi φ ⟨z, hzL⟩ * sec5cdPhi φ ⟨z, hzL⟩ = 1 ∧
      invType (sec5cdPhi φ ⟨z, hzL⟩) = (4, 1) := by
  have hzz : z * z = 1 := by rw [← pow_two, ← hz.1]; exact pow_orderOf_eq_one z
  refine ⟨?_, t5_phi_pocket_invType hφ hL hz hzL⟩
  rw [← map_mul, show (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 from Subtype.ext hzz, map_one]

theorem sec5c_exists_pair [Finite G] (hS : Asc82SchurU43) (hL : IsOm6Z2 L)
    (hodd : oddCoreIn L = ⊥) {z : G} (hz : IsI4PlusIn L z) :
    ∃ K₁ K₂ : Subgroup G, Sec5Pair K₁ K₂ z ∧
      K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G)) := by
  obtain ⟨V, _, _, _, Q, hQ, φ, hφ, hinj, hsurj⟩ := sec5c_cover_iso hS hL hodd
  haveI : Finite (OGroup Q) := sec5c_finite_ogroup
  have hzL : z ∈ L := sec5c_mem_of_isI4PlusIn hz
  obtain ⟨hztt, hzt4⟩ := sec5c_z_model hL hφ hz hzL
  let D : Om6Par Q (sec5cdPhi φ ⟨z, hzL⟩) :=
    Om6Par.mk' hQ hφ.finrank_eq hφ.quadSign_eq hztt hzt4
  have hLle : D.L ≤ omegaGroup hQ := (le_sup_left.trans D.le_omega_cent).trans inf_le_left
  have hRle : D.R ≤ omegaGroup hQ := (le_sup_right.trans D.le_omega_cent).trans inf_le_left
  refine ⟨sec5cdPull φ D.L, sec5cdPull φ D.R, sec5c_pair_pull hinj hsurj hzL D, ?_⟩
  rw [← sec5cdPull_sup hsurj hLle hRle]
  exact sec5cdPull_sup_eq_twoRes hinj hsurj hzL D

end CFSG.OddStandard.SmallF3.Omega
