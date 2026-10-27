module

public import CFSG.LargeExtraspecial.AS35UB
public import CFSG.LargeExtraspecial.S3Basic
public import CFSG.LargeExtraspecial.Transport
public import CFSG.LieType.SteinbergBRUnitaryExtraspecialWidth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35U

open Subgroup Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem pow_three_eq_one_of_mem_center (hm : 3 ≤ m) {g : SUid frob m}
    (hg : g ∈ center (SUid frob m)) : g ^ 3 = 1 := by
  rw [center_SUid hm] at hg
  obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_scalars hg
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 : (fun _ => (1 : K) : Fin m → K) = 0 := by
      rw [← inv_smul_smul g (fun _ => (1 : K)), hc, zero_smul, smul_zero]
    exact one_ne_zero (congrFun h1 ⟨0, by omega⟩)
  have hc3 : c * c * c = 1 := by
    have h := frob_mul_self hc0
    rw [frob_apply] at h
    linear_combination h
  refine ext_smul _ fun x => ?_
  rw [show g ^ 3 = g * g * g by rw [pow_succ, pow_two], mul_smul, mul_smul, hc, hc, hc,
    smul_smul, smul_smul, hc3, one_smul, one_smul]

theorem eq_one_of_mem_center (hm : 3 ≤ m) {ζ : SUid frob m} (hζ : ζ ∈ center (SUid frob m))
    {k : ℕ} (hk : ζ ^ 2 ^ k = 1) : ζ = 1 := by
  have h1 : orderOf ζ ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk)
      (orderOf_dvd_of_pow_eq_one (pow_three_eq_one_of_mem_center hm hζ))
  have h2 : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left _ (by norm_num)
  rwa [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1

theorem exists_lift (hm : 3 ≤ m) (P : Subgroup (PG m)) (hP : IsPGroup 2 P) :
    ∃ Phat : Subgroup (SUid frob m), Phat.map (QuotientGroup.mk' (center (SUid frob m))) = P ∧
      ∀ x ∈ Phat, QuotientGroup.mk' (center (SUid frob m)) x = 1 → x = 1 := by
  set π := QuotientGroup.mk' (center (SUid frob m))
  set Qhat := P.comap π
  set f : Qhat →* P := (π.comp Qhat.subtype).codRestrict P fun x => x.2
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (center (SUid frob m)) (p : PG m)
    exact ⟨⟨g, show π g ∈ P from hg ▸ p.2⟩, Subtype.ext hg⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 Qhat) := inferInstance
  have hTtop : (T.mapSurjective hf : Subgroup P) = ⊤ := by
    have hP' : IsPGroup 2 (⊤ : Subgroup P) := fun x => by
      obtain ⟨k, hk⟩ := hP (x : P)
      exact ⟨k, Subtype.ext hk⟩
    exact ((T.mapSurjective hf).is_maximal' hP' le_top).symm
  refine ⟨T.map Qhat.subtype, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨_, ⟨t, -, rfl⟩, rfl⟩
      exact t.2
    · intro p hp
      have hmem : (⟨p, hp⟩ : P) ∈ (T.mapSurjective hf : Subgroup P) := hTtop ▸ mem_top _
      rw [Sylow.coe_mapSurjective] at hmem
      obtain ⟨t, ht, htp⟩ := hmem
      exact ⟨t, ⟨t, ht, rfl⟩, congrArg Subtype.val htp⟩
  · rintro _ ⟨t, ht, rfl⟩ h1
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨t, ht⟩
    have hk' : (t : SUid frob m) ^ 2 ^ k = 1 := by
      have := congrArg (fun w : T => ((w : Qhat) : SUid frob m)) hk
      simpa using this
    exact eq_one_of_mem_center hm ((QuotientGroup.eq_one_iff _).mp h1) hk'

theorem width_add_two_le (hm : 4 ≤ m) (T : Setting (PG m)) (hn : 1 ≤ T.width)
    {e : Fin m → K} (he0 : e ≠ 0) (he : herm frob e e = 0) (hTz : T.z = tq e) :
    T.width + 2 ≤ m := by
  have hm3 : 3 ≤ m := by omega
  have he' : hermB m e e = 0 := he
  have hd : 3 ≤ Module.finrank K (Fin m → K) := by rw [Module.finrank_fin_fun]; omega
  set π := QuotientGroup.mk' (center (SUid frob m)) with hπ
  have hπtv : π (tvU e) = T.z := by rw [hTz]; rfl
  have hQ2 : IsPGroup 2 T.QG := fun g =>
    ⟨2, Subtype.ext (by simpa using T.pow_four_eq_one g.2)⟩
  obtain ⟨Phat, hmap, hinj⟩ := exists_lift hm3 T.QG hQ2
  have hPhat2 : ∀ x ∈ Phat, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hQ2 ⟨π x, hmap ▸ mem_map_of_mem π hx⟩
    refine ⟨k, hinj _ (pow_mem hx _) ?_⟩
    rw [map_pow]
    exact congrArg Subtype.val hk
  have htv : tvU e ∈ Phat := by
    have hz : π (tvU e) ∈ Phat.map π := by rw [hmap, hπtv]; exact T.z_mem_QG
    obtain ⟨p, hp, hpe⟩ := hz
    have hζZ : (tvU e)⁻¹ * p ∈ center (SUid frob m) := by
      rw [← QuotientGroup.eq_one_iff]
      change π ((tvU e)⁻¹ * p) = 1
      rw [map_mul, map_inv, hpe, inv_mul_cancel]
    obtain ⟨k, hk⟩ := hPhat2 p hp
    have hcomm : Commute (tvU e) ((tvU e)⁻¹ * p) := Subgroup.mem_center_iff.mp hζZ (tvU e)
    have htv2 : tvU e ^ 2 ^ (k + 1) = 1 := by
      rw [Nat.pow_succ, pow_mul', pow_two, tvU_mul_self he, one_pow]
    have hζk : ((tvU e)⁻¹ * p) ^ 2 ^ (k + 1) = 1 := by
      have h1 : (tvU e * ((tvU e)⁻¹ * p)) ^ 2 ^ (k + 1) = 1 := by
        rw [mul_inv_cancel_left, Nat.pow_succ, pow_mul, hk, one_pow]
      rwa [hcomm.mul_pow, htv2, one_mul] at h1
    have hp' : p = tvU e * ((tvU e)⁻¹ * p) := by rw [mul_inv_cancel_left]
    rw [eq_one_of_mem_center hm3 hζZ hζk, mul_one] at hp'
    exact hp' ▸ hp
  set r := π.comp Phat.subtype
  have hr : Function.Injective r := (injective_iff_map_eq_one r).mpr fun x hx =>
    Subtype.ext (hinj x x.2 hx)
  have hrange : r.range = T.QG := by rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  let E : T.Q ≃* Phat.map (ι m) :=
    (T.Q.equivMapOfInjective T.M.subtype T.M.subtype_injective).trans
      (((MonoidHom.ofInjective hr).trans (MulEquiv.subgroupCongr hrange)).symm.trans
        (Phat.equivMapOfInjective (ι m) ι_injective))
  have hP : IsExtraspecialPGroup 2 (Phat.map (ι m)) :=
    isExtraspecialPGroup_of_mulEquiv E T.extraspecial
  have hPcard : Nat.card (Phat.map (ι m)) = 2 ^ (1 + 2 * T.width) := by
    rw [← Nat.card_congr E.toEquiv, T.card_Q_eq]
  have hT : hermTransvectionGL (hermB m) he' 1 ∈ Phat.map (ι m) := ⟨tvU e, htv, ι_tvU he'⟩
  have hTc : ∀ y ∈ Phat.map (ι m),
      y * hermTransvectionGL (hermB m) he' 1 = hermTransvectionGL (hermB m) he' 1 * y := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← ι_tvU he', ← map_mul, ← map_mul]
    have h1 : q * tvU e * q⁻¹ * (tvU e)⁻¹ ∈ Phat :=
      mul_mem (mul_mem (mul_mem hq htv) (inv_mem hq)) (inv_mem htv)
    have hqM : π q * T.z = T.z * π q :=
      mem_centralizer_singleton_iff.mp (T.QG_le_M (hmap ▸ mem_map_of_mem π hq))
    have h2 : π (q * tvU e * q⁻¹ * (tvU e)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπtv, hqM]
      group
    have h3 := hinj _ h1 h2
    congr 1
    calc q * tvU e = q * tvU e * q⁻¹ * (tvU e)⁻¹ * (tvU e * q) := by group
      _ = tvU e * q := by rw [h3, one_mul]
  obtain ⟨f, hff, hef⟩ :=
    (CFSG.LocalAnalysis.GorensteinLyons.four_element_unitary_axis_flag_kernel_and_regular_orbit
      hF hermB_isSymm hermB_separatingLeft hd he0 he').1
  have hne : (⟨_, hT⟩ : Phat.map (ι m)) ≠ 1 := by
    intro h1
    have h := congrArg (fun y : Phat.map (ι m) =>
      ((y : LinearMap.GeneralLinearGroup K (Fin m → K)) : (Fin m → K) →ₗ[K] (Fin m → K)) f) h1
    simp only [coe_hermTransvectionGL, hermTransvection_apply, one_mul, hef, one_smul,
      OneMemClass.coe_one, Units.val_one, Module.End.one_apply, add_eq_left] at h
    exact he0 h
  have hsq' : hermTransvectionGL (hermB m) he' 1 ^ 2 = 1 := by
    rw [← ι_tvU he', ← map_pow, pow_two, tvU_mul_self he, map_one]
  have hsq : (⟨_, hT⟩ : Phat.map (ι m)) ^ 2 = 1 := Subtype.ext (by simpa using hsq')
  have : Finite (Phat.map (ι m)) := Nat.finite_of_card_ne_zero (by rw [hPcard]; positivity)
  have hZ : center (Phat.map (ι m)) = zpowers ⟨_, hT⟩ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [zpowers_le]
      exact mem_center_iff.mpr fun y => Subtype.ext (hTc y y.2)
    · rw [hP.2.2.2, Nat.card_zpowers, orderOf_eq_prime hsq hne]
  obtain ⟨-, -, -, -, hle, -⟩ :=
    CFSG.LieType.unitary_extraspecial_central_transvection_width_and_equality
    hF hermB_isSymm hermB_separatingLeft hd (Phat.map (ι m))
    (fun y hy => by
      obtain ⟨q, -, rfl⟩ := hy
      exact (mem_sesqSpecialUnitaryGroup.mp (ι_mem q)).1)
    hn hP hPcard he0 he' hT hZ hff hef
  rw [Module.finrank_fin_fun] at hle
  omega

end CFSG.LargeExtraspecial.AS35U
