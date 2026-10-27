module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888M1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888M2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888M3a

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

private lemma s888M3_alpha_conj_fixes (hS : PlaneSetup z K α) {t : H}
    (h : ∀ q ∈ Sec5B517Q8 hS.quad, t * q * t⁻¹ * q⁻¹ ∈ zpowers z) :
    ∀ v ∈ planeV hS.quad α, α t * v * (α t)⁻¹ = v := by
  intro v hv
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hv
  have hker : t * q * t⁻¹ * q⁻¹ ∈ α.ker := by
    rw [hS.ker]
    exact h q hq
  have halpha : α (t * q * t⁻¹ * q⁻¹) = 1 := MonoidHom.mem_ker.mp hker
  have h3 : α (t * q * t⁻¹) * (α q)⁻¹ = 1 := by
    rw [← map_inv, ← map_mul]
    exact halpha
  have heq : α (t * q * t⁻¹) = α q := mul_inv_eq_one.mp h3
  calc α t * α q * (α t)⁻¹
      = α (t * q * t⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = α q := heq

private lemma s888M3_zpowers_two {z t : H} (hzsq : z * z = 1) (ht : t ∈ zpowers z) :
    t = 1 ∨ t = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
    exact hzsq
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

private theorem s888M3_actsElemAb (hS : PlaneSetup z K α) {U : Subgroup H}
    (hU : U ≤ normalizer (Sec5B517Q8 hS.quad : Set H))
    (hsq : ∀ u ∈ U, ∀ q ∈ Sec5B517Q8 hS.quad,
      u * u * q * (u * u)⁻¹ * q⁻¹ ∈ zpowers z)
    (hcm : ∀ u ∈ U, ∀ w ∈ U, ∀ q ∈ Sec5B517Q8 hS.quad,
      u * w * u⁻¹ * w⁻¹ * q * (u * w * u⁻¹ * w⁻¹)⁻¹ * q⁻¹ ∈ zpowers z) :
    ActsElemAb (planeV hS.quad α) (U.map α) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    exact (mem_normalizer_planeV_iff hS).mpr (hU hu)
  · intro y hy v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    simpa only [map_mul] using s888M3_alpha_conj_fixes hS (hsq u hu) v hv
  · intro y hy y' hy' v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy'
    set cc : H := u * w * u⁻¹ * w⁻¹ with hcc
    have hfixcc : ∀ v ∈ planeV hS.quad α, α cc * v * (α cc)⁻¹ = v := by
      apply s888M3_alpha_conj_fixes hS
      intro q hq
      rw [hcc]
      exact hcm u hu w hw q hq
    have huw : u * w = cc * (w * u) := by
      rw [hcc]; group
    have hV : α (w * u) * v * (α (w * u))⁻¹ ∈ planeV hS.quad α := by
      have hwuN : w * u ∈ normalizer (Sec5B517Q8 hS.quad : Set H) :=
        Subgroup.mul_mem _ (hU hw) (hU hu)
      exact (Subgroup.mem_set_normalizer_iff.mp
        ((mem_normalizer_planeV_iff hS).mpr hwuN) v).mp hv
    calc α u * α w * v * (α u * α w)⁻¹
        = α (u * w) * v * (α (u * w))⁻¹ := by rw [map_mul]
      _ = α (cc * (w * u)) * v * (α (cc * (w * u)))⁻¹ := by rw [huw]
      _ = (α cc * α (w * u)) * v * (α cc * α (w * u))⁻¹ := by rw [map_mul]
      _ = α cc * (α (w * u) * v * (α (w * u))⁻¹) * (α cc)⁻¹ := by group
      _ = α (w * u) * v * (α (w * u))⁻¹ := hfixcc _ hV
      _ = α w * α u * v * (α w * α u)⁻¹ := by rw [map_mul]

theorem exists_delta_of_relIndex [Finite H] (hS : PlaneSetup z K α)
    (hperm : ∀ x ∈ normalizer (Sec5B517Q8 hS.quad : Set H), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (K i) x = K j)
    (hpar : ∀ w ∈ normalizer (Sec5B517Q8 hS.quad : Set H),
      (∀ i, CFSG.conjugate (K i) w = K i) →
      (∀ q ∈ Sec5B517Q8 hS.quad, w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers z) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ Sec5B517Q8 hS.quad ⊓ K i,
          w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * z}))
    {U : Subgroup H} (hU : U ≤ normalizer (Sec5B517Q8 hS.quad : Set H))
    (hab : ∀ a ∈ U, ∀ b ∈ U,
      (∀ q ∈ Sec5B517Q8 hS.quad,
        a * b * a⁻¹ * b⁻¹ * q * (a * b * a⁻¹ * b⁻¹)⁻¹ * q⁻¹ ∈ zpowers z) ∧
      (∀ q ∈ Sec5B517Q8 hS.quad, a * a * q * (a * a)⁻¹ * q⁻¹ ∈ zpowers z))
    (hcard : 16 ≤ ((centralizer (planeV hS.quad α : Set X)).comap α).relIndex U) :
    ∃ (e : H) (i j : Fin 4), i ≠ j ∧ e ∈ Sec5B517Q8 hS.quad ∧ e * e = 1 ∧ e ≠ 1 ∧ e ≠ z ∧
      e ∈ K i ⊔ K j ∧ ∀ u ∈ U, ∃ r ∈ Sec5B517Q8 hS.quad, (u * r) * e * (u * r)⁻¹ = e := by
  classical
  haveI : Finite X := Finite.of_surjective α hS.surj
  have hSys : PlaneSys (planeV hS.quad α) (planeW hS.quad α) := planeSys_of_setup hS hperm
  have hparX : PlaneParity (planeV hS.quad α) (planeW hS.quad α) :=
    planeParity_of_setup hS hperm hpar
  have hE : ActsElemAb (planeV hS.quad α) (U.map α) :=
    s888M3_actsElemAb hS hU (fun u hu => (hab u hu u hu).2)
      (fun u hu w hw => (hab u hu w hw).1)
  have hcardX : 16 ≤ (centralizer (planeV hS.quad α : Set X)).relIndex (U.map α) := by
    rw [← Subgroup.relIndex_comap
      (H := centralizer (planeV hS.quad α : Set X)) α U]
    exact hcard
  obtain ⟨c, d, hcd, hpres⟩ := exists_pair_of_relIndex hSys hparX hE hcardX
  obtain ⟨a, ha, b, hb, ha1, hb1, hfix⟩ := exists_fixed_support_two hSys hcd hE hpres
  obtain ⟨qc, hqc, hqca⟩ := Subgroup.mem_map.mp ha
  obtain ⟨hqcQ, hqcK⟩ := Subgroup.mem_inf.mp hqc
  obtain ⟨qd, hqd, hqdb⟩ := Subgroup.mem_map.mp hb
  obtain ⟨hqdQ, hqdK⟩ := Subgroup.mem_inf.mp hqd
  have hqc4 : qc ^ 4 = 1 := Sec5B517Q8.pow_four hS.quad hqcQ
  have hqd4 : qd ^ 4 = 1 := Sec5B517Q8.pow_four hS.quad hqdQ
  have hz_alpha : α z = 1 :=
    MonoidHom.mem_ker.mp (by rw [hS.ker]; exact Subgroup.mem_zpowers z)
  have hqc1 : qc ≠ 1 := by
    intro h
    apply ha1
    rw [← hqca, h, map_one]
  have hqc_z : qc ≠ z := by
    intro h
    apply ha1
    rw [← hqca, h, hz_alpha]
  have hqd1 : qd ≠ 1 := by
    intro h
    apply hb1
    rw [← hqdb, h, map_one]
  have hqd_z : qd ≠ z := by
    intro h
    apply hb1
    rw [← hqdb, h, hz_alpha]
  have hqcsq : qc * qc = z := by
    rcases Sec5B517Quad.sq_of_pow4 hS.quad hqcK hqc4 with h | h
    · rcases Sec5B517Quad.eq_of_sq hS.quad hqcK h with h1 | h1
      · exact absurd h1 hqc1
      · exact absurd h1 hqc_z
    · exact h
  have hqdsq : qd * qd = z := by
    rcases Sec5B517Quad.sq_of_pow4 hS.quad hqdK hqd4 with h | h
    · rcases Sec5B517Quad.eq_of_sq hS.quad hqdK h with h1 | h1
      · exact absurd h1 hqd1
      · exact absurd h1 hqd_z
    · exact h
  set e : H := qc * qd with he
  have heQ : e ∈ Sec5B517Q8 hS.quad := by
    rw [he]
    exact (Sec5B517Q8 hS.quad).mul_mem hqcQ hqdQ
  have heK : e ∈ K c ⊔ K d := by
    rw [he]
    exact Subgroup.mul_mem_sup hqcK hqdK
  have he_alpha : α e = a * b := by
    rw [he, map_mul, hqca, hqdb]
  have hze : z * e = e * z := by
    rw [he, ← mul_assoc, hS.quad.z_comm hqcK, mul_assoc, hS.quad.z_comm hqdK,
      ← mul_assoc]
  have hee : e * e = 1 := by
    have hcomm : qc * qd = qd * qc := hS.quad.comm c d hcd qc hqcK qd hqdK
    have h1 : (qc * qd) * (qc * qd) = qc * (qd * qc) * qd := by group
    have h2 : qc * (qd * qc) * qd = qc * (qc * qd) * qd := by rw [hcomm]
    have h3 : qc * (qc * qd) * qd = (qc * qc) * (qd * qd) := by group
    rw [he, h1, h2, h3, hqcsq, hqdsq, hS.quad.z_sq]
  have he1 : e ≠ 1 := by
    intro h
    have hab1 : a * b = 1 := by rw [← he_alpha, h, map_one]
    have ha_bd : a ∈ planeW hS.quad α d := by
      rw [eq_inv_of_mul_eq_one_left hab1]
      exact (planeW hS.quad α d).inv_mem hb
    have haz : a ∈ planeW hS.quad α c ⊓ planeW hS.quad α d := ⟨ha, ha_bd⟩
    rw [hSys.inf_eq_bot hcd] at haz
    exact ha1 (Subgroup.mem_bot.mp haz)
  have hez : e ≠ z := by
    intro h
    have hab1 : a * b = 1 := by rw [← he_alpha, h, hz_alpha]
    have ha_bd : a ∈ planeW hS.quad α d := by
      rw [eq_inv_of_mul_eq_one_left hab1]
      exact (planeW hS.quad α d).inv_mem hb
    have haz : a ∈ planeW hS.quad α c ⊓ planeW hS.quad α d := ⟨ha, ha_bd⟩
    rw [hSys.inf_eq_bot hcd] at haz
    exact ha1 (Subgroup.mem_bot.mp haz)
  refine ⟨e, c, d, hcd, heQ, hee, he1, hez, heK, ?_⟩
  intro u hu
  have hfixu : α u * (a * b) * (α u)⁻¹ = a * b :=
    hfix (α u) (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
  have hae : α (u * e * u⁻¹) = α e := by
    have h1 : α (u * e * u⁻¹) = α u * α e * (α u)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [h1, he_alpha]
    exact hfixu
  have hae' : α u * α e * (α u)⁻¹ = α e := by
    simpa only [map_mul, map_inv] using hae
  have hconjmem : (u * e * u⁻¹) * e⁻¹ ∈ zpowers z := by
    rw [← hS.ker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hae', mul_inv_cancel]
  rcases s888M3_zpowers_two hS.quad.z_sq hconjmem with hcase | hcase
  · exact ⟨1, (Sec5B517Q8 hS.quad).one_mem, by simpa using mul_inv_eq_one.mp hcase⟩
  · have hue : u * e * u⁻¹ = e * z := by
      have h1 : u * e * u⁻¹ = z * e := by
        calc u * e * u⁻¹ = ((u * e * u⁻¹) * e⁻¹) * e := by group
          _ = z * e := by rw [hcase]
      exact h1.trans hze
    obtain ⟨r, hrK, hr4, hrqc⟩ :=
      Sec5B517Quad.exists_inverting hS.quad hqcK hqc4 hqc1 hqc_z
    have hrQ : r ∈ Sec5B517Q8 hS.quad := Sec5B517Q8.mem_of_mem hS.quad hrK hr4
    have hrqd : r * qd * r⁻¹ = qd := by
      rw [hS.quad.comm c d hcd r hrK qd hqdK]
      group
    have hre : r * e * r⁻¹ = e * z := by
      rw [he]
      rw [show r * (qc * qd) * r⁻¹ = (r * qc * r⁻¹) * (r * qd * r⁻¹) by group]
      rw [hrqc, hrqd]
      rw [show qc * z * qd = (qc * qd) * z by
        rw [mul_assoc, hS.quad.z_comm hqdK, ← mul_assoc]]
    have huez : u * z * u⁻¹ = z := by
      have hk : u * z * u⁻¹ ∈ α.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [hz_alpha, mul_one, mul_inv_cancel]
      have hk' : u * z * u⁻¹ ∈ zpowers z := by
        rwa [← hS.ker]
      rcases s888M3_zpowers_two hS.quad.z_sq hk' with h1 | h1
      · exfalso
        have hz1 : z = 1 := by
          calc z = u⁻¹ * (u * z * u⁻¹) * u := by group
            _ = u⁻¹ * 1 * u := by rw [h1]
            _ = 1 := by group
        exact hS.quad.z_ne hz1
      · exact h1
    refine ⟨r, hrQ, ?_⟩
    calc (u * r) * e * (u * r)⁻¹
        = u * (r * e * r⁻¹) * u⁻¹ := by group
      _ = u * (e * z) * u⁻¹ := by rw [hre]
      _ = (u * e * u⁻¹) * (u * z * u⁻¹) := by group
      _ = (e * z) * z := by rw [hue, huez]
      _ = e := by rw [mul_assoc, hS.quad.z_sq, mul_one]

end CFSG.OddStandard.SmallF3.Omega
