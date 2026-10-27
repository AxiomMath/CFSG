module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPCls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open CFSG.GH74.GLS.Th2.P412

variable {G : Type} [Group G] [Finite G] {X : Type} [Group X] {t z : G} {T : Subgroup G}
  {π : ↥(centralizer ({z} : Set G)) →* X}

private theorem sec5op5_exists_mul_of_mem_sup_of_commute {G : Type} [Group G]
    {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact hle hx

theorem sec5op_z_mem_W (hyp : Sec5OPHyp t z T π) : z ∈ sec5op_W hyp := by
  refine (sec5op_mem_W_iff hyp).mpr ⟨hyp.TY hyp.zT, ?_⟩
  have hzker : (⟨z, hyp.TH hyp.zT⟩ : ↥(centralizer ({z} : Set G))) ∈ π.ker := by
    rw [hyp.ker, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers z
  rw [MonoidHom.mem_ker] at hzker
  change sec5g_pi (sec5op_Tb z T π)
    ⟨π ⟨z, sec5op_Y_le hyp.tH (hyp.TY hyp.zT)⟩, sec5op_pi_mem hyp (hyp.TY hyp.zT)⟩ = 1
  have h1 : (⟨π ⟨z, sec5op_Y_le hyp.tH (hyp.TY hyp.zT)⟩,
      sec5op_pi_mem hyp (hyp.TY hyp.zT)⟩ :
      ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))) = 1 := by
    apply Subtype.ext
    change π ⟨z, sec5op_Y_le hyp.tH (hyp.TY hyp.zT)⟩ = 1
    rw [show (⟨z, sec5op_Y_le hyp.tH (hyp.TY hyp.zT)⟩ : ↥(centralizer ({z} : Set G))) =
        ⟨z, hyp.TH hyp.zT⟩ from Subtype.ext rfl]
    exact hzker
  rw [h1, map_one]

theorem sec5op_W_le_Y (hyp : Sec5OPHyp t z T π) : sec5op_W hyp ≤ sec5op_Y t z := by
  intro x hx
  rw [sec5op_W, Subgroup.mem_map] at hx
  obtain ⟨y, _, hyx⟩ := hx
  exact hyx ▸ y.2

theorem sec5op_W_normal (hyp : Sec5OPHyp t z T π) {h : G} (hh : h ∈ centralizer ({z} : Set G))
    {w : G} (hw : w ∈ sec5op_W hyp) : h * w * h⁻¹ ∈ sec5op_W hyp := by
  obtain ⟨hwY, hcls⟩ := (sec5op_mem_W_iff hyp).mp hw
  refine (sec5op_mem_W_iff hyp).mpr
    ⟨sec5op_Y_normal t z h hh w hwY, ?_⟩
  have hrc := sec5op_rho_cls hyp hh ⟨w, hwY⟩
  rw [hcls, map_one] at hrc
  exact hrc.symm

theorem sec5op_oddCore_Y_normal (hyp : Sec5OPHyp t z T π) {h : G}
    (hh : h ∈ centralizer ({z} : Set G)) {x : G} (hx : x ∈ oddCoreIn (sec5op_Y t z)) :
    h * x * h⁻¹ ∈ oddCoreIn (sec5op_Y t z) := by
  refine conj_mem_oddCoreIn ?_ hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact sec5op_Y_normal t z h hh y hy
  · intro hy
    have hconj := sec5op_Y_normal t z h⁻¹ (Subgroup.inv_mem _ hh) (h * y * h⁻¹) hy
    have heq : h⁻¹ * (h * y * h⁻¹) * (h⁻¹)⁻¹ = y := by group
    rwa [heq] at hconj

@[expose] noncomputable def sec5op_N (hyp : Sec5OPHyp t z T π) : Subgroup G :=
  oddCoreIn (sec5op_Y t z) ⊓ sec5op_W hyp

theorem sec5op_N_le_oddCore (hyp : Sec5OPHyp t z T π) :
    sec5op_N hyp ≤ oddCoreIn (sec5op_Y t z) :=
  inf_le_left

theorem sec5op_N_odd (hyp : Sec5OPHyp t z T π) : Odd (Nat.card (sec5op_N hyp)) := by
  refine (odd_card_oddCoreIn (sec5op_Y t z)).of_dvd_nat
    (Subgroup.card_dvd_of_le (sec5op_N_le_oddCore hyp))

theorem sec5op_N_le_H (hyp : Sec5OPHyp t z T π) :
    sec5op_N hyp ≤ centralizer ({z} : Set G) :=
  (inf_le_right.trans (sec5op_W_le_Y hyp)).trans (sec5op_Y_le hyp.tH)

theorem sec5op_N_normal (hyp : Sec5OPHyp t z T π) {h : G} (hh : h ∈ centralizer ({z} : Set G))
    {n : G} (hn : n ∈ sec5op_N hyp) : h * n * h⁻¹ ∈ sec5op_N hyp := by
  rw [sec5op_N, Subgroup.mem_inf] at hn ⊢
  exact ⟨sec5op_oddCore_Y_normal hyp hh hn.1, sec5op_W_normal hyp hh hn.2⟩

private theorem sec5op5_not_dvd_relIndex (hyp : Sec5OPHyp t z T π) :
    ¬ 2 ∣ (Subgroup.zpowers z).relIndex (sec5op_W hyp) := by
  classical
  haveI : Finite X := Finite.of_surjective π hyp.surj
  let M : Subgroup X := normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X)
  let φ : ↥(sec5op_W hyp) →* X :=
    { toFun := fun w => π ⟨w.1, sec5op_Y_le hyp.tH (sec5op_W_le_Y hyp w.2)⟩
      map_one' := by
        have h : (⟨(1 : ↥(sec5op_W hyp)).1,
            sec5op_Y_le hyp.tH (sec5op_W_le_Y hyp (1 : ↥(sec5op_W hyp)).2)⟩ :
            ↥(centralizer ({z} : Set G))) = 1 := Subtype.ext rfl
        rw [h, map_one]
      map_mul' := by
        intro w₁ w₂
        have h : (⟨(w₁ * w₂).1,
            sec5op_Y_le hyp.tH (sec5op_W_le_Y hyp (w₁ * w₂).2)⟩ :
            ↥(centralizer ({z} : Set G))) =
            ⟨w₁.1, sec5op_Y_le hyp.tH (sec5op_W_le_Y hyp w₁.2)⟩ *
              ⟨w₂.1, sec5op_Y_le hyp.tH (sec5op_W_le_Y hyp w₂.2)⟩ := Subtype.ext rfl
        rw [h, map_mul] }
  have hker : φ.ker = (Subgroup.zpowers z).subgroupOf (sec5op_W hyp) := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hw
      have hmem : (⟨w.1, sec5op_Y_le hyp.tH (sec5op_W_le_Y hyp w.2)⟩ :
          ↥(centralizer ({z} : Set G))) ∈ π.ker := by
        rw [MonoidHom.mem_ker]; exact hw
      rwa [hyp.ker, Subgroup.mem_subgroupOf] at hmem
    · intro hw
      have hmem : (⟨w.1, sec5op_Y_le hyp.tH (sec5op_W_le_Y hyp w.2)⟩ :
          ↥(centralizer ({z} : Set G))) ∈ π.ker := by
        rw [hyp.ker, Subgroup.mem_subgroupOf]; exact hw
      rwa [MonoidHom.mem_ker] at hmem
  have hrel : (Subgroup.zpowers z).relIndex (sec5op_W hyp) = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hrange : φ.range ≤ (goldschmidtOddCore ↥M).map M.subtype := by
    rintro x ⟨w, rfl⟩
    obtain ⟨hwY, hcls⟩ := (sec5op_mem_W_iff hyp).mp w.2
    have hcls' : sec5g_pi (sec5op_Tb z T π)
        ⟨π ⟨w.1, sec5op_Y_le hyp.tH hwY⟩, sec5op_pi_mem hyp hwY⟩ = 1 := hcls
    have hmem : (⟨π ⟨w.1, sec5op_Y_le hyp.tH hwY⟩, sec5op_pi_mem hyp hwY⟩ :
        ↥M) ∈ goldschmidtOddCore ↥M := (QuotientGroup.eq_one_iff _).mp hcls'
    have hphi : φ w = π ⟨w.1, sec5op_Y_le hyp.tH hwY⟩ := by
      apply congrArg π
      exact Subtype.ext rfl
    have hphiMem : φ w ∈ M := hphi.symm ▸ sec5op_pi_mem hyp hwY
    refine Subgroup.mem_map.mpr ⟨⟨φ w, hphiMem⟩, ?_, rfl⟩
    rw [show (⟨φ w, hphiMem⟩ : ↥M) =
        ⟨π ⟨w.1, sec5op_Y_le hyp.tH hwY⟩, sec5op_pi_mem hyp hwY⟩ from Subtype.ext hphi]
    exact hmem
  have hcard : Nat.card ((goldschmidtOddCore ↥M).map M.subtype) =
      Nat.card (goldschmidtOddCore ↥M) :=
    Subgroup.card_map_of_injective (K := goldschmidtOddCore ↥M) M.subtype_injective
  have hodd : Odd (Nat.card φ.range) :=
    (odd_card_goldschmidtOddCore (M := ↥M)).of_dvd_nat
      (hcard ▸ Subgroup.card_dvd_of_le hrange)
  rw [hrel]
  obtain ⟨k, hk⟩ := hodd
  intro h2
  obtain ⟨m, hm⟩ := h2
  omega

private theorem sec5op5_isSylow2 (hyp : Sec5OPHyp t z T π) :
    IsSylow2Of (Subgroup.zpowers z) (sec5op_W hyp) := by
  refine ⟨Subgroup.zpowers_le.mpr (sec5op_z_mem_W hyp), ?_, sec5op5_not_dvd_relIndex hyp⟩
  have hcard : Nat.card (Subgroup.zpowers z) = 2 ^ 1 := by
    rw [Nat.card_zpowers, hyp.hz, pow_one]
  exact IsPGroup.of_card hcard

private theorem sec5op5_comm (hyp : Sec5OPHyp t z T π) :
    ∀ k ∈ sec5op_W hyp, ∀ a ∈ Subgroup.zpowers z, a * k = k * a := by
  intro k hk a ha
  have hkH : k ∈ centralizer ({z} : Set G) :=
    sec5op_Y_le hyp.tH (sec5op_W_le_Y hyp hk)
  have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp hkH
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact ((show Commute k z from hkz).zpow_right j).symm

theorem sec5op_W_decomp (hyp : Sec5OPHyp t z T π) {w : G} (hw : w ∈ sec5op_W hyp) :
    ∃ (e : ℕ) (n : G), n ∈ sec5op_N hyp ∧ w = z ^ e * n := by
  classical
  have hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ oddCoreIn (sec5op_W hyp), a * b = b * a :=
    fun a ha b hb => sec5op5_comm hyp b ((oddCoreIn_normal _).1 hb) a ha
  have hsup : Subgroup.zpowers z ⊔ oddCoreIn (sec5op_W hyp) = sec5op_W hyp :=
    sup_oddCoreIn_of_central_sylow (sec5op5_isSylow2 hyp) (sec5op5_comm hyp)
  have hw' : w ∈ Subgroup.zpowers z ⊔ oddCoreIn (sec5op_W hyp) := by
    rw [hsup]
    exact hw
  obtain ⟨a, haZ, b, hbO, haw⟩ :=
    sec5op5_exists_mul_of_mem_sup_of_commute hcomm hw'
  rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at haZ
  obtain ⟨e, _, hae⟩ := haZ
  have hnorm : ((sec5op_W hyp).subgroupOf (sec5op_Y t z)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (sec5op_W_le_Y hyp)]
    intro h k hh hk
    exact sec5op_W_normal hyp (sec5op_Y_le hyp.tH hk) hh
  refine ⟨e, b, ?_, ?_⟩
  · rw [sec5op_N, Subgroup.mem_inf]
    exact ⟨oddCoreIn_le_of_normal (sec5op_W_le_Y hyp) hnorm hbO,
      (oddCoreIn_normal _).1 hbO⟩
  · rw [hae]
    exact haw

end CFSG.OddStandard.SmallF3.Omega
