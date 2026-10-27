module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open CFSG.GH74.GLS.Th2.P412

variable {G : Type} [Group G] {X : Type} [Group X]

theorem sec5op_pi_mem {t z : G} {T : Subgroup G} {π : ↥(centralizer ({z} : Set G)) →* X}
    (hyp : Sec5OPHyp t z T π) {y : G} (hy : y ∈ sec5op_Y t z) :
    π ⟨y, sec5op_Y_le hyp.tH hy⟩ ∈ normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X) := by
  have hYN : sec5op_Y t z ≤
      ((normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X)).comap π).map
        (centralizer ({z} : Set G)).subtype := by
    rw [sec5op_Y]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y' ⟨h, hh, rfl⟩
    have hhH : h * t * h⁻¹ ∈ centralizer ({z} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hh hyp.tH) (Subgroup.inv_mem _ hh)
    refine Subgroup.mem_map.mpr ⟨⟨h * t * h⁻¹, hhH⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have htTb : π ⟨t, hyp.tH⟩ ∈ sec5op_Tb z T π := by
      rw [sec5op_Tb]
      exact Subgroup.mem_map.mpr ⟨⟨t, hyp.tH⟩, hyp.tT, rfl⟩
    have htM : π ⟨t, hyp.tH⟩ ∈
        normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X) :=
      Subgroup.subset_normalClosure htTb
    have hconj : π ⟨h * t * h⁻¹, hhH⟩ =
        π ⟨h, hh⟩ * π ⟨t, hyp.tH⟩ * (π ⟨h, hh⟩)⁻¹ := by
      rw [show (⟨h * t * h⁻¹, hhH⟩ : ↥(centralizer ({z} : Set G))) =
          ⟨h, hh⟩ * ⟨t, hyp.tH⟩ * ⟨h, hh⟩⁻¹ from Subtype.ext rfl]
      rw [map_mul π, map_mul π, map_inv π]
    have hnorm : (normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X)).Normal :=
      Subgroup.normalClosure_normal
    rw [hconj]
    exact hnorm.conj_mem (π ⟨t, hyp.tH⟩) htM (π ⟨h, hh⟩)
  obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp (hYN hy)
  rw [Subgroup.mem_comap] at hn
  have hπ : π ⟨y, sec5op_Y_le hyp.tH hy⟩ = π n := congrArg π (Subtype.ext hny.symm)
  rw [hπ]
  exact hn

@[expose] noncomputable def sec5op_cls {t z : G} {T : Subgroup G}
    {π : ↥(centralizer ({z} : Set G)) →* X} (hyp : Sec5OPHyp t z T π) :
    ↥(sec5op_Y t z) →* Sec5GBar (sec5op_Tb z T π) where
  toFun y := sec5g_pi (sec5op_Tb z T π) ⟨π ⟨y.1, sec5op_Y_le hyp.tH y.2⟩, sec5op_pi_mem hyp y.2⟩
  map_one' := by
    show sec5g_pi (sec5op_Tb z T π)
      ⟨π ⟨(1 : ↥(sec5op_Y t z)).1, sec5op_Y_le hyp.tH (1 : ↥(sec5op_Y t z)).2⟩,
        sec5op_pi_mem hyp (1 : ↥(sec5op_Y t z)).2⟩ = 1
    have h1 : (⟨π ⟨(1 : ↥(sec5op_Y t z)).1,
        sec5op_Y_le hyp.tH (1 : ↥(sec5op_Y t z)).2⟩,
        sec5op_pi_mem hyp (1 : ↥(sec5op_Y t z)).2⟩ :
        ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))) = 1 := by
      apply Subtype.ext
      exact (congrArg π (Subtype.ext rfl)).trans (map_one π)
    rw [h1, map_one (sec5g_pi (sec5op_Tb z T π))]
  map_mul' y₁ y₂ := by
    show sec5g_pi (sec5op_Tb z T π)
      ⟨π ⟨(y₁ * y₂).1, sec5op_Y_le hyp.tH (y₁ * y₂).2⟩,
        sec5op_pi_mem hyp (y₁ * y₂).2⟩ =
      sec5g_pi (sec5op_Tb z T π)
        ⟨π ⟨y₁.1, sec5op_Y_le hyp.tH y₁.2⟩, sec5op_pi_mem hyp y₁.2⟩ *
      sec5g_pi (sec5op_Tb z T π)
        ⟨π ⟨y₂.1, sec5op_Y_le hyp.tH y₂.2⟩, sec5op_pi_mem hyp y₂.2⟩
    have h1 : (⟨π ⟨(y₁ * y₂).1, sec5op_Y_le hyp.tH (y₁ * y₂).2⟩,
        sec5op_pi_mem hyp (y₁ * y₂).2⟩ :
        ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))) =
        ⟨π ⟨y₁.1, sec5op_Y_le hyp.tH y₁.2⟩, sec5op_pi_mem hyp y₁.2⟩ *
        ⟨π ⟨y₂.1, sec5op_Y_le hyp.tH y₂.2⟩, sec5op_pi_mem hyp y₂.2⟩ := by
      apply Subtype.ext
      show π ⟨(y₁ * y₂).1, sec5op_Y_le hyp.tH (y₁ * y₂).2⟩ =
        π ⟨y₁.1, sec5op_Y_le hyp.tH y₁.2⟩ * π ⟨y₂.1, sec5op_Y_le hyp.tH y₂.2⟩
      have he : (⟨(y₁ * y₂).1, sec5op_Y_le hyp.tH (y₁ * y₂).2⟩ :
          ↥(centralizer ({z} : Set G))) =
          ⟨y₁.1, sec5op_Y_le hyp.tH y₁.2⟩ * ⟨y₂.1, sec5op_Y_le hyp.tH y₂.2⟩ :=
        Subtype.ext rfl
      calc π ⟨(y₁ * y₂).1, sec5op_Y_le hyp.tH (y₁ * y₂).2⟩
          = π (⟨y₁.1, sec5op_Y_le hyp.tH y₁.2⟩ * ⟨y₂.1, sec5op_Y_le hyp.tH y₂.2⟩) :=
            congrArg π he
        _ = π ⟨y₁.1, sec5op_Y_le hyp.tH y₁.2⟩ * π ⟨y₂.1, sec5op_Y_le hyp.tH y₂.2⟩ :=
            map_mul π _ _
    rw [h1, map_mul (sec5g_pi (sec5op_Tb z T π))]

private theorem sec5opch_cls_apply {t z : G} {T : Subgroup G}
    {π : ↥(centralizer ({z} : Set G)) →* X} (hyp : Sec5OPHyp t z T π)
    (y : ↥(sec5op_Y t z)) :
    sec5op_cls hyp y = sec5g_pi (sec5op_Tb z T π)
      ⟨π ⟨y.1, sec5op_Y_le hyp.tH y.2⟩, sec5op_pi_mem hyp y.2⟩ := rfl

theorem sec5op_cls_surjective {t z : G} {T : Subgroup G}
    {π : ↥(centralizer ({z} : Set G)) →* X} (hyp : Sec5OPHyp t z T π) :
    Function.Surjective (sec5op_cls hyp) := by
  intro x
  have hYsub_normal : ((sec5op_Y t z).subgroupOf (centralizer ({z} : Set G))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    exact sec5op_Y_normal t z g.1 g.2 n.1 hn
  have hYb_normal : (((sec5op_Y t z).subgroupOf (centralizer ({z} : Set G))).map π).Normal :=
    hYsub_normal.map π hyp.surj
  haveI : (((sec5op_Y t z).subgroupOf (centralizer ({z} : Set G))).map π).Normal := hYb_normal
  have hTYb : sec5op_Tb z T π ≤
      ((sec5op_Y t z).subgroupOf (centralizer ({z} : Set G))).map π := by
    intro a ha
    rw [sec5op_Tb] at ha
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp ha
    exact Subgroup.mem_map.mpr ⟨t', hyp.TY (Subgroup.mem_subgroupOf.mp ht'), rfl⟩
  have hMle : normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X) ≤
      ((sec5op_Y t z).subgroupOf (centralizer ({z} : Set G))).map π :=
    Subgroup.normalClosure_le_normal hTYb
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective
    (N := goldschmidtOddCore ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))) x
  rw [← hm]
  obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.mp (hMle m.2)
  refine ⟨⟨y.1, Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
  rw [sec5opch_cls_apply]
  congr 1
  apply Subtype.ext
  exact (congrArg π (Subtype.ext rfl)).trans hyv

private theorem sec5opch_rho_mk {z : G} {T : Subgroup G} {π : ↥(centralizer ({z} : Set G)) →* X}
    (h : ↥(centralizer ({z} : Set G)))
    (m : ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))) :
    sec5op_rho z T π h (sec5g_pi (sec5op_Tb z T π) m) =
      sec5g_pi (sec5op_Tb z T π) (MulAut.conjNormal (π h) m) := by
  unfold sec5op_rho sec5op_act
  exact psiAut_mk _ (π h) m

theorem sec5op_rho_cls {t z : G} {T : Subgroup G} {π : ↥(centralizer ({z} : Set G)) →* X}
    (hyp : Sec5OPHyp t z T π) {k : G} (hk : k ∈ centralizer ({z} : Set G))
    (y : ↥(sec5op_Y t z)) :
    sec5op_rho z T π ⟨k, hk⟩ (sec5op_cls hyp y) =
      sec5op_cls hyp ⟨k * y * k⁻¹, sec5op_Y_normal t z k hk y y.2⟩ := by
  rw [sec5opch_cls_apply hyp y,
    sec5opch_cls_apply hyp ⟨k * y * k⁻¹, sec5op_Y_normal t z k hk y y.2⟩,
    sec5opch_rho_mk]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  change π ⟨k, hk⟩ * π ⟨y.1, sec5op_Y_le hyp.tH y.2⟩ * (π ⟨k, hk⟩)⁻¹ =
    π ⟨k * y * k⁻¹, sec5op_Y_le hyp.tH (sec5op_Y_normal t z k hk y y.2)⟩
  rw [show (⟨k * y * k⁻¹, sec5op_Y_le hyp.tH (sec5op_Y_normal t z k hk y y.2)⟩ :
      ↥(centralizer ({z} : Set G))) =
      ⟨k, hk⟩ * ⟨y.1, sec5op_Y_le hyp.tH y.2⟩ * ⟨k, hk⟩⁻¹ from Subtype.ext rfl]
  rw [map_mul π, map_mul π, map_inv π]

@[expose] noncomputable def sec5op_W {t z : G} {T : Subgroup G}
    {π : ↥(centralizer ({z} : Set G)) →* X} (hyp : Sec5OPHyp t z T π) : Subgroup G :=
  (sec5op_cls hyp).ker.map (sec5op_Y t z).subtype

theorem sec5op_mem_W_iff {t z : G} {T : Subgroup G} {π : ↥(centralizer ({z} : Set G)) →* X}
    (hyp : Sec5OPHyp t z T π) {x : G} :
    x ∈ sec5op_W hyp ↔ ∃ hx : x ∈ sec5op_Y t z, sec5op_cls hyp ⟨x, hx⟩ = 1 := by
  unfold sec5op_W
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [MonoidHom.mem_ker] at hy
    refine ⟨hyx ▸ y.2, ?_⟩
    rw [show (⟨x, hyx ▸ y.2⟩ : ↥(sec5op_Y t z)) = y from Subtype.ext hyx.symm]
    exact hy
  · rintro ⟨hx, hx1⟩
    exact ⟨⟨x, hx⟩, by rwa [MonoidHom.mem_ker], rfl⟩

@[expose] noncomputable def sec5op_kerG (z : G) (T : Subgroup G)
    (π : ↥(centralizer ({z} : Set G)) →* X) : Subgroup G :=
  (sec5op_rho z T π).ker.map (centralizer ({z} : Set G)).subtype

theorem sec5op_mem_kerG_iff {z : G} {T : Subgroup G} {π : ↥(centralizer ({z} : Set G)) →* X}
    {k : G} :
    k ∈ sec5op_kerG z T π ↔
      ∃ hk : k ∈ centralizer ({z} : Set G), sec5op_rho z T π ⟨k, hk⟩ = 1 := by
  unfold sec5op_kerG
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [MonoidHom.mem_ker] at hy
    refine ⟨hyx ▸ y.2, ?_⟩
    rw [show (⟨k, hyx ▸ y.2⟩ : ↥(centralizer ({z} : Set G))) = y from Subtype.ext hyx.symm]
    exact hy
  · rintro ⟨hk, hk1⟩
    exact ⟨⟨k, hk⟩, by rwa [MonoidHom.mem_ker], rfl⟩

theorem sec5op_comm_mem_W {t z : G} {T : Subgroup G} {π : ↥(centralizer ({z} : Set G)) →* X}
    (hyp : Sec5OPHyp t z T π) {k : G} (hk : k ∈ sec5op_kerG z T π) {y : G}
    (hy : y ∈ sec5op_Y t z) : k * y * k⁻¹ * y⁻¹ ∈ sec5op_W hyp := by
  obtain ⟨hkH, hρ⟩ := (sec5op_mem_kerG_iff).mp hk
  have hky : k * y * k⁻¹ ∈ sec5op_Y t z := sec5op_Y_normal t z k hkH y hy
  have hx : k * y * k⁻¹ * y⁻¹ ∈ sec5op_Y t z :=
    Subgroup.mul_mem _ hky (Subgroup.inv_mem _ hy)
  refine (sec5op_mem_W_iff hyp).mpr ⟨hx, ?_⟩
  have hsplit : (⟨k * y * k⁻¹ * y⁻¹, hx⟩ : ↥(sec5op_Y t z)) =
      ⟨k * y * k⁻¹, hky⟩ * ⟨y, hy⟩⁻¹ := Subtype.ext rfl
  rw [hsplit, map_mul (sec5op_cls hyp), map_inv (sec5op_cls hyp)]
  have hrc := sec5op_rho_cls hyp hkH ⟨y, hy⟩
  rw [← hrc, hρ]
  simp

end CFSG.OddStandard.SmallF3.Omega
