module

public import CFSG.CGT.Harada80.Fusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80.Setting

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo QuadraticMap

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ}

private theorem le_normalizer_inf_blockW_vOmega (S : Setting G M J m) (hE : EvenCase J m) :
    M ≤ Subgroup.normalizer ((blockW J ⊓ vOmega M : Subgroup G) : Set G) := by
  intro x hx
  have hBC : BlockCase J m := hE.toBlockCase
  have hxV : x ∈ Subgroup.normalizer (vOmega M : Set G) := by
    rwa [normalizer_vOmega (S := S) hBC]
  have hxW : x ∈ Subgroup.normalizer (blockW J : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_blockW (S := S) hx hy, fun hy => ?_⟩
    have h := conj_mem_blockW (S := S) (M.inv_mem hx) hy
    have he : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y := by group
    rwa [he] at h
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyW, hyV⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hxW y).mp hyW,
      (Subgroup.mem_normalizer_iff.mp hxV y).mp hyV⟩
  · rintro ⟨hyW, hyV⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := conj_mem_blockW (S := S) (M.inv_mem hx) hyW
      have he : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y := by group
      rwa [he] at h
    · exact (Subgroup.mem_normalizer_iff.mp hxV y).mpr hyV

private theorem exists_mem_inf_blockW_vOmega_centralizing (S : Setting G M J m)
    (hE : EvenCase J m) {g : G}
    (hg : CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) ≤ M) :
    ∃ z, z ∈ blockW J ⊓ vOmega M ∧ z ≠ 1 ∧
      ∀ y ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M), z * y = y * z := by
  have hBC : BlockCase J m := hE.toBlockCase
  have hW₁ne : blockW J ⊓ vOmega M ≠ ⊥ := by
    obtain ⟨z₀, hz₀W, hz₀1, hz₀2⟩ := exists_involution_blockW hE
    have hz₀V : z₀ ∈ vOmega M :=
      (mem_vOmega_iff (S := S) hBC).mpr ⟨blockW_le_pCoreOf (S := S) hz₀W, hz₀2⟩
    intro hbot
    have hmem : z₀ ∈ blockW J ⊓ vOmega M := Subgroup.mem_inf.mpr ⟨hz₀W, hz₀V⟩
    rw [hbot] at hmem
    exact hz₀1 (Subgroup.mem_bot.mp hmem)
  have hV2 : IsPGroup 2 (CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M)) :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le (vOmega_le_pCoreOf M)).map
      (MulAut.conj g).toMonoidHom
  obtain ⟨z, hz, hz1, hc⟩ := CFSG.Timmesfeld.ARS.Linear.exists_ne_one_commute_of_le_normalizer
    hV2 ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
      (Subgroup.centralizer (J : Set G))).to_le inf_le_left)
    (hg.trans (le_normalizer_inf_blockW_vOmega S hE)) hW₁ne
  exact ⟨z, hz, hz1, fun y hy => (hc y hy).eq.symm⟩

private theorem exists_mem_blockW_conj_mem_blockW (S : Setting G M J m)
    (hE : EvenCase J m) {g : G}
    (hg : CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) ≤ M) :
    ∃ z, z ∈ blockW J ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧ g⁻¹ * z * g ∈ blockW J := by
  obtain ⟨z, hzW₁, hz1, hzc⟩ :=
    exists_mem_inf_blockW_vOmega_centralizing S hE hg
  have hBC : BlockCase J m := hE.toBlockCase
  have hzW : z ∈ blockW J := hzW₁.1
  have hzV : z ∈ vOmega M := hzW₁.2
  have hz2 : z ^ 2 = 1 := ((mem_vOmega_iff (S := S) hBC).mp hzV).2
  have hgzV : g⁻¹ * z * g ∈ vOmega M := by
    refine mem_vOmega_of_centralizer (S := S) hBC ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hgv : g * v * g⁻¹ ∈
          CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) := by
        rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
        have he : g⁻¹ * (g * v * g⁻¹) * g = v := by group
        rwa [he]
      have hcomm := hzc (g * v * g⁻¹) hgv
      have h2 := congrArg (fun t => g⁻¹ * t * g) hcomm
      have h2' : (g⁻¹ * z * g) * v = v * (g⁻¹ * z * g) := by
        simpa [mul_assoc] using h2
      exact h2'.symm
    · simpa [hz2] using conj_pow (i := 2) (a := g⁻¹) (b := z)
  obtain ⟨a, ha, w', hw', hzw⟩ :=
    exists_mul_of_mem_pCoreOf (S := S) hBC (vOmega_le_pCoreOf M hgzV)
  let aA : ↥(blockU J) := ⟨a, ha⟩
  have ha1 : aA = 1 := by
    by_contra ha1
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one
      (quadQ m (S.vec aA)) with hq | hq
    · refine conj_ne_of_singular (S := S) hBC ha1 hq hw' hzW hz1 g⁻¹ ?_
      simpa [aA] using hzw
    · refine conj_ne_of_nonsingular (S := S) hE hq hw' hzW hz1 g⁻¹ ?_
      simpa [aA] using hzw
  refine ⟨z, hzW, hz2, hz1, ?_⟩
  have ha1' : a = 1 := congrArg Subtype.val ha1
  rw [hzw, ha1']
  simpa using hw'

theorem conjSubgroup_vOmega_eq (S : Setting G M J m) (hE : EvenCase J m) {g : G}
    (hg : CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) ≤ M) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) = vOmega M := by
  obtain ⟨z, hzW, hz2, hz1, hgzW⟩ :=
    exists_mem_blockW_conj_mem_blockW S hE hg
  have hWle : blockW J ≤ Subgroup.centralizer (J : Set G) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hg1M : g⁻¹ ∈ M :=
    CFSG.CGT.Hall82.mem_of_common_involution_of_isMaximalTwoLocal (M := M) (X := J)
      S.maxLocal S.uniq (hWle hzW) hzord (by simpa using hWle hgzW)
  have hgM : g ∈ M := by simpa using M.inv_mem hg1M
  have hgN : g ∈ Subgroup.normalizer (vOmega M : Set G) := by
    rwa [normalizer_vOmega (S := S) hE.toBlockCase]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN

private theorem exists_singular_conj_mem_pCoreOf (S : Setting G M J m)
    (hE : EvenCase J m) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {w h : G} (hw : w ∈ blockW J)
    (hh : h ∈ Subgroup.centralizer ({(b : G) * w} : Set G)) :
    ∃ u : ↥(blockU J), u ≠ 1 ∧ quadQ m (S.vec u) = 0 ∧
      h * (u : G) * h⁻¹ ∈ pCoreOf 2 M := by
  have hBC : BlockCase J m := hE.toBlockCase
  obtain ⟨u₁, u₂, hu₁, hu₂, hu₁₂, hq₁, hq₂, hq₁₂, hp₁, hp₂⟩ :=
    exists_singular_pair_perp_blockU (S := S) (S.blockZ_eq_bot hBC.h1) hb
  let C : Subgroup G := Subgroup.centralizer ({(b : G) * w} : Set G)
  have hR : pCoreOf 2 C ≤ M := pCoreOf_centralizer_le_of_nonsingular (S := S) hE hb hw
  have hR1 : (u₁ : G) ∈ pCoreOf 2 C :=
    mem_pCoreOf_centralizer_of_perp (S := S) hBC hb hw hR hp₁
  have hR2 : (u₂ : G) ∈ pCoreOf 2 C :=
    mem_pCoreOf_centralizer_of_perp (S := S) hBC hb hw hR hp₂
  have hN : h ∈ Subgroup.normalizer (pCoreOf 2 C : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C hh
  have hc1 : h * (u₁ : G) * h⁻¹ ∈ pCoreOf 2 C :=
    (Subgroup.mem_normalizer_iff.mp hN (u₁ : G)).mp hR1
  have hc2 : h * (u₂ : G) * h⁻¹ ∈ pCoreOf 2 C :=
    (Subgroup.mem_normalizer_iff.mp hN (u₂ : G)).mp hR2
  rcases mem_pCoreOf_or_of_mem (S := S) hBC hb hw hR hc1 hc2 with h1 | h2 | h12
  · exact ⟨u₁, hu₁, hq₁, h1⟩
  · exact ⟨u₂, hu₂, hq₂, h2⟩
  · refine ⟨u₁ * u₂, hu₁₂, hq₁₂, ?_⟩
    have heq : (h * (u₁ : G) * h⁻¹) * (h * (u₂ : G) * h⁻¹) =
        h * ((u₁ * u₂ : ↥(blockU J)) : G) * h⁻¹ := by
      rw [Subgroup.coe_mul]
      group
    rwa [heq] at h12

private theorem mem_of_singular_conj_mem_vOmega (S : Setting G M J m)
    (hE : EvenCase J m) {u : ↥(blockU J)}
    (hu1 : u ≠ 1) (hu : quadQ m (S.vec u) = 0) {h : G}
    (hx : h * (u : G) * h⁻¹ ∈ vOmega M) : h ∈ M := by
  have hBC : BlockCase J m := hE.toBlockCase
  have hle : CFSG.CGT.Timmesfeld75.conjSubgroup h⁻¹ (vOmega M) ≤
      Subgroup.centralizer ({(u : G)} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hz
    have hz' : h * z * h⁻¹ ∈ vOmega M := by simpa using hz
    have hVcomm : ∀ y ∈ vOmega M, ∀ x ∈ vOmega M, y * x = x * y := by
      intro y hy x hx'
      exact pCoreOf_comm (S := S) hBC ((mem_vOmega_iff (S := S) hBC).mp hy).1
        ((mem_vOmega_iff (S := S) hBC).mp hx').1
    have hcomm := hVcomm (h * z * h⁻¹) hz' (h * (u : G) * h⁻¹) hx
    have h2 := congrArg (fun t => h⁻¹ * t * h) hcomm
    have h2' : z * (u : G) = (u : G) * z := by
      simpa [mul_assoc] using h2
    exact h2'
  have hC : Subgroup.centralizer ({(u : G)} : Set G) ≤ M := by
    simpa using centralizer_le_of_singular (S := S) hE hu1 hu (w := 1)
      (blockW J).one_mem
  have hEq : CFSG.CGT.Timmesfeld75.conjSubgroup h⁻¹ (vOmega M) = vOmega M :=
    conjSubgroup_vOmega_eq S hE (hle.trans hC)
  have hN : h⁻¹ ∈ Subgroup.normalizer (vOmega M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq
  have hM : h⁻¹ ∈ M := by
    rwa [normalizer_vOmega (S := S) hBC] at hN
  simpa using M.inv_mem hM

theorem centralizer_le_of_nonsingular (S : Setting G M J m) (hE : EvenCase J m)
    {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {w : G} (hw : w ∈ blockW J) :
    Subgroup.centralizer ({(b : G) * w} : Set G) ≤ M := by
  intro h hh
  obtain ⟨u, hu1, hu, hx⟩ := exists_singular_conj_mem_pCoreOf S hE hb hw hh
  have hx2 : (h * (u : G) * h⁻¹) ^ 2 = 1 := by
    simpa [S.elemU.2 (u : G) u.2] using conj_pow (i := 2) (a := h) (b := (u : G))
  exact mem_of_singular_conj_mem_vOmega S hE hu1 hu
    ((mem_vOmega_iff (S := S) hE.toBlockCase).mpr ⟨hx, hx2⟩)

theorem centralizer_le_of_mem_vOmega (S : Setting G M J m) (hE : EvenCase J m) {x : G}
    (hx : x ∈ vOmega M)
    (hx1 : x ≠ 1) : Subgroup.centralizer ({x} : Set G) ≤ M := by
  have hBC : BlockCase J m := hE.toBlockCase
  obtain ⟨a, ha, w, hw, hxw⟩ :=
    exists_mul_of_mem_pCoreOf (S := S) hBC (vOmega_le_pCoreOf M hx)
  let aA : ↥(blockU J) := ⟨a, ha⟩
  rw [hxw] at hx1 ⊢
  by_cases ha1 : aA = 1
  · have ha' : a = 1 := congrArg Subtype.val ha1
    have hw1 : w ≠ 1 := by
      intro hw1
      exact hx1 (by rw [ha', hw1]; simp)
    simpa [ha'] using centralizer_le_of_mem_blockW (S := S) hw hw1
  · rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one
      (quadQ m (S.vec aA)) with hq | hq
    · exact centralizer_le_of_singular (S := S) hE ha1 hq hw
    · exact centralizer_le_of_nonsingular (S := S) hE hq hw

theorem isTI_vOmega (S : Setting G M J m) (hE : EvenCase J m) :
    CFSG.CGT.Timmesfeld75.IsTI (vOmega M) := by
  intro g
  by_cases hbot : vOmega M ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
    have hxV : (x : G) ∈ vOmega M := (Subgroup.mem_inf.mp x.2).1
    have hxV' : (x : G) ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) :=
      (Subgroup.mem_inf.mp x.2).2
    have hx1' : (x : G) ≠ 1 := by
      intro h1
      exact hx1 (Subtype.ext h1)
    haveI : IsMulCommutative ↥(vOmega M) :=
      (isElemAbelian_vOmega (S := S) hE.toBlockCase).1
    have hcommVg : IsMulCommutative
        ↥(CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M)) :=
      Subgroup.map_isMulCommutative (vOmega M) (MulAut.conj g).toMonoidHom
    have hle : CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) ≤
        Subgroup.centralizer ({(x : G)} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hcommVg.is_comm.comm ⟨y, hy⟩ ⟨(x : G), hxV'⟩)
    have heq := conjSubgroup_vOmega_eq S hE
      (hle.trans (centralizer_le_of_mem_vOmega S hE hxV hx1'))
    rw [heq, inf_idem]

theorem weaklyClosedIn_vOmega (S : Setting G M J m) (hE : EvenCase J m) :
    CFSG.CGT.Timmesfeld75.WeaklyClosedIn (vOmega M)
      (Subgroup.normalizer (vOmega M : Set G)) := by
  refine ⟨Subgroup.le_normalizer, ?_⟩
  intro g hg
  rw [normalizer_vOmega (S := S) hE.toBlockCase] at hg
  exact conjSubgroup_vOmega_eq S hE hg

theorem inCatalog_of_evenCase
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) (S : Setting G M J m)
    (hE : EvenCase J m) : CFSG.Assembly.InCatalog G :=
  CFSG.CGT.Hall82.inCatalog_of_isTI_of_weaklyClosedIn hNode S.simple S.nonab
    (isElemAbelian_vOmega (S := S) hE.toBlockCase)
    (vOmega_ne_bot (S := S) hE.toBlockCase)
    (isTI_vOmega S hE)
    (weaklyClosedIn_vOmega S hE)

end CFSG.CGT.Harada80.Setting
