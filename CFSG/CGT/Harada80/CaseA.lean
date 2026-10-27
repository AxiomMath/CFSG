module

public import CFSG.CGT.Harada80.Nonsingular
public import CFSG.CGT.Harada80.Orbits

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80.Setting

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo QuadraticMap

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ}

structure CaseA (S : Setting G M J m) : Prop where
  h1 : H1Natural m
  centralizer_eq_bot : Subgroup.centralizer (J : Set G) = ⊥
  centralizer_le : ∀ u : ↥(blockU J), u ≠ 1 → quadQ m (S.vec u) = 0 →
    Subgroup.centralizer ({(u : G)} : Set G) ≤ M

namespace CaseA

variable {S : Setting G M J m}

theorem toBlockCase (hA : CaseA S) : BlockCase J m :=
  BlockCase.of_centralizer_eq_bot hA.h1 hA.centralizer_eq_bot

theorem blockZ_eq_bot (hA : CaseA S) : blockZ J = ⊥ :=
  S.blockZ_eq_bot hA.h1

theorem vOmega_eq (hA : CaseA S) : vOmega M = blockU J := by
  rw [vOmega, pCoreOf_eq_blockU (S := S) hA.h1 hA.centralizer_eq_bot]
  exact le_antisymm (CFSG.ComponentClassification.AschbacherTheorem3.omegaOne_le _)
    (CFSG.ComponentClassification.AschbacherTheorem3.le_omegaOne
      fun x hx => S.elemU.2 x hx)

theorem mem_of_conj_eq_of_singular (hA : CaseA S) {u u' : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu1' : u' ≠ 1) (hu : quadQ m (S.vec u) = 0) (hu' : quadQ m (S.vec u') = 0) {g : G}
    (hg : g * (u : G) * g⁻¹ = u') : g ∈ M := by
  have hC : Subgroup.centralizer ({(u : G) * 1} : Set G) ≤ M := by
    simpa using hA.centralizer_le u hu1 hu
  have hg' : g * ((u : G) * 1) * g⁻¹ = (u' : G) * 1 := by simpa using hg
  exact mem_of_conj_eq_of_singular_of_le (S := S) hA.toBlockCase hu1 hu1' hu hu'
    (blockW J).one_mem (blockW J).one_mem hC hg'

theorem quadQ_eq_zero_of_conj_eq (hA : CaseA S) {u u' : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {g : G} (hg : g * (u : G) * g⁻¹ = u') :
    quadQ m (S.vec u') = 0 := by
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one
    (quadQ m (S.vec u')) with h | h
  · exact h
  · exfalso
    exact conj_ne_of_singular_of_nonsingular (S := S) hA.blockZ_eq_bot hu1 hu h
      (hA.centralizer_le u hu1 hu) g hg

theorem mem_of_conj_mem_of_perp (hA : CaseA S) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {g : G}
    (hg : ∀ a : ↥(blockU J), polar (quadQ m) (S.vec a) (S.vec b) = 0 →
      g⁻¹ * (a : G) * g ∈ blockU J) : g ∈ M := by
  obtain ⟨u₁, -, hu₁1, -, -, hu₁, -, -, hu₁perp, -⟩ :=
    exists_singular_pair_perp_blockU (S := S) hA.blockZ_eq_bot hb
  let y : ↥(blockU J) := ⟨g⁻¹ * (u₁ : G) * g, hg u₁ hu₁perp⟩
  have hyval : (y : G) = g⁻¹ * (u₁ : G) * g := rfl
  have hconj : g⁻¹ * (u₁ : G) * (g⁻¹)⁻¹ = (y : G) := by rw [hyval]; group
  have hy1 : y ≠ 1 := by
    intro h
    apply hu₁1
    apply Subtype.ext
    have h2 : (y : G) = 1 := congrArg Subtype.val h
    calc (u₁ : G) = g * (y : G) * g⁻¹ := by rw [hyval]; group
      _ = 1 := by rw [h2]; group
  have hsing : quadQ m (S.vec y) = 0 :=
    hA.quadQ_eq_zero_of_conj_eq (S := S) hu₁1 hu₁ hconj
  have hmem : g⁻¹ ∈ M :=
    hA.mem_of_conj_eq_of_singular hu₁1 hy1 hu₁ hsing hconj
  simpa using M.inv_mem hmem

theorem pCoreOf_centralizer_le (hA : CaseA S) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) :
    pCoreOf 2 (Subgroup.centralizer ({(b : G)} : Set G)) ≤ M := by
  have hperp : ∀ g : G, (∀ a : ↥(blockU J), polar (quadQ m) (S.vec a) (S.vec b) = 0 →
      ∀ w' ∈ blockW J, g⁻¹ * ((a : G) * w') * g ∈ pCoreOf 2 M) → g ∈ M := by
    intro g hg
    refine hA.mem_of_conj_mem_of_perp hb ?_
    intro a ha
    have h1 := hg a ha 1 (blockW J).one_mem
    rw [pCoreOf_eq_blockU (S := S) hA.h1 hA.centralizer_eq_bot] at h1
    simpa using h1
  simpa using pCoreOf_centralizer_le_of_perp (S := S) hA.toBlockCase hb
    (blockW J).one_mem hperp

private theorem mem_of_conj_mem_pCoreOf_of_singular (hA : CaseA S)
    {u : ↥(blockU J)} (hu1 : u ≠ 1) (hu : quadQ m (S.vec u) = 0) {g : G}
    (hmem : g * (u : G) * g⁻¹ ∈ pCoreOf 2 M) : g ∈ M := by
  have hA' : (g * (u : G) * g⁻¹) ∈ blockU J := by
    rwa [pCoreOf_eq_blockU (S := S) hA.h1 hA.centralizer_eq_bot] at hmem
  let u' : ↥(blockU J) := ⟨g * (u : G) * g⁻¹, hA'⟩
  have hu'val : (u' : G) = g * (u : G) * g⁻¹ := rfl
  have hu'1 : u' ≠ 1 := by
    intro h
    apply hu1
    apply Subtype.ext
    have h2 : (u' : G) = 1 := congrArg Subtype.val h
    calc (u : G) = g⁻¹ * (u' : G) * g := by rw [hu'val]; group
      _ = 1 := by rw [h2]; group
  have hsing : quadQ m (S.vec u') = 0 :=
    hA.quadQ_eq_zero_of_conj_eq hu1 hu (g := g) (by rw [hu'val])
  exact hA.mem_of_conj_eq_of_singular hu1 hu'1 hu hsing (by rw [hu'val])

theorem mem_of_conj_eq_of_nonsingular (hA : CaseA S) {b b' : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) (hb' : quadQ m (S.vec b') = 1) {g : G}
    (hg : g * (b : G) * g⁻¹ = b') : g ∈ M := by
  classical
  have hE : BlockCase J m := hA.toBlockCase
  obtain ⟨u₁, u₂, hu₁1, hu₂1, hu₁₂1, hu₁, hu₂, hu₁₂, hu₁perp, hu₂perp⟩ :=
    exists_singular_pair_perp_blockU (S := S) hA.blockZ_eq_bot hb
  have hRb : pCoreOf 2 (Subgroup.centralizer ({(b : G)} : Set G)) ≤ M :=
    hA.pCoreOf_centralizer_le hb
  have hRb' : pCoreOf 2 (Subgroup.centralizer ({(b' : G)} : Set G)) ≤ M :=
    hA.pCoreOf_centralizer_le hb'
  have hmap : pCoreOf 2 (Subgroup.centralizer ({(b' : G)} : Set G)) =
      (pCoreOf 2 (Subgroup.centralizer ({(b : G)} : Set G))).map
        (MulAut.conj g).toMonoidHom :=
    pCoreOf_centralizer_conj (x := (b : G)) (y := (b' : G)) hg
  have hmem₁ : (u₁ : G) ∈ pCoreOf 2 (Subgroup.centralizer ({(b : G)} : Set G)) := by
    simpa using mem_pCoreOf_centralizer_of_perp (S := S) hE hb (blockW J).one_mem
      (by simpa using hRb) hu₁perp
  have hmem₂ : (u₂ : G) ∈ pCoreOf 2 (Subgroup.centralizer ({(b : G)} : Set G)) := by
    simpa using mem_pCoreOf_centralizer_of_perp (S := S) hE hb (blockW J).one_mem
      (by simpa using hRb) hu₂perp
  have hgu₁ : g * (u₁ : G) * g⁻¹ ∈
      pCoreOf 2 (Subgroup.centralizer ({(b' : G)} : Set G)) := by
    rw [hmap]
    exact Subgroup.mem_map.mpr ⟨(u₁ : G), hmem₁, by simp [MulAut.conj_apply]⟩
  have hgu₂ : g * (u₂ : G) * g⁻¹ ∈
      pCoreOf 2 (Subgroup.centralizer ({(b' : G)} : Set G)) := by
    rw [hmap]
    exact Subgroup.mem_map.mpr ⟨(u₂ : G), hmem₂, by simp [MulAut.conj_apply]⟩
  have hor := mem_pCoreOf_or_of_mem (S := S) hE hb' (blockW J).one_mem
    (by simpa using hRb') (by simpa using hgu₁) (by simpa using hgu₂)
  have hprod : (g * (u₁ : G) * g⁻¹) * (g * (u₂ : G) * g⁻¹) =
      g * ((u₁ * u₂ : ↥(blockU J)) : G) * g⁻¹ := by
    rw [Subgroup.coe_mul]
    group
  rcases hor with h | h | h
  · exact hA.mem_of_conj_mem_pCoreOf_of_singular hu₁1 hu₁ h
  · exact hA.mem_of_conj_mem_pCoreOf_of_singular hu₂1 hu₂ h
  · exact hA.mem_of_conj_mem_pCoreOf_of_singular hu₁₂1 hu₁₂ (hprod ▸ h)

theorem mem_of_conj_eq (hA : CaseA S) {x y : ↥(blockU J)} (hx : x ≠ 1) {g : G}
    (hg : g * (x : G) * g⁻¹ = y) : g ∈ M := by
  have hy1 : y ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    have h2 : (y : G) = 1 := congrArg Subtype.val h
    calc (x : G) = g⁻¹ * (g * (x : G) * g⁻¹) * g := by group
      _ = 1 := by rw [hg, h2]; group
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one
      (quadQ m (S.vec x)) with hqx | hqx <;>
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one
      (quadQ m (S.vec y)) with hqy | hqy
  · exact hA.mem_of_conj_eq_of_singular hx hy1 hqx hqy hg
  · exfalso
    have h0 := hA.quadQ_eq_zero_of_conj_eq hx hqx hg
    rw [hqy] at h0
    exact zero_ne_one h0.symm
  · exfalso
    have hgy : g⁻¹ * (y : G) * g = (x : G) := by rw [← hg]; group
    have h0 := hA.quadQ_eq_zero_of_conj_eq (g := g⁻¹) hy1 hqy (by simpa using hgy)
    rw [hqx] at h0
    exact zero_ne_one h0.symm
  · exact hA.mem_of_conj_eq_of_nonsingular hqx hqy hg

private theorem exists_centralizing_of_conjSubgroup (hA : CaseA S) {g : G}
    (hg : CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) ≤ M) :
    ∃ x ∈ vOmega M, x ≠ 1 ∧
      ∀ z ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M), z * x = x * z := by
  have hE : BlockCase J m := hA.toBlockCase
  have hV2 : IsPGroup 2 (vOmega M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le (vOmega_le_pCoreOf M)
  have hVg2 : IsPGroup 2 (CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M)) :=
    hV2.map (MulAut.conj g).toMonoidHom
  obtain ⟨x, hx, hx1, hc⟩ := CFSG.Timmesfeld.ARS.Linear.exists_ne_one_commute_of_le_normalizer
    hVg2 hV2 (by rw [normalizer_vOmega (S := S) hE]; exact hg) (vOmega_ne_bot (S := S) hE)
  exact ⟨x, hx, hx1, fun z hz => (hc z hz).eq⟩

private theorem conjSubgroup_vOmega_eq_of_mem (hA : CaseA S) {g : G} (hg : g ∈ M) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) = vOmega M := by
  have hgN : g ∈ Subgroup.normalizer (vOmega M : Set G) := by
    rwa [normalizer_vOmega (S := S) hA.toBlockCase]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN

theorem conjSubgroup_vOmega_eq (hA : CaseA S) {g : G}
    (hg : CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) ≤ M) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) = vOmega M := by
  classical
  have hE : BlockCase J m := hA.toBlockCase
  obtain ⟨x, hxV, hx1G, hxcent⟩ := hA.exists_centralizing_of_conjSubgroup hg
  have hycent : g⁻¹ * x * g ∈ Subgroup.centralizer (vOmega M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hgv : g * v * g⁻¹ ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) :=
      Subgroup.mem_map.mpr ⟨v, hv, by simp [MulAut.conj_apply]⟩
    have hcomm := hxcent (g * v * g⁻¹) hgv
    calc v * (g⁻¹ * x * g) = g⁻¹ * ((g * v * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * v * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * x * g) * v := by group
  have hx2 : x ^ 2 = 1 := (isElemAbelian_vOmega (S := S) hE).2 x hxV
  have hy2 : (g⁻¹ * x * g) ^ 2 = 1 := by
    simpa [hx2] using conj_pow (i := 2) (a := g⁻¹) (b := x)
  have hyV : g⁻¹ * x * g ∈ vOmega M := mem_vOmega_of_centralizer (S := S) hE hycent hy2
  have hxA : x ∈ blockU J := by
    rw [← hA.vOmega_eq]
    exact hxV
  have hyA : g⁻¹ * x * g ∈ blockU J := by
    rw [← hA.vOmega_eq]
    exact hyV
  have hgM : g⁻¹ ∈ M :=
    hA.mem_of_conj_eq (x := ⟨x, hxA⟩) (y := ⟨g⁻¹ * x * g, hyA⟩)
      (by simpa using hx1G) (by simp)
  exact hA.conjSubgroup_vOmega_eq_of_mem (by simpa using M.inv_mem hgM)

theorem isTI_vOmega (hA : CaseA S) : CFSG.CGT.Timmesfeld75.IsTI (vOmega M) := by
  intro g
  by_cases hbot : vOmega M ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) = ⊥
  · exact Or.inl hbot
  · right
    haveI : Nontrivial ↥(vOmega M ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hbot
    obtain ⟨x, hxmem, hx1⟩ := Subgroup.exists_ne_one_of_nontrivial
      (H := vOmega M ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M))
    have hxV : x ∈ vOmega M := (Subgroup.mem_inf.mp hxmem).1
    have hxVg : x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g (vOmega M) :=
      (Subgroup.mem_inf.mp hxmem).2
    have hyV : g⁻¹ * x * g ∈ vOmega M :=
      CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mp hxVg
    have hxA : x ∈ blockU J := by
      rw [← hA.vOmega_eq]
      exact hxV
    have hyA : g⁻¹ * x * g ∈ blockU J := by
      rw [← hA.vOmega_eq]
      exact hyV
    have hgM : g⁻¹ ∈ M :=
      hA.mem_of_conj_eq (x := ⟨x, hxA⟩) (y := ⟨g⁻¹ * x * g, hyA⟩)
        (by simpa using hx1) (by simp)
    rw [hA.conjSubgroup_vOmega_eq_of_mem (by simpa using M.inv_mem hgM), inf_idem]

theorem weaklyClosedIn_vOmega (hA : CaseA S) :
    CFSG.CGT.Timmesfeld75.WeaklyClosedIn (vOmega M)
      (Subgroup.normalizer (vOmega M : Set G)) := by
  refine ⟨Subgroup.le_normalizer, ?_⟩
  intro g hg
  exact hA.conjSubgroup_vOmega_eq (by rwa [normalizer_vOmega hA.toBlockCase] at hg)

end CaseA

theorem inCatalog_of_caseA
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) (S : Setting G M J m) (hA : CaseA S) :
    CFSG.Assembly.InCatalog G :=
  CFSG.CGT.Hall82.inCatalog_of_isTI_of_weaklyClosedIn hNode S.simple S.nonab
    (isElemAbelian_vOmega (S := S) hA.toBlockCase) (vOmega_ne_bot (S := S) hA.toBlockCase)
    hA.isTI_vOmega hA.weaklyClosedIn_vOmega

end CFSG.CGT.Harada80.Setting
