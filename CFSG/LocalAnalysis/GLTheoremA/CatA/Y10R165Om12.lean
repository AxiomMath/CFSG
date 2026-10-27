module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om11

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap Polynomial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

namespace OmEngine

variable {F V : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {n p q : ℕ}
  {Ã : Subgroup ↥(orthDerived Q)}

theorem not_isPlusType_and_anisotropic_of_finrank_eq_four [Fintype ↥(orthImage Ã)]
    (hQ : (polarBilin Q).Nondegenerate) (hn : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) (h2 : (2 : F) = 0)
    (hAe : IsElemAbelian p (orthImage Ã))
    (hB : ∀ a : ↥(orthImage Ã), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E G : Hyperplane (orthImage Ã) p} (hDE : D ≠ E) (hGD : G ≠ D) (hGE : G ≠ E)
    (hGne : blockSpace (orthImage Ã) G.1 ≠ ⊥)
    {Zv : Submodule F V}
    (hZvdim : Module.finrank F ↥Zv =
      Module.finrank F V - Module.finrank F ↥(blockSpace (orthImage Ã) D.1) -
        Module.finrank F ↥(blockSpace (orthImage Ã) E.1))
    (hregD : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∨
      ∃ ℓ : ℕ, Module.finrank F V = 2 * ℓ ∧ Odd ℓ ∧ 5 ≤ ℓ ∧
        Module.finrank F ↥(blockSpace (orthImage Ã) D.1) = 2 ∧
        Module.finrank F ↥(blockSpace (orthImage Ã) E.1) = 2)
    {xE' : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))}
    (hxE'odd : OddOrderIsometry
      (Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype) p xE')
    (hZdim : Module.finrank F ↥(fixedSpace xE') = Module.finrank F ↥Zv)
    (hVG_le_Zmap : blockSpace (orthImage Ã) G.1 ≤
      (fixedSpace xE').map (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype)
    {xGZ : ↥(fixedSpace xE') ≃ₗ[F] ↥(fixedSpace xE')}
    (hxGZcoe : ∀ z : ↥(fixedSpace xE'),
      ((xGZ z : ↥(fixedSpace xE')) : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) =
        blockEnd (orthImage Ã) hp hpF hAe t ht G
          (z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))))
    (hxGZ : OddOrderIsometry
      ((Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype).comp
        (fixedSpace xE').subtype) p xGZ) :
    (Module.finrank F ↥(fixedSpace xE') = 4 →
        ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
          ((Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype).comp
            (fixedSpace xE').subtype)) ∧
      (Module.finrank F ↥(fixedSpace xE') = 4 →
        ∀ U : Submodule F ↥(fixedSpace xE'), Module.finrank F U = 2 →
          ∃ u ∈ U,
            ((Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype).comp
              (fixedSpace xE').subtype) u ≠ 0) := by
  classical
  have hm0_of_four (h4 : Module.finrank F ↥(fixedSpace xE') = 4) :
      3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n := by
    rcases hregD with hm | ⟨ℓ, hdim, hodd, h5, hdD, hdE⟩
    · exact hm
    · exfalso
      have h6 : 6 ≤ Module.finrank F ↥(fixedSpace xE') := by
        rw [hZdim, hZvdim, hdim, hdD, hdE]; omega
      omega
  have hfree_of_four (h4 : Module.finrank F ↥(fixedSpace xE') = 4) :
      ∀ z : ↥(fixedSpace xE'), xGZ z = z → z = 0 := by
    intro z hz
    have hz_map : (((z : ↥(fixedSpace xE')) :
        ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) ∈
        (fixedSpace xE').map
          (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype :=
      Submodule.mem_map.mpr ⟨z, z.2, rfl⟩
    have hle := Submodule.finrank_mono hVG_le_Zmap
    have hZmapfin : Module.finrank F ↥((fixedSpace xE').map
        (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype) = 4 := by
      rw [Submodule.finrank_map_subtype_eq, h4]
    rw [hZmapfin] at hle
    have hVGfin : Module.finrank F ↥(blockSpace (orthImage Ã) G.1) = 4 := by
      have hd : 4 ≤ Module.finrank F ↥(blockSpace (orthImage Ã) G.1) := by
        have hpos : 0 < Module.finrank F ↥(blockSpace (orthImage Ã) G.1) := by
          rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]; exact hGne
        have hdvd := finrank_blockSpace_dvd_rk2Ord (orthImage Ã) hp hp2 hAe t ht G hGne hn
        have hev := even_finrank_blockSpace (orthImage Ã) h2 hQ hp hpF hAe hB G
        obtain ⟨k, hk⟩ := hev
        have h3 : 3 ≤ Module.finrank F ↥(blockSpace (orthImage Ã) G.1) :=
          le_trans (hm0_of_four h4) (Nat.le_of_dvd hpos hdvd)
        omega
      omega
    have hZmapVG : (fixedSpace xE').map
        (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype =
        blockSpace (orthImage Ã) G.1 :=
      (Submodule.eq_of_le_of_finrank_eq hVG_le_Zmap (by rw [hVGfin, hZmapfin])).symm
    have hzV : (((z : ↥(fixedSpace xE')) :
        ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) ∈
        blockSpace (orthImage Ã) G.1 := by
      rw [← hZmapVG]; exact hz_map
    have hfix : blockEnd (orthImage Ã) hp hpF hAe t ht G
        (((z : ↥(fixedSpace xE')) :
          ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        (((z : ↥(fixedSpace xE')) :
          ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) := by
      have h := congrArg (fun w : ↥(fixedSpace xE') =>
        (((w : ↥(fixedSpace xE')) :
          ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) hz
      rwa [hxGZcoe z] at h
    have hfixT : (t G : V ≃ₗ[F] V) (((z : ↥(fixedSpace xE')) :
        ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) =
        (((z : ↥(fixedSpace xE')) :
          ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) := by
      rw [← blockEnd_apply_mem (orthImage Ã) hp hpF hAe t ht G hzV]
      exact hfix
    have hz0 : (((z : ↥(fixedSpace xE')) :
        ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V) = 0 :=
      eq_zero_of_fixed_mem_blockSpace (orthImage Ã) hp hpF hAe (ht G) hzV hfixT
    exact Subtype.ext (Subtype.ext hz0)
  have hnotplus_of_four (h4 : Module.finrank F ↥(fixedSpace xE') = 4) :
      ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
        ((Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype).comp
          (fixedSpace xE').subtype) :=
    not_isPlusType_of_fixedPointFree_odd hxE'odd.polarBilin_fixed_nondegenerate h4 hp hp2 hn
      (hm0_of_four h4) hxGZ (hfree_of_four h4)
  have hns_of_four (h4 : Module.finrank F ↥(fixedSpace xE') = 4) :
      ∀ U : Submodule F ↥(fixedSpace xE'), Module.finrank F U = 2 →
        ∃ u ∈ U,
          ((Q.comp (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype).comp
            (fixedSpace xE').subtype) u ≠ 0 := by
    intro U hU
    by_contra h
    push Not at h
    exact hnotplus_of_four h4 ⟨U, by rw [hU, h4], h⟩
  exact ⟨hnotplus_of_four, hns_of_four⟩

theorem ne_one_of_restriction [Fintype ↥(orthImage Ã)]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hAe : IsElemAbelian p (orthImage Ã))
    (t : Hyperplane (orthImage Ã) p → ↥(orthImage Ã)) (ht : ∀ D, t D ∉ D.1)
    {D E G : Hyperplane (orthImage Ã) p} (hGD : G ≠ D) (hGne : blockSpace (orthImage Ã) G.1 ≠ ⊥)
    {xE' : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)) ≃ₗ[F]
      ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))}
    (hVG_le_Zmap : blockSpace (orthImage Ã) G.1 ≤
      (fixedSpace xE').map (fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)).subtype)
    {xGZ : ↥(fixedSpace xE') ≃ₗ[F] ↥(fixedSpace xE')}
    (hxGZcoe : ∀ z : ↥(fixedSpace xE'),
      ((xGZ z : ↥(fixedSpace xE')) : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) =
        blockEnd (orthImage Ã) hp hpF hAe t ht G
          (z : ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D)))) :
    xGZ ≠ 1 := by
  intro h1
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hGne
  obtain ⟨z, hzZ, hzv⟩ := Submodule.mem_map.mp (hVG_le_Zmap hv)
  have hfix : blockEnd (orthImage Ã) hp hpF hAe t ht G v = v := by
    have hz_eq : xGZ ⟨z, hzZ⟩ = ⟨z, hzZ⟩ := by rw [h1]; rfl
    have h := congrArg (fun w : ↥(fixedSpace xE') =>
      (((w : ↥(fixedSpace xE')) :
        ↥(fixedSpace (blockEnd (orthImage Ã) hp hpF hAe t ht D))) : V)) hz_eq
    rw [hxGZcoe ⟨z, hzZ⟩] at h
    rw [← hzv]
    exact h
  have hfixT : (t G : V ≃ₗ[F] V) v = v := by
    rw [← blockEnd_apply_mem (orthImage Ã) hp hpF hAe t ht G hv]
    exact hfix
  exact hv0 (eq_zero_of_fixed_mem_blockSpace (orthImage Ã) hp hpF hAe (ht G) hv hfixT)

theorem mem_orthDerived_of_odd_of_dim
    {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {Q : QuadraticForm F W} {p : ℕ} {x : W ≃ₗ[F] W}
    (hnd : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hx : OddOrderIsometry Q p x) (hxne : x ≠ 1)
    (heven : Even (Module.finrank F W))
    (hdim : Module.finrank F W = 4 ∨ 6 ≤ Module.finrank F W)
    (hns : Module.finrank F W = 4 → ∀ U : Submodule F W, Module.finrank F U = 2 →
      ∃ u ∈ U, Q u ≠ 0) :
    x ∈ orthDerived Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxord : orderOf x = p := orderOf_eq_prime hx.pow_eq_one hxne
  have hodd : Odd (orderOf x) := by
    rw [hxord]; exact hp.odd_of_ne_two hp2
  rcases hdim with h4 | h6
  · exact mem_orthDerived_of_odd_of_finrank_four hnd h4 (hns h4) hx.mem hodd
  · by_cases hT : ∃ U : Submodule F W, Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0
    · exact CFSG.LieType.SeitzGeneration.mem_orthDerived_of_odd_pow hnd hT
        (hp.odd_of_ne_two hp2) hx.mem hx.pow_eq_one
    · have hts : ∀ U : Submodule F W, Module.finrank F U = 3 → ∃ u ∈ U, Q u ≠ 0 := by
        intro U hU
        by_contra h
        push Not at h
        exact hT ⟨U, hU, h⟩
      have h6_or : Module.finrank F W = 6 ∨ 8 ≤ Module.finrank F W := by
        obtain ⟨k, hk⟩ := heven
        omega
      rcases h6_or with h6eq | h8
      · exact mem_orthDerived_of_odd_of_finrank_six hnd h6eq hts hx.mem hodd
      · exact absurd (exists_threeSingular_of_eight_le hnd h8) hT


theorem exists_layer
    {xD : V ≃ₗ[F] V} (hxodd : OddOrderIsometry Q p xD)
    {xE' : ↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD)}
    (hxE'odd : OddOrderIsometry (Q.comp (fixedSpace xD).subtype) p xE')
    (h2 : (2 : F) = 0)
    (hZcases : Module.finrank F ↥(fixedSpace xE') = 4 ∨
      6 ≤ Module.finrank F ↥(fixedSpace xE'))
    (hnotplus : Module.finrank F ↥(fixedSpace xE') = 4 →
      ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
        ((Q.comp (fixedSpace xD).subtype).comp (fixedSpace xE').subtype)) :
    ∃ Φ : ↥((supportedFixedDerived Q xD).subgroupOf (orthDerived Q)) →*
        (↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD)),
      (Φ = (restrictFixed Q xD).comp
        ((Subgroup.inclusion (supportedFixedDerived_le_supportedBlock (Q := Q) (x := xD))).comp
          (Subgroup.subgroupOfEquivOfLe hxodd.supportedFixedDerived_le_orthDerived).toMonoidHom)) ∧
      Function.Injective Φ ∧
      Φ.range = orthDerived (Q.comp (fixedSpace xD).subtype) ∧
      ∃ L'SFD : Subgroup (↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD)),
        L'SFD = supportedFixedDerived (Q.comp (fixedSpace xD).subtype) xE' ∧
        CFSG.IsQuasisimple ↥L'SFD ∧
        ∃ L'J : Subgroup ↥((supportedFixedDerived Q xD).subgroupOf (orthDerived Q)),
          L'J = L'SFD.comap Φ ∧ L'J.map Φ = L'SFD ∧
          ∃ L : Subgroup ↥(orthDerived Q),
            L = L'J.map (Subgroup.subtype
              ((supportedFixedDerived Q xD).subgroupOf (orthDerived Q))) ∧
            CFSG.IsQuasisimple ↥L ∧ CFSG.Open.IsQuasisimple ↥L ∧
            Nat.card ↥L = Nat.card ↥L'J ∧
            L ≤ (supportedFixedDerived Q xD).subgroupOf (orthDerived Q) := by
  classical
  set J : Subgroup ↥(orthDerived Q) :=
    (supportedFixedDerived Q xD).subgroupOf (orthDerived Q) with hJdef
  let Z : Submodule F ↥(fixedSpace xD) := fixedSpace xE'
  let QZ : QuadraticForm F ↥Z := (Q.comp (fixedSpace xD).subtype).comp Z.subtype
  have hSFle : supportedFixedDerived Q xD ≤ supportedBlock Q xD (X - 1) :=
    supportedFixedDerived_le_supportedBlock
  let Φ : ↥J →* (↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD)) :=
    (restrictFixed Q xD).comp ((Subgroup.inclusion hSFle).comp
      (Subgroup.subgroupOfEquivOfLe hxodd.supportedFixedDerived_le_orthDerived).toMonoidHom)
  have hΦ_inj : Function.Injective Φ := by
    intro a b hab
    change restrictFixed Q xD ⟨((a : ↥J) : ↥(orthDerived Q)).val,
        hSFle (Subgroup.mem_subgroupOf.mp a.2)⟩ =
      restrictFixed Q xD ⟨((b : ↥J) : ↥(orthDerived Q)).val,
        hSFle (Subgroup.mem_subgroupOf.mp b.2)⟩ at hab
    have h := restrictFixed_injective hxodd hab
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  have hΦ_range : Φ.range = orthDerived (Q.comp (fixedSpace xD).subtype) := by
    ext f
    constructor
    · rintro ⟨j, rfl⟩
      exact (mem_supportedFixedDerived.mp (Subgroup.mem_subgroupOf.mp j.2)).2
    · intro hf
      obtain ⟨g, hgf⟩ :=
        restrictFixed_surjective hxodd f (orthDerived_le_orthogonalGroup hf)
      have hgSFD : (g : V ≃ₗ[F] V) ∈ supportedFixedDerived Q xD :=
        mem_supportedFixedDerived.mpr ⟨g.2, by rw [hgf]; exact hf⟩
      let j : ↥J := ⟨⟨(g : V ≃ₗ[F] V),
        hxodd.supportedFixedDerived_le_orthDerived hgSFD⟩,
        Subgroup.mem_subgroupOf.mpr hgSFD⟩
      refine ⟨j, ?_⟩
      exact hgf
  let L'SFD : Subgroup (↥(fixedSpace xD) ≃ₗ[F] ↥(fixedSpace xD)) :=
    supportedFixedDerived (Q.comp (fixedSpace xD).subtype) xE'
  have hL'SFDq : CFSG.IsQuasisimple ↥L'SFD := by
    by_cases h4 : Module.finrank F ↥Z = 4
    · exact isQuasisimple_supportedFixedDerived_of_four hxE'odd h4 (hnotplus h4)
    · have h6 : 6 ≤ Module.finrank F ↥Z := by
        rcases hZcases with h | h
        · exact absurd h h4
        · exact h
      exact isQuasisimple_supportedFixedDerived_of_six_le hxE'odd h2 h6
  let L'J : Subgroup ↥J := L'SFD.comap Φ
  let L : Subgroup ↥(orthDerived Q) := L'J.map (Subgroup.subtype J)
  have hL'J_map : L'J.map Φ = L'SFD := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨j, hj, rfl⟩
      exact hj
    · intro f hf
      have hfΩ : f ∈ orthDerived (Q.comp (fixedSpace xD).subtype) :=
        hxE'odd.supportedFixedDerived_le_orthDerived hf
      rw [← hΦ_range] at hfΩ
      obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp hfΩ
      refine Subgroup.mem_map.mpr ⟨j, ?_, hj⟩
      rw [show L'J = L'SFD.comap Φ from rfl, Subgroup.mem_comap, hj]
      exact hf
  let eL'J : ↥L'J ≃* ↥L'SFD :=
    (Subgroup.equivMapOfInjective L'J Φ hΦ_inj).trans
      (MulEquiv.subgroupCongr hL'J_map)
  let eL : ↥L ≃* ↥L'J :=
    (Subgroup.equivMapOfInjective L'J (Subgroup.subtype J)
      (Subgroup.subtype_injective J)).symm
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (eL.trans eL'J).symm hL'SFDq
  have hLqOpen : CFSG.Open.IsQuasisimple ↥L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hLq)
  have hLcard : Nat.card ↥L = Nat.card ↥L'J := Nat.card_congr eL.toEquiv
  have hLleJ : L ≤ J := Subgroup.map_subtype_le L'J
  exact ⟨Φ, rfl, hΦ_inj, hΦ_range, L'SFD, rfl, hL'SFDq, L'J, rfl, hL'J_map, L, rfl,
    hLq, hLqOpen, hLcard, hLleJ⟩

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
