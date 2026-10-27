module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142MAmbig
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCD
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResSmall
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110d
public import CFSG.Quasithin.SteinbergCBAlternatingFive

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

private theorem openQuasisimple_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J E : Subgroup G} {d : G} (h : Shape15Cfg p L J E d) :
    CFSG.Open.IsQuasisimple ↥L :=
  ⟨h.qs.1.commutator_eq_top, h.qs.2.1⟩

private theorem chevAut_ne_one_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J E : Subgroup G} {d : G} (h : Shape15Cfg p L J E d)
    {hdN : d ∈ Subgroup.normalizer (L : Set G)} :
    chevAut p L ⟨d, hdN⟩ ≠ 1 := by
  intro h1
  have hpJ : p ∣ Nat.card ↥J :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      h.prime h.pcomp
  have hJleL : J ≤ L := h.pcomp.1.trans inf_le_left
  have hpL : p ∣ Nat.card ↥L := hpJ.trans (Subgroup.card_dvd_of_le hJleL)
  have hq : CFSG.Open.IsQuasisimple ↥L := openQuasisimple_of_cfg h
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI hperfL : Group.IsPerfect ↥L := h.qs.1
  have hcore : GLAPPrimeCore p ↥L ≠ ⊤ := by
    intro htop
    have hc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥L)) := CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hc
    exact h.prime.ne_one (Nat.Coprime.eq_one_of_dvd hc hpL)
  have hOZ : GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L :=
    CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq inferInstance hcore
  have hLself : GLAPComponent p L L :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.glaPComponent_self_of_dvd_card h.prime hq hpL
  have hCent : CentMod p L d := (chevAut_eq_one_iff h.prime hLself hdN).1 h1
  have hcoreG : ∀ y ∈ GLAPPrimeCoreOf p L, ∀ z ∈ L, z * y = y * z := by
    intro y hy z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hy
    have hZ := hOZ hc
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hZ ⟨z, hz⟩)
  have hfix : ∀ x : ↥L, x⁻¹ * L.normalizerMonoidHom ⟨d, hdN⟩ x ∈ Subgroup.center ↥L := by
    intro x
    have hmem : ((x⁻¹ * L.normalizerMonoidHom ⟨d, hdN⟩ x : ↥L) : G) ∈ GLAPPrimeCoreOf p L := by
      have hcoe : ((x⁻¹ * L.normalizerMonoidHom ⟨d, hdN⟩ x : ↥L) : G) =
          ⁅((x⁻¹ : ↥L) : G), d⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, chev_coe_normalizerMonoidHom,
          commutatorElement_def]
        group
      rw [hcoe]
      exact hCent.2 (Subgroup.commutator_mem_commutator (x⁻¹).2 (Subgroup.mem_zpowers d))
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hcoreG _ hmem _ y.2
  have hα : L.normalizerMonoidHom ⟨d, hdN⟩ = MonoidHom.id ↥L :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement _ hfix
  have hcent : d ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 : L.normalizerMonoidHom ⟨d, hdN⟩ ⟨l, hl⟩ = ⟨l, hl⟩ :=
      DFunLike.congr_fun hα ⟨l, hl⟩
    have h3 : d * l * d⁻¹ = l := by
      have := congrArg Subtype.val h2
      rwa [chev_coe_normalizerMonoidHom] at this
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  have hmem : d ∈ E ⊓ Subgroup.centralizer (L : Set G) := ⟨h.d_mem, hcent⟩
  rw [h.faithful, Subgroup.mem_bot] at hmem
  exact h.d_ne hmem

private theorem mulAut_congr_conj_apply {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (r : R) : MulAut.congr e (MulAut.conj r) = MulAut.conj (e r) := by
  ext y
  change e (r * e.symm y * r⁻¹) = e r * y * (e r)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

private theorem map_fixSubgroup_eq_of_commute {Q : Type*} [Group Q] {α β : MulAut Q}
    (h : α * β = β * α) :
    (fixSubgroup β).map α.toMonoidHom = fixSubgroup β := by
  have hinv : α⁻¹ * β = β * α⁻¹ := by
    calc α⁻¹ * β = α⁻¹ * β * α * α⁻¹ := by group
      _ = α⁻¹ * (β * α) * α⁻¹ := by group
      _ = α⁻¹ * (α * β) * α⁻¹ := by rw [← h]
      _ = β * α⁻¹ := by group
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    change β z = z at hz
    show β (α z) = α z
    calc β (α z) = (β * α) z := rfl
      _ = (α * β) z := by rw [← h]
      _ = α (β z) := rfl
      _ = α z := by rw [hz]
  · intro y hy
    change β y = y at hy
    refine ⟨α⁻¹ y, ?_, by simp⟩
    show β (α⁻¹ y) = α⁻¹ y
    calc β (α⁻¹ y) = (β * α⁻¹) y := rfl
      _ = (α⁻¹ * β) y := by rw [← hinv]
      _ = α⁻¹ (β y) := rfl
      _ = α⁻¹ y := by rw [hy]

private theorem card_outer_alt_five_dvd_two :
    Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 5))) ∣ 2 :=
  (CFSG.Quasithin.SteinbergCB.alternating_five_unique_Sylow_two_containment_and_solvable_normalizer
    ).2.2.2.2.2.2

section Certificates


theorem ambigHalf_holds : AmbigHalf := by
  intro G _ _ p L J E d b hcfg hb hcat hshape hin
  have hp := hcfg.prime
  have hp2 := hcfg.odd
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hcfg.idiag.1 hcfg.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hcfg.idiag.1 hb
  have hdp : d ^ p = 1 := hcfg.elem.2 d hcfg.d_mem
  have hbp : b ^ p = 1 := hcfg.elem.2 b hb
  have hdb : d * b = b * d :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_commute hcfg.elem hcfg.d_mem hb
  have hdP : IsPGroup p (Subgroup.zpowers d) := isPGroup_zpowers_of_pow_eq_one hdp
  have hqL : CFSG.Open.IsQuasisimple ↥L := openQuasisimple_of_cfg hcfg
  have hpJ : p ∣ Nat.card ↥J :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      hp hcfg.pcomp
  have hJleL : J ≤ L := hcfg.pcomp.1.trans inf_le_left
  have hpL : p ∣ Nat.card ↥L := hpJ.trans (Subgroup.card_dvd_of_le hJleL)
  have hLL : GLAPComponent p L L :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.glaPComponent_self_of_dvd_card hp hqL hpL
  obtain ⟨hSsimple, hSnc⟩ := chev_pSimple_simple_nonabelian hp hLL
  have hScenter : Subgroup.center (PSimple p L) = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hSnc
  have hOut2 := CFSG.LocalAnalysis.GLTheoremA.T171Sh.isPGroup_outer_of_ambiguous_two hcat
  have hcd_inner : chevAut p L ⟨d, hdN⟩ ∈
    CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p L) :=
    CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer hOut2 hodd
      (chevAut_pow_eq_one p L hdN hdp)
  obtain ⟨x, hx⟩ := hcd_inner
  have hx1 : x ≠ 1 := by
    intro h1
    have h0 : chevAut p L ⟨d, hdN⟩ = 1 := by rw [← hx, h1]; simp
    exact chevAut_ne_one_of_cfg hcfg h0
  have hxp : x ^ p = 1 := by
    refine CFSG.LocalAnalysis.GLTheoremA.I142C.conj_injective_of_center hScenter ?_
    rw [map_pow, hx, chevAut_pow_eq_one p L hdN hdp, map_one]
  let Jstar : Subgroup (PSimple p L) := chevTransfer p L J
  have hJstar : GLAPComponent p (fixSubgroup (chevAut p L ⟨d, hdN⟩)) Jstar :=
    glaPComponent_chevTransfer hp hdN hdP hcfg.pcomp
  have hJstar_perf : ⁅Jstar, Jstar⁆ = Jstar :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJstar
  have hJstar_ne : Jstar ≠ ⊥ := by
    intro hbot
    have hp1 : p ∣ Nat.card ↥Jstar :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
        hp hJstar
    rw [hbot, Subgroup.card_bot] at hp1
    exact hp.not_dvd_one hp1
  have hJstar_le : Jstar ≤ Subgroup.centralizer ({x} : Set (PSimple p L)) := by
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj x, hx]
    exact hJstar.1
  obtain ⟨i, hi, ⟨e0⟩⟩ := hcat
  cases i with
  | cyclic pp hpp => simp [ambiguousChev] at hi
  | sporadic s => simp [ambiguousChev] at hi
  | alternating n hn =>
    have hn' : n = 5 ∨ n = 6 ∨ n = 8 := by
      simp only [ambiguousChev] at hi
      omega
    obtain ⟨e5⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.I142M.Ambig.perfect_alt_equiv_alt5 n hn' e0 hp hp2
        hxp hx1 hJstar_le hJstar_perf hJstar_ne
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    haveI : IsSimpleGroup ↥Jstar := e5.isSimpleGroup
    have hncA5 : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
      refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩,
        ⟨Equiv.swap 0 1 * Equiv.swap 2 3, ?_⟩, ?_⟩
      · exact Equiv.Perm.mem_alternatingGroup.2 (by decide)
      · exact Equiv.Perm.mem_alternatingGroup.2 (by decide)
      · intro h
        have := congrArg Subtype.val h
        revert this
        decide
    have hncJ : ∃ a b : ↥Jstar, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hncA5
      exact ⟨e5.symm a, e5.symm b, fun h => hab (by simpa using congrArg e5 h)⟩
    have hJstarbot : Subgroup.center ↥Jstar = ⊥ :=
      CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hncJ
    obtain ⟨ePJstar⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.AltDown.nonempty_pSimple_equiv hp hJstar hJstarbot
        (MulEquiv.refl ↥Jstar)
    obtain ⟨eT⟩ := nonempty_pSimple_equiv_chevTransfer hp hdN hdP hcfg.pcomp
    have he5 : PSimple p J ≃* alternatingGroup (Fin 5) := (eT.trans ePJstar).trans e5
    have hchevJ : IsChevSimple 2 (PSimple p J) :=
      CFSG.LocalAnalysis.GLTheoremA.FR.Res.chevSimple_alt (by norm_num : 5 ≤ 5)
        (Or.inl rfl) he5
    have hcomm : MulAut.conj b * MulAut.conj d = MulAut.conj d * MulAut.conj b := by
      rw [← map_mul, ← map_mul]
      exact congrArg MulAut.conj hdb.symm
    have hLmap : L.map (MulAut.conj b).toMonoidHom = L := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).1 hbN
    have hCmap : (Subgroup.centralizer ({d} : Set G)).map (MulAut.conj b).toMonoidHom =
        Subgroup.centralizer ({d} : Set G) := by
      rw [← CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj d]
      exact map_fixSubgroup_eq_of_commute hcomm
    have hXmap : (L ⊓ Subgroup.centralizer ({d} : Set G)).map (MulAut.conj b).toMonoidHom =
        L ⊓ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj b).injective, hLmap, hCmap]
    have hJb : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G))
        (J.map (MulAut.conj b).toMonoidHom) := by
      rw [← hXmap]
      refine CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp
        (MulAut.conj b).toMonoidHom ?_ hcfg.pcomp
      have hker : (MulAut.conj b).toMonoidHom.ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj b).injective
      rw [hker, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    have hJbT : GLAPComponent p (fixSubgroup (chevAut p L ⟨d, hdN⟩))
        (chevTransfer p L (J.map (MulAut.conj b).toMonoidHom)) :=
      glaPComponent_chevTransfer hp hdN hdP hJb
    set xd : alternatingGroup (Fin n) := e0 x with hxddef
    have hxd_conj : MulAut.conj xd = MulAut.congr e0 (chevAut p L ⟨d, hdN⟩) := by
      rw [hxddef, ← hx]
      exact (mulAut_congr_conj_apply e0 x).symm
    have hxdp : xd ^ p = 1 := by
      rw [hxddef, ← map_pow, hxp, map_one]
    have hmapA : ∀ (K : Subgroup (PSimple p L)),
        GLAPComponent p (fixSubgroup (chevAut p L ⟨d, hdN⟩)) K →
        GLAPComponent p (Subgroup.centralizer ({xd} : Set (alternatingGroup (Fin n))))
          (K.map (e0 : PSimple p L →* alternatingGroup (Fin n))) := by
      intro K hK
      have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp
        (e0 : PSimple p L →* alternatingGroup (Fin n))
        (by
          have hker : (e0 : PSimple p L →* alternatingGroup (Fin n)).ker = ⊥ :=
            (MonoidHom.ker_eq_bot_iff _).mpr e0.injective
          rw [hker, inf_bot_eq, Subgroup.card_bot]
          exact Nat.coprime_one_right p) hK
      rw [← CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e0
        (chevAut p L ⟨d, hdN⟩)] at h
      rw [← hxd_conj, CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj] at h
      exact h
    have hJA := hmapA Jstar hJstar
    have hJbA := hmapA (chevTransfer p L (J.map (MulAut.conj b).toMonoidHom)) hJbT
    have heqA := (altFix_unique_of_component hp hp2 hxdp hJA).1
    have heqB := (altFix_unique_of_component hp hp2 hxdp hJbA).1
    have htrans : chevTransfer p L (J.map (MulAut.conj b).toMonoidHom) =
        chevTransfer p L J :=
      Subgroup.map_injective (f := (e0 : PSimple p L →* alternatingGroup (Fin n)))
        e0.injective (heqB.trans heqA.symm)
    have hJeq : J.map (MulAut.conj b).toMonoidHom = J :=
      eq_of_chevTransfer_eq hp hdN hdP hJb hcfg.pcomp htrans
    have hbJN : b ∈ Subgroup.normalizer (J : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      simpa using hJeq
    have hOutA5 := IsPGroup.of_card_dvd_pow (p := 2) (n := 1) card_outer_alt_five_dvd_two
    have hOutJ : IsPGroup 2
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PSimple p J)) :=
      hOutA5.of_equiv
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence he5).symm
    have hcdb_inner : chevAut p J ⟨b, hbJN⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple p J) :=
      CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer hOutJ hodd
        (chevAut_pow_eq_one p J hbJN hbp)
    have hindJ : InducesInnerMod p J b :=
      (chevAut_mem_inner_iff hp hcfg.pcomp hbJN).1 hcdb_inner
    exact ⟨hbJN, CFSG.LocalAnalysis.GLTheoremA.MI.inner_innDiag_holds hp hcfg.pcomp hchevJ
      hbJN hindJ⟩
  | lie dd =>
    obtain ⟨d1, hv⟩ := dd
    exfalso
    rcases CFSG.LocalAnalysis.GLTheoremA.I142C.chev2_lie_cases d1 hv hi with
      ⟨q, rfl, hq7⟩ | ⟨q, rfl, hq3⟩
    ·
      haveI : IsSimpleGroup (PSimple p L) := hSsimple
      have hcard : Nat.card (PSimple p L) = 168 := by
        obtain ⟨hq7p, he1⟩ :=
          CFSG.LocalAnalysis.GLTheoremA.I142C.primePower_eq_of_card
            (by norm_num : Nat.Prime 7) hq7
        obtain ⟨-, hSCor⟩ := CFSG.Models.lieModel_A 1 q hv e0
        rcases hSCor with hSC | ⟨h0, -⟩
        · rw [hq7p, he1] at hSC
          exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hSC
        · exact absurd h0 (by norm_num)
      have hconj1 : MulAut.conj x ≠ 1 := fun h1 =>
        hx1 (CFSG.LocalAnalysis.GLTheoremA.I142C.conj_injective_of_center hScenter
          (h1.trans (map_one _).symm))
      have hP : Jstar ≤ fixSubgroup (MulAut.conj x) := by
        rw [hx]
        exact hJstar.1
      have hbot : Jstar = ⊥ :=
        CFSG.LocalAnalysis.GLTheoremA.I142M.Ambig.perfect_eq_bot_of_card_168 hcard hconj1
          hP hJstar_perf
      exact absurd hbot hJstar_ne
    ·
      haveI : IsSimpleGroup (PSimple p L) := hSsimple
      obtain ⟨hcard, -, h7⟩ := CFSG.LocalAnalysis.GLTheoremA.I142C.u33_data hSsimple hSnc
        q hv hq3 e0
      haveI : Fact p.Prime := ⟨hp⟩
      have hord : orderOf x = p := orderOf_eq_prime hxp hx1
      have hP : Jstar ≤ Subgroup.centralizer ({x} : Set (PSimple p L)) := hJstar_le
      have hpd : p ∣ 2 ^ 5 * 3 ^ 3 * 7 := by
        have hh := orderOf_dvd_natCard x
        rw [hord, hcard] at hh
        simpa using hh
      rcases (Nat.Prime.dvd_mul hp).1 hpd with h23 | h7'
      · rcases (Nat.Prime.dvd_mul hp).1 h23 with h2 | h3
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
        · have hp3 : p = 3 :=
            (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
          subst hp3
          have hbot : Jstar = ⊥ :=
            CFSG.LocalAnalysis.GLTheoremA.I142C.perfect_eq_bot_of_not_seven hcard
              (h7 x hxp hx1) hP hJstar_perf
          exact absurd hbot hJstar_ne
      · have hp7 : p = 7 :=
          (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7'
        subst hp7
        have hbot : Jstar = ⊥ :=
          CFSG.LocalAnalysis.GLTheoremA.I142M.Ambig.perfect_eq_bot_of_order_seven hcard hord
            hP hJstar_perf
        exact absurd hbot hJstar_ne

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.F151

end
