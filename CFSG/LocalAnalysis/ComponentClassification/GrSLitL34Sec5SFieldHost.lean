module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldUT
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldComponent
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldProduct

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped commutatorElement

theorem l34FieldHost_of_inputs (hcat : L3TwoPowProperFixedCatalog)
    (hmult : Quasithin.SchurMult2L3) : L34FieldHost := by
  intro G _ _ t P W hset hWodd hW1 hPW
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := normalizer (W : Set G) with hM
  obtain ⟨hbase, ht2, hPt, hPp, hPn, m, hm, hme, hPL⟩ := hset
  have hCM : centralizer ({t} : Set G) ≤ M :=
    ((normal_subgroupOf_iff_le_normalizer hPt).mp hPn).trans hPW
  have htM : t ∈ M := hCM (mem_centralizer_singleton_iff.mpr rfl)
  have hPM : P ≤ M := hPt.trans hCM
  have hMtop : M ≠ ⊤ := by
    intro hMt
    have hWn : W.Normal := ⟨fun n hn g => by
      have hg : g ∈ M := hMt ▸ mem_top g
      exact (mem_normalizer_iff.mp hg n).mp hn⟩
    have := hbase.1
    have := hWn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
    · exact hW1 h
    · have h2 : 2 ∣ Nat.card W := by
        rw [h, card_top, ← ht2]
        exact orderOf_dvd_natCard t
      exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr h2)
  have hKM : SectionRank.IsKGroupCat ↥M :=
    UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
      (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hbase.2.2.1 M hMtop
  set s : ↥M := ⟨t, htM⟩ with hsdef
  have hs : orderOf s = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  set Λ := P.subgroupOf M with hΛdef
  have hΛs : Λ ≤ centralizer ({s} : Set ↥M) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hPt (mem_subgroupOf.mp hx))
  have hΛ : IsPComponent 2 (Λ.subgroupOf (centralizer ({s} : Set ↥M))) := by
    rw [hsdef, FooteLit.centralizer_mk_eq htM,
      UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two,
      inf_of_le_left hCM]
    exact hPp
  have hΛL : Blueprint.LieModel (↥Λ ⧸ Open.fusionZStar ↥Λ) .PSL 3 2 m :=
    Blueprint.LieModel.of_mulEquiv (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hPM).symm) hPL
  obtain ⟨L, n, hL, -, hn, hLn, hcent⟩ :=
    exists_component_l3_of_twoComponent hcat hKM hs hΛs hΛ hm hme hΛL
  have hOX : pPrimeCore 2 (↥M ⧸ pPrimeCore 2 ↥M) = ⊥ :=
    GH74.pPrimeCore_quotient_pPrimeCore_eq_bot _ 2
  have hn4 : 4 ≤ n := by rcases hn with rfl | rfl <;> omega
  have hZ : center ↥L = ⊥ := center_eq_bot_of_isComponent_l3 hmult hOX hL (by omega) hLn
  obtain ⟨k, hk1, ⟨eY⟩⟩ := exists_mulEquiv_pi_normalClosure hL hZ
  have hPSL : Open.StatedClassicalModel (↥L ⧸ center ↥L) .PSL 3 2 n := by
    rcases hLn with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num)
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hPSL
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  let eL : ↥L ≃* projectiveSL 3 F :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eF).trans
      ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
  set πM := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπM
  set YX := normalClosure (L : Set (↥M ⧸ pPrimeCore 2 ↥M)) with hYX
  set YH := YX.comap πM with hYH
  set Y := YH.map M.subtype with hYdef
  let e1 : ↥YH ≃* ↥Y := YH.equivMapOfInjective M.subtype M.subtype_injective
  let ψ : ↥YH →* ↥YX := (πM.comp YH.subtype).codRestrict YX fun y => y.2
  have hψs : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    exact ⟨⟨x, hz⟩, rfl⟩
  let φ₀ : ↥YX ≃* (Fin k → projectiveSL 3 F) := eY.trans (MulEquiv.arrowCongr (Equiv.refl _) eL)
  let φ : ↥Y →* (Fin k → projectiveSL 3 F) := (φ₀.toMonoidHom.comp ψ).comp e1.symm.toMonoidHom
  have hYM : Y.subgroupOf M = YH :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective YH
  refine ⟨Y, k, F, inferInstance, inferInstance, inferInstance, φ, map_subtype_le _, ?_, ?_, ?_,
    ?_, hk1, ?_, ?_⟩
  · rw [hYM]
    exact Subgroup.Normal.comap normalClosure_normal πM
  · refine Subgroup.map_mono fun x hx => ?_
    show πM x ∈ YX
    have h : πM x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h]
    exact one_mem _
  · exact φ₀.surjective.comp (hψs.comp e1.symm.surjective)
  · ext y
    obtain ⟨y', rfl⟩ := e1.surjective y
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    have h1 : φ (e1 y') = φ₀ (ψ y') := by
      simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    have h2 : ((e1 y' : ↥Y) : G) = M.subtype (y' : ↥M) := rfl
    rw [h1, MulEquiv.map_eq_one_iff, h2, oddIn, Subgroup.mem_map_iff_mem M.subtype_injective]
    constructor
    · intro h
      have h3 : πM (y' : ↥M) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp h3
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr h
  · rw [hF]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
  · intro hk hF16
    have hn4' : n = 4 := by
      have h : 2 ^ n = 2 ^ 4 := by rw [← hF, hF16]; norm_num
      exact Nat.pow_right_injective le_rfl h
    have hnm : n = m := by rcases hn with h | h <;> omega
    have hYL : YX = L := by
      have hle : L ≤ YX := le_normalClosure
      have hcard : Nat.card ↥YX = Nat.card ↥L := by
        rw [Nat.card_congr eY.toEquiv, hk, Nat.card_fun, Nat.card_fin, pow_one]
      exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
    have hLnormal : L.Normal := hYL ▸ normalClosure_normal
    have hinv : L.map (MulAut.conj (πM s)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normalizer_eq_top_iff.mpr hLnormal).symm ▸ mem_top _)
    have hc := hcent hnm hinv
    intro y hy
    obtain ⟨y', hy', rfl⟩ := hy
    have hyL : πM y' ∈ L := hYL ▸ hy'
    have h1 : πM (s * y' * s⁻¹ * y'⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc _ hyL]
      group
    exact ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

theorem l34FieldNormalUTSection_of_inputs (hcat : L3TwoPowProperFixedCatalog)
    (hmult : Quasithin.SchurMult2L3) : L34FieldNormalUTSection :=
  l34FieldNormalUTSection_of_host (l34FieldHost_of_inputs hcat hmult)

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
