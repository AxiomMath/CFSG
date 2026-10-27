module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniOmega
public import CFSG.LieType.SeitzGeneration.OrthEvenSingular
import CFSG.RankThree.PartOne.S11d.OrthModels

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173U

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.OrthBlk CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCOrthogonalD4 CFSG.RankThree.PartOne.KCPrimary CFSG.Open
  CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem polarNondegOn_of_nondegenerate {W : Submodule F V}
    (h : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate) : PolarNondegOn Q W := by
  intro x hx hperp
  have := h.1 ⟨x, hx⟩ (fun y => by
    simpa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent] using hperp y y.2)
  exact congrArg Subtype.val this

theorem polarNondegOn_polarPerp (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {W : Submodule F V}
    (hW : PolarNondegOn Q W) : PolarNondegOn Q (polarPerp Q W) := by
  intro x hx hxx
  refine eq_zero_of_polar_eq_zero hQ fun y => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 ((isCompl_perp (Q := Q) hW).sup_eq_top ▸
    Submodule.mem_top (x := y))
  rw [QuadraticMap.polar_add_right]
  have h1 : polar Q x a = 0 := by
    rw [QuadraticMap.polar_comm]
    exact mem_polarPerp_iff.1 hx a ha
  rw [h1, hxx b hb, add_zero]

theorem perp_polarPerp_le (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {W : Submodule F V}
    (hW : PolarNondegOn Q W) : perp Q (polarPerp Q W) ≤ W := by
  intro x hx
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 ((isCompl_perp (Q := Q) hW).sup_eq_top ▸
    Submodule.mem_top (x := x))
  refine Submodule.add_mem _ ha ?_
  have hc0 : c = 0 := by
    refine polarNondegOn_polarPerp hQ hW c hc fun y hy => ?_
    have h1 : polar Q y (a + c) = 0 := mem_perp.1 hx y hy
    have h2 : polar Q y a = 0 := by
      rw [QuadraticMap.polar_comm]
      exact mem_polarPerp_iff.1 hy a ha
    rw [QuadraticMap.polar_add_right, h2, zero_add] at h1
    rw [QuadraticMap.polar_comm]
    exact h1
  rw [hc0]
  exact zero_mem _

theorem exists_hypPair_polarPerp_pair (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) {U : Fin (n - 1) → Submodule F V}
    (hU : IsPlaneSystem Q U) {a b : Fin (n - 1)} (hab : a ≠ b) :
    ∃ P : HypPair Q, P.e ∈ polarPerp Q (U a) ⊓ polarPerp Q (U b) ∧
      P.f ∈ polarPerp Q (U a) ⊓ polarPerp Q (U b) := by
  have hreg : PolarNondegOn Q (U a ⊔ U b) := by
    have h := hU.nondeg_biSup ({a, b} : Finset (Fin (n - 1)))
    have e : (⨆ j ∈ ({a, b} : Finset (Fin (n - 1))), U j) = U a ⊔ U b := by
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [e] at h
    exact polarNondegOn_of_nondegenerate h
  have hfin : Module.finrank F (U a ⊔ U b : Submodule F V) = 4 := by
    have h := hU.finrank_biSup ({a, b} : Finset (Fin (n - 1)))
    have e : (⨆ j ∈ ({a, b} : Finset (Fin (n - 1))), U j) = U a ⊔ U b := by
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [e, Finset.card_pair hab] at h
    omega
  have h3 : 3 ≤ Module.finrank F (polarPerp Q (U a ⊔ U b)) := by
    rw [finrank_polarPerp hQ, hfin, hdim]
    omega
  obtain ⟨s, hsP, hs0, hsQ⟩ := exists_singular_of_three_le_any (Q := Q) h3
  obtain ⟨f, hfP, hfQ, hsf⟩ := exists_partner_of_polarNondegOn (polarNondegOn_polarPerp hQ hreg) hsP hs0 hsQ
  have hle : polarPerp Q (U a ⊔ U b) ≤ polarPerp Q (U a) ⊓ polarPerp Q (U b) := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨mem_polarPerp_iff.2 fun y hy => ?_, mem_polarPerp_iff.2 fun y hy => ?_⟩
    · exact mem_polarPerp_iff.1 hx y (Submodule.mem_sup_left hy)
    · exact mem_polarPerp_iff.1 hx y (Submodule.mem_sup_right hy)
  exact ⟨⟨s, f, hsQ, hfQ, hsf⟩, hle hsP, hle hfP⟩

theorem eichler_mem_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ} (hn : 3 ≤ n)
    (hdim : Module.finrank F V = 2 * n) (e w : V) : eichler Q e w ∈ orthDerived Q := by
  rw [orthDerived_eq_elementaryGroup_of_three_le hQ hn hdim]
  exact eichler_mem_elementaryGroup Q e w

theorem eichlerGroupOn_fixedSpace_le_supportedFixedDerived {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    {m : ℕ} (hm : 3 ≤ m) (hdim : Module.finrank F (fixedSpace x) = 2 * m) :
    eichlerGroupOn Q (fixedSpace x) ≤ supportedFixedDerived Q x := by
  refine eichlerGroupOn_le fun u hu w hw => ?_
  by_cases huw : polar Q u w = 0
  · obtain ⟨-, horth⟩ := hx.fixed_others
    have hxu : x u = u := mem_fixedSpace.mp hu
    have hxw : x w = w := mem_fixedSpace.mp hw
    have hcomm : eichler Q u w * x = x * eichler Q u w := by
      have h := eichler_conj hx.mem u w
      rw [hxu, hxw] at h
      calc eichler Q u w * x = (x * eichler Q u w * x⁻¹) * x := by rw [h]
        _ = x * eichler Q u w := by group
    have hS : eichler Q u w ∈ supportedBlock Q x (X - 1) := by
      refine mem_supportedBlock.mpr ⟨⟨eichler_mem_orthogonalGroup Q u w,
        Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩, fun r hr => ?_⟩
      refine eichler_apply_of_polar_eq_zero ?_ ?_
      · rw [polar_comm]; exact horth u hu r hr
      · rw [polar_comm]; exact horth w hw r hr
    refine mem_supportedFixedDerived.mpr ⟨hS, ?_⟩
    have hres : (restrictFixed Q x ⟨eichler Q u w, hS⟩ : fixedSpace x ≃ₗ[F] fixedSpace x) =
        eichler (Q.comp (fixedSpace x).subtype) ⟨u, hu⟩ ⟨w, hw⟩ := by
      refine LinearEquiv.ext fun z => Subtype.ext ?_
      rw [coe_restrictFixed, CFSG.LieType.SeitzGeneration.OrthNS.eichler_comp_subtype_apply]
    rw [hres, orthDerived_eq_elementaryGroup_of_three_le hx.polarBilin_fixed_nondegenerate hm hdim]
    exact eichler_mem_elementaryGroup _ _ _
  · rw [eichler_of_polar_ne_zero huw]
    exact Subgroup.one_mem _

theorem eq_bot_of_normal_isPGroup_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) (hne : ∃ v, Q v ≠ 0)
    {T : Subgroup ↥(orthDerived Q)} (hTp : IsPGroup 2 T)
    (hTn : (⊤ : Subgroup ↥(orthDerived Q)) ≤ Subgroup.normalizer (T : Set ↥(orthDerived Q))) : T = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Nontrivial V := by
    obtain ⟨T₀, hT₀3, -⟩ := hT
    haveI : Nontrivial T₀ := Module.nontrivial_of_finrank_pos (by rw [hT₀3]; norm_num)
    exact (Submodule.subtype_injective T₀).nontrivial
  haveI hTnormal : T.Normal := Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 hTn)
  have hq : CFSG.IsQuasisimple ↥(orthDerived Q) := isQuasisimple_orthDerived hQ hT
  have hqOpen : CFSG.Open.IsQuasisimple ↥(orthDerived Q) :=
    ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  have hle := CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_center_of_quasisimple
    hqOpen 2 Nat.prime_two T hTnormal hTp
  rw [CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hT] at hle
  exact le_bot_iff.1 hle

theorem eichler_mem_map_closureIn_of_weight_one (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {K : Subgroup ↥(orthDerived Q)} {j : Fin (n - 1)}
    (hK : ∀ e ∈ polarPerp Q (U j), ∀ w ∈ polarPerp Q (U j), ∃ k ∈ K, (k : V ≃ₗ[F] V) = eichler Q e w)
    (c : Fin (n - 1)) :
    ∀ e ∈ polarPerp Q (U c), ∀ w ∈ polarPerp Q (U c),
      eichler Q e w ∈ (closureIn K (Subgroup.normalizer (Bb : Set ↥(orthDerived Q)))).map
        (orthDerived Q).subtype := by
  intro e' he' w' hw'
  obtain ⟨g, hgN, hgU⟩ := exists_mem_normalizer_map_eq hQ hdim hn hp hp2 hF j c
  have hgO : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup g.2
  have hmapsU : ∀ u ∈ U j, (g : V ≃ₗ[F] V) u ∈ U c := fun u hu => by
    rw [← hgU]
    exact Submodule.mem_map_of_mem hu
  have hinv : ∀ y ∈ polarPerp Q (U c), (g : V ≃ₗ[F] V)⁻¹ y ∈ polarPerp Q (U j) := by
    intro y hy
    rw [mem_polarPerp_iff]
    intro u hu
    have h1 := mem_polarPerp_iff.1 hy ((g : V ≃ₗ[F] V) u) (hmapsU u hu)
    rw [← polar_map_of_mem hgO u ((g : V ≃ₗ[F] V)⁻¹ y), LinearEquiv.apply_inv_apply']
    exact h1
  obtain ⟨k, hkK, hk⟩ := hK _ (hinv e' he') _ (hinv w' hw')
  refine ⟨g * k * g⁻¹, ?_, ?_⟩
  · have hmem : g * k * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom :=
      ⟨k, hkK, by simp [MulAut.conj_apply]⟩
    unfold closureIn
    exact (le_iSup₂_of_le g hgN le_rfl : K.map (MulAut.conj g).toMonoidHom ≤ _) hmem
  · show (g : V ≃ₗ[F] V) * (k : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V)⁻¹ = eichler Q e' w'
    rw [hk, eichler_conj hgO]
    simp

private theorem closureIn_layer_eq_top_of_weight_one_part1
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (hd1 : d ≠ 1) {j : Fin (n - 1)}
    (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j))
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) :
    ∀ e ∈ polarPerp Q (U j), ∀ w ∈ polarPerp Q (U j),
      ∃ k ∈ GLALayer (Subgroup.centralizer {d}), (k : V ≃ₗ[F] V) = eichler Q e w := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite F
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d hord
  have hn3 : 3 ≤ n := by omega
  intro e he w hw
  have h1 := eichlerGroupOn_fixedSpace_le_supportedFixedDerived hx (m := n - 1) (by omega)
    (by rw [hfs, finrank_polarPerp hQ (U j), hF.finrank_eq j, hdim]; omega)
  rw [hfs] at h1
  refine ⟨⟨eichler Q e w, eichler_mem_orthDerived hQ hn3 hdim e w⟩, ?_, rfl⟩
  rw [hL]
  exact Subgroup.mem_subgroupOf.2 (h1 (eichler_mem_eichlerGroupOn he hw))

private theorem closureIn_layer_eq_top_of_weight_one_part2
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    {j : Fin (n - 1)}
    (hK : ∀ e ∈ polarPerp Q (U j), ∀ w ∈ polarPerp Q (U j),
      ∃ k ∈ GLALayer (Subgroup.centralizer {d}), (k : V ≃ₗ[F] V) = eichler Q e w) :
    elementaryGroup Q ≤ (closureIn (GLALayer (Subgroup.centralizer {d}))
      (Subgroup.normalizer (Bb : Set ↥(orthDerived Q)))).map (orthDerived Q).subtype := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Nontrivial (Fin (n - 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨b, hbj⟩ := exists_ne j
  have hΩO : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g => orthDerived_le_orthogonalGroup g.2
  have hEich := eichler_mem_map_closureIn_of_weight_one hQ hdim hn hp hp2 hF hK
  set H : Subgroup (V ≃ₗ[F] V) := (closureIn (GLALayer (Subgroup.centralizer {d}))
    (Subgroup.normalizer (Bb : Set ↥(orthDerived Q)))).map (orthDerived Q).subtype with hH
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g, -, rfl⟩
    exact hΩO g
  have hregj : PolarNondegOn Q (polarPerp Q (U j)) :=
    polarNondegOn_polarPerp hQ (polarNondegOn_of_nondegenerate (hF.nondeg j))
  obtain ⟨P, hPe, hPf⟩ := exists_hypPair_polarPerp_pair hQ hdim hn hF.toIsPlaneSystem hbj.symm
  have hle : elementaryGroup Q ≤ H :=
    elementaryGroup_le_of_two hHO hQ hregj
      (le_trans (perp_polarPerp_le hQ (polarNondegOn_of_nondegenerate (hF.nondeg j)))
        (fun x hx => mem_polarPerp_iff.2 fun y hy => by
          rw [QuadraticMap.polar_comm]
          exact hF.perp j b hbj.symm x hx y hy))
      (hEich j) (hEich b) P hPe hPf
  simpa only [hH] using hle

private theorem closureIn_layer_eq_top_of_weight_one_part3
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n)
    {d : ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hle : elementaryGroup Q ≤ (closureIn (GLALayer (Subgroup.centralizer {d}))
      (Subgroup.normalizer (Bb : Set ↥(orthDerived Q)))).map (orthDerived Q).subtype) :
    closureIn (GLALayer (Subgroup.centralizer {d}))
      (Subgroup.normalizer (Bb : Set ↥(orthDerived Q))) = ⊤ := by
  classical
  have hn3 : 3 ≤ n := by omega
  rw [eq_top_iff]
  intro g _
  have hg : (g : V ≃ₗ[F] V) ∈ (closureIn (GLALayer (Subgroup.centralizer {d}))
      (Subgroup.normalizer (Bb : Set ↥(orthDerived Q)))).map (orthDerived Q).subtype := hle (by
    rw [← orthDerived_eq_elementaryGroup_of_three_le hQ hn3 hdim]
    exact g.2)
  obtain ⟨y, hy, hyg⟩ := hg
  rw [← Subtype.ext hyg]
  exact hy

theorem closureIn_layer_eq_top_of_weight_one (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (hd1 : d ≠ 1) {j : Fin (n - 1)}
    (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j))
    (hL : GLALayer (Subgroup.centralizer {d}) =
      (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) :
    closureIn (GLALayer (Subgroup.centralizer {d}))
      (Subgroup.normalizer (Bb : Set ↥(orthDerived Q))) = ⊤ := by
  have hK := closureIn_layer_eq_top_of_weight_one_part1 hQ hdim hn hp hp2 hF hd hd1 hfs hL
  exact closureIn_layer_eq_top_of_weight_one_part3 hQ hdim hn
    (closureIn_layer_eq_top_of_weight_one_part2 hQ hdim hn hp hp2 hF hK)

end CFSG.LocalAnalysis.GLTheoremA.T173U

end
