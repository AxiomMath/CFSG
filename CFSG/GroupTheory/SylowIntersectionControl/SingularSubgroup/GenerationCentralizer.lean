module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.ModuleSetting
import CFSG.Quasithin.Background.AutOnSylow
import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar
import CFSG.LocalAnalysis.AGLEmbedding.AscTenThreeOffender
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.RankThree.GroupTheory.SteinbergBMSmallTwoSylowOddKernel
import CFSG.Quasithin.Background.SmithC27Setup

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset O2Trivial)
open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

omit [Finite Ω] in
theorem le_normalizer_gomiV_of_le_normalizer {H M : Subgroup Ω}
    (h : H ≤ Subgroup.normalizer (M : Set Ω)) :
    H ≤ Subgroup.normalizer (gomiV M : Set Ω) :=
  h.trans ((CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M).trans
    (CFSG.Quasithin.normalizer_le_normalizer_of_map_mulEquiv
      CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv (pCoreOf 2 M)))

omit [Finite Ω] in
private theorem pCoreOf_inf_eq_pCoreOf_g45ib2 {M G : Subgroup Ω} (hMG : M ≤ G)
    (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) :
    pCoreOf 2 G ⊓ M = pCoreOf 2 M := by
  refine le_antisymm ?_ ?_
  · rw [inf_comm]
    exact inf_pCoreOf_le_pCoreOf 2 hMG
  · exact le_inf (pCoreOf_le_pCoreOf_of_le_normalizer 2 hMG hGM)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 M)

omit [Finite Ω] in
private theorem inf_gomiV_le_gomiV_g45ib2 {M G : Subgroup Ω} (hMG : M ≤ G)
    (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) : gomiV G ⊓ M ≤ gomiV M := by
  have hQ : pCoreOf 2 G ⊓ M = pCoreOf 2 M := pCoreOf_inf_eq_pCoreOf_g45ib2 hMG hGM
  have hVR : gomiV G ⊓ M ≤ pCoreOf 2 M := by
    rw [← hQ]
    exact inf_le_inf_right M (CFSG.Quasithin.A4.omegaOneCenterOf_le (pCoreOf 2 G))
  have hVC : gomiV G ⊓ M ≤ Subgroup.centralizer (pCoreOf 2 M : Set Ω) :=
    (inf_le_left.trans (Subgroup.le_centralizer_iff.mp
      (CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf G))).trans
      (Subgroup.centralizer_le (pCoreOf_le_pCoreOf_of_le_normalizer 2 hMG hGM))
  change gomiV G ⊓ M ≤ Subgroup.closure
    {x : Ω | x ∈ centerOf (pCoreOf 2 M) ∧ x ^ 2 = 1}
  intro x hx
  exact Subgroup.subset_closure
    ⟨le_inf hVR hVC hx, CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf hx.1⟩

omit [Finite Ω] in
private theorem conj_mem_inf_gomiV_g45ib2 {M G : Subgroup Ω} (hMG : M ≤ G)
    (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) {d v : Ω}
    (hd : d ∈ M ⊓ Subgroup.centralizer (gomiV M : Set Ω)) (hv : v ∈ gomiV G) :
    v⁻¹ * d * v * d⁻¹ ∈ gomiV G ⊓ M := by
  have hdM : d ∈ M := hd.1
  have hdG : d ∈ G := hMG hdM
  have hdN : d ∈ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2 hdG
  have hvN : v ∈ Subgroup.normalizer (M : Set Ω) :=
    hGM (((CFSG.Quasithin.A4.omegaOneCenterOf_le (pCoreOf 2 G)).trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 G)) hv)
  have hconjV : d * v * d⁻¹ ∈ gomiV G :=
    (Subgroup.mem_normalizer_iff.mp hdN v).mp hv
  refine ⟨?_, ?_⟩
  · rw [show v⁻¹ * d * v * d⁻¹ = v⁻¹ * (d * v * d⁻¹) by group]
    exact (gomiV G).mul_mem ((gomiV G).inv_mem hv) hconjV
  · have hm : d * v * d⁻¹ * v⁻¹ ∈ M := by
      have h1 : v * d⁻¹ * v⁻¹ ∈ M :=
        (Subgroup.mem_normalizer_iff.mp hvN (d⁻¹)).mp (M.inv_mem hdM)
      simpa [mul_assoc] using M.mul_mem hdM h1
    have h2 : v⁻¹ * (d * v * d⁻¹ * v⁻¹) * v ∈ M := by
      have hvG : v ∈ G := ((CFSG.Quasithin.A4.omegaOneCenterOf_le (pCoreOf 2 G)).trans
        (CFSG.LieType.BorelTits.pCoreOf_le 2 G)) hv
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (hGM (G.inv_mem hvG)) _).mp hm
    rw [show v⁻¹ * d * v * d⁻¹ = v⁻¹ * (d * v * d⁻¹ * v⁻¹) * v by group]
    exact h2

omit [Finite Ω] in
private theorem sq_mem_centralizer_g45ib2 {M G : Subgroup Ω} (hMG : M ≤ G)
    (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) {d : Ω}
    (hd : d ∈ M ⊓ Subgroup.centralizer (gomiV M : Set Ω)) :
    d ^ 2 ∈ Subgroup.centralizer (gomiV G : Set Ω) := by
  have key : ∀ v ∈ gomiV G, d * (d * v * d⁻¹) * d⁻¹ = v := by
    intro v hv
    set u : Ω := v⁻¹ * d * v * d⁻¹ with hu
    have huinf : u ∈ gomiV G ⊓ M := conj_mem_inf_gomiV_g45ib2 hMG hGM hd hv
    have huW : u ∈ gomiV M := inf_gomiV_le_gomiV_g45ib2 hMG hGM huinf
    have hdu : d * u * d⁻¹ = u := by
      have hc : u * d = d * u := (Subgroup.mem_centralizer_iff.mp hd.2) u huW
      rw [← hc]
      simp
    have hsq : u * u = 1 := by
      have := CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf huW
      simpa [pow_two] using this
    have hvu : d * v * d⁻¹ = v * u := by
      rw [hu]
      group
    calc d * (d * v * d⁻¹) * d⁻¹ = d * (v * u) * d⁻¹ := by rw [hvu]
      _ = (d * v * d⁻¹) * (d * u * d⁻¹) := by group
      _ = (v * u) * u := by rw [hvu, hdu]
      _ = v * (u * u) := by group
      _ = v := by rw [hsq, mul_one]
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : d * (d * v * d⁻¹) = v * d := by
    calc d * (d * v * d⁻¹) = (d * (d * v * d⁻¹) * d⁻¹) * d := by group
      _ = v * d := by rw [key v hv]
  have h2 : d * (d * v) = v * (d * d) := by
    calc d * (d * v) = (d * (d * v * d⁻¹)) * d := by group
      _ = (v * d) * d := by rw [h1]
      _ = v * (d * d) := by group
  calc v * d ^ 2 = v * (d * d) := by rw [pow_two]
    _ = d * (d * v) := h2.symm
    _ = d ^ 2 * v := by rw [pow_two]; group

theorem inf_centralizer_gomiV_le (h : GomiThm45Counterexample c G S) {M : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) :
    M ⊓ Subgroup.centralizer (gomiV M : Set Ω) ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
  let D : Subgroup Ω := M ⊓ Subgroup.centralizer (gomiV M : Set Ω)
  have hGN : G ≤ Subgroup.normalizer (gomiV M : Set Ω) :=
    le_normalizer_gomiV_of_le_normalizer hGM
  have hDnorm : G ≤ Subgroup.normalizer (D : Set Ω) :=
    (le_inf hGM (hGN.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup
      (gomiV M)))).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hD2 : IsPGroup 2 (autOn D (gomiV G)) := by
    refine isPGroup_iff_pow_pow_eq_one.mpr fun φ => ?_
    obtain ⟨n, hnD, hnφ⟩ := AutOn.mem_autOn_iff.1 φ.2
    have hmem : conjAct (gomiV G) n ∈ autOn D (gomiV G) :=
      AutOn.conjAct_mem_autOn_of_mem n.2 hnD
    refine ⟨1, ?_⟩
    have hd2 : (n : Ω) ^ 2 ∈ Subgroup.centralizer (gomiV G : Set Ω) :=
      sq_mem_centralizer_g45ib2 hMG hGM hnD
    have h2 : (conjAct (gomiV G) n) ^ 2 = 1 := by
      rw [pow_two, ← map_mul]
      exact (AutOn.conjAct_eq_one_iff (n * n)).mpr (by simpa [pow_two] using hd2)
    have hφ : φ = ⟨conjAct (gomiV G) n, hmem⟩ := Subtype.ext hnφ.symm
    rw [hφ]
    exact Subtype.ext (by simpa using h2)
  have hDle : D ≤ G := inf_le_left.trans hMG
  have hPle : autOn D (gomiV G) ≤ autOn G (gomiV G) := AutOn.autOn_mono hDle
  have hPnorm : autOn G (gomiV G) ≤
      Subgroup.normalizer (autOn D (gomiV G) : Set (MulAut ↥(gomiV G))) :=
    AutOn.autOn_le_normalizer_autOn hDnorm
  have hbot : autOn D (gomiV G) = ⊥ :=
    o2Trivial_autOn h _ hPle ((Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr hPnorm) hD2
  intro d hd
  have hdG : d ∈ G := hMG hd.1
  have hdN : d ∈ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2 hdG
  have hmem : conjAct (gomiV G) ⟨d, hdN⟩ ∈ autOn D (gomiV G) :=
    AutOn.conjAct_mem_autOn_of_mem hdN hd
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (AutOn.conjAct_eq_one_iff ⟨d, hdN⟩).mp hmem

theorem odd_card_autOn_inf_centralizer (h : GomiThm45Counterexample c G S) {M : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) :
    Odd (Nat.card (autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M))) := by
  let C' : Subgroup Ω := M ⊓ Subgroup.centralizer (gomiV G : Set Ω)
  let Q : Subgroup Ω := pCoreOf 2 G
  let R : Subgroup Ω := pCoreOf 2 M
  let W : Subgroup Ω := gomiV M
  have hRCV : R ≤ Subgroup.centralizer (gomiV G : Set Ω) :=
    (pCoreOf_le_pCoreOf_of_le_normalizer 2 hMG hGM).trans
      (CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf G)
  have hC'G : C' ≤ G := inf_le_left.trans hMG
  have hGN : G ≤ Subgroup.normalizer (gomiV M : Set Ω) :=
    le_normalizer_gomiV_of_le_normalizer hGM
  have hC'norm : G ≤ Subgroup.normalizer (C' : Set Ω) :=
    (le_inf hGM ((gomiV_moduleSetting G).2.trans
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup
        (gomiV G)))).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hR_sylow : IsSylowTwoOf R C' := by
    have hQ_sylow : IsSylowTwoOf Q (G ⊓ Subgroup.centralizer (gomiV G : Set Ω)) :=
      isSylowTwoOf_pCoreOf_centralizer h
    have hsylow : CFSG.ABGLocalTools.IsSylowOf 2 (Q ⊓ C') C' :=
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp hQ_sylow).inf_of_le_normalizer
        (le_inf hC'G inf_le_right) (inf_le_left.trans hC'norm)
    have hEq : Q ⊓ C' = R := by
      have hQeq : Q ⊓ M = R := pCoreOf_inf_eq_pCoreOf_g45ib2 hMG hGM
      calc Q ⊓ C' = (Q ⊓ M) ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by
            simp only [C', inf_assoc]
        _ = R ⊓ Subgroup.centralizer (gomiV G : Set Ω) := by rw [hQeq]
        _ = R := inf_eq_left.mpr hRCV
    rw [hEq] at hsylow
    exact CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hsylow
  have hC'W : C' ≤ Subgroup.normalizer (W : Set Ω) :=
    inf_le_left.trans (gomiV_moduleSetting M).2
  have hAut_sylow : IsSylowTwoOf (autOn R W) (autOn C' W) :=
    AutOn.isSylowTwoOf_autOn hR_sylow hC'W
  have hR_bot : autOn R W = ⊥ :=
    AutOn.autOn_eq_bot_of_le_centralizer
      (Subgroup.le_centralizer_iff.mp
        ((CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf R).trans
          (CFSG.Quasithin.A4.centerOf_le_centralizer R)))
  rw [hR_bot] at hAut_sylow
  have hodd : ¬ 2 ∣ Nat.card (autOn C' W) := by
    simpa [Subgroup.bot_subgroupOf, Subgroup.index_bot] using hAut_sylow.2.2
  exact Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])

omit [Finite Ω] in
theorem le_normalizer_autOn_inf_centralizer {M G : Subgroup Ω} (hMG : M ≤ G)
    (hVG : G ≤ Subgroup.normalizer (gomiV G : Set Ω)) :
    autOn M (gomiV M) ≤ Subgroup.normalizer
      (autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) :
        Set (MulAut ↥(gomiV M))) := by
  have hMC : M ≤ Subgroup.normalizer
      (Subgroup.centralizer (gomiV G : Set Ω) : Set Ω) :=
    hMG.trans (hVG.trans
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup (gomiV G)))
  have hMinf : M ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer (gomiV G : Set Ω) : Subgroup Ω) : Set Ω) :=
    (le_inf Subgroup.le_normalizer hMC).trans Subgroup.inf_normalizer_le_normalizer_inf
  exact AutOn.autOn_le_normalizer_autOn hMinf

private theorem preimage_le_centralizer_g45ib2 (h : GomiThm45Counterexample c G S)
    {M D : Subgroup Ω} (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hDM : D ≤ M) (hMD : M ≤ Subgroup.normalizer (D : Set Ω))
    (hD2 : ∀ d ∈ D, ∃ k : ℕ,
      d ^ 2 ^ k ∈ M ⊓ Subgroup.centralizer (gomiV M : Set Ω)) :
    D ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
  have hDAut2 : IsPGroup 2 (autOn D (gomiV G)) := by
    refine isPGroup_iff_pow_pow_eq_one.mpr fun φ => ?_
    obtain ⟨n, hnD, hnφ⟩ := AutOn.mem_autOn_iff.1 φ.2
    have hmem : conjAct (gomiV G) n ∈ autOn D (gomiV G) :=
      AutOn.conjAct_mem_autOn_of_mem n.2 hnD
    obtain ⟨k, hk⟩ := hD2 (n : Ω) hnD
    have hkCV : (n : Ω) ^ 2 ^ k ∈ Subgroup.centralizer (gomiV G : Set Ω) :=
      inf_centralizer_gomiV_le h hMG hGM hk
    have h2 : (conjAct (gomiV G) n) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      exact (AutOn.conjAct_eq_one_iff (n ^ 2 ^ k)).mpr hkCV
    refine ⟨k, ?_⟩
    have hφ : φ = ⟨conjAct (gomiV G) n, hmem⟩ := Subtype.ext hnφ.symm
    rw [hφ]
    exact Subtype.ext (by simpa using h2)
  have hDAutnorm : (autOn D (gomiV G)).subgroupOf (autOn M (gomiV G)) |>.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (AutOn.autOn_mono hDM)).mpr
      (AutOn.autOn_le_normalizer_autOn hMD)
  have hMnorm : (autOn M (gomiV G)).subgroupOf (autOn G (gomiV G)) |>.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (AutOn.autOn_mono hMG)).mpr
      (AutOn.autOn_le_normalizer_autOn hGM)
  have hO2M : O2Trivial (autOn M (gomiV G)) :=
    o2Trivial_of_normal (o2Trivial_autOn h) (AutOn.autOn_mono hMG) hMnorm
  have hDAutbot : autOn D (gomiV G) = ⊥ :=
    hO2M (autOn D (gomiV G)) (AutOn.autOn_mono hDM) hDAutnorm hDAut2
  intro d hd
  have hdG : d ∈ G := hMG (hDM hd)
  have hdN : d ∈ Subgroup.normalizer (gomiV G : Set Ω) := (gomiV_moduleSetting G).2 hdG
  have hmem : conjAct (gomiV G) ⟨d, hdN⟩ ∈ autOn D (gomiV G) :=
    AutOn.conjAct_mem_autOn_of_mem hdN hd
  rw [hDAutbot, Subgroup.mem_bot] at hmem
  exact (AutOn.conjAct_eq_one_iff ⟨d, hdN⟩).mp hmem

theorem o2Trivial_autOn_gomiV (h : GomiThm45Counterexample c G S) {M : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) :
    O2Trivial (autOn M (gomiV M)) := by
  intro P hPle hPN hP2
  let W : Subgroup Ω := gomiV M
  let V : Subgroup Ω := gomiV G
  have hMW : M ≤ Subgroup.normalizer (W : Set Ω) := (gomiV_moduleSetting M).2
  have hPnorm : autOn M W ≤ Subgroup.normalizer (P : Set (MulAut ↥W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mp hPN
  obtain ⟨D, hDM, hMD, hD2, hPD, hDsurj⟩ :=
    CFSG.Quasithin.A4.exists_preimage_section (V := W) (X := M) hMW hPle hPnorm hP2
  have hDV : D ≤ Subgroup.centralizer (V : Set Ω) :=
    preimage_le_centralizer_g45ib2 h hMG hGM hDM hMD hD2
  have hPleOdd : P ≤ autOn (M ⊓ Subgroup.centralizer (V : Set Ω)) W := by
    intro q hq
    obtain ⟨x, hxD, hxq⟩ := hDsurj q hq
    have hxCV : (x : Ω) ∈ Subgroup.centralizer (V : Set Ω) := hDV hxD
    have hxN : (x : Ω) ∈ Subgroup.normalizer (W : Set Ω) := hMW x.2
    rw [← hxq]
    exact AutOn.conjAct_mem_autOn_of_mem hxN ⟨x.2, hxCV⟩
  have hodd : Odd (Nat.card (autOn (M ⊓ Subgroup.centralizer (V : Set Ω)) W)) :=
    odd_card_autOn_inf_centralizer h hMG hGM
  exact CFSG.RankThree.GroupTheory.SteinbergBM.eq_bot_of_isPGroup_two_of_le_odd
    hP2 hPleOdd hodd

theorem pset_autOn_gomiV_nonempty (h : GomiThm45Counterexample c G S) {M : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) (hJM : thompsonJ S ≤ M) :
    (Pset (autOn M (gomiV M))).Nonempty := by
  by_contra hne
  have hne' : Pset (autOn M (gomiV M)) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun A hA => hne ⟨A, hA⟩
  apply not_thompsonJ_le_centralizer h
  have hW : IsElemAbelian 2 (gomiV M) := (gomiV_moduleSetting M).1
  have hWM : M ≤ Subgroup.normalizer (gomiV M : Set Ω) := (gomiV_moduleSetting M).2
  have hT : IsSylowTwoOf (S ⊓ M) M :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
      ((CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp
        h.isSylowTwoOf).inf_of_le_normalizer hMG hGM)
  have hWS : gomiV M ≤ S :=
    ((CFSG.Quasithin.A4.omegaOneCenterOf_le (pCoreOf 2 M)).trans
      (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT)).trans inf_le_left
  have hJW : thompsonJ S ≤ Subgroup.centralizer (gomiV M : Set Ω) := by
    rw [thompsonJ]
    refine iSup₂_le fun A hA => ?_
    by_contra hAc
    have hAG : A ≤ G := hA.1.trans h.isSylowTwoOf.1
    have hAM : A ≤ M := (CFSG.Quasithin.B6.le_thompsonJ hA).trans hJM
    have hoff := CFSG.AGLEmbedding.AscTenThree.isFFStarOffender_autOn_of_isMaxElemAbelian
      (H := M) (V := gomiV M) (S := S) (A := A) hW hWS hWM hAM hA hAc
    have hmem : autOn A (gomiV M) ∈ Pset (autOn M (gomiV M)) := by
      change IsFFStarOffender (autOn M (gomiV M)) (autOn A (gomiV M))
      exact hoff
    rw [hne'] at hmem
    exact hmem
  have hJD : thompsonJ S ≤ M ⊓ Subgroup.centralizer (gomiV M : Set Ω) := le_inf hJM hJW
  exact hJD.trans (inf_centralizer_gomiV_le h hMG hGM)

end CFSG.GroupTheory.GomiThm45Counterexample
