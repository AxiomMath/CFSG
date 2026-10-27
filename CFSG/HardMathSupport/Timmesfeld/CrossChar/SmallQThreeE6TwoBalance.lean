module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoSL6CertA
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoSL6CertB
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsBalance
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsLeaf
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotAct
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open scoped MatrixGroups
open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.Balance
open CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6ThreeEnd
open CFSG.StandardType.E6TwoPilot CFSG.SeitzReduction CFSG.SeitzReduction.E6Pilot

@[expose] def negAt (i : Fin 4) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  fun k => if k = i then -v k else v k

@[expose] def genAct : Fin 6 → (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3) :=
  ![msFun, mtFun, negAt 0, negAt 1, negAt 2, negAt 3]

@[expose] def wordAct (w : List (Fin 6)) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  w.foldr genAct v

theorem negAt_eq (i : Fin 4) (v : Fin 4 → ZMod 3) :
    v - reflFunE6Two i v • Pi.single i 1 = negAt i v := by
  funext k
  rw [Pi.sub_apply, Pi.smul_apply, reflFunE6Two_apply, negAt]
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, smul_eq_mul, mul_one, ↓reduceIte, two_mul]
    abel
  · simp [hk]

section Gens

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] noncomputable def genElt : Fin 6 → adjointGroup .E6 K :=
  ![sE6Two K, tE6Two K, nE6Two 0, nE6Two 1, nE6Two 2, nE6Two 3]

variable (K) in
@[expose] noncomputable def genWord (w : List (Fin 6)) : adjointGroup .E6 K :=
  (w.map (genElt K)).prod

theorem genElt_conj_torus (h2 : (2 : K) = 0) (i : Fin 6) (v : Fin 4 → ZMod 3) :
    genElt K i * torusE6Two h2 (.ofAdd v) * (genElt K i)⁻¹ =
      torusE6Two h2 (.ofAdd (genAct i v)) := by
  fin_cases i
  · exact (torusE6Two_msAut h2 _).trans (by rw [msAut_ofAdd]; rfl)
  · exact (torusE6Two_mtAut h2 _).trans (by rw [mtAut_ofAdd]; rfl)
  · exact (nE6Two_conj_torus h2 0 v).trans (by rw [negAt_eq]; rfl)
  · exact (nE6Two_conj_torus h2 1 v).trans (by rw [negAt_eq]; rfl)
  · exact (nE6Two_conj_torus h2 2 v).trans (by rw [negAt_eq]; rfl)
  · exact (nE6Two_conj_torus h2 3 v).trans (by rw [negAt_eq]; rfl)

theorem genWord_conj_torus (h2 : (2 : K) = 0) (w : List (Fin 6)) (v : Fin 4 → ZMod 3) :
    genWord K w * torusE6Two h2 (.ofAdd v) * (genWord K w)⁻¹ =
      torusE6Two h2 (.ofAdd (wordAct w v)) := by
  induction w with
  | nil => simp [genWord, wordAct]
  | cons i w ih =>
    rw [genWord, List.map_cons, List.prod_cons, ← genWord, wordAct, List.foldr_cons, ← wordAct,
      ← genElt_conj_torus h2 i, ← ih]
    group

end Gens

section Pairs

variable {G : Type*} [Group G]

theorem centralizer_pair_eq_inf (a b : G) :
    Subgroup.centralizer ({a, b} : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer {b} :=
  (centralizer_singleton_inf_singleton a b).symm

theorem map_conj_centralizer_pair (g a b : G) :
    (Subgroup.centralizer ({a, b} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * a * g⁻¹, g * b * g⁻¹} : Set G) := by
  rw [centralizer_pair_eq_inf, centralizer_pair_eq_inf,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, SmallQ3.map_conj_centralizer,
    SmallQ3.map_conj_centralizer]

theorem gLAPPrimeCoreOf_eq_bot_of_map_conj [Finite G] {S : Subgroup G} (g : G)
    (h : GLAPPrimeCoreOf 3 (S.map (MulAut.conj g).toMonoidHom) = ⊥) : GLAPPrimeCoreOf 3 S = ⊥ := by
  rw [SmallQ3.gLAPPrimeCoreOf_map_of_injective 3 _ (MulAut.conj g).injective] at h
  exact SmallQ3.eq_bot_of_map_eq_bot (MulAut.conj g).injective h

end Pairs

section Torus

variable {K : Type} [Field K] [CharP K 2]

theorem torusE6Two_comb (h2 : (2 : K) = 0) (c₁ c₂ : ZMod 3) (v w : Fin 4 → ZMod 3) :
    torusE6Two h2 (.ofAdd (c₁ • v + c₂ • w)) =
      torusE6Two h2 (.ofAdd v) ^ c₁.val * torusE6Two h2 (.ofAdd w) ^ c₂.val := by
  rw [ofAdd_add, map_mul, ← ZMod.natCast_zmod_val c₁, ← ZMod.natCast_zmod_val c₂,
    Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, torusE6Two_nsmul, torusE6Two_nsmul,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem centralizer_pair_le_comb (h2 : (2 : K) = 0) {v w x : Fin 4 → ZMod 3} (c₁ c₂ : ZMod 3)
    (hx : x = c₁ • v + c₂ • w) :
    Subgroup.centralizer ({torusE6Two h2 (.ofAdd v), torusE6Two h2 (.ofAdd w)} :
        Set (adjointGroup .E6 K)) ≤
      Subgroup.centralizer {torusE6Two h2 (.ofAdd x)} := by
  intro y hy
  rw [centralizer_pair_eq_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff] at hy
  rw [Subgroup.mem_centralizer_singleton_iff, hx, torusE6Two_comb]
  have h1 : Commute y (torusE6Two h2 (.ofAdd v)) := hy.1
  have h2' : Commute y (torusE6Two h2 (.ofAdd w)) := hy.2
  exact ((h1.pow_right _).mul_right (h2'.pow_right _)).eq

theorem centralizer_pair_eq_of_span (h2 : (2 : K) = 0) {v w p q : Fin 4 → ZMod 3}
    (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ZMod 3) (hp : p = a₁ • v + a₂ • w) (hq : q = b₁ • v + b₂ • w)
    (hv : v = c₁ • p + c₂ • q) (hw : w = d₁ • p + d₂ • q) :
    Subgroup.centralizer ({torusE6Two h2 (.ofAdd v), torusE6Two h2 (.ofAdd w)} :
        Set (adjointGroup .E6 K)) =
      Subgroup.centralizer {torusE6Two h2 (.ofAdd p), torusE6Two h2 (.ofAdd q)} := by
  refine le_antisymm ?_ ?_
  · rw [centralizer_pair_eq_inf (torusE6Two h2 (.ofAdd p))]
    exact le_inf (centralizer_pair_le_comb h2 a₁ a₂ hp) (centralizer_pair_le_comb h2 b₁ b₂ hq)
  · rw [centralizer_pair_eq_inf (torusE6Two h2 (.ofAdd v))]
    exact le_inf (centralizer_pair_le_comb h2 c₁ c₂ hv) (centralizer_pair_le_comb h2 d₁ d₂ hw)

end Torus

section Levi

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def phi0 : SL(6, K) →* adjointGroup .E6 K :=
  (MulAut.conj (E6Pilot.e6RepConj K 2)⁻¹).toMonoidHom.comp (slToAdjointE6 K)

theorem phi0_apply (A : SL(6, K)) :
    phi0 K A = (E6Pilot.e6RepConj K 2)⁻¹ * slToAdjointE6 K A * E6Pilot.e6RepConj K 2 := by
  simp [phi0]

theorem phi0_of_conj {k : Fin 4} {w : List (Fin 6 × Fin 6)}
    (h : E6Pilot.e6RepConj K 2 * uE6Two k * (E6Pilot.e6RepConj K 2)⁻¹ =
      slToAdjointE6 K (tvSLWord w)) : phi0 K (tvSLWord w) = uE6Two k := by
  rw [phi0_apply, ← h]
  group

theorem tvSLWord_replicate (n : ℕ) (l : List (Fin 6 × Fin 6)) :
    (tvSLWord (List.replicate n l).flatten : SL(6, K)) = tvSLWord l ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, tvSLWord_append, ih, pow_succ']

@[expose] def zvec (v : Fin 3 → ℕ) : Fin 4 → ZMod 3 :=
  ![0, (v 0 : ZMod 3), (v 1 : ZMod 3), (v 2 : ZMod 3)]

theorem phi0_zSL (h2 : (2 : K) = 0) {v : Fin 3 → ℕ} (hv : ∀ k, v k < 3) :
    phi0 K (zSL v) = torusE6Two h2 (.ofAdd (zvec v)) := by
  have hz : (zSL v : SL(6, K)) = tvSLWord [(3, 5), (5, 3)] ^ v 0 *
      tvSLWord [(0, 2), (2, 0)] ^ v 1 * tvSLWord [(4, 1), (1, 4)] ^ v 2 := by
    rw [zSL, zword, tvSLWord_append, tvSLWord_append, tvSLWord_replicate, tvSLWord_replicate,
      tvSLWord_replicate]
  have hz' : zvec v = (Pi.single (1 : Fin 4) ((v 0 : ℕ) : ZMod 3) : Fin 4 → ZMod 3) +
      Pi.single (2 : Fin 4) ((v 1 : ℕ) : ZMod 3) + Pi.single (3 : Fin 4) ((v 2 : ℕ) : ZMod 3) := by
    funext k
    fin_cases k <;> simp [zvec]
  rw [hz, map_mul, map_mul, map_pow, map_pow, map_pow, phi0_of_conj conj_uE6Two_one,
    phi0_of_conj conj_uE6Two_two, phi0_of_conj conj_uE6Two_three, hz', ofAdd_add, ofAdd_add,
    map_mul, map_mul, torusE6Two_single_eq_pow, torusE6Two_single_eq_pow, torusE6Two_single_eq_pow,
    ZMod.val_natCast_of_lt (hv 0), ZMod.val_natCast_of_lt (hv 1), ZMod.val_natCast_of_lt (hv 2)]

theorem phi0_injective (hK : Nat.card K = 2) : Function.Injective (phi0 K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [injective_iff_map_eq_one]
  intro A hA
  have hA' : slToAdjointE6 K A = 1 := by
    rw [phi0_apply] at hA
    calc slToAdjointE6 K A = E6Pilot.e6RepConj K 2 *
          ((E6Pilot.e6RepConj K 2)⁻¹ * slToAdjointE6 K A * E6Pilot.e6RepConj K 2) *
            (E6Pilot.e6RepConj K 2)⁻¹ := by group
      _ = 1 := by rw [hA]; group
  have hz : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) K) := by
    rw [← ker_slToAdjointE6]
    exact hA'
  obtain ⟨r, hr6, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  have hr1 : r = 1 := by
    rcases eq_zero_or_one_of_card_two hK r with rfl | rfl
    · simp at hr6
    · rfl
  refine Subtype.ext ?_
  rw [← hrz, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem range_phi0 : (phi0 K).range = leviB0 K := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    rw [mem_leviB0_iff_conj, phi0_apply, ← range_slToAdjointE6]
    exact ⟨A, by group⟩
  · intro hx
    rw [mem_leviB0_iff_conj, ← range_slToAdjointE6] at hx
    obtain ⟨A, hA⟩ := hx
    refine ⟨A, ?_⟩
    rw [phi0_apply, hA]
    group

theorem gLAPPrimeCoreOf_centralizer_u0_phi0 (hK : Nat.card K = 2) {Z : SL(6, K)}
    (hZ : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({Z} : Set SL(6, K))) = ⊥) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer
      ({uE6Two 0, phi0 K Z} : Set (adjointGroup .E6 K))) = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  set D := Subgroup.centralizer ({uE6Two 0, phi0 K Z} : Set (adjointGroup .E6 K)) with hD
  set N := GLAPPrimeCoreOf 3 D with hN
  have hcopN : Nat.Coprime 3 (Nat.card N) := coprime_card_gLAPPrimeCoreOf' Nat.prime_three D
  have hmemD : ∀ g : adjointGroup .E6 K, g ∈ D ↔
      g * uE6Two 0 = uE6Two 0 * g ∧ g * phi0 K Z = phi0 K Z * g := by
    intro g
    rw [hD, centralizer_pair_eq_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
  have hNL : N ≤ (phi0 K).range := by
    intro x hx
    have hxD := (hmemD x).1 (gLAPPrimeCoreOf_le_self' D hx)
    have hxc : x ∈ Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K)) :=
      Subgroup.mem_centralizer_singleton_iff.2 hxD.1
    obtain ⟨y, hy, l, hl, hyl⟩ := exists_mul_of_mem_centralizer_uE6Two_zero hK hxc
    have hcop : Nat.Coprime 3 (orderOf x) := by
      refine hcopN.coprime_dvd_right ?_
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    rw [range_phi0]
    refine SmallQ3.mem_of_pow_three_mem hcop ?_
    have hc : Commute y l := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact Commute.zpow_left (uE6Two_zero_comm_of_mem_leviB0 hl) k
    have hy3 : y ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        uE6Two_pow_three CharTwo.two_eq_zero 0, one_zpow]
    rw [hyl, hc.mul_pow, hy3, one_mul]
    exact pow_mem hl 3
  set N' := N.comap (phi0 K) with hN'
  have hinj := phi0_injective (K := K) hK
  have hφD : ∀ g ∈ Subgroup.centralizer ({Z} : Set SL(6, K)), phi0 K g ∈ D := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [hmemD]
    refine ⟨?_, by rw [← map_mul, hg, map_mul]⟩
    have hgL : phi0 K g ∈ leviB0 K := by rw [← range_phi0]; exact ⟨g, rfl⟩
    exact (uE6Two_zero_comm_of_mem_leviB0 hgL).symm
  have hN'C : N' ≤ Subgroup.centralizer ({Z} : Set SL(6, K)) := by
    intro M hM
    have hMD := (hmemD _).1 (gLAPPrimeCoreOf_le_self' D hM)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hinj (by rw [map_mul, map_mul, hMD.2])
  have hle : N' ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({Z} : Set SL(6, K))) := by
    refine le_gLAPPrimeCoreOf_of_normal' hN'C (fun g hg M hM => ?_) ?_
    · change phi0 K (g * M * g⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact gLAPPrimeCoreOf_conj_mem' _ (hφD g hg) _ hM
    · refine hcopN.coprime_dvd_right ?_
      have hmap : N'.map (phi0 K) ≤ N := Subgroup.map_comap_le _ _
      rw [← Subgroup.card_map_of_injective hinj]
      exact Subgroup.card_dvd_of_le hmap
  rw [hZ] at hle
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨M, rfl⟩ := hNL hx
  have hM : M ∈ N' := hx
  rw [Subgroup.mem_bot.1 (hle hM), map_one]
  exact Subgroup.one_mem _

theorem torusE6Two_single_zero (h2 : (2 : K) = 0) :
    torusE6Two (K := K) h2 (.ofAdd (Pi.single 0 1)) = uE6Two 0 := by
  rw [torusE6Two_single_eq_pow, ZMod.val_one, pow_one]

theorem gLAPPrimeCoreOf_plane (hK : Nat.card K = 2) (h2 : (2 : K) = 0)
    {v w p q : Fin 4 → ZMod 3} (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ZMod 3) (hp : p = a₁ • v + a₂ • w)
    (hq : q = b₁ • v + b₂ • w) (hv : v = c₁ • p + c₂ • q) (hw : w = d₁ • p + d₂ • q)
    (g : List (Fin 6)) {z : Fin 3 → ℕ} (hz : ∀ k, z k < 3)
    (hgp : wordAct g p = Pi.single 0 1) (hgq : wordAct g q = zvec z)
    (hD : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({zSL z} : Set SL(6, K))) = ⊥) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer
      ({torusE6Two h2 (.ofAdd v), torusE6Two h2 (.ofAdd w)} : Set (adjointGroup .E6 K))) = ⊥ := by
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  rw [centralizer_pair_eq_of_span h2 a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ hp hq hv hw]
  refine gLAPPrimeCoreOf_eq_bot_of_map_conj (genWord K g) ?_
  rw [map_conj_centralizer_pair, genWord_conj_torus, genWord_conj_torus, hgp, hgq,
    torusE6Two_single_zero, ← phi0_zSL h2 hz]
  exact gLAPPrimeCoreOf_centralizer_u0_phi0 hK hD

theorem gLAPPrimeCoreOf_centralizer_torus_of_four (h2 : (2 : K) = 0) {v w₁ w₂ : Fin 4 → ZMod 3}
    (hinj : ∀ a b : ZMod 3, a • w₁ + b • w₂ = 0 → a = 0 ∧ b = 0)
    (h1 : GLAPPrimeCoreOf 3 (Subgroup.centralizer
      ({torusE6Two h2 (.ofAdd v), torusE6Two h2 (.ofAdd w₁)} : Set (adjointGroup .E6 K))) = ⊥)
    (h2' : GLAPPrimeCoreOf 3 (Subgroup.centralizer
      ({torusE6Two h2 (.ofAdd v), torusE6Two h2 (.ofAdd w₂)} : Set (adjointGroup .E6 K))) = ⊥)
    (h3 : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({torusE6Two h2 (.ofAdd v),
      torusE6Two h2 (.ofAdd (w₁ + w₂))} : Set (adjointGroup .E6 K))) = ⊥)
    (h4 : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({torusE6Two h2 (.ofAdd v),
      torusE6Two h2 (.ofAdd (w₁ + 2 • w₂))} : Set (adjointGroup .E6 K))) = ⊥) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer
      ({torusE6Two h2 (.ofAdd v)} : Set (adjointGroup .E6 K))) = ⊥ := by
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  set e := torusE6Two (K := K) h2 with he
  have hcomm : ∀ x y : Fin 4 → ZMod 3, e (.ofAdd x) * e (.ofAdd y) = e (.ofAdd y) * e (.ofAdd x) :=
    fun x y => by rw [← map_mul e, ← map_mul e, ← ofAdd_add, ← ofAdd_add, add_comm]
  have hmem : ∀ x, e (.ofAdd x) ∈
      Subgroup.centralizer ({e (.ofAdd v)} : Set (adjointGroup .E6 K)) :=
    fun x => Subgroup.mem_centralizer_singleton_iff.2 (hcomm x v)
  have hcube : ∀ x, e (.ofAdd x) ^ 3 = 1 := fun x => by
    rw [← map_pow, ← ofAdd_nsmul]
    have : (3 • x : Fin 4 → ZMod 3) = 0 := by
      funext k
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
    rw [this, ofAdd_zero, map_one]
  refine gLAPPrimeCoreOf_eq_bot_of_four (hmem w₁) (hmem w₂) (hcomm w₁ w₂) (hcube w₁) (hcube w₂)
    (fun a b hab => hinj a b (by
      rw [← torusE6Two_comb] at hab
      exact Multiplicative.ofAdd.injective (torusE6Two_injective h2 (hab.trans (map_one _).symm))))
    ?_ ?_ ?_ ?_
  · rw [← centralizer_pair_eq_inf]; exact h1
  · rw [← centralizer_pair_eq_inf]; exact h2'
  · rw [← centralizer_pair_eq_inf, ← map_mul, ← ofAdd_add]; exact h3
  · rw [← centralizer_pair_eq_inf, ← map_pow, ← map_mul, ← ofAdd_nsmul, ← ofAdd_add]; exact h4

section Instances

variable (hK : Nat.card K = 2)
include hK

theorem dLevel_z001 : GLAPPrimeCoreOf 3
    (Subgroup.centralizer ({zSL ![0, 0, 1]} : Set SL(6, K))) = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  exact gLAPPrimeCoreOf_centralizer_zSL_z001 hK

theorem dLevel_z110 : GLAPPrimeCoreOf 3
    (Subgroup.centralizer ({zSL ![1, 1, 0]} : Set SL(6, K))) = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  exact gLAPPrimeCoreOf_centralizer_zSL_z110 hK

theorem dLevel_z011 : GLAPPrimeCoreOf 3
    (Subgroup.centralizer ({zSL ![0, 1, 1]} : Set SL(6, K))) = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  exact gLAPPrimeCoreOf_centralizer_zSL_z011 hK

theorem dLevel_z012 : GLAPPrimeCoreOf 3
    (Subgroup.centralizer ({zSL ![0, 1, 2]} : Set SL(6, K))) = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  exact gLAPPrimeCoreOf_centralizer_zSL_z012 hK

theorem dLevel_z121 : GLAPPrimeCoreOf 3
    (Subgroup.centralizer ({zSL ![1, 2, 1]} : Set SL(6, K))) = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  exact gLAPPrimeCoreOf_centralizer_zSL_z121 hK

theorem gLAPPrimeCoreOf_centralizer_u0u3 :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer
      ({uE6Two 0 * uE6Two 3} : Set (adjointGroup .E6 K))) = ⊥ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ht : uE6Two (K := K) 0 * uE6Two 3 = torusE6Two h2 (.ofAdd ![1, 0, 0, 1]) := by
    have e : (![1, 0, 0, 1] : Fin 4 → ZMod 3) = Pi.single 0 1 + Pi.single 3 1 := by decide
    rw [e, ofAdd_add, map_mul, torusE6Two_single_eq_pow, torusE6Two_single_eq_pow, ZMod.val_one,
      pow_one, pow_one]
  rw [ht]
  refine gLAPPrimeCoreOf_centralizer_torus_of_four h2 (w₁ := ![0, 2, 2, 0]) (w₂ := ![2, 1, 1, 0])
    (by decide) ?_ ?_ ?_ ?_
  · exact gLAPPrimeCoreOf_plane hK h2 (p := ![2, 1, 1, 2]) (q := ![1, 1, 1, 1]) 2 2 1 2 1 2 1 1
      (by decide) (by decide) (by decide) (by decide) [0, 0] (z := ![0, 0, 1]) (by decide)
      (by decide) (by decide) (dLevel_z001 hK)
  · exact gLAPPrimeCoreOf_plane hK h2 (p := ![1, 1, 1, 2]) (q := ![1, 0, 0, 1]) 2 1 1 0 0 1 1 1
      (by decide) (by decide) (by decide) (by decide) [0, 0, 2] (z := ![1, 1, 0]) (by decide)
      (by decide) (by decide) (dLevel_z110 hK)
  · exact gLAPPrimeCoreOf_plane hK h2 (p := ![1, 0, 0, 0]) (q := ![0, 0, 0, 1]) 0 2 1 1 1 1 2 0
      (by decide) (by decide) (by decide) (by decide) [] (z := ![0, 0, 1]) (by decide)
      (by decide) (by decide) (dLevel_z001 hK)
  · exact gLAPPrimeCoreOf_plane hK h2 (p := ![2, 1, 1, 1]) (q := ![2, 0, 0, 2]) 1 1 2 0 0 2 1 1
      (by decide) (by decide) (by decide) (by decide) [0] (z := ![1, 1, 0]) (by decide)
      (by decide) (by decide) (dLevel_z110 hK)

theorem gLAPPrimeCoreOf_centralizer_u0u2u3 :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer
      ({uE6Two 0 * uE6Two 2 * uE6Two 3} : Set (adjointGroup .E6 K))) = ⊥ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ht : uE6Two (K := K) 0 * uE6Two 2 * uE6Two 3 = torusE6Two h2 (.ofAdd ![1, 0, 1, 1]) := by
    have e : (![1, 0, 1, 1] : Fin 4 → ZMod 3) = Pi.single 0 1 + Pi.single 2 1 + Pi.single 3 1 := by
      decide
    rw [e, ofAdd_add, ofAdd_add, map_mul, map_mul, torusE6Two_single_eq_pow,
      torusE6Two_single_eq_pow, torusE6Two_single_eq_pow, ZMod.val_one, pow_one, pow_one, pow_one]
  rw [ht]
  refine gLAPPrimeCoreOf_centralizer_torus_of_four h2 (w₁ := ![1, 1, 0, 0]) (w₂ := ![0, 1, 0, 0])
    (by decide) ?_ ?_ ?_ ?_
  · exact gLAPPrimeCoreOf_plane hK h2 (p := ![2, 1, 1, 1]) (q := ![2, 2, 0, 0]) 1 1 0 2 1 1 0 2
      (by decide) (by decide) (by decide) (by decide) [0] (z := ![0, 1, 2]) (by decide)
      (by decide) (by decide) (dLevel_z012 hK)
  · exact gLAPPrimeCoreOf_plane hK h2 (p := ![1, 1, 1, 1]) (q := ![1, 0, 1, 1]) 1 1 1 0 0 1 1 2
      (by decide) (by decide) (by decide) (by decide) [0, 2] (z := ![1, 2, 1]) (by decide)
      (by decide) (by decide) (dLevel_z121 hK)
  · exact gLAPPrimeCoreOf_plane hK h2 (p := ![2, 2, 1, 1]) (q := ![2, 1, 0, 0]) 1 1 0 2 1 1 0 2
      (by decide) (by decide) (by decide) (by decide) [0, 3] (z := ![0, 1, 2]) (by decide)
      (by decide) (by decide) (dLevel_z012 hK)
  · exact gLAPPrimeCoreOf_plane hK h2 (p := ![1, 0, 0, 0]) (q := ![0, 0, 1, 1]) 0 1 1 2 1 1 1 0
      (by decide) (by decide) (by decide) (by decide) [] (z := ![0, 1, 1]) (by decide)
      (by decide) (by decide) (dLevel_z011 hK)

theorem gLAPPrimeCoreOf_centralizer_one_SL6 :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({1} : Set SL(6, K))) = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have htop : Subgroup.centralizer ({1} : Set SL(6, K)) = ⊤ := by
    ext x
    simp [Subgroup.mem_centralizer_singleton_iff]
  rw [htop]
  set N := GLAPPrimeCoreOf 3 (⊤ : Subgroup SL(6, K)) with hN
  have : N.Normal := ⟨fun n hn g => gLAPPrimeCoreOf_conj_mem' g (Subgroup.mem_top g) n hn⟩
  have hQ : CFSG.IsQuasisimple SL(6, K) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple 5 K (by norm_num)
  rcases SmallQ3.le_center_or_eq_top_of_isQuasisimple hQ N with h | h
  · refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨r, hr6, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (h hx)
    have hr1 : r = 1 := by
      rcases eq_zero_or_one_of_card_two hK r with rfl | rfl
      · simp at hr6
      · rfl
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    rw [← hrz, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  · exfalso
    have hcop := coprime_card_gLAPPrimeCoreOf' (G := SL(6, K)) Nat.prime_three ⊤
    rw [← hN, h] at hcop
    set z : SL(6, K) := zSL ![1, 0, 0]
    have hz : ((z : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = real K (wordMask (zword ![1, 0, 0])) :=
      coe_tvSLWord_eq_real _
    have hz3 : z ^ 3 = 1 := by
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_pow, hz, ← real_mpow _ (length_wordMask _),
        show mpow (wordMask (zword ![1, 0, 0])) 3 = mone by decide, real_mone,
        Matrix.SpecialLinearGroup.coe_one]
    have hz1 : z ≠ 1 := by
      intro h1
      have e : real K (wordMask (zword ![1, 0, 0])) = real K mone := by
        rw [← hz, h1, Matrix.SpecialLinearGroup.coe_one, real_mone]
      have := real_injective (length_wordMask _) length_mone (wordMask_lt _) mone_lt e
      exact absurd this (by decide)
    have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have h3 : 3 ∣ Nat.card (⊤ : Subgroup SL(6, K)) := by
      rw [← hord, ← Subgroup.orderOf_mk z (Subgroup.mem_top z)]
      exact orderOf_dvd_natCard _
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)

theorem gLAPPrimeCoreOf_centralizer_u0 :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K))) = ⊥ := by
  have e : Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K)) =
      Subgroup.centralizer ({uE6Two 0, phi0 K 1} : Set (adjointGroup .E6 K)) := by
    rw [map_one, centralizer_pair_eq_inf]
    ext x
    simp [Subgroup.mem_centralizer_singleton_iff]
  rw [e]
  exact gLAPPrimeCoreOf_centralizer_u0_phi0 hK (gLAPPrimeCoreOf_centralizer_one_SL6 hK)

end Instances

end Levi

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
