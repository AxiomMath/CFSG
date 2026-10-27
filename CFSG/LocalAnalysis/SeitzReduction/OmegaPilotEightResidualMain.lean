module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightResidualStable
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightLeviOTwo
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidual
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonal

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem conjIntoIn_plusFour {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    ConjIntoIn (matrixProjectiveImage (coordinateQuadPlus 4 K)) := by
  intro B hB
  obtain ⟨β, hβ⟩ :=
    CFSG.ComponentClassification.RankTwoHypIIOrthogonal.exists_conj_le_image_plus_four hf hK B hB
  exact ⟨β⁻¹, hβ⟩

theorem isLongRoot_map_plus {n : ℕ} (hn : 3 ≤ n)
    (δ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (z : matrixProjectiveDerived (coordinateQuadPlus n K)) (hz : IsLongRoot _ z) :
    IsLongRoot _ (δ z) := by
  obtain ⟨U, hU⟩ := exists_sylow_commute_of_isLongRoot_plus hn hz
  exact isLongRoot_of_commute_sylow_plus_of_mulEquiv δ hn U (ne_one_of_isLongRoot_plus hn hz) hU

theorem perfect_centralizer_plus_four (hq : 4 ≤ Nat.card K)
    {z : matrixProjectiveDerived (coordinateQuadPlus 4 K)} (hz : IsLongRoot _ z) :
    ⁅centralizer ({z} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))),
      centralizer ({z} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))⁆ =
      centralizer ({z} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  obtain ⟨hS, -⟩ := plusFourLeviInput_holds K hq 0 1 h01
  have hQ := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  have hi := isHypCoord_coordinateQuadPlus (K := K) (0 : Fin 4)
  have hj := isHypCoord_coordinateQuadPlus (K := K) (1 : Fin 4)
  have hk := isHypCoord_coordinateQuadPlus (K := K) (2 : Fin 4)
  have h₁₂ := hi.orth hj (pairDisjoint_plus h01)
  have h₁₃ := hi.orth hk (pairDisjoint_plus h02)
  have h₂₃ := hj.orth hk (pairDisjoint_plus h12)
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  have hC₀ := commutator_centralizer_rootPairElt_of hi hj (pairDisjoint_plus h01) hQ h₁₃ h₂₃ hl0
    hl1 hS
  set z₀ := rootPairElt hQ h₁₂ h₁₃ h₂₃ with hz₀def
  have hz₀ : IsLongRoot _ z₀ := isLongRoot_rootPairElt _ _ _ _
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_isLongRoot_plus (by norm_num) hz₀ hz)
  have hmap : centralizer ({z} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) =
      (centralizer ({z₀} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))).map
        (MulAut.conj c).toMonoidHom := by
    ext x
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      MulAut.conj_symm_apply, ← hc]
    constructor
    · intro h
      calc c⁻¹ * x * c * z₀ = c⁻¹ * (x * (c * z₀ * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * z₀ * c⁻¹) * x) * c := by rw [h]
        _ = z₀ * (c⁻¹ * x * c) := by group
    · intro h
      calc x * (c * z₀ * c⁻¹) = c * ((c⁻¹ * x * c) * z₀) * c⁻¹ := by group
        _ = c * (z₀ * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
        _ = c * z₀ * c⁻¹ * x := by group
  rw [hmap, ← map_commutator]
  exact congrArg _ hC₀

end Model

section TwoSided

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_longRoot_twoSided_plus_four_of_oneSided (hset : SeitzSetting G L)
    {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {g : G} {z : L} (hz : IsLongRoot _ (e z)) (hgz : g⁻¹ * t * g = t * (z : G)) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  have htC := mem_centralizer_of_inf_eq hKt
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hLt : L ≤ centralizer ({t} : Set G) :=
    SeitzQ2.le_centralizer_singleton_of_mem_centralizer htC
  have hOut := isSolvable_outer_of_mulEquiv_plus (by norm_num) hf hK e
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hzt : (z : G) * t = t * z := mem_centralizer_singleton_iff.1 (hLt z.2)
  set t' := g⁻¹ * t * g with ht'
  set L' := CFSG.conjugate L g with hL'
  have ht't' : t' * t' = 1 := LinearPilot.conj_mul_conj_eq_one ht g
  have hzz : (z : G) * z = 1 := by
    have h1 : (t * z) * (t * z) = 1 := by rw [← hgz]; exact ht't'
    calc (z : G) * z = t * (z * t) * z := by rw [hzt, ← mul_assoc, ht2, one_mul]
      _ = (t * z) * (t * z) := by group
      _ = 1 := h1
  obtain ⟨U₀, hU₀⟩ := exists_sylow_commute_of_isLongRoot_plus (by norm_num) hz
  set M : Subgroup G :=
    ((centralizer ({e z} : Set (matrixProjectiveDerived (coordinateQuadPlus 4 K)))).map
      e.symm.toMonoidHom).map L.subtype with hM
  have hMperf : ⁅M, M⁆ = M := by
    rw [hM, ← map_commutator, ← map_commutator, perfect_centralizer_plus_four hq hz]
  have hcz : ∀ c : matrixProjectiveDerived (coordinateQuadPlus 4 K), c * e z = e z * c →
      ((e.symm c : L) : G) * z = z * e.symm c := by
    intro c hc
    have h1 : e.symm c * z = z * e.symm c := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hc]
    exact congrArg Subtype.val h1
  have hMC : M ≤ L ⊓ centralizer ({t'} : Set G) := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨(e.symm c).2, ?_⟩
    change ((e.symm c : L) : G) ∈ centralizer ({t'} : Set G)
    rw [mem_centralizer_singleton_iff]
    have h1' := hcz c (mem_centralizer_singleton_iff.1 hc)
    have h2 : ((e.symm c : L) : G) * t = t * e.symm c :=
      mem_centralizer_singleton_iff.1 (hLt (e.symm c).2)
    change ((e.symm c : L) : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * e.symm c
    rw [show g⁻¹ * t * g = t * (z : G) from hgz]
    calc ((e.symm c : L) : G) * (t * z) = (e.symm c * t) * z := by group
      _ = t * (e.symm c * z) := by rw [h2]; group
      _ = t * (z * e.symm c) := by rw [h1']
      _ = t * z * e.symm c := by group
  set U : Subgroup G := ((U₀ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))).map
    e.symm.toMonoidHom).map L.subtype with hU
  have hUM : U ≤ M :=
    map_mono (map_mono fun u hu => mem_centralizer_singleton_iff.2 (hU₀ u hu))
  have hsym := LinearPilot.perfectCore_inf_centralizer_conj_eq hset.standardSetting hOut htC ht g
  have hUL' : U ≤ L' := hUM.trans ((le_perfectCore_of_perfect hMC hMperf).trans (by
    rw [hsym]
    exact (perfectCore_le _).trans inf_le_left))
  have hUL : U ≤ L := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hcardU : Nat.card U = Nat.card (U₀ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) := by
    rw [hU, card_map_of_injective L.subtype_injective,
      card_map_of_injective e.symm.injective]
  have hcardL' : Nat.card L' = Nat.card (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    (Nat.card_congr (conjugateMulEquiv L g).toEquiv).symm.trans (Nat.card_congr e.toEquiv)
  have hcardL : Nat.card L = Nat.card (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    Nat.card_congr e.toEquiv
  have hU₀card := U₀.card_eq_multiplicity
  set U'S : Sylow 2 L' := Sylow.ofCard (U.subgroupOf L') (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUL').toEquiv, hcardU, hU₀card, hcardL'])
    with hU'S
  have hU'mem : ∀ u : L', u ∈ (U'S : Subgroup L') ↔ (u : G) ∈ U := fun u => by
    rw [hU'S, Sylow.coe_ofCard, mem_subgroupOf]
  have htN' : t ∈ normalizer (L' : Set G) :=
    LinearPilot.centralizer_conj_le_normalizer_conjugate hCN g
      (mem_centralizer_singleton_iff.2 (by
        rw [show g⁻¹ * t * g = t * (z : G) from hgz]
        calc t * (t * z) = t * t * z := by group
          _ = t * ((z : G) * t) := by rw [ht2, one_mul, hzt, ← mul_assoc, ht2, one_mul]
          _ = (t * z) * t := by group))
  set β : MulAut L' := L'.normalizerMonoidHom ⟨t, htN'⟩ with hβdef
  have hβ : ∀ l : L', ((β l : L') : G) = t * l * t⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L' ⟨t, htN'⟩ l
  have hβ2 : β ^ 2 = 1 := by
    have h1 : (⟨t, htN'⟩ : normalizer (L' : Set G)) ^ 2 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, sq, ht2, OneMemClass.coe_one])
    rw [hβdef, ← map_pow, h1, map_one]
  have hβU : ∀ u ∈ (U'S : Subgroup L'), β u = u := by
    intro u hu
    apply Subtype.ext
    rw [hβ]
    have huL : (u : G) ∈ L := hUL ((hU'mem u).1 hu)
    rw [← mem_centralizer_iff.1 htC _ huL]
    group
  obtain ⟨w, hw⟩ := autU2_plus_of_mulEquiv ((conjugateMulEquiv L g).symm.trans e) (by norm_num)
    U'S β hβ2 hβU
  have hact : ∀ l ∈ L', t * l * t⁻¹ = w * l * (w : G)⁻¹ := by
    intro l hl
    have h := congrArg (fun φ : MulAut L' => ((φ ⟨l, hl⟩ : L') : G)) hw
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [← hβ ⟨l, hl⟩, ← h]
  have hwL' : (w : G) ∈ L' := w.2
  have hL'C : L' ≤ centralizer ({t'} : Set G) := EPilot.conjugate_le_centralizer_conj htC g
  have htt' : t * t' = t' * t := by
    rw [ht', show g⁻¹ * t * g = t * (z : G) from hgz]
    calc t * (t * z) = t * t * z := by group
      _ = t * ((z : G) * t) := by rw [ht2, one_mul, hzt, ← mul_assoc, ht2, one_mul]
      _ = (t * z) * t := by group
  have hm : g * ((w : G)⁻¹ * t) * g⁻¹ ∈
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro l hl
      have h1 := hact _ (EPilot.conj_mem_conjugate hl g)
      calc l * (g * ((w : G)⁻¹ * t) * g⁻¹) =
            g * ((w : G)⁻¹ * (w * (g⁻¹ * l * g) * (w : G)⁻¹) * t) * g⁻¹ := by group
        _ = g * ((w : G)⁻¹ * (t * (g⁻¹ * l * g) * t⁻¹) * t) * g⁻¹ := by rw [h1]
        _ = g * ((w : G)⁻¹ * t) * g⁻¹ * l := by group
    · rw [mem_centralizer_singleton_iff]
      have hwt' : (w : G) * t' = t' * w := mem_centralizer_singleton_iff.1 (hL'C hwL')
      have hwt'' : (w : G)⁻¹ * t' = t' * (w : G)⁻¹ := by
        calc (w : G)⁻¹ * t' = (w : G)⁻¹ * (t' * w) * (w : G)⁻¹ := by group
          _ = (w : G)⁻¹ * (w * t') * (w : G)⁻¹ := by rw [hwt']
          _ = t' * (w : G)⁻¹ := by group
      calc g * ((w : G)⁻¹ * t) * g⁻¹ * t = g * ((w : G)⁻¹ * (t * t')) * g⁻¹ := by
            rw [ht']; group
        _ = g * (((w : G)⁻¹ * t') * t) * g⁻¹ := by rw [htt']; group
        _ = g * ((t' * (w : G)⁻¹) * t) * g⁻¹ := by rw [hwt'']
        _ = t * (g * ((w : G)⁻¹ * t) * g⁻¹) := by rw [ht']; group
  rw [hKt] at hm
  rcases F4Pilot.eq_one_or_eq_of_mem_zpowers ht hm with h1 | h1
  ·
    exfalso
    have htw : t = w := by
      have h3 : (w : G)⁻¹ * t = 1 := by
        have e1 : (w : G)⁻¹ * t = g⁻¹ * (g * ((w : G)⁻¹ * t) * g⁻¹) * g := by group
        rw [e1, h1]
        group
      calc t = w * ((w : G)⁻¹ * t) := by group
        _ = w := by rw [h3, mul_one]
    have hgtL : g * t * g⁻¹ ∈ L := by
      rw [htw]
      exact LinearPilot.mem_conjugate_iff_mul_mul_inv_mem.1 hwL'
    have hle : U.map (MulAut.conj g).toMonoidHom ≤ L := by
      rintro _ ⟨u, hu, rfl⟩
      exact LinearPilot.mem_conjugate_iff_mul_mul_inv_mem.1 (hUL' hu)
    set V : Sylow 2 L := Sylow.ofCard ((U.map (MulAut.conj g).toMonoidHom).subgroupOf L) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
        card_map_of_injective (MulAut.conj g).injective, hcardU, hU₀card, hcardL]) with hV
    refine not_forall_commute_sylow_conj_plus hset (by norm_num) hK hq e htC ht V g⁻¹
      (by rw [inv_inv]; exact hgtL) ?_
    intro v hv
    rw [hV, Sylow.coe_ofCard, mem_subgroupOf] at hv
    obtain ⟨u, hu, hvu⟩ := hv
    have hut : u * t = t * u := mem_centralizer_singleton_iff.1 (hLt (hUL hu))
    have hv' : (v : G) = g * u * g⁻¹ := by
      rw [← hvu]
      rfl
    rw [inv_inv, hv']
    calc g * u * g⁻¹ * (g * t * g⁻¹) = g * (u * t) * g⁻¹ := by group
      _ = g * (t * u) * g⁻¹ := by rw [hut]
      _ = g * t * g⁻¹ * (g * u * g⁻¹) := by group
  ·
    have hwt : (w : G)⁻¹ * t = t' := by
      calc (w : G)⁻¹ * t = g⁻¹ * (g * ((w : G)⁻¹ * t) * g⁻¹) * g := by group
        _ = t' := by rw [h1]
    have hzinv : (z : G)⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have hwz : (w : G) = z := by
      have h2 : (w : G)⁻¹ = z := by
        calc (w : G)⁻¹ = ((w : G)⁻¹ * t) * t⁻¹ := by group
          _ = t * z * t⁻¹ := by rw [hwt, ht', show g⁻¹ * t * g = t * (z : G) from hgz]
          _ = z := by rw [← hzt]; group
      calc (w : G) = ((w : G)⁻¹)⁻¹ := (inv_inv _).symm
        _ = z := by rw [h2, hzinv]
    have hzL' : (z : G) ∈ L' := hwz ▸ hwL'
    refine ⟨g, z, ⟨z.2, hzL'⟩, hgz, ⟨z.2, hz⟩, ⟨hzL', ?_⟩, fun l hl => ?_⟩
    · refine isLongRoot_of_commute_sylow_plus_of_mulEquiv ((conjugateMulEquiv L g).symm.trans e)
        (by norm_num) U'S ?_ ?_
      · intro h0
        have h0' : (z : G) = 1 := congrArg Subtype.val h0
        exact ne_one_of_isLongRoot_plus (by norm_num) hz (by
          rw [show z = 1 from Subtype.ext h0', map_one])
      · intro u hu
        apply Subtype.ext
        obtain ⟨_, ⟨u₀, hu₀, rfl⟩, hu'⟩ := (hU'mem u).1 hu
        simp only [Subgroup.coe_mul]
        rw [← hu']
        exact hcz u₀ (hU₀ u₀ hu₀)
    · rw [hact l hl, hwz]

end TwoSided

section Residual

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem commutator_mem_of_plusImageFieldPart_eq_one {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {S : Subgroup G}
    (hSt : S ≤ centralizer ({t} : Set G))
    (hSE : ∀ (s : G) (hs : s ∈ S), E6Pilot.normalizerAut e ⟨s, hCN (hSt hs)⟩ ∈
      matrixProjectiveImage (coordinateQuadPlus n K))
    (hfp : ∀ (s : G) (hs : s ∈ S), plusImageFieldPart hf hK (by omega) ⟨_, hSE s hs⟩ = 1) :
    ∀ y ∈ S, ∀ z ∈ S, y * z * y⁻¹ * z⁻¹ ∈ L := by
  have hA := card_abelianization_isometries_plus_le_two hf hK hn
  have hO : ∀ (s : G) (hs : s ∈ S),
      E6Pilot.normalizerAut e ⟨s, hCN (hSt hs)⟩ ∈ (isometryConjugationHom _).range :=
    fun s hs => (plusImageFieldPart_eq_one_iff hf hK (by omega) _).1 (hfp s hs)
  intro y hy z hz
  by_cases hyI : E6Pilot.normalizerAut e ⟨y, hCN (hSt hy)⟩ ∈
      inner (matrixProjectiveDerived (coordinateQuadPlus n K))
  · obtain ⟨l, hl, hyl⟩ :=
      exists_eq_or_eq_mul_of_normalizerAut_mem_inner e ht hKt hCN (hSt hy) hyI
    exact LinearPilot.commutator_mem_of_eq_or_eq_mul hl hyl (hCN (hSt hz)) (hSt hz)
  by_cases hzI : E6Pilot.normalizerAut e ⟨z, hCN (hSt hz)⟩ ∈
      inner (matrixProjectiveDerived (coordinateQuadPlus n K))
  · obtain ⟨l, hl, hzl⟩ :=
      exists_eq_or_eq_mul_of_normalizerAut_mem_inner e ht hKt hCN (hSt hz) hzI
    have h := LinearPilot.commutator_mem_of_eq_or_eq_mul hl hzl (hCN (hSt hy)) (hSt hy)
    have e' : y * z * y⁻¹ * z⁻¹ = (z * y * z⁻¹ * y⁻¹)⁻¹ := by group
    rw [e']
    exact L.inv_mem h
  have hd : z⁻¹ * y ∈ S := S.mul_mem (S.inv_mem hz) hy
  have hdI : E6Pilot.normalizerAut e ⟨z⁻¹ * y, hCN (hSt hd)⟩ ∈
      inner (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    have h1 : (⟨z⁻¹ * y, hCN (hSt hd)⟩ : normalizer (L : Set G)) =
        (⟨z, hCN (hSt hz)⟩ : normalizer (L : Set G))⁻¹ * ⟨y, hCN (hSt hy)⟩ := rfl
    rw [h1, map_mul, map_inv]
    exact inv_mul_mem_inner_of_not_mem _ hA (hO z hz) (hO y hy) hzI hyI
  obtain ⟨l, hl, hdl⟩ := exists_eq_or_eq_mul_of_normalizerAut_mem_inner e ht hKt hCN (hSt hd) hdI
  have h := LinearPilot.commutator_mem_of_eq_or_eq_mul hl hdl (hCN (hSt hz)) (hSt hz)
  have e' : y * z * y⁻¹ * z⁻¹ = z * ((z⁻¹ * y) * z * (z⁻¹ * y)⁻¹ * z⁻¹) * z⁻¹ := by group
  rw [e']
  exact (mem_normalizer_iff.1 (hCN (hSt hz)) _).1 h

theorem exists_conj_eq_mul_longRoot_plus_four_of_residual (hset : SeitzSetting G L) {f : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hFR : NonFieldCoresRigidE (matrixProjectiveImage (coordinateQuadPlus 4 K))
      (plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num)))
    (hRC : FieldRecentreInE (matrixProjectiveImage (coordinateQuadPlus 4 K))
      (plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num))
      (IsLongRoot (coordinateQuadPlus 4 K)))
    (S : Sylow 2 G) (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (hcomm : ∃ y ∈ (S : Subgroup G), ∃ w ∈ (S : Subgroup G), y * w * y⁻¹ * w⁻¹ ∉ L) :
    ∃ (g : G) (z : L), IsLongRoot _ (e z) ∧ g⁻¹ * t * g = t * (z : G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  have htC := mem_centralizer_of_inf_eq hKt
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hOut := isSolvable_outer_of_mulEquiv_plus (by norm_num) hf hK e
  have hB : IsPGroup 2 (((S : Subgroup G).subgroupOf (normalizer (L : Set G))).map
      (E6Pilot.normalizerAut e)) :=
    (S.isPGroup'.comap_of_injective _ (normalizer (L : Set G)).subtype_injective).map _
  obtain ⟨δ, hδ⟩ := conjIntoIn_plusFour hf hK _ hB
  have hSE : ∀ (s : G) (hs : s ∈ (S : Subgroup G)),
      E6Pilot.normalizerAut (e.trans δ) ⟨s, hCN (hSt hs)⟩ ∈
        matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    intro s hs
    rw [normalizerAut_trans]
    exact hδ ⟨_, ⟨⟨s, hCN (hSt hs)⟩, mem_subgroupOf.2 hs, rfl⟩, rfl⟩
  have hS : ∃ (s : G) (hs : s ∈ (S : Subgroup G)),
      plusImageFieldPart hf hK (by norm_num) ⟨_, hSE s hs⟩ ≠ 1 := by
    by_contra hno
    push Not at hno
    obtain ⟨y, hy, w, hw, hyw⟩ := hcomm
    exact hyw (commutator_mem_of_plusImageFieldPart_eq_one hf hK le_rfl (e.trans δ) ht hKt hCN
      hSt hSE hno y hy w hw)
  obtain ⟨h, z, hz, hhz⟩ := exists_conj_eq_mul_of_residual_E hset hOut (e.trans δ) _ _
    (IsLongRoot (coordinateQuadPlus 4 K)) (conjIntoIn_plusFour hf hK)
    (fusionStableIn_plusFour hf hK) (isLongRoot_map_plus (by norm_num)) hFR hRC ht hKt hCN S hSt
    hSE hS
  refine ⟨h, z, ?_, hhz⟩
  have h1 := isLongRoot_map_plus (by norm_num) δ.symm _ hz
  rwa [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1

end Residual

@[expose] def OmegaPlusFourResidualMatrixInput : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f), 2 ≤ f →
    Even f →
      NonFieldCoresRigidE (matrixProjectiveImage (coordinateQuadPlus 4 K))
          (plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num)) ∧
        FieldRecentreInE (matrixProjectiveImage (coordinateQuadPlus 4 K))
          (plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num))
          (IsLongRoot (coordinateQuadPlus 4 K))

theorem omegaPlusFourResidualInput_of_matrixInput (h : OmegaPlusFourResidualMatrixInput) :
    OmegaPlusFourResidualInput := by
  intro G _ _ L hset f K _ _ _ hK hf2 hfe e t ht hKt hres
  obtain ⟨S, hSt, hcomm⟩ := hres
  obtain ⟨hFR, hRC⟩ := h f K hK hf2 hfe
  have hq := (LinearPilot.four_le_card_iff_two_le hK).2 hf2
  obtain ⟨g, z, hz, hgz⟩ :=
    exists_conj_eq_mul_longRoot_plus_four_of_residual hset hK e ht hKt hFR hRC S hSt hcomm
  exact exists_conj_eq_mul_longRoot_twoSided_plus_four_of_oneSided hset hK hq e ht hKt hz hgz

end CFSG.SeitzReduction.OmegaPilot
