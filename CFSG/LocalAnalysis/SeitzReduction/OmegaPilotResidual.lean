module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualRigid
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Basic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualField

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.ClassicalGroups.Orthogonal (rootGroup)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)

section TwoCentral

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem ne_one_of_isLongRoot_plus (hn : 3 ≤ n)
    {z : matrixProjectiveDerived (coordinateQuadPlus n K)} (hz : IsLongRoot _ z) : z ≠ 1 := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_pairs_plus (K := K) hn
  have hQ := (regular_coordinateQuadPlus n K hn).1
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (isConj_of_isLongRoot_plus hn (isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃) hz)
  intro h1
  apply rootPairElt_ne_one hQ h₁₂ h₁₃ h₂₃
  have e1 : rootPairElt hQ h₁₂ h₁₃ h₂₃ = c⁻¹ * (c * rootPairElt hQ h₁₂ h₁₃ h₂₃ * c⁻¹) * c := by
    group
  rw [e1, hc, h1]
  group

theorem exists_sylow_commute_of_isLongRoot_plus (hn : 3 ≤ n)
    {z : matrixProjectiveDerived (coordinateQuadPlus n K)} (hz : IsLongRoot _ z) :
    ∃ U : Sylow 2 (matrixProjectiveDerived (coordinateQuadPlus n K)),
      ∀ u ∈ (U : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))), u * z = z * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 := ne_one_of_isLongRoot_plus hn hz
  obtain ⟨u, w, -, -, huw, -, E, hE, hEz⟩ := id hz
  have hzR : z ∈ rootGroupBar (Q := coordinateQuadPlus n K) u := by
    refine ⟨E, ?_, hEz⟩
    show (E : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈ rootGroup (coordinateQuadPlus n K) u
    rw [hE]
    exact CFSG.ClassicalGroups.Orthogonal.eichler_mem_rootGroup huw
  obtain ⟨U₀, hU₀⟩ := (isPGroup_rootGroupBar (Q := coordinateQuadPlus n K) u).exists_le_sylow
  have hzU₀ : z ∈ (U₀ : Subgroup _) := hU₀ hzR
  have : Nontrivial (U₀ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))) :=
    ⟨⟨⟨z, hzU₀⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  have := U₀.isPGroup'.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne
    (1 : Subgroup.center (U₀ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))))
  have hcU : ∀ v ∈ (U₀ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))),
      v * ((c : U₀) : matrixProjectiveDerived (coordinateQuadPlus n K)) =
        ((c : U₀) : matrixProjectiveDerived (coordinateQuadPlus n K)) * v := by
    intro v hv
    have h := Subgroup.mem_center_iff.mp c.2 ⟨v, hv⟩
    exact congrArg Subtype.val h
  have hc1' : ((c : U₀) : matrixProjectiveDerived (coordinateQuadPlus n K)) ≠ 1 := by
    intro h
    apply hc1
    exact Subtype.ext (Subtype.ext h)
  have hcL := isLongRoot_of_commute_sylow_plus hn U₀ hc1' hcU
  obtain ⟨h, hh⟩ := isConj_iff.mp (isConj_of_isLongRoot_plus hn hcL hz)
  refine ⟨h • U₀, fun v hv => ?_⟩
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv] at hv
  have h1 := hcU _ hv
  rw [← hh]
  calc v * (h * c * h⁻¹) = h * ((h⁻¹ * v * h) * c) * h⁻¹ := by group
    _ = h * (c * (h⁻¹ * v * h)) * h⁻¹ := by rw [h1]
    _ = h * c * h⁻¹ * v := by group

theorem perfect_centralizer_plus (hn : 5 ≤ n) (hq : 4 ≤ Nat.card K)
    {z : matrixProjectiveDerived (coordinateQuadPlus n K)} (hz : IsLongRoot _ z) :
    ⁅centralizer ({z} : Set (matrixProjectiveDerived (coordinateQuadPlus n K))),
      centralizer ({z} : Set (matrixProjectiveDerived (coordinateQuadPlus n K)))⁆ =
      centralizer ({z} : Set (matrixProjectiveDerived (coordinateQuadPlus n K))) := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  set z₀ := plusRootElt K (by omega : 3 ≤ n) h01 h02 h12 with hz₀def
  have hz₀ : IsLongRoot _ z₀ := isLongRoot_rootPairElt _ _ _ _
  have hC₀ := commutator_centralizer_rootPairElt (K := K) hn hq h01 h02 h12
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_isLongRoot_plus (by omega) hz₀ hz)
  have hmap : centralizer ({z} : Set (matrixProjectiveDerived (coordinateQuadPlus n K))) =
      (centralizer ({z₀} : Set (matrixProjectiveDerived (coordinateQuadPlus n K)))).map
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

end TwoCentral

section TwoSided

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_longRoot_twoSided_plus_of_oneSided (hset : SeitzSetting G L)
    {n f : ℕ} (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
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
  have hOut := isSolvable_outer_of_mulEquiv_plus (by omega) hf hK e
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
  obtain ⟨U₀, hU₀⟩ := exists_sylow_commute_of_isLongRoot_plus (by omega) hz
  set M : Subgroup G :=
    ((centralizer ({e z} : Set (matrixProjectiveDerived (coordinateQuadPlus n K)))).map
      e.symm.toMonoidHom).map L.subtype with hM
  have hMperf : ⁅M, M⁆ = M := by
    rw [hM, ← map_commutator, ← map_commutator, perfect_centralizer_plus hn hq hz]
  have hcz : ∀ c : matrixProjectiveDerived (coordinateQuadPlus n K), c * e z = e z * c →
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
  set U : Subgroup G := ((U₀ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))).map
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
  have hcardU : Nat.card U = Nat.card (U₀ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))) := by
    rw [hU, card_map_of_injective L.subtype_injective,
      card_map_of_injective e.symm.injective]
  have hcardL' : Nat.card L' = Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    (Nat.card_congr (conjugateMulEquiv L g).toEquiv).symm.trans (Nat.card_congr e.toEquiv)
  have hcardL : Nat.card L = Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
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
  obtain ⟨w, hw⟩ := autU2_plus_of_mulEquiv ((conjugateMulEquiv L g).symm.trans e) (by omega)
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
    refine not_forall_commute_sylow_conj_plus hset (by omega) hK hq e htC ht V g⁻¹
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
        (by omega) U'S ?_ ?_
      · intro h0
        have h0' : (z : G) = 1 := congrArg Subtype.val h0
        exact ne_one_of_isLongRoot_plus (by omega) hz (by
          rw [show z = 1 from Subtype.ext h0', map_one])
      · intro u hu
        apply Subtype.ext
        obtain ⟨_, ⟨u₀, hu₀, rfl⟩, hu'⟩ := (hU'mem u).1 hu
        simp only [Subgroup.coe_mul]
        rw [← hu']
        exact hcz u₀ (hU₀ u₀ hu₀)
    · rw [hact l hl, hwz]

end TwoSided

section Plus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_longRoot_plus_of_rigid (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hFR : NonFieldCoresRigid (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn))
    (hRC : FieldRecentreIn (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
      (IsLongRoot (coordinateQuadPlus n K))) :
    ∃ (g : G) (z : L), IsLongRoot _ (e z) ∧ g⁻¹ * t * g = t * (z : G) := by
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  have htC := mem_centralizer_of_inf_eq hKt
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  rcases exists_conj_eq_mul_longRoot_plus_or_residual hset hn hK hq e ht hKt with h |
    ⟨-, S, hSt, hcomm⟩
  · exact h
  · obtain ⟨s, hs, hs1⟩ := exists_orthAutFieldPart_ne_one_of_commutator_not_mem
      (plusRealization hf hK (by omega)) (plusImage_eq_top hn)
      (card_abelianization_isometries_plus_le_two hf hK (by omega)) e ht hKt hCN hSt hcomm
    have hs1' : plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn
        (E6Pilot.normalizerAut e ⟨s, hCN (hSt hs)⟩) ≠ 1 := hs1
    exact exists_conj_eq_mul_of_residual (C := matrixProjectiveDerived (coordinateQuadPlus n K))
      (fp := plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
      (R := IsLongRoot (coordinateQuadPlus n K)) hset
      (isSolvable_outer_of_mulEquiv_plus (by omega) hf hK e) e hFR hRC ht hKt S hSt ⟨s, hs, hs1'⟩

theorem exists_conj_eq_mul_longRoot_twoSided_plus_of_rigid (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 5 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hFR : NonFieldCoresRigid (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn))
    (hRC : FieldRecentreIn (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)
      (IsLongRoot (coordinateQuadPlus n K))) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  obtain ⟨g, z, hz, hgz⟩ := exists_conj_eq_mul_longRoot_plus_of_rigid hset hn hK hq e ht hKt hFR hRC
  exact exists_conj_eq_mul_longRoot_twoSided_plus_of_oneSided hset hn hK hq e ht hKt hz hgz

end Plus

end CFSG.SeitzReduction.OmegaPilot
