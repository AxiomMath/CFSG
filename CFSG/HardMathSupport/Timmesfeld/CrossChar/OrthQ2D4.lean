module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Rank2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Family8
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightResidualStable
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthD4Reduce

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Solomon.LocalBalance Module CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.RankThree.PartOne CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Census CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveImage)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus projectivePointFamily coordinatePlusWitnessEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (plusCX plusCXstar coordinate_plus_pointFamily_orbit_subset)
open scoped Pointwise

section Abstract

theorem isElemAbelian_map_three {M M' : Type*} [Group M] [Group M'] (f : M →* M')
    {E : Subgroup M} (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem isElemAbelian_of_le_three {M : Type*} [Group M] {E F : Subgroup M}
    (hE : IsElemAbelian 3 E) (h : F ≤ E) : IsElemAbelian 3 F := CFSG.Open.IsElemAbelian.mono hE h

theorem pow_smul_mod_three {G X : Type*} [Group G] [MulAction G X] {g : G} {a : X}
    (h3 : g ^ 3 • a = a) (n : ℕ) : g ^ n • a = g ^ (n % 3) • a := by
  have hq : ∀ q : ℕ, (g ^ 3) ^ q • a = a := by
    intro q
    induction q with
    | zero => rw [pow_zero, one_smul]
    | succ q ih => rw [pow_succ, mul_smul, h3, ih]
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, mul_smul, pow_mul, hq]

theorem mod_three_of_coprime {n : ℕ} (hn : Nat.Coprime 3 n) : n % 3 = 1 ∨ n % 3 = 2 := by
  have h0 : n % 3 ≠ 0 := by
    intro h0
    have := Nat.Coprime.eq_one_of_dvd hn (Nat.dvd_of_mod_eq_zero h0)
    norm_num at this
  omega

theorem exists_fixed_of_three {G X : Type*} [Group G] [MulAction G X] {g : G}
    (hg : Nat.Coprime 3 (orderOf g)) {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha' : g • a = a ∨ g • a = b ∨ g • a = c) (hb' : g • b = a ∨ g • b = b ∨ g • b = c)
    (hc' : g • c = a ∨ g • c = b ∨ g • c = c) : g • a = a ∨ g • b = b ∨ g • c = c := by
  by_contra hno
  push Not at hno
  obtain ⟨ha, hb, hc⟩ := hno
  have hinj : Function.Injective (fun x : X => g • x) := MulAction.injective g
  obtain ⟨h1, h2, h3⟩ : g • a ≠ a ∧ g ^ 2 • a ≠ a ∧ g ^ 3 • a = a := by
    rcases ha' with h | h | h
    · exact absurd h ha
    · have hgb : g • b = c := by
        rcases hb' with h' | h' | h'
        · exfalso
          rcases hc' with h'' | h'' | h''
          · exact hbc (hinj (h'.trans h''.symm))
          · exact hac (hinj (h.trans h''.symm))
          · exact hc h''
        · exact absurd h' hb
        · exact h'
      have hgc : g • c = a := by
        rcases hc' with h'' | h'' | h''
        · exact h''
        · exact absurd (hinj (h''.trans h.symm)) (Ne.symm hac)
        · exact absurd h'' hc
      refine ⟨ha, ?_, ?_⟩
      · rw [pow_two, mul_smul, h, hgb]
        exact Ne.symm hac
      · rw [pow_three, mul_smul, mul_smul, h, hgb, hgc]
    · have hgc : g • c = b := by
        rcases hc' with h'' | h'' | h''
        · exfalso
          rcases hb' with h' | h' | h'
          · exact hbc (hinj (h'.trans h''.symm))
          · exact hb h'
          · exact hab (hinj (h.trans h'.symm))
        · exact h''
        · exact absurd h'' hc
      have hgb : g • b = a := by
        rcases hb' with h' | h' | h'
        · exact h'
        · exact absurd h' hb
        · exact absurd (hinj (h'.trans h.symm)) (Ne.symm hab)
      refine ⟨ha, ?_, ?_⟩
      · rw [pow_two, mul_smul, h, hgc]
        exact Ne.symm hab
      · rw [pow_three, mul_smul, mul_smul, h, hgc, hgb]
  have h4 : g ^ orderOf g • a = a := by rw [pow_orderOf_eq_one, one_smul]
  rw [pow_smul_mod_three h3] at h4
  rcases mod_three_of_coprime hg with h5 | h5 <;> rw [h5] at h4
  · rw [pow_one] at h4
    exact h1 h4
  · exact h2 h4

theorem smul_eq_of_commute_of_three {G X : Type*} [Group G] [MulAction G X] {g t : G}
    (hgt : Commute g t) (ht3 : t ^ 3 = 1) {a : X} (hta : t • a ≠ a)
    (hg : Nat.Coprime 3 (orderOf g)) (hga : g • a = a ∨ g • a = t • a ∨ g • a = t ^ 2 • a) :
    g • a = a := by
  have ht2 : t ^ 2 • a ≠ a := fun h => hta (by
    calc t • a = t • (t ^ 2 • a) := by rw [h]
      _ = t ^ 3 • a := by rw [← mul_smul, ← pow_succ']
      _ = a := by rw [ht3, one_smul])
  have htmod : ∀ k : ℕ, t ^ k = t ^ (k % 3) := fun k => by
    conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, ht3, one_pow, mul_one]
  have hdesc : ∀ m : ℕ, g • a = t ^ m • a → ∀ n : ℕ, g ^ n • a = t ^ (m * n) • a := by
    intro m hm n
    induction n with
    | zero => rw [pow_zero, mul_zero, pow_zero]
    | succ n ih =>
      rw [pow_succ, mul_smul, hm, ← mul_smul, ((hgt.pow_left n).pow_right m).eq, mul_smul, ih,
        ← mul_smul, ← pow_add, mul_add, mul_one, add_comm]
  have hk := mod_three_of_coprime hg
  rcases hga with h | h | h
  · exact h
  · exfalso
    have h1 := hdesc 1 (by rw [pow_one]; exact h) (orderOf g)
    rw [pow_orderOf_eq_one, one_smul, one_mul, htmod] at h1
    rcases hk with h5 | h5 <;> rw [h5] at h1
    · rw [pow_one] at h1
      exact hta h1.symm
    · exact ht2 h1.symm
  · exfalso
    have h1 := hdesc 2 h (orderOf g)
    rw [pow_orderOf_eq_one, one_smul, htmod] at h1
    rcases hk with h5 | h5
    · rw [show 2 * orderOf g % 3 = 2 by omega] at h1
      exact ht2 h1.symm
    · rw [show 2 * orderOf g % 3 = 1 by omega, pow_one] at h1
      exact hta h1.symm

theorem conj_mem_localDeltaIn_map {M : Type*} [Group M] {p : ℕ} (β : M) {H D : Subgroup M} {g : M}
    (hg : g ∈ localDeltaIn p H D) :
    β * g * β⁻¹ ∈ localDeltaIn p (H.map (MulAut.conj β).toMonoidHom)
      (D.map (MulAut.conj β).toMonoidHom) :=
  map_localDeltaIn_le p (MulAut.conj β).toMonoidHom (MulAut.conj β).injective H D ⟨g, hg, rfl⟩

end Abstract

section D4

variable {K : Type} [Field K] [Finite K]

theorem mulAut_congr_conj {T T' : Type*} [Group T] [Group T'] (φ : T ≃* T') (t : T) :
    MulAut.congr φ (MulAut.conj t) = MulAut.conj (φ t) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem map_congr_le_innerAut {T T' : Type*} [Group T] [Group T'] (φ : T ≃* T')
    {A : Subgroup (MulAut T)} (hA : A ≤ innerAut T) :
    A.map (MulAut.congr φ).toMonoidHom ≤ innerAut T' := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨t, rfl⟩ := hA ha
  exact ⟨φ t, (mulAut_congr_conj φ t).symm⟩

theorem innerAut_le_map_congr {T T' : Type*} [Group T] [Group T'] (φ : T ≃* T')
    {H : Subgroup (MulAut T)} (hH : innerAut T ≤ H) :
    innerAut T' ≤ H.map (MulAut.congr φ).toMonoidHom := by
  rintro _ ⟨t', rfl⟩
  refine ⟨MulAut.conj (φ.symm t'), hH ⟨_, rfl⟩, ?_⟩
  change MulAut.congr φ (MulAut.conj (φ.symm t')) = _
  rw [mulAut_congr_conj, MulEquiv.apply_symm_apply]

theorem d4two_eq_one_of_mem_image (hK : Nat.card K = 2)
    {D : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 3)
    (hDinn : D ≤ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    {H : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))}
    (hH : innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤ H)
    {g : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hg : g ∈ localDeltaIn 3 H D) (hgE : g ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) :
    g = 1 := by
  have hd : 0 < 2 * 4 := by norm_num
  set φ := KCOrthogonalAut.coordBridge (coordinateQuadPlus 4 K) hd with hφ
  obtain ⟨hQ, hT⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
      (n := 4) (K := K) (by norm_num)
  have h8 : 8 ≤ finrank K (Fin (2 * 4) → K) := by rw [Module.finrank_fin_fun]
  have hg' := map_localDeltaIn_le 3 (MulAut.congr φ).toMonoidHom (MulAut.congr φ).injective H D
    ⟨g, hg, rfl⟩
  have hsemi : KCOrthogonalAut.InducedBySemilinear (coordinateQuadPlus 4 K)
      (MulAut.congr φ g) := by
    have hback : MulAut.congr φ.symm (MulAut.congr φ g) = g := by
      ext y
      simp [MulAut.congr_apply]
    obtain ⟨σ, F, hF, μ, hμ, hQF, hind⟩ :=
      KCOrthogonalAut.exists_semilin_of_mem_matrixProjectiveImage _ hd (MulAut.congr φ g)
        (by rw [hback]; exact hgE)
    exact ⟨σ, F, hF, μ, hμ, hQF, hind⟩
  obtain ⟨G, hGO, hGg⟩ := exists_isometry_of_inducedBySemilinear hK hsemi
  have h1 := orth2_eq_one_of_isometry_eight hK hQ hT h8 (isElemAbelian_map_three _ hD)
    (by rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective]; exact hcard)
    (map_congr_le_innerAut φ hDinn) (innerAut_le_map_congr φ hH) hg' hGO
    (fun y => by obtain ⟨_, h⟩ := hGg y; exact h)
  exact (MulAut.congr φ).injective (h1.trans (map_one _).symm)

theorem d4two_eq_one_of_inner (hK : Nat.card K = 2)
    {D : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2)
    (hDinn : D ≤ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    {H : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))}
    (hH : innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤ H)
    {g : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hg : g ∈ localDeltaIn 3 H D)
    (hgin : g ∈ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) : g = 1 := by
  have hd : 0 < 2 * 4 := by norm_num
  set φ := KCOrthogonalAut.coordBridge (coordinateQuadPlus 4 K) hd with hφ
  obtain ⟨hQ, hT⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus
      (n := 4) (K := K) (by norm_num)
  have h8 : finrank K (Fin (2 * 4) → K) = 8 := by rw [Module.finrank_fin_fun]
  have hg' := map_localDeltaIn_le 3 (MulAut.congr φ).toMonoidHom (MulAut.congr φ).injective H D
    ⟨g, hg, rfl⟩
  have hgin' : MulAut.congr φ g ∈ innerAut (ProjOrthDerived (coordinateQuadPlus 4 K)) := by
    obtain ⟨t, rfl⟩ := hgin
    exact ⟨φ t, (mulAut_congr_conj φ t).symm⟩
  have h1 := orth2_eq_one_of_inner_rank_two hK hQ hT h8 (isElemAbelian_map_three _ hD)
    (by rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective]; exact hcard)
    (map_congr_le_innerAut φ hDinn) (innerAut_le_map_congr φ hH) hg' hgin'
  exact (MulAut.congr φ).injective (h1.trans (map_one _).symm)

theorem d4two_mem_innerAut_of_mem_image (hK : Nat.card K = 2)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hβ : β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (h3 : β ^ 3 = 1) :
    β ∈ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
  have : CharP K 2 := charP_two_of_card hK
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  rcases CFSG.SeitzReduction.OmegaPilot.smul_plusCX_of_mem_image hβ with ⟨hX, -⟩ | ⟨hX, hX'⟩
  · obtain ⟨x, hx⟩ := CFSG.SeitzReduction.OmegaPilot.eq_conj_of_smul_plusCX_of_fp_eq_one le_rfl
      hK' hβ hX (KCSpFull.ringEquiv_eq_refl_of_card_two hK _)
    exact ⟨x, hx.symm⟩
  · exfalso
    apply CFSG.SeitzReduction.OmegaPilot.plusCX_ne_plusCXstar 4 K (by norm_num)
    have h1 : β ^ 3 • plusCX 4 K = plusCXstar 4 K (by norm_num) := by
      rw [pow_three, mul_smul, mul_smul, hX, hX', hX]
    rw [h3, one_smul] at h1
    exact h1

theorem ncard_triple_le {α : Type*} (a b c : α) : ({a, b, c} : Set α).ncard ≤ 3 := by
  have h1 := Set.ncard_insert_le a ({b, c} : Set α)
  have h2 := Set.ncard_insert_le b ({c} : Set α)
  rw [Set.ncard_singleton] at h2
  omega

theorem d4two_isLocallyBalancedAbs_three (hK : Nat.card K = 2) :
    IsLocallyBalancedAbs 3 3 (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
  classical
  have : CharP K 2 := charP_two_of_card hK
  have hp : Nat.Prime 3 := Nat.prime_three
  intro D hD hcard H hH _
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  set E := matrixProjectiveImage (coordinateQuadPlus 4 K) with hEdef
  set P := projectivePointFamily (coordinateQuadPlus 4 K) with hPdef
  set X := plusCX 4 K with hXdef
  set X' := plusCXstar 4 K (by norm_num) with hX'def
  set O := MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) P
    with hOdef
  have hmemE : ∀ δ, δ ∈ E ↔ δ • P = P :=
    CFSG.SeitzReduction.OmegaPilot.mem_image_iff_smul_pointFamily le_rfl
  have hsub : O ⊆ {P, X, X'} := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
  have hXX' : X ≠ X' := CFSG.SeitzReduction.OmegaPilot.plusCX_ne_plusCXstar 4 K (by norm_num)
  have hDinn : ∀ d ∈ D, d ∈ E → d ∈ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
    fun d hd hdE => d4two_mem_innerAut_of_mem_image hK hdE (hD.2 d hd)
  obtain ⟨d₁, hd₁, hd₁1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have : D = ⊥ := eq_bot_iff.2 fun d hd => (Subgroup.mem_bot).2 (hall d hd)
    rw [this, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hgk : Nat.Coprime 3 (orderOf g) := coprime_orderOf_of_mem_localDeltaIn hp hg hd₁ hd₁1
  have hO13 : O.ncard = 1 ∨ O.ncard = 3 :=
    CFSG.SeitzReduction.OmegaPilot.orbit_pointFamily_ncard_four (K := K)
  rcases hO13 with h1 | h3
  ·
    have hall : ∀ δ, δ ∈ E := by
      intro δ
      rw [hmemE]
      have hPO : P ∈ O := MulAction.mem_orbit_self P
      have hδO : δ • P ∈ O := MulAction.mem_orbit P δ
      obtain ⟨Y, hY⟩ := Set.ncard_eq_one.1 h1
      rw [hY, Set.mem_singleton_iff] at hPO hδO
      exact hδO.trans hPO.symm
    exact d4two_eq_one_of_mem_image hK hD hcard (fun d hd => hDinn d hd (hall d)) hH hg (hall g)
  have hO3 : O = {P, X, X'} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [h3]; exact ncard_triple_le P X X')
  have hPX : P ≠ X := fun h => by
    have h4 := h3
    rw [hO3, ← h, Set.insert_eq_of_mem (Set.mem_insert P _)] at h4
    have := Set.ncard_insert_le P ({X'} : Set _)
    rw [Set.ncard_singleton] at this
    omega
  have hPX' : P ≠ X' := fun h => by
    have h4 := h3
    rw [hO3, ← h, Set.insert_comm, Set.insert_eq_of_mem (Set.mem_singleton P)] at h4
    have := Set.ncard_insert_le X ({P} : Set _)
    rw [Set.ncard_singleton] at this
    omega
  have hgO : ∀ Y ∈ O, g • Y ∈ O := fun Y hY => by
    obtain ⟨β, rfl⟩ := hY
    exact ⟨g * β, mul_smul _ _ _⟩
  have hmem3 : ∀ Y ∈ O, Y = P ∨ Y = X ∨ Y = X' := fun Y hY => by
    rw [hO3] at hY
    simpa using hY
  by_cases hDE : ∀ d ∈ D, d ∈ E
  ·
    have hDinn' : D ≤ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
      fun d hd => hDinn d hd (hDE d hd)
    have hPO : P ∈ O := MulAction.mem_orbit_self P
    have hXO : X ∈ O := by rw [hO3]; simp
    have hX'O : X' ∈ O := by rw [hO3]; simp
    obtain ⟨Y, hYO, hgY⟩ : ∃ Y ∈ O, g • Y = Y := by
      rcases exists_fixed_of_three hgk hPX hPX' hXX' (hmem3 _ (hgO _ hPO))
          (hmem3 _ (hgO _ hXO)) (hmem3 _ (hgO _ hX'O)) with h | h | h
      · exact ⟨P, hPO, h⟩
      · exact ⟨X, hXO, h⟩
      · exact ⟨X', hX'O, h⟩
    obtain ⟨β, rfl⟩ := hYO
    have hg'E : β⁻¹ * g * β⁻¹⁻¹ ∈ E := by
      rw [hmemE, inv_inv, mul_smul, mul_smul]
      change β⁻¹ • g • β • P = P
      rw [hgY, inv_smul_smul]
    have hg' := conj_mem_localDeltaIn_map β⁻¹ hg
    have hD' : D.map (MulAut.conj β⁻¹).toMonoidHom ≤
        innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨t, rfl⟩ := hDinn' hd
      refine ⟨β⁻¹ t, ?_⟩
      change MulAut.conj (β⁻¹ t) = β⁻¹ * MulAut.conj t * β⁻¹⁻¹
      rw [CFSG.SeitzReduction.OmegaPilot.mul_conj_mul_inv]
    have hH' : innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) ≤
        H.map (MulAut.conj β⁻¹).toMonoidHom := by
      rintro _ ⟨t, rfl⟩
      refine ⟨MulAut.conj (β t), hH ⟨_, rfl⟩, ?_⟩
      change β⁻¹ * MulAut.conj (β t) * β⁻¹⁻¹ = MulAut.conj t
      rw [CFSG.SeitzReduction.OmegaPilot.mul_conj_mul_inv, MulAut.inv_apply,
        MulEquiv.symm_apply_apply]
    have h1 := d4two_eq_one_of_mem_image hK (isElemAbelian_map_three _ hD)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj β⁻¹).injective]; exact hcard)
      hD' hH' hg' hg'E
    have h2 : g = β⁻¹⁻¹ * (β⁻¹ * g * β⁻¹⁻¹) * β⁻¹ := by group
    rw [h2, h1, mul_one, inv_mul_cancel]
  ·
    push Not at hDE
    obtain ⟨t, htD, htE⟩ := hDE
    have htP : t • P ≠ P := fun h => htE ((hmemE t).2 h)
    have ht3 : t ^ 3 = 1 := hD.2 t htD
    have hgt : Commute g t := commute_of_mem_localDeltaIn hg htD
    have ht2P : t ^ 2 • P ≠ P := fun h => htP (by
      calc t • P = t • (t ^ 2 • P) := by rw [h]
        _ = t ^ 3 • P := by rw [← mul_smul, ← pow_succ']
        _ = P := by rw [ht3, one_smul])
    have htt2 : t • P ≠ t ^ 2 • P := fun h => htP (by
      have h' : t⁻¹ • t • P = t⁻¹ • t ^ 2 • P := by rw [h]
      rw [inv_smul_smul, ← mul_smul, pow_two, ← mul_assoc, inv_mul_cancel, one_mul] at h'
      exact h'.symm)
    have hOt : ({P, t • P, t ^ 2 • P} : Set _) = O := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.finite_of_ncard_pos (by rw [h3]; norm_num))
      · rintro _ (rfl | rfl | rfl)
        · exact MulAction.mem_orbit_self P
        · exact MulAction.mem_orbit P t
        · exact MulAction.mem_orbit P (t ^ 2)
      · rw [h3, Set.ncard_eq_three.2 ⟨P, t • P, t ^ 2 • P, Ne.symm htP, Ne.symm ht2P, htt2, rfl⟩]
    have hgP : g • P = P := by
      refine smul_eq_of_commute_of_three hgt ht3 htP hgk ?_
      have : g • P ∈ O := MulAction.mem_orbit P g
      rw [← hOt] at this
      simpa using this
    have hgE : g ∈ E := (hmemE g).2 hgP
    have hgtP : g • t • P = t • P := by rw [← mul_smul, hgt.eq, mul_smul, hgP]
    have hgX : g • X = X := by
      rcases hmem3 _ (MulAction.mem_orbit P t) with h | h | h
      · exact absurd h htP
      · rw [← h]
        exact hgtP
      · have hgX'' : g • X' = X' := by rw [← h]; exact hgtP
        rcases CFSG.SeitzReduction.OmegaPilot.smul_plusCX_of_mem_image hgE with ⟨h', -⟩ | ⟨-, h'⟩
        · exact h'
        · exfalso
          have h'' : g • X' = X := h'
          exact hXX' (h''.symm.trans hgX'')
    have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
    obtain ⟨x, hx⟩ := CFSG.SeitzReduction.OmegaPilot.eq_conj_of_smul_plusCX_of_fp_eq_one le_rfl
      hK' hgE hgX (KCSpFull.ringEquiv_eq_refl_of_card_two hK _)
    have hginn : g ∈ innerAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) :=
      ⟨x, hx.symm⟩
    have hidx : E.index ≤ 3 := by
      have hstab : E = MulAction.stabilizer
          (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) P := by
        ext δ
        exact hmemE δ
      rw [hstab, MulAction.index_stabilizer, ← hOdef, h3]
    have hge := card_inf_ge_of_index_le hp hcard hidx
    have hdvd : Nat.card (D ⊓ E : Subgroup _) ∣ 3 ^ 3 :=
      hcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card (D ⊓ E : Subgroup _) ≠ 3 ^ 3 := fun h => htE (by
      have heq : D ⊓ E = D := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard])
      have htDE : t ∈ D ⊓ E := by rw [heq]; exact htD
      exact htDE.2)
    have h9 : Nat.card (D ⊓ E : Subgroup _) = 3 ^ 2 := by
      obtain ⟨j, hj, hjk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      rw [hjk] at hge hne ⊢
      interval_cases j
      · norm_num at hge
      · norm_num at hge
      · rfl
      · exact absurd rfl hne
    exact d4two_eq_one_of_inner hK (isElemAbelian_of_le_three hD inf_le_left) h9
      (fun d hd => hDinn d hd.1 hd.2) hH (localDeltaIn_antitone H inf_le_left hg) hginn

end D4

section Family

@[expose] def regimeDFourTwo (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ q : TauCeti.PrimePower, idx.1 = .D 4 q ∧ q.card = 2

theorem crossCharFamAt_D_four_two : CrossCharFamAt .D regimeDFourTwo := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨rfl, q, hd, hq2⟩
  change d = _ at hd
  subst hd
  set F := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) with hF
  have : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hK : Nat.card F = 2 := card_fixedField_eq_two_of_card (Or.inl rfl) hq2
  let e₁ := Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv
  exact IsLocallyBalancedAbs.of_mulEquiv (coordinatePlusWitnessEquiv F e₁)
    (d4two_isLocallyBalancedAbs_three hK)

theorem crossCharFamAt_D_two : CrossCharFamAt .D fun idx p =>
    p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .D r q ∧ q.card = 2 := by
  rintro idx hk p hp hp2 hc ⟨h3, r, q, hd, hq⟩
  have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp (hd ▸ idx.2)).1
  rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
  · exact crossCharFamAt_D_four_two idx hk p hp hp2 hc ⟨h3, q, hd, hq⟩
  · exact crossCharFamAt_D_two_five idx hk p hp hp2 hc ⟨h3, r, q, hd, hq, hr5⟩

theorem crossCharFamAt_D_two_lt_six : CrossCharFamAt .D fun idx p =>
    p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .D r q ∧ q.card = 2 ∧ r < 6 := by
  rintro idx hk p hp hp2 hc ⟨h3, r, q, hd, hq, -⟩
  exact crossCharFamAt_D_two idx hk p hp hp2 hc ⟨h3, r, q, hd, hq⟩

theorem crossCharFamAt_twistedD_two_lt_six : CrossCharFamAt .twistedD fun idx p =>
    p = 3 ∧ ∃ (r : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedD r q ∧ q.card = 2 ∧ r < 6 := by
  rintro idx hk p hp hp2 hc ⟨h3, r, q, hd, hq, -⟩
  exact crossCharFamAt_twistedD_two idx hk p hp hp2 hc ⟨h3, r, q, hd, hq⟩

end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
