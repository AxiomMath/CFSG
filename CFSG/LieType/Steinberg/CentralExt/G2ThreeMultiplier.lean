module

public import CFSG.LieType.Steinberg.CentralExt.WeylLiftKernel
public import CFSG.LieType.Steinberg.CentralExt.FieldThreeF4Multiplier
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LieType.Steinberg.RankTwo.G2Extras
public import CFSG.LieType.Steinberg.RankTwo.G2Comm
public import CFSG.LieType.Steinberg.G2.Perfect

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.CentralExt.AdjointClosed CFSG.LieType.Steinberg.CentralExt.WeylLift

namespace CFSG.LieType.Steinberg.CentralExt.FieldThree

section G2Roots

theorem g2_symm (i j : Fin 2) : Tag.symmetrizedCartan .G2 i j =
    (!![6, -3; -3, 2] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem g2_iform_eq (v w : Fin 2 → ℤ) : iform (τ := .G2) v w =
    6 * v 0 * w 0 - 3 * v 0 * w 1 - 3 * v 1 * w 0 + 2 * v 1 * w 1 := by
  change ∑ i : Fin 2, ∑ j : Fin 2, v i * Tag.symmetrizedCartan .G2 i j * w j = _
  simp only [g2_symm, Fin.sum_univ_two]
  simp
  ring

theorem g2_even_of_cartanCoord {z : Fin (Tag.rank .G2) → ℤ} (hz : ∀ i, 2 ∣ cartanCoord z i)
    (a : Fin (Tag.rank .G2)) : 2 ∣ z a := by
  have hrow : ∀ i : Fin 2, 2 ∣ ∑ j : Fin 2, Tag.cartan .G2 i j * z j := hz
  have h0 := hrow 0
  have h1 := hrow 1
  simp only [Fin.sum_univ_two, Tag.cartan] at h0 h1
  norm_num at h0 h1
  have key : ∀ a : Fin 2, 2 ∣ z a := by
    intro a
    fin_cases a <;> simp <;> omega
  exact key a

@[expose] def g2Cond0 : List ℤ → Bool
  | [a, b] => decide (6 * a - 3 * b = 0)
  | _ => false

@[expose] def g2Cond1 : List ℤ → Bool
  | [a, b] => decide (-3 * a + 2 * b = 0)
  | _ => false

theorem g2_enum0 : ∀ l ∈ Tag.G2.artifactRoots, g2Cond0 l = true → l ∈ [[-1, -2], [1, 2]] := by
  decide

theorem g2_enum1 : ∀ l ∈ Tag.G2.artifactRoots, g2Cond1 l = true → l ∈ [[-2, -3], [2, 3]] := by
  decide

theorem g2_ofFn (δ : Fin 2 → ℤ) : List.ofFn δ = [δ 0, δ 1] := by
  simp [List.ofFn_succ]

theorem g2_orbit_of_path (l : List (Fin (Tag.rank .G2))) {a b : Fin (Tag.rank .G2) → ℤ}
    (ha : ∀ i, reflectPath .G2 l (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) i = a i)
    (hb : ∀ i, reflectPath .G2 l (![2, 3] : Fin 2 → ℤ) i = b i) :
    PairOrbit .G2 (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) ![2, 3] a b := by
  have h := (PairOrbit.base (τ := .G2) (γ₀ := (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ))
    (δ₀ := ![2, 3])).path l
  rwa [funext ha, funext hb] at h

theorem g2_base0 (δ : Fin 2 → ℤ) (hδ : List.ofFn δ ∈ Tag.G2.artifactRoots)
    (h0 : iform (τ := .G2) (Pi.single (0 : Fin 2) 1 : Fin 2 → ℤ) δ = 0) :
    PairOrbit .G2 (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) ![2, 3]
      (Pi.single (0 : Fin 2) 1 : Fin 2 → ℤ) δ := by
  rw [g2_iform_eq] at h0
  have hc : g2Cond0 (List.ofFn δ) = true := by
    rw [g2_ofFn]
    simp only [g2Cond0, decide_eq_true_eq]
    simp at h0
    linarith
  have hm := g2_enum0 _ hδ hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · have hδe : δ = ![-1, -2] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact (g2_orbit_of_path ([1, 0, 1] : List (Fin 2)) (by intro i; fin_cases i <;> rfl)
      (by intro i; fin_cases i <;> rfl)).swap
  · have hδe : δ = ![1, 2] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact (g2_orbit_of_path ([0, 1] : List (Fin 2)) (by intro i; fin_cases i <;> rfl)
      (by intro i; fin_cases i <;> rfl)).swap

theorem g2_base1 (δ : Fin 2 → ℤ) (hδ : List.ofFn δ ∈ Tag.G2.artifactRoots)
    (h0 : iform (τ := .G2) (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) δ = 0) :
    PairOrbit .G2 (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) ![2, 3]
      (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) δ := by
  rw [g2_iform_eq] at h0
  have hc : g2Cond1 (List.ofFn δ) = true := by
    rw [g2_ofFn]
    simp only [g2Cond1, decide_eq_true_eq]
    simp at h0
    linarith
  have hm := g2_enum1 _ hδ hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · have hδe : δ = ![-2, -3] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact g2_orbit_of_path ([0, 1, 0, 1, 0] : List (Fin 2)) (by intro i; fin_cases i <;> rfl)
      (by intro i; fin_cases i <;> rfl)
  · have hδe : δ = ![2, 3] := List.ofFn_injective (h.trans (by decide))
    subst hδe
    exact g2_orbit_of_path ([] : List (Fin 2)) (by intro i; fin_cases i <;> rfl)
      (by intro i; fin_cases i <;> rfl)

theorem g2_iform_self {v : Fin (Tag.rank .G2) → ℤ} (hv : IsRoot .G2 v) :
    iform v v = 2 ∨ iform v v = 6 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hv
  rw [hj]
  fin_cases j <;> decide

theorem g2_not_isRoot_of_orth {a b : Fin (Tag.rank .G2) → ℤ} (ha : IsRoot .G2 a)
    (hb : IsRoot .G2 b) (hab : iform a b = 0) (p : ℕ × ℕ) (hp1 : 0 < p.1) (hp2 : 0 < p.2) :
    ¬IsRoot .G2 (p.1 • a + p.2 • b) := by
  intro hr
  have e : iform (p.1 • a + p.2 • b) (p.1 • a + p.2 • b) =
      (p.1 : ℤ) ^ 2 * iform a a + (p.2 : ℤ) ^ 2 * iform b b := by
    rw [← Nat.cast_smul_eq_nsmul ℤ p.1 a, ← Nat.cast_smul_eq_nsmul ℤ p.2 b, iform_add_left,
      iform_add_right, iform_add_right, iform_smul_left, iform_smul_left, iform_smul_left,
      iform_smul_left, iform_smul_right, iform_smul_right, iform_smul_right, iform_smul_right,
      iform_comm b a, hab]
    ring
  have h1 : (1 : ℤ) ≤ p.1 := by exact_mod_cast hp1
  have h2 : (1 : ℤ) ≤ p.2 := by exact_mod_cast hp2
  have hv := g2_iform_self hr
  rw [e] at hv
  rcases g2_iform_self ha with h | h <;> rcases g2_iform_self hb with h' | h' <;>
    rw [h, h'] at hv
  ·
    rcases hv with hv | hv
    · nlinarith
    · have hp : (p.1 : ℤ) ≤ 1 := by nlinarith
      have hq : (p.2 : ℤ) ≤ 1 := by nlinarith
      rw [le_antisymm hp h1, le_antisymm hq h2] at hv
      norm_num at hv
  all_goals rcases hv with hv | hv <;> nlinarith

theorem g2_insep {γ δ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hδ : IsRoot .G2 δ)
    (hli : LinIndepPair γ δ)
    (hpar : (∀ i, 2 ∣ cartanCoord δ i) ∨ ∀ i, 2 ∣ cartanCoord γ i - cartanCoord δ i) :
    iform γ δ = 0 := by
  have hdouble : ∀ z : Fin (Tag.rank .G2) → ℤ, (∀ a, 2 ∣ z a) → ∃ y, z = (2 : ℤ) • y := by
    intro z hz
    choose y hy using hz
    exact ⟨y, funext fun a => by simp [hy a]⟩
  have hne : γ ≠ δ := fun h => by
    have := hli 1 (-1) (by rw [h]; simp)
    omega
  have hne' : γ ≠ -δ := fun h => by
    have := hli 1 1 (by rw [h]; simp)
    omega
  rcases hpar with hδ2 | hγδ
  · exfalso
    obtain ⟨y, hy⟩ := hdouble δ (g2_even_of_cartanCoord hδ2)
    obtain ⟨c, hc⟩ := two_dvd_iform_self y
    have h := g2_iform_self hδ
    rw [hy, iform_smul_left, iform_smul_right, hc] at h
    omega
  · have hz : ∀ i, 2 ∣ cartanCoord (γ - δ) i := fun i => by
      rw [cartanCoord_sub]
      exact hγδ i
    obtain ⟨y, hy⟩ := hdouble (γ - δ) (g2_even_of_cartanCoord hz)
    obtain ⟨c, hc⟩ := two_dvd_iform_self y
    have hval : iform (γ - δ) (γ - δ) = iform γ γ + iform δ δ - 2 * iform γ δ := by
      rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm δ γ]
      ring
    rw [hy, iform_smul_left, iform_smul_right, hc] at hval
    have hcs := iform_sq_lt hγ hδ hne hne'
    have hd1 := iform_self_dvd hγ δ
    have hd2 := iform_self_dvd hδ γ
    rw [iform_comm δ γ] at hd2
    rcases g2_iform_self hγ with ha | ha <;> rcases g2_iform_self hδ with hb | hb <;>
      rw [ha, hb] at hval hcs <;> rw [ha] at hd1 <;> rw [hb] at hd2
    · exfalso
      have h1 : iform γ δ ≤ 1 := by nlinarith
      have h2 : -1 ≤ iform γ δ := by nlinarith
      omega
    · have h1 : iform γ δ ≤ 3 := by nlinarith
      have h2 : -3 ≤ iform γ δ := by nlinarith
      omega
    · have h1 : iform γ δ ≤ 3 := by nlinarith
      have h2 : -3 ≤ iform γ δ := by nlinarith
      omega
    · exfalso
      have h1 : iform γ δ ≤ 5 := by nlinarith
      have h2 : -5 ≤ iform γ δ := by nlinarith
      omega

theorem g2_sep_or_orth {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {γ δ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hδ : IsRoot .G2 δ)
    (hli : LinIndepPair γ δ) :
    (∃ t : Fin (Tag.rank .G2) → Kˣ, rootChar K γ t = 1 ∧ rootChar K δ t ≠ 1) ∨
      iform γ δ = 0 := by
  by_cases h : (∃ j, ¬2 ∣ cartanCoord δ j) ∧ ∃ i, ¬2 ∣ (cartanCoord γ i - cartanCoord δ i)
  · exact Or.inl (exists_sep_of_parity (two_ne_zero_of_card_three hK) h.1 h.2)
  · right
    have hpar : (∀ i, 2 ∣ cartanCoord δ i) ∨ ∀ i, 2 ∣ cartanCoord γ i - cartanCoord δ i := by
      by_contra hcon
      push Not at hcon
      exact h hcon
    exact g2_insep hγ hδ hli hpar

theorem g2_pairOrbit : ∀ {γ : Fin (Tag.rank .G2) → ℤ}, IsRoot .G2 γ → ∀ δ, IsRoot .G2 δ →
    iform γ δ = 0 → PairOrbit .G2 (Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ) ![2, 3] γ δ := by
  intro γ hγ
  induction hγ with
  | basis j =>
    intro δ hδ h0
    have hδl := isRoot_iff_mem_artifactRoots.1 hδ
    fin_cases j
    · exact g2_base0 δ hδl h0
    · exact g2_base1 δ hδl h0
  | @reflect i v hv ih =>
    intro δ hδ h0
    have h := ih (reflect .G2 i δ) (.reflect i hδ)
      (by rwa [← iform_reflect i v (reflect .G2 i δ), reflect_reflect])
    have := h.step i
    rwa [reflect_reflect] at this

end G2Roots

section G2

theorem g2_three_ker_le_zpowers {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {E : Type*} [Group E] [Group.IsPerfect E] {π : E →* adjointGroup .G2 K}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ c : E, c ^ 3 = 1 ∧ π.ker ≤ Subgroup.zpowers c := by
  obtain ⟨-, ⟨O⟩, hP, -⟩ :=
    RankTwo.g2_conclusionB_of_comm fun O => RankTwo.g2_exists_commutatorFormula K O
  obtain ⟨C, -, hC⟩ := RankTwo.g2_exists_commutatorFormula K O
  have hE := RankTwo.g2_chevalleyExtras K O C hC
  have hT : ∀ (t : Fin (Tag.rank .G2) → Kˣ) (γ : Fin (Tag.rank .G2) → ℤ), IsRoot .G2 γ → ∀ c,
      torusAdjHom t * xPar (rootOperatorFamily .G2) γ c * (torusAdjHom t)⁻¹ =
        xPar (rootOperatorFamily .G2) γ ((rootChar K γ t : K) * c) :=
    fun t γ _ c => torusAdj_conj_xPar t γ c
  have h₀ : ((Pi.single (1 : Fin 2) 1 : Fin 2 → ℤ), (![2, 3] : Fin 2 → ℤ)) ∈
      {p : (Fin (Tag.rank .G2) → ℤ) × (Fin (Tag.rank .G2) → ℤ) |
        IsRoot .G2 p.1 ∧ IsRoot .G2 p.2 ∧ iform p.1 p.2 = 0} :=
    ⟨IsRoot.basis (τ := .G2) (1 : Fin 2), isRoot_iff_mem_artifactRoots.2 (by decide),
      by rw [g2_iform_eq]; simp⟩
  exact exists_ker_le_zpowers_of_torus_three (isFiniteType_cartan .G2)
    (RG := rootGroup (rootOperatorFamily .G2) K) hK (adjDatum_roots _ K) hE hP torusAdjHom hT
    (fun _ hγ => exists_unitVec cartan_mul_cartanInvG2 hγ)
    (fun i t => weyl_conj_torus (adjDatum_roots _ K) hE hP torusAdjHom hT
      center_adjointGroup_eq_bot i t)
    {p | IsRoot .G2 p.1 ∧ IsRoot .G2 p.2 ∧ iform p.1 p.2 = 0}
    (fun p hp => ⟨hp.1, hp.2.1, g2_not_isRoot_of_orth hp.1 hp.2.1 hp.2.2⟩)
    (fun _ _ hγ hδ hli => (g2_sep_or_orth hK hγ hδ hli).imp_right fun h =>
      Or.inr ⟨hγ, hδ, h⟩)
    h₀ (fun p hp => g2_pairOrbit hp.1 p.2 hp.2.1 hp.2.2) hπ hcen

theorem g2_three_card_ker_le {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {E : Type*} [Group E] [Group.IsPerfect E] {π : E →* adjointGroup .G2 K}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) : Nat.card π.ker ≤ 3 := by
  obtain ⟨c, hc, hle⟩ := g2_three_ker_le_zpowers hK hπ hcen
  exact card_le_three_of_le_zpowers hc hle

theorem g2_three_card_griessHopfMultiplier_le {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) :
    Nat.card (CFSG.Open.griessHopfMultiplier (adjointGroup .G2 K)) ≤ 3 := by
  have : Group.IsPerfect ↥(adjointGroup .G2 K) := isPerfect_g2_of_three_le_card K (by omega)
  have : Group.IsPerfect (CFSG.RankThree.PerfectCover.HopfCover ↥(adjointGroup .G2 K)) :=
    CFSG.RankThree.PerfectCover.hopfCover_isPerfect
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
  exact g2_three_card_ker_le hK CFSG.RankThree.PerfectCover.hopfCoverMap_surjective
    CFSG.RankThree.PerfectCover.hopfMultiplier_le_center

theorem g2_three_hopfMultiplier {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    commutator (AdjointQuotient .G2 K) = ⊤ ∧
      Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) ≤ 3 := by
  have : Group.IsPerfect ↥(adjointGroup .G2 K) := isPerfect_g2_of_three_le_card K (by omega)
  have : Group.IsPerfect (AdjointQuotient .G2 K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  let e : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot
  rw [Nat.card_congr (griessHopfMultiplierCongr e).toEquiv]
  exact g2_three_card_griessHopfMultiplier_le hK

end G2

end CFSG.LieType.Steinberg.CentralExt.FieldThree
