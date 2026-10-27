module

public import CFSG.CharacterTheory.Semidihedral.Principal.OddKernelGL2PrincipalColumns
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.IsolatedCharacterField
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers GL2ThreeCharacters

namespace GL2ScaledOrders

theorem xvw_core (x v w idx s : ℤ) (hidx : idx % 2 = 1) (hs : s % 2 = 1) (hspos : 0 < s)
    (hx1 : x + 1 ≠ 0) (hw : w ≠ 0) (hD : x + 1 + w + v = 0)
    (E1 : idx * ((x - 2) * (x - 2)) = 96 * s * (x * (x + 1)))
    (E2 : idx * (9 * w * v + (x + 1) * v + 16 * (x + 1) * w) = 192 * s * ((x + 1) * w * v)) :
    (x = 10 ∧ v = 44 ∧ idx = 165 * s) ∨ (x = 26 ∧ v = 12 ∧ idx = 117 * s) := by
  have hw' : w = -(x + 1 + v) := by linear_combination hD
  subst hw'
  have h : 96 * s * (x + 1) *
      (((x - 8) * v - 8 * (x + 1)) * ((2 * x - 1) * v + 2 * x * (x + 1))) = 0 := by
    linear_combination (-(9 * (-(x + 1 + v)) * v + (x + 1) * v +
      16 * (x + 1) * (-(x + 1 + v)))) * E1 + ((x - 2) * (x - 2)) * E2
  have hne : 96 * s * (x + 1) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hspos.ne') hx1
  rcases mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hne) with h1 | h2
  · have hd : (x - 8) * (v - 8) = 72 := by linear_combination h1
    have hdvd : (x - 8) ∣ 72 := ⟨v - 8, hd.symm⟩
    have hb := Int.le_of_dvd (by norm_num) ((abs_dvd (x - 8) 72).mpr hdvd)
    rw [abs_le] at hb
    have hlo : -64 ≤ x := by linarith [hb.1]
    have hhi : x ≤ 80 := by linarith [hb.2]
    clear h hne hb hdvd
    interval_cases x <;> omega
  · have h6 : (2 * x - 1) * (-4 * v - 4 * x - 6) = 6 := by linear_combination (-4) * h2
    have hdvd : (2 * x - 1) ∣ 6 := ⟨-4 * v - 4 * x - 6, h6.symm⟩
    have hb := Int.le_of_dvd (by norm_num) ((abs_dvd (2 * x - 1) 6).mpr hdvd)
    rw [abs_le] at hb
    have hlo : -2 ≤ x := by linarith [hb.1]
    have hhi : x ≤ 3 := by linarith [hb.2]
    clear h hne hb hdvd h6
    interval_cases x <;> omega

theorem degree_solutions {f f₅ f₆ f₇ idx s ε ε₁ ε₂ ε₃ : ℤ} (hf : 0 < f) (hf₂ : 0 < f + ε)
    (hf₅ : 0 < f₅) (hf₆ : 0 < f₆) (hf₇ : 0 < f₇) (hε : ε = 1 ∨ ε = -1) (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hε₃ : ε₃ = 1 ∨ ε₃ = -1) (hidx : idx % 2 = 1) (hs : s % 2 = 1)
    (hspos : 0 < s) (D1 : ε * (f + ε) + ε₁ * f₅ + ε₂ * f₆ = 0)
    (D2 : ε * f + ε₁ * f₅ + ε₃ * f₇ = 0)
    (E1 : idx * ((f - 2 * ε) * (f - 2 * ε)) = 96 * s * (f * (f + ε)))
    (E2 : idx * (9 * ε * f₅ * f₆ + ε₁ * (f + ε) * f₆ + 16 * ε₂ * (f + ε) * f₅) =
      192 * s * ((f + ε) * f₅ * f₆)) :
    (ε = 1 ∧ f = 10 ∧ ε₁ = -1 ∧ f₅ = 55 ∧ ε₂ = 1 ∧ f₆ = 44 ∧ ε₃ = 1 ∧ f₇ = 45 ∧
        idx = 165 * s) ∨
      (ε = 1 ∧ f = 26 ∧ ε₁ = -1 ∧ f₅ = 39 ∧ ε₂ = 1 ∧ f₆ = 12 ∧ ε₃ = 1 ∧ f₇ = 13 ∧
        idx = 117 * s) := by
  obtain ⟨x, hx⟩ : ∃ x, x = ε * f := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = ε₂ * f₆ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = ε₁ * f₅ := ⟨_, rfl⟩
  rcases hε with rfl | rfl <;> rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;>
    rcases hε₃ with rfl | rfl <;>
  · have key := xvw_core x v w idx s hidx hs hspos (by rw [hx]; omega) (by rw [hw]; omega)
      (by rw [hx, hv, hw]; linear_combination D1) (by rw [hx]; linear_combination E1)
      (by rw [hx, hv, hw]; first | linear_combination E2 | linear_combination (-1 : ℤ) * E2)
    omega

theorem rep_eq_one_of_character_eq {K : Type*} [Group K] [Finite K] {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ K V) (g : K)
    (h : ρ.character g = ρ.character 1) : ρ g = 1 := by
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hpow : ρ g ^ orderOf g = 1 := by
    rw [← _root_.map_pow ρ g (orderOf g), pow_orderOf_eq_one, _root_.map_one]
  have htr : LinearMap.trace ℂ V (ρ g) = (Module.finrank ℂ V : ℂ) := by
    rw [← Representation.char_one ρ, ← h]
    rfl
  exact CFSG.Section1.finite_order_eq_one_of_trace_eq_finrank (ρ g) hn hpow htr

theorem class_sum_square {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ K V) [ρ.IsIrreducible] (A : Finset K)
    (hA : ∀ u ∈ A, ∀ c : K, c * u * c⁻¹ ∈ A) :
    (∑ u ∈ A, ∑ v ∈ A, ρ.character (u * v)) * ρ.character 1 =
      (∑ u ∈ A, ρ.character u) ^ 2 := by
  set T : Module.End ℂ V := ∑ u ∈ A, ρ u with hT
  have hconj : ∀ c : K, ρ c * T * ρ c⁻¹ = T := by
    intro c
    rw [hT, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_nbij' (fun u => c * u * c⁻¹) (fun u => c⁻¹ * u * c)
      (fun u hu => hA u hu c) (fun u hu => by simpa using hA u hu c⁻¹)
      (fun u _ => by group) (fun u _ => by group) (fun u _ => by rw [← map_mul, ← map_mul])
  have hcomm : ∀ c : K, T * ρ c = ρ c * T := by
    intro c
    calc T * ρ c = ρ c * T * ρ c⁻¹ * ρ c := by rw [hconj c]
      _ = ρ c * T := by rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  let intertwiner : ρ.IntertwiningMap ρ :=
    { toLinearMap := T
      isIntertwining' := by
        intro member
        change T * ρ member = ρ member * T
        exact hcomm member }
  obtain ⟨scalar, hscalar⟩ :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2
      intertwiner
  have hTs : T = scalar • (1 : Module.End ℂ V) := by
    have hequal := congrArg Representation.IntertwiningMap.toLinearMap hscalar
    rw [Representation.IntertwiningMap.algebraMap_apply,
      Representation.IntertwiningMap.toLinearMap_smul] at hequal
    have hone : (1 : ρ.IntertwiningMap ρ).toLinearMap = (1 : Module.End ℂ V) := by
      ext member
      exact congrFun (Representation.IntertwiningMap.coe_one ρ) member
    rw [hone] at hequal
    exact hequal.symm
  have h1 : ∑ u ∈ A, ρ.character u = scalar * ρ.character 1 := by
    have h := congrArg (LinearMap.trace ℂ V) hTs
    rw [hT, map_sum, map_smul, LinearMap.trace_one] at h
    rw [Representation.char_one]
    simpa [Representation.character] using h
  have h2 : ∑ u ∈ A, ∑ v ∈ A, ρ.character (u * v) = scalar ^ 2 * ρ.character 1 := by
    have h := congrArg (fun X => LinearMap.trace ℂ V (X * X)) hTs
    rw [smul_mul_smul, one_mul, map_smul, LinearMap.trace_one, smul_eq_mul] at h
    rw [Representation.char_one, pow_two, ← h, hT, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← _root_.map_mul ρ u v]
    rfl
  rw [h1, h2]
  ring

theorem mem_centralizer_of_mul_mem_section {G : Type*} [Group G] {t u v : G} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v ∈ centralInvolutionSection t) :
    u ∈ Subgroup.centralizer ({t} : Set G) ∧ v ∈ Subgroup.centralizer ({t} : Set G) := by
  obtain ⟨-, heven, hpow⟩ := huv
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have ht2 : t * t = 1 := by
    rw [← hpow, ← pow_add, ← two_mul, Nat.mul_div_cancel' (even_iff_two_dvd.mp heven),
      pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have key : ∀ y : G, y * (u * v) * y⁻¹ = (u * v)⁻¹ → y ∈ Subgroup.centralizer ({t} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (· ^ (orderOf (u * v) / 2)) hy
    rw [conj_pow, inv_pow, hpow, htinv] at h
    calc y * t = y * t * y⁻¹ * y := by group
      _ = t * y := by rw [h]
  refine ⟨key u ?_, key v ?_⟩
  · rw [mul_inv_rev, huinv, hvinv]
    calc u * (u * v) * u = (u * u) * v * u := by group
      _ = v * u := by rw [hu, one_mul]
  · rw [mul_inv_rev, huinv, hvinv]
    calc v * (u * v) * v = v * u * (v * v) := by group
      _ = v * u := by rw [hv, mul_one]

theorem pair_count_general {G : Type} [Group G] [Fintype G] (C : Subgroup G) (α : C → ℂ)
    (hvan : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → ∀ h : u * v ∈ C,
      α ⟨u * v, h⟩ ≠ 0 → u ∈ C ∧ v ∈ C) :
    ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
        ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), inducedFunction C α (u * v) =
      (C.index : ℂ) * ∑ u ∈ Finset.univ.filter (fun c : C => orderOf c = 2),
        ∑ v ∈ Finset.univ.filter (fun c : C => orderOf c = 2), α (u * v) := by
  let ext : G → ℂ := fun g => if h : g ∈ C then α ⟨g, h⟩ else 0
  have hind : ∀ x : G, inducedFunction C α x =
      (Nat.card C : ℂ)⁻¹ * ∑ c : G, ext (c⁻¹ * x * c) := by
    intro x
    unfold inducedFunction
    congr 1
  have hvan' : ∀ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∀ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ext (u * v) ≠ 0 → u ∈ C ∧ v ∈ C := by
    intro u hu v hv hne
    by_cases hC : u * v ∈ C
    · refine hvan u v (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 hC ?_
      intro h0
      apply hne
      simp only [ext, dite_eq_left hC]
      exact h0
    · exact absurd (by simp only [ext, dite_eq_right hC]) hne
  have hinv : ∀ c : G, ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), ext (c⁻¹ * (u * v) * c) =
      ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
        ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), ext (u * v) := by
    intro c
    have hmem : ∀ g : G, g ∈ Finset.univ.filter (fun g : G => orderOf g = 2) ↔
        (MulAut.conj c⁻¹) g ∈ Finset.univ.filter (fun g : G => orderOf g = 2) := by
      intro g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulEquiv.orderOf_eq]
    refine Finset.sum_equiv (MulAut.conj c⁻¹).toEquiv hmem fun u _ => ?_
    refine Finset.sum_equiv (MulAut.conj c⁻¹).toEquiv hmem fun v _ => ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
    congr 1
    group
  have hJ : (Finset.univ.filter (fun c : C => orderOf c = 2)).map
      (Function.Embedding.subtype (· ∈ C)) =
      (Finset.univ.filter (fun g : G => orderOf g = 2)).filter (· ∈ C) := by
    ext g
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by rwa [Subgroup.orderOf_coe], c.2⟩
    · rintro ⟨hg, hgC⟩
      exact ⟨⟨g, hgC⟩, by rwa [← Subgroup.orderOf_coe], rfl⟩
  have hsub : (Finset.univ.filter (fun g : G => orderOf g = 2)).filter (· ∈ C) ⊆
      Finset.univ.filter (fun g : G => orderOf g = 2) := Finset.filter_subset _ _
  have hrestrict : ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), ext (u * v) =
      ∑ u ∈ Finset.univ.filter (fun c : C => orderOf c = 2),
        ∑ v ∈ Finset.univ.filter (fun c : C => orderOf c = 2), α (u * v) := by
    calc ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
          ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), ext (u * v)
        = ∑ u ∈ (Finset.univ.filter (fun g : G => orderOf g = 2)).filter (· ∈ C),
            ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), ext (u * v) := by
          refine (Finset.sum_subset hsub fun u hu huC => ?_).symm
          refine Finset.sum_eq_zero fun v hv => ?_
          by_contra hne
          exact huC (Finset.mem_filter.mpr ⟨hu, (hvan' u hu v hv hne).1⟩)
      _ = ∑ u ∈ (Finset.univ.filter (fun g : G => orderOf g = 2)).filter (· ∈ C),
            ∑ v ∈ (Finset.univ.filter (fun g : G => orderOf g = 2)).filter (· ∈ C),
              ext (u * v) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          refine (Finset.sum_subset hsub fun v hv hvC => ?_).symm
          by_contra hne
          exact hvC (Finset.mem_filter.mpr ⟨hv, (hvan' u (hsub hu) v hv hne).2⟩)
      _ = ∑ u ∈ Finset.univ.filter (fun c : C => orderOf c = 2),
            ∑ v ∈ Finset.univ.filter (fun c : C => orderOf c = 2), α (u * v) := by
          rw [← hJ, Finset.sum_map]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_map]
          refine Finset.sum_congr rfl fun v _ => ?_
          simp only [ext, Function.Embedding.coe_subtype]
          rw [dite_eq_left (C.mul_mem u.2 v.2)]
          rfl
  calc ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
        ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), inducedFunction C α (u * v)
      = (Nat.card C : ℂ)⁻¹ * ∑ c : G, ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
          ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), ext (c⁻¹ * (u * v) * c) := by
        simp only [hind, Finset.mul_sum]
        conv_lhs => enter [2, u]; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
    _ = (Nat.card C : ℂ)⁻¹ * ((Nat.card G : ℂ) *
          ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
            ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), ext (u * v)) := by
        simp only [hinv]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
    _ = (C.index : ℂ) * ∑ u ∈ Finset.univ.filter (fun c : C => orderOf c = 2),
          ∑ v ∈ Finset.univ.filter (fun c : C => orderOf c = 2), α (u * v) := by
        rw [hrestrict, ← mul_assoc, ← C.index_mul_card, Nat.cast_mul]
        have hC : (Nat.card C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        field_simp

theorem pair_count_induced {G : Type} [Group G] [Fintype G] (t : G)
    (α : Subgroup.centralizer ({t} : Set G) → ℂ)
    (hα : ∀ x : Subgroup.centralizer ({t} : Set G),
      (x : G) ∉ centralInvolutionSection t → α x = 0) :
    ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
        ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
          inducedFunction (Subgroup.centralizer ({t} : Set G)) α (u * v) =
      ((Subgroup.centralizer ({t} : Set G)).index : ℂ) *
        ∑ u ∈ Finset.univ.filter (fun c : Subgroup.centralizer ({t} : Set G) => orderOf c = 2),
          ∑ v ∈ Finset.univ.filter (fun c : Subgroup.centralizer ({t} : Set G) => orderOf c = 2),
            α (u * v) := by
  refine pair_count_general _ α fun u v hu hv h hne => ?_
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hv2 : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  by_contra hsec
  exact hne (hα _ fun hmem => hsec (mem_centralizer_of_mul_mem_section hu2 hv2 hmem))

section Involutions

variable {C : Type*} [Group C] [Finite C] {Q : Type*} [Group Q] (π : C →* Q)

omit [Finite C] in
theorem exists_conj_of_involutions (hN : Odd (Nat.card π.ker)) {u w : C} (hu : u * u = 1)
    (hw : w * w = 1) (hπ : π u = π w) : ∃ n ∈ π.ker, u = n * w * n⁻¹ := by
  have hm : u * w ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, hπ, ← map_mul, hw, map_one]
  obtain ⟨k, hk⟩ : Odd (orderOf (u * w)) := hN.of_dvd_nat (π.ker.orderOf_dvd_natCard hm)
  refine ⟨(u * w) ^ (k + 1), π.ker.pow_mem hm _, ?_⟩
  set n := (u * w) ^ (k + 1) with hn
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hconj : w * (u * w) * w⁻¹ = (u * w)⁻¹ := by
    rw [mul_inv_rev, huinv, hwinv]
    calc w * (u * w) * w = w * u * (w * w) := by group
      _ = w * u := by rw [hw, mul_one]
  have h1 : w * n * w⁻¹ = n⁻¹ := by
    rw [hn, ← conj_pow, hconj, inv_pow]
  have h1' : w * n⁻¹ * w⁻¹ = n := by
    rw [show w * n⁻¹ * w⁻¹ = (w * n * w⁻¹)⁻¹ by group, h1, inv_inv]
  have h2 : w * n⁻¹ = n * w := by
    calc w * n⁻¹ = w * n⁻¹ * w⁻¹ * w := by group
      _ = n * w := by rw [h1']
  have hpow : n * n = u * w := by
    rw [hn, ← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
      pow_orderOf_eq_one, one_mul]
  calc u = u * w * w := by rw [mul_assoc, hw, mul_one]
    _ = n * n * w := by rw [hpow]
    _ = n * (w * n⁻¹) := by rw [h2, mul_assoc]
    _ = n * w * n⁻¹ := by rw [mul_assoc]

omit [Finite C] in
theorem card_involution_fiber (hN : Odd (Nat.card π.ker)) {w : C} (hw : w * w = 1) :
    Nat.card {u : C // u * u = 1 ∧ π u = π w} *
        Nat.card (π.ker ⊓ Subgroup.centralizer ({w} : Set C) : Subgroup C) =
      Nat.card π.ker := by
  let _ : MulAction π.ker C := MulAction.compHom C ((MulAut.conj).comp π.ker.subtype)
  have hsmul : ∀ (n : π.ker) (c : C), n • c = (n : C) * c * (n : C)⁻¹ := fun n c => rfl
  have horbit : MulAction.orbit π.ker w = {u : C | u * u = 1 ∧ π u = π w} := by
    ext u
    constructor
    · rintro ⟨n, rfl⟩
      show n • w ∈ {u : C | u * u = 1 ∧ π u = π w}
      rw [hsmul]
      refine ⟨?_, ?_⟩
      · calc (n : C) * w * (n : C)⁻¹ * ((n : C) * w * (n : C)⁻¹) =
            (n : C) * (w * w) * (n : C)⁻¹ := by group
          _ = 1 := by rw [hw, mul_one, mul_inv_cancel]
      · rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp n.2, one_mul, inv_one, mul_one]
    · rintro ⟨hu, hπu⟩
      obtain ⟨n, hn, rfl⟩ := exists_conj_of_involutions π hN hu hw hπu
      exact ⟨⟨n, hn⟩, rfl⟩
  have hstab : Nat.card (MulAction.stabilizer π.ker w) =
      Nat.card (π.ker ⊓ Subgroup.centralizer ({w} : Set C) : Subgroup C) := by
    have hiff : ∀ n : π.ker, n ∈ MulAction.stabilizer π.ker w ↔
        (n : C) ∈ Subgroup.centralizer ({w} : Set C) := by
      intro n
      rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        calc (n : C) * w = (n : C) * w * (n : C)⁻¹ * (n : C) := by group
          _ = w * (n : C) := by rw [h]
      · intro h
        rw [h, mul_assoc, mul_inv_cancel, mul_one]
    refine Nat.card_congr
      { toFun := fun n => ⟨n.1.1, n.1.2, (hiff n.1).mp n.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, (hiff ⟨x.1, x.2.1⟩).mpr x.2.2⟩
        left_inv := fun n => rfl
        right_inv := fun x => rfl }
  have hmul := (MulAction.stabilizer π.ker w).index_mul_card
  rw [MulAction.index_stabilizer, horbit, hstab] at hmul
  rw [← hmul, ← Nat.card_coe_set_eq]
  rfl

omit [Finite C] in
theorem card_inf_centralizer_conj (N : Subgroup C) [N.Normal] (w c : C) :
    Nat.card (N ⊓ Subgroup.centralizer ({c * w * c⁻¹} : Set C) : Subgroup C) =
      Nat.card (N ⊓ Subgroup.centralizer ({w} : Set C) : Subgroup C) := by
  have hfwd : ∀ x : C, x ∈ N ⊓ Subgroup.centralizer ({c * w * c⁻¹} : Set C) →
      c⁻¹ * x * c ∈ N ⊓ Subgroup.centralizer ({w} : Set C) := by
    intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨by simpa using ‹N.Normal›.conj_mem x hx.1 c⁻¹, ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * x * c * w = c⁻¹ * (x * (c * w * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * w * c⁻¹) * x) * c := by rw [h]
      _ = w * (c⁻¹ * x * c) := by group
  have hbwd : ∀ y : C, y ∈ N ⊓ Subgroup.centralizer ({w} : Set C) →
      c * y * c⁻¹ ∈ N ⊓ Subgroup.centralizer ({c * w * c⁻¹} : Set C) := by
    intro y hy
    rw [Subgroup.mem_inf] at hy ⊢
    refine ⟨‹N.Normal›.conj_mem y hy.1 c, ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * y * c⁻¹ * (c * w * c⁻¹) = c * (y * w) * c⁻¹ := by group
      _ = c * (w * y) * c⁻¹ := by rw [h]
      _ = c * w * c⁻¹ * (c * y * c⁻¹) := by group
  exact Nat.card_congr
    { toFun := fun x => ⟨c⁻¹ * x.1 * c, hfwd x.1 x.2⟩
      invFun := fun y => ⟨c * y.1 * c⁻¹, hbwd y.1 y.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group) }

end Involutions

theorem centralizer_index_odd {G : Type*} [Group G] [Fintype G]
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) {t : G}
    (ht : orderOf t = 2) : Odd (Subgroup.centralizer ({t} : Set G)).index := by
  have hZp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨S, hS⟩ := hZp.exists_le_sylow
  have htS : t ∈ (S : Subgroup G) := hS (Subgroup.mem_zpowers t)
  have hnt : Nontrivial (S : Subgroup G) := by
    refine ⟨⟨⟨t, htS⟩, 1, fun h => ?_⟩⟩
    have h1 : t = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at ht
    norm_num at ht
  have hZnt := S.isPGroup'.center_nontrivial
  have hZp' : IsPGroup 2 (Subgroup.center (S : Subgroup G)) :=
    S.isPGroup'.to_subgroup (Subgroup.center (S : Subgroup G))
  obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card hZp').mp hZnt
  have h2 : 2 ∣ Fintype.card (Subgroup.center (S : Subgroup G)) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 2 h2
  have hz' : orderOf (((z : (S : Subgroup G)) : G)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({((z : (S : Subgroup G)) : G)} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩)
  have hodd : Odd (Subgroup.centralizer ({((z : (S : Subgroup G)) : G)} : Set G)).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
      (Sylow.not_dvd_index S) (h.trans (Subgroup.index_dvd_of_le hSz)))
  have hindex : ∀ x : G, (Subgroup.centralizer ({x} : Set G)).index =
      Nat.card (ConjClasses.mk x).carrier := by
    intro x
    have h1 := CFSG.LyonsUnitaryFour.card_conjClass_mul_card_centralizer x
    have h2 := (Subgroup.centralizer ({x} : Set G)).index_mul_card
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h2.trans h1.symm)
  rw [hindex, (ConjClasses.mk_eq_mk_iff_isConj).mpr (hinv t _ ht hz'), ← hindex]
  exact hodd

theorem orderOf_C : orderOf FourPointMatrices.C = 2 :=
  orderOf_eq_prime FourPointMatrices.C_square (by decide)

theorem C_not_mem_center : FourPointMatrices.C ∉ Subgroup.center G23 := by
  intro h
  have e := Subgroup.mem_center_iff.mp h GL2ThreeStructure.U
  revert e
  decide

theorem orderOf_U : orderOf GL2ThreeStructure.U = 3 :=
  orderOf_eq_prime (by decide) (by decide)

theorem neg_one_mem_center : (-1 : G23) ∈ Subgroup.center G23 :=
  Subgroup.mem_center_iff.mpr fun g => GL2OddKernel.neg_one_mul_comm g

theorem classOf_eq_five_iff (h : G23) : classOf h = 5 ↔ orderOf h = 2 ∧ h ≠ -1 := by
  constructor
  · intro hh
    have hconj : IsConj FourPointMatrices.C h :=
      (isConj_iff_classOf _ _).mpr (by rw [hh]; exact classOf_reference 5)
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    refine ⟨by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_C], fun hneg => ?_⟩
    have := congrArg classOf hneg
    rw [hh, classOf_neg_one] at this
    exact absurd this (by decide)
  · rintro ⟨h2, hne⟩
    exact classOf_of_orderOf_two h2 hne

section CentralizerInvolutions

variable {G : Type} [Group G] [Fintype G] {t : G}

omit [Fintype G] in
theorem exists_noncentral_involution (π : Subgroup.centralizer ({t} : Set G) →* G23)
    (hπ : Function.Surjective π) (hN : Odd (Nat.card π.ker)) :
    ∃ β : Subgroup.centralizer ({t} : Set G), orderOf β = 2 ∧ π β ∉ Subgroup.center G23 := by
  obtain ⟨c, hc⟩ := hπ FourPointMatrices.C
  have hker : c ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hc, FourPointMatrices.C_square]
  obtain ⟨j, hj⟩ : Odd (orderOf (c ^ 2)) := hN.of_dvd_nat (π.ker.orderOf_dvd_natCard hker)
  refine ⟨c ^ orderOf (c ^ 2), ?_, ?_⟩
  · have hπβ : π (c ^ orderOf (c ^ 2)) = FourPointMatrices.C := by
      rw [map_pow, hc, hj, pow_succ, pow_mul, FourPointMatrices.C_square, one_pow, one_mul]
    apply orderOf_eq_prime
    · rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]
    · intro h1
      have := congrArg π h1
      rw [hπβ, map_one] at this
      exact absurd this (by decide)
  · rw [map_pow, hc, hj, pow_succ, pow_mul, FourPointMatrices.C_square, one_pow, one_mul]
    exact C_not_mem_center

theorem involution_sum (ht : orderOf t = 2) (π : Subgroup.centralizer ({t} : Set G) →* G23)
    (hπ : Function.Surjective π) (hN : Odd (Nat.card π.ker)) (hπt : π (GL2OddKernel.tC t) = -1)
    (β : Subgroup.centralizer ({t} : Set G)) (hβ : orderOf β = 2)
    (hβz : π β ∉ Subgroup.center G23) (F : G23 → ℂ) (hF : ∀ c g : G23, F (c * g * c⁻¹) = F g) :
    ∑ u ∈ Finset.univ.filter (fun c : Subgroup.centralizer ({t} : Set G) => orderOf c = 2),
        F (π u) =
      F (-1) + 12 * ((Nat.card π.ker / Nat.card (π.ker ⊓ Subgroup.centralizer
        ({β} : Set (Subgroup.centralizer ({t} : Set G))) : Subgroup _) : ℕ) : ℂ) * F (π β) := by
  have hNodd : ∀ u ∈ π.ker, orderOf u ≠ 2 := by
    intro u hu h2
    have hodd : Odd (orderOf u) := hN.of_dvd_nat (π.ker.orderOf_dvd_natCard hu)
    rw [h2] at hodd
    exact absurd hodd (by decide)
  have hsq : ∀ u : Subgroup.centralizer ({t} : Set G), orderOf u = 2 → u * u = 1 := by
    intro u hu
    rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have hβ2 := hsq β hβ
  have hπβne : π β ≠ -1 := fun h => hβz (h ▸ neg_one_mem_center)
  have hπβ1 : π β ≠ 1 := fun h => hβz (h ▸ Subgroup.one_mem _)
  have hπβ : orderOf (π β) = 2 :=
    orderOf_eq_prime (by rw [pow_two, ← map_mul, hβ2, map_one]) hπβ1
  have hclassβ : classOf (π β) = 5 := classOf_of_orderOf_two hπβ hπβne
  have hcount : ∀ h : G23, ((Finset.univ.filter fun c : Subgroup.centralizer ({t} : Set G) =>
      orderOf c = 2).filter fun u => π u = h).card =
      if h = -1 then 1 else if classOf h = 5 then Nat.card π.ker / Nat.card (π.ker ⊓
        Subgroup.centralizer ({β} : Set (Subgroup.centralizer ({t} : Set G))) : Subgroup _)
      else 0 := by
    intro h
    rw [Finset.filter_filter]
    split_ifs with h1 h5
    ·
      subst h1
      rw [Finset.card_eq_one]
      refine ⟨GL2OddKernel.tC t, ?_⟩
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hu, hπu⟩
        have ht2 : GL2OddKernel.tC t * GL2OddKernel.tC t = 1 := by
          apply Subtype.ext
          show t * t = 1
          rw [← pow_two, ← ht, pow_orderOf_eq_one]
        obtain ⟨n, -, rfl⟩ := exists_conj_of_involutions π hN (hsq u hu) ht2 (hπu.trans hπt.symm)
        rw [(GL2OddKernel.tC_comm t n).eq, mul_assoc, mul_inv_cancel, mul_one]
      · rintro rfl
        refine ⟨?_, hπt⟩
        rw [← Subgroup.orderOf_coe]
        exact ht
    ·
      have hconj : IsConj (π β) h := (isConj_iff_classOf _ _).mpr (by rw [hclassβ, h5])
      obtain ⟨x, hx⟩ := isConj_iff.mp hconj
      obtain ⟨c, rfl⟩ := hπ x
      set w := c * β * c⁻¹ with hw
      have hw2 : w * w = 1 := by
        rw [hw]
        calc c * β * c⁻¹ * (c * β * c⁻¹) = c * (β * β) * c⁻¹ := by group
          _ = 1 := by rw [hβ2, mul_one, mul_inv_cancel]
      have hπw : π w = h := by rw [hw, map_mul, map_mul, map_inv, ← hx]
      have hh1 : h ≠ 1 := by
        intro h1
        rw [h1, classOf_one] at h5
        exact absurd h5 (by decide)
      have hfib := card_involution_fiber π hN hw2
      rw [hw, card_inf_centralizer_conj π.ker β c] at hfib
      have hpos : 0 < Nat.card (π.ker ⊓ Subgroup.centralizer
          ({β} : Set (Subgroup.centralizer ({t} : Set G))) : Subgroup _) := Nat.card_pos
      rw [← Nat.eq_div_of_mul_eq_left hpos.ne' hfib]
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
      rw [← hw, hπw]
      constructor
      · rintro ⟨hu, hπu⟩
        exact ⟨hsq u hu, hπu⟩
      · rintro ⟨hu, hπu⟩
        refine ⟨orderOf_eq_prime (by rw [pow_two]; exact hu) fun h1 => hh1 ?_, hπu⟩
        rw [← hπu, h1, map_one]
    ·
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro u - ⟨hu, hπu⟩
      have hh2 : h * h = 1 := by rw [← hπu, ← map_mul, hsq u hu, map_one]
      have hh1 : h ≠ 1 := by
        intro h1
        rw [h1] at hπu
        exact hNodd u (MonoidHom.mem_ker.mpr hπu) hu
      have horder : orderOf h = 2 := orderOf_eq_prime (by rw [pow_two]; exact hh2) hh1
      exact h5 (classOf_of_orderOf_two horder h1)
  rw [← Finset.sum_fiberwise _ π]
  have hinner : ∀ h : G23, ∑ u ∈ (Finset.univ.filter fun c : Subgroup.centralizer ({t} : Set G) =>
      orderOf c = 2).filter (fun u => π u = h), F (π u) =
      (if h = -1 then F h else 0) + (if classOf h = 5 then ((Nat.card π.ker / Nat.card (π.ker ⊓
        Subgroup.centralizer ({β} : Set (Subgroup.centralizer ({t} : Set G))) : Subgroup _) :
        ℕ) : ℂ) * F (π β) else 0) := by
    intro h
    rw [Finset.sum_congr rfl fun u hu => by rw [(Finset.mem_filter.mp hu).2], Finset.sum_const,
      hcount, nsmul_eq_mul]
    by_cases h1 : h = -1
    · subst h1
      have h5 : classOf (-1 : G23) ≠ 5 := by rw [classOf_neg_one]; decide
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right h5]
      simp
    · by_cases h5 : classOf h = 5
      · have hconj : IsConj (π β) h := (isConj_iff_classOf _ _).mpr (by rw [hclassβ, h5])
        obtain ⟨x, rfl⟩ := isConj_iff.mp hconj
        rw [ite_eq_right h1, ite_eq_left h5, ite_eq_right h1, ite_eq_left h5, hF]
        simp
      · rw [ite_eq_right h1, ite_eq_right h5, ite_eq_right h1, ite_eq_right h5]
        simp
  rw [Finset.sum_congr rfl fun h _ => hinner h, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_univ _), ← Finset.sum_filter, Finset.sum_const, card_filter_classOf,
    nsmul_eq_mul]
  simp only [classSize]
  push_cast
  ring

end CentralizerInvolutions

theorem first_order_equation {idx R0 f₁ X0 X1 X2 ε : ℂ} (hε : ε ^ 2 = 1) (hidx : idx ≠ 0)
    (hX0 : X0 = idx ^ 2) (hX1 : X1 * f₁ = (idx * (2 * ε)) ^ 2)
    (hX2 : X2 * (f₁ + ε) = (idx * (3 * ε)) ^ 2) (hP : X0 + ε * (X1 - X2) = idx * R0) :
    idx * ((f₁ - 2 * ε) * (f₁ - 2 * ε)) = R0 * (f₁ * (f₁ + ε)) := by
  have key : idx * (idx * ((f₁ - 2 * ε) * (f₁ - 2 * ε)) - R0 * (f₁ * (f₁ + ε))) = 0 := by
    linear_combination (f₁ * (f₁ + ε)) * hP + (-(f₁ * (f₁ + ε))) * hX0 +
      (-(ε * (f₁ + ε))) * hX1 + (ε * f₁) * hX2 + (idx ^ 2 * (5 * ε * f₁ - 4 * ε ^ 2)) * hε
  have := (mul_eq_zero.mp key).resolve_left hidx
  linear_combination this

theorem second_order_equation {idx R3 f₂ f₅ f₆ X2 X5 X6 ε ε₁ ε₂ : ℂ} (hε : ε ^ 2 = 1)
    (hε₁ : ε₁ ^ 2 = 1) (hε₂ : ε₂ ^ 2 = 1) (hidx : idx ≠ 0)
    (hX2 : X2 * f₂ = (idx * (3 * ε)) ^ 2) (hX5 : X5 * f₅ = (idx * ε₁) ^ 2)
    (hX6 : X6 * f₆ = (idx * (4 * ε₂)) ^ 2) (hP : ε * X2 + ε₁ * X5 + ε₂ * X6 = idx * R3) :
    idx * (9 * ε * f₅ * f₆ + ε₁ * f₂ * f₆ + 16 * ε₂ * f₂ * f₅) = R3 * (f₂ * f₅ * f₆) := by
  have key : idx * (idx * (9 * ε * f₅ * f₆ + ε₁ * f₂ * f₆ + 16 * ε₂ * f₂ * f₅) -
      R3 * (f₂ * f₅ * f₆)) = 0 := by
    linear_combination (f₂ * f₅ * f₆) * hP + (-(ε * f₅ * f₆)) * hX2 + (-(ε₁ * f₂ * f₆)) * hX5 +
      (-(ε₂ * f₂ * f₅)) * hX6 + (-(idx ^ 2 * 9 * ε * f₅ * f₆)) * hε +
      (-(idx ^ 2 * ε₁ * f₂ * f₆)) * hε₁ + (-(idx ^ 2 * 16 * ε₂ * f₂ * f₅)) * hε₂
  have := (mul_eq_zero.mp key).resolve_left hidx
  linear_combination this

theorem card_involutions_eq_index {G : Type*} [Group G] [Fintype G]
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) {t : G}
    (ht : orderOf t = 2) :
    (Finset.univ.filter fun g : G => orderOf g = 2).card =
      (Subgroup.centralizer ({t} : Set G)).index := by
  have h1 := CFSG.LyonsUnitaryFour.card_conjClass_mul_card_centralizer t
  have h2 := (Subgroup.centralizer ({t} : Set G)).index_mul_card
  rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos (h2.trans h1.symm), ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  constructor
  · intro hg
    exact (hinv t g ht hg).symm
  · intro hg
    obtain ⟨c, rfl⟩ := isConj_iff.mp hg.symm
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]

theorem faithful_of_ne_degree {G : Type} [Group G] [Fintype G]
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) {t : G} (ht : orderOf t = 2)
    (data : FiniteComplexRepresentation G) (hval : data.character t ≠ data.character 1)
    (hodd : ∀ K : Subgroup G, K.Normal → Odd (Nat.card K) → K = ⊥) :
    ∀ g : G, data.character g = data.character 1 → g = 1 := by
  have hKodd : Odd (Nat.card data.representation.ker) := by
    by_contra hev
    have h2 : 2 ∣ Fintype.card data.representation.ker := by
      rw [← Nat.card_eq_fintype_card]
      exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 h2
    have hx' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe, hx]
    have hρx : data.representation x = 1 := MonoidHom.mem_ker.mp x.2
    have hχx : data.character x = data.character 1 := by
      show LinearMap.trace ℂ _ (data.representation x) =
        LinearMap.trace ℂ _ (data.representation 1)
      rw [hρx, _root_.map_one data.representation]
    obtain ⟨g, hg⟩ := isConj_iff.mp (hinv t x ht hx')
    apply hval
    rw [← hχx, ← hg]
    exact (Representation.char_conj _ t g).symm
  have hK := hodd _ (MonoidHom.normal_ker _) hKodd
  intro g hg
  have hmem : g ∈ data.representation.ker :=
    MonoidHom.mem_ker.mpr (rep_eq_one_of_character_eq data.representation g hg)
  rw [hK] at hmem
  exact Subgroup.mem_bot.mp hmem

end GL2ScaledOrders

theorem odd_kernel_GL2_scaled_orders_and_faithful_small_character {G : Type} [Group G]
    [Fintype G] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) (t : G)
    (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hπ : Function.Surjective π) (hN : Odd (Nat.card π.ker))
    (hπt : π ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = -1) :
    let C := Subgroup.centralizer ({t} : Set G)
    let N := π.ker
    let B₀ : Set (G → ℂ) := (fun l => (basis.representation l).character) ''
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal : Set basis.index)
    let degrees : Multiset ℂ :=
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).val.map
        fun l => (basis.representation l).character 1
    (∃ β : C, orderOf β = 2 ∧
      π β ∉ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) ∧
    ∀ β : C, orderOf β = 2 →
      π β ∉ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) →
      let a := Nat.card N
      let a₁ := Nat.card (N ⊓ Subgroup.centralizer ({β} : Set C) : Subgroup C)
      let r := a / a₁
      Xor
        (Nat.card G = 7920 * a * r ^ 2 ∧ degrees = {1, 10, 10, 10, 11, 44, 45, 55} ∧
          ∃ χ ∈ B₀, χ 1 = 10 ∧ χ t = 2 ∧ (∀ ψ ∈ B₀, ψ 1 = 10 → ψ t = 2 → ψ = χ) ∧
            (∀ g : G, ∃ q : ℚ, χ g = q) ∧
            ((∀ K : Subgroup G, K.Normal → Odd (Nat.card K) → K = ⊥) →
              ∀ g : G, χ g = χ 1 → g = 1))
        (Nat.card G = 5616 * a * r ^ 2 ∧ degrees = {1, 12, 13, 26, 26, 26, 27, 39} ∧
          ∃ χ ∈ B₀, χ 1 = 12 ∧ (∀ ψ ∈ B₀, ψ 1 = 12 → ψ = χ) ∧ χ t = 4 ∧
            (∀ g : G, ∃ q : ℚ, χ g = q) ∧
            ((∀ K : Subgroup G, K.Normal → Odd (Nat.card K) → K = ⊥) →
              ∀ g : G, χ g = χ 1 → g = 1)) := by
  intro C N B₀ degrees
  refine ⟨GL2ScaledOrders.exists_noncentral_involution π hπ hN, fun β hβ hβz => ?_⟩
  intro a a₁ r
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := G23)
  obtain ⟨-, -, -, -, φ', hφ'bij, -, hφ'val, -⟩ := GL2_three_ordinary_character_table_construction
    basisH a0 GL2ThreeStructure.U FourPointMatrices.C orderOf_a0 GL2ScaledOrders.orderOf_U
    GL2ScaledOrders.orderOf_C GL2ScaledOrders.C_not_mem_center
  let φ : Fin 8 → G23 → ℂ := fun i => (basisH.representation (φ' i)).character
  have hφirr : ∀ i, φ i ∈ CFSG.BlocksIrr G23 := fun i =>
    GL2Columns.label_mem_blocksIrr basisH (φ' i)
  have hφ' : ∀ i j, φ i (GL2OddKernel.rep a0 GL2ThreeStructure.U FourPointMatrices.C j) =
      (tableA i j : ℂ) + (tableB i j : ℂ) * omega8 := by
    intro i j
    have h : φ i (GL2OddKernel.rep a0 GL2ThreeStructure.U FourPointMatrices.C j) =
        GL2OddKernel.charTable (Complex.exp (2 * Real.pi * Complex.I / 8) +
          Complex.exp (2 * Real.pi * Complex.I / 8) ^ 3) i j := hφ'val i j
    rw [h, GL2OddKernel.charTable_eq, GL2OddKernel.exp_eq_xi]
  have hπt' : π (GL2OddKernel.tC t) = -1 := hπt
  have hidx : Odd C.index := GL2ScaledOrders.centralizer_index_odd hinv ht
  obtain ⟨⟨χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, ε, ε₁, ε₂, ε₃, hsol⟩, hall⟩ :=
    odd_kernel_GL2_principal_character_columns_and_exhaustion ideal basis principal hprincipal t
      ht π hπ hN hπt a0 GL2ThreeStructure.U FourPointMatrices.C orderOf_a0
      GL2ScaledOrders.orderOf_U GL2ScaledOrders.orderOf_C GL2ScaledOrders.C_not_mem_center φ
      hφirr hφ'val
  obtain ⟨hmem, hcols, -, hexh⟩ := hall χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ε ε₁ ε₂ ε₃ hsol
  obtain ⟨hnd, h1, h2, h3, h4, h5, h6, h7, hε, hε₁, hε₂, hε₃, hβ0, hβ1, hβ2, hβ3, hβ4⟩ := hsol
  have hB₀ : B₀ = {1, (χ₁ : G → ℂ), (χ₂ : G → ℂ), (χ₃ : G → ℂ), (χ₄ : G → ℂ), (χ₅ : G → ℂ),
      (χ₆ : G → ℂ), (χ₇ : G → ℂ)} := hexh hidx
  have hβodd : ∀ i : Fin 5, ∀ g : G, Odd (orderOf g) →
      inducedFunction C (fun c => GL2OddKernel.bigPhi φ i (π c)) g = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
      odd_kernel_GL2_centralizer_produces_actual_characters t ht π hπ hN hπt a0
        GL2ThreeStructure.U FourPointMatrices.C orderOf_a0 GL2ScaledOrders.orderOf_U
        GL2ScaledOrders.orderOf_C GL2ScaledOrders.C_not_mem_center φ hφirr hφ'val
    exact h
  obtain ⟨q, hq⟩ := hπ GL2ThreeStructure.U
  have hvt := ((hcols q hq).2 1).1
  simp only [OneMemClass.coe_one, mul_one] at hvt
  have v1 : (χ₁ : G → ℂ) t = 2 * ε := by simpa using congrFun hvt 0
  have v2 : (χ₂ : G → ℂ) t = 3 * ε := by simpa using congrFun hvt 1
  have v3 : (χ₃ : G → ℂ) t = -2 * ε := by simpa using congrFun hvt 2
  have v4 : (χ₄ : G → ℂ) t = -2 * ε := by simpa using congrFun hvt 3
  have v5 : (χ₅ : G → ℂ) t = ε₁ := by simpa using congrFun hvt 4
  have v6 : (χ₆ : G → ℂ) t = 4 * ε₂ := by simpa using congrFun hvt 5
  have v7 : (χ₇ : G → ℂ) t = -3 * ε₃ := by simpa using congrFun hvt 6
  let c : Fin 8 → G → ℂ := ![1, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇]
  have hcirr : ∀ k, c k ∈ CFSG.BlocksIrr G := by
    intro k
    fin_cases k
    exacts [principal_mem_blocksIrr G, χ₁.2, χ₂.2, χ₃.2, χ₄.2, χ₅.2, χ₆.2, χ₇.2]
  have hcinj : Function.Injective c :=
    GL2Columns.injective_of_nodup hnd h1 h2 h3 h4 h5 h6 h7
  choose l hl using fun k => GL2Columns.exists_label_of_mem_blocksIrr basis (hcirr k)
  have hlinj : Function.Injective l := fun i j h => hcinj (by rw [← hl i, ← hl j, h])
  have hcmem : ∀ k, c k ∈ B₀ := by
    intro k
    rw [hB₀]
    fin_cases k <;> simp [c]
  have hcB : ∀ j, j ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      ∃ k, l k = j := by
    intro j
    constructor
    · intro hj
      have hmemj : (basis.representation j).character ∈ B₀ := ⟨j, Finset.mem_coe.mpr hj, rfl⟩
      rw [hB₀] at hmemj
      have hk : ∃ k, (basis.representation j).character = c k := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemj
        rcases hmemj with h | h | h | h | h | h | h | h
        exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩, ⟨6, h⟩, ⟨7, h⟩]
      obtain ⟨k, hk⟩ := hk
      exact ⟨k, basis.distinct (by
        show (basis.representation (l k)).character = (basis.representation j).character
        rw [hl k, hk])⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨j, hj, hjk⟩ := hcmem k
      have hjl : j = l k := basis.distinct (by
        show (basis.representation j).character = (basis.representation (l k)).character
        rw [hl k]
        exact hjk)
      rw [← hjl]
      exact Finset.mem_coe.mp hj
  have hdeg : ∀ k, ∃ n : ℕ, 0 < n ∧ c k 1 = n := by
    intro k
    refine ⟨Module.finrank ℂ (basis.representation (l k)).vector, ?_, ?_⟩
    · have h := irreducible_character_degree_ne_zero (basis.representation (l k))
        (basis.irreducible (l k))
      rw [FiniteComplexRepresentation.character, Representation.char_one] at h
      exact Nat.pos_of_ne_zero (by exact_mod_cast h)
    · rw [← hl k, FiniteComplexRepresentation.character, Representation.char_one]
  choose d hdpos hd using hdeg
  have hβ1z : ∀ i : Fin 5,
      inducedFunction C (fun x => GL2OddKernel.bigPhi φ i (π x)) 1 = 0 :=
    fun i => hβodd i 1 (by rw [orderOf_one]; exact odd_one)
  have e0 : (1 + (ε : ℂ) • ((χ₁ : G → ℂ) - χ₂)) 1 = 0 := by rw [← hβ0]; exact hβ1z 0
  have e1 : ((ε : ℂ) • ((χ₁ : G → ℂ) - χ₃)) 1 = 0 := by rw [← hβ1]; exact hβ1z 1
  have e2 : ((ε : ℂ) • ((χ₃ : G → ℂ) - χ₄)) 1 = 0 := by rw [← hβ2]; exact hβ1z 2
  have e3 : ((ε : ℂ) • (χ₂ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₂ : ℂ) • (χ₆ : G → ℂ)) 1 =
      0 := by rw [← hβ3]; exact hβ1z 3
  have e4 : ((ε : ℂ) • (χ₁ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₃ : ℂ) • (χ₇ : G → ℂ)) 1 =
      0 := by rw [← hβ4]; exact hβ1z 4
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul] at e0 e1 e2 e3 e4
  have hd1 : (χ₁ : G → ℂ) 1 = d 1 := hd 1
  have hd2 : (χ₂ : G → ℂ) 1 = d 2 := hd 2
  have hd3 : (χ₃ : G → ℂ) 1 = d 3 := hd 3
  have hd4 : (χ₄ : G → ℂ) 1 = d 4 := hd 4
  have hd5 : (χ₅ : G → ℂ) 1 = d 5 := hd 5
  have hd6 : (χ₆ : G → ℂ) 1 = d 6 := hd 6
  have hd7 : (χ₇ : G → ℂ) 1 = d 7 := hd 7
  rw [hd1, hd2] at e0
  rw [hd1, hd3] at e1
  rw [hd3, hd4] at e2
  rw [hd2, hd5, hd6] at e3
  rw [hd1, hd5, hd7] at e4
  have z0 : 1 + ε * ((d 1 : ℤ) - d 2) = 0 := by exact_mod_cast e0
  have z1 : ε * ((d 1 : ℤ) - d 3) = 0 := by exact_mod_cast e1
  have z2 : ε * ((d 3 : ℤ) - d 4) = 0 := by exact_mod_cast e2
  have z3 : ε * (d 2 : ℤ) + ε₁ * d 5 + ε₂ * d 6 = 0 := by exact_mod_cast e3
  have z4 : ε * (d 1 : ℤ) + ε₁ * d 5 + ε₃ * d 7 = 0 := by exact_mod_cast e4
  have hdeg2 : (d 2 : ℤ) = d 1 + ε := by rcases hε with rfl | rfl <;> omega
  have hdeg3 : d 3 = d 1 := by rcases hε with rfl | rfl <;> omega
  have hdeg4 : d 4 = d 1 := by rcases hε with rfl | rfl <;> omega
  have hIconj : ∀ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2), ∀ g : G,
      g * u * g⁻¹ ∈ Finset.univ.filter (fun g : G => orderOf g = 2) := by
    intro u hu g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu]
  have hIcard : ((Finset.univ.filter fun g : G => orderOf g = 2).card : ℂ) = C.index := by
    exact_mod_cast GL2ScaledOrders.card_involutions_eq_index hinv ht
  have hS : ∀ k, (∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), c k (u * v)) * c k 1 =
      ((C.index : ℂ) * c k t) ^ 2 := by
    intro k
    have : (basis.representation (l k)).representation.IsIrreducible := basis.irreducible (l k)
    have h := GL2ScaledOrders.class_sum_square (basis.representation (l k)).representation
      (Finset.univ.filter fun g : G => orderOf g = 2) hIconj
    have hsum : ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
        (basis.representation (l k)).representation.character u =
          ((Finset.univ.filter fun g : G => orderOf g = 2).card : ℂ) *
            (basis.representation (l k)).representation.character t := by
      rw [Finset.sum_congr rfl fun u hu => ?_, Finset.sum_const, nsmul_eq_mul]
      obtain ⟨g, rfl⟩ := isConj_iff.mp (hinv t u ht (Finset.mem_filter.mp hu).2)
      exact Representation.char_conj _ t g
    rw [hsum, hIcard] at h
    rw [← hl k]
    exact h
  have hJconj : ∀ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2), ∀ g : C,
      g * u * g⁻¹ ∈ Finset.univ.filter (fun x : C => orderOf x = 2) := by
    intro u hu g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu]
  have hφconj : ∀ j, ∀ x g : G23, φ j (x * g * x⁻¹) = φ j g := fun j =>
    GL2OddKernel.blocksIrr_conj (hφirr j)
  have hT : ∀ j, (∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
      ∑ v ∈ Finset.univ.filter (fun x : C => orderOf x = 2), φ j (π (u * v))) * φ j 1 =
      (φ j (-1) + 12 * (r : ℂ) * φ j (π β)) ^ 2 := by
    intro j
    have : Representation.IsIrreducible ((basisH.representation (φ' j)).representation.comp π) :=
      CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective π hπ _ (basisH.irreducible (φ' j))
    have h := GL2ScaledOrders.class_sum_square
      ((basisH.representation (φ' j)).representation.comp π)
      (Finset.univ.filter fun x : C => orderOf x = 2) hJconj
    have h' : (∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
        ∑ v ∈ Finset.univ.filter (fun x : C => orderOf x = 2), φ j (π (u * v))) * φ j (π 1) =
        (∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2), φ j (π u)) ^ 2 := h
    rw [map_one, GL2ScaledOrders.involution_sum ht π hπ hN hπt' β hβ hβz (φ j) (hφconj j)]
      at h'
    exact h'
  have hβC : ∀ j, φ j (π β) = φ j FourPointMatrices.C := by
    intro j
    have hπβ2 : orderOf (π β) = 2 := by
      have hβ2 : β * β = 1 := by rw [← pow_two, ← hβ, pow_orderOf_eq_one]
      refine orderOf_eq_prime (by rw [pow_two, ← map_mul, hβ2, map_one]) fun h => ?_
      exact hβz (h ▸ Subgroup.one_mem _)
    have hcl : classOf (π β) = 5 := classOf_of_orderOf_two hπβ2
      (fun h => hβz (h ▸ GL2ScaledOrders.neg_one_mem_center))
    obtain ⟨x, hx⟩ := isConj_iff.mp ((isConj_iff_classOf FourPointMatrices.C (π β)).mpr
      (by rw [hcl]; exact classOf_reference 5))
    rw [← hx, hφconj]
  have t00 : φ 0 1 = 1 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 0 0
  have t01 : φ 0 (-1) = 1 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 0 1
  have t05 : φ 0 FourPointMatrices.C = 1 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 0 5
  have t10 : φ 1 1 = 1 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 1 0
  have t11 : φ 1 (-1) = 1 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 1 1
  have t15 : φ 1 FourPointMatrices.C = -1 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 1 5
  have t20 : φ 2 1 = 2 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 2 0
  have t21 : φ 2 (-1) = 2 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 2 1
  have t25 : φ 2 FourPointMatrices.C = 0 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 2 5
  have t40 : φ 4 1 = 3 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 4 0
  have t41 : φ 4 (-1) = 3 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 4 1
  have t45 : φ 4 FourPointMatrices.C = 1 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 4 5
  have t50 : φ 5 1 = 4 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 5 0
  have t51 : φ 5 (-1) = -4 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 5 1
  have t55 : φ 5 FourPointMatrices.C = 0 := by
    simpa [GL2OddKernel.rep, tableA, tableB] using hφ' 5 5
  have hR0 : ∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
      ∑ v ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
        GL2OddKernel.bigPhi φ 0 (π (u * v)) = 96 * (r : ℂ) ^ 2 := by
    have h0 := hT 0
    have h2 := hT 2
    have h4 := hT 4
    rw [t00, t01, hβC, t05] at h0
    rw [t20, t21, hβC, t25] at h2
    rw [t40, t41, hβC, t45] at h4
    simp only [GL2OddKernel.bigPhi, Matrix.cons_val_zero, Pi.add_apply, Pi.sub_apply,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linear_combination h0 + (1 / 2 : ℂ) * h2 - (1 / 3 : ℂ) * h4
  have hR3 : ∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
      ∑ v ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
        GL2OddKernel.bigPhi φ 3 (π (u * v)) = 192 * (r : ℂ) ^ 2 := by
    have h1 := hT 1
    have h4 := hT 4
    have h5 := hT 5
    rw [t10, t11, hβC, t15] at h1
    rw [t40, t41, hβC, t45] at h4
    rw [t50, t51, hβC, t55] at h5
    simp only [GL2OddKernel.bigPhi, Matrix.cons_val, Pi.add_apply, Pi.sub_apply,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    linear_combination h1 + (1 / 3 : ℂ) * h4 - (1 / 4 : ℂ) * h5
  have hpc : ∀ i : Fin 5, ∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
        inducedFunction C (fun x => GL2OddKernel.bigPhi φ i (π x)) (u * v) =
      (C.index : ℂ) * ∑ u ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
        ∑ v ∈ Finset.univ.filter (fun x : C => orderOf x = 2),
          GL2OddKernel.bigPhi φ i (π (u * v)) := fun i =>
    GL2ScaledOrders.pair_count_induced t _ fun x hx =>
      GL2Columns.bigPhi_comp_eq_zero_of_not_mem ht π hN hπt' orderOf_a0
        GL2ScaledOrders.orderOf_U GL2ScaledOrders.orderOf_C GL2ScaledOrders.C_not_mem_center
        hφirr hφ' i x hx
  have hβ0' : inducedFunction C (fun x => GL2OddKernel.bigPhi φ 0 (π x)) =
      1 + (ε : ℂ) • ((χ₁ : G → ℂ) - χ₂) := hβ0
  have hβ3' : inducedFunction C (fun x => GL2OddKernel.bigPhi φ 3 (π x)) =
      (ε : ℂ) • (χ₂ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₂ : ℂ) • (χ₆ : G → ℂ) := hβ3
  have hP0 := hpc 0
  have hP3 := hpc 3
  rw [hR0, hβ0'] at hP0
  rw [hR3, hβ3'] at hP3
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hP0 hP3
  have hsign : ∀ e : ℤ, (e = 1 ∨ e = -1) → ((e : ℂ)) ^ 2 = 1 := by
    rintro e (rfl | rfl) <;> norm_num
  have hidx0 : (C.index : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Subgroup.index_ne_zero_of_finite)
  have hS0 : (∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), (1 : G → ℂ) (u * v)) *
        (1 : G → ℂ) 1 = ((C.index : ℂ) * (1 : G → ℂ) t) ^ 2 := hS 0
  have hS1 : (∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), (χ₁ : G → ℂ) (u * v)) *
        (χ₁ : G → ℂ) 1 = ((C.index : ℂ) * (χ₁ : G → ℂ) t) ^ 2 := hS 1
  have hS2 : (∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), (χ₂ : G → ℂ) (u * v)) *
        (χ₂ : G → ℂ) 1 = ((C.index : ℂ) * (χ₂ : G → ℂ) t) ^ 2 := hS 2
  have hS5 : (∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), (χ₅ : G → ℂ) (u * v)) *
        (χ₅ : G → ℂ) 1 = ((C.index : ℂ) * (χ₅ : G → ℂ) t) ^ 2 := hS 5
  have hS6 : (∑ u ∈ Finset.univ.filter (fun g : G => orderOf g = 2),
      ∑ v ∈ Finset.univ.filter (fun g : G => orderOf g = 2), (χ₆ : G → ℂ) (u * v)) *
        (χ₆ : G → ℂ) 1 = ((C.index : ℂ) * (χ₆ : G → ℂ) t) ^ 2 := hS 6
  simp only [Pi.one_apply, mul_one] at hS0 hP0
  rw [v1, hd1] at hS1
  rw [v2, hd2] at hS2
  rw [v5, hd5] at hS5
  rw [v6, hd6] at hS6
  have hd2' : (d 2 : ℂ) = d 1 + ε := by exact_mod_cast hdeg2
  have E1 := GL2ScaledOrders.first_order_equation (R0 := 96 * (r : ℂ) ^ 2) (hsign ε hε) hidx0
    hS0 hS1
    (by rw [← hd2']; exact hS2) (by linear_combination hP0)
  have E2 := GL2ScaledOrders.second_order_equation (R3 := 192 * (r : ℂ) ^ 2) (hsign ε hε)
    (hsign ε₁ hε₁) (hsign ε₂ hε₂)
    hidx0 hS2 hS5 hS6 (by linear_combination hP3)
  have hdeg2z : (d 2 : ℤ) = d 1 + ε := hdeg2
  have E1z : (C.index : ℤ) * (((d 1 : ℤ) - 2 * ε) * ((d 1 : ℤ) - 2 * ε)) =
      96 * (r : ℤ) ^ 2 * ((d 1 : ℤ) * ((d 1 : ℤ) + ε)) := by exact_mod_cast E1
  have E2z : (C.index : ℤ) * (9 * ε * (d 5 : ℤ) * d 6 + ε₁ * ((d 1 : ℤ) + ε) * d 6 +
      16 * ε₂ * ((d 1 : ℤ) + ε) * d 5) = 192 * (r : ℤ) ^ 2 *
        (((d 1 : ℤ) + ε) * d 5 * d 6) := by
    rw [← hdeg2z]
    exact_mod_cast E2
  have D1 : ε * ((d 1 : ℤ) + ε) + ε₁ * d 5 + ε₂ * d 6 = 0 := by rw [← hdeg2z]; exact z3
  have ha₁ : a₁ ∣ a := Subgroup.card_dvd_of_le inf_le_left
  have hapos : 0 < a := Nat.card_pos
  have ha₁pos : 0 < a₁ := Nat.card_pos
  have hr : r * a₁ = a := Nat.div_mul_cancel ha₁
  have hrodd : Odd r := hN.of_dvd_nat (Dvd.intro _ hr)
  have hrpos : 0 < r := Nat.div_pos (Nat.le_of_dvd hapos ha₁) ha₁pos
  have hidxz : (C.index : ℤ) % 2 = 1 := by
    have := Nat.odd_iff.mp hidx
    omega
  have hsz : (r : ℤ) ^ 2 % 2 = 1 := by
    have h := Nat.odd_iff.mp (hrodd.pow (n := 2))
    have : ((r ^ 2 : ℕ) : ℤ) % 2 = 1 := by omega
    exact_mod_cast this
  have hspos : 0 < (r : ℤ) ^ 2 := by positivity
  have hcardG : Nat.card G = C.index * (a * 48) := by
    rw [← C.index_mul_card, GL2OddKernel.card_centralizer_eq π hπ, card_G23]
  have hd0 : d 0 = 1 := by
    have h := hd 0
    have h1 : (1 : ℂ) = (d 0 : ℂ) := h
    exact_mod_cast h1.symm
  have hcBeq : coefficientBlock basis (localizedComplexIntegerRing ideal) principal =
      Finset.univ.map ⟨l, hlinj⟩ := by
    ext j
    rw [hcB j, Finset.mem_map]
    simp
  have hdegrees : degrees = (Finset.univ.val.map fun k => (d k : ℂ)) := by
    show (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).val.map
      (fun l => (basis.representation l).character 1) = _
    rw [hcBeq, Finset.map_val, Multiset.map_map]
    congr 1
    funext k
    simp only [Function.comp_apply, Function.Embedding.coeFn_mk]
    rw [hl k]
    exact hd k
  have hBset : ∀ ψ ∈ B₀, ψ = 1 ∨ ψ = χ₁ ∨ ψ = χ₂ ∨ ψ = χ₃ ∨ ψ = χ₄ ∨ ψ = χ₅ ∨ ψ = χ₆ ∨
      ψ = χ₇ := by
    intro ψ hψ
    rw [hB₀] at hψ
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hψ
  have hrat : ∀ k, (∀ b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (∀ x ∈ ({1, t} : Set G), (basis.representation b).character x = c k x) → b = l k) →
      (∃ q₁ : ℚ, c k 1 = q₁) → (∃ q₂ : ℚ, c k t = q₂) → ∀ g : G, ∃ q : ℚ, c k g = q := by
    intro k hiso h1 h2 g
    rw [← hl k]
    refine CFSG.LyonsUnitaryFour.character_rat_of_isolated_principal_block basis ideal
      hprincipal ((hcB (l k)).mpr ⟨k, rfl⟩) {1, t} ?_ ?_ g
    · intro x hx
      rw [hl k]
      rcases hx with rfl | rfl
      · exact h1
      · exact h2
    · intro b hb hbx
      exact hiso b hb fun x hx => (hbx x hx).trans (by rw [hl k])
  rcases GL2ScaledOrders.degree_solutions (by exact_mod_cast hdpos 1)
      (by rw [← hdeg2z]; exact_mod_cast hdpos 2) (by exact_mod_cast hdpos 5)
      (by exact_mod_cast hdpos 6) (by exact_mod_cast hdpos 7) hε hε₁ hε₂ hε₃ hidxz hsz hspos
      D1 z4 E1z E2z with
    ⟨rfl, h1d, rfl, h5d, rfl, h6d, rfl, h7d, hidxv⟩ |
      ⟨rfl, h1d, rfl, h5d, rfl, h6d, rfl, h7d, hidxv⟩
  ·
    have hdn : d 1 = 10 ∧ d 2 = 11 ∧ d 3 = 10 ∧ d 4 = 10 ∧ d 5 = 55 ∧ d 6 = 44 ∧ d 7 = 45 := by
      omega
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hdn
    have hidxn : C.index = 165 * r ^ 2 := by exact_mod_cast hidxv
    have hA : Nat.card G = 7920 * a * r ^ 2 := by rw [hcardG, hidxn]; ring
    refine Or.inl ⟨⟨hA, ?_, ?_⟩, fun hB => ?_⟩
    · rw [hdegrees, Fin.univ_val_map]
      simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
      have hnat : (↑([1, 10, 11, 10, 10, 55, 44, 45] : List ℕ) : Multiset ℕ) =
          {1, 10, 10, 10, 11, 44, 45, 55} := by decide
      have hmap := congrArg (Multiset.map (fun n : ℕ => (n : ℂ))) hnat
      simp only [Multiset.map_coe, List.map, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.map_singleton, Nat.cast_one, Nat.cast_ofNat] at hmap
      convert hmap using 2
      simp [hd0, e1, e2, e3, e4, e5, e6, e7]
    · refine ⟨χ₁, hmem.1, by rw [hd1, e1]; norm_num, by rw [v1]; norm_num, ?_, ?_, ?_⟩
      · intro ψ hψ hψ1 hψt
        rcases hBset ψ hψ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · norm_num at hψ1
        · rfl
        · rw [hd2, e2] at hψ1; norm_num at hψ1
        · rw [v3] at hψt; norm_num at hψt
        · rw [v4] at hψt; norm_num at hψt
        · rw [hd5, e5] at hψ1; norm_num at hψ1
        · rw [hd6, e6] at hψ1; norm_num at hψ1
        · rw [hd7, e7] at hψ1; norm_num at hψ1
      · refine hrat 1 ?_ ⟨10, by show (χ₁ : G → ℂ) 1 = _; rw [hd1, e1]; norm_num⟩
          ⟨2, by show (χ₁ : G → ℂ) t = _; rw [v1]; norm_num⟩
        intro b hb hbx
        have hb1 := hbx 1 (Set.mem_insert _ _)
        have hbt := hbx t (Set.mem_insert_of_mem _ rfl)
        obtain ⟨k, rfl⟩ := (hcB b).mp hb
        rw [hl k] at hb1 hbt
        fin_cases k
        · exact absurd hb1 (by show (1 : ℂ) ≠ (χ₁ : G → ℂ) 1; rw [hd1, e1]; norm_num)
        · rfl
        · refine absurd hb1 ?_
          show (χ₂ : G → ℂ) 1 ≠ (χ₁ : G → ℂ) 1
          rw [hd1, hd2, e1, e2]
          norm_num
        · exact absurd hbt (by show (χ₃ : G → ℂ) t ≠ (χ₁ : G → ℂ) t; rw [v1, v3]; norm_num)
        · exact absurd hbt (by show (χ₄ : G → ℂ) t ≠ (χ₁ : G → ℂ) t; rw [v1, v4]; norm_num)
        · refine absurd hb1 ?_
          show (χ₅ : G → ℂ) 1 ≠ (χ₁ : G → ℂ) 1
          rw [hd1, hd5, e1, e5]
          norm_num
        · refine absurd hb1 ?_
          show (χ₆ : G → ℂ) 1 ≠ (χ₁ : G → ℂ) 1
          rw [hd1, hd6, e1, e6]
          norm_num
        · refine absurd hb1 ?_
          show (χ₇ : G → ℂ) 1 ≠ (χ₁ : G → ℂ) 1
          rw [hd1, hd7, e1, e7]
          norm_num
      · intro hodd
        have hf := GL2ScaledOrders.faithful_of_ne_degree hinv ht (basis.representation (l 1))
          (by rw [hl 1]; show (χ₁ : G → ℂ) t ≠ (χ₁ : G → ℂ) 1; rw [v1, hd1, e1]; norm_num) hodd
        rw [hl 1] at hf
        exact hf
    · have h := hA.symm.trans hB.1
      have hpos : 0 < a * r ^ 2 := mul_pos hapos (pow_pos hrpos 2)
      have h' : 7920 * (a * r ^ 2) = 5616 * (a * r ^ 2) := by
        rw [← mul_assoc, ← mul_assoc]
        exact h
      generalize a * r ^ 2 = X at h' hpos
      omega
  ·
    have hdn : d 1 = 26 ∧ d 2 = 27 ∧ d 3 = 26 ∧ d 4 = 26 ∧ d 5 = 39 ∧ d 6 = 12 ∧ d 7 = 13 := by
      omega
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hdn
    have hidxn : C.index = 117 * r ^ 2 := by exact_mod_cast hidxv
    have hB : Nat.card G = 5616 * a * r ^ 2 := by rw [hcardG, hidxn]; ring
    refine Or.inr ⟨⟨hB, ?_, ?_⟩, fun hA => ?_⟩
    · rw [hdegrees, Fin.univ_val_map]
      simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
      have hnat : (↑([1, 26, 27, 26, 26, 39, 12, 13] : List ℕ) : Multiset ℕ) =
          {1, 12, 13, 26, 26, 26, 27, 39} := by decide
      have hmap := congrArg (Multiset.map (fun n : ℕ => (n : ℂ))) hnat
      simp only [Multiset.map_coe, List.map, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.map_singleton, Nat.cast_one, Nat.cast_ofNat] at hmap
      convert hmap using 2
      simp [hd0, e1, e2, e3, e4, e5, e6, e7]
    · refine ⟨χ₆, hmem.2.2.2.2.2.1, by rw [hd6, e6]; norm_num, ?_, by rw [v6]; norm_num, ?_, ?_⟩
      · intro ψ hψ hψ1
        rcases hBset ψ hψ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · norm_num at hψ1
        · rw [hd1, e1] at hψ1; norm_num at hψ1
        · rw [hd2, e2] at hψ1; norm_num at hψ1
        · rw [hd3, e3] at hψ1; norm_num at hψ1
        · rw [hd4, e4] at hψ1; norm_num at hψ1
        · rw [hd5, e5] at hψ1; norm_num at hψ1
        · rfl
        · rw [hd7, e7] at hψ1; norm_num at hψ1
      · refine hrat 6 ?_ ⟨12, by show (χ₆ : G → ℂ) 1 = _; rw [hd6, e6]; norm_num⟩
          ⟨4, by show (χ₆ : G → ℂ) t = _; rw [v6]; norm_num⟩
        intro b hb hbx
        have hb1 := hbx 1 (Set.mem_insert _ _)
        obtain ⟨k, rfl⟩ := (hcB b).mp hb
        rw [hl k] at hb1
        fin_cases k
        · exact absurd hb1 (by show (1 : ℂ) ≠ (χ₆ : G → ℂ) 1; rw [hd6, e6]; norm_num)
        · refine absurd hb1 ?_
          show (χ₁ : G → ℂ) 1 ≠ (χ₆ : G → ℂ) 1
          rw [hd1, hd6, e1, e6]
          norm_num
        · refine absurd hb1 ?_
          show (χ₂ : G → ℂ) 1 ≠ (χ₆ : G → ℂ) 1
          rw [hd2, hd6, e2, e6]
          norm_num
        · refine absurd hb1 ?_
          show (χ₃ : G → ℂ) 1 ≠ (χ₆ : G → ℂ) 1
          rw [hd3, hd6, e3, e6]
          norm_num
        · refine absurd hb1 ?_
          show (χ₄ : G → ℂ) 1 ≠ (χ₆ : G → ℂ) 1
          rw [hd4, hd6, e4, e6]
          norm_num
        · refine absurd hb1 ?_
          show (χ₅ : G → ℂ) 1 ≠ (χ₆ : G → ℂ) 1
          rw [hd5, hd6, e5, e6]
          norm_num
        · rfl
        · refine absurd hb1 ?_
          show (χ₇ : G → ℂ) 1 ≠ (χ₆ : G → ℂ) 1
          rw [hd6, hd7, e6, e7]
          norm_num
      · intro hodd
        have hf := GL2ScaledOrders.faithful_of_ne_degree hinv ht (basis.representation (l 6))
          (by rw [hl 6]; show (χ₆ : G → ℂ) t ≠ (χ₆ : G → ℂ) 1; rw [v6, hd6, e6]; norm_num) hodd
        rw [hl 6] at hf
        exact hf
    · have h := hA.1.symm.trans hB
      have hpos : 0 < a * r ^ 2 := mul_pos hapos (pow_pos hrpos 2)
      have h' : 7920 * (a * r ^ 2) = 5616 * (a * r ^ 2) := by
        rw [← mul_assoc, ← mul_assoc]
        exact h
      generalize a * r ^ 2 = X at h' hpos
      omega

end CFSG.Semidihedral.Principal
