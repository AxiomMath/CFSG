module

public import CFSG.ClassicalInvolution.TwoGroupCase.FourGroupCentralizer
public import CFSG.LocalAnalysis.OddStandard.Harada75Count

public section

namespace CFSG.OddStandard.Harada75

open CFSG.ClassicalInvolution Subgroup
open scoped commutatorElement

private theorem suz_exists_involution_pow {G : Type*} [Group G] (hG : IsPGroup 2 G) {y : G}
    (hy : y ≠ 1) : ∃ n : ℕ, y ^ n * y ^ n = 1 ∧ y ^ n ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hG y
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    rcases k with _ | j
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hk)) hy
    · exact ⟨j, rfl⟩
  have hord : orderOf (y ^ (2 ^ j)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk,
      pow_succ]
    exact Nat.mul_div_cancel_left _ (by positivity)
  have hy2 : y ^ (2 ^ j) * y ^ (2 ^ j) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hord]
  refine ⟨2 ^ j, hy2, fun h1 => ?_⟩
  rw [h1, orderOf_one] at hord
  omega

private theorem suz_card_le_of_cover {G : Type*} [Group G] [Finite G] {T U : Subgroup G}
    (hUT : U ≤ T) {n : ℕ} (x : Fin n → G) (hx : ∀ i, x i ∈ T)
    (hcov : ∀ t ∈ T, ∃ i, ∃ u ∈ U, t = u * x i) : Nat.card T ≤ n * Nat.card U := by
  let f : U × Fin n → T := fun p => ⟨p.1 * x p.2, T.mul_mem (hUT p.1.2) (hx p.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨t, ht⟩
    obtain ⟨i, u, hu, rfl⟩ := hcov t ht
    exact ⟨(⟨u, hu⟩, i), rfl⟩
  have h := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h
  rwa [mul_comm] at h

private theorem suz_exists_rep {Q : Type*} [Group Q] {c r : Q}
    (hcov : ∀ s : Q, s ∈ zpowers c ∨ s * r ∈ zpowers c) (T : Subgroup Q) :
    ∃ t₁ ∈ T, ∀ t ∈ T, t ∈ zpowers c ∨ t * t₁⁻¹ ∈ zpowers c := by
  by_cases h : ∃ t₁ ∈ T, t₁ ∉ zpowers c
  · obtain ⟨t₁, ht₁, ht₁c⟩ := h
    refine ⟨t₁, ht₁, fun t _ => ?_⟩
    by_cases htc : t ∈ zpowers c
    · exact Or.inl htc
    · right
      have h1 : t * r ∈ zpowers c := (hcov t).resolve_left htc
      have h2 : t₁ * r ∈ zpowers c := (hcov t₁).resolve_left ht₁c
      have h3 := mul_mem h1 (inv_mem h2)
      rwa [show t * r * (t₁ * r)⁻¹ = t * t₁⁻¹ by group] at h3
  · push Not at h
    exact ⟨1, T.one_mem, fun t ht => Or.inl (h t ht)⟩

private theorem suz_seventh {Q : Type*} [Group Q] [Finite Q] {c r : Q}
    (hcov : ∀ s : Q, s ∈ zpowers c ∨ s * r ∈ zpowers c) {T U : Subgroup Q} (hUT : U ≤ T)
    (hsq : ∀ x ∈ T, x ^ 2 ∈ U) : Nat.card T ≤ 4 * Nat.card U := by
  obtain ⟨t₁, ht₁, hrep⟩ := suz_exists_rep hcov T
  have hcyc : IsCyclic ↥(T ⊓ zpowers c) := Subgroup.isCyclic_of_le inf_le_right
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(T ⊓ zpowers c))
  have hy₀T : (g : Q) ∈ T := g.2.1
  have hY : ∀ y ∈ T ⊓ zpowers c, ∃ u ∈ U, y = u ∨ y = u * (g : Q) := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    have hyk : y = (g : Q) ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    have hsqU : (g : Q) ^ 2 ∈ U := hsq _ hy₀T
    have hk2 : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
    refine ⟨((g : Q) ^ 2) ^ (k / 2), U.zpow_mem hsqU _, ?_⟩
    have hy' : y = ((g : Q) ^ 2) ^ (k / 2) * (g : Q) ^ (k % 2) := by
      rw [hyk, ← zpow_natCast, ← zpow_mul, ← zpow_add]
      congr 1
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [hy', h0, zpow_zero, mul_one]
    · right
      rw [hy', h1, zpow_one]
  refine suz_card_le_of_cover (n := 4) hUT ![1, (g : Q), t₁, (g : Q) * t₁] ?_ ?_
  · intro i
    fin_cases i
    · exact T.one_mem
    · exact hy₀T
    · exact ht₁
    · exact T.mul_mem hy₀T ht₁
  · intro t ht
    rcases hrep t ht with h | h
    · obtain ⟨u, hu, h'⟩ := hY t ⟨ht, h⟩
      rcases h' with h' | h'
      · exact ⟨0, u, hu, by simp [h']⟩
      · exact ⟨1, u, hu, by simp [h']⟩
    · obtain ⟨u, hu, h'⟩ := hY (t * t₁⁻¹) ⟨T.mul_mem ht (T.inv_mem ht₁), h⟩
      rcases h' with h' | h'
      · refine ⟨2, u, hu, ?_⟩
        simpa using mul_inv_eq_iff_eq_mul.mp h'
      · refine ⟨3, u, hu, ?_⟩
        simpa [mul_assoc] using mul_inv_eq_iff_eq_mul.mp h'

private theorem suz_sixth {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) {c r ζ : Q}
    (hcov : ∀ s : Q, s ∈ zpowers c ∨ s * r ∈ zpowers c)
    (hζ : ∀ y ∈ zpowers c, y * y = 1 → y = 1 ∨ y = ζ) {T : Subgroup Q}
    (hT : 4 ≤ Nat.card T) : ζ ∈ T := by
  obtain ⟨t₁, ht₁, hrep⟩ := suz_exists_rep hcov T
  have hY : Nat.card T ≤ 2 * Nat.card ↥(T ⊓ zpowers c) := by
    refine suz_card_le_of_cover (n := 2) inf_le_left ![1, t₁] ?_ ?_
    · intro i
      fin_cases i
      · exact T.one_mem
      · exact ht₁
    · intro t ht
      rcases hrep t ht with h | h
      · exact ⟨0, t, ⟨ht, h⟩, by simp⟩
      · exact ⟨1, t * t₁⁻¹, ⟨T.mul_mem ht (T.inv_mem ht₁), h⟩, by simp⟩
  have hY1 : 1 < Nat.card ↥(T ⊓ zpowers c) := by omega
  have : Nontrivial ↥(T ⊓ zpowers c) := Finite.one_lt_card_iff_nontrivial.mp hY1
  obtain ⟨⟨y, hyY⟩, hne⟩ := exists_ne (1 : ↥(T ⊓ zpowers c))
  have hy1 : y ≠ 1 := fun h => hne (Subtype.ext h)
  obtain ⟨n, hn2, hn1⟩ := suz_exists_involution_pow hQ hy1
  have hmem : y ^ n ∈ T ⊓ zpowers c := Subgroup.pow_mem _ hyY n
  rcases hζ _ hmem.2 hn2 with h | h
  · exact absurd h hn1
  · rw [← h]
    exact hmem.1

private theorem suz_card_eq {S : Type*} [Group S] (E : Subgroup S) [E.Normal] (X : Subgroup S) :
    Nat.card X = Nat.card ↥(X ⊓ E) * Nat.card ↥(X.map (QuotientGroup.mk' E)) := by
  let ρ : X →* S ⧸ E := (QuotientGroup.mk' E).comp X.subtype
  have h1 := Subgroup.card_ker_mul_card_range ρ
  have e1 : Nat.card ρ.ker = Nat.card ↥(X ⊓ E) := by
    refine Nat.card_congr
      { toFun := fun n => ⟨n.1.1, n.1.2, by
          have := n.2
          rw [MonoidHom.mem_ker] at this
          exact (QuotientGroup.eq_one_iff _).mp this⟩
        invFun := fun h => ⟨⟨h.1, h.2.1⟩, by
          rw [MonoidHom.mem_ker]
          exact (QuotientGroup.eq_one_iff _).mpr h.2.2⟩
        left_inv := fun n => rfl
        right_inv := fun h => rfl }
  have e2 : Nat.card ρ.range = Nat.card ↥(X.map (QuotientGroup.mk' E)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1, by
          obtain ⟨n, hn⟩ := x.2
          exact ⟨n.1, n.2, hn⟩⟩
        invFun := fun w => ⟨w.1, by
          obtain ⟨h, hh, e⟩ := w.2
          exact ⟨⟨h, hh⟩, e⟩⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
  rw [e1, e2] at h1
  exact h1.symm

private theorem suz_quotient_data {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S)
    {E : Subgroup S} [E.Normal] {a : S} (haE : a ∉ E) (ha2 : a * a ∈ E) {D : Subgroup S}
    (hD : ∀ x : S, x * a * x⁻¹ * a⁻¹ ∈ E → x ∈ D) (hDcard : Nat.card D ≤ 4 * Nat.card E)
    (hS8 : 8 * Nat.card E ≤ Nat.card S) :
    ∃ c r ζ : S ⧸ E, ζ * ζ = 1 ∧ ζ ≠ 1 ∧ (∀ s, s * ζ = ζ * s) ∧
      (∀ s : S ⧸ E, s ∈ zpowers c ∨ s * r ∈ zpowers c) ∧
      (∀ y ∈ zpowers c, y * y = 1 → y = 1 ∨ y = ζ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (S ⧸ E) := hS.to_quotient E
  have hED : E ≤ D := by
    intro x hx
    apply hD
    have h1 : a * x⁻¹ * a⁻¹ ∈ E := Subgroup.Normal.conj_mem inferInstance _ (E.inv_mem hx) a
    have h2 := E.mul_mem hx h1
    rwa [show x * (a * x⁻¹ * a⁻¹) = x * a * x⁻¹ * a⁻¹ by group] at h2
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have hQcard : Nat.card S = Nat.card (S ⧸ E) * Nat.card E :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup E
  have hQ8 : 8 ≤ Nat.card (S ⧸ E) := by
    by_contra h
    push Not at h
    have : Nat.card (S ⧸ E) * Nat.card E < 8 * Nat.card E :=
      Nat.mul_lt_mul_of_pos_right h hEpos
    omega
  have hDm : Nat.card ↥(D.map (QuotientGroup.mk' E)) ≤ 4 := by
    have h1 := suz_card_eq E D
    rw [inf_eq_right.mpr hED] at h1
    by_contra h
    push Not at h
    have : Nat.card E * 4 < Nat.card E * Nat.card ↥(D.map (QuotientGroup.mk' E)) :=
      Nat.mul_lt_mul_of_pos_left h hEpos
    omega
  set r : S ⧸ E := QuotientGroup.mk a with hr
  have hr1 : r ≠ 1 := fun h => haE ((QuotientGroup.eq_one_iff a).mp h)
  have hrr : r * r = 1 := by
    rw [hr, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr ha2
  have hcommD : ∀ x : S ⧸ E, x * r = r * x → x ∈ D.map (QuotientGroup.mk' E) := by
    intro x hx
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨x, hD x ((QuotientGroup.eq_one_iff _).mp ?_), rfl⟩
    calc (QuotientGroup.mk (x * a * x⁻¹ * a⁻¹) : S ⧸ E)
        = QuotientGroup.mk x * r * (QuotientGroup.mk x)⁻¹ * r⁻¹ := by
          simp [hr, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      _ = (r * QuotientGroup.mk x) * (QuotientGroup.mk x)⁻¹ * r⁻¹ := by rw [hx]
      _ = 1 := by group
  have : Nontrivial (S ⧸ E) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have := hQ2.center_nontrivial
  obtain ⟨⟨z', hz'⟩, hz'1⟩ := exists_ne (1 : Subgroup.center (S ⧸ E))
  have hz'ne : z' ≠ 1 := fun h => hz'1 (Subtype.ext h)
  obtain ⟨n, hn2, hn1⟩ := suz_exists_involution_pow hQ2 hz'ne
  have hωc : ∀ s : S ⧸ E, s * z' ^ n = z' ^ n * s :=
    fun s => Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz' n) s
  set ω : S ⧸ E := z' ^ n with hω
  have hωr : ω ≠ r := by
    intro h
    have htop : D.map (QuotientGroup.mk' E) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      refine hcommD x ?_
      rw [← h]
      exact hωc x
    have h4 := hDm
    rw [htop, Subgroup.card_top] at h4
    omega
  have hωr' : ω * r ≠ 1 := by
    intro h
    apply hωr
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_eq_of_mul_eq_one_right hrr
  have hcov : ∀ x : S ⧸ E, x * r = r * x → x = 1 ∨ x = r ∨ x = ω ∨ x = ω * r := by
    intro x hx
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2, h3, h4⟩ := hne
    have hsub := finset_card_le_subgroup ({1, r, ω, ω * r, x} : Finset (S ⧸ E))
      (D.map (QuotientGroup.mk' E)) (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact hcommD _ rfl
        · exact hcommD _ (hωc r).symm
        · refine hcommD _ ?_
          calc ω * r * r = ω := by rw [mul_assoc, hrr, mul_one]
            _ = r * (ω * r) := by rw [← mul_assoc, hωc r, mul_assoc, hrr, mul_one]
        · exact hcommD _ hx)
    have hcard5 : ({1, r, ω, ω * r, x} : Finset (S ⧸ E)).card = 5 := by
      have e1 : (1 : S ⧸ E) ∉ ({r, ω, ω * r, x} : Finset (S ⧸ E)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hr1.symm, hn1.symm, hωr'.symm, h1.symm⟩
      have e2 : r ∉ ({ω, ω * r, x} : Finset (S ⧸ E)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hωr.symm, fun h => hn1 (mul_right_cancel (h.symm.trans (one_mul r).symm)), h2.symm⟩
      have e3 : ω ∉ ({ω * r, x} : Finset (S ⧸ E)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hr1 (mul_left_cancel (h.symm.trans (mul_one ω).symm)), h3.symm⟩
      have e4 : ω * r ∉ ({x} : Finset (S ⧸ E)) := by
        simpa using h4.symm
      rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
        Finset.card_insert_of_notMem e3, Finset.card_insert_of_notMem e4, Finset.card_singleton]
    omega
  obtain ⟨ζ, hζ2, hζ1, hζr, hζc, hζcent⟩ := FourCentralizer.exists_central_of_cover hQ2 hQ8 hr1
    hrr hn2 (hωc r).symm hcov
  have hQ : FourCentralizer (S ⧸ E) r ζ := ⟨hQ2, hrr, hr1, hζ2, hζ1, hζr.symm, hζc, hζcent⟩
  obtain ⟨m, hm⟩ := hQ.two.exists_card_eq
  have hm3 : 3 ≤ m := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
  obtain ⟨c, hcord, hcr⟩ :=
    FourCentralizer.exists_cyclic_index_two (m' + 3) (by omega) (S ⧸ E) r ζ hQ hm
  have hcord' : orderOf c = 2 ^ (m' + 2) := hcord
  obtain ⟨hζc', -, hcover⟩ := hQ.cyclic_structure hm hcord' hcr
  refine ⟨c, r, ζ, hζ2, hζ1, hζc, hcover, fun y hy hy2 => ?_⟩
  rcases FourCentralizer.eq_one_or_eq_of_mul_self_eq_one_of_mem_zpowers (m' := m' + 1) hcord' hy
    hy2 with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hζc'.symm)

@[expose] def HasSuz (S : Type) [Group S] (E : Subgroup S) : Prop :=
  ∃ K : Subgroup S, E ≤ K ∧ K.Normal ∧ Nat.card K = 2 * Nat.card E ∧
    (∀ x ∈ K, x * x ∈ E) ∧ (∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ E) ∧
    (∀ T : Subgroup S, E ≤ T → 4 * Nat.card E ≤ Nat.card T → K ≤ T) ∧
    (∀ T U : Subgroup S, U ≤ T → (∀ x ∈ T, x ^ 2 ∈ U) → (∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ U) →
      Nat.card T * Nat.card ↥(U ⊓ E) ≤ 4 * Nat.card U * Nat.card ↥(T ⊓ E))

theorem hasSuz_of_centralizer {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S)
    {E : Subgroup S} (hEn : ∀ s : S, ∀ e ∈ E, s * e * s⁻¹ ∈ E) {a : S} (haE : a ∉ E)
    (ha2 : a * a ∈ E) {D : Subgroup S} (hD : ∀ x : S, x * a * x⁻¹ * a⁻¹ ∈ E → x ∈ D)
    (hDcard : Nat.card D ≤ 4 * Nat.card E) (hS8 : 8 * Nat.card E ≤ Nat.card S) :
    HasSuz S E := by
  have : E.Normal := ⟨fun e he s => hEn s e he⟩
  obtain ⟨c, r, ζ, hζ2, hζ1, hζc, hcov, hζ⟩ := suz_quotient_data hS haE ha2 hD hDcard hS8
  have hQ2 : IsPGroup 2 (S ⧸ E) := hS.to_quotient E
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf ζ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hζ2) hζ1
  obtain ⟨K, hK⟩ : ∃ K : Subgroup S, K = (zpowers ζ).comap (QuotientGroup.mk' E) := ⟨_, rfl⟩
  have hmemK : ∀ x : S, x ∈ K ↔
      (QuotientGroup.mk x : S ⧸ E) = 1 ∨ (QuotientGroup.mk x : S ⧸ E) = ζ := by
    intro x
    rw [hK, Subgroup.mem_comap]
    exact FourCentralizer.mem_zpowers_iff_of_mul_self_eq_one hζ2 hζ1
  have hEK : E ≤ K := fun e he => (hmemK e).mpr (Or.inl ((QuotientGroup.eq_one_iff e).mpr he))
  have hKmap : K.map (QuotientGroup.mk' E) = zpowers ζ := by
    rw [hK]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective E) _
  refine ⟨K, hEK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK]
    exact Subgroup.Normal.comap (FourCentralizer.normal_zpowers_of_central hζc) _
  · have h1 := suz_card_eq E K
    rw [inf_eq_right.mpr hEK, hKmap, Nat.card_zpowers, hord] at h1
    rw [h1, mul_comm]
  · intro x hx
    refine (QuotientGroup.eq_one_iff _).mp ?_
    rw [QuotientGroup.mk_mul]
    rcases (hmemK x).mp hx with h | h
    · rw [h, mul_one]
    · rw [h]
      exact hζ2
  · intro x hx y hy
    have hc : Commute (QuotientGroup.mk x : S ⧸ E) (QuotientGroup.mk y) := by
      rcases (hmemK x).mp hx with h | h
      · rw [h]
        exact Commute.one_left _
      · rw [h]
        exact (hζc _).symm
    exact (QuotientGroup.eq_one_iff _).mp
      ((map_commutatorElement (QuotientGroup.mk' E) x y).trans
        (commutatorElement_eq_one_iff_commute.mpr hc))
  · intro T hET hT
    have h1 := suz_card_eq E T
    rw [inf_eq_right.mpr hET] at h1
    have h4 : 4 ≤ Nat.card ↥(T.map (QuotientGroup.mk' E)) := by
      by_contra h
      push Not at h
      have : Nat.card E * Nat.card ↥(T.map (QuotientGroup.mk' E)) < Nat.card E * 4 :=
        Nat.mul_lt_mul_of_pos_left h hEpos
      omega
    obtain ⟨t, htT, hζt⟩ := suz_sixth hQ2 hcov hζ h4
    intro x hx
    rcases (hmemK x).mp hx with h | h
    · exact hET ((QuotientGroup.eq_one_iff x).mp h)
    · have hxt : (QuotientGroup.mk t : S ⧸ E) = QuotientGroup.mk x := hζt.trans h.symm
      have hE' : t⁻¹ * x ∈ E := QuotientGroup.eq.mp hxt
      have hx' : x = t * (t⁻¹ * x) := by group
      rw [hx']
      exact T.mul_mem htT (hET hE')
  · intro T U hUT hsq _
    have h1 := suz_card_eq E T
    have h2 := suz_card_eq E U
    have h3 : Nat.card ↥(T.map (QuotientGroup.mk' E)) ≤
        4 * Nat.card ↥(U.map (QuotientGroup.mk' E)) := by
      refine suz_seventh hcov (Subgroup.map_mono hUT) ?_
      rintro _ ⟨x, hxT, rfl⟩
      exact ⟨x ^ 2, hsq x hxT, map_pow _ _ _⟩
    rw [h1, h2]
    calc Nat.card ↥(T ⊓ E) * Nat.card ↥(T.map (QuotientGroup.mk' E)) * Nat.card ↥(U ⊓ E)
        = (Nat.card ↥(T ⊓ E) * Nat.card ↥(U ⊓ E)) * Nat.card ↥(T.map (QuotientGroup.mk' E)) := by
          ring
      _ ≤ (Nat.card ↥(T ⊓ E) * Nat.card ↥(U ⊓ E)) *
          (4 * Nat.card ↥(U.map (QuotientGroup.mk' E))) := Nat.mul_le_mul_left _ h3
      _ = 4 * (Nat.card ↥(U ⊓ E) * Nat.card ↥(U.map (QuotientGroup.mk' E))) *
          Nat.card ↥(T ⊓ E) := by ring

end CFSG.OddStandard.Harada75
