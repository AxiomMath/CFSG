module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallGen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitF5B4
public import CFSG.Goldschmidt75.CorollaryB3
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Tools

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem data_of_mulEquiv {D : Subgroup G} {k : ℕ} [NeZero k] (e : D ≃* DihedralGroup k) :
    ∃ c ∈ D, orderOf c = k ∧ Nat.card D = 2 * k ∧
      ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹) := by
  set c := (e.symm (r 1) : G) with hcdef
  have hcD : c ∈ D := (e.symm (r 1)).2
  have hinj : ∀ {x y : G} (hx : x ∈ D) (hy : y ∈ D), e ⟨x, hx⟩ = e ⟨y, hy⟩ → x = y :=
    fun hx hy h => congrArg Subtype.val (e.injective h)
  have hec : e ⟨c, hcD⟩ = r 1 := e.apply_symm_apply _
  have hmul : ∀ {x y : G} (hx : x ∈ D) (hy : y ∈ D),
      e ⟨x * y, mul_mem hx hy⟩ = e ⟨x, hx⟩ * e ⟨y, hy⟩ := fun hx hy => by
    rw [← map_mul]; rfl
  have hinv : ∀ {x : G} (hx : x ∈ D), e ⟨x⁻¹, inv_mem hx⟩ = (e ⟨x, hx⟩)⁻¹ := fun hx => by
    rw [← map_inv]; rfl
  refine ⟨c, hcD, ?_, ?_, ?_⟩
  · rw [hcdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_r_one]
  · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  · intro x hx
    rcases h : e ⟨x, hx⟩ with i | i
    · left
      refine mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
      rw [zpow_natCast]
      apply hinj (pow_mem hcD _) hx
      have hp : e ⟨c ^ i.val, pow_mem hcD _⟩ = e ⟨c, hcD⟩ ^ i.val := by
        rw [← map_pow]; rfl
      rw [hp, hec, h, r_one_pow, ZMod.natCast_zmod_val]
    · right
      constructor
      · apply hinj (mul_mem hx hx) (one_mem D)
        rw [hmul hx hx, h, sr_mul_self, ← map_one e]
        rfl
      · apply hinj (mul_mem (mul_mem hx hcD) (inv_mem hx)) (inv_mem hcD)
        rw [hmul (mul_mem hx hcD) (inv_mem hx), hmul hx hcD, hinv hx, hinv hcD, h, hec,
          inv_sr, sr_mul_r, sr_mul_sr, inv_r]
        congr 1
        ring

@[expose] def HallWeakConclusion (D : Subgroup G) : Prop :=
  ∃ S₀ T : Subgroup G, IsSylowOf 2 T ⊤ ∧ D ≤ S₀ ∧ S₀ ≤ T ∧
    Open.fusionStronglyClosed (S₀ : Set G) T ∧ (∀ x ∈ S₀, x * x = 1 → x ∈ D) ∧
    Nat.card S₀ ≤ 2 * Nat.card D

theorem inv_mul_mem_of_card_le {D S₀ : Subgroup G} (hDS : D ≤ S₀)
    (hcard : Nat.card S₀ ≤ 2 * Nat.card D) {s s' : G} (hs : s ∈ S₀) (hs' : s' ∈ S₀)
    (hsD : s ∉ D) (hs'D : s' ∉ D) : s⁻¹ * s' ∈ D := by
  set H := D.subgroupOf S₀ with hH
  have hHc : Nat.card H = Nat.card D := Nat.card_congr (subgroupOfEquivOfLe hDS).toEquiv
  have hidx := card_mul_index H
  rw [hHc] at hidx
  have hD0 : 0 < Nat.card D := Nat.card_pos
  have hi : H.index = 1 ∨ H.index = 2 := by
    have h1 : H.index ≤ 2 := by
      by_contra h
      push Not at h
      have : Nat.card D * 3 ≤ Nat.card D * H.index := Nat.mul_le_mul_left _ (by omega)
      omega
    have h2 : H.index ≠ 0 := index_ne_zero_of_finite
    omega
  rcases hi with h1 | h2
  · exfalso
    rw [index_eq_one] at h1
    have : (⟨s, hs⟩ : S₀) ∈ H := h1 ▸ mem_top _
    exact hsD this
  · have h := (mul_mem_iff_of_index_two h2 (a := (⟨s, hs⟩ : S₀)⁻¹) (b := ⟨s', hs'⟩)).mpr
      (by
        constructor
        · intro h
          exact absurd (by simpa [hH, mem_subgroupOf] using h) hsD
        · intro h
          exact absurd (by simpa [hH, mem_subgroupOf] using h) hs'D)
    simpa [hH, mem_subgroupOf] using h

theorem card_le_four_of_weak
    {D : Subgroup G} (hD : AschbacherTheorem3.IsDihedralTwoGroup D) (h8 : 8 ≤ Nat.card D)
    (hW : HallWeakConclusion D) {P : Subgroup G} (hP : IsSylowOf 2 P (normalClosure (D : Set G)))
    {E : Subgroup G} (hEP : E ≤ P) (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, T, hT, hDS₀, hS₀T, hsc, hinv, hcard⟩ := hW
  obtain ⟨n, hn, ⟨e⟩⟩ := id hD
  have hcardD : Nat.card D = 2 * 2 ^ (n - 1) := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
  obtain ⟨c, hcD, hco, hDc, hDd⟩ := data_of_mulEquiv e
  rw [← hco] at hDc
  have key : ∀ m ∈ normalizer (S₀ : Set G), ∀ d ∈ D, m * d * m⁻¹ ∈ D := by
    intro m hm d hd
    obtain ⟨a, ha, b, hb, ha2, hb2, rfl⟩ := exists_mul hDd hDc hd
    have hconj : ∀ x ∈ D, x * x = 1 → m * x * m⁻¹ ∈ D := fun x hx hx2 =>
      hinv _ ((mem_normalizer_iff.mp hm x).mp (hDS₀ hx)) (by
        rw [show m * x * m⁻¹ * (m * x * m⁻¹) = m * (x * x) * m⁻¹ by group, hx2]; group)
    rw [show m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) by group]
    exact mul_mem (hconj a ha ha2) (hconj b hb hb2)
  have hND : ∀ m ∈ normalizer (S₀ : Set G), m ∈ normalizer (D : Set G) := by
    intro m hm
    refine mem_normalizer_iff.mpr fun d => ⟨key m hm d, fun h => ?_⟩
    have := key m⁻¹ (inv_mem hm) _ h
    rwa [inv_inv, show m⁻¹ * (m * d * m⁻¹) * m = d by group] at this
  have hAut := FooteLit.F5.isPGroup_mulAut_of_dihedral hD h8
  have hN : ∀ m ∈ normalizer (S₀ : Set G), ∃ k : ℕ, m ^ (2 ^ k) ∈ centralizer (S₀ : Set G) := by
    intro m hm
    obtain ⟨a, ha⟩ := FooteLit.F5.pow_mem_centralizer_of_isPGroup_mulAut hAut (hND m hm)
    set m' := m ^ (2 ^ a) with hm'
    have hm'N : m' ∈ normalizer (S₀ : Set G) := pow_mem hm _
    have hcomm : ∀ d ∈ D, m' * d = d * m' := fun d hd => (mem_centralizer_iff.mp ha d hd).symm
    refine ⟨a + n, ?_⟩
    rw [pow_add, pow_mul, mem_centralizer_iff]
    intro s hs
    set s' := m' * s * m'⁻¹ with hs'
    have hs'S : s' ∈ S₀ := (mem_normalizer_iff.mp hm'N s).mp hs
    have hd : s⁻¹ * s' ∈ D := by
      by_cases hsD : s ∈ D
      · rw [hs', hcomm s hsD, mul_inv_cancel_right, inv_mul_cancel]
        exact one_mem _
      · have hs'D : s' ∉ D := fun h => hsD (by
          have : s = m'⁻¹ * s' * m' := by rw [hs']; group
          rw [this, show m'⁻¹ * s' * m' = m'⁻¹ * (s' * m') by group, ← hcomm s' h]
          group
          exact h)
        exact inv_mul_mem_of_card_le hDS₀ hcard hs hs'S hsD hs'D
    set d := s⁻¹ * s' with hddef
    have hpow : ∀ j : ℕ, m' ^ j * s * (m' ^ j)⁻¹ = s * d ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hdj : m' * d ^ j * m'⁻¹ = d ^ j := by
          rw [hcomm _ (pow_mem hd j), mul_inv_cancel_right]
        calc m' ^ (j + 1) * s * (m' ^ (j + 1))⁻¹ = m' * (m' ^ j * s * (m' ^ j)⁻¹) * m'⁻¹ := by
              group
          _ = (m' * s * m'⁻¹) * (m' * d ^ j * m'⁻¹) := by rw [ih]; group
          _ = s * d ^ (j + 1) := by
            rw [hdj, ← hs', show s' = s * d by rw [hddef]; group, pow_succ', mul_assoc]
    have hd1 : d ^ (2 ^ n) = 1 := by
      have h1 := Subgroup.orderOf_dvd_natCard D hd
      rw [hcardD, show 2 * 2 ^ (n - 1) = 2 ^ n by
        rw [← pow_succ']; congr 1; omega] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    have h := hpow (2 ^ n)
    rw [hd1, mul_one] at h
    calc s * m' ^ 2 ^ n = m' ^ 2 ^ n * s * (m' ^ 2 ^ n)⁻¹ * m' ^ 2 ^ n := by rw [h]
      _ = m' ^ 2 ^ n * s := by group
  obtain ⟨T', hT'⟩ : ∃ T' : Sylow 2 G, (T' : Subgroup G) = T := by
    have h := hT.card_eq
    rw [Subgroup.card_top] at h
    exact ⟨Sylow.ofCard T h, Sylow.coe_ofCard _ _⟩
  have hB3 := Goldschmidt75.corollaryB3 T' (hT' ▸ hS₀T) (by rw [hT']; exact hsc) hN
  obtain ⟨hle, hp, hmax⟩ := hB3
  obtain ⟨B, hB, hS₀B⟩ := FooteLit.exists_isSylowOf_ge_of_le hle hp
  have hBeq : B = S₀ := hmax B hB.le hB.isPGroup hS₀B
  rw [hBeq] at hB
  have hPM : P ≤ normalClosure (S₀ : Set G) :=
    hP.le.trans (normalClosure_mono (show (D : Set G) ⊆ S₀ from hDS₀))
  obtain ⟨k, -, hk⟩ := FooteLit.exists_conj_le_of_isSylowOf hB hPM hP.isPGroup
  have hEk : E.map (MulAut.conj k⁻¹).toMonoidHom ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj k⁻¹).toMonoidHom x ∈ S₀ := by simpa using hk x (hEP hx)
    refine hinv _ h1 ?_
    rw [← map_mul, hE x hx, map_one]
  have hEk2 : ∀ y ∈ E.map (MulAut.conj k⁻¹).toMonoidHom, y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE x hx, map_one]
  have h4 := Foote5.card_le_four_of_dihedral_or_semidihedral (Or.inl hD) hEk hEk2
  rwa [card_map_of_injective (MulAut.conj k⁻¹).injective] at h4

end CFSG.ComponentClassification.Foote5.HallGen
