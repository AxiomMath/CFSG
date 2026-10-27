module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseLabels
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseForms

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ}
  {κ' : Type*} {J : Finset κ'} {χ : κ' → ι} {y₀ C : ι → ℤ} {xj : κ' → ι → ℤ} {M : ℕ}
  {γ : ℕ → Fin 4 → ι} {ε : ℕ → Fin 4 → ℤ} {xk yr : ℕ → ι → ℤ} {cd cd' : ℕ → ι → ℤ}
  {β : Type*} {V : Finset β} {dg : β → ι → ℤ}

theorem diag_degree (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) {γ' : Fin 4 → ι}
    {ε' : Fin 4 → ℤ} {xk' yr' : ι → ℤ} (hQ : Quadruple B p A Bq Dq ω σ τ₀ κ J χ γ' ε' xk' yr')
    {b d : ι → ℤ} (hb1 : b p = 1) (hbA : b A = -σ) (hbB : b Bq = 0) (hbD : b Dq = 0)
    (hbω : b ω = 2 * τ₀) (hbχ : ∀ j ∈ J, b (χ j) = 0)
    (hb0 : ∀ φ ∈ B, Outside p A Bq Dq ω J χ γ' φ → b φ = 0) (hdeg : ∑ φ ∈ B, d φ * b φ = 0) :
    d p - σ * d A + 2 * τ₀ * d ω + ∑ l, b (γ' l) * d (γ' l) = 0 := by
  have hJ0 : ∑ j ∈ J, d (χ j) * b (χ j) = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hbχ j hj, mul_zero]
  have hR0 : ∑ φ ∈ B.filter (Outside p A Bq Dq ω J χ γ'), d φ * b φ = 0 :=
    Finset.sum_eq_zero fun φ hφ => by
      rw [hb0 φ (Finset.mem_filter.mp hφ).1 (Finset.mem_filter.mp hφ).2, mul_zero]
  rw [hS.sum_split hQ, hb1, hbA, hbB, hbD, hbω, hJ0, hR0] at hdeg
  rw [← hdeg, Finset.sum_congr rfl fun l _ => mul_comm (b (γ' l)) (d (γ' l))]
  ring

theorem Quadruple.xk_apply {γ' : Fin 4 → ι} {ε' : Fin 4 → ℤ} {xk' yr' : ι → ℤ}
    (hQ : Quadruple B p A Bq Dq ω σ τ₀ κ J χ γ' ε' xk' yr') (l : Fin 4) : xk' (γ' l) = ε' l := by
  obtain ⟨c1, c2, c3, c4, -⟩ := hQ.core l
  rw [hQ.hxk _ (hQ.mem l), fixedPart_of_ne σ τ₀ κ c1 c2 c3 c4, zero_add,
    Finset.sum_eq_single l (fun l' _ hl' => by
      rw [unitVector_of_ne fun h => hl' (hQ.inj h).symm, mul_zero])
    fun h => absurd (Finset.mem_univ l) h, unitVector_self, mul_one]


theorem BaseFamily.diag_labels
    (hF : BaseFamily B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj M γ ε xk yr cd cd' V dg)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) (hM : 2 ≤ M) (hJ : M ≤ J.card)
    (hnv : ∀ φ ∈ B, ∀ ξ : ℤ, Outside0 p A Bq Dq ω J χ φ →
      (∀ t ∈ Finset.Ico 1 M, ∀ l, φ ≠ γ t l) →
      (∀ t ∈ Finset.Ico 1 M, cd t φ = ξ ∧ cd' t φ = ξ) → (∀ I ∈ V, dg I φ = ξ) → False)
    {d : ι → ℤ} (hd : ∀ φ ∈ B, 0 < d φ)
    (hK1 : d p - σ * d A + 2 * τ₀ * d ω = τ₀ * d Bq + κ * d Dq)
    (hpair : ∀ r ∈ Finset.Ico 1 M,
      ε r 0 * d (γ r 0) + ε r 1 * d (γ r 1) = τ₀ * d Bq - κ * d Dq ∧
        ε r 2 * d (γ r 2) + ε r 3 * d (γ r 3) = τ₀ * d Bq - κ * d Dq)
    (hdegd : ∀ r ∈ Finset.Ico 1 M, ∑ φ ∈ B, d φ * cd r φ = 0 ∧ ∑ φ ∈ B, d φ * cd' r φ = 0)
    {r : ℕ} (hr : r ∈ Finset.Ico 1 M) :
    ∃ P Q : Fin 2 → ι, ((P 0 = γ r 0 ∧ Q 0 = γ r 1) ∨ (P 0 = γ r 1 ∧ Q 0 = γ r 0)) ∧
      ((P 1 = γ r 2 ∧ Q 1 = γ r 3) ∨ (P 1 = γ r 3 ∧ Q 1 = γ r 2)) ∧
      (∀ e, d (P e) = d Bq ∧ d (Q e) = d Dq ∧ xk r (P e) = τ₀ ∧ xk r (Q e) = -κ) ∧
      (((∀ φ ∈ B, cd r φ = baseFixed p A ω σ τ₀ φ - τ₀ * unitVector (P 0) φ -
            κ * unitVector (Q 0) φ) ∧
          (∀ φ ∈ B, cd' r φ = baseFixed p A ω σ τ₀ φ - τ₀ * unitVector (P 1) φ -
            κ * unitVector (Q 1) φ)) ∨
        ((∀ φ ∈ B, cd r φ = baseFixed p A ω σ τ₀ φ - τ₀ * unitVector (P 1) φ -
            κ * unitVector (Q 1) φ) ∧
          (∀ φ ∈ B, cd' r φ = baseFixed p A ω σ τ₀ φ - τ₀ * unitVector (P 0) φ -
            κ * unitVector (Q 0) φ))) := by
  obtain ⟨⟨hc1, hcA, hcB, hcD, hcω, hcχ, hc0⟩, ⟨hc1', hcA', hcB', hcD', hcω', hcχ', hc0'⟩,
    s, s', hs, hs', hpairs⟩ := hF.diag_form hS hM hJ hnv hr
  have hQ := hF.quad r hr
  have hdB : 0 < d Bq := hd Bq hS.hBq
  have hdD : 0 < d Dq := hd Dq hS.hDq
  have hdγ : ∀ l, 0 < d (γ r l) := fun l => hd _ (hQ.mem l)
  have hdeg := diag_degree hS hQ hc1 hcA hcB hcD hcω hcχ hc0 (hdegd r hr).1
  have hdeg' := diag_degree hS hQ hc1' hcA' hcB' hcD' hcω' hcχ' hc0' (hdegd r hr).2
  rw [hK1, Fin.sum_univ_four] at hdeg hdeg'
  have hx := hQ.xk_apply
  have hne : ∀ l l', l ≠ l' → γ r l ≠ γ r l' := fun l l' h e => h (hQ.inj e)
  rcases hpairs with ⟨⟨c0, c1, c2, c3⟩, ⟨c0', c1', c2', c3'⟩⟩ |
      ⟨⟨c0, c1, c2, c3⟩, ⟨c0', c1', c2', c3'⟩⟩
  ·
    rw [c2, c3] at hdeg
    rw [c0', c1'] at hdeg'
    obtain ⟨P₀, Q₀, hPQ₀, hdP₀, hdQ₀, hxP₀, hxQ₀, hbP₀, hbQ₀⟩ := two_point_labels
      (hQ.sign 0) (hQ.sign 1) hs hS.hτ₀ hS.hκ (hdγ 0) (hdγ 1) hdB hdD c0 c1 (hx 0) (hx 1)
      (hpair r hr).1 rfl (by linarith only [hdeg])
    obtain ⟨P₁, Q₁, hPQ₁, hdP₁, hdQ₁, hxP₁, hxQ₁, hbP₁, hbQ₁⟩ := two_point_labels
      (hQ.sign 2) (hQ.sign 3) hs' hS.hτ₀ hS.hκ (hdγ 2) (hdγ 3) hdB hdD c2' c3' (hx 2) (hx 3)
      (hpair r hr).2 rfl (by linarith only [hdeg'])
    refine ⟨![P₀, P₁], ![Q₀, Q₁], hPQ₀, hPQ₁, fun e => ?_, Or.inl ⟨?_, ?_⟩⟩
    · fin_cases e
      · exact ⟨hdP₀, hdQ₀, hxP₀, hxQ₀⟩
      · exact ⟨hdP₁, hdQ₁, hxP₁, hxQ₁⟩
    · refine diag_rep hS hQ hc1 hcA hcB hcD hcω hcχ hc0 ?_ ?_ ?_ hbP₀ hbQ₀ ?_
      · rcases hPQ₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hne _ _ (by decide)
      · rcases hPQ₀ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨_, rfl⟩
      · rcases hPQ₀ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨_, rfl⟩
      · intro l h1 h2
        fin_cases l
        · rcases hPQ₀ with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> first | exact absurd rfl h1 | exact absurd rfl h2
        · rcases hPQ₀ with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> first | exact absurd rfl h1 | exact absurd rfl h2
        · exact c2
        · exact c3
    · refine diag_rep hS hQ hc1' hcA' hcB' hcD' hcω' hcχ' hc0' ?_ ?_ ?_ hbP₁ hbQ₁ ?_
      · rcases hPQ₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hne _ _ (by decide)
      · rcases hPQ₁ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨_, rfl⟩
      · rcases hPQ₁ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨_, rfl⟩
      · intro l h1 h2
        fin_cases l
        · exact c0'
        · exact c1'
        · rcases hPQ₁ with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> first | exact absurd rfl h1 | exact absurd rfl h2
        · rcases hPQ₁ with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> first | exact absurd rfl h1 | exact absurd rfl h2
  ·
    rw [c0, c1] at hdeg
    rw [c2', c3'] at hdeg'
    obtain ⟨P₀, Q₀, hPQ₀, hdP₀, hdQ₀, hxP₀, hxQ₀, hbP₀, hbQ₀⟩ := two_point_labels
      (hQ.sign 0) (hQ.sign 1) hs' hS.hτ₀ hS.hκ (hdγ 0) (hdγ 1) hdB hdD c0' c1' (hx 0) (hx 1)
      (hpair r hr).1 rfl (by linarith only [hdeg'])
    obtain ⟨P₁, Q₁, hPQ₁, hdP₁, hdQ₁, hxP₁, hxQ₁, hbP₁, hbQ₁⟩ := two_point_labels
      (hQ.sign 2) (hQ.sign 3) hs hS.hτ₀ hS.hκ (hdγ 2) (hdγ 3) hdB hdD c2 c3 (hx 2) (hx 3)
      (hpair r hr).2 rfl (by linarith only [hdeg])
    refine ⟨![P₀, P₁], ![Q₀, Q₁], hPQ₀, hPQ₁, fun e => ?_, Or.inr ⟨?_, ?_⟩⟩
    · fin_cases e
      · exact ⟨hdP₀, hdQ₀, hxP₀, hxQ₀⟩
      · exact ⟨hdP₁, hdQ₁, hxP₁, hxQ₁⟩
    · refine diag_rep hS hQ hc1 hcA hcB hcD hcω hcχ hc0 ?_ ?_ ?_ hbP₁ hbQ₁ ?_
      · rcases hPQ₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hne _ _ (by decide)
      · rcases hPQ₁ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨_, rfl⟩
      · rcases hPQ₁ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨_, rfl⟩
      · intro l h1 h2
        fin_cases l
        · exact c0
        · exact c1
        · rcases hPQ₁ with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> first | exact absurd rfl h1 | exact absurd rfl h2
        · rcases hPQ₁ with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> first | exact absurd rfl h1 | exact absurd rfl h2
    · refine diag_rep hS hQ hc1' hcA' hcB' hcD' hcω' hcχ' hc0' ?_ ?_ ?_ hbP₀ hbQ₀ ?_
      · rcases hPQ₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hne _ _ (by decide)
      · rcases hPQ₀ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨_, rfl⟩
      · rcases hPQ₀ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨_, rfl⟩
      · intro l h1 h2
        fin_cases l
        · rcases hPQ₀ with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> first | exact absurd rfl h1 | exact absurd rfl h2
        · rcases hPQ₀ with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> first | exact absurd rfl h1 | exact absurd rfl h2
        · exact c2'
        · exact c3'


theorem BaseFamily.generic_labels
    (hF : BaseFamily B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj M γ ε xk yr cd cd' V dg)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) (hM : 2 ≤ M) (hJ : M ≤ J.card)
    (hnv : ∀ φ ∈ B, ∀ ξ : ℤ, Outside0 p A Bq Dq ω J χ φ →
      (∀ t ∈ Finset.Ico 1 M, ∀ l, φ ≠ γ t l) →
      (∀ t ∈ Finset.Ico 1 M, cd t φ = ξ ∧ cd' t φ = ξ) → (∀ I ∈ V, dg I φ = ξ) → False)
    {d : ι → ℤ} (hd : ∀ φ ∈ B, 0 < d φ)
    (hK1 : d p - σ * d A + 2 * τ₀ * d ω = τ₀ * d Bq + κ * d Dq)
    (hdegg : ∀ I ∈ V, ∑ φ ∈ B, d φ * dg I φ = 0) (hV : V.Nonempty) :
    ∃ (ψ : β → ι) (ρ₀ Δ : ℤ), (ρ₀ = 1 ∨ ρ₀ = -1) ∧ 0 < Δ ∧
      ρ₀ * Δ = -(τ₀ * d Bq + κ * d Dq) ∧ Set.InjOn ψ V ∧
      ∀ I ∈ V, ψ I ∈ B ∧ Outside0 p A Bq Dq ω J χ (ψ I) ∧
        (∀ t ∈ Finset.Ico 1 M, ∀ l, ψ I ≠ γ t l) ∧ d (ψ I) = Δ ∧
        (∀ φ ∈ B, Outside0 p A Bq Dq ω J χ φ → φ ≠ ψ I → dg I φ = 0) ∧
        ∀ φ ∈ B, dg I φ = baseFixed p A ω σ τ₀ φ + ρ₀ * unitVector (ψ I) φ := by
  have hgf : ∀ I, ∃ ψ : ι, I ∈ V → ψ ∈ B ∧ Outside0 p A Bq Dq ω J χ ψ ∧
      (∀ t ∈ Finset.Ico 1 M, ∀ l, ψ ≠ γ t l) ∧ (dg I ψ = 1 ∨ dg I ψ = -1) ∧
      ∀ φ ∈ B, Outside0 p A Bq Dq ω J χ φ → φ ≠ ψ → dg I φ = 0 := by
    intro I
    by_cases hI : I ∈ V
    · obtain ⟨-, -, -, -, -, -, ψ, hψ⟩ := hF.generic_form hS hM hJ hnv hI
      exact ⟨ψ, fun _ => hψ⟩
    · exact ⟨p, fun h => absurd h hI⟩
  choose ψ hψ using hgf
  have hcore : ∀ I ∈ V, dg I p = 1 ∧ dg I A = -σ ∧ dg I Bq = 0 ∧ dg I Dq = 0 ∧
      dg I ω = 2 * τ₀ ∧ ∀ j ∈ J, dg I (χ j) = 0 := fun I hI => by
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hF.generic_form hS hM hJ hnv hI
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hRsum : ∀ I ∈ V, ∀ g : ι → ℤ, ∑ φ ∈ B.filter (Outside0 p A Bq Dq ω J χ), g φ * dg I φ =
      g (ψ I) * dg I (ψ I) := by
    intro I hI g
    obtain ⟨hψB, hψO, -, -, hz⟩ := hψ I hI
    rw [Finset.sum_eq_single (ψ I) (fun φ hφ hne => by
        rw [hz φ (Finset.mem_filter.mp hφ).1 (Finset.mem_filter.mp hφ).2 hne, mul_zero])
      fun h => absurd (Finset.mem_filter.mpr ⟨hψB, hψO⟩) h]
  have hdegrel : ∀ I ∈ V, dg I (ψ I) * d (ψ I) = -(τ₀ * d Bq + κ * d Dq) := by
    intro I hI
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcore I hI
    have h := hdegg I hI
    rw [hS.sum_split0, h1, h2, h3, h4, h5,
      Finset.sum_eq_zero fun j hj => by rw [h6 j hj, mul_zero], hRsum I hI d] at h
    linarith only [h, hK1]
  obtain ⟨I₀, hI₀⟩ := hV
  set ρ₀ := dg I₀ (ψ I₀) with hρ₀
  set Δ := d (ψ I₀) with hΔ
  have hρs : ρ₀ = 1 ∨ ρ₀ = -1 := (hψ I₀ hI₀).2.2.2.1
  have hΔpos : 0 < Δ := hd _ (hψ I₀ hI₀).1
  have hsame : ∀ I ∈ V, dg I (ψ I) = ρ₀ ∧ d (ψ I) = Δ := by
    intro I hI
    have h1 := hdegrel I hI
    have h0 := hdegrel I₀ hI₀
    have hpos := hd _ (hψ I hI).1
    rcases (hψ I hI).2.2.2.1 with h | h <;> rcases hρs with h' | h' <;>
      rw [h] at h1 <;> rw [← hρ₀, ← hΔ, h'] at h0 <;> rw [h'] <;> constructor <;> linarith
  refine ⟨ψ, ρ₀, Δ, hρs, hΔpos, by rw [← hdegrel I₀ hI₀], ?_, fun I hI => ⟨(hψ I hI).1,
    (hψ I hI).2.1, (hψ I hI).2.2.1, (hsame I hI).2, (hψ I hI).2.2.2.2, fun φ hφ => ?_⟩⟩
  ·
    intro I hI I' hI' heq
    by_contra hne
    have h := hF.prod_gen_gen I hI I' hI' hne
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcore I hI
    obtain ⟨h1', h2', h3', h4', h5', -⟩ := hcore I' hI'
    rw [hS.inner_split0 h6, Finset.sum_congr rfl fun φ _ => mul_comm (dg I φ) (dg I' φ),
      hRsum I hI (dg I'), h1, h2, h3, h4, h5, h1', h2', h3', h4', h5'] at h
    have hρI := (hsame I hI).1
    have hρI' : dg I' (ψ I) = ρ₀ := by rw [heq]; exact (hsame I' hI').1
    rw [hρI, hρI'] at h
    have hσ2 : σ * σ = 1 := by rcases hS.hσ with h | h <;> rw [h] <;> norm_num
    have hτ2 : τ₀ * τ₀ = 1 := by rcases hS.hτ₀ with h | h <;> rw [h] <;> norm_num
    have hρ2 : ρ₀ * ρ₀ = 1 := by rcases hρs with h | h <;> rw [h] <;> norm_num
    linarith only [h, hσ2, hτ2, hρ2]
  ·
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcore I hI
    obtain ⟨hψB, hψO, -, -, hz⟩ := hψ I hI
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hψO
    simp only [baseFixed, unitVector]
    by_cases e1 : φ = p
    · subst e1
      simp [h1, hS.hAp.symm, hS.hωp.symm, n1.symm]
    by_cases e2 : φ = A
    · subst e2
      simp [h2, hS.hAp, hS.hωA.symm, n2.symm]
    by_cases e3 : φ = ω
    · subst e3
      simp [h5, hS.hωp, hS.hωA, n5.symm]
    by_cases e4 : φ = ψ I
    · subst e4
      simp [n1, n2, n5, (hsame I hI).1]
    simp only [e1, e2, e3, e4, ite_false, mul_zero, sub_zero, add_zero]
    by_cases e5 : φ = Bq
    · subst e5
      exact h3
    by_cases e6 : φ = Dq
    · subst e6
      exact h4
    by_cases e7 : ∃ j ∈ J, φ = χ j
    · obtain ⟨j, hj, rfl⟩ := e7
      exact h6 j hj
    push Not at e7
    exact hz φ hφ ⟨e1, e2, e5, e6, e3, e7⟩ e4

theorem BaseFamily.exhaustion
    (hF : BaseFamily B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj M γ ε xk yr cd cd' V dg)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) (hM : 2 ≤ M) (hJ : M ≤ J.card)
    (hnv : ∀ φ ∈ B, ∀ ξ : ℤ, Outside0 p A Bq Dq ω J χ φ →
      (∀ t ∈ Finset.Ico 1 M, ∀ l, φ ≠ γ t l) →
      (∀ t ∈ Finset.Ico 1 M, cd t φ = ξ ∧ cd' t φ = ξ) → (∀ I ∈ V, dg I φ = ξ) → False)
    {ψ : β → ι}
    (hψ : ∀ I ∈ V, ∀ φ ∈ B, Outside0 p A Bq Dq ω J χ φ → φ ≠ ψ I → dg I φ = 0) :
    ∀ φ ∈ B, φ = p ∨ φ = A ∨ φ = Bq ∨ φ = Dq ∨ φ = ω ∨ (∃ j ∈ J, φ = χ j) ∨
      (∃ t ∈ Finset.Ico 1 M, ∃ l, φ = γ t l) ∨ ∃ I ∈ V, φ = ψ I := by
  intro φ hφ
  by_contra hno
  push Not at hno
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := hno
  have hout0 : Outside0 p A Bq Dq ω J χ φ := ⟨n1, n2, n3, n4, n5, n6⟩
  refine hnv φ hφ 0 hout0 n7 (fun t ht => ?_) fun I hI => hψ I hI φ hφ hout0 (n8 I hI)
  obtain ⟨⟨-, -, -, -, -, -, h0⟩, ⟨-, -, -, -, -, -, h0'⟩, -⟩ := hF.diag_form hS hM hJ hnv ht
  have hout : Outside p A Bq Dq ω J χ (γ t) φ := outside_iff.mpr ⟨hout0, n7 t ht⟩
  exact ⟨h0 φ hφ hout, h0' φ hφ hout⟩

end CFSG.Wreathed.ConditionalCompleteBase
