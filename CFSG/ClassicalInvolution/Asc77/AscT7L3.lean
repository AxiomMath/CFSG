module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Inv
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyMat
public import CFSG.ClassicalInvolution.RouteD.MultiStarModel

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected

variable (p : ℕ) [Fact p.Prime]

@[expose] def TwinCentralFact : Prop :=
  ∀ (t : StatedLieTag) (k e : ℕ), StatedLieAdmissible t k p e → p ≠ 2 → 5 ≤ p ^ e →
    ((t = .PSL ∧ k = 4 ∧ p ^ e % 4 = 1) ∨ (t = .PSU ∧ k = 4 ∧ p ^ e % 4 = 3) ∨
      (t = .POmegaOdd ∧ k = 3) ∨ (t = .POmegaPlus ∧ k = 4) ∨ (t = .POmegaMinus ∧ k = 4)) →
    ∀ R ∈ ModelFund p t k e, ∀ R' ∈ ModelFund p t k e, R ≠ R' → Commutes R R' →
      ∀ x ∈ R, x * x = 1 → x ≠ 1 → ∀ x' ∈ R', x' * x' = 1 → x' ≠ 1 →
        x * x' ∈ Subgroup.center (modelUniv t k p e Fact.out).K →
        ∀ a ∈ R, a * a = x → ∀ b ∈ R', b * b = x' →
          ∃ R'' ∈ ModelFund p t k e, ∀ r ∈ R'', (a * b) * r = r * (a * b)

variable {p}

namespace T7L

section Model

variable {f : ℕ} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twin_lifts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ) {tg : StatedLieTag}
    {k ee : ℕ} (M : Ih8Model p f Φ tg k ee) (hG2 : tg ≠ .G2) (hD4 : tg ≠ .trialityD4)
    (hnpsl : ¬ (tg = .PSL ∧ k = 2)) {A A' : Subgroup X} {z a₀ b₀ : X} (hA : A ∈ Φ)
    (hA' : A' ∈ Φ) (hne : A ≠ A') (hzA : IsUniqueInvolution A z)
    (hzA' : IsUniqueInvolution A' z) (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∈ A') (ha₀sq : a₀ * a₀ = z)
    (hb₀sq : b₀ * b₀ = z) :
    ∃ (RA RA' : Subgroup (modelUniv tg k p ee Fact.out).K)
      (a b x x' : (modelUniv tg k p ee Fact.out).K),
      RA ∈ M.cls ∧ RA' ∈ M.cls ∧ RA ≠ RA' ∧ Commutes RA RA' ∧ x ∈ RA ∧ x * x = 1 ∧ x ≠ 1 ∧
        x' ∈ RA' ∧ x' * x' = 1 ∧ x' ≠ 1 ∧
        x * x' ∈ Subgroup.center (modelUniv tg k p ee Fact.out).K ∧ a ∈ RA ∧ a * a = x ∧
        b ∈ RA' ∧ b * b = x' ∧ M.ψ a = a₀ ∧ M.ψ b = b₀ ∧ M.ψ x = z ∧ M.ψ x' = z := by
  classical
  have hee : ee = f := M.exp_eq_f hD4
  obtain ⟨RA, hRA, rfl⟩ := (M.mem_iff A).mp hA
  obtain ⟨RA', hRA', rfl⟩ := (M.mem_iff A').mp hA'
  have hpA := M.cls_perfect hp2 hD4 hq hRA
  have hpA' := M.cls_perfect hp2 hD4 hq hRA'
  have hRR : RA ≠ RA' := fun h => hne (by rw [h])
  have hexA := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hRA
  obtain ⟨hcommR, -⟩ := ih8_twin_data hΦ M.ker_le_center hpA (M.map_mem hRA) (M.map_mem hRA')
    hne hzA hzA' hexA
  obtain ⟨eA⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hRA
  obtain ⟨eA'⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hRA'
  have hodd' := M.natCard_galoisField_odd hp2
  have hinjA := M.injOn_fund hnpsl (M.cls_sub hRA)
  have hinjA' := M.injOn_fund hnpsl (M.cls_sub hRA')
  have hxR : sl2Inv eA ∈ RA := sl2Inv_mem eA
  have hx'R : sl2Inv eA' ∈ RA' := sl2Inv_mem eA'
  have hx2 : sl2Inv eA * sl2Inv eA = 1 := sl2Inv_mul_self hodd' eA
  have hx'2 : sl2Inv eA' * sl2Inv eA' = 1 := sl2Inv_mul_self hodd' eA'
  have hx1 : sl2Inv eA ≠ 1 := sl2Inv_ne_one hodd' eA
  have hx'1 : sl2Inv eA' ≠ 1 := sl2Inv_ne_one hodd' eA'
  have hψx : M.ψ (sl2Inv eA) = z := by
    have hmem : M.ψ (sl2Inv eA) ∈ RA.map M.ψ := Subgroup.mem_map_of_mem _ hxR
    have hsq : M.ψ (sl2Inv eA) * M.ψ (sl2Inv eA) = 1 := by rw [← map_mul, hx2, map_one]
    rcases hzA.unique _ hmem hsq with h | h
    · exact absurd (hinjA _ hxR h) hx1
    · exact h
  have hψx' : M.ψ (sl2Inv eA') = z := by
    have hmem : M.ψ (sl2Inv eA') ∈ RA'.map M.ψ := Subgroup.mem_map_of_mem _ hx'R
    have hsq : M.ψ (sl2Inv eA') * M.ψ (sl2Inv eA') = 1 := by rw [← map_mul, hx'2, map_one]
    rcases hzA'.unique _ hmem hsq with h | h
    · exact absurd (hinjA' _ hx'R h) hx'1
    · exact h
  have hxx' : sl2Inv eA * sl2Inv eA' ∈ Subgroup.center (modelUniv tg k p ee Fact.out).K := by
    apply M.ker_le_center
    rw [MonoidHom.mem_ker, map_mul, hψx, hψx']
    exact hzA.sq
  obtain ⟨a, haR, hψa⟩ := Subgroup.mem_map.mp ha₀
  obtain ⟨b, hbR, hψb⟩ := Subgroup.mem_map.mp hb₀
  have hasq : a * a = sl2Inv eA := by
    have : a * a * (sl2Inv eA)⁻¹ = 1 := by
      apply hinjA _ (RA.mul_mem (RA.mul_mem haR haR) (RA.inv_mem hxR))
      rw [map_mul, map_mul, map_inv, hψa, hψx, ha₀sq, mul_inv_cancel]
    exact mul_inv_eq_one.mp this
  have hbsq : b * b = sl2Inv eA' := by
    have : b * b * (sl2Inv eA')⁻¹ = 1 := by
      apply hinjA' _ (RA'.mul_mem (RA'.mul_mem hbR hbR) (RA'.inv_mem hx'R))
      rw [map_mul, map_mul, map_inv, hψb, hψx', hb₀sq, mul_inv_cancel]
    exact mul_inv_eq_one.mp this
  exact ⟨RA, RA', a, b, _, _, hRA, hRA', hRR, hcommR, hxR, hx2, hx1, hx'R, hx'2, hx'1, hxx', haR,
    hasq, hbR, hbsq, hψa, hψb, hψx, hψx'⟩

theorem e4Tag_of_model (htcf : TwinCentralFact p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΦ : HypOmegaMod p f Φ) {tg : StatedLieTag} {k ee : ℕ} (M : Ih8Model p f Φ tg k ee)
    (hsix : (tg = .PSp ∧ k = 2) ∨ (tg = .PSL ∧ k = 4) ∨ (tg = .PSU ∧ k = 4) ∨
      (tg = .POmegaOdd ∧ k = 3) ∨ (tg = .POmegaPlus ∧ k = 4) ∨ (tg = .POmegaMinus ∧ k = 4))
    {A A' : Subgroup X} {z a₀ b₀ w : X} (hA : A ∈ Φ) (hA' : A' ∈ Φ) (hne : A ≠ A')
    (hzA : IsUniqueInvolution A z) (hzA' : IsUniqueInvolution A' z) (ha₀ : a₀ ∈ A)
    (hb₀ : b₀ ∈ A') (ha₀sq : a₀ * a₀ = z) (hb₀sq : b₀ * b₀ = z)
    (hw : w = a₀ * b₀ ∨ w = a₀⁻¹ * b₀) (hF : ∀ L ∈ Φ, ∃ m ∈ L, w * m ≠ m * w) :
    (tg = .PSp ∧ k = 2) ∨ (tg = .PSL ∧ k = 4 ∧ p ^ f % 4 = 3) ∨
      (tg = .PSU ∧ k = 4 ∧ p ^ f % 4 = 1) := by
  classical
  have hodd : Odd (p ^ f) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hmod : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  have hG2 : tg ≠ .G2 := by
    rintro rfl
    rcases hsix with h | h | h | h | h | h <;> simp at h
  have hD4 : tg ≠ .trialityD4 := by
    rintro rfl
    rcases hsix with h | h | h | h | h | h <;> simp at h
  have hnpsl : ¬ (tg = .PSL ∧ k = 2) := by
    rintro ⟨rfl, rfl⟩
    rcases hsix with h | h | h | h | h | h <;> simp at h
  have hee : ee = f := M.exp_eq_f hD4
  have hq' : 5 ≤ p ^ ee := by rw [hee]; exact hq
  have hne' : Φ.Nonempty := ⟨A, hA⟩
  have key : ((tg = .PSL ∧ k = 4 ∧ p ^ f % 4 = 1) ∨ (tg = .PSU ∧ k = 4 ∧ p ^ f % 4 = 3) ∨
      (tg = .POmegaOdd ∧ k = 3) ∨ (tg = .POmegaPlus ∧ k = 4) ∨ (tg = .POmegaMinus ∧ k = 4)) →
      False := by
    intro hS4
    obtain ⟨RA, RA', a, b, x, x', hRA, hRA', hRR, hcommR, hxR, hx2, hx1, hx'R, hx'2, hx'1, hxx',
      haR, hasq, hbR, hbsq, hψa, hψb, hψx, hψx'⟩ :=
      twin_lifts hp2 hq hΦ M hG2 hD4 hnpsl hA hA' hne hzA hzA' ha₀ hb₀ ha₀sq hb₀sq
    have hfund := fun (a' : (modelUniv tg k p ee Fact.out).K) (ha' : a' ∈ RA)
        (ha'sq : a' * a' = x) =>
      htcf tg k ee M.admissible hp2 hq' (by rw [hee]; exact hS4) RA (M.cls_sub hRA) RA'
        (M.cls_sub hRA') hRR hcommR x hxR hx2 hx1 x' hx'R hx'2 hx'1 hxx' a' ha' ha'sq b hbR hbsq
    have hdone : ∀ a' : (modelUniv tg k p ee Fact.out).K, a' ∈ RA → a' * a' = x →
        M.ψ (a' * b) = w → False := by
      intro a' ha' ha'sq hψ
      obtain ⟨R'', hR'', hcR⟩ := hfund a' ha' ha'sq
      have hR''cls : R'' ∈ M.cls := M.fund_subset_cls hne' hG2 hD4 hR''
      obtain ⟨m, hm, hmne⟩ := hF _ (M.map_mem hR''cls)
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hm
      apply hmne
      rw [← hψ, ← map_mul, ← map_mul, hcR r hr]
    rcases hw with hw | hw
    · exact hdone a haR hasq (by rw [map_mul, hψa, hψb, hw])
    · refine hdone a⁻¹ (RA.inv_mem haR) ?_ (by rw [map_mul, map_inv, hψa, hψb, hw])
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = x := by rw [hasq, hxinv]
  rcases hsix with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
    rcases hmod with h | h
    · exact (key (Or.inl ⟨h1, h2, h⟩)).elim
    · exact h
  · refine Or.inr (Or.inr ⟨h1, h2, ?_⟩)
    rcases hmod with h | h
    · exact h
    · exact (key (Or.inr (Or.inl ⟨h1, h2, h⟩))).elim
  · exact (key (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))).elim
  · exact (key (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))).elim
  · exact (key (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))).elim

end Model

end T7L

end CFSG.ClassicalInvolution.Asc77
