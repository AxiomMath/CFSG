module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB8
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem section3Dihedral (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hSz : Section3SzInput) (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne)
    (hBW : BenderWCInput) (hExc : Sec3TenExceptional) : Section3DihedralInput := by
  intro G _ _ _ hnab T T₁ hS n hn hn3 hD
  by_contra hne
  have hn5 : 3 < n := lt_of_le_of_ne hn3 (Ne.symm hne)
  have hDih : Sec3Dih T T₁ n := hD
  have hcard : Nat.card T = Nat.card (normIn T T₁) * 2 := by
    obtain ⟨hN, ⟨e⟩⟩ := hDih
    exact hS.card_eq_two_mul_dihedral hn e
  by_cases hAn : ∀ g ∈ Subgroup.normalizer (T : Set G), ∀ x ∈ conjSubgroup g (normIn T₁ T),
      ∀ l ∈ normIn T T₁, x * l = l * x
  · have hLn : ∀ g ∈ Subgroup.normalizer (T : Set G),
        conjSubgroup g (normIn T T₁) = normIn T T₁ := by
      intro g hg
      apply conjSubgroup_eq_of_le
      intro y hy
      obtain ⟨l, hl, rfl⟩ := mem_conjSubgroup_iff_exists.1 hy
      have hyT : g * l * g⁻¹ ∈ T := conj_mem_of_mem_normalizer hg (normIn_le T T₁ hl)
      have hyC : g * l * g⁻¹ ∈ Subgroup.centralizer (normIn T₁ T : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        have hginv : g⁻¹ ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer _).inv_mem hg
        have hx : g⁻¹ * e * g⁻¹⁻¹ ∈ conjSubgroup g⁻¹ (normIn T₁ T) :=
          conj_mem_conjSubgroup g⁻¹ he
        have := hAn g⁻¹ hginv _ hx l hl
        calc e * (g * l * g⁻¹) = g * (g⁻¹ * e * g⁻¹⁻¹ * l) * g⁻¹ := by group
          _ = g * (l * (g⁻¹ * e * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
          _ = (g * l * g⁻¹) * e := by group
      rw [← hS.cfg.inf_centralizer_normIn]
      exact ⟨hyT, hyC⟩
    exact false_of_normal hTO hBW h214 hInv hnab hS hcard hLn
  · push Not at hAn
    obtain ⟨g, hg, x, hx, l, hl, hxl⟩ := hAn
    exact hS.false_of_caseB h214 hInv hSz hExc hnab hn hn5 hDih hg ⟨x, hx, l, hl, hxl⟩

end CFSG.CGT.Timmesfeld75
