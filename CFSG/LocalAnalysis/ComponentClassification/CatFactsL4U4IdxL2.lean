module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxA
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Sec8L2Inv

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Idx

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.AutL2Facts

theorem card_of_lieModel_psl2 {Y : Type} [Group Y] {p f : ℕ} (hp2 : p ≠ 2)
    (hY : Blueprint.LieModel Y .PSL 2 p f) : Nat.card Y = Cat8.ordL2 (p ^ f) := by
  obtain ⟨hp, hf, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  rw [Nat.card_congr e.toEquiv,
    GorensteinWalter.psl2_card_formula F (isOddPrimePower_of hp hp2 hf hF), hF]

theorem conj_injective_of_lieModel {Y : Type} [Group Y] {p f : ℕ}
    (hY : Blueprint.LieModel Y .PSL 2 p f) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  obtain ⟨-, -, -, -, F, _, _, -, ⟨e⟩⟩ := lieModel_psl2_data hY
  intro y y' hyy
  apply e.injective
  apply incl_injective F
  rw [← autEquiv_conj e, ← autEquiv_conj e]
  exact congrArg (autEquiv e) hyy

theorem fixCat_psl2_sq {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hY : Blueprint.LieModel Y .PSL 2 p (2 * f)) : FixCat Y (Cat8.ordL2 (p ^ f)) := by
  intro α τ hα2 hα1 hτα _ X hXp hXd hXα hXτ
  obtain ⟨L, -, hLperf, hLcard, -, hLcent⟩ :=
    CatFactsSp4.cfL2Inv Y p f hp hp2 hf h5 (Or.inl hY) α hα2 hα1
  set I := X.map (MulAut.conj : Y →* MulAut Y) with hI
  have hIC : I ≤ centralizer ({α} : Set (MulAut Y)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hXα x hx]
  have hIp : ⁅I, I⁆ = I := by rw [hI, ← map_commutator, hXp]
  have hIL : I ≤ L := hLperf I hIC hIp
  have hIcard : Nat.card I = Nat.card X :=
    Subgroup.card_map_of_injective (conj_injective_of_lieModel hY)
  have hn : Cat8.ordL2 (p ^ f) ≤ Nat.card X := Nat.le_of_dvd Nat.card_pos hXd
  have hIL' : I = L := eq_of_le_of_card_ge hIL (by rw [hIcard]; exact hLcard.trans hn)
  have hLeq : Nat.card L = Cat8.ordL2 (p ^ f) :=
    le_antisymm hLcard (by rw [← hIL', hIcard]; exact hn)
  have hτC : τ ∈ centralizer ({α} : Set (MulAut Y)) := mem_centralizer_singleton_iff.mpr hτα
  refine hLcent hLeq τ hτC fun l hl => ?_
  rw [← hIL'] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hXτ x hx]

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem T_le_case_psl2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (hJ : Blueprint.LieModel (OddBar h.J) .PSL 2 p f)
    (hKa : conjugate h.K h.a = h.K) (hK : Blueprint.LieModel (OddBar h.K) .PSL 2 p (2 * f)) :
    h.T ≤ zpowers h.a ⊔ h.B := by
  apply T_le_of_fixCat h hKa
  rw [card_of_lieModel_psl2 hp2 hJ]
  exact fixCat_psl2_sq hp hp2 hf h5 hK

end Idx

end CFSG.ComponentClassification.CatFactsL4U4
