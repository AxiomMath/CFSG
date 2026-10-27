
module

public import CFSG.LargeExtraspecial.AS35QCoSp6Spec
public import CFSG.Sporadic.Co2Smith.Timmesfeld

@[expose] public section

namespace CFSG.LargeExtraspecial.AS35QCo

open Native CFSG.Assembly.LowTwoRank CFSG.Sporadic.Co2Smith
open scoped Matrix

theorem length_le_ncard {T : Set Sp62} {l : List ℕ} (hl : l.Nodup) (hlt : ∀ c ∈ l, c < 2 ^ 36)
    (hrep : ∀ c ∈ l, ∃ g ∈ T, Rep c g) : l.length ≤ T.ncard := by
  classical
  choose! φ hφT hφ using hrep
  have hinj : Set.InjOn φ l.toFinset := by
    intro c hc d hd hcd
    simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hc hd
    exact Rep.code_eq (hφ c hc) (hcd ▸ hφ d hd) (hlt c hc) (hlt d hd)
  have hcard := Finset.card_image_of_injOn hinj
  rw [List.toFinset_card_of_nodup hl] at hcard
  rw [← hcard, ← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ (Set.toFinite T)
  intro g hg
  simp only [Finset.coe_image, List.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq] at hg
  obtain ⟨c, hc, rfl⟩ := hg
  exact hφT c hc

theorem card_centralizer_mul_ncard (g : Sp62) :
    Nat.card (Subgroup.centralizer ({g} : Set Sp62)) * {h : Sp62 | ∃ m, h = m * g * m⁻¹}.ncard =
      1451520 := by
  rw [← natCard_sp62]
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct Sp62) g)
  rw [MulAction.index_stabilizer, Nat.card_congr (ConjAct.toConjAct (G := Sp62)).toEquiv.symm]
    at h1
  rw [← h1]
  congr 1
  · refine Nat.card_congr (Equiv.subtypeEquiv (ConjAct.toConjAct (G := Sp62)).toEquiv ?_)
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, MulAction.mem_stabilizer_iff]
    change x * g = g * x ↔ ConjAct.toConjAct x • g = g
    rw [ConjAct.toConjAct_smul]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc x * g = x * g * x⁻¹ * x := by group
        _ = g * x := by rw [h]
  · congr 1
    ext h
    rw [ConjAct.mem_orbit_conjAct, isConj_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c⁻¹, by rw [hc]; group⟩
    · rintro ⟨c, hc⟩
      exact ⟨c⁻¹, by rw [← hc]; group⟩

theorem exists_bigOrder_rep_of_prodOK {k : ℕ} (hc : prodOK k = true) {ρ : Sp62}
    (hρ : Rep (repc k) ρ) :
    ∃ w : Sp62, ∀ j, 1 ≤ j → j ≤ 4 → (ρ * (w * ρ * w⁻¹)) ^ j ≠ 1 := by
  simp only [prodOK, bigOrder, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne] at hc
  obtain ⟨⟨⟨hsp, h1⟩, h2⟩, ⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩ := hc
  obtain ⟨w, hw, hwi⟩ := exists_rep h1 h2 hsp
  refine ⟨w, fun j hj1 hj4 hX' => ?_⟩
  set x := mulc (repc k) (mulc (mulc witc.1 (repc k)) witc.2)
  have hX : Rep x (ρ * (w * ρ * w⁻¹)) := hρ.mul ((hw.mul hρ).mul hwi)
  set X := ρ * (w * ρ * w⁻¹)
  have e : ∀ {c : ℕ} {g : Sp62}, Rep c g → c < 2 ^ 36 → g = 1 → c = idc :=
    fun hc hlt hg => Rep.code_eq hc (hg ▸ Rep.one) hlt (by decide)
  interval_cases j
  · exact hx1 (e hX (mulc_lt _ _) (by simpa using hX'))
  · exact hx2 (e (hX.mul hX) (mulc_lt _ _) (by rw [← sq]; exact hX'))
  · exact hx3 (e ((hX.mul hX).mul hX) (mulc_lt _ _) (by rw [← pow_two, ← pow_succ]; exact hX'))
  · exact hx4 (e ((hX.mul hX).mul (hX.mul hX)) (mulc_lt _ _)
      (by rw [← hX']; simp only [pow_succ, pow_zero, one_mul, mul_assoc]))

theorem conj_mem_centralizer_iff {ρ m h : Sp62} :
    h ∈ Subgroup.centralizer ({m * ρ * m⁻¹} : Set Sp62) ↔
      m⁻¹ * h * m ∈ Subgroup.centralizer ({ρ} : Set Sp62) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro e
    calc m⁻¹ * h * m * ρ = m⁻¹ * (h * (m * ρ * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * ρ * m⁻¹) * h) * m := by rw [e]
      _ = ρ * (m⁻¹ * h * m) := by group
  · intro e
    calc h * (m * ρ * m⁻¹) = m * (m⁻¹ * h * m * ρ) * m⁻¹ := by group
      _ = m * (ρ * (m⁻¹ * h * m)) * m⁻¹ := by rw [e]
      _ = m * ρ * m⁻¹ * h := by group

end CFSG.LargeExtraspecial.AS35QCo
