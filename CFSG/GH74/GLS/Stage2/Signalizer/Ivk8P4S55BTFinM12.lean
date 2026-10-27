module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinOut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinCkB
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
public import Certificates.Certificate55101

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Mathieu FinGen FinGlue
  Certificates.BTFinCk Certificates.BTFinCk.M12

namespace FinM12

theorem factorization_95040 : (95040 : ℕ).factorization 3 = 3 := by
  rw [show (95040 : ℕ) = 3 ^ 3 * 3520 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem rows_ord : ∀ r ∈ rows, r.2.2.2.1 = 36 ∨ r.2.2.2.1 = 54 ∨ r.2.2.2.1 = 10 ∨
    r.2.2.2.1 = 11 := by
  intro r hr
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h <;> subst h <;> simp


theorem card_centralizerIn {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {u : Equiv.Perm (Fin 12)}
    (hu : u ∈ NativeSporadic.M12) (ho : orderOf u = p) :
    ∃ r ∈ rows, Nat.card (centralizerIn NativeSporadic.M12 u) = r.2.2.2.1 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hck := Certificates.certificate55101
  simp only [m12OddCk, Bool.and_eq_true, List.all_eq_true] at hck
  obtain ⟨hrows, hcov3⟩ := hck
  rw [← m12Certificate_originalSubgroup] at hu ⊢
  have hcard : Nat.card m12Certificate.originalSubgroup = 95040 := by
    rw [m12Certificate_originalSubgroup, m12_card]
  have hpd : p ∣ 95040 := by
    rw [← hcard, ← ho]
    exact Subgroup.orderOf_dvd_natCard _ hu
  have hp3 : p = 3 ∨ p = 5 ∨ p = 11 := by
    have h1 : p ∣ 2 ^ 6 * (3 ^ 3 * (5 * 11)) := by simpa using hpd
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)) hp2
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
  have hok : repsOK 12 gT gIT (cosetOrderTables m12Certificate 1 p) ((repsOf p).map toTable)
      20000 = true := by
    rcases hp3 with rfl | rfl | rfl <;> exact hcov3 _ (by simp)
  have hrow : ∀ r ∈ rows, ordTest 12 r.1 (toTable (evalCodes [m12gA, m12gB] r.2.1)) = true ∧
      ((r.2.2.2.2.map (evalCodes [m12gA, m12gB])).all fun h =>
        commT 12 (toTable h) (toTable (evalCodes [m12gA, m12gB] r.2.1))) = true ∧
      (conjClosure 12 gT gIT (toTable (evalCodes [m12gA, m12gB] r.2.1)) 20000).1.size =
        r.2.2.1 ∧ r.2.2.1 * r.2.2.2.1 = 95040 ∧
      centFourOK 12 ((r.2.2.2.2.map (evalCodes [m12gA, m12gB])).map toTable)
        (toTable (evalCodes [m12gA, m12gB] r.2.1)) r.2.2.2.1 1000 0 = true := by
    intro r hr
    have h := hrows r hr
    simp only [rowOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨h1, h2, h3, h4, h5⟩
  have hreps : ∀ r ∈ repsOf p, 1⁻¹ * r ∈ m12Certificate.originalSubgroup ∧ orderOf r = p := by
    intro r hr
    simp only [repsOf, List.mem_map, List.mem_filter, beq_iff_eq] at hr
    obtain ⟨r0, ⟨hr0, hp0⟩, rfl⟩ := hr
    refine ⟨by simpa using evalCodes_mem _ m12_gens_mem r0.2.1, ?_⟩
    rw [← hp0]
    exact (ordTest_iff perm_faithful (rep_toTable hn _) (by rw [hp0]; exact hp.pos)).1
      (hrow r0 hr0).1
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn m12Certificate hQ (pairTables_spec hn hA hB)
    1 (fun h hh => by simpa using hh) (m := p) hp.pos (repsOf p) hreps 20000 hok
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u (by simpa using hu) ho
  have hsz' := hsize r hr
  simp only [repsOf, List.mem_map, List.mem_filter, beq_iff_eq] at hr
  obtain ⟨r0, ⟨hr0, -⟩, rfl⟩ := hr
  obtain ⟨-, hcomm, hsz, hprod, hfour⟩ := hrow r0 hr0
  set cg := r0.2.2.2.2.map (evalCodes [m12gA, m12gB]) with hcg
  have hKle : closure {x | x ∈ cg} ≤ centralizerIn m12Certificate.originalSubgroup
      (evalCodes [m12gA, m12gB] r0.2.1) :=
    closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
      exact evalCodes_mem _ m12_gens_mem w) hcomm
  have hgK : ∀ l < (cg.map toTable).length,
      Rep 12 (cg.map toTable)[l]! (cg[l]!) ∧ cg[l]! ∈ closure {x | x ∈ cg} := by
    intro l hl
    have hl' : l < cg.length := by simpa using hl
    refine ⟨?_, ?_⟩
    · rw [getElem!_pos (cg.map toTable) l hl, List.getElem_map, getElem!_pos cg l hl']
      exact rep_toTable hn _
    · rw [getElem!_pos cg l hl']
      exact subset_closure (List.getElem_mem hl')
  have hcls : r0.2.2.1 ≤ (conjClass m12Certificate.originalSubgroup
      (evalCodes [m12gA, m12gB] r0.2.1)).ncard := by
    rw [← hsz]
    exact hsz'
  obtain ⟨hC, hKcard⟩ := FinCk.centralizerIn_eq_of_ge _ _ hKle hcls (by rw [hprod, hcard])
    (FinCk.le_card_of_centFourOK hn hgK hfour)
  refine ⟨r0, hr0, ?_⟩
  rw [centralizerIn_conj _ hc, card_map_of_injective (MulEquiv.injective _), hC, hKcard]

theorem isSolvable_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (x : ↥NativeSporadic.M12) (hx : orderOf x = p) :
    Group.IsSolvable ↥(centralizer ({x} : Set ↥NativeSporadic.M12)) := by
  have hx' : orderOf (x : Equiv.Perm (Fin 12)) = p := by rw [Subgroup.orderOf_coe, hx]
  obtain ⟨r, hr, hcard⟩ := card_centralizerIn hp hp2 x.2 hx'
  rw [← FinM22.card_centralizer_subtype] at hcard
  rcases rows_ord r hr with h | h | h | h <;> rw [h] at hcard
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 2) (b := 2) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hcard]; norm_num)
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 1) (b := 3) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hcard]; norm_num)
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 1) (b := 1) Nat.prime_two
      (by norm_num : Nat.Prime 5) (by norm_num) (by rw [hcard]; norm_num)
  · exact isSolvable_of_card_eq_pow_mul_pow (a := 0) (b := 1) Nat.prime_two
      (by norm_num : Nat.Prime 11) (by norm_num) (by rw [hcard]; norm_num)

theorem card_le_nine {E : Subgroup ↥NativeSporadic.M12}
    (hE : IsElementaryAbelian 3 ↥E) : Nat.card ↥E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (IsElementaryAbelian.isPGroup 3 ↥E)
  have hcardM : Nat.card ↥NativeSporadic.M12 = 95040 := m12_card
  have hdvd : 3 ^ k ∣ 95040 := hcardM ▸ hk ▸ Subgroup.card_subgroup_dvd_card E
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 3 ^ 4 ∣ 95040 := (Nat.pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at this
  rcases (by omega : k ≤ 2 ∨ k = 3) with hk2 | rfl
  · rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  exfalso
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard27, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
  have h27 : 3 ^ (Nat.card ↥NativeSporadic.M12).factorization 3 = 27 := by
    rw [hcardM, factorization_95040]
    norm_num
  let S1 : Sylow 3 ↥NativeSporadic.M12 := Sylow.ofCard E (by rw [hk, h27]; norm_num)
  let S2 : Sylow 3 ↥NativeSporadic.M12 :=
    Sylow.ofCard (closure ({x, y} : Set ↥NativeSporadic.M12)) (by rw [hcard27, h27]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥NativeSporadic.M12 S1 S2
  have hmem : ∀ z ∈ ({x, y} : Set ↥NativeSporadic.M12), ∃ e ∈ E, z = g * e * g⁻¹ := by
    intro z hz
    have hzS : z ∈ ((g • S1 : Sylow 3 _) : Subgroup ↥NativeSporadic.M12) := by
      rw [hg, Sylow.coe_ofCard]
      exact subset_closure hz
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hzS
    obtain ⟨e, he, rfl⟩ := hzS
    exact ⟨e, by simpa [S1, Sylow.coe_ofCard] using he, by
      rw [MulAut.smul_def, MulAut.conj_apply]⟩
  obtain ⟨e1, he1, rfl⟩ := hmem x (by simp)
  obtain ⟨e2, he2, hy⟩ := hmem y (by simp)
  have hc : e1 * e2 = e2 * e1 :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥E)).comm ⟨e1, he1⟩ ⟨e2, he2⟩)
  apply hxy
  rw [hy, commutatorElement_eq_one_iff_mul_comm]
  set c := g
  calc c * e1 * c⁻¹ * (c * e2 * c⁻¹) = c * (e1 * e2) * c⁻¹ := by group
    _ = c * (e2 * e1) * c⁻¹ := by rw [hc]
    _ = c * e2 * c⁻¹ * (c * e1 * c⁻¹) := by group

theorem rank_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ∀ k : ℕ, p ^ k ∣ Nat.card ↥NativeSporadic.M12 → k ≤ 1 ∨ (p = 3 ∧ k ≤ 2) := by
  intro k hk
  left
  by_contra h
  rw [m12_card] at hk
  have hp2' : p ^ 2 ∣ 95040 := (Nat.pow_dvd_pow p (by omega)).trans hk
  have hpd : p ∣ 2 ^ 6 * (3 ^ 3 * (5 * 11)) := by
    have := (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hp2'
    simpa using this
  rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h] at hp2'
    norm_num at hp2'
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h] at hp2'
    norm_num at hp2'

theorem noPerfLocal_m12 : NoPerfLocal ↥NativeSporadic.M12 := by
  refine noPerfLocal_of (fun p hp hp2 E hE => ?_)
    (fun p hp hp2 x hx => isSolvable_centralizer hp hp2 x hx)
  by_cases h3 : p = 3
  · subst h3
    exact Or.inr ⟨rfl, card_le_nine hE⟩
  · exact rank_of_dvd hp (rank_dvd hp hp2 h3) E hE

end FinM12

theorem finCellB_m12
    {Y : Type} [Group Y]
    (hY : NativeSporadic.IsSporadic Y .M12) : FinCellB Y := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥NativeSporadic.M12 := e
  have hA : FinCellA Y := finCellA_of (NoPerfLocal.of_equiv (MulAut.congr e')
    (FinOut.noPerfLocal_mulAut m12_center_eq_bot' m12_mulAut_card FinM12.noPerfLocal_m12))
  exact hA.finCellB

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
