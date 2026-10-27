module

public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.RankThree.Literature.ThompsonDihedralCore
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Join

variable {G : Type} [Group G]

private theorem card_iSup_eq_prod_card {ι : Type*} [Fintype ι] (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H) :
    Nat.card (⨆ i, H i : Subgroup G) = ∏ i, Nat.card (H i) := by
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm), ← Nat.card_pi]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private theorem mul_comm_of_mem_iSup {ι : Type*} (H : ι → Subgroup G)
    (hcomm : ∀ i j, ∀ x ∈ H i, ∀ y ∈ H j, x * y = y * x) {x y : G} (hx : x ∈ ⨆ i, H i)
    (hy : y ∈ ⨆ i, H i) : x * y = y * x := by
  have h1 : ∀ j, ∀ y ∈ ⨆ i, H i, ∀ h ∈ H j, h * y = y * h := by
    intro j y hy
    refine Subgroup.iSup_induction H hy (C := fun y => ∀ h ∈ H j, h * y = y * h) ?_ ?_ ?_
    · intro i y hyi h hh
      exact hcomm j i h hh y hyi
    · intro h _
      simp
    · intro y z hy hz h hh
      rw [← mul_assoc, hy h hh, mul_assoc, hz h hh, mul_assoc]
  refine Subgroup.iSup_induction H hx (C := fun x => x * y = y * x) ?_ ?_ ?_
  · intro j x hxj
    exact h1 j y hy x hxj
  · simp
  · intro a b ha hb
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

private theorem pow_eq_one_of_mem_iSup {ι : Type*} (H : ι → Subgroup G)
    (hcomm : ∀ i j, ∀ x ∈ H i, ∀ y ∈ H j, x * y = y * x) {n : ℕ}
    (hpow : ∀ i, ∀ x ∈ H i, x ^ n = 1) {x : G} (hx : x ∈ ⨆ i, H i) : x ^ n = 1 := by
  refine Subgroup.iSup_induction' H (C := fun x _ => x ^ n = 1) ?_ ?_ ?_ hx
  · intro i x hxi
    exact hpow i x hxi
  · exact one_pow n
  · intro x y hx hy hxn hyn
    have hc : Commute x y := mul_comm_of_mem_iSup H hcomm hx hy
    rw [hc.mul_pow, hxn, hyn, one_mul]

end Join

section Extraction

variable {G : Type} [Group G] [Finite G]

open CFSG.RankThree.Literature.Thompson534 in
private theorem exists_of_dihedralBasis {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P U : Subgroup G}
    (hP : IsPGroup p P) {k : ℕ} {A : Fin (k + 1) → Subgroup G} {t : Fin (k + 1) → G}
    (hB : DihedralBasis P U A t) :
    ∃ u ∈ U, u ≠ 1 ∧ ∃ Q₁ : Subgroup G, Q₁ ≤ P ∧ IsElemAbelian p Q₁ ∧ Nat.card Q₁ = p ^ k ∧
      Q₁ ≤ Subgroup.centralizer ({u} : Set G) ∧ (⁅Q₁, U⁆ : Subgroup G) = Q₁ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
    rw [hm]
    exact hpodd.pow
  have hAp : ∀ i, Nat.card (A i) = p := by
    intro i
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hP.to_le (hB.le i))
    have hq := hB.prime i
    rw [hm] at hq ⊢
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hq
      exact Nat.not_prime_one hq
    exact ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp (dvd_pow_self p hm0)).symm
  have hApow : ∀ i, ∀ a ∈ A i, a ^ p = 1 := by
    intro i a ha
    have h := pow_card_eq_one' (G := A i) (x := ⟨a, ha⟩)
    rw [hAp i] at h
    exact congrArg Subtype.val h
  have hAcomm : ∀ i, ∀ a ∈ A i, ∀ b ∈ A i, a * b = b * a := by
    intro i a ha b hb
    haveI : IsCyclic (A i) := isCyclic_of_prime_card (hAp i)
    exact congrArg Subtype.val
      ((inferInstance : IsMulCommutative (A i)).is_comm.comm (⟨a, ha⟩ : A i) ⟨b, hb⟩)
  have hAne : ∀ i, ∃ a ∈ A i, a ≠ 1 := by
    intro i
    have hne : A i ≠ ⊥ := fun h => by
      have := hAp i
      rw [h, Subgroup.card_bot] at this
      exact hp.ne_one this.symm
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨a, ha, fun h => ha1 (Subtype.ext h)⟩
  have hcentl : ∀ i j, i ≠ j → A j ≤ Subgroup.centralizer ({t i} : Set G) := by
    intro i j hij a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hB.mem_centralizer i j hij)) a ha
  set B : Fin k → Subgroup G := fun i => A i.castSucc with hBdef
  have hBcomm : ∀ i j, ∀ x ∈ B i, ∀ y ∈ B j, x * y = y * x := by
    intro i j x hx y hy
    by_cases hij : i = j
    · subst hij
      exact hAcomm _ x hx y hy
    · exact hB.comm (fun h => hij (Fin.castSucc_injective _ h)) x hx y hy
  have hBcomm' : Pairwise fun i j : Fin k => ∀ x y : G, x ∈ B i → y ∈ B j → Commute x y := by
    intro i j hij x y hx hy
    exact hB.comm (fun h => hij (Fin.castSucc_injective _ h)) x hx y hy
  have hind : iSupIndep B := by
    intro j
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxj, hxrest⟩ := Subgroup.mem_inf.mp hx
    have hle : (⨆ (i : Fin k) (_ : i ≠ j), B i) ≤
        Subgroup.centralizer ({t j.castSucc} : Set G) := by
      refine iSup₂_le fun i hij => ?_
      exact hcentl _ _ (fun h => hij (Fin.castSucc_injective _ h).symm)
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hle hxrest)
    have h2 := hB.inv j.castSucc x hxj
    have h3 : x = x⁻¹ := by
      rw [← h2, ← h1]
      group
    exact (Subgroup.mem_bot).mpr (eq_one_of_eq_inv hPodd (hB.le _ hxj) h3)
  set Q : Subgroup G := ⨆ i, B i with hQdef
  have hBQ : ∀ i, B i ≤ Q := fun i => le_iSup B i
  have hlast : ∀ i : Fin k, Fin.last k ≠ i.castSucc := fun i h =>
    (Fin.castSucc_lt_last i).ne h.symm
  refine ⟨t (Fin.last k), hB.mem _, ?_, Q, iSup_le fun i => hB.le _, ?_, ?_, ?_, ?_⟩
  ·
    intro h1
    obtain ⟨a, ha, ha1⟩ := hAne (Fin.last k)
    have h2 := hB.inv (Fin.last k) a ha
    rw [h1, one_mul, inv_one, mul_one] at h2
    exact ha1 (eq_one_of_eq_inv hPodd (hB.le _ ha) h2)
  ·
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · exact mul_comm_of_mem_iSup B hBcomm a.2 b.2
    · exact pow_eq_one_of_mem_iSup B hBcomm (fun i => hApow _) hx
  ·
    rw [hQdef, card_iSup_eq_prod_card B hBcomm' hind]
    simp [hBdef, hAp]
  ·
    exact iSup_le fun i => hcentl _ _ (hlast i)
  ·
    apply le_antisymm
    ·
      have hnorm : ∀ u ∈ U, ∀ q ∈ Q, u * q * u⁻¹ ∈ Q := by
        intro u hu q hq
        refine Subgroup.iSup_induction B hq (C := fun q => u * q * u⁻¹ ∈ Q) ?_ ?_ ?_
        · intro i a ha
          exact hBQ i (((Subgroup.mem_normalizer_iff.mp (hB.le_normalizer i.castSucc hu)) a).mp ha)
        · simp
        · intro a b ha hb
          have : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
          rw [this]
          exact Q.mul_mem ha hb
      refine Subgroup.commutator_le.mpr fun q hq u hu => ?_
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine Q.mul_mem hq ?_
      have := hnorm u hu q⁻¹ (Q.inv_mem hq)
      simpa [mul_assoc] using this
    · refine iSup_le fun i a ha => ?_
      have hsU : t i.castSucc ∈ U := hB.mem _
      have hc : ⁅a, t i.castSucc⁆ ∈ (⁅Q, U⁆ : Subgroup G) :=
        Subgroup.commutator_mem_commutator (hBQ i ha) hsU
      have h2 : ⁅a, t i.castSucc⁆ = a * a := by
        have h3 := hB.inv i.castSucc a ha
        rw [commutatorElement_def]
        calc a * t i.castSucc * a⁻¹ * (t i.castSucc)⁻¹
            = a * (t i.castSucc * a * (t i.castSucc)⁻¹)⁻¹ := by group
          _ = a * a := by rw [h3, inv_inv]
      rw [h2] at hc
      obtain ⟨c, hc'⟩ := hpodd
      have h4 : (a * a) ^ (c + 1) = a := by
        have h5 : (a * a) ^ (c + 1) = a ^ p * a := by
          rw [← sq, ← pow_mul, hc']
          group
        rw [h5, hApow i.castSucc a ha, one_mul]
      rw [← h4]
      exact Subgroup.pow_mem _ hc _

end Extraction

theorem dihedralUsed : DihedralUsed := by
  intro G _ _ p hp hp2 P U k hP hU hcard hUN hfaith
  haveI : Fact p.Prime := ⟨hp⟩
  have hnil : ∀ H : Subgroup G, H ≤ P → Group.IsNilpotent H := fun H hH =>
    (hP.to_le hH).isNilpotent
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
    rw [hm]
    exact (hp.odd_of_ne_two hp2).pow
  have hUcomm : ∀ s ∈ U, ∀ u ∈ U, s * u = u * s := fun s hs u hu => isElemAbelian_commute hU hs hu
  have hU2 : ∀ u ∈ U, u * u = 1 := fun u hu => by
    rw [← sq]
    exact hU.2 u hu
  have hfaith' : U ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨huU, huC⟩
    rw [Subgroup.mem_bot]
    refine hfaith u huU fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp huC x hx
  obtain ⟨A, t, hB⟩ := CFSG.RankThree.Literature.Thompson534.exists_dihedral_basis (k + 1) hnil
    hPodd hUcomm hU2 hcard hUN hfaith'
  exact exists_of_dihedralBasis hp hp2 hP hB

end CFSG.LocalAnalysis.GLTheoremA.P55
