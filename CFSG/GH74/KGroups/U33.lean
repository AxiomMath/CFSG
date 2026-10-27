module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.ClassCount
public import CFSG.Blueprint.Catalog
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Quasithin.Recognition.CertU33Perm
import CFSG.Timmesfeld.Final.PSU33
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.Quasithin.Recognition.CertU33Perm
public import CFSG.GH74.KGroups.U33Inputs
public meta import CFSG.GH74.KGroups.U33Inputs
public import Certificates.Certificate5133
public import Certificates.Certificate8080
public import Certificates.Certificate8081

public section

namespace CFSG.GH74.KGroups.U33

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint

theorem QP_valid :
    QP.check = true ∧ QP.orderCertificate = 6048 :=
  Certificates.certificate5133.1

theorem QA_valid :
    QA.check = true ∧ QA.orderCertificate = 12096 :=
  Certificates.certificate5133.2.1

theorem QP_ok : ValidSchreier QP := QP_valid.1

theorem QA_ok : ValidSchreier QA := QA_valid.1

theorem QP_closure : QP.originalSubgroup = Subgroup.closure {pa, pb} := by
  rw [QP, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem QA_closure : QA.originalSubgroup = Subgroup.closure {pa, pb, sg0} := by
  rw [QA, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem P_le_A : Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))) ≤
    Subgroup.closure {pa, pb, sg0} :=
  Subgroup.closure_mono fun x hx => by
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

theorem pa_mem : pa ∈ Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))) :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem pb_mem : pb ∈ Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem P_eq_uv :
    Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))) = Subgroup.closure {pu, pv} := by
  obtain ⟨-, -, -, ⟨hu, hv, ha, hb⟩, -⟩ := Certificates.certificate5133
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hu
    · exact hv

theorem conj_AP :
    ∀ σ ∈ Subgroup.closure ({pa, pb, sg0} : Set (Equiv.Perm (Fin 28))),
      ∀ x ∈ Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))),
        σ * x * σ⁻¹ ∈ Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))) := by
  obtain ⟨-, -, -, ⟨hu, hv, -, -⟩, ⟨hsu, hsv⟩, -⟩ := Certificates.certificate5133
  refine conj_mem_of_closure _ P_eq_uv _ fun σ hσ => ?_
  rcases hσ with rfl | rfl | rfl
  · exact ⟨conj_mem_self _ _ pa_mem _ hu, conj_mem_self _ _ pa_mem _ hv⟩
  · exact ⟨conj_mem_self _ _ pb_mem _ hu, conj_mem_self _ _ pb_mem _ hv⟩
  · exact ⟨hsu, hsv⟩

theorem ws_pos : ∀ wk ∈ wsU, 0 < wk.2 := by
  intro wk hwk
  simp only [wsU, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rw [hwk]
  norm_num

theorem invol_P :
    ∀ x ∈ Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))), orderOf x = 2 →
      x ∈ conjSet (Subgroup.closure {pa, pb, sg0}) pu := by
  obtain ⟨-, hA, ⟨hu2, -⟩, ⟨hu, -⟩, -, -, h63, -, -, -, -, -, h192, -⟩ :=
    Certificates.certificate5133
  have hcA : Nat.card (Subgroup.closure ({pa, pb, sg0} : Set (Equiv.Perm (Fin 28)))) = 12096 := by
    rw [← QA_closure, card_group QA hA.1, hA.2]
  intro x hx hx2
  obtain ⟨r, hr, hxr⟩ := conj_of_order_count _ _ conj_AP 2 [pu] (by simpa using ⟨hu, hu2⟩)
    (by simp) (by simp [hcA, h63, h192]) x hx hx2
  rw [List.mem_singleton] at hr
  rwa [hr] at hxr

theorem invol_A :
    ∀ x ∈ Subgroup.closure ({pa, pb, sg0} : Set (Equiv.Perm (Fin 28))), orderOf x = 2 →
      ∃ r ∈ [pu, pt2], x ∈ conjSet (Subgroup.closure {pa, pb, sg0}) r := by
  obtain ⟨-, hA, ⟨hu2, -⟩, ⟨hu, -⟩, -, -, -, -, -, -, ⟨ht, ht2⟩, h315, h192, h48, -⟩ :=
    Certificates.certificate5133
  have hcA : Nat.card (Subgroup.closure ({pa, pb, sg0} : Set (Equiv.Perm (Fin 28)))) = 12096 := by
    rw [← QA_closure, card_group QA hA.1, hA.2]
  exact conj_of_order_count _ _ (conj_mem_self _) 2 [pu, pt2]
    (by simpa using ⟨⟨P_le_A hu, hu2⟩, ht, ht2⟩) (by simp [h192, h48])
    (by simp [hcA, h315, h192, h48])

theorem three_A :
    ∀ x ∈ Subgroup.closure ({pa, pb, sg0} : Set (Equiv.Perm (Fin 28))), orderOf x = 3 →
      ∃ r ∈ [px1, px2], x ∈ conjSet (Subgroup.closure {pa, pb, sg0}) r := by
  obtain ⟨-, hA, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨h1, h13⟩, ⟨h2, h23⟩, h728, h216,
    h18, -⟩ := Certificates.certificate5133
  have hcA : Nat.card (Subgroup.closure ({pa, pb, sg0} : Set (Equiv.Perm (Fin 28)))) = 12096 := by
    rw [← QA_closure, card_group QA hA.1, hA.2]
  exact conj_of_order_count _ _ (conj_mem_self _) 3 [px1, px2]
    (by simpa using ⟨⟨h1, h13⟩, h2, h23⟩) (by simp [h216, h18])
    (by simp [hcA, h728, h216, h18])

theorem count_le :
    Nat.card {p : Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))) ×
      Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))) //
        orderOf p.1 = 2 ∧ orderOf p.2 = 7 ∧ PairInv wsU p.1 p.2} ≤
      Nat.card (Subgroup.closure ({pa, pb, sg0} : Set (Equiv.Perm (Fin 28)))) := by
  obtain ⟨-, hA, -, -, -, -, h63, hfib, -⟩ := Certificates.certificate5133
  refine (card_pairs_le _ _ pu conj_AP 2 7 wsU invol_P).trans ?_
  have e : Nat.card {x // x ∈ Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))) ∧
      orderOf x = 2} * Nat.card {y // y ∈ Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))) ∧
      orderOf y = 7 ∧ PairInv wsU pu y} =
      Nat.card (Subgroup.closure ({pa, pb, sg0} : Set (Equiv.Perm (Fin 28)))) := by
    rw [h63, hfib, ← QA_closure, card_group QA hA.1, hA.2]
  exact e.le

theorem pa_eq : pa = CFSG.Quasithin.u33Img 3 := by decide

theorem pb_eq : pb = CFSG.Quasithin.u33Img 4 := by decide

theorem J_eq :
    Subgroup.closure (Set.range CFSG.Quasithin.u33Img) = QP.originalSubgroup := by
  obtain ⟨-, -, -, -, -, himg, -⟩ := Certificates.certificate5133
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, QP_closure]
    exact himg k
  · rw [QP_closure, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.subset_closure ⟨3, pa_eq.symm⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.subset_closure ⟨4, pb_eq.symm⟩

theorem equiv_of_lieModel
    {K : Type} [Group K] (h : LieModel K .PSU 3 3 1) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel h
  obtain ⟨e2⟩ := CFSG.Quasithin.u33Pres_mulEquiv_PSU3
  obtain ⟨e3⟩ := CFSG.Quasithin.u33Pres_mulEquiv_perm
  have hsz : CFSG.Quasithin.u33Gens.size = 5 := CFSG.Quasithin.u33Chain_check.1
  have hset : {g | ∃ k < CFSG.Quasithin.u33Gens.size,
      CFSG.Monster.B.Co2.permOfArr 28 CFSG.Quasithin.u33Gens[k]! = g} =
      Set.range CFSG.Quasithin.u33Img := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [hsz] at hk
      exact ⟨⟨k, hk⟩, (CFSG.Quasithin.permOfArr_u33Gens ⟨k, hk⟩).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [hsz]; exact k.2, CFSG.Quasithin.permOfArr_u33Gens k⟩
  rw [hset, J_eq] at e3
  exact ⟨e1.trans (e2.symm.trans e3)⟩

theorem autModel
    {K : Type} [Group K] (e : K ≃* QP.originalSubgroup) :
    ∃ M : AutModel K (Equiv.Perm (Fin 28)), M.P = QP.originalSubgroup ∧
      M.A = QA.originalSubgroup := by
  obtain ⟨-, -, ⟨hu2, hv7, hI⟩, -, -, -, -, -, -, -, -, -, -, -, hcent, -⟩ :=
    Certificates.certificate5133
  rw [QP_closure] at e ⊢
  rw [QA_closure]
  exact autModel_of_card _ _ pu pv P_eq_uv 2 7 wsU hu2 hv7 hI conj_AP hcent count_le e

theorem primeFactors_96 : (96 : ℕ).primeFactors = {2, 3} := by
  rw [show (96 : ℕ) = 2 ^ 5 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  rfl

theorem primeFactors_24 : (24 : ℕ).primeFactors = {2, 3} := by
  rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
  rfl

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

theorem finite_K : Finite K := Finite.of_equiv QP.originalSubgroup e.symm.toEquiv

theorem finite_mulAut : Finite (MulAut K) := by
  obtain ⟨M, -, -⟩ := autModel e
  exact Finite.of_equiv M.A M.Φ.symm.toEquiv

theorem card_mulAut : Nat.card (MulAut K) = 12096 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  rw [M.card_mulAut, hA, card_group QA QA_ok, QA_valid.2]

theorem autCentralizer
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) (hcard : Nat.card R = 9)
    (ψ : MulAut K) (hψ : ψ ^ 2 = 1) (hc : ∀ r ∈ R, ψ * r = r * ψ) : ψ = 1 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  have he : ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → τ ≠ 1 → ∀ X ∈ QA.originalSubgroup, X ≠ 1 →
      ∀ Y ∈ QA.originalSubgroup, X ^ 3 = 1 → Y ^ 3 = 1 → X * Y = Y * X → X * τ = τ * X →
      Y * τ = τ * Y → Y = 1 ∨ Y = X ∨ Y = X ^ 2 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h9u, h9t, -⟩ :=
      Certificates.certificate5133
    rw [QA_closure]
    intro τ hτ hτ2 hτ1
    exact forall_of_classes _ {x | x ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf x = 2}
      [pu, pt2] (E9At (Subgroup.closure {pa, pb, sg0})) (fun x hx => invol_A x hx.1 hx.2)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h9u
        · exact h9t)
      (fun g hg r hr => e9At_conj hg hr) τ ⟨hτ, orderOf_eq_prime hτ2 hτ1⟩
  rw [← hA] at he
  exact M.autCentralizer he R hR hcard ψ hψ hc

theorem autRank3_le_two
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) : Nat.card R ≤ 9 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  have he : ∀ X ∈ QA.originalSubgroup, ∀ Y ∈ QA.originalSubgroup, ∀ Z ∈ QA.originalSubgroup,
      X ^ 3 = 1 → Y ^ 3 = 1 → Z ^ 3 = 1 → X * Y = Y * X → X * Z = Z * X → Y * Z = Z * Y →
      X = 1 ∨ Y ∈ ([1, X, X ^ 2] : List (Equiv.Perm (Fin 28))) ∨ Z ∈ pow3list X Y := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h27a, h27b⟩ :=
      Certificates.certificate5133
    rw [QA_closure]
    intro X hX Y hY Z hZ hX3 hY3 hZ3 hXY hXZ hYZ
    by_cases hX1 : X = 1
    · exact Or.inl hX1
    · right
      have h := forall_of_classes _ {x | x ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf x = 3}
        [px1, px2] (E27At (Subgroup.closure {pa, pb, sg0})) (fun x hx => three_A x hx.1 hx.2)
        (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h27a
          · exact h27b)
        (fun g hg r hr => e27At_conj hg hr) X ⟨hX, orderOf_eq_prime hX3 hX1⟩
      exact h Y hY Z hZ hY3 hZ3 hXY hXZ hYZ
  rw [← hA] at he
  exact M.autRank3_le_two he R hR

theorem autRank_ge5
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (B : Subgroup (MulAut K))
    (hB : ElemAb p B) : Nat.card B ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_mulAut e
  have := elemAb_card_le (G := MulAut K) p B hB 1 (by
    rw [card_mulAut e]
    intro hdvd
    have hle : p ^ 2 ≤ 12096 := Nat.le_of_dvd (by norm_num) hdvd
    have : p ≤ 109 := by nlinarith
    interval_cases p <;> first | omega | (exfalso; revert hp; norm_num))
  simpa using this

theorem fixed_solvable
    (α : MulAut K) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1) (L : Subgroup K)
    (hL : ∀ x ∈ L, α x = x) : Group.IsSolvable L := by
  obtain ⟨M, hP, hA⟩ := autModel e
  obtain ⟨-, -, -, -, -, -, -, -, h96, h24, -⟩ := Certificates.certificate5133
  refine M.fixed_solvable (fun τ hτ h2 h1 => ?_) α hα2 hα1 L hL
  have hτ' : τ ∈ Subgroup.closure ({pa, pb, sg0} : Set (Equiv.Perm (Fin 28))) :=
    QA_closure ▸ hA ▸ hτ
  rw [hP, QP_closure]
  apply isSolvable_of_two_primes
  obtain ⟨r, hr, g, hg, rfl⟩ := invol_A τ hτ' (orderOf_eq_prime h2 h1)
  rw [card_inf_centralizer_eq, centCard_conj _ _ _ (normal_iff_of_conj conj_AP hg)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h96, primeFactors_96]
    decide
  · rw [h24, primeFactors_24]
    decide

end Consequences

end CFSG.GH74.KGroups.U33
