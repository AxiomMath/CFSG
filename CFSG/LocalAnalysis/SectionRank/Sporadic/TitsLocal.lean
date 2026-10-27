module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import Certificates.Data.CFSGNative.SectionRank.TitsLocal
public meta import Certificates.Data.CFSGNative.SectionRank.TitsLocal
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.SectionRank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  CFSG.SectionRank.TitsGen CFSG.SectionRank.TitsOrder CFSG.SectionRank.Native.Tits
  CFSG.Sporadic.Th CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Th.Native (ap invT invOK idT compT powT Table allIn wordT)
open scoped commutatorElement

attribute [local instance] idxAction

theorem tits_sylow3_check : cubicOK titsSylow3 = true :=
  Certificates.certificate8032.1

theorem tits_sylow5_check : squareOK titsSylow5 = true :=
  Certificates.certificate8032.2

namespace TitsLocal

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem letterG_neg
    (l : ℤ) : letterG K (-l) = (letterG K l)⁻¹ := by
  unfold letterG
  by_cases h1 : 0 < l ∧ l ≤ 4
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left h1, neg_neg]
  · rw [ite_eq_right h1]
    by_cases h2 : l < 0 ∧ -l ≤ 4
    · rw [ite_eq_left (by omega), ite_eq_left h2, inv_inv]
    · rw [ite_eq_right h2, ite_eq_right (by omega), ite_eq_right (by omega), inv_one]

theorem g0_mem :
    g0 K ∈ commutator (reeFixed ReeTag.F4 K 0) := by
  refine mem_commutator_of_conj_mem (x := z1 K) ?_
  have h : z1 K * g0 K * (z1 K)⁻¹ = ⁅(z1 K * z2 K) * g1 K * (z1 K * z2 K)⁻¹, g1 K⁆ :=
    Subtype.ext tits_R2.symm
  rw [h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem g1_sq_mem :
    g1 K ^ 2 ∈ commutator (reeFixed ReeTag.F4 K 0) := by
  refine mem_commutator_of_conj_mem (x := z2 K) ?_
  have h : z2 K * g1 K ^ 2 * (z2 K)⁻¹ =
      ⁅z1 K * g1 K * (z1 K)⁻¹, (z2 K * z1 K) * g0 K * (z2 K * z1 K)⁻¹⁆ :=
    Subtype.ext tits_R1.symm
  rw [h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem wordG_append
    (w w' : List ℤ) :
    wordG (letterG K) (w ++ w') = wordG (letterG K) w * wordG (letterG K) w' := by
  simp [wordG]

theorem mem_of_isManifest
    {w : List ℤ} (h : isManifest w = true) :
    wordG (letterG K) w ∈ commutator (reeFixed ReeTag.F4 K 0) := by
  have h0 := g0_mem (K := K)
  have h1 := g1_sq_mem (K := K)
  have e0 : letterG K 1 = g0 K := rfl
  have e1 : letterG K 2 = g1 K := rfl
  have e0' : letterG K (-1) = (g0 K)⁻¹ := rfl
  have e1' : letterG K (-2) = (g1 K)⁻¹ := rfl
  unfold isManifest at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
  rcases h with ((((rfl | rfl) | rfl) | rfl) | ⟨⟨hlen, h2⟩, h3⟩)
  · simp only [wordG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, e0]
    exact h0
  · simp only [wordG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, e0']
    exact inv_mem h0
  · simp only [wordG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, e1]
    rw [pow_two] at h1
    exact h1
  · have := inv_mem h1
    simp only [wordG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, e1']
    rw [pow_two, mul_inv_rev] at this
    exact this
  · rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, w⟩⟩⟩⟩⟩ <;>
      simp only [List.length_nil, List.length_cons] at hlen <;> try omega
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero] at h2 h3
    subst h2 h3
    have e : wordG (letterG K) [a, b, -a, -b] = ⁅letterG K a, letterG K b⁆ := by
      simp only [wordG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        letterG_neg, commutatorElement_def, mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

variable (K) in
@[expose] noncomputable def tword
    (tw : List ℕ) : reeFixed ReeTag.F4 K 0 :=
  (tw.map fun k => wordG (letterG K) tLetters[k]!).prod

theorem tword_eq
    (tw : List ℕ) : tword K tw = wordG (letterG K) (texpand tw) := by
  induction tw with
  | nil => rfl
  | cons k tw ih =>
    have e : texpand (k :: tw) = tLetters[k]! ++ texpand tw := by simp [texpand]
    rw [e, wordG_append, ← ih]
    simp [tword]

theorem tword_mem
    (hT : allIn 0 tLetters.size (fun k => isManifest tLetters[k]!) = true)
    {tw : List ℕ} (hw : tw.all (· < tLetters.size) = true) :
    tword K tw ∈ commutator (reeFixed ReeTag.F4 K 0) := by
  refine list_prod_mem fun g hg => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
  have hk' : k < tLetters.size := by simpa using List.all_eq_true.1 hw k hk
  exact mem_of_isManifest ((allIn_eq_true.1 hT) k (Nat.zero_le _) hk')

section Tables

variable [Fact (Nat.card K = 2)]

theorem rep_tword
    (tw : List ℕ) : Rep nPts (wT (texpand tw)) (tword K tw) := by
  rw [tword_eq]
  exact Rep.wordT (by norm_num [nPts]) _ fun l _ => rep_letterG l

theorem checkPts_lt : ∀ t < checkPts.size, checkPts[t]! < nPts :=
  (chainOK_parts titsChainCheck_parts.2.2.2.2.1).2.2.2.2.1

theorem eq_of_eqOn
    {P Q : Table} {g h : reeFixed ReeTag.F4 K 0} (hP : Rep nPts P g)
    (hQ : Rep nPts Q h) (he : eqOn P Q = true) : g = h := by
  have h1 : h⁻¹ * g = 1 := by
    apply sep
    intro t ht
    have hlt := checkPts_lt t ht
    have := (allIn_eq_true.1 he) t (Nat.zero_le _) ht
    rw [beq_iff_eq, hP _ hlt, hQ _ hlt] at this
    rw [idx_mul, this, idx_inv_idx]
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem ne_of_eqOn_eq_false
    {P Q : Table}
    {g h : reeFixed ReeTag.F4 K 0} (hP : Rep nPts P g)
    (hQ : Rep nPts Q h) (he : eqOn P Q = false) : g ≠ h := by
  rintro rfl
  have : eqOn P Q = true := by
    refine allIn_eq_true.2 fun t _ ht => ?_
    have hlt := checkPts_lt t ht
    rw [beq_iff_eq, hP _ hlt, hQ _ hlt]
  rw [this] at he
  exact Bool.noConfusion he

theorem rep_nfT
    {X Y Z : Table} {x y z : reeFixed ReeTag.F4 K 0}
    (hX : Rep nPts X x) (hY : Rep nPts Y y) (hZ : Rep nPts Z z) (i j k : ℕ) :
    Rep nPts (nfT X Y Z i j k) (x ^ i * y ^ j * z ^ k) :=
  ((hX.powT (by norm_num [nPts]) i).compT (hY.powT (by norm_num [nPts]) j)).compT
    (hZ.powT (by norm_num [nPts]) k)

theorem rep_idT :
    Rep nPts (idT nPts) (1 : reeFixed ReeTag.F4 K 0) :=
  Rep.idT (by norm_num [nPts])

end Tables

section D

variable [Fact (Nat.card K = 2)]

theorem eqD
    {P Q : Table} {u v : commutator (reeFixed ReeTag.F4 K 0)}
    (hP : Rep nPts P (u : reeFixed ReeTag.F4 K 0)) (hQ : Rep nPts Q (v : reeFixed ReeTag.F4 K 0))
    (he : eqOn P Q = true) : u = v :=
  Subtype.ext (eq_of_eqOn hP hQ he)

theorem neD
    {P Q : Table} {u v : commutator (reeFixed ReeTag.F4 K 0)}
    (hP : Rep nPts P (u : reeFixed ReeTag.F4 K 0)) (hQ : Rep nPts Q (v : reeFixed ReeTag.F4 K 0))
    (he : eqOn P Q = false) : u ≠ v :=
  fun e => ne_of_eqOn_eq_false hP hQ he (congrArg Subtype.val e)

theorem repD_mul
    {P Q : Table} {u v : commutator (reeFixed ReeTag.F4 K 0)}
    (hP : Rep nPts P (u : reeFixed ReeTag.F4 K 0)) (hQ : Rep nPts Q (v : reeFixed ReeTag.F4 K 0)) :
    Rep nPts (compT nPts P Q) ((u * v : commutator (reeFixed ReeTag.F4 K 0)) :
      reeFixed ReeTag.F4 K 0) := by
  rw [Subgroup.coe_mul]
  exact hP.compT hQ

theorem repD_pow
    {P : Table} {u : commutator (reeFixed ReeTag.F4 K 0)}
    (hP : Rep nPts P (u : reeFixed ReeTag.F4 K 0)) (e : ℕ) :
    Rep nPts (powT nPts e P) ((u ^ e : commutator (reeFixed ReeTag.F4 K 0)) :
      reeFixed ReeTag.F4 K 0) := by
  rw [Subgroup.coe_pow]
  exact hP.powT (by norm_num [nPts]) e

theorem repD_one :
    Rep nPts (idT nPts) ((1 : commutator (reeFixed ReeTag.F4 K 0)) : reeFixed ReeTag.F4 K 0) :=
  rep_idT

theorem repD_inv
    {P : Table} {u : commutator (reeFixed ReeTag.F4 K 0)}
    (hP : Rep nPts P (u : reeFixed ReeTag.F4 K 0)) (h : invOK nPts P (invT nPts P) = true) :
    Rep nPts (invT nPts P) ((u⁻¹ : commutator (reeFixed ReeTag.F4 K 0)) :
      reeFixed ReeTag.F4 K 0) := by
  rw [Subgroup.coe_inv]
  exact hP.inv_of_invOK h

theorem repD_comm
    {X Y : Table} {x y : commutator (reeFixed ReeTag.F4 K 0)}
    (rX : Rep nPts X (x : reeFixed ReeTag.F4 K 0)) (rY : Rep nPts Y (y : reeFixed ReeTag.F4 K 0))
    (hXi : invOK nPts X (invT nPts X) = true) (hYi : invOK nPts Y (invT nPts Y) = true) :
    Rep nPts (compT nPts (compT nPts (compT nPts X Y) (invT nPts X)) (invT nPts Y))
      ((⁅x, y⁆ : commutator (reeFixed ReeTag.F4 K 0)) : reeFixed ReeTag.F4 K 0) := by
  rw [commutatorElement_def]
  exact repD_mul (repD_mul (repD_mul rX rY) (repD_inv rX hXi)) (repD_inv rY hYi)

theorem repD_nf
    {X Y Z : Table} {x y z : commutator (reeFixed ReeTag.F4 K 0)}
    (rX : Rep nPts X (x : reeFixed ReeTag.F4 K 0)) (rY : Rep nPts Y (y : reeFixed ReeTag.F4 K 0))
    (rZ : Rep nPts Z (z : reeFixed ReeTag.F4 K 0)) (i j k : ℕ) :
    Rep nPts (nfT X Y Z i j k) ((x ^ i * y ^ j * z ^ k : commutator (reeFixed ReeTag.F4 K 0)) :
      reeFixed ReeTag.F4 K 0) :=
  repD_mul (repD_mul (repD_pow rX i) (repD_pow rY j)) (repD_pow rZ k)

omit [Fact (Nat.card K = 2)] in
theorem conj_of_mul
    {g u v : commutator (reeFixed ReeTag.F4 K 0)} (e : g * u = v * g) :
    g * u * g⁻¹ = v := by
  rw [e, mul_inv_cancel_right]

theorem injective_cube
    {X Y Z : Table}
    {x y z : commutator (reeFixed ReeTag.F4 K 0)} (rX : Rep nPts X (x : reeFixed ReeTag.F4 K 0))
    (rY : Rep nPts Y (y : reeFixed ReeTag.F4 K 0)) (rZ : Rep nPts Z (z : reeFixed ReeTag.F4 K 0))
    (hnf : allIn 0 27 (fun u => allIn 0 27 fun v => u == v ||
      !eqOn (nfT X Y Z (u % 3) (u / 3 % 3) (u / 9)) (nfT X Y Z (v % 3) (v / 3 % 3) (v / 9))) =
        true) :
    Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 =>
      x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * z ^ (t.2.2 : ℕ) := by
  rintro ⟨i, j, m⟩ ⟨i', j', m'⟩ e
  by_contra hne
  have hu : (i : ℕ) + 3 * j + 9 * m < 27 := by omega
  have hv : (i' : ℕ) + 3 * j' + 9 * m' < 27 := by omega
  have huv : (i : ℕ) + 3 * j + 9 * m ≠ i' + 3 * j' + 9 * m' := by
    intro huv
    apply hne
    have h1 : (i : ℕ) = i' := by omega
    have h2 : (j : ℕ) = j' := by omega
    have h3 : (m : ℕ) = m' := by omega
    rw [Fin.ext h1, Fin.ext h2, Fin.ext h3]
  have hc := (allIn_eq_true.1 ((allIn_eq_true.1 hnf) _ (Nat.zero_le _) hu)) _ (Nat.zero_le _) hv
  beta_reduce at hc
  rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  rcases hc with hc | hc
  · exact huv hc
  · rw [show ((i : ℕ) + 3 * j + 9 * m) % 3 = i by omega,
      show ((i : ℕ) + 3 * j + 9 * m) / 3 % 3 = j by omega,
      show ((i : ℕ) + 3 * j + 9 * m) / 9 = m by omega,
      show ((i' : ℕ) + 3 * j' + 9 * m') % 3 = i' by omega,
      show ((i' : ℕ) + 3 * j' + 9 * m') / 3 % 3 = j' by omega,
      show ((i' : ℕ) + 3 * j' + 9 * m') / 9 = m' by omega] at hc
    exact neD (repD_nf rX rY rZ i j m) (repD_nf rX rY rZ i' j' m') hc e

theorem injective_sq
    {X Y : Table}
    {x y : commutator (reeFixed ReeTag.F4 K 0)} (rX : Rep nPts X (x : reeFixed ReeTag.F4 K 0))
    (rY : Rep nPts Y (y : reeFixed ReeTag.F4 K 0))
    (hnf : allIn 0 25 (fun u => allIn 0 25 fun v => u == v ||
      !eqOn (nfT X Y (idT nPts) (u % 5) (u / 5) 0) (nfT X Y (idT nPts) (v % 5) (v / 5) 0)) =
        true) :
    Function.Injective fun t : Fin 5 × Fin 5 => x ^ (t.1 : ℕ) * y ^ (t.2 : ℕ) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ e
  by_contra hne
  have hu : (i : ℕ) + 5 * j < 25 := by omega
  have hv : (i' : ℕ) + 5 * j' < 25 := by omega
  have huv : (i : ℕ) + 5 * j ≠ i' + 5 * j' := by
    intro huv
    apply hne
    have h1 : (i : ℕ) = i' := by omega
    have h2 : (j : ℕ) = j' := by omega
    rw [Fin.ext h1, Fin.ext h2]
  have hc := (allIn_eq_true.1 ((allIn_eq_true.1 hnf) _ (Nat.zero_le _) hu)) _ (Nat.zero_le _) hv
  beta_reduce at hc
  rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  rcases hc with hc | hc
  · exact huv hc
  · rw [show ((i : ℕ) + 5 * j) % 5 = i by omega, show ((i : ℕ) + 5 * j) / 5 = j by omega,
      show ((i' : ℕ) + 5 * j') % 5 = i' by omega, show ((i' : ℕ) + 5 * j') / 5 = j' by omega] at hc
    have r1 := repD_nf rX rY (repD_one (K := K)) i j 0
    have r2 := repD_nf rX rY (repD_one (K := K)) i' j' 0
    rw [pow_zero, mul_one] at r1 r2
    exact neD r1 r2 hc e

theorem cubic_of_tables
    {X Y H : Table} {x y g : commutator (reeFixed ReeTag.F4 K 0)}
    {a b c d k l μ : ℕ}
    (rX : Rep nPts X (x : reeFixed ReeTag.F4 K 0)) (rY : Rep nPts Y (y : reeFixed ReeTag.F4 K 0))
    (rH : Rep nPts H (g : reeFixed ReeTag.F4 K 0))
    (hXi : invOK nPts X (invT nPts X) = true) (hYi : invOK nPts Y (invT nPts Y) = true)
    (hX3 : eqOn (powT nPts 3 X) (idT nPts) = true) (hY3 : eqOn (powT nPts 3 Y) (idT nPts) = true)
    (hZ1 : eqOn (compT nPts (compT nPts (compT nPts X Y) (invT nPts X)) (invT nPts Y))
      (idT nPts) = false)
    (hZX : eqOn (compT nPts (compT nPts (compT nPts (compT nPts X Y) (invT nPts X))
      (invT nPts Y)) X) (compT nPts X (compT nPts (compT nPts (compT nPts X Y) (invT nPts X))
        (invT nPts Y))) = true)
    (hZY : eqOn (compT nPts (compT nPts (compT nPts (compT nPts X Y) (invT nPts X))
      (invT nPts Y)) Y) (compT nPts Y (compT nPts (compT nPts (compT nPts X Y) (invT nPts X))
        (invT nPts Y))) = true)
    (hnf : allIn 0 27 (fun u => allIn 0 27 fun v => u == v ||
      !eqOn (nfT X Y (compT nPts (compT nPts (compT nPts X Y) (invT nPts X)) (invT nPts Y))
          (u % 3) (u / 3 % 3) (u / 9))
        (nfT X Y (compT nPts (compT nPts (compT nPts X Y) (invT nPts X)) (invT nPts Y))
          (v % 3) (v / 3 % 3) (v / 9))) = true)
    (hHX : eqOn (compT nPts H X) (compT nPts (nfT X Y (compT nPts (compT nPts (compT nPts X Y)
      (invT nPts X)) (invT nPts Y)) a b k) H) = true)
    (hHY : eqOn (compT nPts H Y) (compT nPts (nfT X Y (compT nPts (compT nPts (compT nPts X Y)
      (invT nPts X)) (invT nPts Y)) c d l) H) = true)
    (hHZ : eqOn (compT nPts H (compT nPts (compT nPts (compT nPts X Y) (invT nPts X))
      (invT nPts Y))) (compT nPts (powT nPts μ (compT nPts (compT nPts (compT nPts X Y)
        (invT nPts X)) (invT nPts Y))) H) = true) :
    x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set (commutator (reeFixed ReeTag.F4 K 0)))) =
        3 ^ 3 ∧
      g * x * g⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k ∧
      g * y * g⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l ∧ g * ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆ ^ μ := by
  have rZ := repD_comm rX rY hXi hYi
  have hx3 : x ^ 3 = 1 := eqD (repD_pow rX 3) repD_one hX3
  have hy3 : y ^ 3 = 1 := eqD (repD_pow rY 3) repD_one hY3
  have hzx : Commute ⁅x, y⁆ x := eqD (repD_mul rZ rX) (repD_mul rX rZ) hZX
  have hzy : Commute ⁅x, y⁆ y := eqD (repD_mul rZ rY) (repD_mul rY rZ) hZY
  exact ⟨hx3, hy3, neD rZ repD_one hZ1, hzx, hzy,
    LocalWitness.card_closure_eq_cube (by norm_num) hx3 hy3 hzx hzy (injective_cube rX rY rZ hnf),
    conj_of_mul (eqD (repD_mul rH rX) (repD_mul (repD_nf rX rY rZ a b k) rH) hHX),
    conj_of_mul (eqD (repD_mul rH rY) (repD_mul (repD_nf rX rY rZ c d l) rH) hHY),
    conj_of_mul (eqD (repD_mul rH rZ) (repD_mul (repD_pow rZ μ) rH) hHZ)⟩

theorem square_of_tables
    {X Y H : Table} {x y g : commutator (reeFixed ReeTag.F4 K 0)}
    {a b c d : ℕ}
    (rX : Rep nPts X (x : reeFixed ReeTag.F4 K 0)) (rY : Rep nPts Y (y : reeFixed ReeTag.F4 K 0))
    (rH : Rep nPts H (g : reeFixed ReeTag.F4 K 0))
    (hX5 : eqOn (powT nPts 5 X) (idT nPts) = true) (hY5 : eqOn (powT nPts 5 Y) (idT nPts) = true)
    (hXY : eqOn (compT nPts X Y) (compT nPts Y X) = true)
    (hnf : allIn 0 25 (fun u => allIn 0 25 fun v => u == v ||
      !eqOn (nfT X Y (idT nPts) (u % 5) (u / 5) 0) (nfT X Y (idT nPts) (v % 5) (v / 5) 0)) =
        true)
    (hHX : eqOn (compT nPts H X) (compT nPts (nfT X Y (idT nPts) a c 0) H) = true)
    (hHY : eqOn (compT nPts H Y) (compT nPts (nfT X Y (idT nPts) b d 0) H) = true) :
    x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set (commutator (reeFixed ReeTag.F4 K 0)))) =
        5 ^ 2 ∧
      g * x * g⁻¹ = x ^ a * y ^ c ∧ g * y * g⁻¹ = x ^ b * y ^ d := by
  have hx5 : x ^ 5 = 1 := eqD (repD_pow rX 5) repD_one hX5
  have hy5 : y ^ 5 = 1 := eqD (repD_pow rY 5) repD_one hY5
  have hxy : x * y = y * x := eqD (repD_mul rX rY) (repD_mul rY rX) hXY
  have rNF : ∀ i j : ℕ, Rep nPts (nfT X Y (idT nPts) i j 0)
      ((x ^ i * y ^ j : commutator (reeFixed ReeTag.F4 K 0)) : reeFixed ReeTag.F4 K 0) := by
    intro i j
    have := repD_nf rX rY (repD_one (K := K)) i j 0
    rwa [pow_zero, mul_one] at this
  exact ⟨hx5, hy5, hxy,
    LocalWitness.card_closure_eq_sq (by norm_num) hx5 hy5 hxy (injective_sq rX rY hnf),
    conj_of_mul (eqD (repD_mul rH rX) (repD_mul (rNF a c) rH) hHX),
    conj_of_mul (eqD (repD_mul rH rY) (repD_mul (rNF b d) rH) hHY)⟩

end D

theorem cubic_of_cubicOK
    (hK : Nat.card K = 2) (W : TitsWitness) (h : cubicOK W = true)
    {a b c d k l μ : ℕ} (hn : W.nums = [a, b, c, d, k, l, μ]) :
    ∃ x y g : commutator (reeFixed ReeTag.F4 K 0),
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set (commutator (reeFixed ReeTag.F4 K 0)))) =
        3 ^ 3 ∧
      g * x * g⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k ∧
      g * y * g⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l ∧ g * ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆ ^ μ := by
  have : Fact (Nat.card K = 2) := ⟨hK⟩
  unfold cubicOK at h
  simp only [hn, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.getElem!_cons_zero,
    List.getElem!_cons_succ] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL, -⟩, hXi⟩, hYi⟩, hX3⟩, hY3⟩, hZ1⟩, hZX⟩, hZY⟩, hnf⟩, hHX⟩, hHY⟩,
    hHZ⟩ := h
  simp only [lettersOK, Bool.and_eq_true, List.all_append] at hL
  obtain ⟨hT, ⟨hwx, hwy⟩, hwh⟩ := hL
  exact ⟨⟨tword K W.wx, tword_mem hT hwx⟩, ⟨tword K W.wy, tword_mem hT hwy⟩,
    ⟨tword K W.wh, tword_mem hT hwh⟩,
    cubic_of_tables (rep_tword W.wx) (rep_tword W.wy) (rep_tword W.wh) hXi hYi hX3 hY3 hZ1 hZX
      hZY hnf hHX hHY hHZ⟩

theorem square_of_squareOK
    (hK : Nat.card K = 2) (W : TitsWitness) (h : squareOK W = true)
    {a b c d : ℕ} (hn : W.nums = [a, b, c, d]) :
    ∃ x y g : commutator (reeFixed ReeTag.F4 K 0),
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set (commutator (reeFixed ReeTag.F4 K 0)))) =
        5 ^ 2 ∧
      g * x * g⁻¹ = x ^ a * y ^ c ∧ g * y * g⁻¹ = x ^ b * y ^ d := by
  have : Fact (Nat.card K = 2) := ⟨hK⟩
  unfold squareOK at h
  simp only [hn, Bool.and_eq_true, beq_iff_eq, List.getElem!_cons_zero,
    List.getElem!_cons_succ] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hL, -⟩, hX5⟩, hY5⟩, hXY⟩, hnf⟩, hHX⟩, hHY⟩ := h
  simp only [lettersOK, Bool.and_eq_true, List.all_append] at hL
  obtain ⟨hT, ⟨hwx, hwy⟩, hwh⟩ := hL
  exact ⟨⟨tword K W.wx, tword_mem hT hwx⟩, ⟨tword K W.wy, tword_mem hT hwy⟩,
    ⟨tword K W.wh, tword_mem hT hwh⟩,
    square_of_tables (rep_tword W.wx) (rep_tword W.wy) (rep_tword W.wh) hX5 hY5 hXY hnf hHX
      hHY⟩

end TitsLocal

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem Tits_sylow3_cubic_witness
    (hK : Nat.card K = 2) :
    ∃ x y h : commutator (reeFixed ReeTag.F4 K 0),
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set (commutator (reeFixed ReeTag.F4 K 0)))) =
        3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 1 * y ^ 2 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 2 * y ^ 2 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 :=
  TitsLocal.cubic_of_cubicOK hK titsSylow3 tits_sylow3_check rfl

theorem Tits_sylow5_square_witness
    (hK : Nat.card K = 2) :
    ∃ x y h : commutator (reeFixed ReeTag.F4 K 0),
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set (commutator (reeFixed ReeTag.F4 K 0)))) =
        5 ^ 2 ∧
      h * x * h⁻¹ = x ^ 3 * y ^ 3 ∧ h * y * h⁻¹ = x ^ 4 * y ^ 2 :=
  TitsLocal.square_of_squareOK hK titsSylow5 tits_sylow5_check rfl

end CFSG.SectionRank
