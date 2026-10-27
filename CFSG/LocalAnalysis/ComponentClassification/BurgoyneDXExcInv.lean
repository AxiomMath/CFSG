module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG Subgroup
open scoped MatrixGroups

theorem sl2_eq_neg_one_of_mul_self {k : Type} [Field k] (hk : ringChar k ≠ 2) {A : SL(2, k)}
    (h : A * A = 1) (hA : A ≠ 1) : A = -1 := by
  obtain ⟨a, b, c, d, hm⟩ : ∃ a b c d : k, (A : Matrix (Fin 2) (Fin 2) k) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have := A.2
    rwa [hm, Matrix.det_fin_two_of] at this
  have hsq := congrArg (fun M : SL(2, k) => (M : Matrix (Fin 2) (Fin 2) k)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hm] at hsq
  have h00 := congrFun (congrFun hsq 0) 0
  have h01 := congrFun (congrFun hsq 0) 1
  have h10 := congrFun (congrFun hsq 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  have hs : a + d ≠ 0 := by
    intro hs
    apply Ring.two_ne_zero hk
    linear_combination -(h00 + hdet) + a * hs
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination h01
    exact (mul_eq_zero.1 this).resolve_right hs
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination h10
    exact (mul_eq_zero.1 this).resolve_right hs
  subst hb hc
  have ha : a * a = 1 := by linear_combination h00
  have had : a * d = 1 := by linear_combination hdet
  have hda : d = a := by linear_combination a * had - d * ha
  subst hda
  rcases mul_self_eq_one_iff.1 ha with rfl | rfl
  · exfalso
    apply hA
    ext i j
    rw [hm, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp
  · ext i j
    rw [hm, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp

theorem eq_of_mul_self_of_sl {L : Type} [Group L] [Finite L] {Q : Subgroup L} {k : Type}
    [Field k] (hk : ringChar k ≠ 2) (e : Q ⧸ pPrimeCore 2 Q ≃* SL(2, k)) {c : L}
    (hcZ : c ∈ center L) (hcQ : c ∈ Q) (hc2 : orderOf c = 2) {u : L} (huQ : u ∈ Q)
    (huu : u * u = 1) (hu1 : u ≠ 1) : u = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ∀ x ∈ pPrimeCore 2 Q, x * x = 1 → x = 1 := by
    intro x hx hxx
    have hdvd : orderOf (⟨x, hx⟩ : pPrimeCore 2 Q) ∣ Nat.card (pPrimeCore 2 Q) :=
      orderOf_dvd_natCard _
    have hcop := Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card
    have h2 : orderOf (⟨x, hx⟩ : pPrimeCore 2 Q) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by
        change (x : Q) ^ 2 = 1
        rw [pow_two, hxx]))
    have h1 : orderOf (⟨x, hx⟩ : pPrimeCore 2 Q) = 1 :=
      Nat.Coprime.eq_one_of_dvd hcop.symm h2
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  have himage : ∀ v : Q, (v : L) * v = 1 → (v : L) ≠ 1 →
      e (QuotientGroup.mk v) = -1 := by
    intro v hvv hv1
    apply sl2_eq_neg_one_of_mul_self hk
    · rw [← map_mul, ← QuotientGroup.mk_mul, show v * v = 1 from Subtype.ext hvv,
        QuotientGroup.mk_one, map_one]
    · intro h
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h
      exact hv1 (congrArg Subtype.val (hodd v h (Subtype.ext hvv)))
  have hcc : c * c = 1 := by rw [← pow_two, ← hc2, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have h1 := himage ⟨u, huQ⟩ huu hu1
  have h2 := himage ⟨c, hcQ⟩ hcc hc1
  have hmem : (⟨u, huQ⟩ : Q)⁻¹ * ⟨c, hcQ⟩ ∈ pPrimeCore 2 Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      ← MulEquiv.map_eq_one_iff e, map_mul, map_inv, h1, h2, inv_mul_cancel]
  have hsq : ((⟨u, huQ⟩ : Q)⁻¹ * ⟨c, hcQ⟩) * ((⟨u, huQ⟩ : Q)⁻¹ * ⟨c, hcQ⟩) = 1 := by
    apply Subtype.ext
    change (u⁻¹ * c) * (u⁻¹ * c) = 1
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    rw [hu', mul_assoc, ← mul_assoc c, ← mem_center_iff.mp hcZ u, mul_assoc, ← mul_assoc,
      huu, one_mul, hcc]
  have := hodd _ hmem hsq
  have h3 : u⁻¹ * c = 1 := congrArg Subtype.val this
  exact inv_mul_eq_one.mp h3

section Quaternion

variable {G : Type*} [Group G]

theorem isPGroup_two_closure_quaternion {a b z : G} (hz : z ∈ center G) (hzz : z * z = 1)
    (ha : a * a = z) (hb : b * b = z) (hba : b * a = z * (a * b)) :
    IsPGroup 2 (closure ({a, b} : Set G)) := by
  have hzc : ∀ x : G, x * z = z * x := fun x => mem_center_iff.mp hz x
  set S : Set G := {1, z, a, z * a, b, z * b, a * b, z * (a * b)} with hS
  have hzS : ∀ x ∈ S, z * x ∈ S := by
    intro x hx
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h]
    · right; left; exact mul_one z
    · left; exact hzz
    · right; right; right; left; rfl
    · right; right; left; rw [← mul_assoc, hzz, one_mul]
    · right; right; right; right; right; left; rfl
    · right; right; right; right; left; rw [← mul_assoc, hzz, one_mul]
    · right; right; right; right; right; right; right; rfl
    · right; right; right; right; right; right; left; rw [← mul_assoc, hzz, one_mul]
  have haS : ∀ x ∈ S, a * x ∈ S := by
    intro x hx
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h]
    · right; right; left; exact mul_one a
    · right; right; right; left; exact hzc a
    · right; left; exact ha
    · left; rw [← mul_assoc, hzc, mul_assoc, ha, hzz]
    · right; right; right; right; right; right; left; rfl
    · right; right; right; right; right; right; right; rw [← mul_assoc, hzc, mul_assoc]
    · right; right; right; right; right; left; rw [← mul_assoc, ha]
    · right; right; right; right; left
      rw [← mul_assoc, hzc, mul_assoc, ← mul_assoc a, ha, ← mul_assoc, hzz, one_mul]
  have hbS : ∀ x ∈ S, b * x ∈ S := by
    intro x hx
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h]
    · right; right; right; right; left; exact mul_one b
    · right; right; right; right; right; left; exact hzc b
    · right; right; right; right; right; right; right; exact hba
    · right; right; right; right; right; right; left
      rw [← mul_assoc, hzc, mul_assoc, hba, ← mul_assoc, hzz, one_mul]
    · right; left; exact hb
    · left; rw [← mul_assoc, hzc, mul_assoc, hb, hzz]
    · right; right; left
      rw [← mul_assoc, hba, mul_assoc, mul_assoc, hb, hzc a, ← mul_assoc, hzz, one_mul]
    · right; right; right; left
      rw [← mul_assoc, hzc, mul_assoc, ← mul_assoc b, hba, mul_assoc, mul_assoc, hb, hzc a,
        ← mul_assoc z, hzz, one_mul]
  have key : ∀ g ∈ ({a, b} : Set G), ∀ x ∈ S, g * x ∈ S := by
    intro g hg x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg <;> rw [hg]
    · exact haS x hx
    · exact hbS x hx
  have hinv : ∀ g ∈ ({a, b} : Set G), g⁻¹ = z * g := by
    intro g hg
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg <;> rw [hg]
    · rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hzc a, mul_assoc, ha, hzz]
    · rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hzc b, mul_assoc, hb, hzz]
  have hmem : ∀ x ∈ closure ({a, b} : Set G), x ∈ S := by
    intro x hx
    induction hx using closure_induction_left with
    | one => exact Set.mem_insert _ _
    | mul_left g hg y _ hy => exact key g hg y hy
    | inv_mul_cancel g hg y _ hy =>
      rw [hinv g hg, mul_assoc]
      exact hzS _ (key g hg y hy)
  have hsq : ∀ x ∈ S, x * x = 1 ∨ x * x = z := by
    have hab : (a * b) * (a * b) = z := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (z * (a * b)) * b := by rw [hba]
        _ = z * (a * a * (b * b)) := by
            rw [show a * (z * (a * b)) * b = a * z * a * (b * b) by group, hzc a]; group
        _ = z := by rw [ha, hb, hzz, mul_one]
    have hzy : ∀ y : G, y * y = z → (z * y) * (z * y) = z := by
      intro y hy
      calc (z * y) * (z * y) = z * (y * z) * y := by group
        _ = z * z * (y * y) := by rw [hzc y]; group
        _ = z := by rw [hzz, one_mul, hy]
    intro x hx
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h]
    · left; exact mul_one 1
    · left; exact hzz
    · right; exact ha
    · right; exact hzy a ha
    · right; exact hb
    · right; exact hzy b hb
    · right; exact hab
    · right; exact hzy _ hab
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  have e : (g : G) ^ 2 ^ 2 = ((g : G) * g) * ((g : G) * g) := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, pow_two]
  rw [e]
  rcases hsq g (hmem g g.2) with h | h <;> rw [h]
  · exact mul_one 1
  · exact hzz

end Quaternion

theorem exists_lift_of_odd_kernel {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (π : G →* H)
    (hπ : Function.Surjective π) (hodd : Nat.Coprime 2 (Nat.card π.ker)) {E : Subgroup H}
    (hE : IsPGroup 2 E) :
    ∃ T : Subgroup G, T.map π = E ∧ ∀ t ∈ T, π t = 1 → t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := E.comap π with hM
  set N := π.ker.subgroupOf M with hN
  have hNn : N.Normal := inferInstance
  let πM : M →* E := (π.comp M.subtype).codRestrict E fun m => m.2
  have hπM : Function.Surjective πM := by
    rintro ⟨e, he⟩
    obtain ⟨g, rfl⟩ := hπ e
    exact ⟨⟨g, he⟩, rfl⟩
  have hkerM : πM.ker = N := by
    ext m
    rw [MonoidHom.mem_ker, hN, mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hindex : N.index = Nat.card E := by
    rw [← hkerM, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπM, Subgroup.card_top]
  have hcardN : Nat.card N = Nat.card (π.ker.subgroupOf M) := rfl
  have hNcop : Nat.Coprime 2 (Nat.card N) := by
    have hle : π.ker ≤ M := fun g hg => by
      rw [hM, mem_comap, MonoidHom.mem_ker.mp hg]
      exact one_mem _
    rw [hN, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact hodd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hE
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hindex, hk]
    exact Nat.Coprime.pow_right k hNcop.symm
  obtain ⟨T, hT⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨T.map M.subtype, ?_, ?_⟩
  · ext e
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact t.2
    · intro he
      obtain ⟨g, rfl⟩ := hπ e
      obtain ⟨⟨⟨n, hn⟩, ⟨t, ht⟩⟩, hnt, -⟩ := hT.existsUnique ⟨g, he⟩
      refine ⟨(t : G), ⟨t, ht, rfl⟩, ?_⟩
      have h1 : π (n : G) = 1 := by
        have := hn
        rw [SetLike.mem_coe, hN, mem_subgroupOf, MonoidHom.mem_ker] at this
        exact this
      have h2 : (n : G) * t = g := congrArg Subtype.val hnt
      rw [← h2, map_mul, h1, one_mul]
  · rintro _ ⟨t, ht, rfl⟩ h1
    have htN : t ∈ N := by
      rw [hN, mem_subgroupOf, MonoidHom.mem_ker]
      exact h1
    have := hT.disjoint.le_bot ⟨htN, ht⟩
    rw [mem_bot] at this
    rw [this]
    rfl

section SL2Quaternion

variable {k : Type} [Field k]

@[expose] def qI : SL(2, k) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

@[expose] def qJ {a b : k} (hab : a ^ 2 + b ^ 2 = -1) : SL(2, k) :=
  ⟨!![a, b; b, -a], by rw [Matrix.det_fin_two_of]; linear_combination -hab⟩

theorem coe_qI : ((qI : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl

theorem coe_qJ {a b : k} (hab : a ^ 2 + b ^ 2 = -1) :
    ((qJ hab : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![a, b; b, -a] := rfl

theorem qI_mul_self : (qI : SL(2, k)) * qI = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_qI, Matrix.mul_apply, Fin.sum_univ_two]

theorem qJ_mul_self {a b : k} (hab : a ^ 2 + b ^ 2 = -1) : qJ hab * qJ hab = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_qJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination hab | linear_combination -hab | ring

theorem qJ_mul_qI {a b : k} (hab : a ^ 2 + b ^ 2 = -1) :
    qJ hab * qI = -1 * (qI * qJ hab) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_qI, coe_qJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem neg_one_mem_center_sl : (-1 : SL(2, k)) ∈ center SL(2, k) := by
  rw [mem_center_iff]
  intro g
  ext i j
  simp

theorem exists_sq_add_sq_eq_neg_one [Finite k] (hk : ringChar k ≠ 2) :
    ∃ a b : k, a ^ 2 + b ^ 2 = -1 := by
  have : Fintype k := Fintype.ofFinite k
  have hodd : Fintype.card k % 2 = 1 := by
    obtain ⟨n, hp, hn⟩ := FiniteField.card k (ringChar k)
    rw [hn]
    have hp2 : ringChar k % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hp with h | h
      · exact absurd h hk
      · exact h
    rw [Nat.pow_mod, hp2, one_pow]
    rfl
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 + Polynomial.C 1)
    (by rw [Polynomial.degree_X_pow]; rfl)
    (by rw [Polynomial.degree_X_pow_add_C (by norm_num)]; rfl) hodd
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_C] at hab
  linear_combination hab

theorem qI_ne {a b : k} (hk : ringChar k ≠ 2) (hab : a ^ 2 + b ^ 2 = -1) :
    (qI : SL(2, k)) ≠ 1 ∧ (qI : SL(2, k)) ≠ -1 ∧ qJ hab ≠ 1 ∧ qJ hab ≠ -1 ∧ qJ hab ≠ qI ∧
      qJ hab ≠ -1 * qI := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have entry : ∀ {A B : SL(2, k)} (i j : Fin 2), A = B →
      (A : Matrix (Fin 2) (Fin 2) k) i j = (B : Matrix (Fin 2) (Fin 2) k) i j :=
    fun i j h => by rw [h]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := entry 0 1 h
    simp [coe_qI] at this
  · have := entry 0 1 h
    simp [coe_qI] at this
  · have h1 := entry 0 1 h
    have h2' := entry 0 0 h
    have h3 := entry 1 1 h
    simp [coe_qJ] at h1 h2' h3
    subst h1
    apply h2
    linear_combination -h2' - h3
  · have h1 := entry 0 1 h
    have h2' := entry 0 0 h
    have h3 := entry 1 1 h
    simp [coe_qJ] at h1 h2' h3
    subst h1
    apply h2
    linear_combination h2' - h3
  · have h1 := entry 0 1 h
    have h3 := entry 1 0 h
    simp [coe_qI, coe_qJ] at h1 h3
    apply h2
    linear_combination -h1 + h3
  · have h1 := entry 0 1 h
    have h3 := entry 1 0 h
    simp [coe_qI, coe_qJ] at h1 h3
    apply h2
    linear_combination h1 - h3

end SL2Quaternion

end CFSG.ComponentClassification.Burgoyne.DX
