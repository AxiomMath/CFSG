module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

theorem c25_mem_of_pow_three_of_index {M : Type*} [Group M] [Finite M] (H : Subgroup M)
    [H.Normal] (hidx : H.index ∣ 2) {α : M} (hα : α ^ 3 = 1) : α ∈ H := by
  have h1 : orderOf (QuotientGroup.mk α : M ⧸ H) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one])
  have h2 : orderOf (QuotientGroup.mk α : M ⧸ H) ∣ Nat.card (M ⧸ H) := orderOf_dvd_natCard _
  rw [← Subgroup.index_eq_card] at h2
  have h3 := Nat.dvd_gcd h1 (h2.trans hidx)
  have h4 : orderOf (QuotientGroup.mk α : M ⧸ H) = 1 := by
    have : Nat.gcd 3 2 = 1 := by norm_num
    rw [this] at h3
    exact Nat.dvd_one.1 h3
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h4)

section Extraspecial

variable {Q : Type*} [Group Q] [Finite Q]

theorem c25_index_centralizer_le (hZ : Nat.card (Subgroup.center Q) = 3)
    (hcomm : ∀ a b : Q, ⁅a, b⁆ ∈ Subgroup.center Q) (g : Q) :
    (Subgroup.centralizer ({g} : Set Q)).index ≤ 3 := by
  let φ : Q →* ↥(Subgroup.center Q) :=
    { toFun := fun x => ⟨⁅x, g⁆, hcomm x g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have h1 : ⁅x * y, g⁆ = x * ⁅y, g⁆ * x⁻¹ * ⁅x, g⁆ := by
          simp only [commutatorElement_def]
          group
        have h2 := Subgroup.mem_center_iff.1 (hcomm y g) x
        have h3 := Subgroup.mem_center_iff.1 (hcomm x g) ⁅y, g⁆
        have h4 : x * ⁅y, g⁆ * x⁻¹ = ⁅y, g⁆ := by rw [h2]; group
        show ⁅x * y, g⁆ = ⁅x, g⁆ * ⁅y, g⁆
        rw [h1, h4]
        exact h3 }
  have hker : φ.ker = Subgroup.centralizer ({g} : Set Q) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h h' hh'
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      have := congrArg Subtype.val h
      exact (commutatorElement_eq_one_iff_commute.1 this).symm
    · intro h
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_commute.2 (h g rfl).symm
  rw [← hker, Subgroup.index_ker]
  exact (Subgroup.card_le_card_group φ.range).trans hZ.le

theorem c25_exists_centralizer_notin (hQ : IsThreeOnePlusFour Q) (P : Subgroup Q)
    (hP : Nat.card P = 27) (hnc : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) :
    ∃ e : Q, (∀ p ∈ P, p * e = e * p) ∧ e ∉ P := by
  obtain ⟨hcard, -, hZ, hcomm⟩ := hQ
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T : Subgroup Q := Subgroup.closure ({a, b} : Set Q) with hT
  have hTP : T ≤ P := by
    rw [hT, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hb
  have haT : a ∈ T := Subgroup.subset_closure (by simp)
  have hbT : b ∈ T := Subgroup.subset_closure (by simp)
  have hTcard : Nat.card T = 27 := by
    by_contra hne
    have hdvd : Nat.card T ∣ 3 ^ 3 := by
      have := Subgroup.card_dvd_of_le hTP
      rwa [hP] at this
    obtain ⟨i, hi, hTi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hi3 : i ≠ 3 := by
      rintro rfl
      exact hne (by rw [hTi]; norm_num)
    have hcommT : ∀ x y : T, x * y = y * x := by
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · have : IsCyclic T := isCyclic_of_card_dvd_prime (p := 3) (by rw [hTi]; norm_num)
        exact fun x y => IsMulCommutative.is_comm.comm x y
      · have : IsCyclic T := isCyclic_of_card_dvd_prime (p := 3) (by rw [hTi]; norm_num)
        exact fun x y => IsMulCommutative.is_comm.comm x y
      · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := T) (by rw [hTi])
        exact fun x y => IsMulCommutative.is_comm.comm x y
    exact hab (congrArg Subtype.val (hcommT ⟨a, haT⟩ ⟨b, hbT⟩))
  have hTeq : T = P := Subgroup.eq_of_le_of_card_ge hTP (by rw [hTcard, hP])
  set D : Subgroup Q := Subgroup.centralizer ({a} : Set Q) ⊓ Subgroup.centralizer ({b} : Set Q)
    with hD
  have hDC : D ≤ Subgroup.centralizer (P : Set Q) := by
    rw [← hTeq, hT, Subgroup.centralizer_closure]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | hh
    · exact Subgroup.mem_centralizer_iff.1 hx.1 _ rfl
    · rw [Set.mem_singleton_iff] at hh
      subst hh
      exact Subgroup.mem_centralizer_iff.1 hx.2 _ rfl
  have hidx : D.index ≤ 9 := by
    refine Subgroup.index_inf_le.trans ?_
    exact Nat.mul_le_mul (c25_index_centralizer_le hZ hcomm a) (c25_index_centralizer_le hZ hcomm b)
  have hDcard : 27 ≤ Nat.card D := by
    have h1 := Subgroup.card_mul_index D
    rw [hcard] at h1
    by_contra hlt
    push Not at hlt
    have := Nat.mul_le_mul (Nat.le_of_lt_succ hlt) hidx
    omega
  have hCcard : 27 ≤ Nat.card (Subgroup.centralizer (P : Set Q)) :=
    hDcard.trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hDC))
  by_contra hall
  push Not at hall
  have hle : Subgroup.centralizer (P : Set Q) ≤ P := fun x hx =>
    hall x (fun p hp => Subgroup.mem_centralizer_iff.1 hx p hp)
  have heq : Subgroup.centralizer (P : Set Q) = P :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hP]; exact hCcard)
  have haC : a ∈ Subgroup.centralizer (P : Set Q) := by rw [heq]; exact ha
  exact hab (Subgroup.mem_centralizer_iff.1 haC b hb).symm

end Extraspecial

end CFSG.HardMathSupport.Solomon.Coordinator
