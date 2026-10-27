module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.Order5616Profile

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.GL2ThreeCharacters

section GL2

theorem orderOf_V_GL2 : orderOf GL2ThreeStructure.V = 3 := by
  apply orderOf_eq_prime
  · apply Units.ext
    change GL2ThreeStructure.matrixV ^ 3 = 1
    decide
  · intro h
    have hM : GL2ThreeStructure.matrixV = 1 := congrArg Units.val h
    have hn : GL2ThreeStructure.matrixV ≠ 1 := by decide
    exact hn hM

theorem C_not_mem_K : FourPointMatrices.C ∉ GL2ThreeStructure.K := by
  intro h
  change Matrix.GeneralLinearGroup.det FourPointMatrices.C = 1 at h
  have h' := congrArg Units.val h
  change FourPointMatrices.matrixC.det = 1 at h'
  revert h'
  decide

theorem mem_of_orderOf_eq_three_of_involutions_mem (S : Subgroup G23)
    (hS : ∀ g : G23, orderOf g = 2 → g ∈ S) {a : G23} (ha : orderOf a = 3) : a ∈ S := by
  obtain ⟨b, hb, -, hba, -⟩ := GL2ThreeStructure.order_three_inverting_involution a ha
  have hb2 : b * b = 1 := by
    have h := pow_orderOf_eq_one b
    rw [hb, sq] at h
    exact h
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hba2 : orderOf (b * a) = 2 := by
    apply orderOf_eq_prime
    · calc (b * a) ^ 2 = b * a * b⁻¹ * a := by rw [sq, hbinv, ← mul_assoc]
        _ = 1 := by rw [hba, inv_mul_cancel]
    · intro h
      have hab : a = b⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [hab, hbinv, hb] at ha
      norm_num at ha
  have h := S.mul_mem (S.inv_mem (hS b hb)) (hS _ hba2)
  rwa [inv_mul_cancel_left] at h

theorem GL2_eq_top_of_involutions_mem (S : Subgroup G23)
    (hS : ∀ g : G23, orderOf g = 2 → g ∈ S) : S = ⊤ := by
  have hK : GL2ThreeStructure.K ≤ S := by
    rw [← GL2ThreeStructure.unipotents_generate_K, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact mem_of_orderOf_eq_three_of_involutions_mem S hS GL2ThreeStructure.U_order
    · exact mem_of_orderOf_eq_three_of_involutions_mem S hS orderOf_V_GL2
  have hC := hS _ GL2ThreeStructure.C_order
  have hdvd1 := Subgroup.card_dvd_of_le hK
  rw [GL2ThreeStructure.K_card] at hdvd1
  have hdvd2 : Nat.card S ∣ 48 := card_G23 ▸ Subgroup.card_subgroup_dvd_card S
  have h48 : Nat.card S = 48 := by
    obtain ⟨k, hk⟩ := hdvd1
    have hle := Nat.le_of_dvd (by norm_num) hdvd2
    have hpos : 0 < Nat.card S := Nat.card_pos
    rw [hk] at hle hpos
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl
    · exfalso
      have hSK : GL2ThreeStructure.K = S :=
        Subgroup.eq_of_le_of_card_ge hK (by rw [hk, GL2ThreeStructure.K_card])
      exact C_not_mem_K (hSK ▸ hC)
    · rw [hk]
  exact Subgroup.eq_top_of_card_eq S (h48.trans card_G23.symm)

end GL2

section Three

variable {G : Type*} [Group G] {t : G}

theorem card_inf_centralizer_eq {u x : G} (hx : x ∈ Subgroup.centralizer ({u} : Set G)) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({u} : Set G)) =
      Nat.card (Subgroup.centralizer ({(⟨x, hx⟩ : Subgroup.centralizer ({u} : Set G))} :
        Set (Subgroup.centralizer ({u} : Set G)))) := by
  refine Nat.card_congr
    { toFun := fun d => ⟨⟨d, d.2.2⟩, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp d.2.1))⟩
      invFun := fun y => ⟨y.1.1, ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp y.2)), y.1.2⟩⟩
      left_inv := fun d => rfl
      right_inv := fun y => rfl }

variable [Finite G]

theorem not_four_dvd_card_centralizer_of_orderOf_eq_three
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) {x : G} (hx : orderOf x = 3) :
    ¬ 4 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  intro h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := Subgroup.centralizer ({x} : Set G)) 2 (n := 2) (by norm_num; exact h4)
  have hQcomm : IsMulCommutative Q :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hQ
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by rw [hQ]; norm_num)
  have hu₀ : orderOf (((u : Subgroup.centralizer ({x} : Set G)) : G)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu]
  obtain ⟨ψ⟩ := nonempty_centralizer_involution_mulEquiv hinv ht φ hu₀
  have hxu : x ∈ Subgroup.centralizer
      ({((u : Subgroup.centralizer ({x} : Set G)) : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (u : Subgroup.centralizer ({x} : Set G)).2).symm
  have hQ'card : Nat.card (Q.map (Subgroup.centralizer ({x} : Set G)).subtype) = 4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.centralizer ({x} : Set G)).subtype_injective, hQ]
    norm_num
  have hQ'le : Q.map (Subgroup.centralizer ({x} : Set G)).subtype ≤
      Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({((u : Subgroup.centralizer ({x} : Set G)) : G)} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨q.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg (fun y : Q => ((y : Subgroup.centralizer ({x} : Set G)) : G))
        (hQcomm.is_comm.comm (⟨q, hq⟩ : Q) u))⟩
  have hD := card_inf_centralizer_eq hxu
  rw [card_centralizer_mulEquiv ψ] at hD
  have hψx : orderOf (ψ ⟨x, hxu⟩) = 3 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  rw [(card_centralizer_GL2 _).1 hψx] at hD
  have h := Subgroup.card_dvd_of_le hQ'le
  rw [hQ'card, hD] at h
  norm_num at h

theorem not_thirteen_dvd_card_centralizer_of_orderOf_eq_three
    (hcent : ∀ A : Subgroup G, Nat.card A = 13 → Subgroup.centralizer (A : Set G) = A)
    {x : G} (hx : orderOf x = 3) : ¬ 13 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  intro h13
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({x} : Set G)) 13 h13
  have hy' : orderOf (y : G) = 13 := by rw [Subgroup.orderOf_coe, hy]
  have hxy : x ∈ Subgroup.centralizer ({(y : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
  rw [centralizer_eq_zpowers_of_orderOf_eq_thirteen hcent hy'] at hxy
  have h := Subgroup.orderOf_dvd_natCard _ hxy
  rw [hx, Nat.card_zpowers, hy'] at h
  norm_num at h

theorem card_centralizer_dvd_54_of_orderOf_eq_three (hG : Nat.card G = 5616)
    (hcent : ∀ A : Subgroup G, Nat.card A = 13 → Subgroup.centralizer (A : Set G) = A)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) {x : G} (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 54 := by
  have h4 := not_four_dvd_card_centralizer_of_orderOf_eq_three hinv ht φ hx
  have h13 := not_thirteen_dvd_card_centralizer_of_orderOf_eq_three hcent hx
  have hdvd : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 13 * 432 := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({x} : Set G))
    rw [hG] at h
    exact h
  have hcop : Nat.Coprime (Nat.card (Subgroup.centralizer ({x} : Set G))) 13 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h13).symm
  have h432 := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
  have key : ∀ c ∈ Nat.divisors 432, ¬ 4 ∣ c → c ∣ 54 := by decide
  exact key _ (Nat.mem_divisors.mpr ⟨h432, by norm_num⟩) h4

end Three

section Simplicity

variable {G : Type*} [Group G] [Finite G] {t : G}

theorem eq_bot_of_normal_of_odd_card (hG : Nat.card G = 5616) (hperf : commutator G = ⊤)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (φ : Subgroup.centralizer ({t} : Set G) ≃* G23) (R : Subgroup G) (hRn : R.Normal)
    (hodd : Odd (Nat.card R)) : R = ⊥ := by
  have := Fintype.ofFinite G
  obtain ⟨h13, -, -, -, hsize13, -⟩ := order5616_classes hG hperf hinv ht φ
  have hcent : ∀ A : Subgroup G, Nat.card A = 13 → Subgroup.centralizer (A : Set G) = A :=
    fun A hA => (h13 A hA).1
  have hdvd : Nat.card R ∣ 16 * 351 := by
    have h := Subgroup.card_subgroup_dvd_card R
    rw [hG] at h
    exact h
  have hcop : Nat.Coprime (Nat.card R) 16 := by
    have h := Nat.Coprime.pow_right 4 (Nat.coprime_two_right.mpr hodd)
    rwa [show (2 : ℕ) ^ 4 = 16 by norm_num] at h
  have h351 := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
  have hclass : ∀ x ∈ R, Nat.card (ConjClasses.mk x).carrier ≤ Nat.card R := by
    intro x hx
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1, ?_⟩) ?_
    · obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp
        (ConjClasses.mem_carrier_iff_mk_eq.mp y.2)).symm
      rw [← hc]
      exact hRn.conj_mem x hx c
    · intro y y' h
      apply Subtype.ext
      simpa using congrArg Subtype.val h
  by_contra hne
  by_cases h13d : 13 ∣ Nat.card R
  · have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 13 h13d
    have hsz := hsize13 (x : G) (by rw [Subgroup.orderOf_coe, hx])
    have hle := hclass x x.2
    have := Nat.le_of_dvd (by norm_num) h351
    omega
  · have hcop13 : Nat.Coprime (Nat.card R) 13 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h13d).symm
    have h27 : Nat.card R ∣ 27 := Nat.Coprime.dvd_of_dvd_mul_left hcop13 (by simpa using h351)
    have h1 : Nat.card R ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
    have h3 : 3 ∣ Nat.card R := by
      have key : ∀ m ∈ Nat.divisors 27, m ≠ 1 → 3 ∣ m := by decide
      exact key _ (Nat.mem_divisors.mpr ⟨h27, by norm_num⟩) h1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 3 h3
    have hx' : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
    have h54 := Nat.le_of_dvd (by norm_num)
      (card_centralizer_dvd_54_of_orderOf_eq_three hG hcent hinv ht φ hx')
    have hcl := CFSG.LyonsUnitaryFour.card_conjClass_mul_card_centralizer (x : G)
    rw [hG] at hcl
    have hle := hclass x x.2
    have hR27 := Nat.le_of_dvd (by norm_num) h27
    have := Nat.mul_le_mul (hle.trans hR27) h54
    omega

theorem perfect_order5616_GL2_centralizer_simplicity (hG : Nat.card G = 5616)
    (hperf : commutator G = ⊤)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer {t} ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :
    IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧
      ∀ R : Subgroup G, R.Normal → Odd (Nat.card R) → R = ⊥ := by
  obtain ⟨φ⟩ := hC
  have hoddR : ∀ R : Subgroup G, R.Normal → Odd (Nat.card R) → R = ⊥ :=
    fun R hRn hodd => eq_bot_of_normal_of_odd_card hG hperf hinv ht φ R hRn hodd
  obtain ⟨-, -, -, -, -, -, -, -, -, hN2, hN4, hN6, hN8, -, -⟩ :=
    order5616_classes hG hperf hinv ht φ
  have hnt : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by rw [hG]; norm_num)
  have hnc : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    have hall : ∀ a b : G, a * b = b * a := fun a b => by
      by_contra h
      exact hcon ⟨a, b, h⟩
    have htop : Subgroup.centralizer ({t} : Set G) = ⊤ :=
      eq_top_iff.mpr fun a _ => Subgroup.mem_centralizer_singleton_iff.mpr (hall a t)
    have h := card_centralizer_involution hinv ht φ ht
    rw [htop, Subgroup.card_top, hG] at h
    norm_num at h
  refine ⟨{ eq_bot_or_eq_top_of_normal := fun R hRn => ?_ }, hnc, hoddR⟩
  by_cases hR : R = ⊥
  · exact Or.inl hR
  right
  have heven : 2 ∣ Nat.card R := by
    by_contra h
    exact hR (hoddR R hRn (Nat.odd_iff.mpr (by omega)))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 heven
  have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have hinvR : ∀ v : G, orderOf v = 2 → v ∈ R := by
    intro v hv
    obtain ⟨c, hc⟩ := isConj_iff.mp (hinv (u : G) v hu' hv)
    rw [← hc]
    exact hRn.conj_mem _ u.2 c
  have hS := GL2_eq_top_of_involutions_mem
    ((R.comap (Subgroup.centralizer ({t} : Set G)).subtype).comap φ.symm.toMonoidHom)
    fun g hg => hinvR ((φ.symm g : Subgroup.centralizer ({t} : Set G)) : G)
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hg])
  have hCR : ∀ c : Subgroup.centralizer ({t} : Set G), (c : G) ∈ R := by
    intro c
    have h : φ c ∈ (R.comap (Subgroup.centralizer ({t} : Set G)).subtype).comap
        φ.symm.toMonoidHom := by
      rw [hS]
      exact Subgroup.mem_top _
    simpa [Subgroup.mem_subgroupOf] using h
  have hevR : ∀ g : G, Even (orderOf g) → g ∈ R := by
    intro g hg
    obtain ⟨c, hc⟩ := exists_conj_pow_half_eq hinv ht hg
    have h := hRn.conj_mem _ (hCR ⟨_, mem_centralizer_of_pow_eq hc⟩) c⁻¹
    simpa [mul_assoc] using h
  have hcount : Nat.card {g : G // orderOf g ∈ ({1, 2, 4, 6, 8} : Finset ℕ)} = 3160 := by
    rw [card_orderOf_mem_eq_sum]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton, hN2, hN4, hN6, hN8]
    have hN1 : Nat.card {g : G // orderOf g = 1} = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      exact ⟨⟨1, orderOf_one⟩, fun g => Subtype.ext (orderOf_eq_one_iff.mp g.2)⟩
    rw [hN1]
    norm_num
  have hle : 3160 ≤ Nat.card R := by
    rw [← hcount]
    refine Nat.card_le_card_of_injective (fun g => ⟨g.1, ?_⟩) ?_
    · have h := g.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h | h | h
      · rw [orderOf_eq_one_iff.mp h]
        exact R.one_mem
      all_goals exact hevR _ (by rw [h]; decide)
    · intro g g' h
      apply Subtype.ext
      simpa using congrArg Subtype.val h
  have hdvd : Nat.card R ∣ 5616 := hG ▸ Subgroup.card_subgroup_dvd_card R
  obtain ⟨k, hk⟩ := hdvd
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> omega
    · nlinarith
  rw [hk1, mul_one] at hk
  exact Subgroup.eq_top_of_card_eq R (hk.symm.trans hG.symm)

end Simplicity

end CFSG.Semidihedral.GL2Recognition
