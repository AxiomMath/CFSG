module

public import CFSG.ClassicalInvolution.Q3.Q3T6XSw
public import CFSG.ClassicalInvolution.Q3.Q3T6BTrivEx
public import CFSG.ClassicalInvolution.Q3.Q3T6BSym

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Uniform.U4
  CFSG.ClassicalInvolution.Q3.Q3T6B
open scoped commutatorElement MatrixGroups

section Abs

variable {X : Type} [Group X] [Finite X]

theorem bal368_abs {K J : Subgroup X} {z t : X} (hJ : Mem3 J t) (htex : ExAt t)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzJ : z ∈ Subgroup.normalizer (J : Set X))
    (hnt : ¬ ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J)
    (htK : ∀ k ∈ K, k * t = t * k) (hzK : ∀ k ∈ K, k * z = z * k)
    (hKgen : K ≤ Subgroup.closure {g : X | g ∈ K ∧ Odd (orderOf g)})
    (hsub : IsSubnormal K (Subgroup.centralizer ({z} : Set X))) (hzKmem : z ∈ K)
    (hK2 : ∀ c ∈ K, IsPGroup 2 (Subgroup.zpowers c) → c * c = 1 ∨ c * c = z)
    (hK1 : ∀ c ∈ K, c * c = 1 → c = 1 ∨ c = z) : False := by
  classical
  have hOJ : oddCoreOf J = ⊥ := Mem3.oddCoreOf_eq_bot hJ htex
  have hnt' : ∃ j ∈ J, z * j ≠ j * z := by
    by_contra hcon
    push Not at hcon
    apply hnt
    intro j hj
    rw [hOJ, Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcon j hj)
  set P : Subgroup X := twinProd K J with hP
  set A : Subgroup X := P ⊓ Subgroup.centralizer ({z} : Set X) with hA
  have hA2 : IsPGroup 2 A := isPGroup_twinProd_centralizer hJ htK htex hz2 hzJ hzK hnt'
  have hKA : K ≤ Subgroup.normalizer (A : Set X) := le_normalizer_twinProd_inf_centralizer hzK
  have hAC : A ≤ Subgroup.centralizer ({z} : Set X) := inf_le_right
  have hKC : K ≤ Subgroup.centralizer ({z} : Set X) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzK k hk)
  have hsub' : IsSubnormal K (K ⊔ A) :=
    isSubnormal_of_le_of_le hsub (sup_le hKC hAC) le_sup_left
  have hM : ∀ m ∈ K ⊔ A, ∃ k ∈ K, ∃ a ∈ A, m = k * a := by
    intro m hm
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K A hKA] at hm
    obtain ⟨k, hk, a, ha, hka⟩ := hm
    exact ⟨k, hk, a, ha, hka.symm⟩
  have hAN : A ≤ Subgroup.normalizer (K : Set X) :=
    subnormal_odd_normalizer hKgen hA2 hsub' le_sup_right hM
  obtain ⟨e⟩ := Q3T6.nonempty_equiv_of_memberU hJ.member
  have hρz : Q3T6.normalizerToAutSL3 e ⟨z, hzJ⟩ ≠ 1 := by
    intro h1
    exact hnt ((Q3T6.normalizerToAutSL3_eq_one_iff e ⟨z, hzJ⟩).mp h1)
  have hcomm : ∀ g' ∈ K, Odd (orderOf g') → ∀ a ∈ A, g' * a = a * g' := by
    intro g' hg' hg'odd a ha
    have hgz : g' * z = z * g' := hzK g' hg'
    obtain ⟨c, hc⟩ : ∃ c : X, c = g' * a * g'⁻¹ * a⁻¹ := ⟨_, rfl⟩
    have hcK : c ∈ K := by
      have h1 : a * g'⁻¹ * a⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hAN ha) g'⁻¹).mp (K.inv_mem hg')
      have : c = g' * (a * g'⁻¹ * a⁻¹) := by rw [hc]; group
      rw [this]
      exact K.mul_mem hg' h1
    have hcA : c ∈ A := by
      have h1 : g' * a * g'⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hKA hg') a).mp ha
      rw [hc]
      exact A.mul_mem h1 (A.inv_mem ha)
    have hc2 : IsPGroup 2 (Subgroup.zpowers c) := hA2.to_le (Subgroup.zpowers_le.mpr hcA)
    have hga : g' * a * g'⁻¹ = c * a := by rw [hc]; group
    have hconj : g' * a * g'⁻¹ = a ∨ g' * a * g'⁻¹ = z * a := by
      rcases hK2 c hcK hc2 with h | h
      · rcases hK1 c hcK h with h' | h'
        · left
          rw [hga, h', one_mul]
        · right
          rw [hga, h']
      · exfalso
        have hc4 : c ^ 4 = 1 := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, h, hz2]
        obtain ⟨hcN, hcin⟩ := twinProd_act_mem_inn3 hJ htK htex e hcA.1
        have hsq : (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) ^ 2 =
            Q3T6.normalizerToAutSL3 e ⟨z, hzJ⟩ := by
          rw [← map_pow]
          congr 1
          exact Subtype.ext (by simpa [pow_two] using h)
        have hord4 : (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) ^ 4 = 1 := by
          rw [← map_pow]
          have : (⟨c, hcN⟩ : Subgroup.normalizer (J : Set X)) ^ 4 = 1 := Subtype.ext hc4
          rw [this, map_one]
        have hdvd : orderOf (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) ∣ 4 :=
          orderOf_dvd_of_pow_eq_one hord4
        have hne2 : ¬ orderOf (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) ∣ 2 := by
          intro h2
          have := orderOf_dvd_iff_pow_eq_one.mp h2
          rw [hsq] at this
          exact hρz this
        have h4 : orderOf (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) = 4 := by
          generalize orderOf (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) = d at hdvd hne2
          have hle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
          interval_cases d <;> omega
        exact Q3T6.orderOf_ne_four_of_mem_inn3 hcin h4
    exact comm_of_conj_eq_one_or_mul hgz hz2 hz1 hg'odd hconj
  obtain ⟨ρ, hρ⟩ := exists_action hJ
  have hρz' : ρ ⟨z, hzJ⟩ ≠ 1 := fun h1 => hnt ((hρ ⟨z, hzJ⟩).mp h1)
  have hS : ∀ g ∈ {g : X | g ∈ K ∧ Odd (orderOf g)},
      ∃ hg : g ∈ Subgroup.normalizer (J : Set X), ρ ⟨g, hg⟩ = 1 := by
    rintro g ⟨hgK, hodd⟩
    have hgN : g ∈ Subgroup.normalizer (J : Set X) :=
      odd_mem_normalizer_of_centralizes hJ htex hz2 hzJ hnt htK hzK hcomm hgK hodd
    exact ⟨hgN, act_trivial_of_odd ρ hzJ hz2 hρz' hgN (hzK g hgK) hodd⟩
  obtain ⟨_, hz1'⟩ := closure_act_trivial ρ hS z (hKgen hzKmem)
  exact hρz' hz1'

end Abs


section Lift

variable {F : Type} [Group F] [Finite F]

theorem comm_mem_oddCoreOf_Cz_of_piz {z a b : F} (ha : a ∈ Cz z) (hb : b ∈ Cz z)
    (h : piz z ⟨a, ha⟩ * piz z ⟨b, hb⟩ = piz z ⟨b, hb⟩ * piz z ⟨a, ha⟩) :
    ⁅a, b⁆ ∈ oddCoreOf (Cz z) := by
  have hc : ⁅a, b⁆ ∈ Cz z := by
    rw [commutatorElement_def]
    exact (Cz z).mul_mem ((Cz z).mul_mem ((Cz z).mul_mem ha hb) ((Cz z).inv_mem ha))
      ((Cz z).inv_mem hb)
  refine (mem_oddCoreOf_Cz_iff z).mpr ⟨hc, ?_⟩
  have e : (⟨⁅a, b⁆, hc⟩ : ↥(Cz z)) = ⁅(⟨a, ha⟩ : ↥(Cz z)), ⟨b, hb⟩⁆ := rfl
  rw [e, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr h

theorem comm_mem_oddCoreOf_of_imgz {J : Subgroup F} {t : F} (hJ : Mem3 J t) {a b : F}
    (ha : a ∈ Cz t) (hb : b ∈ J)
    (h : ⁅piz t ⟨a, ha⟩, piz t ⟨b, hJ.le_centralizer hb⟩⁆ ∈ oddCoreOf (imgz t J)) :
    ⁅a, b⁆ ∈ oddCoreOf J := by
  have hOJ : oddCoreOf (imgz t J) = ⊥ := Mem3.oddCoreOf_eq_bot (Mem3.imgz hJ) (exAt_zb t)
  rw [hOJ, Subgroup.mem_bot] at h
  have h1 := comm_mem_oddCoreOf_Cz_of_piz ha (hJ.le_centralizer hb)
    (commutatorElement_eq_one_iff_mul_comm.mp h)
  have h2 : oddCoreOf J = oddCoreOf (Cz t) :=
    Uniform.oddCoreIn_eq_of_intrinsic hJ.member (hJ.intrinsic solvableType_three)
  rw [h2]
  exact h1

end Lift


section Elem

variable {F : Type} [Group F] [Finite F]

theorem imgz_Kf_le_closure (r : F) (I : Subgroup F) :
    imgz r (Kf r I) ≤ Subgroup.closure {g : Qz r | g ∈ imgz r (Kf r I) ∧ Odd (orderOf g)} := by
  have key : ∀ (κ : F) (hκ : κ ∈ Kf r I), ∃ hC : κ ∈ Cz r,
      piz r ⟨κ, hC⟩ ∈ Subgroup.closure {g : Qz r | g ∈ imgz r (Kf r I) ∧ Odd (orderOf g)} := by
    intro κ hκ
    unfold Kf at hκ
    induction hκ using Subgroup.closure_induction with
    | mem x hx =>
      refine ⟨hx.2.1, Subgroup.subset_closure ⟨piz_mem_imgz hx.2.1 (Subgroup.subset_closure hx),
        ?_⟩⟩
      have h1 : orderOf (piz r ⟨x, hx.2.1⟩) ∣ orderOf (⟨x, hx.2.1⟩ : ↥(Cz r)) :=
        orderOf_map_dvd (piz r) _
      rw [Subgroup.orderOf_mk] at h1
      exact hx.2.2.of_dvd_nat h1
    | one =>
      refine ⟨(Cz r).one_mem, ?_⟩
      have : (⟨1, (Cz r).one_mem⟩ : ↥(Cz r)) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      obtain ⟨hCx, hx'⟩ := ihx
      obtain ⟨hCy, hy'⟩ := ihy
      refine ⟨(Cz r).mul_mem hCx hCy, ?_⟩
      have : piz r ⟨x * y, (Cz r).mul_mem hCx hCy⟩ = piz r ⟨x, hCx⟩ * piz r ⟨y, hCy⟩ := by
        rw [← map_mul]; rfl
      rw [this]
      exact Subgroup.mul_mem _ hx' hy'
    | inv x hx ih =>
      obtain ⟨hCx, hx'⟩ := ih
      refine ⟨(Cz r).inv_mem hCx, ?_⟩
      have : piz r ⟨x⁻¹, (Cz r).inv_mem hCx⟩ = (piz r ⟨x, hCx⟩)⁻¹ := by
        rw [← map_inv]; rfl
      rw [this]
      exact Subgroup.inv_mem _ hx'
  intro x hx
  obtain ⟨κ, hC, hκK, rfl⟩ := (mem_imgz_iff r).mp hx
  obtain ⟨_, h⟩ := key κ hκK
  exact h

theorem imgz_Kf_involution {r u : F} {I : Subgroup F} (hI : Mem3 I u) (hu : u ∈ Cz r)
    {x : Qz r} (hx : x ∈ imgz r (Kf r I)) (hx2 : x * x = 1) :
    x = 1 ∨ x = piz r ⟨u, hu⟩ := by
  obtain ⟨w, hC, hwK, hw2, rfl⟩ := exists_lift_involution_of_mem r hx hx2
  rcases hI.isUniqueInvolution.unique w (Kf_le r I hwK).1 hw2 with h | h
  · left
    subst h
    have : (⟨1, hC⟩ : ↥(Cz r)) = 1 := rfl
    rw [this, map_one]
  · right
    subst h
    rfl

theorem imgz_Kf_two_element {r u : F} {I : Subgroup F} (hI : Mem3 I u) (hu : u ∈ Cz r)
    {c : Qz r} (hc : c ∈ imgz r (Kf r I)) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    c * c = 1 ∨ c * c = piz r ⟨u, hu⟩ := by
  classical
  have hcc := hc
  obtain ⟨w, hC, hwK, rfl⟩ := (mem_imgz_iff r).mp hc
  have hw0 : orderOf w ≠ 0 := (orderOf_pos w).ne'
  obtain ⟨a, m, hm, hwn⟩ := Nat.exists_eq_two_pow_mul_odd hw0
  have hd : w ^ m ∈ Kf r I := (Kf r I).pow_mem hwK m
  have hdpow : (w ^ m) ^ (2 ^ a) = 1 := by
    rw [← pow_mul, Nat.mul_comm m, ← hwn, pow_orderOf_eq_one]
  have hd2 : IsPGroup 2 (Subgroup.zpowers (w ^ m)) := by
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hdpow)
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers]; exact hb)
  have hd4 : (w ^ m) ^ 4 = 1 := hI.pow_four_of_isPGroup (Kf_le r I hd).1 hd2
  have hw4 : w ^ (m * 4) = 1 := by rw [pow_mul]; exact hd4
  have hc4 : (piz r ⟨w, hC⟩) ^ (m * 4) = 1 := by
    rw [← map_pow]
    have : (⟨w, hC⟩ : ↥(Cz r)) ^ (m * 4) = 1 := Subtype.ext hw4
    rw [this, map_one]
  obtain ⟨n, hn⟩ := hc2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have hcop : Nat.Coprime (orderOf (piz r ⟨w, hC⟩)) m := by
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hm)
  have h4 : orderOf (piz r ⟨w, hC⟩) ∣ 4 :=
    hcop.dvd_of_dvd_mul_left (orderOf_dvd_of_pow_eq_one hc4)
  have hsq : (piz r ⟨w, hC⟩ * piz r ⟨w, hC⟩) * (piz r ⟨w, hC⟩ * piz r ⟨w, hC⟩) = 1 := by
    have := orderOf_dvd_iff_pow_eq_one.mp h4
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two] at this
    exact this
  exact imgz_Kf_involution hI hu ((imgz r (Kf r I)).mul_mem hcc hcc) hsq

end Elem


section Main

theorem bal368_all (F : Type) [Group F] [Finite F] : Q3T6B.Bal368 F := by
  classical
  intro K J z t hK hJ _ _ htriv hzJ
  by_contra hnt
  have hz2 : z * z = 1 := hK.mul_self
  have ht2 : t * t = 1 := hJ.mul_self
  have hzord : orderOf z = 2 := hK.orderOf_eq_two
  have hzt : z * t = t * z := by
    have h1 : z * t * z⁻¹ = t := hJ.isUniqueInvolution.conj_eq (conjSub_eq_of_mem_normalizer hzJ)
    calc z * t = (z * t * z⁻¹) * z := by group
      _ = t * z := by rw [h1]
  have hz : z ∈ Cz t := Subgroup.mem_centralizer_singleton_iff.mpr hzt
  have hJt : J ≤ Cz t := hJ.le_centralizer
  have hOJ : oddCoreOf (Cz t) ≤ J := hJ.intrinsic solvableType_three
  have hzKf : z ∈ Kf t K := u_mem_Kf hK ht2 hzt htriv
  have hzb2 : piz t ⟨z, hz⟩ * piz t ⟨z, hz⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hz⟩ * ⟨z, hz⟩ : ↥(Cz t)) = 1 := Subtype.ext hz2
    rw [this, map_one]
  refine bal368_abs (X := Qz t) (K := imgz t (Kf t K)) (J := imgz t J) (z := piz t ⟨z, hz⟩)
    (t := zb t) (Mem3.imgz hJ) (exAt_zb t) hzb2 (piz_ne_one_of_orderOf_eq_two t hz hzord)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact AscHypOmega.mem_normalizer_of_conjSub_eq
      ((conjSub_eq_iff_imgz t hJt hOJ ⟨z, hz⟩).mp (conjSub_eq_of_mem_normalizer hzJ))
  · intro h
    apply hnt
    intro j hj
    exact comm_mem_oddCoreOf_of_imgz hJ hz hj (h _ (piz_mem_imgz (hJt hj) hj))
  · intro k _
    have : k ∈ Subgroup.centralizer ({zb t} : Set (Qz t)) := by
      rw [centralizer_zb]
      exact Subgroup.mem_top k
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  · intro k hk
    obtain ⟨a, hC, haK, rfl⟩ := (mem_imgz_iff t).mp hk
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hK.mul_comm_of_mem (Kf_le t K haK).1)
  · exact imgz_Kf_le_closure t K
  · have h := isSubnormal_imgz t (isSubnormal_Kf (r := t) hK)
    rwa [← centralizer_piz t hz hzord] at h
  · exact piz_mem_imgz hz hzKf
  · intro c hc hc2
    exact imgz_Kf_two_element hK hz hc hc2
  · intro c hc hc2
    exact imgz_Kf_involution hK hz hc hc2

end Main

end CFSG.ClassicalInvolution.Q3.Q3T6X
