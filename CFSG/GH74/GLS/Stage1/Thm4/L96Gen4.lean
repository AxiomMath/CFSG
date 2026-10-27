module

public import CFSG.GH74.GLS.Stage1.Thm4.L96Act
public import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

open Subgroup Equiv Equiv.Perm CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.Stage1.Thm4.Alt51
  CFSG.GH74.GLS.Stage1.Thm4.L97
open scoped commutatorElement

@[expose] def emb8' {n : ℕ} (hn : 8 ≤ n) : Fin 8 ≃ {x : Fin n // x.val < 8} where
  toFun i := ⟨⟨i.val, lt_of_lt_of_le i.isLt hn⟩, i.isLt⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def ι8' {n : ℕ} (hn : 8 ≤ n) : Perm (Fin 8) →* Perm (Fin n) :=
  Equiv.Perm.extendDomainHom (emb8' hn)

theorem cycleType_ι8' {n : ℕ} (hn : 8 ≤ n) (σ : Perm (Fin 8)) :
    (ι8' hn σ).cycleType = σ.cycleType :=
  Equiv.Perm.cycleType_extendDomain (emb8' hn)

theorem ι8'_eq_one {n : ℕ} (hn : 8 ≤ n) {σ : Perm (Fin 8)} (h : ι8' hn σ = 1) : σ = 1 := by
  have h1 := cycleType_ι8' hn σ
  rw [h, Equiv.Perm.cycleType_one] at h1
  exact Equiv.Perm.cycleType_eq_zero.1 h1.symm

theorem exists_Q8Q8_of_cover {X : Type} [Group X] {n : ℕ} (hn : 8 ≤ n)
    {π : X →* alternatingGroup (Fin n)} (hπ : TwoCover π) :
    ∃ (zh : X) (a : Fin 4 → X), zh ∈ center X ∧ zh ≠ 1 ∧ zh * zh = 1 ∧
      (∀ y ∈ π.ker, y = 1 ∨ y = zh) ∧ (∀ i, a i * a i = zh) ∧
      (∀ i j, a i * a j = a j * a i ∨ a i * a j = zh * (a j * a i)) ∧
      (∀ c : Fin 4 → Fin 2, c ≠ 0 →
        (List.ofFn fun i => a i ^ (c i : ℕ)).prod ≠ 1 ∧
          (List.ofFn fun i => a i ^ (c i : ℕ)).prod ≠ zh) ∧
      (∀ i, ((π (a i) : alternatingGroup (Fin n)) : Perm (Fin n)) = ι8' hn (q8Perm i)) := by
  classical
  have hn5 : 5 ≤ n := by omega
  obtain ⟨zh, hzc, hz1, hz2, hzk⟩ := hπ.exists_z
  have hzz : zh * zh = 1 := by rw [← sq]; exact hz2
  let σ : Fin 4 → Perm (Fin n) := fun i => ι8' hn (q8Perm i)
  have hσct : ∀ i, (σ i).cycleType = {2, 2} := fun i => by
    show (ι8' hn (q8Perm i)).cycleType = {2, 2}
    rw [cycleType_ι8', q8Perm_ct]
  have hσalt : ∀ i, σ i ∈ alternatingGroup (Fin n) := fun i => mem_alt_of_ct_two_two (hσct i)
  choose a ha using fun i => hπ.surj ⟨σ i, hσalt i⟩
  have hπa : ∀ i, ((π (a i) : alternatingGroup (Fin n)) : Perm (Fin n)) = σ i := fun i => by
    rw [ha i]
  refine ⟨zh, a, hzc, hz1, hzz, hzk, ?_, ?_, ?_, hπa⟩
  · intro i
    obtain ⟨hk, h1⟩ := hπ.sq_mem_ker_ne_one_of_cycleType_two_two hn5 (x := a i)
      (by rw [hπa i]; exact hσct i)
    have : a i ^ 2 = zh := (hzk _ hk).resolve_left h1
    rw [← this, sq]
  · intro i j
    have hcomm : σ i * σ j = σ j * σ i := by
      show ι8' hn (q8Perm i) * ι8' hn (q8Perm j) = ι8' hn (q8Perm j) * ι8' hn (q8Perm i)
      rw [← map_mul, ← map_mul, q8Perm_comm]
    have hmem : a i * a j * (a j * a i)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one, hπa]
      rw [hcomm]
      simp
    rcases hzk _ hmem with h | h
    · left
      exact mul_inv_eq_one.1 h
    · right
      exact mul_inv_eq_iff_eq_mul.1 h
  · intro c hc
    have hprod : ((π (List.ofFn fun i => a i ^ (c i : ℕ)).prod : alternatingGroup (Fin n)) :
        Perm (Fin n)) = ι8' hn (List.ofFn fun i => q8Perm i ^ (c i : ℕ)).prod := by
      have h1 : ((π (List.ofFn fun i => a i ^ (c i : ℕ)).prod : alternatingGroup (Fin n)) :
          Perm (Fin n)) = (List.ofFn fun i => σ i ^ (c i : ℕ)).prod := by
        have := map_list_prod ((alternatingGroup (Fin n)).subtype.comp π)
          (List.ofFn fun i => a i ^ (c i : ℕ))
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, List.map_ofFn, Function.comp_def,
          map_pow, hπa] at this
        exact this
      have h2 : ι8' hn (List.ofFn fun i => q8Perm i ^ (c i : ℕ)).prod =
          (List.ofFn fun i => σ i ^ (c i : ℕ)).prod := by
        have := map_list_prod (ι8' hn) (List.ofFn fun i => q8Perm i ^ (c i : ℕ))
        simp only [List.map_ofFn, Function.comp_def, map_pow] at this
        exact this
      rw [h1, h2]
    have hne : π (List.ofFn fun i => a i ^ (c i : ℕ)).prod ≠ 1 := by
      intro h1
      have h2 : ι8' hn (List.ofFn fun i => q8Perm i ^ (c i : ℕ)).prod = 1 := by
        rw [← hprod, h1]
        rfl
      exact q8Perm_indep c hc (ι8'_eq_one hn h2)
    constructor
    · intro h
      apply hne
      rw [h, map_one]
    · intro h
      apply hne
      rw [h]
      exact MonoidHom.mem_ker.1 (show zh ∈ π.ker from by
        have hk : (π zh : alternatingGroup (Fin n)) = 1 := by
          have hcen : zh ∈ center X := hzc
          have hn4 : 4 ≤ Nat.card (Fin n) := by
            rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
          have hmem : π zh ∈ center (alternatingGroup (Fin n)) := by
            rw [Subgroup.mem_center_iff]
            intro g
            obtain ⟨y, rfl⟩ := hπ.surj g
            rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hcen y)]
          rw [alternatingGroup.center_eq_bot hn4] at hmem
          exact hmem
        exact hk)

theorem commute_ι8'_swap {n : ℕ} (hn : 8 ≤ n) (σ : Perm (Fin 8)) {a b : Fin n} (ha : 8 ≤ a.val)
    (hb : 8 ≤ b.val) : Commute (ι8' hn σ) (swap a b) := by
  have hdis : Disjoint (ι8' hn σ) (swap a b) := by
    intro x
    by_cases hx : x.val < 8
    · right
      apply swap_apply_of_ne_of_ne
      · intro h; rw [h] at hx; omega
      · intro h; rw [h] at hx; omega
    · left
      exact Equiv.Perm.extendDomain_apply_not_subtype σ (emb8' hn) hx
  exact hdis.commute

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}

theorem false_of_outer_swap (hG : CFSG.GH74.Gen4 G) (h : Ctx98 G Lh z t S K) {n : ℕ} (hn : 10 ≤ n)
    (hcov : IsDoubleCoverOfAlt Lh n) (A : Act h n) {u : G} (huC : u ∈ Cz z)
    (huρ : A.ρ ⟨u, huC⟩ = swap (⟨8, by omega⟩ : Fin n) ⟨9, by omega⟩) (hu2 : u * u ∈ zStar K) :
    False := by
  classical
  have hn8 : 8 ≤ n := by omega
  have hcovHat : IsDoubleCoverOfAlt (HatT K) n := isDoubleCoverOfAlt_hat h hcov
  obtain ⟨zh, a, hzhc, hzh1, hzhh, hzk, hasq, hacomm, haind, hπa⟩ :=
    exists_Q8Q8_of_cover hn8 A.cover
  have hcen : ∀ y ∈ center (HatT K), y = 1 ∨ y = zh := fun y hy =>
    hzk y (by rw [A.ker_eq_center hcov]; exact hy)
  have huN : u ∈ normalizer (K : Set G) := h.mem_normalizer huC
  have huK : u ∉ K := by
    intro huK
    have h1 := A.sign_K ⟨u, huK⟩
    have h2 : A.ρ ⟨(⟨u, huK⟩ : ↥K), h.K_le huK⟩ = swap (⟨8, by omega⟩ : Fin n) ⟨9, by omega⟩ := huρ
    rw [h2, Equiv.Perm.sign_swap (by simp [Fin.ext_iff])] at h1
    exact absurd h1 (by decide)
  choose xk hxk using fun i => hatMk_surjective K (a i)
  let xs : Fin 4 → G := fun i => (xk i : G)
  let x : Fin 5 → G := Fin.snoc (α := fun _ => G) xs u
  have hxlast : x (Fin.last 4) = u := by simp only [x, Fin.snoc_last]
  have hxcast : ∀ i : Fin 4, x i.castSucc = (xk i : G) := fun i => by simp [x, xs]
  have hcommu : ∀ j : Fin 4, ⁅(xk j : G), u⁆ ∈ zStar K := by
    intro j
    have hmem : ⁅(xk j : G), u⁆ ∈ K := by
      have e : ⁅(xk j : G), u⁆ = (xk j : G) * (u * (xk j : G)⁻¹ * u⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact K.mul_mem (xk j).2 ((Subgroup.mem_normalizer_iff.1 huN _).1 (K.inv_mem (xk j).2))
    refine (mem_zStar_iff_hat_mem_center (⟨⁅(xk j : G), u⁆, hmem⟩ : ↥K)).2 ?_
    rw [← A.ker_eq_center hcov, MonoidHom.mem_ker]
    have hρ : A.ρ ⟨((⟨⁅(xk j : G), u⁆, hmem⟩ : ↥K) : G),
        h.K_le (⟨⁅(xk j : G), u⁆, hmem⟩ : ↥K).2⟩ = 1 := by
      have e : (⟨((⟨⁅(xk j : G), u⁆, hmem⟩ : ↥K) : G),
          h.K_le (⟨⁅(xk j : G), u⁆, hmem⟩ : ↥K).2⟩ : ↥(Cz z)) =
          ⁅(⟨(xk j : G), h.K_le (xk j).2⟩ : ↥(Cz z)), (⟨u, huC⟩ : ↥(Cz z))⁆ := Subtype.ext rfl
      have hxk' : (QuotientGroup.mk (xk j) : HatT K) = a j := hxk j
      rw [e, map_commutatorElement, A.ρ_K (xk j), hxk', hπa j, huρ]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (commute_ι8'_swap hn8 (q8Perm j) (by simp) (by simp)).eq
    have h3 := A.ρ_K (⟨⁅(xk j : G), u⁆, hmem⟩ : ↥K)
    rw [hρ] at h3
    exact Subtype.ext (by simpa using h3.symm)
  have hnorm : ∀ i, x i ∈ normalizer (zStar K : Set G) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hxlast]; exact mem_normalizer_zStar huN
    · rw [hxcast]; exact mem_normalizer_zStar (Subgroup.le_normalizer (xk j).2)
  have hsq : ∀ i, x i ^ 2 ∈ zStar K := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hxlast, pow_two]; exact hu2
    · rw [hxcast]
      have h1 : (xk j : G) ^ 2 = ((xk j ^ 2 : ↥K) : G) := by simp
      rw [h1, mem_zStar_iff_hat_mem_center, map_pow, hxk, pow_two, hasq]
      exact hzhc
  have hcomm : ∀ i j, ⁅x i, x j⁆ ∈ zStar K := by
    intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [hxlast]; simp [one_mem]
      · rw [hxlast, hxcast]
        have h2 : ⁅u, (xk j' : G)⁆ = ⁅(xk j' : G), u⁆⁻¹ := (commutatorElement_inv _ _).symm
        rw [h2]
        exact (zStar K).inv_mem (hcommu j')
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [hxlast, hxcast]
        exact hcommu i'
      · rw [hxcast, hxcast]
        have h1 : ⁅(xk i' : G), (xk j' : G)⁆ = ((⁅xk i', xk j'⁆ : ↥K) : G) := by
          simp [commutatorElement_def]
        rw [h1, mem_zStar_iff_hat_mem_center]
        have h2 : hatMk K ⁅xk i', xk j'⁆ = ⁅a i', a j'⁆ := by
          rw [map_commutatorElement, hxk, hxk]
        rw [h2]
        exact commutator_mem_center_of hzhc (hacomm i' j')
  have hprod : ∀ c : Fin 5 → Fin 2, (List.ofFn fun i => x i ^ (c i : ℕ)).prod =
      (List.ofFn fun i : Fin 4 => (xk i : G) ^ ((c i.castSucc : Fin 2) : ℕ)).prod *
        u ^ ((c (Fin.last 4) : Fin 2) : ℕ) := by
    intro c
    rw [List.ofFn_succ', List.prod_concat]
    simp only [hxcast, hxlast]
  have hker : ∀ c : Fin 5 → Fin 2, c ≠ 0 →
      (List.ofFn fun i => x i ^ (c i : ℕ)).prod ∉ zStar K := by
    intro c hc hmem
    rw [hprod c] at hmem
    set c' : Fin 4 → Fin 2 := fun i => c i.castSucc with hc'
    let uk : ↥K := (List.ofFn fun i : Fin 4 => xk i ^ ((c' i : Fin 2) : ℕ)).prod
    have huk : (uk : G) =
        (List.ofFn fun i : Fin 4 => (xk i : G) ^ ((c' i : Fin 2) : ℕ)).prod := by
      have h := map_list_prod K.subtype (List.ofFn fun i : Fin 4 => xk i ^ ((c' i : Fin 2) : ℕ))
      rw [List.map_ofFn] at h
      have e : (K.subtype ∘ fun i : Fin 4 => xk i ^ ((c' i : Fin 2) : ℕ)) =
          fun i => (xk i : G) ^ ((c' i : Fin 2) : ℕ) := by
        funext i
        simp only [Function.comp_apply, map_pow]
        rfl
      rw [e] at h
      exact h
    have hukhat : hatMk K uk = (List.ofFn fun i : Fin 4 => a i ^ ((c' i : Fin 2) : ℕ)).prod := by
      have h := map_list_prod (hatMk K) (List.ofFn fun i : Fin 4 => xk i ^ ((c' i : Fin 2) : ℕ))
      rw [List.map_ofFn] at h
      have e : (hatMk K ∘ fun i : Fin 4 => xk i ^ ((c' i : Fin 2) : ℕ)) =
          fun i => a i ^ ((c' i : Fin 2) : ℕ) := by
        funext i
        simp only [Function.comp_apply, map_pow, hxk]
      rw [e] at h
      exact h
    rw [← huk] at hmem
    by_cases h0 : (c (Fin.last 4) : Fin 2) = 0
    · have hc'0 : c' ≠ 0 := by
        intro h
        apply hc
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact h0
        · exact congrFun h j
      rw [h0] at hmem
      simp only [Fin.val_zero, pow_zero, mul_one] at hmem
      have hcent := (mem_zStar_iff_hat_mem_center uk).1 hmem
      rw [hukhat] at hcent
      rcases hcen _ hcent with h | h
      · exact (haind c' hc'0).1 h
      · exact (haind c' hc'0).2 h
    · have h1 : (c (Fin.last 4) : Fin 2) = 1 := by
        have hlt := (c (Fin.last 4)).isLt
        rw [Fin.ext_iff] at h0 ⊢
        simp only [Fin.val_zero, Fin.val_one] at h0 ⊢
        omega
      rw [h1] at hmem
      simp only [Fin.val_one, pow_one] at hmem
      apply huK
      have := K.mul_mem (K.inv_mem uk.2) hmem.1
      simpa using this
  have hcert := Generic.rankCertified_of_section_involutions (zStar K) x hnorm hsq hcomm hker
    (s := 4) (by norm_num)
  exact hcert.not_gen4 le_rfl hG

theorem sign_eq_one_of_ten_eleven (hG : CFSG.GH74.Gen4 G) (h : Ctx98 G Lh z t S K) {n : ℕ}
    (hn : 10 ≤ n) (hcov : IsDoubleCoverOfAlt Lh n) (A : Act h n) (c : ↥(Cz z)) :
    Equiv.Perm.sign (A.ρ c) = 1 := by
  by_contra hc
  have hcm1 : Equiv.Perm.sign (A.ρ c) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (A.ρ c)) with h1 | h1
    · exact absurd h1 hc
    · exact h1
  set a : Fin n := ⟨8, by omega⟩ with ha
  set b : Fin n := ⟨9, by omega⟩ with hb
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hs : Equiv.Perm.sign (swap a b * (A.ρ c)⁻¹) = 1 := by
    rw [map_mul, map_inv, hcm1, Equiv.Perm.sign_swap hab]
    decide
  obtain ⟨k, hk⟩ := A.exists_K _ hs
  set c₁ : ↥(Cz z) := ⟨(k : G), h.K_le k.2⟩ * c with hc₁
  have hc₁ρ : A.ρ c₁ = swap a b := by
    rw [hc₁, map_mul, hk]
    group
  obtain ⟨e, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd
    (n := orderOf c₁) (orderOf_pos c₁).ne'
  set u : ↥(Cz z) := c₁ ^ m with hu
  have hu2 : u ^ (2 ^ e) = 1 := by
    rw [hu, ← pow_mul, mul_comm, ← hord]
    exact pow_orderOf_eq_one c₁
  have hswsq : swap a b * swap a b = 1 := swap_mul_self a b
  have huρ : A.ρ u = swap a b := by
    rw [hu, map_pow]
    obtain ⟨j, rfl⟩ := hm
    have hswpow : swap a b ^ 2 = 1 := by rw [sq]; exact hswsq
    rw [hc₁ρ, pow_succ, pow_mul, hswpow, one_pow, one_mul]
  have hu2G : ((u * u : ↥(Cz z)) : G) ^ (2 ^ e) = 1 := by
    have : (u * u) ^ (2 ^ e) = 1 := by
      rw [← sq, ← pow_mul, mul_comm, pow_mul, hu2, one_pow]
    simpa using congrArg Subtype.val this
  have huu : A.ρ (u * u) = 1 := by rw [map_mul, huρ, hswsq]
  have hzmem : ((u * u : ↥(Cz z)) : G) ∈ zStar K :=
    (Subgroup.zpowers_le).2 (z_mem_zStar h.K_le h.z_mem) (A.mem_zpowers_of_ker huu hu2G)
  exact false_of_outer_swap hG h hn hcov A (u := (u : G)) u.2 huρ hzmem

end CFSG.GH74.GLS.Stage1.Thm4.L96
