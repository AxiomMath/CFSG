module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Main
public import CFSG.LocalAnalysis.EvenBN.Tits.I21BranchData
public import CFSG.LocalAnalysis.EvenBN.Tits.I21BranchE
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Comp2
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Idx
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Local

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open

section Aux

variable {G : Type*} [Group G] {t u x : G}

theorem dich_crel_pow_nf (h : I21.CRel t u x) (n a i j : ℕ) :
    ∃ m : ℕ, (t ^ a * x ^ i * u ^ j) ^ n = t ^ (n * a) * x ^ m * u ^ (n * j) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + i * 2 ^ (n * j), ?_⟩
    rw [pow_succ, hm, h.nf_mul, show (n + 1) * a = n * a + a by ring,
      show (n + 1) * j = n * j + j by ring]

theorem dich_exists_pow_of_pow_five (h : I21.CRel t u x) {g : G}
    (hg : g ∈ closure ({t, u, x} : Set G)) (h5 : g ^ 5 = 1) : ∃ i : ℕ, g = x ^ i := by
  obtain ⟨a, i, j, rfl⟩ := h.mem_closure_iff.mp hg
  obtain ⟨m, hm⟩ := dich_crel_pow_nf h 5 a i j
  rw [hm, h.nf_eq_one_iff] at h5
  obtain ⟨ha, -, hj⟩ := h5
  refine ⟨i, ?_⟩
  have ha' : t ^ a = 1 := by
    obtain ⟨k, hk⟩ : 2 ∣ a := by omega
    rw [hk, pow_mul, h.t_sq, one_pow]
  have hj' : u ^ j = 1 := by
    obtain ⟨k, hk⟩ : 4 ∣ j := by omega
    rw [hk, pow_mul, h.u_four, one_pow]
  rw [ha', hj', one_mul, mul_one]

theorem dich_eq_one_of_sq_mem (h : I21.CRel t u x) {A : Subgroup G} (hA : A.Normal)
    (hA2 : IsPGroup 2 A) (hz : u ^ 2 ∈ A) : x = 1 := by
  have h1 : u ^ 2 * x = x ^ 4 * u ^ 2 := by simpa using h.pow_u_mul_x_pow 2 1
  have h2 : x ^ 3 * u ^ 2 ∈ A := by
    have h3 : x⁻¹ * (u ^ 2 * x) = x ^ 3 * u ^ 2 := by rw [h1]; group
    rw [← h3, ← mul_assoc]
    exact hA.conj_mem' _ hz x
  have h4 : x ^ 3 ∈ A := by
    have h5 : x ^ 3 = (x ^ 3 * u ^ 2) * (u ^ 2)⁻¹ := by group
    rw [h5]
    exact mul_mem h2 (inv_mem hz)
  have hxA : x ∈ A := by
    have h6 : x = (x ^ 3) ^ 2 := by
      rw [← pow_mul, show 3 * 2 = 5 + 1 by norm_num, pow_add, h.x_five, one_mul, pow_one]
    rw [h6]
    exact pow_mem h4 2
  obtain ⟨k, hk⟩ := hA2 ⟨x, hxA⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  exact (pow_eq_one_iff_of_coprime (a := x) (m := 2 ^ k) (n := 5)
    (Nat.Coprime.pow_left k (by norm_num))).1 ⟨hk', h.x_five⟩

theorem dich_order_five [Finite G] (hc : I21.CRel t u x)
    (hC : centralizer ({t} : Set G) = closure {t, u, x}) {L : Subgroup G}
    (hcard : Nat.card ↥(L ⊓ centralizer ({t} : Set G)) = 10) : x ≠ 1 ∧ x ∈ L := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L ⊓ centralizer ({t} : Set G))) 5
    (by rw [hcard]; norm_num)
  have hgL : (g : G) ∈ L := (mem_inf.mp g.2).1
  have hgC : (g : G) ∈ closure ({t, u, x} : Set G) := by
    rw [← hC]
    exact (mem_inf.mp g.2).2
  have hg5 : orderOf (g : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hg
  obtain ⟨i, hi⟩ := dich_exists_pow_of_pow_five hc hgC (by
    have := pow_orderOf_eq_one (g : G)
    rwa [hg5] at this)
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [one_pow] at hi
    rw [hi, orderOf_one] at hg5
    omega
  refine ⟨hx1, ?_⟩
  have hx5 : orderOf x = 5 := orderOf_eq_prime hc.x_five hx1
  have hcop : Nat.Coprime i (orderOf x) := by
    rw [hx5]
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 ?_)
    rintro ⟨k, rfl⟩
    rw [pow_mul, hc.x_five, one_pow] at hi
    rw [hi, orderOf_one] at hg5
    omega
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, ← hi]
  exact pow_mem hgL m

theorem dich_sq_mem [Finite G] (hc : I21.CRel t u x)
    (hC : centralizer ({t} : Set G) = closure {t, u, x}) {L : Subgroup G} (hL : L.Normal)
    (htL : t ∉ L) (hcard : Nat.card ↥(L ⊓ centralizer ({t} : Set G)) = 10) (hxL : x ∈ L)
    {h : G} (hh : h * t * h⁻¹ = t * u ^ 2) : u ^ 2 ∈ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L ⊓ centralizer ({t} : Set G))) 2
    (by rw [hcard]; norm_num)
  have heL : (e : G) ∈ L := (mem_inf.mp e.2).1
  have heC : (e : G) ∈ closure ({t, u, x} : Set G) := by
    rw [← hC]
    exact (mem_inf.mp e.2).2
  have he2 : orderOf (e : G) = 2 := by rw [Subgroup.orderOf_coe]; exact he
  have he_sq : (e : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (e : G)
    rwa [he2] at this
  have he1 : (e : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at he2
    omega
  rcases hc.eq_of_sq_eq_one heC he_sq he1 with h1 | ⟨i, h1⟩ | ⟨i, h1⟩
  · exact absurd (h1 ▸ heL) htL
  · have h2 : u ^ 2 = (x ^ i)⁻¹ * (e : G) := by rw [h1]; group
    rw [h2]
    exact mul_mem (inv_mem (pow_mem hxL i)) heL
  · have h2 : t * u ^ 2 = (x ^ i)⁻¹ * (e : G) := by
      rw [h1, ← mul_assoc t, hc.t_comm_x_pow i]
      group
    have h3 : t * u ^ 2 ∈ L := by
      rw [h2]
      exact mul_mem (inv_mem (pow_mem hxL i)) heL
    have h4 := hL.conj_mem' _ h3 h
    rw [← hh, show h⁻¹ * (h * t * h⁻¹) * h = t by group] at h4
    exact absurd h4 htL

end Aux

section Dich


theorem sec622_bar_precise {G : Type} [Group G] [Finite G] {t u x : G} (h : Sec622Bar G t u x) :
    Sec622T1 u ∨ ∃ L : Subgroup G, L.Normal ∧ centralizer (L : Set G) = ⊥ ∧ IsPSLTwo L 9 ∧
      t ∉ L ∧ Nat.card ↥(L ⊓ centralizer ({t} : Set G)) = 10 ∧ PGLTwoSquareOuter L t := by
  have hs := h.secTwo
  obtain ⟨S, hRS⟩ := hs.exists_sylow_ge
  by_cases hSR : secTwoR t u = (S : Subgroup G)
  · left
    have h2 : IsPGroup 2 G := h.isPGroup_of_sylow_eq S hSR
    exact ⟨⊤, inferInstance, h2.to_subgroup _, Subgroup.mem_top _⟩
  · by_cases hcon : ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ centralizer (Q : Set G) ≤ Q
    · obtain ⟨Q, hQn, hQ2, hCQ⟩ := hcon
      exact Or.inl (sec622_constrained hs hQn hQ2 hCQ)
    · push Not at hcon
      have hN := h.exists_normal_index_two S hRS hSR
      have hfus := (sec622_two_two_fusion h S.isPGroup' hRS hSR).2
      rcases sec622_three_one h hcon hN hfus with
        hT | ⟨L, hLn, hLs, hnonab, hcent, hzL, -, htL, htzL⟩
      · exact Or.inl hT
      · right
        haveI := hLs
        have htL' : t ∉ L := by simpa using htL 1
        have ht2 : t ^ 2 = 1 := hs.t_sq
        obtain ⟨M, hM, hMt, hMC, hbranch⟩ := sec622_branch_data h hLn htL' hzL htzL
        rcases hbranch with ⟨hE, hcard⟩ | ⟨w, hw, hZ, hcard⟩
        · obtain ⟨-, hL⟩ := sec622_branch_E h hLn hnonab htL' hM hMt hE
          rcases hL with h5 | h7 | h9 | hA7
          · exfalso
            have := sec622_outer_L2_five hLn hcent h5 ht2 htL'
            omega
          · exfalso
            have := sec622_outer_L2_seven hLn hcent h7 ht2 htL'
            omega
          · rcases sec622_outer_L2_nine hLn hcent h9 ht2 htL' with ⟨h10, hPGL⟩ | h24
            · exact ⟨L, hLn, hcent, h9, htL', h10, hPGL⟩
            · exfalso
              omega
          · exfalso
            have := sec622_outer_A7 hLn hcent hA7 ht2 htL'
            omega
        · exfalso
          exact sec622_branch_Z_false h hLn hnonab hcent htL' hM hMt hMC hw hZ hcard

theorem dichotomy {Y : Type} [Group Y] [Finite Y] {t u x h : Y} (hH : SecTwoHyp Y t u)
    (hx : orderOf x = 5) (htx : t * x = x * t) (hux : u * x * u⁻¹ = x ^ 2)
    (hC : centralizer ({t} : Set Y) = closure {t, u, x}) (hh : h * t * h⁻¹ = t * u ^ 2)
    (hcard : Nat.card Y ∣ sec622N)
    (hexp : ∀ g : Y, (∃ k : ℕ, orderOf g = 2 ^ k) → g ^ 8 = 1) :
    x ∈ standardComponentOddCore Y ∨
      (x ∉ standardComponentOddCore Y ∧
        ∃ L : Subgroup (Y ⧸ standardComponentOddCore Y), L.Normal ∧
          centralizer (L : Set (Y ⧸ standardComponentOddCore Y)) = ⊥ ∧ IsPSLTwo L 9 ∧
          (QuotientGroup.mk t : Y ⧸ standardComponentOddCore Y) ∉ L ∧
          (QuotientGroup.mk x : Y ⧸ standardComponentOddCore Y) ∈ L ∧
          (QuotientGroup.mk (u ^ 2) : Y ⧸ standardComponentOddCore Y) ∈ L ∧
          PGLTwoSquareOuter L (QuotientGroup.mk t : Y ⧸ standardComponentOddCore Y)) := by
  have hbar := sec622_quotient hH hx htx hux hC hcard hexp
  have hcr := hbar.crel
  rcases sec622_bar_precise hbar with ⟨A, hA, hA2, hz⟩ | ⟨L, hLn, hcent, h9, htL, h10, hPGL⟩
  · left
    exact (QuotientGroup.eq_one_iff x).mp (dich_eq_one_of_sq_mem hcr hA hA2 hz)
  · right
    obtain ⟨hx1, hxL⟩ := dich_order_five hcr hbar.cent h10
    have hhbar : (QuotientGroup.mk h : Y ⧸ standardComponentOddCore Y) * QuotientGroup.mk t *
        (QuotientGroup.mk h)⁻¹ = QuotientGroup.mk t * (QuotientGroup.mk u) ^ 2 := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hh,
        QuotientGroup.mk_mul, QuotientGroup.mk_pow]
    have hzL := dich_sq_mem hcr hbar.cent hLn htL h10 hxL hhbar
    refine ⟨fun hxO => hx1 ((QuotientGroup.eq_one_iff x).mpr hxO), L, hLn, hcent, h9, htL, hxL, ?_,
      hPGL⟩
    rw [QuotientGroup.mk_pow]
    exact hzL

end Dich

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
