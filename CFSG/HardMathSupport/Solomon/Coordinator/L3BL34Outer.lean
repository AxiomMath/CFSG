module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BL34Inner

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.RankThree.Asc83Table

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gl23_unip_commute : ∀ M N : GL23, M * N = N * M → M ^ 3 = 1 → M ≠ 1 →
    (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 = 1 → (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 0 →
    (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0 = 1 → (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0 = 0 →
    N ^ 3 = 1 := by
  decide +kernel

theorem apply_eq_of_fix_pair {G : Type*} [Group G] (α : MulAut G) {a b : G} (ha : α a = a)
    (hb : α b = b) : ∀ y ∈ Subgroup.closure ({a, b} : Set G), α y = y := by
  have hle : Subgroup.closure ({a, b} : Set G) ≤
      MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id G) := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact ha
    · exact hb
  intro y hy
  exact hle hy

theorem apply_eq_of_commute_conj {G : Type*} [Group G] (hZ : Function.Injective
    (MulAut.conj : G →* MulAut G)) {x : G} {g : MulAut G}
    (h : g * MulAut.conj x = MulAut.conj x * g) : g x = x := by
  apply hZ
  rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, h]
  group

variable {k : Type} [Field k]

theorem exists_pair_of_pow_three (hk : Nat.card k = 4) {x : projectiveSL 3 k} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) :
    ∃ f : projectiveSL 3 k, f ^ 3 = 1 ∧ x * f = f * x ∧ f ∉ Subgroup.zpowers x := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hzp : IsPGroup 3 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by rw [hz3]; rfl)
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hQ9 : Nat.card (Q : Subgroup (projectiveSL 3 k)) = 9 := by
    rw [Sylow.card_eq_multiplicity, factorization_card hk]
    norm_num
  have hxQ : x ∈ (Q : Subgroup (projectiveSL 3 k)) := hQ (Subgroup.mem_zpowers x)
  have hcent := centralizer_eq_of_card_eq_nine hk hQ9 hxQ hx1
  have hnot : ¬ (Q : Subgroup (projectiveSL 3 k)) ≤ Subgroup.zpowers x := by
    intro h
    have := Subgroup.card_le_of_le h
    omega
  obtain ⟨f, hfQ, hfz⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  refine ⟨f, ?_, ?_, hfz⟩
  · have hel := isElementaryAbelian_of_card_eq_nine hk hQ9
    have h3 := hel.exponent_dvd_p
    obtain ⟨t, ht⟩ := h3
    have := Monoid.pow_exponent_eq_one (⟨f, hfQ⟩ : (Q : Subgroup (projectiveSL 3 k)))
    have h' : (⟨f, hfQ⟩ : (Q : Subgroup (projectiveSL 3 k))) ^ 3 = 1 := by
      have h2 := congrArg (fun z => z ^ t) this
      simp only [one_pow, ← pow_mul] at h2
      rwa [← ht] at h2
    simpa using congrArg Subtype.val h'
  · rw [← hcent, Subgroup.mem_centralizer_singleton_iff] at hfQ
    exact hfQ.symm

theorem not_forall_apply_eq_of_not_mem_range (hk : Nat.card k = 4) [Finite k]
    {F : Subgroup (projectiveSL 3 k)} (hF : Nat.card F = 9) {ε : MulAut (projectiveSL 3 k)}
    (hε3 : ε ^ 3 = 1)
    (hε : ε ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range) :
    ¬ ∀ y ∈ F, ε y = y := by
  intro hfix
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨g, hg⟩ := exists_eq_map_conj_eZero hk hF
  set d : MulAut (projectiveSL 3 k) := MulAut.conj g with hd
  set α : MulAut (projectiveSL 3 k) := d⁻¹ * ε * d with hα
  have hαfix : ∀ y ∈ eZero k, α y = y := by
    intro y hy
    have hdy : d y ∈ F := by
      rw [hg]
      exact ⟨y, hy, rfl⟩
    have h1 := hfix _ hdy
    rw [hα, MulAut.mul_apply, MulAut.mul_apply, h1, MulAut.inv_apply, d.symm_apply_apply]
  have hα3 : α ^ 3 = 1 := by
    have : α ^ 3 = d⁻¹ * ε ^ 3 * d := by
      rw [hα, pow_three, pow_three]
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [this, hε3]
    group
  obtain ⟨e', he', h | h⟩ := (forall_fixes_eZero_iff hk hσ α).1 hαfix
  · apply hε
    refine ⟨g * e' * g⁻¹, ?_⟩
    have hεα : ε = d * α * d⁻¹ := by
      rw [hα]
      group
    rw [hεα, h, hd, ← map_inv, ← map_mul, ← map_mul]
  · have hβ : betaAut (frobeniusEquiv k 2) * MulAut.conj e' *
        (betaAut (frobeniusEquiv k 2))⁻¹ = MulAut.conj e' := by
      rw [CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv,
        betaAut_fixed hk hσ he']
    have hcomm : Commute (MulAut.conj e') (betaAut (frobeniusEquiv k 2)) := by
      show MulAut.conj e' * betaAut (frobeniusEquiv k 2) =
        betaAut (frobeniusEquiv k 2) * MulAut.conj e'
      calc MulAut.conj e' * betaAut (frobeniusEquiv k 2)
          = (betaAut (frobeniusEquiv k 2) * MulAut.conj e' *
              (betaAut (frobeniusEquiv k 2))⁻¹) * betaAut (frobeniusEquiv k 2) := by rw [hβ]
        _ = betaAut (frobeniusEquiv k 2) * MulAut.conj e' := by group
    have hb2 := betaAut_mul_self hk hσ
    have : α ^ 3 = betaAut (frobeniusEquiv k 2) := by
      rw [h, hcomm.mul_pow, ← map_pow, pow_three_of_mem_eZero hk he', map_one, one_mul]
      rw [pow_succ, sq, hb2, one_mul]
    exact betaAut_ne_one hk (σ := frobeniusEquiv k 2) (this.symm.trans hα3)

theorem fix_of_unipotent {G : Type*} [Group G]
    (hZ : Function.Injective (MulAut.conj : G →* MulAut G))
    {x f : G} (hx : x ^ 3 = 1) (hf : f ^ 3 = 1) (hxf : Commute x f) (hx1 : x ≠ 1)
    (hfx : f ∉ Subgroup.zpowers x) {ε s : MulAut G} (hεx : ε x = x) (hsx : s x = x)
    {i j k m : ℕ} (hi : i < 3) (hj : j < 3) (hk : k < 3) (hm : m < 3)
    (hεf : ε f = x ^ i * f ^ j) (hsf : s f = x ^ k * f ^ m)
    (hcomm : s * ε = ε * s) (hε3 : ε ^ 3 = 1) (hεne : ε f ≠ f)
    {n : ℕ} (hn : Nat.Coprime 3 n) (hsn : s ^ n = 1) : s f = f := by
  have hax : (MulAut.conj x : MulAut G) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  have hbf : (MulAut.conj f : MulAut G) ^ 3 = 1 := by rw [← map_pow, hf, map_one]
  have habc : Commute (MulAut.conj x : MulAut G) (MulAut.conj f) := hxf.map _
  have ha1 : (MulAut.conj x : MulAut G) ≠ 1 := fun h => hx1 (hZ (h.trans (map_one _).symm))
  have hnot : (MulAut.conj f : MulAut G) ∉ Subgroup.zpowers (MulAut.conj x : MulAut G) := by
    rintro ⟨t, ht⟩
    apply hfx
    refine ⟨t, hZ ?_⟩
    rw [← ht, map_zpow]
  let E : E9Basis (MulAut G) :=
    ⟨MulAut.conj x, MulAut.conj f, hax, hbf, habc, card_closure_pair_eq_nine hax hbf habc ha1 hnot⟩
  have hconj : ∀ (α : MulAut G) (y : G),
      α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) :=
    CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv
  have hN : ∀ (α : MulAut G) (p q r t : ℕ), α x = x ^ p * f ^ r → α f = x ^ q * f ^ t →
      α ∈ Subgroup.normalizer (Subgroup.closure (Set.range E.vec) : Set (MulAut G)) := by
    intro α p q r t h1 h2
    refine E.mem_normalizer_of_conj p q r t ?_ ?_
    · show α * MulAut.conj x * α⁻¹ = (MulAut.conj x) ^ p * (MulAut.conj f) ^ r
      rw [hconj, h1, map_mul, map_pow, map_pow]
    · show α * MulAut.conj f * α⁻¹ = (MulAut.conj x) ^ q * (MulAut.conj f) ^ t
      rw [hconj, h2, map_mul, map_pow, map_pow]
  have hεx' : ε x = x ^ 1 * f ^ 0 := by rw [hεx]; simp
  have hsx' : s x = x ^ 1 * f ^ 0 := by rw [hsx]; simp
  have hεN := hN ε 1 i 0 j hεx' hεf
  have hsN := hN s 1 k 0 m hsx' hsf
  have hMat : ∀ (α : MulAut G) (p q r t : ℕ) (h1 : α x = x ^ p * f ^ r) (h2 : α f = x ^ q * f ^ t),
      ((E.rhoE ⟨α, hN α p q r t h1 h2⟩ : GL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        !![(p : ZMod 3), q; r, t] := by
    intro α p q r t h1 h2
    refine E.rhoE_apply_of_conj _ p q r t ?_ ?_
    · show α * MulAut.conj x * α⁻¹ = (MulAut.conj x) ^ p * (MulAut.conj f) ^ r
      rw [hconj, h1, map_mul, map_pow, map_pow]
    · show α * MulAut.conj f * α⁻¹ = (MulAut.conj x) ^ q * (MulAut.conj f) ^ t
      rw [hconj, h2, map_mul, map_pow, map_pow]
  set M : GL23 := E.rhoE ⟨ε, hεN⟩ with hM
  set N : GL23 := E.rhoE ⟨s, hsN⟩ with hNdef
  have hMm := hMat ε 1 i 0 j hεx' hεf
  have hNm := hMat s 1 k 0 m hsx' hsf
  rw [← hM] at hMm
  rw [← hNdef] at hNm
  have hMN : M * N = N * M := by
    rw [hM, hNdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm.symm
  have hM3 : M ^ 3 = 1 := by
    rw [hM, ← map_pow]
    have : (⟨ε, hεN⟩ : ↥(Subgroup.normalizer (Subgroup.closure (Set.range E.vec) :
        Set (MulAut G)))) ^ 3 = 1 := Subtype.ext hε3
    rw [this, map_one]
  have hM1 : M ≠ 1 := by
    intro h1
    rw [h1] at hMm
    have e00 : ((i : ℕ) : ZMod 3) = 0 := by
      have := congrFun (congrFun hMm 0) 1
      simp at this
      exact this.symm
    have e11 : ((j : ℕ) : ZMod 3) = 1 := by
      have := congrFun (congrFun hMm 1) 1
      simp at this
      exact this.symm
    have hi0 : i = 0 := by
      interval_cases i <;> first | rfl | (exfalso; revert e00; decide)
    have hj1 : j = 1 := by
      interval_cases j <;> first | rfl | (exfalso; revert e11; decide)
    apply hεne
    rw [hεf, hi0, hj1]
    simp
  have hN3 := gl23_unip_commute M N hMN hM3 hM1 (by rw [hMm]; exact Nat.cast_one) (by rw [hMm]; exact Nat.cast_zero)
    (by rw [hNm]; exact Nat.cast_one) (by rw [hNm]; exact Nat.cast_zero)
  have hNn : N ^ n = 1 := by
    rw [hNdef, ← map_pow]
    have : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (Subgroup.closure (Set.range E.vec) :
        Set (MulAut G)))) ^ n = 1 := Subtype.ext hsn
    rw [this, map_one]
  have hN1 : N = 1 := by
    have := (pow_gcd_eq_one (a := N) (m := 3) (n := n)).2 ⟨hN3, hNn⟩
    rwa [hn, pow_one] at this
  rw [hN1] at hNm
  have e01 : ((k : ℕ) : ZMod 3) = 0 := by
    have := congrFun (congrFun hNm 0) 1
    simp at this
    exact this.symm
  have e11 : ((m : ℕ) : ZMod 3) = 1 := by
    have := congrFun (congrFun hNm 1) 1
    simp at this
    exact this.symm
  have hk0 : k = 0 := by
    interval_cases k <;> first | rfl | (exfalso; revert e01; decide)
  have hm1 : m = 1 := by
    interval_cases m <;> first | rfl | (exfalso; revert e11; decide)
  rw [hsf, hk0, hm1]
  simp

theorem outer_core (hk : Nat.card k = 4) {E S : Subgroup (MulAut (projectiveSL 3 k))}
    {x : projectiveSL 3 k} (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hx1 : x ≠ 1) (hxE : MulAut.conj x ∈ E) (hS : ¬ 3 ∣ Nat.card S)
    (hcomm : ∀ e ∈ E, ∀ s ∈ S, s * e = e * s) :
    ∀ s ∈ S, ∀ c : projectiveSL 3 k, c * x = x * c → s c = c := by
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have hZ := conj_injective hk
  have hcon : ∀ e ∈ E, ∀ t ∈ S, e * t * e⁻¹ = t := fun e he t ht => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hcomm e he t ht).symm
  by_cases hinn : E ≤ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range
  · refine inner_core hk hE9 hinn hx1 hxE hS ?_
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => by rw [hcon e he h hh]; exact hh, fun hh => ?_⟩
    have h2 := hcon e⁻¹ (inv_mem he) _ hh
    rw [inv_inv] at h2
    have h3 : e⁻¹ * (e * h * e⁻¹) * e = h := by group
    rw [← h3, h2]
    exact hh
  · rw [IsConcreteLE.le_iff] at hinn
    push Not at hinn
    obtain ⟨ε, hεE, hεnot⟩ := hinn
    have hx3 : x ^ 3 = 1 := by
      apply hZ
      rw [map_pow, hE.2 _ hxE, map_one]
    obtain ⟨f, hf3, hxf, hfz⟩ := exists_pair_of_pow_three hk hx3 hx1
    have hxf' : Commute x f := hxf
    have hcard := card_closure_pair_eq_nine hx3 hf3 hxf' hx1 hfz
    let B : E9Basis (projectiveSL 3 k) := ⟨x, f, hx3, hf3, hxf', hcard⟩
    have hxF : x ∈ B.sub := Subgroup.subset_closure (Set.mem_insert _ _)
    have hcent : Subgroup.centralizer ({x} : Set (projectiveSL 3 k)) = B.sub :=
      centralizer_eq_of_card_eq_nine hk hcard hxF hx1
    have hfix : ∀ g : MulAut (projectiveSL 3 k), g * MulAut.conj x = MulAut.conj x * g → g x = x :=
      fun g hg => apply_eq_of_commute_conj hZ hg
    have hdecomp : ∀ g : MulAut (projectiveSL 3 k), g x = x →
        ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ g f = x ^ i * f ^ j := by
      intro g hg
      have hmem : g f ∈ Subgroup.centralizer ({x} : Set (projectiveSL 3 k)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [← hg, ← map_mul, ← map_mul, hxf']
      rw [hcent] at hmem
      obtain ⟨i, j, hi, hj, h⟩ := B.exists_pow_mul_pow hmem
      exact ⟨i, j, hi, hj, h⟩
    have hεcomm : ε * MulAut.conj x = MulAut.conj x * ε :=
      hE.1.is_comm.comm (⟨ε, hεE⟩ : E) ⟨MulAut.conj x, hxE⟩ |> congrArg Subtype.val
    have hεx := hfix ε hεcomm
    have hε3 : ε ^ 3 = 1 := hE.2 ε hεE
    have hεne : ε f ≠ f := by
      intro h
      refine not_forall_apply_eq_of_not_mem_range hk hcard hε3 hεnot ?_
      exact apply_eq_of_fix_pair ε hεx h
    obtain ⟨i, j, hi, hj, hεf⟩ := hdecomp ε hεx
    intro t ht c hc
    have hsx := hfix t (hcomm _ hxE t ht)
    obtain ⟨k', m, hk', hm, hsf⟩ := hdecomp t hsx
    have hord : orderOf t ∣ Nat.card S := by
      have e : orderOf t = orderOf (⟨t, ht⟩ : S) := Subgroup.orderOf_coe (⟨t, ht⟩ : S)
      rw [e]
      exact orderOf_dvd_natCard (⟨t, ht⟩ : S)
    have hcop : Nat.Coprime 3 (orderOf t) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 => hS (h3.trans hord)
    have htf : t f = f :=
      fix_of_unipotent hZ hx3 hf3 hxf' hx1 hfz hεx hsx hi hj hk' hm hεf hsf
        (hcomm ε hεE t ht) hε3 hεne hcop (pow_orderOf_eq_one t)
    have hcF : c ∈ B.sub := by
      rw [← hcent, Subgroup.mem_centralizer_singleton_iff]
      exact hc
    exact apply_eq_of_fix_pair t hsx htf c hcF

end CFSG.HardMathSupport.Solomon.Coordinator
