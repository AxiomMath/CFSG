module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Solid
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
import all CFSG.ClassicalInvolution.Phan.PhanDn.Perp

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

private theorem two_eq_zero_of_card_eq_four (hK : Nat.card K = 4) : (2 : K) = 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [Fintype.card_eq_nat_card, hK]
  have h4 : (4 : K) = 0 := by
    have h := FiniteField.cast_card_eq_zero (K := K)
    rw [hcard] at h
    simpa using h
  have h22 : (2 : K) * 2 = 0 := by
    rw [← h4]
    norm_num
  exact mul_self_eq_zero.mp h22

private theorem eq_zero_or_one_of_fixed (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {x : K} (hx : σ x = x) : x = 0 ∨ x = 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hcard : Nat.card {c : K // σ c = c} = 2 := by
    have h := card_fixed_eq hσ (q := 2) (by rw [hK]; norm_num)
    simpa using h
  have : Fintype {c : K // σ c = c} := Fintype.ofFinite _
  have hcard' : Fintype.card {c : K // σ c = c} = 2 := by
    rw [Fintype.card_eq_nat_card, hcard]
  have hne : (⟨0, map_zero σ⟩ : {c : K // σ c = c}) ≠ ⟨1, map_one σ⟩ := by
    intro h
    exact zero_ne_one (congrArg Subtype.val h)
  have huniv : ({⟨0, map_zero σ⟩, ⟨1, map_one σ⟩} : Finset {c : K // σ c = c}) =
      Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair hne, hcard'])
  have hmem : (⟨x, hx⟩ : {c : K // σ c = c}) ∈
      ({⟨0, map_zero σ⟩, ⟨1, map_one σ⟩} : Finset {c : K // σ c = c}) := by
    rw [huniv]
    exact Finset.mem_univ _
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

private theorem exists_omega (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) :
    ∃ ω : K, σ ω = ω ^ 2 ∧ ω ^ 2 + ω + 1 = 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_eq_four hK
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨ω, hω⟩ := hσ.exists_ne
  have hω0 : ω ≠ 0 := fun h => hω (by rw [h, map_zero])
  have hω1 : ω ≠ 1 := fun h => hω (by rw [h, map_one])
  have hcard : Fintype.card K = 4 := by rw [Fintype.card_eq_nat_card, hK]
  have h4 : ω ^ 4 = ω := by
    have h := FiniteField.pow_card (K := K) ω
    rwa [hcard] at h
  have h3 : ω ^ 3 = 1 := by
    refine mul_left_cancel₀ hω0 ?_
    rw [mul_one]
    rwa [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ'] at h4
  have hquad : ω ^ 2 + ω + 1 = 0 := by
    have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      have h : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
      rw [h, h3, sub_self]
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hω1)
  have hsum : ω ^ 2 + ω = 1 := by
    have h : ω ^ 2 + ω = -1 := by linear_combination hquad
    rwa [CharTwo.neg_eq] at h
  have hroot : (σ ω) ^ 2 + σ ω + 1 = 0 := by
    have h := congrArg σ hquad
    simpa using h
  have hprod : (σ ω + ω) * (σ ω + ω ^ 2) = 0 := by
    have hωω2 : ω * ω ^ 2 = 1 := by
      rw [← pow_succ']
      exact h3
    have hcomm : ω + ω ^ 2 = 1 := by rw [add_comm]; exact hsum
    have h : (σ ω + ω) * (σ ω + ω ^ 2) = (σ ω) ^ 2 + σ ω * (ω + ω ^ 2) + ω * ω ^ 2 := by
      ring
    rw [h, hcomm, hωω2, mul_one, hroot]
  refine ⟨ω, ?_, hquad⟩
  rcases mul_eq_zero.mp hprod with h | h
  · exfalso
    have h1 : σ ω = -ω := eq_neg_of_add_eq_zero_left h
    rw [CharTwo.neg_eq] at h1
    exact hω h1
  · have h1 : σ ω = -ω ^ 2 := eq_neg_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq] at h1

private theorem polar_self_eq_zero (h2 : (2 : K) = 0) (v : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) v v = 0 := by
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

private theorem quadPlus_fixed_of_fixed {u : Fin n ⊕ Fin n → K} (hu : dFlip σ u = u) :
    σ (quadPlus n K u) = quadPlus n K u := by
  have h := quadPlus_dFlip (σ := σ) (n := n) u
  rw [hu] at h
  exact h.symm

private theorem polar_fixed_of_fixed {u w : Fin n ⊕ Fin n → K}
    (hu : dFlip σ u = u) (hw : dFlip σ w = w) :
    σ (polar (quadPlus n K) u w) = polar (quadPlus n K) u w := by
  have h := polar_dFlip (σ := σ) (n := n) u w
  rw [hu, hw] at h
  exact h.symm

private theorem exists_fixed_decomp (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {ω : K} (hσω : σ ω = ω ^ 2) (hω : ω ^ 2 + ω + 1 = 0)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : dFlipSub σ U = U)
    {v : Fin n ⊕ Fin n → K} (hv : v ∈ U) :
    ∃ s ∈ U, ∃ t ∈ U, dFlip σ s = s ∧ dFlip σ t = t ∧ v = s + ω • t := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_eq_four hK
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hsum : ω ^ 2 + ω = 1 := by
    have h : ω ^ 2 + ω = -1 := by linear_combination hω
    rwa [CharTwo.neg_eq] at h
  have hσ2 : σ (ω ^ 2) = ω := by rw [← hσω, hσ.invol]
  have hdv : dFlip σ v ∈ U := by
    rw [← hU]
    exact Submodule.subset_span ⟨v, hv, rfl⟩
  refine ⟨ω ^ 2 • v + ω • dFlip σ v, U.add_mem (U.smul_mem _ hv) (U.smul_mem _ hdv),
    v + dFlip σ v, U.add_mem hv hdv, ?_, ?_, ?_⟩
  · rw [dFlip_add, dFlip_smul, dFlip_smul, dFlip_dFlip hσ.invol, hσ2, hσω, add_comm]
  · rw [dFlip_add, dFlip_dFlip hσ.invol, add_comm]
  · have h1 : ω ^ 2 • v + ω • v = v := by
      rw [← add_smul, hsum, one_smul]
    have h2' : ω • dFlip σ v + ω • dFlip σ v = 0 := by
      rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
    have hcalc : (ω ^ 2 • v + ω • dFlip σ v) + ω • (v + dFlip σ v) = v := by
      calc (ω ^ 2 • v + ω • dFlip σ v) + ω • (v + dFlip σ v)
          = (ω ^ 2 • v + ω • v) + (ω • dFlip σ v + ω • dFlip σ v) := by
            rw [smul_add]
            abel
        _ = v + 0 := by rw [h1, h2']
        _ = v := add_zero _
    exact hcalc.symm

private theorem le_qPerp_of_fixed_polar (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : dFlipSub σ U = U)
    (hB : ∀ u ∈ U, dFlip σ u = u → ∀ w ∈ U, dFlip σ w = w →
      polar (quadPlus n K) u w = 0) :
    U ≤ qPerp n K U := by
  obtain ⟨ω, hσω, hω⟩ := exists_omega hσ hK
  intro v hv
  obtain ⟨s, hsU, t, htU, hsfix, htfix, rfl⟩ := exists_fixed_decomp hσ hK hσω hω hU hv
  rw [mem_qPerp]
  intro x hx
  obtain ⟨s', hs'U, t', ht'U, hs'fix, ht'fix, rfl⟩ :=
    exists_fixed_decomp hσ hK hσω hω hU hx
  have h1 : polar (quadPlus n K) s' s = 0 := hB s' hs'U hs'fix s hsU hsfix
  have h2 : polar (quadPlus n K) t' s = 0 := hB t' ht'U ht'fix s hsU hsfix
  have h3 : polar (quadPlus n K) s' t = 0 := hB s' hs'U hs'fix t htU htfix
  have h4 : polar (quadPlus n K) t' t = 0 := hB t' ht'U ht'fix t htU htfix
  rw [polar_add_left, polar_add_right, polar_add_right, polar_smul_left, polar_smul_left,
    polar_smul_right, polar_smul_right, h1, h2, h3, h4]
  simp

private theorem exists_fixed_quadPlus_eq_one_notMem_qPerp (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : dFlipSub σ U = U)
    (hrad : Module.finrank K ↥(U ⊓ qPerp n K U) + 3 ≤ Module.finrank K U) :
    ∃ x ∈ U, dFlip σ x = x ∧ quadPlus n K x = 1 ∧ x ∉ qPerp n K U := by
  have hQ01 : ∀ u ∈ U, dFlip σ u = u → quadPlus n K u = 0 ∨ quadPlus n K u = 1 := by
    intro u hu hufix
    exact eq_zero_or_one_of_fixed hσ hK (quadPlus_fixed_of_fixed hufix)
  by_contra hcon
  have hcon' : ∀ x ∈ U, dFlip σ x = x → quadPlus n K x = 1 → x ∈ qPerp n K U := by
    intro x hx hxfix hxq
    by_contra hxperp
    exact hcon ⟨x, hx, hxfix, hxq, hxperp⟩
  have hB : ∀ u ∈ U, dFlip σ u = u → ∀ w ∈ U, dFlip σ w = w →
      polar (quadPlus n K) u w = 0 := by
    intro u hu hufix w hw hwfix
    by_cases huP : u ∈ qPerp n K U
    · rw [polar_comm]
      exact (mem_qPerp.mp huP) w hw
    by_cases hwP : w ∈ qPerp n K U
    · exact (mem_qPerp.mp hwP) u hu
    have hu0 : quadPlus n K u = 0 := by
      rcases hQ01 u hu hufix with h | h
      · exact h
      · exact absurd (hcon' u hu hufix h) huP
    have hw0 : quadPlus n K w = 0 := by
      rcases hQ01 w hw hwfix with h | h
      · exact h
      · exact absurd (hcon' w hw hwfix h) hwP
    by_cases hsumP : u + w ∈ qPerp n K U
    · have h1 := (mem_qPerp.mp hsumP) u hu
      rw [polar_add_right, polar_self_of_singular hu0, zero_add] at h1
      exact h1
    · have hsum0 : quadPlus n K (u + w) = 0 := by
        rcases hQ01 (u + w) (U.add_mem hu hw) (by rw [dFlip_add, hufix, hwfix]) with h | h
        · exact h
        · exact absurd
            (hcon' (u + w) (U.add_mem hu hw) (by rw [dFlip_add, hufix, hwfix]) h) hsumP
      have hmap := QuadraticMap.map_add (quadPlus n K) u w
      rw [hu0, hw0, hsum0] at hmap
      simpa using hmap.symm
  have hUle : U ≤ qPerp n K U := le_qPerp_of_fixed_polar hσ hK hU hB
  have hinf : U ⊓ qPerp n K U = U := inf_eq_left.mpr hUle
  rw [hinf] at hrad
  omega

private theorem exists_fixed_polar_eq_one (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : dFlipSub σ U = U)
    {x : Fin n ⊕ Fin n → K} (hxfix : dFlip σ x = x) (hxperp : x ∉ qPerp n K U) :
    ∃ y ∈ U, dFlip σ y = y ∧ polar (quadPlus n K) x y = 1 := by
  obtain ⟨ω, hσω, hω⟩ := exists_omega hσ hK
  have hex : ∃ u ∈ U, polar (quadPlus n K) u x ≠ 0 := by
    by_contra h
    push Not at h
    exact hxperp (mem_qPerp.mpr h)
  obtain ⟨u, huU, hux⟩ := hex
  obtain ⟨s, hsU, t, htU, hsfix, htfix, rfl⟩ := exists_fixed_decomp hσ hK hσω hω hU huU
  have hs01 : polar (quadPlus n K) s x = 0 ∨ polar (quadPlus n K) s x = 1 :=
    eq_zero_or_one_of_fixed hσ hK (polar_fixed_of_fixed hsfix hxfix)
  have ht01 : polar (quadPlus n K) t x = 0 ∨ polar (quadPlus n K) t x = 1 :=
    eq_zero_or_one_of_fixed hσ hK (polar_fixed_of_fixed htfix hxfix)
  have hexp : polar (quadPlus n K) (s + ω • t) x =
      polar (quadPlus n K) s x + ω * polar (quadPlus n K) t x := by
    rw [polar_add_left, polar_smul_left, smul_eq_mul]
  rw [hexp] at hux
  rcases hs01 with hs0 | hs1
  · rcases ht01 with ht0 | ht1
    · exact absurd hux (by rw [hs0, ht0]; simp)
    · exact ⟨t, htU, htfix, by rw [polar_comm]; exact ht1⟩
  · exact ⟨s, hsU, hsfix, by rw [polar_comm]; exact hs1⟩

private theorem le_qPerp_of_forall_quadPlus_add_ne_one (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : dFlipSub σ U = U)
    {x y : Fin n ⊕ Fin n → K} (hxfix : dFlip σ x = x) (hyfix : dFlip σ y = y)
    (hqy : quadPlus n K y = 0)
    (hcon : ∀ t ∈ U, dFlip σ t = t → polar (quadPlus n K) x t = 0 →
      quadPlus n K (y + t) ≠ 1) :
    U ⊓ qPerp n K (K ∙ x) ≤ qPerp n K (U ⊓ qPerp n K (K ∙ x)) := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_eq_four hK
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hxmem : x ∈ (K ∙ x : Submodule K (Fin n ⊕ Fin n → K)) :=
    Submodule.mem_span_singleton_self x
  have key : ∀ t ∈ U ⊓ qPerp n K (K ∙ x), dFlip σ t = t →
      quadPlus n K t = polar (quadPlus n K) y t := by
    intro t ht htfix
    have hxt : polar (quadPlus n K) x t = 0 := (mem_qPerp.mp ht.2) x hxmem
    have hne := hcon t ht.1 htfix hxt
    have hfix : dFlip σ (y + t) = y + t := by rw [dFlip_add, hyfix, htfix]
    have h01 : quadPlus n K (y + t) = 0 ∨ quadPlus n K (y + t) = 1 :=
      eq_zero_or_one_of_fixed hσ hK (quadPlus_fixed_of_fixed hfix)
    have h0 : quadPlus n K (y + t) = 0 := by
      rcases h01 with h | h
      · exact h
      · exact absurd h hne
    have hmap := QuadraticMap.map_add (quadPlus n K) y t
    rw [hqy, h0, zero_add] at hmap
    have h1 : quadPlus n K t = -polar (quadPlus n K) y t :=
      eq_neg_of_add_eq_zero_left hmap.symm
    rwa [CharTwo.neg_eq] at h1
  have hBT : ∀ u ∈ U ⊓ qPerp n K (K ∙ x), dFlip σ u = u →
      ∀ w ∈ U ⊓ qPerp n K (K ∙ x), dFlip σ w = w → polar (quadPlus n K) u w = 0 := by
    intro u hu hufix w hw hwfix
    have hu' := key u hu hufix
    have hw' := key w hw hwfix
    have huw' : quadPlus n K (u + w) = polar (quadPlus n K) y (u + w) :=
      key (u + w) (Submodule.add_mem _ hu hw) (by rw [dFlip_add, hufix, hwfix])
    have hmap := QuadraticMap.map_add (quadPlus n K) u w
    rw [hu', hw', huw', polar_add_right] at hmap
    linear_combination -hmap
  have hTinv : dFlipSub σ (U ⊓ qPerp n K (K ∙ x)) = U ⊓ qPerp n K (K ∙ x) := by
    rw [dFlipSub_inf hσ.invol, hU, ← qPerp_dFlipSub hσ.invol, dFlipSub_span_singleton, hxfix]
  exact le_qPerp_of_fixed_polar hσ hK hTinv hBT

private theorem finrank_le_of_le_qPerp_span {U : Submodule K (Fin n ⊕ Fin n → K)}
    {x : Fin n ⊕ Fin n → K} (hxU : x ∈ U) (hx0 : x ≠ 0)
    (hle : U ⊓ qPerp n K (K ∙ x) ≤ qPerp n K (U ⊓ qPerp n K (K ∙ x))) :
    Module.finrank K U ≤ Module.finrank K ↥(U ⊓ qPerp n K U) + 2 := by
  have ha_le_c : Module.finrank K ↥(U ⊓ qPerp n K U) ≤ Module.finrank K ↥(qPerp n K U) :=
    Submodule.finrank_mono inf_le_right
  have hqT : qPerp n K (U ⊓ qPerp n K (U ⊓ qPerp n K (K ∙ x))) =
      qPerp n K U ⊔ (U ⊓ qPerp n K (K ∙ x)) := by
    have h1 : qPerp n K (qPerp n K U ⊔ (U ⊓ qPerp n K (K ∙ x))) =
        U ⊓ qPerp n K (U ⊓ qPerp n K (K ∙ x)) := by
      rw [qPerp_sup, qPerp_qPerp]
    rw [← h1, qPerp_qPerp]
  have hinf : qPerp n K U ⊓ (U ⊓ qPerp n K (K ∙ x)) = U ⊓ qPerp n K U := by
    have hle' : U ⊓ qPerp n K U ≤ qPerp n K (K ∙ x) := by
      refine le_trans inf_le_right (qPerp_antitone ?_)
      rw [Submodule.span_singleton_le_iff_mem]
      exact hxU
    rw [← inf_assoc, inf_comm (qPerp n K U) U, inf_eq_left.mpr hle']
  have hsupfin : Module.finrank K ↥(qPerp n K U ⊔ (U ⊓ qPerp n K (K ∙ x))) =
      Module.finrank K ↥(qPerp n K U) + Module.finrank K ↥(U ⊓ qPerp n K (K ∙ x)) -
        Module.finrank K ↥(U ⊓ qPerp n K U) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (qPerp n K U) (U ⊓ qPerp n K (K ∙ x))
    rw [hinf] at h
    omega
  have hperm : Module.finrank K ↥(U ⊓ qPerp n K (U ⊓ qPerp n K (K ∙ x))) +
      Module.finrank K ↥(U ⊓ qPerp n K (K ∙ x)) =
      Module.finrank K U + Module.finrank K ↥(U ⊓ qPerp n K U) := by
    have h := finrank_qPerp (n := n) (K := K) (U ⊓ qPerp n K (U ⊓ qPerp n K (K ∙ x)))
    rw [hqT] at h
    have h' := finrank_qPerp (n := n) (K := K) U
    omega
  have hlow : Module.finrank K ↥(U ⊓ qPerp n K (K ∙ x)) ≤
      Module.finrank K ↥(U ⊓ qPerp n K (U ⊓ qPerp n K (K ∙ x))) :=
    Submodule.finrank_mono (le_inf inf_le_left hle)
  have hTtop : Module.finrank K U ≤ Module.finrank K ↥(U ⊓ qPerp n K (K ∙ x)) + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U (qPerp n K (K ∙ x))
    have hn1 : 1 ≤ 2 * n := by
      have h' := Submodule.finrank_le (K ∙ x : Submodule K (Fin n ⊕ Fin n → K))
      rw [finrank_flipSpace, finrank_span_singleton hx0] at h'
      exact h'
    have hqKx : Module.finrank K ↥(qPerp n K (K ∙ x)) = 2 * n - 1 := by
      have h' := finrank_qPerp (n := n) (K := K) (K ∙ x)
      rw [finrank_span_singleton hx0] at h'
      omega
    have htop : Module.finrank K ↥(U ⊔ qPerp n K (K ∙ x)) ≤ 2 * n := by
      have h' := Submodule.finrank_le (U ⊔ qPerp n K (K ∙ x))
      rwa [finrank_flipSpace] at h'
    omega
  omega

private theorem exists_fixed_polar_eq_zero_quadPlus_eq_one (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : dFlipSub σ U = U)
    (hrad : Module.finrank K ↥(U ⊓ qPerp n K U) + 3 ≤ Module.finrank K U)
    {x : Fin n ⊕ Fin n → K} (hxU : x ∈ U) (hxfix : dFlip σ x = x)
    (hxq : quadPlus n K x = 1) {y : Fin n ⊕ Fin n → K} (hyfix : dFlip σ y = y) :
    ∃ t ∈ U, dFlip σ t = t ∧ polar (quadPlus n K) x t = 0 ∧ quadPlus n K (y + t) = 1 := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_eq_four hK
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hxq
    exact one_ne_zero hxq.symm
  by_contra hcon
  have hcon' : ∀ t ∈ U, dFlip σ t = t → polar (quadPlus n K) x t = 0 →
      quadPlus n K (y + t) ≠ 1 := by
    intro t htU htfix hxt hq
    exact hcon ⟨t, htU, htfix, hxt, hq⟩
  have hqy : quadPlus n K y = 0 := by
    have h0 : polar (quadPlus n K) x (0 : Fin n ⊕ Fin n → K) = 0 := by simp
    have hne := hcon' 0 U.zero_mem dFlip_zero h0
    rw [add_zero] at hne
    rcases eq_zero_or_one_of_fixed hσ hK (quadPlus_fixed_of_fixed hyfix) with h | h
    · exact h
    · exact absurd h hne
  have hle := le_qPerp_of_forall_quadPlus_add_ne_one hσ hK hU hxfix hyfix hqy hcon'
  have hdim := finrank_le_of_le_qPerp_span (n := n) hxU hx0 hle
  have hcontr : Module.finrank K ↥(U ⊓ qPerp n K U) + 3 ≤
      Module.finrank K ↥(U ⊓ qPerp n K U) + 2 := le_trans hrad hdim
  omega

theorem exists_isFlipflopPt_le_of_card_eq_four (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : dFlipSub σ U = U)
    (hrad : Module.finrank K ↥(U ⊓ qPerp n K U) + 3 ≤ Module.finrank K U) :
    ∃ z, IsFlipflopPt σ z ∧ z ≤ U := by
  obtain ⟨ω, hσω, hω⟩ := exists_omega hσ hK
  obtain ⟨x, hxU, hxfix, hxq, hxperp⟩ :=
    exists_fixed_quadPlus_eq_one_notMem_qPerp hσ hK hU hrad
  obtain ⟨y₀, hy₀U, hy₀fix, hxy₀⟩ := exists_fixed_polar_eq_one hσ hK hU hxfix hxperp
  obtain ⟨t, htU, htfix, hxt, hyt⟩ :=
    exists_fixed_polar_eq_zero_quadPlus_eq_one hσ hK hU hrad hxU hxfix hxq hy₀fix
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_eq_four hK
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hyU : y₀ + t ∈ U := U.add_mem hy₀U htU
  have hxy : polar (quadPlus n K) x (y₀ + t) = 1 := by
    rw [polar_add_right, hxy₀, hxt, add_zero]
  have hyq : quadPlus n K (y₀ + t) = 1 := hyt
  have hsum : ω ^ 2 + ω = 1 := by
    have h : ω ^ 2 + ω = -1 := by linear_combination hω
    rwa [CharTwo.neg_eq] at h
  have hqv : quadPlus n K (x + ω • (y₀ + t)) = 0 := by
    have hmap := QuadraticMap.map_add (quadPlus n K) x (ω • (y₀ + t))
    rw [QuadraticMap.map_smul, polar_smul_right, smul_eq_mul, smul_eq_mul, hxq, hyq, hxy] at hmap
    rw [hmap, mul_one, mul_one, ← pow_two, add_assoc, hsum, CharTwo.add_self_eq_zero]
  have hdv : dFlip σ (x + ω • (y₀ + t)) = x + ω ^ 2 • (y₀ + t) := by
    rw [dFlip_add, dFlip_smul, dFlip_add, hxfix, hy₀fix, htfix, hσω]
  have hfh : flipHerm σ (x + ω • (y₀ + t)) (x + ω • (y₀ + t)) = 1 := by
    rw [flipHerm, hdv]
    have hxx : polar (quadPlus n K) x x = 0 := polar_self_eq_zero h2 x
    have hyy : polar (quadPlus n K) (y₀ + t) (y₀ + t) = 0 := polar_self_eq_zero h2 (y₀ + t)
    have hyx : polar (quadPlus n K) (y₀ + t) x = 1 := by rw [polar_comm]; exact hxy
    have hexp : polar (quadPlus n K) (x + ω • (y₀ + t)) (x + ω ^ 2 • (y₀ + t)) =
        polar (quadPlus n K) x x + ω ^ 2 * polar (quadPlus n K) x (y₀ + t) +
          (ω * polar (quadPlus n K) (y₀ + t) x +
            ω * (ω ^ 2 * polar (quadPlus n K) (y₀ + t) (y₀ + t))) := by
      simp only [polar_add_left, polar_smul_left, polar_add_right, polar_smul_right, smul_eq_mul]
      ring
    rw [hexp, hxx, hyy, hxy, hyx]
    simp [hsum]
  have hv0 : x + ω • (y₀ + t) ≠ 0 := by
    intro h
    rw [h, flipHerm_zero_left] at hfh
    exact one_ne_zero hfh.symm
  refine ⟨K ∙ (x + ω • (y₀ + t)), ?_, ?_⟩
  · exact (isFlipflopPt_span_singleton_iff hv0).mpr ⟨hqv, by rw [hfh]; exact one_ne_zero⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (U.add_mem hxU (U.smul_mem _ hyU))

private theorem finrank_radical_inf_qPerp_add_three_le {W S P : Submodule K (Fin n ⊕ Fin n → K)}
    (hWnd : QNondeg W) (hSW : S ≤ W) (hPleS : P ≤ S) (hPnd : QNondeg P)
    (hP2 : Module.finrank K ↥P = 2) (hS4 : Module.finrank K ↥S ≤ 4)
    (hW10 : 10 ≤ Module.finrank K W) :
    Module.finrank K ↥((W ⊓ qPerp n K S) ⊓ qPerp n K (W ⊓ qPerp n K S)) + 3 ≤
      Module.finrank K ↥(W ⊓ qPerp n K S) := by
  have hUU : (W ⊓ qPerp n K S) ⊓ qPerp n K (W ⊓ qPerp n K S) = S ⊓ qPerp n K S := by
    have hUq : qPerp n K (W ⊓ qPerp n K S) = qPerp n K W ⊔ S := by
      have h1 : qPerp n K (qPerp n K W ⊔ S) = W ⊓ qPerp n K S := by
        rw [qPerp_sup, qPerp_qPerp]
      rw [← h1, qPerp_qPerp]
    have hmod : W ⊓ (qPerp n K W ⊔ S) = S := by
      rw [← inf_sup_assoc_of_le (qPerp n K W) hSW, hWnd, bot_sup_eq]
    rw [hUq]
    calc (W ⊓ qPerp n K S) ⊓ (qPerp n K W ⊔ S)
        = qPerp n K S ⊓ (W ⊓ (qPerp n K W ⊔ S)) := by ac_rfl
      _ = qPerp n K S ⊓ S := by rw [hmod]
      _ = S ⊓ qPerp n K S := by rw [inf_comm]
  have hAS : Module.finrank K ↥(S ⊓ qPerp n K S) + 2 ≤ Module.finrank K S := by
    have hAleS : S ⊓ qPerp n K S ≤ S := inf_le_left
    have hdisj : S ⊓ qPerp n K S ⊓ P = ⊥ := by
      have h1 : qPerp n K S ≤ qPerp n K P := qPerp_antitone hPleS
      refine le_bot_iff.mp ?_
      calc S ⊓ qPerp n K S ⊓ P ≤ qPerp n K P ⊓ P :=
            le_inf (le_trans (le_trans inf_le_left inf_le_right) h1) inf_le_right
        _ = P ⊓ qPerp n K P := by rw [inf_comm]
        _ = ⊥ := hPnd
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ qPerp n K S) P
    rw [hdisj, finrank_bot, add_zero] at h2
    have h3 : Module.finrank K ↥((S ⊓ qPerp n K S) ⊔ P) ≤ Module.finrank K ↥S :=
      Submodule.finrank_mono (sup_le hAleS hPleS)
    rw [hP2] at h2
    omega
  have hUdim : Module.finrank K ↥(W ⊓ qPerp n K S) = Module.finrank K W - Module.finrank K S := by
    have h := finrank_inf_qPerp (n := n) (K := K) hWnd hSW
    omega
  have hUrad : Module.finrank K ↥((W ⊓ qPerp n K S) ⊓ qPerp n K (W ⊓ qPerp n K S)) ≤ 2 := by
    rw [hUU]
    omega
  have hsw : Module.finrank K S + 5 ≤ Module.finrank K W := by
    have h1 : Module.finrank K S + 5 ≤ 4 + 5 := Nat.add_le_add_right hS4 5
    have h2 : 4 + 5 ≤ Module.finrank K W := le_trans (by norm_num) hW10
    exact le_trans h1 h2
  omega

private theorem exists_flipStable_common_perp (hσ : IsUnitaryInvolution σ)
    {W : Submodule K (Fin n ⊕ Fin n → K)} (hW : dFlipSub σ W = W) (hWnd : QNondeg W)
    (hdim : 10 ≤ Module.finrank K W) {p p' : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) (hp' : IsFlipflopPt σ p') (hpW : p ≤ W) (hp'W : p' ≤ W) :
    ∃ U, dFlipSub σ U = U ∧
      Module.finrank K ↥(U ⊓ qPerp n K U) + 3 ≤ Module.finrank K U ∧ U ≤ W ∧
      U ≤ qPerp n K p ∧ U ≤ qPerp n K p' ∧ U ≤ qPerp n K (dFlipSub σ p') := by
  have hinvol : ∀ x, σ (σ x) = x := hσ.invol
  obtain ⟨hPnd, -, hPdim, hPinv⟩ := hp.1.sup_dFlipSub hinvol
  obtain ⟨-, -, hP'dim, hP'inv⟩ := hp'.1.sup_dFlipSub hinvol
  have hP2 : Module.finrank K ↥(p ⊔ dFlipSub σ p) = 2 := by
    rw [hPdim, hp.2, mul_one]
  have hP'2 : Module.finrank K ↥(p' ⊔ dFlipSub σ p') = 2 := by
    rw [hP'dim, hp'.2, mul_one]
  have hPW : p ⊔ dFlipSub σ p ≤ W := by
    refine sup_le hpW ?_
    rw [← hW]
    exact dFlipSub_mono hpW
  have hP'W : p' ⊔ dFlipSub σ p' ≤ W := by
    refine sup_le hp'W ?_
    rw [← hW]
    exact dFlipSub_mono hp'W
  have hSW : (p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p') ≤ W := sup_le hPW hP'W
  have hSinv : dFlipSub σ ((p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p')) =
      (p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p') := by
    rw [dFlipSub_sup hinvol, hPinv, hP'inv]
  have hS4 : Module.finrank K ↥((p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p')) ≤ 4 := by
    have h := Submodule.finrank_add_le_finrank_add_finrank (p ⊔ dFlipSub σ p)
      (p' ⊔ dFlipSub σ p')
    omega
  have hpP : p ≤ p ⊔ dFlipSub σ p := le_sup_left
  have hPS : p ⊔ dFlipSub σ p ≤ (p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p') := le_sup_left
  have hpS : p ≤ (p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p') := le_trans hpP hPS
  have hp'P' : p' ≤ p' ⊔ dFlipSub σ p' := le_sup_left
  have hP'S : p' ⊔ dFlipSub σ p' ≤ (p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p') := le_sup_right
  have hp'S : p' ≤ (p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p') := le_trans hp'P' hP'S
  have hdp'S : dFlipSub σ p' ≤ (p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p') := by
    have h := dFlipSub_mono (σ := σ) hp'S
    rwa [hSinv] at h
  have hrad := finrank_radical_inf_qPerp_add_three_le (n := n) hWnd hSW le_sup_left hPnd hP2 hS4
    hdim
  have hUp : W ⊓ qPerp n K ((p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p')) ≤ qPerp n K p :=
    le_trans inf_le_right (qPerp_antitone hpS)
  have hUp' : W ⊓ qPerp n K ((p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p')) ≤ qPerp n K p' :=
    le_trans inf_le_right (qPerp_antitone hp'S)
  refine ⟨W ⊓ qPerp n K ((p ⊔ dFlipSub σ p) ⊔ (p' ⊔ dFlipSub σ p')), ?_, hrad, inf_le_left, hUp,
    hUp', ?_⟩
  · rw [dFlipSub_inf hinvol, hW, ← qPerp_dFlipSub hinvol, hSinv]
  · exact le_trans inf_le_right (qPerp_antitone hdp'S)

theorem exists_flipColl_flipColl_of_card_eq_four (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {W : Submodule K (Fin n ⊕ Fin n → K)} (hW : dFlipSub σ W = W)
    (hWnd : QNondeg W) (hdim : 10 ≤ Module.finrank K W)
    {p p' : Submodule K (Fin n ⊕ Fin n → K)} (hp : IsFlipflopPt σ p) (hp' : IsFlipflopPt σ p')
    (hpW : p ≤ W) (hp'W : p' ≤ W) :
    ∃ z, IsFlipflopPt σ z ∧ z ≤ W ∧ FlipColl σ p z ∧ FlipColl σ z p' := by
  have hinvol : ∀ x, σ (σ x) = x := hσ.invol
  obtain ⟨U, hUinv, hrad, hUW, hUp, hUp', hUdp'⟩ :=
    exists_flipStable_common_perp hσ hW hWnd hdim hp hp' hpW hp'W
  obtain ⟨z, hz, hzU⟩ := exists_isFlipflopPt_le_of_card_eq_four hσ hK hUinv hrad
  have hzW : z ≤ W := le_trans hzU hUW
  have hzp : p ≤ qPerp n K z := by
    have h := qPerp_antitone (le_trans hzU hUp)
    rwa [qPerp_qPerp] at h
  have hzo : p ≤ flipOrth σ z := by
    rw [flipOrth_eq_qPerp_dFlipSub hinvol]
    have h1 : dFlipSub σ z ≤ qPerp n K p :=
      le_trans (dFlipSub_mono (σ := σ) hzU) (le_trans hUinv.le hUp)
    have h := qPerp_antitone h1
    rwa [qPerp_qPerp] at h
  have hcol₁ : FlipColl σ p z := flipColl_of_orth hinvol hp hz hzp hzo
  have hcol₂ : FlipColl σ z p' := by
    refine flipColl_of_orth hinvol hz hp' (le_trans hzU hUp') ?_
    rw [flipOrth_eq_qPerp_dFlipSub hinvol]
    exact le_trans hzU hUdp'
  exact ⟨z, hz, hzW, hcol₁, hcol₂⟩

theorem exists_flipGraph_adj_adj_of_card_eq_four (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hn : 5 ≤ n) (p p' : FlipPt σ n) :
    ∃ x, (flipGraph σ n).Adj p x ∧ (flipGraph σ n).Adj x p' := by
  have hinvol : ∀ x, σ (σ x) = x := hσ.invol
  have hW : dFlipSub σ (⊤ : Submodule K (Fin n ⊕ Fin n → K)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    rw [mem_dFlipSub hinvol]
    exact Submodule.mem_top
  have hqtop : qPerp n K (⊤ : Submodule K (Fin n ⊕ Fin n → K)) = ⊥ := by
    have h1 := qPerp_bot (n := n) (K := K)
    have h2 := qPerp_qPerp (n := n) (K := K) (⊥ : Submodule K (Fin n ⊕ Fin n → K))
    rw [h1] at h2
    exact h2
  have hWnd : QNondeg (⊤ : Submodule K (Fin n ⊕ Fin n → K)) := by
    rw [QNondeg, hqtop, inf_bot_eq]
  have hdim : 10 ≤ Module.finrank K (⊤ : Submodule K (Fin n ⊕ Fin n → K)) := by
    rw [finrank_top, finrank_flipSpace]
    exact Nat.mul_le_mul_left 2 hn
  obtain ⟨z, hz, -, hcol₁, hcol₂⟩ :=
    exists_flipColl_flipColl_of_card_eq_four hσ hK hW hWnd hdim p.2 p'.2 le_top le_top
  exact ⟨⟨z, hz⟩, hcol₁, hcol₂⟩

theorem flipGraph_ediam_le_two_of_card_eq_four (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hn : 5 ≤ n) : (flipGraph σ n).ediam ≤ 2 := by
  refine SimpleGraph.ediam_le_of_edist_le fun p p' => ?_
  obtain ⟨x, h1, h2⟩ := exists_flipGraph_adj_adj_of_card_eq_four hσ hK hn p p'
  calc (flipGraph σ n).edist p p' ≤ (SimpleGraph.Walk.cons h1 h2.toWalk).length :=
        SimpleGraph.edist_le (SimpleGraph.Walk.cons h1 h2.toWalk)
    _ = 2 := by simp

theorem flipGraph_connected_of_card_eq_four (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) (hn : 5 ≤ n) : (flipGraph σ n).Connected := by
  have : Nonempty (FlipPt σ n) := ⟨⟨_, isFlipflopPt_stdE (K := K) (σ := σ) (by omega)⟩⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨z, h1, h2⟩ := exists_flipGraph_adj_adj_of_card_eq_four hσ hK hn x y
  exact (SimpleGraph.Walk.cons h1 h2.toWalk).reachable

end CFSG.ClassicalInvolution.PhanDn
