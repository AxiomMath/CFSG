module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigInvJL
public import CFSG.RankThree.PartOne.SecRank.AltRank

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup Equiv Equiv.Perm Finset
open CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

section Transport

variable {L : Type} [Group L] [Finite L]

theorem rigidAt_of_mulAut (α : MulAut L) {x : L} (hx2 : x * x = 1)
    (hO : Assembly.Dichotomy.involutionOddCore (α x) = ⊥)
    (hR : ∀ β : MulAut L, Odd (orderOf β) →
      (∀ c ∈ Subgroup.centralizer ({α x} : Set L), β c = c) → β = 1) :
    Assembly.Dichotomy.involutionOddCore x = ⊥ ∧
      ∀ β : MulAut L, Odd (orderOf β) →
        (∀ c ∈ Subgroup.centralizer ({x} : Set L), β c = c) → β = 1 := by
  refine ⟨?_, fun β hβ hβC => ?_⟩
  · have hle := ClassicalInvolution.Balance.map_involutionOddCore_le α.toMonoidHom α.surjective
      (ClassicalInvolution.Balance.isPGroup_zpowers_of_mul_self_eq_one hx2)
    have h1 : α.toMonoidHom x = α x := rfl
    rw [h1, hO] at hle
    exact (map_eq_bot_iff_of_injective _ α.injective).mp (le_bot_iff.mp hle)
  · have hodd : Odd (orderOf (MulAut.conj α β)) := by
      rw [show orderOf (MulAut.conj α β) = orderOf β from
        orderOf_injective (MulAut.conj α).toMonoidHom (MulAut.conj α).injective β]
      exact hβ
    have hC : ∀ c ∈ Subgroup.centralizer ({α x} : Set L), (MulAut.conj α β) c = c := by
      intro c hc
      have hc' : α.symm c ∈ Subgroup.centralizer ({x} : Set L) := by
        rw [mem_centralizer_singleton_iff] at hc ⊢
        apply α.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hc
      have h2 := hβC _ hc'
      show α (β (α⁻¹ c)) = c
      rw [MulAut.inv_apply, h2, MulEquiv.apply_symm_apply]
    have h1 := hR _ hodd hC
    calc β = α⁻¹ * (MulAut.conj α β) * α := by rw [MulAut.conj_apply]; group
      _ = 1 := by rw [h1]; group

end Transport

section Support

theorem map_support_eq_of_conj_eq {σ c : Perm (Fin 9)} (h : σ * c * σ⁻¹ = c) :
    c.support.map σ.toEmbedding = c.support := by
  rw [← Equiv.Perm.support_conj, h]

theorem apply_apply_of_map_pair {σ : Perm (Fin 9)} {a b : Fin 9}
    (h : ({a, b} : Finset (Fin 9)).map σ.toEmbedding = {a, b}) : σ (σ a) = a := by
  have ha : σ a ∈ ({a, b} : Finset (Fin 9)) := by
    rw [← h]
    exact Finset.mem_map_of_mem _ (by simp)
  have hb : σ b ∈ ({a, b} : Finset (Fin 9)) := by
    rw [← h]
    exact Finset.mem_map_of_mem _ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with ha | ha
  · rw [ha, ha]
  · rcases hb with hb | hb
    · rw [ha, hb]
    · have hab : a = b := σ.injective (ha.trans hb.symm)
      rw [ha, hb]
      exact hab.symm

theorem apply_of_map_singleton {σ : Perm (Fin 9)} {a : Fin 9}
    (h : ({a} : Finset (Fin 9)).map σ.toEmbedding = {a}) : σ a = a := by
  have ha : σ a ∈ ({a} : Finset (Fin 9)) := by
    rw [← h]
    exact Finset.mem_map_of_mem _ (Finset.mem_singleton_self a)
  simpa using ha

theorem eq_one_of_odd_of_sq_eq_one {σ : Perm (Fin 9)} (hσ : Odd (orderOf σ)) (h2 : σ ^ 2 = 1) :
    σ = 1 := by
  have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hσ
    exact absurd hσ (by decide)

theorem conj_eq_of_conjNormal {σ : Perm (Fin 9)} {c : alternatingGroup (Fin 9)}
    (h : MulAut.conjNormal σ c = c) : σ * (c : Perm (Fin 9)) * σ⁻¹ = c := by
  have h1 := congrArg Subtype.val h
  rwa [MulAut.conjNormal_apply] at h1

end Support

@[expose] def aNineInvTwo : alternatingGroup (Fin 9) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem exists_conjNormal_eq_of_mul_self (x : alternatingGroup (Fin 9)) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : ∃ τ : Perm (Fin 9),
      MulAut.conjNormal τ x = aNineInvTwo ∨ MulAut.conjNormal τ x = aNineEGenX := by
  set σ : Perm (Fin 9) := (x : Perm (Fin 9)) with hσ
  have hσ2 : σ * σ = 1 := congrArg Subtype.val hx2
  have hσ1 : σ ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hsq : σ ^ 2 = 1 := by rw [sq, hσ2]
  have hord : orderOf σ = 2 := orderOf_eq_prime hsq hσ1
  set k := Multiset.card σ.cycleType with hk
  have hrep := CFSG.RankThree.PartOne.SecRank.cycleType_eq_replicate_of_orderOf_two hord
  rw [← hk] at hrep
  have hsupp : #σ.support = 2 * k :=
    (CFSG.ProperTwoGeneratedCore.Lemma37.cycleType_eq_replicate_iff_of_sq_eq_one hsq k).mp hrep
  have hle : #σ.support ≤ 9 := (Finset.card_le_univ _).trans (by simp)
  have hk0 : k ≠ 0 := by
    intro h0
    apply hσ1
    rw [← Equiv.Perm.cycleType_eq_zero, hrep, h0, Multiset.replicate_zero]
  have hsign : sign σ = 1 := Perm.mem_alternatingGroup.mp x.2
  have hkeven : Even k := by
    rw [Equiv.Perm.sign_of_cycleType, hrep, Multiset.sum_replicate, Multiset.card_replicate,
      smul_eq_mul] at hsign
    rcases Nat.even_or_odd k with he | ho
    · exact he
    · exfalso
      have hodd : Odd (k * 2 + k) := Even.add_odd (Nat.even_mul.mpr (Or.inr even_two)) ho
      rw [hodd.neg_one_pow] at hsign
      exact absurd hsign (by decide)
  have hk24 : k = 2 ∨ k = 4 := by
    obtain ⟨m, hm⟩ := hkeven
    omega
  rcases hk24 with h2 | h4
  · have hct : σ.cycleType = (aNineInvTwo : Perm (Fin 9)).cycleType := by
      rw [hrep, h2]
      symm
      exact (CFSG.ProperTwoGeneratedCore.Lemma37.cycleType_eq_replicate_iff_of_sq_eq_one
        (by decide +kernel) 2).mpr (by decide +kernel)
    obtain ⟨τ, hτ⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct)
    exact ⟨τ, Or.inl (Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hτ))⟩
  · have hct : σ.cycleType = (aNineEGenX : Perm (Fin 9)).cycleType := by
      rw [hrep, h4]
      symm
      exact (CFSG.ProperTwoGeneratedCore.Lemma37.cycleType_eq_replicate_iff_of_sq_eq_one
        (by decide +kernel) 4).mpr (by decide +kernel)
    obtain ⟨τ, hτ⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct)
    exact ⟨τ, Or.inr (Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hτ))⟩

@[expose] def aNineOf (p : Perm (Fin 9)) (hp : sign p = 1) : alternatingGroup (Fin 9) :=
  ⟨p, Perm.mem_alternatingGroup.mpr hp⟩

theorem map_support_of_commute {x : alternatingGroup (Fin 9)} {σ : Perm (Fin 9)}
    (hC : ∀ c ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 9))),
      σ * (c : Perm (Fin 9)) * σ⁻¹ = c)
    (p : Perm (Fin 9)) (hp : sign p = 1) (hpx : p * (x : Perm (Fin 9)) = x * p) :
    p.support.map σ.toEmbedding = p.support :=
  map_support_eq_of_conj_eq (hC (aNineOf p hp) (mem_centralizer_singleton_iff.mpr
    (Subtype.ext hpx)))

theorem eq_one_of_odd_of_commute_aNineEGenX {σ : Perm (Fin 9)} (hσ : Odd (orderOf σ))
    (hC : ∀ c ∈ Subgroup.centralizer ({aNineEGenX} : Set (alternatingGroup (Fin 9))),
      σ * (c : Perm (Fin 9)) * σ⁻¹ = c) : σ = 1 := by
  have hA := map_support_of_commute hC (swap 0 1 * swap 2 3) (by decide) (by decide +kernel)
  have hB := map_support_of_commute hC (swap 0 1 * swap 4 5) (by decide) (by decide +kernel)
  have hC' := map_support_of_commute hC (swap 2 3 * swap 4 5) (by decide) (by decide +kernel)
  have hD := map_support_of_commute hC (swap 0 1 * swap 6 7) (by decide) (by decide +kernel)
  have hE := map_support_of_commute hC (swap 2 3 * swap 6 7) (by decide) (by decide +kernel)
  have hX := map_support_eq_of_conj_eq (hC aNineEGenX (mem_centralizer_singleton_iff.mpr rfl))
  rw [show (swap 0 1 * swap 2 3 : Perm (Fin 9)).support = {0, 1, 2, 3} by decide +kernel] at hA
  rw [show (swap 0 1 * swap 4 5 : Perm (Fin 9)).support = {0, 1, 4, 5} by decide +kernel] at hB
  rw [show (swap 2 3 * swap 4 5 : Perm (Fin 9)).support = {2, 3, 4, 5} by decide +kernel] at hC'
  rw [show (swap 0 1 * swap 6 7 : Perm (Fin 9)).support = {0, 1, 6, 7} by decide +kernel] at hD
  rw [show (swap 2 3 * swap 6 7 : Perm (Fin 9)).support = {2, 3, 6, 7} by decide +kernel] at hE
  rw [show (aNineEGenX : Perm (Fin 9)).support = {0, 1, 2, 3, 4, 5, 6, 7} by decide +kernel]
    at hX
  have p01 : ({0, 1} : Finset (Fin 9)).map σ.toEmbedding = {0, 1} := by
    rw [show ({0, 1} : Finset (Fin 9)) = {0, 1, 2, 3} ∩ {0, 1, 4, 5} by decide, Finset.map_inter,
      hA, hB]
  have p10 : ({1, 0} : Finset (Fin 9)).map σ.toEmbedding = {1, 0} := by
    rw [Finset.pair_comm]; exact p01
  have p23 : ({2, 3} : Finset (Fin 9)).map σ.toEmbedding = {2, 3} := by
    rw [show ({2, 3} : Finset (Fin 9)) = {0, 1, 2, 3} ∩ {2, 3, 4, 5} by decide, Finset.map_inter,
      hA, hC']
  have p32 : ({3, 2} : Finset (Fin 9)).map σ.toEmbedding = {3, 2} := by
    rw [Finset.pair_comm]; exact p23
  have p45 : ({4, 5} : Finset (Fin 9)).map σ.toEmbedding = {4, 5} := by
    rw [show ({4, 5} : Finset (Fin 9)) = {0, 1, 4, 5} ∩ {2, 3, 4, 5} by decide, Finset.map_inter,
      hB, hC']
  have p54 : ({5, 4} : Finset (Fin 9)).map σ.toEmbedding = {5, 4} := by
    rw [Finset.pair_comm]; exact p45
  have p67 : ({6, 7} : Finset (Fin 9)).map σ.toEmbedding = {6, 7} := by
    rw [show ({6, 7} : Finset (Fin 9)) = {0, 1, 6, 7} ∩ {2, 3, 6, 7} by decide, Finset.map_inter,
      hD, hE]
  have p76 : ({7, 6} : Finset (Fin 9)).map σ.toEmbedding = {7, 6} := by
    rw [Finset.pair_comm]; exact p67
  have h8 : σ 8 = 8 := by
    by_contra hne
    have hmem : σ 8 ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by
      have : ∀ i : Fin 9, i ≠ 8 → i ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 9)) := by decide
      exact this _ hne
    rw [← hX] at hmem
    obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp hmem
    have : a = 8 := σ.injective hae
    rw [this] at ha
    exact absurd ha (by decide)
  refine eq_one_of_odd_of_sq_eq_one hσ (Equiv.ext fun i => ?_)
  rw [sq, Perm.mul_apply, Perm.one_apply]
  fin_cases i
  · exact apply_apply_of_map_pair p01
  · exact apply_apply_of_map_pair p10
  · exact apply_apply_of_map_pair p23
  · exact apply_apply_of_map_pair p32
  · exact apply_apply_of_map_pair p45
  · exact apply_apply_of_map_pair p54
  · exact apply_apply_of_map_pair p67
  · exact apply_apply_of_map_pair p76
  · show σ (σ 8) = 8
    rw [h8, h8]

theorem eq_one_of_odd_of_commute_aNineInvTwo {σ : Perm (Fin 9)} (hσ : Odd (orderOf σ))
    (hC : ∀ c ∈ Subgroup.centralizer ({aNineInvTwo} : Set (alternatingGroup (Fin 9))),
      σ * (c : Perm (Fin 9)) * σ⁻¹ = c) : σ = 1 := by
  have t456 := map_support_of_commute hC (swap 4 5 * swap 5 6) (by decide) (by decide +kernel)
  have t478 := map_support_of_commute hC (swap 4 7 * swap 7 8) (by decide) (by decide +kernel)
  have t578 := map_support_of_commute hC (swap 5 7 * swap 7 8) (by decide) (by decide +kernel)
  have t678 := map_support_of_commute hC (swap 6 7 * swap 7 8) (by decide) (by decide +kernel)
  have t457 := map_support_of_commute hC (swap 4 5 * swap 5 7) (by decide) (by decide +kernel)
  have t458 := map_support_of_commute hC (swap 4 5 * swap 5 8) (by decide) (by decide +kernel)
  have d0145 := map_support_of_commute hC (swap 0 1 * swap 4 5) (by decide) (by decide +kernel)
  have d0167 := map_support_of_commute hC (swap 0 1 * swap 6 7) (by decide) (by decide +kernel)
  have d2345 := map_support_of_commute hC (swap 2 3 * swap 4 5) (by decide) (by decide +kernel)
  have d2367 := map_support_of_commute hC (swap 2 3 * swap 6 7) (by decide) (by decide +kernel)
  rw [show (swap 4 5 * swap 5 6 : Perm (Fin 9)).support = {4, 5, 6} by decide +kernel] at t456
  rw [show (swap 4 7 * swap 7 8 : Perm (Fin 9)).support = {4, 7, 8} by decide +kernel] at t478
  rw [show (swap 5 7 * swap 7 8 : Perm (Fin 9)).support = {5, 7, 8} by decide +kernel] at t578
  rw [show (swap 6 7 * swap 7 8 : Perm (Fin 9)).support = {6, 7, 8} by decide +kernel] at t678
  rw [show (swap 4 5 * swap 5 7 : Perm (Fin 9)).support = {4, 5, 7} by decide +kernel] at t457
  rw [show (swap 4 5 * swap 5 8 : Perm (Fin 9)).support = {4, 5, 8} by decide +kernel] at t458
  rw [show (swap 0 1 * swap 4 5 : Perm (Fin 9)).support = {0, 1, 4, 5} by decide +kernel] at d0145
  rw [show (swap 0 1 * swap 6 7 : Perm (Fin 9)).support = {0, 1, 6, 7} by decide +kernel] at d0167
  rw [show (swap 2 3 * swap 4 5 : Perm (Fin 9)).support = {2, 3, 4, 5} by decide +kernel] at d2345
  rw [show (swap 2 3 * swap 6 7 : Perm (Fin 9)).support = {2, 3, 6, 7} by decide +kernel] at d2367
  have h4 : σ 4 = 4 := apply_of_map_singleton (by
    rw [show ({4} : Finset (Fin 9)) = {4, 5, 6} ∩ {4, 7, 8} by decide, Finset.map_inter, t456,
      t478])
  have h5 : σ 5 = 5 := apply_of_map_singleton (by
    rw [show ({5} : Finset (Fin 9)) = {4, 5, 6} ∩ {5, 7, 8} by decide, Finset.map_inter, t456,
      t578])
  have h6 : σ 6 = 6 := apply_of_map_singleton (by
    rw [show ({6} : Finset (Fin 9)) = {4, 5, 6} ∩ {6, 7, 8} by decide, Finset.map_inter, t456,
      t678])
  have h7 : σ 7 = 7 := apply_of_map_singleton (by
    rw [show ({7} : Finset (Fin 9)) = {4, 5, 7} ∩ {6, 7, 8} by decide, Finset.map_inter, t457,
      t678])
  have h8 : σ 8 = 8 := apply_of_map_singleton (by
    rw [show ({8} : Finset (Fin 9)) = {4, 5, 8} ∩ {6, 7, 8} by decide, Finset.map_inter, t458,
      t678])
  have p01 : ({0, 1} : Finset (Fin 9)).map σ.toEmbedding = {0, 1} := by
    rw [show ({0, 1} : Finset (Fin 9)) = {0, 1, 4, 5} ∩ {0, 1, 6, 7} by decide, Finset.map_inter,
      d0145, d0167]
  have p10 : ({1, 0} : Finset (Fin 9)).map σ.toEmbedding = {1, 0} := by
    rw [Finset.pair_comm]; exact p01
  have p23 : ({2, 3} : Finset (Fin 9)).map σ.toEmbedding = {2, 3} := by
    rw [show ({2, 3} : Finset (Fin 9)) = {2, 3, 4, 5} ∩ {2, 3, 6, 7} by decide, Finset.map_inter,
      d2345, d2367]
  have p32 : ({3, 2} : Finset (Fin 9)).map σ.toEmbedding = {3, 2} := by
    rw [Finset.pair_comm]; exact p23
  refine eq_one_of_odd_of_sq_eq_one hσ (Equiv.ext fun i => ?_)
  rw [sq, Perm.mul_apply, Perm.one_apply]
  fin_cases i
  · exact apply_apply_of_map_pair p01
  · exact apply_apply_of_map_pair p10
  · exact apply_apply_of_map_pair p23
  · exact apply_apply_of_map_pair p32
  · show σ (σ 4) = 4
    rw [h4, h4]
  · show σ (σ 5) = 5
    rw [h5, h5]
  · show σ (σ 6) = 6
    rw [h6, h6]
  · show σ (σ 7) = 7
    rw [h7, h7]
  · show σ (σ 8) = 8
    rw [h8, h8]

theorem eq_one_of_odd_of_centralizes_of_rep {x : alternatingGroup (Fin 9)}
    (hx : x = aNineInvTwo ∨ x = aNineEGenX) (β : MulAut (alternatingGroup (Fin 9)))
    (hβ : Odd (orderOf β))
    (hβC : ∀ c ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 9))), β c = c) :
    β = 1 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
    (by norm_num) (by norm_num)
  obtain ⟨σ, rfl⟩ := hbij.2 β
  have hσ : Odd (orderOf σ) := by
    rwa [orderOf_injective _ hbij.1 σ] at hβ
  have hC : ∀ c ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 9))),
      σ * (c : Perm (Fin 9)) * σ⁻¹ = c := fun c hc => conj_eq_of_conjNormal (hβC c hc)
  have h1 : σ = 1 := by
    rcases hx with rfl | rfl
    · exact eq_one_of_odd_of_commute_aNineInvTwo hσ hC
    · exact eq_one_of_odd_of_commute_aNineEGenX hσ hC
  rw [h1, map_one]

theorem centralizer_le_normalizer_involutionOddCore {X : Type*} [Group X] (a : X) :
    Subgroup.centralizer ({a} : Set X) ≤
      normalizer (Assembly.Dichotomy.involutionOddCore a : Set X) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => ClassicalInvolution.Balance.conj_mem_involutionOddCore hg hy, fun hy => ?_⟩
  have h := ClassicalInvolution.Balance.conj_mem_involutionOddCore (inv_mem hg) hy
  have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  rwa [e] at h

theorem odd_card_involutionOddCore {X : Type*} [Group X] [Finite X] (a : X) :
    Odd (Nat.card (Assembly.Dichotomy.involutionOddCore a)) := by
  rw [ClassicalInvolution.Balance.involutionOddCore_eq_oddCoreCentralizer]
  exact ClassicalInvolution.Balance.odd_card_oddCoreCentralizer _

theorem involutionOddCore_le_centralizer {X : Type*} [Group X] (a : X) :
    Assembly.Dichotomy.involutionOddCore a ≤ Subgroup.centralizer ({a} : Set X) := by
  rw [ClassicalInvolution.Balance.involutionOddCore_eq_oddCoreCentralizer,
    ← ClassicalInvolution.Balance.centralizer_zpowers_eq]
  exact ClassicalInvolution.Balance.oddCoreCentralizer_le_centralizer _

theorem sq_eq_one_of_mem_aNineEZero {f : alternatingGroup (Fin 9)} (hf : f ∈ ANineEZero) :
    f ^ 2 = 1 := by
  obtain ⟨v, hv⟩ := isRegularTriple_aNineEZero.exists_tripleWord_eq_coe hf
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hv]
  exact isRegularTriple_aNineEZero.sq v

theorem commute_of_mem_aNineEZero {f g : alternatingGroup (Fin 9)} (hf : f ∈ ANineEZero)
    (hg : g ∈ ANineEZero) : f * g = g * f := by
  obtain ⟨v, hv⟩ := isRegularTriple_aNineEZero.exists_tripleWord_eq_coe hf
  obtain ⟨w, hw⟩ := isRegularTriple_aNineEZero.exists_tripleWord_eq_coe hg
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hv, ← hw]
  exact isRegularTriple_aNineEZero.comm v w

theorem aNineEGenX_mem_aNineEZero : aNineEGenX ∈ ANineEZero :=
  Subgroup.subset_closure (by simp)

theorem aNineEZeroGenY_mem_aNineEZero : aNineEZeroGenY ∈ ANineEZero :=
  Subgroup.subset_closure (by simp)

theorem involutionOddCore_aNineEGenX :
    Assembly.Dichotomy.involutionOddCore aNineEGenX = ⊥ := by
  refine eq_bot_of_odd_of_regular_le_normalizer (p := 8)
    (fun f hf => sq_eq_one_of_mem_aNineEZero hf) (fun f hf => apply_eight_of_mem_aNineEZero hf)
    (fun i j hi hj => existsUnique_mem_aNineEZero_apply_eq hi hj) (odd_card_involutionOddCore _)
    fun f hf => centralizer_le_normalizer_involutionOddCore _
      (mem_centralizer_singleton_iff.mpr (commute_of_mem_aNineEZero hf aNineEGenX_mem_aNineEZero))

theorem tripleWord_commute_aNineInvTwo : ∀ v : Fin 8, ∀ i j : Fin 9,
    ((i.val < 4 ∧ j.val < 4) ∨ (4 ≤ i.val ∧ i.val < 8 ∧ 4 ≤ j.val ∧ j.val < 8)) →
      tripleWord (aNineEGenX : Perm (Fin 9)) aNineEZeroGenY aNineEZeroGenZ v i = j →
        tripleWord (aNineEGenX : Perm (Fin 9)) aNineEZeroGenY aNineEZeroGenZ v *
            (aNineInvTwo : Perm (Fin 9)) =
          (aNineInvTwo : Perm (Fin 9)) *
            tripleWord (aNineEGenX : Perm (Fin 9)) aNineEZeroGenY aNineEZeroGenZ v := by
  decide +kernel

theorem mem_centralizer_aNineInvTwo_of_mem {f : alternatingGroup (Fin 9)} (hf : f ∈ ANineEZero)
    {i j : Fin 9} (hij : (i.val < 4 ∧ j.val < 4) ∨ (4 ≤ i.val ∧ i.val < 8 ∧ 4 ≤ j.val ∧ j.val < 8))
    (hfi : (f : Perm (Fin 9)) i = j) :
    f ∈ Subgroup.centralizer ({aNineInvTwo} : Set (alternatingGroup (Fin 9))) := by
  obtain ⟨v, hv⟩ := isRegularTriple_aNineEZero.exists_tripleWord_eq_coe hf
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hv]
  exact tripleWord_commute_aNineInvTwo v i j hij (by rw [hv]; exact hfi)

theorem lt_four_iff_of_mem_centralizer {k : alternatingGroup (Fin 9)}
    (hk : k ∈ Subgroup.centralizer ({aNineInvTwo} : Set (alternatingGroup (Fin 9)))) (i : Fin 9) :
    ((k : Perm (Fin 9)) i).val < 4 ↔ i.val < 4 := by
  have hc : (k : Perm (Fin 9)) * (aNineInvTwo : Perm (Fin 9)) * (k : Perm (Fin 9))⁻¹ =
      aNineInvTwo := by
    have h := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hk)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    rw [h, mul_inv_cancel_right]
  have hS := map_support_eq_of_conj_eq hc
  rw [show (aNineInvTwo : Perm (Fin 9)).support = {0, 1, 2, 3} by decide +kernel] at hS
  have hmem : ∀ j : Fin 9, j ∈ ({0, 1, 2, 3} : Finset (Fin 9)) ↔ j.val < 4 := by decide
  rw [← hmem, ← hmem]
  constructor
  · intro h
    rw [← hS] at h
    obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp h
    have : a = i := (k : Perm (Fin 9)).injective hae
    rwa [← this]
  · intro h
    rw [← hS]
    exact Finset.mem_map_of_mem _ h

private def conjEndA9 {K : Subgroup (alternatingGroup (Fin 9))} {f : alternatingGroup (Fin 9)}
    (hf : f ∈ normalizer (K : Set (alternatingGroup (Fin 9)))) : K →* K :=
  ((MulAut.conj f).toMonoidHom.comp K.subtype).codRestrict K fun y =>
    (Subgroup.mem_normalizer_iff.mp hf y).mp y.2

theorem involutionOddCore_aNineInvTwo :
    Assembly.Dichotomy.involutionOddCore aNineInvTwo = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Assembly.Dichotomy.involutionOddCore aNineInvTwo with hKdef
  set C := Subgroup.centralizer ({aNineInvTwo} : Set (alternatingGroup (Fin 9))) with hCdef
  set F := ANineEZero ⊓ C with hFdef
  have hK : Odd (Nat.card K) := odd_card_involutionOddCore _
  have hKC : K ≤ C := involutionOddCore_le_centralizer _
  have hF2 : IsPGroup 2 F :=
    (IsPGroup.of_card (n := 3) (by rw [card_aNineEZero]; norm_num)).to_le inf_le_left
  have hFK : F ≤ normalizer (K : Set (alternatingGroup (Fin 9))) :=
    inf_le_right.trans (centralizer_le_normalizer_involutionOddCore _)
  have hfree : ∀ i : Fin 9, i ≠ 8 → ∀ f ∈ F, (f : Perm (Fin 9)) i = i → f = 1 :=
    fun i hi f hf hfi => eq_one_of_mem_aNineEZero_of_apply_eq hf.1 hi hfi
  have h8 : ∀ i : Fin 9, i.val < 4 → i ≠ 8 := fun i hi h => by
    rw [h] at hi
    exact absurd hi (by decide)
  have hstep1 : ∀ k ∈ K, ∀ i : Fin 9, i.val < 4 → (k : Perm (Fin 9)) i = i := by
    intro k hk i hi
    refine smul_eq_self_of_odd_of_isPGroup (X := Fin 9) hK hF2 hFK (x := i)
      (fun f hf hfi => hfree i (h8 i hi) f hf hfi) (fun k' hk' => ?_) hk
    set j := (k' : Perm (Fin 9)) i with hj
    have hjlt : j.val < 4 := (lt_four_iff_of_mem_centralizer (hKC hk') i).mpr hi
    obtain ⟨f, ⟨hf, hfi⟩, -⟩ := existsUnique_mem_aNineEZero_apply_eq (h8 i hi) (h8 j hjlt)
    exact ⟨f, ⟨hf, mem_centralizer_aNineInvTwo_of_mem hf (Or.inl ⟨hi, hjlt⟩) hfi⟩, hfi⟩
  have hfix8 : ∀ y ∈ K, (y : Perm (Fin 9)) 8 = 8 → y = 1 := by
    intro y hy hy8
    set S := MulAction.stabilizer (alternatingGroup (Fin 9)) (8 : Fin 9) with hS
    have hFS : F ≤ S := fun f hf => apply_eight_of_mem_aNineEZero hf.1
    have hKS : Odd (Nat.card (K ⊓ S : Subgroup _)) :=
      Odd.of_dvd_nat hK (Subgroup.card_dvd_of_le inf_le_left)
    have hFKS : F ≤ normalizer ((K ⊓ S : Subgroup _) : Set (alternatingGroup (Fin 9))) :=
      (le_inf hFK (hFS.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    refine Subtype.ext (Perm.ext fun i => ?_)
    show (y : Perm (Fin 9)) i = i
    by_cases hi4 : i.val < 4
    · exact hstep1 y hy i hi4
    by_cases hi8 : i = 8
    · rw [hi8]; exact hy8
    have hi48 : 4 ≤ i.val ∧ i.val < 8 := ⟨by omega, by
      have := i.isLt
      have : i.val ≠ 8 := fun h => hi8 (Fin.ext h)
      omega⟩
    refine smul_eq_self_of_odd_of_isPGroup (X := Fin 9) hKS hF2 hFKS (x := i)
      (fun f hf hfi => hfree i hi8 f hf hfi) (fun k hk => ?_) (k := y) ⟨hy, hy8⟩
    have hkp : (k : Perm (Fin 9)) 8 = 8 := hk.2
    set j := (k : Perm (Fin 9)) i with hj
    have hj8 : j ≠ 8 := fun h => hi8 ((k : Perm (Fin 9)).injective (h.trans hkp.symm))
    have hj4 : ¬ j.val < 4 := fun h =>
      hi4 ((lt_four_iff_of_mem_centralizer (hKC hk.1) i).mp h)
    have hj48 : 4 ≤ j.val ∧ j.val < 8 := ⟨by omega, by
      have := j.isLt
      have : j.val ≠ 8 := fun h => hj8 (Fin.ext h)
      omega⟩
    obtain ⟨f, ⟨hf, hfi⟩, -⟩ := existsUnique_mem_aNineEZero_apply_eq hi8 hj8
    exact ⟨f, ⟨hf, mem_centralizer_aNineInvTwo_of_mem hf
      (Or.inr ⟨hi48.1, hi48.2, hj48.1, hj48.2⟩) hfi⟩, hfi⟩
  have hconj1 : ∀ f ∈ F, f ≠ 1 → ∀ y ∈ K, f * y * f⁻¹ = y → y = 1 := by
    intro f hf hf1 y hy hfy
    refine hfix8 y hy ?_
    by_contra hy8
    have hfy' : (f : Perm (Fin 9)) ((y : Perm (Fin 9)) 8) = (y : Perm (Fin 9)) 8 := by
      have h := congrArg (fun g : alternatingGroup (Fin 9) => (g : Perm (Fin 9)) 8)
        (mul_inv_eq_iff_eq_mul.mp hfy)
      simp only [Subgroup.coe_mul, Perm.mul_apply, apply_eight_of_mem_aNineEZero hf.1] at h
      exact h
    exact hf1 (hfree _ hy8 f hf hfy')
  have hinv : ∀ f ∈ F, f ≠ 1 → ∀ y ∈ K, f * y * f⁻¹ = y⁻¹ := fun f hf hf1 y hy => by
    have hfix : MonoidHom.FixedPointFree (conjEndA9 (hFK hf)) := fun z hz =>
      Subtype.ext (hconj1 f hf hf1 z z.2 (congrArg Subtype.val hz))
    have hf2 : f ^ 2 = 1 := sq_eq_one_of_mem_aNineEZero hf.1
    have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_left (by rw [← sq, hf2])
    have hinvol : Function.Involutive (conjEndA9 (hFK hf)) := fun z => Subtype.ext (by
      change f * (f * z * f⁻¹) * f⁻¹ = z
      rw [hfinv, ← mul_assoc, ← mul_assoc, ← sq, hf2, one_mul, mul_assoc, ← sq, hf2, mul_one])
    exact congrArg Subtype.val (congrFun (hfix.coe_eq_inv_of_involutive hinvol) ⟨y, hy⟩)
  have hf₁ : aNineEGenX ∈ F := ⟨aNineEGenX_mem_aNineEZero,
    mem_centralizer_singleton_iff.mpr (Subtype.ext (by decide +kernel))⟩
  have hf₂ : aNineEZeroGenY ∈ F := ⟨aNineEZeroGenY_mem_aNineEZero,
    mem_centralizer_singleton_iff.mpr (Subtype.ext (by decide +kernel))⟩
  have hf₁1 : aNineEGenX ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide +kernel)
  have hf₂1 : aNineEZeroGenY ≠ 1 := fun h => absurd (congrArg Subtype.val h) (by decide +kernel)
  have hf₁₂ : aNineEGenX * aNineEZeroGenY ≠ 1 := fun h =>
    absurd (congrArg Subtype.val h) (by decide +kernel)
  refine (Subgroup.eq_bot_iff_forall K).mpr fun y hy => ?_
  refine hconj1 _ (F.mul_mem hf₁ hf₂) hf₁₂ y hy ?_
  have h2 := hinv _ hf₂ hf₂1 y hy
  have h1 := hinv _ hf₁ hf₁1 y⁻¹ (K.inv_mem hy)
  calc aNineEGenX * aNineEZeroGenY * y * (aNineEGenX * aNineEZeroGenY)⁻¹ =
      aNineEGenX * (aNineEZeroGenY * y * aNineEZeroGenY⁻¹) * aNineEGenX⁻¹ := by group
    _ = y := by rw [h2, h1, inv_inv]

theorem rigidAt_A9 (x : alternatingGroup (Fin 9)) (hx2 : x * x = 1) :
    Assembly.Dichotomy.involutionOddCore x = ⊥ ∧
      ∀ β : MulAut (alternatingGroup (Fin 9)), Odd (orderOf β) →
        (∀ c ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 9))), β c = c) → β = 1 := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  by_cases hx1 : x = 1
  · subst hx1
    refine ⟨involutionOddCore_one_eq_bot_of_simple ?_, fun β _ hβ => MulEquiv.ext fun g =>
      hβ g (mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one]))⟩
    have h2 : orderOf aNineInvTwo ∣ Nat.card (alternatingGroup (Fin 9)) := orderOf_dvd_natCard _
    have ho : orderOf aNineInvTwo = 2 := by
      refine orderOf_eq_prime (Subtype.ext (by decide +kernel)) fun h =>
        absurd (congrArg Subtype.val h) (by decide +kernel)
    rw [ho] at h2
    exact even_iff_two_dvd.mpr h2
  · obtain ⟨τ, hτ⟩ := exists_conjNormal_eq_of_mul_self x hx2 hx1
    refine rigidAt_of_mulAut (MulAut.conjNormal τ) hx2 ?_ ?_
    · rcases hτ with h | h <;> rw [h]
      · exact involutionOddCore_aNineInvTwo
      · exact involutionOddCore_aNineEGenX
    · exact fun β hβ hβC => eq_one_of_odd_of_centralizes_of_rep hτ β hβ hβC

theorem isInvolutionCoreFree_A9 : IsInvolutionCoreFree (alternatingGroup (Fin 9)) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  have hnab : ∃ a b : alternatingGroup (Fin 9), a * b ≠ b * a :=
    ⟨aNineOf (swap 0 1 * swap 1 2) (by decide), aNineOf (swap 1 2 * swap 2 3) (by decide),
      fun h => absurd (congrArg Subtype.val h) (by decide +kernel)⟩
  have hZ : center (alternatingGroup (Fin 9)) = ⊥ := GrSLit.center_eq_bot_of_simple hnab
  exact isInvolutionCoreFree_of_rigid hZ (fun x hx2 => (rigidAt_A9 x hx2).1)
    fun x hx2 => (rigidAt_A9 x hx2).2

theorem involutionCoreFreeA9_holds : InvolutionCoreFreeA9 := fun _ _ _ ⟨e⟩ =>
  isInvolutionCoreFree_of_mulEquiv e.symm isInvolutionCoreFree_A9

theorem involutionCoreFreeJLA_holds :
    InvolutionCoreFreeJLA :=
  involutionCoreFreeJLA_of_A9 involutionCoreFreeA9_holds

end CFSG.ComponentClassification.Sol76.Sig
