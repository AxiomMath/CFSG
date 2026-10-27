module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptClass
public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched
import CFSG.ClassicalInvolution.RouteD.TypeF4TwinP1

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.Balance.Theorem5
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G}

section Counting

theorem mem_closure_insert_involution {S : Set G} {c : G} (hc : c * c = 1)
    (hcS : ∀ s ∈ S, c * s = s * c) {x : G} (hx : x ∈ Subgroup.closure (insert c S)) :
    x ∈ Subgroup.closure S ∨ ∃ g ∈ Subgroup.closure S, x = g * c :=
  CFSG.ClassicalInvolution.RouteD.NonClassical.mem_closure_insert_of_involution hc hcS hx

variable [Finite G]

theorem card_closure_insert_eq {S : Set G} {c : G} (hc : c * c = 1)
    (hcS : ∀ s ∈ S, c * s = s * c) (hnot : c ∉ Subgroup.closure S) :
    Nat.card (Subgroup.closure (insert c S)) = 2 * Nat.card (Subgroup.closure S) := by
  have hle := Balance.Theorem5.card_closure_insert_le hc hcS
  have hFA : Subgroup.closure S ≤ Subgroup.closure (insert c S) :=
    Subgroup.closure_mono (Set.subset_insert c S)
  have hdvd : Nat.card (Subgroup.closure S) ∣ Nat.card (Subgroup.closure (insert c S)) :=
    Subgroup.card_dvd_of_le hFA
  have hne : Nat.card (Subgroup.closure (insert c S)) ≠ Nat.card (Subgroup.closure S) := by
    intro h
    have heq : Subgroup.closure S = Subgroup.closure (insert c S) :=
      Subgroup.eq_of_le_of_card_ge hFA (by rw [h])
    exact hnot (heq ▸ Subgroup.subset_closure (Set.mem_insert c S))
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < Nat.card (Subgroup.closure S) := Nat.card_pos
  have hposA : 0 < Nat.card (Subgroup.closure (insert c S)) := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact hne hk
  have hk3 : k ≤ 2 := by
    by_contra h
    push Not at h
    have h3 : Nat.card (Subgroup.closure S) * 3 ≤ Nat.card (Subgroup.closure S) * k :=
      Nat.mul_le_mul_left _ h
    omega
  have hk2 : k = 2 := by omega
  rw [hk, hk2, mul_comm]

end Counting

section Nodes

variable {c : UCtx p f 5 Ω K z} {nd : UNodes c} {Θ : Su (GaloisField p (2 * f)) p f 6 →* G}

theorem mem_center_of_map_eq (hΘ : TE6Chart c nd Θ) {s : Su (GaloisField p (2 * f)) p f 6}
    (hs : Θ s = z) : s ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f 6) := by
  have : Group.IsPerfect (Su (GaloisField p (2 * f)) p f 6) :=
    isPerfect_su_gen c.card_eq c.hq (by norm_num)
  refine mem_center_of_commutator_mem_center fun y => hΘ.ker_le ?_
  rw [MonoidHom.mem_ker, map_commutatorElement, hs, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hΘ.range_le_centralizer_z ⟨y, rfl⟩)).symm

theorem zEltU_mul_not_mem_center (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    zEltU (GaloisField p (2 * f)) p f (nodePair 5 0 (by norm_num)) *
      zEltU (GaloisField p (2 * f)) p f (nodePair 5 2 (by norm_num)) ∉
        Subgroup.center (Su (GaloisField p (2 * f)) p f 6) := by
  intro hz
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center
    (isUnitaryInvolution_unitaryInvolution (p := p) (f := f) (card_galoisField_two_mul_eq hq))
    (by norm_num : 3 ≤ 6) hz
  have e1 := congrFun (congrFun hu 0) 0
  have e2 := congrFun (congrFun hu 4) 4
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at e1 e2
  have hm : ∀ r : Fin 6, suMat (zEltU (GaloisField p (2 * f)) p f (nodePair 5 0 (by norm_num)) *
      zEltU (GaloisField p (2 * f)) p f (nodePair 5 2 (by norm_num))) r r =
      (if r.val < 2 then (-1 : GaloisField p (2 * f)) else 1) *
        (if 2 ≤ r.val ∧ r.val < 4 then -1 else 1) := by
    intro r
    rw [suMat_mul, suMat_zEltU, suMat_zEltU, zMat, zMat, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq]
    have h1 : r ∈ (nodePair 5 0 (by norm_num)).1 ↔ r.val < 2 := by
      simp only [nodePair, natPair, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    have h2 : r ∈ (nodePair 5 2 (by norm_num)).1 ↔ 2 ≤ r.val ∧ r.val < 4 := by
      simp only [nodePair, natPair, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    simp only [h1, h2]
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have := (hm 0).symm.trans (e1.trans e2.symm |>.trans (hm 4))
  simp at this
  apply h2
  linear_combination (-1 : GaloisField p (2 * f)) * this

end Nodes

section Triple

variable [Finite G]

omit [Finite G] in
theorem eq_one_or_eq_of_mem_closure_singleton {c x : G} (hc : c * c = 1)
    (hx : x ∈ Subgroup.closure ({c} : Set G)) : x = 1 ∨ x = c := by
  rw [← insert_empty_eq] at hx
  rcases mem_closure_insert_involution hc (S := ∅) (fun s hs => absurd hs (Set.notMem_empty s))
    hx with h | ⟨g, hg, rfl⟩
  · rw [Subgroup.closure_empty] at h
    exact Or.inl (Subgroup.mem_bot.mp h)
  · rw [Subgroup.closure_empty] at hg
    rw [Subgroup.mem_bot.mp hg, one_mul]
    exact Or.inr rfl

theorem card_closure_nodes (c : UCtx p f 5 Ω K z) (nd : UNodes c) :
    Nat.card (Subgroup.closure ({z, nd.w 0, nd.w 2} : Set G)) = 8 := by
  classical
  obtain ⟨Θ, hΘ⟩ := c.exists_te6Chart nd
  have hz2 : z * z = 1 := DeltaClosure.sq_eq_one c.hz
  have hw0 : nd.w 0 * nd.w 0 = 1 := DeltaClosure.sq_eq_one (nd.isCl 0 (by norm_num))
  have hw2 : nd.w 2 * nd.w 2 = 1 := DeltaClosure.sq_eq_one (nd.isCl 2 (by norm_num))
  have hzw0 : z * nd.w 0 = nd.w 0 * z := (nd.wz 0 (by norm_num)).symm
  have hzw2 : z * nd.w 2 = nd.w 2 * z := (nd.wz 2 (by norm_num)).symm
  have hw02 : nd.w 0 * nd.w 2 = nd.w 2 * nd.w 0 := nd.wcomm 0 (by norm_num) 2 (by norm_num)
  have hord : ∀ g : G, IsClassicalMember p f K g → g ≠ 1 := fun g hg h => by
    have := hg.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hΘ0 := map_zEltU_eq hΘ (a := 0) (by norm_num)
  have hΘ2 := map_zEltU_eq hΘ (a := 2) (by norm_num)
  have hne0 : nd.w 0 ≠ 1 := by
    have := (nd.isCl 0 (by norm_num)).orderOf_eq_two
    intro h
    rw [h, orderOf_one] at this
    omega
  have hne2 : nd.w 2 ≠ 1 := by
    have := (nd.isCl 2 (by norm_num)).orderOf_eq_two
    intro h
    rw [h, orderOf_one] at this
    omega
  have hz1 : z ≠ 1 := by
    have := c.hz.orderOf_eq_two
    intro h
    rw [h, orderOf_one] at this
    omega
  have hker : ∀ s : Su (GaloisField p (2 * f)) p f 6, Θ s = 1 →
      s ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f 6) := fun s hs =>
    hΘ.ker_le (MonoidHom.mem_ker.mpr hs)
  have hnc : ∀ g : G, Θ (zEltU (GaloisField p (2 * f)) p f (nodePair 5 0 (by norm_num)) *
      zEltU (GaloisField p (2 * f)) p f (nodePair 5 2 (by norm_num))) = g → g ≠ 1 ∧ g ≠ z := by
    intro g hg
    rw [map_mul, hΘ0, hΘ2] at hg
    refine ⟨fun h1 => zEltU_mul_not_mem_center c.hp2 c.hq
        (hker _ (by rw [map_mul, hΘ0, hΘ2, hg, h1])),
      fun h1 => zEltU_mul_not_mem_center c.hp2 c.hq (mem_center_of_map_eq hΘ (by
        rw [map_mul, hΘ0, hΘ2, hg, h1]))⟩
  have hN1 : nd.w 0 ∉ Subgroup.closure ({nd.w 2} : Set G) := by
    intro h
    rcases eq_one_or_eq_of_mem_closure_singleton hw2 h with h1 | h1
    · exact hne0 h1
    · refine (hnc 1 ?_).1 rfl
      rw [map_mul, hΘ0, hΘ2, ← h1, hw0]
  have hN2 : z ∉ Subgroup.closure (insert (nd.w 0) ({nd.w 2} : Set G)) := by
    intro h
    rcases mem_closure_insert_involution hw0 (S := ({nd.w 2} : Set G)) (by
      intro s hs
      rw [Set.mem_singleton_iff.mp hs]
      exact hw02) h with h1 | ⟨g, hg, hzg⟩
    · rcases eq_one_or_eq_of_mem_closure_singleton hw2 h1 with h2 | h2
      · exact hz1 h2
      · exact zEltU_not_mem_center c.card_eq c.h2 (by norm_num : 3 ≤ 5 + 1)
          (nodePair 5 2 (by norm_num)) (mem_center_of_map_eq hΘ (hΘ2.trans h2.symm))
    · rcases eq_one_or_eq_of_mem_closure_singleton hw2 hg with h2 | h2
      · rw [h2, one_mul] at hzg
        exact zEltU_not_mem_center c.card_eq c.h2 (by norm_num : 3 ≤ 5 + 1)
          (nodePair 5 0 (by norm_num)) (mem_center_of_map_eq hΘ (hΘ0.trans hzg.symm))
      · rw [h2] at hzg
        exact (hnc z (by rw [map_mul, hΘ0, hΘ2, hw02]; exact hzg.symm)).2 rfl
  have c1 : Nat.card (Subgroup.closure ({nd.w 2} : Set G)) = 2 := by
    have h := card_closure_insert_eq (S := (∅ : Set G)) hw2
      (fun s hs => absurd hs (Set.notMem_empty s))
      (by rw [Subgroup.closure_empty, Subgroup.mem_bot]; exact hne2)
    rwa [insert_empty_eq, Subgroup.closure_empty, Subgroup.card_bot, mul_one] at h
  have c2 : Nat.card (Subgroup.closure (insert (nd.w 0) ({nd.w 2} : Set G))) = 4 := by
    rw [card_closure_insert_eq hw0 (S := ({nd.w 2} : Set G)) (by
      intro s hs
      rw [Set.mem_singleton_iff.mp hs]
      exact hw02) hN1, c1]
  rw [card_closure_insert_eq hz2 (S := insert (nd.w 0) ({nd.w 2} : Set G)) (by
    rintro s (rfl | hs)
    · exact hzw0
    · rw [Set.mem_singleton_iff.mp hs]
      exact hzw2) hN2, c2]

omit [Finite G] in
theorem nodes_members (c : UCtx p f 5 Ω K z) (nd : UNodes c) :
    ∀ i : Fin 3, ![K, nd.j 0, nd.j 2] i ∈ Ω ∧
      IsClassicalMember p f (![K, nd.j 0, nd.j 2] i) (![z, nd.w 0, nd.w 2] i) := by
  intro i
  fin_cases i
  · exact ⟨c.hK, c.hz⟩
  · exact ⟨(nd.mem 0 (by norm_num)).1, nd.isCl 0 (by norm_num)⟩
  · exact ⟨(nd.mem 2 (by norm_num)).1, nd.isCl 2 (by norm_num)⟩

omit [Finite G] in
theorem nodes_comm (c : UCtx p f 5 Ω K z) (nd : UNodes c) :
    ∀ i j : Fin 3, i ≠ j → ∀ x ∈ ![K, nd.j 0, nd.j 2] i, ∀ y ∈ ![K, nd.j 0, nd.j 2] j,
      x * y = y * x := by
  intro i j hij x hx y hy
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact nd.commK 0 (by norm_num) x hx y hy
  · exact nd.commK 2 (by norm_num) x hx y hy
  · exact (nd.commK 0 (by norm_num) y hy x hx).symm
  · exact absurd rfl hij
  · exact nd.far 0 (by norm_num) 2 (by norm_num) (by norm_num) x hx y hy
  · exact (nd.commK 2 (by norm_num) y hy x hx).symm
  · exact (nd.far 0 (by norm_num) 2 (by norm_num) (by norm_num) y hy x hx).symm
  · exact absurd rfl hij

omit [Finite G] in
theorem nodes_range (c : UCtx p f 5 Ω K z) (nd : UNodes c) :
    Subgroup.closure ({z, nd.w 0, nd.w 2} : Set G) =
      Subgroup.closure (Set.range ![z, nd.w 0, nd.w 2]) := by
  congr 1
  ext x
  simp
  tauto

omit [Finite G] in
theorem nodes_elemAbelian (c : UCtx p f 5 Ω K z) (nd : UNodes c) :
    IsElemAbelian 2 (Subgroup.closure ({z, nd.w 0, nd.w 2} : Set G)) := by
  have hz2 : z * z = 1 := DeltaClosure.sq_eq_one c.hz
  have hw0 : nd.w 0 * nd.w 0 = 1 := DeltaClosure.sq_eq_one (nd.isCl 0 (by norm_num))
  have hw2 : nd.w 2 * nd.w 2 = 1 := DeltaClosure.sq_eq_one (nd.isCl 2 (by norm_num))
  have hzw0 : z * nd.w 0 = nd.w 0 * z := (nd.wz 0 (by norm_num)).symm
  have hzw2 : z * nd.w 2 = nd.w 2 * z := (nd.wz 2 (by norm_num)).symm
  have hw02 : nd.w 0 * nd.w 2 = nd.w 2 * nd.w 0 := nd.wcomm 0 (by norm_num) 2 (by norm_num)
  refine isElemAbelian_closure_of_commuting_involutions ?_ ?_
  · rintro s (rfl | rfl | rfl)
    · exact hz2
    · exact hw0
    · exact hw2
  · rintro s (rfl | rfl | rfl) t (rfl | rfl | rfl)
    · rfl
    · exact hzw0
    · exact hzw2
    · exact hzw0.symm
    · rfl
    · exact hw02
    · exact hzw2.symm
    · exact hw02.symm
    · rfl

theorem indepTripleOn_nodes (c : UCtx p f 5 Ω K z) (nd : UNodes c) :
    IndepTripleOn p f Ω (Subgroup.closure ({z, nd.w 0, nd.w 2} : Set G)) :=
  ⟨![K, nd.j 0, nd.j 2], ![z, nd.w 0, nd.w 2], nodes_members c nd, nodes_comm c nd,
    nodes_range c nd, nodes_elemAbelian c nd, card_closure_nodes c nd⟩

end Triple

section P1

variable [Finite G]

theorem localOddCentral_mul_of_alphaCore [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hIH : LocalLieSystems p f Ω)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    (c : UCtx p f 5 Ω K z) (nd : UNodes c) {F₀ : Subgroup G}
    (hF₀ : F₀ ∈ signalizerFunctorEk 2 2 (Subgroup.closure ({z, nd.w 0, nd.w 2} : Set G)))
    (hα : alphaCore F₀ = ⊥) : LocalOddCentral Ω {z * nd.w 0} := by
  classical
  have hx : z * nd.w 0 ∈ Subgroup.closure
      ({(![z, nd.w 0, nd.w 2] : Fin 3 → G) 0, (![z, nd.w 0, nd.w 2] : Fin 3 → G) 1} : Set G) := by
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (Subgroup.subset_closure ?_)
    · simp
    · simp
  have hx1 : z * nd.w 0 ≠ 1 := by
    intro h1
    have hzw : z = nd.w 0 := by
      have h2 : nd.w 0 * nd.w 0 = 1 := DeltaClosure.sq_eq_one (nd.isCl 0 (by norm_num))
      calc z = z * (nd.w 0 * nd.w 0) := by rw [h2, mul_one]
        _ = (z * nd.w 0) * nd.w 0 := by rw [mul_assoc]
        _ = nd.w 0 := by rw [h1, one_mul]
    have hle := card_closure_pair_le_four (a := nd.w 0) (b := nd.w 2)
      (DeltaClosure.sq_eq_one (nd.isCl 0 (by norm_num)))
      (DeltaClosure.sq_eq_one (nd.isCl 2 (by norm_num)))
      (nd.wcomm 0 (by norm_num) 2 (by norm_num))
    have h8 := card_closure_nodes c nd
    have hset : ({z, nd.w 0, nd.w 2} : Set G) = {nd.w 0, nd.w 2} := by
      ext y
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hzw]
      tauto
    rw [hset] at h8
    omega
  exact localOddCentral_of_indepTriple_pair hnab c.hp2 c.hq c.hΩ hIH c.hex hlay
    (nodes_members c nd) (nodes_comm c nd) (nodes_range c nd) (nodes_elemAbelian c nd)
    (card_closure_nodes c nd) hF₀ hα (i := 0) (j := 1) (by decide) hx hx1

theorem localOddCentral_mul_of_triangleConnected [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hIH : LocalLieSystems p f Ω)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    (htri : TriangleConnected p f Ω) (c : UCtx p f 5 Ω K z) (nd : UNodes c) :
    LocalOddCentral Ω {z * nd.w 0} := by
  have hf : 0 < f := Nat.pos_of_ne_zero c.hf
  have hbal : ∀ A ∈ triangleFrames p f Ω, RankThreeBalance A := fun A hA =>
    rankThreeBalance_of_indepTripleOn_of_layers hnab c.hp2 hf c.hq c.hΩ hIH hA (hlay A hA)
  have hα := alphaCore_eq_bot_of_connected_frames (𝒯 := triangleFrames p f Ω)
    (componentClassificationOddCore_eq_bot_of_simple hnab)
    (fun A hA g => indepTripleOn_map c.hΩ.conjInvariant hA g) hbal htri
  have hA := indepTripleOn_nodes c nd
  obtain ⟨F₀, hF₀⟩ := exists_mem_signalizerFunctorEk (hbal _ hA)
  exact localOddCentral_mul_of_alphaCore hnab hIH hlay c nd hF₀ (hα _ hA F₀ hF₀)

theorem localOddCentral_mul_of_triangleInputs [IsSimpleGroup G] (hlay : TriangleLayers p f)
    (htri : TriangleConnectedAll p f) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hBelow : CITBelowU p f (Nat.card G))
    (hconn : RouteD.DeltaConnected (CoreAssembly.conjClass K))
    (c : UCtx p f 5 (CoreAssembly.conjClass K) K z) (nd : UNodes c) :
    LocalOddCentral (CoreAssembly.conjClass K) {z * nd.w 0} :=
  localOddCentral_mul_of_triangleConnected hnab (localLieSystems_of_citBelowU c.hΩ hBelow)
    (fun A' hA' => hlay G hnab c.hp2 c.hq K z c.hz hBelow hconn A' hA')
    (htri G hnab c.hp2 c.hq K z c.hz hBelow hconn) c nd

end P1

end CFSG.ClassicalInvolution.RouteD.NonClassical
