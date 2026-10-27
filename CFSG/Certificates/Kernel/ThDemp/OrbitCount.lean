module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

namespace CFSG.Certificates.ThDemp.OrbitCount

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

theorem ncard_orbit_mul_card_stabilizer (D : Subgroup G) [Finite D] (p : X) :
    (orbit D p).ncard * Nat.card (stabilizer D p) = Nat.card D := by
  rw [← index_stabilizer, mul_comm, Subgroup.card_mul_index]

theorem stabilizer_eq_and_cover [Finite G] {n : ℕ} (D : Subgroup G) (x₀ : X)
    (hD : D ≤ stabilizer G x₀) (p : Fin n → X) (hp : ∀ i, p i ∈ orbit G x₀)
    (hdisj : ∀ i j, i ≠ j → p j ∉ orbit D (p i))
    (hle : Nat.card G ≤ Nat.card D * ∑ i, (orbit D (p i)).ncard) :
    stabilizer G x₀ = D ∧ ∀ x ∈ orbit G x₀, ∃ i, x ∈ orbit D (p i) := by
  classical
  have hfin : (orbit G x₀).Finite := Set.finite_range _
  set F := hfin.toFinset with hF
  have hsub : ∀ i, orbit D (p i) ⊆ orbit G x₀ := by
    intro i y hy
    have h1 := mem_orbit_of_mem_orbit_subgroup hy
    rw [orbit_eq_iff.mpr (hp i)] at h1
    exact h1
  have hfi : ∀ i, (orbit D (p i)).Finite := fun i => hfin.subset (hsub i)
  let O : Fin n → Finset X := fun i => (hfi i).toFinset
  have hO : ∀ i, (O i).card = (orbit D (p i)).ncard := fun i =>
    (Set.ncard_eq_toFinset_card _ (hfi i)).symm
  have hdis : (Set.univ : Set (Fin n)).PairwiseDisjoint O := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro y hyi hyj
    have hi : y ∈ orbit D (p i) := (hfi i).mem_toFinset.mp hyi
    have hj : y ∈ orbit D (p j) := (hfi j).mem_toFinset.mp hyj
    have e1 : orbit D y = orbit D (p i) := orbit_eq_iff.mpr hi
    have e2 : orbit D y = orbit D (p j) := orbit_eq_iff.mpr hj
    exact hdisj i j hij (by rw [← e1, e2]; exact mem_orbit_self _)
  have hU : (Finset.univ.biUnion O) ⊆ F := by
    intro y hy
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hy
    exact hfin.mem_toFinset.mpr (hsub i ((hfi i).mem_toFinset.mp hi))
  have hcardU : (Finset.univ.biUnion O).card = ∑ i, (orbit D (p i)).ncard := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdis (Set.mem_univ i) (Set.mem_univ j) hij)]
    exact Finset.sum_congr rfl fun i _ => hO i
  have hF' : F.card = (orbit G x₀).ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
  have horb := ncard_orbit_mul_card_stabilizer (⊤ : Subgroup G) x₀
  have hG : (orbit G x₀).ncard * Nat.card (stabilizer G x₀) = Nat.card G := by
    rw [← index_stabilizer, mul_comm, Subgroup.card_mul_index]
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hle2 : ∑ i, (orbit D (p i)).ncard ≤ (orbit G x₀).ncard := by
    rw [← hcardU, ← hF']
    exact Finset.card_le_card hU
  have hDH : Nat.card D ≤ Nat.card (stabilizer G x₀) := Subgroup.card_le_of_le hD
  have hopos : 0 < (orbit G x₀).ncard := (Set.ncard_pos hfin).mpr ⟨x₀, mem_orbit_self _⟩
  have h1 : Nat.card D * (orbit G x₀).ncard ≤ Nat.card G := by
    rw [← hG, mul_comm]
    exact Nat.mul_le_mul_left _ hDH
  have h2 : Nat.card G ≤ Nat.card D * (orbit G x₀).ncard :=
    hle.trans (Nat.mul_le_mul_left _ hle2)
  have hHD : Nat.card (stabilizer G x₀) ≤ Nat.card D := by
    have e : (orbit G x₀).ncard * Nat.card (stabilizer G x₀) ≤ (orbit G x₀).ncard * Nat.card D := by
      rw [hG, mul_comm]
      exact h2
    exact Nat.le_of_mul_le_mul_left e hopos
  refine ⟨(Subgroup.eq_of_le_of_card_ge hD hHD).symm, ?_⟩
  have hsum : ∑ i, (orbit D (p i)).ncard = (orbit G x₀).ncard := by
    refine le_antisymm hle2 ?_
    have e := hle.trans (le_of_eq rfl)
    have e2 : Nat.card D * (orbit G x₀).ncard ≤ Nat.card D * ∑ i, (orbit D (p i)).ncard :=
      h1.trans hle
    exact Nat.le_of_mul_le_mul_left e2 hpos
  have heq : Finset.univ.biUnion O = F :=
    Finset.eq_of_subset_of_card_le hU (by rw [hF', hcardU, hsum])
  intro x hx
  have hxF : x ∈ F := hfin.mem_toFinset.mpr hx
  rw [← heq] at hxF
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hxF
  exact ⟨i, (hfi i).mem_toFinset.mp hi⟩

theorem ncard_fix_mul_le (D : Subgroup G) [Finite D] (p : X) (x : D) (T : Finset D)
    (hT : ∀ t ∈ stabilizer D p, IsConj x t → t ∈ T) :
    {q ∈ orbit D p | x • q = q}.ncard * Nat.card (stabilizer D p) ≤
      Nat.card (Subgroup.centralizer ({x} : Set D)) * T.card := by
  classical
  have : Fintype D := Fintype.ofFinite D
  set S : Finset D := Finset.univ.filter (fun d => x • (d • p) = d • p) with hS
  have hfib : {q ∈ orbit D p | x • q = q}.ncard * Nat.card (stabilizer D p) = S.card := by
    have hfin : {q ∈ orbit D p | x • q = q}.Finite :=
      (Set.finite_range (fun d : D => d • p)).subset (fun q hq => hq.1)
    rw [Set.ncard_eq_toFinset_card _ hfin]
    have key : ∀ q ∈ hfin.toFinset,
        (S.filter (fun d => d • p = q)).card = Nat.card (stabilizer D p) := by
      intro q hq
      obtain ⟨hqo, hqx⟩ := hfin.mem_toFinset.mp hq
      obtain ⟨d₀, rfl⟩ := mem_orbit_iff.mp hqo
      have e : {d // d ∈ S.filter (fun d => d • p = d₀ • p)} ≃ stabilizer D p :=
        { toFun := fun d => ⟨d₀⁻¹ * d.1, by
            rw [mem_stabilizer_iff, mul_smul, (Finset.mem_filter.mp d.2).2, ← mul_smul,
              inv_mul_cancel, one_smul]⟩
          invFun := fun s => ⟨d₀ * s.1, by
            have hs : s.1 • p = p := s.2
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · rw [mul_smul, hs]
              exact hqx
            · rw [mul_smul, hs]⟩
          left_inv := fun d => Subtype.ext (by simp)
          right_inv := fun s => Subtype.ext (by simp) }
      rw [← Nat.card_eq_finsetCard, Nat.card_congr e]
    have hmapsto : ∀ d ∈ S, d • p ∈ hfin.toFinset := by
      intro d hd
      exact hfin.mem_toFinset.mpr ⟨mem_orbit _ _, (Finset.mem_filter.mp hd).2⟩
    rw [Finset.card_eq_sum_card_fiberwise hmapsto, Finset.sum_congr rfl key, Finset.sum_const,
      smul_eq_mul]
  have hcount : S.card ≤ Nat.card (Subgroup.centralizer ({x} : Set D)) * T.card := by
    have hmap : ∀ d ∈ S, d⁻¹ * x * d ∈ T := by
      intro d hd
      have hd' : x • (d • p) = d • p := (Finset.mem_filter.mp hd).2
      refine hT _ ?_ (isConj_iff.mpr ⟨d⁻¹, by rw [inv_inv]⟩)
      rw [mem_stabilizer_iff, mul_smul, mul_smul, hd', ← mul_smul, inv_mul_cancel, one_smul]
    have hfibre : ∀ t ∈ T, (S.filter (fun d => d⁻¹ * x * d = t)).card ≤
        Nat.card (Subgroup.centralizer ({x} : Set D)) := by
      intro t _
      rcases (S.filter (fun d => d⁻¹ * x * d = t)).eq_empty_or_nonempty with h | ⟨d₀, hd₀⟩
      · rw [h, Finset.card_empty]
        exact Nat.zero_le _
      · have e₀ : d₀⁻¹ * x * d₀ = t := (Finset.mem_filter.mp hd₀).2
        rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
        have hc : ∀ d ∈ S.filter (fun d => d⁻¹ * x * d = t),
            d * d₀⁻¹ ∈ Subgroup.centralizer ({x} : Set D) := by
          intro d hd
          have e : d⁻¹ * x * d = d₀⁻¹ * x * d₀ := (Finset.mem_filter.mp hd).2.trans e₀.symm
          rw [Subgroup.mem_centralizer_singleton_iff]
          have e2 : x * (d * d₀⁻¹) = d * d₀⁻¹ * x := by
            calc x * (d * d₀⁻¹) = d * (d⁻¹ * x * d) * d₀⁻¹ := by group
              _ = d * (d₀⁻¹ * x * d₀) * d₀⁻¹ := by rw [e]
              _ = d * d₀⁻¹ * x := by group
          exact e2.symm
        let f : D → Subgroup.centralizer ({x} : Set D) := fun d =>
          if h : d * d₀⁻¹ ∈ Subgroup.centralizer ({x} : Set D) then ⟨_, h⟩ else 1
        refine Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) ?_
        intro a ha b hb h
        have h' := congrArg Subtype.val h
        simp only [f, dif_pos (hc a ha), dif_pos (hc b hb)] at h'
        exact mul_right_cancel h'
    calc S.card = ∑ t ∈ T, (S.filter (fun d => d⁻¹ * x * d = t)).card :=
          Finset.card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ _t ∈ T, Nat.card (Subgroup.centralizer ({x} : Set D)) := Finset.sum_le_sum hfibre
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hfib]
  exact hcount

theorem card_centralizer_le [Finite G] (x₀ : X) (x : G) (hx : x • x₀ = x₀) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ≤
      {q ∈ orbit G x₀ | x • q = q}.ncard *
        Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ stabilizer G x₀) := by
  set C := Subgroup.centralizer ({x} : Set G)
  have h1 := ncard_orbit_mul_card_stabilizer C x₀
  have hsub : orbit C x₀ ⊆ {q ∈ orbit G x₀ | x • q = q} := by
    rintro q ⟨c, rfl⟩
    refine ⟨mem_orbit_of_mem_orbit_subgroup (mem_orbit _ _), ?_⟩
    have hc : c.1 * x = x * c.1 := Subgroup.mem_centralizer_singleton_iff.mp c.2
    change x • (c.1 • x₀) = c.1 • x₀
    rw [← mul_smul, ← hc, mul_smul, hx]
  have hfin : {q ∈ orbit G x₀ | x • q = q}.Finite :=
    (Set.finite_range (fun g : G => g • x₀)).subset (fun q hq => hq.1)
  have h2 : (orbit C x₀).ncard ≤ {q ∈ orbit G x₀ | x • q = q}.ncard := Set.ncard_le_ncard hsub hfin
  have e : stabilizer C x₀ ≃ ↥(C ⊓ stabilizer G x₀) :=
    { toFun := fun s => ⟨s.1.1, s.1.2, s.2⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      left_inv := fun s => rfl
      right_inv := fun g => rfl }
  rw [← h1, ← Nat.card_congr e]
  exact Nat.mul_le_mul_right _ h2

end CFSG.Certificates.ThDemp.OrbitCount

end
