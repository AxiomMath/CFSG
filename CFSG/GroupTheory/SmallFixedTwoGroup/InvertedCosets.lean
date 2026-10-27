module

public import CFSG.GroupTheory.SmallFixedTwoGroup.InvertedBasic

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

variable {G : Type*} [Group G]

open Subgroup

private lemma card_inverted_bound_le_centralizer {θ : MulAut G} {P : Subgroup G}
    (hPS : ∀ x ∈ P, θ x = x⁻¹) :
    P ≤ Subgroup.centralizer (P : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (mul_comm_of_apply_eq_inv hPS x hx y hy).symm

private lemma card_inverted_bound_fibre [Finite G] {θ : MulAut G} {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) (hPS : ∀ x ∈ P, θ x = x⁻¹)
    {s₀ : G} (hs₀ : θ s₀ = s₀⁻¹) (hs₀C : s₀ ∉ Subgroup.centralizer (P : Set G)) :
    p * Nat.card {s : G // θ s = s⁻¹ ∧ s₀⁻¹ * s ∈ P} ≤ Nat.card P := by
  classical
  let D : Subgroup P := (Subgroup.centralizer ({s₀} : Set G)).comap P.subtype
  have hle1 : Nat.card {s : G // θ s = s⁻¹ ∧ s₀⁻¹ * s ∈ P} ≤ Nat.card D := by
    let f : {s : G // θ s = s⁻¹ ∧ s₀⁻¹ * s ∈ P} → D := fun s =>
      ⟨⟨s₀⁻¹ * s.1, s.2.2⟩, by
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        have key : θ (s₀ * (s₀⁻¹ * s.1)) = (s₀ * (s₀⁻¹ * s.1))⁻¹ := by
          rw [mul_inv_cancel_left]
          exact s.2.1
        exact (inverted_mul_iff_commute hs₀ (hPS _ s.2.2)).1 key⟩
    refine Nat.card_le_card_of_injective f ?_
    intro a b hab
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val (congrArg Subtype.val hab))
  have hle2 : Nat.card D ≤ Nat.card {s : G // θ s = s⁻¹ ∧ s₀⁻¹ * s ∈ P} := by
    let f : D → {s : G // θ s = s⁻¹ ∧ s₀⁻¹ * s ∈ P} := fun x =>
      ⟨s₀ * (x.1 : G), by
        have hx : (x.1 : G) ∈ Subgroup.centralizer ({s₀} : Set G) :=
          Subgroup.mem_comap.mp x.2
        rw [Subgroup.mem_centralizer_iff] at hx
        exact (inverted_mul_iff_commute hs₀ (hPS _ x.1.2)).2
          (hx s₀ (Set.mem_singleton s₀)),
      by
        rw [inv_mul_cancel_left]
        exact x.1.2⟩
    refine Nat.card_le_card_of_injective f ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val hab)
  have hcard : Nat.card {s : G // θ s = s⁻¹ ∧ s₀⁻¹ * s ∈ P} = Nat.card D :=
    le_antisymm hle1 hle2
  have hDne : D ≠ ⊤ := by
    rw [Subgroup.mem_centralizer_iff] at hs₀C
    push Not at hs₀C
    obtain ⟨y, hyP, hyne⟩ := hs₀C
    intro htop
    have hyD : (⟨y, hyP⟩ : P) ∈ D := by rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hyD
    exact hyne (hyD s₀ (Set.mem_singleton s₀)).symm
  obtain ⟨n, hn⟩ := hP.index D
  have hDne1 : D.index ≠ 1 := fun h => hDne (Subgroup.index_eq_one.mp h)
  have hn0 : n ≠ 0 := by
    intro hn0
    exact hDne1 (by rw [hn, hn0, pow_zero])
  have hpdvd : p ∣ D.index := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    refine ⟨p ^ m, ?_⟩
    rw [hn, pow_succ]
    exact mul_comm _ _
  have hDindex_pos : 0 < D.index := by
    rcases Nat.eq_zero_or_pos D.index with h | h
    · exfalso
      have hc := D.card_mul_index
      rw [h, mul_zero] at hc
      exact Nat.card_pos.ne' hc.symm
    · exact h
  have hp_le : p ≤ D.index := Nat.le_of_dvd hDindex_pos hpdvd
  have hDbound : p * Nat.card D ≤ Nat.card P := by
    calc p * Nat.card D = Nat.card D * p := by rw [mul_comm]
      _ ≤ Nat.card D * D.index := Nat.mul_le_mul_left _ hp_le
      _ = Nat.card P := D.card_mul_index
  calc p * Nat.card {s : G // θ s = s⁻¹ ∧ s₀⁻¹ * s ∈ P}
      = p * Nat.card D := by rw [hcard]
    _ ≤ Nat.card P := hDbound

private lemma card_inverted_bound_fibre_g [Finite G] {θ : MulAut G} {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) (hPS : ∀ x ∈ P, θ x = x⁻¹)
    (g : {g : G // g ∉ Subgroup.centralizer (P : Set G)}) :
    p * Nat.card {s : G // θ s = s⁻¹ ∧ s ∉ Subgroup.centralizer (P : Set G) ∧
        s⁻¹ * g.1 ∈ P} ≤ Nat.card P := by
  classical
  by_cases hne : Nonempty {s : G // θ s = s⁻¹ ∧ s ∉ Subgroup.centralizer (P : Set G) ∧
      s⁻¹ * g.1 ∈ P}
  · obtain ⟨s₀, hs₀⟩ := hne
    have hle : Nat.card {s : G // θ s = s⁻¹ ∧ s ∉ Subgroup.centralizer (P : Set G) ∧
          s⁻¹ * g.1 ∈ P} ≤ Nat.card {s : G // θ s = s⁻¹ ∧ s₀⁻¹ * s ∈ P} := by
      let f : {s : G // θ s = s⁻¹ ∧ s ∉ Subgroup.centralizer (P : Set G) ∧
            s⁻¹ * g.1 ∈ P} → {s : G // θ s = s⁻¹ ∧ s₀⁻¹ * s ∈ P} := fun s =>
        ⟨s.1, s.2.1, by
          have h1 : s₀⁻¹ * s.1 = (s₀⁻¹ * g.1) * (s.1⁻¹ * g.1)⁻¹ := by group
          rw [h1]
          exact P.mul_mem hs₀.2.2 (P.inv_mem s.2.2.2)⟩
      refine Nat.card_le_card_of_injective f ?_
      intro a b hab
      exact Subtype.ext (congrArg
        (fun x : {s : G // θ s = s⁻¹ ∧ s₀⁻¹ * s ∈ P} => (x : G)) hab)
    calc p * Nat.card {s : G // θ s = s⁻¹ ∧ s ∉ Subgroup.centralizer (P : Set G) ∧
            s⁻¹ * g.1 ∈ P}
        ≤ p * Nat.card {s : G // θ s = s⁻¹ ∧ s₀⁻¹ * s ∈ P} := Nat.mul_le_mul_left p hle
      _ ≤ Nat.card P := card_inverted_bound_fibre hP hPS hs₀.1 hs₀.2.1
  · haveI : IsEmpty {s : G // θ s = s⁻¹ ∧ s ∉ Subgroup.centralizer (P : Set G) ∧
        s⁻¹ * g.1 ∈ P} := ⟨fun x => hne ⟨x⟩⟩
    haveI : Fintype {s : G // θ s = s⁻¹ ∧ s ∉ Subgroup.centralizer (P : Set G) ∧
        s⁻¹ * g.1 ∈ P} := Fintype.ofFinite _
    have h0 : Nat.card {s : G // θ s = s⁻¹ ∧ s ∉ Subgroup.centralizer (P : Set G) ∧
        s⁻¹ * g.1 ∈ P} = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_eq_zero_iff.mpr inferInstance
    rw [h0, mul_zero]
    exact Nat.zero_le _

private lemma card_inverted_bound_fibre_card [Finite G] {P : Subgroup G}
    (hPC : P ≤ Subgroup.centralizer (P : Set G)) {s : G}
    (hsC : s ∉ Subgroup.centralizer (P : Set G)) :
    Nat.card {g : {g : G // g ∉ Subgroup.centralizer (P : Set G)} // s⁻¹ * g.1 ∈ P} =
      Nat.card P := by
  classical
  refine Nat.card_congr ?_
  refine
    { toFun := fun g => ⟨s⁻¹ * g.1.1, g.2⟩
      invFun := fun h => ⟨⟨s * h.1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro hc
    exact hsC (by
      have hmem : (s * h.1) * h.1⁻¹ ∈ Subgroup.centralizer (P : Set G) :=
        (Subgroup.centralizer (P : Set G)).mul_mem hc
          ((Subgroup.centralizer (P : Set G)).inv_mem (hPC h.2))
      rwa [mul_assoc, mul_inv_cancel, mul_one] at hmem)
  · rw [inv_mul_cancel_left]
    exact h.2
  · intro g
    apply Subtype.ext
    apply Subtype.ext
    simp [mul_inv_cancel_left]
  · intro h
    apply Subtype.ext
    simp [inv_mul_cancel_left]

theorem card_inverted_bound [Finite G] {θ : MulAut G} {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) (hPS : ∀ x ∈ P, θ x = x⁻¹) :
    p * Nat.card {g : G // θ g = g⁻¹} + Nat.card (centralizer (P : Set G)) ≤
      p * Nat.card (centralizer (P : Set G)) + Nat.card G := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hPC : P ≤ centralizer (P : Set G) := card_inverted_bound_le_centralizer hPS
  set nS : ℕ := Nat.card {g : G // θ g = g⁻¹} with hnS
  set nC : ℕ := Nat.card (centralizer (P : Set G)) with hnC
  set nG : ℕ := Nat.card G with hnG
  haveI : Nonempty P := ⟨1⟩
  set nP : ℕ := Nat.card P with hnP
  let T := {s : G // θ s = s⁻¹ ∧ s ∉ centralizer (P : Set G)}
  let GC := {g : G // g ∉ centralizer (P : Set G)}
  let Z := {p : T × GC // p.1.1⁻¹ * p.2.1 ∈ P}
  set nT : ℕ := Nat.card T with hnT
  haveI : Fintype T := Fintype.ofFinite T
  haveI : Fintype GC := Fintype.ofFinite GC
  haveI : Fintype Z := Fintype.ofFinite Z
  have hZcol : Nat.card Z = nT * nP := by
    rw [hnT, hnP]
    calc Nat.card Z
        = Nat.card (Σ s : T, {g : GC // s.1⁻¹ * g.1 ∈ P}) :=
          Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
            (fun (s : T) (g : GC) => s.1⁻¹ * g.1 ∈ P))
      _ = ∑ s : T, Nat.card {g : GC // s.1⁻¹ * g.1 ∈ P} := Nat.card_sigma
      _ = ∑ _s : T, Nat.card P := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          exact card_inverted_bound_fibre_card hPC s.2.2
      _ = Nat.card T * Nat.card P := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Nat.card_eq_fintype_card (α := T), Nat.cast_id]
  have hZrow : Nat.card Z = ∑ g : GC, Nat.card {s : T // s.1⁻¹ * g.1 ∈ P} := by
    calc Nat.card Z
        = Nat.card (Σ g : GC, {s : T // s.1⁻¹ * g.1 ∈ P}) :=
          Nat.card_congr
            { toFun := fun z => ⟨z.1.2, ⟨z.1.1, z.2⟩⟩
              invFun := fun x => ⟨(x.2.1, x.1), x.2.2⟩
              left_inv := by intro z; rfl
              right_inv := by intro x; rfl }
      _ = ∑ g : GC, Nat.card {s : T // s.1⁻¹ * g.1 ∈ P} := Nat.card_sigma
  have hfib : ∀ g : GC, p * Nat.card {s : T // s.1⁻¹ * g.1 ∈ P} ≤ nP := by
    intro g
    rw [hnP]
    have hEq : Nat.card {s : T // s.1⁻¹ * g.1 ∈ P} =
        Nat.card {s : G // θ s = s⁻¹ ∧ s ∉ centralizer (P : Set G) ∧ s⁻¹ * g.1 ∈ P} :=
      Nat.card_congr
        { toFun := fun s => ⟨s.1.1, s.1.2.1, s.1.2.2, s.2⟩
          invFun := fun s => ⟨⟨s.1, s.2.1, s.2.2.1⟩, s.2.2.2⟩
          left_inv := by intro s; rfl
          right_inv := by intro s; rfl }
    rw [hEq]
    exact card_inverted_bound_fibre_g hP hPS g
  have hGC : Nat.card GC = nG - nC := by
    rw [hnG, hnC]
    have h := Fintype.card_subtype_compl (fun g : G => g ∈ centralizer (P : Set G))
    simpa only [Nat.card_eq_fintype_card] using h
  have hnPpos : 0 < nP := by rw [hnP]; exact Nat.card_pos
  have hmain : p * nT * nP ≤ (nG - nC) * nP := by
    have hstep : p * Nat.card Z =
        ∑ g : GC, p * Nat.card {s : T // s.1⁻¹ * g.1 ∈ P} := by
      rw [hZrow, Finset.mul_sum]
    calc p * nT * nP = p * Nat.card Z := by rw [hZcol, mul_assoc]
      _ = ∑ g : GC, p * Nat.card {s : T // s.1⁻¹ * g.1 ∈ P} := hstep
      _ ≤ ∑ _g : GC, nP := Finset.sum_le_sum (fun g _ => hfib g)
      _ = Nat.card GC * nP := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Nat.card_eq_fintype_card (α := GC), Nat.cast_id]
      _ = (nG - nC) * nP := by rw [hGC]
  have hkey : p * nT ≤ nG - nC := Nat.le_of_mul_le_mul_right hmain hnPpos
  have hnC_le : nC ≤ nG := by
    rw [hnC, hnG]
    exact Nat.card_le_card_of_injective (fun x : centralizer (P : Set G) => (x : G))
      Subtype.coe_injective
  have hTnC : p * nT + nC ≤ nG := by
    have h := Nat.add_le_add_right hkey nC
    rwa [Nat.sub_add_cancel hnC_le] at h
  have hnS_le : nS ≤ nT + nC := by
    rw [hnS, hnT, hnC]
    calc Nat.card {g : G // θ g = g⁻¹}
        ≤ Nat.card (T ⊕ (centralizer (P : Set G))) := by
          refine Nat.card_le_card_of_injective
            (fun s : {g : G // θ g = g⁻¹} =>
              if hs : s.1 ∈ centralizer (P : Set G)
              then Sum.inr (⟨s.1, hs⟩ : centralizer (P : Set G))
              else Sum.inl (⟨s.1, s.2, hs⟩ : T)) ?_
          intro a b hab
          dsimp only at hab
          by_cases ha : a.1 ∈ centralizer (P : Set G) <;>
            by_cases hb : b.1 ∈ centralizer (P : Set G)
          · rw [dif_pos ha, dif_pos hb] at hab
            have h2 : (⟨a.1, ha⟩ : centralizer (P : Set G)) = ⟨b.1, hb⟩ :=
              Sum.inr.inj hab
            exact Subtype.ext (congrArg (fun x : centralizer (P : Set G) => (x : G)) h2)
          · rw [dif_pos ha, dif_neg hb] at hab
            cases hab
          · rw [dif_neg ha, dif_pos hb] at hab
            cases hab
          · rw [dif_neg ha, dif_neg hb] at hab
            have h2 : (⟨a.1, a.2, ha⟩ : T) = ⟨b.1, b.2, hb⟩ := Sum.inl.inj hab
            exact Subtype.ext (congrArg (fun x : T => (x : G)) h2)
      _ = Nat.card T + Nat.card (centralizer (P : Set G)) := Nat.card_sum
  calc p * nS + nC
      ≤ p * (nT + nC) + nC := Nat.add_le_add_right (Nat.mul_le_mul_left p hnS_le) nC
    _ = (p * nT + nC) + p * nC := by rw [Nat.mul_add]; ring
    _ ≤ nG + p * nC := Nat.add_le_add_right hTnC (p * nC)
    _ = p * nC + nG := by rw [Nat.add_comm]

end CFSG.GroupTheory.SmallFixedTwoGroup
