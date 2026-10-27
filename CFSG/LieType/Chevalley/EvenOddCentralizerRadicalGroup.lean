module

public import CFSG.GroupTheory.SolvableHallNodes
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open scoped Pointwise

variable {G : Type*} [Group G]

theorem le_normalizer_of_conj_mem {H X : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ H, x * y * x⁻¹ ∈ H) :
    X ≤ Subgroup.normalizer (H : Set G) := fun x hx => by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h x hx y, fun hy => ?_⟩
  have := h x⁻¹ (inv_mem hx) _ hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this

theorem exists_conj_le_of_complement [Finite G] {p : ℕ} [Fact p.Prime] {P Q M S : Subgroup G}
    (hQp : IsPGroup p Q) (hQP : Q ≤ P) (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hQM : Q ⊓ M = ⊥) (hdec : ∀ g ∈ P, ∃ q ∈ Q, ∃ m ∈ M, q * m = g) (hSP : S ≤ P)
    (hS : ¬ p ∣ Nat.card S) : ∃ y ∈ Q, S.map (MulAut.conj y).toMonoidHom ≤ M := by
  classical
  set F := Q ⊔ S with hF
  have hQF : Q ≤ F := le_sup_left
  have hSF : S ≤ F := le_sup_right
  have hFP : F ≤ P := sup_le hQP hSP
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card S) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQp
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hS)
  have hQS : Q ⊓ S = ⊥ := disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard hcop)
  have hprod : (F : Set G) = (Q : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q S (hSP.trans hPQ)
  have hNn : (Q.subgroupOf F).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQF).2 (hFP.trans hPQ)
  have hNH : ((Q.subgroupOf F : Subgroup F) : Set F) * ((S.subgroupOf F : Subgroup F) : Set F) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun f => ?_
    have hf : (f : G) ∈ (Q : Set G) * (S : Set G) := by rw [← hprod]; exact f.2
    obtain ⟨q, hq, s, hs, hqs⟩ := hf
    exact ⟨⟨q, hQF hq⟩, Subgroup.mem_subgroupOf.2 hq, ⟨s, hSF hs⟩, Subgroup.mem_subgroupOf.2 hs,
      Subtype.ext hqs⟩
  have hNK : ((Q.subgroupOf F : Subgroup F) : Set F) * ((M.subgroupOf F : Subgroup F) : Set F) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun f => ?_
    obtain ⟨q, hq, m, hm, hqm⟩ := hdec f (hFP f.2)
    have hmF : m ∈ F := by
      have e : m = q⁻¹ * f := by rw [← hqm]; group
      rw [e]
      exact mul_mem (inv_mem (hQF hq)) f.2
    exact ⟨⟨q, hQF hq⟩, Subgroup.mem_subgroupOf.2 hq, ⟨m, hmF⟩, Subgroup.mem_subgroupOf.2 hm,
      Subtype.ext hqm⟩
  have hinf : ∀ {X : Subgroup G}, Q ⊓ X = ⊥ → Q.subgroupOf F ⊓ X.subgroupOf F = ⊥ := by
    intro X hX
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : (x : G) ∈ Q ⊓ X := Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1
      (Subgroup.mem_inf.1 hx).1, Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hx).2⟩
    rw [hX] at hx'
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hx'))
  have hsolv : Group.IsSolvable (Q.subgroupOf F) := by
    have hp : IsPGroup p (Q.subgroupOf F) := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQF).symm
    have := hp.isNilpotent
    infer_instance
  have hcop' : Nat.Coprime (Nat.card (Q.subgroupOf F)) (Q.subgroupOf F).index := by
    have hc : Subgroup.IsComplement' (Q.subgroupOf F) (S.subgroupOf F) :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 (hinf hQS)) hNH
    have h1 := hc.card_mul_card
    have h2 := (Q.subgroupOf F).card_mul_index
    have hidx : (Q.subgroupOf F).index = Nat.card (S.subgroupOf F) :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSF).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQF).toEquiv]
    exact hcop
  obtain ⟨n, hn, hK⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy
    (Q.subgroupOf F) hsolv hcop' hNH hNK (hinf hQS) (hinf hQM)
  refine ⟨((n⁻¹ : F) : G), Subgroup.mem_subgroupOf.1 (inv_mem hn), ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hmem : (MulAut.conj n⁻¹).toMonoidHom (⟨s, hSF hs⟩ : F) ∈ M.subgroupOf F := by
    rw [hK]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
  have h := Subgroup.mem_subgroupOf.1 hmem
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
  exact h

theorem exists_invariant_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {C S N : Subgroup G}
    (hSC : S ≤ Subgroup.normalizer (C : Set G)) (hNC : N ≤ C)
    (hCN : C ≤ Subgroup.normalizer (N : Set G)) (hNp : IsPGroup p N) (hN : N ≠ ⊥) :
    ∃ R : Subgroup G, R ≤ C ∧ C ≤ Subgroup.normalizer (R : Set G) ∧
      S ≤ Subgroup.normalizer (R : Set G) ∧ IsPGroup p R ∧ R ≠ ⊥ := by
  classical
  let Ns : S → Subgroup G := fun s => N.map (MulAut.conj (s : G)).toMonoidHom
  have hconj : ∀ (s : S) (y : G), y ∈ Ns s ↔ ∃ n ∈ N, (s : G) * n * (s : G)⁻¹ = y := fun s y =>
    Iff.rfl
  have hsC : ∀ (s : S), ∀ c ∈ C, (s : G)⁻¹ * c * (s : G) ∈ C := fun s c hc => by
    have := (Subgroup.mem_normalizer_iff.1 (hSC (inv_mem s.2)) c).1 hc
    rwa [inv_inv] at this
  have hNsC : ∀ s : S, Ns s ≤ C := fun s y hy => by
    obtain ⟨n, hn, rfl⟩ := (hconj s y).1 hy
    exact (Subgroup.mem_normalizer_iff.1 (hSC s.2) n).1 (hNC hn)
  have hCNs : ∀ s : S, C ≤ Subgroup.normalizer (Ns s : Set G) := fun s =>
    le_normalizer_of_conj_mem fun c hc y hy => by
      obtain ⟨n, hn, rfl⟩ := (hconj s y).1 hy
      refine (hconj s _).2 ⟨((s : G)⁻¹ * c * s) * n * ((s : G)⁻¹ * c * s)⁻¹,
        (Subgroup.mem_normalizer_iff.1 (hCN (hsC s c hc)) n).1 hn, by group⟩
  set R := ⨆ s : S, Ns s with hR
  have hNsR : ∀ s : S, Ns s ≤ R := fun s => le_iSup Ns s
  refine ⟨R, iSup_le hNsC, le_normalizer_of_conj_mem fun c hc y hy => ?_,
    le_normalizer_of_conj_mem fun s' hs' y hy => ?_, ?_, ?_⟩
  · refine Subgroup.iSup_induction Ns (C := fun y => c * y * c⁻¹ ∈ R) hy (fun s y hy => ?_)
      (by rw [mul_one, mul_inv_cancel]; exact one_mem _) (fun x y hx hy => ?_)
    · exact hNsR s ((Subgroup.mem_normalizer_iff.1 (hCNs s hc) y).1 hy)
    · rw [show c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) by group]
      exact mul_mem hx hy
  · refine Subgroup.iSup_induction Ns (C := fun y => s' * y * s'⁻¹ ∈ R) hy (fun s y hy => ?_)
      (by rw [mul_one, mul_inv_cancel]; exact one_mem _) (fun x y hx hy => ?_)
    · obtain ⟨n, hn, rfl⟩ := (hconj s y).1 hy
      refine hNsR ⟨s' * s, mul_mem hs' s.2⟩ ((hconj _ _).2 ⟨n, hn, ?_⟩)
      change s' * s * n * (s' * s)⁻¹ = s' * (s * n * (s : G)⁻¹) * s'⁻¹
      group
    · rw [show s' * (x * y) * s'⁻¹ = (s' * x * s'⁻¹) * (s' * y * s'⁻¹) by group]
      exact mul_mem hx hy
  ·
    let _ : Fintype S := Fintype.ofFinite S
    have key : ∀ T : Finset S, IsPGroup p ↥(⨆ s ∈ T, Ns s) := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        have h0 : (⨆ s ∈ (∅ : Finset S), Ns s) = ⊥ := by simp
        rw [h0]
        exact IsPGroup.of_bot
      | insert a T ha ih =>
        rw [Finset.iSup_insert]
        have hNa : IsPGroup p (Ns a) := hNp.map _
        exact hNa.to_sup_of_normal_left' ih
          ((iSup₂_le fun s _ => hNsC s).trans (hCNs a))
    have h0 : (⨆ s ∈ (Finset.univ : Finset S), Ns s) = R := by simp [hR]
    have := key Finset.univ
    rw [h0] at this
    exact this
  · intro h0
    apply hN
    rw [eq_bot_iff]
    intro n hn
    have : n ∈ R := hNsR 1 ((hconj 1 n).2 ⟨n, hn, by simp⟩)
    rw [h0] at this
    exact this

theorem exists_fixed_ne_one [Finite G] {X : Subgroup G} (hX : IsPGroup 2 X) (hX1 : X ≠ ⊥)
    (f : G →* G) (hf : ∀ x ∈ X, f x ∈ X) (hff : ∀ x ∈ X, f (f x) = x) :
    ∃ w ∈ X, w ≠ 1 ∧ f w = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype X := Fintype.ofFinite X
  let φ : Function.End X := fun x => ⟨f x, hf x x.2⟩
  have hφ : φ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext x
    exact Subtype.ext (hff x x.2)
  have hmod := Equiv.Perm.card_fixedPoints_modEq hφ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hX
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hX1 ((Subgroup.card_eq_one).1 hk)
  have heven : Fintype.card X ≡ 0 [MOD 2] := by
    rw [Fintype.card_eq_nat_card, hk]
    exact (Nat.modEq_zero_iff_dvd).2 (dvd_pow_self 2 hk0)
  have hfix : Fintype.card φ.fixedPoints ≡ 0 [MOD 2] := hmod.symm.trans heven
  have h1 : (1 : X) ∈ φ.fixedPoints := Subtype.ext (map_one f)
  have hcard : 1 < Fintype.card φ.fixedPoints := by
    have hpos : 0 < Fintype.card φ.fixedPoints := Fintype.card_pos_iff.2 ⟨⟨1, h1⟩⟩
    have := (Nat.modEq_zero_iff_dvd).1 hfix
    omega
  obtain ⟨⟨w, hw⟩, hw1⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨1, h1⟩
  refine ⟨w, w.2, fun h => hw1 (Subtype.ext (Subtype.ext h)), congrArg Subtype.val hw⟩

end CFSG.LieType.Chevalley.EvenOddRadical
