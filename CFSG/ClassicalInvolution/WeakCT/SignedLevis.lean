module

public import CFSG.ClassicalInvolution.WeakCT.EdgeSL3
public import CFSG.ClassicalInvolution.WeakCT.SL3Injective

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open scoped commutatorElement MatrixGroups

section SL2SL2

variable {F : Type} [Field F] {H : Type*} [Group H]

theorem injective_noncommCoprod' {φ ψ : SL(2, F) →* H} (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (hc : ∀ a b, Commute (φ a) (ψ b))
    (hZ : ∀ a b : SL(2, F), a ∈ Subgroup.center SL(2, F) → b ∈ Subgroup.center SL(2, F) →
      φ a = ψ b → φ a = 1) :
    Function.Injective (φ.noncommCoprod ψ hc) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ h
  rw [MonoidHom.noncommCoprod_apply] at h
  have e : φ a = ψ b⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
  have ha : a ∈ Subgroup.center SL(2, F) :=
    Subgroup.mem_center_iff.2 fun y => hφ (by rw [map_mul, map_mul, e]; exact (hc y b⁻¹).eq)
  have hb : b⁻¹ ∈ Subgroup.center SL(2, F) :=
    Subgroup.mem_center_iff.2 fun y => hψ (by rw [map_mul, map_mul, ← e]; exact (hc a y).symm.eq)
  have ha1 : a = 1 := (injective_iff_map_eq_one φ).1 hφ a (hZ a b⁻¹ ha hb e)
  rw [ha1, map_one] at e
  have hb1 : b⁻¹ = 1 := (injective_iff_map_eq_one ψ).1 hψ _ e.symm
  rw [ha1, inv_eq_one.1 hb1]
  rfl

end SL2SL2

section Levis

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {i j : Fin D.rank}

theorem exists_sl2sl2 (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hij : i ≠ j) (hcij : D.cartan i j = 0) (hcji : D.cartan j i = 0)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k) :
    ∃ l : SL(2, F) × SL(2, F) →* K, Function.Injective l ∧ ∀ c, l (tv 0 1 c, 1) = x (sroot i) c ∧
      l (tv 1 0 c, 1) = x (-sroot i) c ∧ l (1, tv 0 1 c) = x (sroot j) c ∧
      l (1, tv 1 0 c) = x (-sroot j) c := by
  obtain ⟨φ, hφ, hupφ, hlowφ, hsqφ⟩ := weylElement_one_sq hE i
  obtain ⟨ψ, hψ, hupψ, hlowψ, hsqψ⟩ := weylElement_one_sq hE j
  have hc : ∀ a b, Commute (φ a) (ψ b) := commute_of_tv φ ψ fun c d => by
    rw [tv01_eq_sl2Upper, tv10_eq_sl2Lower, tv01_eq_sl2Upper, tv10_eq_sl2Lower, hupφ, hlowφ,
      hupψ, hlowψ]
    exact commute_nonadj hE hdiv hij hcij hcji c d
  have hcenter : ∀ (k : Fin D.rank) (θ : SL(2, F) →* K),
      θ (wS (1 : Fˣ) * wS (1 : Fˣ)) = Steinberg.weylElement x k 1 ^ 2 →
        ∀ a : SL(2, F), a ∈ Subgroup.center SL(2, F) → θ a ∈ H k := by
    intro k θ hθ a ha
    rcases eq_one_or_eq_sq_of_mem_center ha with rfl | rfl
    · rw [map_one]
      exact one_mem _
    · rw [hθ]
      exact hsq k
  refine ⟨φ.noncommCoprod ψ hc, injective_noncommCoprod' hφ hψ hc ?_, fun c => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro a b ha hb hab
    have hi : φ a ∈ H i := hcenter i φ hsqφ.symm a ha
    have hj : φ a ∈ H j := by
      rw [hab]
      exact hcenter j ψ hsqψ.symm b hb
    have hdis := hind i
    rw [Subgroup.disjoint_def] at hdis
    exact hdis hi (Subgroup.mem_iSup_of_mem j (Subgroup.mem_iSup_of_mem hij.symm hj))
  · rw [MonoidHom.noncommCoprod_apply, map_one, mul_one, tv01_eq_sl2Upper, hupφ]
  · rw [MonoidHom.noncommCoprod_apply, map_one, mul_one, tv10_eq_sl2Lower, hlowφ]
  · rw [MonoidHom.noncommCoprod_apply, map_one, one_mul, tv01_eq_sl2Upper, hupψ]
  · rw [MonoidHom.noncommCoprod_apply, map_one, one_mul, tv10_eq_sl2Lower, hlowψ]

end Levis

section Signs

variable {F : Type} [Field F] {r : ℕ} (C : (Fin r → ℤ) → (Fin r → ℤ) → ℕ × ℕ → ℤ)
  (adj : Fin r → Fin r → Prop)

open Classical in
@[expose] noncomputable def edgeSign (F : Type) [Field F] (γ : Fin r → ℤ) : F :=
  if h : ∃ q : Fin r × Fin r, adj q.1 q.2 ∧ γ = sroot q.1 + sroot q.2 then
    epsPos F C (Classical.choose h).1 (Classical.choose h).2
  else if h : ∃ q : Fin r × Fin r, adj q.1 q.2 ∧ γ = -(sroot q.1 + sroot q.2) then
    epsNeg F C (Classical.choose h).1 (Classical.choose h).2
  else 1

variable {C adj}

theorem edgeSign_pos (hasymm : ∀ i j, adj i j → ¬ adj j i) (hne : ∀ i j, adj i j → i ≠ j)
    {i j : Fin r} (hij : adj i j) :
    edgeSign C adj F (sroot i + sroot j) = epsPos F C i j := by
  have h : ∃ q : Fin r × Fin r, adj q.1 q.2 ∧ sroot i + sroot j = sroot q.1 + sroot q.2 :=
    ⟨(i, j), hij, rfl⟩
  rw [edgeSign, dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hq, hs⟩ := Classical.choose_spec h
  rcases eq_of_add_eq_add (hne i j hij) hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · exact absurd hij (hasymm _ _ (by rwa [h1, h2] at hq))

theorem edgeSign_neg (hasymm : ∀ i j, adj i j → ¬ adj j i) (hne : ∀ i j, adj i j → i ≠ j)
    {i j : Fin r} (hij : adj i j) :
    edgeSign C adj F (-(sroot i + sroot j)) = epsNeg F C i j := by
  have h1 : ¬ ∃ q : Fin r × Fin r, adj q.1 q.2 ∧ -(sroot i + sroot j) = sroot q.1 + sroot q.2 := by
    rintro ⟨q, hq, h⟩
    exact add_ne_neg_add (hne _ _ hq) i j h.symm
  have h : ∃ q : Fin r × Fin r, adj q.1 q.2 ∧
      -(sroot i + sroot j) = -(sroot q.1 + sroot q.2) := ⟨(i, j), hij, rfl⟩
  rw [edgeSign, dite_eq_right_of_eq_false (eq_false h1), dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hq, hs⟩ := Classical.choose_spec h
  rcases eq_of_add_eq_add (hne i j hij) (neg_injective hs) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · exact absurd hij (hasymm _ _ (by rwa [h1, h2] at hq))

theorem edgeSign_single (hne : ∀ i j, adj i j → i ≠ j) (k : Fin r) :
    edgeSign C adj F (sroot k) = 1 ∧ edgeSign C adj F (-sroot k) = 1 := by
  have h1 : ¬ ∃ q : Fin r × Fin r, adj q.1 q.2 ∧ sroot k = sroot q.1 + sroot q.2 := by
    rintro ⟨q, hq, h⟩
    exact sroot_ne_add (hne _ _ hq) k h
  have h2 : ¬ ∃ q : Fin r × Fin r, adj q.1 q.2 ∧ sroot k = -(sroot q.1 + sroot q.2) := by
    rintro ⟨q, hq, h⟩
    exact sroot_ne_neg_add (hne _ _ hq) k h
  have h3 : ¬ ∃ q : Fin r × Fin r, adj q.1 q.2 ∧ -sroot k = sroot q.1 + sroot q.2 := by
    rintro ⟨q, hq, h⟩
    exact neg_sroot_ne_add (hne _ _ hq) k h
  have h4 : ¬ ∃ q : Fin r × Fin r, adj q.1 q.2 ∧ -sroot k = -(sroot q.1 + sroot q.2) := by
    rintro ⟨q, hq, h⟩
    exact neg_sroot_ne_neg_add (hne _ _ hq) k h
  constructor
  · rw [edgeSign, dite_eq_right_of_eq_false (eq_false h1),
      dite_eq_right_of_eq_false (eq_false h2)]
  · rw [edgeSign, dite_eq_right_of_eq_false (eq_false h3),
      dite_eq_right_of_eq_false (eq_false h4)]

theorem edgeSign_cases (γ : Fin r → ℤ) :
    (∃ i j, adj i j ∧ edgeSign C adj F γ = epsPos F C i j) ∨
      (∃ i j, adj i j ∧ edgeSign C adj F γ = epsNeg F C i j) ∨ edgeSign C adj F γ = 1 := by
  by_cases h1 : ∃ q : Fin r × Fin r, adj q.1 q.2 ∧ γ = sroot q.1 + sroot q.2
  · left
    exact ⟨_, _, (Classical.choose_spec h1).1, by
      rw [edgeSign, dite_eq_left_of_eq_true (eq_true h1)]⟩
  · by_cases h2 : ∃ q : Fin r × Fin r, adj q.1 q.2 ∧ γ = -(sroot q.1 + sroot q.2)
    · right
      left
      exact ⟨_, _, (Classical.choose_spec h2).1, by
        rw [edgeSign, dite_eq_right_of_eq_false (eq_false h1),
          dite_eq_left_of_eq_true (eq_true h2)]⟩
    · right
      right
      rw [edgeSign, dite_eq_right_of_eq_false (eq_false h1),
        dite_eq_right_of_eq_false (eq_false h2)]

end Signs

section Main

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem exists_simplyLacedLevis [Finite F] (hE : Steinberg.ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1)
    {adj : Fin D.rank → Fin D.rank → Prop} (hasymm : ∀ i j, adj i j → ¬ adj j i)
    (hadj : ∀ i j, adj i j → D.cartan i j = -1 ∧ D.cartan j i = -1)
    (hnadj : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → D.cartan i j = 0 ∧ D.cartan j i = 0)
    (hnb : ∀ i j, adj i j → ∃ k, k ≠ i ∧ k ≠ j ∧
      ((adj j k ∨ adj k j) ∧ ¬ adj i k ∧ ¬ adj k i ∨
        (adj i k ∨ adj k i) ∧ ¬ adj j k ∧ ¬ adj k j))
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k) :
    ∃ x' : (Fin D.rank → ℤ) → F → K, SimplyLacedLevis D F adj x' ∧
      ∀ k c, x' (sroot k) c = x (sroot k) c ∧ x' (-sroot k) c = x (-sroot k) c := by
  classical
  have hne : ∀ i j, adj i j → i ≠ j := fun i j h e => by
    subst e
    have := (hadj i i h).1
    rw [D.isFiniteType.apply_self] at this
    norm_num at this
  have hsl3 := fun i j (h : adj i j) =>
    exists_sl3_signed hE hC hdiv (hne i j h) (hadj i j h).1 (hadj i j h).2
  have hcomm := fun i j (hij : i ≠ j) (h1 : ¬ adj i j) (h2 : ¬ adj j i) =>
    commute_nonadj hE hdiv hij (hnadj i j hij h1 h2).1 (hnadj i j hij h1 h2).2
  have hinj : ∀ k, Function.Injective (x (sroot k)) := fun k =>
    (hE.param _ (single_mem_roots k)).2.2
  have hnt : ∀ k, ∃ c, x (sroot k) c ≠ 1 := fun k => ⟨1, fun h => one_ne_zero
    (hinj k (h.trans (x_zero hE (single_mem_roots k)).symm))⟩
  have hadjoins : ∀ l k, (adj l k ∨ adj k l) →
      Adj3 (x (sroot l)) (x (-sroot l)) (x (sroot k)) := by
    rintro l k (h | h)
    · obtain ⟨ρ, hρ⟩ := hsl3 l k h
      exact Or.inl ⟨ρ, fun c => ⟨(hρ c).1, (hρ c).2.1, (hρ c).2.2.1⟩⟩
    · obtain ⟨ρ, hρ⟩ := hsl3 k l h
      exact Or.inr ⟨ρ, fun c => ⟨(hρ c).2.2.1, (hρ c).2.2.2.1, (hρ c).1⟩⟩
  have hsgn_ne : ∀ γ, edgeSign C adj F γ ≠ 0 := by
    intro γ
    rcases edgeSign_cases (C := C) (adj := adj) (F := F) γ with
      ⟨i, j, hij, h⟩ | ⟨i, j, hij, h⟩ | h
    · rw [h]
      exact left_ne_zero_of_mul_eq_one (epsPos_mul_self hdiv (hadj i j hij).1 (hadj i j hij).2
        (hne i j hij) hC)
    · rw [h]
      exact left_ne_zero_of_mul_eq_one (epsNeg_mul_self hdiv (hadj i j hij).1 (hadj i j hij).2
        (hne i j hij) hC)
    · rw [h]
      exact one_ne_zero
  have es1 : ∀ k, edgeSign C adj F (sroot k) = 1 := fun k => (edgeSign_single hne k).1
  have es2 : ∀ k, edgeSign C adj F (-sroot k) = 1 := fun k => (edgeSign_single hne k).2
  refine ⟨fun γ c => x γ (edgeSign C adj F γ * c), ?_, fun k c => ?_⟩
  swap
  · simp only [es1, es2, one_mul, and_self]
  refine
    { asymm := hasymm
      ne := hne
      mem := fun γ hγ c => ((hE.param γ hγ).1 _).2 ⟨_, rfl⟩
      surj := fun γ hγ g hg => ?_
      pairRoots_adj := fun i j h => ?_
      pairRoots_nonadj := fun i j h1 h2 => ?_
      sl3 := fun i j h => ?_
      sl2 := fun k => ?_
      sl2sl2 := fun i j hij h1 h2 => ?_ }
  · obtain ⟨c₀, hc₀⟩ := ((hE.param γ hγ).1 g).1 hg
    exact ⟨(edgeSign C adj F γ)⁻¹ * c₀, by
      rw [mul_inv_cancel_left₀ (hsgn_ne γ), hc₀]⟩
  · intro γ hγ
    obtain ⟨z, hz, rfl⟩ := pairRoots_subset_pair hdiv (Z := zEdge) (by decide) (by decide)
      (by rw [(hadj i j h).1]; decide) (by rw [(hadj i j h).2]; decide) hγ
    rw [Finset.mem_coe] at hz
    simp only [zEdge, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [pair_one_zero]; simp
    · rw [pair_neg_one_zero]; simp
    · rw [pair_zero_one]; simp
    · rw [pair_zero_neg_one]; simp
    · rw [pair_one_one]; simp
    · rw [pair_neg_one_neg_one]; simp
  · by_cases hij : i = j
    · subst hij
      refine (pairRoots_subset hdiv (S := {sroot i, -sroot i}) (by simp) (by simp) ?_ ?_).trans
        (by intro γ hγ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ ⊢; tauto) <;>
      · intro γ hγ
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ ⊢
        rcases hγ with rfl | rfl
        · right
          exact reflection_single_self (D.isFiniteType.apply_self i)
        · left
          rw [map_neg, reflection_single_self (D.isFiniteType.apply_self i), neg_neg]
    · intro γ hγ
      obtain ⟨z, hz, rfl⟩ := pairRoots_subset_pair hdiv (Z := zNon) (by decide) (by decide)
        (by rw [(hnadj i j hij h1 h2).1]; decide) (by rw [(hnadj i j hij h1 h2).2]; decide) hγ
      rw [Finset.mem_coe] at hz
      simp only [zNon, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · rw [pair_one_zero]; simp
      · rw [pair_neg_one_zero]; simp
      · rw [pair_zero_one]; simp
      · rw [pair_zero_neg_one]; simp
  · obtain ⟨ρ, hρ⟩ := hsl3 i j h
    refine ⟨ρ, ?_, fun c => ?_⟩
    · obtain ⟨k, hki, hkj, hk | hk⟩ := hnb i j h
      · obtain ⟨hjk, hik, hki'⟩ := hk
        have hc := hcomm i k (Ne.symm hki) hik hki'
        exact injective_of_adj3 (fun c => ⟨(hρ c).1, (hρ c).2.1⟩)
          (fun c => ⟨(hρ c).2.2.1, (hρ c).2.2.2.1⟩) (hnt i) (hinj k)
          (Or.inl ⟨fun c => (hc c 1).1, fun c => (hc c 1).2.2.1, hadjoins j k hjk⟩)
      · obtain ⟨hik, hjk, hkj'⟩ := hk
        have hc := hcomm j k (Ne.symm hkj) hjk hkj'
        exact injective_of_adj3 (fun c => ⟨(hρ c).1, (hρ c).2.1⟩)
          (fun c => ⟨(hρ c).2.2.1, (hρ c).2.2.2.1⟩) (hnt i) (hinj k)
          (Or.inr ⟨fun c => (hc c 1).1, fun c => (hc c 1).2.2.1, hadjoins i k hik⟩)
    · simp only [es1, es2, edgeSign_pos hasymm hne h, edgeSign_neg hasymm hne h, one_mul]
      exact hρ c
  · obtain ⟨φ, hφ, hup, hlow⟩ := hE.rankOne k
    refine ⟨φ, hφ, fun c => ⟨?_, ?_⟩⟩
    · simp only [es1, one_mul, tv01_eq_sl2Upper, hup]
    · simp only [es2, one_mul, tv10_eq_sl2Lower, hlow]
  · obtain ⟨l, hl, hl'⟩ := exists_sl2sl2 hE hdiv hij (hnadj i j hij h1 h2).1
      (hnadj i j hij h1 h2).2 hind hsq
    refine ⟨l, hl, fun c => ?_⟩
    simp only [es1, es2, one_mul]
    exact hl' c

end Main

end CFSG.ClassicalInvolution.WeakCT
