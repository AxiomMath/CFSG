module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInner
public import CFSG.LieType.SeitzGeneration.ExcHigh.Product

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeOrthTwoAux

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.CTP OrthBlk OrthNS HyperBlocks
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeInnerAux

section Setup

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

@[expose] def AStable (A : Subgroup (elementaryGroup Q)) (W : Submodule K V) : Prop :=
  ∀ a ∈ A, ∀ u ∈ W, (a : V ≃ₗ[K] V) u ∈ W

@[expose] def fixA (A : Subgroup (elementaryGroup Q)) : Submodule K V where
  carrier := {v | ∀ a ∈ A, (a : V ≃ₗ[K] V) v = v}
  add_mem' := fun {u v} hu hv a ha => by rw [map_add, hu a ha, hv a ha]
  zero_mem' := fun a _ => map_zero _
  smul_mem' := fun c v hv a ha => by rw [map_smul, hv a ha]

@[expose] def pieceKer (A : Subgroup (elementaryGroup Q)) (W : Submodule K V) : Subgroup A :=
  (stabPW W).comap ((elementaryGroup Q).subtype.comp A.subtype)

theorem mem_pieceKer {A : Subgroup (elementaryGroup Q)} {W : Submodule K V} {b : A} :
    b ∈ pieceKer A W ↔ ∀ u ∈ W, ((b : elementaryGroup Q) : V ≃ₗ[K] V) u = u := Iff.rfl

theorem mem_O (a : elementaryGroup Q) :
    (a : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  elementaryGroup_le_orthogonalGroup Q a.2

theorem AStable.inf {A : Subgroup (elementaryGroup Q)} {W W' : Submodule K V} (h : AStable A W)
    (h' : AStable A W') : AStable A (W ⊓ W') := fun a ha u hu => ⟨h a ha u hu.1, h' a ha u hu.2⟩

theorem apply_inv_apply (a : elementaryGroup Q) (v : V) :
    (a : V ≃ₗ[K] V) (((a⁻¹ : elementaryGroup Q) : V ≃ₗ[K] V) v) = v := by
  show ((a * a⁻¹ : elementaryGroup Q) : V ≃ₗ[K] V) v = v
  rw [mul_inv_cancel]
  rfl

theorem AStable.perp {A : Subgroup (elementaryGroup Q)} {W : Submodule K V} (h : AStable A W) :
    AStable A (OrthBlk.perp Q W) := by
  intro a ha t ht
  refine mem_perp.mpr fun s hs => ?_
  rw [← apply_inv_apply a s, polar_map_of_mem (mem_O a)]
  exact mem_perp.mp ht _ (h _ (A.inv_mem ha) s hs)

theorem fixA_astable (A : Subgroup (elementaryGroup Q)) : AStable A (fixA A) :=
  fun a ha u hu => by rw [hu a ha]; exact hu

theorem fix_sup {f : V ≃ₗ[K] V} {U₁ U₂ : Submodule K V} (h₁ : ∀ u ∈ U₁, f u = u)
    (h₂ : ∀ u ∈ U₂, f u = u) : ∀ u ∈ U₁ ⊔ U₂, f u = u := by
  have : f ∈ stabPW (U₁ ⊔ U₂) := by
    rw [stabPW_sup]
    exact ⟨mem_stabPW.mpr h₁, mem_stabPW.mpr h₂⟩
  exact mem_stabPW.mp this

structure TwoSetup (Q : QuadraticForm K V) (p : ℕ) (A : Subgroup (elementaryGroup Q)) :
    Prop where
  nondeg : (polarBilin Q).Nondegenerate
  prime : p.Prime
  cast_ne_zero : (p : K) ≠ 0
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  pow_eq_one : ∀ a ∈ A, a ^ p = 1
  card_eq : Nat.card A = p ^ 3
  two : orderOf ((Nat.card K : ℕ) : ZMod p) = 2
  aniso : ∀ W : Submodule K V, (∀ w ∈ W, Q w = 0) → AStable A W → W = ⊥

@[expose] def IsCubePiece (A : Subgroup (elementaryGroup Q)) (P : Submodule K V) : Prop :=
  P ≠ ⊥ ∧ PolarNondegOn Q P ∧ OrthSep Q P (fixA A) ∧ AStable A P ∧
    ∀ W : Submodule K V, W ≤ P → AStable A W → W = ⊥ ∨ W = P

namespace IsCubePiece

variable {A : Subgroup (elementaryGroup Q)} {P : Submodule K V}

theorem ne_bot (hP : IsCubePiece A P) : P ≠ ⊥ := hP.1

theorem regular (hP : IsCubePiece A P) : PolarNondegOn Q P := hP.2.1

theorem orthSep (hP : IsCubePiece A P) : OrthSep Q P (fixA A) := hP.2.2.1

theorem astable (hP : IsCubePiece A P) : AStable A P := hP.2.2.2.1

theorem minimal (hP : IsCubePiece A P) {W : Submodule K V} (hW : W ≤ P) (hst : AStable A W) :
    W = ⊥ ∨ W = P := hP.2.2.2.2 W hW hst

theorem pieceKer_ne_top (hP : IsCubePiece A P) : pieceKer A P ≠ ⊤ := by
  intro htop
  apply hP.ne_bot
  rw [eq_bot_iff]
  intro u hu
  have huV : u ∈ fixA A := fun a ha => by
    have : (⟨a, ha⟩ : A) ∈ pieceKer A P := by rw [htop]; exact Subgroup.mem_top _
    exact (mem_pieceKer.mp this) u hu
  exact (Submodule.mem_bot K).mpr (hP.regular u hu fun y hy => by
    rw [polar_comm]
    exact hP.orthSep y hy u huV)

end IsCubePiece

theorem exists_minimal_astable {A : Subgroup (elementaryGroup Q)} {W : Submodule K V}
    (hW : W ≠ ⊥) (hWst : AStable A W) :
    ∃ U : Submodule K V, U ≤ W ∧ U ≠ ⊥ ∧ AStable A U ∧
      ∀ U' : Submodule K V, U' ≤ U → AStable A U' → U' = ⊥ ∨ U' = U := by
  obtain ⟨U, ⟨hUW, hU0, hUst⟩, hUmin⟩ := (wellFounded_lt (α := Submodule K V)).has_min
    {U | U ≤ W ∧ U ≠ ⊥ ∧ AStable A U} ⟨W, le_rfl, hW, hWst⟩
  refine ⟨U, hUW, hU0, hUst, fun U' hU'U hU'st => ?_⟩
  by_cases hU'0 : U' = ⊥
  · exact Or.inl hU'0
  · right
    by_contra hne
    exact hUmin U' ⟨hU'U.trans hUW, hU'0, hU'st⟩ (lt_of_le_of_ne hU'U hne)

theorem hyperH_le_O (A : Subgroup (elementaryGroup Q)) (p : ℕ) :
    (hyperClosure p ⊤ A).map (elementaryGroup Q).subtype ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
  rintro _ ⟨x, -, rfl⟩
  exact elementaryGroup_le_orthogonalGroup Q x.2

namespace TwoSetup

variable {p : ℕ} {A : Subgroup (elementaryGroup Q)} (S : TwoSetup Q p A)
include S

theorem ne_two : p ≠ 2 := (manyTwo_ne_two_and_ne_ringChar S.prime S.two).1

theorem ne_ringChar : p ≠ ringChar K := (manyTwo_ne_two_and_ne_ringChar S.prime S.two).2

theorem comm' (a b : A) : a * b = b * a := Subtype.ext (S.comm a a.2 b b.2)

theorem pow' (a : A) : a ^ p = 1 := Subtype.ext (by simpa using S.pow_eq_one a a.2)

theorem apply_comm {a b : elementaryGroup Q} (ha : a ∈ A) (hb : b ∈ A) (v : V) :
    (a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = (b : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v) := by
  show ((a * b : elementaryGroup Q) : V ≃ₗ[K] V) v = ((b * a : elementaryGroup Q) : V ≃ₗ[K] V) v
  rw [S.comm a ha b hb]

theorem coe_pow_eq_one {a : elementaryGroup Q} (ha : a ∈ A) : (a : V ≃ₗ[K] V) ^ p = 1 := by
  have := congrArg (fun g : elementaryGroup Q => (g : V ≃ₗ[K] V)) (S.pow_eq_one a ha)
  simpa using this

theorem card_of_index {F : Subgroup A} (hF : F.index = p) : Nat.card F = p ^ 2 := by
  have h := F.card_mul_index
  rw [hF, S.card_eq] at h
  have : Nat.card F * p = p ^ 2 * p := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right S.prime.pos this

theorem fixA_regular : PolarNondegOn Q (fixA A) := by
  classical
  haveI := finite_sub A
  letI : Fintype A := Fintype.ofFinite A
  have h := polarNondegOn_qFix (φ := (elementaryGroup Q).subtype.comp A.subtype) S.nondeg
    (fun f => mem_O (f : elementaryGroup Q)) (by
      rw [Fintype.card_eq_nat_card, S.card_eq, Nat.cast_pow]
      exact pow_ne_zero 3 S.cast_ne_zero)
  intro x hx hxy
  exact h x (fun f => hx f f.2) fun y hy => hxy y fun a ha => hy ⟨a, ha⟩

theorem fixA_aniso {v : V} (hv : v ∈ fixA A) (hQ : Q v = 0) : v = 0 := by
  have h := S.aniso (Submodule.span K {v}) (fun w hw => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul_eq_sq, hQ, mul_zero]) (fun a ha w hw => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, hv a ha]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  simpa using h

theorem finrank_fixA_le_two : finrank K (fixA A) ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx, hx0, hxQ⟩ := exists_singular_of_three_le_any (Q := Q) (S := fixA A) (by omega)
  exact hx0 (S.fixA_aniso hx hxQ)

theorem two_ne_zero_of_finrank_fixA (h1 : finrank K (fixA A) = 1) : (2 : K) ≠ 0 := by
  intro h2
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  apply hv0
  refine Subtype.ext (S.fixA_regular v v.2 fun y hy => ?_)
  obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
  have hvv : polar Q (v : V) (v : V) = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hy' : y = c • (v : V) := (congrArg Subtype.val hc).symm
  rw [hy', polar_smul_right_eq, hvv, mul_zero]

theorem regular_of_minimal {W : Submodule K V} (hW0 : W ≠ ⊥) (hWV : Disjoint W (fixA A))
    (hst : AStable A W) (hmin : ∀ W' : Submodule K V, W' ≤ W → AStable A W' → W' = ⊥ ∨ W' = W) :
    PolarNondegOn Q W := by
  classical
  have hR : AStable A (W ⊓ OrthBlk.perp Q W) := hst.inf hst.perp
  rcases hmin _ inf_le_left hR with hR0 | hRS
  · intro x hxW hx
    have hxR : x ∈ W ⊓ OrthBlk.perp Q W :=
      ⟨hxW, mem_perp.mpr fun s hs => by rw [polar_comm]; exact hx s hs⟩
    rw [hR0] at hxR
    exact (Submodule.mem_bot K).mp hxR
  · exfalso
    have hSS : ∀ s ∈ W, ∀ t ∈ W, polar Q s t = 0 := fun s hs t ht => by
      have ht' : t ∈ W ⊓ OrthBlk.perp Q W := by rw [hRS]; exact ht
      exact mem_perp.mp ht'.2 s hs
    let W₀ : Submodule K V :=
      { carrier := {s | s ∈ W ∧ Q s = 0}
        add_mem' := fun {a b} ha hb => ⟨W.add_mem ha.1 hb.1, by
          rw [QuadraticMap.map_add Q a b, ha.2, hb.2, hSS a ha.1 b hb.1]; simp⟩
        zero_mem' := ⟨W.zero_mem, QuadraticMap.map_zero Q⟩
        smul_mem' := fun c a ha => ⟨W.smul_mem c ha.1, by
          rw [map_smul_eq_sq, ha.2, mul_zero]⟩ }
    have hW₀st : AStable A W₀ := fun a ha u hu =>
      ⟨hst a ha u hu.1, by rw [map_of_mem (mem_O a), hu.2]⟩
    rcases hmin W₀ (fun s hs => hs.1) hW₀st with h0 | hfull
    · obtain ⟨s, hsW, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      have hsV : s ∉ fixA A := fun hsV => hs0 (Submodule.disjoint_def.mp hWV s hsW hsV)
      obtain ⟨a, ha, has⟩ : ∃ a ∈ A, (a : V ≃ₗ[K] V) s ≠ s := by
        by_contra hcon
        push Not at hcon
        exact hsV hcon
      have hasW := hst a ha s hsW
      have hQ2 : (2 : K) * Q s = 0 := by rw [← polar_self_eq_two_mul]; exact hSS s hsW s hsW
      have hd : (a : V ≃ₗ[K] V) s - s ∈ W₀ := by
        refine ⟨W.sub_mem hasW hsW, ?_⟩
        rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right,
          map_of_mem (mem_O a), hSS _ hasW s hsW]
        linear_combination hQ2
      rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
      exact has hd
    · refine hW0 (S.aniso W (fun v hv => ?_) hst)
      have hv' : v ∈ W₀ := by rw [hfull]; exact hv
      exact hv'.2

theorem exists_pieces_of_stable :
    ∀ (n : ℕ) (W : Submodule K V), finrank K W = n → AStable A W → PolarNondegOn Q W →
      OrthSep Q W (fixA A) →
      ∃ (m : ℕ) (P : Fin m → Submodule K V), (∀ i, IsCubePiece A (P i)) ∧
        (∀ i j, i ≠ j → OrthSep Q (P i) (P j)) ∧ (∀ i, P i ≤ W) ∧ W ≤ ⨆ i, P i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hWst hWreg hWV
  by_cases hW0 : W = ⊥
  · exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp [hW0]⟩
  obtain ⟨U, hUW, hU0, hUst, hUmin⟩ := exists_minimal_astable hW0 hWst
  have hV0 := S.fixA_regular
  have hUdisj : Disjoint U (fixA A) := by
    rw [Submodule.disjoint_def]
    intro x hxU hxV
    exact hV0 x hxV fun y hy => hWV x (hUW hxU) y hy
  have hUreg : PolarNondegOn Q U := S.regular_of_minimal hU0 hUdisj hUst hUmin
  set W' : Submodule K V := W ⊓ OrthBlk.perp Q U with hW'
  have hW'st : AStable A W' := hWst.inf hUst.perp
  have hW'reg : PolarNondegOn Q W' := polarNondegOn_inf_perp hWreg hUreg hUW
  have hW'V : OrthSep Q W' (fixA A) := fun w hw v hv => hWV w hw.1 v hv
  have hlt : finrank K W' < n := by
    rw [← hn]
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => ?_)
    obtain ⟨s, hsU, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have : s ∈ W' := by rw [h]; exact hUW hsU
    exact hs0 (hUreg s hsU fun t ht => by rw [polar_comm]; exact mem_perp.mp this.2 t ht)
  obtain ⟨m, P', hP'piece, hP'orth, hP'le, hP'sp⟩ := ih _ hlt W' rfl hW'st hW'reg hW'V
  have hUpiece : IsCubePiece A U :=
    ⟨hU0, hUreg, fun s hs v hv => hWV s (hUW hs) v hv, hUst, hUmin⟩
  refine ⟨m + 1, Fin.cons U P', ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hUpiece
    · simpa using hP'piece j
  · intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · exact absurd rfl hij
    · intro s hs t ht
      simp only [Fin.cons_zero, Fin.cons_succ] at hs ht
      exact mem_perp.mp (hP'le j' ht).2 s hs
    · intro s hs t ht
      simp only [Fin.cons_zero, Fin.cons_succ] at hs ht
      rw [polar_comm]
      exact mem_perp.mp (hP'le i' hs).2 t ht
    · simp only [Fin.cons_succ]
      exact hP'orth i' j' fun h => hij (by rw [h])
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hUW
    · simpa using (hP'le j).trans inf_le_left
  · intro w hw
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_add_inf_perp hUreg hUW hw
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_iSup_of_mem (0 : Fin (m + 1)) (by simpa using ha)
    · have hr' : r ∈ ⨆ j, P' j := hP'sp hr
      refine (iSup_le fun j => ?_ : (⨆ j, P' j) ≤ ⨆ i, (Fin.cons U P' : Fin (m + 1) → _) i) hr'
      exact le_iSup_of_le j.succ (by simp)

theorem exists_decomposition :
    ∃ (n : ℕ) (P : Fin n → Submodule K V), (∀ i, IsCubePiece A (P i)) ∧
      (∀ i j, i ≠ j → OrthSep Q (P i) (P j)) ∧ (∀ i, OrthSep Q (fixA A) (P i)) ∧
      (⊤ : Submodule K V) ≤ fixA A ⊔ ⨆ i, P i := by
  have hV0 := S.fixA_regular
  obtain ⟨n, P, hP, hPP, hPle, hPsp⟩ := S.exists_pieces_of_stable _ (OrthBlk.perp Q (fixA A)) rfl
    (fixA_astable A).perp (polarNondegOn_perp S.nondeg hV0)
    (fun w hw v hv => by rw [polar_comm]; exact mem_perp.mp hw v hv)
  refine ⟨n, P, hP, hPP, fun i s hs t ht => mem_perp.mp (hPle i ht) s hs, ?_⟩
  rw [← (isCompl_perp hV0).sup_eq_top]
  exact sup_le_sup_left hPsp _

variable {P : Submodule K V}

theorem exists_hyperplane_fix (hP : IsCubePiece A P) :
    ∃ F : Subgroup A, F.index = p ∧ F ≤ pieceKer A P := by
  classical
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := finite_sub A
  by_contra hcon
  push Not at hcon
  have hbot : ∀ F : Subgroup A, F.index = p → hyperFixed (aRep A) F ⊓ P = ⊥ := by
    intro F hF
    have hst : AStable A (hyperFixed (aRep A) F ⊓ P) := by
      intro a ha u hu
      refine ⟨mem_hyperFixed.mpr fun f hf => ?_, hP.astable a ha u hu.2⟩
      have h1 := mem_hyperFixed.mp hu.1 f hf
      rw [aRep_apply] at h1 ⊢
      rw [S.apply_comm f.2 ha, h1]
    rcases hP.minimal inf_le_right hst with h0 | hfull
    · exact h0
    · exfalso
      apply hcon F hF
      intro f hf
      rw [mem_pieceKer]
      intro u hu
      have : u ∈ hyperFixed (aRep A) F ⊓ P := by rw [hfull]; exact hu
      have h1 := mem_hyperFixed.mp this.1 f hf
      rwa [aRep_apply] at h1
  obtain ⟨v, hvP, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP.ne_bot
  have h := mem_iSup_hyperFixed_top S.cast_ne_zero S.comm' S.pow' (aRep A) P
    (fun e x hx => hP.astable e e.2 x hx) (k := 3) (by norm_num) S.card_eq hvP
  have hle : (⨆ (F' : Subgroup A) (_ : F'.index = p), hyperFixed (aRep A) F' ⊓ P) = ⊥ :=
    le_bot_iff.mp (iSup₂_le fun F hF => (hbot F hF).le)
  rw [hle] at h
  exact hv0 ((Submodule.mem_bot K).mp h)

theorem index_pieceKer (hP : IsCubePiece A P) : (pieceKer A P).index = p := by
  obtain ⟨F, hF, hFle⟩ := S.exists_hyperplane_fix hP
  suffices h : pieceKer A P = F by rw [h]; exact hF
  by_contra hne
  obtain ⟨x, hxK, hxF⟩ : ∃ x ∈ pieceKer A P, x ∉ F := by
    by_contra h
    push Not at h
    exact hne (le_antisymm h hFle)
  have hsup := sup_zpowers_eq S.prime le_top (by rw [Subgroup.relIndex_top_right]; exact hF)
    (Subgroup.mem_top x) hxF
  apply hP.pieceKer_ne_top
  rw [eq_top_iff, ← hsup]
  exact sup_le hFle (Subgroup.zpowers_le.mpr hxK)

theorem eq_zero_of_fixed (hP : IsCubePiece A P) {b : A} (hb : b ∉ pieceKer A P) {v : V}
    (hv : v ∈ P) (hbv : ((b : elementaryGroup Q) : V ≃ₗ[K] V) v = v) : v = 0 := by
  obtain ⟨C, hC⟩ : ∃ C : Submodule K V, C = P ⊓ LinearMap.ker
      (((b : elementaryGroup Q) : V ≃ₗ[K] V).toLinearMap - LinearMap.id) := ⟨_, rfl⟩
  have hmemC : ∀ u, u ∈ C ↔ u ∈ P ∧ ((b : elementaryGroup Q) : V ≃ₗ[K] V) u = u := by
    intro u
    rw [hC, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact Iff.rfl
  have hCst : AStable A C := by
    intro a ha u hu
    obtain ⟨huP, hbu⟩ := (hmemC u).mp hu
    refine (hmemC _).mpr ⟨hP.astable a ha u huP, ?_⟩
    rw [S.apply_comm b.2 ha, hbu]
  rcases hP.minimal (fun u hu => ((hmemC u).mp hu).1) hCst with h0 | hCP
  · have : v ∈ C := (hmemC v).mpr ⟨hv, hbv⟩
    rw [h0] at this
    exact (Submodule.mem_bot K).mp this
  · exfalso
    apply hb
    rw [mem_pieceKer]
    intro u hu
    have : u ∈ C := by rw [hCP]; exact hu
    exact ((hmemC u).mp this).2

theorem astable_of_apply_mem (hP : IsCubePiece A P) {b : A} (hb : b ∉ pieceKer A P)
    {W : Submodule K V} (hWP : W ≤ P)
    (hWb : ∀ w ∈ W, ((b : elementaryGroup Q) : V ≃ₗ[K] V) w ∈ W) : AStable A W := by
  let T : Subgroup A :=
    { carrier := {c | ∀ w ∈ W, ((c : elementaryGroup Q) : V ≃ₗ[K] V) w ∈ W}
      mul_mem' := fun {c d} hc hd w hw => hc _ (hd w hw)
      one_mem' := fun w hw => hw
      inv_mem' := fun {c} hc w hw =>
        stable_symm_of_pow (S.coe_pow_eq_one c.2) S.prime.pos hc w hw }
  have hKT : pieceKer A P ≤ T := fun c hc w hw => by
    rw [(mem_pieceKer.mp hc) w (hWP hw)]
    exact hw
  have hbT : b ∈ T := hWb
  have hsup := sup_zpowers_eq S.prime le_top
    (by rw [Subgroup.relIndex_top_right]; exact S.index_pieceKer hP) (Subgroup.mem_top b) hb
  have htop : T = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le hKT (Subgroup.zpowers_le.mpr hbT)
  intro a ha w hw
  have : (⟨a, ha⟩ : A) ∈ T := by rw [htop]; exact Subgroup.mem_top _
  exact this w hw

theorem exists_quadratic (hP : IsCubePiece A P) {b : A} (hb : b ∉ pieceKer A P) :
    finrank K P = 2 ∧ ∃ q : K[X], q.Monic ∧ Irreducible q ∧ q ≠ X - 1 ∧ q ∣ X ^ p - 1 ∧
      (∃ τ : K, q = X ^ 2 - C τ * X + 1 ∧ ∀ r : K, r ^ 2 - τ * r + 1 ≠ 0) ∧
      ∀ v ∈ P, aeval ((b : elementaryGroup Q) : V ≃ₗ[K] V).toLinearMap q v = 0 := by
  classical
  set T : Module.End K V := ((b : elementaryGroup Q) : V ≃ₗ[K] V).toLinearMap with hT
  have hTP : ∀ x ∈ P, T x ∈ P := fun x hx => hP.astable b b.2 x hx
  haveI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.mpr hP.ne_bot
  have hTp : T ^ p = 1 := by
    rw [hT, ← toLinearMap_pow, S.coe_pow_eq_one b.2]
    rfl
  have hpow : T.restrict hTP ^ p = 1 := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    rw [coe_pow_of_intertwine (A := T.restrict hTP) (B := T) (fun u => rfl), hTp]
    rfl
  have hfix : ∀ v : P, T.restrict hTP v = v → v = 0 := by
    intro v hv
    exact Subtype.ext (S.eq_zero_of_fixed hP hb v.2 (congrArg Subtype.val hv))
  have hsimple : ∀ W : Submodule K P, (∀ s ∈ W, T.restrict hTP s ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hWb : ∀ s ∈ W.map P.subtype,
        ((b : elementaryGroup Q) : V ≃ₗ[K] V) s ∈ W.map P.subtype := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨T.restrict hTP s, hW s hs, rfl⟩
    rcases hP.minimal (Submodule.map_subtype_le P W)
        (S.astable_of_apply_mem hP hb (Submodule.map_subtype_le P W) hWb) with h0 | h1
    · left
      rw [eq_bot_iff]
      intro s hs
      have : (s : V) ∈ W.map P.subtype := ⟨s, hs, rfl⟩
      rw [h0] at this
      exact Subtype.ext ((Submodule.mem_bot K).mp this)
    · right
      rw [eq_top_iff]
      intro s _
      have : (s : V) ∈ W.map P.subtype := by rw [h1]; exact s.2
      obtain ⟨t, ht, hts⟩ := this
      have : t = s := Subtype.ext hts
      rwa [← this]
  obtain ⟨h, hmon, hirr, hdvd, hne1, hgh, hfin⟩ :=
    exists_irreducible_of_simple_endomorphism S.prime.pos (T.restrict hTP) hpow hfix hsimple
  have hkerP : ∀ v ∈ P, aeval T h v = 0 := fun v hv => by
    have := coe_aeval_of_intertwine (A := T.restrict hTP) (B := T) (fun u => rfl) h ⟨v, hv⟩
    rw [hgh, LinearMap.zero_apply] at this
    exact this.symm
  have hdeg : h.natDegree = 2 :=
    (natDegree_eq_orderOf_of_dvd S.prime S.ne_ringChar hmon hirr hdvd hne1).trans S.two
  have hx : OddOrderIsometry Q p ((b : elementaryGroup Q) : V ≃ₗ[K] V) :=
    ⟨mem_O _, S.coe_pow_eq_one b.2, S.cast_ne_zero,
      fun v hv => eq_zero_of_polar_eq_zero S.nondeg hv⟩
  obtain ⟨v₀, hv₀P, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP.ne_bot
  have hhf : h ∈ primaryFactors T :=
    CFSG.RankThree.PartOne.KCUnitaryMixing.mem_primaryFactors_of_apply_eq_zero hirr hmon
      (hkerP v₀ hv₀P) hv₀0
  have hself : h = reciprocalPolynomial h := by
    by_contra hne
    refine hP.ne_bot (eq_bot_iff.mpr fun x hxP => ?_)
    refine (Submodule.mem_bot K).mpr (hP.regular x hxP fun y hyP => ?_)
    exact hx.polar_eq_zero_of_ne hhf hne (mem_primaryComponent.mpr (hkerP x hxP))
      (mem_primaryComponent.mpr (hkerP y hyP))
  obtain ⟨τ, hτ⟩ := manyTwo_exists_eq_X_sq_sub hmon hirr hdeg hself
  refine ⟨hfin.trans hdeg, h, hmon, hirr, hne1, hdvd, ⟨τ, hτ, fun r hr => ?_⟩, hkerP⟩
  refine manyTwo_not_isRoot_of_natDegree_two hirr hdeg r ?_
  rw [hτ]
  simpa [Polynomial.IsRoot] using hr

theorem exists_not_mem_pieceKer (hP : IsCubePiece A P) : ∃ b : A, b ∉ pieceKer A P := by
  by_contra h
  push Not at h
  exact hP.pieceKer_ne_top (eq_top_iff.mpr fun b _ => h b)

theorem anisotropic (hP : IsCubePiece A P) : ∀ s ∈ P, Q s = 0 → s = 0 := by
  classical
  obtain ⟨b, hb⟩ := S.exists_not_mem_pieceKer hP
  obtain ⟨hd, q, hmon, hirr, hne1, hdvd, ⟨τ, hq, hnoroot⟩, hker⟩ := S.exists_quadratic hP hb
  have hτ : τ ≠ 0 := by
    subst hq
    exact manyTwo_tau_ne_zero S.prime S.ne_two hmon hirr hdvd hne1
  set g : V ≃ₗ[K] V := ((b : elementaryGroup Q) : V ≃ₗ[K] V) with hg
  have hrel : ∀ v ∈ P, g (g v) = τ • g v - v := fun v hv => by
    have := hker v hv
    rw [hq] at this
    exact manyTwo_apply_sq_of_aeval g.toLinearMap τ v this
  intro s hsP hsQ
  by_contra hs0
  have hli := manyTwo_linearIndependent_pair hs0 (hrel s hsP) hnoroot
  have hgsP : g s ∈ P := hP.astable b b.2 s hsP
  have hspan : Submodule.span K (Set.range ![s, g s]) = P := by
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hsP
      · exact hgsP
    · rw [finrank_span_eq_card hli, hd]
      simp
  have hpol : polar Q s (g s) = 0 := polar_self_apply_eq_zero (mem_O _) hτ (hrel s hsP) hsQ
  refine hs0 (hP.regular s hsP fun y hy => ?_)
  rw [← hspan] at hy
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_self_eq_zero hsQ, hpol]
  ring

theorem eichler_mem_of_fix {F : Subgroup A} (hF : F.index = p) {e w : V}
    (he : ∀ f ∈ F, ((f : elementaryGroup Q) : V ≃ₗ[K] V) e = e)
    (hw : ∀ f ∈ F, ((f : elementaryGroup Q) : V ≃ₗ[K] V) w = w) :
    eichler Q e w ∈ (hyperClosure p ⊤ A).map (elementaryGroup Q).subtype := by
  refine ⟨⟨eichler Q e w, eichler_mem_elementaryGroup Q e w⟩,
    Subgroup.subset_closure ⟨Subgroup.mem_top _, F.map A.subtype, Subgroup.map_subtype_le _, ?_,
      ?_⟩, rfl⟩
  · have hsub : (F.map A.subtype).subgroupOf A = F :=
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective F
    rw [Subgroup.relIndex, hsub]
    exact hF
  · rintro _ ⟨f, hf, rfl⟩
    exact Subtype.ext (commute_eichler_of_fix (mem_O _) (he f hf) (hw f hf))

theorem mem_hyperH_of_commute {a b : elementaryGroup Q} (ha : a ∈ A) (hb : b ∈ A)
    (hind : ∀ i j : ℤ, a ^ i * b ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) {g : V ≃ₗ[K] V}
    (hg : g ∈ elementaryGroup Q) (hga : Commute g (a : V ≃ₗ[K] V))
    (hgb : Commute g (b : V ≃ₗ[K] V)) :
    g ∈ (hyperClosure p ⊤ A).map (elementaryGroup Q).subtype :=
  ⟨⟨g, hg⟩, mem_hyperClosure_of_commute S.prime S.card_eq ha hb (S.comm a ha b hb)
    (S.pow_eq_one a ha) (S.pow_eq_one b hb) hind (Subtype.ext hga.eq) (Subtype.ext hgb.eq), rfl⟩

theorem indep_of_fix {z x : elementaryGroup Q} (hz : z ∈ A) (hx : x ∈ A) (hz1 : z ≠ 1)
    {U : Submodule K V} (hzU : ∀ u ∈ U, (z : V ≃ₗ[K] V) u = u)
    (hxj : ∀ j : ℤ, (∀ u ∈ U, ((x ^ j : elementaryGroup Q) : V ≃ₗ[K] V) u = u) → (p : ℤ) ∣ j) :
    ∀ i j : ℤ, z ^ i * x ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
  haveI : Fact p.Prime := ⟨S.prime⟩
  intro i j hij
  have hc : Commute z x := S.comm z hz x hx
  have hji : x ^ j * z ^ i = 1 := by rw [← (hc.zpow_zpow i j).eq]; exact hij
  have hzi : ∀ u ∈ U, ((z ^ i : elementaryGroup Q) : V ≃ₗ[K] V) u = u := by
    have hmem : (z : V ≃ₗ[K] V) ∈ stabPW U := mem_stabPW.mpr hzU
    have := (stabPW U).zpow_mem hmem i
    intro u hu
    rw [Subgroup.coe_zpow]
    exact mem_stabPW.mp this u hu
  have hxfix : ∀ u ∈ U, ((x ^ j : elementaryGroup Q) : V ≃ₗ[K] V) u = u := by
    intro u hu
    have h1 : ((x ^ j * z ^ i : elementaryGroup Q) : V ≃ₗ[K] V) u = u := by rw [hji]; rfl
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hzi u hu] at h1
    exact h1
  obtain ⟨m, hm⟩ := hxj j hxfix
  have hxj1 : x ^ j = 1 := by
    rw [hm, zpow_mul, zpow_natCast, S.pow_eq_one x hx, one_zpow]
  rw [hxj1, mul_one] at hij
  refine ⟨?_, ⟨m, hm⟩⟩
  rw [← orderOf_eq_prime (S.pow_eq_one z hz) hz1]
  exact orderOf_dvd_iff_zpow_eq_one.mpr hij

theorem eichler_mem_pair {P₁ P₂ : Submodule K V} (hP₁ : IsCubePiece A P₁)
    (hP₂ : IsCubePiece A P₂) (hne : pieceKer A P₁ ≠ pieceKer A P₂) (hperp : OrthSep Q P₁ P₂) :
    ∀ e ∈ P₁ ⊔ P₂, ∀ w ∈ P₁ ⊔ P₂,
      eichler Q e w ∈ (hyperClosure p ⊤ A).map (elementaryGroup Q).subtype := by
  classical
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI := finite_sub A
  set F₁ := pieceKer A P₁ with hF₁
  set F₂ := pieceKer A P₂ with hF₂
  have hi₁ : F₁.index = p := S.index_pieceKer hP₁
  have hi₂ : F₂.index = p := S.index_pieceKer hP₂
  have hnle : ∀ {G G' : Subgroup A}, G.index = p → G'.index = p → G ≠ G' →
      ∃ x ∈ G, x ∉ G' := by
    intro G G' hG hG' hGG
    by_contra h
    push Not at h
    exact hGG (Subgroup.eq_of_le_of_card_ge h (by rw [S.card_of_index hG, S.card_of_index hG']))
  obtain ⟨a₁, ha₁F₁, ha₁F₂⟩ := hnle hi₁ hi₂ hne
  obtain ⟨a₂, ha₂F₂, ha₂F₁⟩ := hnle hi₂ hi₁ (Ne.symm hne)
  obtain ⟨-, q₁, hmo₁, hir₁, hn₁, hdv₁, ⟨τ, hq₁, hnoroot⟩, hk₁⟩ := S.exists_quadratic hP₁ ha₂F₁
  obtain ⟨-, q₂, hmo₂, hir₂, hn₂, hdv₂, -, hk₂⟩ := S.exists_quadratic hP₂ ha₁F₂
  obtain ⟨c, hcp, hcq⟩ :=
    manyTwo_exists_dvd_comp_X_pow S.prime hmo₁ hmo₂ hir₁ hir₂ hdv₁ hdv₂ hn₁ hn₂
  have hτ : τ ≠ 0 := by
    subst hq₁
    exact manyTwo_tau_ne_zero S.prime S.ne_two hmo₁ hir₁ hdv₁ hn₁
  set g₁ : V ≃ₗ[K] V := ((a₁ : elementaryGroup Q) : V ≃ₗ[K] V) with hg₁
  set g₂ : V ≃ₗ[K] V := ((a₂ : elementaryGroup Q) : V ≃ₗ[K] V) with hg₂
  have hfix₁ : ∀ n : ℕ, ∀ u ∈ P₁, (g₁ ^ n) u = u := by
    intro n u hu
    have h1 : g₁ u = u := (mem_pieceKer.mp ha₁F₁) u hu
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, h1, ih]
  have hfix₂ : ∀ u ∈ P₂, g₂ u = u := fun u hu => (mem_pieceKer.mp ha₂F₂) u hu
  have hst₁ : ∀ u ∈ P₁, g₂ u ∈ P₁ := fun u hu => hP₁.astable a₂ a₂.2 u hu
  have hst₁' : ∀ u ∈ P₁, g₂.symm u ∈ P₁ := fun u hu =>
    stable_symm_of_pow (S.coe_pow_eq_one a₂.2) S.prime.pos hst₁ u hu
  have hst₂ : ∀ u ∈ P₂, g₁ u ∈ P₂ := fun u hu => hP₂.astable a₁ a₁.2 u hu
  have hst₂c : ∀ u ∈ P₂, (g₁ ^ c) u ∈ P₂ := OrthBlk.pow_apply_mem hst₂ c
  have hrel₂ : ∀ u ∈ P₁, g₂ (g₂ u) = τ • g₂ u - u := fun u hu => by
    have := hk₁ u hu
    rw [hq₁] at this
    exact manyTwo_apply_sq_of_aeval g₂.toLinearMap τ u this
  have hrel₁ : ∀ u ∈ P₂, (g₁ ^ c) ((g₁ ^ c) u) = τ • (g₁ ^ c) u - u := by
    intro u hu
    obtain ⟨g, hg⟩ := hcq
    have h0 : aeval g₁.toLinearMap (q₁.comp (X ^ c)) u = 0 := by
      rw [hg, mul_comm, map_mul, Module.End.mul_apply, hk₂ u hu, map_zero]
    rw [aeval_comp, aeval_X_pow, ← toLinearMap_pow, hq₁] at h0
    exact manyTwo_apply_sq_of_aeval (g₁ ^ c).toLinearMap τ u h0
  set b₁ : A := a₁ ^ c with hb₁
  have hb₁F₁ : b₁ ∈ F₁ := F₁.pow_mem ha₁F₁ c
  have hb₁F₂ : b₁ ∉ F₂ := fun h => hcp (by
    have := HighSetup.dvd_of_zpow_mem S.prime (S.pow' a₁) ha₁F₂ (j := (c : ℤ))
      (by rw [zpow_natCast]; exact h)
    exact_mod_cast this)
  set x : A := b₁ * a₂ with hx
  set y : A := b₁ * a₂⁻¹ with hy
  have hxa : ∀ u, ((x : elementaryGroup Q) : V ≃ₗ[K] V) u = (g₁ ^ c) (g₂ u) := fun u => rfl
  have hya : ∀ u, ((y : elementaryGroup Q) : V ≃ₗ[K] V) u = (g₁ ^ c) (g₂.symm u) :=
    fun u => rfl
  have hx₁ : ∀ u ∈ P₁, ((x : elementaryGroup Q) : V ≃ₗ[K] V) u = g₂ u := fun u hu => by
    rw [hxa]
    exact hfix₁ c _ (hst₁ u hu)
  have hx₂ : ∀ u ∈ P₂, ((x : elementaryGroup Q) : V ≃ₗ[K] V) u = (g₁ ^ c) u := fun u hu => by
    rw [hxa, hfix₂ u hu]
  have hy₁ : ∀ u ∈ P₁, ((y : elementaryGroup Q) : V ≃ₗ[K] V) u = g₂.symm u := fun u hu => by
    rw [hya]
    exact hfix₁ c _ (hst₁' u hu)
  have hy₂ : ∀ u ∈ P₂, ((y : elementaryGroup Q) : V ≃ₗ[K] V) u = (g₁ ^ c) u := fun u hu => by
    rw [hya, (LinearEquiv.symm_apply_eq g₂).mpr (hfix₂ u hu).symm]
  have hrx := manyTwo_sqRel_sup (manyTwo_sqRel_congr hst₁ hx₁ hrel₂)
    (manyTwo_sqRel_congr hst₂c hx₂ hrel₁)
  have hry := manyTwo_sqRel_sup
    (manyTwo_sqRel_congr hst₁' hy₁ (manyTwo_sqRel_symm hst₁' hrel₂))
    (manyTwo_sqRel_congr hst₂c hy₂ hrel₁)
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ F₁ ⊓ F₂, z ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : F₁ ⊓ F₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    have hle := Subgroup.index_inf_le (H := F₁) (K := F₂)
    rw [hbot, Subgroup.index_bot, S.card_eq, hi₁, hi₂] at hle
    have : p * p < p ^ 3 := by
      have := S.prime.two_le
      calc p * p = p ^ 2 := by ring
        _ < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  have hzX : ∀ u ∈ P₁ ⊔ P₂, ((z : elementaryGroup Q) : V ≃ₗ[K] V) u = u :=
    fix_sup (mem_pieceKer.mp hz.1) (mem_pieceKer.mp hz.2)
  have hz1' : (z : elementaryGroup Q) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hxj : ∀ j : ℤ, (∀ u ∈ P₁, (((x : elementaryGroup Q) ^ j : elementaryGroup Q) :
      V ≃ₗ[K] V) u = u) → (p : ℤ) ∣ j := by
    intro j hj
    refine HighSetup.dvd_of_zpow_mem S.prime (S.pow' a₂) ha₂F₁ (mem_pieceKer.mpr fun u hu => ?_)
    have h1 := hj u hu
    have e1 : ((x : elementaryGroup Q) ^ j : elementaryGroup Q) =
        ((b₁ ^ j : A) : elementaryGroup Q) * ((a₂ ^ j : A) : elementaryGroup Q) := by
      rw [← Subgroup.coe_zpow, hx, Commute.mul_zpow (S.comm' b₁ a₂), Subgroup.coe_mul]
    rw [e1, Subgroup.coe_mul, LinearEquiv.mul_apply] at h1
    have hb₁j : b₁ ^ j ∈ F₁ := F₁.zpow_mem hb₁F₁ j
    rwa [(mem_pieceKer.mp hb₁j) _ (hP₁.astable _ (a₂ ^ j).2 u hu)] at h1
  have hyj : ∀ j : ℤ, (∀ u ∈ P₁, (((y : elementaryGroup Q) ^ j : elementaryGroup Q) :
      V ≃ₗ[K] V) u = u) → (p : ℤ) ∣ j := by
    intro j hj
    have hneg : (p : ℤ) ∣ -j := by
      refine HighSetup.dvd_of_zpow_mem S.prime (S.pow' a₂) ha₂F₁
        (mem_pieceKer.mpr fun u hu => ?_)
      have h1 := hj u hu
      have e1 : ((y : elementaryGroup Q) ^ j : elementaryGroup Q) =
          ((b₁ ^ j : A) : elementaryGroup Q) * ((a₂ ^ (-j) : A) : elementaryGroup Q) := by
        rw [← Subgroup.coe_zpow, hy, Commute.mul_zpow (S.comm' b₁ a₂⁻¹), inv_zpow',
          Subgroup.coe_mul]
      rw [e1, Subgroup.coe_mul, LinearEquiv.mul_apply] at h1
      have hb₁j : b₁ ^ j ∈ F₁ := F₁.zpow_mem hb₁F₁ j
      rwa [(mem_pieceKer.mp hb₁j) _ (hP₁.astable _ (a₂ ^ (-j)).2 u hu)] at h1
    exact dvd_neg.mp hneg
  have hindx := S.indep_of_fix z.2 x.2 hz1' (U := P₁)
    (fun u hu => hzX u (Submodule.mem_sup_left hu)) hxj
  have hindy := S.indep_of_fix z.2 y.2 hz1' (U := P₁)
    (fun u hu => hzX u (Submodule.mem_sup_left hu)) hyj
  have hAst : ∀ T : Submodule K V, T ≤ P₁ ⊔ P₂ →
      (∀ t ∈ T, ((x : elementaryGroup Q) : V ≃ₗ[K] V) t ∈ T) →
      (∀ t ∈ T, ((y : elementaryGroup Q) : V ≃ₗ[K] V) t ∈ T) → AStable A T := by
    intro T hTX hTx hTy
    let G : Subgroup A :=
      { carrier := {d | ∀ t ∈ T, ((d : elementaryGroup Q) : V ≃ₗ[K] V) t ∈ T}
        mul_mem' := fun {d d'} hd hd' t ht => hd _ (hd' t ht)
        one_mem' := fun t ht => ht
        inv_mem' := fun {d} hd t ht =>
          stable_symm_of_pow (S.coe_pow_eq_one d.2) S.prime.pos hd t ht }
    have hxG : x ∈ G := hTx
    have hyG : y ∈ G := hTy
    have h12G : F₁ ⊓ F₂ ≤ G := fun f hf t ht => by
      rw [fix_sup (mem_pieceKer.mp hf.1) (mem_pieceKer.mp hf.2) t (hTX ht)]
      exact ht
    have ha₂sq : a₂ ^ 2 ∈ G := by
      have key : x * y⁻¹ = a₂ ^ 2 := by
        rw [hx, hy]
        calc b₁ * a₂ * (b₁ * a₂⁻¹)⁻¹ = (b₁ * (a₂ * a₂)) * b₁⁻¹ := by group
          _ = ((a₂ * a₂) * b₁) * b₁⁻¹ := by rw [S.comm' b₁ (a₂ * a₂)]
          _ = a₂ ^ 2 := by rw [mul_inv_cancel_right, pow_two]
      rw [← key]
      exact G.mul_mem hxG (G.inv_mem hyG)
    have ha₂G : a₂ ∈ G := by
      obtain ⟨k, hk⟩ := S.prime.odd_of_ne_two S.ne_two
      have : a₂ = (a₂ ^ 2) ^ (k + 1) := by
        rw [← pow_mul]
        have h3 : 2 * (k + 1) = p + 1 := by omega
        rw [h3, pow_succ, S.pow' a₂, one_mul]
      rw [this]
      exact G.pow_mem ha₂sq _
    have hb₁G : b₁ ∈ G := by
      have : b₁ = x * a₂⁻¹ := by rw [hx]; group
      rw [this]
      exact G.mul_mem hxG (G.inv_mem ha₂G)
    have hsup₂ : F₂ ⊔ Subgroup.zpowers b₁ = ⊤ := sup_zpowers_eq S.prime le_top
      (by rw [Subgroup.relIndex_top_right]; exact hi₂) (Subgroup.mem_top _) hb₁F₂
    have hF₁G : F₁ ≤ G := by
      intro f hf
      haveI : (Subgroup.zpowers b₁).Normal :=
        ⟨fun n hn g => by rw [S.comm' g n, mul_inv_cancel_right]; exact hn⟩
      have hfmem : f ∈ ((F₂ ⊔ Subgroup.zpowers b₁ : Subgroup A) : Set A) := by
        rw [hsup₂]
        exact Subgroup.mem_top f
      rw [Subgroup.mul_normal] at hfmem
      obtain ⟨y', hy', z', hz', hyz⟩ := Set.mem_mul.mp hfmem
      have hz'F₁ : z' ∈ F₁ := (Subgroup.zpowers_le.mpr hb₁F₁) hz'
      have hy'F₁ : y' ∈ F₁ := by
        have : y' = f * z'⁻¹ := by rw [← hyz]; group
        rw [this]
        exact F₁.mul_mem hf (F₁.inv_mem hz'F₁)
      rw [← hyz]
      exact G.mul_mem (h12G ⟨hy'F₁, hy'⟩) ((Subgroup.zpowers_le.mpr hb₁G) hz')
    have hsup₁ : F₁ ⊔ Subgroup.zpowers a₂ = ⊤ := sup_zpowers_eq S.prime le_top
      (by rw [Subgroup.relIndex_top_right]; exact hi₁) (Subgroup.mem_top _) ha₂F₁
    have hGtop : G = ⊤ := by
      rw [eq_top_iff, ← hsup₁]
      exact sup_le hF₁G (Subgroup.zpowers_le.mpr ha₂G)
    intro a ha t ht
    have : (⟨a, ha⟩ : A) ∈ G := by rw [hGtop]; exact Subgroup.mem_top _
    exact this t ht
  set X : Submodule K V := P₁ ⊔ P₂ with hXdef
  have hXreg : PolarNondegOn Q X := polarNondegOn_sup hP₁.regular hP₂.regular hperp
  have hX4 : finrank K X = 4 := by
    have hdisj := OrthSep.disjoint hP₁.regular hperp
    have := Submodule.finrank_sup_add_finrank_inf_eq P₁ P₂
    rw [hdisj.eq_bot, finrank_bot, add_zero, ← hXdef] at this
    have h₁ := (S.exists_quadratic hP₁ ha₂F₁).1
    have h₂ := (S.exists_quadratic hP₂ ha₁F₂).1
    omega
  have hXst : ∀ g : A, ∀ u ∈ X, ((g : elementaryGroup Q) : V ≃ₗ[K] V) u ∈ X := by
    intro g u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    exact Submodule.add_mem_sup (hP₁.astable g g.2 u₁ hu₁) (hP₂.astable g g.2 u₂ hu₂)
  have hroot : ∀ e ∈ X, e ≠ 0 → Q e = 0 → ∀ w ∈ X, polar Q e w = 0 →
      eichler Q e w ∈ (hyperClosure p ⊤ A).map (elementaryGroup Q).subtype := by
    intro e heX he0 heQ w hwX hew
    set gx : V ≃ₗ[K] V := ((x : elementaryGroup Q) : V ≃ₗ[K] V) with hgx
    set gy : V ≃ₗ[K] V := ((y : elementaryGroup Q) : V ≃ₗ[K] V) with hgy
    have hrxe := hrx e heX
    have hrye := hry e heX
    have hlix := manyTwo_linearIndependent_pair he0 hrxe hnoroot
    have hliy := manyTwo_linearIndependent_pair he0 hrye hnoroot
    obtain ⟨hTxQ, hTxp⟩ := manyTwo_plane_facts (mem_O (x : elementaryGroup Q)) heQ hτ hrxe
    obtain ⟨hTyQ, hTyp⟩ := manyTwo_plane_facts (mem_O (y : elementaryGroup Q)) heQ hτ hrye
    set Tx := Submodule.span K (Set.range ![e, gx e]) with hTx
    set Ty := Submodule.span K (Set.range ![e, gy e]) with hTy
    have hexT : e ∈ Tx := Submodule.subset_span ⟨0, rfl⟩
    have hexT' : e ∈ Ty := Submodule.subset_span ⟨0, rfl⟩
    have hTx2 : finrank K Tx = 2 := by rw [hTx, finrank_span_eq_card hlix]; simp
    have hTy2 : finrank K Ty = 2 := by rw [hTy, finrank_span_eq_card hliy]; simp
    have hTxg : ∀ t ∈ Tx, gx t ∈ Tx := by
      intro t ht
      obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
      rw [hrxe]
      have h1 : gx e ∈ Tx := Submodule.subset_span ⟨1, rfl⟩
      exact Tx.add_mem (Tx.smul_mem _ h1) (Tx.smul_mem _ (Tx.sub_mem (Tx.smul_mem _ h1) hexT))
    have hTyg : ∀ t ∈ Ty, gy t ∈ Ty := by
      intro t ht
      obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
      rw [hrye]
      have h1 : gy e ∈ Ty := Submodule.subset_span ⟨1, rfl⟩
      exact Ty.add_mem (Ty.smul_mem _ h1) (Ty.smul_mem _ (Ty.sub_mem (Ty.smul_mem _ h1) hexT'))
    have hTxX : Tx ≤ X := by
      rw [hTx, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact heX
      · exact hXst x e heX
    have hTyX : Ty ≤ X := by
      rw [hTy, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact heX
      · exact hXst y e heX
    have hmemx : ∀ a ∈ Tx,
        eichler Q e a ∈ (hyperClosure p ⊤ A).map (elementaryGroup Q).subtype := by
      intro a ha
      have hdet := manyTwo_det_restrict_pair hlix hrxe hTxg
      have hc := commute_eichler_of_det_one (mem_O (x : elementaryGroup Q)) hTx2 hTxQ hTxp hTxg
        hdet hexT ha
      have hcz : Commute (eichler Q e a) ((z : elementaryGroup Q) : V ≃ₗ[K] V) :=
        (show Commute ((z : elementaryGroup Q) : V ≃ₗ[K] V) (eichler Q e a) from
          commute_eichler_of_fix (mem_O _) (hzX e heX) (hzX a (hTxX ha))).symm
      exact S.mem_hyperH_of_commute z.2 x.2 hindx (eichler_mem_elementaryGroup Q e a) hcz hc
    have hmemy : ∀ a ∈ Ty,
        eichler Q e a ∈ (hyperClosure p ⊤ A).map (elementaryGroup Q).subtype := by
      intro a ha
      have hdet := manyTwo_det_restrict_pair hliy hrye hTyg
      have hc := commute_eichler_of_det_one (mem_O (y : elementaryGroup Q)) hTy2 hTyQ hTyp hTyg
        hdet hexT' ha
      have hcz : Commute (eichler Q e a) ((z : elementaryGroup Q) : V ≃ₗ[K] V) :=
        (show Commute ((z : elementaryGroup Q) : V ≃ₗ[K] V) (eichler Q e a) from
          commute_eichler_of_fix (mem_O _) (hzX e heX) (hzX a (hTyX ha))).symm
      exact S.mem_hyperH_of_commute z.2 y.2 hindy (eichler_mem_elementaryGroup Q e a) hcz hc
    set Sp : Submodule K V := X ⊓ LinearMap.ker (polarBilin Q e) with hSp
    have hmemS : ∀ v, v ∈ Sp ↔ v ∈ X ∧ polar Q e v = 0 := fun v => by
      rw [hSp, Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply]
    have hTxS : Tx ≤ Sp := fun v hv => (hmemS v).mpr ⟨hTxX hv, hTxp e hexT v hv⟩
    have hTyS : Ty ≤ Sp := fun v hv => (hmemS v).mpr ⟨hTyX hv, hTyp e hexT' v hv⟩
    have hSlt : Sp < X := by
      refine lt_of_le_of_ne inf_le_left fun hSX => ?_
      obtain ⟨u, huX, hu⟩ := hXreg.exists_polar_ne_zero heX he0
      have : u ∈ Sp := hSX ▸ huX
      exact hu ((hmemS u).mp this).2
    have hS3 : finrank K Sp ≤ 3 := by
      have := Submodule.finrank_lt_finrank_of_lt hSlt
      omega
    have hne' : Tx ≠ Ty := by
      intro hxy
      have hTsty : ∀ t ∈ Tx, gy t ∈ Tx := by rw [hxy]; exact hTyg
      have hbot := S.aniso Tx hTxQ (hAst Tx hTxX hTxg hTsty)
      rw [hbot] at hexT
      exact he0 ((Submodule.mem_bot K).mp hexT)
    have hinf : finrank K ↥(Tx ⊓ Ty) ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have e1 : Tx ⊓ Ty = Tx := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      have e2 : Tx ⊓ Ty = Ty := Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
      exact hne' (e1.symm.trans e2)
    have hsup3 : 3 ≤ finrank K ↥(Tx ⊔ Ty) := by
      have := Submodule.finrank_sup_add_finrank_inf_eq Tx Ty
      omega
    have hSeq : Tx ⊔ Ty = Sp :=
      Submodule.eq_of_le_of_finrank_le (sup_le hTxS hTyS) (by omega)
    have hwS : w ∈ Tx ⊔ Ty := by rw [hSeq, hmemS]; exact ⟨hwX, hew⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hwS
    rw [← eichler_mul (hTxp e hexT a ha) (hTyp e hexT' b hb)]
    exact Subgroup.mul_mem _ (hmemx a ha) (hmemy b hb)
  obtain ⟨u, huX, hu0, huQ⟩ := exists_singular_of_three_le_any (Q := Q) (S := X) (by omega)
  obtain ⟨u', hu'X, hu'Q, huu'⟩ := exists_partner_of_polarNondegOn hXreg huX hu0 huQ
  have hu'0 : u' ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at huu'
    exact zero_ne_one huu'
  exact eichler_mem_of_relRoot (hyperH_le_O A p) hXreg huX hu'X huQ hu'Q
    (by rw [huu']; exact one_ne_zero) (fun w hw hpw => hroot u huX hu0 huQ w hw hpw)
    (fun w hw hpw => hroot u' hu'X hu'0 hu'Q w hw hpw)

end TwoSetup

theorem elementaryGroup_le_of_two_pieces (hQ : (polarBilin Q).Nondegenerate)
    {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hK3 : 3 ≤ Nat.card K) {V₀ : Submodule K V} (hV0reg : PolarNondegOn Q V₀)
    (hV02 : finrank K V₀ ≤ 2) (hV0two : finrank K V₀ = 1 → (2 : K) ≠ 0)
    {n : ℕ} (P : Fin n → Submodule K V) (hPreg : ∀ i, PolarNondegOn Q (P i))
    (hdimP : ∀ i, finrank K (P i) = 2) (haniso : ∀ i, ∀ t ∈ P i, Q t = 0 → t = 0)
    (hPP : ∀ i j, i ≠ j → OrthSep Q (P i) (P j)) (hPV : ∀ i, OrthSep Q V₀ (P i))
    (hPsp : (⊤ : Submodule K V) ≤ V₀ ⊔ ⨆ i, P i) (hdim : 7 ≤ finrank K V)
    (hEichPair : ∀ i j : Fin n, i ≠ j → ∀ e ∈ P i ⊔ P j, ∀ w ∈ P i ⊔ P j, eichler Q e w ∈ H)
    (hEich0 : ∀ k : Fin n, ∀ e ∈ V₀ ⊔ P k, ∀ w ∈ V₀ ⊔ P k, eichler Q e w ∈ H) :
    elementaryGroup Q ≤ H := by
  classical
  have hcount : 7 ≤ finrank K V₀ + 2 * n := by
    have h1 : finrank K V ≤ finrank K ↥(V₀ ⊔ ⨆ i, P i) := by
      rw [← finrank_top K V]
      exact Submodule.finrank_mono hPsp
    have h3 := Submodule.finrank_add_le_finrank_add_finrank V₀ (⨆ i, P i)
    have h4 := manyTwo_finrank_iSup_fin_le P
    simp only [hdimP, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h4
    omega
  have hn3 : 3 ≤ n := by omega
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a = ⟨0, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b = ⟨1, by omega⟩ := ⟨_, rfl⟩
  have hab' : a ≠ b := by
    rw [ha, hb]
    intro h
    exact absurd (congrArg Fin.val h) (by simp)
  have hY : ∀ k : Fin n, k ≠ a → k ≠ b → ∃ Y : Submodule K V, P k ≤ Y ∧
      (V₀ ≠ ⊥ → V₀ ≤ Y) ∧ OrthSep Q Y (P a ⊔ P b) ∧
      PolarNondegOn Q Y ∧ (∀ e ∈ Y, ∀ w ∈ Y, eichler Q e w ∈ H) ∧
      3 ≤ finrank K Y ∧ (finrank K Y = 3 → (2 : K) ≠ 0) := by
    intro k hka hkb
    have hkab : OrthSep Q (P k) (P a ⊔ P b) :=
      manyTwo_orthSep_sup_right (hPP k a hka) (hPP k b hkb)
    by_cases hV0 : V₀ = ⊥
    ·
      have hn4 : 4 ≤ n := by
        have : finrank K V₀ = 0 := by rw [hV0]; exact finrank_bot K V
        omega
      obtain ⟨l, hl⟩ := manyTwo_exists_fin_notMem (S := {a, b, k}) (m := 3) (by omega)
        Finset.card_le_three
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      obtain ⟨hla, hlb, hlk⟩ := hl
      have hkl : OrthSep Q (P k) (P l) := hPP k l (Ne.symm hlk)
      have hlab : OrthSep Q (P l) (P a ⊔ P b) :=
        manyTwo_orthSep_sup_right (hPP l a hla) (hPP l b hlb)
      have hdisj := OrthSep.disjoint (hPreg k) hkl
      have hdimY : finrank K ↥(P k ⊔ P l) = 4 := by
        have := Submodule.finrank_sup_add_finrank_inf_eq (P k) (P l)
        rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP k, hdimP l] at this
        omega
      exact ⟨P k ⊔ P l, le_sup_left, fun h => absurd hV0 h, manyTwo_orthSep_sup_left hkab hlab,
        polarNondegOn_sup (hPreg k) (hPreg l) hkl,
        hEichPair k l (Ne.symm hlk), by omega, fun h => absurd h (by omega)⟩
    ·
      have hd0 : 1 ≤ finrank K V₀ := Submodule.one_le_finrank_iff.mpr hV0
      have hdisj : Disjoint V₀ (P k) := (OrthSep.disjoint (hPreg k) (hPV k).symm).symm
      have hdimY : finrank K ↥(V₀ ⊔ P k) = finrank K V₀ + 2 := by
        have := Submodule.finrank_sup_add_finrank_inf_eq V₀ (P k)
        rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP k] at this
        omega
      refine ⟨V₀ ⊔ P k, le_sup_right, fun _ => le_sup_left,
        manyTwo_orthSep_sup_left (manyTwo_orthSep_sup_right (hPV a) (hPV b)) hkab,
        polarNondegOn_sup hV0reg (hPreg k) (hPV k), hEich0 k, by omega, fun h3 => ?_⟩
      exact hV0two (by omega)
  have hRoot : ∀ s ∈ P a ⊔ P b, s ≠ 0 → Q s = 0 → IsRootCenter Q H s := by
    intro s hs hs0 hsQ
    have hrel : ∀ w ∈ P a ⊔ P b, polar Q s w = 0 → w ∈ rootSet Q H s :=
      fun w hw hsw => ⟨hsw, hEichPair a b hab' s hs w hw⟩
    have hYR : ∀ k : Fin n, k ≠ a → k ≠ b → ∃ Y : Submodule K V, P k ≤ Y ∧
        (V₀ ≠ ⊥ → V₀ ≤ Y) ∧ ∀ y ∈ Y, y ∈ rootSet Q H s := by
      intro k hka hkb
      obtain ⟨Y, hPY, hV0Y, hYP, hYreg, hYH, hY3, h2Y⟩ := hY k hka hkb
      have hsY : ∀ y ∈ Y, polar Q s y = 0 := fun y hy => by
        rw [polar_comm]
        exact hYP y hy s hs
      have hmix := exists_mixed_vector hH (hPreg a) (hPreg b) (hPreg k)
        (hPP a b hab') (hPP a k (Ne.symm hka)) (hPP b k (Ne.symm hkb)) (hdimP a) (hdimP b)
        (hdimP k) (haniso a) (haniso b) (haniso k) hK3 hPY hYP
        (hEichPair b k (Ne.symm hkb)) hs hs0 hsQ hrel
      exact ⟨Y, hPY, hV0Y, manyTwo_subset_rootSet_of_pivot hH hYreg hY3 h2Y hYH hsY hmix⟩
    refine ⟨hs0, hsQ, fun w hsw => ?_⟩
    have hspan : (⊤ : Submodule K V) ≤ (P a ⊔ P b) ⊔
        (V₀ ⊔ ⨆ k : {k : Fin n // k ≠ a ∧ k ≠ b}, P k.1) := by
      refine hPsp.trans (sup_le ?_ (iSup_le fun i => ?_))
      · exact le_sup_of_le_right le_sup_left
      · by_cases hia : i = a
        · rw [hia]
          exact le_sup_of_le_left le_sup_left
        by_cases hib : i = b
        · rw [hib]
          exact le_sup_of_le_left le_sup_right
        · exact le_sup_of_le_right (le_sup_of_le_right
            (le_iSup (fun k : {k : Fin n // k ≠ a ∧ k ≠ b} => P k.1) ⟨i, hia, hib⟩))
    obtain ⟨w₁, hw₁, z, hz, rfl⟩ := Submodule.mem_sup.mp (hspan (Submodule.mem_top (x := w)))
    have hzR : polar Q s z = 0 ∧ z ∈ rootSet Q H s := by
      obtain ⟨v₀, hv₀, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
      have hv₀perp : polar Q s v₀ = 0 := by
        rw [polar_comm]
        exact manyTwo_orthSep_sup_right (hPV a) (hPV b) v₀ hv₀ s hs
      have hz'R : polar Q s z' = 0 ∧ z' ∈ rootSet Q H s := by
        refine Submodule.iSup_induction (fun k : {k : Fin n // k ≠ a ∧ k ≠ b} => P k.1)
          (motive := fun x => polar Q s x = 0 ∧ x ∈ rootSet Q H s) hz'
          ?_ ⟨polar_zero_right Q s, AddSubgroup.zero_mem _⟩ ?_
        · rintro ⟨k, hka, hkb⟩ x hx
          obtain ⟨Y, hPY, -, hYR'⟩ := hYR k hka hkb
          refine ⟨?_, hYR' x (hPY hx)⟩
          rw [polar_comm]
          exact manyTwo_orthSep_sup_right (hPP k a hka) (hPP k b hkb) x hx s hs
        · rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
          exact ⟨by rw [polar_add_right, hx1, hy1, add_zero], AddSubgroup.add_mem _ hx2 hy2⟩
      have hv₀R : v₀ ∈ rootSet Q H s := by
        by_cases hV0 : V₀ = ⊥
        · rw [hV0] at hv₀
          rw [(Submodule.mem_bot K).mp hv₀]
          exact AddSubgroup.zero_mem _
        · obtain ⟨k, hk⟩ := manyTwo_exists_fin_notMem (S := {a, b}) (m := 2) (by omega)
            Finset.card_le_two
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          obtain ⟨Y, -, hV0Y, hYR'⟩ := hYR k hk.1 hk.2
          exact hYR' v₀ (hV0Y hV0 hv₀)
      exact ⟨by rw [polar_add_right, hv₀perp, hz'R.1, add_zero],
        AddSubgroup.add_mem _ hv₀R hz'R.2⟩
    have hw₁perp : polar Q s w₁ = 0 := by
      rw [polar_add_right, hzR.1, add_zero] at hsw
      exact hsw
    exact (AddSubgroup.add_mem _ (hrel w₁ hw₁ hw₁perp) hzR.2).2
  have hXreg : PolarNondegOn Q (P a ⊔ P b) :=
    polarNondegOn_sup (hPreg a) (hPreg b) (hPP a b hab')
  have hX3 : 3 ≤ finrank K ↥(P a ⊔ P b) := by
    have hdisj := OrthSep.disjoint (hPreg a) (hPP a b hab')
    have := Submodule.finrank_sup_add_finrank_inf_eq (P a) (P b)
    rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP a, hdimP b] at this
    omega
  obtain ⟨u, huX, hu0, huQ⟩ := exists_singular_of_three_le_any (Q := Q) hX3
  obtain ⟨u', hu'X, hu'Q, huu'⟩ := exists_partner_of_polarNondegOn hXreg huX hu0 huQ
  have hu'0 : u' ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at huu'
    exact zero_ne_one huu'
  exact elementaryGroup_le_of_hypPair hQ hH ⟨u, u', huQ, hu'Q, huu'⟩ (hRoot u huX hu0 huQ)
    (hRoot u' hu'X hu'0 hu'Q)

namespace TwoSetup

variable {p : ℕ} {A : Subgroup (elementaryGroup Q)} (S : TwoSetup Q p A)
include S

theorem hyperClosure_eq_top (hK3 : 3 ≤ Nat.card K) (hdim : 7 ≤ finrank K V) :
    hyperClosure p ⊤ A = ⊤ := by
  classical
  obtain ⟨n, P, hP, hPP, hPV, hPsp⟩ := S.exists_decomposition
  have hdimP : ∀ i, finrank K (P i) = 2 := fun i => by
    obtain ⟨b, hb⟩ := S.exists_not_mem_pieceKer (hP i)
    exact (S.exists_quadratic (hP i) hb).1
  have hfixV0 : ∀ f : A, ∀ u ∈ fixA A, ((f : elementaryGroup Q) : V ≃ₗ[K] V) u = u :=
    fun f u hu => hu f f.2
  have hle := elementaryGroup_le_of_two_pieces S.nondeg (hyperH_le_O A p) hK3 S.fixA_regular
    S.finrank_fixA_le_two S.two_ne_zero_of_finrank_fixA P (fun i => (hP i).regular) hdimP
    (fun i => S.anisotropic (hP i)) hPP hPV hPsp hdim ?_ ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ := hle x.2
    rwa [show x = y from Subtype.ext hyx.symm]
  · intro i j hij
    by_cases hker : pieceKer A (P i) = pieceKer A (P j)
    · intro e he w hw
      have hfix : ∀ f ∈ pieceKer A (P i), ∀ u ∈ P i ⊔ P j,
          ((f : elementaryGroup Q) : V ≃ₗ[K] V) u = u := fun f hf =>
        fix_sup (mem_pieceKer.mp hf) (mem_pieceKer.mp (hker ▸ hf))
      exact S.eichler_mem_of_fix (S.index_pieceKer (hP i)) (fun f hf => hfix f hf e he)
        (fun f hf => hfix f hf w hw)
    · exact S.eichler_mem_pair (hP i) (hP j) hker (hPP i j hij)
  · intro k e he w hw
    have hfix : ∀ f ∈ pieceKer A (P k), ∀ u ∈ fixA A ⊔ P k,
        ((f : elementaryGroup Q) : V ≃ₗ[K] V) u = u := fun f hf =>
      fix_sup (hfixV0 f) (mem_pieceKer.mp hf)
    exact S.eichler_mem_of_fix (S.index_pieceKer (hP k)) (fun f hf => hfix f hf e he)
      (fun f hf => hfix f hf w hw)

end TwoSetup

end Setup

section F2

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

@[expose] noncomputable def sgn2 (x : K) : ℤ :=
  haveI := Classical.decEq K
  if x = 0 then 1 else -1

theorem sgn2_zero : sgn2 (0 : K) = 1 := by
  unfold sgn2
  exact if_pos rfl

theorem sgn2_of_ne {x : K} (hx : x ≠ 0) : sgn2 x = -1 := by
  unfold sgn2
  exact if_neg hx

omit [Finite K] in
theorem eq_one_of_ne_zero_of_card [Finite K] (hK2 : Nat.card K = 2) {x : K} (hx : x ≠ 0) :
    x = 1 := by
  classical
  haveI := Fintype.ofFinite K
  have hu : Fintype.card Kˣ = 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK2]
  have h1 : Units.mk0 x hx = 1 := Fintype.card_le_one_iff.mp hu.le _ _
  simpa using congrArg Units.val h1

theorem one_add_one_eq_zero_of_card (hK2 : Nat.card K = 2) : (1 : K) + 1 = 0 := by
  by_contra h
  have h1 := eq_one_of_ne_zero_of_card hK2 h
  exact one_ne_zero (by linear_combination h1)

theorem sgn2_add (hK2 : Nat.card K = 2) (x y : K) : sgn2 (x + y) = sgn2 x * sgn2 y := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_add, sgn2_zero, one_mul]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [add_zero, sgn2_zero, mul_one]
  rw [eq_one_of_ne_zero_of_card hK2 hx, eq_one_of_ne_zero_of_card hK2 hy,
    one_add_one_eq_zero_of_card hK2, sgn2_zero, sgn2_of_ne one_ne_zero]
  norm_num

theorem sgn2_sum (hK2 : Nat.card K = 2) {ι : Type*} (s : Finset ι) (f : ι → K) :
    sgn2 (∑ i ∈ s, f i) = ∏ i ∈ s, sgn2 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn2_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn2_add hK2, ih]

@[expose] noncomputable def chi2 (Q : QuadraticForm K V) (S : Submodule K V) : ℤ :=
  ∑ᶠ x : S, sgn2 (Q x)

theorem chi2_bot : chi2 Q ⊥ = 1 := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype (⊥ : Submodule K V) := Fintype.ofFinite _
  rw [chi2, finsum_eq_sum_of_fintype, Fintype.sum_unique]
  have : ((default : (⊥ : Submodule K V)) : V) = 0 :=
    (Submodule.mem_bot K).mp (default : (⊥ : Submodule K V)).2
  rw [this, QuadraticMap.map_zero, sgn2_zero]

theorem chi2_sup (hK2 : Nat.card K = 2) {U W : Submodule K V} (hUW : Disjoint U W)
    (horth : OrthSep Q U W) : chi2 Q (U ⊔ W) = chi2 Q U * chi2 Q W := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype U := Fintype.ofFinite U
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype ↥(U ⊔ W) := Fintype.ofFinite _
  rw [chi2, chi2, chi2, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype]
  let f : U × W → ↥(U ⊔ W) := fun x => ⟨x.1 + x.2, Submodule.add_mem_sup x.1.2 x.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u, w⟩ ⟨u', w'⟩ h
      have h1 : (u : V) + w = u' + w' := congrArg Subtype.val h
      have h2 : (u : V) - u' = w' - w := sub_eq_sub_iff_add_eq_add.mpr (h1.trans (add_comm _ _))
      have hU : (u : V) - u' ∈ U := U.sub_mem u.2 u'.2
      have hW : (u : V) - u' ∈ W := h2 ▸ W.sub_mem w'.2 w.2
      have h0 := Submodule.disjoint_def.mp hUW _ hU hW
      have hu : u = u' := Subtype.ext (sub_eq_zero.mp h0)
      have hw : w = w' := Subtype.ext (by rw [hu] at h1; exact add_left_cancel h1)
      rw [hu, hw]
    · rintro ⟨x, hx⟩
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
      exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl⟩
  rw [← Fintype.sum_bijective f hf (fun x => sgn2 (Q ((x.1 : V) + x.2)))
    (fun y => sgn2 (Q (y : V))) (fun x => rfl), Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  rw [QuadraticMap.map_add Q, horth u u.2 w w.2, add_zero, sgn2_add hK2]

theorem chi2_plane (hK2 : Nat.card K = 2) {P : Submodule K V} (hP : finrank K P = 2)
    (haniso : ∀ s ∈ P, Q s = 0 → s = 0) : chi2 Q P = -2 := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype P := Fintype.ofFinite P
  rw [chi2, finsum_eq_sum_of_fintype]
  have hcard : Fintype.card P = 4 := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := K), hK2, hP]
    norm_num
  have key : ∀ x : P, sgn2 (Q x) = (if x = 0 then 2 else 0) - 1 := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [if_pos rfl, Submodule.coe_zero, QuadraticMap.map_zero, sgn2_zero]
      norm_num
    · rw [if_neg hx, sgn2_of_ne fun h => hx (Subtype.ext (haniso x x.2 h))]
      norm_num
  rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp [hcard]

theorem chi2_iSup (hK2 : Nat.card K = 2) {n : ℕ} (P : Fin n → Submodule K V)
    (hreg : ∀ i, PolarNondegOn Q (P i)) (horth : ∀ i j, i ≠ j → OrthSep Q (P i) (P j))
    (hdim : ∀ i, finrank K (P i) = 2) (haniso : ∀ i, ∀ s ∈ P i, Q s = 0 → s = 0) :
    chi2 Q (⨆ i, P i) = (-2) ^ n ∧ finrank K ↥(⨆ i, P i) = 2 * n := by
  induction n with
  | zero => simp [chi2_bot]
  | succ n ih =>
    have h1 : (⨆ i : Fin (n + 1), P i) = (⨆ i : Fin n, P i.castSucc) ⊔ P (Fin.last n) := by
      apply le_antisymm
      · refine iSup_le fun i => ?_
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact le_sup_right
        · exact le_sup_of_le_left (le_iSup (fun i : Fin n => P i.castSucc) j)
      · exact sup_le (iSup_le fun j => le_iSup P j.castSucc) (le_iSup P (Fin.last n))
    obtain ⟨ihχ, ihd⟩ := ih (fun i => P i.castSucc) (fun i => hreg _)
      (fun i j hij => horth _ _ fun h => hij (Fin.castSucc_injective _ h)) (fun i => hdim _)
      (fun i => haniso _)
    have horth' : OrthSep Q (⨆ i : Fin n, P i.castSucc) (P (Fin.last n)) := by
      intro x hx y hy
      refine Submodule.iSup_induction (fun i : Fin n => P i.castSucc)
        (motive := fun x => polar Q x y = 0) hx ?_ ?_ ?_
      · intro i x hx'
        exact horth _ _ (Fin.castSucc_lt_last i).ne x hx' y hy
      · exact polar_zero_left Q y
      · intro a b ha hb
        rw [polar_add_left, ha, hb, add_zero]
    have hdisj : Disjoint (⨆ i : Fin n, P i.castSucc) (P (Fin.last n)) :=
      (OrthSep.disjoint (hreg (Fin.last n)) horth'.symm).symm
    rw [h1]
    refine ⟨?_, ?_⟩
    · rw [chi2_sup hK2 hdisj horth', ihχ, chi2_plane hK2 (hdim _) (haniso _), pow_succ]
    · have := Submodule.finrank_sup_add_finrank_inf_eq (⨆ i : Fin n, P i.castSucc)
        (P (Fin.last n))
      rw [hdisj.eq_bot, finrank_bot, add_zero, ihd, hdim] at this
      omega

theorem chi2_top_eq [Fintype V] : chi2 Q ⊤ = ∑ v : V, sgn2 (Q v) := by
  classical
  haveI : Fintype (⊤ : Submodule K V) := Fintype.ofFinite _
  rw [chi2, finsum_eq_sum_of_fintype]
  exact Fintype.sum_equiv Submodule.topEquiv.toEquiv _ _ (fun x => rfl)

namespace TwoSetup

variable {p : ℕ} {A : Subgroup (elementaryGroup Q)} (S : TwoSetup Q p A)
include S

theorem chi_top (hK2 : Nat.card K = 2) :
    ∃ m : ℕ, finrank K V = 2 * m ∧ chi2 Q ⊤ = (-2) ^ m := by
  classical
  obtain ⟨n, P, hP, hPP, hPV, hPsp⟩ := S.exists_decomposition
  have hdimP : ∀ i, finrank K (P i) = 2 := fun i => by
    obtain ⟨b, hb⟩ := S.exists_not_mem_pieceKer (hP i)
    exact (S.exists_quadratic (hP i) hb).1
  obtain ⟨hχP, hdP⟩ := chi2_iSup hK2 P (fun i => (hP i).regular) hPP hdimP
    (fun i => S.anisotropic (hP i))
  have htop : fixA A ⊔ ⨆ i, P i = ⊤ := eq_top_iff.mpr hPsp
  have horth : OrthSep Q (fixA A) (⨆ i, P i) := by
    intro x hx y hy
    refine Submodule.iSup_induction P (motive := fun y => polar Q x y = 0) hy ?_ ?_ ?_
    · intro i y hy'
      exact hPV i x hx y hy'
    · exact polar_zero_right Q x
    · intro a b ha hb
      rw [polar_add_right, ha, hb, add_zero]
  have hdisj : Disjoint (fixA A) (⨆ i, P i) := OrthSep.disjoint S.fixA_regular horth
  have hχ := chi2_sup hK2 hdisj horth
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq (fixA A) (⨆ i, P i)
  rw [hdisj.eq_bot, finrank_bot, add_zero, htop, finrank_top, hdP] at hfin
  rw [htop] at hχ
  rw [hχ, hχP]
  have h2K : (2 : K) = 0 := by rw [← one_add_one_eq_two]; exact one_add_one_eq_zero_of_card hK2
  have hd0 := S.finrank_fixA_le_two
  rcases (show finrank K (fixA A) = 0 ∨ finrank K (fixA A) = 1 ∨ finrank K (fixA A) = 2 by
    omega) with h0 | h1 | h2
  · rw [Submodule.finrank_eq_zero.mp h0, chi2_bot]
    exact ⟨n, by omega, by ring⟩
  · exact absurd h2K (S.two_ne_zero_of_finrank_fixA h1)
  · rw [chi2_plane hK2 h2 (fun s hs hsQ => S.fixA_aniso hs hsQ)]
    exact ⟨n + 1, by omega, by ring⟩

end TwoSetup

end F2

section Models

variable {K : Type} [Field K] [Finite K]

theorem univ_eq_pair (hK2 : Nat.card K = 2) [Fintype K] [DecidableEq K] :
    (Finset.univ : Finset K) = {0, 1} := by
  symm
  apply Finset.eq_univ_of_card
  rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK2]

theorem sum_sgn2_mul (hK2 : Nat.card K = 2) [Fintype K] :
    ∑ w : K × K, sgn2 (w.1 * w.2) = 2 := by
  classical
  rw [Fintype.sum_prod_type, univ_eq_pair hK2, Finset.sum_pair zero_ne_one,
    Finset.sum_pair zero_ne_one, Finset.sum_pair zero_ne_one]
  simp only [zero_mul, one_mul, mul_one, sgn2_zero, sgn2_of_ne (one_ne_zero (α := K))]
  norm_num

theorem sum_sgn2_pairs (hK2 : Nat.card K = 2) [Fintype K] (m : ℕ) :
    ∑ x : Fin m → K, ∑ y : Fin m → K, ∏ i, sgn2 (x i * y i) = 2 ^ m := by
  classical
  have e1 := Fintype.sum_prod_type' (fun (x y : Fin m → K) => ∏ i, sgn2 (x i * y i))
  have e2 := (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => K) (fun _ => K)).sum_comp
    (fun xy : (Fin m → K) × (Fin m → K) => ∏ i, sgn2 (xy.1 i * xy.2 i))
  have h := Fintype.prod_sum (fun (_ : Fin m) (w : K × K) => sgn2 (w.1 * w.2))
  rw [sum_sgn2_mul hK2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← e1, ← e2, h]
  rfl

theorem sum_sgn2_aniso (hK2 : Nat.card K = 2) [Fintype K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∑ z : Fin 2 → K, sgn2 (z 0 ^ 2 + b * z 0 * z 1 + c * z 1 ^ 2) = -2 := by
  classical
  have hzero : ∀ z : Fin 2 → K, z 0 ^ 2 + b * z 0 * z 1 + c * z 1 ^ 2 = 0 → z = 0 := by
    intro z hz
    by_cases h1 : z 1 = 0
    · rw [h1] at hz
      have h0 : z 0 = 0 := by
        have : z 0 ^ 2 = 0 := by linear_combination hz
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      funext i
      fin_cases i
      · exact h0
      · exact h1
    · exfalso
      apply hirr (z 0 / z 1)
      field_simp
      linear_combination hz
  have key : ∀ z : Fin 2 → K, sgn2 (z 0 ^ 2 + b * z 0 * z 1 + c * z 1 ^ 2) =
      (if z = 0 then 2 else 0) - 1 := by
    intro z
    by_cases hz : z = 0
    · subst hz
      simp [sgn2_zero]
    · rw [if_neg hz, sgn2_of_ne fun h => hz (hzero z h)]
      norm_num
  rw [Finset.sum_congr rfl fun z _ => key z, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  have hcard : Fintype.card (Fin 2 → K) = 4 := by
    rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hK2]
    norm_num
  simp [hcard]

open CFSG.LieType.Universal.Spin

theorem chi2_quadPlus (hK2 : Nat.card K = 2) (r : ℕ) : chi2 (quadPlus r K) ⊤ = 2 ^ r := by
  classical
  haveI := Fintype.ofFinite K
  rw [chi2_top_eq]
  simp only [quadPlus_apply, sgn2_sum hK2]
  rw [← (Equiv.sumArrowEquivProdArrow (Fin r) (Fin r) K).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  exact sum_sgn2_pairs hK2 r

theorem chi2_quadMinus (hK2 : Nat.card K = 2) {r : ℕ} (hr : 1 ≤ r) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : chi2 (quadMinus r K b c) ⊤ = -2 ^ r := by
  classical
  haveI := Fintype.ofFinite K
  rw [chi2_top_eq]
  simp only [quadMinus_apply]
  have hsplit : ∀ v : Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K,
      sgn2 (∑ i, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) + v (Sum.inr (Sum.inr 0)) ^ 2 +
        b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + c * v (Sum.inr (Sum.inr 1)) ^ 2) =
      (∏ i, sgn2 (v (Sum.inl i) * v (Sum.inr (Sum.inl i)))) *
        sgn2 (v (Sum.inr (Sum.inr 0)) ^ 2 + b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) +
          c * v (Sum.inr (Sum.inr 1)) ^ 2) := by
    intro v
    rw [← sgn2_sum hK2, ← sgn2_add hK2]
    congr 1
    ring
  simp only [hsplit]
  rw [← (Equiv.sumArrowEquivProdArrow (Fin (r - 1)) (Fin (r - 1) ⊕ Fin 2) K).symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  have h2 : ∀ x : Fin (r - 1) → K, ∑ w : Fin (r - 1) ⊕ Fin 2 → K,
      (∏ i, sgn2 (x i * w (Sum.inl i))) *
        sgn2 (w (Sum.inr 0) ^ 2 + b * w (Sum.inr 0) * w (Sum.inr 1) + c * w (Sum.inr 1) ^ 2) =
      (∑ y : Fin (r - 1) → K, ∏ i, sgn2 (x i * y i)) * (-2) := by
    intro x
    rw [← (Equiv.sumArrowEquivProdArrow (Fin (r - 1)) (Fin 2) K).symm.sum_comp,
      Fintype.sum_prod_type]
    simp only [Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, sum_sgn2_aniso hK2 hirr]
  simp only [h2]
  rw [← Finset.sum_mul, sum_sgn2_pairs hK2]
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

end Models

section Cover

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_twoSetup {G : Type} [Group G] {π : elementaryGroup Q →* G}
    (hc : IsOrthogonalCover Q π) {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) {E₀ : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E₀) (hcard : Nat.card E₀ = p ^ 3)
    (haniso : ∀ W : Submodule K V, (∀ x ∈ W, Q x = 0) →
      (∀ g : elementaryGroup Q, π g ∈ E₀ → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W) → W = ⊥) :
    ∃ A : Subgroup (elementaryGroup Q), TwoSetup Q p A ∧ A.map π = E₀ ∧ Disjoint A π.ker := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  have hp2 : p ≠ 2 := (manyTwo_ne_two_and_ne_ringChar hp h2).1
  have hE1 : 1 < Nat.card E₀ := by
    rw [hcard]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have h1 : ∀ a b : elementaryGroup Q, a = b := fun a b =>
      Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)
    have h2' : ∀ a b : G, a = b := fun a b => by
      obtain ⟨a', rfl⟩ := hc.surjective a
      obtain ⟨b', rfl⟩ := hc.surjective b
      rw [h1 a' b']
    have h3 : Nat.card E₀ ≤ 1 := Finite.card_le_one_iff_subsingleton.2
      ⟨fun a b => Subtype.ext (h2' _ _)⟩
    omega
  have hker := not_dvd_card_ker_of_scalar hc hp hp2
  have hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨A, hAE, hAdis, hAcomm, hAexp, hAcard⟩ :=
    exists_lift_elemAbelian π hc.surjective hker hcomm hE.2
  have hAaniso : ∀ W : Submodule K V, (∀ w ∈ W, Q w = 0) → AStable A W → W = ⊥ := by
    intro W hWQ hWst
    refine haniso W hWQ fun g hg w hw => ?_
    rw [← hAE] at hg
    obtain ⟨a, ha, hag⟩ := hg
    have hz : a⁻¹ * g ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hag, inv_mul_cancel]
    obtain ⟨c, hcz⟩ := CFSG.ClassicalGroups.Orthogonal.mem_scalars.1 (hc.ker_scalar _ hz)
    have hga : g = a * (a⁻¹ * g) := by group
    rw [hga, Subgroup.coe_mul, LinearEquiv.mul_apply, hcz w]
    exact hWst a ha _ (W.smul_mem c hw)
  exact ⟨A, ⟨hc.nondegenerate, hp, hpK, hAcomm, hAexp, hAcard.trans hcard, h2, hAaniso⟩, hAE,
    hAdis⟩

theorem hyperGen_of_orderOf_two {G : Type} [Group G] {π : elementaryGroup Q →* G}
    (hc : IsOrthogonalCover Q π) {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) (hK3 : 3 ≤ Nat.card K)
    (hdim : 7 ≤ finrank K V) {E₀ : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E₀)
    (hcard : Nat.card E₀ = p ^ 3)
    (haniso : ∀ W : Submodule K V, (∀ x ∈ W, Q x = 0) →
      (∀ g : elementaryGroup Q, π g ∈ E₀ → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W) → W = ⊥) :
    HyperGen p (⊤ : Subgroup G) E₀ := by
  obtain ⟨A, S, hAE, hAdis⟩ := exists_twoSetup hc hp hpK h2 hE hcard haniso
  have htop := S.hyperClosure_eq_top hK3 hdim
  intro k _
  obtain ⟨g, rfl⟩ := hc.surjective k
  have hg : g ∈ hyperClosure p ⊤ A := by
    rw [htop]
    exact Subgroup.mem_top g
  exact map_hyperClosure_le_of_lift hAE hAdis ⟨g, hg, rfl⟩

theorem chi_top_of_aniso (hK2 : Nat.card K = 2) {G : Type} [Group G]
    {π : elementaryGroup Q →* G} (hc : IsOrthogonalCover Q π) {p : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) {E₀ : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E₀) (hcard : Nat.card E₀ = p ^ 3)
    (haniso : ∀ W : Submodule K V, (∀ x ∈ W, Q x = 0) →
      (∀ g : elementaryGroup Q, π g ∈ E₀ → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W) → W = ⊥) :
    ∃ m : ℕ, finrank K V = 2 * m ∧ chi2 Q ⊤ = (-2) ^ m := by
  obtain ⟨A, S, -, -⟩ := exists_twoSetup hc hp hpK h2 hE hcard haniso
  exact S.chi_top hK2

end Cover

section Model

open CFSG.LieType.Universal.Spin

theorem exists_orth_model_dim {d : TauCeti.ValidLieTypeIndex} (hd : IsOrthogonalIndex d.1)
    {p : ℕ} (hp : p.Prime) (hpd : p ≠ d.1.characteristic) :
    ∃ (q : TauCeti.PrimePower) (K V : Type) (_ : Field K) (_ : Finite K) (_ : AddCommGroup V)
      (_ : Module K V) (_ : FiniteDimensional K V) (Q : QuadraticForm K V)
      (π : elementaryGroup Q →* Cat d),
      (∃ r, d.1 = .B r q ∨ d.1 = .D r q ∨ d.1 = .twistedD r q) ∧ Nat.card K = q.card ∧
        IsOrthogonalCover Q π ∧ (p : K) ≠ 0 ∧ 7 ≤ finrank K V := by
  obtain ⟨d, hv⟩ := d
  rcases hd with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  · have hq' : p ≠ q.p := by simpa using hpd
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h2 : (2 : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 := by
      have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
        q.exponent_pos hcard
      have : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p :=
        ringChar.of_eq hring
      intro h
      have : q.p ∣ 2 := (CharP.cast_eq_zero_iff
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p 2).mp (by exact_mod_cast h)
      exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
    have hpK : (p : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 :=
      CFSG.LieType.SeitzGeneration.ExcHigh.natCast_ne_zero_of_not_dvd_card hp
        (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
    have hreg := regular_quadOdd
      (K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) h2 hr3
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadOdd r _)
      (commutator_orthogonalGroup_quadOdd h2 hr3) hreg.1
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq hr3)
    have hdim : 7 ≤ finrank ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)
        (Fin r ⊕ Fin r ⊕ Unit → ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
      omega
    exact ⟨q, _, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _,
      π, ⟨r, Or.inl rfl⟩, by rw [hcard, TauCeti.PrimePower.card_def], hπ, hpK, hdim⟩
  · have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hpK : (p : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) ≠ 0 :=
      CFSG.LieType.SeitzGeneration.ExcHigh.natCast_ne_zero_of_not_dvd_card hp
        (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
    have hreg := regular_quadPlus
      (K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) (n := r) (by omega)
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadPlus r _)
      (commutator_orthogonalGroup_quadPlus (by omega)) hreg.1
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv)
    have hdim : 7 ≤ finrank ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)
        (Fin r ⊕ Fin r → ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
      omega
    exact ⟨q, _, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _,
      π, ⟨r, Or.inr (Or.inl rfl)⟩, by rw [hcard, TauCeti.PrimePower.card_def], hπ, hpK, hdim⟩
  · have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hpK : (p : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩)) ≠ 0 :=
      CFSG.LieType.SeitzGeneration.ExcHigh.natCast_ne_zero_of_not_dvd_card hp
        (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
    have hreg := regular_quadMinus (n := r) hr4 hirr
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadMinus r _ b c)
      (commutator_orthogonalGroup_quadMinus hr4 hirr) hreg.1 e
    have hdim : 7 ≤ finrank ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩)
        (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 →
          ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩)) := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
      omega
    exact ⟨q, _, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _,
      π, ⟨r, Or.inr (Or.inr rfl)⟩, by rw [hcard, TauCeti.PrimePower.card_def], hπ, hpK, hdim⟩

end Model

theorem card_ne_two_of_B {d : TauCeti.LieTypeIndex} (ho : IsOrthogonalIndex d) {r : ℕ}
    {q : TauCeti.PrimePower} (h : d = .B r q) : q.card ≠ 2 := by
  intro hq2
  rcases ho with ⟨r', q', h', -, hq'⟩ | ⟨r', q', h'⟩ | ⟨r', q', h'⟩ <;> rw [h] at h'
  · cases h'
    apply hq'
    exact ((Nat.Prime.pow_eq_iff Nat.prime_two).mp
      (by simpa [TauCeti.PrimePower.card_def] using hq2)).1
  · exact absurd h' (by simp)
  · exact absurd h' (by simp)

theorem hyperGen_orth_of_orderOf_two {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOrthogonalIndex d.1) {p : ℕ} (hp : p.Prime) (hpd : p ≠ d.1.characteristic)
    (h2 : OrthOrderTwo d.1 p) (hq : ∀ (r : ℕ) (q : TauCeti.PrimePower),
      (d.1 = .B r q ∨ d.1 = .D r q ∨ d.1 = .twistedD r q) → q.card ≠ 2)
    {E₀ : Subgroup (Cat d)} (hE : CFSG.Open.IsElemAbelian p E₀) (hcard : Nat.card E₀ = p ^ 3)
    (hred : ¬ OReducible d p E₀) : HyperGen p (⊤ : Subgroup (Cat d)) E₀ := by
  obtain ⟨q, K, V, _, _, _, _, _, Q, π, ⟨r, hdq⟩, hK, hc, hpK, hdim⟩ :=
    exists_orth_model_dim hd hp hpd
  obtain ⟨r', q', hdq', h2'⟩ := h2
  obtain rfl := eq_of_orth_index hdq' hdq
  have hK3 : 3 ≤ Nat.card K := by
    have h1 : 2 ≤ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
    have := hq r q hdq
    rw [hK]
    omega
  refine hyperGen_of_orderOf_two hc hp hpK (by rw [hK]; exact h2') hK3 hdim hE hcard ?_
  intro W hWQ hWst
  by_contra hW0
  exact hred ⟨K, V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q,
    π, hc, hpK, W, hW0, hWQ, hWst⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeOrthTwoAux

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open Module CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeOrthTwoAux

@[expose] def OrthOverF2 (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), (d = .D r q ∨ d = .twistedD r q) ∧ q.card = 2

@[expose] def SeitzGoodInnerOrthTwoF2 : Prop :=
  SeitzHyperLie fun d p E₀ => IsOrthogonalIndex d.1 ∧ ¬ OReducible d p E₀ ∧
    SeitzGoodIndex p d.1 ∧ OrthOrderTwo d.1 p ∧ OrthOverF2 d.1

theorem seitzHyperLie_orthTwo_off_F2 :
    SeitzHyperLie fun d p E₀ => IsOrthogonalIndex d.1 ∧ ¬ OReducible d p E₀ ∧
      OrthOrderTwo d.1 p ∧ ¬ OrthOverF2 d.1 := by
  intro d p hp _ hpd _ E₀ hE hcard ⟨ho, hred, h2, hF2⟩
  refine hyperGen_orth_of_orderOf_two ho hp hpd h2 (fun r q hdq hq2 => ?_) hE hcard hred
  rcases hdq with h | h | h
  · exact card_ne_two_of_B ho h hq2
  · exact hF2 ⟨r, q, Or.inl h, hq2⟩
  · exact hF2 ⟨r, q, Or.inr h, hq2⟩

theorem seitzGoodInnerOrthTwo_of_F2 (h : SeitzGoodInnerOrthTwoF2) : SeitzGoodInnerOrthTwo := by
  intro d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨ho, hred, hgood, h2⟩
  by_cases hF2 : OrthOverF2 d.1
  · exact h d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨ho, hred, hgood, h2, hF2⟩
  · exact seitzHyperLie_orthTwo_off_F2 d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨ho, hred, h2, hF2⟩

open CFSG.LieType.Universal.Spin in
theorem seitzGoodInnerOrthTwoF2_holds : SeitzGoodInnerOrthTwoF2 := by
  intro d p hp _ hpd _ E₀ hE hcard ⟨_, hred, hgood, h2, hF2⟩
  exfalso
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, hdq, hq2⟩ := hF2
  change d = .D r q ∨ d = .twistedD r q at hdq
  have hqp : q.p = 2 ∧ q.exponent = 1 := (Nat.Prime.pow_eq_iff Nat.prime_two).mp
    (show q.p ^ q.exponent = 2 by simpa [TauCeti.PrimePower.card_def] using hq2)
  have hIT : IsTwoPow q 1 := hqp
  obtain ⟨r', q', hdq', h2'⟩ := h2
  have hqq : q' = q := SeitzCubeInnerAux.eq_of_orth_index (Or.inr hdq) hdq'
  rw [hqq, hq2] at h2'
  have hp3 : p = 3 := by
    have hsq : ((2 : ℕ) : ZMod p) ^ 2 = 1 := by
      have := pow_orderOf_eq_one ((2 : ℕ) : ZMod p)
      rwa [h2'] at this
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      have : ((3 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) ^ 2 - 1 := by push_cast; ring
      rw [this, hsq, sub_self]
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
  have hq' : p ≠ q.p := by rw [hqp.1, hp3]; norm_num
  rcases hdq with rfl | rfl
  ·
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    have hsix : ¬ IsSixIndex (.D r q) := by
      simp [IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex, IsTwoPow, hqp]
    have hexc : ¬ ExcIndex p (.D r q) := hgood.resolve_right hsix
    have hodd : Odd r := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      apply hexc
      refine Or.inl ⟨hp3, ?_⟩
      by_cases h4 : r = 4
      · exact Or.inr ⟨hIT, h4⟩
      · obtain ⟨k, hk⟩ := hev
        exact Or.inl ⟨Or.inl hIT, ⟨k, hk⟩, by omega⟩
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hK2 : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) = 2 := by
      rw [hcardK, hqp.1, hqp.2, pow_one]
    have hpK : (p : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) ≠ 0 :=
      CFSG.LieType.SeitzGeneration.ExcHigh.natCast_ne_zero_of_not_dvd_card hp
        (by rw [hcardK]; exact not_dvd_pow_of_ne hp q.prime_p hq')
    have hreg := regular_quadPlus
      (K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) (n := r) (by omega)
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadPlus r _)
      (commutator_orthogonalGroup_quadPlus (by omega)) hreg.1
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv)
    obtain ⟨m, hm, hχ⟩ := chi_top_of_aniso hK2 hπ hp hpK (by rw [hK2]; exact h2') hE hcard
      fun W hWQ hWst => by
        by_contra hW0
        exact hred ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance,
          inferInstance, _, π, hπ, hpK, W, hW0, hWQ, hWst⟩
    have hfin : finrank ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)
        (Fin r ⊕ Fin r → ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) = 2 * r := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
      ring
    have hmr : m = r := by omega
    rw [hmr, chi2_quadPlus hK2, Odd.neg_pow hodd] at hχ
    have : (0 : ℤ) < 2 ^ r := by positivity
    linarith
  ·
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    have hsix : ¬ IsSixIndex (.twistedD r q) := by
      simp [IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex, IsTwoPow, hqp]
    have hexc : ¬ ExcIndex p (.twistedD r q) := hgood.resolve_right hsix
    have hev : Even r := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      apply hexc
      refine Or.inl ⟨hp3, Or.inl hIT, hodd, ?_⟩
      obtain ⟨k, hk⟩ := hodd
      omega
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hK2 : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) = 2 := by
      rw [hcardK, hqp.1, hqp.2, pow_one]
    have hpK : (p : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩)) ≠ 0 :=
      CFSG.LieType.SeitzGeneration.ExcHigh.natCast_ne_zero_of_not_dvd_card hp
        (by rw [hcardK]; exact not_dvd_pow_of_ne hp q.prime_p hq')
    have hreg := regular_quadMinus (n := r) hr4 hirr
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadMinus r _ b c)
      (commutator_orthogonalGroup_quadMinus hr4 hirr) hreg.1 e
    obtain ⟨m, hm, hχ⟩ := chi_top_of_aniso hK2 hπ hp hpK (by rw [hK2]; exact h2') hE hcard
      fun W hWQ hWst => by
        by_contra hW0
        exact hred ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance,
          inferInstance, _, π, hπ, hpK, W, hW0, hWQ, hWst⟩
    have hfin : finrank ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩)
        (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 →
          ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩)) = 2 * r := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp
      omega
    have hmr : m = r := by omega
    rw [hmr, chi2_quadMinus hK2 (by omega) hirr, Even.neg_pow hev] at hχ
    have : (0 : ℤ) < 2 ^ r := by positivity
    linarith

theorem seitzGoodInnerOrthTwo_holds : SeitzGoodInnerOrthTwo :=
  seitzGoodInnerOrthTwo_of_F2 seitzGoodInnerOrthTwoF2_holds

theorem seitzGoodInnerOrth_holds : SeitzGoodInnerOrth :=
  seitzGoodInnerOrth_of_two seitzGoodInnerOrthTwo_holds

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
