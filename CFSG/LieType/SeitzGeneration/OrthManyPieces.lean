module

public import CFSG.LieType.SeitzGeneration.OrthStatementScopes
public import CFSG.LieType.SeitzGeneration.OrthSdLines
public import CFSG.LieType.SeitzGeneration.OrthEvenSingular

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryMixing CFSG.RankThree.Classical CFSG.Open OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Basic

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem nondegenerate_of_kernelLineData (hK : KernelLineData Q p E) :
    (polarBilin Q).Nondegenerate := by
  classical
  have key : ∀ v : V, (∀ w, polar Q v w = 0) → v = 0 := by
    intro v hv
    have hv' : v ∈ ⨆ i, innerSummand p E i := by
      rw [hK.internal.submodule_iSup_eq_top]
      exact Submodule.mem_top
    obtain ⟨f, hfi, hfv⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ v).mp hv'
    have hf0 : ∀ i, f i = 0 := by
      intro i
      have hreg := (hK.regular i).1 ⟨f i, hfi i⟩ (fun y => ?_)
      · exact congrArg Subtype.val hreg
      · have h1 : polarBilin Q v (y : V) = 0 := by
          rw [polarBilin_apply_apply]
          exact hv y
        rw [← hfv] at h1
        have h2 : polarBilin Q (f.sum fun _ x => x) (y : V) =
            f.sum fun _ x => polarBilin Q x (y : V) := by
          simp only [Finsupp.sum, map_sum, LinearMap.sum_apply]
        rw [h2, Finsupp.sum_eq_single i] at h1
        · simpa [LinearMap.BilinForm.restrict_apply, polarBilin_apply_apply] using h1
        · intro j _ hji
          exact hK.orth j i hji (f j) (hfi j) y y.2
        · intro _
          simp
    rw [← hfv, Finsupp.ext hf0 (g := 0)]
    simp
  exact ⟨fun v hv => key v fun w => by simpa using hv w, fun v hv => key v fun w => by
    rw [polar_comm]; simpa using hv w⟩

omit [Finite K] [FiniteDimensional K V] in
theorem polarNondegOn_planeFixSpace (hK : KernelLineData Q p E) :
    PolarNondegOn Q (planeFixSpace E) :=
  polarNondegOn_of_nondegenerate (hK.regular none)

omit [Finite K] [FiniteDimensional K V] in
theorem two_ne_zero_of_finrank_planeFixSpace (hK : KernelLineData Q p E)
    (h1 : Module.finrank K (planeFixSpace E) = 1) : (2 : K) ≠ 0 := by
  intro h2
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  apply hv0
  refine Subtype.ext (polarNondegOn_planeFixSpace hK v v.2 fun y hy => ?_)
  obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
  have hvv : polar Q (v : V) (v : V) = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hy' : y = c • (v : V) := (congrArg Subtype.val hc).symm
  rw [hy', polar_smul_right_eq, hvv, mul_zero]

omit [Finite K] [FiniteDimensional K V] in
theorem eq_zero_of_singular_planeFixSpace (hNS : OrthNoInvariantSingular Q E) {x : V}
    (hx : x ∈ planeFixSpace E) (hxQ : Q x = 0) : x = 0 := by
  have := hNS (Submodule.span K {x}) ?_ ?_
  · simpa using Submodule.span_singleton_eq_bot.mp this
  · intro e he v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hfix : ((e : orthDerived Q) : V ≃ₗ[K] V) x = x := hx _ ⟨e, he, rfl⟩
    rw [map_smul, hfix]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  · intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul_eq_sq, hxQ, mul_zero]

theorem finrank_planeFixSpace_le_two (hNS : OrthNoInvariantSingular Q E) :
    finrank K (planeFixSpace E) ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx, hx0, hxQ⟩ := exists_singular_of_three_le_any (Q := Q) (S := planeFixSpace E) h
  exact hx0 (eq_zero_of_singular_planeFixSpace hNS hx hxQ)

end Basic

section Piece

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

omit [Finite K] [FiniteDimensional K V] in
@[expose] def IsPiece (Q : QuadraticForm K V) (E : Subgroup (orthDerived Q)) (P : Submodule K V) :
    Prop :=
  P ≠ ⊥ ∧ PolarNondegOn Q P ∧ Disjoint P (planeFixSpace E) ∧ OrthSep Q P (planeFixSpace E) ∧
    (∀ x ∈ E, ∀ u ∈ P, ((x : orthDerived Q) : V ≃ₗ[K] V) u ∈ P) ∧
    ∀ S : Submodule K V, S ≤ P → (∀ x ∈ E, ∀ u ∈ S, ((x : orthDerived Q) : V ≃ₗ[K] V) u ∈ S) →
      S = ⊥ ∨ S = P

omit [Finite K] [FiniteDimensional K V] in
@[expose] def EStable (E : Subgroup (orthDerived Q)) (S : Submodule K V) : Prop :=
  ∀ x ∈ E, ∀ u ∈ S, ((x : orthDerived Q) : V ≃ₗ[K] V) u ∈ S

section Accessors

variable {E : Subgroup (orthDerived Q)} {P : Submodule K V}

omit [Finite K] [FiniteDimensional K V] in
theorem IsPiece.ne_bot (hP : IsPiece Q E P) : P ≠ ⊥ := hP.1

omit [Finite K] [FiniteDimensional K V] in
theorem IsPiece.regular (hP : IsPiece Q E P) : PolarNondegOn Q P := hP.2.1

omit [Finite K] [FiniteDimensional K V] in
theorem IsPiece.disjoint (hP : IsPiece Q E P) : Disjoint P (planeFixSpace E) := hP.2.2.1

omit [Finite K] [FiniteDimensional K V] in
theorem IsPiece.orthSep (hP : IsPiece Q E P) : OrthSep Q P (planeFixSpace E) := hP.2.2.2.1

omit [Finite K] [FiniteDimensional K V] in
theorem IsPiece.eStable (hP : IsPiece Q E P) : EStable E P := hP.2.2.2.2.1

omit [Finite K] [FiniteDimensional K V] in
theorem IsPiece.minimal (hP : IsPiece Q E P) {S : Submodule K V} (hSP : S ≤ P)
    (hS : EStable E S) : S = ⊥ ∨ S = P := hP.2.2.2.2.2 S hSP hS

end Accessors

section Stable

variable {E : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem EStable.symm_apply_mem (hK : KernelLineData Q p E) (hp : 0 < p) {S : Submodule K V}
    (hS : EStable E S) {x : orthDerived Q} (hx : x ∈ E) {u : V} (hu : u ∈ S) :
    ((x : orthDerived Q) : V ≃ₗ[K] V).symm u ∈ S :=
  stable_symm_of_pow (coe_pow_eq_one hK ⟨x, hx⟩) hp (fun s hs => hS x hx s hs) u hu

omit [Finite K] [FiniteDimensional K V] in
theorem EStable.perp (hK : KernelLineData Q p E) (hp : 0 < p) {S : Submodule K V}
    (hS : EStable E S) : EStable E (OrthBlk.perp Q S) := by
  intro x hx t ht
  refine mem_perp.mpr fun s hs => ?_
  have hxO := orthDerived_mem_orthogonalGroup (Q := Q) (g := x)
  have hs' := hS.symm_apply_mem hK hp hx hs
  have := polar_map_of_mem hxO (((x : orthDerived Q) : V ≃ₗ[K] V).symm s) t
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this]
  exact mem_perp.mp ht _ hs'

omit [Finite K] [FiniteDimensional K V] in
theorem EStable.of_fixed {S : Submodule K V} (hS : ∀ x ∈ E, ∀ u ∈ S,
    ((x : orthDerived Q) : V ≃ₗ[K] V) u = u) : EStable E S :=
  fun x hx u hu => by rw [hS x hx u hu]; exact hu

omit [Finite K] [FiniteDimensional K V] in
theorem EStable.inf {S T : Submodule K V} (hS : EStable E S) (hT : EStable E T) :
    EStable E (S ⊓ T) := fun x hx u hu => ⟨hS x hx u hu.1, hT x hx u hu.2⟩

end Stable

section Decomposition

variable {E : Subgroup (orthDerived Q)}

omit [Finite K] in
theorem exists_minimal_stable {W : Submodule K V} (hW : W ≠ ⊥) (hWst : EStable E W) :
    ∃ S : Submodule K V, S ≤ W ∧ S ≠ ⊥ ∧ EStable E S ∧
      ∀ S' : Submodule K V, S' ≤ S → EStable E S' → S' = ⊥ ∨ S' = S := by
  obtain ⟨S, ⟨hSW, hS0, hSst⟩, hSmin⟩ := (wellFounded_lt (α := Submodule K V)).has_min
    {S | S ≤ W ∧ S ≠ ⊥ ∧ EStable E S} ⟨W, le_rfl, hW, hWst⟩
  refine ⟨S, hSW, hS0, hSst, fun S' hS'S hS'st => ?_⟩
  by_cases hS'0 : S' = ⊥
  · exact Or.inl hS'0
  · right
    by_contra hne
    exact hSmin S' ⟨hS'S.trans hSW, hS'0, hS'st⟩ (lt_of_le_of_ne hS'S hne)

omit [Finite K] in
theorem polarNondegOn_of_minimal (hK : KernelLineData Q p E) (hp : 0 < p)
    (hNS : OrthNoInvariantSingular Q E) {S : Submodule K V} (hS0 : S ≠ ⊥)
    (hSV : Disjoint S (planeFixSpace E)) (hst : EStable E S)
    (hmin : ∀ S' : Submodule K V, S' ≤ S → EStable E S' → S' = ⊥ ∨ S' = S) :
    PolarNondegOn Q S := by
  classical
  have hR : EStable E (S ⊓ OrthBlk.perp Q S) := hst.inf (hst.perp hK hp)
  rcases hmin _ inf_le_left hR with hR0 | hRS
  · intro x hxS hx
    have hxR : x ∈ S ⊓ OrthBlk.perp Q S :=
      ⟨hxS, mem_perp.mpr fun s hs => by rw [polar_comm]; exact hx s hs⟩
    rw [hR0] at hxR
    exact (Submodule.mem_bot K).mp hxR
  · exfalso
    have hSS : ∀ s ∈ S, ∀ t ∈ S, polar Q s t = 0 := fun s hs t ht => by
      have ht' : t ∈ S ⊓ OrthBlk.perp Q S := by rw [hRS]; exact ht
      exact mem_perp.mp ht'.2 s hs
    let S₀ : Submodule K V :=
      { carrier := {s | s ∈ S ∧ Q s = 0}
        add_mem' := fun {a b} ha hb => ⟨S.add_mem ha.1 hb.1, by
          rw [QuadraticMap.map_add Q a b, ha.2, hb.2, hSS a ha.1 b hb.1]; simp⟩
        zero_mem' := ⟨S.zero_mem, QuadraticMap.map_zero Q⟩
        smul_mem' := fun c a ha => ⟨S.smul_mem c ha.1, by
          rw [map_smul_eq_sq, ha.2, mul_zero]⟩ }
    have hS₀st : EStable E S₀ := fun x hx u hu =>
      ⟨hst x hx u hu.1, by
        rw [map_of_mem (orthDerived_mem_orthogonalGroup (Q := Q) (g := x)), hu.2]⟩
    rcases hmin S₀ (fun s hs => hs.1) hS₀st with h0 | hfull
    · obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
      have hsV : s ∉ planeFixSpace E := fun hsV =>
        hs0 (Submodule.disjoint_def.mp hSV s hsS hsV)
      obtain ⟨x, hx, hxs⟩ : ∃ x ∈ E, ((x : orthDerived Q) : V ≃ₗ[K] V) s ≠ s := by
        by_contra hcon
        push Not at hcon
        exact hsV fun g hg => by
          obtain ⟨y, hy, rfl⟩ := hg
          exact hcon y hy
      have hxsS := hst x hx s hsS
      have hQ2 : (2 : K) * Q s = 0 := by rw [← polar_self_eq_two_mul]; exact hSS s hsS s hsS
      have hd : (((x : orthDerived Q) : V ≃ₗ[K] V) s - s) ∈ S₀ := by
        refine ⟨S.sub_mem hxsS hsS, ?_⟩
        rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right,
          map_of_mem (orthDerived_mem_orthogonalGroup (Q := Q) (g := x)),
          hSS _ hxsS s hsS]
        linear_combination hQ2
      rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
      exact hxs hd
    · refine hS0 (hNS S hst fun v hv => ?_)
      have hv' : v ∈ S₀ := by rw [hfull]; exact hv
      exact hv'.2

omit [Finite K] in
theorem exists_pieces_of_stable (hK : KernelLineData Q p E) (hp : 0 < p)
    (hNS : OrthNoInvariantSingular Q E) :
    ∀ (n : ℕ) (W : Submodule K V), finrank K W = n → EStable E W → PolarNondegOn Q W →
      OrthSep Q W (planeFixSpace E) →
      ∃ (m : ℕ) (P : Fin m → Submodule K V), (∀ i, IsPiece Q E (P i)) ∧
        (∀ i j, i ≠ j → OrthSep Q (P i) (P j)) ∧ (∀ i, P i ≤ W) ∧ W ≤ ⨆ i, P i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hWst hWreg hWV
  by_cases hW0 : W = ⊥
  · exact ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp [hW0]⟩
  obtain ⟨S, hSW, hS0, hSst, hSmin⟩ := exists_minimal_stable hW0 hWst
  have hV0 := polarNondegOn_planeFixSpace hK
  have hSdisj : Disjoint S (planeFixSpace E) := by
    rw [Submodule.disjoint_def]
    intro x hxS hxV
    exact hV0 x hxV fun y hy => hWV x (hSW hxS) y hy
  have hSreg : PolarNondegOn Q S := polarNondegOn_of_minimal hK hp hNS hS0 hSdisj hSst hSmin
  set W' : Submodule K V := W ⊓ OrthBlk.perp Q S with hW'
  have hW'st : EStable E W' := hWst.inf (hSst.perp hK hp)
  have hW'reg : PolarNondegOn Q W' := polarNondegOn_inf_perp hWreg hSreg hSW
  have hW'V : OrthSep Q W' (planeFixSpace E) := fun w hw v hv => hWV w hw.1 v hv
  have hlt : finrank K W' < n := by
    rw [← hn]
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => ?_)
    obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    have : s ∈ W' := by rw [h]; exact hSW hsS
    exact hs0 (hSreg s hsS fun t ht => by rw [polar_comm]; exact mem_perp.mp this.2 t ht)
  obtain ⟨m, P', hP'piece, hP'orth, hP'le, hP'sp⟩ :=
    ih _ hlt W' rfl hW'st hW'reg hW'V
  have hSpiece : IsPiece Q E S :=
    ⟨hS0, hSreg, hSdisj, fun s hs v hv => hWV s (hSW hs) v hv, hSst, hSmin⟩
  refine ⟨m + 1, Fin.cons S P', ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hSpiece
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
    · simpa using hSW
    · simpa using (hP'le j).trans inf_le_left
  · intro w hw
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_add_inf_perp hSreg hSW hw
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_iSup_of_mem (0 : Fin (m + 1)) (by simpa using ha)
    · have hr' : r ∈ ⨆ j, P' j := hP'sp hr
      refine (iSup_le fun j => ?_ : (⨆ j, P' j) ≤ ⨆ i, (Fin.cons S P' : Fin (m + 1) → _) i) hr'
      exact le_iSup_of_le j.succ (by simp)

omit [Finite K] [FiniteDimensional K V] in
theorem nontrivial_of_card_sq (hp : 1 < p) (hcard : Nat.card E = p ^ 2) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have : Subsingleton E :=
    ⟨fun x y => Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _))⟩
  have h1 : Nat.card E = 1 := Nat.card_of_subsingleton (1 : E)
  have h2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp
  omega

end Decomposition

section NoSingularStruct

theorem exists_piece_decomposition (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) (hNS : OrthNoInvariantSingular Q E) :
    ∃ (n : ℕ) (P : Fin n → Submodule K V), (∀ i, IsPiece Q E (P i)) ∧
      (∀ i j, i ≠ j → OrthSep Q (P i) (P j)) ∧ (∀ i, OrthSep Q (planeFixSpace E) (P i)) ∧
      (⊤ : Submodule K V) ≤ planeFixSpace E ⊔ ⨆ i, P i := by
  classical
  haveI : Nontrivial V := nontrivial_of_card_sq hp.one_lt hcard
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  have hV0 := polarNondegOn_planeFixSpace hK
  have hWst : EStable E (OrthBlk.perp Q (planeFixSpace E)) :=
    (EStable.of_fixed (S := planeFixSpace E) fun x hx u hu => hu _ ⟨x, hx, rfl⟩).perp hK hp.pos
  obtain ⟨n, P, hP, hPP, hPle, hPsp⟩ := exists_pieces_of_stable hK hp.pos hNS _
    (OrthBlk.perp Q (planeFixSpace E)) rfl hWst (polarNondegOn_perp hQ hV0)
    (fun w hw v hv => by rw [polar_comm]; exact mem_perp.mp hw v hv)
  refine ⟨n, P, hP, hPP, fun i s hs t ht => mem_perp.mp (hPle i ht) s hs, ?_⟩
  rw [← (isCompl_planeFixSpace hK).sup_eq_top]
  exact sup_le_sup_left hPsp _

end NoSingularStruct

section SmallFacts

variable {E : Subgroup (orthDerived Q)}

theorem exists_pieces_diff_lines (hK : KernelLineData Q p E) (hp : p.Prime)
    (hpl : p ≠ ringChar K) {n : ℕ} {P : Fin n → Submodule K V} (hP : ∀ i, IsPiece Q E (P i))
    (hspan : (⊤ : Submodule K V) ≤ planeFixSpace E ⊔ ⨆ i, P i)
    {M : Fin n → Subgroup E} (hM : ∀ i, Nat.card (M i) = p ∧ P i ≤ lineSpace (M i)) :
    ∃ i j, M i ≠ M j := by
  classical
  by_contra hcon
  push Not at hcon
  have hfinE : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hK.card]; exact pow_ne_zero 2 hp.ne_zero)
  obtain ⟨x₀, hx₀1, hx₀⟩ : ∃ x₀ : E, x₀ ≠ 1 ∧
      ∀ i, ∀ u ∈ P i, ((x₀ : orthDerived Q) : V ≃ₗ[K] V) u = u := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by
        rw [hK.card]; exact Nat.one_lt_pow two_ne_zero hp.one_lt)
      obtain ⟨a, ha⟩ := exists_ne (1 : E)
      exact ⟨a, ha, fun i => i.elim0⟩
    · let i₀ : Fin n := ⟨0, hn⟩
      haveI : Nontrivial (M i₀) := Finite.one_lt_card_iff_nontrivial.mp (by
        rw [(hM i₀).1]; exact hp.one_lt)
      obtain ⟨m, hm⟩ := exists_ne (1 : M i₀)
      refine ⟨(m : E), fun h => hm (Subtype.ext h), fun i u hu => ?_⟩
      have hle : P i ≤ lineSpace (M i₀) := by rw [← hcon i i₀]; exact (hM i).2
      exact apply_eq_of_mem_lineFixSpace (E := E) m (lineSpace_le_lineFixSpace _ (hle hu))
  have hle : (⊤ : Submodule K V) ≤ fixedSpace ((x₀ : orthDerived Q) : V ≃ₗ[K] V) := by
    refine hspan.trans (sup_le (fun u hu => mem_fixedSpace.mpr ?_)
      (iSup_le fun i u hu => mem_fixedSpace.mpr (hx₀ i u hu)))
    exact hu _ ⟨x₀, x₀.2, rfl⟩
  exact hx₀1 (Subtype.ext (Subtype.ext (LinearEquiv.ext fun v =>
    mem_fixedSpace.mp (hle Submodule.mem_top))))

end SmallFacts

end Piece

section PolyAlgebra

open Polynomial

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_irreducible_of_simple_endomorphism [Nontrivial W] {p : ℕ} (hp : 0 < p)
    (g : Module.End K W)
    (hpow : g ^ p = 1) (hfix : ∀ v, g v = v → v = 0)
    (hsimple : ∀ S : Submodule K W, (∀ s ∈ S, g s ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∃ h : K[X], h.Monic ∧ Irreducible h ∧ h ∣ X ^ p - 1 ∧ h ≠ X - 1 ∧ aeval g h = 0 ∧
      finrank K W = h.natDegree := by
  classical
  haveI : Nontrivial (AEval' g) := (AEval.of K W g).toEquiv.symm.nontrivial
  haveI hso : IsSimpleOrder (Submodule K[X] (AEval' g)) :=
    { eq_bot_or_eq_top := fun N => by
        let S : Submodule K W := (N.restrictScalars K).comap (AEval.of K W g : W →ₗ[K] AEval' g)
        have hSst : ∀ s ∈ S, g s ∈ S := fun s hs => by
          have h1 : (AEval.of K W g) (g s) = (X : K[X]) • (AEval.of K W g) s :=
            (AEval'.X_smul_of g s).symm
          show (AEval.of K W g) (g s) ∈ N
          rw [h1]
          exact N.smul_mem _ hs
        rcases hsimple S hSst with h0 | h1
        · left
          rw [eq_bot_iff]
          intro z hz
          have : (AEval.of K W g).symm z ∈ S := by
            show (AEval.of K W g) ((AEval.of K W g).symm z) ∈ N
            simpa using hz
          rw [h0, Submodule.mem_bot] at this
          simpa using congrArg (AEval.of K W g) this
        · right
          rw [eq_top_iff]
          intro z _
          have : (AEval.of K W g).symm z ∈ S := by rw [h1]; trivial
          have h2 : (AEval.of K W g) ((AEval.of K W g).symm z) ∈ N := this
          simpa using h2 }
  haveI : IsSimpleModule K[X] (AEval' g) := ⟨⟩
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule K[X] (AEval' g)›
  set h₀ : K[X] := Submodule.IsPrincipal.generator I with hh₀
  have hI0 : I = Ideal.span {h₀} := (Ideal.span_singleton_generator I).symm
  have hann : ∀ f : K[X], (∀ w : W, aeval g f w = 0) → f ∈ I := by
    intro f hf
    let q₀ : K[X] ⧸ I := Submodule.Quotient.mk (1 : K[X])
    have h1 : f • (e.symm q₀ : AEval' g) = 0 := by
      have := AEval.of_aeval_smul g f ((AEval.of K W g).symm (e.symm q₀))
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      have : aeval g f • ((AEval.of K W g).symm (e.symm q₀)) = 0 := hf _
      rw [this, map_zero]
    have h2 : f • q₀ = 0 := by
      have := congrArg e h1
      rwa [map_smul, LinearEquiv.apply_symm_apply, map_zero] at this
    have h4 : (Submodule.Quotient.mk (f • (1 : K[X])) : K[X] ⧸ I) = 0 := by
      rw [Submodule.Quotient.mk_smul]
      exact h2
    have := (Submodule.Quotient.mk_eq_zero I).mp h4
    simpa using this
  have hXp : (X ^ p - 1 : K[X]) ∈ I := by
    refine hann _ fun w => ?_
    have : aeval g (X ^ p - 1 : K[X]) = 0 := by
      rw [map_sub, map_pow, aeval_X, map_one, hpow, sub_self]
    rw [this]; rfl
  have hne : (X ^ p - 1 : K[X]) ≠ 0 := by
    have := X_pow_sub_C_ne_zero hp (1 : K)
    simpa using this
  have hh₀ne : h₀ ≠ 0 := by
    intro h0
    rw [hI0, h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hXp
    exact hne hXp
  have hirr₀ : Irreducible h₀ :=
    ((Ideal.span_singleton_prime hh₀ne).mp (hI0 ▸ hI.isPrime)).irreducible
  have hunit : IsUnit (C (leadingCoeff h₀)⁻¹) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hh₀ne)))
  set h : K[X] := h₀ * C (leadingCoeff h₀)⁻¹ with hh
  have hmon : h.Monic := monic_mul_leadingCoeff_inv hh₀ne
  have hirr : Irreducible h := irreducible_mul_leadingCoeff_inv.mpr hirr₀
  have hIh : I = Ideal.span {h} := by rw [hI0, hh, Ideal.span_singleton_mul_right_unit hunit]
  have hhI : h ∈ I := hIh ▸ Ideal.mem_span_singleton_self h
  have hker : ∀ w : W, aeval g h w = 0 := by
    intro w
    apply (AEval.of K W g).injective
    have h1 := AEval.of_aeval_smul g h w
    rw [map_zero]
    change (AEval.of K W g) (aeval g h • w) = 0
    rw [h1]
    apply e.injective
    rw [map_smul, map_zero]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective I (e (AEval.of K W g w))
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right y I hhI
  refine ⟨h, hmon, hirr, Ideal.mem_span_singleton.mp (hIh ▸ hXp), ?_, LinearMap.ext hker, ?_⟩
  · intro hX
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    refine hv (hfix v ?_)
    have := hker v
    rw [hX, map_sub, aeval_X, map_one] at this
    simpa [sub_eq_zero] using this
  · have e1 : W ≃ₗ[K] K[X] ⧸ I := (AEval.of K W g).trans (e.restrictScalars K)
    rw [e1.finrank_eq, hIh]
    exact finrank_quotient_span_eq_natDegree

theorem natDegree_eq_orderOf_of_dvd [Finite K] {p : ℕ} (hp : p.Prime) (hpl : p ≠ ringChar K)
    {h : K[X]} (hmon : h.Monic) (hirr : Irreducible h) (hdvd : h ∣ X ^ p - 1)
    (hne : h ≠ X - 1) : h.natDegree = orderOf ((Nat.card K : ℕ) : ZMod p) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact p.Prime := ⟨hp⟩
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
  have hcop : (ringChar K).Coprime p := (Nat.coprime_primes hℓ hp).mpr (Ne.symm hpl)
  have hdvdΦ : h ∣ cyclotomic p K := by
    have h1 : h ∣ cyclotomic p K * (X - 1) := by
      rw [cyclotomic_prime_mul_X_sub_one]; exact hdvd
    rcases hirr.prime.dvd_or_dvd h1 with h2 | h2
    · exact h2
    · exfalso
      have h3 : (X - 1 : K[X]) = X - C 1 := by rw [map_one]
      rw [h3] at h2 hne
      exact hne (eq_of_monic_of_associated hmon (monic_X_sub_C 1)
        (hirr.associated_of_dvd (irreducible_X_sub_C 1) h2))
  rw [natDegree_of_dvd_cyclotomic_of_irreducible hcard hcop hdvdΦ hirr, ← orderOf_units,
    ZMod.coe_unitOfCoprime, Nat.card_eq_fintype_card, hcard]

end PolyAlgebra

section Intertwine

open Polynomial

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem coe_pow_of_intertwine {U : Submodule K V} {A : Module.End K U} {B : Module.End K V}
    (hAB : ∀ u : U, (A u : V) = B u) (n : ℕ) (u : U) : (((A ^ n) u : U) : V) = (B ^ n) u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ih, hAB]

theorem coe_aeval_of_intertwine {U : Submodule K V} {A : Module.End K U} {B : Module.End K V}
    (hAB : ∀ u : U, (A u : V) = B u) (q : K[X]) (u : U) :
    ((aeval A q u : U) : V) = aeval B q (u : V) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial]
    change ((algebraMap K (Module.End K U) c) ((A ^ n) u) : V) =
      (algebraMap K (Module.End K V) c) ((B ^ n) u)
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul,
      coe_pow_of_intertwine hAB]

end Intertwine


section Line

open Polynomial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)} {P : Submodule K V}

omit [Finite K] [FiniteDimensional K V] in
theorem avgOp_mem_of_eStable {D : Subgroup E} [Fintype D] {S : Submodule K V} (hS : EStable E S)
    {x : V} (hx : x ∈ S) : avgOp (orthRep E) D x ∈ S := by
  rw [avgOp_def, LinearMap.smul_apply, LinearMap.sum_apply]
  refine S.smul_mem _ (Submodule.sum_mem _ fun d _ => ?_)
  exact hS d d.1.2 x hx

theorem IsPiece.exists_lineSpace_le (hK : KernelLineData Q p E) (hp : p.Prime)
    (hpl : p ≠ ringChar K) (hP : IsPiece Q E P) :
    ∃ M : Subgroup E, Nat.card M = p ∧ P ≤ lineSpace M := by
  classical
  have hQ := nondegenerate_of_kernelLineData hK
  have hfinE : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hK.card]; exact pow_ne_zero 2 hp.ne_zero)
  letI : Fintype E := Fintype.ofFinite E
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_ne_ringChar hp hpl
  have hsum := sum_lineIdem (K := K) (V := V) (ρ := orthRep E) hp hK.exp hK.card hpK
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP.ne_bot
  have hx : ∑ i, lineIdem (orthRep E) p i x = x := by
    have := LinearMap.congr_fun hsum x
    simpa [LinearMap.sum_apply] using this
  have hterm : ∀ i, lineIdem (orthRep E) p i x ∈ P := by
    intro i
    rcases i with _ | ⟨M, hM⟩
    · exact avgOp_mem_of_eStable hP.eStable hxP
    · simp only [lineIdem, LinearMap.sub_apply]
      exact P.sub_mem (avgOp_mem_of_eStable hP.eStable hxP) (avgOp_mem_of_eStable hP.eStable hxP)
  have hnone : lineIdem (orthRep E) p none x = 0 := by
    have h1 : lineIdem (orthRep E) p none x ∈ innerSummand p E none := by
      rw [innerSummand_eq_range hQ hK.card hpK none]
      exact ⟨x, rfl⟩
    exact Submodule.disjoint_def.mp hP.disjoint _ (hterm none) h1
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := Finset.univ) (f := fun i => lineIdem (orthRep E) p i x) (by rw [hx]; exact hx0)
  rcases i with _ | ⟨M, hM⟩
  · exact absurd hnone hi
  · refine ⟨M, hM, ?_⟩
    have hmemL : lineIdem (orthRep E) p (some ⟨M, hM⟩) x ∈ lineSpace M := by
      have : lineIdem (orthRep E) p (some ⟨M, hM⟩) x ∈ innerSummand p E (some ⟨M, hM⟩) := by
        rw [innerSummand_eq_range hQ hK.card hpK]
        exact ⟨x, rfl⟩
      exact this
    have hS : EStable E (P ⊓ lineSpace M) :=
      hP.eStable.inf (fun y hy u hu => lineSpace_stable hK.comm M ⟨y, hy⟩ hu)
    rcases hP.minimal inf_le_left hS with h0 | hP'
    · exfalso
      apply hi
      have : lineIdem (orthRep E) p (some ⟨M, hM⟩) x ∈ P ⊓ lineSpace M := ⟨hterm _, hmemL⟩
      rw [h0] at this
      exact (Submodule.mem_bot K).mp this
    · intro u hu
      have : u ∈ P ⊓ lineSpace M := by rw [hP']; exact hu
      exact this.2


omit [Finite K] [FiniteDimensional K V] in
theorem act_comm_apply (hcomm : ∀ x y : E, x * y = y * x) (x y : E) (v : V) :
    ((x : orthDerived Q) : V ≃ₗ[K] V) (((y : orthDerived Q) : V ≃ₗ[K] V) v) =
      ((y : orthDerived Q) : V ≃ₗ[K] V) (((x : orthDerived Q) : V ≃ₗ[K] V) v) := by
  have := LinearEquiv.congr_fun (congrArg (fun z : E => ((z : orthDerived Q) : V ≃ₗ[K] V))
    (hcomm x y)) v
  exact this

omit [Finite K] [FiniteDimensional K V] in
theorem IsPiece.eq_zero_of_fixed (hP : IsPiece Q E P) (hcomm : ∀ x y : E, x * y = y * x) {c : E}
    (hc : ∃ u ∈ P, ((c : orthDerived Q) : V ≃ₗ[K] V) u ≠ u) {u : V} (hu : u ∈ P)
    (hfix : ((c : orthDerived Q) : V ≃ₗ[K] V) u = u) : u = 0 := by
  have hFst : EStable E (P ⊓ LinearMap.ker
      (((c : orthDerived Q) : V ≃ₗ[K] V).toLinearMap - LinearMap.id)) := by
    intro x hx v hv
    refine ⟨hP.eStable x hx v hv.1, LinearMap.mem_ker.mpr ?_⟩
    have h : ((c : orthDerived Q) : V ≃ₗ[K] V) v = v := by
      simpa [sub_eq_zero] using LinearMap.mem_ker.mp hv.2
    show ((c : orthDerived Q) : V ≃ₗ[K] V) (((x : orthDerived Q) : V ≃ₗ[K] V) v) -
      ((x : orthDerived Q) : V ≃ₗ[K] V) v = 0
    rw [← act_comm_apply hcomm ⟨x, hx⟩ c v, h, sub_self]
  rcases hP.minimal inf_le_left hFst with h0 | hPF
  · have hu' : u ∈ P ⊓ LinearMap.ker
        (((c : orthDerived Q) : V ≃ₗ[K] V).toLinearMap - LinearMap.id) :=
      ⟨hu, LinearMap.mem_ker.mpr (by simp [hfix])⟩
    rw [h0] at hu'
    exact (Submodule.mem_bot K).mp hu'
  · exfalso
    obtain ⟨u', hu', hne⟩ := hc
    have hu'F : u' ∈ P ⊓ LinearMap.ker
        (((c : orthDerived Q) : V ≃ₗ[K] V).toLinearMap - LinearMap.id) := by
      rw [hPF]; exact hu'
    exact hne (by simpa [sub_eq_zero] using LinearMap.mem_ker.mp hu'F.2)

omit [Finite K] [FiniteDimensional K V] in
theorem eq_top_of_line_lt (hK : KernelLineData Q p E) (hp : p.Prime) {M N : Subgroup E}
    (hM : Nat.card M = p) (hMN : M ≤ N) (hne : N ≠ M) : N = ⊤ := by
  have hfinE : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hK.card]; exact pow_ne_zero 2 hp.ne_zero)
  have hdvd1 : p ∣ Nat.card N := hM ▸ Subgroup.card_dvd_of_le hMN
  have hdvd2 : Nat.card N ∣ p ^ 2 := hK.card ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk⟩ := hdvd1
  rw [hk] at hdvd2
  have hk' : k ∣ p := by
    have : p * k ∣ p * p := by rwa [_root_.sq] at hdvd2
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
  rcases (Nat.dvd_prime hp).mp hk' with rfl | rfl
  · exact absurd (Subgroup.eq_of_le_of_card_ge hMN (by rw [hk, hM, mul_one])).symm hne
  · exact Subgroup.eq_top_of_card_eq _ (by rw [hk, hK.card, _root_.sq])

omit [Finite K] [FiniteDimensional K V] in
@[expose] def actKernel (E : Subgroup (orthDerived Q)) (P : Submodule K V) : Subgroup E :=
  (stabPW P).comap ((orthDerived Q).subtype.comp E.subtype)

omit [Finite K] [FiniteDimensional K V] in
theorem mem_actKernel {x : E} :
    x ∈ actKernel E P ↔ ∀ u ∈ P, ((x : orthDerived Q) : V ≃ₗ[K] V) u = u := Iff.rfl

omit [Finite K] [FiniteDimensional K V] in
theorem IsPiece.actKernel_eq (hK : KernelLineData Q p E) (hp : p.Prime) (hP : IsPiece Q E P)
    {M : Subgroup E} (hM : Nat.card M = p) (hPM : P ≤ lineSpace M) : actKernel E P = M := by
  have hMA : M ≤ actKernel E P := fun m hm => by
    rw [mem_actKernel]
    intro u hu
    exact apply_eq_of_mem_lineFixSpace (E := E) ⟨m, hm⟩ (lineSpace_le_lineFixSpace M (hPM hu))
  have hnetop : actKernel E P ≠ ⊤ := by
    intro htop
    apply hP.ne_bot
    rw [eq_bot_iff]
    intro u hu
    have hV0 : u ∈ planeFixSpace E := fun g hg => by
      obtain ⟨y, hy, rfl⟩ := hg
      have hy' : (⟨y, hy⟩ : E) ∈ actKernel E P := by rw [htop]; exact Subgroup.mem_top _
      exact (mem_actKernel.mp hy') u hu
    exact (Submodule.mem_bot K).mpr (Submodule.disjoint_def.mp hP.disjoint u hu hV0)
  by_contra hne
  exact hnetop (eq_top_of_line_lt hK hp hM hMA hne)

omit [Finite K] [FiniteDimensional K V] in
theorem EStable.of_apply_mem (hK : KernelLineData Q p E) (hp : p.Prime)
    {M : Subgroup E} (hM : Nat.card M = p) (hker : actKernel E P = M) {a : E} (haM : a ∉ M)
    {S : Submodule K V} (hSP : S ≤ P)
    (hSa : ∀ s ∈ S, ((a : orthDerived Q) : V ≃ₗ[K] V) s ∈ S) : EStable E S := by
  let T : Subgroup E :=
    { carrier := {b | ∀ s ∈ S, ((b : orthDerived Q) : V ≃ₗ[K] V) s ∈ S}
      mul_mem' := fun {b c} hb hc s hs => hb _ (hc s hs)
      one_mem' := fun s hs => hs
      inv_mem' := fun {b} hb s hs =>
        stable_symm_of_pow (coe_pow_eq_one hK b) hp.pos hb s hs }
  have hMT : M ≤ T := fun m hm s hs => by
    have hm' : m ∈ actKernel E P := by rw [hker]; exact hm
    rw [mem_actKernel.mp hm' s (hSP hs)]
    exact hs
  have haT : a ∈ T := hSa
  have hsup : M ⊔ Subgroup.zpowers a = ⊤ := by
    refine eq_top_of_line_lt hK hp hM le_sup_left fun h => haM ?_
    rw [← h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have htop : T = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le hMT (Subgroup.zpowers_le.mpr haT)
  intro x hx s hs
  have : (⟨x, hx⟩ : E) ∈ T := by rw [htop]; exact Subgroup.mem_top _
  exact this s hs

theorem IsPiece.exists_primary (hK : KernelLineData Q p E) (hp : p.Prime) (hpl : p ≠ ringChar K)
    (hP : IsPiece Q E P) {M : Subgroup E} (hM : Nat.card M = p) (hker : actKernel E P = M)
    {a : E} (haM : a ∉ M) :
    ∃ h : K[X], h.Monic ∧ Irreducible h ∧ h ≠ X - 1 ∧ h = reciprocalPolynomial h ∧
      h ∈ primaryFactors (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap ∧
      (∀ v ∈ P, aeval (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap h v = 0) ∧
      finrank K P = h.natDegree ∧ h.natDegree = orderOf ((Nat.card K : ℕ) : ZMod p) := by
  classical
  set T : Module.End K V := (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap with hT
  have hTP : ∀ x ∈ P, T x ∈ P := fun x hx => hP.eStable a a.2 x hx
  haveI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.mpr hP.ne_bot
  have hmove : ∃ u ∈ P, ((a : orthDerived Q) : V ≃ₗ[K] V) u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact haM (hker ▸ mem_actKernel.mpr hcon)
  have hTp : T ^ p = 1 := by
    rw [hT, ← toLinearMap_pow, coe_pow_eq_one hK a]
    rfl
  have hpow : T.restrict hTP ^ p = 1 := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    rw [coe_pow_of_intertwine (A := T.restrict hTP) (B := T) (fun u => rfl), hTp]
    rfl
  have hfix : ∀ v : P, T.restrict hTP v = v → v = 0 := by
    intro v hv
    exact Subtype.ext (hP.eq_zero_of_fixed hK.comm hmove v.2 (congrArg Subtype.val hv))
  have hsimple : ∀ S : Submodule K P, (∀ s ∈ S, T.restrict hTP s ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hSa : ∀ s ∈ S.map P.subtype, ((a : orthDerived Q) : V ≃ₗ[K] V) s ∈ S.map P.subtype := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨T.restrict hTP s, hS s hs, rfl⟩
    rcases hP.minimal (Submodule.map_subtype_le P S)
        (EStable.of_apply_mem hK hp hM hker haM (Submodule.map_subtype_le P S) hSa) with h0 | h1
    · left
      rw [eq_bot_iff]
      intro s hs
      have : (s : V) ∈ S.map P.subtype := ⟨s, hs, rfl⟩
      rw [h0] at this
      exact Subtype.ext ((Submodule.mem_bot K).mp this)
    · right
      rw [eq_top_iff]
      intro s _
      have : (s : V) ∈ S.map P.subtype := by rw [h1]; exact s.2
      obtain ⟨t, ht, hts⟩ := this
      have : t = s := Subtype.ext hts
      rwa [← this]
  obtain ⟨h, hmon, hirr, hdvd, hne1, hgh, hfin⟩ :=
    exists_irreducible_of_simple_endomorphism hp.pos (T.restrict hTP) hpow hfix hsimple
  have hkerP : ∀ v ∈ P, aeval T h v = 0 := fun v hv => by
    have := coe_aeval_of_intertwine (A := T.restrict hTP) (B := T) (fun u => rfl) h ⟨v, hv⟩
    rw [hgh, LinearMap.zero_apply] at this
    exact this.symm
  have hQ := nondegenerate_of_kernelLineData hK
  have ha1 : a ≠ 1 := fun h1 => haM (h1 ▸ M.one_mem)
  have hx := oddOrderIsometry_of_mem hQ hp hpl hK ha1
  obtain ⟨v₀, hv₀P, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP.ne_bot
  have hhf : h ∈ primaryFactors T :=
    mem_primaryFactors_of_apply_eq_zero hirr hmon (hkerP v₀ hv₀P) hv₀0
  have hself : h = reciprocalPolynomial h := by
    by_contra hne
    refine hP.ne_bot (eq_bot_iff.mpr fun x hxP => ?_)
    refine (Submodule.mem_bot K).mpr (hP.regular x hxP fun y hyP => ?_)
    exact hx.polar_eq_zero_of_ne hhf hne (mem_primaryComponent.mpr (hkerP x hxP))
      (mem_primaryComponent.mpr (hkerP y hyP))
  refine ⟨h, hmon, hirr, hne1, hself, hhf, hkerP, hfin, ?_⟩
  exact natDegree_eq_orderOf_of_dvd hp hpl hmon hirr hdvd hne1

end Line

section NoSingularLine

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem IsPiece.exists_line {E : Subgroup (orthDerived Q)} (hK : KernelLineData Q p E)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) {P : Submodule K V}
    (hP : IsPiece Q E P) :
    ∃ M : Subgroup E, Nat.card M = p ∧ P ≤ lineSpace M ∧
      (∀ x : E, (∀ u ∈ P, ((x : orthDerived Q) : V ≃ₗ[K] V) u = u) → x ∈ M) ∧
      finrank K P = orderOf ((Nat.card K : ℕ) : ZMod p) ∧
      Even (orderOf ((Nat.card K : ℕ) : ZMod p)) ∧ 2 ≤ orderOf ((Nat.card K : ℕ) : ZMod p) := by
  obtain ⟨M, hM, hPM⟩ := hP.exists_lineSpace_le hK hp hpl
  have hker := hP.actKernel_eq hK hp hM hPM
  obtain ⟨a, haM⟩ := exists_notMem_line hK hp hM
  obtain ⟨h, hmon, hirr, hne1, hself, hhf, hkerP, hfin, hdeg⟩ :=
    hP.exists_primary hK hp hpl hM hker haM
  have ha1 : a ≠ 1 := fun h1 => haM (h1 ▸ M.one_mem)
  have hx := oddOrderIsometry_of_mem (nondegenerate_of_kernelLineData hK) hp hpl hK ha1
  obtain ⟨d, hd, -⟩ := hx.selfDualModel (hp.odd_of_ne_two hp2) hhf hne1 hself
  refine ⟨M, hM, hPM, fun x hx => hker ▸ mem_actKernel.mpr hx, hfin.trans hdeg, ?_, ?_⟩
  · rw [← hdeg, hd]
    exact even_two_mul d
  · rw [← hdeg]
    have := hirr.natDegree_pos
    omega

theorem noSingular_ord (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpl : p ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) (hNS : OrthNoInvariantSingular Q E) :
    2 ≤ orderOf ((Nat.card K : ℕ) : ZMod p) ∧ Even (orderOf ((Nat.card K : ℕ) : ZMod p)) := by
  classical
  haveI : Nontrivial V := nontrivial_of_card_sq hp.one_lt hcard
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  obtain ⟨n, P, hP, -, -, hPsp⟩ :=
    exists_piece_decomposition hQ hp hp2 hpl E hcomm hexp hcard hNS
  have hn : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have hfinE : Finite E :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcard]; exact Nat.one_lt_pow two_ne_zero hp.one_lt)
    obtain ⟨a, ha⟩ := exists_ne (1 : E)
    refine ha (Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_)))
    have hv : v ∈ planeFixSpace E := by simpa using hPsp Submodule.mem_top
    exact hv _ ⟨a, a.2, rfl⟩
  obtain ⟨M, hM, hPM, -, -, hev, h2⟩ := (hP ⟨0, hn⟩).exists_line hK hp hp2 hpl
  exact ⟨h2, hev⟩

end NoSingularLine

section RestrictPlane

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem hasSelfDualFactor_restrict {E : Subgroup (orthDerived Q)} (hK : KernelLineData Q p E)
    (hp : p.Prime) (hpl : p ≠ ringChar K) {U : Submodule K V} (hU : PolarNondegOn Q U)
    (ρ : E →* orthDerived (Q.comp U.subtype))
    (hρ : ∀ (x : E) (u : U), (((ρ x : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U) u : V) =
      ((x : orthDerived Q) : V ≃ₗ[K] V) u)
    {P : Submodule K V} (hP : IsPiece Q E P) (hPU : P ≤ U) :
    HasSelfDualFactor (Q.comp U.subtype) ρ.range := by
  obtain ⟨M, hM, hPM⟩ := hP.exists_lineSpace_le hK hp hpl
  have hker := hP.actKernel_eq hK hp hM hPM
  obtain ⟨a, haM⟩ := exists_notMem_line hK hp hM
  obtain ⟨h, hmon, hirr, hne1, hself, hhf, hkerP, hfin, hdeg⟩ :=
    hP.exists_primary hK hp hpl hM hker haM
  obtain ⟨v₀, hv₀P, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP.ne_bot
  refine ⟨ρ a, ⟨a, rfl⟩, ?_, h, ?_, hne1, hself⟩
  · intro h1
    apply haM
    rw [← hker]
    refine mem_actKernel.mpr fun u hu => ?_
    have := hρ a ⟨u, hPU hu⟩
    rw [h1] at this
    exact this.symm
  · refine mem_primaryFactors_of_apply_eq_zero hirr hmon (v := ⟨v₀, hPU hv₀P⟩) ?_ ?_
    · refine Subtype.ext ?_
      rw [coe_aeval_of_intertwine (B := (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap)
        (fun u => hρ a u)]
      exact hkerP v₀ hv₀P
    · intro h0
      exact hv₀0 (congrArg Subtype.val h0)

end RestrictPlane

section Aniso

open Polynomial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)} {P : Submodule K V}

omit [FiniteDimensional K V] in
theorem dvd_card_sub_one_of_root {ζ : K} (hp : p.Prime) (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) :
    p ∣ Nat.card K - 1 := by
  have hne : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζ
    exact zero_ne_one hζ
  have : Fact p.Prime := ⟨hp⟩
  let u : Kˣ := Units.mk0 ζ hne
  have hu : orderOf u = p := orderOf_eq_prime (by ext; simpa [u] using hζ)
    (fun h => hζ1 (by simpa [u] using congrArg Units.val h))
  have := orderOf_dvd_natCard u
  rwa [hu, Nat.card_units] at this

omit [FiniteDimensional K V] in
theorem false_of_eigenvector (hp : p.Prime) (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    {T : V ≃ₗ[K] V} (hTp : T ^ p = 1) {u : V} (hu0 : u ≠ 0) {c : K} (hc : T u = c • u)
    (hfix : T u ≠ u) : False := by
  have hpow : ∀ n : ℕ, (T ^ n) u = c ^ n • u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hc, smul_smul, pow_succ]
  have h1 : u = c ^ p • u := by
    have := hpow p
    rwa [hTp] at this
  have hcp : c ^ p = 1 := by
    have h3 : (1 - c ^ p) • u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hu0)).symm
  have hc1 : c ≠ 1 := fun h => hfix (by rw [hc, h, one_smul])
  have hdvd := dvd_card_sub_one_of_root hp hcp hc1
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have h4 : (((Nat.card K - 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [Nat.cast_sub hq1, Nat.cast_one, sub_eq_zero] at h4
  rw [h4, orderOf_one] at h2
  omega

theorem IsPiece.anisotropic_of_orderOf_two (hP : IsPiece Q E P)
    (hK : KernelLineData Q p E) (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) : ∀ s ∈ P, Q s = 0 → s = 0 := by
  classical
  obtain ⟨M, hM, hPM⟩ := hP.exists_lineSpace_le hK hp hpl
  have hker := hP.actKernel_eq hK hp hM hPM
  obtain ⟨a, haM⟩ := exists_notMem_line hK hp hM
  obtain ⟨h, hmon, hirr, hne1, hself, hhf, hkerP, hfin, hdeg⟩ :=
    hP.exists_primary hK hp hpl hM hker haM
  have hdim : finrank K P = 2 := by rw [hfin, hdeg, h2]
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega : p ≠ 2)
  have hbM : a ^ 2 ∉ M := by
    intro hb
    apply haM
    have h1 : a = (a ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      have h3 : 2 * (k + 1) = p + 1 := by omega
      rw [h3, pow_succ, hK.exp a, one_mul]
    rw [h1]
    exact M.pow_mem hb _
  have hmovea : ∃ u ∈ P, ((a : orthDerived Q) : V ≃ₗ[K] V) u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact haM (hker ▸ mem_actKernel.mpr hcon)
  have hmoveb : ∃ u ∈ P, (((a ^ 2 : E) : orthDerived Q) : V ≃ₗ[K] V) u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact hbM (hker ▸ mem_actKernel.mpr hcon)
  have hfixa := fun u (hu : u ∈ P) (h : ((a : orthDerived Q) : V ≃ₗ[K] V) u = u) =>
    hP.eq_zero_of_fixed hK.comm hmovea hu h
  have hfixb := fun u (hu : u ∈ P) (h : (((a ^ 2 : E) : orthDerived Q) : V ≃ₗ[K] V) u = u) =>
    hP.eq_zero_of_fixed hK.comm hmoveb hu h
  have hgg : ∀ u, (((a ^ 2 : E) : orthDerived Q) : V ≃ₗ[K] V) u =
      ((a : orthDerived Q) : V ≃ₗ[K] V) (((a : orthDerived Q) : V ≃ₗ[K] V) u) := fun u => by
    rw [pow_two]; rfl
  have hgO : ((a : orthDerived Q) : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_mem_orthogonalGroup
  intro s hsP hsQ
  by_contra hs0
  by_cases h1 : ∃ c : K, ((a : orthDerived Q) : V ≃ₗ[K] V) s = c • s
  · obtain ⟨c, hc⟩ := h1
    exact false_of_eigenvector hp h2 (coe_pow_eq_one hK a) hs0 hc
      (fun h => hs0 (hfixa s hsP h))
  push Not at h1
  set t : V := ((a : orthDerived Q) : V ≃ₗ[K] V) s with ht
  have htP : t ∈ P := hP.eStable a a.2 s hsP
  have hQt : Q t = 0 := by rw [ht, map_of_mem hgO, hsQ]
  have ht0 : t ≠ 0 := fun h => hs0 (by
    have : ((a : orthDerived Q) : V ≃ₗ[K] V) s = 0 := h
    exact (map_eq_zero_iff _ ((a : orthDerived Q) : V ≃ₗ[K] V).injective).mp this)
  have hli : LinearIndependent K ![s, t] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    by_cases hβ : β = 0
    · rw [hβ, zero_smul, add_zero] at hαβ
      exact ⟨(smul_eq_zero.mp hαβ).resolve_right hs0, hβ⟩
    · exfalso
      apply h1 (-(α / β))
      have : β • t = -(α • s) := eq_neg_of_add_eq_zero_right hαβ
      calc t = β⁻¹ • (β • t) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
        _ = (-(α / β)) • s := by rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hspan : Submodule.span K {s, t} = P := by
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
    · rintro x (rfl | rfl)
      exacts [hsP, htP]
    · have hr : Set.range ![s, t] = {s, t} := by
        ext x
        simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
      have := finrank_span_eq_card hli
      rw [hr] at this
      rw [hdim, this]
      simp
  have hpst : polar Q s t ≠ 0 := by
    intro h0
    refine hs0 (hP.regular s hsP fun y hy => ?_)
    rw [← hspan] at hy
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_self_eq_zero hsQ, h0]
    ring
  have hgtP : ((a : orthDerived Q) : V ≃ₗ[K] V) t ∈ P := hP.eStable a a.2 t htP
  rw [← hspan] at hgtP
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hgtP
  have hQgt : Q (((a : orthDerived Q) : V ≃ₗ[K] V) t) = 0 := by rw [map_of_mem hgO, hQt]
  rw [← hαβ, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hsQ, hQt,
    polar_smul_left_eq, polar_smul_right_eq] at hQgt
  have hαβ0 : α * β * polar Q s t = 0 := by linear_combination hQgt
  rcases mul_eq_zero.mp hαβ0 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    ·
      subst h4
      refine false_of_eigenvector hp h2 (coe_pow_eq_one hK a) ht0 (c := β) ?_
        (fun h => ht0 (hfixa t htP h))
      rw [← hαβ, zero_smul, zero_add]
    ·
      subst h4
      refine false_of_eigenvector hp h2 (coe_pow_eq_one hK (a ^ 2)) hs0 (c := α) ?_
        (fun h => hs0 (hfixb s hsP h))
      rw [hgg, ← ht, ← hαβ, zero_smul, add_zero]
  · exact hpst h3

end Aniso

end CFSG.LieType.SeitzGeneration
