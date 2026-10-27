module

public import CFSG.LieType.SeitzGeneration.ExcHigh.SpinFrameEven

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest2

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical CFSG.Open
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Fix

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem mem_planeFixSpace_iff' {E : Subgroup (orthDerived Q)} {v : V} :
    v ∈ planeFixSpace E ↔ ∀ x : E, ((x : orthDerived Q) : V ≃ₗ[K] V) v = v := by
  constructor
  · intro hv x
    exact hv _ ⟨(x : orthDerived Q), x.2, rfl⟩
  · rintro hv g ⟨y, hy, rfl⟩
    exact hv ⟨y, hy⟩

theorem polarNondegOn_planeFixSpace_of_card (hQ : (polarBilin Q).Nondegenerate)
    (E : Subgroup (orthDerived Q)) [Finite E] (hE : (Nat.card E : K) ≠ 0) :
    PolarNondegOn Q (planeFixSpace E) := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  set e : Module.End K V := avgOp (orthRep E) (⊤ : Subgroup E) with he
  have hcard : (Fintype.card (⊤ : Subgroup E) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, Subgroup.card_top]
    exact hE
  have he_fix : ∀ v ∈ planeFixSpace E, e v = v := fun v hv =>
    avgOp_apply_of_fixed hcard (fun d _ => (mem_planeFixSpace_iff'.1 hv) d)
  have he_mem : ∀ u, e u ∈ planeFixSpace E := fun u =>
    mem_planeFixSpace_iff'.2 fun x => apply_avgOp (ρ := orthRep E) (Subgroup.mem_top x) u
  have hinv : ∀ (g : E) (u w : V),
      polarBilin Q (orthRep E g u) (orthRep E g w) = polarBilin Q u w := fun g u w => by
    rw [polarBilin_apply_apply, polarBilin_apply_apply, orthRep_apply, orthRep_apply]
    exact polar_map_of_mem orthDerived_mem_orthogonalGroup u w
  intro v hv hperp
  refine eq_zero_of_polar_eq_zero hQ fun u => ?_
  have h1 : polarBilin Q (e v) u = polarBilin Q v (e u) := bilin_avgOp _ hinv ⊤ v u
  rw [he_fix v hv, polarBilin_apply_apply, polarBilin_apply_apply] at h1
  rw [h1]
  exact hperp _ (he_mem u)

end Fix

section Stable

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {E : Subgroup (orthDerived Q)}

theorem estable_symm_mem {S : Submodule K V} (hS : EStable E S) {x : orthDerived Q} (hx : x ∈ E)
    {u : V} (hu : u ∈ S) : ((x : orthDerived Q) : V ≃ₗ[K] V).symm u ∈ S :=
  hS x⁻¹ (E.inv_mem hx) u hu

theorem estable_perp {S : Submodule K V} (hS : EStable E S) :
    EStable E (OrthBlk.perp Q S) := by
  intro x hx t ht
  refine OrthBlk.mem_perp.mpr fun s hs => ?_
  have hxO := orthDerived_mem_orthogonalGroup (Q := Q) (g := x)
  have hs' := estable_symm_mem hS hx hs
  have := polar_map_of_mem hxO (((x : orthDerived Q) : V ≃ₗ[K] V).symm s) t
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this]
  exact OrthBlk.mem_perp.mp ht _ hs'

end Stable

section Decomposition

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {E : Subgroup (orthDerived Q)}

theorem polarNondegOn_of_minimal' (hNS : OrthNoInvariantSingular Q E) {S : Submodule K V}
    (hS0 : S ≠ ⊥) (hSV : Disjoint S (planeFixSpace E)) (hst : EStable E S)
    (hmin : ∀ S' : Submodule K V, S' ≤ S → EStable E S' → S' = ⊥ ∨ S' = S) :
    PolarNondegOn Q S := by
  classical
  have hR : EStable E (S ⊓ OrthBlk.perp Q S) := hst.inf (estable_perp hst)
  rcases hmin _ inf_le_left hR with hR0 | hRS
  · intro x hxS hx
    have hxR : x ∈ S ⊓ OrthBlk.perp Q S :=
      ⟨hxS, OrthBlk.mem_perp.mpr fun s hs => by rw [polar_comm]; exact hx s hs⟩
    rw [hR0] at hxR
    exact (Submodule.mem_bot K).mp hxR
  · exfalso
    have hSS : ∀ s ∈ S, ∀ t ∈ S, polar Q s t = 0 := fun s hs t ht => by
      have ht' : t ∈ S ⊓ OrthBlk.perp Q S := by rw [hRS]; exact ht
      exact OrthBlk.mem_perp.mp ht'.2 s hs
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

theorem exists_pieces_of_stable' (hV0 : PolarNondegOn Q (planeFixSpace E))
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
  have hSdisj : Disjoint S (planeFixSpace E) := by
    rw [Submodule.disjoint_def]
    intro x hxS hxV
    exact hV0 x hxV fun y hy => hWV x (hSW hxS) y hy
  have hSreg : PolarNondegOn Q S := polarNondegOn_of_minimal' hNS hS0 hSdisj hSst hSmin
  set W' : Submodule K V := W ⊓ OrthBlk.perp Q S with hW'
  have hW'st : EStable E W' := hWst.inf (estable_perp hSst)
  have hW'reg : PolarNondegOn Q W' := OrthBlk.polarNondegOn_inf_perp hWreg hSreg hSW
  have hW'V : OrthSep Q W' (planeFixSpace E) := fun w hw v hv => hWV w hw.1 v hv
  have hlt : finrank K W' < n := by
    rw [← hn]
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => ?_)
    obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    have : s ∈ W' := by rw [h]; exact hSW hsS
    exact hs0 (hSreg s hsS fun t ht => by rw [polar_comm]; exact OrthBlk.mem_perp.mp this.2 t ht)
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
      exact OrthBlk.mem_perp.mp (hP'le j' ht).2 s hs
    · intro s hs t ht
      simp only [Fin.cons_zero, Fin.cons_succ] at hs ht
      rw [polar_comm]
      exact OrthBlk.mem_perp.mp (hP'le i' hs).2 t ht
    · simp only [Fin.cons_succ]
      exact hP'orth i' j' fun h => hij (by rw [h])
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hSW
    · simpa using (hP'le j).trans inf_le_left
  · intro w hw
    obtain ⟨a, ha, r, hr, rfl⟩ := OrthBlk.exists_add_inf_perp hSreg hSW hw
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_iSup_of_mem (0 : Fin (m + 1)) (by simpa using ha)
    · have hr' : r ∈ ⨆ j, P' j := hP'sp hr
      refine (iSup_le fun j => ?_ : (⨆ j, P' j) ≤ ⨆ i, (Fin.cons S P' : Fin (m + 1) → _) i) hr'
      exact le_iSup_of_le j.succ (by simp)

theorem exists_piece_decomposition' (hQ : (polarBilin Q).Nondegenerate)
    (hV0 : PolarNondegOn Q (planeFixSpace E)) (hNS : OrthNoInvariantSingular Q E) :
    ∃ (n : ℕ) (P : Fin n → Submodule K V), (∀ i, IsPiece Q E (P i)) ∧
      (∀ i j, i ≠ j → OrthSep Q (P i) (P j)) ∧ (∀ i, OrthSep Q (planeFixSpace E) (P i)) ∧
      (⊤ : Submodule K V) ≤ planeFixSpace E ⊔ ⨆ i, P i := by
  classical
  have hWst : EStable E (OrthBlk.perp Q (planeFixSpace E)) :=
    estable_perp (EStable.of_fixed (S := planeFixSpace E) fun x hx u hu => hu _ ⟨x, hx, rfl⟩)
  obtain ⟨n, P, hP, hPP, hPle, hPsp⟩ := exists_pieces_of_stable' hV0 hNS _
    (OrthBlk.perp Q (planeFixSpace E)) rfl hWst (OrthBlk.polarNondegOn_perp hQ hV0)
    (fun w hw v hv => by rw [polar_comm]; exact OrthBlk.mem_perp.mp hw v hv)
  refine ⟨n, P, hP, hPP, fun i s hs t ht => OrthBlk.mem_perp.mp (hPle i ht) s hs, ?_⟩
  rw [← (OrthBlk.isCompl_perp hV0).sup_eq_top]
  exact sup_le_sup_left hPsp _

end Decomposition

section Cyclic

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {E : Subgroup (orthDerived Q)} {P : Submodule K V}

@[expose] noncomputable def restrictE (hP : EStable E P) (x : E) : Module.End K P :=
  (((x : orthDerived Q) : V ≃ₗ[K] V) : V →ₗ[K] V).restrict fun u hu => hP x x.2 u hu

theorem restrictE_apply (hP : EStable E P) (x : E) (u : P) :
    ((restrictE hP x u : P) : V) = ((x : orthDerived Q) : V ≃ₗ[K] V) u :=
  rfl

theorem restrictE_pow_apply (hP : EStable E P) (x : E) (n : ℕ) (u : P) :
    (((restrictE hP x ^ n) u : P) : V) = (((x : orthDerived Q) : V ≃ₗ[K] V) ^ n) u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, LinearEquiv.mul_apply, restrictE_apply]

theorem restrictE_commute (hP : EStable E P) (hcomm : ∀ x y : E, x * y = y * x) (x y : E) :
    Commute (restrictE hP x) (restrictE hP y) := by
  refine LinearMap.ext fun u => Subtype.ext ?_
  change ((x : orthDerived Q) : V ≃ₗ[K] V) (((y : orthDerived Q) : V ≃ₗ[K] V) u) =
    ((y : orthDerived Q) : V ≃ₗ[K] V) (((x : orthDerived Q) : V ≃ₗ[K] V) u)
  exact act_comm_apply hcomm x y u

theorem isPiece_eq_zero_or_injective (hP : IsPiece Q E P) {f : Module.End K P}
    (hf : ∀ x : E, Commute f (restrictE hP.eStable x)) : f = 0 ∨ Function.Injective f := by
  set N : Submodule K V := (LinearMap.ker f).map P.subtype with hN
  have hNP : N ≤ P := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hNst : EStable E N := by
    rintro x hx _ ⟨w, hw, rfl⟩
    refine ⟨restrictE hP.eStable ⟨x, hx⟩ w, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hw ⊢
    have h2 := congrArg (fun g : Module.End K P => g w) (hf ⟨x, hx⟩).eq
    simp only [Module.End.mul_apply] at h2
    rw [h2, hw, map_zero]
  rcases hP.minimal hNP hNst with h0 | h1
  · right
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    have : (w : V) ∈ N := ⟨w, hw, rfl⟩
    rw [h0, Submodule.mem_bot] at this
    exact (Submodule.mem_bot K).mpr (Subtype.ext this)
  · left
    ext w
    have : (w : V) ∈ N := by rw [h1]; exact w.2
    obtain ⟨w', hw', hw'e⟩ := this
    have hww : w' = w := Subtype.ext hw'e
    rw [← hww]
    simpa using hw'

open scoped IsMulCommutative in
theorem isPiece_exists_pow_eq (hP : IsPiece Q E P) (hcomm : ∀ x y : E, x * y = y * x)
    {p : ℕ} (hp : p.Prime) (hexp : ∀ x : E, x ^ p = 1) {a : E}
    (ha : ∃ u ∈ P, ((a : orthDerived Q) : V ≃ₗ[K] V) u ≠ u) (b : E) :
    ∃ i : ℕ, ∀ u ∈ P, ((b : orthDerived Q) : V ≃ₗ[K] V) u =
      (((a : orthDerived Q) : V ≃ₗ[K] V) ^ i) u := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set r := restrictE hP.eStable with hr
  set s : Set (Module.End K P) := {r a, r b} with hsdef
  have hs : s.Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      exact restrictE_commute hP.eStable hcomm _ _
  haveI := Algebra.isMulCommutative_adjoin K hs
  set C := Algebra.adjoin K s with hCdef
  have hCcent : ∀ c ∈ C, ∀ x : E, Commute c (r x) := fun c hc x =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hc fun y hy => by
      rcases hy with rfl | rfl <;> exact restrictE_commute hP.eStable hcomm _ _).symm
  haveI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.mpr hP.ne_bot
  haveI : NoZeroDivisors C := ⟨fun {c d} hcd => by
    rcases isPiece_eq_zero_or_injective hP (f := (c : Module.End K P)) (hCcent c c.2) with
      h0 | hinj
    · exact Or.inl (Subtype.ext h0)
    · right
      apply Subtype.ext
      refine LinearMap.ext fun w => ?_
      have h1 : (c : Module.End K P) ((d : Module.End K P) w) = 0 := by
        have := congrArg (fun z : C => ((z : Module.End K P) w)) hcd
        simpa using this
      have h2 : (d : Module.End K P) w = 0 := hinj (by rw [h1, map_zero])
      simpa using h2⟩
  haveI : IsDomain C := NoZeroDivisors.to_isDomain C
  set T : C := ⟨r a, Algebra.subset_adjoin (Set.mem_insert _ _)⟩ with hTdef
  set S : C := ⟨r b, Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)⟩ with hSdef
  have hpow : ∀ x : E, r x ^ p = 1 := fun x => by
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [restrictE_pow_apply]
    have := congrArg (fun z : E => ((z : orthDerived Q) : V ≃ₗ[K] V)) (hexp x)
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    rw [this]
    rfl
  have hTp : T ^ p = 1 :=
    Subtype.ext (by rw [Subalgebra.coe_pow, Subalgebra.coe_one]; exact hpow a)
  have hSp : S ^ p = 1 :=
    Subtype.ext (by rw [Subalgebra.coe_pow, Subalgebra.coe_one]; exact hpow b)
  have hT1 : T ≠ 1 := by
    intro h1
    obtain ⟨u, hu, hne⟩ := ha
    apply hne
    have h2 : r a = 1 := congrArg Subtype.val h1
    have h3 := congrArg (fun g : Module.End K P => ((g ⟨u, hu⟩ : P) : V)) h2
    simpa [hr, restrictE_apply] using h3
  have hprim : IsPrimitiveRoot T p := by
    have := IsPrimitiveRoot.orderOf T
    rwa [orderOf_eq_prime hTp hT1] at this
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hSp
  have h4 : r a ^ i = r b := by
    have := congrArg Subtype.val hi
    rwa [Subalgebra.coe_pow] at this
  refine ⟨i, fun u hu => ?_⟩
  have h5 := congrArg (fun g : Module.End K P => ((g ⟨u, hu⟩ : P) : V)) h4
  rw [hr, restrictE_pow_apply, restrictE_apply] at h5
  exact h5.symm

end Cyclic

section Dim

open Polynomial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {E : Subgroup (orthDerived Q)} {P : Submodule K V}

theorem isPiece_exists_moving (hP : IsPiece Q E P) :
    ∃ a : E, ∃ u ∈ P, ((a : orthDerived Q) : V ≃ₗ[K] V) u ≠ u := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP.ne_bot
  have huV : u ∉ planeFixSpace E := fun h => hu0 (Submodule.disjoint_def.mp hP.disjoint u hu h)
  by_contra hcon
  push Not at hcon
  exact huV (mem_planeFixSpace_iff'.2 fun x => hcon x u hu)

theorem restrictE_pow_eq_one (hP : EStable E P) {p : ℕ} {x : E} (hx : x ^ p = 1) :
    restrictE hP x ^ p = 1 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [restrictE_pow_apply]
  have := congrArg (fun z : E => ((z : orthDerived Q) : V ≃ₗ[K] V)) hx
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
  rw [this]
  rfl

theorem isPiece_finrank_eq (hP : IsPiece Q E P) (hcomm : ∀ x y : E, x * y = y * x)
    {p : ℕ} (hp : p.Prime) (hpl : p ≠ ringChar K) (hexp : ∀ x : E, x ^ p = 1) {a : E}
    (ha : ∃ u ∈ P, ((a : orthDerived Q) : V ≃ₗ[K] V) u ≠ u) :
    finrank K P = orderOf ((Nat.card K : ℕ) : ZMod p) := by
  classical
  haveI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.mpr hP.ne_bot
  set T : Module.End K P := restrictE hP.eStable a with hT
  have hpow : T ^ p = 1 := restrictE_pow_eq_one hP.eStable (hexp a)
  have hfix : ∀ v : P, T v = v → v = 0 := fun v hv =>
    Subtype.ext (hP.eq_zero_of_fixed hcomm ha v.2 (congrArg Subtype.val hv))
  have hTn : ∀ (S : Submodule K P), (∀ s ∈ S, T s ∈ S) → ∀ (n : ℕ), ∀ s ∈ S, (T ^ n) s ∈ S := by
    intro S hS n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih =>
      intro s hs
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hS s hs)
  have hsimple : ∀ S : Submodule K P, (∀ s ∈ S, T s ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hNst : EStable E (S.map P.subtype) := by
      rintro x hx _ ⟨s, hs, rfl⟩
      obtain ⟨i, hi⟩ := isPiece_exists_pow_eq hP hcomm hp hexp ha ⟨x, hx⟩
      refine ⟨(T ^ i) s, hTn S hS i s hs, ?_⟩
      change (((T ^ i) s : P) : V) = ((x : orthDerived Q) : V ≃ₗ[K] V) s
      rw [hT, restrictE_pow_apply, hi s s.2]
    rcases hP.minimal (Submodule.map_subtype_le P S) hNst with h0 | h1
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
  obtain ⟨h, hmon, hirr, hdvd, hne1, -, hfin⟩ :=
    exists_irreducible_of_simple_endomorphism hp.pos T hpow hfix hsimple
  rw [hfin]
  exact natDegree_eq_orderOf_of_dvd hp hpl hmon hirr hdvd hne1

theorem isPiece_anisotropic (hP : IsPiece Q E P) (hcomm : ∀ x y : E, x * y = y * x)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) (hexp : ∀ x : E, x ^ p = 1) :
    ∀ s ∈ P, Q s = 0 → s = 0 := by
  classical
  obtain ⟨a, hmovea⟩ := isPiece_exists_moving hP
  have hdim : finrank K P = 2 := by rw [isPiece_finrank_eq hP hcomm hp hpl hexp hmovea, h2]
  have hpowE : ∀ x : E, ((x : orthDerived Q) : V ≃ₗ[K] V) ^ p = 1 := fun x => by
    have := congrArg (fun z : E => ((z : orthDerived Q) : V ≃ₗ[K] V)) (hexp x)
    simpa using this
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega : p ≠ 2)
  have hmoveb : ∃ u ∈ P, (((a ^ 2 : E) : orthDerived Q) : V ≃ₗ[K] V) u ≠ u := by
    by_contra hcon
    push Not at hcon
    have hb : a ^ 2 ∈ actKernel E P := mem_actKernel.mpr hcon
    have ha' : a ∈ actKernel E P := by
      have h1 : a = (a ^ 2) ^ (k + 1) := by
        rw [← pow_mul]
        have h3 : 2 * (k + 1) = p + 1 := by omega
        rw [h3, pow_succ, hexp a, one_mul]
      rw [h1]
      exact (actKernel E P).pow_mem hb _
    obtain ⟨u, hu, hne⟩ := hmovea
    exact hne (mem_actKernel.mp ha' u hu)
  have hfixa := fun u (hu : u ∈ P) (h : ((a : orthDerived Q) : V ≃ₗ[K] V) u = u) =>
    hP.eq_zero_of_fixed hcomm hmovea hu h
  have hfixb := fun u (hu : u ∈ P) (h : (((a ^ 2 : E) : orthDerived Q) : V ≃ₗ[K] V) u = u) =>
    hP.eq_zero_of_fixed hcomm hmoveb hu h
  have hgg : ∀ u, (((a ^ 2 : E) : orthDerived Q) : V ≃ₗ[K] V) u =
      ((a : orthDerived Q) : V ≃ₗ[K] V) (((a : orthDerived Q) : V ≃ₗ[K] V) u) := fun u => by
    rw [pow_two]; rfl
  have hgO : ((a : orthDerived Q) : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_mem_orthogonalGroup
  intro s hsP hsQ
  by_contra hs0
  by_cases h1 : ∃ c : K, ((a : orthDerived Q) : V ≃ₗ[K] V) s = c • s
  · obtain ⟨c, hc⟩ := h1
    exact false_of_eigenvector hp h2 (hpowE a) hs0 hc (fun h => hs0 (hfixa s hsP h))
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
      refine false_of_eigenvector hp h2 (hpowE a) ht0 (c := β) ?_
        (fun h => ht0 (hfixa t htP h))
      rw [← hαβ, zero_smul, zero_add]
    ·
      subst h4
      refine false_of_eigenvector hp h2 (hpowE (a ^ 2)) hs0 (c := α) ?_
        (fun h => hs0 (hfixb s hsP h))
      rw [hgg, ← ht, ← hαβ, zero_smul, add_zero]
  · exact hpst h3

end Dim

section Planes

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_goodPlanes_elem (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    (E : Subgroup (orthDerived Q)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hNS : OrthNoInvariantSingular Q E)
    {k : ℕ} (hk : Module.finrank K V = 4 * k) :
    ∃ Pl : Fin (2 * k) → Submodule K V,
      GoodPlanes Q {g | ∃ e ∈ E, g = ((e : orthDerived Q) : V ≃ₗ[K] V)} Pl := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (β := V → V) (fun f => (f : V → V)) fun f g h =>
      LinearEquiv.ext (congrFun h)
  haveI : Finite E := inferInstance
  have hpg : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpg
  have hpK : (p : K) ≠ 0 := OrthBlk.natCast_ne_zero_of_ne_ringChar hp hpl
  have hEK : (Nat.card E : K) ≠ 0 := by
    rw [hm, Nat.cast_pow]
    exact pow_ne_zero _ hpK
  have hV0reg : PolarNondegOn Q (planeFixSpace E) := polarNondegOn_planeFixSpace_of_card hQ E hEK
  have hcomm' : ∀ x y : E, x * y = y * x := fun x y => Subtype.ext (hcomm x x.2 y y.2)
  have hexp' : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  obtain ⟨n, P, hP, hPP, hPV, hPsp⟩ := exists_piece_decomposition' hQ hV0reg hNS
  have hPdim : ∀ i, Module.finrank K ↥(P i) = 2 := fun i => by
    obtain ⟨a, ha⟩ := isPiece_exists_moving (hP i)
    rw [isPiece_finrank_eq (hP i) hcomm' hp hpl hexp' ha, hord]
  have hPan : ∀ i, ∀ s ∈ P i, Q s = 0 → s = 0 := fun i =>
    isPiece_anisotropic (hP i) hcomm' hp hp5 hpl hord hexp'
  have hPreg : ∀ i, PolarNondegOn Q (P i) := fun i => (hP i).regular
  have hV0an : ∀ s ∈ planeFixSpace E, Q s = 0 → s = 0 := fun s hs hsQ =>
    eq_zero_of_singular_planeFixSpace hNS hs hsQ
  have hV0dim : Module.finrank K ↥(planeFixSpace E) ≤ 2 := finrank_planeFixSpace_le_two hNS
  have hPst : ∀ i, ∀ e ∈ E, ∀ x ∈ P i, ((e : orthDerived Q) : V ≃ₗ[K] V) x ∈ P i :=
    fun i e he x hx => (hP i).eStable e he x hx
  have hV0st : ∀ e ∈ E, ∀ x ∈ planeFixSpace E,
      ((e : orthDerived Q) : V ≃ₗ[K] V) x ∈ planeFixSpace E := by
    intro e he x hx
    have : ((e : orthDerived Q) : V ≃ₗ[K] V) x = x := hx _ ⟨e, he, rfl⟩
    rw [this]
    exact hx
  let Pl₀ : Fin (n + 1) → Submodule K V :=
    Fin.snoc (α := fun _ => Submodule K V) P (planeFixSpace E)
  have hPl₀reg : ∀ i, PolarNondegOn Q (Pl₀ i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [Pl₀] using hV0reg
    · simpa [Pl₀] using hPreg j
  have hl : Pl₀ (Fin.last n) = planeFixSpace E := by simp [Pl₀]
  have hc : ∀ i : Fin n, Pl₀ i.castSucc = P i := fun i => by simp [Pl₀]
  have hPl₀orth : ∀ i j, i ≠ j → ∀ x ∈ Pl₀ i, ∀ y ∈ Pl₀ j, polar Q x y = 0 := by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · intro x hx y hy
      rw [hc] at hx hy
      exact hPP i' j' (fun h => hij (by rw [h])) x hx y hy
    · intro x hx y hy
      rw [hc] at hx
      rw [hl] at hy
      rw [polar_comm]
      exact hPV i' y hy x hx
    · intro x hx y hy
      rw [hl] at hx
      rw [hc] at hy
      exact hPV j' x hx y hy
    · exact absurd rfl hij
  have hPl₀span : ⨆ i, Pl₀ i = ⊤ := by
    rw [eq_top_iff]
    refine hPsp.trans (sup_le ?_ (iSup_le fun i => ?_))
    · exact le_iSup_of_le (Fin.last n) (by simp [Pl₀])
    · exact le_iSup_of_le i.castSucc (by simp [Pl₀])
  obtain ⟨-, hsum⟩ := polarNondegOn_iSup_fin Pl₀ hPl₀reg hPl₀orth
  rw [hPl₀span, finrank_top, hk, Fin.sum_univ_castSucc] at hsum
  have hsum' : 4 * k = 2 * n + Module.finrank K ↥(planeFixSpace E) := by
    have hfin : ∀ i : Fin n, Module.finrank K ↥(Pl₀ i.castSucc) = 2 := fun i => by
      rw [hc]; exact hPdim i
    have hfinl : Module.finrank K ↥(Pl₀ (Fin.last n)) = Module.finrank K ↥(planeFixSpace E) := by
      rw [hl]
    rw [Finset.sum_congr rfl (fun i _ => hfin i), hfinl, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hsum
    omega
  have hgood₀ : GoodPlanes Q {g | ∃ e ∈ E, g = ((e : orthDerived Q) : V ≃ₗ[K] V)} Pl₀ →
      Module.finrank K ↥(planeFixSpace E) = 2 →
      ∃ Pl : Fin (2 * k) → Submodule K V,
        GoodPlanes Q {g | ∃ e ∈ E, g = ((e : orthDerived Q) : V ≃ₗ[K] V)} Pl := fun hg h2 =>
    ⟨_, hg.congr (show n + 1 = 2 * k by omega)⟩
  rcases (show Module.finrank K ↥(planeFixSpace E) = 0 ∨
      Module.finrank K ↥(planeFixSpace E) = 2 by omega) with h0 | h2
  ·
    have hbot : planeFixSpace E = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hPspan : ⨆ i, P i = ⊤ := by
      rw [eq_top_iff]
      refine hPsp.trans (sup_le ?_ le_rfl)
      rw [hbot]
      exact bot_le
    have hg : GoodPlanes Q {g | ∃ e ∈ E, g = ((e : orthDerived Q) : V ≃ₗ[K] V)} P :=
      ⟨hPreg, hPdim, hPan, fun i j hij => hPP i j hij, hPspan, by
        rintro g ⟨e, he, rfl⟩ i x hx
        exact hPst i e he x hx⟩
    exact ⟨_, hg.congr (show n = 2 * k by omega)⟩
  · refine hgood₀ ⟨hPl₀reg, ?_, ?_, hPl₀orth, hPl₀span, ?_⟩ h2
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hl]; exact h2
      · rw [hc]; exact hPdim j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hl]; exact hV0an
      · rw [hc]; exact hPan j
    · rintro g ⟨e, he, rfl⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hl]; exact hV0st e he
      · rw [hc]; exact hPst j e he

end Planes

section Spin

open CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] [Finite K]

theorem exists_goodPlanes_spin {n : ℕ} (hn : 3 ≤ n) {k : ℕ} (hnk : n = 2 * k) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    (Ep : Subgroup (spinGroup (quadPlus n K))) (hcommEp : ∀ a ∈ Ep, ∀ b ∈ Ep, a * b = b * a)
    (hexp : ∀ x ∈ Ep, x ^ p = 1)
    (hNS : ∀ T : Submodule K (Fin n ⊕ Fin n → K),
      (∀ e ∈ Ep, ∀ v ∈ T, spinAction (quadPlus n K) e v ∈ T) →
      (∀ v ∈ T, quadPlus n K v = 0) → T = ⊥) :
    ∃ Pl : Fin (2 * k) → Submodule K (Fin n ⊕ Fin n → K),
      GoodPlanes (quadPlus n K) {g | ∃ e ∈ Ep, g = spinAction (quadPlus n K) e} Pl := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hQnd : (polarBilin (quadPlus n K)).Nondegenerate := nondegenerate_polarBilin_quadPlus n K
  have hrange : (spinAction (quadPlus n K)).range = orthDerived (quadPlus n K) :=
    range_spinAction_quadPlus_eq_commutator hn
  let sa : spinGroup (quadPlus n K) →* orthDerived (quadPlus n K) :=
    (spinAction (quadPlus n K)).codRestrict (orthDerived (quadPlus n K))
      (fun x => by rw [← hrange]; exact ⟨x, rfl⟩)
  set E : Subgroup (orthDerived (quadPlus n K)) := Ep.map sa with hE
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcommEp a ha b hb]
  have hexpE : ∀ x ∈ E, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hexp a ha, map_one]
  have hNSE : OrthNoInvariantSingular (quadPlus n K) E := fun T hTi hTs =>
    hNS T (fun e he v hv => hTi (sa e) ⟨e, he, rfl⟩ v hv) hTs
  have hk : Module.finrank K (Fin n ⊕ Fin n → K) = 4 * k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨Pl, hGP⟩ := exists_goodPlanes_elem hQnd hp hp5 hpl hord E hcommE hexpE hNSE hk
  exact ⟨Pl, hGP.mono (by
    rintro g ⟨e, he, rfl⟩
    exact ⟨sa e, ⟨e, he, rfl⟩, rfl⟩)⟩

theorem exists_spin_conj_frameGroup_elem (hodd : Odd (Nat.card K)) {n : ℕ} (hn : 3 ≤ n) {k : ℕ}
    (hnk : n = 2 * k) (ι : Fin k × Bool ≃ Fin n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpl : p ≠ ringChar K) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    (Ep : Subgroup (spinGroup (quadPlus n K))) (hcommEp : ∀ a ∈ Ep, ∀ b ∈ Ep, a * b = b * a)
    (hexp : ∀ x ∈ Ep, x ^ p = 1)
    (hNS : ∀ T : Submodule K (Fin n ⊕ Fin n → K),
      (∀ e ∈ Ep, ∀ v ∈ T, spinAction (quadPlus n K) e v ∈ T) →
      (∀ v ∈ T, quadPlus n K v = 0) → T = ⊥) :
    ∃ x : spinGroup (quadPlus n K), ∀ e ∈ Ep, x * e * x⁻¹ ∈ spinFrameGroup n K hn ι := by
  obtain ⟨Pl, hGP⟩ := exists_goodPlanes_spin hn hnk hp hp5 hpl hord Ep hcommEp hexp hNS
  exact exists_spin_conj_of_goodPlanes hodd hn hnk ι hp (by omega) Ep hexp hGP

theorem exists_spin_conj_frameGroup_elem_charTwo [CharP K 2] {n : ℕ} (hn : 3 ≤ n) {k : ℕ}
    (hnk : n = 2 * k) (ι : Fin k × Bool ≃ Fin n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpl : p ≠ ringChar K) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    (Ep : Subgroup (spinGroup (quadPlus n K))) (hcommEp : ∀ a ∈ Ep, ∀ b ∈ Ep, a * b = b * a)
    (hexp : ∀ x ∈ Ep, x ^ p = 1)
    (hNS : ∀ T : Submodule K (Fin n ⊕ Fin n → K),
      (∀ e ∈ Ep, ∀ v ∈ T, spinAction (quadPlus n K) e v ∈ T) →
      (∀ v ∈ T, quadPlus n K v = 0) → T = ⊥) :
    ∃ x : spinGroup (quadPlus n K), ∀ e ∈ Ep, x * e * x⁻¹ ∈ spinFrameGroup n K hn ι := by
  obtain ⟨Pl, hGP⟩ := exists_goodPlanes_spin hn hnk hp hp5 hpl hord Ep hcommEp hexp hNS
  exact exists_spin_conj_of_goodPlanes_charTwo hn hnk ι hp (by omega) Ep hexp hGP

end Spin

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest2
