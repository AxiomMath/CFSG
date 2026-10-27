module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDOrb

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section Cards

variable {F : Type} [Field F] [Finite F]

theorem finrank_le_of_natCard_le {V V' : Type*} [AddCommGroup V] [Module F V] [AddCommGroup V']
    [Module F V'] [Module.Finite F V] [Module.Finite F V'] (h : Nat.card V ≤ Nat.card V') :
    Module.finrank F V ≤ Module.finrank F V' := by
  rw [Module.natCard_eq_pow_finrank (K := F) (V := V),
    Module.natCard_eq_pow_finrank (K := F) (V := V')] at h
  exact (Nat.pow_le_pow_iff_right Finite.one_lt_card).1 h

end Cards

section Iso

variable {p n : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F] [CharP F p]
  {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
  (σ : Representation (ZMod p) (SLm F) W)

instance stRep_moduleFinite {F : Type} [Field F] [Finite F] (A : ℕ) :
    Module.Finite F (stRep F A).asModule :=
  Module.Finite.equiv (stRep F A).asModuleEquiv.symm

instance repXT_moduleFinite : Module.Finite F (repXT σ).asModule :=
  haveI : Module.Finite F (XT p F W) := Module.Finite.equiv xtEquiv
  Module.Finite.equiv (repXT σ).asModuleEquiv.symm

instance submodule_moduleFinite (Y : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) :
    Module.Finite F ↥Y :=
  Module.Finite.of_injective (Y.subtype.restrictScalars F) Y.injective_subtype

instance submodule_finite (Y : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) :
    Finite ↥Y :=
  Module.finite_of_finite F

@[expose, reducible] noncomputable def isoC (B : ℕ) :
    Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule :=
  isotypicComponent (MonoidAlgebra F (SLm F)) (repXT σ).asModule (stRep F B).asModule

omit [Module.Finite (ZMod p) W] in
theorem map_phi_isoC_le (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n) {B : ℕ} (hB : B < p ^ n) :
    (isoC σ B).map (phiMod σ).toLinearMap ≤ isoC σ (rot p n B) := by
  unfold isoC isotypicComponent
  rw [sSup_eq_iSup', Submodule.map_iSup]
  refine iSup_le fun m => ?_
  obtain ⟨ι⟩ := m.2
  obtain ⟨e⟩ := map_phi_label σ hS hp2 hn hF m.1 hB ι
  exact le_sSup ⟨e⟩

omit [Module.Finite (ZMod p) W] in
theorem natCard_map_phi (Y : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) :
    Nat.card ↥(Y.map (phiMod σ).toLinearMap) = Nat.card ↥Y :=
  Nat.card_congr (Y.equivMapOfInjective (phiMod σ).toLinearMap (phiMod σ).injective).toEquiv.symm

theorem finrank_map_phi (Y : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) :
    Module.finrank F ↥(Y.map (phiMod σ).toLinearMap) = Module.finrank F ↥Y := by
  have h := natCard_map_phi σ Y
  rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥(Y.map (phiMod σ).toLinearMap)),
    Module.natCard_eq_pow_finrank (K := F) (V := ↥Y)] at h
  exact Nat.pow_right_injective (Nat.succ_le_of_lt Finite.one_lt_card) h

end Iso

section Rot

theorem mix11cD_rot_injOn {p : ℕ} (hp : 1 < p) {n : ℕ} (hn : 0 < n) {A B : ℕ} (hA : A < p ^ n)
    (hB : B < p ^ n) (h : rot p n A = rot p n B) : A = B := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hpos : 0 < p ^ m := by positivity
  have hYA : A / p ^ m < p := by
    rw [Nat.div_lt_iff_lt_mul hpos]; simpa [pow_succ, mul_comm] using hA
  have hYB : B / p ^ m < p := by
    rw [Nat.div_lt_iff_lt_mul hpos]; simpa [pow_succ, mul_comm] using hB
  simp only [rot, Nat.succ_sub_one] at h
  have hmodA : ((A % p ^ m) * p + A / p ^ m) % p = A / p ^ m := by
    rw [mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hYA
  have hmodB : ((B % p ^ m) * p + B / p ^ m) % p = B / p ^ m := by
    rw [mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hYB
  have hdivA : ((A % p ^ m) * p + A / p ^ m) / p = A % p ^ m := by
    rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hYA, add_zero]
  have hdivB : ((B % p ^ m) * p + B / p ^ m) / p = B % p ^ m := by
    rw [mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hYB, add_zero]
  have e1 : A / p ^ m = B / p ^ m := by rw [← hmodA, ← hmodB, h]
  have e2 : A % p ^ m = B % p ^ m := by rw [← hdivA, ← hdivB, h]
  rw [← Nat.mod_add_div A (p ^ m), ← Nat.mod_add_div B (p ^ m), e1, e2]

theorem mix11cD_rot_periodic {p : ℕ} (hp : 1 < p) {n : ℕ} (hn : 0 < n) {A : ℕ} (hA : A < p ^ n) :
    ∃ k, 0 < k ∧ (rot p n)^[k] A = A := by
  have hmaps : ∀ B, B < p ^ n → rot p n B < p ^ n := fun B hB => mix11cD_rot_lt hp hn hB
  let g : Fin (p ^ n) → Fin (p ^ n) := fun B => ⟨rot p n B.1, hmaps B.1 B.2⟩
  have hginj : Function.Injective g := fun B B' h =>
    Fin.ext (mix11cD_rot_injOn hp hn B.2 B'.2 (congrArg Fin.val h))
  have hbij : Function.Bijective g := ⟨hginj, Finite.surjective_of_injective hginj⟩
  let σ' : Equiv.Perm (Fin (p ^ n)) := Equiv.ofBijective g hbij
  have hfin : IsOfFinOrder σ' := isOfFinOrder_of_finite σ'
  obtain ⟨k, hk0, hk⟩ := hfin.exists_pow_eq_one
  refine ⟨k, hk0, ?_⟩
  have hiter : ∀ (j : ℕ) (B : Fin (p ^ n)), ((σ' ^ j) B).1 = (rot p n)^[j] B.1 := by
    intro j
    induction j with
    | zero => intro B; simp
    | succ j ih =>
      intro B
      rw [pow_succ, Equiv.Perm.mul_apply, Function.iterate_succ_apply]
      have := ih (σ' B)
      simpa [σ', g] using this
  have := hiter k ⟨A, hA⟩
  rw [hk] at this
  simpa using this.symm

theorem mix11cD_rotPeriod_pos {p : ℕ} (hp : 1 < p) {n : ℕ} (hn : 0 < n) {A : ℕ} (hA : A < p ^ n) :
    0 < rotPeriod p n A := by
  obtain ⟨k, hk0, hk⟩ := mix11cD_rot_periodic hp hn hA
  exact Function.IsPeriodicPt.minimalPeriod_pos hk0 hk

end Rot

section Orbit

variable {p n : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F] [CharP F p]
  {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
  (σ : Representation (ZMod p) (SLm F) W)

omit [Fact p.Prime] in
theorem mix11cD_iterate_rot_lt (hp : 1 < p) (hn : 0 < n) {A : ℕ} (hA : A < p ^ n) (j : ℕ) :
    (rot p n)^[j] A < p ^ n := by
  induction j with
  | zero => simpa using hA
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact mix11cD_rot_lt hp hn ih

theorem finrank_isoC_le (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    {B : ℕ} (hB : B < p ^ n) :
    Module.finrank F ↥(isoC σ B) ≤ Module.finrank F ↥(isoC σ (rot p n B)) := by
  have hle := map_phi_isoC_le σ hS hp2 hn hF hB
  rw [← finrank_map_phi σ (isoC σ B)]
  exact finrank_le_of_natCard_le
    (Nat.card_le_card_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle))

theorem finrank_isoC_orbit (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n) {A : ℕ} (hA : A < p ^ n) (j : ℕ) :
    Module.finrank F ↥(isoC σ ((rot p n)^[j] A)) = Module.finrank F ↥(isoC σ A) := by
  have hp : 1 < p := Nat.Prime.one_lt Fact.out
  set f : ℕ → ℕ := fun j => Module.finrank F ↥(isoC σ ((rot p n)^[j] A)) with hf
  have hmono : ∀ j, f j ≤ f (j + 1) := by
    intro j
    simp only [hf]
    rw [Function.iterate_succ_apply']
    exact finrank_isoC_le σ hS hp2 hn hF (mix11cD_iterate_rot_lt hp hn hA j)
  have hmon : Monotone f := monotone_nat_of_le_succ hmono
  have hr : 0 < rotPeriod p n A := mix11cD_rotPeriod_pos hp hn hA
  have hper : (rot p n)^[rotPeriod p n A] A = A := Function.iterate_minimalPeriod
  have hfr : f (rotPeriod p n A) = f 0 := by
    simp only [hf, Function.iterate_zero, id_eq]
    rw [hper]
    rfl
  have hjmod : (rot p n)^[j] A = (rot p n)^[j % rotPeriod p n A] A :=
    (Function.iterate_mod_minimalPeriod_eq).symm
  have hlt : j % rotPeriod p n A ≤ rotPeriod p n A := (Nat.mod_lt _ hr).le
  show f j = f 0
  have h1 : f j = f (j % rotPeriod p n A) := by simp only [hf]; rw [hjmod]
  rw [h1]
  exact le_antisymm (hfr ▸ hmon hlt) (hmon (Nat.zero_le _))

end Orbit

section Sum

variable {p n : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F] [CharP F p]
  {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
  (σ : Representation (ZMod p) (SLm F) W)

omit [Module.Finite (ZMod p) W] in
theorem isotypic_eq_orbit (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n)
    (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule)
    (hsimple : ∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j))
    (htop : ⨆ j, orbSub σ N j = ⊤) :
    (∀ c ∈ isotypicComponents (MonoidAlgebra F (SLm F)) (repXT σ).asModule,
        ∃ j, c = isoC σ ((rot p n)^[j] A)) ∧
      ∀ j, isoC σ ((rot p n)^[j] A) ∈
        isotypicComponents (MonoidAlgebra F (SLm F)) (repXT σ).asModule := by
  constructor
  · rintro c ⟨S, hS', rfl⟩
    have hs : sSup (Set.range (orbSub σ N)) = ⊤ := by rw [sSup_range]; exact htop
    have : ∀ m : (Set.range (orbSub σ N)), IsSimpleModule (MonoidAlgebra F (SLm F)) m := by
      rintro ⟨m, j, rfl⟩
      exact hsimple j
    obtain ⟨S', ⟨j, rfl⟩, ⟨e⟩⟩ := Submodule.linearEquiv_of_sSup_eq_top S (Set.range (orbSub σ N)) hs
    obtain ⟨-, ⟨e2⟩⟩ := orbSub_label σ hS hp2 hn hF N hA ι j
    exact ⟨j, (e.trans e2).isotypicComponent_eq⟩
  · intro j
    obtain ⟨-, ⟨e2⟩⟩ := orbSub_label σ hS hp2 hn hF N hA ι j
    refine ⟨orbSub σ N j, hsimple j, ?_⟩
    exact e2.isotypicComponent_eq.symm

omit [Module.Finite (ZMod p) W] in
theorem orbSub_le_isoC (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule) (j : ℕ) :
    orbSub σ N j ≤ isoC σ ((rot p n)^[j] A) := by
  obtain ⟨-, ⟨e2⟩⟩ := orbSub_label σ hS hp2 hn hF N hA ι j
  have h := (orbSub σ N j).le_isotypicComponent
  unfold isoC
  rw [← e2.isotypicComponent_eq]
  exact h

omit [Module.Finite (ZMod p) W] in
theorem isoC_orbit_injOn (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule)
    (hsimple : ∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j))
    {j k : ℕ} (hj : j < rotPeriod p n A) (hk : k < rotPeriod p n A)
    (h : isoC σ ((rot p n)^[j] A) = isoC σ ((rot p n)^[k] A)) : j = k := by
  have hp : 1 < p := Nat.Prime.one_lt Fact.out
  obtain ⟨hltj, ⟨ej⟩⟩ := orbSub_label σ hS hp2 hn hF N hA ι j
  obtain ⟨hltk, ⟨ek⟩⟩ := orbSub_label σ hS hp2 hn hF N hA ι k
  have hle : orbSub σ N j ≤ isoC σ ((rot p n)^[k] A) :=
    (orbSub_le_isoC σ hS hp2 hn hF hA ι j).trans h.le
  have hiso : IsIsotypicOfType (MonoidAlgebra F (SLm F)) ↥(isoC σ ((rot p n)^[k] A))
      (stRep F ((rot p n)^[k] A)).asModule :=
    have := stRep_simple hS hp2 hn hF hltk
    IsIsotypicOfType.isotypicComponent _ _ _
  have := hsimple j
  obtain ⟨e'⟩ := (isIsotypicOfType_submodule_iff.mp hiso) (orbSub σ N j) hle
  have e'' : (steinbergRep F F ((rot p n)^[j] A)).asModule ≃ₗ[MonoidAlgebra F (SLm F)]
      (steinbergRep F F ((rot p n)^[k] A)).asModule :=
    (stEquiv F _).trans ((ej.symm.trans e').trans (stEquiv F _).symm)
  have hlab : (rot p n)^[j] A = (rot p n)^[k] A :=
    (hS p n Fact.out hp2 hn F hF).2.1 _ _ hltj hltk ⟨e''⟩
  exact Function.iterate_injOn_Iio_minimalPeriod hj hk hlab

instance repXT_isNoetherian : IsNoetherian (MonoidAlgebra F (SLm F)) (repXT σ).asModule :=
  isNoetherian_of_tower F (inferInstance : IsNoetherian F (repXT σ).asModule)

theorem finrank_X_eq (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule)
    (hsimple : ∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j))
    (htop : ⨆ j, orbSub σ N j = ⊤) :
    Module.finrank F (repXT σ).asModule =
      rotPeriod p n A * Module.finrank F ↥(isoC σ A) := by
  classical
  obtain ⟨hcomp, hmem⟩ := isotypic_eq_orbit σ hS hp2 hn hF hA ι hsimple htop
  have hp : 1 < p := Nat.Prime.one_lt Fact.out
  have hr : 0 < rotPeriod p n A := mix11cD_rotPeriod_pos hp hn hA
  let C := isotypicComponents (MonoidAlgebra F (SLm F)) (repXT σ).asModule
  have : Finite C := inferInstance
  have := Fintype.ofFinite C
  have hsemi : IsSemisimpleModule (MonoidAlgebra F (SLm F)) (repXT σ).asModule := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    rw [eq_top_iff, ← htop]
    exact iSup_le fun j => le_sSup (hsimple j)
  have hind : iSupIndep (fun c : C => c.1) :=
    (sSupIndep_iff _).1 (sSupIndep_isotypicComponents _ _)
  have hsup : ⨆ c : C, c.1 = ⊤ := by
    rw [← sSup_eq_iSup']
    exact sSup_isotypicComponents _ _
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  let e : (DirectSum C fun c : C => ↥c.1) ≃ₗ[MonoidAlgebra F (SLm F)] (repXT σ).asModule :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun c : C => c.1)) hint
  have h1 : Module.finrank F (repXT σ).asModule = ∑ c : C, Module.finrank F ↥c.1 := by
    rw [← (e.restrictScalars F).finrank_eq, Module.finrank_directSum]
  let g : Fin (rotPeriod p n A) → C := fun j => ⟨isoC σ ((rot p n)^[j.1] A), hmem j.1⟩
  have hginj : Function.Injective g := by
    intro j k hjk
    exact Fin.ext (isoC_orbit_injOn σ hS hp2 hn hF hA ι hsimple j.2 k.2 (congrArg Subtype.val hjk))
  have hgsurj : Function.Surjective g := by
    intro c
    obtain ⟨j, hj⟩ := hcomp c.1 c.2
    refine ⟨⟨j % rotPeriod p n A, Nat.mod_lt _ hr⟩, Subtype.ext ?_⟩
    simp only [g]
    have hj' : (rot p n)^[j % rotPeriod p n A] A = (rot p n)^[j] A :=
      Function.iterate_mod_minimalPeriod_eq
    rw [hj, hj']
  have h2 : ∑ c : C, Module.finrank F ↥c.1 =
      ∑ j : Fin (rotPeriod p n A), Module.finrank F ↥(isoC σ ((rot p n)^[j.1] A)) :=
    (Fintype.sum_bijective g ⟨hginj, hgsurj⟩ _ _ (fun j => rfl)).symm
  rw [h1, h2]
  simp [finrank_isoC_orbit σ hS hp2 hn hF hA]

theorem finrank_isoC_eq (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < p ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule) (hN : N ≠ ⊥) :
    ∃ c : ℕ, 0 < c ∧ Module.finrank F ↥(isoC σ A) =
      c * Module.finrank F (stRep F A).asModule := by
  have hsimpA := stRep_simple hS hp2 hn hF hA
  have hiso : IsIsotypicOfType (MonoidAlgebra F (SLm F)) ↥(isoC σ A) (stRep F A).asModule :=
    IsIsotypicOfType.isotypicComponent _ _ _
  obtain ⟨c, ⟨e⟩⟩ := hiso.linearEquiv_fun
  refine ⟨c, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos c with rfl | hc
    · exfalso
      have hsub : Subsingleton ↥(isoC σ A) := e.toEquiv.subsingleton
      have hle : N ≤ isoC σ A := orbSub_le_isoC σ hS hp2 hn hF hA ι 0
      apply hN
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hle hx⟩ : ↥(isoC σ A)) = 0 := Subsingleton.elim _ _
      have := congrArg Subtype.val this
      simpa using this
    · exact hc
  · rw [(e.restrictScalars F).finrank_eq, Module.finrank_pi_fintype]
    simp

theorem descent_data (hS : Mix11cSteinberg) (hp2 : p ≠ 2) (hn : 0 < n) (hF : Nat.card F = p ^ n)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod p) (SLm F)) σ.asModule) :
    ∃ (N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule) (A c : ℕ),
      A < p ^ n ∧ 0 < c ∧
      Nonempty (↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule) ∧
      (∀ j, IsSimpleModule (MonoidAlgebra F (SLm F)) ↥(orbSub σ N j)) ∧
      ⨆ j, orbSub σ N j = ⊤ ∧
      Module.finrank (ZMod p) W = c * rotPeriod p n A * digitProd p n A ∧
      (c = 1 → Module.finrank F ↥(isoC σ A) = Module.finrank F (stRep F A).asModule) := by
  obtain ⟨N, A, hNatom, hA, ⟨ι⟩, hsimple, htop, -⟩ := orbit_structure σ hS hp2 hn hF hW
  obtain ⟨c, hc, hcdim⟩ := finrank_isoC_eq σ hS hp2 hn hF hA ι hNatom.1
  have hX := finrank_X_eq σ hS hp2 hn hF hA ι hsimple htop
  have hW1 : Module.finrank (ZMod p) W = Module.finrank F (repXT σ).asModule := by
    let e : (repXT σ).asModule ≃ₗ[F] F ⊗[ZMod p] W := (repXT σ).asModuleEquiv.trans xtEquiv.symm
    rw [e.finrank_eq, Module.finrank_baseChange]
  have hfin : Module.finrank F (stRep F A).asModule = digitProd p n A := by
    have h1 := ((hS p n Fact.out hp2 hn F hF).1 A hA).2.1
    rw [← h1]
    exact (stRep F A).asModuleEquiv.finrank_eq
  refine ⟨N, A, c, hA, hc, ⟨ι⟩, hsimple, htop, ?_, fun h1 => by rw [hcdim, h1, one_mul]⟩
  rw [hW1, hX, hcdim, hfin]
  ring

end Sum

end CFSG.GH74.GLS.Stage4.Rest
