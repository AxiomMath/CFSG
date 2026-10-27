module

public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.CharacterTheory.Semidihedral.MatrixFourGroupNormalizer
public import CFSG.CharacterTheory.Semidihedral.Principal.InvertedCyclicModuleBound

public section

namespace CFSG.Semidihedral.DefiningCharacteristicDimension

noncomputable section

open Matrix

universe u v w

variable {F : Type u} [Field F] {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

@[expose] def negativeSpace
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V) : Submodule k V :=
  Module.End.eigenspace (ρ (OddFieldSL2.minusIdentity F) : Module.End k V) (-1)

theorem mem_negativeSpace
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V) (v : V) :
    v ∈ negativeSpace ρ ↔ (ρ (OddFieldSL2.minusIdentity F) : Module.End k V) v = -v := by
  simp only [negativeSpace, Module.End.mem_eigenspace_iff, neg_one_smul]

theorem negativeSpace_invariant
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V)
    (g : SpecialLinearGroup (Fin 2) F) :
    negativeSpace ρ ≤ (negativeSpace ρ).comap (ρ g : Module.End k V) := by
  intro v hv
  apply (mem_negativeSpace ρ _).mpr
  have hzv := (mem_negativeSpace ρ v).mp hv
  have hcomm : ρ (OddFieldSL2.minusIdentity F) * ρ g =
      ρ g * ρ (OddFieldSL2.minusIdentity F) := by
    simpa only [map_mul] using congrArg ρ
      ((Subgroup.mem_center_iff.mp (OddFieldSL2.minusIdentity_mem_center F)) g).symm
  have heval := congrArg (fun A : LinearMap.GeneralLinearGroup k V =>
    (A : Module.End k V) v) hcomm
  simpa only [Units.val_mul, Module.End.mul_apply, hzv, map_neg] using heval

@[expose] def negativeRepresentation
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V) :
    Representation k (SpecialLinearGroup (Fin 2) F) (negativeSpace ρ) :=
  Representation.subrepresentation ((Units.coeHom (Module.End k V)).comp ρ)
    (negativeSpace ρ) (negativeSpace_invariant ρ)

@[expose] def negativeAction
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V) :
    SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k (negativeSpace ρ) :=
  (negativeRepresentation ρ).asGroupHom

theorem negativeAction_apply
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V)
    (g : SpecialLinearGroup (Fin 2) F) (v : negativeSpace ρ) :
    ((negativeAction ρ g : Module.End k (negativeSpace ρ)) v : V) =
      (ρ g : Module.End k V) (v : V) := by
  simp only [negativeAction, Representation.asGroupHom_apply]
  rfl

theorem negativeAction_minusIdentity
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V) :
    negativeAction ρ (OddFieldSL2.minusIdentity F) = -1 := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [negativeAction_apply]
  simpa using (mem_negativeSpace ρ (v : V)).mp v.property

theorem negativeSpace_ne_bot
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V)
    (hρ : ρ (OddFieldSL2.minusIdentity F) ≠ 1) : negativeSpace ρ ≠ ⊥ := by
  intro hbot
  apply hρ
  apply Units.ext
  ext v
  have hv : (ρ (OddFieldSL2.minusIdentity F) : Module.End k V) v - v ∈
      negativeSpace ρ := by
    apply (mem_negativeSpace ρ _).mpr
    have hsquare : (ρ (OddFieldSL2.minusIdentity F) : Module.End k V) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, OddFieldSL2.minusIdentity_square, map_one]
      rfl
    have heval := congrArg (fun T : Module.End k V => T v) hsquare
    simp only [pow_two, Module.End.mul_apply, Module.End.one_apply] at heval
    simp only [map_sub, heval]
    abel
  rw [hbot, Submodule.mem_bot] at hv
  exact sub_eq_zero.mp hv

theorem nativeSL2_quasisimple [Finite F] (hF : 4 ≤ Nat.card F) :
    CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin 2) F) := by
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hF
  exact ⟨Group.IsPerfect.commutator_eq_top,
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF⟩

theorem nativeSL2_action_injective [Finite F] (hF : 4 ≤ Nat.card F)
    {H : Type*} [Group H] (φ : SpecialLinearGroup (Fin 2) F →* H)
    (hφ : φ (OddFieldSL2.minusIdentity F) ≠ 1) : Function.Injective φ := by
  have hproper : φ.ker ≠ ⊤ := by
    intro htop
    apply hφ
    apply MonoidHom.mem_ker.mp
    rw [htop]
    trivial
  have hcentral := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
    (nativeSL2_quasisimple hF) φ.ker hproper
  apply (MonoidHom.ker_eq_bot_iff φ).mp
  apply le_antisymm _ bot_le
  intro g hg
  rcases (ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F g).mp
      (hcentral hg) with rfl | hz
  · exact Subgroup.one_mem _
  · have hg' := MonoidHom.mem_ker.mp hg
    rw [hz, ProjectiveSL2Cover.minusIdentity_eq_neg_one] at hg'
    exact (hφ (by simpa only [OddFieldSL2.minusIdentity] using hg')).elim

theorem negativeAction_minusIdentity_ne_one [Finite k]
    (hkodd : Odd (Nat.card k))
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V)
    (hρ : ρ (OddFieldSL2.minusIdentity F) ≠ 1) :
    negativeAction ρ (OddFieldSL2.minusIdentity F) ≠ 1 := by
  let : Nontrivial (negativeSpace ρ) :=
    Submodule.nontrivial_iff_ne_bot.mpr (negativeSpace_ne_bot ρ hρ)
  obtain ⟨v, hv⟩ := exists_ne (0 : negativeSpace ρ)
  intro h
  have heval := congrArg (fun A : LinearMap.GeneralLinearGroup k (negativeSpace ρ) =>
    (A : Module.End k (negativeSpace ρ)) v) h
  rw [negativeAction_minusIdentity] at heval
  have hneg : -v = v := by simpa using heval
  have hzero : (2 : k) • v = 0 := by
    rw [two_smul]
    calc
      v + v = -v + v := congrArg (fun x => x + v) hneg.symm
      _ = 0 := neg_add_cancel v
  exact (smul_eq_zero.mp hzero).elim
    (OddFieldSL2.two_ne_zero_of_odd_card k hkodd) hv

theorem negativeAction_injective [Finite F] [Finite k]
    (hF : 4 ≤ Nat.card F) (hkodd : Odd (Nat.card k))
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V)
    (hρ : ρ (OddFieldSL2.minusIdentity F) ≠ 1) :
    Function.Injective (negativeAction ρ) :=
  nativeSL2_action_injective hF (negativeAction ρ)
    (negativeAction_minusIdentity_ne_one hkodd ρ hρ)

theorem exists_native_inverted_torus [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ (T : Subgroup (SpecialLinearGroup (Fin 2) F))
      (u : T) (w : SpecialLinearGroup (Fin 2) F),
      IsCyclic T ∧ Nat.card T = Nat.card F + 1 ∧
      (∀ x : T, x ∈ Subgroup.zpowers u) ∧
      orderOf (u : SpecialLinearGroup (Fin 2) F) = Nat.card F + 1 ∧
      (u : SpecialLinearGroup (Fin 2) F) ^ ((Nat.card F + 1) / 2) =
        OddFieldSL2.minusIdentity F ∧
      w ^ 2 = OddFieldSL2.minusIdentity F ∧
      (∀ x : T, w * (x : SpecialLinearGroup (Fin 2) F) * w⁻¹ =
        (x : SpecialLinearGroup (Fin 2) F)⁻¹) := by
  have hchar : ringChar F ≠ 2 := by
    intro hc
    apply OddFieldSL2.two_ne_zero_of_odd_card F hodd
    simpa [hc] using CharP.cast_eq_zero F (ringChar F)
  obtain ⟨d, hd⟩ := FiniteField.exists_nonsquare
    hchar
  have hd0 : d ≠ 0 := fun heq => hd (by rw [heq]; exact ⟨0, by simp⟩)
  let a : Fˣ := -Units.mk0 d hd0
  have ha : ¬IsSquare (-(a : F)) := by simpa [a] using hd
  let T := MatrixTorus.Torus F a
  let : IsCyclic T := MatrixTorus.nonsplit_torus_cyclic F a ha
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := T)
  have hcard : Nat.card T = Nat.card F + 1 := MatrixTorus.nonsplit_torus_card F a ha
  have horder : orderOf u = Nat.card F + 1 :=
    (orderOf_eq_card_of_forall_mem_zpowers hu).trans hcard
  have heven : 2 ∣ orderOf u := by
    rw [horder]
    exact even_iff_two_dvd.mp hodd.add_one
  have hhalf : orderOf (u ^ ((Nat.card F + 1) / 2)) = 2 := by
    rw [← horder]
    exact orderOf_pow_orderOf_div (by rw [horder]; omega) heven
  have hz : u ^ ((Nat.card F + 1) / 2) = MatrixTorus.z F a :=
    (MatrixTorus.torus_unique_involution F a hodd _).mp hhalf
  obtain ⟨x, y, hxy⟩ := MatrixFourGroupNormalizer.scaled_two_squares F hodd
    (a : F) a.ne_zero (-1)
  refine ⟨T, u, MatrixFourGroupNormalizer.nativeX F a x y hxy, inferInstance,
    hcard, hu, ?_, ?_, MatrixFourGroupNormalizer.nativeX_square F a x y hxy, ?_⟩
  · exact (Subgroup.orderOf_mk (u : SpecialLinearGroup (Fin 2) F) u.property).symm.trans horder
  · exact congrArg Subtype.val hz
  · exact MatrixFourGroupNormalizer.nativeX_inverts_torus F a x y hxy

theorem irreducible_of_surjective_pullback {G H : Type*} [Monoid G] [Monoid H]
    (ρ : Representation k H V) (φ : G →* H) (hφ : Function.Surjective φ)
    (hirr : Representation.IsIrreducible ρ) : Representation.IsIrreducible (ρ.comp φ) := by
  let : Representation.IsIrreducible ρ := hirr
  have hbot : (⊥ : Subrepresentation (ρ.comp φ)) ≠ ⊤ := by
    intro heq
    have hsub : (⊥ : Submodule k V) = ⊤ :=
      congrArg Subrepresentation.toSubmodule heq
    apply IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ)
    exact Subrepresentation.toSubmodule_injective hsub
  refine (isSimpleOrder_iff _).mpr ⟨⟨⟨⊥, ⊤, hbot⟩⟩, ?_⟩
  intro W
  let W' : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro h v hv
        obtain ⟨g, rfl⟩ := hφ h
        exact W.apply_mem_toSubmodule g hv }
  rcases IsSimpleOrder.eq_bot_or_eq_top W' with hb | ht
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun S : Subrepresentation ρ => S.toSubmodule) hb)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun S : Subrepresentation ρ => S.toSubmodule) ht)

theorem irreducible_of_subgroup_restriction {G : Type*} [Group G]
    (ρ : Representation k G V) (T : Subgroup G)
    (hirr : Representation.IsIrreducible (ρ.comp T.subtype)) :
    Representation.IsIrreducible ρ := by
  let : Representation.IsIrreducible (ρ.comp T.subtype) := hirr
  have hbot : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro heq
    have hsub : (⊥ : Submodule k V) = ⊤ :=
      congrArg Subrepresentation.toSubmodule heq
    apply IsSimpleOrder.bot_ne_top (α := Subrepresentation (ρ.comp T.subtype))
    exact Subrepresentation.toSubmodule_injective hsub
  refine (isSimpleOrder_iff _).mpr ⟨⟨⟨⊥, ⊤, hbot⟩⟩, ?_⟩
  intro W
  let W' : Subrepresentation (ρ.comp T.subtype) :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := fun g v hv => W.apply_mem_toSubmodule g hv }
  rcases IsSimpleOrder.eq_bot_or_eq_top W' with hb | ht
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun S : Subrepresentation (ρ.comp T.subtype) => S.toSubmodule) hb)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun S : Subrepresentation (ρ.comp T.subtype) => S.toSubmodule) ht)

theorem cyclic_torus_image_surjective
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V)
    (T : Subgroup (SpecialLinearGroup (Fin 2) F)) (u : T)
    (hu : ∀ x : T, x ∈ Subgroup.zpowers u) :
    ∃ φ : T →* Subgroup.zpowers (ρ (u : SpecialLinearGroup (Fin 2) F)),
      Function.Surjective φ ∧
      ∀ x : T, (φ x : LinearMap.GeneralLinearGroup k V) =
        ρ (x : SpecialLinearGroup (Fin 2) F) := by
  let ψ := ρ.comp T.subtype
  have hmem (x : T) : ψ x ∈ Subgroup.zpowers (ρ (u : SpecialLinearGroup (Fin 2) F)) := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hu x)
    rw [map_zpow]
    exact (Subgroup.zpowers (ρ (u : SpecialLinearGroup (Fin 2) F))).zpow_mem
      (Subgroup.mem_zpowers _) _
  let φ := ψ.codRestrict _ hmem
  refine ⟨φ, ?_, fun _ => rfl⟩
  intro x
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.property
  refine ⟨u ^ j, ?_⟩
  apply Subtype.ext
  change ψ (u ^ j) = (x : LinearMap.GeneralLinearGroup k V)
  simpa only [map_zpow, ψ, MonoidHom.comp_apply, Subgroup.coe_subtype] using hj

theorem negativeSpace_dimension_bound [Finite F] [Finite k] [FiniteDimensional k V]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) (hk : Nat.card k = p)
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V)
    (hρ : ρ (OddFieldSL2.minusIdentity F) ≠ 1) :
    2 * f ≤ Module.finrank k (negativeSpace ρ) := by
  let : Fintype k := Fintype.ofFinite k
  let : Nontrivial (negativeSpace ρ) :=
    Submodule.nontrivial_iff_ne_bot.mpr (negativeSpace_ne_bot ρ hρ)
  have hkodd : Odd (Nat.card k) := by rw [hk]; exact hpodd
  have hFodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hFfour : 4 ≤ Nat.card F := by omega
  obtain ⟨T, u, w, _, _, _, huorder, huhalf, _, hwinv⟩ :=
    exists_native_inverted_torus hFodd
  let σ := negativeAction ρ
  have hσ : Function.Injective σ := negativeAction_injective hFfour hkodd ρ hρ
  have horder : orderOf (σ (u : SpecialLinearGroup (Fin 2) F)) = p ^ f + 1 := by
    rw [orderOf_injective σ hσ, huorder, hcard]
  have heven : Even (p ^ f + 1) := hpodd.pow.add_one
  have hpn : ¬ p ∣ p ^ f + 1 := by
    intro hdvd
    have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hpq).mpr hdvd)
  have hhalf : σ (u : SpecialLinearGroup (Fin 2) F) ^ ((p ^ f + 1) / 2) = -1 := by
    rw [← map_pow, ← hcard, huhalf]
    exact negativeAction_minusIdentity ρ
  have hinv : σ w * σ (u : SpecialLinearGroup (Fin 2) F) * (σ w)⁻¹ =
      (σ (u : SpecialLinearGroup (Fin 2) F))⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg σ (hwinv u)
  have hbound := (Principal.inverted_cyclic_prime_field_module_even_order_bound hp hpodd hk
    (Module.finrank_pos) (σ (u : SpecialLinearGroup (Fin 2) F)) (σ w)
    horder heven hpn hhalf hinv).1
  have hexponent : f ≤ Module.finrank k (negativeSpace ρ) / 2 :=
    (Nat.pow_le_pow_iff_right hp.one_lt).mp (by omega)
  omega

theorem original_minusIdentity_action_of_negativeSpace_eq_top
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V)
    (hspace : negativeSpace ρ = ⊤) : ρ (OddFieldSL2.minusIdentity F) = -1 := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  have hv : v ∈ negativeSpace ρ := by rw [hspace]; trivial
  simpa using (mem_negativeSpace ρ v).mp hv

theorem odd_defining_characteristic_SL2_action_minimum_dimension
    [Finite F] [Finite k] [FiniteDimensional k V]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) (hk : Nat.card k = p)
    (ρ : SpecialLinearGroup (Fin 2) F →* LinearMap.GeneralLinearGroup k V)
    (hρ : ρ (OddFieldSL2.minusIdentity F) ≠ 1) :
    Function.Injective (negativeAction ρ) ∧
      2 * f ≤ Module.finrank k (negativeSpace ρ) ∧
      Function.Injective ρ ∧ 2 * f ≤ Module.finrank k V ∧
      (Module.finrank k V = 2 * f →
        Representation.IsIrreducible ((Units.coeHom (Module.End k V)).comp ρ) ∧
          ∃ T : Subgroup (SpecialLinearGroup (Fin 2) F), IsCyclic T ∧
            Nat.card T = p ^ f + 1 ∧
            Representation.IsIrreducible
              (((Units.coeHom (Module.End k V)).comp ρ).comp T.subtype)) := by
  let : Fintype k := Fintype.ofFinite k
  have hkodd : Odd (Nat.card k) := by rw [hk]; exact hpodd
  have hFodd : Odd (Nat.card F) := by rw [hcard]; exact hpodd.pow
  have hFfour : 4 ≤ Nat.card F := by omega
  have hfaithful := nativeSL2_action_injective hFfour ρ hρ
  have hdim := negativeSpace_dimension_bound hp hpodd hf hcard hq hk ρ hρ
  have hwhole : 2 * f ≤ Module.finrank k V :=
    hdim.trans (Submodule.finrank_le (negativeSpace ρ))
  refine ⟨negativeAction_injective hFfour hkodd ρ hρ, hdim, hfaithful, hwhole, ?_⟩
  intro heq
  have hnegdim : Module.finrank k (negativeSpace ρ) = Module.finrank k V := by
    have hle := Submodule.finrank_le (negativeSpace ρ)
    omega
  have hspace := Submodule.eq_top_of_finrank_eq hnegdim
  have hz := original_minusIdentity_action_of_negativeSpace_eq_top ρ hspace
  obtain ⟨T, u, w, hcyclic, hTcard, hu, huorder, huhalf, _, hwinv⟩ :=
    exists_native_inverted_torus hFodd
  have horder : orderOf (ρ (u : SpecialLinearGroup (Fin 2) F)) = p ^ f + 1 := by
    rw [orderOf_injective ρ hfaithful, huorder, hcard]
  have hpn : ¬ p ∣ p ^ f + 1 := by
    intro hdvd
    exact hp.not_dvd_one
      ((Nat.dvd_add_iff_right (dvd_pow_self p (by omega : f ≠ 0))).mpr hdvd)
  have hhalf : ρ (u : SpecialLinearGroup (Fin 2) F) ^ ((p ^ f + 1) / 2) = -1 := by
    rw [← map_pow, ← hcard, huhalf, hz]
  have hinv : ρ w * ρ (u : SpecialLinearGroup (Fin 2) F) * (ρ w)⁻¹ =
      (ρ (u : SpecialLinearGroup (Fin 2) F))⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg ρ (hwinv u)
  have hirr := (Principal.inverted_cyclic_prime_field_module_even_order_bound hp hpodd hk
    (by omega) (ρ (u : SpecialLinearGroup (Fin 2) F)) (ρ w) horder
    hpodd.pow.add_one hpn hhalf hinv).2 f hf heq rfl |>.2
  obtain ⟨φ, hφ, hφvalue⟩ := cyclic_torus_image_surjective ρ T u hu
  have hpull := irreducible_of_surjective_pullback
    ((Units.coeHom (Module.End k V)).comp (Subgroup.zpowers
      (ρ (u : SpecialLinearGroup (Fin 2) F))).subtype) φ hφ hirr
  have haction : ((Units.coeHom (Module.End k V)).comp
      (Subgroup.zpowers (ρ (u : SpecialLinearGroup (Fin 2) F))).subtype).comp φ =
      (((Units.coeHom (Module.End k V)).comp ρ).comp T.subtype) := by
    ext x v
    exact congrArg (fun A : LinearMap.GeneralLinearGroup k V => (A : Module.End k V) v)
      (hφvalue x)
  rw [haction] at hpull
  refine ⟨irreducible_of_subgroup_restriction _ T hpull,
    T, hcyclic, ?_, hpull⟩
  exact hTcard.trans (by rw [hcard])

end

end CFSG.Semidihedral.DefiningCharacteristicDimension
