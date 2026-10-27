module

public import CFSG.CharacterTheory.Semidihedral.DefiningCharacteristicDimension
public import CFSG.CharacterTheory.Semidihedral.OddCentralSL2Kernel

public section

namespace CFSG.Semidihedral.OddCentralDimension

noncomputable section

universe u v w

variable {G : Type u} [Group G] {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

theorem nilpotent_end_eq_zero_of_injective (T : Module.End k V)
    (hT : IsNilpotent T) (hinj : Function.Injective T) : T = 0 := by
  obtain ⟨n, hn⟩ := hT
  have hpow : ∀ m : ℕ, Function.Injective (T ^ m : Module.End k V) := by
    intro m
    induction m with
    | zero =>
      intro x y hxy
      simpa using hxy
    | succ m ih =>
      intro x y hxy
      apply ih
      apply hinj
      simpa only [pow_succ', Module.End.mul_apply] using hxy
  have hz : ∀ v : V, v = 0 := by
    intro v
    apply hpow n
    rw [hn]
    simp
  ext v
  rw [hz v]
  simp

theorem central_p_element_action_eq_one {p : ℕ} [Fact p.Prime] [CharP k p]
    (ρ : Representation k G V) (hirr : Representation.IsIrreducible ρ)
    (g : G) (hcentral : g ∈ Subgroup.center G) (n : ℕ)
    (hpow : g ^ (p ^ n) = 1) : ρ g = 1 := by
  let : Representation.IsIrreducible ρ := hirr
  let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra k G) ρ.asModule
  let : CharP (Module.End k V) p := charP_of_injective_algebraMap' k p
  let T : Module.End k V := ρ g - 1
  let f : ρ.IntertwiningMap ρ :=
    { toLinearMap := T
      isIntertwining' := by
        intro h
        have hc : ρ g * ρ h = ρ h * ρ g := by
          rw [← map_mul, ← map_mul]
          exact congrArg ρ ((Subgroup.mem_center_iff.mp hcentral) h).symm
        ext v
        have heval := congrArg (fun A : Module.End k V => A v) hc
        simpa only [T, LinearMap.comp_apply, LinearMap.sub_apply,
          Module.End.one_apply, map_sub, Module.End.mul_apply] using
          congrArg (fun w => w - ρ h v) heval }
  have hnil : IsNilpotent T := by
    refine ⟨p ^ n, ?_⟩
    change (ρ g - 1) ^ (p ^ n) = 0
    rw [sub_pow_char_pow_of_commute p n (Commute.one_right _),
      ← map_pow, hpow, map_one, one_pow, sub_self]
  have hzero : T = 0 := by
    rcases Representation.IsIrreducible.injective_or_eq_zero f with hinj | hzero
    · exact nilpotent_end_eq_zero_of_injective T hnil hinj
    · exact congrArg Representation.IntertwiningMap.toLinearMap hzero
  exact sub_eq_zero.mp hzero

theorem central_pGroup_le_kernel {p : ℕ} [Fact p.Prime] [CharP k p]
    (ρ : Representation k G V) (hirr : Representation.IsIrreducible ρ)
    (A : Subgroup G) (hcentral : A ≤ Subgroup.center G) (hp : IsPGroup p A) :
    A ≤ ρ.ker := by
  intro a ha
  obtain ⟨n, hn⟩ := hp (⟨a, ha⟩ : A)
  exact central_p_element_action_eq_one ρ hirr a (hcentral ha) n
    (by simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using
      congrArg Subtype.val hn)

@[expose] def negativeSpace (ρ : Representation k G V) (t : G) : Submodule k V :=
  Module.End.eigenspace (ρ t) (-1)

theorem mem_negativeSpace (ρ : Representation k G V) (t : G) (v : V) :
    v ∈ negativeSpace ρ t ↔ ρ t v = -v := by
  simp only [negativeSpace, Module.End.mem_eigenspace_iff, neg_one_smul]

theorem negativeSpace_invariant (ρ : Representation k G V) (t : G)
    (ht : t ∈ Subgroup.center G) (g : G) :
    negativeSpace ρ t ≤ (negativeSpace ρ t).comap (ρ g) := by
  intro v hv
  apply (mem_negativeSpace ρ t _).mpr
  have hcomm : ρ t * ρ g = ρ g * ρ t := by
    rw [← map_mul, ← map_mul]
    exact congrArg ρ ((Subgroup.mem_center_iff.mp ht) g).symm
  have heval := congrArg (fun A : Module.End k V => A v) hcomm
  simpa only [Module.End.mul_apply, (mem_negativeSpace ρ t v).mp hv,
    map_neg] using heval

@[expose] def negativeSubrepresentation (ρ : Representation k G V) (t : G)
    (ht : t ∈ Subgroup.center G) : Subrepresentation ρ where
  toSubmodule := negativeSpace ρ t
  apply_mem_toSubmodule g := negativeSpace_invariant ρ t ht g

@[expose] def negativeRepresentation (ρ : Representation k G V) (t : G)
    (ht : t ∈ Subgroup.center G) : Representation k G (negativeSpace ρ t) :=
  (negativeSubrepresentation ρ t ht).toRepresentation

theorem negativeRepresentation_at_central (ρ : Representation k G V) (t : G)
    (ht : t ∈ Subgroup.center G) : negativeRepresentation ρ t ht t = -1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact (mem_negativeSpace ρ t v.val).mp v.property

theorem negativeSpace_ne_bot (ρ : Representation k G V) (t : G)
    (ht : t ^ 2 = 1) (hρ : ρ t ≠ 1) : negativeSpace ρ t ≠ ⊥ := by
  intro hbot
  apply hρ
  ext v
  have hsquare : ρ t * ρ t = 1 := by rw [← map_mul, ← pow_two, ht, map_one]
  have hval := congrArg (fun A : Module.End k V => A v) hsquare
  simp only [Module.End.mul_apply, Module.End.one_apply] at hval
  have hv : ρ t v - v ∈ negativeSpace ρ t := by
    apply (mem_negativeSpace ρ t _).mpr
    rw [map_sub, hval]
    abel
  rw [hbot, Submodule.mem_bot] at hv
  exact sub_eq_zero.mp hv

theorem irreducible_of_isAtom_subrepresentation (ρ : Representation k G V)
    (W : Subrepresentation ρ) (hW : IsAtom W) :
    Representation.IsIrreducible W.toRepresentation := by
  have hbot : (⊥ : Subrepresentation W.toRepresentation) ≠ ⊤ := by
    intro heq
    apply hW.1
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    intro v hv
    have hv' : (⟨v, hv⟩ : W.toSubmodule) ∈
        (⊥ : Subrepresentation W.toRepresentation) := by rw [heq]; trivial
    change (⟨v, hv⟩ : W.toSubmodule) = 0 at hv'
    exact congrArg Subtype.val hv'
  refine (isSimpleOrder_iff _).mpr ⟨⟨⟨⊥, ⊤, hbot⟩⟩, ?_⟩
  intro U
  let U' : Subrepresentation ρ :=
    { toSubmodule := U.toSubmodule.map W.toSubmodule.subtype
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
        exact Submodule.mem_map.mpr ⟨W.toRepresentation g w,
          U.apply_mem_toSubmodule g hw, rfl⟩ }
  have hle : U' ≤ W := by
    intro v hv
    obtain ⟨w, _, rfl⟩ := Submodule.mem_map.mp hv
    exact w.property
  rcases eq_or_lt_of_le hle with heq | hlt
  · right
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm le_top
    intro v _
    have hv : (v : V) ∈ U' := by rw [heq]; exact v.property
    obtain ⟨w, hw, hval⟩ := Submodule.mem_map.mp hv
    have hwv : w = v := Subtype.ext hval
    exact hwv ▸ hw
  · left
    have hz := hW.2 U' hlt
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    intro v hv
    have hv' : (v : V) ∈ U' := Submodule.mem_map.mpr ⟨v, hv, rfl⟩
    rw [hz] at hv'
    have hzero : (v : V) = 0 := hv'
    exact Subtype.ext hzero

theorem exists_irreducible_subrepresentation [Finite k] [FiniteDimensional k V]
    [Nontrivial V] (ρ : Representation k G V) :
    ∃ W : Subrepresentation ρ, W ≠ ⊥ ∧
      Representation.IsIrreducible W.toRepresentation := by
  let : Finite V := Module.finite_of_finite k
  let : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro heq
    have hsub : (⊥ : Submodule k V) = ⊤ := congrArg Subrepresentation.toSubmodule heq
    exact bot_ne_top hsub
  obtain ⟨W, hW⟩ := IsAtomic.exists_atom (Subrepresentation ρ)
  exact ⟨W, hW.1, irreducible_of_isAtom_subrepresentation ρ W hW⟩

@[expose] def descendedAction {H : Type*} [Group H] (β : G →* H)
    (hβ : Function.Surjective β) (ρ : Representation k G V)
    (hker : β.ker ≤ ρ.ker) : H →* LinearMap.GeneralLinearGroup k V :=
  β.liftOfSurjective hβ ⟨ρ.asGroupHom, by
    intro g hg
    apply Units.ext
    simpa only [Representation.asGroupHom_apply, Units.val_one]
      using MonoidHom.mem_ker.mp (hker hg)⟩

theorem descendedAction_apply {H : Type*} [Group H] (β : G →* H)
    (hβ : Function.Surjective β) (ρ : Representation k G V)
    (hker : β.ker ≤ ρ.ker) (g : G) :
    descendedAction β hβ ρ hker (β g) = ρ.asGroupHom g := by
  simp only [descendedAction, MonoidHom.liftOfRightInverse_comp_apply]

theorem kernel_eq_of_descendedAction_injective {H : Type*} [Group H] (β : G →* H)
    (hβ : Function.Surjective β) (ρ : Representation k G V)
    (hker : β.ker ≤ ρ.ker)
    (hinj : Function.Injective (descendedAction β hβ ρ hker)) : ρ.ker = β.ker := by
  apply le_antisymm _ hker
  intro g hg
  apply hinj
  rw [map_one, descendedAction_apply]
  apply Units.ext
  simpa only [Representation.asGroupHom_apply, Units.val_one]
    using MonoidHom.mem_ker.mp hg

theorem neg_one_end_ne_one [Finite k] [Nontrivial V] (hkodd : Odd (Nat.card k)) :
    (-1 : Module.End k V) ≠ 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  intro heq
  have hvneg : -v = v := by
    simpa only [LinearMap.neg_apply, Module.End.one_apply] using
      congrArg (fun A : Module.End k V => A v) heq
  have hz : (2 : k) • v = 0 := by
    rw [two_smul]
    calc
      v + v = -v + v := congrArg (fun w => w + v) hvneg.symm
      _ = 0 := neg_add_cancel v
  exact (smul_eq_zero.mp hz).elim
    (OddFieldSL2.two_ne_zero_of_odd_card k hkodd) hv

theorem central_minus_on_subrepresentation (ρ : Representation k G V) (t : G)
    (ht : ρ t = -1) (U : Subrepresentation ρ) : U.toRepresentation t = -1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change ρ t v.val = -v.val
  rw [ht]
  rfl

theorem central_minus_on_surjective_intertwiner
    {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W) (t : G)
    (ht : ρ t = -1) (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    σ t = -1 := by
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := hf w
  rw [← f.isIntertwining, ht]
  simp

theorem irreducible_negative_central_p_cover_bound
    {F : Type*} [Field F] [Finite F] [Finite k] [FiniteDimensional k V]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) (hk : Nat.card k = p)
    (β : G →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center G) (hpker : IsPGroup p β.ker)
    (t : G) (htβ : β t = OddFieldSL2.minusIdentity F)
    (ρ : Representation k G V) (hirr : Representation.IsIrreducible ρ)
    (hminus : ρ t = -1) :
    (β.ker ≤ ρ.ker) ∧
      ∃ (hker : β.ker ≤ ρ.ker),
        Function.Injective (descendedAction β hβ ρ hker) ∧
          2 * f ≤ Module.finrank k V ∧ ρ.ker = β.ker ∧
          (descendedAction β hβ ρ hker).comp β = ρ.asGroupHom := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype k := Fintype.ofFinite k
  let : CharP k p := charP_of_card_eq_prime (by simpa only [Nat.card_eq_fintype_card] using hk)
  let : Representation.IsIrreducible ρ := hirr
  let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra k G) ρ.asModule
  have hker := central_pGroup_le_kernel ρ hirr β.ker hcentral hpker
  let φ := descendedAction β hβ ρ hker
  have hφminus : φ (OddFieldSL2.minusIdentity F) ≠ 1 := by
    intro heq
    have heqt : φ (β t) = 1 := by rw [htβ]; exact heq
    rw [descendedAction_apply] at heqt
    have hval := congrArg Units.val heqt
    rw [Representation.asGroupHom_apply, hminus] at hval
    exact neg_one_end_ne_one (by rw [hk]; exact hpodd) hval
  have hbound := DefiningCharacteristicDimension.odd_defining_characteristic_SL2_action_minimum_dimension
    hp hpodd hf hF hq hk φ hφminus
  refine ⟨hker, hker, hbound.2.2.1, hbound.2.2.2.1, ?_, ?_⟩
  · exact kernel_eq_of_descendedAction_injective β hβ ρ hker hbound.2.2.1
  · apply MonoidHom.ext
    intro g
    exact descendedAction_apply β hβ ρ hker g

theorem central_action_of_negativeSpace_eq_top (ρ : Representation k G V) (t : G)
    (hspace : negativeSpace ρ t = ⊤) : ρ t = -1 := by
  ext v
  have hv : v ∈ negativeSpace ρ t := by rw [hspace]; trivial
  exact (mem_negativeSpace ρ t v).mp hv

theorem irreducible_negative_subquotient_central_p_cover_bound
    {F : Type*} [Field F] [Finite F] [Finite k] [FiniteDimensional k V]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) (hk : Nat.card k = p)
    (β : G →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center G) (hpker : IsPGroup p β.ker)
    (t : G) (ht : t ∈ Subgroup.center G)
    (htβ : β t = OddFieldSL2.minusIdentity F) (ρ : Representation k G V)
    (U : Subrepresentation (negativeRepresentation ρ t ht))
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k G W) (hirr : Representation.IsIrreducible σ)
    (π : U.toRepresentation.IntertwiningMap σ) (hπ : Function.Surjective π) :
    (β.ker ≤ σ.ker) ∧
      ∃ (hker : β.ker ≤ σ.ker),
        Function.Injective (descendedAction β hβ σ hker) ∧
          2 * f ≤ Module.finrank k W ∧ σ.ker = β.ker ∧
          (descendedAction β hβ σ hker).comp β = σ.asGroupHom := by
  let : FiniteDimensional k W := Module.Finite.of_surjective π.toLinearMap hπ
  have hUminus : U.toRepresentation t = -1 :=
    central_minus_on_subrepresentation (negativeRepresentation ρ t ht) t
      (negativeRepresentation_at_central ρ t ht) U
  have hσminus : σ t = -1 :=
    central_minus_on_surjective_intertwiner U.toRepresentation σ t hUminus π hπ
  exact irreducible_negative_central_p_cover_bound hp hpodd hf hF hq hk β hβ
    hcentral hpker t htβ σ hirr hσminus

theorem negativeSpace_central_p_cover_dimension_bound
    {F : Type*} [Field F] [Finite F] [Finite k] [FiniteDimensional k V]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) (hk : Nat.card k = p)
    (β : G →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center G) (hpker : IsPGroup p β.ker)
    (t : G) (ht : t ∈ Subgroup.center G) (htsquare : t ^ 2 = 1)
    (htβ : β t = OddFieldSL2.minusIdentity F)
    (ρ : Representation k G V) (hρ : ρ t ≠ 1) :
    2 * f ≤ Module.finrank k (negativeSpace ρ t) ∧
      2 * f ≤ Module.finrank k V := by
  let : Nontrivial (negativeSpace ρ t) :=
    Submodule.nontrivial_iff_ne_bot.mpr (negativeSpace_ne_bot ρ t htsquare hρ)
  obtain ⟨U, _, hirr⟩ := exists_irreducible_subrepresentation (negativeRepresentation ρ t ht)
  have hminus : U.toRepresentation t = -1 :=
    central_minus_on_subrepresentation (negativeRepresentation ρ t ht) t
      (negativeRepresentation_at_central ρ t ht) U
  obtain ⟨_, _, _, hdim, _, _⟩ :=
    irreducible_negative_central_p_cover_bound hp hpodd hf hF hq hk β hβ
      hcentral hpker t htβ U.toRepresentation hirr hminus
  have hneg : 2 * f ≤ Module.finrank k (negativeSpace ρ t) :=
    hdim.trans (Submodule.finrank_le U.toSubmodule)
  exact ⟨hneg, hneg.trans (Submodule.finrank_le (negativeSpace ρ t))⟩

theorem central_p_cover_irreducible_at_minimum_dimension
    {F : Type*} [Field F] [Finite F] [Finite k] [FiniteDimensional k V]
    [Nontrivial V] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) (hk : Nat.card k = p)
    (β : G →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center G) (hpker : IsPGroup p β.ker)
    (t : G) (htβ : β t = OddFieldSL2.minusIdentity F)
    (ρ : Representation k G V) (hminus : ρ t = -1)
    (hdim : Module.finrank k V = 2 * f) : Representation.IsIrreducible ρ := by
  let : Finite V := Module.finite_of_finite k
  let : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro heq
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule heq)
  obtain ⟨U, hU⟩ := IsAtomic.exists_atom (Subrepresentation ρ)
  have hirr := irreducible_of_isAtom_subrepresentation ρ U hU
  have hUminus := central_minus_on_subrepresentation ρ t hminus U
  obtain ⟨_, _, _, hUdim, _, _⟩ :=
    irreducible_negative_central_p_cover_bound hp hpodd hf hF hq hk β hβ
      hcentral hpker t htβ U.toRepresentation hirr hUminus
  have hdimU : Module.finrank k U.toSubmodule = Module.finrank k V := by
    have hle := Submodule.finrank_le U.toSubmodule
    omega
  have hUtop : U = ⊤ := Subrepresentation.toSubmodule_injective
    (Submodule.eq_top_of_finrank_eq hdimU)
  exact isSimpleOrder_iff_isAtom_top.mpr (hUtop ▸ hU)

@[expose] def AllNegativeIrreducibleSubquotientsBound
    {H : Type*} [Group H] (β : G →* H) (hβ : Function.Surjective β)
    (ρ : Representation k G V) (t : G) (ht : t ∈ Subgroup.center G) (n : ℕ) : Prop :=
  ∀ (U : Subrepresentation (negativeRepresentation ρ t ht))
    (W : Type w) [AddCommGroup W] [Module k W]
    (σ : Representation k G W), Representation.IsIrreducible σ →
      ∀ (π : U.toRepresentation.IntertwiningMap σ), Function.Surjective π →
        (β.ker ≤ σ.ker) ∧
          ∃ (hker : β.ker ≤ σ.ker),
            Function.Injective (descendedAction β hβ σ hker) ∧
              n ≤ Module.finrank k W ∧ σ.ker = β.ker ∧
              (descendedAction β hβ σ hker).comp β = σ.asGroupHom

theorem central_p_cover_full_negative_dimension_and_equality
    {F : Type*} [Field F] [Finite F] [Finite k] [FiniteDimensional k V]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) (hk : Nat.card k = p)
    (β : G →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center G) (hpker : IsPGroup p β.ker)
    (t : G) (ht : t ∈ Subgroup.center G) (htsquare : t ^ 2 = 1)
    (htβ : β t = OddFieldSL2.minusIdentity F)
    (ρ : Representation k G V) (hρ : ρ t ≠ 1) :
    2 * f ≤ Module.finrank k (negativeSpace ρ t) ∧
      2 * f ≤ Module.finrank k V ∧
      AllNegativeIrreducibleSubquotientsBound β hβ ρ t ht (2 * f) ∧
      (Module.finrank k V = 2 * f →
        negativeSpace ρ t = ⊤ ∧ Representation.IsIrreducible ρ ∧
          ρ.ker = β.ker ∧
          ∃ (hker : β.ker ≤ ρ.ker),
            Function.Injective (descendedAction β hβ ρ hker) ∧
              (descendedAction β hβ ρ hker).comp β = ρ.asGroupHom) := by
  obtain ⟨hneg, hwhole⟩ := negativeSpace_central_p_cover_dimension_bound hp hpodd hf hF hq hk
    β hβ hcentral hpker t ht htsquare htβ ρ hρ
  refine ⟨hneg, hwhole, ?_, ?_⟩
  · intro U W _ _ σ hirr π hπ
    exact irreducible_negative_subquotient_central_p_cover_bound hp hpodd hf hF hq hk
      β hβ hcentral hpker t ht htβ ρ U σ hirr π hπ
  · intro hdim
    have hnegdim : Module.finrank k (negativeSpace ρ t) = Module.finrank k V := by
      have hle := Submodule.finrank_le (negativeSpace ρ t)
      omega
    have hspace := Submodule.eq_top_of_finrank_eq hnegdim
    have hminus := central_action_of_negativeSpace_eq_top ρ t hspace
    let : Nontrivial V := (Module.finrank_pos_iff).mp (by omega : 0 < Module.finrank k V)
    have hirr := central_p_cover_irreducible_at_minimum_dimension hp hpodd hf hF hq hk
      β hβ hcentral hpker t htβ ρ hminus hdim
    obtain ⟨_, hker, hinj, _, hkerEq, hcomp⟩ :=
      irreducible_negative_central_p_cover_bound hp hpodd hf hF hq hk β hβ hcentral
        hpker t htβ ρ hirr hminus
    exact ⟨hspace, hirr, hkerEq, hker, hinj, hcomp⟩

@[expose] def quotientIntertwiner (ρ : Representation k G V) (N : Subrepresentation ρ) :
    ρ.IntertwiningMap N.quotient where
  toLinearMap := N.toSubmodule.mkQ
  isIntertwining' _ := rfl

theorem quotientIntertwiner_surjective (ρ : Representation k G V) (N : Subrepresentation ρ) :
    Function.Surjective (quotientIntertwiner ρ N) :=
  N.toSubmodule.mkQ_surjective

theorem negative_nested_quotient_factor_bound
    {H : Type*} [Group H] (β : G →* H) (hβ : Function.Surjective β)
    (ρ : Representation k G V) (t : G) (ht : t ∈ Subgroup.center G) (n : ℕ)
    (hbound : AllNegativeIrreducibleSubquotientsBound β hβ ρ t ht n)
    (U : Subrepresentation (negativeRepresentation ρ t ht))
    (N : Subrepresentation U.toRepresentation) (hirr : Representation.IsIrreducible N.quotient) :
    (β.ker ≤ N.quotient.ker) ∧
      ∃ (hker : β.ker ≤ N.quotient.ker),
        Function.Injective (descendedAction β hβ N.quotient hker) ∧
          n ≤ Module.finrank k (U.toSubmodule ⧸ N.toSubmodule) ∧
          N.quotient.ker = β.ker ∧
          (descendedAction β hβ N.quotient hker).comp β = N.quotient.asGroupHom :=
  hbound U (U.toSubmodule ⧸ N.toSubmodule) N.quotient hirr
    (quotientIntertwiner U.toRepresentation N)
    (quotientIntertwiner_surjective U.toRepresentation N)

theorem asGroupHom_coeHom_comp
    (ρ : G →* LinearMap.GeneralLinearGroup k V) :
    Representation.asGroupHom ((Units.coeHom (Module.End k V)).comp ρ) = ρ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  simp only [Representation.asGroupHom_apply, MonoidHom.comp_apply, Units.coeHom_apply]

theorem coeHom_comp_kernel
    (ρ : G →* LinearMap.GeneralLinearGroup k V) :
    ((Units.coeHom (Module.End k V)).comp ρ).ker = ρ.ker :=
  MonoidHom.ker_comp_of_injective ρ (Units.coeHom (Module.End k V)) Units.coeHom_injective

theorem coeHom_comp_ne_one
    (ρ : G →* LinearMap.GeneralLinearGroup k V) (t : G) (hρ : ρ t ≠ 1) :
    ((Units.coeHom (Module.End k V)).comp ρ) t ≠ 1 := by
  intro heq
  apply hρ
  apply Units.ext
  simpa only [MonoidHom.comp_apply, Units.coeHom_apply, Units.val_one] using heq

theorem central_p_cover_original_action_full_negative_dimension_and_equality
    {F : Type*} [Field F] [Finite F] [Finite k] [FiniteDimensional k V]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) (hk : Nat.card k = p)
    (β : G →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center G) (hpker : IsPGroup p β.ker)
    (t : G) (ht : t ∈ Subgroup.center G) (htsquare : t ^ 2 = 1)
    (htβ : β t = OddFieldSL2.minusIdentity F)
    (ρ : G →* LinearMap.GeneralLinearGroup k V) (hρ : ρ t ≠ 1) :
    let σ : Representation k G V := (Units.coeHom (Module.End k V)).comp ρ
    2 * f ≤ Module.finrank k (negativeSpace σ t) ∧
      2 * f ≤ Module.finrank k V ∧
      AllNegativeIrreducibleSubquotientsBound β hβ σ t ht (2 * f) ∧
      (Module.finrank k V = 2 * f →
        negativeSpace σ t = ⊤ ∧ Representation.IsIrreducible σ ∧
          ρ.ker = β.ker ∧
          ∃ (hker : β.ker ≤ σ.ker),
            Function.Injective (descendedAction β hβ σ hker) ∧
              (descendedAction β hβ σ hker).comp β = ρ) := by
  let σ : Representation k G V := (Units.coeHom (Module.End k V)).comp ρ
  obtain ⟨hneg, hwhole, hfactors, hequality⟩ :=
    central_p_cover_full_negative_dimension_and_equality hp hpodd hf hF hq hk
      β hβ hcentral hpker t ht htsquare htβ σ (coeHom_comp_ne_one ρ t hρ)
  refine ⟨hneg, hwhole, hfactors, ?_⟩
  intro hdim
  obtain ⟨hspace, hirr, hkernel, hker, hinj, hcomp⟩ := hequality hdim
  refine ⟨hspace, hirr, ?_, hker, hinj, ?_⟩
  · exact (coeHom_comp_kernel ρ).symm.trans hkernel
  · exact hcomp.trans (asGroupHom_coeHom_comp ρ)

theorem odd_central_SL2_cover_defining_characteristic_minimum_dimension
    [Finite G] [Group.IsPerfect G]
    {F : Type*} [Field F] [Finite F] [Finite k] [FiniteDimensional k V]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f) (hk : Nat.card k = p)
    (β : G →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center G) (hodd : Odd (Nat.card β.ker))
    (t : G) (ht : t ∈ Subgroup.center G) (htorder : orderOf t = 2)
    (htβ : β t = OddFieldSL2.minusIdentity F)
    (ρ : G →* LinearMap.GeneralLinearGroup k V) (hρ : ρ t ≠ 1) :
    let σ : Representation k G V := (Units.coeHom (Module.End k V)).comp ρ
    2 * f ≤ Module.finrank k (negativeSpace σ t) ∧
      2 * f ≤ Module.finrank k V ∧
      AllNegativeIrreducibleSubquotientsBound β hβ σ t ht (2 * f) ∧
      (Module.finrank k V = 2 * f →
        negativeSpace σ t = ⊤ ∧ Representation.IsIrreducible σ ∧
          ρ.ker = β.ker ∧
          ∃ (hker : β.ker ≤ σ.ker),
            Function.Injective (descendedAction β hβ σ hker) ∧
              (descendedAction β hβ σ hker).comp β = ρ) := by
  have hpker := OddCentralSL2Kernel.central_odd_SL2_cover_kernel_isPGroup F
    hp hpodd hf hF hq β hβ hcentral hodd t ht htorder htβ
  have htsquare : t ^ 2 = 1 := by
    rw [← htorder]
    exact pow_orderOf_eq_one t
  exact central_p_cover_original_action_full_negative_dimension_and_equality
    hp hpodd hf hF hq hk β hβ hcentral hpker t ht htsquare htβ ρ hρ

end

end CFSG.Semidihedral.OddCentralDimension
