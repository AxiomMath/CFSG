module

public import CFSG.FeitThompson.Representations.OddOrderNonrealCharacters
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
import CFSG.FeitThompson.Representations.PrimeOrderAutFixesOnePointPerOrbit
import CFSG.FeitThompson.Representations.BrauerPermutationLemma
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FreeCore

open CFSG.FeitThompson.NormalInduction (conjClassFun conjClassFun_apply)
open MulAction Pointwise

variable {M : Type*} [Group M]

structure IsInternalSemidirectProduct (X A B : Subgroup M) : Prop where
  sup_eq : A ⊔ B = X
  le_normalizer : X ≤ Subgroup.normalizer (A : Set M)
  disjoint : Disjoint A B

namespace IsInternalSemidirectProduct

variable {X A B : Subgroup M}

theorem left_le (h : IsInternalSemidirectProduct X A B) : A ≤ X := h.sup_eq ▸ le_sup_left

theorem right_le (h : IsInternalSemidirectProduct X A B) : B ≤ X := h.sup_eq ▸ le_sup_right

theorem right_le_normalizer (h : IsInternalSemidirectProduct X A B) :
    B ≤ Subgroup.normalizer (A : Set M) := le_trans h.right_le h.le_normalizer

theorem coe_eq_mul (h : IsInternalSemidirectProduct X A B) :
    (X : Set M) = (A : Set M) * (B : Set M) := by
  rw [← h.sup_eq, Subgroup.coe_mul_of_right_le_normalizer_left A B h.right_le_normalizer]

theorem exists_mul (h : IsInternalSemidirectProduct X A B) {x : M} (hx : x ∈ X) :
    ∃ a ∈ A, ∃ y ∈ B, x = a * y := by
  rw [← SetLike.mem_coe, h.coe_eq_mul] at hx
  obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.1 hx
  exact ⟨a, ha, y, hy, rfl⟩

theorem inf_eq_bot (h : IsInternalSemidirectProduct X A B) : A ⊓ B = ⊥ :=
  disjoint_iff.1 h.disjoint

theorem normal_subgroupOf (h : IsInternalSemidirectProduct X A B) : (A.subgroupOf X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hg := Subgroup.mem_normalizer_iff.1 (h.le_normalizer g.2) (n : M)
  simpa [Subgroup.mem_subgroupOf] using hg.1 hn

theorem normal_of_top (h : IsInternalSemidirectProduct (⊤ : Subgroup M) A B) : A.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  exact top_le_iff.1 h.le_normalizer

theorem natCard_eq_mul [Finite M] (h : IsInternalSemidirectProduct X A B) :
    Nat.card ↥X = Nat.card ↥A * Nat.card ↥B := by
  have hcard := natCard_mul_mul_natCard_inf A B
  rw [h.inf_eq_bot, ← h.coe_eq_mul] at hcard
  simpa using hcard

end IsInternalSemidirectProduct

theorem mem_normalizer_iff_map (A : Subgroup M) (z : M) :
    z ∈ Subgroup.normalizer (A : Set M) ↔ A.map (MulAut.conj z).toMonoidHom = A := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ (h y).1 hy, fun hx => ⟨z⁻¹ * x * z, ?_, by group⟩⟩
    exact (h (z⁻¹ * x * z)).2 (by simpa [mul_assoc] using hx)
  · intro h x
    refine ⟨fun hx => h ▸ ⟨x, hx, rfl⟩, fun hx => ?_⟩
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have hxy : y = x := by
      have h2 : z⁻¹ * (z * y * z⁻¹) * z = z⁻¹ * (z * x * z⁻¹) * z := by rw [hyx]
      simpa [mul_assoc] using h2
    exact hxy ▸ hy

theorem mem_normalizer_sup {A B : Subgroup M} {z : M}
    (hA : z ∈ Subgroup.normalizer (A : Set M)) (hB : z ∈ Subgroup.normalizer (B : Set M)) :
    z ∈ Subgroup.normalizer ((A ⊔ B : Subgroup M) : Set M) := by
  rw [mem_normalizer_iff_map] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem normal_sup_of_isInternalSemidirectProduct {H U Q : Subgroup M}
    (hUQ : IsInternalSemidirectProduct (U ⊔ Q) U Q)
    (hM : IsInternalSemidirectProduct (⊤ : Subgroup M) H (U ⊔ Q)) : (H ⊔ U).Normal := by
  have hHnormal : H.Normal := hM.normal_of_top
  rw [← Subgroup.normalizer_eq_top_iff]
  refine top_le_iff.1 fun g _ => ?_
  obtain ⟨h, hh, y, hy, rfl⟩ := hM.exists_mul (Subgroup.mem_top g)
  refine mul_mem ?_ (mem_normalizer_sup (hM.le_normalizer trivial) (hUQ.le_normalizer hy))
  exact Subgroup.le_normalizer (le_sup_left (a := H) (b := U) hh)

section Action

variable {H : Subgroup M} [H.Normal]

theorem conjClassFun_one_fun (t : M) : conjClassFun H t (1 : ↥H → ℂ) = 1 := by
  funext n
  rw [conjClassFun_apply]
  rfl

theorem conjClassFun_ne_one (t : M) {θ : ↥H → ℂ} (hθ : θ ≠ 1) : conjClassFun H t θ ≠ 1 := by
  intro h
  refine hθ ?_
  have h' := congrArg (conjClassFun H t⁻¹) h
  rwa [← conjClassFun_mul, inv_mul_cancel, conjClassFun_one, conjClassFun_one_fun] at h'

instance instMulActionNonprincipalIrr : MulAction M ↥(nonprincipalIrr ↥H) where
  smul t θ := ⟨conjClassFun H t (θ : ↥H → ℂ),
    mem_nonprincipalIrr.2 ⟨conjClassFun_mem_Irr H t (mem_nonprincipalIrr.1 θ.2).1,
      conjClassFun_ne_one t (mem_nonprincipalIrr.1 θ.2).2⟩⟩
  one_smul _ := Subtype.ext (conjClassFun_one H _)
  mul_smul s t _ := Subtype.ext (conjClassFun_mul H s t _)

@[simp] theorem coe_smul_nonprincipalIrr (t : M) (θ : ↥(nonprincipalIrr ↥H)) :
    ((t • θ : ↥(nonprincipalIrr ↥H)) : ↥H → ℂ) = conjClassFun H t (θ : ↥H → ℂ) := (rfl)

theorem smul_self_eq {h : M} (hh : h ∈ H) (θ : ↥(nonprincipalIrr ↥H)) : h • θ = θ :=
  Subtype.ext (mem_inertiaGroup.1
    (le_inertiaGroup H (Irr_subset_classFun (mem_nonprincipalIrr.1 θ.2).1) hh))

end Action

section OrbitAux

variable {X : Type*} [MulAction M X] {U : Subgroup M}

theorem mem_orbit_subgroup_iff {y θ : X} : y ∈ orbit ↥U θ ↔ ∃ u ∈ U, u • θ = y := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, u.2, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩

theorem pow_smul_mem_orbit {s : M} (hs : s ∈ Subgroup.normalizer (U : Set M)) {θ : X}
    (h : s • θ ∈ orbit ↥U θ) (m : ℕ) : s ^ m • θ ∈ orbit ↥U θ := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨u, hu, hue⟩ := mem_orbit_subgroup_iff.1 ih
    obtain ⟨v, hv, hve⟩ := mem_orbit_subgroup_iff.1 h
    refine mem_orbit_subgroup_iff.2 ⟨s * u * s⁻¹ * v,
      mul_mem ((Subgroup.mem_normalizer_iff.1 hs u).1 hu) hv, ?_⟩
    calc (s * u * s⁻¹ * v) • θ = (s * u * s⁻¹) • (v • θ) := by rw [mul_smul]
      _ = (s * u * s⁻¹) • (s • θ) := by rw [hve]
      _ = (s * u) • θ := by rw [← mul_smul]; congr 1; group
      _ = s • (u • θ) := by rw [mul_smul]
      _ = s • (s ^ m • θ) := by rw [hue]
      _ = s ^ (m + 1) • θ := by rw [← mul_smul, ← pow_succ']

end OrbitAux

section Abelian

variable {A : Type*} [Group A] [IsMulCommutative A]

theorem isConj_iff_eq_of_isMulCommutative {a c : A} : IsConj a c ↔ a = c := by
  refine ⟨fun h => ?_, fun h => h ▸ IsConj.refl a⟩
  obtain ⟨d, rfl⟩ := isConj_iff.1 h
  rw [setLike_mul_comm (s := (⊤ : Subgroup A)) (a := d) (b := a) (by trivial) (by trivial)]
  group

theorem carrier_mk_eq_singleton (a : A) : (ConjClasses.mk a).carrier = {a} := by
  ext x
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
    isConj_iff_eq_of_isMulCommutative]
  simp [eq_comm]

theorem card_fixed_conjClasses_eq (α : MulAut A) :
    Nat.card {K : ConjClasses A // (α : A → A) '' K.carrier = K.carrier}
      = Nat.card {a : A // α a = a} := by
  refine (Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.ofBijective (ConjClasses.mk : A → ConjClasses A)
      ⟨fun a c h => isConj_iff_eq_of_isMulCommutative.1 (ConjClasses.mk_eq_mk_iff_isConj.1 h),
        ConjClasses.mk_surjective⟩)
    (p := fun a : A => α a = a)
    (q := fun K : ConjClasses A => (α : A → A) '' K.carrier = K.carrier) fun a => ?_)).symm
  change α a = a ↔ (α : A → A) '' (ConjClasses.mk a).carrier = (ConjClasses.mk a).carrier
  rw [carrier_mk_eq_singleton, Set.image_singleton, Set.singleton_eq_singleton_iff]

end Abelian

section Brauer

variable {H : Subgroup M} [H.Normal]

theorem conjNormal_eq_self_iff {t : M} {a : ↥H} :
    MulAut.conjNormal t⁻¹ a = a ↔ (a : M) ∈ Subgroup.centralizer {t} := by
  rw [Subtype.ext_iff, MulAut.conjNormal_apply, inv_inv, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc t * (a : M) = t * (t⁻¹ * (a : M) * t) := by rw [h]
      _ = (a : M) * t := by group
  · intro h
    have ht := h t rfl
    calc t⁻¹ * (a : M) * t = t⁻¹ * ((a : M) * t) := by group
      _ = t⁻¹ * (t * (a : M)) := by rw [ht]
      _ = (a : M) := by group

theorem card_fixed_conjNormal (t : M) :
    Nat.card {a : ↥H // MulAut.conjNormal t⁻¹ a = a}
      = Nat.card ↥(H ⊓ Subgroup.centralizer {t}) :=
  Nat.card_congr
    { toFun := fun a => ⟨(a.1 : M), Subgroup.mem_inf.2 ⟨a.1.2, conjNormal_eq_self_iff.1 a.2⟩⟩
      invFun := fun x => ⟨⟨(x : M), (Subgroup.mem_inf.1 x.2).1⟩,
        conjNormal_eq_self_iff.2 (Subgroup.mem_inf.1 x.2).2⟩
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl }

theorem card_fixed_Irr_eq_card_centralizer [Finite M] [IsMulCommutative ↥H] (t : M) :
    Nat.card {χ : ↥(Irr ↥H) // conjClassFun H t (χ : ↥H → ℂ) = (χ : ↥H → ℂ)}
      = Nat.card ↥(H ⊓ Subgroup.centralizer {t}) := by
  have h1 : Nat.card {χ : ↥(Irr ↥H) // conjClassFun H t (χ : ↥H → ℂ) = (χ : ↥H → ℂ)}
      = Nat.card {χ : ↥(Irr ↥H) // ∀ h : ↥H,
        (χ : ↥H → ℂ) (MulAut.conjNormal t⁻¹ h) = (χ : ↥H → ℂ) h} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => by
      rw [funext_iff]
      exact forall_congr' fun _ => by rw [conjClassFun_apply])
  rw [h1, card_fixed_Irr_eq_card_fixed_conjClasses (H := ↥H) (MulAut.conjNormal t⁻¹),
    card_fixed_conjClasses_eq, card_fixed_conjNormal]

end Brauer

theorem mem_Irr_indClassFun_iff [Fintype M] (N : Subgroup M) [N.Normal] {θ : ↥N → ℂ}
    (hθ : θ ∈ Irr ↥N) : indClassFun N θ ∈ Irr M ↔ inertiaGroup N θ = N := by
  constructor
  · intro h
    refine le_antisymm ?_ (le_inertiaGroup N (Irr_subset_classFun hθ))
    have h1 : ((N.relIndex (inertiaGroup N θ) : ℕ) : ℂ) = 1 := by
      rw [← cfInner_self_indClassFun N hθ, cfInner_self_of_mem_Irr h]
    exact Subgroup.relIndex_eq_one.1 (by exact_mod_cast h1)
  · intro h
    obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_of_mem_indFam N
      (indClassFun_mem_indFam N hθ)
    have h2 : Representation.character W.ρ = indClassFun N θ := hW
    have h3 : Representation.IsIrreducible W.ρ := by
      rw [isIrreducible_iff_cfInner_self_eq_one, h2, cfInner_self_indClassFun N hθ, h,
        Subgroup.relIndex_self]
      norm_num
    simpa [h2] using character_mem_Irr_of_isIrreducible W.ρ h3

theorem natCard_subtype_ne {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  have : Fintype α := Fintype.ofFinite α
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (p := fun x => x = a)]

theorem natCard_nonprincipalIrr {A : Type*} [Group A] [IsMulCommutative A] [Finite A] :
    Nat.card ↥(nonprincipalIrr A) = Nat.card A - 1 := by
  let _ : CommGroup A := { mul_comm := fun a c => IsMulCommutative.is_comm.comm a c }
  have h1 : nonprincipalIrr A = Irr A \ {1} := by ext χ; simp [mem_nonprincipalIrr]
  rw [Nat.card_coe_set_eq, h1, Set.ncard_sdiff_singleton_of_mem one_mem_Irr,
    ← Nat.card_coe_set_eq, card_Irr_eq_card]

section Perm

variable {H U : Subgroup M} [H.Normal]

noncomputable def conjPerm (b : M) : Equiv.Perm ↥(nonprincipalIrr ↥H) := MulAction.toPerm b

@[simp] theorem conjPerm_apply (b : M) (θ : ↥(nonprincipalIrr ↥H)) :
    conjPerm (H := H) b θ = b • θ := (rfl)

theorem conjPerm_pow (b : M) (n : ℕ) (θ : ↥(nonprincipalIrr ↥H)) :
    ((conjPerm (H := H) b) ^ n) θ = b ^ n • θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, conjPerm_apply, ih, smul_smul, ← pow_succ']

theorem conjPerm_pow_eq_one {b : M} {q : ℕ} (hb : b ^ q = 1) : (conjPerm (H := H) b) ^ q = 1 :=
  Equiv.ext fun θ => by rw [conjPerm_pow, hb, one_smul, Equiv.Perm.one_apply]

noncomputable def conjAut (U : Subgroup M) {b : M} (hb : b ∈ Subgroup.normalizer (U : Set M)) :
    MulAut ↥U := U.normalizerMonoidHom ⟨b, hb⟩

@[simp] theorem coe_conjAut_apply {b : M} (hb : b ∈ Subgroup.normalizer (U : Set M)) (u : ↥U) :
    ((conjAut U hb u : ↥U) : M) = b * (u : M) * b⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe U ⟨b, hb⟩ u

theorem conjPerm_smul {b : M} (hb : b ∈ Subgroup.normalizer (U : Set M)) (u : ↥U)
    (θ : ↥(nonprincipalIrr ↥H)) :
    conjPerm (H := H) b (u • θ) = conjAut U hb u • conjPerm (H := H) b θ := by
  rw [conjPerm_apply, conjPerm_apply]
  change (b : M) • ((u : M) • θ) = ((conjAut U hb u : ↥U) : M) • ((b : M) • θ)
  rw [smul_smul, smul_smul, coe_conjAut_apply]
  congr 1
  group

theorem conjAut_eq_self_imp_eq_one {b : M} (hb : b ∈ Subgroup.normalizer (U : Set M))
    (hCU : U ⊓ Subgroup.centralizer {b} = ⊥) (u : ↥U) (h : conjAut U hb u = u) : u = 1 := by
  have h' : b * (u : M) * b⁻¹ = (u : M) := by rw [← coe_conjAut_apply hb u, h]
  have hmem : (u : M) ∈ U ⊓ Subgroup.centralizer {b} := by
    refine Subgroup.mem_inf.2 ⟨u.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc b * (u : M) = (b * (u : M) * b⁻¹) * b := by group
      _ = (u : M) * b := by rw [h']
  rw [hCU] at hmem
  exact Subtype.ext (Subgroup.mem_bot.1 hmem)

end Perm

section Free

variable {H U : Subgroup M} [H.Normal] [IsMulCommutative ↥H] [Finite M]

theorem eq_one_of_conjClassFun_eq (t : M) (hcent : H ⊓ Subgroup.centralizer {t} = ⊥)
    {χ : ↥H → ℂ} (hχ : χ ∈ Irr ↥H) (h : conjClassFun H t χ = χ) : χ = 1 := by
  have hcount := card_fixed_Irr_eq_card_centralizer (H := H) t
  rw [hcent] at hcount
  have h1 : Nat.card {ψ : ↥(Irr ↥H) // conjClassFun H t (ψ : ↥H → ℂ) = (ψ : ↥H → ℂ)} = 1 := by
    rw [hcount]
    simp
  rw [Nat.card_eq_one_iff_unique] at h1
  have e1 : (⟨⟨χ, hχ⟩, h⟩ : {ψ : ↥(Irr ↥H) // conjClassFun H t (ψ : ↥H → ℂ) = (ψ : ↥H → ℂ)})
      = ⟨⟨1, one_mem_Irr⟩, conjClassFun_one_fun t⟩ := h1.1.allEq _ _
  exact congrArg (fun x => (x.1.1 : ↥H → ℂ)) e1

theorem smul_eq_self_imp_eq_one (hUH : ∀ u ∈ U, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (u : ↥U) (θ : ↥(nonprincipalIrr ↥H)) (h : u • θ = θ) : u = 1 := by
  by_contra hu
  have hu' : (u : M) ≠ 1 := fun hc => hu (Subtype.ext hc)
  refine (mem_nonprincipalIrr.1 θ.2).2 ?_
  refine eq_one_of_conjClassFun_eq (u : M) (hUH (u : M) u.2 hu')
    (mem_nonprincipalIrr.1 θ.2).1 ?_
  have h' : conjClassFun H ((u : M)) (θ : ↥H → ℂ) = (θ : ↥H → ℂ) := by
    rw [← coe_smul_nonprincipalIrr (u : M) θ]
    exact congrArg (fun x : ↥(nonprincipalIrr ↥H) => (x : ↥H → ℂ)) h
  exact h'

end Free

section Stable

variable {H U Q : Subgroup M} [H.Normal] [Fintype M]

theorem conjPerm_mem_orbit {b : M} {q : ℕ} (hq : q.Prime) (hord : orderOf b = q)
    (hbU : b ∈ Subgroup.normalizer (U : Set M))
    (hfree : ∀ (u : ↥U) (θ : ↥(nonprincipalIrr ↥H)), u • θ = θ → u = 1)
    (hUQ : IsInternalSemidirectProduct (U ⊔ Q) U Q) (hQ : Q = Subgroup.zpowers b)
    (hM : IsInternalSemidirectProduct (⊤ : Subgroup M) H (U ⊔ Q))
    (hno : ∀ θ : ↥(nonprincipalIrr ↥H), indClassFun H (θ : ↥H → ℂ) ∉ Irr M)
    (θ : ↥(nonprincipalIrr ↥H)) : conjPerm (H := H) b θ ∈ orbit ↥U θ := by
  rw [conjPerm_apply]
  have hθ := (mem_nonprincipalIrr.1 θ.2).1
  have hne : inertiaGroup H (θ : ↥H → ℂ) ≠ H := fun hc =>
    hno θ ((mem_Irr_indClassFun_iff H hθ).2 hc)
  have hle : H ≤ inertiaGroup H (θ : ↥H → ℂ) := le_inertiaGroup H (Irr_subset_classFun hθ)
  obtain ⟨t, ht, htH⟩ : ∃ t ∈ inertiaGroup H (θ : ↥H → ℂ), t ∉ H := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    exact hne (le_antisymm (fun x hx => hc x hx) hle)
  have htfix : t • θ = θ := Subtype.ext (mem_inertiaGroup.1 ht)
  obtain ⟨h, hh, u, hu, i, rfl⟩ : ∃ h ∈ H, ∃ u ∈ U, ∃ i : ℕ, t = h * u * b ^ i := by
    obtain ⟨h, hh, y, hy, rfl⟩ := hM.exists_mul (Subgroup.mem_top t)
    obtain ⟨u, hu, z, hz, rfl⟩ := hUQ.exists_mul hy
    rw [hQ] at hz
    obtain ⟨i, hi⟩ := (mem_powers_iff_mem_zpowers (x := b) (y := z)).2 hz
    exact ⟨h, hh, u, hu, i, by rw [← hi, mul_assoc]⟩
  have hub : u • (b ^ i • θ) = θ := by
    have h2 := htfix
    rw [show h * u * b ^ i = h * (u * b ^ i) from by group, mul_smul, mul_smul,
      show h • (u • (b ^ i • θ)) = u • (b ^ i • θ) from smul_self_eq hh _] at h2
    exact h2
  have hbi : b ^ i ≠ 1 := by
    intro hc
    rw [hc, one_smul] at hub
    have hu1 : u = 1 := congrArg Subtype.val (hfree ⟨u, hu⟩ θ hub)
    exact htH (by rw [hu1, hc]; simpa using hh)
  have hbiorb : b ^ i • θ ∈ orbit ↥U θ :=
    mem_orbit_subgroup_iff.2 ⟨u⁻¹, inv_mem hu, by
      calc u⁻¹ • θ = u⁻¹ • (u • (b ^ i • θ)) := by rw [hub]
        _ = b ^ i • θ := inv_smul_smul u _⟩
  have hgen : Subgroup.zpowers (b ^ i) = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.2 (Subgroup.mem_zpowers_iff.2 ⟨i, by simp⟩)) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hord]
    have hdvd : orderOf (b ^ i) ∣ q := hord ▸ orderOf_pow_dvd i
    rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hbi
    · omega
  obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers (x := b ^ i) (y := b)).2
    (hgen ▸ Subgroup.mem_zpowers b)
  have hm' : (b ^ i) ^ m = b := hm
  rw [← hm']
  exact pow_smul_mem_orbit (pow_mem hbU i) hbiorb m

end Stable

section FixedCount

variable {H : Subgroup M} [H.Normal]

theorem mem_fixedPoints_conjPerm_iff (b : M) (θ : ↥(nonprincipalIrr ↥H)) :
    θ ∈ Function.fixedPoints (conjPerm (H := H) b)
      ↔ conjClassFun H b (θ : ↥H → ℂ) = (θ : ↥H → ℂ) := by
  rw [Function.mem_fixedPoints_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← coe_smul_nonprincipalIrr b θ]
    exact congrArg (fun y : ↥(nonprincipalIrr ↥H) => (y : ↥H → ℂ)) (conjPerm_apply b θ ▸ h)
  · rw [conjPerm_apply]
    exact Subtype.ext (by rw [coe_smul_nonprincipalIrr, h])

theorem natCard_fixedPoints_conjPerm [IsMulCommutative ↥H] [Finite M] (b : M) :
    Nat.card (Function.fixedPoints (conjPerm (H := H) b))
      = Nat.card ↥(H ⊓ Subgroup.centralizer {b}) - 1 := by
  have e1 : Function.fixedPoints (conjPerm (H := H) b)
      ≃ {χ : {ψ : ↥(Irr ↥H) // conjClassFun H b (ψ : ↥H → ℂ) = (ψ : ↥H → ℂ)} //
          χ ≠ ⟨⟨1, one_mem_Irr⟩, conjClassFun_one_fun b⟩} := by
    refine Equiv.ofBijective
      (fun x => ⟨⟨⟨(x.1 : ↥H → ℂ), (mem_nonprincipalIrr.1 x.1.2).1⟩,
        (mem_fixedPoints_conjPerm_iff b x.1).1 x.2⟩, fun hc => ?_⟩) ⟨?_, ?_⟩
    · exact (mem_nonprincipalIrr.1 x.1.2).2 (congrArg (fun z => (z.1.1 : ↥H → ℂ)) hc)
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z => (z.1.1.1 : ↥H → ℂ)) hxy))
    · intro χ
      refine ⟨⟨⟨(χ.1.1 : ↥H → ℂ), mem_nonprincipalIrr.2 ⟨χ.1.1.2, fun hc => χ.2 ?_⟩⟩, ?_⟩, rfl⟩
      · exact Subtype.ext (Subtype.ext hc)
      · exact (mem_fixedPoints_conjPerm_iff b _).2 χ.1.2
  rw [Nat.card_congr e1, natCard_subtype_ne, card_fixed_Irr_eq_card_centralizer]

end FixedCount

theorem natCard_eq_of_no_induced_irr [Fintype M] {H U Q : Subgroup M} [H.Normal]
    [IsMulCommutative ↥H] {b : M} {p q : ℕ}
    (hp : 2 ≤ p) (hq : q.Prime) (hord : orderOf b = q) (hQ : Q = Subgroup.zpowers b)
    (hUQ : IsInternalSemidirectProduct (U ⊔ Q) U Q)
    (hM : IsInternalSemidirectProduct (⊤ : Subgroup M) H (U ⊔ Q))
    (hH : Nat.card ↥H = p ^ q) (hqU : ¬ q ∣ Nat.card ↥U)
    (hCU : U ⊓ Subgroup.centralizer {b} = ⊥)
    (hCH : Nat.card ↥(H ⊓ Subgroup.centralizer {b}) = p)
    (hUH : ∀ u ∈ U, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hno : ∀ θ : ↥(nonprincipalIrr ↥H), indClassFun H (θ : ↥H → ℂ) ∉ Irr M) :
    Nat.card ↥U = (p ^ q - 1) / (p - 1) := by
  have hbU : b ∈ Subgroup.normalizer (U : Set M) := by
    refine hUQ.le_normalizer (le_sup_right (a := U) (b := Q) ?_)
    rw [hQ]
    exact Subgroup.mem_zpowers b
  have hbq : b ^ q = 1 := by rw [← hord]; exact pow_orderOf_eq_one b
  have hfree := smul_eq_self_imp_eq_one (U := U) hUH
  have hcount := natCard_eq_natCard_mul_natCard_fixedPoints (D := ↥U)
    (Ω := ↥(nonprincipalIrr ↥H)) (b := conjAut U hbU) (β := conjPerm (H := H) b)
    hfree (conjAut_eq_self_imp_eq_one hbU hCU) (conjPerm_smul hbU)
    (conjPerm_mem_orbit hq hord hbU hfree hUQ hQ hM hno) hq hqU (conjPerm_pow_eq_one hbq)
  rw [natCard_nonprincipalIrr, hH, natCard_fixedPoints_conjPerm, hCH] at hcount
  rw [hcount, Nat.mul_div_cancel _ (by omega)]

end FreeCore

end CFSG.FeitThompson
