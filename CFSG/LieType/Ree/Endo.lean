module

public import CFSG.LieType.Ree.Faithful
public import CFSG.LieType.Ree.Catalog
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits

section Generators

variable {τ : Tag} {K : Type} [Field K]

theorem closure_xElement_yElement :
    Subgroup.closure {g : adjointGroup τ K | ∃ (i : Fin τ.rank) (c : K),
      g = xElement i c ∨ g = yElement i c} = ⊤ := by
  have hcl : Subgroup.closure (((↑) : adjointGroup τ K → ModGL τ K) ⁻¹'
      {g | ∃ (i : Fin τ.rank) (c : K), (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
        (g : Module.End K (RootModule τ K)) = yOp τ K i c}) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [eq_top_iff, ← hcl]
  refine Subgroup.closure_mono fun g ⟨i, c, h⟩ => ⟨i, c, ?_⟩
  rcases h with h | h
  · exact .inl (Subtype.ext (Units.ext h))
  · exact .inr (Subtype.ext (Units.ext h))

theorem adjointGroup_hom_ext {M : Type*} [Monoid M] {f g : adjointGroup τ K →* M}
    (hx : ∀ i c, f (xElement i c) = g (xElement i c))
    (hy : ∀ i c, f (yElement i c) = g (yElement i c)) : f = g :=
  MonoidHom.eq_of_eqOn_dense closure_xElement_yElement fun _ ⟨i, c, h⟩ => by
    rcases h with rfl | rfl
    · exact hx i c
    · exact hy i c

end Generators

section Entrywise

variable {τ : Tag} {K : Type} [Field K] (σ : K →+* K)

theorem mapRange_smul_ringHom (r : K) (x : RootModule τ K) :
    Finsupp.mapRange σ σ.map_zero (r • x) = σ r • Finsupp.mapRange σ σ.map_zero x := by
  ext a
  simp

theorem entrywise_xOp (i : Fin τ.rank) (c : K) :
    entrywise σ (xOp τ K i c) = xOp τ K i (σ c) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff, LinearMap.sum_apply,
    LinearMap.sum_apply, Finsupp.mapRange_finsetSum σ]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, mapRange_smul_ringHom, map_pow,
    mapRange_xCoeff_single]

theorem entrywise_yOp (i : Fin τ.rank) (c : K) :
    entrywise σ (yOp τ K i c) = yOp τ K i (σ c) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff, LinearMap.sum_apply,
    LinearMap.sum_apply, Finsupp.mapRange_finsetSum σ]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, mapRange_smul_ringHom, map_pow,
    mapRange_yCoeff_single]

variable (τ K) in
@[expose] def entrywiseGL : ModGL τ K →* ModGL τ K :=
  Units.map (entrywiseHom σ)

theorem entrywiseGL_xUnit (i : Fin τ.rank) (c : K) :
    entrywiseGL τ K σ (xUnit τ K i c) = xUnit τ K i (σ c) :=
  Units.ext (entrywise_xOp σ i c)

theorem entrywiseGL_yUnit (i : Fin τ.rank) (c : K) :
    entrywiseGL τ K σ (yUnit τ K i c) = yUnit τ K i (σ c) :=
  Units.ext (entrywise_yOp σ i c)

theorem entrywiseGL_mem {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) :
    entrywiseGL τ K σ g ∈ adjointGroup τ K := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, c, h | h⟩ := hg
    · rw [show g = xUnit τ K i c from Units.ext h, entrywiseGL_xUnit]
      exact xUnit_mem_adjointGroup i _
    · rw [show g = yUnit τ K i c from Units.ext h, entrywiseGL_yUnit]
      exact yUnit_mem_adjointGroup i _
  | one => rw [map_one]; exact one_mem _
  | mul g h _ _ ihg ihh => rw [map_mul]; exact mul_mem ihg ihh
  | inv g _ ihg => rw [map_inv]; exact inv_mem ihg

theorem entrywiseGL_injective : Function.Injective (entrywiseGL τ K σ) := by
  intro g g' h
  refine Units.ext (Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_)
  have h' := congrArg (fun u : ModGL τ K =>
    (u : Module.End K (RootModule τ K)) (Finsupp.single b 1)) h
  simp only [entrywiseGL, Units.coe_map, entrywiseHom, MonoidHom.coe_mk, OneHom.coe_mk,
    entrywise_single] at h'
  exact Finsupp.mapRange_injective σ σ.map_zero σ.injective h'

variable (τ K) in
@[expose] def frobeniusTwist : adjointGroup τ K →* adjointGroup τ K :=
  ((entrywiseGL τ K σ).comp (adjointGroup τ K).subtype).codRestrict (adjointGroup τ K)
    fun g => entrywiseGL_mem σ g.2

theorem coe_frobeniusTwist (g : adjointGroup τ K) :
    (frobeniusTwist τ K σ g : ModGL τ K) = entrywiseGL τ K σ g :=
  rfl

theorem frobeniusTwist_xElement (i : Fin τ.rank) (c : K) :
    frobeniusTwist τ K σ (xElement i c) = xElement i (σ c) :=
  Subtype.ext (entrywiseGL_xUnit σ i c)

theorem frobeniusTwist_yElement (i : Fin τ.rank) (c : K) :
    frobeniusTwist τ K σ (yElement i c) = yElement i (σ c) :=
  Subtype.ext (entrywiseGL_yUnit σ i c)

theorem frobeniusTwist_injective : Function.Injective (frobeniusTwist τ K σ) :=
  fun _ _ h => Subtype.ext (entrywiseGL_injective σ (congrArg Subtype.val h))

end Entrywise

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K]

instance fact_prime (t : ReeTag) : Fact t.prime.Prime :=
  ⟨by cases t <;> norm_num [prime]⟩

theorem exponent_mul_exponent_perm (t : ReeTag) (i : Fin t.tag.rank) :
    t.exponent i * t.exponent (t.perm i) = t.prime := by
  revert i
  cases t <;> decide

theorem exists_twist (hp : (t.prime : K) = 0) {g : ModGL t.tag K}
    (hg : g ∈ adjointGroup t.tag K) :
    ∃ g' ∈ adjointGroup t.tag K, (g' : Module.End K (RootModule t.tag K)) * t.lengthMap K =
      t.lengthMap K * (g : Module.End K (RootModule t.tag K)) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, c, h | h⟩ := hg
    · exact ⟨xUnit t.tag K (t.perm i) (c ^ t.exponent i), xUnit_mem_adjointGroup _ _, by
        rw [h, coe_xUnit, lengthMap_mul_xOp K hp]⟩
    · exact ⟨yUnit t.tag K (t.perm i) (c ^ t.exponent i), yUnit_mem_adjointGroup _ _, by
        rw [h, coe_yUnit, lengthMap_mul_yOp K hp]⟩
  | one => exact ⟨1, one_mem _, by simp only [Units.val_one, one_mul, mul_one]⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨g', hg', eg⟩ := ihg
    obtain ⟨h', hh', eh⟩ := ihh
    refine ⟨g' * h', mul_mem hg' hh', ?_⟩
    rw [Units.val_mul, Units.val_mul, mul_assoc, eh, ← mul_assoc, eg, mul_assoc]
  | inv g _ ihg =>
    obtain ⟨g', hg', eg⟩ := ihg
    refine ⟨g'⁻¹, inv_mem hg', ?_⟩
    calc ((g'⁻¹ : ModGL t.tag K) : Module.End K (RootModule t.tag K)) * t.lengthMap K
        = ((g'⁻¹ : ModGL t.tag K) : Module.End K (RootModule t.tag K)) * t.lengthMap K *
            ((g : Module.End K (RootModule t.tag K)) *
              ((g⁻¹ : ModGL t.tag K) : Module.End K (RootModule t.tag K))) := by
          rw [Units.mul_inv, mul_one]
      _ = ((g'⁻¹ : ModGL t.tag K) : Module.End K (RootModule t.tag K)) *
            (t.lengthMap K * (g : Module.End K (RootModule t.tag K))) *
              ((g⁻¹ : ModGL t.tag K) : Module.End K (RootModule t.tag K)) := by
          simp only [mul_assoc]
      _ = ((g'⁻¹ : ModGL t.tag K) : Module.End K (RootModule t.tag K)) *
            ((g' : Module.End K (RootModule t.tag K)) * t.lengthMap K) *
              ((g⁻¹ : ModGL t.tag K) : Module.End K (RootModule t.tag K)) := by
          rw [eg]
      _ = t.lengthMap K * ((g⁻¹ : ModGL t.tag K) : Module.End K (RootModule t.tag K)) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]

theorem twist_unique (hf : t.ShortFaithful K) {g₁ g₂ : ModGL t.tag K}
    (h₁ : g₁ ∈ adjointGroup t.tag K) (h₂ : g₂ ∈ adjointGroup t.tag K)
    (h : (g₁ : Module.End K (RootModule t.tag K)) * t.lengthMap K =
      (g₂ : Module.End K (RootModule t.tag K)) * t.lengthMap K) : g₁ = g₂ :=
  hf.eq_of_eqOn h₁ h₂ fun v hv => by
    obtain ⟨u, rfl⟩ : v ∈ LinearMap.range (t.lengthMap K) := by rwa [range_lengthMap K]
    rw [← Module.End.mul_apply, h, Module.End.mul_apply]

variable (t K) in
@[expose] def twist (hp : (t.prime : K) = 0) (g : adjointGroup t.tag K) : adjointGroup t.tag K :=
  ⟨(exists_twist hp g.2).choose, (exists_twist hp g.2).choose_spec.1⟩

theorem twist_spec (hp : (t.prime : K) = 0) (g : adjointGroup t.tag K) :
    glRep _ (t.twist K hp g) * t.lengthMap K = t.lengthMap K * glRep _ g :=
  (exists_twist hp g.2).choose_spec.2

theorem twist_eq_of (hp : (t.prime : K) = 0) (hf : t.ShortFaithful K)
    {g g' : adjointGroup t.tag K} (h : glRep _ g' * t.lengthMap K = t.lengthMap K * glRep _ g) :
    t.twist K hp g = g' :=
  Subtype.ext (twist_unique hf (t.twist K hp g).2 g'.2 ((twist_spec hp g).trans h.symm))

variable (t K) in
@[expose] def exceptionalEndo (hp : (t.prime : K) = 0) (hf : t.ShortFaithful K) :
    adjointGroup t.tag K →* adjointGroup t.tag K where
  toFun := t.twist K hp
  map_one' := twist_eq_of hp hf (by simp only [map_one, one_mul, mul_one])
  map_mul' g h := twist_eq_of hp hf (by
    rw [map_mul, map_mul, mul_assoc, twist_spec, ← mul_assoc, twist_spec, mul_assoc])

variable (hp : (t.prime : K) = 0) (hf : t.ShortFaithful K)

theorem exceptionalEndo_spec (g : adjointGroup t.tag K) :
    glRep _ (t.exceptionalEndo K hp hf g) * t.lengthMap K = t.lengthMap K * glRep _ g :=
  twist_spec hp g

theorem exceptionalEndo_eq_iff {g g' : adjointGroup t.tag K} :
    t.exceptionalEndo K hp hf g = g' ↔
      glRep _ g' * t.lengthMap K = t.lengthMap K * glRep _ g :=
  ⟨fun h => h ▸ exceptionalEndo_spec hp hf g, twist_eq_of hp hf⟩

theorem exceptionalEndo_xElement (i : Fin t.tag.rank) (c : K) :
    t.exceptionalEndo K hp hf (xElement i c) = xElement (t.perm i) (c ^ t.exponent i) :=
  twist_eq_of hp hf (lengthMap_mul_xOp K hp i c).symm

theorem exceptionalEndo_yElement (i : Fin t.tag.rank) (c : K) :
    t.exceptionalEndo K hp hf (yElement i c) = yElement (t.perm i) (c ^ t.exponent i) :=
  twist_eq_of hp hf (lengthMap_mul_yOp K hp i c).symm

theorem exceptionalEndo_comp_self [CharP K t.prime] :
    (t.exceptionalEndo K hp hf).comp (t.exceptionalEndo K hp hf) =
      frobeniusTwist t.tag K (frobenius K t.prime) := by
  refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
  · rw [MonoidHom.comp_apply, exceptionalEndo_xElement, exceptionalEndo_xElement, perm_perm,
      ← pow_mul, exponent_mul_exponent_perm, frobeniusTwist_xElement, frobenius_def]
  · rw [MonoidHom.comp_apply, exceptionalEndo_yElement, exceptionalEndo_yElement, perm_perm,
      ← pow_mul, exponent_mul_exponent_perm, frobeniusTwist_yElement, frobenius_def]

theorem exceptionalEndo_injective [CharP K t.prime] :
    Function.Injective (t.exceptionalEndo K hp hf) := by
  refine Function.Injective.of_comp (f := t.exceptionalEndo K hp hf) ?_
  rw [← MonoidHom.coe_comp, exceptionalEndo_comp_self]
  exact frobeniusTwist_injective _

variable (t) in
@[expose] def relationExponent (a : ℕ) (i : Fin t.tag.rank) : ℕ :=
  if i ∈ t.longSet then t.prime ^ a else t.prime ^ (a + 1)

variable (t K) in
@[expose] def reeEndo [CharP K t.prime] (hf : t.ShortFaithful K) (a : ℕ) :
    adjointGroup t.tag K →* adjointGroup t.tag K :=
  (t.exceptionalEndo K (CharP.cast_eq_zero K t.prime) hf).comp
    (frobeniusTwist t.tag K (iterateFrobenius K t.prime a))

variable [CharP K t.prime] (a : ℕ)

theorem reeEndo_xElement (i : Fin t.tag.rank) (c : K) :
    t.reeEndo K hf a (xElement i c) = xElement (t.perm i) (c ^ t.relationExponent a i) := by
  rw [reeEndo, MonoidHom.comp_apply, frobeniusTwist_xElement, exceptionalEndo_xElement,
    iterateFrobenius_def, ← pow_mul, relationExponent, relationExponent_eq]

theorem reeEndo_yElement (i : Fin t.tag.rank) (c : K) :
    t.reeEndo K hf a (yElement i c) = yElement (t.perm i) (c ^ t.relationExponent a i) := by
  rw [reeEndo, MonoidHom.comp_apply, frobeniusTwist_yElement, exceptionalEndo_yElement,
    iterateFrobenius_def, ← pow_mul, relationExponent, relationExponent_eq]

theorem reeEndo_injective : Function.Injective (t.reeEndo K hf a) :=
  (exceptionalEndo_injective (CharP.cast_eq_zero K t.prime) hf).comp
    (frobeniusTwist_injective _)

theorem reeRelationGroup_eq_graph :
    reeRelationGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
        else t.prime ^ (a + 1)) =
      ((adjointGroup t.tag K).subtype.prod
        ((adjointGroup t.tag K).subtype.comp (t.reeEndo K hf a))).range := by
  apply le_antisymm
  · rw [reeRelationGroup, Subgroup.closure_le]
    rintro ⟨g₁, g₂⟩ ⟨i, c, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
    · refine ⟨xElement i c, Prod.ext (Units.ext h₁.symm) ?_⟩
      change ((t.reeEndo K hf a (xElement i c) : adjointGroup t.tag K) : ModGL t.tag K) = g₂
      rw [reeEndo_xElement]
      exact Units.ext h₂.symm
    · refine ⟨yElement i c, Prod.ext (Units.ext h₁.symm) ?_⟩
      change ((t.reeEndo K hf a (yElement i c) : adjointGroup t.tag K) : ModGL t.tag K) = g₂
      rw [reeEndo_yElement]
      exact Units.ext h₂.symm
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    change (g, ((t.reeEndo K hf a ⟨g, hg⟩ : adjointGroup t.tag K) : ModGL t.tag K)) ∈ _
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, c, h | h⟩ := hg
      · have hx : (⟨g, Subgroup.subset_closure ⟨i, c, .inl h⟩⟩ : adjointGroup t.tag K) =
            xElement i c := Subtype.ext (Units.ext h)
        rw [hx, reeEndo_xElement]
        exact Subgroup.subset_closure ⟨i, c, .inl ⟨h, rfl⟩⟩
      · have hy : (⟨g, Subgroup.subset_closure ⟨i, c, .inr h⟩⟩ : adjointGroup t.tag K) =
            yElement i c := Subtype.ext (Units.ext h)
        rw [hy, reeEndo_yElement]
        exact Subgroup.subset_closure ⟨i, c, .inr ⟨h, rfl⟩⟩
    | one =>
      have h1 : (⟨1, one_mem _⟩ : adjointGroup t.tag K) = 1 := rfl
      rw [h1, map_one]
      exact one_mem _
    | mul x y hx hy ihx ihy =>
      have hxy : (⟨x * y, mul_mem hx hy⟩ : adjointGroup t.tag K) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [hxy, map_mul]
      exact mul_mem ihx ihy
    | inv x hx ihx =>
      have hxi : (⟨x⁻¹, inv_mem hx⟩ : adjointGroup t.tag K) = (⟨x, hx⟩)⁻¹ := rfl
      rw [hxi, map_inv]
      exact inv_mem ihx

theorem reeRelationGroup_inf_prod :
    reeRelationGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
        else t.prime ^ (a + 1)) ⊓ (adjointGroup t.tag K).prod (adjointGroup t.tag K) =
      ((adjointGroup t.tag K).subtype.prod
        ((adjointGroup t.tag K).subtype.comp (t.reeEndo K hf a))).range := by
  rw [reeRelationGroup_eq_graph hf a, inf_eq_left]
  rintro _ ⟨x, rfl⟩
  exact ⟨x.2, (t.reeEndo K hf a x).2⟩

theorem pair_mem_reeRelationGroup_iff {g : ModGL t.tag K} :
    (g, g) ∈ reeRelationGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
        else t.prime ^ (a + 1)) ↔
      ∃ hg : g ∈ adjointGroup t.tag K, t.reeEndo K hf a ⟨g, hg⟩ = ⟨g, hg⟩ := by
  rw [reeRelationGroup_eq_graph hf a, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    have h1 : (x : ModGL t.tag K) = g := congrArg Prod.fst hx
    have h2 : ((t.reeEndo K hf a x : adjointGroup t.tag K) : ModGL t.tag K) = g :=
      congrArg Prod.snd hx
    subst h1
    exact ⟨x.2, Subtype.ext h2⟩
  · rintro ⟨hg, h⟩
    refine ⟨⟨g, hg⟩, Prod.ext rfl ?_⟩
    change ((t.reeEndo K hf a ⟨g, hg⟩ : adjointGroup t.tag K) : ModGL t.tag K) = g
    rw [h]

theorem reeFixedGroup_eq :
    reeFixedGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
        else t.prime ^ (a + 1)) =
      ((t.reeEndo K hf a).eqLocus (MonoidHom.id _)).map (adjointGroup t.tag K).subtype := by
  ext g
  rw [reeFixedGroup, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map]
  change (g ∈ adjointGroup t.tag K ∧ (g, g) ∈ _) ↔ _
  rw [pair_mem_reeRelationGroup_iff hf a]
  constructor
  · rintro ⟨-, hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, x.2, hx⟩

theorem mem_reeFixedGroup_iff {g : ModGL t.tag K} :
    g ∈ reeFixedGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
        else t.prime ^ (a + 1)) ↔
      ∃ hg : g ∈ adjointGroup t.tag K, t.reeEndo K hf a ⟨g, hg⟩ = ⟨g, hg⟩ := by
  rw [reeFixedGroup_eq hf a, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

variable (t K) in
@[expose] def reeAut [Finite K] (a : ℕ) : adjointGroup t.tag K ≃* adjointGroup t.tag K :=
  MulEquiv.ofBijective (t.reeEndo K (shortFaithful (CharP.cast_eq_zero K t.prime)) a)
    (reeEndo_injective _ a).bijective_of_finite

omit hf in
theorem reeAut_apply [Finite K] (g : adjointGroup t.tag K) :
    t.reeAut K a g = t.reeEndo K (shortFaithful (CharP.cast_eq_zero K t.prime)) a g :=
  rfl

end ReeTag

open ReeTag

theorem exceptional_reeFixedGroup_eq (t : ReeTag) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (a : ℕ) :
    (∀ (i : Fin t.tag.rank) (c : K),
      t.reeAut K a (xElement i c) = xElement (t.perm i) (c ^ t.relationExponent a i) ∧
        t.reeAut K a (yElement i c) = yElement (t.perm i) (c ^ t.relationExponent a i)) ∧
    reeRelationGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
        else t.prime ^ (a + 1)) =
      ((adjointGroup t.tag K).subtype.prod
        ((adjointGroup t.tag K).subtype.comp (t.reeAut K a).toMonoidHom)).range ∧
    reeFixedGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
        else t.prime ^ (a + 1)) =
      ((t.reeAut K a).toMonoidHom.eqLocus (MonoidHom.id _)).map (adjointGroup t.tag K).subtype :=
  ⟨fun i c => ⟨reeEndo_xElement (shortFaithful (CharP.cast_eq_zero K t.prime)) a i c,
      reeEndo_yElement (shortFaithful (CharP.cast_eq_zero K t.prime)) a i c⟩,
    reeRelationGroup_eq_graph (shortFaithful (CharP.cast_eq_zero K t.prime)) a,
    reeFixedGroup_eq (shortFaithful (CharP.cast_eq_zero K t.prime)) a⟩

theorem reeFixedGroup_G2_eq (K : Type) [Field K] [Finite K] [CharP K 3] (a : ℕ) :
    ∃ F : adjointGroup .G2 K ≃* adjointGroup .G2 K,
      (∀ (i : Fin Tag.G2.rank) (c : K),
        F (xElement i c) = xElement (reeG2Perm i) (c ^ if i ∈ reeG2Long then 3 ^ a
          else 3 ^ (a + 1)) ∧
        F (yElement i c) = yElement (reeG2Perm i) (c ^ if i ∈ reeG2Long then 3 ^ a
          else 3 ^ (a + 1))) ∧
      reeFixedGroup .G2 K reeG2Perm (fun i => if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1)) =
        (F.toMonoidHom.eqLocus (MonoidHom.id _)).map (adjointGroup .G2 K).subtype := by
  have : CharP K ReeTag.G2.prime := ‹CharP K 3›
  obtain ⟨h1, -, h3⟩ := exceptional_reeFixedGroup_eq .G2 K a
  exact ⟨ReeTag.G2.reeAut K a, h1, h3⟩

theorem reeFixedGroup_F4_eq (K : Type) [Field K] [Finite K] [CharP K 2] (a : ℕ) :
    ∃ F : adjointGroup .F4 K ≃* adjointGroup .F4 K,
      (∀ (i : Fin Tag.F4.rank) (c : K),
        F (xElement i c) = xElement (reeF4Perm i) (c ^ if i ∈ reeF4Long then 2 ^ a
          else 2 ^ (a + 1)) ∧
        F (yElement i c) = yElement (reeF4Perm i) (c ^ if i ∈ reeF4Long then 2 ^ a
          else 2 ^ (a + 1))) ∧
      reeFixedGroup .F4 K reeF4Perm (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) =
        (F.toMonoidHom.eqLocus (MonoidHom.id _)).map (adjointGroup .F4 K).subtype := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨h1, -, h3⟩ := exceptional_reeFixedGroup_eq .F4 K a
  exact ⟨ReeTag.F4.reeAut K a, h1, h3⟩

end CFSG.LieType.Ree
