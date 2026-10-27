module

public import CFSG.LieType.Ree.SmallReeFixedGroupSchreier
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.ScalarNormalizerFieldPart

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.OrderReductions.FrattiniAutomorphisms
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section FieldPart

theorem Sylow_scalar_Frattini_outer_field_section {G Ω : Type*} [Group G] [Finite G]
    [MulAction G Ω] [Finite Ω] [MulAction.IsPretransitive G Ω] [FaithfulSMul G Ω]
    (hΩ : 3 ≤ Nat.card Ω) (ξ : Ω) {p : ℕ} [Fact p.Prime] (U : Sylow p G)
    (hUξ : (U : Subgroup G) ≤ MulAction.stabilizer G ξ)
    (hUn : ((U : Subgroup G).subgroupOf (MulAction.stabilizer G ξ)).Normal)
    (htr : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ u : (U : Subgroup G), (u : G) • ω = ω')
    (w : G) (hw : w • ξ ≠ ξ) {n : ℕ} {K : Type*} [Field K] (hK : Nat.card K = p ^ n)
    (e : Additive ((U : Subgroup G) ⧸ frattini (U : Subgroup G)) ≃+ K)
    (hT : (((Subgroup.normalizer (((U : Subgroup G).map (MulAut.conj w).toMonoidHom :
        Subgroup G) : Set G)).subgroupOf (Subgroup.normalizer ((U : Subgroup G) : Set G))).map
          (U : Subgroup G).normalizerMonoidHom).map (frattiniScalarRep e) = scalarAddAut K)
    (ψ : (K ≃+* K) →* MulAut G)
    (hψ : ∀ σ, ψ σ ∈ pairAutSubgroup (U : Subgroup G)
      ((U : Subgroup G).map (MulAut.conj w).toMonoidHom))
    (hψρ : ∀ σ x, (frattiniScalarRep e (pairAutRestrict (U : Subgroup G)
      ((U : Subgroup G).map (MulAut.conj w).toMonoidHom) ⟨ψ σ, hψ σ⟩)).toAdd x = σ x) :
    ∃ χ : Outer G →* (K ≃+* K), IsPGroup p χ.ker ∧
      ∀ σ, χ (QuotientGroup.mk (ψ σ) : Outer G) = σ := by
  have hp : p.Prime := Fact.out
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero n hp.ne_zero)
  set V := (U : Subgroup G).map (MulAut.conj w).toMonoidHom
  set Th : Subgroup (MulAut (U : Subgroup G)) :=
    ((Subgroup.normalizer (V : Set G)).subgroupOf
      (Subgroup.normalizer ((U : Subgroup G) : Set G))).map
        (U : Subgroup G).normalizerMonoidHom with hTh
  obtain ⟨-, hinj, hprod, -⟩ := Suzuki_opposite_Sylow_restriction hΩ ξ U hUξ hUn htr w hw
  set A := pairAutSubgroup (U : Subgroup G) V
  set r := pairAutRestrict (U : Subgroup G) V
  set ρ := frattiniScalarRep e
  have hconj : ∀ (α : A) (t : Subgroup.normalizer ((U : Subgroup G) : Set G)),
      r α * (U : Subgroup G).normalizerMonoidHom t * (r α)⁻¹ =
        (U : Subgroup G).normalizerMonoidHom
          ⟨(α : MulAut G) t, apply_mem_normalizer_of_map_eq α.2.1 t.2⟩ := by
    intro α t
    refine MulEquiv.ext fun u => Subtype.ext ?_
    change (α : MulAut G) ((t : G) * (α : MulAut G).symm (u : G) * (t : G)⁻¹) =
      (α : MulAut G) t * u * ((α : MulAut G) t)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hmapTh : ∀ (α : A), ∀ φ ∈ Th, r α * φ * (r α)⁻¹ ∈ Th := by
    intro α φ hφ
    rw [hTh] at hφ ⊢
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hφ
    rw [hconj]
    refine Subgroup.mem_map.2 ⟨⟨(α : MulAut G) t, apply_mem_normalizer_of_map_eq α.2.1 t.2⟩,
      ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact apply_mem_normalizer_of_map_eq α.2.2 ht
  have hrN : ∀ α : A, r α ∈ Subgroup.normalizer (Th : Set (MulAut (U : Subgroup G))) := by
    intro α
    rw [Subgroup.mem_normalizer_iff]
    intro φ
    refine ⟨hmapTh α φ, fun h => ?_⟩
    have h2 := hmapTh α⁻¹ _ h
    rw [map_inv, inv_inv] at h2
    have h3 : (r α)⁻¹ * (r α * φ * (r α)⁻¹) * r α = φ := by group
    rwa [h3] at h2
  have hNS : ∀ α : A,
      ρ (r α) ∈ Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) := by
    intro α
    have hα := hrN α
    rw [Subgroup.mem_normalizer_iff] at hα ⊢
    intro y
    rw [← hT]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨r α * s * (r α)⁻¹, (hα s).1 hs, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨s, hs, hseq⟩
      refine ⟨(r α)⁻¹ * s * r α, ?_, ?_⟩
      · have h := (hα ((r α)⁻¹ * s * r α)).2
        rw [show r α * ((r α)⁻¹ * s * r α) * (r α)⁻¹ = s by group] at h
        exact h hs
      · rw [map_mul, map_mul, map_inv, hseq]
        group
  let ρA : A →* Subgroup.normalizer (scalarAddAut K : Set (Multiplicative (AddAut K))) :=
    (ρ.comp r).codRestrict _ hNS
  let η : A →* (K ≃+* K) := scalarNormalizerFieldPart.comp ρA
  have hη : ∀ α : A, η α = 1 ↔ ρ (r α) ∈ scalarAddAut K := fun α =>
    scalarNormalizerFieldPart_eq_one_iff (ρA α)
  let φ : A →* Outer G := (QuotientGroup.mk' (inner G)).comp A.subtype
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner G) q
    obtain ⟨g, β, hβ, rfl⟩ := hprod α
    refine ⟨⟨β, hβ⟩, ?_⟩
    change ((β : MulAut G) : Outer G) = ((MulAut.conj g * β : MulAut G) : Outer G)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := inner G) (MulAut.conj g)).2 ⟨g, rfl⟩,
      one_mul]
  have hconjA : ∀ t : Subgroup.normalizer ((U : Subgroup G) : Set G),
      (t : G) ∈ Subgroup.normalizer (V : Set G) → MulAut.conj (t : G) ∈ A := fun t ht =>
    ⟨Subgroup.mem_normalizer_iff_map_conj_eq.1 t.2, Subgroup.mem_normalizer_iff_map_conj_eq.1 ht⟩
  have hker : φ.ker ≤ η.ker := by
    intro α hα
    have hαi : (α : MulAut G) ∈ inner G := (QuotientGroup.eq_one_iff (N := inner G) _).1 hα
    obtain ⟨g, hg⟩ := hαi
    have hgU : g ∈ Subgroup.normalizer ((U : Subgroup G) : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 (by rw [hg]; exact α.2.1)
    have hgV : g ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 (by rw [hg]; exact α.2.2)
    have hrα : r α ∈ Th := by
      refine ⟨⟨g, hgU⟩, Subgroup.mem_subgroupOf.2 hgV, MulEquiv.ext fun u => Subtype.ext ?_⟩
      change g * (u : G) * g⁻¹ = (α : MulAut G) u
      rw [← hg]
      rfl
    have hρα : ρ (r α) ∈ scalarAddAut K := by
      rw [← hT]
      exact ⟨r α, hrα, rfl⟩
    exact MonoidHom.mem_ker.2 ((hη α).2 hρα)
  let χ : Outer G →* (K ≃+* K) := φ.liftOfSurjective hφ ⟨η, hker⟩
  have hχ : ∀ α : A, χ (φ α) = η α := fun α =>
    φ.liftOfRightInverse_comp_apply _ _ ⟨η, hker⟩ α
  have hQ : IsPGroup p (ρ.comp r).ker := by
    have hmem : ∀ β : (ρ.comp r).ker,
        r β ∈ (quotientAutomorphism (frattini (U : Subgroup G))).ker := fun β =>
      mem_ker_of_frattiniScalarRep_eq_one e (MonoidHom.mem_ker.1 β.2)
    let ι : (ρ.comp r).ker →* (quotientAutomorphism (frattini (U : Subgroup G))).ker :=
      (r.comp (ρ.comp r).ker.subtype).codRestrict _ hmem
    have hι : Function.Injective ι := fun x y h =>
      Subtype.ext (hinj (congrArg Subtype.val h))
    exact (CFSG.GroupTheory.frattini_automorphism_kernel U.isPGroup').2.of_injective ι hι
  have hle : χ.ker ≤ (ρ.comp r).ker.map φ := by
    intro x hx
    obtain ⟨α, rfl⟩ := hφ x
    have hηα : η α = 1 := by
      rw [← hχ α]
      exact hx
    have hρα := (hη α).1 hηα
    rw [← hT] at hρα
    obtain ⟨τ, ⟨t, ht, rfl⟩, hτ⟩ := hρα
    have htV : (t : G) ∈ Subgroup.normalizer (V : Set G) := Subgroup.mem_subgroupOf.1 ht
    set γ : A := ⟨MulAut.conj (t : G), hconjA t htV⟩
    have hrγ : r γ = (U : Subgroup G).normalizerMonoidHom t :=
      MulEquiv.ext fun u => Subtype.ext rfl
    have hφγ : φ γ = 1 := (QuotientGroup.eq_one_iff (N := inner G) _).2 ⟨t, rfl⟩
    refine ⟨α * γ⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.comp_apply,
        MonoidHom.comp_apply, hrγ, hτ, mul_inv_cancel]
    · rw [map_mul, map_inv, hφγ, inv_one, mul_one]
  refine ⟨χ, (hQ.map φ).to_le hle, fun σ => ?_⟩
  have h := hχ ⟨ψ σ, hψ σ⟩
  change χ (φ ⟨ψ σ, hψ σ⟩) = σ
  rw [h]
  exact scalarNormalizerFieldPart_eq (c := 1) fun x => by
    rw [Units.val_one, one_mul]
    exact hψρ σ x

end FieldPart

theorem isComplement'_ker_range_of_section {O F : Type*} [Group O] [Group F] (χ : O →* F)
    (s : F →* O) (h : ∀ x, χ (s x) = x) : χ.ker.IsComplement' s.range := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    rw [MonoidHom.mem_ker, h] at hx
    rw [hx, map_one]
  · refine Set.eq_univ_of_forall fun x => ⟨x * (s (χ x))⁻¹, ?_, s (χ x), ⟨χ x, rfl⟩,
      inv_mul_cancel_right _ _⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]

namespace ReeTag

section FieldAut

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem finiteReeAut_frobeniusTwist
    (σ : K →+* K) (g : adjointGroup t.tag K) :
    t.finiteReeAut K a (frobeniusTwist t.tag K σ g) =
      frobeniusTwist t.tag K σ (t.finiteReeAut K a g) := by
  have hF : ∀ x, t.finiteReeAut K a x =
      t.reeEndo K (shortFaithful (CharP.cast_eq_zero K t.prime)) a x := fun x =>
    DFunLike.congr_fun (finiteReeAut_toMonoidHom a) x
  have h := adjointGroup_hom_ext
    (f := (t.finiteReeAut K a).toMonoidHom.comp (frobeniusTwist t.tag K σ))
    (g := (frobeniusTwist t.tag K σ).comp (t.finiteReeAut K a).toMonoidHom)
    (fun i c => by
      change t.finiteReeAut K a (frobeniusTwist t.tag K σ (xElement i c)) =
        frobeniusTwist t.tag K σ (t.finiteReeAut K a (xElement i c))
      rw [hF, hF, frobeniusTwist_xElement, reeEndo_xElement, reeEndo_xElement,
        frobeniusTwist_xElement, map_pow])
    (fun i c => by
      change t.finiteReeAut K a (frobeniusTwist t.tag K σ (yElement i c)) =
        frobeniusTwist t.tag K σ (t.finiteReeAut K a (yElement i c))
      rw [hF, hF, frobeniusTwist_yElement, reeEndo_yElement, reeEndo_yElement,
        frobeniusTwist_yElement, map_pow])
  exact DFunLike.congr_fun h g

theorem exactEntrywiseAut_mem_reeGamma
    (σ : K ≃+* K) {g : ModGL t.tag K}
    (hg : g ∈ t.reeGamma K a) : exactEntrywiseAut t.tag σ g ∈ t.reeGamma K a := by
  obtain ⟨hg', hF⟩ := mem_reeGamma.1 hg
  refine mem_reeGamma.2 ⟨entrywiseGL_mem σ.toRingHom hg', ?_⟩
  have h := finiteReeAut_frobeniusTwist (a := a) σ.toRingHom ⟨g, hg'⟩
  rw [hF] at h
  exact h

theorem map_reeGamma_exactEntrywiseAut
    (σ : K ≃+* K) :
    (t.reeGamma K a).map (exactEntrywiseAut t.tag σ).toMonoidHom = t.reeGamma K a := by
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact exactEntrywiseAut_mem_reeGamma σ hg
  · exact ⟨exactEntrywiseAut t.tag σ.symm g, exactEntrywiseAut_mem_reeGamma σ.symm hg,
      exactEntrywiseAut_right_inv σ g⟩

theorem map_reeFixedPosUnipotent_exactEntrywiseAut
    (σ : K ≃+* K) :
    (t.reeFixedPosUnipotent K a).map (exactEntrywiseAut t.tag σ).toMonoidHom =
      t.reeFixedPosUnipotent K a := by
  rw [reeFixedPosUnipotent, Subgroup.map_inf _ _ (exactEntrywiseAut t.tag σ).toMonoidHom
    (exactEntrywiseAut t.tag σ).injective,
    map_exactEntrywiseAut σ (Or.inr (Or.inl rfl)), map_reeGamma_exactEntrywiseAut]

variable (t K a) in
@[expose] def reeGammaFieldAut
    (σ : K ≃+* K) : MulAut (t.reeGamma K a) :=
  mulAutRestrict (t.reeGamma K a) (exactEntrywiseAut t.tag σ) (map_reeGamma_exactEntrywiseAut σ)

theorem coe_reeGammaFieldAut
    (σ : K ≃+* K) (g : t.reeGamma K a) :
    ((t.reeGammaFieldAut K a σ g : t.reeGamma K a) : ModGL t.tag K) =
      Units.map (entrywiseHom σ.toRingHom) (g : ModGL t.tag K) :=
  rfl

variable (t K a) in
@[expose] def reeGammaFieldAutHom :
    (K ≃+* K) →* MulAut (t.reeGamma K a) where
  toFun := t.reeGammaFieldAut K a
  map_one' := MulEquiv.ext fun g => Subtype.ext (Units.ext (entrywise_id _))
  map_mul' σ τ := MulEquiv.ext fun g => Subtype.ext (Units.ext (by
    change entrywise (σ * τ).toRingHom
        ((g : ModGL t.tag K) : Module.End K (RootModule t.tag K)) =
      entrywise σ.toRingHom (entrywise τ.toRingHom
        ((g : ModGL t.tag K) : Module.End K (RootModule t.tag K)))
    rw [entrywise_entrywise]
    rfl))

theorem reeGammaFieldAutHom_apply
    (σ : K ≃+* K) :
    t.reeGammaFieldAutHom K a σ = t.reeGammaFieldAut K a σ :=
  rfl

variable (t K a) in
@[expose] def reeGammaFld :
    Subgroup (MulAut (t.reeGamma K a)) :=
  (t.reeGammaFieldAutHom K a).range

theorem mem_reeGammaFld_iff
    {α : MulAut (t.reeGamma K a)} :
    α ∈ t.reeGammaFld K a ↔ ∃ σ : K ≃+* K, t.reeGammaFieldAut K a σ = α :=
  Iff.rfl

end FieldAut

end ReeTag

theorem map_map_conj_of_apply_eq {X : Type*} [Group X] {α : MulAut X} {H : Subgroup X}
    (hH : H.map α.toMonoidHom = H) {n : X} (hn : α n = n) :
    (H.map (MulAut.conj n).toMonoidHom).map α.toMonoidHom = H.map (MulAut.conj n).toMonoidHom := by
  have e : α.toMonoidHom.comp (MulAut.conj n).toMonoidHom =
      (MulAut.conj n).toMonoidHom.comp α.toMonoidHom := MonoidHom.ext fun x => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
      hn]
  rw [Subgroup.map_map, e, ← Subgroup.map_map, hH]

section SmallRee

variable {K : Type} [Field K] {a : ℕ}

theorem entrywise_smallReeX
    (σ : K →+* K) (i : Fin 6) (c : K) :
    Units.map (entrywiseHom σ) (smallReeX K i c) = smallReeX K i (σ c) :=
  Units.ext (entrywise_pinnedX σ (smallReeRoot i) c)

theorem entrywise_smallReeCoord
    (σ : K →+* K) (t b c : K) :
    Units.map (entrywiseHom σ) (smallReeCoord a K t b c) =
      smallReeCoord a K (σ t) (σ b) (σ c) := by
  simp only [smallReeCoord, map_mul, entrywise_smallReeX, smallReeSigma, map_sub, map_pow]

variable [Finite K] [CharP K ReeTag.G2.prime] in
theorem frattiniScalarRep_of_entrywise
    (hK : Nat.card K = 3 ^ (2 * a + 1))
    (e : Additive (((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)) ⧸
      frattini ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a))) ≃+ K)
    (he : ∀ (x : (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a))
      (t b c : K), ((x : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) =
        smallReeCoord a K t b c → e (Additive.ofMul (x : _ ⧸ frattini _)) = t)
    (σ : K ≃+* K)
    (α : MulAut ((ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)))
    (hα : ∀ x, ((α x : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) =
      Units.map (entrywiseHom σ.toRingHom) ((x : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K))
    (y : K) : (frattiniScalarRep e α).toAdd y = σ y := by
  obtain ⟨x₀, h1⟩ : ∃ x₀ : (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf
      (ReeTag.G2.reeGamma K a), ((x₀ : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) =
        smallReeCoord a K y 0 0 :=
    ⟨⟨⟨smallReeCoord a K y 0 0, ReeTag.reeFixedPosUnipotent_le_reeGamma
      (ReeTag.smallReeCoord_mem_reeFixedPosUnipotent hK y 0 0)⟩,
        Subgroup.mem_subgroupOf.2 (ReeTag.smallReeCoord_mem_reeFixedPosUnipotent hK y 0 0)⟩, rfl⟩
  have hy : e.symm y = Additive.ofMul (x₀ : _ ⧸ frattini _) := by
    rw [AddEquiv.symm_apply_eq, he x₀ y 0 0 h1]
  rewrite [frattiniScalarRep_apply, hy, toMul_ofMul]
  have hq : quotientAutomorphism (frattini _) α (x₀ : _ ⧸ frattini _) =
      ((α x₀ : _) : _ ⧸ frattini _) :=
    quotientAutomorphism_apply (frattini _) α x₀
  rewrite [hq]
  refine he _ (σ y) (σ 0) (σ 0) ?_
  rw [hα, h1]
  exact entrywise_smallReeCoord σ.toRingHom y 0 0

end SmallRee

theorem small_Ree_outer_three_kernel_field_complement
    (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    (∀ (σ : K ≃+* K) (g : ReeTag.G2.reeGamma K a),
      ((ReeTag.G2.reeGammaFieldAut K a σ g : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) =
        Units.map (entrywiseHom σ.toRingHom) (g : ModGL ReeTag.G2.tag K)) ∧
    Nat.card (ReeTag.G2.reeGammaFld K a) = 2 * a + 1 ∧
    Nat.card ((ReeTag.G2.reeGammaFld K a).map
      (QuotientGroup.mk' (inner (ReeTag.G2.reeGamma K a)))) = 2 * a + 1 ∧
    (∃ (R : Subgroup (Outer (ReeTag.G2.reeGamma K a)))
      (χ : Outer (ReeTag.G2.reeGamma K a) →* (K ≃+* K)), χ.ker = R ∧
      (∀ σ : K ≃+* K, χ (QuotientGroup.mk (ReeTag.G2.reeGammaFieldAut K a σ)) = σ) ∧
      R.Normal ∧ IsPGroup 3 R ∧
      R.IsComplement' ((ReeTag.G2.reeGammaFld K a).map
        (QuotientGroup.mk' (inner (ReeTag.G2.reeGamma K a))))) ∧
    Odd (Nat.card (Outer (ReeTag.G2.reeGamma K a))) ∧
    ∀ p : ℕ, p.Prime → 3 < p → ∀ E : Subgroup (Outer (ReeTag.G2.reeGamma K a)),
      CFSG.IsElementaryAbelian p E → IsCyclic E := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨hn, hηξ, hfaith, htrans, -, -, hreg, hcardΩ, -, -, ⟨⟨P, hPp, hPmax⟩, rfl⟩, hstab, hUn,
    -, hNUV⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  obtain ⟨-, -, -, -, -, -, -, hΦ₀, π, hπ, hπs, hπker, e₀, he₀, hT₀⟩ :=
    small_Ree_positive_Frattini_quotient a ha K hK
  set Γ := ReeTag.G2.reeGamma K a
  set B' := (ReeTag.G2.reeFixedBorel K a).subgroupOf Γ
  set U' := (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf Γ
  set n' : Γ := ⟨_, hn⟩
  have hUΓ : ReeTag.G2.reeFixedPosUnipotent K a ≤ Γ := ReeTag.reeFixedPosUnipotent_le_reeGamma
  have hHΓ : ReeTag.G2.reeFixedTorus K a ≤ Γ :=
    ReeTag.reeFixedTorus_le_reeFixedBorel.trans ReeTag.reeFixedBorel_le_reeGamma
  have hq : 3 ≤ 3 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 3
  have hq3 : 3 ≤ (3 ^ (2 * a + 1)) ^ 3 := hq.trans (Nat.le_self_pow (by norm_num) _)
  have hΩ : 3 ≤ Nat.card (Γ ⧸ B') := by
    rw [hcardΩ]
    omega
  set ι : U' ≃* ReeTag.G2.reeFixedPosUnipotent K a := Subgroup.subgroupOfEquivOfLe hUΓ
  set π' : U' →* Multiplicative K := π.comp ι.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπs.comp ι.surjective
  have hΦ' : frattini U' = π'.ker := by
    rw [frattini_eq_comap_mulEquiv ι, hπ', ← MonoidHom.comap_ker, hπker, hΦ₀]
  obtain ⟨e, he'⟩ : ∃ e : Additive (U' ⧸ frattini U') ≃+ K,
      ∀ x : U', e (Additive.ofMul (x : U' ⧸ frattini U')) = (π (ι x)).toAdd :=
    ⟨MulEquiv.toAdditiveLeft ((QuotientGroup.quotientMulEquivOfEq hΦ').trans
      (QuotientGroup.quotientKerEquivOfSurjective π' hπ's)), fun x => rfl⟩
  have hee : ∀ x : U', e (Additive.ofMul (x : U' ⧸ frattini U')) =
      e₀ (Additive.ofMul (ι x : ReeTag.G2.reeFixedPosUnipotent K a ⧸
        frattini (ReeTag.G2.reeFixedPosUnipotent K a))) := fun x => by
    rw [he₀, he']
  have hT : (((Subgroup.normalizer ((U'.map (MulAut.conj n').toMonoidHom : Subgroup Γ) :
      Set Γ)).subgroupOf (Subgroup.normalizer (U' : Set Γ))).map
        U'.normalizerMonoidHom).map (frattiniScalarRep e) = scalarAddAut K := by
    rw [← hT₀]
    ext f
    constructor
    · rintro ⟨φ, ⟨t, ht, rfl⟩, rfl⟩
      have htH : ((t : Γ) : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedTorus K a := by
        have h : (t : Γ) ∈ Subgroup.normalizer (U' : Set Γ) ⊓
            Subgroup.normalizer ((U'.map (MulAut.conj n').toMonoidHom : Subgroup Γ) :
              Set Γ) :=
          Subgroup.mem_inf.2 ⟨t.2, ht⟩
        rw [hNUV] at h
        exact h
      exact ⟨ReeTag.G2.reeFixedTorusConj K a ⟨_, htH⟩, ⟨_, rfl⟩,
        (frattiniScalarRep_eq_of_comm ι e e₀ hee fun x => Subtype.ext rfl).symm⟩
    · rintro ⟨φ, ⟨h, rfl⟩, rfl⟩
      have hmem : (⟨h, hHΓ h.2⟩ : Γ) ∈ Subgroup.normalizer (U' : Set Γ) ⊓
          Subgroup.normalizer ((U'.map (MulAut.conj n').toMonoidHom : Subgroup Γ) : Set Γ) := by
        rw [hNUV]
        exact h.2
      exact ⟨U'.normalizerMonoidHom ⟨_, (Subgroup.mem_inf.1 hmem).1⟩,
        ⟨⟨_, (Subgroup.mem_inf.1 hmem).1⟩, (Subgroup.mem_inf.1 hmem).2, rfl⟩,
        frattiniScalarRep_eq_of_comm ι e e₀ hee fun x => Subtype.ext rfl⟩
  have hUξ : U' ≤ MulAction.stabilizer Γ (QuotientGroup.mk 1 : Γ ⧸ B') := by
    rw [hstab]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ReeTag.reeFixedPosUnipotent_le_reeFixedBorel hx
  have hUn' : (U'.subgroupOf (MulAction.stabilizer Γ (QuotientGroup.mk 1 : Γ ⧸ B'))).Normal := by
    rw [hstab]
    exact hUn
  have hw : n' • (QuotientGroup.mk 1 : Γ ⧸ B') ≠ QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact hηξ
  set ψ := ReeTag.G2.reeGammaFieldAutHom K a
  have hψU : ∀ σ : K ≃+* K, U'.map (ψ σ).toMonoidHom = U' := fun σ =>
    map_subgroupOf_mulAutRestrict (ReeTag.map_reeGamma_exactEntrywiseAut σ)
      (ReeTag.map_reeFixedPosUnipotent_exactEntrywiseAut σ)
  have hψn : ∀ σ : K ≃+* K, ψ σ n' = n' := fun σ => Subtype.ext (entrywise_canonicalRep σ w₀)
  have hψA : ∀ σ : K ≃+* K, ψ σ ∈ pairAutSubgroup U' (U'.map (MulAut.conj n').toMonoidHom) :=
    fun σ => ⟨hψU σ, map_map_conj_of_apply_eq (hψU σ) (hψn σ)⟩
  have hπU : ∀ (x : U') (t b c : K), ((x : Γ) : ModGL ReeTag.G2.tag K) = smallReeCoord a K t b c →
      e (Additive.ofMul (x : U' ⧸ frattini U')) = t := by
    intro x t b c hx
    rw [he']
    have hιx : ι x = ⟨smallReeCoord a K t b c,
        ReeTag.smallReeCoord_mem_reeFixedPosUnipotent hK t b c⟩ := Subtype.ext hx
    rw [hιx, hπ]
    rfl
  have hψρ : ∀ (σ : K ≃+* K) (y : K), (frattiniScalarRep e (pairAutRestrict U'
      (U'.map (MulAut.conj n').toMonoidHom) ⟨ψ σ, hψA σ⟩)).toAdd y = σ y := fun σ =>
    frattiniScalarRep_of_entrywise hK e hπU σ _ fun x => rfl
  obtain ⟨χ, hχp, hχψ⟩ := Sylow_scalar_Frattini_outer_field_section hΩ
    (QuotientGroup.mk 1 : Γ ⧸ B') (p := 3) ⟨U', hPp, hPmax⟩ hUξ hUn'
    (fun ω ω' hω hω' => (hreg ω ω' hω hω').exists) n' hw hK e hT ψ hψA hψρ
  set s : (K ≃+* K) →* Outer Γ := (QuotientGroup.mk' (inner Γ)).comp ψ with hs
  have hχs : ∀ σ, χ (s σ) = σ := hχψ
  have hsinj : Function.Injective s := fun σ τ h => by rw [← hχs σ, ← hχs τ, h]
  have hψinj : Function.Injective ψ := fun σ τ h => hsinj (by rw [hs, MonoidHom.comp_apply,
    MonoidHom.comp_apply, h])
  have hFbar : (ReeTag.G2.reeGammaFld K a).map (QuotientGroup.mk' (inner Γ)) = s.range := by
    rw [ReeTag.reeGammaFld, hs, MonoidHom.range_comp]
  obtain ⟨σ₀, -, -, hσ₀, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_three (by omega) hK
  have hcycAut : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ₀, hσ₀⟩
  have hcardFld : Nat.card (ReeTag.G2.reeGammaFld K a) = 2 * a + 1 := by
    rw [← hcardAut, ReeTag.reeGammaFld]
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hcardFbar : Nat.card ((ReeTag.G2.reeGammaFld K a).map
      (QuotientGroup.mk' (inner Γ))) = 2 * a + 1 := by
    rw [hFbar, ← hcardAut]
    exact (Nat.card_congr (MonoidHom.ofInjective hsinj).toEquiv).symm
  have hcompl := isComplement'_ker_range_of_section χ s hχs
  have hcompl' : χ.ker.IsComplement' ((ReeTag.G2.reeGammaFld K a).map
      (QuotientGroup.mk' (inner Γ))) := by
    rw [hFbar]
    exact hcompl
  refine ⟨fun σ g => ReeTag.coe_reeGammaFieldAut σ g, hcardFld, hcardFbar,
    ⟨χ.ker, χ, rfl, hχψ, inferInstance, hχp, hcompl'⟩, ?_, fun p hp hp3 E hE => ?_⟩
  · obtain ⟨b, hb⟩ := hχp.exists_card_eq
    rw [← hcompl.card_mul_card, hb, ← hFbar, hcardFbar]
    exact (Odd.pow (by decide : Odd 3)).mul (odd_two_mul_add_one a)
  · have : Fact p.Prime := ⟨hp⟩
    have hdisj : Disjoint E χ.ker :=
      IsPGroup.disjoint_of_ne p 3 (by omega) E χ.ker (CFSG.IsElementaryAbelian.isPGroup p E) hχp
    have hinj : Function.Injective (χ.comp E.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact Subtype.ext (Subgroup.disjoint_def.1 hdisj x.2 hx)
    exact isCyclic_of_injective _ hinj

end CFSG.LieType.Ree
