module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionLift
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionFactorization

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open QuaternionOvergroups
open scoped Classical
universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem subgroupWreathImage_quaternion_unique
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (A : Subgroup G) (hAS : A ≤ S)
    (hquat : Nonempty (QuaternionGroup (2 ^ n / 2) ≃* A)) :
    sylowEmbeddedSubgroup S e.toMonoidHom A = Original.Y (2 ^ n) := by
  obtain ⟨E⟩ := hquat
  have hunique :=
    proper_overgroups_of_maximal_quaternion_have_no_odd_abelian_centric_automorphisms
  apply (hunique n hn).1.2
  exact ⟨E.trans (sylowEmbeddedSubgroupEquiv S e.toMonoidHom e.injective A hAS)⟩

theorem two_subgroup_conjugate_into_original_sylow
    (S : Sylow 2 G) (A : Subgroup G) (hA : IsPGroup 2 A) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S := by
  obtain ⟨T, hAT⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  refine ⟨g, ?_⟩
  have hmap : (T : Subgroup G).map (MulAut.conj g).toMonoidHom = (S : Subgroup G) := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  rw [← hmap]
  exact Subgroup.map_mono hAT

@[expose] def originalComponentInclusion {G : Type} [Group G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    originalComponentPreimage n S e K →* K where
  toFun d := ⟨d.val.val, d.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem originalComponentInclusion_coe {G : Type} [Group G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (d : originalComponentPreimage n S e K) :
    (originalComponentInclusion n S e K d : G) = d.val.val := rfl

theorem originalComponentInclusion_injective {G : Type} [Group G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) :
    Function.Injective (originalComponentInclusion n S e K) := by
  intro d r h
  have hv : d.val.val = r.val.val := congrArg (fun k : K => (k : G)) h
  exact Subtype.ext (Subtype.ext hv)

@[expose] def originalQuaternionSubgroup {G : Type} [Group G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (Q : Sylow 2 (originalComponentPreimage n S e K)) : Subgroup K :=
  (Q : Subgroup (originalComponentPreimage n S e K)).map (originalComponentInclusion n S e K)

theorem originalQuaternionSubgroup_quaternion
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (Q : Sylow 2 (originalComponentPreimage n S e K)) :
    Nonempty (QuaternionGroup (2 ^ n / 2) ≃* originalQuaternionSubgroup n S e K Q) := by
  obtain ⟨E⟩ := original_component_preimage_sylow_quaternion hnonab n hn S e hfour K hcover Q
  exact ⟨E.trans ((Q : Subgroup (originalComponentPreimage n S e K)).equivMapOfInjective
    (originalComponentInclusion n S e K) (originalComponentInclusion_injective n S e K))⟩

theorem originalQuaternionSubgroup_involution_mem
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (Q : Sylow 2 (originalComponentPreimage n S e K)) :
    (⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K) ∈
      originalQuaternionSubgroup n S e K Q := by
  exact Subgroup.mem_map.mpr
    ⟨⟨centralInvolution n S e,
      original_involution_mem_component_preimage hnonab n hn S e hfour K hxK⟩,
        original_involution_mem_every_component_sylow hnonab n hn S e hfour K hxK Q, rfl⟩

omit [Finite G] in
theorem quaternion_position_conjugate_image_eq_original_Y
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (A : Subgroup G) (hquat : Nonempty (QuaternionGroup (2 ^ n / 2) ≃* A))
    (g : G) (hAS : A.map (MulAut.conj g).toMonoidHom ≤ S) :
    A.map (MulAut.conj g).toMonoidHom = modelY S e := by
  let Ag := A.map (MulAut.conj g).toMonoidHom
  have hquatg : Nonempty (QuaternionGroup (2 ^ n / 2) ≃* Ag) := by
    obtain ⟨E⟩ := hquat
    exact ⟨E.trans (A.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)⟩
  have hAg := subgroupWreathImage_quaternion_unique n hn S e Ag hAS hquatg
  have hmap := congrArg (Subgroup.map (wreathModelHom S e)) hAg
  rw [sylowEmbeddedSubgroup, Subgroup.map_map] at hmap
  have hcomp : (wreathModelHom S e).comp e.toMonoidHom = (S : Subgroup G).subtype := by
    ext s
    simp [wreathModelHom]
  rw [hcomp, Subgroup.map_subgroupOf_eq_of_le hAS] at hmap
  exact hmap

omit [Finite G] in
theorem quaternion_position_conjugator_fixes_original_involution
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (A : Subgroup G) (hquat : Nonempty (QuaternionGroup (2 ^ n / 2) ≃* A))
    (hxA : wreathModelHom S e (Original.x (2 ^ n)) ∈ A)
    (g : G) (hAS : A.map (MulAut.conj g).toMonoidHom ≤ S) :
    g * wreathModelHom S e (Original.x (2 ^ n)) * g⁻¹ =
      wreathModelHom S e (Original.x (2 ^ n)) := by
  have hmodel := quaternion_position_conjugate_image_eq_original_Y n hn S e A hquat g hAS
  have hxg : g * wreathModelHom S e (Original.x (2 ^ n)) * g⁻¹ ∈ modelY S e := by
    rw [← hmodel]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hxA
  apply modelY_unique_involution n hn S e _ hxg
  exact ((MulAut.conj g).orderOf_eq _).trans
    ((orderOf_injective _ (wreathModelHom_injective S e) _).trans
      (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1)

theorem quaternion_subgroup_positions_actual_sylow
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (A : Subgroup K)
    (hquat : Nonempty (QuaternionGroup (2 ^ n / 2) ≃* A))
    (hxA : wreathModelHom S e (Original.x (2 ^ n)) ∈ A.map K.subtype) :
    ∃ P : Sylow 2 K, A ≤ P ∧ ∃ g : G,
      g * wreathModelHom S e (Original.x (2 ^ n)) * g⁻¹ =
        wreathModelHom S e (Original.x (2 ^ n)) ∧
      ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S ∧
      (A.map K.subtype).map (MulAut.conj g).toMonoidHom = modelY S e := by
  let A0 := A.map K.subtype
  obtain ⟨E⟩ := hquat
  have htwo : IsPGroup 2 A := by
    have hYtwo : IsPGroup 2 (Original.Y (2 ^ n)) := by
      exact (S.isPGroup'.of_equiv e).to_subgroup _
    exact (hYtwo.of_equiv (originalYQuaternionEquiv n hn).symm).of_equiv E
  obtain ⟨P, hAP⟩ := htwo.exists_le_sylow
  let P0 := (P : Subgroup K).map K.subtype
  obtain ⟨g, hg⟩ := two_subgroup_conjugate_into_original_sylow S P0
    (P.isPGroup'.map K.subtype)
  have hAg : A0.map (MulAut.conj g).toMonoidHom ≤ S :=
    (Subgroup.map_mono (Subgroup.map_mono hAP)).trans hg
  have hA0quat : Nonempty (QuaternionGroup (2 ^ n / 2) ≃* A0) :=
    ⟨E.trans (A.equivMapOfInjective K.subtype K.subtype_injective)⟩
  exact ⟨P, hAP, g,
    quaternion_position_conjugator_fixes_original_involution n hn S e A0 hA0quat hxA g hAg,
    hg, quaternion_position_conjugate_image_eq_original_Y n hn S e A0 hA0quat g hAg⟩

@[expose] def positionedSylowEmbedding
    (S : Sylow 2 G) {m : ℕ} (e : S ≃* Wreath m) (K : Subgroup G)
    (P : Sylow 2 K) (g : G)
    (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S) :
    P →* Wreath m :=
  e.toMonoidHom.comp
    (((MulAut.conj g).toMonoidHom.comp
      (K.subtype.comp (P : Subgroup K).subtype)).codRestrict (S : Subgroup G) (fun p =>
        hPS (Subgroup.mem_map.mpr ⟨(p : K),
          Subgroup.mem_map.mpr ⟨(p : K), p.property, rfl⟩, rfl⟩)))

omit [Finite G] in
theorem positionedSylowEmbedding_ambient
    (S : Sylow 2 G) {m : ℕ} (e : S ≃* Wreath m) (K : Subgroup G)
    (P : Sylow 2 K) (g : G)
    (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S)
    (p : P) :
    wreathModelHom S e (positionedSylowEmbedding S e K P g hPS p) =
      g * ((p : K) : G) * g⁻¹ := by
  simp [positionedSylowEmbedding, wreathModelHom]

omit [Finite G] in
theorem positionedSylowEmbedding_injective
    (S : Sylow 2 G) {m : ℕ} (e : S ≃* Wreath m) (K : Subgroup G)
    (P : Sylow 2 K) (g : G)
    (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S) :
    Function.Injective (positionedSylowEmbedding S e K P g hPS) := by
  intro a b h
  have ha := congrArg (wreathModelHom S e) h
  rw [positionedSylowEmbedding_ambient, positionedSylowEmbedding_ambient] at ha
  have hb : ((a : K) : G) = ((b : K) : G) := (MulAut.conj g).injective ha
  exact Subtype.ext (Subtype.ext hb)

omit [Finite G] in
theorem positionedSylowEmbedding_covers_original_Y
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G)
    (P : Sylow 2 K) (g : G)
    (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S)
    (A : Subgroup K) (hAP : A ≤ P)
    (hAg : (A.map K.subtype).map (MulAut.conj g).toMonoidHom = modelY S e) :
    Original.Y (2 ^ n) ≤ (positionedSylowEmbedding S e K P g hPS).range := by
  intro y hy
  have hyG : wreathModelHom S e y ∈ modelY S e := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  rw [← hAg] at hyG
  obtain ⟨aG, haG, hay⟩ := Subgroup.mem_map.mp hyG
  obtain ⟨aK, haK, rfl⟩ := Subgroup.mem_map.mp haG
  refine ⟨⟨aK, hAP haK⟩, ?_⟩
  apply wreathModelHom_injective S e
  exact (positionedSylowEmbedding_ambient S e K P g hPS _).trans hay

theorem original_component_covering_quaternion_sylow_position
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (Q : Sylow 2 (originalComponentPreimage n S e K)) :
    let xK : K := ⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩
    let A := originalQuaternionSubgroup n S e K Q
    ∃ (P : Sylow 2 K) (hxP : xK ∈ P) (g : G)
      (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S),
      A ≤ P ∧
      g * wreathModelHom S e (Original.x (2 ^ n)) * g⁻¹ =
        wreathModelHom S e (Original.x (2 ^ n)) ∧
      (A.map K.subtype).map (MulAut.conj g).toMonoidHom = modelY S e ∧
      let i := positionedSylowEmbedding S e K P g hPS
      Function.Injective i ∧ Original.Y (2 ^ n) ≤ i.range ∧
        i ⟨xK, hxP⟩ = Original.x (2 ^ n) ∧
        ∀ p : P, wreathModelHom S e (i p) = g * ((p : K) : G) * g⁻¹ := by
  let xK : K := ⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩
  let A := originalQuaternionSubgroup n S e K Q
  have hxA : xK ∈ A := originalQuaternionSubgroup_involution_mem
    hnonab n hn S e hfour K hxK Q
  have hA0 : wreathModelHom S e (Original.x (2 ^ n)) ∈ A.map K.subtype :=
    Subgroup.mem_map.mpr ⟨xK, hxA, rfl⟩
  obtain ⟨P, hAP, g, hfix, hPS, hAg⟩ := quaternion_subgroup_positions_actual_sylow
    n hn S e K A
    (originalQuaternionSubgroup_quaternion hnonab n hn S e hfour K hcover Q) hA0
  have hxP : xK ∈ P := hAP hxA
  refine ⟨P, hxP, g, hPS, hAP, hfix, hAg,
    positionedSylowEmbedding_injective S e K P g hPS,
    positionedSylowEmbedding_covers_original_Y n S e K P g hPS A hAP hAg, ?_,
    positionedSylowEmbedding_ambient S e K P g hPS⟩
  apply wreathModelHom_injective S e
  exact (positionedSylowEmbedding_ambient S e K P g hPS ⟨xK, hxP⟩).trans hfix

end CFSG.Wreathed.SmallerRecognitionOriginalField
