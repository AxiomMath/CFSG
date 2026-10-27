module
public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalAlternative
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionPosition
public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open CFSG.Assembly.LowTwoRank
open scoped Classical Pointwise

theorem proper_position_original_factorization
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (P : Sylow 2 K)
    (hxP : (⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K) ∈ P)
    (g : G)
    (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S)
    (hY : Original.Y (2 ^ n) ≤ (positionedSylowEmbedding S e K P g hPS).range)
    (hproper : (positionedSylowEmbedding S e K P g hPS).range < ⊤)
    (hx : positionedSylowEmbedding S e K P g hPS
      ⟨(⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K), hxP⟩ =
        Original.x (2 ^ n)) :
    (K : Set G) = ((CFSG.oddCore K).map K.subtype : Set G) *
      (K ⊓ involutionCentralizer n S e : Set G) ∧
    QuotientGroup.mk' (CFSG.oddCore K)
      (⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K) ∈
        Subgroup.center (K ⧸ CFSG.oddCore K) := by
  let xK : K := ⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩
  let xP : P := ⟨xK, hxP⟩
  obtain ⟨_, hfac, hquot⟩ :=
    proper_quaternion_wreath_overgroup_Sylow_forces_centralizer_factorization
      n hn P (positionedSylowEmbedding S e K P g hPS)
        (positionedSylowEmbedding_injective S e K P g hPS) hY hproper xP hx
  have hcentralizer : Subgroup.centralizer ({xK} : Set K) =
      (involutionCentralizer n S e).subgroupOf K := by
    ext k
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hk
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg K.subtype hk
    · intro hk
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hk
  have hfactor : CFSG.oddCore K ⊔ (involutionCentralizer n S e).subgroupOf K = ⊤ := by
    apply (Subgroup.eq_top_iff' _).mpr
    intro k
    obtain ⟨o, ho, c, hc, rfl⟩ := hfac k
    rw [hcentralizer] at hc
    exact Subgroup.mul_mem_sup ho hc
  exact ⟨FullSylowCoveringObstruction.internal_odd_core_factorization_iff_ambient_product.mp
    hfactor, hquot⟩

theorem proper_position_original_core_intersection
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (hfactor : (K : Set G) = ((CFSG.oddCore K).map K.subtype : Set G) *
      (K ⊓ involutionCentralizer n S e : Set G)) :
    (CFSG.oddCore K).map K.subtype ⊓ involutionCentralizer n S e =
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓ K := by
  have hnormal : (ComponentCoveringLocal.originalImage n S e K).Normal :=
    Subgroup.Normal.of_commutator_le _
      ((ComponentCoveringLocal.original_derived_eq_layer hnonab n hn S e hfour
        p f hp hpodd hf hlocal).le.trans hcover)
  exact ComponentCoveringLocal.component_factorization_core_intersection
    K (involutionCentralizer n S e)
    (ComponentCoveringLocal.original_centralizer_odd_core_eq_kernel n S e K hnormal)
    (FullSylowCoveringObstruction.internal_odd_core_factorization_iff_ambient_product.mpr hfactor)

theorem proper_position_original_factorization_and_intersection
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (P : Sylow 2 K)
    (hxP : (⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K) ∈ P)
    (g : G)
    (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S)
    (hY : Original.Y (2 ^ n) ≤ (positionedSylowEmbedding S e K P g hPS).range)
    (hproper : (positionedSylowEmbedding S e K P g hPS).range < ⊤)
    (hx : positionedSylowEmbedding S e K P g hPS
      ⟨(⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K), hxP⟩ =
        Original.x (2 ^ n)) :
    (K : Set G) = ((CFSG.oddCore K).map K.subtype : Set G) *
      (K ⊓ involutionCentralizer n S e : Set G) ∧
    QuotientGroup.mk' (CFSG.oddCore K)
      (⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K) ∈
        Subgroup.center (K ⧸ CFSG.oddCore K) ∧
    (CFSG.oddCore K).map K.subtype ⊓ involutionCentralizer n S e =
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓ K := by
  obtain ⟨hfactor, hcenter⟩ := proper_position_original_factorization
    n hn S e K hxK P hxP g hPS hY hproper hx
  exact ⟨hfactor, hcenter, proper_position_original_core_intersection
    hnonab n hn S e hfour p f hp hpodd hf hlocal K hcover hfactor⟩

theorem proper_position_original_element_factorization
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K)
    (P : Sylow 2 K)
    (hxP : (⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K) ∈ P)
    (g : G)
    (hPS : ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ≤ S)
    (hY : Original.Y (2 ^ n) ≤ (positionedSylowEmbedding S e K P g hPS).range)
    (hproper : (positionedSylowEmbedding S e K P g hPS).range < ⊤)
    (hx : positionedSylowEmbedding S e K P g hPS
      ⟨(⟨wreathModelHom S e (Original.x (2 ^ n)), hxK⟩ : K), hxP⟩ =
        Original.x (2 ^ n)) :
    ∀ k : K, ∃ o ∈ CFSG.oddCore K,
      ∃ c ∈ (involutionCentralizer n S e).subgroupOf K, k = o * c := by
  have hfac := (proper_position_original_factorization
    n hn S e K hxK P hxP g hPS hY hproper hx).1
  have hfactor :=
    FullSylowCoveringObstruction.internal_odd_core_factorization_iff_ambient_product.mpr hfac
  intro k
  have hk : k ∈ CFSG.oddCore K ⊔ (involutionCentralizer n S e).subgroupOf K := by
    rw [hfactor]
    exact Subgroup.mem_top k
  obtain ⟨o, ho, c, hc, hprod⟩ := Subgroup.mem_sup_of_normal_left.mp hk
  exact ⟨o, ho, c, hc, hprod.symm⟩

end CFSG.Wreathed.SmallerRecognitionOriginalField
