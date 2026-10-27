module

public import CFSG.CharacterTheory.Wreathed.CentralizerFullQuotient

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u v

variable {G : Type u} [Group G]

theorem centralizer_normal_index_eq_transferKernel [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal]
    (hK : K.index = 2 ^ n) : K = centralizerTransferKernel n hn S e := by
  have hquot : IsPGroup 2 (involutionCentralizer n S e ⧸ K) :=
    IsPGroup.of_card (K.index_eq_card.symm.trans hK)
  have htrivial := centralizerTransferKernel_hom_to_two_group_eq_one hnonab n hn S e
    hquot ((QuotientGroup.mk' K).comp (centralizerTransferKernel n hn S e).subtype)
  have hle : centralizerTransferKernel n hn S e ≤ K := by
    intro k hk
    apply (QuotientGroup.eq_one_iff (N := K) k).mp
    exact congrArg (fun f : centralizerTransferKernel n hn S e →*
      (involutionCentralizer n S e ⧸ K) => f ⟨k, hk⟩) htrivial
  have hcard : Nat.card K = Nat.card (centralizerTransferKernel n hn S e) := by
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ n)
    calc
      Nat.card K * 2 ^ n = Nat.card (involutionCentralizer n S e) :=
        hK ▸ K.card_mul_index
      _ = Nat.card (centralizerTransferKernel n hn S e) * 2 ^ n := by
        rw [← centralizerTransferKernel_index hnonab n hn S e]
        exact (centralizerTransferKernel n hn S e).card_mul_index.symm
  exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

@[expose] def centralizerArbitraryKernelEquiv [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    K ≃* centralizerTransferKernel n hn S e :=
  MulEquiv.subgroupCongr (centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK)

theorem centralizerArbitraryKernelEquiv_coe [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) (k : K) :
    (centralizerArbitraryKernelEquiv hnonab n hn S e K hK k : involutionCentralizer n S e) = k := rfl

theorem centralizerArbitraryKernelEquiv_symm_coe [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n)
    (k : centralizerTransferKernel n hn S e) :
    ((centralizerArbitraryKernelEquiv hnonab n hn S e K hK).symm k : involutionCentralizer n S e) = k := rfl

@[expose] def centralizerArbitraryKernelQuotientEquiv [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    involutionCentralizer n S e ⧸ K ≃* Multiplicative (ZMod (2 ^ n)) :=
  (QuotientGroup.quotientMulEquivOfEq
    (centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK)).trans
      (centralizerTransferQuotientEquiv hnonab n hn S e)

theorem centralizerArbitraryKernelQuotientEquiv_mk [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n)
    (g : involutionCentralizer n S e) :
    centralizerArbitraryKernelQuotientEquiv hnonab n hn S e K hK (QuotientGroup.mk' K g) =
      centralizerTransferQuotientEquiv hnonab n hn S e
        (QuotientGroup.mk' (centralizerTransferKernel n hn S e) g) := by
  exact congrArg (centralizerTransferQuotientEquiv hnonab n hn S e)
    (QuotientGroup.quotientMulEquivOfEq_mk
      (centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK) g)

theorem centralizerOddCore_le_arbitraryKernel [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    centralizerOddCore n S e ≤ K := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  exact centralizerOddCore_le_transferKernel n hn S e

theorem centralizerArbitraryKernel_oddCore_map [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    (CFSG.oddCore K).map K.subtype = centralizerOddCore n S e := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  exact centralizerTransferKernel_oddCore_map n hn S e

theorem centralizerArbitraryKernel_oddCore_eq_subgroupOf [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    CFSG.oddCore K = (centralizerOddCore n S e).subgroupOf K := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  exact centralizerTransferKernel_oddCore_eq_subgroupOf n hn S e

theorem centralizerArbitraryKernel_oddCore_ambient [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    (CFSG.oddCore K).map ((involutionCentralizer n S e).subtype.comp K.subtype) =
      (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype := by
  rw [← Subgroup.map_map, centralizerArbitraryKernel_oddCore_map hnonab n hn S e K hK]

theorem centralizerArbitraryKernel_inf_sylow [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    K ⊓ (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) =
      centralizerQuaternion n hn S e := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  exact centralizerTransferKernel_inf_eq_quaternion hnonab n hn S e

theorem centralizerArbitraryKernel_ambient_intersection [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    K.map (involutionCentralizer n S e).subtype ⊓ (S : Subgroup G) = modelY S e := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  exact (wreathed_involution_centralizer_quaternion_two_residual hnonab n hn S e).ambient_intersection

theorem centralizerQuaternion_le_arbitraryKernel [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    centralizerQuaternion n hn S e ≤ K := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  exact centralizerQuaternion_le_transferKernel hnonab n hn S e

theorem centralizerArbitraryKernel_sylow [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    ∃ P : Sylow 2 K, (P : Subgroup K) = (centralizerQuaternion n hn S e).subgroupOf K := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  exact centralizerTransferKernel_sylow hnonab n hn S e

theorem centralizerArbitraryKernel_no_index_two [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    ∀ M : Subgroup K, M.index ≠ 2 := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  exact centralizerTransferKernel_no_index_two hnonab n hn S e

theorem centralizerArbitraryKernel_hom_to_two_group_eq_one [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n)
    {P : Type v} [Group P] [Finite P] (hP : IsPGroup 2 P) (f : K →* P) : f = 1 :=
  hom_to_two_group_eq_one_of_no_index_two
    (centralizerArbitraryKernel_no_index_two hnonab n hn S e K hK) hP f

@[expose] def centralizerArbitraryResidualImage (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) :
    Subgroup (centralizerOddCoreQuotient n S e) := K.map (centralizerOddCoreMap n S e)

instance centralizerArbitraryResidualImage_normal (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] :
    (centralizerArbitraryResidualImage n S e K).Normal :=
  Subgroup.Normal.map inferInstance _ (centralizerOddCoreMap_surjective n S e)

@[expose] def centralizerArbitraryResidualMap (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) :
    K →* centralizerArbitraryResidualImage n S e K :=
  (centralizerOddCoreMap n S e).subgroupMap K

theorem centralizerArbitraryResidualMap_coe (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) (k : K) :
    (centralizerArbitraryResidualMap n S e K k : centralizerOddCoreQuotient n S e) =
      centralizerOddCoreMap n S e (k : involutionCentralizer n S e) := rfl

theorem centralizerArbitraryResidualMap_comp (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) :
    (centralizerArbitraryResidualImage n S e K).subtype.comp (centralizerArbitraryResidualMap n S e K) =
      (centralizerOddCoreMap n S e).comp K.subtype := rfl

theorem centralizerArbitraryResidualMap_surjective (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) :
    Function.Surjective (centralizerArbitraryResidualMap n S e K) :=
  (centralizerOddCoreMap n S e).subgroupMap_surjective K

theorem centralizerArbitraryResidualMap_ker_subgroupOf (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) :
    (centralizerArbitraryResidualMap n S e K).ker = (centralizerOddCore n S e).subgroupOf K := by
  ext k
  change centralizerArbitraryResidualMap n S e K k = 1 ↔
    (k : involutionCentralizer n S e) ∈ centralizerOddCore n S e
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

theorem centralizerArbitraryResidualMap_ker [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    (centralizerArbitraryResidualMap n S e K).ker = CFSG.oddCore K := by
  rw [centralizerArbitraryResidualMap_ker_subgroupOf,
    centralizerArbitraryKernel_oddCore_eq_subgroupOf hnonab n hn S e K hK]

@[expose] def centralizerArbitraryResidualQuotientEquiv [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    K ⧸ CFSG.oddCore K ≃* centralizerArbitraryResidualImage n S e K :=
  QuotientGroup.liftEquiv (CFSG.oddCore K) (centralizerArbitraryResidualMap_surjective n S e K)
    (centralizerArbitraryResidualMap_ker hnonab n hn S e K hK).symm

theorem centralizerArbitraryResidualQuotientEquiv_mk [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) (k : K) :
    centralizerArbitraryResidualQuotientEquiv hnonab n hn S e K hK
      (QuotientGroup.mk' (CFSG.oddCore K) k) = centralizerArbitraryResidualMap n S e K k := rfl

theorem centralizerArbitraryResidualQuotientEquiv_coe [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) (k : K) :
    (centralizerArbitraryResidualQuotientEquiv hnonab n hn S e K hK
      (QuotientGroup.mk' (CFSG.oddCore K) k) : centralizerOddCoreQuotient n S e) =
        centralizerOddCoreMap n S e (k : involutionCentralizer n S e) := rfl

theorem centralizerArbitraryResidualImage_eq [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    centralizerArbitraryResidualImage n S e K = centralizerResidualImage n hn S e := by
  rw [centralizerArbitraryResidualImage,
    centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  rfl

theorem centralizerArbitraryResidualImage_index [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    (centralizerArbitraryResidualImage n S e K).index = 2 ^ n := by
  rw [centralizerArbitraryResidualImage_eq hnonab n hn S e K hK]
  exact centralizerResidualImage_index hnonab n hn S e

theorem centralizerArbitraryResidualImage_oddCore_eq_bot [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    CFSG.oddCore (centralizerArbitraryResidualImage n S e K) = ⊥ := by
  rw [centralizerArbitraryResidualImage_eq hnonab n hn S e K hK]
  exact centralizerResidualImage_oddCore_eq_bot n hn S e

theorem centralizerArbitraryResidualImage_no_index_two [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    ∀ M : Subgroup (centralizerArbitraryResidualImage n S e K), M.index ≠ 2 := by
  intro M hM
  apply centralizerArbitraryKernel_no_index_two hnonab n hn S e K hK
    (M.comap (centralizerArbitraryResidualMap n S e K))
  exact (M.index_comap_of_surjective (centralizerArbitraryResidualMap_surjective n S e K)).trans hM

theorem centralizerArbitraryResidualImage_hom_to_two_group_eq_one [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n)
    {P : Type v} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (f : centralizerArbitraryResidualImage n S e K →* P) : f = 1 :=
  hom_to_two_group_eq_one_of_no_index_two
    (centralizerArbitraryResidualImage_no_index_two hnonab n hn S e K hK) hP f


@[expose] def centralizerArbitraryResidualEquiv [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    centralizerArbitraryResidualImage n S e K ≃* centralizerResidualImage n hn S e :=
  MulEquiv.subgroupCongr (centralizerArbitraryResidualImage_eq hnonab n hn S e K hK)

theorem centralizerArbitraryResidualEquiv_coe [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n)
    (t : centralizerArbitraryResidualImage n S e K) :
    (centralizerArbitraryResidualEquiv hnonab n hn S e K hK t : centralizerOddCoreQuotient n S e) = t := rfl

theorem centralizerArbitraryResidualMap_transport [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) (k : K) :
    centralizerArbitraryResidualEquiv hnonab n hn S e K hK (centralizerArbitraryResidualMap n S e K k) =
      centralizerResidualMap n hn S e (centralizerArbitraryKernelEquiv hnonab n hn S e K hK k) := rfl

theorem centralizerArbitraryResidualImage_sylow [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    ∃ P : Sylow 2 (centralizerArbitraryResidualImage n S e K),
      (P : Subgroup (centralizerArbitraryResidualImage n S e K)).map
        (centralizerArbitraryResidualImage n S e K).subtype =
          (centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e) := by
  rw [centralizerArbitraryResidualImage_eq hnonab n hn S e K hK]
  exact ⟨centralizerResidualSylow hnonab n hn S e, centralizerResidualSylow_image hnonab n hn S e⟩

theorem centralizerArbitraryResidualImage_involution_mem [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    centralizerOddCoreMap n S e (centralInvolution n S e) ∈
      centralizerArbitraryResidualImage n S e K := by
  rw [centralizerArbitraryResidualImage_eq hnonab n hn S e K hK]
  exact (centralizerResidualInvolution hnonab n hn S e).property

theorem centralizerArbitraryResidualImage_unique_involution [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n)
    (y : centralizerOddCoreQuotient n S e) (hy : y ∈ centralizerArbitraryResidualImage n S e K)
    (horder : orderOf y = 2) : y = centralizerOddCoreMap n S e (centralInvolution n S e) := by
  rw [centralizerArbitraryResidualImage_eq hnonab n hn S e K hK] at hy
  exact centralizerResidualImage_unique_involution_ambient hnonab n hn S e y hy horder

theorem centralizerFullCenter_inf_arbitraryKernel [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    centralizerFullCenter n hn S e ⊓ K = Subgroup.zpowers (centralInvolution n S e) := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  exact centralizerFullCenter_inf_transferKernel hnonab n hn S e

theorem centralizerFullCenterImage_inf_arbitraryResidualImage [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    centralizerFullCenterImage n hn S e ⊓ centralizerArbitraryResidualImage n S e K =
      Subgroup.zpowers (centralizerOddCoreMap n S e (centralInvolution n S e)) := by
  rw [centralizerArbitraryResidualImage_eq hnonab n hn S e K hK]
  exact centralizerFullCenterImage_inf_residualImage hnonab n hn S e

theorem centralizerFullCenterImage_inf_arbitraryResidualImage_card [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    Nat.card (centralizerFullCenterImage n hn S e ⊓ centralizerArbitraryResidualImage n S e K :
      Subgroup (centralizerOddCoreQuotient n S e)) = 2 := by
  rw [centralizerArbitraryResidualImage_eq hnonab n hn S e K hK]
  exact centralizerFullCenterImage_inf_residualImage_card hnonab n hn S e

theorem centralizerFullCenterImage_sup_arbitraryResidualImage_index [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    (centralizerFullCenterImage n hn S e ⊔ centralizerArbitraryResidualImage n S e K).index = 2 := by
  rw [centralizerArbitraryResidualImage_eq hnonab n hn S e K hK]
  exact centralizerFullCenterImage_sup_residualImage_index hnonab n hn S e

@[expose] def centralizerArbitraryDihedralImage [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) : Subgroup (centralizerFullQuotient n hn S e) :=
  (centralizerArbitraryResidualImage n S e K).map (centralizerFullQuotientMap n hn S e)

instance centralizerArbitraryDihedralImage_normal [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] :
    (centralizerArbitraryDihedralImage n hn S e K).Normal :=
  Subgroup.Normal.map inferInstance _ (centralizerFullQuotientMap_surjective n hn S e)

@[expose] def centralizerArbitraryDihedralImageMap [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) :
    centralizerArbitraryResidualImage n S e K →* centralizerArbitraryDihedralImage n hn S e K :=
  (centralizerFullQuotientMap n hn S e).subgroupMap (centralizerArbitraryResidualImage n S e K)

theorem centralizerArbitraryDihedralImageMap_coe [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) (t : centralizerArbitraryResidualImage n S e K) :
    (centralizerArbitraryDihedralImageMap n hn S e K t : centralizerFullQuotient n hn S e) =
      centralizerFullQuotientMap n hn S e (t : centralizerOddCoreQuotient n S e) := rfl

theorem centralizerArbitraryDihedralImageMap_comp [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) :
    (centralizerArbitraryDihedralImage n hn S e K).subtype.comp
      (centralizerArbitraryDihedralImageMap n hn S e K) =
        (centralizerFullQuotientMap n hn S e).comp (centralizerArbitraryResidualImage n S e K).subtype := rfl

theorem centralizerArbitraryDihedralImageMap_surjective [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) :
    Function.Surjective (centralizerArbitraryDihedralImageMap n hn S e K) :=
  (centralizerFullQuotientMap n hn S e).subgroupMap_surjective _

theorem centralizerArbitraryDihedralImageMap_ker [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) :
    (centralizerArbitraryDihedralImageMap n hn S e K).ker =
      (centralizerFullCenterImage n hn S e).subgroupOf (centralizerArbitraryResidualImage n S e K) := by
  ext t
  change centralizerArbitraryDihedralImageMap n hn S e K t = 1 ↔
    (t : centralizerOddCoreQuotient n S e) ∈ centralizerFullCenterImage n hn S e
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

theorem centralizerArbitraryDihedralImageMap_kernel_image [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    (centralizerArbitraryDihedralImageMap n hn S e K).ker.map
      (centralizerArbitraryResidualImage n S e K).subtype =
        Subgroup.zpowers (centralizerOddCoreMap n S e (centralInvolution n S e)) := by
  rw [centralizerArbitraryDihedralImageMap_ker, Subgroup.subgroupOf_map_subtype,
    centralizerFullCenterImage_inf_arbitraryResidualImage hnonab n hn S e K hK]

@[expose] def centralizerArbitraryDihedralQuotientEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) :
    centralizerArbitraryResidualImage n S e K ⧸
      (centralizerFullCenterImage n hn S e).subgroupOf (centralizerArbitraryResidualImage n S e K) ≃*
        centralizerArbitraryDihedralImage n hn S e K :=
  QuotientGroup.liftEquiv _ (centralizerArbitraryDihedralImageMap_surjective n hn S e K)
    (centralizerArbitraryDihedralImageMap_ker n hn S e K).symm

theorem centralizerArbitraryDihedralQuotientEquiv_mk [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) (t : centralizerArbitraryResidualImage n S e K) :
    centralizerArbitraryDihedralQuotientEquiv n hn S e K
      (QuotientGroup.mk' ((centralizerFullCenterImage n hn S e).subgroupOf
        (centralizerArbitraryResidualImage n S e K)) t) =
          centralizerArbitraryDihedralImageMap n hn S e K t := rfl

theorem centralizerArbitraryDihedralQuotientEquiv_coe [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) (t : centralizerArbitraryResidualImage n S e K) :
    (centralizerArbitraryDihedralQuotientEquiv n hn S e K
      (QuotientGroup.mk' ((centralizerFullCenterImage n hn S e).subgroupOf
        (centralizerArbitraryResidualImage n S e K)) t) : centralizerFullQuotient n hn S e) =
          centralizerFullQuotientMap n hn S e (t : centralizerOddCoreQuotient n S e) := rfl

theorem centralizerArbitraryDihedralImage_eq [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    centralizerArbitraryDihedralImage n hn S e K = centralizerDihedralImage n hn S e := by
  rw [centralizerArbitraryDihedralImage, centralizerArbitraryResidualImage_eq hnonab n hn S e K hK]
  rfl

theorem centralizerArbitraryDihedralImage_index [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    (centralizerArbitraryDihedralImage n hn S e K).index = 2 := by
  rw [centralizerArbitraryDihedralImage_eq hnonab n hn S e K hK]
  exact centralizerDihedralImage_index hnonab n hn S e

theorem centralizerArbitraryDihedralImage_oddCore_eq_bot [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    CFSG.oddCore (centralizerArbitraryDihedralImage n hn S e K) = ⊥ := by
  rw [centralizerArbitraryDihedralImage_eq hnonab n hn S e K hK]
  exact centralizerDihedralImage_oddCore_eq_bot n hn S e

theorem centralizerArbitraryDihedralImage_hom_to_two_group_eq_one [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n)
    {P : Type v} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (f : centralizerArbitraryDihedralImage n hn S e K →* P) : f = 1 :=
  hom_to_two_group_eq_one_of_surjective (centralizerArbitraryDihedralImageMap n hn S e K)
    (centralizerArbitraryDihedralImageMap_surjective n hn S e K)
    (centralizerArbitraryResidualImage_no_index_two hnonab n hn S e K hK) hP f


theorem centralizerArbitraryDihedralImage_sylow [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    ∃ P : Sylow 2 (centralizerArbitraryDihedralImage n hn S e K),
      (P : Subgroup (centralizerArbitraryDihedralImage n hn S e K)).map
        (centralizerArbitraryDihedralImage n hn S e K).subtype =
          ((centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e)).map
            (centralizerFullQuotientMap n hn S e) ∧
      Nonempty (P ≃* DihedralGroup (2 ^ n / 2)) ∧ Nat.card P = 2 ^ n ∧
        (n = 2 → IsKleinFour P) := by
  rw [centralizerArbitraryDihedralImage_eq hnonab n hn S e K hK]
  exact (wreathed_centralizer_full_center_dihedral_quotient.{u, u} hnonab n hn S e).residual_dihedral_sylow

@[expose] def centralizerArbitraryDihedralEquiv [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    centralizerArbitraryDihedralImage n hn S e K ≃* centralizerDihedralImage n hn S e :=
  MulEquiv.subgroupCongr (centralizerArbitraryDihedralImage_eq hnonab n hn S e K hK)

theorem centralizerArbitraryDihedralEquiv_coe [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n)
    (j : centralizerArbitraryDihedralImage n hn S e K) :
    (centralizerArbitraryDihedralEquiv hnonab n hn S e K hK j : centralizerFullQuotient n hn S e) = j := rfl

theorem centralizerArbitraryDihedralImageMap_transport [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n)
    (t : centralizerArbitraryResidualImage n S e K) :
    centralizerArbitraryDihedralEquiv hnonab n hn S e K hK
      (centralizerArbitraryDihedralImageMap n hn S e K t) =
        centralizerDihedralImageMap n hn S e (centralizerArbitraryResidualEquiv hnonab n hn S e K hK t) := rfl

theorem centralizerArbitraryDihedralImageMap_comp_residual_coe [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) (k : K) :
    (centralizerArbitraryDihedralImageMap n hn S e K (centralizerArbitraryResidualMap n S e K k) :
      centralizerFullQuotient n hn S e) =
        centralizerFullQuotientMap n hn S e (centralizerOddCoreMap n S e (k : involutionCentralizer n S e)) := rfl

theorem centralizerArbitraryKernel_map_eq_residualImage [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    K.map (centralizerOddCoreMap n S e) = centralizerResidualImage n hn S e :=
  centralizerArbitraryResidualImage_eq hnonab n hn S e K hK

theorem centralizerArbitraryKernel_map_map_eq_dihedralImage [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    (K.map (centralizerOddCoreMap n S e)).map (centralizerFullQuotientMap n hn S e) =
      centralizerDihedralImage n hn S e :=
  centralizerArbitraryDihedralImage_eq hnonab n hn S e K hK

structure WreathedArbitraryCentralizerQuaternionResidualData [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) : Prop where
  actual_sylow : (centralizerSylow n hn S e :
    Subgroup (involutionCentralizer n S e)).map (involutionCentralizer n S e).subtype = S
  kernel_normal : K.Normal
  kernel_index : K.index = 2 ^ n
  kernel_intersection : K ⊓
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) =
      centralizerQuaternion n hn S e
  ambient_quaternion : (centralizerQuaternion n hn S e).map
    (involutionCentralizer n S e).subtype = modelY S e
  ambient_intersection : (K.map
    (involutionCentralizer n S e).subtype) ⊓ (S : Subgroup G) = modelY S e
  quaternion_sylow : ∃ T : Sylow 2 K,
    (T : Subgroup K) =
      (centralizerQuaternion n hn S e).subgroupOf K
  quaternion : Nonempty (QuaternionGroup (2 ^ n / 2) ≃* centralizerQuaternion n hn S e)
  quaternion_order : Nat.card (centralizerQuaternion n hn S e) = 2 * 2 ^ n
  no_index_two : ∀ M : Subgroup K, M.index ≠ 2
  full_center_weak_closure : ∀ u g : G, u ∈ modelCenter S e →
    g ∈ involutionCentralizer n S e → g⁻¹ * u * g ∈ (S : Subgroup G) → g⁻¹ * u * g = u
  base_normalizer_order :
    Nat.card (Subgroup.normalizer
      (modelBase (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
        Set (involutionCentralizer n S e)) ⧸
      (Subgroup.centralizer
        (modelBase (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
          Set (involutionCentralizer n S e))).subgroupOf
        (Subgroup.normalizer
          (modelBase (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
            Set (involutionCentralizer n S e)))) = 2
  ambient_v_normalizer : Subgroup.normalizer (modelV S e : Set G) ≤
    involutionCentralizer n S e
  centralizer_v_normalizer : Nonempty (Subgroup.normalizer
    (modelV (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
      Set (involutionCentralizer n S e)) ⧸
    modelVInnerCentralizer (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) ≃*
      Equiv.Perm (Fin 3))

theorem wreathed_arbitrary_centralizer_quaternion_two_residual [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    WreathedArbitraryCentralizerQuaternionResidualData n hn S e K := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  have h := wreathed_involution_centralizer_quaternion_two_residual hnonab n hn S e
  exact ⟨h.actual_sylow, h.kernel_normal, h.kernel_index, h.kernel_intersection,
    h.ambient_quaternion, h.ambient_intersection, h.quaternion_sylow,
    h.quaternion, h.quaternion_order, h.no_index_two, h.full_center_weak_closure,
    h.base_normalizer_order, h.ambient_v_normalizer, h.centralizer_v_normalizer⟩

structure WreathedArbitraryCentralizerKernelOddCoreData [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) : Prop where
  ambient_odd_core_le_kernel : centralizerOddCore n S e ≤ K
  kernel_odd_core_image : (CFSG.oddCore K).map
    K.subtype = centralizerOddCore n S e
  kernel_odd_core : CFSG.oddCore K =
    (centralizerOddCore n S e).subgroupOf K
  residual_normal : (centralizerArbitraryResidualImage n S e K).Normal
  residual_index : (centralizerArbitraryResidualImage n S e K).index = 2 ^ n
  actual_surjection : Function.Surjective (centralizerArbitraryResidualMap n S e K)
  actual_kernel : (centralizerArbitraryResidualMap n S e K).ker =
    CFSG.oddCore K
  actual_quotient : Nonempty (K ⧸
    CFSG.oddCore K ≃* centralizerArbitraryResidualImage n S e K)
  residual_corefree : CFSG.oddCore (centralizerArbitraryResidualImage n S e K) = ⊥
  quaternion_sylow : ∃ P : Sylow 2 (centralizerArbitraryResidualImage n S e K),
    (P : Subgroup (centralizerArbitraryResidualImage n S e K)).map
      (centralizerArbitraryResidualImage n S e K).subtype =
        (centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e)
  quaternion_image : Nonempty (QuaternionGroup (2 ^ n / 2) ≃*
    (centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e))
  quaternion_image_order : Nat.card ((centralizerQuaternion n hn S e).map
    (centralizerOddCoreMap n S e)) = 2 * 2 ^ n
  involution_mem : centralizerOddCoreMap n S e (centralInvolution n S e) ∈
    centralizerArbitraryResidualImage n S e K
  involution_central : centralizerOddCoreMap n S e (centralInvolution n S e) ∈
    Subgroup.center (centralizerOddCoreQuotient n S e)
  involution_order : orderOf (centralizerOddCoreMap n S e (centralInvolution n S e)) = 2
  unique_involution : ∀ y : centralizerOddCoreQuotient n S e,
    y ∈ centralizerArbitraryResidualImage n S e K → orderOf y = 2 →
      y = centralizerOddCoreMap n S e (centralInvolution n S e)

theorem wreathed_arbitrary_centralizer_kernel_odd_core_data [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    WreathedArbitraryCentralizerKernelOddCoreData n hn S e K := by
  rw [centralizer_normal_index_eq_transferKernel hnonab n hn S e K hK]
  have h := wreathed_centralizer_kernel_odd_core_data hnonab n hn S e
  exact ⟨h.ambient_odd_core_le_kernel, h.kernel_odd_core_image, h.kernel_odd_core,
    h.residual_normal, h.residual_index, h.actual_surjection, h.actual_kernel, h.actual_quotient,
    h.residual_corefree, h.quaternion_sylow, h.quaternion_image, h.quaternion_image_order,
    h.involution_mem, h.involution_central, h.involution_order, h.unique_involution⟩

structure WreathedArbitraryCentralizerFullQuotientData [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) : Prop where
  full_center : WreathedCentralizerFullCenterData n hn S e
  quaternion_residual : WreathedArbitraryCentralizerQuaternionResidualData n hn S e K
  kernel_odd_core : WreathedArbitraryCentralizerKernelOddCoreData n hn S e K
  center_residual_intersection :
    centralizerFullCenterImage n hn S e ⊓ centralizerArbitraryResidualImage n S e K =
      Subgroup.zpowers (centralizerOddCoreMap n S e (centralInvolution n S e))
  center_residual_product_index :
    (centralizerFullCenterImage n hn S e ⊔ centralizerArbitraryResidualImage n S e K).index = 2
  quotient_residual_normal : (centralizerArbitraryDihedralImage n hn S e K).Normal
  quotient_residual_index : (centralizerArbitraryDihedralImage n hn S e K).index = 2
  quotient_corefree : CFSG.oddCore (centralizerFullQuotient n hn S e) = ⊥
  quotient_residual_corefree : CFSG.oddCore (centralizerArbitraryDihedralImage n hn S e K) = ⊥
  kernel_two_group_homs : ∀ {P : Type v} [Group P] [Finite P], IsPGroup 2 P →
    ∀ f : K →* P, f = 1
  residual_two_group_homs : ∀ {P : Type v} [Group P] [Finite P], IsPGroup 2 P →
    ∀ f : centralizerArbitraryResidualImage n S e K →* P, f = 1
  quotient_residual_two_group_homs : ∀ {P : Type v} [Group P] [Finite P], IsPGroup 2 P →
    ∀ f : centralizerArbitraryDihedralImage n hn S e K →* P, f = 1
  quotient_dihedral_sylow : ∃ P : Sylow 2 (centralizerFullQuotient n hn S e),
    (P : Subgroup (centralizerFullQuotient n hn S e)) =
      (centralizerOddCoreSylow n hn S e : Subgroup (centralizerOddCoreQuotient n S e)).map
        (centralizerFullQuotientMap n hn S e) ∧
    Nonempty (P ≃* DihedralGroup (2 ^ n)) ∧ Nat.card P = 2 * 2 ^ n
  residual_dihedral_sylow : ∃ P : Sylow 2 (centralizerArbitraryDihedralImage n hn S e K),
    (P : Subgroup (centralizerArbitraryDihedralImage n hn S e K)).map
      (centralizerArbitraryDihedralImage n hn S e K).subtype =
        ((centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e)).map
          (centralizerFullQuotientMap n hn S e) ∧
    Nonempty (P ≃* DihedralGroup (2 ^ n / 2)) ∧ Nat.card P = 2 ^ n ∧
      (n = 2 → IsKleinFour P)

theorem wreathed_arbitrary_centralizer_full_center_dihedral_quotient [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup (involutionCentralizer n S e)) [K.Normal] (hK : K.index = 2 ^ n) :
    WreathedArbitraryCentralizerFullQuotientData.{u, v} n hn S e K := by
  have h := wreathed_centralizer_full_center_dihedral_quotient.{u, v} hnonab n hn S e
  refine ⟨h.full_center,
    wreathed_arbitrary_centralizer_quaternion_two_residual hnonab n hn S e K hK,
    wreathed_arbitrary_centralizer_kernel_odd_core_data hnonab n hn S e K hK,
    centralizerFullCenterImage_inf_arbitraryResidualImage hnonab n hn S e K hK,
    centralizerFullCenterImage_sup_arbitraryResidualImage_index hnonab n hn S e K hK,
    inferInstance, centralizerArbitraryDihedralImage_index hnonab n hn S e K hK,
    h.quotient_corefree, centralizerArbitraryDihedralImage_oddCore_eq_bot hnonab n hn S e K hK,
    ?_, ?_, ?_, h.quotient_dihedral_sylow,
    centralizerArbitraryDihedralImage_sylow hnonab n hn S e K hK⟩
  · intro P _ _ hP f
    exact centralizerArbitraryKernel_hom_to_two_group_eq_one hnonab n hn S e K hK hP f
  · intro P _ _ hP f
    exact centralizerArbitraryResidualImage_hom_to_two_group_eq_one hnonab n hn S e K hK hP f
  · intro P _ _ hP f
    exact centralizerArbitraryDihedralImage_hom_to_two_group_eq_one hnonab n hn S e K hK hP f

end CFSG.Wreathed
