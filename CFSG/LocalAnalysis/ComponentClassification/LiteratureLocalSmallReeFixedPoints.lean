module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeWhole
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalOrder504
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeSemilinear
public import CFSG.LieType.Ree.SmallReeRank

public noncomputable section

namespace CFSG.ComponentClassification.LiteratureLocal

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.GorensteinWalter
open scoped MatrixGroups

theorem xOp_apply_hVec (τ : Tag) (R : Type) [CommRing R] (i j : Fin τ.rank) (c : R) :
    xOp τ R i c (hVec τ R j) =
      hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (Pi.single i 1) := by
  change xOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [xOp, Finsupp.linearCombination_single, one_smul]

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

omit [Finite K] in
theorem G2_xElement_zero_ne_xElement_one :
    (xElement ⟨0, by decide⟩ (1 : K) : adjointGroup ReeTag.G2.tag K) ≠
      xElement ⟨1, by decide⟩ 1 := by
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  intro h
  have h1 := congrArg (fun g : adjointGroup ReeTag.G2.tag K =>
    ((g : ModGL ReeTag.G2.tag K) : Module.End K (RootModule ReeTag.G2.tag K))
      (hVec ReeTag.G2.tag K ⟨0, by decide⟩)) h
  change xOp ReeTag.G2.tag K _ 1 (hVec ReeTag.G2.tag K _) =
    xOp ReeTag.G2.tag K _ 1 (hVec ReeTag.G2.tag K _) at h1
  rw [xOp_apply_hVec, xOp_apply_hVec, add_right_inj, rootVec_single_eq, rootVec_single_eq] at h1
  have h2 := congrArg (fun v : RootModule ReeTag.G2.tag K =>
    v (Sum.inr ⟨Pi.single ⟨0, by decide⟩ 1, isRoot_single _ _⟩)) h1
  have hne : (Sum.inr ⟨Pi.single ⟨1, by decide⟩ 1, isRoot_single _ _⟩ :
      Fin ReeTag.G2.tag.rank ⊕ Root ReeTag.G2.tag) ≠
        Sum.inr ⟨Pi.single ⟨0, by decide⟩ 1, isRoot_single _ _⟩ := by
    intro he
    have he' := congrFun (congrArg Subtype.val (Sum.inr.inj he)) ⟨0, by decide⟩
    simp at he'
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h2
  rw [Finsupp.single_apply, ite_eq_right hne, mul_zero] at h2
  have hc : (ReeTag.G2.tag.cartan ⟨0, by decide⟩ ⟨0, by decide⟩).natAbs = 2 := by decide
  rw [hc] at h2
  have h3 : ((2 : ℕ) : K) = 0 := h2
  rw [CharP.cast_eq_zero_iff K 3] at h3
  omega

theorem G2_finiteReeAut_ne_one (a : ℕ) : ReeTag.G2.finiteReeAut K a ≠ 1 := by
  intro h
  have h1 := congrArg (fun F : MulAut (adjointGroup ReeTag.G2.tag K) =>
    F (xElement ⟨0, by decide⟩ (1 : K))) h
  simp only [ReeTag.finiteReeAut, MulAut.mul_apply, ReeTag.finiteFrobeniusAut_pow_xElement,
    one_pow, ReeTag.finiteExceptionalAut_xElement, MulAut.one_apply] at h1
  have hp : ReeTag.G2.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  rw [hp] at h1
  exact G2_xElement_zero_ne_xElement_one h1.symm

theorem G2_orderOf_finiteReeAut (a : ℕ) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    orderOf (ReeTag.G2.finiteReeAut K a) = 2 := by
  apply orderOf_eq_prime
  · refine MulEquiv.ext fun g => ?_
    rw [pow_two, MulAut.mul_apply, ReeTag.finiteReeAut_eq_reeAut,
      ReeTag.reeAut_reeAut ReeTag.G2 a hK, MulAut.one_apply]
  · exact G2_finiteReeAut_ne_one a

theorem G2_card_reeGamma (a : ℕ) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nat.card (ReeTag.G2.reeGamma K a) =
      (3 ^ (2 * a + 1)) ^ 3 * ((3 ^ (2 * a + 1)) ^ 3 + 1) * (3 ^ (2 * a + 1) - 1) := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  rw [h, mul_right_comm]

omit [Field K] [Finite K] [CharP K ReeTag.G2.prime] in
theorem centralizer_commutator_eq_bot {Γ : Type*} [Group Γ] (hZ : Subgroup.center Γ = ⊥)
    (hsimple : IsSimpleGroup (commutator Γ)) (hnab : ∃ x y : commutator Γ, x * y ≠ y * x)
    (hidx : (commutator Γ).index = 3) :
    Subgroup.centralizer ((commutator Γ : Subgroup Γ) : Set Γ) = ⊥ := by
  set D := commutator Γ with hD
  set C := Subgroup.centralizer (D : Set Γ) with hC
  have hZD : Subgroup.center D = ⊥ := by
    rcases (Subgroup.center D).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)
  have hCD : ∀ c ∈ C, c ∈ D → c = 1 := by
    intro c hc hcD
    have hcen : (⟨c, hcD⟩ : D) ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc y y.2)
    rw [hZD, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hCab : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c := by
    intro c hc c' hc'
    have hk : c * c' * c⁻¹ * c'⁻¹ ∈ D :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top c) (Subgroup.mem_top c')
    have hk' : c * c' * c⁻¹ * c'⁻¹ ∈ C :=
      C.mul_mem (C.mul_mem (C.mul_mem hc hc') (C.inv_mem hc)) (C.inv_mem hc')
    have h1 := hCD _ hk' hk
    calc c * c' = (c * c' * c⁻¹ * c'⁻¹) * (c' * c) := by group
      _ = c' * c := by rw [h1, one_mul]
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  by_contra hc1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (Γ ⧸ D) = 3 := by rw [← Subgroup.index]; exact hidx
  have hcD : (c : Γ ⧸ D) ≠ 1 := fun h => hc1 (hCD c hc ((QuotientGroup.eq_one_iff c).mp h))
  have htop := zpowers_eq_top_of_prime_card hcard hcD
  have hcen : c ∈ Subgroup.center Γ := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : (g : Γ ⧸ D) ∈ Subgroup.zpowers (c : Γ ⧸ D) := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hd : (c ^ k)⁻¹ * g ∈ D := by
      rw [← QuotientGroup.eq]
      rw [← hk, QuotientGroup.mk_zpow]
    have hg' : g = c ^ k * ((c ^ k)⁻¹ * g) := by group
    have h1 : c * c ^ k = c ^ k * c := (Commute.self_zpow c k).eq
    have h2 : ((c ^ k)⁻¹ * g) * c = c * ((c ^ k)⁻¹ * g) :=
      Subgroup.mem_centralizer_iff.mp hc _ hd
    rw [hg']
    calc c ^ k * ((c ^ k)⁻¹ * g) * c = c ^ k * (((c ^ k)⁻¹ * g) * c) := by group
      _ = c ^ k * (c * ((c ^ k)⁻¹ * g)) := by rw [h2]
      _ = (c * c ^ k) * ((c ^ k)⁻¹ * g) := by rw [h1]; group
      _ = c * (c ^ k * ((c ^ k)⁻¹ * g)) := by group
  rw [hZ, Subgroup.mem_bot] at hcen
  exact hc1 hcen

omit [Field K] [Finite K] [CharP K ReeTag.G2.prime] in
theorem nonempty_mulEquiv_mulAut_of_centralizer_eq_bot {Γ L : Type*} [Group Γ] [Finite Γ]
    [Group L] [Finite (MulAut L)] (e : commutator Γ ≃* L)
    (hC : Subgroup.centralizer ((commutator Γ : Subgroup Γ) : Set Γ) = ⊥)
    (hcard : Nat.card (MulAut L) ≤ Nat.card Γ) : Nonempty (Γ ≃* MulAut L) := by
  let f : Γ →* MulAut L :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := commutator Γ))
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hg' : MulAut.conjNormal (H := commutator Γ) g = 1 := by
      have h1 : (MulAut.congr e).toMonoidHom (MulAut.conjNormal (H := commutator Γ) g) =
          (MulAut.congr e).toMonoidHom 1 := by
        rw [map_one]
        exact hg
      exact (MulAut.congr e).injective h1
    rw [← hC]
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h2 := congrArg (fun φ : MulAut (commutator Γ) => ((φ ⟨h, hh⟩ : commutator Γ) : Γ)) hg'
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc h * g = g * h * g⁻¹ * g := by rw [h2]
      _ = g * h := by group
  exact ⟨MulEquiv.ofBijective f (hinj.bijective_of_nat_card_le hcard)⟩

theorem card_semilinearFractionalGroup_eight :
    Nat.card (semilinearFractionalGroup (GaloisField 2 3)) = 1512 := by
  have hK : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  rw [card_semilinearFractionalGroup (GaloisField 2 3) Nat.prime_two hK, hK]
  norm_num

instance finite_mulAut_psl2_eight : Finite (MulAut (PSL2 (GaloisField 2 3))) :=
  Finite.of_equiv _ (mulAutPSL2EquivSemilinearFractional (GaloisField 2 3)).symm.toEquiv

theorem G2_reeGamma_zero_structure (hK : Nat.card K = 3 ^ (2 * 0 + 1)) :
    Nat.card (ReeTag.G2.reeGamma K 0) = 1512 ∧
      Nonempty (ReeTag.G2.reeGamma K 0 ≃* semilinearFractionalGroup (GaloisField 2 3)) ∧
      (commutator (ReeTag.G2.reeGamma K 0)).index = 3 ∧
      Nonempty (commutator (ReeTag.G2.reeGamma K 0) ≃* PSL(2, GaloisField 2 3)) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (commutator (ReeTag.G2.reeGamma K 0))
        .PSL 2 2 3 ∧
      CFSG.Assembly.ComponentType.ClassicalModel (commutator (ReeTag.G2.reeGamma K 0))
        .PSL 2 2 3 := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  set Γ := ReeTag.G2.reeGamma K 0 with hΓ
  have hcardΓ : Nat.card Γ = 1512 := by
    rw [hΓ, G2_card_reeGamma 0 hK]
    norm_num
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨hsimple, hnab, -, -, hzero, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components 0 K hK
  obtain ⟨-, h504, hidx⟩ := hzero rfl w₀ hw₀
  have hZ := (small_Ree_fixed_group_center_trivial 0 K hK).1
  have hnormal : ∀ N : Subgroup (commutator Γ), N.Normal → N = ⊥ ∨ N = ⊤ :=
    fun N hN => hN.eq_bot_or_eq_top
  obtain ⟨hstated, hmodel, ⟨e⟩⟩ := simple_order_504_is_psl2_eight (commutator Γ) h504 hnormal
  have hC := centralizer_commutator_eq_bot hZ hsimple hnab hidx
  have hcardAut : Nat.card (MulAut (PSL2 (GaloisField 2 3))) ≤ Nat.card Γ := by
    rw [Nat.card_congr (mulAutPSL2EquivSemilinearFractional (GaloisField 2 3)).toEquiv,
      card_semilinearFractionalGroup_eight, hcardΓ]
  obtain ⟨E⟩ := nonempty_mulEquiv_mulAut_of_centralizer_eq_bot e hC hcardAut
  exact ⟨hcardΓ, ⟨E.trans (mulAutPSL2EquivSemilinearFractional (GaloisField 2 3))⟩, hidx, ⟨e⟩,
    hstated, hmodel⟩

theorem small_Ree_G2_fixed_points_and_Ree3_PGammaL2_8 (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    orderOf (ReeTag.G2.finiteReeAut K a) = 2 ∧
    (∀ g : adjointGroup ReeTag.G2.tag K,
      g ∈ ReeTag.G2.finiteReeFixedGroup K a ↔ ReeTag.G2.finiteReeAut K a g = g) ∧
    ReeTag.G2.reeGamma K a =
      (ReeTag.G2.finiteReeFixedGroup K a).map (adjointGroup ReeTag.G2.tag K).subtype ∧
    Nat.card (ReeTag.G2.finiteReeFixedGroup K a) =
      (3 ^ (2 * a + 1)) ^ 3 * ((3 ^ (2 * a + 1)) ^ 3 + 1) * (3 ^ (2 * a + 1) - 1) ∧
    Nat.card (ReeTag.G2.reeGamma K a) =
      (3 ^ (2 * a + 1)) ^ 3 * ((3 ^ (2 * a + 1)) ^ 3 + 1) * (3 ^ (2 * a + 1) - 1) ∧
    (1 ≤ a → IsSimpleGroup (ReeTag.G2.reeGamma K a) ∧
      ∃ x y : ReeTag.G2.reeGamma K a, x * y ≠ y * x) ∧
    (a = 0 → Nat.card (ReeTag.G2.reeGamma K a) = 1512 ∧
      Nonempty (ReeTag.G2.reeGamma K a ≃* semilinearFractionalGroup (GaloisField 2 3)) ∧
      (commutator (ReeTag.G2.reeGamma K a)).index = 3 ∧
      Nonempty (commutator (ReeTag.G2.reeGamma K a) ≃* PSL(2, GaloisField 2 3)) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (commutator (ReeTag.G2.reeGamma K a))
        .PSL 2 2 3 ∧
      CFSG.Assembly.ComponentType.ClassicalModel (commutator (ReeTag.G2.reeGamma K a))
        .PSL 2 2 3) := by
  have hcard := G2_card_reeGamma a hK
  have hmap : ReeTag.G2.reeGamma K a =
      (ReeTag.G2.finiteReeFixedGroup K a).map (adjointGroup ReeTag.G2.tag K).subtype := rfl
  refine ⟨G2_orderOf_finiteReeAut a hK, fun g => ReeTag.mem_finiteReeFixedGroup, hmap, ?_, hcard,
    fun ha => ?_, fun ha => ?_⟩
  · rw [← hcard, hmap, Subgroup.card_map_of_injective Subtype.val_injective]
  · obtain ⟨-, hs, hnab⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple ha K hK
    exact ⟨hs, hnab⟩
  · subst ha
    exact G2_reeGamma_zero_structure hK

end CFSG.ComponentClassification.LiteratureLocal
