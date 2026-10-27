module

public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.Holt.H78.Start
import CFSG.Holt.General.AltGood
import CFSG.Holt.General.Simple
import CFSG.Holt.General.ComponentsImage

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General

section OneFactor

theorem isGoodZ_subtype_top_iff {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]
    (L : Subgroup G) (α : Ω) : IsGoodZ L Ω α ⊤ ↔ IsGoodZ G Ω α L := by
  have hbij : Function.Bijective (L.subtype.subgroupMap (⊤ : Subgroup L)) := by
    refine ⟨fun a b hab => ?_, L.subtype.subgroupMap_surjective ⊤⟩
    have h1 := congrArg (fun x : (⊤ : Subgroup L).map L.subtype => (x : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  have h := comap_zStarIn_of_bijective _ hbij
  have key := isGoodZ_congr (zStarQuotientEquiv _ (L.subtype.subgroupMap_surjective ⊤) h)
    (map_stabilizerImage_zStarQuotientEquiv (α := α) (α' := α) (stabilizer_subgroupOf L α) h)
  rwa [Subgroup.map_top, Subgroup.range_subtype] at key

namespace HoltData

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

@[expose] def rhoL (i : D.ι) : D.L i →* Equiv.Perm (D.Ψc i) :=
  (D.ρ i).comp (Subgroup.inclusion (D.L_le i))

@[simp] theorem rhoL_apply (i : D.ι) (l : D.L i) : D.rhoL i l = D.ρ i ⟨l, D.L_le i l.2⟩ :=
  rfl

theorem range_rhoL (i : D.ι) : (D.rhoL i).range = D.M i := by
  rw [rhoL, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

variable {D} in
theorem rhoL_injective (hO : jOddCore G Ω = ⊥) (i : D.ι) : Function.Injective (D.rhoL i) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro l hl
  have h := mem_jOddCore_of_mem_L (D := D) (h := ⟨l, D.L_le i l.2⟩) l.2 (MonoidHom.mem_ker.mp hl)
  rw [hO, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr (Subtype.ext h)

@[expose] noncomputable def lEquiv (hO : jOddCore G Ω = ⊥) (i : D.ι) : D.L i ≃* D.M i :=
  (MonoidHom.ofInjective (rhoL_injective hO i)).trans (MulEquiv.subgroupCongr (D.range_rhoL i))

@[simp] theorem coe_lEquiv_apply (hO : jOddCore G Ω = ⊥) (i : D.ι) (l : D.L i) :
    (D.lEquiv hO i l : Equiv.Perm (D.Ψc i)) = D.ρ i ⟨l, D.L_le i l.2⟩ :=
  rfl

theorem exists_mul_ne_mul_L (hO : jOddCore G Ω = ⊥) (i : D.ι) :
    ∃ a b : D.L i, a * b ≠ b * a := by
  by_contra h
  refine D.not_isMulCommutative_M i ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨a, rfl⟩ := (D.lEquiv hO i).surjective x
  obtain ⟨b, rfl⟩ := (D.lEquiv hO i).surjective y
  have hab : a * b = b * a := not_not.mp fun hab => h ⟨a, b, hab⟩
  rw [← map_mul, ← map_mul, hab]

variable {D} in
theorem bijective_coord (hO : jOddCore G Ω = ⊥) {i₀ : D.ι} (hι : ∀ i, i = i₀) :
    Function.Bijective fun ω => D.coord ω i₀ := by
  refine ⟨fun ω ω' h => ?_, D.exists_coord_apply_eq i₀⟩
  have hc : D.coord ω = D.coord ω' := funext fun i => by
    obtain rfl := hι i
    exact h
  have h' := (D.coord_eq_iff ω ω').mp hc
  rw [orbit_jOddCore_eq_singleton hO, Set.mem_singleton_iff] at h'
  exact h'.symm

@[expose] noncomputable def coordEquiv (hO : jOddCore G Ω = ⊥) {i₀ : D.ι} (hι : ∀ i, i = i₀) :
    Ω ≃ D.Ψc i₀ :=
  Equiv.ofBijective _ (bijective_coord hO hι)

@[simp] theorem coordEquiv_apply (hO : jOddCore G Ω = ⊥) {i₀ : D.ι} (hι : ∀ i, i = i₀)
    (ω : Ω) : D.coordEquiv hO hι ω = D.coord ω i₀ :=
  rfl

theorem coordEquiv_smul (hO : jOddCore G Ω = ⊥) {i₀ : D.ι} (hι : ∀ i, i = i₀) (l : D.L i₀)
    (ω : Ω) : D.coordEquiv hO hι (l • ω) = D.lEquiv hO i₀ l • D.coordEquiv hO hι ω := by
  rw [coordEquiv_apply, coordEquiv_apply, Subgroup.smul_def, Subgroup.smul_def,
    coe_lEquiv_apply, Equiv.Perm.smul_def]
  exact D.coord_smul ⟨l, D.L_le i₀ l.2⟩ ω i₀

theorem faithfulSMul_L (hO : jOddCore G Ω = ⊥) {i₀ : D.ι} (hι : ∀ i, i = i₀) :
    FaithfulSMul (D.L i₀) Ω := by
  refine ⟨fun {l l'} h => (D.lEquiv hO i₀).injective (Subtype.ext (Equiv.ext fun b => ?_))⟩
  obtain ⟨ω, rfl⟩ := (D.coordEquiv hO hι).surjective b
  have h1 := D.coordEquiv_smul hO hι l ω
  rw [h ω, D.coordEquiv_smul hO hι l' ω] at h1
  simpa only [Subgroup.smul_def, Equiv.Perm.smul_def] using h1.symm

theorem alternatingGroup_le_range_L [Fintype Ω] [DecidableEq Ω] (hO : jOddCore G Ω = ⊥)
    {i₀ : D.ι} (hι : ∀ i, i = i₀) (hA : D.M i₀ = alternatingGroup (D.Ψc i₀)) :
    alternatingGroup Ω ≤ (toPermHom (D.L i₀) Ω).range := by
  intro σ hσ
  set e := D.coordEquiv hO hι
  have hτ : e.permCongr σ ∈ D.M i₀ := by
    rw [hA, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
    exact Equiv.Perm.mem_alternatingGroup.mp hσ
  refine ⟨(D.lEquiv hO i₀).symm ⟨_, hτ⟩, Equiv.ext fun ω => e.injective ?_⟩
  rw [toPermHom_apply, toPerm_apply, coordEquiv_smul, MulEquiv.apply_symm_apply,
    Subgroup.smul_def, Equiv.Perm.smul_def, Equiv.permCongr_apply, Equiv.symm_apply_apply]

theorem fusionIsBenderGroup_L (hO : jOddCore G Ω = ⊥) {i : D.ι} (hM : IsNaturalSE (D.M i)) :
    CFSG.Open.fusionIsBenderGroup (D.L i) := by
  obtain ⟨q, e, hN⟩ := hM
  exact CFSG.RankThree.PartTwo.Sec21.fusionIsBenderGroup_of_mulEquiv
    (Subgroup.topEquiv.trans (D.lEquiv hO i).symm) hN.fusionIsBenderGroup

theorem exists_forall_eq_of_le_L (hO : jOddCore G Ω = ⊥) [Nontrivial Ω] {B : Subgroup G}
    (hB : B ≠ ⊥) (hBL : ∀ i, B ≤ D.L i) : ∃ i₀ : D.ι, ∀ i, i = i₀ := by
  obtain ⟨i₀⟩ : Nonempty D.ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := (D.isEmpty_ι_iff).mp hne
    obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
    obtain ⟨g, hg⟩ := exists_smul_eq (jOddCore G Ω) a b
    have hg1 : (g : G) = 1 := Subgroup.mem_bot.mp (le_bot_iff.mpr hO g.2)
    rw [Subgroup.smul_def, hg1, one_smul] at hg
    exact hab hg
  refine ⟨i₀, fun i => ?_⟩
  by_contra hne
  refine hB (eq_bot_iff.mpr fun b hb => ?_)
  have hbH : b ∈ jHull G Ω := D.L_le i (hBL i hb)
  have h1 := rho_eq_one_of_mem_L (D := D) hne (h := ⟨b, hbH⟩) (hBL i hb)
  have h2 := mem_jOddCore_of_mem_L (D := D) (h := ⟨b, hbH⟩) (hBL i₀ hb) h1
  rwa [hO] at h2

end HoltData

end OneFactor

namespace HoltData

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

theorem isBenderAction_L (hO : jOddCore G Ω = ⊥) {i₀ : D.ι} (hι : ∀ i, i = i₀)
    (hM : IsNaturalSE (D.M i₀)) : ∃ n i e : ℕ, IsBenderAction (D.L i₀) Ω n i e := by
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hM
  refine ⟨n, i, e, hA.of_equiv (D.lEquiv hO i₀).symm (D.coordEquiv hO hι).symm fun m b => ?_⟩
  apply (D.coordEquiv hO hι).injective
  rw [Equiv.apply_symm_apply, coordEquiv_smul, MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem isGoodZ_L_top [Finite G] [Finite Ω] (hO : jOddCore G Ω = ⊥) {i₀ : D.ι}
    (hι : ∀ i, i = i₀) (α : Ω) : IsGoodZ (D.L i₀) Ω α ⊤ := by
  have := isSimpleGroup_L (D := D) hO i₀
  have := D.faithfulSMul_L hO hι
  have hnonab := D.exists_mul_ne_mul_L hO i₀
  rcases D.factor i₀ with ⟨hA, -⟩ | hM
  · classical
    have := Fintype.ofFinite Ω
    have hodd : Odd (Nat.card Ω) := by
      rw [Nat.card_congr (D.coordEquiv hO hι), Nat.card_eq_fintype_card]
      exact D.odd_card_Ψc i₀
    exact isGoodZ_top_of_alternatingGroup_le hnonab hodd
      (D.alternatingGroup_le_range_L hO hι hA) α
  · obtain ⟨n, i, e, hB⟩ := D.isBenderAction_L hO hι hM
    exact (isGoodZ_top_iff hnonab α).mpr
      (Or.inl ⟨D.fusionIsBenderGroup_L hO hM, hB.isStronglyEmbedded_stabilizer α⟩)

end HoltData

section Simple

variable {X : Type*} [Group X] [IsSimpleGroup X] {Ω : Type*} [MulAction X Ω]

theorem jHull_eq_top_of_isSimpleGroup {t : X} (ht : t ∈ longInv X Ω) : jHull X Ω = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (jHull X Ω) with h | h
  · have h1 : t = 1 := Subgroup.mem_bot.mp (h ▸ mem_jHull_of_mem_longInv ht)
    have h2 := ht.1
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · exact h

theorem jOddCore_eq_bot_of_isSimpleGroup [Finite X] {t : X} (ht : t ∈ longInv X Ω) :
    jOddCore X Ω = ⊥ :=
  le_bot_iff.mp ((jOddCore_le_pPrimeCore (G := X) (Ω := Ω)).trans
    (CFSG.RankThree.PartTwo.Sec21.pPrimeCore_two_eq_bot_of_simple ht.1).le)

theorem HoltData.isGoodZ_top_of_isSimpleGroup [Finite X] [Finite Ω] [Nontrivial Ω]
    (D : HoltData X Ω) (α : Ω) : IsGoodZ X Ω α ⊤ := by
  have hH := jHull_eq_top_of_isSimpleGroup D.t_mem
  have hO := jOddCore_eq_bot_of_isSimpleGroup D.t_mem
  have hL : ∀ i, D.L i = ⊤ := fun i => by
    have hn : (D.L i).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (hH ▸ D.le_normalizer i))
    have := HoltData.isSimpleGroup_L (D := D) hO i
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.L i) with h | h
    · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).mp inferInstance)
    · exact h
  obtain ⟨i₀, hι⟩ := D.exists_forall_eq_of_le_L hO (B := ⊤) top_ne_bot fun i => (hL i).ge
  have h := D.isGoodZ_L_top hO hι α
  rwa [isGoodZ_subtype_top_iff, hL i₀] at h

end Simple

section Consumers

theorem IsHoltTriple.three_le_card {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]
    [Finite Ω] [FaithfulSMul G Ω] {z : G} {α : Ω} (hT : IsHoltTriple G Ω z α) :
    3 ≤ Nat.card Ω := by
  have hnt : Nontrivial Ω := by
    by_contra hΩ
    rw [not_nontrivial_iff_subsingleton] at hΩ
    have h1 : z = 1 := eq_of_smul_eq_smul fun ω => by
      rw [one_smul]
      exact (hT.smul_eq_iff ω).mpr (Subsingleton.elim ω α)
    have h2 := hT.orderOf_eq_two
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have h1 := Finite.one_lt_card_iff_nontrivial.mpr hnt
  obtain ⟨k, hk⟩ := CFSG.Holt.odd_card hT.orderOf_eq_two
    ⟨α, (hT.smul_eq_iff α).mpr rfl, fun ω hω => (hT.smul_eq_iff ω).mp hω⟩
  omega

theorem isGoodZ_top_of_holtTheorem1 (h : HoltTheorem1) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {Ω : Type} [MulAction X Ω] [Finite Ω] [FaithfulSMul X Ω] {z : X} {α : Ω}
    (hT : IsHoltTriple X Ω z α) : IsGoodZ X Ω α ⊤ := by
  have h3 := IsHoltTriple.three_le_card hT
  have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨D⟩ := h X Ω (IsHoltTriple.isStarGroup hT h3)
  exact D.isGoodZ_top_of_isSimpleGroup α

theorem holtUniqueFixedPointSimple_of_holtTheorem1 (h : HoltTheorem1) :
    CFSG.RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple := by
  intro X _ _ _ hnonab N hN z hz hS hfix
  obtain ⟨q, hq, huniq⟩ := hfix
  have := CFSG.RankThree.PartTwo.Sec21.faithfulSMul_quotient_of_simple hN
  have hT : IsHoltTriple X (X ⧸ N) z q :=
    ⟨inferInstance, hz, fun ω => ⟨huniq ω, fun h => h ▸ hq⟩, hS⟩
  rcases (isGoodZ_top_iff hnonab q).mp (isGoodZ_top_of_holtTheorem1 h hT) with
    ⟨-, hSE⟩ | ⟨m, -, e, -⟩
  · exact Or.inl ⟨_, hSE⟩
  · exact Or.inr ⟨2 * m + 1, odd_two_mul_add_one m, ⟨e⟩⟩

end Consumers

end CFSG.Holt.H78
