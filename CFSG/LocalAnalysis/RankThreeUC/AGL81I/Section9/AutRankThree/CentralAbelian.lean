module

public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Artinian.Module

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists
open scoped Pointwise IsMulCommutative

section Abstract

variable {G K S : Type*} [Group G] [Field K] [CommRing S] [Algebra K S] [MulSemiringAction G S]

theorem smul_maximal_eq_of_isPerfect [IsArtinianRing S] (hG : Group.IsPerfect G)
    (hS : Nat.card (MaximalSpectrum S) ≤ 4) (m : Ideal S) [m.IsMaximal] (g : G) : g • m = m := by
  have hsub : MulAction.orbit G m ⊆ Set.range (MaximalSpectrum.asIdeal (R := S)) := by
    rintro _ ⟨h, rfl⟩
    exact ⟨⟨h • m, by rw [Ideal.pointwise_smul_eq_comap]; infer_instance⟩, rfl⟩
  have hfin : (Set.range (MaximalSpectrum.asIdeal (R := S))).Finite := Set.finite_range _
  set H := MulAction.stabilizer G m
  have h4 : H.index ≤ 4 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard hsub hfin).trans
      ((Set.ncard_range_of_injective fun _ _ h => MaximalSpectrum.ext h).le.trans hS)
  have h0 : H.index ≠ 0 := by
    rw [MulAction.index_stabilizer]
    exact ((Set.ncard_pos (hfin.subset hsub)).mpr (MulAction.nonempty_orbit m)).ne'
  have : H.FiniteIndex := ⟨h0⟩
  have : Group.IsSolvable (Equiv.Perm (G ⧸ H)) :=
    Equiv.Perm.isSolvable (by rwa [← Subgroup.index_eq_card])
  have hsub1 : Subsingleton (MulAction.toPermHom G (G ⧸ H)).range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    have : Group.IsPerfect G := hG
    have := Group.IsPerfect.range (MulAction.toPermHom G (G ⧸ H))
    exact Group.IsPerfect.not_isSolvable (G := (MulAction.toPermHom G (G ⧸ H)).range) inferInstance
  have hg : MulAction.toPermHom G (G ⧸ H) g = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨_, g, rfl⟩ : (MulAction.toPermHom G (G ⧸ H)).range) 1)
  have h1 : ((g : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    simpa using congrArg (fun σ => σ ((1 : G) : G ⧸ H)) hg
  have h2 := QuotientGroup.eq.mp h1
  simpa [H] using h2

variable [SMulCommClass G K S]

def residueHom (m : Ideal S) (hm : ∀ g : G, g • m = m) : G →* ((S ⧸ m) ≃ₐ[K] (S ⧸ m)) where
  toFun g := Ideal.quotientEquivAlg m m (MulSemiringAction.toAlgEquiv K S g) (hm g).symm
  map_one' := by ext ⟨x⟩; exact congrArg (Ideal.Quotient.mk m) (one_smul G x)
  map_mul' g h := by ext ⟨x⟩; exact congrArg (Ideal.Quotient.mk m) (mul_smul g h x)

theorem mk_smul_eq_of_isPerfect [Finite K] [Finite S] (hG : Group.IsPerfect G) (m : Ideal S)
    [m.IsMaximal] (hm : ∀ g : G, g • m = m) (g : G) (s : S) :
    Ideal.Quotient.mk m (g • s) = Ideal.Quotient.mk m s := by
  let := Ideal.Quotient.field m
  have : Finite (S ⧸ m) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have h1 : residueHom (K := K) m hm g = 1 :=
    Abelianization.commutator_subset_ker _ (Group.IsPerfect.mem_commutator (hP := hG))
  have h2 := congrArg (fun σ => σ (Ideal.Quotient.mk m s)) h1
  simp only [residueHom, MonoidHom.coe_mk, OneHom.coe_mk] at h2
  exact h2

theorem smul_eq_self_of_isPerfect [Finite K] [Finite S] [IsArtinianRing S] [IsReduced S]
    (hG : Group.IsPerfect G) (hS : Nat.card (MaximalSpectrum S) ≤ 4) (g : G) (s : S) :
    g • s = s := by
  apply (IsArtinianRing.equivPi S).injective
  funext I
  exact mk_smul_eq_of_isPerfect (K := K) hG I.asIdeal
    (smul_maximal_eq_of_isPerfect hG hS I.asIdeal) g s

end Abstract

section Linear

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem card_maximalSpectrum_le (S : Subalgebra K (Matrix ι ι K)) [IsMulCommutative S]
    [IsArtinianRing S] [IsReduced S] : Nat.card (MaximalSpectrum S) ≤ Fintype.card ι := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum S)
  let e : MaximalSpectrum S → Matrix ι ι K := fun I =>
    ((IsArtinianRing.equivPi S).symm (Pi.single I 1) : S)
  have he : ∀ I J, e I * e J = if I = J then e I else 0 := by
    intro I J
    simp only [e, ← Subalgebra.coe_mul, ← map_mul]
    split_ifs with h
    · subst h; rw [← Pi.single_mul, mul_one]
    · have h0 : (Pi.single I 1 : ∀ I : MaximalSpectrum S, S ⧸ I.asIdeal) * Pi.single J 1 = 0 := by
        funext k
        by_cases hk : k = I
        · subst hk; simp [h]
        · simp [hk]
      rw [h0, map_zero, ZeroMemClass.coe_zero]
  have hne : ∀ I, e I ≠ 0 := fun I h => by
    simp only [e, ZeroMemClass.coe_eq_zero, map_eq_zero_iff _ (AlgEquiv.injective _),
      Pi.single_eq_zero_iff] at h
    exact one_ne_zero h
  have hv : ∀ I, ∃ v : ι → K, e I *ᵥ v ≠ 0 := fun I => by
    by_contra h
    push Not at h
    exact hne I (Matrix.ext_of_mulVec_single fun i => by rw [h, Matrix.zero_mulVec])
  choose v hv using hv
  have hli : LinearIndependent K fun I => e I *ᵥ v I := by
    rw [linearIndependent_iff']
    intro s c hs I hI
    have h := congrArg (e I *ᵥ ·) hs
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec, he,
      Matrix.mulVec_zero] at h
    have hite : ∀ x, c x • (if I = x then e I else 0) *ᵥ v x =
        if I = x then c x • e I *ᵥ v x else 0 := fun x => by split_ifs <;> simp
    simp only [hite, Finset.sum_ite_eq, if_pos hI] at h
    exact (smul_eq_zero.mp h).resolve_right (hv I)
  simpa [Nat.card_eq_fintype_card] using hli.fintype_card_le_finrank

variable {Y : Subgroup (GL ι K)}

@[expose] def glMatHom (A : Subgroup Y) : A →* Matrix ι ι K :=
  (Units.coeHom _).comp (Y.subtype.comp A.subtype)

@[expose] def glAdjAlg (A : Subgroup Y) : Subalgebra K (Matrix ι ι K) :=
  Algebra.adjoin K (Set.range (glMatHom A))

instance (A : Subgroup Y) [IsMulCommutative A] : IsMulCommutative (glAdjAlg A) :=
  Algebra.isMulCommutative_adjoin K (by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ -
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm a b])

private def conjMat (g : GL ι K) (x : Matrix ι ι K) : Matrix ι ι K :=
  (g : Matrix ι ι K) * x * ((g⁻¹ : GL ι K) : Matrix ι ι K)

private theorem conjMat_mem (A : Subgroup Y) [A.Normal] (y : Y) {x : Matrix ι ι K}
    (hx : x ∈ glAdjAlg A) : conjMat y x ∈ glAdjAlg A := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    refine Algebra.subset_adjoin ⟨⟨y * a * y⁻¹, Subgroup.Normal.conj_mem ‹_› _ a.2 y⟩, ?_⟩
    simp [glMatHom, conjMat]
  | algebraMap r =>
    rw [conjMat, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
    exact Subalgebra.algebraMap_mem _ r
  | add x z _ _ hx hz =>
    rw [conjMat, mul_add, add_mul]
    exact add_mem hx hz
  | mul x z _ _ hx hz =>
    have : conjMat y (x * z) = conjMat y x * conjMat y z := by
      simp [conjMat, mul_assoc]
    rw [this]
    exact mul_mem hx hz

private instance (A : Subgroup Y) [A.Normal] : SMul Y (glAdjAlg A) where
  smul y x := ⟨conjMat y x, conjMat_mem A y x.2⟩

private theorem coe_smul_adjAlg (A : Subgroup Y) [A.Normal] (y : Y) (x : glAdjAlg A) :
    ((y • x : glAdjAlg A) : Matrix ι ι K) = conjMat y x := rfl

private instance (A : Subgroup Y) [A.Normal] : MulSemiringAction Y (glAdjAlg A) where
  one_smul x := Subtype.ext (by simp [coe_smul_adjAlg, conjMat])
  mul_smul y z x := Subtype.ext (by simp [coe_smul_adjAlg, conjMat, mul_assoc])
  smul_zero y := Subtype.ext (by simp [coe_smul_adjAlg, conjMat])
  smul_add y x z := Subtype.ext (by simp [coe_smul_adjAlg, conjMat, mul_add, add_mul])
  smul_one y := Subtype.ext (by simp [coe_smul_adjAlg, conjMat])
  smul_mul y x z := Subtype.ext (by simp [coe_smul_adjAlg, conjMat, mul_assoc])

private instance (A : Subgroup Y) [A.Normal] : SMulCommClass Y K (glAdjAlg A) where
  smul_comm y c x := Subtype.ext (by simp [coe_smul_adjAlg, conjMat])

theorem isReduced_glAdjAlg (A : Subgroup Y) [IsMulCommutative A] [Finite A]
    (hA : ¬ ringChar K ∣ Nat.card A) : IsReduced (glAdjAlg A) := by
  have : NeZero (Nat.card A : K) := ⟨by rwa [Ne, ringChar.spec]⟩
  let f := MonoidAlgebra.lift K (Matrix ι ι K) A (glMatHom A)
  have hf : ∀ x, f x ∈ glAdjAlg A := fun x => by
    induction x using MonoidAlgebra.induction_on with
    | of a => rw [MonoidAlgebra.lift_of]; exact Algebra.subset_adjoin ⟨a, rfl⟩
    | add x z hx hz => rw [map_add]; exact add_mem hx hz
    | smul r x hx => rw [map_smul]; exact Subalgebra.smul_mem _ hx r
  have hsurj : Function.Surjective (f.codRestrict (glAdjAlg A) hf) := by
    have hle : glAdjAlg A ≤ f.range := Algebra.adjoin_le (by
      rintro _ ⟨a, rfl⟩
      exact ⟨MonoidAlgebra.of K A a, MonoidAlgebra.lift_of _ a⟩)
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := hle hx
    exact ⟨z, rfl⟩
  have := RingHom.isSemisimpleRing_of_surjective
    ((f.codRestrict (glAdjAlg A) hf : MonoidAlgebra K A →ₐ[K] glAdjAlg A) :
      MonoidAlgebra K A →+* glAdjAlg A) hsurj
  infer_instance

end Linear

theorem le_center_of_normal_of_isMulCommutative {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι ≤ 4)
    {Y : Subgroup (GL ι K)} (hY : Group.IsPerfect Y)
    {A : Subgroup Y} (hA : A.Normal) (hAc : IsMulCommutative A)
    (hAℓ : Nat.Coprime (ringChar K) (Nat.card A)) : A ≤ Subgroup.center Y := by
  have : IsMulCommutative A := hAc
  have : A.Normal := hA
  have : IsReduced (glAdjAlg A) := isReduced_glAdjAlg A fun h =>
    CharP.ringChar_ne_one (Nat.Coprime.eq_one_of_dvd hAℓ h)
  have hS := (card_maximalSpectrum_le (glAdjAlg A)).trans hι
  intro a ha
  rw [Subgroup.mem_center_iff]
  intro y
  have h := congrArg Subtype.val (smul_eq_self_of_isPerfect (K := K) hY hS y
    ⟨glMatHom A ⟨a, ha⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩)
  simp only [coe_smul_adjAlg, conjMat, glMatHom, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype, Units.coeHom_apply] at h
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul]
  conv_rhs => rw [← h]
  simp [mul_assoc]

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
