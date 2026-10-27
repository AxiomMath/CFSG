module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.GroupTheory.Complement
public import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
public import CFSG.FeitThompson.Local.ChiefFactorCentralizationCentralSeries

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace ChiefFactorLinearAction

variable {M : Type*} [Group M]

theorem map_conjNormal_subgroupOf (X Y : Subgroup M) [X.Normal] [hY : Y.Normal] (g : M) :
    Subgroup.map (↑(MulAut.conjNormal (H := X) g) : ↥X →* ↥X) (Y.subgroupOf X)
      = Y.subgroupOf X := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  refine ⟨?_, fun hx => ⟨(MulAut.conjNormal (H := X) g)⁻¹ x, ?_, by simp⟩⟩
  · rintro ⟨y, hy, rfl⟩
    rw [show ((↑(MulAut.conjNormal (H := X) g) : ↥X →* ↥X) y : M) = g * (y : M) * g⁻¹ from
      MulAut.conjNormal_apply g y]
    exact hY.conj_mem _ hy g
  · rw [MulAut.conjNormal_inv_apply]
    simpa [mul_assoc] using hY.conj_mem _ hx g⁻¹

def factorConjAut (X Y : Subgroup M) [X.Normal] [Y.Normal] :
    M →* MulAut (↥X ⧸ Y.subgroupOf X) where
  toFun g := QuotientGroup.congr _ _ (MulAut.conjNormal g) (map_conjNormal_subgroupOf X Y g)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      change QuotientGroup.mk (MulAut.conjNormal (1 : M) y) = QuotientGroup.mk y
      congr 1; ext; simp
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      change QuotientGroup.mk (MulAut.conjNormal (g * h) y)
        = QuotientGroup.mk (MulAut.conjNormal g (MulAut.conjNormal h y))
      congr 1; ext; simp [MulAut.conjNormal_apply, mul_assoc]

theorem factorConjAut_mk (X Y : Subgroup M) [X.Normal] [Y.Normal] (g : M) (y : ↥X) :
    factorConjAut X Y g (QuotientGroup.mk y) = QuotientGroup.mk (MulAut.conjNormal g y) := (rfl)

theorem coe_factorConjAut_mk (X Y : Subgroup M) [hX : X.Normal] [Y.Normal] (g : M) (x : M)
    (hx : x ∈ X) :
    factorConjAut X Y g (QuotientGroup.mk ⟨x, hx⟩)
      = QuotientGroup.mk ⟨g * x * g⁻¹, hX.conj_mem _ hx g⟩ := by
  rw [factorConjAut_mk]
  congr 1

theorem factorConjAut_eq_one_of_mem (X Y : Subgroup M) [X.Normal] [Y.Normal]
    [IsMulCommutative (↥X ⧸ Y.subgroupOf X)] {g : M} (hg : g ∈ X) :
    factorConjAut X Y g = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [factorConjAut_mk]
    have h : MulAut.conjNormal (H := X) g y = ⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹ := by
      ext; simp [MulAut.conjNormal_apply]
    rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      mul_comm' (QuotientGroup.mk (⟨g, hg⟩ : ↥X) : ↥X ⧸ Y.subgroupOf X), mul_assoc,
      mul_inv_cancel, mul_one]
    rfl

theorem forall_factorConjAut_mem (X Y : Subgroup M) [X.Normal] [Y.Normal]
    [IsMulCommutative (↥X ⧸ Y.subgroupOf X)] {B : Subgroup M} (hsup : X ⊔ B = ⊤)
    (S : Subgroup (↥X ⧸ Y.subgroupOf X))
    (hS : ∀ b ∈ B, ∀ x ∈ S, factorConjAut X Y b x ∈ S) :
    ∀ g : M, ∀ x ∈ S, factorConjAut X Y g x ∈ S := by
  set E := ↥X ⧸ Y.subgroupOf X
  set T := (MulAction.stabilizer (MulAut E) S).comap (factorConjAut X Y) with hT
  have hXT : X ≤ T := by
    intro g hg
    simp only [hT, Subgroup.mem_comap, factorConjAut_eq_one_of_mem X Y hg]
    exact one_mem _
  have hBT : B ≤ T := by
    intro b hb
    simp only [hT, Subgroup.mem_comap]
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h' := hS b hb _ h
      rwa [show factorConjAut X Y b ((factorConjAut X Y b)⁻¹ • x) = x from by
        simp [MulAut.smul_def]] at h'
    · have h' := hS b⁻¹ (B.inv_mem hb) x h
      rwa [map_inv] at h'
  intro g x hx
  have hg : g ∈ T := (hsup ▸ sup_le hXT hBT : (⊤ : Subgroup M) ≤ T) (Subgroup.mem_top g)
  rw [hT, Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hg
  have hmem : factorConjAut X Y g x ∈ factorConjAut X Y g • S := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def] using hx
  rwa [hg] at hmem

def factorPreimage (X Y : Subgroup M) [Y.Normal] (S : Subgroup (↥X ⧸ Y.subgroupOf X)) :
    Subgroup M :=
  (S.comap (QuotientGroup.mk' (Y.subgroupOf X))).map X.subtype

theorem mem_factorPreimage (X Y : Subgroup M) [Y.Normal] (S : Subgroup (↥X ⧸ Y.subgroupOf X))
    {g : M} : g ∈ factorPreimage X Y S ↔ ∃ hg : g ∈ X, QuotientGroup.mk (⟨g, hg⟩ : ↥X) ∈ S := by
  simp only [factorPreimage, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨h ▸ y.2, by subst h; simpa using hy⟩,
    fun ⟨hg, h⟩ => ⟨⟨g, hg⟩, by simpa using h, rfl⟩⟩

theorem factorPreimage_le (X Y : Subgroup M) [Y.Normal] (S : Subgroup (↥X ⧸ Y.subgroupOf X)) :
    factorPreimage X Y S ≤ X := Subgroup.map_subtype_le _

theorem le_factorPreimage (X Y : Subgroup M) [Y.Normal] (hle : Y ≤ X)
    (S : Subgroup (↥X ⧸ Y.subgroupOf X)) : Y ≤ factorPreimage X Y S := by
  intro g hg
  rw [mem_factorPreimage]
  refine ⟨hle hg, ?_⟩
  rw [show (QuotientGroup.mk (⟨g, hle hg⟩ : ↥X) : ↥X ⧸ Y.subgroupOf X) = 1 from
    (QuotientGroup.eq_one_iff _).2 hg]
  exact S.one_mem

@[simp]
theorem factorPreimage_bot (X Y : Subgroup M) [Y.Normal] (hle : Y ≤ X) :
    factorPreimage X Y (⊥ : Subgroup (↥X ⧸ Y.subgroupOf X)) = Y := by
  refine le_antisymm (fun g hg => ?_) (le_factorPreimage X Y hle ⊥)
  rw [mem_factorPreimage] at hg
  obtain ⟨hgX, hg2⟩ := hg
  rwa [Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hg2

@[simp]
theorem factorPreimage_top (X Y : Subgroup M) [Y.Normal] :
    factorPreimage X Y (⊤ : Subgroup (↥X ⧸ Y.subgroupOf X)) = X := by
  ext g
  rw [mem_factorPreimage]
  exact ⟨fun ⟨hg, _⟩ => hg, fun hg => ⟨hg, trivial⟩⟩

theorem factorPreimage_injective (X Y : Subgroup M) [Y.Normal] :
    Function.Injective (factorPreimage X Y) := fun _ _ h =>
  Subgroup.comap_injective (QuotientGroup.mk'_surjective _)
    (Subgroup.map_injective X.subtype_injective h)

theorem normal_factorPreimage (X Y : Subgroup M) [hX : X.Normal] [Y.Normal]
    (S : Subgroup (↥X ⧸ Y.subgroupOf X)) (hinv : ∀ g : M, ∀ x ∈ S, factorConjAut X Y g x ∈ S) :
    (factorPreimage X Y S).Normal := by
  constructor
  intro n hn g
  rw [mem_factorPreimage] at hn ⊢
  obtain ⟨hnX, hnS⟩ := hn
  exact ⟨hX.conj_mem _ hnX g, by rw [← coe_factorConjAut_mk X Y g n hnX]; exact hinv g _ hnS⟩

noncomputable def multAutToEnd (p : ℕ) (V : Type*) [AddCommGroup V] [Module (ZMod p) V] :
    MulAut (Multiplicative V) →* Module.End (ZMod p) V where
  toFun f := AddMonoidHom.toZModLinearMap p
    { toFun := fun v => (f (Multiplicative.ofAdd v)).toAdd
      map_zero' := by simp
      map_add' := fun v w => by rw [ofAdd_add, map_mul, toAdd_mul] }
  map_one' := by ext v; rfl
  map_mul' f g := by ext v; rfl

theorem multAutToEnd_apply (p : ℕ) (V : Type*) [AddCommGroup V] [Module (ZMod p) V]
    (f : MulAut (Multiplicative V)) (v : V) :
    multAutToEnd p V f v = (f (Multiplicative.ofAdd v)).toAdd := (rfl)

section Submodules

variable {p : ℕ} {E : Type*} [Group E] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

def subgroupOfSubmodule (e : E ≃* Multiplicative V) (W : Submodule (ZMod p) V) : Subgroup E :=
  Subgroup.comap e.toMonoidHom (AddSubgroup.toSubgroup W.toAddSubgroup)

theorem mem_subgroupOfSubmodule (e : E ≃* Multiplicative V) (W : Submodule (ZMod p) V) (y : E) :
    y ∈ subgroupOfSubmodule e W ↔ (e y).toAdd ∈ W := Iff.rfl

@[simp]
theorem subgroupOfSubmodule_bot (e : E ≃* Multiplicative V) :
    subgroupOfSubmodule e (⊥ : Submodule (ZMod p) V) = ⊥ := by
  ext y
  rw [mem_subgroupOfSubmodule, Submodule.mem_bot, Subgroup.mem_bot]
  exact ⟨fun h => e.injective (by rw [map_one]; exact toAdd_eq_zero.mp h),
    fun h => by rw [h]; simp⟩

@[simp]
theorem subgroupOfSubmodule_top (e : E ≃* Multiplicative V) :
    subgroupOfSubmodule e (⊤ : Submodule (ZMod p) V) = ⊤ := by
  ext y; simp [mem_subgroupOfSubmodule]

theorem subgroupOfSubmodule_injective (e : E ≃* Multiplicative V) :
    Function.Injective (subgroupOfSubmodule (p := p) e) := fun _ _ h =>
  SetLike.ext fun v => by
    simpa [mem_subgroupOfSubmodule] using SetLike.ext_iff.1 h (e.symm (Multiplicative.ofAdd v))

end Submodules

noncomputable def factorRepresentation {p d : ℕ} (H H₀ A : Subgroup M) [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative (Fin d → ZMod p)) :
    Representation (ZMod p) ↥A (Fin d → ZMod p) :=
  (multAutToEnd p _).comp (((MulAut.congr e).toMonoidHom).comp
    ((factorConjAut H H₀).comp A.subtype))

theorem factorRepresentation_apply {p d : ℕ} (H H₀ A : Subgroup M) [H.Normal] [H₀.Normal]
    (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative (Fin d → ZMod p)) (a : ↥A)
    (y : ↥H ⧸ H₀.subgroupOf H) :
    factorRepresentation H H₀ A e a ((e y).toAdd) = (e (factorConjAut H H₀ (a : M) y)).toAdd := by
  simp [factorRepresentation, multAutToEnd_apply, MulAut.congr_apply]

variable [Finite M] [Group.IsSolvable M] {H H₀ : Subgroup M} [H.Normal] [H₀.Normal]

noncomputable def factorMulEquivMapMk (H H₀ : Subgroup M) [H₀.Normal] :
    (↥H ⧸ H₀.subgroupOf H) ≃* ↥(H.map (QuotientGroup.mk' H₀)) :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl)).trans
    ((QuotientGroup.quotientKerEquivRange ((QuotientGroup.mk' H₀).comp H.subtype)).trans
      (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])))

theorem exists_prime_nonempty_mulEquiv_of_isChiefFactor (hchief : IsChiefFactor H H₀) :
    ∃ p d : ℕ, p.Prime ∧ 1 ≤ d ∧
      Nonempty ((↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative (Fin d → ZMod p)) := by
  set N := H.map (QuotientGroup.mk' H₀) with hN
  have hsurj := QuotientGroup.mk'_surjective H₀
  have hsolv : Group.IsSolvable (M ⧸ H₀) := Group.isSolvable_of_surjective hsurj
  have hNne : N ≠ ⊥ := by
    rw [hN, Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact fun h => hchief.lt.ne' (le_antisymm h hchief.le)
  have hmin : ∀ K : Subgroup (M ⧸ H₀), K.Normal → K < N → K = ⊥ := by
    intro K hKn hK
    have : K.Normal := hKn
    set K' := K.comap (QuotientGroup.mk' H₀) with hK'
    have hmapK' : K'.map (QuotientGroup.mk' H₀) = K :=
      Subgroup.map_comap_eq_self_of_surjective hsurj K
    have hle : K' ≤ H := by
      have h := Subgroup.comap_mono (f := QuotientGroup.mk' H₀) hK.le
      rw [hN, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
      simpa [sup_eq_left.2 hchief.le] using h
    have hH₀le : H₀ ≤ K' := by
      intro x hx
      have h1 : (QuotientGroup.mk' H₀) x = 1 := by
        simpa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] using hx
      simp [hK', Subgroup.mem_comap, h1]
    rcases hchief.eq_or_eq (Z := K') inferInstance hH₀le hle with h | h
    · rw [← hmapK', h, QuotientGroup.map_mk'_self]
    · exact absurd (by rw [← hmapK', h]) hK.ne
  obtain ⟨p, d, hp, hd, ⟨e⟩⟩ :=
    exists_prime_nonempty_mulEquiv_of_isSolvable_of_forall_normal_lt_eq_bot hNne hmin
  exact ⟨p, d, hp, hd, ⟨(factorMulEquivMapMk H H₀).trans e⟩⟩

theorem exists_prime_isIrreducible_factorRepresentation {A : Subgroup M}
    (hcomp : H.IsComplement' A) (hchief : IsChiefFactor H H₀) :
    ∃ (p d : ℕ) (hp : p.Prime) (_ : 1 ≤ d)
      (e : (↥H ⧸ H₀.subgroupOf H) ≃* Multiplicative (Fin d → ZMod p)),
      haveI := Fact.mk hp; (factorRepresentation H H₀ A e).IsIrreducible := by
  obtain ⟨p, d, hp, hd, ⟨e⟩⟩ := exists_prime_nonempty_mulEquiv_of_isChiefFactor hchief
  have hfact := Fact.mk hp
  refine ⟨p, d, hp, hd, e, ?_⟩
  have hcomm : IsMulCommutative (↥H ⧸ H₀.subgroupOf H) :=
    ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm' (e x)])⟩⟩
  have hnt : Nontrivial (Fin d → ZMod p) := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have hbt : (⊥ : Subrepresentation (factorRepresentation H H₀ A e)) ≠ ⊤ := fun hbt =>
    absurd (congrArg Subrepresentation.toSubmodule hbt
      : (⊥ : Submodule (ZMod p) (Fin d → ZMod p)) = ⊤) bot_ne_top
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun R => ?_ }
  have hSA : ∀ a ∈ A, ∀ x ∈ subgroupOfSubmodule e R.toSubmodule,
      factorConjAut H H₀ a x ∈ subgroupOfSubmodule e R.toSubmodule := by
    intro a ha x hx
    rw [mem_subgroupOfSubmodule] at hx ⊢
    have hmem := R.apply_mem_toSubmodule (⟨a, ha⟩ : ↥A) hx
    rwa [show factorRepresentation H H₀ A e (⟨a, ha⟩ : ↥A) ((e x).toAdd)
        = (e (factorConjAut H H₀ a x)).toAdd from by
          simpa using factorRepresentation_apply H H₀ A e (⟨a, ha⟩ : ↥A) x] at hmem
  have hSM : ∀ g : M, ∀ x ∈ subgroupOfSubmodule e R.toSubmodule,
      factorConjAut H H₀ g x ∈ subgroupOfSubmodule e R.toSubmodule :=
    forall_factorConjAut_mem H H₀ hcomp.sup_eq_top _ hSA
  have hnormal := normal_factorPreimage H H₀ _ hSM
  rcases hchief.eq_or_eq hnormal (le_factorPreimage H H₀ hchief.le _)
    (factorPreimage_le H H₀ _) with h | h
  · refine Or.inl (Subrepresentation.toSubmodule_injective
      (subgroupOfSubmodule_injective e ?_ : R.toSubmodule = ⊥))
    rw [subgroupOfSubmodule_bot]
    exact factorPreimage_injective H H₀ (h.trans (factorPreimage_bot H H₀ hchief.le).symm)
  · refine Or.inr (Subrepresentation.toSubmodule_injective
      (subgroupOfSubmodule_injective e ?_ : R.toSubmodule = ⊤))
    rw [subgroupOfSubmodule_top]
    exact factorPreimage_injective H H₀ (h.trans (factorPreimage_top H H₀).symm)

end ChiefFactorLinearAction

end CFSG.FeitThompson
