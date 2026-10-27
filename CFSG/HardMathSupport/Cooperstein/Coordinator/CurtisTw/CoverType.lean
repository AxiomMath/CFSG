module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.OfCentralCover
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import CFSG.Quasithin.Background.SmithCurtisMain

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Quasithin.SmithCurtis CoxeterSystem

variable {Ĝ G : Type*} [Group Ĝ] [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*}
  [Group W] {cs : CoxeterSystem M W} {p : ℕ}

structure CoverRankOne {D : CurtisDatum G cs p} {π : Ĝ →* G} [Finite Ĝ] [Fact p.Prime]
    (C : CentralCoverData D π p) (F : B → Type) [∀ s, Field (F s)] where
  x : (s : B) → F s → Ĝ
  y : (s : B) → F s → Ĝ
  hh : (s : B) → (F s)ˣ → Ĝ
  x_mem : ∀ s c, x s c ∈ C.lX s
  x_surj : ∀ s g, g ∈ C.lX s → ∃ c, x s c = g
  x_zero : ∀ s, x s 0 = 1
  x_inj : ∀ s, Function.Injective (x s)
  y_mem : ∀ s c, y s c ∈ C.lL
  hh_mem : ∀ s u, hh s u ∈ D.H.comap π
  hh_mul : ∀ s u v, hh s (u * v) = hh s u * hh s v
  hh_one : ∀ s, hh s 1 = 1
  phi_id : ∀ s (u : (F s)ˣ), x s u * C.nhat s =
    y s ((u⁻¹ : (F s)ˣ) : F s) * hh s (-u) * x s (-((u⁻¹ : (F s)ˣ) : F s))
  psi_id : ∀ s (u : (F s)ˣ), C.nhat s * x s u * C.nhat s =
    x s (-((u⁻¹ : (F s)ˣ) : F s)) * C.nhat s * hh s (-u) * x s (-((u⁻¹ : (F s)ˣ) : F s))

namespace CoverRankOne

variable [Finite Ĝ] [Fact p.Prime] {D : CurtisDatum G cs p} {π : Ĝ →* G}
  {C : CentralCoverData D π p} {F : B → Type} [∀ s, Field (F s)] (R : CoverRankOne C F)

theorem x_ne_one (s : B) {u : (F s)ˣ} : R.x s (u : F s) ≠ 1 := by
  intro h
  rw [← R.x_zero s] at h
  exact u.ne_zero (R.x_inj s h)

theorem mem_lX_iff (s : B) {g : Ĝ} : g ∈ C.lX s ↔ ∃ c, R.x s c = g :=
  ⟨R.x_surj s g, fun ⟨c, hc⟩ => hc ▸ R.x_mem s c⟩

theorem x_mem_lU (s : B) (c : F s) : R.x s c ∈ C.lU :=
  ⟨D.X_le s (R.x_mem s c).1, (R.x_mem s c).2⟩

theorem phiHat_x (hodd : ∀ h ∈ D.H.comap π, IsPElt p h → h = 1) (s : B) (u : (F s)ˣ) :
    C.phiHat s (R.x s (u : F s)) = R.hh s (-u) :=
  C.eq_phiHat_of_spec hodd s (R.x_mem s _) (R.x_ne_one s) (R.y_mem s _) (R.hh_mem s _)
    (R.x_mem_lU s _) (R.phi_id s u)

theorem psiHat_x (hodd : ∀ h ∈ D.H.comap π, IsPElt p h → h = 1) (s : B) (u : (F s)ˣ) :
    C.psiHat s (R.x s (u : F s)) = R.hh s (-u) :=
  C.eq_psiHat_of_spec hodd s (R.x_mem s _) (R.x_ne_one s) (R.x_mem s _) (R.hh_mem s _)
    (R.x_mem_lU s _) (R.psi_id s u)

@[expose] noncomputable def xEquiv (s : B) : F s ≃ ↥(C.datum.X s) :=
  Equiv.ofBijective (fun c => ⟨R.x s c, R.x_mem s c⟩)
    ⟨fun c d h => R.x_inj s (congrArg Subtype.val h), fun g => by
      obtain ⟨c, hc⟩ := R.x_surj s g.1 g.2
      exact ⟨c, Subtype.ext hc⟩⟩

theorem heckeT_datum [∀ s, Fintype (F s)] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k Ĝ V) (s : B) (v : V) :
    C.datum.heckeT ρ s v = ∑ c : F s, ρ (R.x s c * C.nhat s) v := by
  have := Fintype.ofFinite (C.datum.X s)
  rw [CurtisDatum.heckeT_apply]
  refine Fintype.sum_equiv (R.xEquiv s).symm _ _ fun x => ?_
  rw [show (R.x s ((R.xEquiv s).symm x) : Ĝ) = (x : Ĝ) from
    congrArg Subtype.val ((R.xEquiv s).apply_symm_apply x)]
  rfl

open Classical in
theorem sum_erase_eq (s : B) [Fintype (F s)ˣ] {N : Type*} [AddCommMonoid N] {_ : Fintype (C.datum.X s)}
    (f : Ĝ → N) :
    ∑ x ∈ (Finset.univ : Finset (C.datum.X s)).erase 1, f x =
      ∑ u : (F s)ˣ, f (R.x s (-(u : F s))) := by
  symm
  refine Finset.sum_nbij (fun u => ⟨R.x s (-(u : F s)), R.x_mem s _⟩) (fun u _ => ?_)
    (fun u _ u' _ h => ?_) (fun x hx => ?_) fun u _ => rfl
  · refine Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩
    exact R.x_ne_one s (u := -u) (by
      have := congrArg Subtype.val h
      simpa using this)
  · have h1 := R.x_inj s (congrArg Subtype.val h)
    exact Units.ext (neg_inj.mp h1)
  · obtain ⟨c, hc⟩ := R.x_surj s x.1 x.2
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply (Finset.mem_erase.mp hx).1
      exact Subtype.ext (by rw [← hc]; exact R.x_zero s)
    refine ⟨-Units.mk0 c hc0, Finset.mem_coe.mpr (Finset.mem_univ _), Subtype.ext ?_⟩
    simp only [Units.val_neg, Units.val_mk0, neg_neg]
    exact hc

open Classical in
theorem d'Scalar_datum (hodd : ∀ h ∈ D.H.comap π, IsPElt p h → h = 1) (s : B) [Fintype (F s)ˣ] {k : Type*} [Field k] (χ : Ĝ → k) :
    C.datum.d'Scalar χ s = ∑ u : (F s)ˣ, χ (R.hh s u) := by
  unfold CurtisDatum.d'Scalar
  dsimp only
  rw [R.sum_erase_eq s (fun x => χ (C.datum.psi s x))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [show (-(u : F s)) = ((-u : (F s)ˣ) : F s) from (Units.val_neg u).symm]
  show χ (C.psiHat s _) = _
  rw [R.psiHat_x hodd s (-u), neg_neg]

open Classical in
theorem dScalar_datum (hodd : ∀ h ∈ D.H.comap π, IsPElt p h → h = 1) (s : B) [Fintype (F s)ˣ] {k : Type*} [Field k] (χ : Ĝ → k) :
    C.datum.dScalar χ s = ∑ u : (F s)ˣ, χ (R.hh s u) := by
  unfold CurtisDatum.dScalar
  dsimp only
  rw [R.sum_erase_eq s (fun x => χ (C.datum.phi s x))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [show (-(u : F s)) = ((-u : (F s)ˣ) : F s) from (Units.val_neg u).symm]
  show χ (C.phiHat s _) = _
  rw [R.phiHat_x hodd s (-u), neg_neg]

end CoverRankOne

section Types

variable [Finite Ĝ] [Fact p.Prime] {D : CurtisDatum G cs p} {π : Ĝ →* G}
  {C : CentralCoverData D π p} {F : B → Type} [∀ s, Field (F s)] {R : CoverRankOne C F}
  [Fintype B]

theorem sum_chi_hh {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k Ĝ V} {y : V} {χ : Ĝ → k} {μ : B → k}
    (ht : C.datum.IsCurtisType ρ y χ μ) (s : B) [Fintype (F s)ˣ]
    (hs : ¬ ∀ u : (F s)ˣ, χ (R.hh s u) = 1) : ∑ u : (F s)ˣ, χ (R.hh s u) = 0 := by
  let f : (F s)ˣ →* k :=
    { toFun := fun u => χ (R.hh s u)
      map_one' := by rw [R.hh_one, ht.chi_one]
      map_mul' := fun u v => by
        rw [R.hh_mul, ht.chi_mul (R.hh_mem s u) (R.hh_mem s v)] }
  refine sum_hom_units_eq_zero f fun hf => hs fun u => ?_
  exact DFunLike.congr_fun hf u

variable (R) in
@[expose] def IsCoverType {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k Ĝ V) (y : V) (χ : Ĝ → k) (J : Finset B) : Prop :=
  y ∈ C.datum.fixU ρ ∧ y ≠ 0 ∧ (∀ h ∈ D.H.comap π, ρ h y = χ h • y) ∧
    ∀ s, s ∈ J ↔ (∀ u : (F s)ˣ, χ (R.hh s u) = 1) ∧ C.datum.heckeT ρ s y = 0

theorem IsCoverType.exists_mu [Finite W] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [CharP k p] {ρ : Representation k Ĝ V} (hρ : IsSimpleRep ρ) {y : V} {χ : Ĝ → k}
    {J : Finset B} (hsplit : SplitOver k (D.H.comap π)) (ht : IsCoverType R ρ y χ J) :
    ∃ μ : B → k, C.datum.IsCurtisType ρ y χ μ := by
  have hU : ∀ s, C.datum.heckeT ρ s y ∈ C.datum.fixU ρ :=
    fun s => C.datum.heckeT_mem_fixU ρ s ht.1
  obtain ⟨y₀, χ₀, μ₀, ht₀⟩ := C.datum.exists_isCurtisType hsplit hρ
  have hsmul : ∀ x ∈ C.datum.fixU ρ, ∃ c : k, x = c • y := by
    intro x hx
    obtain ⟨c, hc⟩ := C.datum.fixU_eq_smul hρ ht₀ hx
    obtain ⟨d, hd⟩ := C.datum.fixU_eq_smul hρ ht₀ ht.1
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact ht.2.1 (by rw [hd, zero_smul])
    refine ⟨c * d⁻¹, ?_⟩
    rw [hc, hd, smul_smul, mul_assoc, inv_mul_cancel₀ hd0, mul_one]
  exact ⟨fun s => (hsmul _ (hU s)).choose, ht.1, ht.2.1, ht.2.2.1,
    fun s => (hsmul _ (hU s)).choose_spec⟩

theorem exists_isCoverType [Finite W] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [CharP k p] {ρ : Representation k Ĝ V} (hρ : IsSimpleRep ρ)
    (hsplit : SplitOver k (D.H.comap π)) :
    ∃ y : V, ∃ χ : Ĝ → k, ∃ J : Finset B, IsCoverType R ρ y χ J := by
  classical
  obtain ⟨y, χ, μ, ht⟩ := C.datum.exists_isCurtisType hsplit hρ
  refine ⟨y, χ, Finset.univ.filter fun s => (∀ u : (F s)ˣ, χ (R.hh s u) = 1) ∧
    C.datum.heckeT ρ s y = 0, ht.1, ht.2.1, ht.2.2.1, fun s => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem IsCoverType.unique [Finite W] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [CharP k p] {ρ : Representation k Ĝ V} (hρ : IsSimpleRep ρ) {y y' : V} {χ χ' : Ĝ → k}
    {J J' : Finset B} (hsplit : SplitOver k (D.H.comap π))
    (ht : IsCoverType R ρ y χ J) (ht' : IsCoverType R ρ y' χ' J') :
    (∀ h ∈ D.H.comap π, χ h = χ' h) ∧ J = J' := by
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ hsplit
  obtain ⟨μ', hμ'⟩ := ht'.exists_mu hρ hsplit
  obtain ⟨hχ, hμμ⟩ := hμ.unique hρ hμ'
  obtain ⟨c, hc⟩ := C.datum.fixU_eq_smul hρ hμ ht'.1
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ht'.2.1 (by rw [hc, zero_smul])
  refine ⟨hχ, Finset.ext fun s => ?_⟩
  rw [ht.2.2.2 s, ht'.2.2.2 s, hc, map_smul, smul_eq_zero, or_iff_right hc0]
  have e : ∀ u : (F s)ˣ, χ (R.hh s u) = χ' (R.hh s u) := fun u => hχ _ (R.hh_mem s u)
  simp only [e]

open Classical in
theorem IsCoverType.mu_eq (hodd : ∀ h ∈ D.H.comap π, IsPElt p h → h = 1)
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [CharP k p]
    {ρ : Representation k Ĝ V} {y : V} {χ : Ĝ → k} {J : Finset B}
    (ht : IsCoverType R ρ y χ J) {μ : B → k} (hμ : C.datum.IsCurtisType ρ y χ μ) (s : B)
    [Fintype (F s)ˣ] :
    μ s = if (∀ u : (F s)ˣ, χ (R.hh s u) = 1) ∧ s ∉ J then ∑ u : (F s)ˣ, χ (R.hh s u)
      else 0 := by
  have hmu := hμ.mu_eq s
  rw [R.d'Scalar_datum hodd] at hmu
  split_ifs with h
  · obtain ⟨hS, hJ⟩ := h
    rcases hmu with h0 | h1
    · exfalso
      apply hJ
      rw [ht.2.2.2 s]
      exact ⟨hS, by rw [hμ.2.2.2 s, h0, zero_smul]⟩
    · exact h1
  · rcases hmu with h0 | h1
    · exact h0
    · rw [h1]
      by_cases hS : ∀ u : (F s)ˣ, χ (R.hh s u) = 1
      · have hJ : s ∈ J := by
          by_contra hJ
          exact h ⟨hS, hJ⟩
        have hT := ((ht.2.2.2 s).mp hJ).2
        rw [hμ.2.2.2 s] at hT
        have hμ0 : μ s = 0 := (smul_eq_zero.mp hT).resolve_right ht.2.1
        rw [← h1, hμ0]
      · exact sum_chi_hh (R := R) hμ s hS

theorem IsCoverType.mu_eq_dScalar (hodd : ∀ h ∈ D.H.comap π, IsPElt p h → h = 1)
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [CharP k p]
    {ρ : Representation k Ĝ V} {y : V} {χ : Ĝ → k} {J : Finset B}
    (ht : IsCoverType R ρ y χ J) {μ : B → k} (hμ : C.datum.IsCurtisType ρ y χ μ) {s : B}
    (hs : s ∉ J) [Fintype (F s)ˣ] : μ s = C.datum.dScalar χ s := by
  classical
  rw [ht.mu_eq hodd hμ s, R.dScalar_datum hodd]
  by_cases h : ∀ u : (F s)ˣ, χ (R.hh s u) = 1
  · simp [h, hs]
  · rw [sum_chi_hh (R := R) hμ s h]
    simp [h]

theorem iso_of_isCoverType [Finite W] (hodd : ∀ h ∈ D.H.comap π, IsPElt p h → h = 1)
    [∀ s, Finite (F s)] {k V V' : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [CharP k p] {ρ : Representation k Ĝ V}
    {ρ' : Representation k Ĝ V'} (hρ : IsSimpleRep ρ) (hρ' : IsSimpleRep ρ') {y : V} {y' : V'}
    {χ : Ĝ → k} {J : Finset B} (hsplit : SplitOver k (D.H.comap π))
    (ht : IsCoverType R ρ y χ J) (ht' : IsCoverType R ρ' y' χ J) :
    ∃ β : V ≃ₗ[k] V', ∀ (g : Ĝ) (v : V), β (ρ g v) = ρ' g (β v) := by
  classical
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ hsplit
  obtain ⟨μ', hμ'⟩ := ht'.exists_mu hρ' hsplit
  have hμμ : μ = μ' := funext fun s => by
    have : Fintype (F s)ˣ := Fintype.ofFinite _
    rw [ht.mu_eq hodd hμ s, ht'.mu_eq hodd hμ' s]
  rw [← hμμ] at hμ'
  exact C.datum.iso_of_isCurtisType hρ hρ' hμ hμ'

theorem exists_split_X_pow_sub_one (K : Type*) [Field K] [Finite K] (k : Type*) [Field k]
    [Algebra K k] :
    ∃ l : List k, (Polynomial.X ^ (Nat.card K - 1) - 1 : Polynomial k) =
      (l.map fun a => Polynomial.X - Polynomial.C a).prod := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hq : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
    omega
  have hprim : IsPrimitiveRoot (algebraMap K k (g : K)) (Nat.card K - 1) := by
    have h1 : IsPrimitiveRoot (g : K) (Nat.card K - 1) := by
      rw [← Nat.card_units K, ← hg, ← orderOf_units]
      exact IsPrimitiveRoot.orderOf _
    exact h1.map_of_injective (algebraMap K k).injective
  exact ⟨(Polynomial.nthRootsFinset (Nat.card K - 1) (1 : k)).toList, by
    rw [Finset.prod_map_toList]
    exact Polynomial.X_pow_sub_one_eq_prod hq hprim⟩

theorem splitOver_of_pow_card_sub_one {K : Type*} [Field K] [Finite K] (k : Type*) [Field k]
    [Algebra K k] {H : Subgroup Ĝ} (hH : ∀ h ∈ H, h ^ (Nat.card K - 1) = 1) : SplitOver k H :=
  fun h hh => ⟨Nat.card K - 1, hH h hh, exists_split_X_pow_sub_one K k⟩

end Types

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
