module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SLFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SUFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SpFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CentralQuotient
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

section OrbitFamily

variable {G : Type*} [Group G]

private def dsub (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => ⁅dsub H n, dsub H n⁆

private theorem commutator_le_self' (K : Subgroup G) : ⁅K, K⁆ ≤ K := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

private theorem dsub_anti (H : Subgroup G) : Antitone (dsub H) :=
  antitone_nat_of_succ_le fun n => commutator_le_self' (dsub H n)

private theorem dsub_le_self (H : Subgroup G) (n : ℕ) : dsub H n ≤ H := dsub_anti H (Nat.zero_le n)

private theorem map_subtype_derivedSeries (H : Subgroup G) (n : ℕ) :
    (derivedSeries ↥H n).map H.subtype = dsub H n := by
  induction n with
  | zero => rw [derivedSeries_zero, dsub, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih => rw [derivedSeries_succ, dsub, Subgroup.map_commutator, ih]

private theorem dsub_iSup {ι : Type*} (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (n : ℕ) :
    dsub (⨆ i, A i) n = ⨆ i, dsub (A i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dsub, ih]
    exact CFSG.RankThree.PartOne.KCUnitary.commutator_iSup_commuting (fun i => dsub (A i) n)
      (fun i j hij a ha b hb => hc i j hij a (dsub_le_self _ n ha) b (dsub_le_self _ n hb))

private theorem isSolvable_quotient_of_orbit_family {ι : Type*} [Finite ι] (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (P : ι → Prop)
    (hP : ∀ i, ¬ P i → Group.IsSolvable ↥(A i)) {C N : Subgroup G} (hCA : ⨆ i, A i = C)
    (hN : ∀ i, P i → ⁅A i, A i⁆ ≤ N) [(N.subgroupOf C).Normal] :
    Group.IsSolvable (↥C ⧸ N.subgroupOf C) := by
  classical
  subst hCA
  have hk : ∀ i, ∃ k : ℕ, ¬ P i → dsub (A i) k = ⊥ := by
    intro i
    by_cases hi : P i
    · exact ⟨0, fun h => absurd hi h⟩
    · obtain ⟨k, hk⟩ := (hP i hi).solvable
      refine ⟨k, fun _ => ?_⟩
      rw [← map_subtype_derivedSeries, hk, Subgroup.map_bot]
  choose k hk using hk
  cases nonempty_fintype ι
  refine ⟨⟨Finset.univ.sup k + 1, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (N.subgroupOf (⨆ i, A i))),
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', Subgroup.subgroupOf,
    ← Subgroup.map_le_iff_le_comap, map_subtype_derivedSeries, dsub_iSup A hc]
  refine iSup_le fun i => ?_
  by_cases hi : P i
  · exact (dsub_anti (A i) (Nat.le_add_left 1 _)).trans (hN i hi)
  · have h1 : dsub (A i) (Finset.univ.sup k + 1) ≤ dsub (A i) (k i) :=
      dsub_anti (A i) ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))
    exact (h1.trans (hk i hi).le).trans bot_le

end OrbitFamily

section Assembly

variable {X T : Type*} [Group X] [Group T]

private theorem fixSubgroup_conj_eq_centralizer (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem conj_mem_iSup' {ι : Type*} {C : Subgroup X} (F : ι → Subgroup X)
    (hF : ∀ i, ∀ c ∈ C, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i) :
    ∀ c ∈ C, ∀ g ∈ ⨆ i, F i, c * g * c⁻¹ ∈ ⨆ i, F i := by
  intro c hc g hg
  refine Subgroup.iSup_induction F (C := fun x => c * x * c⁻¹ ∈ ⨆ i, F i) hg
    (fun i x hx => Subgroup.mem_iSup_of_mem i (hF i c hc x hx)) (by simp) fun x y hx hy => ?_
  have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hx hy

theorem components_conj_of_orbit_family [Finite T] (π : X →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X) (x : X) {ι : Type*}
    [Finite ι] (A : ι → Subgroup X)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b)
    (hjoin : ⨆ i, A i = Subgroup.centralizer ({x} : Set X))
    (htame : ∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i)) :
    ∀ K : Subgroup T, IsComponentOf K (fixSubgroup (MulAut.conj (π x))) →
      ∃ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∧ K = (⁅A i, A i⁆).map π := by
  classical
  have hfix : ⨆ i, A i = fixSubgroup (MulAut.conj x) := by
    rw [hjoin, fixSubgroup_conj_eq_centralizer]
  have hnormA : ∀ i, ∀ c ∈ ⨆ j, A j, ∀ g ∈ A i, c * g * c⁻¹ ∈ A i := by
    intro i c hc'
    refine Subgroup.iSup_induction A (C := fun c => ∀ g ∈ A i, c * g * c⁻¹ ∈ A i) hc' ?_ ?_ ?_
    · intro j y hy g hg
      by_cases hji : j = i
      · subst hji
        exact (A j).mul_mem ((A j).mul_mem hy hg) ((A j).inv_mem hy)
      · rw [(hc j i hji y hy g hg).eq, mul_inv_cancel_right]
        exact hg
    · intro g hg
      simpa using hg
    · intro u v hu hv g hg
      have e : u * v * g * (u * v)⁻¹ = u * (v * g * v⁻¹) * u⁻¹ := by group
      rw [e]
      exact hu _ (hv g hg)
  have hnormD : ∀ i, ∀ c ∈ ⨆ j, A j, ∀ g ∈ ⁅A i, A i⁆, c * g * c⁻¹ ∈ ⁅A i, A i⁆ := by
    intro i c hc' g hg
    have hmap : (A i).map (MulAut.conj c).toMonoidHom ≤ A i := by
      rintro _ ⟨y, hy, rfl⟩
      exact hnormA i c hc' y hy
    have h1 : (⁅A i, A i⁆).map (MulAut.conj c).toMonoidHom ≤ ⁅A i, A i⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmap hmap
    exact h1 ⟨g, hg, rfl⟩
  let F : {i : ι // CFSG.IsQuasisimple ↥⁅A i, A i⁆} → Subgroup X := fun i => ⁅A i.1, A i.1⁆
  have hFn : ∀ i, ∀ c ∈ fixSubgroup (MulAut.conj x), ∀ g ∈ F i, c * g * c⁻¹ ∈ F i :=
    fun i c hc' g hg => hnormD i.1 c (hfix ▸ hc') g hg
  have hNn := conj_mem_iSup' (C := fixSubgroup (MulAut.conj x)) F hFn
  haveI : ((⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn
  haveI hsol : Group.IsSolvable (↥(fixSubgroup (MulAut.conj x)) ⧸
      (⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x))) := by
    refine isSolvable_quotient_of_orbit_family A hc (fun i => CFSG.IsQuasisimple ↥⁅A i, A i⁆)
      (fun i hi => (htame i).resolve_left hi) hfix fun i hi => ?_
    exact le_iSup F ⟨i, hi⟩
  intro K hK
  obtain ⟨i, hKi⟩ := components_of_centralQuotient π hπ hker (MulAut.conj x) (MulAut.conj (π x))
    (fun g => by simp [MulAut.conj_apply]) F
    (fun i => (commutator_le_self' _).trans ((le_iSup A i.1).trans hfix.le)) hFn (fun i => i.2)
    (QuotientGroup.mk' ((⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x)))) (fun g hg => by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hg) K hK
  exact ⟨i.1, i.2, hKi⟩

end Assembly

section Generic

variable {G : Type*} [Group G]

private theorem map_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) :
    (commutator A).map φ.toMonoidHom = commutator B := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective]

private theorem range_eq_commutator_of_perfect {X B Ab : Type*} [Group X] [Group B]
    [CommGroup Ab] (θ : X →* B) (hX : commutator X = ⊤) (D : B →* Ab) (hD : D.ker ≤ θ.range) :
    θ.range = commutator B := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← hX, _root_.commutator_def, Subgroup.map_commutator,
      _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · refine le_trans ?_ hD
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

private theorem range_comp_eq_commutator {A : Subgroup G} {B X : Type*} [Group B] [Group X]
    (φ : A ≃* B) (θ : X →* B) (hθ : θ.range = commutator B) :
    (A.subtype.comp (φ.symm.toMonoidHom.comp θ)).range = ⁅A, A⁆ := by
  have h1 : (φ.symm.toMonoidHom.comp θ).range = commutator ↥A := by
    rw [MonoidHom.range_comp, hθ]
    exact map_commutator_mulEquiv φ.symm
  rw [MonoidHom.range_comp, h1]
  exact Subgroup.map_subtype_commutator A

private theorem not_isSolvable_of_isQuasisimple_commutator {H : Subgroup G}
    (hQ : CFSG.IsQuasisimple ↥⁅H, H⁆) : ¬ Group.IsSolvable ↥H := by
  intro hs
  haveI := hs
  have hle : ⁅H, H⁆ ≤ H := commutator_le_self' H
  haveI : Group.IsSolvable ↥⁅H, H⁆ :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  haveI : Group.IsPerfect ↥⁅H, H⁆ := hQ.1
  haveI : Nontrivial ↥⁅H, H⁆ := by
    obtain ⟨a, b, hab⟩ := hQ.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [h])⟩
  exact Group.IsPerfect.not_isSolvable ↥⁅H, H⁆ inferInstance

end Generic

section Cover

@[expose] def IsLieFactorOf (P : (X : Type) → Group X → Prop) {r : ℕ} {K : Type} [Field K]
    (H : Subgroup (StatedSp r K)) : Prop :=
  ∃ (X : Type) (inst : Group X) (_ : Finite X) (ψ : X →* StatedSp r K), Function.Injective ψ ∧
    ψ.range = H ∧ P X inst

@[expose] def SpFactorOver (ℓ q : ℕ) (K : Type) [Field K] (X : Type) [inst : Group X] : Prop :=
  letI := inst
  (∃ (m j : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 2 ≤ m ∧ 1 ≤ j ∧ ringChar E = ℓ ∧
      Fintype.card E = q ^ j ∧ (m = 2 → 4 ≤ Fintype.card E) ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin m) E))
  ∨ (∃ (m j q' : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 3 ≤ m ∧ 1 ≤ j ∧
      ringChar E = ℓ ∧ q' = q ^ j ∧ Fintype.card E = q' ^ 2 ∧ (m, q') ≠ (3, 2) ∧
      Nonempty (X ≃* ↥(StatedSU m q' E)))
  ∨ (q = Nat.card K ∧ ringChar K = ℓ ∧ ∃ s : ℕ, 2 ≤ s ∧ (s, Nat.card K) ≠ (2, 2) ∧
      Nonempty (X ≃* StatedSp s K))
  ∨ (q = Nat.card K ∧ ringChar K = ℓ ∧ Nat.card K = 2 ∧
      Nonempty (X ≃* ↥(commutator (StatedSp 2 K))))

private abbrev GoodOver (a6 : Prop) (ℓ : ℕ) {r : ℕ} {K : Type} [Field K]
    (H : Subgroup (StatedSp r K)) : Prop :=
  IsLieFactorOf (fun X inst => by
    letI := inst
    exact (LieFactorData ℓ X ∧
        (a6 → Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6)) →
          Nat.card K = 2)) ∧
      SpFactorOver ℓ (Nat.card K) K X) H

private theorem exists_cover_of_range {G T : Type*} [Group G] [Group T] (π : G →* T)
    (hker : π.ker ≤ Subgroup.center G) {X : Type*} [Group X] (ψ : X →* G)
    (hψ : Function.Injective ψ) {H : Subgroup G} (hH : ψ.range = H) :
    ∃ f : X →* ↥(H.map π), Function.Surjective f ∧ f.ker ≤ Subgroup.center X := by
  subst hH
  refine ⟨(π.subgroupMap ψ.range).comp ψ.rangeRestrict,
    (MonoidHom.subgroupMap_surjective _ _).comp ψ.rangeRestrict_surjective, fun x hx => ?_⟩
  have h1 : π (ψ x) = 1 := congrArg Subtype.val hx
  have h2 : ψ x ∈ Subgroup.center G := hker h1
  rw [Subgroup.mem_center_iff]
  intro y
  apply hψ
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.1 h2 (ψ y)

end Cover

section Export

theorem components_of_orbit_family_lieFactor {P : (X : Type) → Group X → Prop} {r : ℕ}
    {K : Type} [Field K] [Finite K]
    (x : StatedSp r K) {ι : Type*} [Finite ι] (A : ι → Subgroup (StatedSp r K))
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b)
    (hjoin : ⨆ i, A i = Subgroup.centralizer ({x} : Set (StatedSp r K)))
    (htame : ∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i))
    (hgood : ∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ → IsLieFactorOf P ⁅A i, A i⁆) :
    ∀ K' : Subgroup (StatedProj (StatedSp r K)),
      IsComponentOf K' (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))) →
      ∃ (X : Type) (inst : Group X) (_ : Finite X), P X inst ∧
        (∃ f : X →* ↥K', Function.Surjective f ∧ f.ker ≤ Subgroup.center X) := by
  have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hcomp := components_conj_of_orbit_family (SymplecticFlag.proj r K)
    SymplecticHigher.proj_surjective hZc x A hc hjoin htame
  intro K' hK'
  obtain ⟨i, hi, rfl⟩ := hcomp K' hK'
  obtain ⟨X, inst, hfin, ψ, hψ, hrange, hX⟩ := hgood i hi
  exact ⟨X, inst, hfin, hX,
    exists_cover_of_range (SymplecticFlag.proj r K) hZc ψ hψ hrange⟩

end Export

section SpFactor

variable {G : Type*} [Group G]

private theorem isSolvable_sl_two_of_card_lt_four {E : Type} [Field E] [Fintype E]
    (h : Fintype.card E < 4) : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) := by
  have hcard : Nat.card E = 2 ∨ Nat.card E = 3 := by
    have h2 : 1 < Fintype.card E := Fintype.one_lt_card
    rw [Nat.card_eq_fintype_card]
    omega
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) E) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable E hcard
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) E →* _))
    Matrix.SpecialLinearGroup.toGL_injective

private theorem four_le_card_of_equiv_sl_two {E : Type} [Field E] [Fintype E] {A : Subgroup G}
    (φ : A ≃* Matrix.SpecialLinearGroup (Fin 2) E) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    4 ≤ Fintype.card E := by
  by_contra hlt
  haveI := isSolvable_sl_two_of_card_lt_four (not_le.1 hlt)
  exact not_isSolvable_of_isQuasisimple_commutator hQ
    (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)

private theorem ringChar_eq_three_of_card_eq_nine {E : Type} [Field E] [Fintype E]
    (h9 : Fintype.card E = 9) : ringChar E = 3 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card E (ringChar E)
  have hdvd : ringChar E ∣ 3 ^ 2 := by
    have : ringChar E ∣ ringChar E ^ (n : ℕ) := dvd_pow_self _ n.ne_zero
    rw [← hn, h9] at this
    simpa using this
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)

private theorem ringChar_eq_two_of_card_eq_two {E : Type} [Field E] [Fintype E]
    (h2 : Fintype.card E = 2) : ringChar E = 2 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card E (ringChar E)
  have hdvd : ringChar E ∣ 2 := by
    have : ringChar E ∣ ringChar E ^ (n : ℕ) := dvd_pow_self _ n.ne_zero
    rwa [← hn, h2] at this
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd

private theorem range_equiv_eq_commutator {X B : Type*} [Group X] [Group B] (e : X ≃* B)
    (hX : commutator X = ⊤) : e.toMonoidHom.range = commutator B := by
  rw [MonoidHom.range_eq_map, ← map_commutator_mulEquiv e, hX]

private theorem good_sp {a6 : Prop} {r : ℕ} {K : Type} [Field K] [Finite K] {ℓ : ℕ}
    (hKℓ : ringChar K = ℓ) (hℓ3 : a6 → ℓ ≠ 3) (hSL : SLFactorFacts) (hA6 : a6 → SLAltSixFacts)
    (hSp : SpFactorFacts) (hSp6 : a6 → SpAltSixFacts) (hSp42 : SpFourTwoFacts)
    {A : Subgroup (StatedSp r K)} {s : ℕ} (hs : 1 ≤ s) (φ : A ≃* StatedSp s K)
    (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) : GoodOver a6 ℓ ⁅A, A⁆ := by
  classical
  haveI := Fintype.ofFinite K
  subst hKℓ
  by_cases hs1 : s = 1
  · subst hs1
    let e1 : Matrix.SpecialLinearGroup (Fin 2) K ≃* StatedSp 1 K :=
      CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K
    have h4 : 4 ≤ Fintype.card K := four_le_card_of_equiv_sl_two (φ.trans e1.symm) hQ
    have hX := hSL K 2 le_rfl (fun _ => h4)
    have hfac : SpFactorOver (ringChar K) (Nat.card K) K
        (Matrix.SpecialLinearGroup (Fin 2) K) := by
      refine Or.inl ⟨2, 1, K, inferInstance, inferInstance, le_rfl, le_rfl, rfl, ?_, ?_,
        ⟨MulEquiv.refl _⟩⟩
      · rw [Nat.card_eq_fintype_card, pow_one]
      · intro _
        exact h4
    refine ⟨Matrix.SpecialLinearGroup (Fin 2) K, inferInstance, inferInstance,
      A.subtype.comp (φ.symm.toMonoidHom.comp e1.toMonoidHom),
      Subtype.val_injective.comp (φ.symm.injective.comp e1.injective),
      range_comp_eq_commutator φ _ (range_equiv_eq_commutator e1 hX.perfect),
      ⟨⟨hX, ?_⟩, hfac⟩⟩
    intro h6 ⟨e⟩
    exfalso
    obtain ⟨-, h9⟩ := hA6 h6 K 2 le_rfl ⟨e⟩
    exact hℓ3 h6 (ringChar_eq_three_of_card_eq_nine h9)
  · have hs2 : 2 ≤ s := by omega
    by_cases hspecial : s = 2 ∧ Fintype.card K = 2
    · obtain ⟨rfl, hc2⟩ := hspecial
      have hX := hSp42 K hc2
      have h2 : ringChar K = 2 := ringChar_eq_two_of_card_eq_two hc2
      have hfac : SpFactorOver (ringChar K) (Nat.card K) K
          ↥(commutator ↥(StatedSp 2 K)) := by
        refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_, ⟨MulEquiv.refl _⟩⟩))
        rw [Nat.card_eq_fintype_card]
        exact hc2
      refine ⟨↥(commutator ↥(StatedSp 2 K)), inferInstance, inferInstance,
        A.subtype.comp (φ.symm.toMonoidHom.comp (commutator ↥(StatedSp 2 K)).subtype),
        Subtype.val_injective.comp (φ.symm.injective.comp Subtype.val_injective),
        range_comp_eq_commutator φ _ (Subgroup.range_subtype _),
        ⟨⟨h2 ▸ hX, ?_⟩, hfac⟩⟩
      intro _ _
      rw [Nat.card_eq_fintype_card]
      exact hc2
    · have hne : (s, Fintype.card K) ≠ (2, 2) := fun h =>
        hspecial ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      have hne' : (s, Nat.card K) ≠ (2, 2) := by
        rwa [Nat.card_eq_fintype_card]
      have hX := hSp K s hs2 hne
      have hθ : (MonoidHom.id ↥(StatedSp s K)).range = commutator ↥(StatedSp s K) := by
        rw [MonoidHom.range_eq_top.2 Function.surjective_id, hX.perfect]
      have hfac : SpFactorOver (ringChar K) (Nat.card K) K ↥(StatedSp s K) :=
        Or.inr (Or.inr (Or.inl ⟨rfl, rfl, s, hs2, hne', ⟨MulEquiv.refl _⟩⟩))
      refine ⟨↥(StatedSp s K), inferInstance, inferInstance,
        A.subtype.comp (φ.symm.toMonoidHom.comp (MonoidHom.id _)),
        Subtype.val_injective.comp (φ.symm.injective.comp Function.injective_id),
        range_comp_eq_commutator φ _ hθ, ⟨⟨hX, ?_⟩, hfac⟩⟩
      intro h6 ⟨e⟩
      exact ((hSp6 h6 K s hs2 hne).false e).elim

end SpFactor

section GLFactor

variable {G : Type*} [Group G]

private theorem isSolvable_gl_of_le_one {E : Type*} [Field E] {m : ℕ} (hm : m ≤ 1) :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) E) := by
  refine Group.isSolvable_of_comm fun a b => Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · exact Matrix.ext fun i => i.elim0
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one,
      Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact mul_comm _ _

private theorem good_gl {a6 : Prop} {r : ℕ} {K : Type} [Field K] {ℓ : ℕ} {E : Type} [Field E]
    [Fintype E] {j : ℕ} (hEℓ : ringChar E = ℓ) (hj : 1 ≤ j)
    (hEc : Fintype.card E = Nat.card K ^ j) (hℓ3 : a6 → ℓ ≠ 3) (h4 : 4 ≤ Fintype.card E)
    (hSL : SLFactorFacts) (hA6 : a6 → SLAltSixFacts) {m : ℕ} {A : Subgroup (StatedSp r K)}
    (φ : A ≃* Matrix.GeneralLinearGroup (Fin m) E) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    GoodOver a6 ℓ ⁅A, A⁆ := by
  classical
  have hm : 2 ≤ m := by
    by_contra hlt
    haveI := isSolvable_gl_of_le_one (E := E) (not_le.1 hlt |> Nat.lt_succ_iff.1)
    exact not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  have hX := hSL E m hm (fun _ => h4)
  let θ : Matrix.SpecialLinearGroup (Fin m) E →* Matrix.GeneralLinearGroup (Fin m) E :=
    Matrix.SpecialLinearGroup.toGL
  have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin m) E) := by
    refine range_eq_commutator_of_perfect θ hX.perfect
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin m) E →* Eˣ) fun g hg => ?_
    rw [MonoidHom.mem_ker] at hg
    have hdet : (g : Matrix (Fin m) (Fin m) E).det = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  have hfac : SpFactorOver ℓ (Nat.card K) K (Matrix.SpecialLinearGroup (Fin m) E) :=
    Or.inl ⟨m, j, E, inferInstance, inferInstance, hm, hj, hEℓ, hEc, (fun _ => h4),
      ⟨MulEquiv.refl _⟩⟩
  refine ⟨Matrix.SpecialLinearGroup (Fin m) E, inferInstance, inferInstance,
    A.subtype.comp (φ.symm.toMonoidHom.comp θ),
    Subtype.val_injective.comp (φ.symm.injective.comp Matrix.SpecialLinearGroup.toGL_injective),
    range_comp_eq_commutator φ θ hθ, ⟨⟨hEℓ ▸ hX, ?_⟩, hfac⟩⟩
  intro h6 ⟨e⟩
  exfalso
  obtain ⟨-, h9⟩ := hA6 h6 E m hm ⟨e⟩
  exact hℓ3 h6 (hEℓ.symm.trans (ringChar_eq_three_of_card_eq_nine h9))

end GLFactor

section GUFactor

private theorem card_primeFactors_two_three (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 ^ a * 3 ^ b).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow ha Nat.prime_two, Nat.primeFactors_prime_pow hb Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

private theorem isSolvable_of_card_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G :=
  isSolvable_of_card_primeFactors_le_two (h ▸ card_primeFactors_two_three a b ha hb)

private theorem finite_generalLinearGroup {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] : Finite (LinearMap.GeneralLinearGroup E W) := by
  have := hE.finite
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  exact Finite.of_injective _ Units.val_injective

private theorem isSolvable_sesqUnitaryGroup_of_small {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft)
    (hsmall : Module.finrank E W ≤ 1 ∨ (¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧
      (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)))) : Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
  have hq2 : 2 ≤ ℓ ^ g := by
    have := Nat.one_lt_pow (by have := hE.one_le; omega : g ≠ 0) hE.prime.one_lt
    omega
  haveI := finite_generalLinearGroup hE (W := W)
  by_cases hm : 2 ≤ Module.finrank E W
  · have hq : ¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧ (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)) := by
      rcases hsmall with h | h
      · omega
      · exact h
    obtain ⟨hcard, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
      rfl (by omega : 1 ≤ Module.finrank E W)
    have hexc : (Module.finrank E W = 2 ∧ ℓ ^ g = 2) ∨ (Module.finrank E W = 2 ∧ ℓ ^ g = 3) ∨
        (Module.finrank E W = 3 ∧ ℓ ^ g = 2) := by
      by_contra hn
      push Not at hn
      obtain ⟨h1, h2, h3⟩ := hn
      refine hq ⟨fun h2' => ?_, fun h3' => ?_⟩
      · by_contra hlt
        rcases (show ℓ ^ g = 2 ∨ ℓ ^ g = 3 by omega) with hQ | hQ
        · exact h1 h2' hQ
        · exact h2 h2' hQ
      · by_contra hlt
        exact h3 h3' (by omega)
    rcases hexc with ⟨hm2, hQ⟩ | ⟨hm2, hQ⟩ | ⟨hm3, hQ⟩
    · rw [hm2, hQ] at hcard
      have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
      have h18 : Nat.card ↥(sesqUnitaryGroup Hf) = 18 := by exact_mod_cast hcard.trans e
      exact isSolvable_of_card_two_three (a := 1) (b := 2) (by norm_num) (by norm_num)
        (by rw [h18]; norm_num)
    · rw [hm2, hQ] at hcard
      have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 96 := by decide +kernel
      have h96 : Nat.card ↥(sesqUnitaryGroup Hf) = 96 := by exact_mod_cast hcard.trans e
      exact isSolvable_of_card_two_three (a := 5) (b := 1) (by norm_num) (by norm_num)
        (by rw [h96]; norm_num)
    · rw [hm3, hQ] at hcard
      have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
      have h648 : Nat.card ↥(sesqUnitaryGroup Hf) = 648 := by exact_mod_cast hcard.trans e
      exact isSolvable_of_card_two_three (a := 3) (b := 4) (by norm_num) (by norm_num)
        (by rw [h648]; norm_num)
  · refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
    have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W)
      (by omega) ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
      ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
    simpa [Subgroup.coe_mul, Units.val_mul] using this

end GUFactor

section GUGood

private theorem exists_range_of_special_equiv {ℓ g : ℕ} {G : Type*} [Group G] {E : Type}
    [Field E] (hE : UnitaryFieldData ℓ g E) {V : Type*} [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (hm1 : 1 ≤ Module.finrank E V) {A : Subgroup G}
    (φ : A ≃* sesqUnitaryGroup Hf) {X : Type} [Group X] (hXp : commutator X = ⊤)
    (e : ↥(sesqSpecialUnitaryGroup Hf) ≃* X) :
    ∃ ψ : X →* G, Function.Injective ψ ∧ ψ.range = ⁅A, A⁆ := by
  obtain ⟨-, -, -, -, hker, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl hm1
  let θ : X →* ↥(sesqUnitaryGroup Hf) :=
    (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf)).comp e.symm.toMonoidHom
  have hθi : Function.Injective θ :=
    (Subgroup.inclusion_injective (sesqSpecialUnitaryGroup_le Hf)).comp e.symm.injective
  have hθ : θ.range = commutator ↥(sesqUnitaryGroup Hf) := by
    refine range_eq_commutator_of_perfect θ hXp (CFSG.LinearGroups.unitaryDet Hf) fun u hu => ?_
    rw [hker] at hu
    exact ⟨e ⟨u, hu⟩, Subtype.ext (by simp [θ])⟩
  exact ⟨A.subtype.comp (φ.symm.toMonoidHom.comp θ),
    Subtype.val_injective.comp (φ.symm.injective.comp hθi), range_comp_eq_commutator φ θ hθ⟩

open CFSG.RankThree.CentralLift CFSG.RankThree.Classical CFSG.ClassicalGroups.UnitaryFlag in
private theorem good_gu {a6 : Prop} {r : ℕ} {K : Type} [Field K] {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {f d : ℕ} (hK : Nat.card K = ℓ ^ f) (hd : 1 ≤ d)
    (hg : g = f * d) (hℓ3 : a6 → ℓ ≠ 3) (hSL : SLFactorFacts)
    (hA6 : a6 → SLAltSixFacts) (hSU : SUFactorFacts) (hSU6 : a6 → SUAltSixFacts) {V : Type}
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] {Hf : V →ₛₗ[hE.bar] V →ₗ[E] E}
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft) {m : ℕ} (b : Module.Basis (Fin m) E V)
    (hb : ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0) {A : Subgroup (StatedSp r K)}
    (φ : A ≃* sesqUnitaryGroup Hf) (hQ : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    GoodOver a6 ℓ ⁅A, A⁆ := by
  classical
  have hfin : Module.finrank E V = m := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hsolv : ¬ (Module.finrank E V ≤ 1 ∨ ¬ ((Module.finrank E V = 2 → 4 ≤ ℓ ^ g) ∧
      (Module.finrank E V = 3 → 3 ≤ ℓ ^ g))) := fun h => by
    haveI := isSolvable_sesqUnitaryGroup_of_small hE hHf hHfl h
    exact not_isSolvable_of_isQuasisimple_commutator hQ
      (Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective)
  rw [hfin] at hsolv
  push Not at hsolv
  obtain ⟨hm, hq2, hq3⟩ := hsolv
  haveI := hE.finite
  haveI := Fintype.ofFinite E
  haveI : Fact ℓ.Prime := ⟨hE.prime⟩
  haveI : CharP E ℓ := hE.charP
  have hEℓ : ringChar E = ℓ := ringChar.eq E ℓ
  have hEcard : Fintype.card E = (ℓ ^ g) ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_eq_sq
  haveI : Finite ↥hE.fixedField := inferInstance
  haveI : Fintype ↥hE.fixedField := Fintype.ofFinite _
  have hFcard : Fintype.card ↥hE.fixedField = ℓ ^ g := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_fixedField
  haveI : CharP ↥hE.fixedField ℓ := charP_of_card_eq_prime_pow (f := g) hFcard
  have hFℓ : ringChar ↥hE.fixedField = ℓ := ringChar.eq _ ℓ
  have hFq : Fintype.card ↥hE.fixedField = Nat.card K ^ d := by
    rw [hFcard, hg, hK, pow_mul]
  have hEF : Fintype.card E = Fintype.card ↥hE.fixedField ^ 2 := by
    rw [hEcard, hFcard]
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    obtain rfl : m = 2 := by omega
    obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hfin
    have hX := hSL ↥hE.fixedField 2 le_rfl (fun _ => by rw [hFcard]; exact hq2 rfl)
    obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv hE hHf hHfl (by omega) φ hX.perfect e
    have hX' : LieFactorData ℓ (Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField) := by
      rw [hFℓ] at hX
      exact hX
    have hfac : SpFactorOver ℓ (Nat.card K) K
        (Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField) :=
      Or.inl ⟨2, d, ↥hE.fixedField, inferInstance, inferInstance, le_rfl, hd, hFℓ, hFq,
        (fun _ => by rw [hFcard]; exact hq2 rfl), ⟨MulEquiv.refl _⟩⟩
    refine ⟨Matrix.SpecialLinearGroup (Fin 2) ↥hE.fixedField, inferInstance, inferInstance, ψ,
      hψi, hψ, ⟨⟨hX', ?_⟩, hfac⟩⟩
    intro h6 ⟨e'⟩
    exfalso
    obtain ⟨-, h9⟩ := hA6 h6 ↥hE.fixedField 2 le_rfl ⟨e'⟩
    exact hℓ3 h6 (hFℓ.symm.trans (ringChar_eq_three_of_card_eq_nine h9))
  ·
    have hnq : (m, ℓ ^ g) ≠ (3, 2) := by
      intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      have := hq3 h1
      omega
    have hX := hSU E m (ℓ ^ g) hEcard hm3 hnq
    obtain ⟨e⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin m) (Fin m) E)) (fun i j => by rw [hb i j, Matrix.one_apply])
    have hSUeq : StatedSU m (ℓ ^ g) E = gramSU hE (1 : Matrix (Fin m) (Fin m) E) :=
      unitarySU_eq_gramSU hE m
    let e' : ↥(sesqSpecialUnitaryGroup Hf) ≃* ↥(StatedSU m (ℓ ^ g) E) :=
      e.trans (MulEquiv.subgroupCongr hSUeq.symm)
    obtain ⟨ψ, hψi, hψ⟩ := exists_range_of_special_equiv hE hHf hHfl (by omega) φ hX.perfect e'
    have hX' : LieFactorData ℓ ↥(StatedSU m (ℓ ^ g) E) := by
      rw [hEℓ] at hX
      exact hX
    have hq' : ℓ ^ g = Nat.card K ^ d := by
      rw [← hFcard, hFq]
    have hfac : SpFactorOver ℓ (Nat.card K) K ↥(StatedSU m (ℓ ^ g) E) :=
      Or.inr (Or.inl ⟨m, d, ℓ ^ g, E, inferInstance, inferInstance, hm3, hd, hEℓ, hq',
        hEcard, hnq, ⟨MulEquiv.refl _⟩⟩)
    exact ⟨↥(StatedSU m (ℓ ^ g) E), inferInstance, inferInstance, ψ, hψi, hψ,
      ⟨⟨hX', fun h6 ⟨e''⟩ => ((hSU6 h6 E m (ℓ ^ g) hEcard hm3).false e'').elim⟩, hfac⟩⟩

end GUGood

section Blocks

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r : ℕ} {K : Type} [Field K]

private theorem good_spSupported_of_factor {a6 : Prop} [Finite K] {ℓ f p : ℕ} (hp3 : 3 ≤ p)
    (hK : Nat.card K = ℓ ^ f) (hKℓ : ringChar K = ℓ) (hℓ3 : a6 → ℓ ≠ 3)
    (hSL : SLFactorFacts) (hA6 : a6 → SLAltSixFacts)
    (hSU : SUFactorFacts) (hSU6 : a6 → SUAltSixFacts) (hSp : SpFactorFacts)
    (hSp6 : a6 → SpAltSixFacts) (hSp42 : SpFourTwoFacts) (hq : 2 ≤ ℓ ^ f) {x : StatedSp r K}
    {a : StatedProj (StatedSp r K)} (hsq : Squarefree (minpoly K (spEnd x)))
    (blocks : SpPrimaryBlocks ℓ f p x a) (h : primaryFactors (spEnd x))
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆) :
    GoodOver a6 ℓ ⁅spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}⁆ := by
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    rw [hO] at hQ ⊢
    by_cases h1 : (h : K[X]) = X - 1
    · obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      have : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hm)
      obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      have hs1 : 1 ≤ s := by
        have := Module.finrank_pos (R := K) (M := primaryComponent (spEnd x) (X - 1))
        omega
      exact good_sp hKℓ hℓ3 hSL hA6 hSp hSp6 hSp42 hs1 (φ.trans e) hQ
    · obtain ⟨d, hdeg, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, hφ⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      have hd : 1 ≤ d := by
        have hpos : 1 ≤ (h : K[X]).natDegree :=
          Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
        omega
      exact good_gu (f := f) (d := d) hE hK hd rfl hℓ3 hSL hA6 hSU hSU6 hHf hHfl e he φ hQ
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ⟩ := hP.matrixFactor
    haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    haveI := Fintype.ofFinite (AdjoinRoot (h : K[X]))
    have hEℓ : ringChar (AdjoinRoot (h : K[X])) = ℓ :=
      (Algebra.ringChar_eq K (AdjoinRoot (h : K[X]))).symm.trans hKℓ
    have hdeg : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    have hEc : Fintype.card (AdjoinRoot (h : K[X])) = Nat.card K ^ (h : K[X]).natDegree := by
      rw [Fintype.card_eq_nat_card, hP.card_field, hK]
    have h4 : 4 ≤ Fintype.card (AdjoinRoot (h : K[X])) := by
      have hN : ℓ ^ f ≤ (ℓ ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
      have hle := Nat.le_of_dvd (by omega) hP.dvd
      rw [Fintype.card_eq_nat_card, hP.card_field]
      omega
    exact good_gl (j := (h : K[X]).natDegree) hEℓ hdeg hEc hℓ3 h4 hSL hA6 φ hQ

end Blocks

section NoThree

open CFSG.LieType.Steinberg.CentralExt
open scoped commutatorElement

private theorem commutatorElement_central_mul {G : Type*} [Group G] {k a b : G}
    (hk : k ∈ Subgroup.center G) : ⁅k * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hc : k * (a * b * a⁻¹) * k⁻¹ = a * b * a⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.1 hk _).symm
  calc k * a * b * (k * a)⁻¹ * b⁻¹ = (k * (a * b * a⁻¹) * k⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hc]

private theorem commutatorElement_mul_central {G : Type*} [Group G] {k a b : G}
    (hk : k ∈ Subgroup.center G) : ⁅a, k * b⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_central_mul hk, commutatorElement_inv]

private theorem noThreeCover_statedProj_sp_two
    {r : ℕ} (hr : 1 ≤ r) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    NoThreeCover (StatedProj (StatedSp r K)) := by
  intro Y _ _ hY ⟨e⟩ h3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 2 := by
    haveI := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK]; simp)
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  have hker : (SymplecticFlag.proj r K).ker = ⊥ := by
    rw [SymplecticHigher.ker_proj, ← Subgroup.card_eq_one, card_spScalars_eq_gcd K hr, hK]
    norm_num
  let pe : StatedSp r K ≃* StatedProj (StatedSp r K) :=
    MulEquiv.ofBijective (SymplecticFlag.proj r K)
      ⟨(MonoidHom.ker_eq_bot_iff _).1 hker, SymplecticHigher.proj_surjective⟩
  let ε : Y →* StatedSp r K :=
    pe.symm.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)))
  have hε : Function.Surjective ε :=
    pe.symm.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hεker : ε.ker = Subgroup.center Y := by
    ext y
    rw [MonoidHom.mem_ker]
    change pe.symm (e (QuotientGroup.mk' (Subgroup.center Y) y)) = 1 ↔ _
    rw [map_eq_one_iff pe.symm pe.symm.injective, map_eq_one_iff e e.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcen : Subgroup.center Y ≤ Subgroup.center Y := le_rfl
  set N := CoprimeSplit.copPart 3 (Subgroup.center Y) hcen with hN
  have hNker : N ≤ ε.ker := fun n hn => by rw [hεker]; exact hn.1
  let π₁ : Y ⧸ N →* StatedSp r K := QuotientGroup.lift N ε hNker
  have hπ₁e : ∀ y : Y, π₁ (y : Y ⧸ N) = ε y := fun y => rfl
  have hπ₁ : Function.Surjective π₁ := fun g => by
    obtain ⟨y, rfl⟩ := hε g
    exact ⟨(y : Y ⧸ N), rfl⟩
  have hker₁ : π₁.ker ≤ Subgroup.center (Y ⧸ N) := by
    intro u hu
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
    have hy : y ∈ ε.ker := by
      rw [MonoidHom.mem_ker, ← hπ₁e]
      exact hu
    rw [hεker] at hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hy z']
  have hp₁ : IsPGroup 3 π₁.ker := by
    rintro ⟨u, hu⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
    have hy : y ∈ ε.ker := by
      rw [MonoidHom.mem_ker, ← hπ₁e]
      exact hu
    rw [hεker] at hy
    obtain ⟨a, ha⟩ := CoprimeSplit.exists_pow_prime_pow_mem_copPart (p := 3) hcen hy
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ha
  have hcop : Nat.Coprime 2 (Nat.card π₁.ker) := by
    obtain ⟨n, hn⟩ := hp₁.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨σ, hσ⟩ := SpClosed.sp_exists_section_of_coprime (p := 2) (Y ⧸ N) π₁ hπ₁ hker₁ hcop
  have : Group.IsPerfect (Y ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hdec : ∀ u : Y ⧸ N, ∃ k ∈ Subgroup.center (Y ⧸ N), u = k * σ (π₁ u) := by
    intro u
    refine ⟨u * (σ (π₁ u))⁻¹, hker₁ ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
  have hcomm : commutator (Y ⧸ N) ≤ σ.range := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro u _ v _
    have key : ⁅u, v⁆ = ⁅σ (π₁ u), σ (π₁ v)⁆ := by
      obtain ⟨k₁, hk₁, hu⟩ := hdec u
      obtain ⟨k₂, hk₂, hv⟩ := hdec v
      calc ⁅u, v⁆ = ⁅k₁ * σ (π₁ u), k₂ * σ (π₁ v)⁆ := by rw [← hu, ← hv]
        _ = ⁅σ (π₁ u), σ (π₁ v)⁆ := by
          rw [commutatorElement_central_mul hk₁, commutatorElement_mul_central hk₂]
    rw [key, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  have hrange : σ.range = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup (Y ⧸ N)) = commutator (Y ⧸ N) := Group.IsPerfect.commutator_eq_top.symm
      _ ≤ σ.range := hcomm
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Y) 3 h3
  have hzN : (z : Y) ∉ N := fun hzN => by
    have h := hzN.2
    rw [Subgroup.orderOf_coe, hz] at h
    norm_num at h
  have hmk : ((z : Y) : Y ⧸ N) ∈ π₁.ker := by
    rw [MonoidHom.mem_ker, hπ₁e]
    have : (z : Y) ∈ ε.ker := by rw [hεker]; exact z.2
    exact this
  obtain ⟨a, ha⟩ : ((z : Y) : Y ⧸ N) ∈ σ.range := by rw [hrange]; trivial
  have h1 : a = 1 := by
    calc a = π₁ (σ a) := (hσ a).symm
      _ = π₁ ((z : Y) : Y ⧸ N) := by rw [ha]
      _ = 1 := hmk
  apply hzN
  have : ((z : Y) : Y ⧸ N) = 1 := by rw [← ha, h1, map_one]
  exact (QuotientGroup.eq_one_iff _).1 this

end NoThree

section TopTame

private theorem tame_statedSp {s : ℕ} (hs : 1 ≤ s) {K : Type} [Field K] [Finite K] :
    CFSG.IsQuasisimple ↥(commutator (StatedSp s K)) ∨ Group.IsSolvable (StatedSp s K) := by
  by_cases hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨
      (Nat.card K = 2 ∧ 3 ≤ s)
  · left
    have h := CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs hq
    have h1 : commutator (StatedSp s K) = ⊤ := Group.isPerfect_def.mp h.1
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr h1).trans Subgroup.topEquiv).symm h
  · have hK2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
    have hK4 : Nat.card K < 4 := by
      by_contra h
      exact hq (Or.inl (Or.inr (by omega)))
    have h3 : Nat.card K = 3 → s < 2 := fun h => by
      by_contra h'
      exact hq (Or.inr (Or.inl ⟨h, by omega⟩))
    have h2 : Nat.card K = 2 → s < 3 := fun h => by
      by_contra h'
      exact hq (Or.inr (Or.inr ⟨h, by omega⟩))
    have hcard := SymplecticFlag.card_statedSp (K := K) s
    rcases (show Nat.card K = 2 ∨ Nat.card K = 3 by omega) with hK | hK
    · rcases (show s = 1 ∨ s = 2 by have := h2 hK; omega) with rfl | rfl
      · right
        refine isSolvable_of_card_two_three (a := 1) (b := 1) (by norm_num) (by norm_num) ?_
        rw [hcard, hK]
        norm_num [Finset.Icc_self]
      · left
        have hd : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
        obtain ⟨E⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hK
          (CFSG.RankThree.Classical.spForm_isAlt (r := 2) (K := K))
          (CFSG.RankThree.Classical.spForm_nondegenerate (r := 2) (K := K)) hd
        let e₀ : StatedSp 2 K ≃* sesqUnitaryGroup (CFSG.RankThree.Classical.spForm 2 K) :=
          (MonoidHom.ofInjective
            (CFSG.RankThree.Classical.spLin_injective (r := 2) (K := K))).trans
            (MulEquiv.subgroupCongr (CFSG.RankThree.Classical.range_spLin (r := 2) (K := K)))
        exact (CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour (e₀.trans E)).1
    · have hs1 : s = 1 := by have := h3 hK; omega
      subst hs1
      right
      refine isSolvable_of_card_two_three (a := 3) (b := 1) (by norm_num) (by norm_num) ?_
      rw [hcard, hK]
      norm_num [Finset.Icc_self]

private theorem tame_top_statedSp {r : ℕ} (hr : 1 ≤ r) {K : Type} [Field K] [Finite K] :
    CFSG.IsQuasisimple ↥⁅(⊤ : Subgroup ↥(StatedSp r K)), (⊤ : Subgroup ↥(StatedSp r K))⁆ ∨
      Group.IsSolvable ↥(⊤ : Subgroup ↥(StatedSp r K)) := by
  rcases tame_statedSp (s := r) (K := K) hr with h | h
  · left
    rw [← _root_.commutator_def]
    exact h
  · right
    let e : ↥(StatedSp r K) ≃* ↥(⊤ : Subgroup ↥(StatedSp r K)) := Subgroup.topEquiv.symm
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

end TopTame

section Main

open Polynomial CFSG.RankThree.Classical in
theorem lieCompsCore_conj_sp_card {a6 : Prop} (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    (hSp : SpFactorFacts) (hSp42 : SpFourTwoFacts) (hA6 : a6 → SLAltSixFacts)
    (hSU6 : a6 → SUAltSixFacts) (hSp6 : a6 → SpAltSixFacts) {p r ℓ f : ℕ} {K : Type} [Field K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 1 ≤ r) (hpℓ : p ≠ ℓ) (hℓ3 : a6 → ℓ ≠ 3) (x : StatedSp r K) (hx : x ^ p = 1) :
    PerfectInLayer (MulAut.conj (SymplecticFlag.proj r K x)) ∧
      ∀ K' : Subgroup (StatedProj (StatedSp r K)),
        IsComponentOf K' (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))) →
        ∃ (X : Type) (inst : Group X) (_ : Finite X),
          (LieFactorData ℓ X ∧
            (a6 → Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6)) →
              Nat.card K = 2)) ∧
          SpFactorOver ℓ (Nat.card K) K X ∧
          (∃ f : X →* ↥K', Function.Surjective f ∧ f.ker ≤ Subgroup.center X) := by
  classical
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  have hq : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) hcardK
  have hKℓ : ringChar K = ℓ := ringChar.eq K ℓ
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  refine ⟨LieSemisimple.perfectInLayer_conj_sp hℓ hf hK hr hp hp2 hpℓ x hx, ?_⟩
  by_cases hx1 : x = 1
  · subst hx1
    intro K' hK'
    obtain ⟨X, inst, hfin, ⟨⟨hX, hA6'⟩, hfac⟩, hf'⟩ :=
      components_of_orbit_family_lieFactor (r := r) 1
        (fun _ : Unit => (⊤ : Subgroup (StatedSp r K)))
        (fun i j hij => absurd (Subsingleton.elim i j) hij)
        (by ext g; simp [Subgroup.mem_centralizer_iff]) (fun _ => tame_top_statedSp hr)
        (fun _ hQ => good_sp hKℓ hℓ3 hSL hA6 hSp hSp6 hSp42 hr Subgroup.topEquiv hQ) K' hK'
    exact ⟨X, inst, hfin, ⟨hX, hA6'⟩, hfac, hf'⟩
  · have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
      rw [SymplecticHigher.ker_proj]
      exact SymplecticHigher.spScalars_le_center
    have hZp : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) p := by
      rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
      exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _)
        ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have ha1 : SymplecticFlag.proj r K x ≠ 1 := fun h =>
      hx1 (CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime (a := 1) (b := 0)
        (SymplecticFlag.proj r K) hZc hZp (by rwa [pow_one]) (by simp)
        (by rw [h, map_one]))
    have ha : orderOf (SymplecticFlag.proj r K x) = p :=
      orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
    have hxp : orderOf x = p := orderOf_eq_prime hx hx1
    have blocks := (symplectic_cross_prime_primary_centralizer_blocks hℓ hf hK hp hp2 hpℓ hr _
      ha).2 x rfl hxp
    have hpK : (p : K) ≠ 0 := by
      intro h
      rw [CharP.cast_eq_zero_iff K ℓ] at h
      exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
    have hsq := (altPrimaryData_spLin hpK hx).squarefree
    haveI : Finite (reciprocalOrbits (spEnd x)) :=
      (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
    obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
    intro K' hK'
    obtain ⟨X, inst, hfin, ⟨⟨hX, hA6'⟩, hfac⟩, hf'⟩ :=
      components_of_orbit_family_lieFactor x
        (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
        (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
        hjoin (fun O => LieSemisimple.quasisimple_or_solvable_spSupported hp3 hq hsq blocks O)
        (fun O hQ => by
          obtain ⟨O, h, hh, rfl⟩ := O
          exact good_spSupported_of_factor hp3 hK hKℓ hℓ3 hSL hA6 hSU hSU6 hSp hSp6 hSp42 hq hsq
            blocks ⟨h, hh⟩ hQ) K' hK'
    exact ⟨X, inst, hfin, ⟨hX, hA6'⟩, hfac, hf'⟩

theorem lieCompsCore_conj_sp {a6 : Prop} (hSL : SLFactorFacts) (hSU : SUFactorFacts)
    (hSp : SpFactorFacts) (hSp42 : SpFourTwoFacts) (hA6 : a6 → SLAltSixFacts)
    (hSU6 : a6 → SUAltSixFacts) (hSp6 : a6 → SpAltSixFacts) {p r ℓ f : ℕ} {K : Type} [Field K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 1 ≤ r) (hpℓ : p ≠ ℓ) (hℓ3 : a6 → ℓ ≠ 3) (x : StatedSp r K) (hx : x ^ p = 1) :
    PerfectInLayer (MulAut.conj (SymplecticFlag.proj r K x)) ∧
      ∀ K' : Subgroup (StatedProj (StatedSp r K)),
        IsComponentOf K' (fixSubgroup (MulAut.conj (SymplecticFlag.proj r K x))) →
        ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData ℓ X ∧
          (∃ f : X →* ↥K', Function.Surjective f ∧ f.ker ≤ Subgroup.center X) ∧
          (a6 → Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6)) →
            Nat.card K = 2) := by
  obtain ⟨hlayer, hcomps⟩ := lieCompsCore_conj_sp_card hSL hSU hSp hSp42 hA6 hSU6 hSp6 hp hp2
    hℓ hf hK hr hpℓ hℓ3 x hx
  refine ⟨hlayer, fun K' hK' => ?_⟩
  obtain ⟨X, inst, hfin, ⟨hX, hA6'⟩, -, hf'⟩ := hcomps K' hK'
  exact ⟨X, inst, hfin, hX, hf', hA6'⟩

theorem lieCompExport_conj_sp
    (hSL : SLFactorFacts) (hA6 : SLAltSixFacts) (hSU : SUFactorFacts)
    (hSU6 : SUAltSixFacts) (hSp : SpFactorFacts) (hSp6 : SpAltSixFacts)
    (hSp42 : SpFourTwoFacts) {r ℓ f : ℕ} {K : Type} [Field K] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hne : ¬(r = 2 ∧ ℓ ^ f = 2)) (hℓ3 : ℓ ≠ 3)
    (x : StatedSp r K) (hx : x ^ 3 = 1) :
    LieCompExport ℓ (MulAut.conj (SymplecticFlag.proj r K x)) := by
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  obtain ⟨hlayer, hcomps⟩ := lieCompsCore_conj_sp (a6 := True) hSL hSU hSp hSp42 (fun _ => hA6)
    (fun _ => hSU6) (fun _ => hSp6) Nat.prime_three (by decide) hℓ hf hK (by omega)
    (Ne.symm hℓ3) (fun _ => hℓ3) x hx
  refine ⟨hlayer, fun K' hK' => ?_, fun ⟨K', hK', ⟨a⟩⟩ => ?_⟩
  · obtain ⟨X, _, _, hX, hf', -⟩ := hcomps K' hK'
    exact ⟨X, inferInstance, inferInstance, hX, hf'⟩
  · obtain ⟨X, _, _, hX, ⟨f', hf', hfk⟩, hA6'⟩ := hcomps K' hK'
    obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hX.perfect f' hf' hfk
    exact noThreeCover_statedProj_sp_two (by omega) (hA6' trivial ⟨e.trans a⟩)

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
