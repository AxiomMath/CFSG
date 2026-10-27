module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Kind
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.GH74.GLS.Stage2.Local
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage12
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.Classical.SteinbergBY CFSG.RankThree.PartTwo.KFacts
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open Matrix

namespace BS4

variable {F : Type} [Field F]

theorem formJ_map_ringHom {E : Type} [Field E] (f : E →+* F) :
    (formJ 2 E).map f = formJ 2 F := by
  rw [formJ, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f), Matrix.map_one _ (map_zero f)
    (map_one f), Matrix.map_neg _ (map_neg f), Matrix.map_one _ (map_zero f) (map_one f)]

theorem exists_subfield_embedding (σ : F ≃+* F) :
    ∃ ρ : StatedProj (StatedSp 2 ↥(semilinearFixedSubfield σ)) →* StatedProj (StatedSp 2 F),
      Function.Injective ρ ∧ ∀ x, fieldAut 2 F σ (ρ x) = ρ x := by
  set F0 := semilinearFixedSubfield σ with hF0
  let φ : GL (Fin 2 ⊕ Fin 2) ↥F0 →* GL (Fin 2 ⊕ Fin 2) F :=
    Units.map (RingHom.mapMatrix F0.subtype).toMonoidHom
  have hφ : ∀ g : GL (Fin 2 ⊕ Fin 2) ↥F0, ((φ g : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ↥F0).map F0.subtype := fun g => rfl
  have hmem : ∀ g ∈ StatedSp 2 ↥F0, φ g ∈ StatedSp 2 F := by
    intro g hg
    rw [SymplecticTorusWeyl.mem_statedSp_iff] at hg ⊢
    have h1 := congrArg (fun X => X.map F0.subtype) hg
    simp only [Matrix.map_mul, Matrix.transpose_map] at h1
    rw [hφ]
    have h2 := formJ_map_ringHom F0.subtype
    rw [formJ] at h2
    rwa [h2] at h1
  let ρ0 : StatedSp 2 ↥F0 →* StatedSp 2 F :=
    (φ.comp (StatedSp 2 ↥F0).subtype).codRestrict (StatedSp 2 F) fun g => hmem g g.2
  have hρ0 : ∀ g : StatedSp 2 ↥F0, (((ρ0 g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        ((g : GL (Fin 2 ⊕ Fin 2) ↥F0) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ↥F0).map
          F0.subtype := fun g => rfl
  have hker : spScalars 2 ↥F0 ≤ ((proj 2 F).comp ρ0).ker := by
    intro s hs
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hs :)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    refine ⟨Units.map F0.subtype.toMonoidHom c, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, hρ0, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  let ρ : StatedProj (StatedSp 2 ↥F0) →* StatedProj (StatedSp 2 F) :=
    QuotientGroup.lift (spScalars 2 ↥F0) ((proj 2 F).comp ρ0) hker
  have hρ : ∀ g, ρ (QuotientGroup.mk g) = proj 2 F (ρ0 g) := fun g => rfl
  refine ⟨ρ, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hρ, proj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      at hx
    obtain ⟨c, hc⟩ := hx
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hentry : ∀ i j, F0.subtype (((g : GL (Fin 2 ⊕ Fin 2) ↥F0) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ↥F0) i j) =
          Matrix.scalar (Fin 2 ⊕ Fin 2) (c : F) i j := by
      intro i j
      have := congrArg (fun A : GL (Fin 2 ⊕ Fin 2) F =>
        (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j) hc
      simp only [Matrix.GeneralLinearGroup.coe_scalar] at this
      rw [this, hρ0]
      rfl
    have h00 := hentry (Sum.inl 0) (Sum.inl 0)
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00
    have hne : ((g : GL (Fin 2 ⊕ Fin 2) ↥F0) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ↥F0)
        (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h00
      exact c.ne_zero h00.symm
    refine ⟨Units.mk0 _ hne, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    show F0.subtype _ = F0.subtype _
    rw [hentry i j]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Units.val_mk0]
      exact h00
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
  · intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hρ, fieldAut_proj]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [coe_fieldSp, hρ0]
    ext i j
    exact (((g : GL (Fin 2 ⊕ Fin 2) ↥F0) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ↥F0)
      i j).2

theorem psp4_bad {k : Kind} (hk : IsClassicalKind k) {F0 : Type} [Field F0] [Finite F0] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hcard : Nat.card F0 = p ^ e) :
    IsSimpleGroup (StatedProj (StatedSp 2 F0)) ∧ ¬ Group.IsSolvable (StatedProj (StatedSp 2 F0)) ∧
      ¬ KindFactorAll k (StatedProj (StatedSp 2 F0)) := by
  have h3 : 3 ≤ Nat.card F0 := by
    rw [hcard]
    have h2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    obtain ⟨m, hm⟩ := (hp.odd_of_ne_two hp2).pow (n := e)
    omega
  have hsimple : IsSimpleGroup (StatedProj (StatedSp 2 F0)) := by
    refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F0 2 (by norm_num) ?_
    rcases Nat.lt_or_ge (Nat.card F0) 4 with h | h
    · exact Or.inr (Or.inl ⟨by omega, le_rfl⟩)
    · exact Or.inl (Or.inr h)
  have hlie : LieModel (StatedProj (StatedSp 2 F0)) .PSp 2 p e :=
    CFSG.GH74.lieModel_of_statedClassicalModel (by decide)
      ⟨⟨hp, he, le_rfl, fun h => by
        have h' : p ^ e = 2 := congrArg Prod.snd h
        omega⟩, F0, inferInstance, inferInstance, hcard, ⟨MulEquiv.refl _⟩⟩
  have hFSp4 : FSp4 (StatedProj (StatedSp 2 F0)) := ⟨p, e, hp, he, hp2, hlie⟩
  refine ⟨hsimple, fun hsol => ?_, fun hkfa => ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_quaternion_psp4 (ringChar_ne_two_of_card_psp4 hp hp2 hcard)
    have hcomm := (IsSimpleGroup.comm_iff_isSolvable).mpr hsol
    apply (show ¬ ∀ a b : QuaternionGroup 2, a * b = b * a by decide)
    intro a b
    exact hψ (by rw [map_mul, map_mul, hcomm])
  · have hnotL2 := not_isL2_of_FSp4 hFSp4
    have hdvd4 := pow_four_dvd_card_of_psp4 hp hp2 hlie
    rcases hk with rfl | ⟨ε, rfl⟩
    · exact hnotL2 hkfa
    · rcases hkfa with h | h
      · exact hnotL2 h
      · have h7 : (p ^ e) ^ 4 ∣ Nat.factorial 7 :=
          hdvd4.trans ((h.card_dvd).trans (card_alt_dvd_factorial 7 (by norm_num)))
        have h11 : (p ^ e) ^ 4 ∣ Nat.factorial 11 :=
          h7.trans (Nat.factorial_dvd_factorial (by norm_num))
        obtain ⟨rfl, rfl⟩ := prime_pow_four_dvd_factorial hp hp2 he h11
        norm_num [Nat.factorial] at h7

variable [Finite F]

theorem not_admAut_field {k : Kind} (hk : IsClassicalKind k) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    {u : MulAut (StatedProj (StatedSp 2 F))} (hu2 : u * u = 1) (hu1 : u ≠ 1) (A : gsp 2 F)
    (σ : F ≃+* F) (hσ : σ ≠ 1) (hueq : u = conjAut 2 F A * fieldAut 2 F σ) :
    ¬ AdmAut k u := by
  intro hadm
  obtain ⟨-, hinj, hDF, -, -, -, -, -, -, hdesc⟩ :=
    symplectic_prime_semilinear_field_descent (ℓ := p) (f := f) (r := 2) hp hf (le_refl 2) hcard
  have hE : u ∈ spSemilinearAutGroup 2 F := by
    rw [hueq]
    exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ)
  have hD : u ∉ spLinearAutGroup 2 F := by
    intro hD
    have h1 : fieldAut 2 F σ ∈ spLinearAutGroup 2 F ⊓ (fieldAut 2 F).range := by
      refine Subgroup.mem_inf.mpr ⟨?_, σ, rfl⟩
      have : fieldAut 2 F σ = (conjAut 2 F A)⁻¹ * u := by rw [hueq]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (conjAut_mem_spLinearAutGroup A)) hD
    rw [hDF, Subgroup.mem_bot] at h1
    exact hσ (hinj (h1.trans (map_one _).symm))
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  obtain ⟨h2f, σ', -, hfix, h, -, hαh⟩ := hdesc 2 Nat.prime_two u hE hD hord
  obtain ⟨ρ, hρ, hρfix⟩ := exists_subfield_embedding σ'
  have hf2 : 1 ≤ f / 2 := by
    obtain ⟨m, rfl⟩ := h2f
    omega
  obtain ⟨hsimple, hns, hbad⟩ := psp4_bad hk hp hp2 hf2 hfix
  apply hbad
  have hψ : ∀ x, h (ρ x) ∈ fixSub u := by
    intro x
    show u (h (ρ x)) = h (ρ x)
    rw [hαh]
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hρfix]
  let ψ : StatedProj (StatedSp 2 ↥(semilinearFixedSubfield σ')) →* ↥(fixSub u) :=
    (h.toMonoidHom.comp ρ).codRestrict (fixSub u) hψ
  have hψinj : Function.Injective ψ := fun x y hxy =>
    hρ (h.injective (congrArg Subtype.val hxy))
  exact hadm _ hns ⟨ψ.range, (MonoidHom.ofInjective hψinj).symm.toMonoidHom,
    (MonoidHom.ofInjective hψinj).symm.surjective⟩

theorem linear_of_admAut {k : Kind} (hk : IsClassicalKind k) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    {u : MulAut (StatedProj (StatedSp 2 F))} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hadm : AdmAut k u) : ∃ A : gsp 2 F, u = conjAut 2 F A := by
  have hodd : ringChar F ≠ 2 := ringChar_ne_two_of_card_psp4 hp hp2 hcard
  obtain ⟨A, σ, hueq⟩ := psp4_odd_automorphism_normal_form hodd u
  by_cases hσ : σ = 1
  · refine ⟨A, ?_⟩
    rw [hueq, hσ, map_one, mul_one]
  · exact absurd hadm (not_admAut_field hk hp hp2 hf hcard hu2 hu1 A σ hσ hueq)

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
