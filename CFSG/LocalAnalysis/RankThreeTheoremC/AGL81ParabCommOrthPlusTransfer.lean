module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusLevi
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusTwo
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus

open Matrix QuadraticMap CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.Open
open scoped Pointwise commutatorElement MatrixGroups
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem plusFlagStab_le_E (D : Finset ℕ) :
    plusFlagStab K r D ≤ orthElementaryGroup (quadPlus r K) := fun _ hg =>
  (mem_plusFlagStab.1 hg).1

section Setup

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {D : Finset ℕ}
  (ρ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥Y)
  (hρ : ∀ x : ↥(orthElementaryGroup (quadPlus r K)),
    (x : GLV r K) ∈ plusFlagStab K r D ↔ ((ρ x : ↥Y) : A) ∈ P)

@[expose] noncomputable def toP : ↥(plusFlagStab K r D) →* ↥P :=
  (((Y.subtype.comp ρ.toMonoidHom).comp (Subgroup.inclusion (plusFlagStab_le_E D))).codRestrict P
    fun q => (hρ ⟨q.1, plusFlagStab_le_E D q.2⟩).1 q.2)

include hρ in
theorem toP_injective : Function.Injective (toP ρ hρ) := by
  intro q₁ q₂ h
  have h0 : ((toP ρ hρ q₁ : ↥P) : A) = ((toP ρ hρ q₂ : ↥P) : A) := Subtype.ext_iff.1 h
  have h1 : ρ ⟨q₁.1, plusFlagStab_le_E D q₁.2⟩ = ρ ⟨q₂.1, plusFlagStab_le_E D q₂.2⟩ :=
    Subtype.ext h0
  have h2 := ρ.injective h1
  have h3 : ((⟨q₁.1, plusFlagStab_le_E D q₁.2⟩ : ↥(orthElementaryGroup (quadPlus r K))) :
      GLV r K) = ((⟨q₂.1, plusFlagStab_le_E D q₂.2⟩ : ↥(orthElementaryGroup (quadPlus r K))) :
        GLV r K) := Subtype.ext_iff.1 h2
  exact Subtype.ext h3

include hρ in
theorem toP_surjective (hPY : P ≤ Y) : Function.Surjective (toP ρ hρ) := by
  rintro ⟨w, hw⟩
  set x := ρ.symm ⟨w, hPY hw⟩ with hx
  have hxw : ((ρ x : ↥Y) : A) = w := by rw [hx, MulEquiv.apply_symm_apply]
  have hxQ : (x : GLV r K) ∈ plusFlagStab K r D := (hρ x).2 (hxw ▸ hw)
  exact ⟨⟨x.1, hxQ⟩, Subtype.ext hxw⟩

@[expose] noncomputable def toHat : ↥(plusFlagStab K r D) →* ↥P ⧸ CFSG.pCore 2 ↥P :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).comp (toP ρ hρ)

include hρ in
theorem toHat_surjective (hPY : P ≤ Y) : Function.Surjective (toHat ρ hρ) :=
  (QuotientGroup.mk'_surjective _).comp (toP_surjective ρ hρ hPY)

variable {ρ} {hρ}

include hρ in
theorem toHat_eq_one_of_mem_leviKer (hPY : P ≤ Y) {hD : ∀ d ∈ D, d ≤ r} {t m : ℕ}
    {ht : t = 0 ∨ t ∈ D} {htm : t + m = r} (hD1 : ∀ d ∈ D, 1 ≤ d) (hDt : ∀ d ∈ D, d ≤ t)
    {g : ↥(plusFlagStab K r D)} (hg : g ∈ leviKer hD ht htm) : toHat ρ hρ g = 1 := by
  have hmap : (leviKer hD ht htm).map (toP ρ hρ) ≤ CFSG.pCore 2 ↥P := by
    haveI := leviKer_normal (K := K) (hD := hD) (ht := ht) (htm := htm)
    have hnorm : ((leviKer hD ht htm).map (toP ρ hρ)).Normal :=
      Subgroup.Normal.map inferInstance _ (toP_surjective ρ hρ hPY)
    have hp : IsPGroup 2 ((leviKer hD ht htm).map (toP ρ hρ)) :=
      (isPGroup_leviKer (hD := hD) (ht := ht) (htm := htm) hD1 hDt).map _
    exact le_sSup ⟨hnorm, hp⟩
  change QuotientGroup.mk' _ (toP ρ hρ g) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hmap (Subgroup.mem_map_of_mem _ hg)

end Setup

section W

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {D : Finset ℕ}
  {ρ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥Y}
  {hρ : ∀ x : ↥(orthElementaryGroup (quadPlus r K)),
    (x : GLV r K) ∈ plusFlagStab K r D ↔ ((ρ x : ↥Y) : A) ∈ P}
  (hPY : P ≤ Y) {hD : ∀ d ∈ D, d ≤ r} {t m : ℕ} {ht : t = 0 ∨ t ∈ D} {htm : t + m = r}
  (hD1 : ∀ d ∈ D, 1 ≤ d) (hDt : ∀ d ∈ D, d ≤ t)

include hPY hD1 hDt in
theorem toHat_mem_wSup_aux (N : Subgroup ↥(plusFlagStab K r D)) [N.Normal] {S : Type} [Group S]
    (ℓ : ↥N →* S) (hℓ : Function.Surjective ℓ)
    (hker : ∀ x : ↥N, ℓ x = 1 → (x : ↥(plusFlagStab K r D)) ∈ leviKer hD ht htm)
    (hS : CFSG.Open.IsQuasisimple S ∨ Nonempty (S ≃* Equiv.Perm (Fin 3))) :
    ∀ x ∈ N, toHat ρ hρ x ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  have hH := CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' (X := ↥P) 2
  have hrange : ((toHat ρ hρ).comp N.subtype).range = N.map (toHat ρ hρ) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hnormal : ((toHat ρ hρ).comp N.subtype).range.Normal := by
    rw [hrange]
    exact Subgroup.Normal.map inferInstance _ (toHat_surjective ρ hρ hPY)
  have hle := Lin.range_le_wSup hH ℓ hℓ ((toHat ρ hρ).comp N.subtype) (fun x hx =>
    toHat_eq_one_of_mem_leviKer hPY hD1 hDt (hker x hx)) hnormal hS
  intro x hx
  exact hle ⟨⟨x, hx⟩, rfl⟩

include hPY hD1 hDt in
theorem toHat_mem_wSup_block (hr : 3 ≤ r) {b : ℕ} (hb : b ∈ D) (hk : 2 ≤ b - predCut D b)
    (hbt : b ≤ t) {q : ↥(plusFlagStab K r D)}
    (hq1 : plusEBlockHom hD hb q ∈
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (b - predCut D b)) K →*
        GL (Fin (b - predCut D b)) K).range)
    (hq2 : ∀ (b' : ℕ) (hb' : b' ∈ D), b' ≠ b → plusEBlockHom hD hb' q = 1)
    (hq3 : plusResBlockHom hD ht htm q = 1) :
    toHat ρ hρ q ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  let G₀ : Subgroup (GL (Fin (b - predCut D b)) K) :=
    (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (b - predCut D b)) K →*
      GL (Fin (b - predCut D b)) K).range
  haveI hG₀ : G₀.Normal := by
    change (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (b - predCut D b)) K →*
      GL (Fin (b - predCut D b)) K).range.Normal
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact MonoidHom.normal_ker _
  let N : Subgroup ↥(plusFlagStab K r D) :=
    (⨅ b' : {b' // b' ∈ D ∧ b' ≠ b}, (plusEBlockHom (K := K) hD b'.2.1).ker) ⊓
      (plusResBlockHom (K := K) hD ht htm).ker ⊓ G₀.comap (plusEBlockHom hD hb)
  have hmemN : ∀ x, x ∈ N ↔ (∀ (b' : ℕ) (hb' : b' ∈ D), b' ≠ b → plusEBlockHom hD hb' x = 1) ∧
      plusResBlockHom hD ht htm x = 1 ∧ plusEBlockHom hD hb x ∈ G₀ := by
    intro x
    simp only [N, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap,
      Subtype.forall, and_imp]
    tauto
  haveI hNn : N.Normal := by
    haveI h1 : (⨅ b' : {b' // b' ∈ D ∧ b' ≠ b}, (plusEBlockHom (K := K) hD b'.2.1).ker).Normal :=
      Subgroup.normal_iInf_normal fun b' => MonoidHom.normal_ker _
    haveI h2 := MonoidHom.normal_ker (plusResBlockHom (K := K) hD ht htm)
    haveI h3 : (G₀.comap (plusEBlockHom hD hb)).Normal := hG₀.comap _
    exact Subgroup.normal_inf_normal _ _
  let ℓ : ↥N →* ↥G₀ := ((plusEBlockHom hD hb).comp N.subtype).codRestrict G₀
    fun x => ((hmemN x.1).1 x.2).2.2
  refine toHat_mem_wSup_aux (hD := hD) (ht := ht) (htm := htm) hPY hD1 hDt N ℓ ?_ ?_
    (Lin.isQuasisimple_or_perm_three hk (slEquivToGLRange (K := K) (b - predCut D b))) q
    ((hmemN q).2 ⟨hq2, hq3, hq1⟩)
  · rintro ⟨s, hs⟩
    obtain ⟨q', h1, h2, h3⟩ := exists_plusFlagLevi_of_mem hr hD hb hs
    exact ⟨⟨q', (hmemN q').2 ⟨h2, h3 ht htm hbt, h1 ▸ hs⟩⟩, Subtype.ext h1⟩
  · intro x hx
    have hx1 : plusEBlockHom hD hb x.1 = 1 := congrArg Subtype.val hx
    obtain ⟨h2, h3, -⟩ := (hmemN x.1).1 x.2
    refine mem_leviKer.2 ⟨fun b' hb' => ?_, h3⟩
    by_cases hbb : b' = b
    · subst hbb
      exact hx1
    · exact h2 b' hb' hbb

include hPY hD1 hDt in
theorem toHat_mem_wSup_res_three (hm : 3 ≤ m) {q : ↥(plusFlagStab K r D)}
    (hq1 : ∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD hb q = 1)
    (hq2 : plusResAut hD ht htm q ∈ orthElementaryGroup (quadPlus m K)) :
    toHat ρ hρ q ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  set Em := orthElementaryGroup (quadPlus m K) with hEm
  let N : Subgroup ↥(plusFlagStab K r D) :=
    (⨅ b : ↥D, (plusEBlockHom (K := K) hD b.2).ker) ⊓ Em.comap (plusResAut hD ht htm)
  have hmemN : ∀ x, x ∈ N ↔ (∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD hb x = 1) ∧
      plusResAut hD ht htm x ∈ Em := by
    intro x
    simp only [N, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap,
      Subtype.forall]
  haveI hNn : N.Normal := by
    haveI h1 : (⨅ b : ↥D, (plusEBlockHom (K := K) hD b.2).ker).Normal :=
      Subgroup.normal_iInf_normal fun b => MonoidHom.normal_ker _
    haveI h3 : (Em.comap (plusResAut hD ht htm)).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_comap] at hn ⊢
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_orthElementaryGroup (plusResAut_mem_orthogonalGroup hD ht htm g) hn⟩
    exact Subgroup.normal_inf_normal _ _
  let ℓ : ↥N →* ↥Em := ((plusResAut hD ht htm).comp N.subtype).codRestrict Em
    fun x => ((hmemN x.1).1 x.2).2
  refine toHat_mem_wSup_aux (hD := hD) (ht := ht) (htm := htm) hPY hD1 hDt N ℓ ?_ ?_
    (Or.inl (isQuasisimple_plusElementary hm).1) q ((hmemN q).2 ⟨hq1, hq2⟩)
  · rintro ⟨e, he⟩
    have hqe : plusResExt K htm e ∈ plusFlagStab K r D :=
      plusResExt_mem_plusFlagStab htm hm hDt he
    refine ⟨⟨⟨plusResExt K htm e, hqe⟩, (hmemN _).2 ⟨fun b hb =>
      plusEBlockHom_plusResExt hD htm hDt hb hqe, by
        rw [plusResAut_plusResExt hD ht htm hqe]
        exact he⟩⟩, Subtype.ext (plusResAut_plusResExt hD ht htm hqe)⟩
  · intro x hx
    have hx1 : plusResAut hD ht htm x.1 = 1 := congrArg Subtype.val hx
    exact mem_leviKer.2 ⟨((hmemN x.1).1 x.2).1, plusResBlockHom_eq_one_of_plusResAut hD ht htm hx1⟩

include hPY hD1 hDt in
theorem toHat_mem_wSup_fam {f f' : ↥(plusFlagStab K r D) →* GL (Fin 2) K}
    (hf : ∀ g, f g ∈ (SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K).range)
    (hreal : ∀ A : SL(2, K), ∃ q : ↥(plusFlagStab K r D),
      f q = SpecialLinearGroup.toGL A ∧ f' q = 1 ∧
        ∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD hb q = 1)
    (hres : ∀ g : ↥(plusFlagStab K r D), (∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD hb g = 1) →
      f g = 1 → f' g = 1 → plusResBlockHom hD ht htm g = 1)
    {q : ↥(plusFlagStab K r D)} (hq1 : ∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD hb q = 1)
    (hq2 : f' q = 1) : toHat ρ hρ q ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  let N : Subgroup ↥(plusFlagStab K r D) :=
    (⨅ b : ↥D, (plusEBlockHom (K := K) hD b.2).ker) ⊓ f'.ker
  have hmemN : ∀ x, x ∈ N ↔ (∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD hb x = 1) ∧ f' x = 1 := by
    intro x
    simp only [N, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subtype.forall]
  haveI hNn : N.Normal := by
    haveI h1 : (⨅ b : ↥D, (plusEBlockHom (K := K) hD b.2).ker).Normal :=
      Subgroup.normal_iInf_normal fun b => MonoidHom.normal_ker _
    haveI := MonoidHom.normal_ker f'
    exact Subgroup.normal_inf_normal _ _
  let ℓ : ↥N →* ↥(SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K).range :=
    (f.comp N.subtype).codRestrict _ fun x => hf x.1
  refine toHat_mem_wSup_aux (hD := hD) (ht := ht) (htm := htm) hPY hD1 hDt N ℓ ?_ ?_
    (Lin.isQuasisimple_or_perm_three (le_refl 2) (slEquivToGLRange (K := K) 2)) q
    ((hmemN q).2 ⟨hq1, hq2⟩)
  · rintro ⟨s, A, rfl⟩
    obtain ⟨q', h1, h2, h3⟩ := hreal A
    exact ⟨⟨q', (hmemN q').2 ⟨h3, h2⟩⟩, Subtype.ext h1⟩
  · intro x hx
    have hx1 : f x.1 = 1 := congrArg Subtype.val hx
    obtain ⟨h3, h2⟩ := (hmemN x.1).1 x.2
    exact mem_leviKer.2 ⟨h3, hres x.1 h3 hx1 h2⟩

omit hPY hD1 hDt in
theorem toHat_mem_wSup_res_two (hPY : P ≤ Y) (hD1 : ∀ d ∈ D, 1 ≤ d) (hDt : ∀ d ∈ D, d ≤ t)
    (hr : 3 ≤ r) (ht2 : t + 2 = r) (j j' : Fin 2) (hjj : j ≠ j')
    {q : ↥(plusFlagStab K r D)} (hq1 : ∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD hb q = 1)
    (hq2 : plusFamHom K hr (fun d hd => ⟨hD1 d hd, Nat.le_sub_of_add_le
      (le_of_le_of_eq (Nat.add_le_add_right (hDt d hd) 2) ht2)⟩) hD ht ht2 j' q = 1) :
    toHat ρ hρ q ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  have hD₂ : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2 := fun d hd => ⟨hD1 d hd, by have := hDt d hd; omega⟩
  have hres : ∀ g : ↥(plusFlagStab K r D), (∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD hb g = 1) →
      plusFamHom K hr hD₂ hD ht ht2 0 g = 1 → plusFamHom K hr hD₂ hD ht ht2 1 g = 1 →
        plusResBlockHom hD ht ht2 g = 1 := fun g _ h0 h1 =>
    plusResBlockHom_eq_one_of_plusResAut hD ht ht2
      (plusResAut_eq_one_of_plusFamHom hr hD₂ hD ht ht2 h0 h1)
  have hmem : ∀ (j : Fin 2) (g : ↥(plusFlagStab K r D)),
      plusFamHom K hr hD₂ hD ht ht2 j g ∈
        (SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K).range := by
    intro j g
    fin_cases j
    · exact ⟨_, (plusFamHom_zero hr hD₂ hD ht ht2 g).symm⟩
    · exact ⟨_, (plusFamHom_one hr hD₂ hD ht ht2 g).symm⟩
  fin_cases j <;> fin_cases j'
  · exact absurd rfl hjj
  · refine toHat_mem_wSup_fam hPY hD1 hDt (hmem 0) (fun A => ?_) (fun g h3 h0 h1 => hres g h3 h0 h1)
      hq1 hq2
    have hq := plusResExt_iotaTwo_mem hr ht2 (D := D) hDt A
    exact ⟨⟨_, hq⟩, (plusFamHom_iotaTwo hr hD₂ hD ht ht2 hq).1,
      (plusFamHom_iotaTwo hr hD₂ hD ht ht2 hq).2, fun b hb =>
        plusEBlockHom_plusResExt hD ht2 hDt hb hq⟩
  · refine toHat_mem_wSup_fam hPY hD1 hDt (hmem 1) (fun A => ?_)
      (fun g h3 h1 h0 => hres g h3 h0 h1) hq1 hq2
    have hq := plusResExt_iotaOne_mem hr ht2 (D := D) hDt A
    exact ⟨⟨_, hq⟩, (plusFamHom_iotaOne hr hD₂ hD ht ht2 hq).2,
      (plusFamHom_iotaOne hr hD₂ hD ht ht2 hq).1, fun b hb =>
        plusEBlockHom_plusResExt hD ht2 hDt hb hq⟩
  · exact absurd rfl hjj

end W

section Aut

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A} {D : Finset ℕ}
  (ρ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥Y)

@[expose] noncomputable def autHom :
    ↥(Subgroup.normalizer (Y : Set A)) →* MulAut ↥(orthElementaryGroup (quadPlus r K)) :=
  (MulAut.congr ρ.symm).toMonoidHom.comp Y.normalizerMonoidHom

theorem coe_rho_autHom (b : ↥(Subgroup.normalizer (Y : Set A)))
    (x : ↥(orthElementaryGroup (quadPlus r K))) :
    ((ρ (autHom ρ b x) : ↥Y) : A) = (b : A) * ((ρ x : ↥Y) : A) * (b : A)⁻¹ := by
  have h : ρ (autHom ρ b x) = Y.normalizerMonoidHom b (ρ x) := by
    change ρ (ρ.symm (Y.normalizerMonoidHom b (ρ x))) = _
    exact ρ.apply_symm_apply _
  rw [h]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem autHom_pow_eq_one (b : ↥(Subgroup.normalizer (Y : Set A))) {p k : ℕ}
    (hb : (b : A) ^ p ^ k = 1) : autHom ρ b ^ p ^ k = 1 := by
  have h : b ^ p ^ k = 1 := Subtype.ext (by simpa using hb)
  rw [← map_pow, h, map_one]

theorem odd_orderOf_autHom (b : ↥(Subgroup.normalizer (Y : Set A))) {p k : ℕ}
    (hp : Odd p) (hb : (b : A) ^ p ^ k = 1) : Odd (orderOf (autHom ρ b)) :=
  (hp.pow (n := k)).of_dvd_nat (orderOf_dvd_of_pow_eq_one (autHom_pow_eq_one ρ b hb))

theorem centralizes_of_autHom_eq_one (c : ↥(Subgroup.normalizer (Y : Set A)))
    (h : autHom ρ c = 1) : ∀ y ∈ Y, (c : A) * y = y * c := by
  intro y hy
  obtain ⟨x, hx⟩ := ρ.surjective ⟨y, hy⟩
  have h1 := coe_rho_autHom ρ c x
  rw [h, MulAut.one_apply, hx] at h1
  have h2 : (c : A) * y * (c : A)⁻¹ * (c : A) = y * c := by
    rw [← h1]
  simpa using h2

variable {ρ}
  {hρ : ∀ x : ↥(orthElementaryGroup (quadPlus r K)),
    (x : GLV r K) ∈ plusFlagStab K r D ↔ ((ρ x : ↥Y) : A) ∈ P}
  (hPY : P ≤ Y) {hD : ∀ d ∈ D, d ≤ r} {t m : ℕ} {ht : t = 0 ∨ t ∈ D} {htm : t + m = r}
  (hr : 3 ≤ r) (hD1 : ∀ d ∈ D, 1 ≤ d) (hDt : ∀ d ∈ D, d ≤ t) (hm : m = 0 ∨ 2 ≤ m)

include hρ hPY hr hD1 hDt hm in
theorem leviTriv_autQ {b : A} (hbY : b ∈ Subgroup.normalizer (Y : Set A)) (hW : WCent P b)
    {q : ↥(plusFlagStab K r D)} (hq : toHat ρ hρ q ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P)) :
    LeviTriv hD ht htm (autQ (autHom ρ ⟨b, hbY⟩) q * (q : GLV r K)⁻¹) := by
  set α := autHom ρ ⟨b, hbY⟩ with hα
  let q' : ↥(orthElementaryGroup (quadPlus r K)) := ⟨q.1, plusFlagStab_le_E D q.2⟩
  have hρu : ((ρ (α q' * q'⁻¹) : ↥Y) : A) = b * ((toP ρ hρ q : ↥P) : A) * b⁻¹ *
      ((toP ρ hρ q : ↥P) : A)⁻¹ := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hα, coe_rho_autHom]
    rfl
  have hc : b * ((toP ρ hρ q : ↥P) : A) * b⁻¹ * ((toP ρ hρ q : ↥P) : A)⁻¹ ∈ pCoreOf 2 P :=
    hW _ (toP ρ hρ q).2 hq
  have hcP : b * ((toP ρ hρ q : ↥P) : A) * b⁻¹ * ((toP ρ hρ q : ↥P) : A)⁻¹ ∈ P :=
    Subgroup.map_subtype_le _ hc
  have hu : ((α q' * q'⁻¹ : ↥(orthElementaryGroup (quadPlus r K))) : GLV r K) ∈
      plusFlagStab K r D := (hρ _).2 (by rw [hρu]; exact hcP)
  let R : Subgroup ↥(plusFlagStab K r D) := (CFSG.pCore 2 ↥P).comap (toP ρ hρ)
  haveI hRn : R.Normal := Subgroup.Normal.comap CFSG.pCore_normal _
  have hR2 : IsPGroup 2 R :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥P)).comap_of_injective (toP ρ hρ) (toP_injective ρ hρ)
  have hmem : (⟨_, hu⟩ : ↥(plusFlagStab K r D)) ∈ R := by
    obtain ⟨y, hy, hyeq⟩ := hc
    have : toP ρ hρ ⟨_, hu⟩ = y := Subtype.ext (hρu.trans hyeq.symm)
    change toP ρ hρ ⟨_, hu⟩ ∈ CFSG.pCore 2 ↥P
    rw [this]
    exact hy
  have hker := le_leviKer_of_normal_isPGroup hD (ht := ht) (htm := htm) R hR2 hr hD1 hDt hm hmem
  exact ⟨hu, mem_leviKer.1 hker⟩

include hρ hPY hD1 hDt in
theorem toHat_mem_wSup_plusResExt_two (hD : ∀ d ∈ D, d ≤ r) (ht : t = 0 ∨ t ∈ D)
    (hr : 3 ≤ r) (ht2 : t + 2 = r)
    {x : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)}
    (hx : (∃ A : SL(2, K), x = plusIotaTwo K A) ∨ ∃ A : SL(2, K), x = plusIotaOne K A)
    (hqe : plusResExt K ht2 x ∈ plusFlagStab K r D) :
    toHat ρ hρ ⟨plusResExt K ht2 x, hqe⟩ ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  have hD₂ : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2 := fun d hd => ⟨hD1 d hd, by have := hDt d hd; omega⟩
  have hq1 : ∀ (b : ℕ) (hb : b ∈ D), plusEBlockHom hD hb ⟨plusResExt K ht2 x, hqe⟩ = 1 :=
    fun b hb => plusEBlockHom_plusResExt hD ht2 hDt hb hqe
  rcases hx with ⟨A, rfl⟩ | ⟨A, rfl⟩
  · exact toHat_mem_wSup_res_two hPY hD1 hDt hr ht2 0 1 (by decide) hq1
      (plusFamHom_iotaTwo hr hD₂ hD ht ht2 hqe).2
  · exact toHat_mem_wSup_res_two hPY hD1 hDt hr ht2 1 0 (by decide) hq1
      (plusFamHom_iotaOne hr hD₂ hD ht ht2 hqe).1

include hρ hPY hr hD1 hDt hm in
theorem normFix_autHom {b : A} (hbY : b ∈ Subgroup.normalizer (Y : Set A))
    (hbP : b ∈ Subgroup.normalizer (P : Set A)) (hW : WCent P b) :
    NormFix hD ht htm (autHom ρ ⟨b, hbY⟩) := by
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [hρ x, hρ (autHom ρ ⟨b, hbY⟩ x), coe_rho_autHom]
    exact Subgroup.mem_normalizer_iff.1 hbP _
  · intro q b' hb' A hk hq
    refine leviTriv_autQ (hρ := hρ) hPY hr hD1 hDt hm hbY hW ?_
    have hq' : q = ⟨plusFlagLevi K (hD b' hb') (SpecialLinearGroup.toGL A),
        plusFlagLevi_mem_plusFlagStab hr hD hb' _⟩ := Subtype.ext hq
    rw [hq']
    exact toHat_mem_wSup_block hPY hD1 hDt hr hb' hk (hDt b' hb')
      ⟨A, (plusEBlockHom_plusFlagLevi_self hr hD hb' _).symm⟩
      (fun b'' hb'' hne => plusEBlockHom_plusFlagLevi_of_ne hr hD hb' hb'' hne _)
      (plusResBlockHom_plusFlagLevi hr hD ht htm hb' (hDt b' hb') _)
  · intro hm2 q a c s hac hq
    obtain ⟨q, hqmem⟩ := q
    change q = plusResExt K htm (rpElt a c s) at hq
    have hw : toHat ρ hρ ⟨q, hqmem⟩ ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
      subst hq
      rcases hm2.eq_or_lt with rfl | hm3
      · exact toHat_mem_wSup_plusResExt_two hPY hD1 hDt hD ht hr htm (rpElt_two_cases hac s) hqmem
      · refine toHat_mem_wSup_res_three (hD := hD) (ht := ht) (htm := htm) hPY hD1 hDt hm3
          (fun b' hb' => plusEBlockHom_plusResExt hD htm hDt hb' hqmem) ?_
        change plusResAut hD ht htm ⟨plusResExt K htm (rpElt a c s), hqmem⟩ ∈ _
        rw [plusResAut_plusResExt hD ht htm hqmem]
        exact eichler_mem_elementaryGroup _ _ _
    exact leviTriv_autQ (hρ := hρ) hPY hr hD1 hDt hm hbY hW hw

include hρ hPY hD1 hDt in
theorem exists_block_of_nonabelian (hD : ∀ d ∈ D, d ≤ r) (ht : t = 0 ∨ t ∈ D)
    (htm : t + m = r) (hm : m = 0 ∨ 2 ≤ m)
    (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) :
    (∃ b ∈ D, 2 ≤ b - predCut D b) ∨ 2 ≤ m := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hlt, hm2⟩ := hcon
  obtain rfl : m = 0 := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := hna
  obtain ⟨x', hx'⟩ := toP_surjective ρ hρ hPY ⟨x, hx⟩
  obtain ⟨y', hy'⟩ := toP_surjective ρ hρ hPY ⟨y, hy⟩
  apply hxy
  have hc : ⁅x', y'⁆ ∈ leviKer hD ht htm := by
    refine mem_leviKer.2 ⟨fun b hb => ?_, ?_⟩
    · rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (gl_mul_comm_of_lt_two (hlt b hb) _ _)
    · haveI := gl_subsingleton_zero (K := K)
      exact Subsingleton.elim _ _
  have h1 : toHat ρ hρ ⁅x', y'⁆ = 1 := toHat_eq_one_of_mem_leviKer hPY hD1 hDt hc
  change QuotientGroup.mk' _ (toP ρ hρ ⁅x', y'⁆) = 1 at h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, map_commutatorElement, hx', hy'] at h1
  exact ⟨_, h1, rfl⟩

end Aut

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus
