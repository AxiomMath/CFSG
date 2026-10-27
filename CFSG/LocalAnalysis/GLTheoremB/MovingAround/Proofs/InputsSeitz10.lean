module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzBal2
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21D4
public import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4InnerEx
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz10

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (Seitz2313Even seitz2313Even_holds
  seitzHyperGamma_eq_top_of_seitz2313Even)
open GL83.CompFam

set_option linter.unusedSectionVars false

section HyperCube

variable {X : Type} [Group X] [Finite X]

theorem le_glbCore_of_seitzHyperGamma_cube {B K : Subgroup X} (hB : IsElemAbelian 3 B)
    {E : Subgroup X} (hEB : E ≤ B) (hEC : E ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    {F : Subgroup (MulAut ↥K)} (hFA : F ≤ InputsSeitz3.autIm E K) (hF27 : Nat.card F = 3 ^ 3)
    (hgen : CFSG.LieType.Seitz.seitzHyperGamma 3 F = ⊤) :
    K ≤ GLBCore 3 2 B := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEel : IsElemAbelian 3 E := elem_mono hB hEB
  set E₂ : Subgroup X := InputsSeitz3.autPre E K F with hE₂
  have hE₂E : E₂ ≤ E := InputsSeitz3.autPre_le E K F
  have hE₂N : E₂ ≤ Subgroup.normalizer (K : Set X) := by
    rintro _ ⟨n, -, rfl⟩
    exact n.2
  have hE₂C : E₂ ⊓ Subgroup.centralizer (K : Set X) = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_right _ hE₂E).trans hEC.le)
  have hE₂card : Nat.card E₂ = 3 ^ 3 := (InputsSeitz3.card_autPre hEC hFA).trans hF27
  have hAF : InputsSeitz3.autIm E₂ K = F := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      have hn' : (n : X) ∈ InputsSeitz3.autPre E K F := Subgroup.mem_subgroupOf.1 hn
      unfold InputsSeitz3.autPre at hn'
      obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.1 hn'
      have hmn' : m = n := Subtype.ext hmn
      rw [← hmn']
      exact (Subgroup.mem_inf.1 hm).2
    · rw [InputsSeitz3.card_autIm hE₂N hE₂C, hE₂card, hF27]
  exact InputsSeitz3.le_glbCore_of_centGenI Nat.prime_three (hE₂E.trans hEB) (elem_mono hEel hE₂E)
    (by rw [hE₂card]) (InputsSeitz3.le_centGenI_of_autIm hE₂N hE₂C (by rw [hAF]; exact hgen))

end HyperCube

section TwoGroup


variable {X : Type} [Group X] [Finite X]

theorem le_glbCore_of_e27_twoGroup {B K : Subgroup X} (hB : IsElemAbelian 3 B)
    {d : TauCeti.ValidLieTypeIndex}
    (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1)
    (eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    {E : Subgroup X} (hEB : E ≤ B) (hEC : E ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    {F : Subgroup (MulAut ↥K)} (hFA : F ≤ InputsSeitz3.autIm E K) (hF27 : Nat.card F = 3 ^ 3)
    {U : Subgroup ↥K} (hU0 : U ≠ ⊥) (hU2 : IsPGroup 2 ↥U) (hUF : ∀ φ ∈ F, ∀ u ∈ U, φ u ∈ U) :
    K ≤ GLBCore 3 2 B := by
  have hEel : IsElemAbelian 3 E := elem_mono hB hEB
  have hFel : IsElemAbelian 3 F :=
    GL83.CompFam.elem_mono (InputsSeitz3.isElemAbelian_autIm hEel K) hFA
  have hF0 : F ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hF27
    norm_num at hF27
  exact le_glbCore_of_seitzHyperGamma_cube hB hEB hEC hFA hF27
    (seitzHyperGamma_eq_top_of_seitz2313Even seitz2313Even_holds Nat.prime_three (by norm_num) d ⟨eK⟩ hs hFel hF0
      ⟨U, hU0, hU2, hUF⟩)

end TwoGroup

section OrthD4Two

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadPlus nondegenerate_polarBilin_quadPlus)
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (IsPlusSpace)

theorem exists_hyp_twoGroup_d4Two {S : Type} [Group S]
    (ψ : S ≃* ↥(elementaryGroup (quadPlus 4 (ZMod 2))))
    {D : Subgroup S} (hD : IsElemAbelian 3 D) {r : ℕ} (hDc : Nat.card D = 3 ^ r) (hr : 4 ≤ r)
    (hmax : ∀ F : Subgroup S, IsElemAbelian 3 F → Nat.card F ≤ Nat.card D) :
    ∃ H : Subgroup S, H ≤ D ∧ Nat.card H = 3 ^ 3 ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := quadPlus 4 (ZMod 2) with hQdef
  have hQ : (polarBilin Q).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 (ZMod 2)
  have hstd : IsPlusSpace Q 4 := ⟨LinearEquiv.refl _ _, fun v => rfl⟩
  set E := elementaryGroup Q with hEdef
  haveI : Finite ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) :=
    ClassicalEA.finite_linearEquiv
  let θ : S →* ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) :=
    E.subtype.comp ψ.toMonoidHom
  have hθ : Function.Injective θ := E.subtype_injective.comp ψ.injective
  have hθmem : ∀ s, θ s ∈ E := fun s => (ψ s).2
  have hθE : ∀ g ∈ E, ∃ s, θ s = g := fun g hg =>
    ⟨ψ.symm ⟨g, hg⟩, by simp [θ]⟩
  have hcomap : ∀ F : Subgroup ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)),
      F ≤ E → (F.comap θ).map θ = F := fun F hF =>
    Subgroup.map_comap_eq_self fun g hg => by
      obtain ⟨s, rfl⟩ := hθE g (hF hg)
      exact ⟨s, rfl⟩
  set D' := D.map θ with hD'
  have hD'O : D' ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨s, -, rfl⟩
    exact elementaryGroup_le_orthogonalGroup Q (hθmem s)
  have hD'el : IsElemAbelian 3 D' := CFSG.SectionRank.isElemAbelian_map hD θ
  have hD'c : Nat.card D' = 3 ^ r := by rw [hD', Subgroup.card_map_of_injective hθ, hDc]
  have hmax' : ∀ F : Subgroup ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)),
      F ≤ TauCeti.QuadraticMap.orthogonalGroup Q → IsElemAbelian 3 F → Nat.card F ≤ Nat.card D' := by
    intro F hFO hF
    have hFE : F ≤ E := fun g hg =>
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.mem_elementaryGroup_of_odd_pow_of_isPlusSpace
        (by norm_num) hstd (hFO hg) (by decide) (hF.2 g hg)
    have h1 := hmax (F.comap θ)
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.I102UniqAux.isElemAbelian_comap' θ hθ hF)
    rw [← Subgroup.card_map_of_injective hθ, hcomap F hFE] at h1
    rw [hD', Subgroup.card_map_of_injective hθ]
    exact h1
  have hfin : finrank (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨F, hFD, hF27, U, hUE, hU0, hU2, hUF⟩ : ∃ F : Subgroup
      ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)), F ≤ D' ∧ 27 ≤ Nat.card F ∧
      ∃ U : Subgroup ((Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)), U ≤ E ∧ U ≠ ⊥ ∧
        IsPGroup 2 ↥U ∧ ∀ g ∈ F, ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    rcases InputsSeitz8.exists_fixed_hypPair_or_swap_of_maxEA_orthF2 hQ hD'O hD'el hD'c hr hmax' with
      ⟨F, hFD, hF27, P, hP⟩ | ⟨-, F, hFD, hF27, u, huE, hu1, hu2, hFu⟩
    · have hc := card_rootGroup hQ P.Q_e P.e_ne_zero
      rw [hfin, Nat.card_zmod] at hc
      refine ⟨F, hFD, hF27, rootGroup Q P.e, rootGroup_le_elementaryGroup Q P.e, ?_,
        IsPGroup.of_card hc, ?_⟩
      · intro h
        rw [h, Subgroup.card_bot] at hc
        norm_num at hc
      · intro g hg x hx
        have h1 := conj_mem_rootGroup (hD'O (hFD hg)) hx
        rwa [(hP g hg).1] at h1
    · refine ⟨F, hFD, hF27, Subgroup.zpowers u, (Subgroup.zpowers_le).2 huE, ?_, ?_, ?_⟩
      · rwa [Ne, Subgroup.zpowers_eq_bot]
      · refine IsPGroup.of_card (n := 1) ?_
        rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1, pow_one]
      · rintro g hg _ ⟨k, rfl⟩
        have hgu : Commute g u := hFu g hg
        refine ⟨k, ?_⟩
        simp only
        rw [(hgu.zpow_right k).eq, mul_inv_cancel_right]
  have hFp : IsPGroup 3 ↥F := (hD'el.mono hFD).isPGroup
  obtain ⟨m, hm⟩ := hFp.exists_card_eq
  have hm3 : 3 ≤ m := by
    by_contra hlt
    have : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 3) (G := ↥F)
    (by rw [hm]; exact Nat.pow_dvd_pow 3 hm3)
  set F' := F₀.map F.subtype with hF'def
  have hF'F : F' ≤ F := Subgroup.map_subtype_le _
  have hF'c : Nat.card F' = 3 ^ 3 := by
    rw [hF'def, Subgroup.card_map_of_injective F.subtype_injective, hF₀]
  have hD'E : D' ≤ E := by
    rintro _ ⟨s, -, rfl⟩
    exact hθmem s
  refine ⟨F'.comap θ, ?_, ?_, U.comap θ, ?_, hU2.comap_of_injective θ hθ, ?_⟩
  · intro s hs
    obtain ⟨s', hs', hss'⟩ := hFD (hF'F hs)
    exact hθ hss' ▸ hs'
  · rw [← Subgroup.card_map_of_injective hθ, hcomap F' ((hF'F.trans hFD).trans hD'E), hF'c]
  · intro h
    apply hU0
    rw [← hcomap U hUE, h, Subgroup.map_bot]
  · intro h hh x hx
    show θ (h * x * h⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact hUF (θ h) (hF'F hh) (θ x) hx

end OrthD4Two

section GraphRank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LieType.SeitzGeneration.ExcWideThree (D4ElemType)


theorem exists_coordinateQuadPlus_ne_zero_d4Eight (F : Type) [Field F] :
    ∃ v, coordinateQuadPlus 4 F v ≠ 0 := by
  classical
  refine ⟨fun j => Sum.elim (fun i : Fin 4 => if i = 0 then (1 : F) else 0)
    (fun i : Fin 4 => if i = 0 then (1 : F) else 0) ((plusIndexEquiv 4).symm j), ?_⟩
  rw [coordinateQuadPlus_apply]
  simp [Fin.sum_univ_four]

theorem card_le_nine_of_graphType_d4Eight {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    {α : MulAut ↥(adjointGroup Tag.D4 F)} (h3 : α ^ 3 = 1) (hG : D4ElemType α fun ε _ => ε ≠ 0)
    (A : Subgroup ↥(adjointGroup Tag.D4 F)) (hA : IsElemAbelian 3 A) (hfix : ∀ x ∈ A, α x = x) :
    Nat.card A ≤ 9 := by
  classical
  obtain ⟨g, a, σ, ε, hε3, -, hε0, hα⟩ := hG
  have hε : ε = 1 ∨ ε = 2 := by omega
  have hns := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.not_semilin_of_graphNF hF hε hα h3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) hF
  set ψ := coordinatePlusWitnessEquiv F (CFSG.HardMathSupport.Dickson.Bal207.D4Graph.isoAdj F).symm with hψ
  set t := MulAut.congr ψ α with ht
  have ht3 : t ^ 3 = 1 := by rw [ht, ← map_pow, h3, map_one]
  have htE : t ∉ matrixProjectiveImage (coordinateQuadPlus 4 F) := fun h =>
    hns ⟨F, inferInstance, inferInstance, (CFSG.HardMathSupport.Dickson.Bal207.D4Graph.isoAdj F).symm,
      by rw [hF]; norm_num, h⟩
  have hA' : IsElemAbelian 3 (A.map ψ.toMonoidHom) := CFSG.SectionRank.isElemAbelian_map hA _
  have hfix' : ∀ y ∈ A.map ψ.toMonoidHom, t y = y := by
    rintro _ ⟨x, hx, rfl⟩
    show ψ (α (ψ.symm (ψ x))) = ψ x
    rw [MulEquiv.symm_apply_apply, hfix x hx]
  have h9 := CFSG.HardMathSupport.Timmesfeld.DFour.card_le_nine_of_charTwo
    (exists_coordinateQuadPlus_ne_zero_d4Eight F) t ht3 htE _ hA' hfix'
  rwa [Subgroup.card_map_of_injective ψ.injective] at h9

end GraphRank

section NF

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Dickson.I271
open CFSG.LieType.SeitzGeneration.ExcWideThree (HasNF D4ElemType)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz (hasNF_pow d4ElemType_of_hasNF
  exists_frobenius_eight)


theorem pow_eq_one_of_mod_three_d4Eight {G : Type*} [Monoid G] {T : G} (hT3 : T ^ 3 = 1) {n : ℕ}
    (hn : n % 3 = 0) : T ^ n = 1 := by
  obtain ⟨m, rfl⟩ : 3 ∣ n := Nat.dvd_of_mod_eq_zero hn
  rw [pow_mul, hT3, one_pow]

variable {F : Type} [Field F] [Finite F]

theorem exists_eq_frob_pow_d4Eight (hF : Nat.card F = 2 ^ 3) {T : F ≃+* F} (hT : ∀ c, T c = c ^ 2)
    (hT3 : T ^ 3 = 1) {σ : F ≃+* F} (hσ3 : σ ^ 3 = 1) : ∃ k : ℕ, σ = T ^ k := by
  by_cases h1 : σ = 1
  · exact ⟨0, by rw [h1, pow_zero]⟩
  obtain ⟨T', hT', -, -, hσT⟩ := exists_frobenius_eight hF hσ3 h1
  have hTT : T' = T := RingEquiv.ext fun c => by rw [hT', hT]
  subst hTT
  rcases hσT with h | h
  · exact ⟨1, by rw [h, pow_one]⟩
  · exact ⟨2, by rw [h]; exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)⟩

theorem exists_conj_of_hasNF_zero_d4Eight {α : MulAut ↥(adjointGroup Tag.D4 F)} {ε : ℕ}
    (h : HasNF α ε 1) (hε : ε % 3 = 0) (h3 : α ^ 3 = 1) : ∃ g, MulAut.conj g = α := by
  obtain ⟨g, c, hα⟩ := h.mod_three
  rw [hε] at hα
  have hin := CFSG.HardMathSupport.Lang.E6Descent.mem_inner_of_normal_form_one g c (hα ▸ h3)
  rw [← hα] at hin
  exact hin

variable {X : Type} [Group X]

theorem congr_actHom_pow_three_d4Eight {K : Subgroup X} {M : Type*} [Group M]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* M) {z : X} (hz : z ∈ Subgroup.normalizer (K : Set X))
    (hz3 : z ^ 3 = 1) : MulAut.congr e (actHom K ⟨z, hz⟩) ^ 3 = 1 := by
  have h1 : (⟨z, hz⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hz3)
  rw [← map_pow, ← map_pow, h1, map_one, map_one]

theorem congr_actHom_mul_pow_d4Eight {K : Subgroup X} {M : Type*} [Group M]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* M) {β a b : X} (hβ : β ∈ Subgroup.normalizer (K : Set X))
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (hb : b ∈ Subgroup.normalizer (K : Set X)) (i j : ℕ)
    (h : β * a ^ i * b ^ j ∈ Subgroup.normalizer (K : Set X)) :
    MulAut.congr e (actHom K ⟨β * a ^ i * b ^ j, h⟩) =
      MulAut.congr e (actHom K ⟨β, hβ⟩) * MulAut.congr e (actHom K ⟨a, ha⟩) ^ i *
        MulAut.congr e (actHom K ⟨b, hb⟩) ^ j := by
  have h1 : (⟨β * a ^ i * b ^ j, h⟩ : Subgroup.normalizer (K : Set X)) =
      ⟨β, hβ⟩ * ⟨a, ha⟩ ^ i * ⟨b, hb⟩ ^ j :=
    Subtype.ext (by simp)
  rw [h1, map_mul, map_mul, map_pow, map_pow, map_mul, map_mul, map_pow, map_pow]

theorem exists_conj_of_nfCombo_d4Eight {K : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F)) {T : F ≃+* F} (hT3 : T ^ 3 = 1)
    {β a b : X} (hβ : β ∈ Subgroup.normalizer (K : Set X))
    (ha : a ∈ Subgroup.normalizer (K : Set X)) (hb : b ∈ Subgroup.normalizer (K : Set X))
    {εβ εa εb kβ ka kb : ℕ}
    (hNβ : HasNF (MulAut.congr e (actHom K ⟨β, hβ⟩)) εβ (T ^ kβ))
    (hNa : HasNF (MulAut.congr e (actHom K ⟨a, ha⟩)) εa (T ^ ka))
    (hNb : HasNF (MulAut.congr e (actHom K ⟨b, hb⟩)) εb (T ^ kb)) {i j : ℕ}
    (hε : (εβ + i * εa + j * εb) % 3 = 0) (hk : (kβ + i * ka + j * kb) % 3 = 0)
    (h3 : (β * a ^ i * b ^ j) ^ 3 = 1) :
    ∃ κ : ↥K, ∀ x : ↥K, (β * a ^ i * b ^ j) * (x : X) * (β * a ^ i * b ^ j)⁻¹ = κ * x * κ⁻¹ := by
  have hN : β * a ^ i * b ^ j ∈ Subgroup.normalizer (K : Set X) :=
    mul_mem (mul_mem hβ (pow_mem ha i)) (pow_mem hb j)
  have hNF := (hNβ.mul (hasNF_pow hNa i)).mul (hasNF_pow hNb j)
  have hk' : (kβ + ka * i + kb * j) % 3 = 0 := by rw [mul_comm ka, mul_comm kb]; exact hk
  rw [← congr_actHom_mul_pow_d4Eight e hβ ha hb i j hN, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
    pow_eq_one_of_mod_three_d4Eight hT3 hk'] at hNF
  obtain ⟨g, hg⟩ := exists_conj_of_hasNF_zero_d4Eight hNF hε (congr_actHom_pow_three_d4Eight e hN h3)
  exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2.exists_conj_of_inner hZ e hN hg.symm

theorem exists_frob_pow_one_two_d4Eight {T σ : F ≃+* F} (hT3 : T ^ 3 = 1) (h : σ = T ∨ σ = T⁻¹) :
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ σ = T ^ k := by
  rcases h with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, pow_one]⟩
  · exact ⟨2, Or.inr rfl, by rw [h]; exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)⟩

theorem cover_of_field_graph_d4Eight {K B : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hF : Nat.card F = 2 ^ 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F)) {a b : X} (haB : a ∈ B) (hbB : b ∈ B)
    (hA : D4ElemType (MulAut.congr e (actHom K ⟨a, hBN haB⟩)) fun ε _ => ε ≠ 0)
    (hBf : D4ElemType (MulAut.congr e (actHom K ⟨b, hBN hbB⟩)) fun ε σ => ε = 0 ∧ σ ≠ 1) :
    ∀ β ∈ B, ∃ i j : ℕ, ∃ κ : ↥K, ∀ x : ↥K,
      (β * a ^ i * b ^ j) * (x : X) * (β * a ^ i * b ^ j)⁻¹ = κ * x * κ⁻¹ := by
  intro β hβ
  obtain ⟨g₂, c₂, σ₂, ε₂, -, hσ₂3, ⟨rfl, hσ₂1⟩, hαb⟩ := hBf
  obtain ⟨T, hT, hT3, -, hσ₂T⟩ := exists_frobenius_eight hF hσ₂3 hσ₂1
  obtain ⟨g₁, c₁, σ₁, ε₁, hε₁3, hσ₁3, hε₁0, hαa⟩ := hA
  obtain ⟨g₃, c₃, σ₃, ε₃, -, hσ₃3, hαβ⟩ := CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma _
    (congr_actHom_pow_three_d4Eight e (hBN hβ) (hB.2 β hβ))
  obtain ⟨k₁, rfl⟩ := exists_eq_frob_pow_d4Eight hF hT hT3 hσ₁3
  obtain ⟨k₃, rfl⟩ := exists_eq_frob_pow_d4Eight hF hT hT3 hσ₃3
  obtain ⟨k₂, hk₂, rfl⟩ := exists_frob_pow_one_two_d4Eight hT3 hσ₂T
  have hε₁ : ε₁ = 1 ∨ ε₁ = 2 := by omega
  refine ⟨2 * ε₃ * ε₁, 2 * (k₃ + 2 * ε₃ * ε₁ * k₁) * k₂,
    exists_conj_of_nfCombo_d4Eight hZ e hT3 (hBN hβ) (hBN haB) (hBN hbB) ⟨g₃, c₃, hαβ⟩ ⟨g₁, c₁, hαa⟩
      ⟨g₂, c₂, hαb⟩ ?_ ?_ (hB.2 _ (mul_mem (mul_mem hβ (pow_mem haB _)) (pow_mem hbB _)))⟩
  · rcases hε₁ with rfl | rfl <;> omega
  · generalize k₃ + 2 * ε₃ * ε₁ * k₁ = s
    rcases hk₂ with rfl | rfl <;> omega

theorem cover_of_field_d4Eight {K B : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hF : Nat.card F = 2 ^ 3)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F)) {b : X} (hbB : b ∈ B)
    (hBf : D4ElemType (MulAut.congr e (actHom K ⟨b, hBN hbB⟩)) fun ε σ => ε = 0 ∧ σ ≠ 1)
    (hnoG : ∀ z (hz : z ∈ B), ¬ D4ElemType (MulAut.congr e (actHom K ⟨z, hBN hz⟩)) fun ε _ => ε ≠ 0) :
    ∀ β ∈ B, ∃ j : ℕ, ∃ κ : ↥K, ∀ x : ↥K, (β * b ^ j) * (x : X) * (β * b ^ j)⁻¹ = κ * x * κ⁻¹ := by
  intro β hβ
  obtain ⟨g₂, c₂, σ₂, ε₂, -, hσ₂3, ⟨rfl, hσ₂1⟩, hαb⟩ := hBf
  obtain ⟨T, hT, hT3, -, hσ₂T⟩ := exists_frobenius_eight hF hσ₂3 hσ₂1
  obtain ⟨g₃, c₃, σ₃, ε₃, hε₃3, hσ₃3, hαβ⟩ := CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma _
    (congr_actHom_pow_three_d4Eight e (hBN hβ) (hB.2 β hβ))
  have hε₃ : ε₃ = 0 := by
    by_contra h
    exact hnoG β hβ ⟨g₃, c₃, σ₃, ε₃, hε₃3, hσ₃3, h, hαβ⟩
  subst hε₃
  obtain ⟨k₃, rfl⟩ := exists_eq_frob_pow_d4Eight hF hT hT3 hσ₃3
  obtain ⟨k₂, hk₂, rfl⟩ := exists_frob_pow_one_two_d4Eight hT3 hσ₂T
  have h := exists_conj_of_nfCombo_d4Eight (i := 0) (j := 2 * k₃ * k₂) hZ e hT3 (hBN hβ) (hBN hbB) (hBN hbB)
    ⟨g₃, c₃, hαβ⟩ ⟨g₂, c₂, hαb⟩ ⟨g₂, c₂, hαb⟩ (by omega) (by rcases hk₂ with rfl | rfl <;> omega)
    (by rw [pow_zero, mul_one]; exact hB.2 _ (mul_mem hβ (pow_mem hbB _)))
  simp only [pow_zero, mul_one] at h
  exact ⟨_, h⟩

theorem cover_of_graph_d4Eight {K B : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(adjointGroup Tag.D4 F)) {a : X} (haB : a ∈ B)
    (hA : D4ElemType (MulAut.congr e (actHom K ⟨a, hBN haB⟩)) fun ε _ => ε ≠ 0)
    (hnoF : ∀ z (hz : z ∈ B),
      ¬ D4ElemType (MulAut.congr e (actHom K ⟨z, hBN hz⟩)) fun ε σ => ε = 0 ∧ σ ≠ 1) :
    ∀ β ∈ B, ∃ i : ℕ, ∃ κ : ↥K, ∀ x : ↥K, (β * a ^ i) * (x : X) * (β * a ^ i)⁻¹ = κ * x * κ⁻¹ := by
  intro β hβ
  obtain ⟨g₁, c₁, σ₁, ε₁, hε₁3, hσ₁3, hε₁0, hαa⟩ := hA
  obtain ⟨g₃, c₃, σ₃, ε₃, -, hσ₃3, hαβ⟩ := CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma _
    (congr_actHom_pow_three_d4Eight e (hBN hβ) (hB.2 β hβ))
  have hε₁ : ε₁ = 1 ∨ ε₁ = 2 := by omega
  refine ⟨2 * ε₃ * ε₁, ?_⟩
  set i := 2 * ε₃ * ε₁ with hi
  have hγB : β * a ^ i ∈ B := mul_mem hβ (pow_mem haB i)
  have hγ3 : (β * a ^ i) ^ 3 = 1 := hB.2 _ hγB
  have hprod : MulAut.congr e (actHom K ⟨β * a ^ i, hBN hγB⟩) =
      MulAut.congr e (actHom K ⟨β, hBN hβ⟩) * MulAut.congr e (actHom K ⟨a, hBN haB⟩) ^ i := by
    have h1 : (⟨β * a ^ i, hBN hγB⟩ : Subgroup.normalizer (K : Set X)) = ⟨β, hBN hβ⟩ * ⟨a, hBN haB⟩ ^ i :=
      Subtype.ext (by simp)
    rw [h1, map_mul, map_mul, map_pow, map_pow]
  have hNF : HasNF (MulAut.congr e (actHom K ⟨β * a ^ i, hBN hγB⟩)) (ε₃ + i * ε₁) (σ₃ * σ₁ ^ i) := by
    rw [hprod]
    exact (show HasNF _ ε₃ σ₃ from ⟨g₃, c₃, hαβ⟩).mul (hasNF_pow ⟨g₁, c₁, hαa⟩ i)
  have hε : (ε₃ + i * ε₁) % 3 = 0 := by rw [hi]; rcases hε₁ with rfl | rfl <;> omega
  have h3' := congr_actHom_pow_three_d4Eight e (hBN hγB) hγ3
  by_cases hσ : σ₃ * σ₁ ^ i = 1
  · rw [hσ] at hNF
    obtain ⟨g, hg⟩ := exists_conj_of_hasNF_zero_d4Eight hNF hε h3'
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2.exists_conj_of_inner hZ e (hBN hγB)
      hg.symm
  · exact absurd (d4ElemType_of_hasNF hNF h3' (c := fun ε σ => ε = 0 ∧ σ ≠ 1) ⟨hε, hσ⟩) (hnoF _ hγB)

theorem normalizerMonoidHom_eq_conj_d4Eight {K : Subgroup X} (n : Subgroup.normalizer (K : Set X))
    {κ : ↥K} (h : ∀ x : ↥K, (n : X) * (x : X) * (n : X)⁻¹ = κ * x * κ⁻¹) :
    K.normalizerMonoidHom n = MulAut.conj κ := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply, h x]
  simp

variable [Finite X]

theorem card_autIm_le_nine_mul_d4Eight {B K : Subgroup X} (hB : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) {a b : X} (haB : a ∈ B) (hbB : b ∈ B)
    (hcov : ∀ β ∈ B, ∃ i j : ℕ, ∃ κ : ↥K, ∀ x : ↥K,
      (β * a ^ i * b ^ j) * (x : X) * (β * a ^ i * b ^ j)⁻¹ = κ * x * κ⁻¹) :
    Nat.card ↥(InputsSeitz3.autIm B K) ≤
      Nat.card ↥(InputsSeitz3.autIm B K ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range) * 3 * 3 := by
  classical
  haveI : Finite (MulAut ↥K) := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.CartanConjAux.finite_mulAut ↥K
  set A := InputsSeitz3.autIm B K with hAdef
  set A₁ := A ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range with hA₁def
  have hmemA : ∀ z (hz : z ∈ B), K.normalizerMonoidHom ⟨z, hBN hz⟩ ∈ A := fun z hz =>
    ⟨⟨z, hBN hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
  have hAel := InputsSeitz3.isElemAbelian_autIm hB K
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set φa := K.normalizerMonoidHom ⟨a, hBN haB⟩ with hφa
  set φb := K.normalizerMonoidHom ⟨b, hBN hbB⟩ with hφb
  have hle : A ≤ (A₁ ⊔ Subgroup.zpowers φa) ⊔ Subgroup.zpowers φb := by
    rintro _ ⟨n, hn, rfl⟩
    have hnB : (n : X) ∈ B := Subgroup.mem_subgroupOf.1 hn
    obtain ⟨i, j, κ, hκ⟩ := hcov n hnB
    have hγB : (n : X) * a ^ i * b ^ j ∈ B := mul_mem (mul_mem hnB (pow_mem haB i)) (pow_mem hbB j)
    have hγ := normalizerMonoidHom_eq_conj_d4Eight ⟨(n : X) * a ^ i * b ^ j, hBN hγB⟩ hκ
    have hsplit : K.normalizerMonoidHom ⟨(n : X) * a ^ i * b ^ j, hBN hγB⟩ =
        K.normalizerMonoidHom n * φa ^ i * φb ^ j := by
      rw [hφa, hφb, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
      congr 1
    have hneq : K.normalizerMonoidHom n = MulAut.conj κ * (φb ^ j)⁻¹ * (φa ^ i)⁻¹ := by
      rw [← hγ, hsplit]
      group
    rw [hneq]
    have hκA : MulAut.conj κ ∈ A₁ := ⟨hγ ▸ hmemA _ hγB, ⟨κ, rfl⟩⟩
    refine mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hκA))
      (Subgroup.mem_sup_right (inv_mem (pow_mem (Subgroup.mem_zpowers _) j))))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (inv_mem (pow_mem (Subgroup.mem_zpowers _) i))))
  have hφa3 : φa ^ 3 = 1 := by
    rw [hφa, ← map_pow]
    have : (⟨a, hBN haB⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hB.2 a haB)
    rw [this, map_one]
  have hφb3 : φb ^ 3 = 1 := by
    rw [hφb, ← map_pow]
    have : (⟨b, hBN hbB⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hB.2 b hbB)
    rw [this, map_one]
  have hsupA : A₁ ⊔ Subgroup.zpowers φa ≤ A :=
    sup_le inf_le_left ((Subgroup.zpowers_le).2 (hmemA a haB))
  have h1 := Subgroup.card_le_of_le hle
  have h2 := InputsSeitz8.card_sup_le_mul_orthF2 (A := A₁ ⊔ Subgroup.zpowers φa) (C := Subgroup.zpowers φb)
    fun x hx y hy => hAcomm x (hsupA hx) y ((Subgroup.zpowers_le).2 (hmemA b hbB) hy)
  have h3 := InputsSeitz8.card_sup_le_mul_orthF2 (A := A₁) (C := Subgroup.zpowers φa)
    fun x hx y hy => hAcomm x (Subgroup.mem_inf.1 hx).1 y ((Subgroup.zpowers_le).2 (hmemA a haB) hy)
  have h4 := InputsSeitz8.card_zpowers_le_three_orthF2 hφa3
  have h5 := InputsSeitz8.card_zpowers_le_three_orthF2 hφb3
  calc Nat.card ↥A ≤ Nat.card ↥((A₁ ⊔ Subgroup.zpowers φa) ⊔ Subgroup.zpowers φb) := h1
    _ ≤ Nat.card ↥(A₁ ⊔ Subgroup.zpowers φa) * Nat.card ↥(Subgroup.zpowers φb) := h2
    _ ≤ Nat.card ↥A₁ * Nat.card ↥(Subgroup.zpowers φa) * Nat.card ↥(Subgroup.zpowers φb) :=
        Nat.mul_le_mul_right _ h3
    _ ≤ Nat.card ↥A₁ * 3 * 3 := Nat.mul_le_mul (Nat.mul_le_mul_left _ h4) h5

theorem card_autIm_le_three_mul_d4Eight {B K : Subgroup X} (hB : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) {a : X} (haB : a ∈ B)
    (hcov : ∀ β ∈ B, ∃ i : ℕ, ∃ κ : ↥K, ∀ x : ↥K, (β * a ^ i) * (x : X) * (β * a ^ i)⁻¹ = κ * x * κ⁻¹) :
    Nat.card ↥(InputsSeitz3.autIm B K) ≤
      Nat.card ↥(InputsSeitz3.autIm B K ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range) * 3 := by
  classical
  haveI : Finite (MulAut ↥K) := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.CartanConjAux.finite_mulAut ↥K
  set A := InputsSeitz3.autIm B K with hAdef
  set A₁ := A ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range with hA₁def
  have hmemA : ∀ z (hz : z ∈ B), K.normalizerMonoidHom ⟨z, hBN hz⟩ ∈ A := fun z hz =>
    ⟨⟨z, hBN hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
  have hAel := InputsSeitz3.isElemAbelian_autIm hB K
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set φa := K.normalizerMonoidHom ⟨a, hBN haB⟩ with hφa
  have hle : A ≤ A₁ ⊔ Subgroup.zpowers φa := by
    rintro _ ⟨n, hn, rfl⟩
    have hnB : (n : X) ∈ B := Subgroup.mem_subgroupOf.1 hn
    obtain ⟨i, κ, hκ⟩ := hcov n hnB
    have hγB : (n : X) * a ^ i ∈ B := mul_mem hnB (pow_mem haB i)
    have hγ := normalizerMonoidHom_eq_conj_d4Eight ⟨(n : X) * a ^ i, hBN hγB⟩ hκ
    have hsplit : K.normalizerMonoidHom ⟨(n : X) * a ^ i, hBN hγB⟩ = K.normalizerMonoidHom n * φa ^ i := by
      rw [hφa, ← map_pow, ← map_mul]
      congr 1
    have hneq : K.normalizerMonoidHom n = MulAut.conj κ * (φa ^ i)⁻¹ := by
      rw [← hγ, hsplit]
      group
    rw [hneq]
    have hκA : MulAut.conj κ ∈ A₁ := ⟨hγ ▸ hmemA _ hγB, ⟨κ, rfl⟩⟩
    exact mul_mem (Subgroup.mem_sup_left hκA)
      (Subgroup.mem_sup_right (inv_mem (pow_mem (Subgroup.mem_zpowers _) i)))
  have hφa3 : φa ^ 3 = 1 := by
    rw [hφa, ← map_pow]
    have : (⟨a, hBN haB⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hB.2 a haB)
    rw [this, map_one]
  have h1 := Subgroup.card_le_of_le hle
  have h3 := InputsSeitz8.card_sup_le_mul_orthF2 (A := A₁) (C := Subgroup.zpowers φa)
    fun x hx y hy => hAcomm x (Subgroup.mem_inf.1 hx).1 y ((Subgroup.zpowers_le).2 (hmemA a haB) hy)
  have h4 := InputsSeitz8.card_zpowers_le_three_orthF2 hφa3
  calc Nat.card ↥A ≤ Nat.card ↥(A₁ ⊔ Subgroup.zpowers φa) := h1
    _ ≤ Nat.card ↥A₁ * Nat.card ↥(Subgroup.zpowers φa) := h3
    _ ≤ Nat.card ↥A₁ * 3 := Nat.mul_le_mul_left _ h4

end NF

section D4EightOuter

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Dickson.I271
open CFSG.LieType.SeitzGeneration.ExcWideThree (HasNF D4ElemType)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

theorem not_fieldAutD4_one_d4Eight
    {S : Type} [Group S] : ¬ OuterFourInAux.FieldAutD4 S 1 := by
  rintro ⟨F, _, _, e, σ, γ, -, hσ1, hmat⟩
  apply hσ1
  apply OuterFourSeitz.eq_one_of_entrywise_eq_one
  refine MulEquiv.ext fun g => ?_
  obtain ⟨g', hg', hg''⟩ := hmat g
  have h1 : (γ * MulAut.congr e 1 * γ⁻¹) g = g := by simp
  rw [h1] at hg''
  apply Subtype.ext
  rw [MulAut.one_apply, coe_entrywiseAdjointAut, ← hg', ← hg'']


variable {X : Type} [Group X] [Finite X]

theorem le_glbCore_of_d4Eight_outer (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X}
    (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : OuterFourAux.IsD4EightIndex d.1)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hout : ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    exact InputsSeitz7.cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN hC
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  have hconj := Gen2318E68Aux.conj_injective_of_center_eq_bot hZ
  have hLie : IsLieQuot ↥K OuterFourAux.IsD4EightIndex := ⟨d, hd, ⟨e⟩⟩
  obtain ⟨d0, hv⟩ := d
  obtain ⟨q, rfl, hq⟩ : ∃ q : TauCeti.PrimePower, d0 = .D 4 q ∧ IsTwoPow q 3 := by
    cases d0 with
    | D r q =>
      obtain ⟨rfl, hq⟩ := hd
      exact ⟨q, rfl, hq⟩
    | _ => exact absurd hd (by simp [OuterFourAux.IsD4EightIndex])
  have hs : Seitz2313Cover.EvenScope (.D 4 q) := hq.1
  obtain ⟨F, _, _, e₁, hF⟩ := OuterFourInAux.exists_mulEquiv_adjointD4 hv hq e
  set A := InputsSeitz3.autIm B K with hAdef
  have hAel : IsElemAbelian 3 A := InputsSeitz3.isElemAbelian_autIm hB K
  have hAc : Nat.card A = 3 ^ CFSG.Open.pRank 3 B :=
    (InputsSeitz3.card_autIm hBN hC).trans (GL83.PiGen.card_eq_pow_pRank hB)
  set A₁ := A ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range with hA₁def
  have hA₁el : IsElemAbelian 3 A₁ := elem_mono hAel inf_le_left
  set D : Subgroup ↥K := A₁.comap (MulAut.conj : ↥K →* MulAut ↥K) with hDdef
  have hDmap : D.map MulAut.conj = A₁ := Subgroup.map_comap_eq_self inf_le_right
  have hDc : Nat.card D = Nat.card A₁ := by
    rw [← hDmap, Subgroup.card_map_of_injective hconj]
  have hDel : IsElemAbelian 3 D := InputsSeitz7.isElemAbelian_comap_of_injective hconj hA₁el
  have hDfix : ∀ z ∈ B, ∀ k ∈ D, z * (k : X) * z⁻¹ = k := by
    intro z hz k hk
    have hzA : K.normalizerMonoidHom ⟨z, hBN hz⟩ ∈ A := ⟨⟨z, hBN hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    have hkA : MulAut.conj k ∈ A := (hk : MulAut.conj k ∈ A₁).1
    set β := K.normalizerMonoidHom ⟨z, hBN hz⟩ with hβdef
    have hcomm : β * MulAut.conj k = MulAut.conj k * β :=
      congrArg Subtype.val (hAel.1.is_comm.comm ⟨_, hzA⟩ ⟨_, hkA⟩)
    have h1 : MulAut.conj (β k) = MulAut.conj k := by
      have e1 : MulAut.conj (β k) = β * MulAut.conj k * β⁻¹ := by
        ext x
        simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
      rw [e1, hcomm, mul_inv_cancel_right]
    have h2 : β k = k := hconj h1
    have h3 := congrArg Subtype.val h2
    rwa [hβdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
  have hgraph : ∀ a (ha : a ∈ B),
      D4ElemType (MulAut.congr e₁ (actHom K ⟨a, hBN ha⟩)) (fun ε _ => ε ≠ 0) → Nat.card D ≤ 9 := by
    intro a ha hG
    set ψK : ↥K ≃* ↥(adjointGroup Tag.D4 F) :=
      (OuterFourSeitz2.quotEquivOfCenterBot hZ).trans e₁ with hψKdef
    have hfix : ∀ y ∈ D.map ψK.toMonoidHom, MulAut.congr e₁ (actHom K ⟨a, hBN ha⟩) y = y := by
      rintro _ ⟨k, hk, rfl⟩
      show MulAut.congr e₁ (actHom K ⟨a, hBN ha⟩) (e₁ (QuotientGroup.mk k)) = e₁ (QuotientGroup.mk k)
      rw [OuterFourSeitz2.congr_actHom_apply]
      congr 2
      exact Subtype.ext (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe]; exact hDfix a ha k hk)
    have h9 := card_le_nine_of_graphType_d4Eight hF
      (congr_actHom_pow_three_d4Eight e₁ (hBN ha) (hB.2 a ha)) hG (D.map ψK.toMonoidHom)
      (CFSG.SectionRank.isElemAbelian_map hDel _) hfix
    rwa [Subgroup.card_map_of_injective ψK.injective] at h9
  have h81 : 3 ^ 4 ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) hB4
  by_cases hFt : ∃ b, ∃ hb : b ∈ B,
      D4ElemType (MulAut.congr e₁ (actHom K ⟨b, hBN hb⟩)) fun ε σ => ε = 0 ∧ σ ≠ 1
  ·
    obtain ⟨b, hbB, hbF⟩ := hFt
    have hbN := hBN hbB
    have hb3 : b ^ 3 = 1 := hB.2 b hbB
    have hFA := OuterFourSeitz.fieldAutD4_of_fieldType hF e₁ (by
      have h1 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set X)) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hb3)
      rw [← map_pow, h1, map_one]) hbF
    obtain ⟨hLs, hLq, -, ⟨⟨d0', hv'⟩, hd', ⟨eL'⟩⟩⟩ :=
      OuterFourInAux.d4FieldFixed_holds X K b hbN hK hLie hb3 hFA
    set L : Subgroup X := K ⊓ Subgroup.centralizer ({b} : Set X) with hLdef
    have hZL : Subgroup.center ↥L = ⊥ := by
      haveI := hLs
      refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative fun hc => ?_
      have h1 := (commutator_eq_bot_iff ↥L).2 hc
      rw [hLq.1] at h1
      obtain ⟨a, c, hac⟩ := exists_pair_ne ↥L
      have ha : a ∈ (⊥ : Subgroup ↥L) := h1 ▸ Subgroup.mem_top a
      have hc' : c ∈ (⊥ : Subgroup ↥L) := h1 ▸ Subgroup.mem_top c
      exact hac ((Subgroup.mem_bot.1 ha).trans (Subgroup.mem_bot.1 hc').symm)
    obtain ⟨q', rfl, hq'p, hq'e⟩ : ∃ q' : TauCeti.PrimePower, d0' = .D 4 q' ∧ q'.p = 2 ∧ q'.exponent = 1 := by
      cases d0' with
      | D r q' =>
        obtain ⟨rfl, hq'⟩ := hd'
        exact ⟨q', rfl, hq'.1, hq'.2⟩
      | _ => exact absurd hd' (by simp [OuterFourInAux.IsD4TwoIndex])
    let eL : ↥L ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q', hv'⟩).Group :=
      (InputsSeitz3.equivCenterQuot hZL).trans eL'
    have hbK : b ∉ K := by
      intro hbK
      have hbL : b ∈ L := ⟨hbK, Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]⟩
      have hbZ : (⟨b, hbL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.1 y.2.2 b (Set.mem_singleton b)).symm
      rw [hZL, Subgroup.mem_bot] at hbZ
      have hb1' : b = 1 := congrArg Subtype.val hbZ
      have h1 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set X)) = 1 := Subtype.ext hb1'
      rw [h1, map_one] at hFA
      exact not_fieldAutD4_one_d4Eight hFA
    have hb1 : b ≠ 1 := fun h => hbK (h ▸ K.one_mem)
    have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
    have hEel : IsElemAbelian 3 (Subgroup.zpowers b) := F4InnerExAux.isElemAbelian_zpowers hb3
    have hEc : Nat.card (Subgroup.zpowers b) = 3 ^ 1 := by rw [Nat.card_zpowers, hbo, pow_one]
    have hrankL : ∀ F' : Subgroup ↥L, IsElemAbelian 3 F' → ∀ f : ℕ, Nat.card F' = 3 ^ f →
        1 + f ≤ CFSG.Open.pRank 3 B := by
      intro F' hF' f hf
      have hFel : IsElemAbelian 3 (F'.map L.subtype) := CFSG.SectionRank.isElemAbelian_map hF' _
      have hFc : Nat.card (F'.map L.subtype) = 3 ^ f := by
        rw [Subgroup.card_map_of_injective L.subtype_injective, hf]
      have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ F'.map L.subtype, x * y = y * x := by
        rintro x hx _ ⟨y, -, rfl⟩
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        have hyb : Commute b (y : X) := Subgroup.mem_centralizer_iff.1 y.2.2 b (Set.mem_singleton b)
        exact (hyb.zpow_left i).eq
      have hdisj : Subgroup.zpowers b ⊓ F'.map L.subtype = ⊥ := by
        have hdvd : Nat.card ↥(Subgroup.zpowers b ⊓ F'.map L.subtype) ∣ 3 := by
          rw [← pow_one 3, ← hEc]
          exact Subgroup.card_dvd_of_le inf_le_left
        rcases (Nat.dvd_prime hp).1 hdvd with h1 | h3
        · exact Subgroup.eq_bot_of_card_eq _ h1
        · exfalso
          have heq : Subgroup.zpowers b ⊓ F'.map L.subtype = Subgroup.zpowers b :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hEc, h3, pow_one])
          have hbE : b ∈ Subgroup.zpowers b ⊓ F'.map L.subtype := by
            rw [heq]
            exact Subgroup.mem_zpowers b
          obtain ⟨y, -, hy⟩ := hbE.2
          apply hbK
          rw [← hy]
          exact y.2.1
      have h := InputsSeitz.add_le_pRank_of_commute hp hEel hFel hcomm hdisj hEc hFc
      rw [hrk]
      exact h
    have h5 : 5 ≤ CFSG.Open.pRank 3 B := by
      have hL4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
        have hmod := CFSG.Models.lieModel_D 4 q' hv' eL
        rw [hq'p, hq'e] at hmod
        exact CFSG.HardMathSupport.Solomon.Coordinator.i1021_d4_pRank_ge_four
          (hmod.statedClassicalModel (by decide))
      obtain ⟨E₀, -, hE₀el, hE₀c⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup ↥L)
      obtain ⟨E₄, hE₄c, -, hE₄E₀⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 4) (H := ⊥)
        (L := E₀) (by rw [Subgroup.card_bot]; exact one_dvd _) (by rw [hE₀c]; exact Nat.pow_dvd_pow 3 hL4)
        bot_le
      have := hrankL E₄ (elem_mono hE₀el hE₄E₀) 4 hE₄c
      omega
    by_cases hGt : ∃ a, ∃ ha : a ∈ B, D4ElemType (MulAut.congr e₁ (actHom K ⟨a, hBN ha⟩)) fun ε _ => ε ≠ 0
    ·
      exfalso
      obtain ⟨a, haB, haG⟩ := hGt
      have h9 := hgraph a haB haG
      have hidx := card_autIm_le_nine_mul_d4Eight hB hBN haB hbB
        (cover_of_field_graph_d4Eight hZ hB hBN hF e₁ haB hbB haG hbF)
      rw [← hAdef, ← hA₁def, hAc, ← hDc] at hidx
      have h243 : 3 ^ 5 ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) h5
      omega
    ·
      have hnoG : ∀ z (hz : z ∈ B),
          ¬ D4ElemType (MulAut.congr e₁ (actHom K ⟨z, hBN hz⟩)) fun ε _ => ε ≠ 0 :=
        fun z hz h => hGt ⟨z, hz, h⟩
      have hidx := card_autIm_le_three_mul_d4Eight hB hBN hbB (cover_of_field_d4Eight hZ hB hBN hF e₁ hbB hbF hnoG)
      rw [← hAdef, ← hA₁def, hAc, ← hDc] at hidx
      set r := CFSG.Open.pRank 3 B with hr
      have hDlow : 3 ^ (r - 1) ≤ Nat.card D := by
        have h2 : 3 ^ r = 3 ^ (r - 1) * 3 := by rw [← pow_succ]; congr 1; omega
        rw [h2] at hidx
        exact Nat.le_of_mul_le_mul_right hidx (by norm_num)
      set DX : Subgroup X := D.map K.subtype with hDX
      have hDXL : DX ≤ L := by
        rintro _ ⟨k, hk, rfl⟩
        refine ⟨k.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have h3 := hDfix y hbB k hk
        calc y * (k : X) = (y * k * y⁻¹) * y := by group
          _ = k * y := by rw [h3]
      set DL : Subgroup ↥L := DX.subgroupOf L with hDL
      have hDLc : Nat.card DL = Nat.card D := by
        rw [hDL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDXL).toEquiv, hDX,
          Subgroup.card_map_of_injective K.subtype_injective]
      have hDLel : IsElemAbelian 3 DL :=
        CFSG.Open.IsElemAbelian.subgroupOf (CFSG.SectionRank.isElemAbelian_map hDel _) L
      have hmaxL : ∀ F' : Subgroup ↥L, IsElemAbelian 3 F' → Nat.card F' ≤ Nat.card DL := by
        intro F' hF'
        obtain ⟨f, hf⟩ := GL83.CompFam.exists_card_eq_pow hF'
        have h1 := hrankL F' hF' f hf
        rw [hf, hDLc]
        exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hDlow
      obtain ⟨r', hr'⟩ := GL83.CompFam.exists_card_eq_pow hDLel
      have hr'4 : 4 ≤ r' := by
        have h1 : 3 ^ (r - 1) ≤ 3 ^ r' := by rw [← hr', hDLc]; exact hDlow
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
        omega
      obtain ⟨ψL⟩ := InputsSeitz8.nonempty_equiv_elementaryGroup_plus_orthF2 (by norm_num : 3 ≤ 4) hv' hq'p
        hq'e eL
      obtain ⟨H, hHD, hHc, U, hU0, hU2, hUH⟩ := exists_hyp_twoGroup_d4Two ψL hDLel hr' hr'4 hmaxL
      have hLK : L ≤ K := inf_le_left
      set HK : Subgroup ↥K := (H.map L.subtype).comap K.subtype with hHK
      set UK : Subgroup ↥K := (U.map L.subtype).comap K.subtype with hUK
      have hHKmap : HK.map K.subtype = H.map L.subtype := Subgroup.map_comap_eq_self (by
        rw [Subgroup.range_subtype]
        exact (Subgroup.map_subtype_le H).trans hLK)
      have hUKmap : UK.map K.subtype = U.map L.subtype := Subgroup.map_comap_eq_self (by
        rw [Subgroup.range_subtype]
        exact (Subgroup.map_subtype_le U).trans hLK)
      have hHKc : Nat.card HK = 3 ^ 3 := by
        rw [← Subgroup.card_map_of_injective K.subtype_injective, hHKmap,
          Subgroup.card_map_of_injective L.subtype_injective, hHc]
      have hHKD : HK ≤ D := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := (hx : (x : X) ∈ H.map L.subtype)
        obtain ⟨k, hk, hkx⟩ := (Subgroup.mem_subgroupOf.1 (hHD hy) : (y : X) ∈ DX)
        have hkx' : k = x := Subtype.ext (hkx.trans hyx)
        exact hkx' ▸ hk
      have hUK0 : UK ≠ ⊥ := by
        intro h
        apply hU0
        have h1 : U.map L.subtype = ⊥ := by rw [← hUKmap, h, Subgroup.map_bot]
        exact (Subgroup.map_eq_bot_iff_of_injective U L.subtype_injective).1 h1
      have hUK2 : IsPGroup 2 ↥UK := (hU2.map L.subtype).comap_of_injective K.subtype K.subtype_injective
      refine le_glbCore_of_e27_twoGroup hB hs eK le_rfl hC (F := HK.map MulAut.conj) ?_ ?_ hUK0 hUK2 ?_
      · exact (Subgroup.map_mono hHKD).trans (hDmap.le.trans inf_le_left)
      · rw [Subgroup.card_map_of_injective hconj, hHKc]
      · rintro _ ⟨h, hh, rfl⟩ u hu
        obtain ⟨h₁, hh₁, hh₁h⟩ := (hh : (h : X) ∈ H.map L.subtype)
        obtain ⟨u₁, hu₁, hu₁u⟩ := (hu : (u : X) ∈ U.map L.subtype)
        show ((MulAut.conj h u : ↥K) : X) ∈ U.map L.subtype
        refine ⟨h₁ * u₁ * h₁⁻¹, hUH h₁ hh₁ u₁ hu₁, ?_⟩
        rw [MulAut.conj_apply]
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hh₁h hu₁u ⊢
        rw [hh₁h, hu₁u]
  ·
    have hnoF : ∀ z (hz : z ∈ B),
        ¬ D4ElemType (MulAut.congr e₁ (actHom K ⟨z, hBN hz⟩)) fun ε σ => ε = 0 ∧ σ ≠ 1 :=
      fun z hz h => hFt ⟨z, hz, h⟩
    by_cases hGt : ∃ a, ∃ ha : a ∈ B, D4ElemType (MulAut.congr e₁ (actHom K ⟨a, hBN ha⟩)) fun ε _ => ε ≠ 0
    ·
      exfalso
      obtain ⟨a, haB, haG⟩ := hGt
      have h9 := hgraph a haB haG
      have hidx := card_autIm_le_three_mul_d4Eight hB hBN haB (cover_of_graph_d4Eight hZ hB hBN e₁ haB haG hnoF)
      rw [← hAdef, ← hA₁def, hAc, ← hDc] at hidx
      omega
    ·
      exfalso
      apply hout
      rintro _ ⟨n, hn, rfl⟩
      have hnB : (n : X) ∈ B := Subgroup.mem_subgroupOf.1 hn
      obtain ⟨g, c, σ, ε, hε3, hσ3, hα⟩ := CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma _
        (congr_actHom_pow_three_d4Eight e₁ (hBN hnB) (hB.2 _ hnB))
      have hε0 : ε = 0 := by
        by_contra h
        exact hGt ⟨n, hnB, g, c, σ, ε, hε3, hσ3, h, hα⟩
      have hσ1 : σ = 1 := by
        by_contra h
        exact hnoF n hnB ⟨g, c, σ, ε, hε3, hσ3, ⟨hε0, h⟩, hα⟩
      subst hε0 hσ1
      obtain ⟨g', hg'⟩ := exists_conj_of_hasNF_zero_d4Eight ⟨g, c, hα⟩ (by norm_num)
        (congr_actHom_pow_three_d4Eight e₁ (hBN hnB) (hB.2 _ hnB))
      obtain ⟨κ, hκ⟩ := OuterFourSeitz2.exists_conj_of_inner hZ e₁ (hBN hnB) hg'.symm
      exact ⟨κ, (normalizerMonoidHom_eq_conj_d4Eight n hκ).symm⟩

end D4EightOuter

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz10

end
