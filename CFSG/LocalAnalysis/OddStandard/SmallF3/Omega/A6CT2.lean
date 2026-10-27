module

public import Certificates.Data.A6CMatK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CDet
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CKind
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CPairK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CRefl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CT1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CThetaR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem a6c_refl0M6_toMat :
    A6CToMat 6 (Certificates.A6C.refl0M6 ()) =
      Matrix.diagonal fun i : Fin 6 =>
        if i ∈ ({0} : Finset (Fin 6)) then (-1 : ZMod 3) else 1 := by
  decide +kernel

theorem a6c_KM2_of_refl (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (fr : NFrame Q (Fin 6) 1) {m : A6CModel 6 (ProjSim Q)}
    (hm : ∀ J : Finset (Fin 6),
      m.ofMat (Matrix.diagonal fun i => if i ∈ J then (-1 : ZMod 3) else 1) =
        QuotientGroup.mk (orthToSim Q (fr.signChange J))) {y : ProjSim Q}
    (hy : IsConj (A6CElt m (Certificates.A6C.refl0M6 ())) y) : KM2 y := by
  obtain ⟨δ, rfl⟩ := isConj_iff.mp hy
  have h0 : A6CElt m (Certificates.A6C.refl0M6 ()) =
      QuotientGroup.mk (orthToSim Q (fr.signChange {0})) := by
    rw [A6CElt, a6c_refl0M6_toMat]
    exact hm {0}
  rw [h0] at *
  exact a6c_KM2_conj hQ (a6c_signChange_KM2 hdim fr 0) δ

theorem a6c_invol_class (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) {m : A6CModel 6 (ProjSim Q)}
    (hm : ∀ J : Finset (Fin 6),
      m.ofMat (Matrix.diagonal fun i => if i ∈ J then (-1 : ZMod 3) else 1) =
        QuotientGroup.mk (orthToSim Q (fr.signChange J))) {X : Type} [Group X]
    (φ : X →* ProjSim Q)
    (hmem : ∀ x : X, ∃ u : ↥(omegaProj hQ), φ x = projOrthToProjSim Q (u : ProjOrth Q)) :
    ∀ a ∈ φ.range, a * a = 1 → a ≠ 1 →
      IsConj (A6CElt m (Certificates.A6C.a0M6 ())) a := by
  have hJ : Even ({0, 1} : Finset (Fin 6)).card := by decide
  let u0 : ↥(omegaProj hQ) :=
    omegaToProj hQ ⟨fr.signChange {0, 1}, fr.signChange_mem_omegaGroup hQ {0, 1} hJ⟩
  have hu0img : projOrthToProjSim Q (u0 : ProjOrth Q) = A6CElt m (Certificates.A6C.a0M6 ()) := by
    show QuotientGroup.mk (orthToSim Q (fr.signChange {0, 1})) = _
    rw [← hm {0, 1}, A6CElt, a6c_a0M6_toMat]
  have hu0sq : u0 * u0 = 1 := by
    rw [← map_mul]
    have : (⟨fr.signChange {0, 1}, fr.signChange_mem_omegaGroup hQ {0, 1} hJ⟩ *
        ⟨fr.signChange {0, 1}, fr.signChange_mem_omegaGroup hQ {0, 1} hJ⟩ : omegaGroup hQ) = 1 :=
      Subtype.ext (fr.signChange_mul_self {0, 1})
    rw [this, map_one]
  have hu01 : u0 ≠ 1 := by
    intro h
    apply a6c_a0M6_ne_one m
    rw [← hu0img, h]
    exact map_one _
  rintro a ⟨x, rfl⟩ haa ha1
  obtain ⟨u, hu⟩ := hmem x
  rw [hu] at haa ha1 ⊢
  have hu2 : u * u = 1 := by
    refine Subtype.ext (projOrthToProjSim_injective (Q := Q) ?_)
    show projOrthToProjSim Q ((u : ProjOrth Q) * (u : ProjOrth Q)) = projOrthToProjSim Q 1
    rw [map_mul, map_one]
    exact haa
  have hu1 : u ≠ 1 := fun h => ha1 (by rw [h]; exact map_one _)
  obtain ⟨b, hb⟩ := ff6m_conj_involutions hQ hdim hsgn hu0sq hu2 hu01 hu1
  refine isConj_iff.mpr ⟨projOrthToProjSim Q (b : ProjOrth Q), ?_⟩
  have hb' := congrArg (fun w : ↥(omegaProj hQ) => projOrthToProjSim Q (w : ProjOrth Q)) hb
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hu0img] at hb'
  exact hb'

private theorem a6c_two_ne_one {K : Type} [Group K] [Finite K] (h : 2 < Nat.card K) :
    ∃ a b : K, a ≠ b ∧ a ≠ 1 ∧ b ≠ 1 := by
  haveI := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h
  by_cases ha : a = 1
  · exact ⟨b, c, hbc, fun hb => hab (ha.trans hb.symm), fun hc => hac (ha.trans hc.symm)⟩
  · by_cases hb : b = 1
    · exact ⟨a, c, hac, ha, fun hc => hbc (hb.trans hc.symm)⟩
    · exact ⟨a, b, hab, ha, hb⟩

@[expose] def A6CKFacts : Prop :=
  ∀ {Γ : Type} [Group Γ] (m : A6CModel 6 Γ), Nat.card Γ = 26127360 →
    A6CPairFactsK Γ (fun a => IsConj (A6CElt m (Certificates.A6C.a0M6 ())) a)
      (fun y => IsConj (A6CElt m (Certificates.A6C.refl0M6 ())) y) 40 4

theorem a6c_e8LayerFact_of_facts (hF : A6CKFacts) : Asc82E8LayerFact := by
  intro G _ _ X Y R hX hY hXL hY6 hXY hR2 hR hrel
  have hY' : IsOm6M Y := ⟨hY, hY6⟩
  obtain ⟨V, _, _, _, Q, hQ, hdim, hsgn, ⟨e⟩⟩ := ff_isOmegaStar_center_six_minus hY'
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hsh : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)) :=
    Or.inr ⟨hdim, Or.inr hsgn⟩
  obtain ⟨φ, ψ, hker, hmem, hcomm, hψ, hind⟩ := a6c_theta_homs_ind hQ hsh
    hY.1.commutator_eq_top e hXY (fun r hr => (hR hr).1) (fun r hr => (hR hr).2)
  obtain ⟨⟨eA⟩, hodd⟩ := a6c_X_facts hX hXL
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  obtain ⟨m, hm⟩ := a6c_model_of_frame fr one_ne_zero
  have hcard : Nat.card (ProjSim Q) = 26127360 := ff_natCard_projSim_six_minus hQ hdim hsgn
  haveI : Finite (ProjSim Q) := Nat.finite_of_card_ne_zero (by omega)
  have hΓ : ¬ 25 ∣ Nat.card (ProjSim Q) := by rw [hcard]; norm_num
  have hA := a6c_invol_class hQ hdim hsgn fr hm φ hmem
  obtain ⟨⟨hle, hexp⟩, hrefl⟩ := a6c_redK
    (P := fun a => IsConj (A6CElt m (Certificates.A6C.a0M6 ())) a)
    (Rf := fun a => IsConj (A6CElt m (Certificates.A6C.refl0M6 ())) a) (kc := 40) (bound := 4)
    (fun a δ ha => ha.trans (isConj_iff.mpr ⟨δ, rfl⟩))
    (fun a δ ha => ha.trans (isConj_iff.mpr ⟨δ, rfl⟩)) hΓ (by norm_num)
    (hF m hcard) φ ψ eA hodd hker hA hcomm
  have hK4 : Nat.card ψ.range = 4 := by
    have h4 := hrel
    rw [Subgroup.relIndex, ← hψ, Subgroup.index_ker] at h4
    exact h4
  have hss : ∀ r : ↥R, (r : G) * (r : G) ∈ centralizer (Y : Set G) := by
    intro r
    have h1 : ψ (r * r) = 1 := by
      rw [map_mul]
      exact hexp _ ⟨r, rfl⟩
    have h3 : (r * r) ∈ ψ.ker := h1
    rw [hψ] at h3
    exact h3
  have hKM2 : ∀ r : ↥R, IsOmega5 (layerCent Y r) → KM2 (ψ r) := fun r hΩ =>
    a6c_KM2_of_isOmega5 hY' hdim hsgn (hind r) (hss r) (hexp _ ⟨r, rfl⟩) hΩ
  refine ⟨?_, ?_⟩
  ·
    haveI : Finite ψ.range := inferInstance
    obtain ⟨y₁, y₂, hne, h1, h2'⟩ := a6c_two_ne_one (K := ψ.range) (by omega)
    have hRf : ∃ κ ∈ ψ.range, IsConj (A6CElt m (Certificates.A6C.refl0M6 ())) κ := by
      rcases hrefl y₁ y₁.2 y₂ y₂.2 (fun h => hne (Subtype.ext h)) (fun h => h1 (Subtype.ext h))
        (fun h => h2' (Subtype.ext h)) with k | k | k
      · exact ⟨y₁, y₁.2, k⟩
      · exact ⟨y₂, y₂.2, k⟩
      · exact ⟨y₁ * y₂, mul_mem y₁.2 y₂.2, k⟩
    obtain ⟨κ, ⟨r₀, hr₀⟩, hκ⟩ := hRf
    refine ⟨(r₀ : G), r₀.2, a6c_isOmega5_of_KM2 hY' hdim hsgn (hind r₀) (hss r₀) ?_⟩
    rw [hr₀]
    exact a6c_KM2_of_refl hQ hdim fr hm hκ
  · intro r hr hΩ
    let r' : ↥R := ⟨r, hr⟩
    have hx := hKM2 r' hΩ
    refine ⟨(isComponentIn_layerCent (Or.inl hΩ)).isQuasisimple, ?_, ?_⟩
    · refine a6c_le_layerCent hY' hdim hsgn (hind r') (hss r') hx hX.1 hXY ?_
      intro u hu
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hR hr).2 u hu)
    · intro s hs
      obtain ⟨hsR, hsC⟩ := Subgroup.mem_inf.mp hs
      let s' : ↥R := ⟨s, hsR⟩
      obtain ⟨E₀, hE₀perf, hE₀card, hE₀mem⟩ :=
        a6c_layerCent_image hY' hdim hsgn (hind r') (hss r') hx
      have hfixs : ∀ w ∈ E₀, ffSimOmegaAct hQ h2 (ψ s') w = w := by
        intro w hw
        obtain ⟨c, hcL, rfl⟩ := hE₀mem w hw
        have hcs : (c : G) * s = s * (c : G) := Subgroup.mem_centralizer_iff.mp hsC (c : G) hcL
        exact ff6m_phi_conj hQ h2 e (hind s') c c
          (mul_inv_eq_iff_eq_mul.mpr hcs.symm).symm
      have hfixr : ∀ w ∈ E₀, ffSimOmegaAct hQ h2 (ψ r') w = w := by
        intro w hw
        obtain ⟨c, hcL, rfl⟩ := hE₀mem w hw
        have hcr : (c : G) * r = r * (c : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp (a6c_layerCent_le Y r hcL).2
        exact ff6m_phi_conj hQ h2 e (hind r') c c (mul_inv_eq_iff_eq_mul.mpr hcr.symm).symm
      have hE₀big : 6048 < Nat.card ↥E₀ := by rw [hE₀card]; norm_num
      have key : ψ s' = 1 ∨ ψ s' = ψ r' := by
        by_contra hcon
        push Not at hcon
        obtain ⟨hy1, hyx⟩ := hcon
        have hy2 : ψ s' * ψ s' = 1 := hexp _ ⟨s', rfl⟩
        have hKy : KM2 (ψ s') := a6c_fix_small hQ hdim hsgn hy2 hy1 E₀
          (fun w hw => mem_fixSub_iff.mpr (hfixs w hw)) hE₀perf hE₀big
        have hx2 : ψ r' * ψ r' = 1 := hexp _ ⟨r', rfl⟩
        have hxy1 : ψ r' * ψ s' ≠ 1 := by
          intro h
          exact hyx ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hx2))
        have hxy2 : (ψ r' * ψ s') * (ψ r' * ψ s') = 1 :=
          hexp _ (mul_mem ⟨r', rfl⟩ ⟨s', rfl⟩)
        have hKxy : KM2 (ψ r' * ψ s') := a6c_fix_small hQ hdim hsgn hxy2 hxy1 E₀
          (fun w hw => mem_fixSub_iff.mpr (by
            rw [map_mul, MulAut.mul_apply, hfixs w hw, hfixr w hw])) hE₀perf hE₀big
        exact a6c_not_KM2_mul hdim hx hKy hKxy
      rcases key with k | k
      · have h3 : s' ∈ ψ.ker := k
        rw [hψ] at h3
        exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hsR, h3⟩)
      · have h3 : s' * r'⁻¹ ∈ ψ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, k, mul_inv_cancel]
        rw [hψ] at h3
        have h4 : s = (s * r⁻¹) * r := by group
        rw [h4]
        exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨mul_mem hsR (inv_mem hr), h3⟩)
          (Subgroup.mem_zpowers r)

end CFSG.OddStandard.SmallF3.Omega
