module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Glob
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18j
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18m
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbThm3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL412
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13o
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18q2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18r

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4B

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma k18t2_inv_conj_eq_of_comm {x c : G} (h : x * c = c * x) : c⁻¹ * x * c = x := by
  have h1 : c⁻¹ * x = x * c⁻¹ := by
    calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * x) * c⁻¹ := by rw [h]
      _ = x * c⁻¹ := by group
  rw [h1]; group

theorem k18_glob_B' {OK V W E₀ : Subgroup G} {g₁ : G}
    (hOKsylow : IsSylowIn 2 OK (centralizer (V : Set G)))
    (hE₀2 : IsPGroup 2 E₀) (hE₀W : E₀ ≤ centralizer (W : Set G)) (hg₁ : cj g₁ W = V) :
    ∃ g₂ : G, cj g₂ W = V ∧ cj g₂ E₀ ≤ OK := by
  have hE₁le : cj g₁ E₀ ≤ centralizer (V : Set G) := by
    have h := cj_mono (g := g₁) hE₀W
    rwa [cj_centralizer g₁ W, hg₁] at h
  have hE₁2 : IsPGroup 2 (cj g₁ E₀) := isPGroup_cj hE₀2
  obtain ⟨T, hTsyl, hE₁T⟩ := exists_isSylowIn_of_le hE₁le hE₁2
  obtain ⟨c, hcV, hcT⟩ := exists_cj_of_isSylowIn hOKsylow hTsyl
  refine ⟨c⁻¹ * g₁, ?_, ?_⟩
  · calc cj (c⁻¹ * g₁) W = cj c⁻¹ (cj g₁ W) := by rw [cj_cj c⁻¹ g₁ W]
      _ = cj c⁻¹ V := by rw [hg₁]
      _ = V := by
        apply cj_eq_self_of_centralizes
        intro x hx
        simpa using k18t2_inv_conj_eq_of_comm ((Subgroup.mem_centralizer_iff.mp hcV) x hx)
  · calc cj (c⁻¹ * g₁) E₀ = cj c⁻¹ (cj g₁ E₀) := by rw [cj_cj c⁻¹ g₁ E₀]
      _ ≤ cj c⁻¹ T := cj_mono hE₁T
      _ = cj c⁻¹ (cj c OK) := by rw [hcT]
      _ = cj (c⁻¹ * c) OK := by rw [cj_cj c⁻¹ c OK]
      _ = cj 1 OK := by rw [inv_mul_cancel c]
      _ = OK := by rw [cj_one OK]

theorem k18_glob_D' {C Y V W Q : Subgroup G} {g₂ : G}
    (hE : IsSylowIn 2 C (centralizer (Y : Set G)))
    (hW : cj g₂ W = V) (hY : cj g₂ Y = Y) (hVY : V ≤ Y)
    (hQ : ∀ h ∈ normalizer (C : Set G), ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (hVQ : ∀ h : G, (∀ q ∈ Q, h * q * h⁻¹ ∈ Q) → ∀ v ∈ V, h * v * h⁻¹ ∈ V)
    (hWV : W ≠ V) : False := by
  have hAB : centralizer (Y : Set G) ≤ normalizer (Y : Set G) :=
    Subgroup.centralizer_le_normalizer (Y : Set G)
  have hAnorm : ∀ b ∈ normalizer (Y : Set G), ∀ a ∈ centralizer (Y : Set G),
      b * a * b⁻¹ ∈ centralizer (Y : Set G) := by
    intro b hb a ha
    rw [Subgroup.mem_centralizer_iff] at ha ⊢
    intro y hy
    have hby : b⁻¹ * y * b ∈ Y := (Subgroup.mem_normalizer_iff''.mp hb y).mp hy
    calc y * (b * a * b⁻¹) = b * ((b⁻¹ * y * b) * a) * b⁻¹ := by group
      _ = b * (a * (b⁻¹ * y * b)) * b⁻¹ := by rw [ha _ hby]
      _ = (b * a * b⁻¹) * y := by group
  have hg₂B : g₂ ∈ normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    constructor
    · intro hx
      have hx' : x ∈ cj g₂ Y := by rw [hY]; exact hx
      exact mem_cj.mp hx'
    · intro hx
      have hx' : x ∈ cj g₂ Y := mem_cj.mpr hx
      rwa [hY] at hx'
  obtain ⟨a, ha, h, _hhB, hhcj, hga⟩ :=
    exists_mul_mem_normalizer hAB hAnorm hE g₂ hg₂B
  have hnorm : h ∈ normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    constructor
    · intro hx
      have hx' : x ∈ cj h C := by rw [hhcj]; exact hx
      exact mem_cj.mp hx'
    · intro hx
      have hx' : x ∈ cj h C := mem_cj.mpr hx
      rwa [hhcj] at hx'
  have hhV : cj h V = V := cj_eq_self_of_normalizes (hVQ h (hQ h hnorm))
  have haV : ∀ v ∈ V, a * v * a⁻¹ = v := by
    intro v hv
    have hav : v * a = a * v := (Subgroup.mem_centralizer_iff.mp ha) v (hVY hv)
    calc a * v * a⁻¹ = (v * a) * a⁻¹ := by rw [← hav]
      _ = v := by group
  have haVinv : ∀ v ∈ V, a⁻¹ * v * (a⁻¹)⁻¹ = v := by
    intro v hv
    have hv' := haV v hv
    calc a⁻¹ * v * (a⁻¹)⁻¹ = a⁻¹ * (a * v * a⁻¹) * a := by rw [hv']; group
      _ = v := by group
  have haVinv_cj : cj a⁻¹ V = V := cj_eq_self_of_centralizes haVinv
  have hVeq : V = cj a (cj h W) := by
    calc V = cj g₂ W := hW.symm
      _ = cj (a * h) W := by rw [hga]
      _ = cj a (cj h W) := by rw [cj_cj a h W]
  have hhW : cj h W = V := by
    have hthis := congrArg (cj a⁻¹) hVeq
    rw [haVinv_cj] at hthis
    rw [cj_cj a⁻¹ a (cj h W), inv_mul_cancel a, cj_one (cj h W)] at hthis
    exact hthis.symm
  have hWV' : W = V := cj_injective h (by rw [hhW, hhV])
  exact hWV hWV'

theorem k18_caseA_false_of_sylowV (hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮)
    (hV : IsSylowIn 2 (ctxOK t tau x₁ x₂ rho)
      (centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G))) : False := by
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  have hc18S : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮 := hc.toCtx18S
  have hc18 : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮 := hc.toCtx18
  obtain ⟨V', v₁, v₂, hVd⟩ := hc13.data_V
  have h𝒮2 : IsPGroup 2 𝒮 := hc.sylow.2.1
  have hfus : ∃ h : G, h * t * h⁻¹ = lam * t := by
    obtain ⟨h, hh⟩ := l17_tlam_conj hc13
    exact ⟨h, by rw [hh, (l17_lam_comm hc13).1]⟩
  obtain ⟨g₁, hg₁⟩ := k18_glob_A (S := S) (D := 𝒮 ⊓ centralizer ({lam * t} : Set G))
    (W := ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) (V := fourGrp x₁ x₂)
    (t := t) (u := lam * t)
    ⟨hc.le_invCent, hc.isPGroup, hc.relIndex_odd⟩ (Ctx4.card_S_seven hc.toCtx4) hfus
    (h𝒮2.to_le inf_le_left) inf_le_right (k18_card_Csylow_u hc18 hVd)
    (k18_W_normal hc18S).1 (k18_W_normal hc18S).2 (k18_W_elem hc13) (k18_W_card hc13 hVd)
    (k18_W_tG hc13) (fun W' h1 h2 h3 h4 => (hc.l45 W' h1 h2 h3 h4).1)
  obtain ⟨g₂, hg₂W, hg₂E⟩ := k18_glob_B' (OK := ctxOK t tau x₁ x₂ rho)
    (V := fourGrp x₁ x₂) (W := ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G))
    (E₀ := k18E0 t tau x₁ x₂ lam rho om) hV (h𝒮2.to_le (k18_E0_le_sylow hc18S))
    (k18_E0_cent_W hc13) hg₁
  have hY : cj g₂ (ctxYq t tau x₁ x₂ rho) = ctxYq t tau x₁ x₂ rho :=
    k18_glob_C (OK := ctxOK t tau x₁ x₂ rho) (E₀ := k18E0 t tau x₁ x₂ lam rho om)
      (B₀ := k18B0 t tau x₁ x₂ rho) (Y := ctxYq t tau x₁ x₂ rho)
      (N := ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) hg₂E (k18_B0_le_derived hc13 hVd)
      (k18_OK_derived_le hc) (k18_B0_card hc13) (k18_card_QT hc13) (k18_B0_cent hc13)
      (l17_Y_elem hc13) (l17_card_Y hc13) (lemma4_15_proof hc13)
  exact k18_glob_D' (C := ctxCY t tau x₁ x₂ rho) (Y := ctxYq t tau x₁ x₂ rho)
    (V := fourGrp x₁ x₂) (W := ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G))
    (Q := ctxQ t tau x₁ x₂ rho) (k18_C_sylow hc)
    hg₂W hY (l17_V_le_Y hc13) (k18_normalizer_C_Q hc) (fun h hh => k18_V_conj hc13 hh)
    (k18_W_ne_V hc13 hVd)

end S4B

@[expose] def Lemma418CaseASylowVStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}
    (_hG : Sec4Glob G) (_hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮),
    IsSylowIn 2 (ctxOK t tau x₁ x₂ rho) (centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G))

@[expose] def Lemma418CaseAFuStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}
    (_hG : Sec4Glob G) (_hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) {g e : G},
    e ∈ ctxOK t tau x₁ x₂ rho → g * t * g⁻¹ = e * (lam * t) →
      ∃ o ∈ ctxOK t tau x₁ x₂ rho, e * (lam * t) = o * (lam * t) * o⁻¹

theorem lemma418_sylowV_of_Fu (h : Lemma418CaseAFuStmt) : Lemma418CaseASylowVStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau om 𝒮 hG hc
  exact S4B.k18_sylowV_of_Fu hc (fun {g e} he hg => h hG hc he hg)

theorem lemma418_caseA_of_sylowV (h : Lemma418CaseASylowVStmt) : Lemma418CaseAStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau om 𝒮 hG hc hcard
  exact S4B.k18_caseA_false_of_sylowV ⟨hc, hcard⟩ (h hG ⟨hc, hcard⟩)

theorem harris1981_bound_reduced13B (h41 : Lemma4_1Stmt) (h41c : CtxOfLemma4_1Stmt)
    (h411 : Lemma4_11Stmt) (h413 : Lemma4_13Stmt) (hK : Ctx13KStmt)
    (hV : Lemma418CaseASylowVStmt) (hI : Sec4Inputs) (hB : Sec4BInputs) :
    FritzII.Harris1981Bound :=
  harris1981_bound_reduced18 h41 h41c h411 ctx11_of_tm lemma4_12 h413 (ctx13_exists_of_K hK)
      (lemma418_caseA_of_sylowV hV) hI hB

theorem harris1981_bound_reduced13C (h41 : Lemma4_1Stmt) (h41c : CtxOfLemma4_1Stmt)
    (h411 : Lemma4_11Stmt) (h413 : Lemma4_13Stmt) (hK : Ctx13KStmt)
    (hFu : Lemma418CaseAFuStmt) (hI : Sec4Inputs) (hB : Sec4BInputs) :
    FritzII.Harris1981Bound :=
  harris1981_bound_reduced13B h41 h41c h411 h413 hK (lemma418_sylowV_of_Fu hFu) hI hB

end CFSG.OddStandard.SmallF3.HarrisU33
