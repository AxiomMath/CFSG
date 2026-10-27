module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredF4Aux6
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredF4Aux2
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredF4Aux3
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredF4Aux5

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


theorem emb_add {K L : Type} [Field K] [Field L] [Algebra K L] (u v : (Fin Tag.F4.rank → ℤ) → K) :
    emb (L := L) (u + v) = emb u + emb v := by
  funext β
  simp [emb]

theorem emb_smul {K L : Type} [Field K] [Field L] [Algebra K L] (c : K)
    (v : (Fin Tag.F4.rank → ℤ) → K) :
    emb (L := L) (c • v) = algebraMap K L c • emb v := by
  funext β
  simp [emb]

theorem emb_zero {K L : Type} [Field K] [Field L] [Algebra K L] :
    emb (L := L) (0 : (Fin Tag.F4.rank → ℤ) → K) = 0 := by
  funext β
  simp [emb]

theorem emb_onDeg1 {K L : Type} [Field K] [Field L] [Algebra K L] {v : (Fin Tag.F4.rank → ℤ) → K}
    (hv : OnDeg1 v) : OnDeg1 (emb (L := L) v) := by
  intro β hβ
  simp [emb, hv β hβ]

variable {K : Type} [Field K] [Finite K]

structure Ctx (D : LangLevi Tag.F4 K wF) (W : Submodule K ((Fin Tag.F4.rank → ℤ) → K)) where
  Φ : ((Fin Tag.F4.rank → ℤ) → D.L) →ₗ[D.L] ((Fin Tag.F4.rank → ℤ) → D.L)
  hΦ : ∀ q ∈ Qθ Tag.F4 D.L, D.g⁻¹ * q * D.g ∈ Qθ Tag.F4 D.L ∧
    heisCoord Tag.F4 D.L (D.g⁻¹ * q * D.g) = Φ (heisCoord Tag.F4 D.L q)
  hWV : W ≤ VM (D.frame TwClass.f4Six.S₁ ⊔ D.frame TwClass.f4Six.S₂)
  hst : ∀ l ∈ (D.frame TwClass.f4Six.S₁ ⊔ D.frame TwClass.f4Six.S₂) ⊓ Lθ Tag.F4 K,
    ∀ q ∈ Qθ Tag.F4 K, heisCoord Tag.F4 K q ∈ W → heisCoord Tag.F4 K (l * q * l⁻¹) ∈ W

variable {D : LangLevi Tag.F4 K wF} {W : Submodule K ((Fin Tag.F4.rank → ℤ) → K)}

@[expose] def WbOf (C : Ctx D W) : Submodule D.L ((Fin Tag.F4.rank → ℤ) → D.L) :=
  (Submodule.span D.L (emb '' (W : Set ((Fin Tag.F4.rank → ℤ) → K)))).map C.Φ

@[expose] def WbGen (C : Ctx D W) : Set ((Fin Tag.F4.rank → ℤ) → D.L) :=
  {v | ∃ w ∈ W, v = C.Φ (emb w)}

theorem WbOf_eq_span (C : Ctx D W) : WbOf C = Submodule.span D.L (WbGen C) := by
  unfold WbOf
  rw [Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_image, SetLike.mem_coe, WbGen, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨emb w, ⟨w, hw, rfl⟩, rfl⟩

theorem conj_coord (C : Ctx D W) {q : ModGL Tag.F4 K} (hq : q ∈ Qθ Tag.F4 K) :
    D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g ∈ Qθ Tag.F4 D.L ∧
      heisCoord Tag.F4 D.L (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g) =
        C.Φ (emb (heisCoord Tag.F4 K q)) := by
  obtain ⟨h1, h2⟩ := coord_baseChange (algebraMap K D.L) hq
  obtain ⟨h3, h4⟩ := C.hΦ _ h1
  exact ⟨h3, by rw [h4, h2]; rfl⟩

theorem gen_data (C : Ctx D W) {w : (Fin Tag.F4.rank → ℤ) → K} (hw : w ∈ W) :
    ∃ q : ModGL Tag.F4 K, q ∈ Qθ Tag.F4 K ∧ heisCoord Tag.F4 K q = w := by
  exact (heisCoord_spec Tag.F4 K).surj w (VM_onDeg1 _ w (C.hWV hw))

theorem Wb_stab_of_rational (C : Ctx D W)
    {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ}
    (hact : ∀ γ ∈ rootFinset Tag.F4, γ 0 = 0 → ∀ t : D.L, ∀ q ∈ Qθ Tag.F4 D.L,
      heisCoord Tag.F4 D.L (pinnedX Tag.F4 D.L γ t * q * (pinnedX Tag.F4 D.L γ t)⁻¹) =
        actFun a1 a2 γ t (heisCoord Tag.F4 D.L q))
    {γ₁ γ₂ γ₃ : Fin Tag.F4.rank → ℤ} (h₁ : γ₁ ∈ f4ShortList) (h₂ : γ₂ ∈ f4ShortList)
    (h₃ : γ₃ ∈ f4ShortList) (t₁ t₂ t₃ : D.L) (x₀ : ModGL Tag.F4 K)
    (hx₀X : x₀ ∈ D.frame TwClass.f4Six.S₁ ⊔ D.frame TwClass.f4Six.S₂) (hx₀L : x₀ ∈ Lθ Tag.F4 K)
    (hb : baseChangeGL (algebraMap K D.L) x₀ = D.g * (pinnedX Tag.F4 D.L γ₁ t₁ *
      pinnedX Tag.F4 D.L γ₂ t₂ * pinnedX Tag.F4 D.L γ₃ t₃) * D.g⁻¹) :
    ∀ v ∈ WbOf C, actFun a1 a2 γ₁ t₁ (actFun a1 a2 γ₂ t₂ (actFun a1 a2 γ₃ t₃ v)) ∈ WbOf C := by
  rw [WbOf_eq_span]
  refine stab_span hact (WbGen C) h₁ h₂ h₃ t₁ t₂ t₃ ?_
  rintro v ⟨w, hw, rfl⟩
  obtain ⟨q, hq, hqw⟩ := gen_data C hw
  obtain ⟨hqb, hqbc⟩ := conj_coord C hq
  refine ⟨D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g, hqb, by rw [hqbc, hqw], ?_⟩
  have hq₁ : x₀ * q * x₀⁻¹ ∈ Qθ Tag.F4 K := Lθ_conj_mem_Qθ hx₀L hq
  obtain ⟨-, hq₁c⟩ := conj_coord C hq₁
  have hw₁ : heisCoord Tag.F4 K (x₀ * q * x₀⁻¹) ∈ W :=
    C.hst x₀ ⟨hx₀X, hx₀L⟩ q hq (hqw ▸ hw)
  have e : pinnedX Tag.F4 D.L γ₁ t₁ * pinnedX Tag.F4 D.L γ₂ t₂ * pinnedX Tag.F4 D.L γ₃ t₃ *
      (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g) *
      (pinnedX Tag.F4 D.L γ₁ t₁ * pinnedX Tag.F4 D.L γ₂ t₂ * pinnedX Tag.F4 D.L γ₃ t₃)⁻¹ =
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x₀ * q * x₀⁻¹) * D.g := by
    rw [map_mul, map_mul, map_inv, hb]
    group
  rw [e, hq₁c]
  exact ⟨_, hw₁, rfl⟩

theorem coord_sRoots_zero (hK : 3 ≤ Nat.card K) (hodd : ringChar K ≠ 2) (D : LangLevi Tag.F4 K wF)
    {q : ModGL Tag.F4 K} (hq : q ∈ Qθ Tag.F4 K)
    (hqc : ∀ r ∈ Rθ (D.frame TwClass.f4Six.S₁ ⊔ D.frame TwClass.f4Six.S₂), r * q = q * r) :
    heisCoord Tag.F4 D.L (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g) alpha1 = 0 ∧
    heisCoord Tag.F4 D.L (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g) root1342 = 0 := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨N, hN⟩ := pair_comm_s1
  obtain ⟨e, A, he, hA, hfix⟩ := exists_sigmaFixed_pair D isRoot_alpha1 isRoot_root1342
    (isRoot_highRoot Tag.F4) wF_alpha1 wF_root1342 wF_theta N (fun a b => hN D.L a b) hK hodd
  obtain ⟨a₁, ha₁, a₂, ha₂, hdet⟩ := exists_two_indep (L := D.L) (Nat.card K) (by omega) e he A
    (by omega)
  have hqh : baseChangeGL (algebraMap K D.L) q ∈ Qθ Tag.F4 D.L := (coord_baseChange _ hq).1
  have hqb : D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g ∈ Qθ Tag.F4 D.L := by
    simpa using Lθ_conj_mem_Qθ (inv_mem D.g_mem) hqh
  have key : ∀ a ∈ A, ∃ c : D.L,
      pinnedX Tag.F4 D.L (highRoot Tag.F4) c * pinnedX Tag.F4 D.L alpha1 a *
        pinnedX Tag.F4 D.L root1342 (e * a ^ Nat.card K) *
        (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g) =
      (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g) *
        (pinnedX Tag.F4 D.L (highRoot Tag.F4) c * pinnedX Tag.F4 D.L alpha1 a *
          pinnedX Tag.F4 D.L root1342 (e * a ^ Nat.card K)) := by
    intro a ha
    obtain ⟨c, hc⟩ := hfix a ha
    refine ⟨c, ?_⟩
    set x := pinnedX Tag.F4 D.L (highRoot Tag.F4) c * pinnedX Tag.F4 D.L alpha1 a *
      pinnedX Tag.F4 D.L root1342 (e * a ^ Nat.card K) with hx
    have hxQ : x ∈ Qθ Tag.F4 D.L := by
      refine mul_mem (mul_mem ?_ ?_) ?_
      · exact pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff _).2 (Or.inr rfl)) _
      · exact pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff _).2 (Or.inl alpha1_deg1)) _
      · exact pinnedX_mem_rootSpan ((CoordAux.mem_radRoots_iff _).2 (Or.inl root1342_deg1)) _
    have hxS : x ∈ rootSpan Tag.F4 D.L TwClass.f4Six.S₁ := by
      refine mul_mem (mul_mem ?_ ?_) ?_
      · exact pinnedX_mem_rootSpan (TwBasicAux.highRoot_mem_S₁ TwClass.f4Six) _
      · exact pinnedX_mem_rootSpan (mem_S₁ alpha1_mem) _
      · exact pinnedX_mem_rootSpan (mem_S₁ root1342_mem) _
    obtain ⟨r, hrQ, hrb⟩ := sigma_fixed_rational_Qθ D hxQ hc
    have hrX : r ∈ D.frame TwClass.f4Six.S₁ :=
      mem_frame_of_rational D hxS (Qθ_le_adjointGroup Tag.F4 K hrQ) hrb
    have hcomm := hqc r ⟨Subgroup.mem_sup_left hrX, hrQ⟩
    have hcomm' := congrArg (baseChangeGL (algebraMap K D.L)) hcomm
    rw [map_mul, map_mul, hrb] at hcomm'
    calc x * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g)
        = D.g⁻¹ * (D.g * x * D.g⁻¹ * baseChangeGL (algebraMap K D.L) q) * D.g := by group
      _ = D.g⁻¹ * (baseChangeGL (algebraMap K D.L) q * (D.g * x * D.g⁻¹)) * D.g := by rw [hcomm']
      _ = (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g) * x := by group
  obtain ⟨c₁, hc₁⟩ := key a₁ ha₁
  obtain ⟨c₂, hc₂⟩ := key a₂ ha₂
  exact coord_zero_of_commutes hqb hdet hc₁ hc₂

theorem VM_support (C : Ctx D W) (hK : 3 ≤ Nat.card K) (hodd : ringChar K ≠ 2) :
    ∀ w ∈ VM (D.frame TwClass.f4Six.S₁ ⊔ D.frame TwClass.f4Six.S₂),
      ∀ ν, ν ∉ mRoots → C.Φ (emb w) ν = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨q, hq, rfl⟩ := hw
    intro ν hν
    obtain ⟨hqQ, hqc⟩ := hq
    have hqc' : ∀ r ∈ Rθ (D.frame TwClass.f4Six.S₁ ⊔ D.frame TwClass.f4Six.S₂), r * q = q * r :=
      fun r hr => Subgroup.mem_centralizer_iff.1 hqc r hr
    obtain ⟨hb, hbc⟩ := conj_coord C hqQ
    rw [← hbc]
    by_cases hD : ν ∈ Deg1 Tag.F4
    · rcases deg_one_roots ν (mem_rootFinset.2 hD.1) hD.2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hν
      · obtain ⟨h0, h1⟩ := coord_sRoots_zero hK hodd D hqQ hqc'
        rcases List.mem_cons.1 h with h | h
        · rw [h]
          exact h0
        · rw [List.mem_singleton.1 h]
          exact h1
    · exact (heisCoord_spec Tag.F4 D.L).support _ hb ν hD
  | zero => intro ν _; simp [emb_zero]
  | add x y _ _ hx hy =>
    intro ν hν
    rw [emb_add, map_add, Pi.add_apply, hx ν hν, hy ν hν, add_zero]
  | smul c x _ hx =>
    intro ν hν
    rw [emb_smul, map_smul, Pi.smul_apply, hx ν hν, smul_zero]

theorem Wb_support (C : Ctx D W) (hK : 3 ≤ Nat.card K) (hodd : ringChar K ≠ 2) :
    ∀ v ∈ WbOf C, ∀ ν, ν ∉ mRoots → v ν = 0 := by
  rw [WbOf_eq_span]
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    exact VM_support C hK hodd w (C.hWV hw)
  | zero => intro ν _; rfl
  | add x y _ _ hx hy => intro ν hν; rw [Pi.add_apply, hx ν hν, hy ν hν, add_zero]
  | smul c x _ hx => intro ν hν; rw [Pi.smul_apply, hx ν hν, smul_zero]

open Classical in
theorem Wb_stab_S (C : Ctx D W) {ε : (Fin Tag.F4.rank → ℤ) → D.L}
    (hε : ∀ α, IsRoot Tag.F4 α → ε α * ε α = 1)
    (hn : ∀ q ∈ Qθ Tag.F4 D.L,
      (canonicalRep (coxeterSystem Tag.F4) D.L wF)⁻¹ * q *
        canonicalRep (coxeterSystem Tag.F4) D.L wF ∈ Qθ Tag.F4 D.L ∧
      ∀ α, heisCoord Tag.F4 D.L ((canonicalRep (coxeterSystem Tag.F4) D.L wF)⁻¹ * q *
          canonicalRep (coxeterSystem Tag.F4) D.L wF) α =
        if α ∈ Deg1 Tag.F4 then ε α * heisCoord Tag.F4 D.L q (wF • α) else 0) :
    ∀ v ∈ WbOf C, Sfun D.Fr ε v ∈ WbOf C := by
  rw [WbOf_eq_span]
  refine stab_span_semilinear D.Fr (Sfun D.Fr ε) (Sfun_add D.Fr ε) (Sfun_smul D.Fr ε) (WbGen C) ?_
  rintro v ⟨w, hw, rfl⟩
  obtain ⟨q, hq, hqw⟩ := gen_data C hw
  obtain ⟨hqb, hqbc⟩ := conj_coord C hq
  have hF : Units.map (entrywiseHom D.Fr) (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g) =
      (canonicalRep (coxeterSystem Tag.F4) D.L wF)⁻¹ *
        (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g) *
        canonicalRep (coxeterSystem Tag.F4) D.L wF := by
    rw [map_mul, map_mul, map_inv, D.lang,
      units_map_entrywiseHom_baseChangeGL_algebraMap D.Fr D.hFr q]
    group
  have hfix := Sfun_fixed D.Fr hε hqb (hn _ hqb).2 hF
  rw [hqbc, hqw] at hfix
  rw [hfix]
  exact Submodule.subset_span ⟨w, hw, rfl⟩

theorem stab_single_root (C : Ctx D W) (hK : 3 ≤ Nat.card K)
    {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ}
    (hact : ∀ γ ∈ rootFinset Tag.F4, γ 0 = 0 → ∀ t : D.L, ∀ q ∈ Qθ Tag.F4 D.L,
      heisCoord Tag.F4 D.L (pinnedX Tag.F4 D.L γ t * q * (pinnedX Tag.F4 D.L γ t)⁻¹) =
        actFun a1 a2 γ t (heisCoord Tag.F4 D.L q))
    {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ f4ShortList) (hwγ : wF • γ = γ) :
    ∀ t : D.L, ∀ v ∈ WbOf C, actFun a1 a2 γ t v ∈ WbOf C := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨hγr, -⟩ := f4ShortList_deg0 γ hγ
  obtain ⟨T, hT, hfix⟩ := exists_sigmaFixed_single D (mem_rootFinset.1 hγr) hwγ hK
  refine algebraize_single (WbOf C) γ T hT (fun t ht v hv => ?_)
  have hxS : pinnedX Tag.F4 D.L γ t ∈ rootSpan Tag.F4 D.L TwClass.f4Six.S₂ :=
    pinnedX_mem_rootSpan (mem_S₂ hγ) t
  have hxA : pinnedX Tag.F4 D.L γ t ∈ adjointGroup Tag.F4 D.L :=
    rootSubgroup_le_adjointGroup (τ := Tag.F4) γ (mem_rootSubgroup.2 ⟨t, rfl⟩)
  obtain ⟨x₀, hx₀, hb⟩ := sigma_fixed_rational D hxA (hfix t ht)
  have hx₀F : x₀ ∈ D.frame TwClass.f4Six.S₂ := mem_frame_of_rational D hxS hx₀ hb
  have h := Wb_stab_of_rational C hact hγ hγ hγ t 0 0 x₀ (Subgroup.mem_sup_right hx₀F)
    (frame_S₂_le_Lθ D hx₀F) (by rw [hb, pinnedX_zero, mul_one, mul_one]) v hv
  rwa [actFun_zero_param, actFun_zero_param] at h

theorem stab_pair (C : Ctx D W) (hK : 3 ≤ Nat.card K) (hodd : ringChar K ≠ 2)
    {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ} (h1 : Adm1 a1) (h2 : Adm2 a2)
    (hact : ∀ γ ∈ rootFinset Tag.F4, γ 0 = 0 → ∀ t : D.L, ∀ q ∈ Qθ Tag.F4 D.L,
      heisCoord Tag.F4 D.L (pinnedX Tag.F4 D.L γ t * q * (pinnedX Tag.F4 D.L γ t)⁻¹) =
        actFun a1 a2 γ t (heisCoord Tag.F4 D.L q))
    (hsupp : ∀ v ∈ WbOf C, ∀ ν, ν ∉ mRoots → v ν = 0)
    {δ₁ δ₂ γ : Fin Tag.F4.rank → ℤ} (hδ₁ : δ₁ ∈ f4ShortList) (hδ₂ : δ₂ ∈ f4ShortList)
    (hγ : γ ∈ f4ShortList) (hw₁ : wF • δ₁ = δ₂) (hw₂ : wF • δ₂ = δ₁) (hwγ : wF • γ = γ) (N : ℤ)
    (hcomm : ∀ a b : D.L, pinnedX Tag.F4 D.L δ₁ a * pinnedX Tag.F4 D.L δ₂ b *
        pinnedX Tag.F4 D.L δ₁ (-a) * pinnedX Tag.F4 D.L δ₂ (-b) =
      pinnedX Tag.F4 D.L γ ((N : D.L) * a * b))
    (hstabγ : ∀ t : D.L, ∀ v ∈ WbOf C, actFun a1 a2 γ t v ∈ WbOf C) :
    (∀ t : D.L, ∀ v ∈ WbOf C, actFun a1 a2 δ₁ t v ∈ WbOf C) ∧
      (∀ t : D.L, ∀ v ∈ WbOf C, actFun a1 a2 δ₂ t v ∈ WbOf C) := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨hδ₁r, -⟩ := f4ShortList_deg0 δ₁ hδ₁
  obtain ⟨hδ₂r, -⟩ := f4ShortList_deg0 δ₂ hδ₂
  obtain ⟨hγr, -⟩ := f4ShortList_deg0 γ hγ
  obtain ⟨e, A, he, hA, hfix⟩ := exists_sigmaFixed_pair D (mem_rootFinset.1 hδ₁r)
    (mem_rootFinset.1 hδ₂r) (mem_rootFinset.1 hγr) hw₁ hw₂ hwγ N hcomm hK hodd
  refine algebraize_pair (WbOf C) δ₁ δ₂ (Nat.card K) hK e he A hA (fun a ha v hv => ?_)
  obtain ⟨c, hc⟩ := hfix a ha
  have hxS : pinnedX Tag.F4 D.L γ c * pinnedX Tag.F4 D.L δ₁ a *
      pinnedX Tag.F4 D.L δ₂ (e * a ^ Nat.card K) ∈ rootSpan Tag.F4 D.L TwClass.f4Six.S₂ :=
    mul_mem (mul_mem (pinnedX_mem_rootSpan (mem_S₂ hγ) _) (pinnedX_mem_rootSpan (mem_S₂ hδ₁) _))
      (pinnedX_mem_rootSpan (mem_S₂ hδ₂) _)
  have hA' : ∀ (α : Fin Tag.F4.rank → ℤ) (t : D.L),
      pinnedX Tag.F4 D.L α t ∈ adjointGroup Tag.F4 D.L := fun α t =>
    rootSubgroup_le_adjointGroup (τ := Tag.F4) α (mem_rootSubgroup.2 ⟨t, rfl⟩)
  have hxA : pinnedX Tag.F4 D.L γ c * pinnedX Tag.F4 D.L δ₁ a *
      pinnedX Tag.F4 D.L δ₂ (e * a ^ Nat.card K) ∈ adjointGroup Tag.F4 D.L :=
    mul_mem (mul_mem (hA' _ _) (hA' _ _)) (hA' _ _)
  obtain ⟨x₀, hx₀, hb⟩ := sigma_fixed_rational D hxA hc
  have hx₀F : x₀ ∈ D.frame TwClass.f4Six.S₂ := mem_frame_of_rational D hxS hx₀ hb
  have hcomp := Wb_stab_of_rational C hact hγ hδ₁ hδ₂ c a (e * a ^ Nat.card K) x₀
    (Subgroup.mem_sup_right hx₀F) (frame_S₂_le_Lθ D hx₀F) hb v hv
  have hu : OnDeg1 (actFun a1 a2 δ₁ a (actFun a1 a2 δ₂ (e * a ^ Nat.card K) v)) := by
    intro β hβ
    have hβ' : β ∉ mRoots := fun hm =>
      hβ ⟨mem_rootFinset.1 (mRoots_data β hm).1, (mRoots_data β hm).2.1⟩
    exact actFun_supp D.L h1 h2 hδ₁ a (fun ν hν =>
      actFun_supp D.L h1 h2 hδ₂ (e * a ^ Nat.card K) (hsupp v hv) ν hν) β hβ'
  have h3 := hstabγ (-c) _ hcomp
  rw [actFun_param_add hact hγ (-c) c hu, neg_add_cancel, actFun_zero_param] at h3
  exact h3

theorem Wb_stab_all (C : Ctx D W) (hK : 3 ≤ Nat.card K) (hodd : ringChar K ≠ 2)
    {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ} (h1 : Adm1 a1) (h2 : Adm2 a2)
    (hact : ∀ γ ∈ rootFinset Tag.F4, γ 0 = 0 → ∀ t : D.L, ∀ q ∈ Qθ Tag.F4 D.L,
      heisCoord Tag.F4 D.L (pinnedX Tag.F4 D.L γ t * q * (pinnedX Tag.F4 D.L γ t)⁻¹) =
        actFun a1 a2 γ t (heisCoord Tag.F4 D.L q))
    (hsupp : ∀ v ∈ WbOf C, ∀ ν, ν ∉ mRoots → v ν = 0) :
    ∀ γ ∈ f4ShortList, ∀ t : D.L, ∀ v ∈ WbOf C, actFun a1 a2 γ t v ∈ WbOf C := by
  have hs34 := stab_single_root C hK hact r34_mem wF_r34
  have hsn34 := stab_single_root C hK hact neg_r34_mem wF_neg_r34
  obtain ⟨N, hN⟩ := pair_comm_s2
  obtain ⟨N', hN'⟩ := pair_comm_s2_neg
  obtain ⟨hp3, hp4⟩ := stab_pair C hK hodd h1 h2 hact hsupp r3_mem r4_mem r34_mem wF_r3 wF_r4
    wF_r34 N (fun a b => hN D.L a b) hs34
  obtain ⟨hn3, hn4⟩ := stab_pair C hK hodd h1 h2 hact hsupp neg_r3_mem neg_r4_mem neg_r34_mem
    wF_neg_r3 wF_neg_r4 wF_neg_r34 N' (fun a b => hN' D.L a b) hsn34
  intro γ hγ
  rcases f4ShortList_cases γ hγ with rfl | rfl | rfl | rfl | h | h
  · exact hp3
  · exact hn3
  · exact hp4
  · exact hn4
  · rw [h, reflect_two_single_three]; exact hs34
  · rw [h, reflect_two_single_three]; exact hsn34

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredF4Aux
