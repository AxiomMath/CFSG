module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.DegZero
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE8TwelveAux1b
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE8TwelveAux2
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE8TwelveAux3
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

set_option linter.unusedSectionVars false


section Transport

variable {K : Type} [Field K] [Finite K] {w : WeylGroup Tag.E8} (D : LangLevi Tag.E8 K w)

@[expose] def iotaV : (V8 → K) →ₗ[K] (V8 → D.L) where
  toFun v ν := algebraMap K D.L (v ν)
  map_add' v v' := by
    funext ν
    simp
  map_smul' c v := by
    funext ν
    simp [Algebra.smul_def]

theorem iotaV_apply (v : V8 → K) (ν : V8) : iotaV D v ν = algebraMap K D.L (v ν) := rfl

theorem iotaV_injective : Function.Injective (iotaV D) := by
  intro v v' h
  funext ν
  exact (algebraMap K D.L).injective (congrFun h ν)

structure LinData where
  Gi : (V8 → D.L) →ₗ[D.L] (V8 → D.L)
  G : (V8 → D.L) →ₗ[D.L] (V8 → D.L)
  N : (V8 → D.L) →ₗ[D.L] (V8 → D.L)
  N' : (V8 → D.L) →ₗ[D.L] (V8 → D.L)
  Gi_supp : ∀ v ν, ν ∉ Deg1 Tag.E8 → Gi v ν = 0
  Gi_spec : ∀ q ∈ Qθ Tag.E8 D.L, D.g⁻¹ * q * D.g ∈ Qθ Tag.E8 D.L ∧
    heisCoord Tag.E8 D.L (D.g⁻¹ * q * D.g) = Gi (heisCoord Tag.E8 D.L q)
  G_spec : ∀ q ∈ Qθ Tag.E8 D.L, D.g * q * D.g⁻¹ ∈ Qθ Tag.E8 D.L ∧
    heisCoord Tag.E8 D.L (D.g * q * D.g⁻¹) = G (heisCoord Tag.E8 D.L q)
  N_spec : ∀ q ∈ Qθ Tag.E8 D.L, nW D * q * (nW D)⁻¹ ∈ Qθ Tag.E8 D.L ∧
    heisCoord Tag.E8 D.L (nW D * q * (nW D)⁻¹) = N (heisCoord Tag.E8 D.L q)
  N'_spec : ∀ q ∈ Qθ Tag.E8 D.L, (nW D)⁻¹ * q * nW D ∈ Qθ Tag.E8 D.L ∧
    heisCoord Tag.E8 D.L ((nW D)⁻¹ * q * nW D) = N' (heisCoord Tag.E8 D.L q)

theorem nW_mem_Lθ (hw : w • highRoot Tag.E8 = highRoot Tag.E8) : nW D ∈ Lθ Tag.E8 D.L :=
  canonicalRep_mem_parabolicLevi (mem_parabolicWeylGroup_of_smul_highRoot Tag.E8 hw)

theorem exists_linData (hw : w • highRoot Tag.E8 = highRoot Tag.E8) : Nonempty (LinData D) := by
  obtain ⟨Gi, hGiS, hGi⟩ := exists_heisAct D.L (inv_mem D.g_mem)
  obtain ⟨G, -, hG⟩ := exists_heisAct D.L D.g_mem
  obtain ⟨N, -, hN⟩ := exists_heisAct D.L (nW_mem_Lθ D hw)
  obtain ⟨N', -, hN'⟩ := exists_heisAct D.L (inv_mem (nW_mem_Lθ D hw))
  refine ⟨⟨Gi, G, N, N', hGiS, ?_, hG, hN, ?_⟩⟩
  · simpa only [inv_inv] using hGi
  · simpa only [inv_inv] using hN'

variable {D}

theorem LinData.G_Gi (T : LinData D) {v : V8 → D.L} (hv : ∀ ν, ν ∉ Deg1 Tag.E8 → v ν = 0) :
    T.G (T.Gi v) = v := by
  refine heisAct_inv_left (l := D.g⁻¹) (A := T.Gi) (A' := T.G) ?_ ?_ hv
  · intro q hq
    simpa only [inv_inv] using T.Gi_spec q hq
  · intro q hq
    simpa only [inv_inv] using T.G_spec q hq

theorem LinData.N_N' (T : LinData D) {v : V8 → D.L} (hv : ∀ ν, ν ∉ Deg1 Tag.E8 → v ν = 0) :
    T.N (T.N' v) = v := by
  refine heisAct_inv_left (l := (nW D)⁻¹) (A := T.N') (A' := T.N) ?_ ?_ hv
  · intro q hq
    simpa only [inv_inv] using T.N'_spec q hq
  · intro q hq
    simpa only [inv_inv] using T.N_spec q hq

theorem coord_bc {q : ModGL Tag.E8 K} (hq : q ∈ Qθ Tag.E8 K) :
    baseChangeGL (algebraMap K D.L) q ∈ Qθ Tag.E8 D.L ∧
      heisCoord Tag.E8 D.L (baseChangeGL (algebraMap K D.L) q) = iotaV D (heisCoord Tag.E8 K q) :=
  heisCoord_baseChange (algebraMap K D.L) hq

theorem transport_coord (T : LinData D) {q : ModGL Tag.E8 K} (hq : q ∈ Qθ Tag.E8 K) :
    D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g ∈ Qθ Tag.E8 D.L ∧
      heisCoord Tag.E8 D.L (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g) =
        T.Gi (iotaV D (heisCoord Tag.E8 K q)) := by
  obtain ⟨h1, h2⟩ := coord_bc (D := D) hq
  obtain ⟨h3, h4⟩ := T.Gi_spec _ h1
  exact ⟨h3, by rw [h4, h2]⟩

theorem frobGL_eq_baseChange (x : ModGL Tag.E8 D.L) : frobGL D x = baseChangeGL D.Fr x := rfl

theorem sigma_fixed (T : LinData D) {q : ModGL Tag.E8 K} (hq : q ∈ Qθ Tag.E8 K) :
    T.N (fun ν => D.Fr (T.Gi (iotaV D (heisCoord Tag.E8 K q)) ν)) =
      T.Gi (iotaV D (heisCoord Tag.E8 K q)) := by
  obtain ⟨h1, h2⟩ := transport_coord T hq
  set q' := D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g with hq'
  have hF : frobGL D q' = (nW D)⁻¹ * q' * nW D := frobGL_conj_g_inv_baseChange D q
  obtain ⟨h3, h4⟩ := heisCoord_baseChange D.Fr h1
  obtain ⟨h5, h6⟩ := T.N'_spec q' h1
  rw [← frobGL_eq_baseChange, hF] at h4
  have h7 : (fun β => D.Fr (heisCoord Tag.E8 D.L q' β)) = T.N' (heisCoord Tag.E8 D.L q') := by
    rw [← h4, ← h6]
  have hsupp : ∀ ν, ν ∉ Deg1 Tag.E8 → heisCoord Tag.E8 D.L q' ν = 0 := fun ν hν =>
    (heisCoord_spec Tag.E8 D.L).support q' h1 ν hν
  rw [← h2]
  show T.N (fun β => D.Fr (heisCoord Tag.E8 D.L q' β)) = _
  rw [h7]
  exact T.N_N' hsupp

@[expose] def genSet (T : LinData D) (W : Submodule K (V8 → K)) : Set (V8 → D.L) :=
  (fun v => T.Gi (iotaV D v)) '' (W : Set (V8 → K))

@[expose] def Zsp (T : LinData D) (W : Submodule K (V8 → K)) : Submodule D.L (V8 → D.L) :=
  Submodule.span D.L (genSet T W)

theorem mem_Zsp_of_mem (T : LinData D) {W : Submodule K (V8 → K)} {v : V8 → K} (hv : v ∈ W) :
    T.Gi (iotaV D v) ∈ Zsp T W :=
  Submodule.subset_span ⟨v, hv, rfl⟩

theorem Zsp_sigma (T : LinData D) {W : Submodule K (V8 → K)}
    (hW : ∀ v ∈ W, ∀ ν, ν ∉ Deg1 Tag.E8 → v ν = 0) :
    ∀ z ∈ Zsp T W, T.N (fun ν => D.Fr (z ν)) ∈ Zsp T W := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨q, hq, hqv⟩ := (heisCoord_spec Tag.E8 K).surj v (hW v hv)
    rw [← hqv, sigma_fixed T hq, hqv]
    exact mem_Zsp_of_mem T hv
  | zero =>
    have : (fun ν => D.Fr ((0 : V8 → D.L) ν)) = 0 := by
      funext ν
      simp
    rw [this, map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun ν => D.Fr ((x + y) ν)) = (fun ν => D.Fr (x ν)) + (fun ν => D.Fr (y ν)) := by
      funext ν
      simp
    rw [this, map_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    have : (fun ν => D.Fr ((c • x) ν)) = D.Fr c • (fun ν => D.Fr (x ν)) := by
      funext ν
      simp
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ hx

theorem mem_Deg1_iff_deg1Roots (β : V8) : β ∈ Deg1 Tag.E8 ↔ β ∈ deg1Roots := by
  rw [mem_deg1Roots]
  rfl

theorem Zsp_support (T : LinData D) {W : Submodule K (V8 → K)}
    (hW : ∀ v ∈ W, ∀ β ∈ sig1, T.Gi (iotaV D v) β = 0) :
    ∀ z ∈ Zsp T W, ∀ ν, ν ∉ dl → z ν = 0 := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    intro ν hν
    by_cases h1 : ν ∈ sig1
    · exact hW v hv ν h1
    · apply T.Gi_supp
      intro hD
      exact hν (Finset.mem_sdiff.2 ⟨(mem_Deg1_iff_deg1Roots ν).1 hD, h1⟩)
  | zero => intro ν _; rfl
  | add x y _ _ hx hy => intro ν hν; simp [hx ν hν, hy ν hν]
  | smul c x _ hx => intro ν hν; simp [hx ν hν]

theorem Zsp_stable_of_rational (T : LinData D) {W : Submodule K (V8 → K)}
    (hW : ∀ v ∈ W, ∀ ν, ν ∉ Deg1 Tag.E8 → v ν = 0) {P : Subgroup (ModGL Tag.E8 K)}
    (hstab : ∀ l ∈ P, ∀ q ∈ Qθ Tag.E8 K, heisCoord Tag.E8 K q ∈ W →
      heisCoord Tag.E8 K (l * q * l⁻¹) ∈ W)
    {l₀ : ModGL Tag.E8 K} (hl₀P : l₀ ∈ P) (hl₀L : l₀ ∈ Lθ Tag.E8 K)
    {u : ModGL Tag.E8 D.L} (hl₀u : baseChangeGL (algebraMap K D.L) l₀ = D.g * u * D.g⁻¹)
    (Act : (V8 → D.L) →ₗ[D.L] (V8 → D.L))
    (hAct : ∀ q ∈ Qθ Tag.E8 D.L, u * q * u⁻¹ ∈ Qθ Tag.E8 D.L ∧
      heisCoord Tag.E8 D.L (u * q * u⁻¹) = Act (heisCoord Tag.E8 D.L q)) :
    ∀ z ∈ Zsp T W, Act z ∈ Zsp T W := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨q, hq, hqv⟩ := (heisCoord_spec Tag.E8 K).surj v (hW v hv)
    have hqn : l₀ * q * l₀⁻¹ ∈ Qθ Tag.E8 K :=
      (Subgroup.mem_normalizer_iff.1
        (Pθ_le_normalizer_Qθ Tag.E8 K (Lθ_le_Pθ Tag.E8 K hl₀L)) q).1 hq
    have hv2 : heisCoord Tag.E8 K (l₀ * q * l₀⁻¹) ∈ W :=
      hstab l₀ hl₀P q hq (by rw [hqv]; exact hv)
    obtain ⟨hA1, hA2⟩ := transport_coord T hq
    obtain ⟨hB1, hB2⟩ := transport_coord T hqn
    have hconj : D.g⁻¹ * baseChangeGL (algebraMap K D.L) (l₀ * q * l₀⁻¹) * D.g =
        u * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) q * D.g) * u⁻¹ := by
      simp only [map_mul, map_inv, hl₀u]
      group
    obtain ⟨hC1, hC2⟩ := hAct _ hA1
    have key : Act (T.Gi (iotaV D v)) =
        T.Gi (iotaV D (heisCoord Tag.E8 K (l₀ * q * l₀⁻¹))) := by
      rw [← hqv, ← hA2, ← hC2, ← hconj, hB2]
    rw [key]
    exact mem_Zsp_of_mem T hv2
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem frobGL_pinnedX (γ : V8) (c : D.L) :
    frobGL D (pinnedX Tag.E8 D.L γ c) = pinnedX Tag.E8 D.L γ (D.Fr c) := by
  rw [frobGL_eq_baseChange, baseChangeGL_pinnedX]

theorem sign_pow {ε : D.L} (h : ε * ε = 1) : ε ^ Nat.card K = ε := by
  rcases mul_self_eq_one_iff.1 h with rfl | rfl
  · simp
  · rw [← D.hFr, map_neg, map_one]

theorem Fr_sign {ε : D.L} (h : ε * ε = 1) : D.Fr ε = ε := by
  rw [D.hFr, sign_pow h]

theorem exists_sign {γ : V8} (hγ : IsRoot Tag.E8 γ) :
    ∃ ε : D.L, ε * ε = 1 ∧ ∀ c : D.L,
      nW D * pinnedX Tag.E8 D.L γ c * (nW D)⁻¹ = pinnedX Tag.E8 D.L (w • γ) (ε * c) :=
  exists_canonicalRep_mul_pinnedX_mul_inv D.L w hγ

theorem single_sigma {γ : V8} (hγ : IsRoot Tag.E8 γ) (hw : w • γ = γ) :
    ∃ ε : D.L, ε * ε = 1 ∧ ∀ x : D.L, x ^ Nat.card K = ε * x →
      nW D * frobGL D (pinnedX Tag.E8 D.L γ x) * (nW D)⁻¹ = pinnedX Tag.E8 D.L γ x := by
  obtain ⟨ε, hε, hn⟩ := exists_sign (D := D) hγ
  refine ⟨ε, hε, fun x hx => ?_⟩
  rw [frobGL_pinnedX, hn, hw, D.hFr, hx, ← mul_assoc, hε, one_mul]

theorem conj_mul3 {G : Type*} [Group G] (n a b c : G) :
    n * (a * b * c) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) * (n * c * n⁻¹) := by
  group

theorem triple_sigma {γ₀ γ₁ γ₂ : V8} (h₀ : IsRoot Tag.E8 γ₀) (h₁ : IsRoot Tag.E8 γ₁)
    (h₂ : IsRoot Tag.E8 γ₂) (hw₀ : w • γ₀ = γ₁) (hw₁ : w • γ₁ = γ₂) (hw₂ : w • γ₂ = γ₀)
    (hc₁ : ∀ c d : D.L, Commute (pinnedX Tag.E8 D.L γ₀ c) (pinnedX Tag.E8 D.L γ₁ d))
    (hc₂ : ∀ c d : D.L, Commute (pinnedX Tag.E8 D.L γ₀ c) (pinnedX Tag.E8 D.L γ₂ d)) :
    ∃ s : SignData D.L, s.s₁ * s.s₁ = 1 ∧ s.s₂ * s.s₂ = 1 ∧ s.ε * s.ε = 1 ∧
      ∀ x : D.L, x ^ (Nat.card K ^ 3) = s.ε * x →
        nW D * frobGL D (pinnedX Tag.E8 D.L γ₀ x *
            pinnedX Tag.E8 D.L γ₁ (s.s₁ * x ^ Nat.card K) *
            pinnedX Tag.E8 D.L γ₂ (s.s₂ * x ^ (Nat.card K ^ 2))) * (nW D)⁻¹ =
          pinnedX Tag.E8 D.L γ₀ x * pinnedX Tag.E8 D.L γ₁ (s.s₁ * x ^ Nat.card K) *
            pinnedX Tag.E8 D.L γ₂ (s.s₂ * x ^ (Nat.card K ^ 2)) := by
  obtain ⟨ε₀, h0, hn₀⟩ := exists_sign (D := D) h₀
  obtain ⟨ε₁, h1, hn₁⟩ := exists_sign (D := D) h₁
  obtain ⟨ε₂, h2, hn₂⟩ := exists_sign (D := D) h₂
  rw [hw₀] at hn₀
  rw [hw₁] at hn₁
  rw [hw₂] at hn₂
  have hε₀ : ε₀ ≠ 0 := left_ne_zero_of_mul_eq_one h0
  have hε₁ : ε₁ ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hε₂ : ε₂ ≠ 0 := left_ne_zero_of_mul_eq_one h2
  have hs₂ : (ε₁ * ε₀) * (ε₁ * ε₀) = 1 := by
    calc (ε₁ * ε₀) * (ε₁ * ε₀) = (ε₁ * ε₁) * (ε₀ * ε₀) := by ring
      _ = 1 := by rw [h1, h0, one_mul]
  have hs₃ : (ε₂ * ε₁ * ε₀) * (ε₂ * ε₁ * ε₀) = 1 := by
    calc (ε₂ * ε₁ * ε₀) * (ε₂ * ε₁ * ε₀) = (ε₂ * ε₂) * (ε₁ * ε₁) * (ε₀ * ε₀) := by ring
      _ = 1 := by rw [h2, h1, h0, one_mul, one_mul]
  refine ⟨⟨ε₀, ε₁ * ε₀, ε₂ * ε₁ * ε₀, hε₀, mul_ne_zero hε₁ hε₀,
    mul_ne_zero (mul_ne_zero hε₂ hε₁) hε₀⟩, h0, hs₂, hs₃, ?_⟩
  intro x hx
  simp only at hx ⊢
  have hFx : D.Fr x = x ^ Nat.card K := D.hFr x
  have hF0 : D.Fr ε₀ = ε₀ := Fr_sign h0
  have hF1 : D.Fr ε₁ = ε₁ := Fr_sign h1
  have hF10 : D.Fr (ε₁ * ε₀) = ε₁ * ε₀ := Fr_sign hs₂
  have e1 : D.Fr (ε₀ * x ^ Nat.card K) = ε₀ * x ^ (Nat.card K ^ 2) := by
    rw [map_mul, map_pow, hF0, hFx]
    ring
  have e2 : D.Fr (ε₁ * ε₀ * x ^ (Nat.card K ^ 2)) = ε₁ * ε₀ * x ^ (Nat.card K ^ 3) := by
    rw [map_mul, map_pow, hF10, hFx]
    ring
  rw [map_mul, map_mul, frobGL_pinnedX, frobGL_pinnedX, frobGL_pinnedX, conj_mul3, hn₀, hn₁, hn₂,
    e1, e2, hFx, hx]
  have a1 : ε₀ * x ^ Nat.card K = ε₀ * x ^ Nat.card K := rfl
  have a2 : ε₁ * (ε₀ * x ^ (Nat.card K ^ 2)) = ε₁ * ε₀ * x ^ (Nat.card K ^ 2) := by ring
  have a3 : ε₂ * (ε₁ * ε₀ * (ε₂ * ε₁ * ε₀ * x)) = x := by
    calc ε₂ * (ε₁ * ε₀ * (ε₂ * ε₁ * ε₀ * x)) = (ε₂ * ε₂) * (ε₁ * ε₁) * (ε₀ * ε₀) * x := by ring
      _ = x := by rw [h2, h1, h0]; ring
  rw [a2, a3]
  set A₀ := pinnedX Tag.E8 D.L γ₀ x
  set A₁ := pinnedX Tag.E8 D.L γ₁ (ε₀ * x ^ Nat.card K)
  set A₂ := pinnedX Tag.E8 D.L γ₂ (ε₁ * ε₀ * x ^ (Nat.card K ^ 2))
  have c1 : A₀ * A₁ = A₁ * A₀ := (hc₁ _ _).eq
  have c2 : A₀ * A₂ = A₂ * A₀ := (hc₂ _ _).eq
  calc A₁ * A₂ * A₀ = A₁ * (A₂ * A₀) := by rw [mul_assoc]
    _ = A₁ * (A₀ * A₂) := by rw [c2]
    _ = (A₁ * A₀) * A₂ := by rw [mul_assoc]
    _ = (A₀ * A₁) * A₂ := by rw [c1]

section Act

variable (D)

theorem conj_mem_Qθ_of_deg_zero {γ : V8} (hγ : γ ∈ rootFinset Tag.E8) (hd : γ 7 = 0) (t : D.L)
    {q : ModGL Tag.E8 D.L} (hq : q ∈ Qθ Tag.E8 D.L) :
    pinnedX Tag.E8 D.L γ t * q * (pinnedX Tag.E8 D.L γ t)⁻¹ ∈ Qθ Tag.E8 D.L :=
  (Subgroup.mem_normalizer_iff.1 (Pθ_le_normalizer_Qθ Tag.E8 D.L (Lθ_le_Pθ Tag.E8 D.L
    (pinnedX_mem_Lθ_of_deg_zero (mem_rootFinset.1 hγ) hd t))) q).1 hq

variable {D}

theorem act_triple {a : V8 → V8 → ℤ}
    (hact : ∀ γ ∈ rootFinset Tag.E8, γ 7 = 0 → ∀ t : D.L, ∀ q ∈ Qθ Tag.E8 D.L,
      heisCoord Tag.E8 D.L (pinnedX Tag.E8 D.L γ t * q * (pinnedX Tag.E8 D.L γ t)⁻¹) =
        actFun a γ t (heisCoord Tag.E8 D.L q))
    {γ₀ γ₁ γ₂ : V8} (hr₀ : γ₀ ∈ rootFinset Tag.E8) (hd₀ : γ₀ 7 = 0)
    (hr₁ : γ₁ ∈ rootFinset Tag.E8) (hd₁ : γ₁ 7 = 0)
    (hr₂ : γ₂ ∈ rootFinset Tag.E8) (hd₂ : γ₂ 7 = 0) (t₀ t₁ t₂ : D.L)
    {q : ModGL Tag.E8 D.L} (hq : q ∈ Qθ Tag.E8 D.L) :
    (pinnedX Tag.E8 D.L γ₀ t₀ * pinnedX Tag.E8 D.L γ₁ t₁ * pinnedX Tag.E8 D.L γ₂ t₂) * q *
        (pinnedX Tag.E8 D.L γ₀ t₀ * pinnedX Tag.E8 D.L γ₁ t₁ * pinnedX Tag.E8 D.L γ₂ t₂)⁻¹ ∈
        Qθ Tag.E8 D.L ∧
      heisCoord Tag.E8 D.L
        ((pinnedX Tag.E8 D.L γ₀ t₀ * pinnedX Tag.E8 D.L γ₁ t₁ * pinnedX Tag.E8 D.L γ₂ t₂) * q *
          (pinnedX Tag.E8 D.L γ₀ t₀ * pinnedX Tag.E8 D.L γ₁ t₁ * pinnedX Tag.E8 D.L γ₂ t₂)⁻¹) =
        actOp a γ₀ t₀ (actOp a γ₁ t₁ (actOp a γ₂ t₂ (heisCoord Tag.E8 D.L q))) := by
  have e : (pinnedX Tag.E8 D.L γ₀ t₀ * pinnedX Tag.E8 D.L γ₁ t₁ * pinnedX Tag.E8 D.L γ₂ t₂) * q *
        (pinnedX Tag.E8 D.L γ₀ t₀ * pinnedX Tag.E8 D.L γ₁ t₁ * pinnedX Tag.E8 D.L γ₂ t₂)⁻¹ =
      pinnedX Tag.E8 D.L γ₀ t₀ * (pinnedX Tag.E8 D.L γ₁ t₁ * (pinnedX Tag.E8 D.L γ₂ t₂ * q *
        (pinnedX Tag.E8 D.L γ₂ t₂)⁻¹) * (pinnedX Tag.E8 D.L γ₁ t₁)⁻¹) *
        (pinnedX Tag.E8 D.L γ₀ t₀)⁻¹ := by
    group
  have h2 := conj_mem_Qθ_of_deg_zero D hr₂ hd₂ t₂ hq
  have h1 := conj_mem_Qθ_of_deg_zero D hr₁ hd₁ t₁ h2
  have h0 := conj_mem_Qθ_of_deg_zero D hr₀ hd₀ t₀ h1
  rw [e]
  refine ⟨h0, ?_⟩
  rw [hact γ₀ hr₀ hd₀ t₀ _ h1, hact γ₁ hr₁ hd₁ t₁ _ h2, hact γ₂ hr₂ hd₂ t₂ _ hq]
  rfl

end Act

theorem pinnedX_mem_Lθ' {γ : V8} (hγ : γ ∈ rootFinset Tag.E8) (hd : γ 7 = 0) (t : D.L) :
    pinnedX Tag.E8 D.L γ t ∈ Lθ Tag.E8 D.L :=
  pinnedX_mem_Lθ_of_deg_zero (mem_rootFinset.1 hγ) hd t

theorem levi_triple_stable (T : LinData D) {W : Submodule K (V8 → K)}
    (hW : ∀ v ∈ W, ∀ ν, ν ∉ Deg1 Tag.E8 → v ν = 0) {X : Subgroup (ModGL Tag.E8 K)}
    {S : Set V8} (hSX : D.frame S ≤ X)
    (hstab : ∀ l ∈ X ⊓ Lθ Tag.E8 K, ∀ q ∈ Qθ Tag.E8 K, heisCoord Tag.E8 K q ∈ W →
      heisCoord Tag.E8 K (l * q * l⁻¹) ∈ W)
    {a : V8 → V8 → ℤ}
    (hact : ∀ γ ∈ rootFinset Tag.E8, γ 7 = 0 → ∀ t : D.L, ∀ q ∈ Qθ Tag.E8 D.L,
      heisCoord Tag.E8 D.L (pinnedX Tag.E8 D.L γ t * q * (pinnedX Tag.E8 D.L γ t)⁻¹) =
        actFun a γ t (heisCoord Tag.E8 D.L q))
    {γ₀ γ₁ γ₂ : V8} (hr₀ : γ₀ ∈ rootFinset Tag.E8) (hr₁ : γ₁ ∈ rootFinset Tag.E8)
    (hr₂ : γ₂ ∈ rootFinset Tag.E8) (hd₀ : γ₀ 7 = 0) (hd₁ : γ₁ 7 = 0) (hd₂ : γ₂ 7 = 0)
    (hS₀ : γ₀ ∈ S) (hS₁ : γ₁ ∈ S) (hS₂ : γ₂ ∈ S)
    (hw₀ : w • γ₀ = γ₁) (hw₁ : w • γ₁ = γ₂) (hw₂ : w • γ₂ = γ₀)
    (hc₁ : ∀ c d : D.L, Commute (pinnedX Tag.E8 D.L γ₀ c) (pinnedX Tag.E8 D.L γ₁ d))
    (hc₂ : ∀ c d : D.L, Commute (pinnedX Tag.E8 D.L γ₀ c) (pinnedX Tag.E8 D.L γ₂ d)) :
    ∃ s : SignData D.L,
      TripleStable a (Zsp T W) γ₀ γ₁ γ₂ (Nat.card K) s.s₁ s.s₂ s.ε := by
  obtain ⟨s, -, -, -, hσ⟩ := triple_sigma (D := D) (mem_rootFinset.1 hr₀) (mem_rootFinset.1 hr₁)
    (mem_rootFinset.1 hr₂) hw₀ hw₁ hw₂ hc₁ hc₂
  refine ⟨s, fun x hx z hz => ?_⟩
  set u := pinnedX Tag.E8 D.L γ₀ x * pinnedX Tag.E8 D.L γ₁ (s.s₁ * x ^ Nat.card K) *
    pinnedX Tag.E8 D.L γ₂ (s.s₂ * x ^ (Nat.card K ^ 2)) with hu
  have huL : u ∈ Lθ Tag.E8 D.L :=
    mul_mem (mul_mem (pinnedX_mem_Lθ' hr₀ hd₀ _) (pinnedX_mem_Lθ' hr₁ hd₁ _))
      (pinnedX_mem_Lθ' hr₂ hd₂ _)
  have huS : u ∈ rootSpan Tag.E8 D.L S :=
    mul_mem (mul_mem (pinnedX_mem_rootSpan hS₀ _) (pinnedX_mem_rootSpan hS₁ _))
      (pinnedX_mem_rootSpan hS₂ _)
  obtain ⟨l₀, hl₀G, hl₀L, hl₀u⟩ := exists_rational_levi D huL (hσ x hx)
  have hl₀X : l₀ ∈ X := hSX ((mem_frame_iff' D S l₀).2 ⟨hl₀G, by
    rw [hl₀u]
    have : D.g⁻¹ * (D.g * u * D.g⁻¹) * D.g = u := by group
    rw [this]
    exact huS⟩)
  exact Zsp_stable_of_rational T hW hstab (Subgroup.mem_inf.2 ⟨hl₀X, hl₀L⟩) hl₀L hl₀u
    (tripleOp a γ₀ γ₁ γ₂ (Nat.card K) s.s₁ s.s₂ x)
    (fun q hq => act_triple hact hr₀ hd₀ hr₁ hd₁ hr₂ hd₂ _ _ _ hq) z hz

theorem levi_single_stable (T : LinData D) {W : Submodule K (V8 → K)}
    (hW : ∀ v ∈ W, ∀ ν, ν ∉ Deg1 Tag.E8 → v ν = 0) {X : Subgroup (ModGL Tag.E8 K)}
    {S : Set V8} (hSX : D.frame S ≤ X)
    (hstab : ∀ l ∈ X ⊓ Lθ Tag.E8 K, ∀ q ∈ Qθ Tag.E8 K, heisCoord Tag.E8 K q ∈ W →
      heisCoord Tag.E8 K (l * q * l⁻¹) ∈ W)
    {a : V8 → V8 → ℤ}
    (hact : ∀ γ ∈ rootFinset Tag.E8, γ 7 = 0 → ∀ t : D.L, ∀ q ∈ Qθ Tag.E8 D.L,
      heisCoord Tag.E8 D.L (pinnedX Tag.E8 D.L γ t * q * (pinnedX Tag.E8 D.L γ t)⁻¹) =
        actFun a γ t (heisCoord Tag.E8 D.L q))
    {γ : V8} (hr : γ ∈ rootFinset Tag.E8) (hd : γ 7 = 0) (hS : γ ∈ S) (hw : w • γ = γ) :
    ∃ ε : D.L, ε ≠ 0 ∧ SingleStable a (Zsp T W) γ (Nat.card K) ε := by
  obtain ⟨ε, hε, hσ⟩ := single_sigma (D := D) (mem_rootFinset.1 hr) hw
  refine ⟨ε, left_ne_zero_of_mul_eq_one hε, fun x hx z hz => ?_⟩
  set u := pinnedX Tag.E8 D.L γ x with hu
  have huL : u ∈ Lθ Tag.E8 D.L := pinnedX_mem_Lθ' hr hd _
  have huS : u ∈ rootSpan Tag.E8 D.L S := pinnedX_mem_rootSpan hS _
  obtain ⟨l₀, hl₀G, hl₀L, hl₀u⟩ := exists_rational_levi D huL (hσ x hx)
  have hl₀X : l₀ ∈ X := hSX ((mem_frame_iff' D S l₀).2 ⟨hl₀G, by
    rw [hl₀u]
    have : D.g⁻¹ * (D.g * u * D.g⁻¹) * D.g = u := by group
    rw [this]
    exact huS⟩)
  refine Zsp_stable_of_rational T hW hstab (Subgroup.mem_inf.2 ⟨hl₀X, hl₀L⟩) hl₀L hl₀u
    (actOp a γ x) (fun q hq => ⟨conj_mem_Qθ_of_deg_zero D hr hd x hq, hact γ hr hd x q hq⟩) z hz

instance instIsAlgClosedL : IsAlgClosed D.L := (inferInstance : IsAlgClosure K D.L).isAlgClosed

theorem card_cast_zero : ((Nat.card K : ℕ) : D.L) = 0 := by
  haveI := Fintype.ofFinite K
  have h : ((Nat.card K : ℕ) : K) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero K
  have h2 := congrArg (algebraMap K D.L) h
  rw [map_natCast, map_zero] at h2
  exact h2

theorem comm_rearr {G : Type*} [Group G] {X₀ X₁ X₂ y₀ y₁ y₂ : G} (h10 : y₀ * X₁ = X₁ * y₀)
    (h20 : y₀ * X₂ = X₂ * y₀) (h21 : y₁ * X₂ = X₂ * y₁) :
    X₀ * y₀ * (X₁ * y₁) * (X₂ * y₂) = X₀ * X₁ * X₂ * (y₀ * y₁ * y₂) := by
  calc X₀ * y₀ * (X₁ * y₁) * (X₂ * y₂) = X₀ * (y₀ * X₁) * y₁ * (X₂ * y₂) := by group
    _ = X₀ * (X₁ * y₀) * y₁ * (X₂ * y₂) := by rw [h10]
    _ = X₀ * X₁ * (y₀ * (y₁ * X₂)) * y₂ := by group
    _ = X₀ * X₁ * (y₀ * (X₂ * y₁)) * y₂ := by rw [h21]
    _ = X₀ * X₁ * ((y₀ * X₂) * y₁) * y₂ := by group
    _ = X₀ * X₁ * ((X₂ * y₀) * y₁) * y₂ := by rw [h20]
    _ = X₀ * X₁ * X₂ * (y₀ * y₁ * y₂) := by group

theorem conj_pinnedX_deg1 {F : Type} [Field F] {β : V8} (hβ : β ∈ Deg1 Tag.E8) :
    ∃ N : ℤ, (N = 1 ∨ N = -1) ∧ ∀ (q : ModGL Tag.E8 F), q ∈ Qθ Tag.E8 F → ∀ c : F,
      q * pinnedX Tag.E8 F β c * q⁻¹ = pinnedX Tag.E8 F (highRoot Tag.E8)
        ((N : F) * c * heisCoord Tag.E8 F q (highRoot Tag.E8 - β)) * pinnedX Tag.E8 F β c := by
  obtain ⟨N, hN, h⟩ := commutator_Qθ_pinnedX hβ
  refine ⟨N, hN, fun q hq c => ?_⟩
  have := h F q hq c
  rw [← this]
  group

theorem pinnedX_θ_comm {F : Type} [Field F] {β : V8} (hβ : β ∈ Deg1 Tag.E8) (t c : F) :
    pinnedX Tag.E8 F β c * pinnedX Tag.E8 F (highRoot Tag.E8) t =
      pinnedX Tag.E8 F (highRoot Tag.E8) t * pinnedX Tag.E8 F β c :=
  (CoordAux.Uθ_comm (mem_rootSubgroup.2 ⟨t, rfl⟩) (CoordAux.pinnedX_mem_pos hβ c)).symm

theorem int_cast_ne_zero_of {N : ℤ} (hN : N = 1 ∨ N = -1) {F : Type} [Field F] :
    (N : F) ≠ 0 := by
  rcases hN with rfl | rfl <;> simp

theorem R_triple (T : LinData D) {X : Subgroup (ModGL Tag.E8 K)} {S : Set V8}
    (hSX : D.frame S ≤ X) (hq2 : 2 ≤ Nat.card K)
    {γ₀ γ₁ γ₂ : V8} (hD₀ : γ₀ ∈ Deg1 Tag.E8) (hD₁ : γ₁ ∈ Deg1 Tag.E8) (hD₂ : γ₂ ∈ Deg1 Tag.E8)
    (hS₀ : γ₀ ∈ S) (hS₁ : γ₁ ∈ S) (hS₂ : γ₂ ∈ S)
    (hw₀ : w • γ₀ = γ₁) (hw₁ : w • γ₁ = γ₂) (hw₂ : w • γ₂ = γ₀)
    (hc₁ : ∀ c d : D.L, Commute (pinnedX Tag.E8 D.L γ₀ c) (pinnedX Tag.E8 D.L γ₁ d))
    (hc₂ : ∀ c d : D.L, Commute (pinnedX Tag.E8 D.L γ₀ c) (pinnedX Tag.E8 D.L γ₂ d))
    {q₀ : ModGL Tag.E8 K} (hq₀ : q₀ ∈ Qθ Tag.E8 K)
    (hcomm : ∀ r ∈ X ⊓ Qθ Tag.E8 K, q₀ * r = r * q₀) :
    T.Gi (iotaV D (heisCoord Tag.E8 K q₀)) (highRoot Tag.E8 - γ₀) = 0 ∧
    T.Gi (iotaV D (heisCoord Tag.E8 K q₀)) (highRoot Tag.E8 - γ₁) = 0 ∧
    T.Gi (iotaV D (heisCoord Tag.E8 K q₀)) (highRoot Tag.E8 - γ₂) = 0 := by
  obtain ⟨s, -, -, -, hσ⟩ := triple_sigma (D := D) hD₀.1 hD₁.1 hD₂.1 hw₀ hw₁ hw₂ hc₁ hc₂
  obtain ⟨N₀, hN₀, hcN₀⟩ := conj_pinnedX_deg1 (F := D.L) hD₀
  obtain ⟨N₁, hN₁, hcN₁⟩ := conj_pinnedX_deg1 (F := D.L) hD₁
  obtain ⟨N₂, hN₂, hcN₂⟩ := conj_pinnedX_deg1 (F := D.L) hD₂
  obtain ⟨hq'Q, hq'c⟩ := transport_coord T hq₀
  set q' := D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g with hq'
  set v := heisCoord Tag.E8 D.L q' with hv
  have hzero : ∀ x : D.L, x ^ (Nat.card K ^ 3) = s.ε * x →
      (N₀ : D.L) * v (highRoot Tag.E8 - γ₀) * x ^ 1 +
        (N₁ : D.L) * s.s₁ * v (highRoot Tag.E8 - γ₁) * x ^ Nat.card K +
        (N₂ : D.L) * s.s₂ * v (highRoot Tag.E8 - γ₂) * x ^ (Nat.card K ^ 2) = 0 := by
    intro x hx
    set y₀ := pinnedX Tag.E8 D.L γ₀ x with hy₀
    set y₁ := pinnedX Tag.E8 D.L γ₁ (s.s₁ * x ^ Nat.card K) with hy₁
    set y₂ := pinnedX Tag.E8 D.L γ₂ (s.s₂ * x ^ (Nat.card K ^ 2)) with hy₂
    set u := y₀ * y₁ * y₂ with hu
    have huQ : u ∈ Qθ Tag.E8 D.L :=
      mul_mem (mul_mem (pinnedX_mem_Qθ_of_mem_Deg1 hD₀ _) (pinnedX_mem_Qθ_of_mem_Deg1 hD₁ _))
        (pinnedX_mem_Qθ_of_mem_Deg1 hD₂ _)
    have huS : u ∈ rootSpan Tag.E8 D.L S :=
      mul_mem (mul_mem (pinnedX_mem_rootSpan hS₀ _) (pinnedX_mem_rootSpan hS₁ _))
        (pinnedX_mem_rootSpan hS₂ _)
    obtain ⟨r, hrQ, hru⟩ := exists_rational_Qθ D huQ (hσ x hx)
    have hrX : r ∈ X := hSX ((mem_frame_iff' D S r).2 ⟨Qθ_le_adjointGroup Tag.E8 K hrQ, by
      rw [hru]
      have : D.g⁻¹ * (D.g * u * D.g⁻¹) * D.g = u := by group
      rw [this]
      exact huS⟩)
    have h1 := hcomm r (Subgroup.mem_inf.2 ⟨hrX, hrQ⟩)
    have h2 : q' * u = u * q' := by
      have h1' := congrArg (baseChangeGL (algebraMap K D.L)) h1
      rw [map_mul, map_mul, hru] at h1'
      have h3 : q' * u = D.g⁻¹ * (baseChangeGL (algebraMap K D.L) q₀ * (D.g * u * D.g⁻¹)) * D.g := by
        simp only [hq']
        group
      have h4 : u * q' = D.g⁻¹ * ((D.g * u * D.g⁻¹) * baseChangeGL (algebraMap K D.L) q₀) * D.g := by
        simp only [hq']
        group
      rw [h3, h4, h1']
    set X₀ := pinnedX Tag.E8 D.L (highRoot Tag.E8) ((N₀ : D.L) * x * v (highRoot Tag.E8 - γ₀))
      with hX₀
    set X₁ := pinnedX Tag.E8 D.L (highRoot Tag.E8)
      ((N₁ : D.L) * (s.s₁ * x ^ Nat.card K) * v (highRoot Tag.E8 - γ₁)) with hX₁
    set X₂ := pinnedX Tag.E8 D.L (highRoot Tag.E8)
      ((N₂ : D.L) * (s.s₂ * x ^ (Nat.card K ^ 2)) * v (highRoot Tag.E8 - γ₂)) with hX₂
    have e0 : q' * y₀ * q'⁻¹ = X₀ * y₀ := hcN₀ q' hq'Q x
    have e1 : q' * y₁ * q'⁻¹ = X₁ * y₁ := hcN₁ q' hq'Q _
    have e2 : q' * y₂ * q'⁻¹ = X₂ * y₂ := hcN₂ q' hq'Q _
    have hconj : q' * u * q'⁻¹ = X₀ * X₁ * X₂ * u := by
      calc q' * u * q'⁻¹ = (q' * y₀ * q'⁻¹) * (q' * y₁ * q'⁻¹) * (q' * y₂ * q'⁻¹) := by
            rw [hu]
            exact conj_mul3 q' y₀ y₁ y₂
        _ = X₀ * y₀ * (X₁ * y₁) * (X₂ * y₂) := by rw [e0, e1, e2]
        _ = X₀ * X₁ * X₂ * (y₀ * y₁ * y₂) :=
            comm_rearr (pinnedX_θ_comm hD₀ _ _) (pinnedX_θ_comm hD₀ _ _) (pinnedX_θ_comm hD₁ _ _)
        _ = X₀ * X₁ * X₂ * u := rfl
    have hq'u : q' * u * q'⁻¹ = u := by rw [h2]; group
    have h6 : X₀ * X₁ * X₂ * u = u := by rw [← hconj, hq'u]
    have h7 : X₀ * X₁ * X₂ = 1 := mul_right_cancel (b := u) (by rw [h6, one_mul])
    have h8 : pinnedX Tag.E8 D.L (highRoot Tag.E8) ((N₀ : D.L) * x * v (highRoot Tag.E8 - γ₀) +
        (N₁ : D.L) * (s.s₁ * x ^ Nat.card K) * v (highRoot Tag.E8 - γ₁) +
        (N₂ : D.L) * (s.s₂ * x ^ (Nat.card K ^ 2)) * v (highRoot Tag.E8 - γ₂)) = 1 := by
      rw [pinnedX_add, pinnedX_add]
      exact h7
    have h9 := pinnedX_injective Tag.E8 D.L (highRoot Tag.E8)
      (h8.trans (pinnedX_zero Tag.E8 D.L (highRoot Tag.E8)).symm)
    linear_combination h9
  have hN : 2 ≤ Nat.card K ^ 3 := by
    calc 2 ≤ Nat.card K := hq2
      _ ≤ Nat.card K ^ 3 := Nat.le_self_pow (by norm_num) _
  have key := sum_coeff_eq_zero (L := D.L) (N := Nat.card K ^ 3) hN
    (by rw [Nat.cast_pow, card_cast_zero]; norm_num) s.hε (ι := Fin 3)
    ![(N₀ : D.L) * v (highRoot Tag.E8 - γ₀), (N₁ : D.L) * s.s₁ * v (highRoot Tag.E8 - γ₁),
      (N₂ : D.L) * s.s₂ * v (highRoot Tag.E8 - γ₂)] ![1, Nat.card K, Nat.card K ^ 2]
    (by
      intro i j hij
      have hp1 : 1 < Nat.card K := hq2
      have hp2 : Nat.card K < Nat.card K ^ 2 := by nlinarith
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega)
    (by
      intro i
      have hp1 : 1 < Nat.card K := hq2
      have hp0 : Nat.card K < Nat.card K ^ 2 := by nlinarith
      have hp2 : Nat.card K ^ 2 < Nat.card K ^ 3 := by
        have : 0 < Nat.card K ^ 2 := by positivity
        calc Nat.card K ^ 2 < Nat.card K ^ 2 * Nat.card K := lt_mul_of_one_lt_right this hp1
          _ = Nat.card K ^ 3 := by ring
      fin_cases i <;> simp <;> omega)
    (fun x hx => by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]
      exact hzero x hx)
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at k0 k1 k2
  have n0 := int_cast_ne_zero_of (F := D.L) hN₀
  have n1 := int_cast_ne_zero_of (F := D.L) hN₁
  have n2 := int_cast_ne_zero_of (F := D.L) hN₂
  rw [← hq'c]
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.1 k0).resolve_left n0
  · exact (mul_eq_zero.1 k1).resolve_left (mul_ne_zero n1 s.hs₁)
  · exact (mul_eq_zero.1 k2).resolve_left (mul_ne_zero n2 s.hs₂)

theorem R_single (T : LinData D) {X : Subgroup (ModGL Tag.E8 K)} {S : Set V8}
    (hSX : D.frame S ≤ X) (hq2 : 2 ≤ Nat.card K) {γ : V8} (hD : γ ∈ Deg1 Tag.E8) (hS : γ ∈ S)
    (hw : w • γ = γ) {q₀ : ModGL Tag.E8 K} (hq₀ : q₀ ∈ Qθ Tag.E8 K)
    (hcomm : ∀ r ∈ X ⊓ Qθ Tag.E8 K, q₀ * r = r * q₀) :
    T.Gi (iotaV D (heisCoord Tag.E8 K q₀)) (highRoot Tag.E8 - γ) = 0 := by
  obtain ⟨ε, hε, hσ⟩ := single_sigma (D := D) hD.1 hw
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul_eq_one hε
  obtain ⟨N, hN, hcN⟩ := conj_pinnedX_deg1 (F := D.L) hD
  obtain ⟨hq'Q, hq'c⟩ := transport_coord T hq₀
  set q' := D.g⁻¹ * baseChangeGL (algebraMap K D.L) q₀ * D.g with hq'
  set v := heisCoord Tag.E8 D.L q' with hv
  have hzero : ∀ x : D.L, x ^ Nat.card K = ε * x → (N : D.L) * v (highRoot Tag.E8 - γ) * x ^ 1 = 0 := by
    intro x hx
    set u := pinnedX Tag.E8 D.L γ x with hu
    have huQ : u ∈ Qθ Tag.E8 D.L := pinnedX_mem_Qθ_of_mem_Deg1 hD _
    have huS : u ∈ rootSpan Tag.E8 D.L S := pinnedX_mem_rootSpan hS _
    obtain ⟨r, hrQ, hru⟩ := exists_rational_Qθ D huQ (hσ x hx)
    have hrX : r ∈ X := hSX ((mem_frame_iff' D S r).2 ⟨Qθ_le_adjointGroup Tag.E8 K hrQ, by
      rw [hru]
      have : D.g⁻¹ * (D.g * u * D.g⁻¹) * D.g = u := by group
      rw [this]
      exact huS⟩)
    have h1 := hcomm r (Subgroup.mem_inf.2 ⟨hrX, hrQ⟩)
    have h2 : q' * u = u * q' := by
      have h1' := congrArg (baseChangeGL (algebraMap K D.L)) h1
      rw [map_mul, map_mul, hru] at h1'
      have h3 : q' * u = D.g⁻¹ * (baseChangeGL (algebraMap K D.L) q₀ * (D.g * u * D.g⁻¹)) * D.g := by
        simp only [hq']
        group
      have h4 : u * q' = D.g⁻¹ * ((D.g * u * D.g⁻¹) * baseChangeGL (algebraMap K D.L) q₀) * D.g := by
        simp only [hq']
        group
      rw [h3, h4, h1']
    set X₀ := pinnedX Tag.E8 D.L (highRoot Tag.E8) ((N : D.L) * x * v (highRoot Tag.E8 - γ)) with hX₀
    have e0 : q' * u * q'⁻¹ = X₀ * u := hcN q' hq'Q x
    have hq'u : q' * u * q'⁻¹ = u := by rw [h2]; group
    have h7 : X₀ = 1 := mul_right_cancel (b := u) (by rw [← e0, hq'u, one_mul])
    have h9 := pinnedX_injective Tag.E8 D.L (highRoot Tag.E8)
      (h7.trans (pinnedX_zero Tag.E8 D.L (highRoot Tag.E8)).symm)
    linear_combination h9
  have key := sum_coeff_eq_zero (L := D.L) (N := Nat.card K) hq2 (card_cast_zero (D := D)) hε0
    (ι := Fin 1) ![(N : D.L) * v (highRoot Tag.E8 - γ)] ![1]
    (fun i j _ => by fin_cases i; fin_cases j; rfl)
    (fun i => by fin_cases i; simp; omega)
    (fun x hx => by
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
      exact hzero x hx)
  have k0 := key 0
  simp only [Matrix.cons_val_zero] at k0
  rw [← hq'c]
  exact (mul_eq_zero.1 k0).resolve_left (int_cast_ne_zero_of hN)

end Transport

section Data

open CFSG.LieType.Steinberg.Adjoint

@[expose] def o1 : V8 := ![0, 0, 0, 0, 0, 0, 0, 1]
@[expose] def p0 : V8 := ![0, 0, 0, 0, 0, 0, 1, 1]
@[expose] def p1 : V8 := ![2, 2, 3, 4, 3, 2, 1, 1]
@[expose] def p2 : V8 := ![0, 1, 1, 2, 2, 2, 1, 1]
@[expose] def r0 : V8 := ![0, 1, 1, 2, 2, 2, 2, 1]
@[expose] def r1 : V8 := ![2, 2, 3, 4, 3, 2, 2, 1]
@[expose] def r2 : V8 := ![2, 3, 4, 6, 5, 4, 2, 1]
@[expose] def o4 : V8 := ![2, 3, 4, 6, 5, 4, 3, 1]

@[expose] def allRoots : List V8 :=
  [a0, a1, a2, -a0, -a1, -a2, lf1, lf2, lf4, -lf1, -lf2, -lf4, cn, -cn, o1, p0, p1, p2, r0, r1, r2, o4]

theorem allRoots_mem : ∀ γ ∈ allRoots, γ ∈ rootFinset Tag.E8 := by decide +kernel

@[expose] def wPairs : List (V8 × V8) :=
  [(a0, a2), (a2, a1), (a1, a0), (-a0, -a2), (-a2, -a1), (-a1, -a0), (lf1, lf2), (lf2, lf4),
    (lf4, lf1), (-lf1, -lf2), (-lf2, -lf4), (-lf4, -lf1), (cn, cn), (-cn, -cn), (o1, o1),
    (p0, p1), (p1, p2), (p2, p0), (r0, r1), (r1, r2), (r2, r0), (o4, o4)]

theorem wPairs_eq : ∀ pr ∈ wPairs, wp pr.1 = pr.2 := by decide +kernel

@[expose] def commPairs : List (V8 × V8) :=
  [(a0, a2), (a0, a1), (-a0, -a2), (-a0, -a1), (lf1, lf2), (lf1, lf4), (-lf1, -lf2), (-lf1, -lf4),
    (p0, p1), (p0, p2), (r0, r1), (r0, r2)]

theorem commPairs_data :
    ∀ pr ∈ commPairs, pr.1 ≠ pr.2 ∧ pr.1 ≠ -pr.2 ∧ pr.1 + pr.2 ∉ rootFinset Tag.E8 := by
  decide +kernel

@[expose] def s1List : List V8 := [a0, a1, a2, -a0, -a1, -a2, o1, p0, p1, p2, r0, r1, r2, o4]

theorem s1List_orth : ∀ β ∈ s1List, ∀ j : Fin Tag.E8.rank,
    j.val ∈ ({1, 2, 3, 4} : Finset ℕ) → iform β (Pi.single j 1) = 0 := by decide +kernel

@[expose] def s2List : List V8 := [lf1, lf2, lf4, -lf1, -lf2, -lf4, cn, -cn]

theorem s2List_supp : ∀ α ∈ s2List, ∀ i : Fin Tag.E8.rank, i.val ∉ ({1, 2, 3, 4} : Finset ℕ) →
    α i = 0 := by
  decide +kernel

@[expose] def levi0List : List V8 :=
  [a0, a1, a2, -a0, -a1, -a2, lf1, lf2, lf4, -lf1, -lf2, -lf4, cn, -cn]

theorem levi0List_deg : ∀ γ ∈ levi0List, γ 7 = 0 := by decide +kernel

@[expose] def deg1List : List V8 := [o1, p0, p1, p2, r0, r1, r2, o4]

theorem deg1List_deg : ∀ γ ∈ deg1List, γ 7 = 1 := by decide +kernel

theorem sig1_sub : ∀ β ∈ sig1, β ∈ deg1List := by decide +kernel

theorem theta_sub : highRoot Tag.E8 - o1 = o4 ∧ highRoot Tag.E8 - o4 = o1 ∧
    highRoot Tag.E8 - p0 = r2 ∧ highRoot Tag.E8 - p1 = r0 ∧ highRoot Tag.E8 - p2 = r1 ∧
    highRoot Tag.E8 - r0 = p1 ∧ highRoot Tag.E8 - r1 = p2 ∧ highRoot Tag.E8 - r2 = p0 := by
  decide +kernel

@[expose] def wE8 : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd TwClass.wordE8Twelve

theorem w_smul (u : V8) : wE8 • u = wp u := by
  change (coxeterSystem Tag.E8).wordProd TwClass.wordE8Twelve • u =
    TwClass.wordE8Twelve.foldr (reflect Tag.E8) u
  generalize TwClass.wordE8Twelve = l
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem w_smul_eq {γ γ' : V8} (h : (γ, γ') ∈ wPairs) : wE8 • γ = γ' := by
  rw [w_smul]
  exact wPairs_eq (γ, γ') h

theorem mem_allRoots {γ : V8} (h : γ ∈ allRoots) : IsRoot Tag.E8 γ :=
  mem_rootFinset.1 (allRoots_mem γ h)

theorem orth_of_simple {τ : Tag} (β : Fin τ.rank → ℤ) (J : Finset ℕ)
    (hβ : ∀ j : Fin τ.rank, j.val ∈ J → iform β (Pi.single j 1) = 0) (α : Fin τ.rank → ℤ)
    (hα : ∀ i : Fin τ.rank, i.val ∉ J → α i = 0) : iform β α = 0 := by
  rw [Heis.iform_eq_sum_single]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j.val ∈ J
  · rw [hβ j hj, zero_mul]
  · rw [hα j hj, mul_zero]

theorem mem_S₁ {β : V8} (hr : β ∈ allRoots) (h : β ∈ s1List) : β ∈ TwClass.e8Twelve.S₁ :=
  ⟨mem_allRoots hr, fun α hα => orth_of_simple β {1, 2, 3, 4} (s1List_orth β h) α hα.2⟩

theorem mem_S₂ {α : V8} (hr : α ∈ allRoots) (h : α ∈ s2List) : α ∈ TwClass.e8Twelve.S₂ :=
  ⟨mem_allRoots hr, s2List_supp α h⟩

end Data

section Families

variable {K : Type} [Field K] [Finite K] {D : LangLevi Tag.E8 K wE8}

theorem commute_of_pair {γ γ' : V8} (hγ : γ ∈ allRoots) (hγ' : γ' ∈ allRoots)
    (h : (γ, γ') ∈ commPairs) {R : Type} [CommRing R] (c d : R) :
    Commute (pinnedX Tag.E8 R γ c) (pinnedX Tag.E8 R γ' d) := by
  obtain ⟨h1, h2, h3⟩ := commPairs_data (γ, γ') h
  exact (simply_laced_root_commutator_unit.{0} Tag.E8 (Or.inr (Or.inr (Or.inr rfl)))
    (mem_allRoots hγ) (mem_allRoots hγ') h1 h2).2 (fun hr => h3 (mem_rootFinset.2 hr)) R _
    (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem Deg1_of_deg1List {γ : V8} (hr : γ ∈ allRoots) (h : γ ∈ deg1List) : γ ∈ Deg1 Tag.E8 :=
  ⟨mem_allRoots hr, deg1List_deg γ h⟩

variable (T : LinData D) {W : Submodule K (V8 → K)}
  (hW : ∀ v ∈ W, ∀ ν, ν ∉ Deg1 Tag.E8 → v ν = 0) {X : Subgroup (ModGL Tag.E8 K)}
  (hstab : ∀ l ∈ X ⊓ Lθ Tag.E8 K, ∀ q ∈ Qθ Tag.E8 K, heisCoord Tag.E8 K q ∈ W →
      heisCoord Tag.E8 K (l * q * l⁻¹) ∈ W)
  {a : V8 → V8 → ℤ}
  (hact : ∀ γ ∈ rootFinset Tag.E8, γ 7 = 0 → ∀ t : D.L, ∀ q ∈ Qθ Tag.E8 D.L,
      heisCoord Tag.E8 D.L (pinnedX Tag.E8 D.L γ t * q * (pinnedX Tag.E8 D.L γ t)⁻¹) =
        actFun a γ t (heisCoord Tag.E8 D.L q))

include hW hstab hact

theorem stab_Apos (hSX : D.frame TwClass.e8Twelve.S₁ ≤ X) :
    ∃ s : SignData D.L, TripleStable a (Zsp T W) a0 a2 a1 (Nat.card K) s.s₁ s.s₂ s.ε :=
  levi_triple_stable T hW hSX hstab hact (allRoots_mem _ (by simp [allRoots]))
    (allRoots_mem _ (by simp [allRoots])) (allRoots_mem _ (by simp [allRoots]))
    (levi0List_deg _ (by simp [levi0List])) (levi0List_deg _ (by simp [levi0List]))
    (levi0List_deg _ (by simp [levi0List]))
    (mem_S₁ (by simp [allRoots]) (by simp [s1List])) (mem_S₁ (by simp [allRoots]) (by simp [s1List]))
    (mem_S₁ (by simp [allRoots]) (by simp [s1List]))
    (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs]))

theorem stab_Aneg (hSX : D.frame TwClass.e8Twelve.S₁ ≤ X) :
    ∃ s : SignData D.L,
      TripleStable a (Zsp T W) (-a0) (-a2) (-a1) (Nat.card K) s.s₁ s.s₂ s.ε :=
  levi_triple_stable T hW hSX hstab hact (allRoots_mem _ (by simp [allRoots]))
    (allRoots_mem _ (by simp [allRoots])) (allRoots_mem _ (by simp [allRoots]))
    (levi0List_deg _ (by simp [levi0List])) (levi0List_deg _ (by simp [levi0List]))
    (levi0List_deg _ (by simp [levi0List]))
    (mem_S₁ (by simp [allRoots]) (by simp [s1List])) (mem_S₁ (by simp [allRoots]) (by simp [s1List]))
    (mem_S₁ (by simp [allRoots]) (by simp [s1List]))
    (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs]))

theorem stab_Lpos (hSX : D.frame TwClass.e8Twelve.S₂ ≤ X) :
    ∃ s : SignData D.L, TripleStable a (Zsp T W) lf1 lf2 lf4 (Nat.card K) s.s₁ s.s₂ s.ε :=
  levi_triple_stable T hW hSX hstab hact (allRoots_mem _ (by simp [allRoots]))
    (allRoots_mem _ (by simp [allRoots])) (allRoots_mem _ (by simp [allRoots]))
    (levi0List_deg _ (by simp [levi0List])) (levi0List_deg _ (by simp [levi0List]))
    (levi0List_deg _ (by simp [levi0List]))
    (mem_S₂ (by simp [allRoots]) (by simp [s2List])) (mem_S₂ (by simp [allRoots]) (by simp [s2List]))
    (mem_S₂ (by simp [allRoots]) (by simp [s2List]))
    (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs]))

theorem stab_Lneg (hSX : D.frame TwClass.e8Twelve.S₂ ≤ X) :
    ∃ s : SignData D.L,
      TripleStable a (Zsp T W) (-lf1) (-lf2) (-lf4) (Nat.card K) s.s₁ s.s₂ s.ε :=
  levi_triple_stable T hW hSX hstab hact (allRoots_mem _ (by simp [allRoots]))
    (allRoots_mem _ (by simp [allRoots])) (allRoots_mem _ (by simp [allRoots]))
    (levi0List_deg _ (by simp [levi0List])) (levi0List_deg _ (by simp [levi0List]))
    (levi0List_deg _ (by simp [levi0List]))
    (mem_S₂ (by simp [allRoots]) (by simp [s2List])) (mem_S₂ (by simp [allRoots]) (by simp [s2List]))
    (mem_S₂ (by simp [allRoots]) (by simp [s2List]))
    (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs]))

theorem stab_Cpos (hSX : D.frame TwClass.e8Twelve.S₂ ≤ X) :
    ∃ ε : D.L, ε ≠ 0 ∧ SingleStable a (Zsp T W) cn (Nat.card K) ε :=
  levi_single_stable T hW hSX hstab hact (allRoots_mem _ (by simp [allRoots]))
    (levi0List_deg _ (by simp [levi0List])) (mem_S₂ (by simp [allRoots]) (by simp [s2List]))
    (w_smul_eq (by simp [wPairs]))

theorem stab_Cneg (hSX : D.frame TwClass.e8Twelve.S₂ ≤ X) :
    ∃ ε : D.L, ε ≠ 0 ∧ SingleStable a (Zsp T W) (-cn) (Nat.card K) ε :=
  levi_single_stable T hW hSX hstab hact (allRoots_mem _ (by simp [allRoots]))
    (levi0List_deg _ (by simp [levi0List])) (mem_S₂ (by simp [allRoots]) (by simp [s2List]))
    (w_smul_eq (by simp [wPairs]))

omit hW hstab hact

theorem propA (T : LinData D) {X : Subgroup (ModGL Tag.E8 K)}
    (hS₁ : D.frame TwClass.e8Twelve.S₁ ≤ X) (hq2 : 2 ≤ Nat.card K) {q₀ : ModGL Tag.E8 K}
    (hq₀ : q₀ ∈ Qθ Tag.E8 K) (hcomm : ∀ r ∈ X ⊓ Qθ Tag.E8 K, q₀ * r = r * q₀) :
    ∀ β ∈ sig1, T.Gi (iotaV D (heisCoord Tag.E8 K q₀)) β = 0 := by
  set V := T.Gi (iotaV D (heisCoord Tag.E8 K q₀)) with hV
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := theta_sub
  have s1 : V (highRoot Tag.E8 - o1) = 0 :=
    R_single T hS₁ hq2 (Deg1_of_deg1List (by simp [allRoots]) (by simp [deg1List]))
      (mem_S₁ (by simp [allRoots]) (by simp [s1List])) (w_smul_eq (by simp [wPairs])) hq₀ hcomm
  have s4 : V (highRoot Tag.E8 - o4) = 0 :=
    R_single T hS₁ hq2 (Deg1_of_deg1List (by simp [allRoots]) (by simp [deg1List]))
      (mem_S₁ (by simp [allRoots]) (by simp [s1List])) (w_smul_eq (by simp [wPairs])) hq₀ hcomm
  obtain ⟨u0, u1, u2⟩ := R_triple T hS₁ hq2 (γ₀ := p0) (γ₁ := p1) (γ₂ := p2)
    (Deg1_of_deg1List (by simp [allRoots]) (by simp [deg1List]))
    (Deg1_of_deg1List (by simp [allRoots]) (by simp [deg1List]))
    (Deg1_of_deg1List (by simp [allRoots]) (by simp [deg1List]))
    (mem_S₁ (by simp [allRoots]) (by simp [s1List])) (mem_S₁ (by simp [allRoots]) (by simp [s1List]))
    (mem_S₁ (by simp [allRoots]) (by simp [s1List]))
    (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs])) hq₀ hcomm
  obtain ⟨v0, v1, v2⟩ := R_triple T hS₁ hq2 (γ₀ := r0) (γ₁ := r1) (γ₂ := r2)
    (Deg1_of_deg1List (by simp [allRoots]) (by simp [deg1List]))
    (Deg1_of_deg1List (by simp [allRoots]) (by simp [deg1List]))
    (Deg1_of_deg1List (by simp [allRoots]) (by simp [deg1List]))
    (mem_S₁ (by simp [allRoots]) (by simp [s1List])) (mem_S₁ (by simp [allRoots]) (by simp [s1List]))
    (mem_S₁ (by simp [allRoots]) (by simp [s1List]))
    (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs])) (w_smul_eq (by simp [wPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs]))
    (commute_of_pair (by simp [allRoots]) (by simp [allRoots]) (by simp [commPairs])) hq₀ hcomm
  rw [t1] at s1
  rw [t2] at s4
  rw [t3] at u0
  rw [t4] at u1
  rw [t5] at u2
  rw [t6] at v0
  rw [t7] at v1
  rw [t8] at v2
  intro β hβ
  have hmem := sig1_sub β hβ
  simp only [deg1List, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s4
  · exact v2
  · exact v0
  · exact v1
  · exact u1
  · exact u2
  · exact u0
  · exact s1

end Families

section Descent

variable {K : Type} [Field K] [Finite K] {D : LangLevi Tag.E8 K wE8}

theorem mem_of_iotaV_mem_span (D : LangLevi Tag.E8 K wE8) (W : Submodule K (V8 → K))
    {v : V8 → K} (h : iotaV D v ∈ Submodule.span D.L (iotaV D '' (W : Set (V8 → K)))) :
    v ∈ W := by
  obtain ⟨φ, hφ⟩ : ∃ φ : D.L →ₗ[K] K, φ 1 = 1 := by
    have hinj : LinearMap.ker (Algebra.linearMap K D.L) = ⊥ :=
      LinearMap.ker_eq_bot.2 (algebraMap K D.L).injective
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K D.L) hinj
    refine ⟨g, ?_⟩
    have := LinearMap.congr_fun hg 1
    simpa using this
  have key : ∀ y ∈ Submodule.span D.L (iotaV D '' (W : Set (V8 → K))),
      ∀ ψ : D.L →ₗ[K] K, (fun ν => ψ (y ν)) ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      intro ψ
      have : (fun ν => ψ (iotaV D w ν)) = ψ 1 • w := by
        funext ν
        have : algebraMap K D.L (w ν) = (w ν) • (1 : D.L) := by simp [Algebra.smul_def]
        simp only [iotaV_apply, this, map_smul, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this]
      exact W.smul_mem _ hw
    | zero =>
      intro ψ
      have : (fun ν => ψ ((0 : V8 → D.L) ν)) = 0 := by
        funext ν
        simp
      rw [this]
      exact zero_mem _
    | add x y _ _ hx hy =>
      intro ψ
      have : (fun ν => ψ ((x + y) ν)) = (fun ν => ψ (x ν)) + (fun ν => ψ (y ν)) := by
        funext ν
        simp
      rw [this]
      exact add_mem (hx ψ) (hy ψ)
    | smul c x _ hx =>
      intro ψ
      have : (fun ν => ψ ((c • x) ν)) = fun ν => (ψ.comp (LinearMap.mulLeft K c)) (x ν) := by
        funext ν
        simp
      rw [this]
      exact hx _
  have h1 := key _ h φ
  have : (fun ν => φ (iotaV D v ν)) = v := by
    funext ν
    have : algebraMap K D.L (v ν) = (v ν) • (1 : D.L) := by simp [Algebra.smul_def]
    simp only [iotaV_apply, this, map_smul, hφ, smul_eq_mul, mul_one]
  rw [this] at h1
  exact h1

theorem N_single (T : LinData D) {μ : V8} (hμ : μ ∈ Deg1 Tag.E8) (hwμ : wE8 • μ ∈ Deg1 Tag.E8) :
    ∃ ε : D.L, ε * ε = 1 ∧ T.N (Pi.single μ 1) = Pi.single (wE8 • μ) ε := by
  obtain ⟨ε, hε, hn⟩ := exists_sign (D := D) hμ.1
  refine ⟨ε, hε, ?_⟩
  have hq : pinnedX Tag.E8 D.L μ 1 ∈ Qθ Tag.E8 D.L := pinnedX_mem_Qθ_of_mem_Deg1 hμ 1
  obtain ⟨-, h2⟩ := T.N_spec _ hq
  rw [hn, (heisCoord_spec Tag.E8 D.L).pinnedX_deg1 _ hμ,
    (heisCoord_spec Tag.E8 D.L).pinnedX_deg1 _ hwμ, mul_one] at h2
  exact h2.symm

theorem wp_mem_deg1 : ∀ μ ∈ dl, wp μ ∈ deg1Roots := by decide +kernel

theorem eq_sum_single_of_supp {x : V8 → D.L} (hx : ∀ ν, ν ∉ dl → x ν = 0) :
    x = ∑ μ ∈ dl, x μ • (Pi.single μ (1 : D.L) : V8 → D.L) := by
  funext ν
  rw [Finset.sum_apply]
  by_cases hν : ν ∈ dl
  · rw [Finset.sum_eq_single ν]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, Ne.symm hb]
    · intro h
      exact absurd hν h
  · rw [hx ν hν]
    symm
    refine Finset.sum_eq_zero fun μ hμ => ?_
    have : ν ≠ μ := fun h => hν (h ▸ hμ)
    simp [Pi.single_apply, this]

end Descent

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrE8
