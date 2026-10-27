module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitNCData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitNative
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Lin
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Second

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage2

theorem toMatK_zero : toMatK 0 = 0 := by
  ext i j
  simp [toMatK]

theorem not_isUnit_of_rep_zero {z : GL12} (hz : Rep 0 z) : False := by
  have h1 : ((z * z⁻¹ : GL12) : Mat12) = 1 := by rw [mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, ← hz, toMatK_zero, zero_mul] at h1
  have := congrFun (congrFun h1 0) 0
  simp at this

theorem relPair_conj {a b c d : ℕ} {A B y : GL12} (ha : Rep a A) (hb : Rep b B)
    (hc : Rep c (y * A * y⁻¹)) (hd : Rep d (y * B * y⁻¹)) : relPair a b c d = true := by
  have hab : (mulK a b = mulK b a) ↔ A * B = B * A := by
    constructor
    · intro e
      have h1 := hb.mul ha
      rw [← e] at h1
      exact (ha.mul hb).unique h1
    · intro e
      exact key_eq_of_mul ha hb e
  have hcd : (mulK c d = mulK d c) ↔ A * B = B * A := by
    constructor
    · intro e
      have h0 := hd.mul hc
      rw [← e] at h0
      have h1 := (hc.mul hd).unique h0
      have h2 : y * (A * B) * y⁻¹ = y * (B * A) * y⁻¹ := by
        calc y * (A * B) * y⁻¹ = y * A * y⁻¹ * (y * B * y⁻¹) := by group
          _ = y * B * y⁻¹ * (y * A * y⁻¹) := h1
          _ = y * (B * A) * y⁻¹ := by group
      simpa using h2
    · intro e
      refine key_eq_of_mul hc hd ?_
      calc y * A * y⁻¹ * (y * B * y⁻¹) = y * (A * B) * y⁻¹ := by group
        _ = y * (B * A) * y⁻¹ := by rw [e]
        _ = y * B * y⁻¹ * (y * A * y⁻¹) := by group
  have hab3 : (powK (mulK a b) 3 = idK) ↔ (A * B) ^ 3 = 1 := by
    constructor
    · intro e
      exact ((ha.mul hb).pow 3).unique (e ▸ rep_one)
    · intro e
      exact ((ha.mul hb).pow 3).key_unique (e ▸ rep_one) (powK_lt _ _) idK_lt
  have hcd3 : (powK (mulK c d) 3 = idK) ↔ (A * B) ^ 3 = 1 := by
    have hconj : (y * A * y⁻¹ * (y * B * y⁻¹)) ^ 3 = y * (A * B) ^ 3 * y⁻¹ := by
      rw [show y * A * y⁻¹ * (y * B * y⁻¹) = y * (A * B) * y⁻¹ by group, conj_pow]
    constructor
    · intro e
      have h1 := ((hc.mul hd).pow 3).unique (e ▸ rep_one)
      rw [hconj] at h1
      have : (A * B) ^ 3 = y⁻¹ * (y * (A * B) ^ 3 * y⁻¹) * y := by group
      rw [this, h1]
      group
    · intro e
      refine ((hc.mul hd).pow 3).key_unique ?_ (powK_lt _ _) idK_lt
      rw [hconj, e, mul_one, mul_inv_cancel]
      exact rep_one
  simp only [relPair, Bool.and_eq_true, Bool.beq_eq_decide_eq, decide_eq_true_eq]
  exact ⟨decide_eq_decide.mpr (hab.trans hcd.symm), decide_eq_decide.mpr (hab3.trans hcd3.symm)⟩

theorem exists_of_chainAux {cs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK cs E = true)
    {R ρs₀ : List ℕ} (hrep : ∀ ρ ∈ ρs₀, Rep ρ (glOf ρ ρ))
    (hR : ∀ y : GL12, (∀ c ∈ grpOf cs, y * c * y⁻¹ ∈ grpOf cs) → ∀ ρ ∈ ρs₀,
      keyOfMat ((y * glOf ρ ρ * y⁻¹ : GL12) : Mat12) ∈ R) :
    ∀ (ρs fx : List ℕ) (kss : List (List (ℕ × ℕ))), chainAux E.keys R fx ρs kss = true →
      (∀ φ ∈ fx, φ ∈ ρs₀) → (∀ ρ ∈ ρs, ρ ∈ ρs₀) →
      ∀ y : GL12, (∀ c ∈ grpOf cs, y * c * y⁻¹ ∈ grpOf cs) →
        (∀ φ ∈ fx, y * glOf φ φ = glOf φ φ * y) →
        ∃ K ∈ grpOf cs, ∀ ρ ∈ fx ++ ρs, K⁻¹ * y * glOf ρ ρ = glOf ρ ρ * (K⁻¹ * y)
  | [], fx, _, _, _, _, y, _, hfx => ⟨1, one_mem _, fun ρ hρ => by
      rw [List.append_nil] at hρ
      rw [inv_one, one_mul]
      exact hfx ρ hρ⟩
  | _ :: _, _, [], h, _, _, _, _, _ => by simp [chainAux] at h
  | ρ :: ρs, fx, ks :: kss, h, hfx0, hρs0, y, hy, hfx => by
    simp only [chainAux, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.any_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hρ0 : ρ ∈ ρs₀ := hρs0 ρ List.mem_cons_self
    have hσR := hR y hy ρ hρ0
    rcases h1 _ hσR with h3 | ⟨p, -, ⟨⟨-, hpm⟩, hpc⟩, hpρ⟩
    · exfalso
      have : (fx.all fun φ => relPair φ ρ φ (keyOfMat ((y * glOf ρ ρ * y⁻¹ : GL12) : Mat12))) =
          true := by
        refine List.all_eq_true.2 fun φ hφ => ?_
        have hφ0 := hfx0 φ hφ
        refine relPair_conj (hrep φ hφ0) (hrep ρ hρ0) (y := y) ?_ (rep_keyOfMat _)
        rw [show y * glOf φ φ * y⁻¹ = glOf φ φ by rw [hfx φ hφ]; group]
        exact hrep φ hφ0
      rw [h3] at this
      exact Bool.false_ne_true this
    · obtain ⟨K₁, hK₁, hrK₁⟩ := Enum.rep_of_memK hE hpm
      have hK₁φ : ∀ φ ∈ fx, K₁ * glOf φ φ = glOf φ φ * K₁ := fun φ hφ =>
        (commute_iff_key hrK₁ (hrep φ (hfx0 φ hφ))).2 (hpc φ hφ)
      have hK₁ρ : K₁ * glOf ρ ρ = (y * glOf ρ ρ * y⁻¹) * K₁ := by
        have e1 := hrK₁.mul (hrep ρ hρ0)
        rw [hpρ] at e1
        exact e1.unique ((rep_keyOfMat _).mul hrK₁)
      set y' := K₁⁻¹ * y with hy'
      have hy'N : ∀ c ∈ grpOf cs, y' * c * y'⁻¹ ∈ grpOf cs := by
        intro c hc
        have e : y' * c * y'⁻¹ = K₁⁻¹ * (y * c * y⁻¹) * K₁ := by rw [hy']; group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hK₁) (hy c hc)) hK₁
      have hy'fx : ∀ φ ∈ fx ++ [ρ], y' * glOf φ φ = glOf φ φ * y' := by
        intro φ hφ
        rcases List.mem_append.1 hφ with hφ | hφ
        · have e1 := hK₁φ φ hφ
          have e2 := hfx φ hφ
          calc y' * glOf φ φ = K₁⁻¹ * (y * glOf φ φ) := by rw [hy']; group
            _ = K₁⁻¹ * (glOf φ φ * y) := by rw [e2]
            _ = K₁⁻¹ * (glOf φ φ * K₁) * K₁⁻¹ * y := by group
            _ = K₁⁻¹ * (K₁ * glOf φ φ) * K₁⁻¹ * y := by rw [e1]
            _ = glOf φ φ * y' := by rw [hy']; group
        · rw [List.mem_singleton] at hφ
          subst hφ
          calc y' * glOf φ φ = K₁⁻¹ * ((y * glOf φ φ * y⁻¹) * K₁) * K₁⁻¹ * y := by
                rw [hy']; group
            _ = K₁⁻¹ * (K₁ * glOf φ φ) * K₁⁻¹ * y := by rw [hK₁ρ]
            _ = glOf φ φ * y' := by rw [hy']; group
      obtain ⟨K', hK', hK'c⟩ := exists_of_chainAux hE hrep hR ρs (fx ++ [ρ]) kss h2
        (fun φ hφ => by
          rcases List.mem_append.1 hφ with hφ | hφ
          · exact hfx0 φ hφ
          · rw [List.mem_singleton] at hφ
            rw [hφ]
            exact hρ0)
        (fun ρ' hρ' => hρs0 ρ' (List.mem_cons_of_mem _ hρ')) y' hy'N hy'fx
      refine ⟨K₁ * K', mul_mem hK₁ hK', fun ρ' hρ' => ?_⟩
      have e : (K₁ * K')⁻¹ * y = K'⁻¹ * y' := by rw [hy']; group
      rw [e]
      exact hK'c ρ' (by simpa using hρ')

theorem forall_of_linCheckWith {cons : List (ℕ × ℕ)} {qc : List (List ℕ)} {qf fs : List ℕ}
    (h : linCheckWith cons qc qf fs = true) {P : ℕ → Bool} (hP : spanAll qf fs.length P = true)
    {m : ℕ} (hm : m < 2 ^ 144) (hsol : ∀ c ∈ cons, mulK c.1 m = mulK m c.2) : P m = true := by
  rw [eq_linComb_of_linCheckWith h hm hsol]
  simp only [spanAll, List.all_eq_true, List.mem_range] at hP
  exact hP _ (freeBits_lt _ _)

theorem mem_of_normalizes {cs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK cs E = true)
    {R ρs : List ℕ} {kss : List (List (ℕ × ℕ))}
    (hR : ((List.range E.keys.size).all fun i =>
      mulK (E.keys.getD i 0) (E.keys.getD i 0) != idK || E.keys.getD i 0 == idK ||
        fixCountF (E.keys.getD i 0) != 1024 || R.contains (E.keys.getD i 0)) = true)
    (hρ : (ρs.all fun ρ => invPair ρ ρ && memK E.keys ρ && fixCountF ρ == 1024) = true)
    (hch : chainAux E.keys R [] ρs kss = true)
    (hP : ∀ {m : ℕ}, m < 2 ^ 144 → (∀ c ∈ commCons ρs, mulK c.1 m = mulK m c.2) →
      (m == 0 || m == idK || m == phiK || m == (idK ^^^ phiK)) = true)
    (hsq : mulK (idK ^^^ phiK) (idK ^^^ phiK) = 0) (hphi : invPair phiK phiK = true)
    (htC : memK E.keys phiK = true) (hct : ∀ x ∈ grpOf cs, tbarG * x = x * tbarG)
    {y : GL12} (hy : ∀ c ∈ grpOf cs, y * c * y⁻¹ ∈ grpOf cs) (hyt : y * tbarG = tbarG * y) :
    y ∈ grpOf cs := by
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hρ
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, List.contains_eq_any_beq, List.any_eq_true] at hR
  have hrepρ : ∀ ρ ∈ ρs, Rep ρ (glOf ρ ρ) := fun ρ hρ' => rep_glOf (hρ ρ hρ').1.1
  have hmemρ : ∀ ρ ∈ ρs, glOf ρ ρ ∈ grpOf cs := fun ρ hρ' =>
    Enum.mem_of_memK hE (hρ ρ hρ').1.2 (hrepρ ρ hρ')
  have hfR : ∀ y : GL12, (∀ c ∈ grpOf cs, y * c * y⁻¹ ∈ grpOf cs) → ∀ ρ ∈ ρs,
      keyOfMat ((y * glOf ρ ρ * y⁻¹ : GL12) : Mat12) ∈ R := by
    intro y hy ρ hρ'
    have hσ := hy _ (hmemρ ρ hρ')
    obtain ⟨i, hi, hri⟩ := Enum.exists_key hE hσ
    have hki : E.keys.getD i 0 = keyOfMat ((y * glOf ρ ρ * y⁻¹ : GL12) : Mat12) :=
      hri.key_unique (rep_keyOfMat _) (Enum.key_lt hE hi) (keyOfMat_lt _)
    have hsq1 : glOf ρ ρ * glOf ρ ρ = 1 := by
      have h1 := (hρ ρ hρ').1.1
      simp only [invPair, Bool.and_eq_true, beq_iff_eq] at h1
      exact ((hrepρ ρ hρ').mul (hrepρ ρ hρ')).unique (by rw [h1.1]; exact rep_one)
    rcases hR i hi with ((h1 | h1) | h1) | ⟨r, hr, h1⟩
    · exfalso
      apply h1
      refine (hri.mul hri).key_unique ?_ (mulK_lt _ _) idK_lt
      have : y * glOf ρ ρ * y⁻¹ * (y * glOf ρ ρ * y⁻¹) = 1 := by
        calc y * glOf ρ ρ * y⁻¹ * (y * glOf ρ ρ * y⁻¹) = y * (glOf ρ ρ * glOf ρ ρ) * y⁻¹ := by
              group
          _ = 1 := by rw [hsq1, mul_one, mul_inv_cancel]
      rw [this]
      exact rep_one
    · exfalso
      rw [h1] at hri
      have e : y * glOf ρ ρ * y⁻¹ = 1 := hri.unique rep_one
      have e' : glOf ρ ρ = 1 := by
        calc glOf ρ ρ = y⁻¹ * (y * glOf ρ ρ * y⁻¹) * y := by group
          _ = 1 := by rw [e]; group
      have hfix := (hρ ρ hρ').2
      rw [fixCountF_eq, ← card_fixM_eq, hrepρ ρ hρ', e', card_fixM_one] at hfix
      norm_num at hfix
    · exfalso
      apply h1
      rw [fixCountF_eq, ← card_fixM_eq, hri, card_fixM_conj, ← hrepρ ρ hρ', card_fixM_eq,
        ← fixCountF_eq]
      exact (hρ ρ hρ').2
    · rw [← hki, h1]
      exact hr
  obtain ⟨K, hK, hKz⟩ := exists_of_chainAux hE hrepρ hfR ρs [] kss hch
    (fun _ h => absurd h List.not_mem_nil) (fun ρ h => h) y hy
    (fun _ h => absurd h List.not_mem_nil)
  set z := K⁻¹ * y with hz
  have hzρ : ∀ ρ ∈ ρs, glOf ρ ρ * z = z * glOf ρ ρ := fun ρ hρ' =>
    (hKz ρ (by simpa using hρ')).symm
  have hzt : tbarG * z = z * tbarG := by
    have hKt := hct K hK
    calc tbarG * z = tbarG * K⁻¹ * y := by rw [hz]; group
      _ = K⁻¹ * (K * tbarG) * K⁻¹ * y := by group
      _ = K⁻¹ * (tbarG * K) * K⁻¹ * y := by rw [hKt]
      _ = K⁻¹ * (tbarG * y) := by group
      _ = K⁻¹ * (y * tbarG) := by rw [hyt]
      _ = z * tbarG := by rw [hz]; group
  have hrphi : Rep phiK tbarG := rep_glOf hphi
  have hsol : ∀ c ∈ commCons ρs, mulK c.1 (keyOfMat z) = mulK (keyOfMat z) c.2 := by
    intro c hc
    simp only [commCons, List.mem_append, List.mem_map, List.mem_singleton] at hc
    rcases hc with ⟨ρ, hρ', rfl⟩ | rfl
    · exact key_eq_of_mul (hrepρ ρ hρ') (rep_keyOfMat z) (hzρ ρ hρ')
    · exact key_eq_of_mul hrphi (rep_keyOfMat z) hzt
  have hPz := hP (keyOfMat_lt _) hsol
  simp only [Bool.or_eq_true, beq_iff_eq] at hPz
  have hyKz : y = K * z := by rw [hz]; group
  rcases hPz with ((h0 | h1) | ht) | h2
  · exact absurd (h0 ▸ rep_keyOfMat z) (fun h => not_isUnit_of_rep_zero h)
  · have : z = 1 := (rep_keyOfMat z).unique (h1 ▸ rep_one)
    rw [hyKz, this, mul_one]
    exact hK
  · have : z = tbarG := (rep_keyOfMat z).unique (ht ▸ hrphi)
    rw [hyKz, this]
    exact mul_mem hK (Enum.mem_of_memK hE htC hrphi)
  · exfalso
    have h3 := (rep_keyOfMat z).mul (rep_keyOfMat z)
    rw [h2, hsq] at h3
    exact not_isUnit_of_rep_zero h3

section Hyp

variable {G : Type*} [Group G] {M : Model} {t : G} {TH W : Subgroup G}
  {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)}

theorem mem_X_of_conj [Finite G] (h : Stage2Hyp M t TH W φ)
    (hNC : ∀ y : GL12, (∀ c ∈ M.CC, y * c * y⁻¹ ∈ M.CC) → y * M.tbar = M.tbar * y → y ∈ M.CC)
    (hCt : ∀ c ∈ M.CC, c * M.tbar = M.tbar * c) {x₀ x : GL12}
    (hx₀ : ∀ c ∈ M.CC, x₀ * c * x₀⁻¹ ∈ Xof W φ) (hx : x ∈ Xof W φ)
    (hxx : x * M.tbar * x⁻¹ = x₀ * M.tbar * x₀⁻¹) : x₀ ∈ Xof W φ := by
  have hle : M.CC.map (MulAut.conj x₀).toMonoidHom ≤ M.CC.map (MulAut.conj x).toMonoidHom := by
    rintro _ ⟨c, hc, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    have hmem : x⁻¹ * (x₀ * c * x₀⁻¹) * x ∈ Xof W φ :=
      (Xof W φ).mul_mem ((Xof W φ).mul_mem ((Xof W φ).inv_mem hx) (hx₀ c hc)) hx
    have hc' := hCt c hc
    have h1 : (x₀ * c * x₀⁻¹) * (x₀ * M.tbar * x₀⁻¹) =
        (x₀ * M.tbar * x₀⁻¹) * (x₀ * c * x₀⁻¹) := by
      calc (x₀ * c * x₀⁻¹) * (x₀ * M.tbar * x₀⁻¹) = x₀ * (c * M.tbar) * x₀⁻¹ := by group
        _ = x₀ * (M.tbar * c) * x₀⁻¹ := by rw [hc']
        _ = (x₀ * M.tbar * x₀⁻¹) * (x₀ * c * x₀⁻¹) := by group
    rw [← hxx] at h1
    have hcom : x⁻¹ * (x₀ * c * x₀⁻¹) * x * M.tbar = M.tbar * (x⁻¹ * (x₀ * c * x₀⁻¹) * x) := by
      calc x⁻¹ * (x₀ * c * x₀⁻¹) * x * M.tbar =
          x⁻¹ * ((x₀ * c * x₀⁻¹) * (x * M.tbar * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * M.tbar * x⁻¹) * (x₀ * c * x₀⁻¹)) * x := by rw [h1]
        _ = M.tbar * (x⁻¹ * (x₀ * c * x₀⁻¹) * x) := by group
    refine ⟨_, h.mem_CC_of_commute hmem hcom, ?_⟩
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
    group
  have hc0 : Nat.card (M.CC.map (MulAut.conj x₀).toMonoidHom) = Nat.card M.CC :=
    card_map_of_injective (MulAut.conj x₀).injective
  have hc1 : Nat.card (M.CC.map (MulAut.conj x).toMonoidHom) = Nat.card M.CC :=
    card_map_of_injective (MulAut.conj x).injective
  have heq : M.CC.map (MulAut.conj x₀).toMonoidHom = M.CC.map (MulAut.conj x).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hc0, hc1])
  have hyC : x₀⁻¹ * x ∈ M.CC := by
    refine hNC _ (fun c hc => ?_) ?_
    · have h1 : x * c * x⁻¹ ∈ M.CC.map (MulAut.conj x₀).toMonoidHom := by
        rw [heq]
        exact ⟨c, hc, rfl⟩
      obtain ⟨c', hc', e⟩ := h1
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at e
      have : x₀⁻¹ * x * c * (x₀⁻¹ * x)⁻¹ = c' := by
        calc x₀⁻¹ * x * c * (x₀⁻¹ * x)⁻¹ = x₀⁻¹ * (x * c * x⁻¹) * x₀ := by group
          _ = x₀⁻¹ * (x₀ * c' * x₀⁻¹) * x₀ := by rw [e]
          _ = c' := by group
      rw [this]
      exact hc'
    · calc x₀⁻¹ * x * M.tbar = x₀⁻¹ * (x * M.tbar * x⁻¹) * x := by group
        _ = x₀⁻¹ * (x₀ * M.tbar * x₀⁻¹) * x := by rw [hxx]
        _ = M.tbar * (x₀⁻¹ * x) := by group
  have e : x₀ = x * (x₀⁻¹ * x)⁻¹ := by group
  rw [e]
  exact (Xof W φ).mul_mem hx ((Xof W φ).inv_mem (h.CC_le_X hyC))

theorem not_conj_of_pow (h : Stage2Hyp M t TH W φ) {τ z : GL12} {p q : ℕ}
    (hzX : z ∈ Xof W φ) (hzτ : z * τ = τ * z) (hzp : z ^ p = 1) (hzq : z ^ q ≠ 1)
    (hno : ∀ c ∈ M.CC, c ^ p = 1 → c ^ q = 1) : ∀ x ∈ Xof W φ, x * M.tbar * x⁻¹ ≠ τ := by
  intro x hx hxt
  have hwX : x⁻¹ * z * x ∈ Xof W φ :=
    (Xof W φ).mul_mem ((Xof W φ).mul_mem ((Xof W φ).inv_mem hx) hzX) hx
  have hwt : x⁻¹ * z * x * M.tbar = M.tbar * (x⁻¹ * z * x) := by
    have e : M.tbar = x⁻¹ * τ * x := by rw [← hxt]; group
    rw [e]
    calc x⁻¹ * z * x * (x⁻¹ * τ * x) = x⁻¹ * (z * τ) * x := by group
      _ = x⁻¹ * (τ * z) * x := by rw [hzτ]
      _ = x⁻¹ * τ * x * (x⁻¹ * z * x) := by group
  have hwC := h.mem_CC_of_commute hwX hwt
  have hpow : ∀ n : ℕ, (x⁻¹ * z * x) ^ n = x⁻¹ * z ^ n * x := fun n => by
    have e : x⁻¹ * z * x = x⁻¹ * z * x⁻¹⁻¹ := by rw [inv_inv]
    rw [e, conj_pow, inv_inv]
  have h1 := hno _ hwC (by rw [hpow, hzp, mul_one, inv_mul_cancel])
  rw [hpow] at h1
  apply hzq
  calc z ^ q = x * (x⁻¹ * z ^ q * x) * x⁻¹ := by group
    _ = 1 := by rw [h1]; group

end Hyp

end CFSG.EvenSmallLie.OmegaEight.N3Split
