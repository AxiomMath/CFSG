module

public import CFSG.GH74.QTGen4.Recog.Ku.RStructD

public section

namespace CFSG.GH74.QTGen4.Ku

def detw {F : Type} [Field F] (w x : Fin 2 → F) : F := w 0 * x 1 - w 1 * x 0

theorem detw_add {F : Type} [Field F] (w x y : Fin 2 → F) :
    detw w (x + y) = detw w x + detw w y := by
  simp only [detw, Pi.add_apply]
  ring

theorem detw_smul {F : Type} [Field F] (w : Fin 2 → F) (c : F) (x : Fin 2 → F) :
    detw w (c • x) = c * detw w x := by
  simp only [detw, Pi.smul_apply, smul_eq_mul]
  ring

theorem detw_scale {F : Type} [Field F] {D : Matrix (Fin 2) (Fin 2) F}
    (hdet : D 0 0 * D 1 1 - D 0 1 * D 1 0 = 1) {a : F} {w : Fin 2 → F}
    (hw : D.mulVec w = a • w) (x : Fin 2 → F) :
    a * detw w (D.mulVec x) = detw w x := by
  have h0 := congrFun hw 0
  have h1 := congrFun hw 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at h0 h1
  have e0 : a * w 0 = D 0 0 * w 0 + D 0 1 * w 1 := by linear_combination -h0
  have e1 : a * w 1 = D 1 0 * w 0 + D 1 1 * w 1 := by linear_combination -h1
  have key := det_scale_of_fix (D := D) hdet e0 e1 (x 0) (x 1)
  simp only [detw, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination key

theorem detw_eq_zero_smul {F : Type} [Field F] {w x : Fin 2 → F} (hw : w ≠ 0)
    (hx : detw w x = 0) : ∃ c : F, x = c • w := by
  unfold detw at hx
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      by_contra h1'
      apply hw
      funext i
      fin_cases i
      · exact h0
      · exact h1'
    have hx0' : x 0 = 0 := by
      rw [h0] at hx
      have h2 : w 1 * x 0 = 0 := by linear_combination -hx
      exact (mul_eq_zero.mp h2).resolve_left h1
    refine ⟨x 1 / w 1, ?_⟩
    funext i
    fin_cases i
    · simp [h0, hx0']
    · simpa using (div_mul_cancel₀ (x 1) h1).symm
  · refine ⟨x 0 / w 0, ?_⟩
    funext i
    fin_cases i
    · simpa using (div_mul_cancel₀ (x 0) h0).symm
    · show x 1 = x 0 / w 0 * w 1
      rw [div_mul_eq_mul_div, eq_div_iff h0]
      linear_combination hx

theorem detw_self {F : Type} [Field F] (w : Fin 2 → F) : detw w w = 0 := by
  unfold detw
  ring

theorem descend_form {Γ F : Type} [Group Γ] [AddCommGroup F] (V : Subgroup Γ) (B : Γ → Γ → F)
    (hl : ∀ x x' y, B (x * x') y = B x y + B x' y)
    (hr : ∀ x y y', B x (y * y') = B x y + B x y')
    (hVl : ∀ v ∈ V, ∀ y, B v y = 0) (hVr : ∀ v ∈ V, ∀ x, B x v = 0) :
    ∃ B' : Γ ⧸ V → Γ ⧸ V → F, ∀ x y : Γ, B' (QuotientGroup.mk x) (QuotientGroup.mk y) = B x y := by
  have hlv : ∀ a a' b : Γ, a⁻¹ * a' ∈ V → B a' b = B a b := by
    intro a a' b hv
    have e : a' = a * (a⁻¹ * a') := (mul_inv_cancel_left a a').symm
    rw [e, hl, hVl _ hv, add_zero]
  have hrv : ∀ a b b' : Γ, b⁻¹ * b' ∈ V → B a b' = B a b := by
    intro a b b' hv
    have e : b' = b * (b⁻¹ * b') := (mul_inv_cancel_left b b').symm
    rw [e, hr, hVr _ hv, add_zero]
  refine ⟨Quotient.lift₂ B (fun a b a' b' ha hb => ?_), fun x y => rfl⟩
  have ha' : a⁻¹ * a' ∈ V := QuotientGroup.leftRel_apply.mp ha
  have hb' : b⁻¹ * b' ∈ V := QuotientGroup.leftRel_apply.mp hb
  calc B a b = B a' b := (hlv a a' b ha').symm
    _ = B a' b' := (hrv a' b b' hb').symm

theorem cover_of_card {A : Type} [Group A] (N : A →* A) (hN3 : ∀ x, N (N (N x)) = x)
    (hfix : ∀ x, N x = x → x = 1) (hcard : Nat.card A = 4) (x : A) (hx : x ≠ 1) :
    ∀ y : A, y = 1 ∨ y = x ∨ y = N x ∨ y = N (N x) := by
  have n01 : (1 : A) ≠ x := fun e => hx e.symm
  have n02 : (1 : A) ≠ N x := fun e => by
    apply hx
    rw [← hN3 x, ← e, map_one, map_one]
  have n03 : (1 : A) ≠ N (N x) := fun e => by
    apply hx
    rw [← hN3 x, ← e, map_one]
  have n12 : x ≠ N x := fun e => hx (hfix x e.symm)
  have n13 : x ≠ N (N x) := fun e => by
    apply hx
    apply hfix
    have h1 : N (N (N x)) = N x := by rw [← e]
    rw [hN3] at h1
    exact h1.symm
  have n23 : N x ≠ N (N x) := fun e => by
    have h1 : N (N x) = x := by
      have h2 := congrArg N e.symm
      rw [hN3] at h2
      exact h2.symm
    exact hx (hfix x (e.trans h1))
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have := Fintype.ofFinite A
  have hcardF : Fintype.card A = 4 := by rw [← Nat.card_eq_fintype_card, hcard]
  have hinj : Function.Injective (![1, x, N x, N (N x)] : Fin 4 → A) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd hij n01
      | exact absurd hij n02
      | exact absurd hij n03
      | exact absurd hij n12
      | exact absurd hij n13
      | exact absurd hij n23
      | exact absurd hij.symm n01
      | exact absurd hij.symm n02
      | exact absurd hij.symm n03
      | exact absurd hij.symm n12
      | exact absurd hij.symm n13
      | exact absurd hij.symm n23
  have hbij : Function.Bijective (![1, x, N x, N (N x)] : Fin 4 → A) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by rw [Fintype.card_fin, hcardF]⟩
  intro y
  obtain ⟨i, hi⟩ := hbij.2 y
  fin_cases i
  · exact Or.inl hi.symm
  · exact Or.inr (Or.inl hi.symm)
  · exact Or.inr (Or.inr (Or.inl hi.symm))
  · exact Or.inr (Or.inr (Or.inr hi.symm))

section Bridge

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem detw_kuFix (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K} (hw0 : w0 ≠ 0)
    (hfix : ∀ g : Subgroup.normalizer (pCoreOf 2 M : Set G), (g : G) ∈ kuR T M →
      h.mNat.data.conj g w0 = w0)
    {x : Fin 2 → h.mNat.data.K} (hx : x ∈ kuFix h.mNat.data (kuR_le (T := T) (M := M))) :
    detw w0 x = 0 := by
  have hw0mem : w0 ∈ kuFix h.mNat.data (kuR_le (T := T) (M := M)) := mem_kuFix.mpr hfix
  have hfin := h.finrank_kuFix
  have hnz : (⟨w0, hw0mem⟩ : kuFix h.mNat.data (kuR_le (T := T) (M := M))) ≠ 0 := by
    intro e
    apply hw0
    exact congrArg Subtype.val e
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hnz).mp hfin ⟨x, hx⟩
  have hcx : x = c • w0 := congrArg Subtype.val hc.symm
  rw [hcx, detw_smul, detw_self, mul_zero]

theorem mem_kuV2_iff_detw (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K} (hw0 : w0 ≠ 0)
    (hfix : ∀ g : Subgroup.normalizer (pCoreOf 2 M : Set G), (g : G) ∈ kuR T M →
      h.mNat.data.conj g w0 = w0)
    (v : ↥(pCoreOf 2 M)) :
    (v : G) ∈ kuV2 T M ↔ detw w0 (Multiplicative.toAdd (h.mNat.data.E v)) = 0 := by
  constructor
  · intro hv
    exact h.detw_kuFix hw0 hfix ((h.mem_kuV2_iff_fix v).mp hv)
  · intro hv
    obtain ⟨c, hc⟩ := detw_eq_zero_smul hw0 hv
    refine (h.mem_kuV2_iff_fix v).mpr ?_
    rw [hc, mem_kuFix]
    intro g hg
    obtain ⟨A, hA⟩ := h.mNat.data.exists_matrix_of_mem g (kuR_le hg)
    rw [hA, Matrix.mulVec_smul, ← hA, hfix g hg]

theorem detw_conj (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K}
    (hfix : ∀ g : Subgroup.normalizer (pCoreOf 2 M : Set G), (g : G) ∈ kuR T M →
      h.mNat.data.conj g w0 = w0)
    {r : G} (hr : r ∈ kuR T M) (v c : ↥(pCoreOf 2 M)) (hc : (c : G) = r * (v : G) * r⁻¹) :
    detw w0 (Multiplicative.toAdd (h.mNat.data.E c)) =
      detw w0 (Multiplicative.toAdd (h.mNat.data.E v)) := by
  have hrN := h.kuR_normalizer hr
  obtain ⟨A, hA⟩ := h.mNat.data.exists_matrix_of_mem ⟨r, hrN⟩ (kuR_le hr)
  have hAw : (A : Matrix (Fin 2) (Fin 2) h.mNat.data.K).mulVec w0 = w0 := by
    rw [← hA]
    exact hfix ⟨r, hrN⟩ hr
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  have key := detw_scale (a := 1) (w := w0) hdet (by rw [hAw, one_smul])
    (Multiplicative.toAdd (h.mNat.data.E v))
  rw [one_mul] at key
  have hcv : c = conjAct (pCoreOf 2 M) ⟨r, hrN⟩ v := Subtype.ext (by
    rw [conjAct_apply_coe']
    exact hc)
  have e : Multiplicative.toAdd (h.mNat.data.E c) =
      (A : Matrix (Fin 2) (Fin 2) h.mNat.data.K).mulVec
        (Multiplicative.toAdd (h.mNat.data.E v)) := by
    rw [← hA, h.mNat.data.conj_apply ⟨r, hrN⟩ v, hcv]
  rw [e]
  exact key

@[expose] noncomputable def Bf (h : KuHyp G T M H P z) (w0 : Fin 2 → h.mNat.data.K) {r s : G} (hr : r ∈ kuR T M)
    (hs : s ∈ kuR T M) : h.mNat.data.K :=
  detw w0 (Multiplicative.toAdd (h.mNat.data.E ⟨r * s * r⁻¹ * s⁻¹, h.comm_mem_pCore hr hs⟩))

theorem Bf_mul_left (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K}
    (hfix : ∀ g : Subgroup.normalizer (pCoreOf 2 M : Set G), (g : G) ∈ kuR T M →
      h.mNat.data.conj g w0 = w0)
    {r r' s : G} (hr : r ∈ kuR T M) (hr' : r' ∈ kuR T M) (hs : s ∈ kuR T M) :
    Bf h w0 ((kuR T M).mul_mem hr hr') hs = Bf h w0 hr hs + Bf h w0 hr' hs := by
  have hrN := h.kuR_normalizer hr
  have hc := h.comm_mem_pCore hr' hs
  have hu : r * (r' * s * r'⁻¹ * s⁻¹) * r⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.mp hrN _).mp hc
  have hsplit : (⟨r * r' * s * (r * r')⁻¹ * s⁻¹, h.comm_mem_pCore ((kuR T M).mul_mem hr hr') hs⟩ :
      ↥(pCoreOf 2 M)) =
      ⟨r * (r' * s * r'⁻¹ * s⁻¹) * r⁻¹, hu⟩ * ⟨r * s * r⁻¹ * s⁻¹, h.comm_mem_pCore hr hs⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  have hcj := detw_conj h hfix hr ⟨r' * s * r'⁻¹ * s⁻¹, hc⟩ ⟨r * (r' * s * r'⁻¹ * s⁻¹) * r⁻¹, hu⟩ rfl
  unfold Bf
  rw [hsplit, map_mul, toAdd_mul, detw_add, hcj]
  ring

theorem Bf_mul_right (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K}
    (hfix : ∀ g : Subgroup.normalizer (pCoreOf 2 M : Set G), (g : G) ∈ kuR T M →
      h.mNat.data.conj g w0 = w0)
    {r s s' : G} (hr : r ∈ kuR T M) (hs : s ∈ kuR T M) (hs' : s' ∈ kuR T M) :
    Bf h w0 hr ((kuR T M).mul_mem hs hs') = Bf h w0 hr hs + Bf h w0 hr hs' := by
  have hsN := h.kuR_normalizer hs
  have hc := h.comm_mem_pCore hr hs'
  have hu : s * (r * s' * r⁻¹ * s'⁻¹) * s⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.mp hsN _).mp hc
  have hsplit : (⟨r * (s * s') * r⁻¹ * (s * s')⁻¹, h.comm_mem_pCore hr ((kuR T M).mul_mem hs hs')⟩ :
      ↥(pCoreOf 2 M)) =
      ⟨r * s * r⁻¹ * s⁻¹, h.comm_mem_pCore hr hs⟩ * ⟨s * (r * s' * r⁻¹ * s'⁻¹) * s⁻¹, hu⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  have hcj := detw_conj h hfix hs ⟨r * s' * r⁻¹ * s'⁻¹, hc⟩ ⟨s * (r * s' * r⁻¹ * s'⁻¹) * s⁻¹, hu⟩ rfl
  unfold Bf
  rw [hsplit, map_mul, toAdd_mul, detw_add, hcj]

theorem Bf_self (h : KuHyp G T M H P z) (w0 : Fin 2 → h.mNat.data.K) {r : G}
    (hr : r ∈ kuR T M) : Bf h w0 hr hr = 0 := by
  unfold Bf
  have e : (⟨r * r * r⁻¹ * r⁻¹, h.comm_mem_pCore hr hr⟩ : ↥(pCoreOf 2 M)) = 1 :=
    Subtype.ext (by show r * r * r⁻¹ * r⁻¹ = 1; group)
  rw [e, map_one, toAdd_one]
  simp [detw]

theorem Bf_V_left (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K} (hw0 : w0 ≠ 0)
    (hfix : ∀ g : Subgroup.normalizer (pCoreOf 2 M : Set G), (g : G) ∈ kuR T M →
      h.mNat.data.conj g w0 = w0)
    (v : ↥(pCoreOf 2 M)) {s : G} (hs : s ∈ kuR T M) :
    Bf h w0 (h.pCore_le_kuR v.2) hs = 0 := by
  have hc : (v : G) * s * (v : G)⁻¹ * s⁻¹ ∈ kuV2 T M := by
    have := (kuV2 T M).inv_mem (h.comm_mem_kuV2_of_V hs v)
    convert this using 1
    group
  unfold Bf
  exact (h.mem_kuV2_iff_detw hw0 hfix
    ⟨(v : G) * s * (v : G)⁻¹ * s⁻¹, h.comm_mem_pCore (h.pCore_le_kuR v.2) hs⟩).mp hc

theorem Bf_V_right (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K} (hw0 : w0 ≠ 0)
    (hfix : ∀ g : Subgroup.normalizer (pCoreOf 2 M : Set G), (g : G) ∈ kuR T M →
      h.mNat.data.conj g w0 = w0)
    {r : G} (hr : r ∈ kuR T M) (v : ↥(pCoreOf 2 M)) :
    Bf h w0 hr (h.pCore_le_kuR v.2) = 0 := by
  unfold Bf
  exact (h.mem_kuV2_iff_detw hw0 hfix
    ⟨r * (v : G) * r⁻¹ * (v : G)⁻¹, h.comm_mem_pCore hr (h.pCore_le_kuR v.2)⟩).mp
    (h.comm_mem_kuV2_of_V hr v)

theorem conj_y_eq_smul (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K} (hw0 : w0 ≠ 0)
    (hfix : ∀ g : Subgroup.normalizer (pCoreOf 2 M : Set G), (g : G) ∈ kuR T M →
      h.mNat.data.conj g w0 = w0)
    {y : G} (hyR : y ∈ Subgroup.normalizer (kuR T M : Set G))
    (hyV : y ∈ Subgroup.normalizer (pCoreOf 2 M : Set G)) :
    ∃ a : h.mNat.data.K, h.mNat.data.conj ⟨y, hyV⟩ w0 = a • w0 := by
  have hw0mem : w0 ∈ kuFix h.mNat.data (kuR_le (T := T) (M := M)) := mem_kuFix.mpr hfix
  have hfin := h.finrank_kuFix
  have hnz : (⟨w0, hw0mem⟩ : kuFix h.mNat.data (kuR_le (T := T) (M := M))) ≠ 0 := by
    intro e
    apply hw0
    exact congrArg Subtype.val e
  have hu : h.mNat.data.conj ⟨y, hyV⟩ w0 ∈ kuFix h.mNat.data (kuR_le (T := T) (M := M)) := by
    rw [mem_kuFix]
    intro g hg
    have hk : y⁻¹ * (g : G) * y ∈ kuR T M := (Subgroup.mem_normalizer_iff.mp hyR _).mpr (by
      convert hg using 1
      group)
    have e1 : h.mNat.data.conj g (h.mNat.data.conj ⟨y, hyV⟩ w0) =
        h.mNat.data.conj ⟨y, hyV⟩ (h.mNat.data.conj ⟨y⁻¹ * (g : G) * y, h.kuR_normalizer hk⟩ w0) := by
      have hm : g * (⟨y, hyV⟩ : ↥(Subgroup.normalizer (pCoreOf 2 M : Set G))) =
          (⟨y, hyV⟩ : ↥(Subgroup.normalizer (pCoreOf 2 M : Set G))) *
            ⟨y⁻¹ * (g : G) * y, h.kuR_normalizer hk⟩ :=
        Subtype.ext (by show (g : G) * y = y * (y⁻¹ * (g : G) * y); group)
      rw [← h.mNat.data.conj_mul, ← h.mNat.data.conj_mul, hm]
    rw [e1, hfix ⟨y⁻¹ * (g : G) * y, h.kuR_normalizer hk⟩ hk]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hnz).mp hfin ⟨_, hu⟩
  exact ⟨c, congrArg Subtype.val hc.symm⟩

theorem a_ne_one (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K} (hw0 : w0 ≠ 0)
    (hfix : ∀ g : Subgroup.normalizer (pCoreOf 2 M : Set G), (g : G) ∈ kuR T M →
      h.mNat.data.conj g w0 = w0)
    {y : G} (hyL : y ∈ oTwoUpper M) (hyV : y ∈ Subgroup.normalizer (pCoreOf 2 M : Set G))
    (hK : ∀ v ∈ kuV2 T M, y * v * y⁻¹ = v → v = 1)
    {a : h.mNat.data.K} (hA : h.mNat.data.conj ⟨y, hyV⟩ w0 = a • w0) : a ≠ 1 := by
  intro ha
  obtain ⟨A, hAeq⟩ := h.mNat.data.exists_matrix_of_mem ⟨y, hyV⟩ hyL
  have : Nontrivial ↥(kuV2 T M) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h.card_kuV2]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥(kuV2 T M))
  have hxV : (x : G) ∈ pCoreOf 2 M := x.2.1
  have hdet0 : detw w0 (Multiplicative.toAdd (h.mNat.data.E ⟨x, hxV⟩)) = 0 :=
    (h.mem_kuV2_iff_detw hw0 hfix ⟨x, hxV⟩).mp x.2
  obtain ⟨c, hc⟩ := detw_eq_zero_smul hw0 hdet0
  have hw : (A : Matrix (Fin 2) (Fin 2) h.mNat.data.K).mulVec w0 = w0 := by
    rw [← hAeq, hA, ha, one_smul]
  have hL : h.mNat.data.conj ⟨y, hyV⟩ (Multiplicative.toAdd (h.mNat.data.E ⟨x, hxV⟩)) =
      Multiplicative.toAdd (h.mNat.data.E ⟨x, hxV⟩) := by
    rw [hc, hAeq, Matrix.mulVec_smul, hw]
  have hcv := h.mNat.data.conj_apply ⟨y, hyV⟩ ⟨x, hxV⟩
  have hEq := hcv.symm.trans hL
  have hEq2 : conjAct (pCoreOf 2 M) ⟨y, hyV⟩ ⟨x, hxV⟩ = ⟨x, hxV⟩ :=
    h.mNat.data.E.injective (Multiplicative.toAdd.injective hEq)
  have hK' : y * (x : G) * y⁻¹ = x := by
    have := congrArg Subtype.val hEq2
    rw [conjAct_apply_coe'] at this
    exact this
  apply hx
  exact Subtype.ext ((hK _ x.2 hK').trans (by simp))

theorem Bf_conj_y (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K}
    {y : G} (hyL : y ∈ oTwoUpper M) (hyR : y ∈ Subgroup.normalizer (kuR T M : Set G))
    (hyV : y ∈ Subgroup.normalizer (pCoreOf 2 M : Set G)) {a : h.mNat.data.K}
    (hA : h.mNat.data.conj ⟨y, hyV⟩ w0 = a • w0) {r s : G} (hr : r ∈ kuR T M)
    (hs : s ∈ kuR T M) :
    a * Bf h w0 ((Subgroup.mem_normalizer_iff.mp hyR r).mp hr)
      ((Subgroup.mem_normalizer_iff.mp hyR s).mp hs) = Bf h w0 hr hs := by
  obtain ⟨A, hAeq⟩ := h.mNat.data.exists_matrix_of_mem ⟨y, hyV⟩ hyL
  have hw' : (A : Matrix (Fin 2) (Fin 2) h.mNat.data.K).mulVec w0 = a • w0 := by
    rw [← hAeq, hA]
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  have hc' : (⟨y * r * y⁻¹ * (y * s * y⁻¹) * (y * r * y⁻¹)⁻¹ * (y * s * y⁻¹)⁻¹,
      h.comm_mem_pCore ((Subgroup.mem_normalizer_iff.mp hyR r).mp hr)
        ((Subgroup.mem_normalizer_iff.mp hyR s).mp hs)⟩ : ↥(pCoreOf 2 M)) =
      conjAct (pCoreOf 2 M) ⟨y, hyV⟩ ⟨r * s * r⁻¹ * s⁻¹, h.comm_mem_pCore hr hs⟩ :=
    Subtype.ext (by
      rw [conjAct_apply_coe']
      show _ = y * (r * s * r⁻¹ * s⁻¹) * y⁻¹
      group)
  have hcv := h.mNat.data.conj_apply ⟨y, hyV⟩ ⟨r * s * r⁻¹ * s⁻¹, h.comm_mem_pCore hr hs⟩
  rw [hAeq] at hcv
  unfold Bf
  rw [hc', ← hcv]
  exact detw_scale hdet hw' _

theorem card_quot_kuR (h : KuHyp G T M H P z) :
    Nat.card (↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) = 4 := by
  have hle : pCoreOf 2 M ≤ kuR T M := h.pCore_le_kuR
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ((pCoreOf 2 M).subgroupOf (kuR T M))
  have hV : Nat.card ((pCoreOf 2 M).subgroupOf (kuR T M)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, h.vCard]
  rw [h.card_kuR, hV] at hcard
  omega

theorem V_subgroupOf_normal (h : KuHyp G T M H P z) :
    ((pCoreOf 2 M).subgroupOf (kuR T M)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.pCore_le_kuR).mpr
    (fun _ hx => h.kuR_normalizer hx)

theorem quot_comm_kuR (h : KuHyp G T M H P z)
    [((pCoreOf 2 M).subgroupOf (kuR T M)).Normal] (a b : ↥(kuR T M)) :
    (QuotientGroup.mk a : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) *
        (QuotientGroup.mk b : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) =
      (QuotientGroup.mk b : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) *
        (QuotientGroup.mk a : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hc := h.comm_mem_pCore ((kuR T M).inv_mem b.2) ((kuR T M).inv_mem a.2)
  have hgoal : (((a * b)⁻¹ * (b * a) : ↥(kuR T M)) : G) =
      (b : G)⁻¹ * (a : G)⁻¹ * (b : G)⁻¹⁻¹ * (a : G)⁻¹⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hgoal]
  exact hc

def conjR {y : G} (hyR : y ∈ Subgroup.normalizer (kuR T M : Set G)) :
    ↥(kuR T M) →* ↥(kuR T M) where
  toFun x := ⟨y * (x : G) * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyR (x : G)).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x x' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem V_le_comap_conjR (h : KuHyp G T M H P z) {y : G} (hyL : y ∈ oTwoUpper M)
    (hyR : y ∈ Subgroup.normalizer (kuR T M : Set G)) :
    (pCoreOf 2 M).subgroupOf (kuR T M) ≤
      ((pCoreOf 2 M).subgroupOf (kuR T M)).comap (conjR hyR) := by
  intro x hx
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  exact (Subgroup.mem_normalizer_iff.mp (h.oTwoUpper_le_normalizer_V hyL) (x : G)).mp
    (Subgroup.mem_subgroupOf.mp hx)

def Nq (h : KuHyp G T M H P z) [((pCoreOf 2 M).subgroupOf (kuR T M)).Normal] {y : G}
    (hyL : y ∈ oTwoUpper M) (hyR : y ∈ Subgroup.normalizer (kuR T M : Set G)) :
    (↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) →*
      (↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) :=
  QuotientGroup.map ((pCoreOf 2 M).subgroupOf (kuR T M)) ((pCoreOf 2 M).subgroupOf (kuR T M))
    (conjR hyR) (h.V_le_comap_conjR hyL hyR)

theorem conjR_pow3 {y : G} (hyR : y ∈ Subgroup.normalizer (kuR T M : Set G)) (hy3 : y ^ 3 = 1)
    (a : ↥(kuR T M)) : conjR hyR (conjR hyR (conjR hyR a)) = a := by
  apply Subtype.ext
  show y * (y * (y * (a : G) * y⁻¹) * y⁻¹) * y⁻¹ = a
  have h3 : y * y * y = 1 := (pow_three' y).symm.trans hy3
  have e : y * (y * (y * (a : G) * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * a * (y * y * y)⁻¹ := by
    group
  rw [e, h3, inv_one, mul_one, one_mul]

theorem Nq_pow3 (h : KuHyp G T M H P z) [((pCoreOf 2 M).subgroupOf (kuR T M)).Normal] {y : G}
    (hyL : y ∈ oTwoUpper M) (hyR : y ∈ Subgroup.normalizer (kuR T M : Set G))
    (hy3 : y ^ 3 = 1) (x : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) :
    h.Nq hyL hyR (h.Nq hyL hyR (h.Nq hyL hyR x)) = x := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [Nq, QuotientGroup.map_mk]
  rw [conjR_pow3 hyR hy3 a]

theorem Nq_fix (h : KuHyp G T M H P z) [((pCoreOf 2 M).subgroupOf (kuR T M)).Normal] {y : G}
    (hyL : y ∈ oTwoUpper M) (hyR : y ∈ Subgroup.normalizer (kuR T M : Set G))
    (hcl : ∀ r ∈ kuR T M, y * r * y⁻¹ * r⁻¹ ∈ pCoreOf 2 M → r ∈ pCoreOf 2 M)
    (x : ↥(kuR T M) ⧸ (pCoreOf 2 M).subgroupOf (kuR T M)) (hx : h.Nq hyL hyR x = x) : x = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [Nq, QuotientGroup.map_mk] at hx
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hx
  have hx' : (y * (a : G) * y⁻¹)⁻¹ * (a : G) ∈ pCoreOf 2 M := hx
  have hm := (Subgroup.mem_normalizer_iff.mp (h.kuR_normalizer a.2) _).mp hx'
  have e : (a : G) * ((y * (a : G) * y⁻¹)⁻¹ * (a : G)) * (a : G)⁻¹ =
      (y * (a : G) * y⁻¹ * (a : G)⁻¹)⁻¹ := by
    group
  rw [e] at hm
  have hc := (pCoreOf 2 M).inv_mem hm
  rw [inv_inv] at hc
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hcl a a.2 hc

theorem Nq_mk (h : KuHyp G T M H P z) [((pCoreOf 2 M).subgroupOf (kuR T M)).Normal] {y : G}
    (hyL : y ∈ oTwoUpper M) (hyR : y ∈ Subgroup.normalizer (kuR T M : Set G))
    (p : ↥(kuR T M)) :
    h.Nq hyL hyR (QuotientGroup.mk p) = QuotientGroup.mk (conjR hyR p) := by
  simp only [Nq, QuotientGroup.map_mk]

theorem a_ne_zero (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K} (hw0 : w0 ≠ 0)
    {y : G} (hyL : y ∈ oTwoUpper M) (hyV : y ∈ Subgroup.normalizer (pCoreOf 2 M : Set G))
    {a : h.mNat.data.K} (hA : h.mNat.data.conj ⟨y, hyV⟩ w0 = a • w0) : a ≠ 0 := by
  intro ha
  obtain ⟨A, hAeq⟩ := h.mNat.data.exists_matrix_of_mem ⟨y, hyV⟩ hyL
  have hw' : (A : Matrix (Fin 2) (Fin 2) h.mNat.data.K).mulVec w0 = a • w0 := by
    rw [← hAeq, hA]
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  have key : ∀ x, detw w0 x = 0 := fun x => by
    have := detw_scale hdet hw' x
    rw [ha, zero_mul] at this
    exact this.symm
  have e1 : w0 0 = 0 := by simpa [detw] using key ![0, 1]
  have e2 : w0 1 = 0 := by simpa [detw] using key ![1, 0]
  apply hw0
  funext i
  fin_cases i <;> simp [e1, e2]

@[expose] noncomputable def Bq (h : KuHyp G T M H P z) (w0 : Fin 2 → h.mNat.data.K) (p q : ↥(kuR T M)) :
    h.mNat.data.K :=
  Bf h w0 p.2 q.2

theorem Bq_def (h : KuHyp G T M H P z) (w0 : Fin 2 → h.mNat.data.K) (p q : ↥(kuR T M)) :
    Bq h w0 p q = Bf h w0 p.2 q.2 := rfl

theorem Bq_eq_detw (h : KuHyp G T M H P z) (w0 : Fin 2 → h.mNat.data.K) {r s : G}
    (hr : r ∈ kuR T M) (hs : s ∈ kuR T M) :
    Bq h w0 ⟨r, hr⟩ ⟨s, hs⟩ = detw w0 (Multiplicative.toAdd
      (h.mNat.data.E ⟨r * s * r⁻¹ * s⁻¹, h.comm_mem_pCore hr hs⟩)) := rfl

theorem Bq_conj (h : KuHyp G T M H P z) {w0 : Fin 2 → h.mNat.data.K} {y : G}
    (hyL : y ∈ oTwoUpper M) (hyR : y ∈ Subgroup.normalizer (kuR T M : Set G))
    (hyV : y ∈ Subgroup.normalizer (pCoreOf 2 M : Set G)) {a : h.mNat.data.K} (ha0 : a ≠ 0)
    (hA : h.mNat.data.conj ⟨y, hyV⟩ w0 = a • w0) (p q : ↥(kuR T M)) :
    Bq h w0 (conjR hyR p) (conjR hyR q) = a⁻¹ * Bq h w0 p q := by
  have key := Bf_conj_y h hyL hyR hyV hA p.2 q.2
  calc Bq h w0 (conjR hyR p) (conjR hyR q)
      = a⁻¹ * (a * Bq h w0 (conjR hyR p) (conjR hyR q)) := by
        rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    _ = a⁻¹ * Bq h w0 p q := by
        congr 1

end KuHyp

end Bridge

end CFSG.GH74.QTGen4.Ku

end
