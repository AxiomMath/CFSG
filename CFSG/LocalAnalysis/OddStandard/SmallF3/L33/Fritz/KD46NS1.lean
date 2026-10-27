module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NInv
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NS1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NQ0T

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable {I : Inst S} {H : Hyp S R}

namespace Data6

variable (D : I.Data6 H)

theorem u_sq : D.u ^ 2 = 1 := by
  rcases D.u_eq with h | h <;> rw [h]
  · exact I.ui_sq
  · have hc : t * I.ui = I.ui * t := ((comm_tE S) I.ui_mem_TE).symm
    rw [(Commute.mul_pow hc 2), (t_sq' (A := A)), I.ui_sq, one_mul]

theorem u_not_mem_Q₁ : D.u ∉ D.Q₁ := by
  intro h
  have hK : D.u ∈ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)) := (mem_inf.mp h).2
  rw [I.oddTwoCoreIn_eq H] at hK
  obtain ⟨n, hn, hn'⟩ := hK
  have hn'' : n = ⟨D.u, D.u_mat.mem⟩ := Subtype.ext hn'
  subst hn''
  apply xCols_transl_ne
  intro j
  have h1 : ∀ j, I.blockHom H ⟨D.u, D.u_mat.mem⟩ j = j + I.blockHom H ⟨D.u, D.u_mat.mem⟩ 0 := hn
  have hcols : (fun i => I.μ ⟨D.u, D.u_mat.mem⟩ (bas i)) = xCols := funext D.u_mat.2
  have := h1 j
  rwa [I.blockHom_apply, I.blockHom_apply, I.μ_eq_lin, I.μ_eq_lin _ (pt 0), hcols] at this

variable (Rl : D.Rel)

include Rl in
theorem S₁_eq : D.S₁ = I.E ⊔ zpowers D.v ⊔ zpowers D.w₁ ⊔ zpowers D.w₂ ⊔ zpowers D.u := by
  rw [← D.Q₁_eq Rl]
  have huN : D.u ∈ normalizer (D.Q₁ : Set X) := D.S₁_le_normalizer_Q₁ D.u_S₁
  have hu2 : D.u ^ 2 ∈ D.Q₁ := by rw [D.u_sq]; exact one_mem _
  have hcard := card_sup_zpowers huN hu2 D.u_not_mem_Q₁
  have hle : D.Q₁ ⊔ zpowers D.u ≤ D.S₁ := sup_le D.Q₁_le_S₁ (zpowers_le.mpr D.u_S₁)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, D.card_Q₁, D.card]

include Rl in
theorem T₁_eq : R = S.TE ⊔ zpowers D.v ⊔ zpowers D.w₁ := by
  have hTt : ∀ {x : X}, x ∈ S.TE → x * t * x⁻¹ = t := fun hx => by
    rw [mem_centralizer_singleton_iff.mp ((TE_le_C S) hx)]; group
  have htw : t = I.wV (0, 0, 1, 0) := by simp [wV]
  have hvN : D.v ∈ normalizer (S.TE : Set X) := H.le_normalizer D.v_T₁
  have hv2 : D.v ^ 2 ∈ S.TE := I.E_le_TE D.v_sq_E
  have hvT : D.v ∉ S.TE := fun h => by
    have := hTt h
    rw [D.v_mat.conj_t] at this
    exact vC_t' (I.wV_injective (this.trans htw))
  have hc1 := card_sup_zpowers hvN hv2 hvT
  have hmem : ∀ {x : X}, x ∈ S.TE ⊔ zpowers D.v ↔ x ∈ S.TE ∨ D.v⁻¹ * x ∈ S.TE :=
    mem_sup_zpowers_iff hvN hv2
  have hw₁N : D.w₁ ∈ normalizer ((S.TE ⊔ zpowers D.v : Subgroup X) : Set X) := by
    have hwN : D.w₁ ∈ normalizer (S.TE : Set X) := H.le_normalizer D.w₁_T₁
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    rcases hmem.mp hx with h | h
    · exact mem_sup_left ((mem_normalizer_iff.mp hwN x).mp h)
    · have e : D.w₁ * x * D.w₁⁻¹ = (D.v * D.w₁ * D.v⁻¹ * D.w₁⁻¹)⁻¹ * D.v *
          (D.w₁ * (D.v⁻¹ * x) * D.w₁⁻¹) := by group
      rw [e, D.v_w₁, I.wV_inv]
      exact mul_mem (mul_mem (mem_sup_left (I.E_le_TE (I.wV_mem _))) (mem_sup_right
        (mem_zpowers _))) (mem_sup_left ((mem_normalizer_iff.mp hwN _).mp h))
  have hw₁2 : D.w₁ ^ 2 ∈ S.TE ⊔ zpowers D.v := by
    rw [Rl.rel.sq1]; exact mem_sup_left (I.E_le_TE (I.wV_mem _))
  have hw₁T : D.w₁ ∉ S.TE ⊔ zpowers D.v := by
    intro h
    rcases hmem.mp h with h' | h'
    · have := hTt h'
      rw [D.w₁_mat.conj_t] at this
      exact M1C_t' D.ε (I.wV_injective (this.trans htw))
    · have := hTt h'
      rw [((D.v_mat.inv vC_vC).mul D.w₁_mat).conj_t] at this
      exact vM1C_t D.ε (I.wV_injective (this.trans htw))
  have hc2 := card_sup_zpowers hw₁N hw₁2 hw₁T
  have hle : S.TE ⊔ zpowers D.v ⊔ zpowers D.w₁ ≤ R :=
    sup_le (sup_le H.le (zpowers_le.mpr D.v_T₁)) (zpowers_le.mpr D.w₁_T₁)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hc2, hc1, H.card]
  omega

theorem comm_E {g : X} {c : Fin 4 → V4} (hg : I.Mat g c)
    (hc : ∀ e : V4, (addV e (lin c e)).2.2.1 = 0) (p : V4) :
    I.wV p * g * (I.wV p)⁻¹ * g⁻¹ ∈ S.E0 I.yi I.ki := by
  have e : I.wV p * g * (I.wV p)⁻¹ * g⁻¹ = I.wV p * (g * I.wV p * g⁻¹)⁻¹ := by group
  rw [e, hg.conj, I.wV_inv, ← I.wV_add]
  exact I.wV_mem_E0' (hc p)

include Rl in
theorem normalizer_W {g : X} (hg0 : g ∈ normalizer (S.E0 I.yi I.ki : Set X))
    (hg1 : g * D.w₁ * g⁻¹ ∈ S.E0 I.yi I.ki ⊔ zpowers D.w₁) :
    g ∈ normalizer ((S.E0 I.yi I.ki ⊔ zpowers D.w₁ : Subgroup X) : Set X) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  rcases Rl.rel.mem_M₁_iff.mp hx with h | h
  · exact mem_sup_left ((mem_normalizer_iff.mp hg0 x).mp h)
  · have e : g * x * g⁻¹ = (g * D.w₁ * g⁻¹) * (g * (D.w₁⁻¹ * x) * g⁻¹) := by group
    rw [e]
    exact mul_mem hg1 (mem_sup_left ((mem_normalizer_iff.mp hg0 _).mp h))

include Rl in
theorem S₁_commutator_mem : ∀ a ∈ D.S₁, ∀ b ∈ D.S₁,
    a * b * a⁻¹ * b⁻¹ ∈ S.E0 I.yi I.ki ⊔ zpowers D.w₁ := by
  set W := S.E0 I.yi I.ki ⊔ zpowers D.w₁ with hW
  set s : Set X := (I.E : Set X) ∪ {D.v, D.w₁, D.w₂, D.u} with hs
  have hS : D.S₁ ≤ closure s := by
    rw [D.S₁_eq Rl]
    refine sup_le (sup_le (sup_le (sup_le (fun e he => subset_closure (Or.inl he)) ?_) ?_) ?_) ?_
    all_goals exact zpowers_le.mpr (subset_closure (Or.inr (by simp)))
  have hE0W : ∀ {e : X}, e ∈ S.E0 I.yi I.ki → e ∈ W := fun he => mem_sup_left he
  have hw₁W : D.w₁ ∈ W := mem_sup_right (mem_zpowers _)
  have hN : ∀ g ∈ s, g ∈ normalizer (W : Set X) := by
    intro g hg
    rcases hg with hg | hg
    · obtain ⟨p, rfl⟩ := I.eq_wV hg
      refine D.normalizer_W Rl (I.mem_normalizer_E0 (Mat.of_mem_centralizer
        (I.E_le_centralizer hg)) (fun a b d => by rw [lin_bas_self])) ?_
      obtain ⟨f, hf, hf'⟩ := conj_E Rl.rel.m1 (fun e => (E_conj_E0 D.ε e).1) (M1C_sq D.ε) p
      rw [hf']; exact mul_mem hw₁W (hE0W hf)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · refine D.normalizer_W Rl (I.mem_normalizer_E0 D.v_mat vC_E0) ?_
        have e : D.v * D.w₁ * D.v⁻¹ = (D.v * D.w₁ * D.v⁻¹ * D.w₁⁻¹) * D.w₁ := by group
        rw [e, D.v_w₁]; exact mul_mem (hE0W (I.wV_mem_E0 _ _ _)) hw₁W
      · exact le_normalizer hw₁W
      · refine D.normalizer_W Rl Rl.rel.w₂_normalizer ?_
        have e : D.w₂ * D.w₁ * D.w₂⁻¹ = (D.w₁ * D.w₂ * D.w₁⁻¹ * D.w₂⁻¹)⁻¹ * D.w₁ := by group
        rw [e, Rl.rel.comm, I.wV_inv]; exact mul_mem (hE0W (I.wV_mem_E0' Rl.rel.γ_E0)) hw₁W
      · refine D.normalizer_W Rl (I.mem_normalizer_E0 D.u_mat xCols_E0) ?_
        obtain ⟨φ, hφ, hw⟩ := D.u_conj_w₁
        rw [hw]; exact mul_mem hw₁W (hE0W (I.wV_mem_E0' hφ))
  have hNc : ∀ g ∈ closure s, g ∈ normalizer (W : Set X) := fun g hg =>
    (closure_le (normalizer (W : Set X))).mpr hN hg
  have hvw₁ : D.v * D.w₁ * D.v⁻¹ * D.w₁⁻¹ ∈ W := by rw [D.v_w₁]; exact hE0W (I.wV_mem_E0 _ _ _)
  have hvw₂ : D.v * D.w₂ * D.v⁻¹ * D.w₂⁻¹ ∈ W := by
    rw [D.v_w₂]; exact hE0W (I.wV_mem_E0' (dCols_E0 _ _))
  have hvu : D.v * D.u * D.v⁻¹ * D.u⁻¹ ∈ W := by rw [← D.u_v]; group; exact one_mem _
  have hw₁w₂ : D.w₁ * D.w₂ * D.w₁⁻¹ * D.w₂⁻¹ ∈ W := by
    rw [Rl.rel.comm]; exact hE0W (I.wV_mem_E0' Rl.rel.γ_E0)
  have hw₁u : D.w₁ * D.u * D.w₁⁻¹ * D.u⁻¹ ∈ W := by
    obtain ⟨φ, hφ, hw⟩ := D.u_conj_w₁
    have e : D.w₁ * D.u * D.w₁⁻¹ * D.u⁻¹ = D.w₁ * (D.u * D.w₁ * D.u⁻¹)⁻¹ := by group
    rw [e, hw, mul_inv_rev, ← mul_assoc]
    exact hE0W ((mem_normalizer_iff.mp Rl.rel.w₁_normalizer _).mp (inv_mem (I.wV_mem_E0' hφ)))
  have hw₂u : D.w₂ * D.u * D.w₂⁻¹ * D.u⁻¹ ∈ W := by
    obtain ⟨φ, hφ, hw⟩ := D.u_conj_w₂
    have e : D.w₂ * D.u * D.w₂⁻¹ * D.u⁻¹ = D.w₂ * (D.u * D.w₂ * D.u⁻¹)⁻¹ := by group
    rw [e, hw]
    have e2 : D.w₂ * (D.w₁ * D.w₂ * I.wV φ)⁻¹ = (D.w₂ * (I.wV φ)⁻¹ * D.w₂⁻¹) * D.w₁⁻¹ := by group
    rw [e2]
    exact mul_mem (hE0W ((mem_normalizer_iff.mp Rl.rel.w₂_normalizer _).mp
      (inv_mem (I.wV_mem_E0' hφ)))) (inv_mem hw₁W)
  have hgg : ∀ a ∈ ({D.v, D.w₁, D.w₂, D.u} : Set X), ∀ b ∈ ({D.v, D.w₁, D.w₂, D.u} : Set X),
      a * b * a⁻¹ * b⁻¹ ∈ W := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    all_goals first
      | (group; exact one_mem _)
      | assumption
      | exact comm_symm (by assumption)
  have hgE : ∀ a ∈ ({D.v, D.w₁, D.w₂, D.u} : Set X), ∀ p : V4,
      I.wV p * a * (I.wV p)⁻¹ * a⁻¹ ∈ W := by
    intro a ha p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hE0W (comm_E D.v_mat (fun e => (E_conj_E0 D.ε e).2.2.1) p)
    · exact hE0W (comm_E D.w₁_mat (fun e => (E_conj_E0 D.ε e).1) p)
    · exact hE0W (comm_E D.w₂_mat (fun e => (E_conj_E0 D.ε e).2.1) p)
    · exact hE0W (comm_E D.u_mat (fun e => (E_conj_E0 D.ε e).2.2.2) p)
  have hgen : ∀ a ∈ s, ∀ b ∈ s, a * b * a⁻¹ * b⁻¹ ∈ W := by
    intro a ha b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [I.comm ha hb]; group; exact one_mem _
    · obtain ⟨p, rfl⟩ := I.eq_wV ha
      exact hgE b hb p
    · obtain ⟨p, rfl⟩ := I.eq_wV hb
      exact comm_symm (hgE a ha p)
    · exact hgg a ha b hb
  intro a ha b hb
  exact comm_mem_of_closure hNc hgen a (hS ha) b (hS hb)

include Rl in
theorem Q₁_eq_centralizer (hε : D.ε = 0) {x : X} (hx : x ∈ D.S₁) :
    x ∈ D.Q₁ ↔ ∀ e ∈ S.E0 I.yi I.ki, x * e = e * x := by
  have hle : D.Q₁ ≤ centralizer (S.E0 I.yi I.ki : Set X) := by
    rw [D.Q₁_eq Rl]
    have hfix : ∀ {g : X} {c : Fin 4 → V4}, I.Mat g c →
        (∀ a b d : Fin 2, lin c (a, b, 0, d) = (a, b, 0, d)) →
        g ∈ centralizer (S.E0 I.yi I.ki : Set X) := fun hg hc => by
      rw [mem_centralizer_iff]
      intro e he
      obtain ⟨a, b, d, rfl⟩ := (I.mem_E0_iff).mp he
      exact (commute_of_fix hg (hc a b d)).symm
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · intro e he
      rw [mem_centralizer_iff]
      intro f hf
      exact I.comm (I.E0_le_E hf) he
    · exact zpowers_le.mpr (hfix D.v_mat vC_E0_fix)
    · exact zpowers_le.mpr (hfix D.w₁_mat (by rw [hε]; exact M1C_fix_one))
    · exact zpowers_le.mpr (hfix D.w₂_mat (by rw [hε]; exact M2C_fix_one))
  have hC : ∀ {y : X}, y ∈ D.Q₁ → ∀ e ∈ S.E0 I.yi I.ki, y * e = e * y := fun hy e he =>
    ((mem_centralizer_iff.mp (hle hy)) e he).symm
  refine ⟨fun h => hC h, fun h => ?_⟩
  have huN : D.u ∈ normalizer (D.Q₁ : Set X) := D.S₁_le_normalizer_Q₁ D.u_S₁
  have hu2 : D.u ^ 2 ∈ D.Q₁ := by rw [D.u_sq]; exact one_mem _
  have hx' : x ∈ D.Q₁ ⊔ zpowers D.u := by rwa [D.Q₁_eq Rl, ← D.S₁_eq Rl]
  rcases (mem_sup_zpowers_iff huN hu2).mp hx' with h' | h'
  · exact h'
  · exfalso
    have hy : I.yi ∈ S.E0 I.yi I.ki := subset_closure (by simp)
    have h1 := h I.yi hy
    have h2 := hC h' I.yi hy
    have hu : D.u * I.yi = I.yi * D.u := by
      have e : D.u = x * (D.u⁻¹ * x)⁻¹ := by group
      rw [e]
      calc x * (D.u⁻¹ * x)⁻¹ * I.yi = x * ((D.u⁻¹ * x)⁻¹ * I.yi) := by group
        _ = x * (I.yi * (D.u⁻¹ * x)⁻¹) := by
            congr 1
            calc (D.u⁻¹ * x)⁻¹ * I.yi = (D.u⁻¹ * x)⁻¹ * (I.yi * (D.u⁻¹ * x)) * (D.u⁻¹ * x)⁻¹ := by
                  group
              _ = (D.u⁻¹ * x)⁻¹ * ((D.u⁻¹ * x) * I.yi) * (D.u⁻¹ * x)⁻¹ := by rw [h2]
              _ = I.yi * (D.u⁻¹ * x)⁻¹ := by group
        _ = I.yi * (x * (D.u⁻¹ * x)⁻¹) := by rw [← mul_assoc, h1, mul_assoc]
    have h3 := D.u_mat.conj_yi
    rw [xCols_yi] at h3
    have h4 : D.u * I.yi * D.u⁻¹ = I.yi := by rw [hu]; group
    rw [h4] at h3
    have := I.wV_injective ((show I.wV (0, 1, 0, 0) = I.yi by simp [wV]).trans h3)
    simp at this

include Rl in
theorem Q₁_char (hε : D.ε = 0) (hs : Rl.s1 = 1 ∨ Rl.s4 = 1) {n : X}
    (hn : n ∈ normalizer (D.S₁ : Set X)) : D.Q₁.map (MulAut.conj n).toMonoidHom = D.Q₁ := by
  set W := S.E0 I.yi I.ki ⊔ zpowers D.w₁ with hW
  have hinv : ∀ {x : X}, x ∈ W → x ^ 2 = 1 → x ∈ S.E0 I.yi I.ki := by
    intro x hx hx2
    rcases Rl.rel.mem_M₁_iff.mp hx with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, d, hd⟩ := (I.mem_E0_iff).mp h
      have hc : D.w₁ * I.wV (a, b, 0, d) = I.wV (a, b, 0, d) * D.w₁ :=
        commute_of_fix Rl.rel.m1 (by rw [hε]; exact M1C_fix_one a b d)
      have e : x = D.w₁ * I.wV (a, b, 0, d) := by rw [← hd]; group
      rw [e, (Commute.mul_pow hc 2), I.sq_eq_one (I.wV_mem _), mul_one, Rl.rel.sq1,
        ← I.wV_zero] at hx2
      have := I.wV_injective hx2
      simp only [Prod.mk.injEq] at this
      rcases hs with h1 | h1
      · rw [h1] at this; exact absurd this.1 (by decide)
      · rw [h1] at this; exact absurd this.2.2.2 (by decide)
  have hcomm : ∀ {m : X}, m ∈ normalizer (D.S₁ : Set X) → ∀ {a b : X}, a ∈ D.S₁ → b ∈ D.S₁ →
      m * (a * b * a⁻¹ * b⁻¹) * m⁻¹ ∈ W := by
    intro m hm a b ha hb
    have e : m * (a * b * a⁻¹ * b⁻¹) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) *
        (m * a * m⁻¹)⁻¹ * (m * b * m⁻¹)⁻¹ := by group
    rw [e]
    exact D.S₁_commutator_mem Rl _ ((mem_normalizer_iff.mp hm a).mp ha) _
      ((mem_normalizer_iff.mp hm b).mp hb)
  have hES : ∀ {e : X}, e ∈ I.E → e ∈ D.S₁ := fun he => D.Q₁_le_S₁ (D.E_le_Q₁ he)
  have hz : S.z = D.u * I.yi * D.u⁻¹ * I.yi⁻¹ := by
    rw [D.u_mat.conj_yi, xCols_yi]; simp [wV]
  have hk : I.ki = D.v * t * D.v⁻¹ * t⁻¹ := by
    rw [D.v_mat.conj_t]; simp [vC, wV, I.comm I.t_mem_E I.ki_mem_E]
  have hy : I.yi = D.w₂ * t * D.w₂⁻¹ * t⁻¹ := by
    rw [D.w₂_mat.conj_t, hε, M2C_zero_t]; simp [wV]
  have hE0 : ∀ {m : X}, m ∈ normalizer (D.S₁ : Set X) → ∀ e ∈ S.E0 I.yi I.ki,
      m * e * m⁻¹ ∈ S.E0 I.yi I.ki := by
    intro m hm e he
    refine conj_mem_closure (fun g hg => ?_) he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hg2 : (m * g * m⁻¹) ^ 2 = 1 := by
      rw [conj_pow]
      rcases hg with rfl | rfl | rfl
      · rw [(z_sq S)]; group
      · rw [I.yi_sq]; group
      · rw [I.ki_sq]; group
    refine hinv ?_ hg2
    rcases hg with rfl | rfl | rfl
    · rw [hz]; exact hcomm hm D.u_S₁ (hES I.yi_mem_E)
    · rw [hy]; exact hcomm hm (D.Q₁_le_S₁ D.w₂_Q₁) (hES I.t_mem_E)
    · rw [hk]; exact hcomm hm (D.Q₁_le_S₁ D.v_Q₁) (hES I.t_mem_E)
  have hle : D.Q₁.map (MulAut.conj n).toMonoidHom ≤ D.Q₁ := by
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hqS : n * q * n⁻¹ ∈ D.S₁ := (mem_normalizer_iff.mp hn q).mp (D.Q₁_le_S₁ hq)
    refine (D.Q₁_eq_centralizer Rl hε hqS).mpr fun e he => ?_
    have he' : n⁻¹ * e * n⁻¹⁻¹ ∈ S.E0 I.yi I.ki := hE0 (inv_mem hn) e he
    have h1 := (D.Q₁_eq_centralizer Rl hε (D.Q₁_le_S₁ hq)).mp hq _ he'
    rw [inv_inv] at h1
    calc n * q * n⁻¹ * e = n * (q * (n⁻¹ * e * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * e * n) * q) * n⁻¹ := by rw [h1]
      _ = e * (n * q * n⁻¹) := by group
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective (MulAut.conj n).injective])

end Data6

end Inst

end CFSG.OddStandard.SmallF3.L33.KD.KD46
