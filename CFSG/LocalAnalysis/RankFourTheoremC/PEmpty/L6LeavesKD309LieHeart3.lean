module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieEps
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieHeart2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Cfg

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Equiv Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
open scoped commutatorElement

variable {A : Type} [Group A]

@[expose] def Pt (Φ : M5 →* A) : Subgroup A := Pm.map Φ

@[expose] def Jt (Φ : M5 →* A) : Subgroup A := T5.map Φ

@[expose] def Et (Φ : M5 →* A) : Subgroup A := T0.map Φ

@[expose] def pi5 : Perm (Fin 5) := swap 0 1

@[expose] def nt (Φ : M5 →* A) : A := Φ (monS pi5)

@[expose] def Nt (Φ : M5 →* A) : Subgroup A := Pt Φ ⊔ conjSub (nt Φ) (Pt Φ)

theorem comm_Jt_Pt (Φ : M5 →* A) : ⁅Jt Φ, Pt Φ⁆ = Et Φ := by
  unfold Jt Pt Et
  rw [← Subgroup.map_commutator, commutator_T5_Pm]

variable {Φ : M5 →* A}

theorem mem_Et_iff (hΦ : KerSc Φ) (e : A) : e ∈ Et Φ ↔ ∃ v : V3, eps Φ v = e := by
  constructor
  · rintro ⟨x, ⟨hx5, hx⟩, rfl⟩
    have hxe := mem_T5.mp hx5
    have h1 : monDet x = 1 := hx
    rw [hxe, monDet_monT] at h1
    set s : Fin 5 → C5 := x.left with hs
    set y : Fin 5 → ZMod 5 := fun i => Multiplicative.toAdd (s i) with hy
    have hsum : ∑ i, y i = 0 := by
      have : Multiplicative.toAdd (∏ i, s i) = ∑ i, Multiplicative.toAdd (s i) := toAdd_prod _ _
      rw [← this, h1]
      rfl
    refine ⟨ch5 y, ?_⟩
    unfold eps
    rw [ext5_ch5 hsum, Phi_mT_sub_const hΦ, hxe, monT_eq_mT]
  · rintro ⟨v, rfl⟩
    refine ⟨mT (ext5 v), ⟨monT_mem_T5 _, ?_⟩, rfl⟩
    change monDet (monT _) = 1
    rw [monDet_monT]
    have : ∏ i, Multiplicative.ofAdd (ext5 v i) = Multiplicative.ofAdd (∑ i, ext5 v i) :=
      (ofAdd_sum _ _).symm
    rw [this, sum_ext5]
    rfl

theorem monS_mul' (a b : Perm (Fin 5)) : monS (C := C5) (a * b) = monS a * monS b :=
  map_mul (SemidirectProduct.inr : Perm (Fin 5) →* M5) a b

theorem monS_pow' (a : Perm (Fin 5)) (n : ℕ) : monS (C := C5) (a ^ n) = (monS a) ^ n :=
  map_pow (SemidirectProduct.inr : Perm (Fin 5) →* M5) a n

theorem gw_mem_Nt (w : Perm (Fin 5)) (hw : w ∈ words) : Φ (monS w) ∈ Nt Φ := by
  unfold words at hw
  obtain ⟨⟨i, j, k⟩, -, rfl⟩ := Finset.mem_image.mp hw
  have hσ : Φ (monS (C := C5) sig5) ∈ Pt Φ :=
    ⟨monS sig5, by simpa using monS_zpow_mem_Pm (1 : ℤ), rfl⟩
  have hσ' : Φ (monS (C := C5) sg') ∈ conjSub (nt Φ) (Pt Φ) := by
    refine mem_conjSub.mpr ⟨Φ (monS (C := C5) sig5), hσ, ?_⟩
    unfold nt sg' pi5
    have hinv : (Φ (monS (C := C5) (swap 0 1)))⁻¹ = Φ (monS (C := C5) (swap 0 1)) := by
      rw [← map_inv, ← monS_inv, swap_inv]
    rw [hinv, monS_mul', monS_mul', map_mul, map_mul]
  rw [monS_mul', monS_mul', monS_pow', monS_pow', monS_pow', map_mul, map_mul, map_pow, map_pow,
    map_pow]
  have hσ0 : Φ (monS (C := C5) sg) ∈ Nt Φ := Subgroup.mem_sup_left hσ
  refine (Nt Φ).mul_mem ((Nt Φ).mul_mem ?_ ?_) ?_
  · exact (Nt Φ).pow_mem hσ0 _
  · exact (Nt Φ).pow_mem (Subgroup.mem_sup_right hσ') _
  · exact (Nt Φ).pow_mem hσ0 _

theorem act_add (σ : Perm (Fin 5)) (v w : V3) : act σ (v + w) = act σ v + act σ w :=
  (actL σ).map_add v w

theorem act_smul (σ : Perm (Fin 5)) (c : ZMod 5) (v : V3) : act σ (c • v) = c • act σ v :=
  (actL σ).map_smul c v

theorem act_zero (σ : Perm (Fin 5)) : act σ 0 = 0 := (actL σ).map_zero

theorem vec_ext {a b : V3} (h : ∀ x, a ⬝ᵥ x = b ⬝ᵥ x) : a = b := by
  funext i
  have := h (Pi.single i 1)
  simpa using this

theorem actD_dot (σ : Perm (Fin 5)) (u x : V3) : actD σ u ⬝ᵥ x = u ⬝ᵥ act σ⁻¹ x := by
  let ψ : V3 →+ ZMod 5 :=
    { toFun := fun x => u ⬝ᵥ act σ⁻¹ x
      map_zero' := by simp [act_zero]
      map_add' := fun a b => by simp [act_add, dotProduct_add] }
  exact (functional_eq_dot ψ x).symm

theorem actD_smul (σ : Perm (Fin 5)) (c : ZMod 5) (u : V3) : actD σ (c • u) = c • actD σ u := by
  funext k
  simp [actD, dotProduct_smul]

theorem actD_actD (σ τ : Perm (Fin 5)) (u : V3) : actD σ (actD τ u) = actD (σ * τ) u := by
  refine vec_ext fun x => ?_
  rw [actD_dot, actD_dot, actD_dot, act_act, mul_inv_rev]

theorem card_image_le_of_factor {α β γ : Type} [Nonempty α] [DecidableEq β] [DecidableEq γ]
    (s : Finset α)
    (key : α → β) (c : α → γ) (h : ∀ a ∈ s, ∀ a' ∈ s, c a = c a' → key a = key a') :
    (s.image key).card ≤ (s.image c).card := by
  classical
  refine Finset.card_le_card_of_surjOn (fun g => key (Function.invFunOn c (↑s) g)) ?_
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (by simpa using hb)
  refine ⟨c a, by simp [Finset.mem_image]; exact ⟨a, ha, rfl⟩, ?_⟩
  have hex : ∃ a' ∈ (↑s : Set α), c a' = c a := ⟨a, ha, rfl⟩
  exact h _ (Function.invFunOn_mem hex) a ha (Function.invFunOn_eq hex)

theorem heart_irr (hΦ : KerSc Φ) {S F : Subgroup A} (hS : S ≤ Nt Φ)
    (hidx : S.relIndex (Nt Φ) ≤ 5) (hF : F ≤ Et Φ)
    (hinv : ∀ s ∈ S, ∀ f ∈ F, s * f * s⁻¹ ∈ F) : F = ⊥ ∨ F = Et Φ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hFbot, hFtop⟩ := hcon
  let F₃ : AddSubgroup V3 :=
    { carrier := {v | eps Φ v ∈ F}
      add_mem' := fun {a b} ha hb => by
        change eps Φ (a + b) ∈ F
        rw [eps_add]
        exact F.mul_mem ha hb
      zero_mem' := by
        change eps Φ 0 ∈ F
        rw [eps_zero]
        exact F.one_mem
      neg_mem' := fun {a} ha => by
        change eps Φ (-a) ∈ F
        rw [eps_neg]
        exact F.inv_mem ha }
  have hmem3 : ∀ v, v ∈ F₃ ↔ eps Φ v ∈ F := fun v => Iff.rfl
  have hF3bot : F₃ ≠ ⊥ := by
    intro hb
    apply hFbot
    rw [eq_bot_iff]
    intro f hf
    obtain ⟨v, rfl⟩ := (mem_Et_iff hΦ f).mp (hF hf)
    have : v ∈ F₃ := (hmem3 v).mpr hf
    rw [hb, AddSubgroup.mem_bot] at this
    rw [this, eps_zero]
    exact one_mem _
  have hF3top : F₃ ≠ ⊤ := by
    intro ht
    apply hFtop
    refine le_antisymm hF (fun e he => ?_)
    obtain ⟨v, rfl⟩ := (mem_Et_iff hΦ e).mp he
    have : v ∈ F₃ := by rw [ht]; exact AddSubgroup.mem_top v
    exact (hmem3 v).mp this
  set N₁ := Nt Φ with hN₁
  set S' : Subgroup ↥N₁ := S.subgroupOf N₁ with hS'
  let gw : Perm (Fin 5) → A := fun w => Φ (monS w)
  have hgw : ∀ w ∈ words, gw w ∈ N₁ := fun w hw => gw_mem_Nt w hw
  let cw : Perm (Fin 5) → (↥N₁ ⧸ S') := fun w =>
    if h : w ∈ words then (QuotientGroup.mk (⟨gw w, hgw w h⟩ : ↥N₁) : ↥N₁ ⧸ S')
    else (QuotientGroup.mk (1 : ↥N₁) : ↥N₁ ⧸ S')
  have hcS : ∀ w ∈ words, ∀ w' ∈ words, cw w = cw w' → (gw w)⁻¹ * gw w' ∈ S := by
    intro w hw w' hw' h
    simp only [cw, dif_pos hw, dif_pos hw'] at h
    exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h)
  have hinv3 : ∀ w ∈ words, ∀ w' ∈ words, cw w = cw w' → ∀ v : V3,
      v ∈ F₃ ↔ act (w⁻¹ * w') v ∈ F₃ := by
    intro w hw w' hw' h v
    have hs := hcS w hw w' hw' h
    have hsx : (gw w)⁻¹ * gw w' = Φ (monS (w⁻¹ * w')) := by
      show (Φ (monS w))⁻¹ * Φ (monS w') = _
      rw [monS_mul', map_mul, monS_inv, map_inv]
    rw [hsx] at hs
    constructor
    · intro hv
      have h1 := hinv _ hs _ ((hmem3 v).mp hv)
      rw [eps_conj hΦ (monS (w⁻¹ * w')) v] at h1
      exact (hmem3 _).mpr h1
    · intro hv
      have hs' : Φ (monS (w⁻¹ * w')⁻¹) ∈ S := by
        have := S.inv_mem hs
        rwa [← map_inv, ← monS_inv] at this
      have h1 := hinv _ hs' _ ((hmem3 _).mp hv)
      rw [eps_conj hΦ (monS (w⁻¹ * w')⁻¹) _] at h1
      exact (hmem3 v).mpr (by
        have : act (monS (C := C5) (w⁻¹ * w')⁻¹).right (act (w⁻¹ * w') v) = v :=
          act_inv_act _ v
        rw [← this]
        exact h1)
  have hNle : N₁ ≤ Φ.range := by
    refine sup_le (Subgroup.map_le_range _ _) ?_
    rintro _ hx
    obtain ⟨p, hp, rfl⟩ := mem_conjSub.mp hx
    exact Φ.range.mul_mem (Φ.range.mul_mem ⟨monS pi5, rfl⟩ (Subgroup.map_le_range _ _ hp))
      (Φ.range.inv_mem ⟨monS pi5, rfl⟩)
  haveI : Finite ↥(Φ.range) :=
    Finite.of_surjective (fun x : M5 => (⟨Φ x, x, rfl⟩ : Φ.range)) (fun ⟨_, x, hx⟩ =>
      ⟨x, Subtype.ext hx⟩)
  haveI : Finite ↥N₁ := Finite.of_injective (Subgroup.inclusion hNle)
    (Subgroup.inclusion_injective hNle)
  haveI : Fintype (↥N₁ ⧸ S') := Fintype.ofFinite _
  have hcosets : (words.image cw).card ≤ 5 := by
    refine (Finset.card_le_univ _).trans ?_
    have : Fintype.card (↥N₁ ⧸ S') = S.relIndex N₁ := by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
      rfl
    rw [this]
    exact hidx
  rcases card_dichotomy F₃ hF3bot hF3top with h5 | h25
  ·
    obtain ⟨v, hv0, hv⟩ := line_of_card_five F₃ h5
    have hvF : v ∈ F₃ := (hv v).mpr ⟨1, by simp⟩
    have hP : ∀ w ∈ words, ∀ w' ∈ words, cw w = cw w' →
        canon (act w v) = canon (act w' v) := by
      intro w hw w' hw' h
      obtain ⟨c, hc⟩ := (hv _).mp ((hinv3 w hw w' hw' h v).mp hvF)
      have h2 : act w' v = c • act w v := by
        have h3 : act w (act (w⁻¹ * w') v) = act w' v := by
          rw [act_act, mul_inv_cancel_left]
        rw [← h3, hc, act_smul]
      have hc0 : c ≠ 0 := by
        intro hc0
        apply hv0
        rw [hc0, zero_smul] at hc
        have := congrArg (act (w⁻¹ * w')⁻¹) hc
        rwa [act_inv_act, act_zero] at this
      rw [h2, canon_smul c hc0]
    have hle := card_image_le_of_factor words (fun w => canon (act w v)) cw hP
    have h6 := lines_ge_six v hv0
    omega
  ·
    obtain ⟨u, hu0, hu⟩ := plane_of_card_25 F₃ h25
    have hP : ∀ w ∈ words, ∀ w' ∈ words, cw w = cw w' →
        canon (actD w u) = canon (actD w' u) := by
      intro w hw w' hw' h
      have hk : ∀ x, u ⬝ᵥ x = 0 ↔ (actD (w⁻¹ * w')⁻¹ u) ⬝ᵥ x = 0 := by
        intro x
        rw [actD_dot, inv_inv, ← hu x, ← hu (act (w⁻¹ * w') x)]
        exact hinv3 w hw w' hw' h x
      have hne : actD (w⁻¹ * w')⁻¹ u ≠ 0 := by
        intro h0
        apply hu0
        refine vec_ext fun y => ?_
        have h1 := actD_dot (w⁻¹ * w')⁻¹ u (act (w⁻¹ * w')⁻¹ y)
        rw [h0, inv_inv, act_act_inv] at h1
        have h2 : u ⬝ᵥ y = 0 := by simpa using h1.symm
        rw [h2]
        simp
      obtain ⟨c, hc0, hc⟩ := prop_of_ker_eq hu0 hne hk
      have h2 : actD w u = c • actD w' u := by
        have h3 : actD w' (actD (w⁻¹ * w')⁻¹ u) = actD w u := by
          rw [actD_actD, mul_inv_rev, inv_inv, mul_inv_cancel_left]
        rw [← h3, hc, actD_smul]
      rw [h2, canon_smul c hc0]
    have hle := card_image_le_of_factor words (fun w => canon (actD w u)) cw hP
    have h6 := planes_ge_six u hu0
    omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
