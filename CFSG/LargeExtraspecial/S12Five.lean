module

public import CFSG.LargeExtraspecial.S12Comp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

section LinAlg

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem s12_span_pair_eq {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 2) {p₁ p₂ : V}
    (h₁ : p₁ ∈ W) (h₂ : p₂ ∈ W) (h₁0 : p₁ ≠ 0) (h₂0 : p₂ ≠ 0) (h12 : p₁ ≠ p₂) :
    Submodule.span (ZMod 2) {p₁, p₂} = W := by
  have hli : LinearIndependent (ZMod 2) ![p₁, p₂] :=
    OrthoF2.linearIndependent_pair_iff.mpr ⟨h₁0, h₂0, h12⟩
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact h₁
    · exact h₂
  · rw [OrthoF2.finrank_span_pair hli, hW]

theorem s12_mem_of_span_pair {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 2)
    {p₁ p₂ : V} (h₁ : p₁ ∈ W) (h₂ : p₂ ∈ W) (h₁0 : p₁ ≠ 0) (h₂0 : p₂ ≠ 0) (h12 : p₁ ≠ p₂)
    {w : V} (hw : w ∈ W) : w = 0 ∨ w = p₁ ∨ w = p₂ ∨ w = p₁ + p₂ := by
  rw [← s12_span_pair_eq hW h₁ h₂ h₁0 h₂0 h12, Submodule.mem_span_pair] at hw
  obtain ⟨a, b, rfl⟩ := hw
  rcases OrthoF2.zmod2_eq_zero_or_eq_one a with rfl | rfl <;>
    rcases OrthoF2.zmod2_eq_zero_or_eq_one b with rfl | rfl <;> simp

theorem s12_fix_of_fix_pair {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 2)
    {σ : V ≃ₗ[ZMod 2] V} {p₁ p₂ : V} (h₁ : p₁ ∈ W) (h₂ : p₂ ∈ W) (h₁0 : p₁ ≠ 0) (h₂0 : p₂ ≠ 0)
    (h12 : p₁ ≠ p₂) (hσ₁ : σ p₁ = p₁) (hσ₂ : σ p₂ = p₂) : ∀ w ∈ W, σ w = w := by
  intro w hw
  rcases s12_mem_of_span_pair hW h₁ h₂ h₁0 h₂0 h12 hw with rfl | rfl | rfl | rfl
  · simp
  · exact hσ₁
  · exact hσ₂
  · rw [map_add, hσ₁, hσ₂]

theorem s12_apply_eq_or {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 2)
    {σ : V ≃ₗ[ZMod 2] V} (hσσ : σ * σ = 1) (hσW : ∀ w ∈ W, σ w ∈ W) (hσ1 : ∃ w ∈ W, σ w ≠ w)
    {p : V} (hp : p ∈ W) (hp0 : p ≠ 0) (hσp : σ p = p) {w : V} (hw : w ∈ W) :
    σ w = w ∨ σ w = w + p := by
  set c := σ w - w with hc
  have hcW : c ∈ W := W.sub_mem (hσW w hw) hw
  have hσσw : σ (σ w) = w := by rw [← LinearEquiv.mul_apply, hσσ]; rfl
  have hσc : σ c = c := by
    rw [hc, map_sub, hσσw, OrthoF2.vec_sub, OrthoF2.vec_sub, add_comm]
  by_cases hc0 : c = 0
  · left
    exact sub_eq_zero.mp hc0
  · by_cases hcp : c = p
    · right
      rw [← hcp, hc]
      abel
    · exfalso
      obtain ⟨w', hw', hw'1⟩ := hσ1
      exact hw'1 (s12_fix_of_fix_pair hW hp hcW hp0 hc0 (Ne.symm hcp) hσp hσc w' hw')

theorem s12_apply_eq_of_fix {W : Submodule (ZMod 2) V} (hW : finrank (ZMod 2) W = 2)
    {σ σ' : V ≃ₗ[ZMod 2] V} (hσσ : σ * σ = 1) (hσ'σ' : σ' * σ' = 1)
    (hσW : ∀ w ∈ W, σ w ∈ W) (hσ'W : ∀ w ∈ W, σ' w ∈ W) (hσ1 : ∃ w ∈ W, σ w ≠ w)
    (hσ'1 : ∃ w ∈ W, σ' w ≠ w) {p : V} (hp : p ∈ W) (hp0 : p ≠ 0) (hσp : σ p = p)
    (hσ'p : σ' p = p) : ∀ w ∈ W, σ w = σ' w := by
  intro w hw
  have hfix : ∀ {τ : V ≃ₗ[ZMod 2] V}, (∃ w ∈ W, τ w ≠ w) → τ p = p → τ w = w → w = 0 ∨ w = p := by
    intro τ hτ1 hτp hτw
    by_contra hc
    push Not at hc
    obtain ⟨w', hw', hw'1⟩ := hτ1
    exact hw'1 (s12_fix_of_fix_pair hW hp hw hp0 hc.1 (Ne.symm hc.2) hτp hτw w' hw')
  rcases s12_apply_eq_or hW hσσ hσW hσ1 hp hp0 hσp hw with h1 | h1 <;>
    rcases s12_apply_eq_or hW hσ'σ' hσ'W hσ'1 hp hp0 hσ'p hw with h2 | h2
  · rw [h1, h2]
  · exfalso
    rcases hfix hσ1 hσp h1 with hw0 | hwp
    · rw [hw0, map_zero, zero_add] at h2
      exact hp0 h2.symm
    · rw [hwp, hσ'p, OrthoF2.vec_add_self] at h2
      exact hp0 h2
  · exfalso
    rcases hfix hσ'1 hσ'p h2 with hw0 | hwp
    · rw [hw0, map_zero, zero_add] at h1
      exact hp0 h1.symm
    · rw [hwp, hσp, OrthoF2.vec_add_self] at h1
      exact hp0 h1
  · rw [h1, h2]

end LinAlg

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def fixSub12 (W : Submodule (ZMod 2) S.Qt) : Subgroup S.O where
  carrier := {y | ∀ w ∈ W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w}
  mul_mem' {x y} hx hy w hw := by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hy w hw, hx w hw]
  one_mem' w _ := rfl
  inv_mem' {x} hx w hw := by
    have e := hx w hw
    conv_lhs => rw [← e]
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl

variable {S}

theorem mem_fixSub12 {W : Submodule (ZMod 2) S.Qt} {y : S.O} :
    y ∈ S.fixSub12 W ↔ ∀ w ∈ W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := Iff.rfl

theorem apply_mem_commSpace_of_commute {y τ : S.O} (h : y * τ = τ * y) {w : S.Qt}
    (hw : w ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
  refine mem_commSpace.mpr ⟨(y : S.Qt ≃ₗ[ZMod 2] S.Qt) v, ?_⟩
  rw [map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul,
    ← Subgroup.coe_mul, h]

theorem mem_normalizer_of_commute {X : Subgroup S.O} {e : S.O} (h : ∀ y ∈ X, e * y = y * e) :
    e ∈ normalizer (X : Set S.O) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have e1 := h _ hy
    have : y = e * y * e⁻¹ := by
      calc y = e⁻¹ * (e * y * e⁻¹ * e) := by group
        _ = e * y * e⁻¹ := by rw [← e1]; group
    rw [this]
    exact hy

@[expose] noncomputable def compl12 (g : G) (τ : S.O) : Set S.O :=
  {f | f ∈ S.Ebar12 g ∧ f ∉ S.comp12 τ}

theorem compl12_subset_Ebar12 {g : G} {τ : S.O} : compl12 g τ ⊆ S.Ebar12 g := fun _ h => h.1

theorem commute_of_mem_compl12 {g : G} {τ e f : S.O} (hτ : τ ∈ S.Ebar12 g)
    (he : e ∈ S.comp12 τ) (hf : f ∈ compl12 g τ) : e * f = f * e :=
  commute_of_not_mem_comp12 he (Ebar12_subset_Dbar12 hτ) (Ebar12_subset_Dbar12 hf.1) hf.2

theorem commute_closure_compl12 {g : G} {τ e : S.O} (hτ : τ ∈ S.Ebar12 g)
    (he : e ∈ S.comp12 τ) : ∀ y ∈ closure (compl12 g τ), e * y = y * e := by
  intro y hy
  have : closure (compl12 g τ) ≤ centralizer ({e} : Set S.O) := by
    rw [closure_le]
    intro f hf
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (commute_of_mem_compl12 hτ he hf).symm
  exact (mem_centralizer_singleton_iff.mp (this hy)).symm

theorem Xbar12_le_normalizer_closure_compl12 {g : G} {τ : S.O} (hτ : τ ∈ S.Ebar12 g) :
    S.Xbar12 g ≤ normalizer (closure (compl12 g τ) : Set S.O) := by
  rw [Xbar12, closure_le]
  intro e he
  by_cases hec : e ∈ S.comp12 τ
  · exact mem_normalizer_of_commute (commute_closure_compl12 hτ hec)
  · exact le_normalizer (subset_closure ⟨he, hec⟩)

theorem closure_compl12_le_Xbar12 {g : G} {τ : S.O} :
    closure (compl12 g τ) ≤ S.Xbar12 g := closure_mono compl12_subset_Ebar12

theorem noNormalTwo_closure_compl12 {g : G} {τ : S.O} (hτ : τ ∈ S.Ebar12 g) :
    S12NoNormalTwo (closure (compl12 g τ)) := by
  have hX : S12NoNormalTwo (S.Xbar12 g) :=
    S.s12_noNormalTwo_Mbar.of_normal Xbar12_le_Mbar Mbar_le_normalizer_Xbar12
  exact hX.of_normal closure_compl12_le_Xbar12 (Xbar12_le_normalizer_closure_compl12 hτ)

theorem mem_normalizer_of_conj_le {X : Subgroup S.O} {m : S.O}
    (h₁ : ∀ y ∈ X, m * y * m⁻¹ ∈ X) (h₂ : ∀ y ∈ X, m⁻¹ * y * m⁻¹⁻¹ ∈ X) :
    m ∈ normalizer (X : Set S.O) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h₁ y, fun hy => ?_⟩
  have := h₂ _ hy
  simpa [mul_assoc] using this

theorem conj_mem_closure_of_conj_mem {T : Set S.O} {m : S.O} (h : ∀ y ∈ T, m * y * m⁻¹ ∈ T) :
    ∀ y ∈ closure T, m * y * m⁻¹ ∈ closure T := by
  intro y hy
  have : (closure T).map (MulAut.conj m).toMonoidHom ≤ closure T := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact subset_closure (h x hx)
  exact this ⟨y, hy, rfl⟩

theorem conj_mem_fixSub12 {τ y k : S.O} (hy : y * τ = τ * y)
    (hk : k ∈ S.fixSub12 (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))) :
    y * k * y⁻¹ ∈ S.fixSub12 (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  intro w hw
  have hy' : y⁻¹ * τ = τ * y⁻¹ := by
    calc y⁻¹ * τ = y⁻¹ * (τ * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * τ) * y⁻¹ := by rw [hy]
      _ = τ * y⁻¹ := by group
  have h1 := hk _ (apply_mem_commSpace_of_commute hy' hw)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply]
  rw [show ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ w = ((y⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w
    from rfl, h1]
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
  rfl

theorem kernel_closure_compl12_eq_bot {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {τ : S.O} (hτ : τ ∈ S.Ebar12 g) :
    closure (compl12 g τ) ⊓ S.fixSub12 (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = ⊥ := by
  obtain ⟨h, hτL⟩ := S.s12_exists_Lbar_of_mem_Ebar12 hτ
  obtain ⟨hbQ, hbne⟩ := S.s12_conj_mem haQ hne h
  set Y := closure (compl12 g τ) with hY
  set W := commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hW
  set K := Y ⊓ S.fixSub12 W with hK
  have hYτ : ∀ y ∈ Y, y * τ = τ * y := fun y hy =>
    (commute_closure_compl12 hτ (mem_comp12_self τ) y hy).symm
  have hKY : S12NoNormalTwo K := by
    refine (noNormalTwo_closure_compl12 hτ).of_normal inf_le_left fun y hy => ?_
    have hy' : y⁻¹ ∈ Y := Y.inv_mem hy
    refine mem_normalizer_of_conj_le (fun k hk => ⟨?_, ?_⟩) (fun k hk => ⟨?_, ?_⟩)
    · exact Y.mul_mem (Y.mul_mem hy hk.1) hy'
    · exact conj_mem_fixSub12 (hYτ y hy) hk.2
    · exact Y.mul_mem (Y.mul_mem hy' hk.1) (Y.inv_mem hy')
    · exact conj_mem_fixSub12 (hYτ _ hy') hk.2
  have hKM : K ≤ S.Mbar := fun k hk =>
    Xbar12_le_Mbar (closure_compl12_le_Xbar12 hk.1)
  have hbW : S.cl (((h : G) * g) * S.z * ((h : G) * g)⁻¹) ∈ W := by
    have hτA := isTypeA_of_mem_Ebar12 hτ
    exact (S.timmesfeld_12_6 hbQ hbne hτL hτA).1
  have hLN : S.Lbar ((h : G) * g) ≤ normalizer (K : Set S.O) := by
    intro ℓ hℓ
    have hcomm : ∀ {x : S.O}, x ∈ S.Lbar ((h : G) * g) → x * τ = τ * x := fun {x} hx =>
      congrArg Subtype.val ((S.isElementaryAbelian_Lbar hbQ).is_comm.comm ⟨x, hx⟩ ⟨τ, hτL⟩)
    have hℓM : ∀ {x : S.O}, x ∈ S.Lbar ((h : G) * g) → x ∈ S.Mbar := fun hx =>
      S.Lbar_le_Mbar _ hx
    have hF : ∀ {x : S.O}, x ∈ S.Lbar ((h : G) * g) → ∀ f ∈ compl12 g τ,
        x * f * x⁻¹ ∈ compl12 g τ := by
      intro x hx f hf
      refine ⟨conj_mem_Ebar12 (hℓM hx) hf.1, fun hc => hf.2 ?_⟩
      have h1 := conj_mem_comp12 (S.Mbar.inv_mem (hℓM hx)) hc
      have e1 : x⁻¹ * τ * x⁻¹⁻¹ = τ := by
        rw [inv_inv, mul_assoc, ← hcomm hx]
        group
      have e2 : x⁻¹ * (x * f * x⁻¹) * x⁻¹⁻¹ = f := by group
      rw [e1, e2] at h1
      exact h1
    have hℓ' : ℓ⁻¹ ∈ S.Lbar ((h : G) * g) := (S.Lbar _).inv_mem hℓ
    have hℓτ' : ℓ⁻¹ * τ = τ * ℓ⁻¹ := hcomm hℓ'
    refine mem_normalizer_of_conj_le (fun k hk => ⟨?_, ?_⟩) (fun k hk => ⟨?_, ?_⟩)
    · exact conj_mem_closure_of_conj_mem (hF hℓ) k hk.1
    · exact conj_mem_fixSub12 (hcomm hℓ) hk.2
    · exact conj_mem_closure_of_conj_mem (hF hℓ') k hk.1
    · exact conj_mem_fixSub12 hℓτ' hk.2
  exact S.s12_eq_bot_of_fix hbQ hbne hn hKY hKM (fun k hk => hk.2 _ hbW) hLN

theorem s12_lemma_S5 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) {τ : S.O} (hτ : τ ∈ S.Ebar12 g) (hF : (compl12 g τ).Nonempty) :
    (∃ f₁ ∈ compl12 g τ, ∃ f₂ ∈ compl12 g τ, compl12 g τ ⊆ closure {f₁, f₂}) ∧
      ∀ f ∈ compl12 g τ, commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
        commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ ⊥ := by
  set F := compl12 g τ with hFdef
  set Y := closure F with hY
  set W := commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hW
  have hK := S.kernel_closure_compl12_eq_bot haQ hne hn hτ
  have hWdim : finrank (ZMod 2) W = 2 := (isTypeA_of_mem_Ebar12 hτ).2.2.2.1
  have hYτ : ∀ y ∈ Y, y * τ = τ * y := fun y hy =>
    (commute_closure_compl12 hτ (mem_comp12_self τ) y hy).symm
  have hYW : ∀ y ∈ Y, ∀ w ∈ W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W := fun y hy w hw =>
    apply_mem_commSpace_of_commute (hYτ y hy) hw
  have hinj : ∀ y ∈ Y, ∀ y' ∈ Y, (∀ w ∈ W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
      (y' : S.Qt ≃ₗ[ZMod 2] S.Qt) w) → y = y' := by
    intro y hy y' hy' h
    have hmem : y⁻¹ * y' ∈ Y ⊓ S.fixSub12 W := by
      refine ⟨Y.mul_mem (Y.inv_mem hy) hy', fun w hw => ?_⟩
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ← h w hw, ← LinearEquiv.mul_apply,
        ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
    rw [hK, mem_bot] at hmem
    calc y = y * (y⁻¹ * y') := by rw [hmem, mul_one]
      _ = y' := by group
  have hA : ∀ f ∈ F, IsTypeA S.q (f : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := fun f hf =>
    isTypeA_of_mem_Ebar12 hf.1
  have hmoved : ∀ f ∈ F, ∃ w ∈ W, (f : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w := by
    intro f hf
    by_contra hc
    push Not at hc
    have hmem : f ∈ Y ⊓ S.fixSub12 W := ⟨subset_closure hf, hc⟩
    rw [hK, mem_bot] at hmem
    exact (hA f hf).2.1 (by rw [hmem]; rfl)
  have hfixvec : ∀ f ∈ F, ∃ p ∈ W, p ≠ 0 ∧ (f : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
    intro f hf
    obtain ⟨w, hw, hw1⟩ := hmoved f hf
    refine ⟨(f : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w, W.sub_mem (hYW f (subset_closure hf) w hw) hw,
      sub_ne_zero.mpr hw1, ?_⟩
    have hff : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ((f : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w := by
      rw [← LinearEquiv.mul_apply, (hA f hf).2.2.1]
      rfl
    rw [map_sub, hff, OrthoF2.vec_sub, OrthoF2.vec_sub, add_comm]
  have huniq : ∀ y ∈ Y, ∀ y' ∈ Y, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) * y = 1 →
      (y' : S.Qt ≃ₗ[ZMod 2] S.Qt) * y' = 1 → (∃ w ∈ W, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w) →
      (∃ w ∈ W, (y' : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w) → ∀ p ∈ W, p ≠ 0 →
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p → (y' : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p → y = y' := by
    intro y hy y' hy' h1 h2 h3 h4 p hp hp0 h5 h6
    exact hinj y hy y' hy' (s12_apply_eq_of_fix hWdim h1 h2 (hYW y hy) (hYW y' hy') h3 h4 hp
      hp0 h5 h6)
  refine ⟨?_, ?_⟩
  · obtain ⟨f₁, hf₁⟩ := hF
    by_cases hall : ∀ f ∈ F, f = f₁
    · exfalso
      have hYf : Y = zpowers f₁ := by
        refine le_antisymm ((closure_le _).mpr fun f hf => ?_) ?_
        · rw [hall f hf]
          exact mem_zpowers f₁
        · rw [zpowers_le]
          exact subset_closure hf₁
      have hf₁2 : f₁ * f₁ = 1 := Subtype.ext (hA f₁ hf₁).2.2.1
      have h2 : IsPGroup 2 Y := by
        rintro ⟨y, hy⟩
        rw [hYf] at hy
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
        refine ⟨1, Subtype.ext ?_⟩
        simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hf₁2,
          one_zpow]
      have hbot := noNormalTwo_closure_compl12 hτ Y le_rfl h2 le_normalizer
      have : f₁ ∈ Y := subset_closure hf₁
      rw [hbot, mem_bot] at this
      exact (hA f₁ hf₁).2.1 (by rw [this]; rfl)
    · push Not at hall
      obtain ⟨f₂, hf₂, h12⟩ := hall
      refine ⟨f₁, hf₁, f₂, hf₂, fun f hf => ?_⟩
      obtain ⟨p₁, hp₁W, hp₁0, hp₁⟩ := hfixvec f₁ hf₁
      obtain ⟨p₂, hp₂W, hp₂0, hp₂⟩ := hfixvec f₂ hf₂
      obtain ⟨p, hpW, hp0, hp⟩ := hfixvec f hf
      have hY₁ : f₁ ∈ Y := subset_closure hf₁
      have hY₂ : f₂ ∈ Y := subset_closure hf₂
      have hYf : f ∈ Y := subset_closure hf
      have hp12 : p₁ ≠ p₂ := by
        intro e
        apply h12
        exact huniq f₂ hY₂ f₁ hY₁ (hA f₂ hf₂).2.2.1 (hA f₁ hf₁).2.2.1 (hmoved f₂ hf₂)
          (hmoved f₁ hf₁) p₂ hp₂W hp₂0 hp₂ (e ▸ hp₁)
      rcases s12_mem_of_span_pair hWdim hp₁W hp₂W hp₁0 hp₂0 hp12 hpW with h | h | h | h
      · exact absurd h hp0
      · rw [huniq f hYf f₁ hY₁ (hA f hf).2.2.1 (hA f₁ hf₁).2.2.1 (hmoved f hf) (hmoved f₁ hf₁)
          p hpW hp0 hp (h ▸ hp₁)]
        exact subset_closure (by simp)
      · rw [huniq f hYf f₂ hY₂ (hA f hf).2.2.1 (hA f₂ hf₂).2.2.1 (hmoved f hf) (hmoved f₂ hf₂)
          p hpW hp0 hp (h ▸ hp₂)]
        exact subset_closure (by simp)
      ·
        set σ := f₁ * f₂ * f₁ with hσ
        have hσY : σ ∈ Y := Y.mul_mem (Y.mul_mem hY₁ hY₂) hY₁
        have hσmem : σ ∈ closure ({f₁, f₂} : Set S.O) :=
          (Subgroup.closure _).mul_mem ((Subgroup.closure _).mul_mem (subset_closure (by simp))
            (subset_closure (by simp))) (subset_closure (by simp))
        have hf₁2 : f₁ * f₁ = 1 := Subtype.ext (hA f₁ hf₁).2.2.1
        have hf₂2 : f₂ * f₂ = 1 := Subtype.ext (hA f₂ hf₂).2.2.1
        have hσσ : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) * σ = 1 := by
          rw [← Subgroup.coe_mul]
          have : σ * σ = 1 := by
            calc σ * σ = f₁ * f₂ * (f₁ * f₁) * f₂ * f₁ := by rw [hσ]; group
              _ = 1 := by rw [hf₁2, mul_one, mul_assoc f₁, hf₂2, mul_one, hf₁2]
          rw [this]
          rfl
        have hf₁p₂ : (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) p₂ = p₂ + p₁ := by
          rcases s12_apply_eq_or hWdim (hA f₁ hf₁).2.2.1 (hYW f₁ hY₁) (hmoved f₁ hf₁) hp₁W
            hp₁0 hp₁ hp₂W with h' | h'
          · exfalso
            obtain ⟨w, hw, hw1⟩ := hmoved f₁ hf₁
            exact hw1 (s12_fix_of_fix_pair hWdim hp₁W hp₂W hp₁0 hp₂0 hp12 hp₁ h' w hw)
          · exact h'
        have hσp : (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
          have e : p₁ + (p₂ + p₁) = p₂ := by
            rw [add_comm p₂, ← add_assoc, OrthoF2.vec_add_self, zero_add]
          rw [h, hσ, Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
            LinearEquiv.mul_apply, map_add, hp₁, hf₁p₂, e, hp₂, hf₁p₂, add_comm]
        have hσmoved : ∃ w ∈ W, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w := by
          by_contra hc
          push Not at hc
          obtain ⟨w, hw, hw1⟩ := hmoved f₂ hf₂
          apply hw1
          have hw' := hYW f₁ hY₁ w hw
          have e1 := hc _ hw'
          rw [hσ, Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
            LinearEquiv.mul_apply] at e1
          have hff : ∀ v, (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
            intro v
            rw [← LinearEquiv.mul_apply, (hA f₁ hf₁).2.2.1]
            rfl
          rw [hff] at e1
          have := congrArg (f₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) e1
          rwa [hff, hff] at this
        rw [huniq f hYf σ hσY (hA f hf).2.2.1 hσσ (hmoved f hf) hσmoved p hpW hp0 hp hσp]
        exact hσmem
  · intro f hf hbot
    obtain ⟨w, hw, hw1⟩ := hmoved f hf
    have hmem : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
        commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ W :=
      ⟨sub_mem_commSpace _ w, W.sub_mem (hYW f (subset_closure hf) w hw) hw⟩
    rw [hbot] at hmem
    exact hw1 (sub_eq_zero.mp ((Submodule.mem_bot _).mp hmem))

end Setting

end CFSG.LargeExtraspecial
