module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAClose5
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAClose6
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseGen2
public import CFSG.LocalAnalysis.OddStandard.Seitz77Lift4Group

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

section ConjAut

variable {G : Type} [Group G] {F : Type} [Field F] {S₀ : Subgroup G}

@[expose] noncomputable def conjAutHom (e : ↥S₀ ≃* ↥(unipAll F)) (N : Subgroup G)
    (hN : ∀ x ∈ N, ∀ s, s ∈ S₀ ↔ x * s * x⁻¹ ∈ S₀) : ↥N →* MulAut ↥(unipAll F) where
  toFun x := e.symm.trans ((conjOn S₀ x (hN x x.2)).trans e)
  map_one' := by
    refine MulEquiv.ext fun u => ?_
    have h1 : conjOn S₀ (((1 : N) : G)) (hN 1 N.one_mem) (e.symm u) = e.symm u :=
      Subtype.ext (by simp [coe_conjOn])
    show e (conjOn S₀ (((1 : N) : G)) (hN 1 N.one_mem) (e.symm u)) = u
    rw [h1, MulEquiv.apply_symm_apply]
  map_mul' x y := by
    refine MulEquiv.ext fun u => ?_
    have h1 : conjOn S₀ ((x * y : N) : G) (hN (x * y) (x * y).2) (e.symm u) =
        conjOn S₀ (x : G) (hN x x.2) (conjOn S₀ (y : G) (hN y y.2) (e.symm u)) :=
      Subtype.ext (by simp only [coe_conjOn, Subgroup.coe_mul, mul_inv_rev]; group)
    show e (conjOn S₀ ((x * y : N) : G) (hN (x * y) (x * y).2) (e.symm u)) =
      e (conjOn S₀ (x : G) (hN x x.2) (e.symm (e (conjOn S₀ (y : G) (hN y y.2) (e.symm u)))))
    rw [h1, MulEquiv.symm_apply_apply]

theorem conjAutHom_apply (e : ↥S₀ ≃* ↥(unipAll F)) (N : Subgroup G)
    (hN : ∀ x ∈ N, ∀ s, s ∈ S₀ ↔ x * s * x⁻¹ ∈ S₀) (x : N) (s : S₀) :
    conjAutHom e N hN x (e s) = e ⟨x * s * x⁻¹, (hN x x.2 s).1 s.2⟩ := by
  show e (conjOn S₀ (x : G) (hN x x.2) (e.symm (e s))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem conjAutHom_eq_conj (e : ↥S₀ ≃* ↥(unipAll F)) (N : Subgroup G)
    (hN : ∀ x ∈ N, ∀ s, s ∈ S₀ ↔ x * s * x⁻¹ ∈ S₀) (x : N) (hx : (x : G) ∈ S₀) :
    conjAutHom e N hN x = MulAut.conj (e ⟨x, hx⟩) := by
  refine MulEquiv.ext fun u => ?_
  obtain ⟨s, rfl⟩ := e.surjective u
  rw [conjAutHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg e (Subtype.ext (by simp))

end ConjAut


section SwapType

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem autSwap_eq_false_of_map_le (α : MulAut ↥(unipAll F)) (h : ∀ u ∈ radOne F, α u ∈ radOne F) :
    autSwap α = false := by
  by_contra hne
  have htrue : autSwap α = true := by simpa using hne
  have hmap := (autSwap_eq_true_iff_map α).1 htrue
  have hle : (radOne F).map α.toMonoidHom ≤ radOne F := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  rw [hmap] at hle
  have heq : radTwo F = radOne F := Subgroup.eq_of_le_of_card_ge hle (by
    rw [card_radOne, card_radTwo])
  exact radOne_ne_radTwo heq.symm

theorem autSwap_eq_true_of_map_le (α : MulAut ↥(unipAll F)) (h : ∀ u ∈ radOne F, α u ∈ radTwo F) :
    autSwap α = true := by
  rw [autSwap_eq_true_iff_map]
  have hle : (radOne F).map α.toMonoidHom ≤ radTwo F := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective α.injective, card_radOne, card_radTwo]

end SwapType



section Homs

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def fieldHom : MulAut ↥(unipAll F) →* RingAut F :=
  MonoidHom.mk' autField autField_mul

@[expose] noncomputable def swapHom : MulAut ↥(unipAll F) →* Multiplicative (ZMod 2) where
  toFun α := if autSwap α then Multiplicative.ofAdd 1 else 1
  map_one' := by simp [autSwap_eq autData_one]
  map_mul' α β := by
    rw [autSwap_mul]
    cases autSwap α <;> cases autSwap β <;> decide

omit [Finite F] in
theorem fieldHom_apply (α : MulAut ↥(unipAll F)) : fieldHom α = autField α := rfl

omit [Finite F] in
theorem swapHom_eq_one_iff (α : MulAut ↥(unipAll F)) : swapHom α = 1 ↔ autSwap α = false := by
  show (if autSwap α then Multiplicative.ofAdd (1 : ZMod 2) else 1) = 1 ↔ _
  cases autSwap α <;> decide

end Homs

section Hat

variable {G : Type} [Group G] {S₁ T : Subgroup G} {δ : G}

@[expose] def hat (D : Delta S₁ T δ) : Subgroup G := extByElt S₁ δ D.norm D.sq_mem

theorem mem_hat_iff (D : Delta S₁ T δ) {x : G} : x ∈ hat D ↔ x ∈ S₁ ∨ δ⁻¹ * x ∈ S₁ := Iff.rfl

theorem S₁_le_hat (D : Delta S₁ T δ) : S₁ ≤ hat D := fun _ hx => Or.inl hx

theorem delta_mem_hat (D : Delta S₁ T δ) : δ ∈ hat D :=
  Or.inr (by rw [inv_mul_cancel]; exact S₁.one_mem)

theorem hat_le (D : Delta S₁ T δ) (hST : S₁ ≤ T) : hat D ≤ T := by
  rintro x (hx | hx)
  · exact hST hx
  · have : x = δ * (δ⁻¹ * x) := by group
    rw [this]
    exact T.mul_mem D.mem (hST hx)

theorem conj_mem_conjSub {W : Subgroup G} {w : G} (hw : w ∈ W) : δ * w * δ⁻¹ ∈ conjSub δ W := by
  rw [mem_conjSub_iff]
  simpa [mul_assoc] using hw

end Hat

structure SplitEq {G : Type} [Group G] {F : Type} [Field F] (W S₀ : Subgroup G) (κ : G → F)
    (δ : G) (e : ↥S₀ ≃* ↥(unipAll F)) : Prop where
  hκ : ∀ s : S₀, coordB (e s) = κ s
  hW : ∀ s : S₀, (s : G) ∈ W ↔ e s ∈ radOne F
  hW' : ∀ s : S₀, (s : G) ∈ conjSub δ W ↔ e s ∈ radTwo F

section Split2

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {F : Type} [Field F]
  [Finite F] [CharP F 2] {W S₁ S₀ W₀ : Subgroup G} {ι : G → F × F} {κ : G → F}
  {φ : G → RingAut F} (S : SylowA d W S₁ S₀ W₀ ι κ φ)

include S

namespace SylowA

variable {T : Subgroup G} {δ : G}

omit [Finite G] in
theorem conj_conjSub_mem (D : Delta S₁ T δ) {x : G} (hx : x ∈ conjSub δ W) :
    δ * x * δ⁻¹ ∈ W := by
  have h1 : δ⁻¹ * x * δ ∈ W := mem_conjSub_iff.1 hx
  have h2 : (δ * δ) * (δ⁻¹ * x * δ) * (δ * δ)⁻¹ ∈ W := S.normal_W D.sq_mem h1
  have e : (δ * δ) * (δ⁻¹ * x * δ) * (δ * δ)⁻¹ = δ * x * δ⁻¹ := by group
  rwa [e] at h2

omit [Finite G] in
theorem exists_mul_of_mem_S₀ (hle : conjSub δ W ≤ S₀)
    (hκ : ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b) {s : G} (hs : s ∈ S₀) :
    ∃ w ∈ W, ∃ w' ∈ conjSub δ W, s = w * w' := by
  obtain ⟨w', hw', hκw'⟩ := hκ (κ s)
  have hw'S : w' ∈ S₀ := hle hw'
  refine ⟨s * w'⁻¹, ?_, w', hw', by group⟩
  rw [← S.κ_eq_zero_iff _ (S₀.mul_mem hs (S₀.inv_mem hw'S)), S.κ_add s hs w'⁻¹ (S₀.inv_mem hw'S),
    S.κ_inv hw'S, hκw']
  exact add_neg_cancel _

omit [Finite G] in
theorem norm_S₀_of_mem_S₁ {x : G} (hx : x ∈ S₁) : ∀ s, s ∈ S₀ ↔ x * s * x⁻¹ ∈ S₀ := fun s =>
  ⟨S.S₀_normal x hx s, fun h => by simpa [mul_assoc] using S.S₀_normal x⁻¹ (S₁.inv_mem hx) _ h⟩

omit [Finite G] in
theorem norm_S₀_delta (D : Delta S₁ T δ) (hle : conjSub δ W ≤ S₀)
    (hκ : ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b) : ∀ s, s ∈ S₀ ↔ δ * s * δ⁻¹ ∈ S₀ := by
  have fwd : ∀ s ∈ S₀, δ * s * δ⁻¹ ∈ S₀ := by
    intro s hs
    obtain ⟨w, hw, w', hw', rfl⟩ := S.exists_mul_of_mem_S₀ hle hκ hs
    have e : δ * (w * w') * δ⁻¹ = (δ * w * δ⁻¹) * (δ * w' * δ⁻¹) := by group
    rw [e]
    exact S₀.mul_mem (hle (conj_mem_conjSub hw)) (S.W_le_S₀ (S.conj_conjSub_mem D hw'))
  intro s
  refine ⟨fwd s, fun h => ?_⟩
  have h2 := fwd _ h
  have e : δ * (δ * s * δ⁻¹) * δ⁻¹ = (δ * δ) * s * (δ * δ)⁻¹ := by group
  rw [e] at h2
  have h3 := (S.norm_S₀_of_mem_S₁ D.sq_mem s).2 h2
  exact h3

omit [Finite G] in
theorem hat_norm_S₀ (D : Delta S₁ T δ) (hle : conjSub δ W ≤ S₀)
    (hκ : ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b) :
    ∀ x ∈ hat D, ∀ s, s ∈ S₀ ↔ x * s * x⁻¹ ∈ S₀ := by
  rintro x (hx | hx) s
  · exact S.norm_S₀_of_mem_S₁ hx s
  · have e : x * s * x⁻¹ = δ * ((δ⁻¹ * x) * s * (δ⁻¹ * x)⁻¹) * δ⁻¹ := by group
    rw [e, ← S.norm_S₀_delta D hle hκ, ← S.norm_S₀_of_mem_S₁ hx]


omit [Finite G] in
theorem autSwap_rho_of_mem_S₁ (hle : conjSub δ W ≤ S₀)
    (hκ : ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b) (D : Delta S₁ T δ)
    {e : ↥S₀ ≃* ↥(unipAll F)} (E : SplitEq W S₀ κ δ e) (x : ↥(hat D)) (hx : (x : G) ∈ S₁) :
    autSwap (conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ) x) = false := by
  refine autSwap_eq_false_of_map_le _ fun u hu => ?_
  obtain ⟨s, rfl⟩ := e.surjective u
  rw [conjAutHom_apply, ← E.hW]
  rw [← E.hW] at hu
  exact S.normal_W hx hu

omit [Finite G] in
theorem autSwap_rho_delta (hle : conjSub δ W ≤ S₀)
    (hκ : ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b) (D : Delta S₁ T δ)
    {e : ↥S₀ ≃* ↥(unipAll F)} (E : SplitEq W S₀ κ δ e) :
    autSwap (conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ) ⟨δ, delta_mem_hat D⟩) = true := by
  refine autSwap_eq_true_of_map_le _ fun u hu => ?_
  obtain ⟨s, rfl⟩ := e.surjective u
  rw [conjAutHom_apply, ← E.hW']
  rw [← E.hW] at hu
  exact conj_mem_conjSub hu

omit [Finite G] in
theorem autField_rho_of_mem_S₁ (hle : conjSub δ W ≤ S₀)
    (hκ : ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b) (D : Delta S₁ T δ)
    {e : ↥S₀ ≃* ↥(unipAll F)} (E : SplitEq W S₀ κ δ e) (x : ↥(hat D)) (hx : (x : G) ∈ S₁) :
    autField (conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ) x) = φ x := by
  have hsw := S.autSwap_rho_of_mem_S₁ hle hκ D E x hx
  obtain ⟨σ, l, m, sw, hd⟩ := aut_data (conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ) x)
  have hsw' : sw = false := (autSwap_eq hd).symm.trans hsw
  subst hsw'
  rw [autField_eq hd]
  obtain ⟨l', hl', hκx⟩ := S.conj_κ x hx
  have key : ∀ s : S₀, (m : F) * σ (κ s) = l' * φ x (κ s) := by
    intro s
    have h1 := hd.coordB_eq (e s)
    simp only [Bool.false_eq_true, ite_false] at h1
    rw [conjAutHom_apply, E.hκ, E.hκ] at h1
    exact h1.symm.trans (hκx s s.2)
  obtain ⟨s₁, hs₁, hκs₁⟩ := S.κ_surj 1
  have hml : (m : F) = l' := by
    have := key ⟨s₁, hs₁⟩
    simpa [hκs₁] using this
  refine RingEquiv.ext fun b => ?_
  obtain ⟨s, hs, hκs⟩ := S.κ_surj b
  have := key ⟨s, hs⟩
  rw [hκs, ← hml] at this
  exact mul_left_cancel₀ m.ne_zero this


omit [Finite G] in
theorem mem_S₀_iff_rho (hle : conjSub δ W ≤ S₀) (hκ : ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b)
    (D : Delta S₁ T δ) {e : ↥S₀ ≃* ↥(unipAll F)} (E : SplitEq W S₀ κ δ e) (x : ↥(hat D)) :
    (x : G) ∈ S₀ ↔ fieldHom (conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ) x) = 1 ∧
      swapHom (conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ) x) = 1 := by
  constructor
  · intro hx
    rw [conjAutHom_eq_conj e _ _ x hx]
    exact ⟨autField_conj _, (swapHom_eq_one_iff _).2 (autSwap_conj _)⟩
  · rintro ⟨h1, h2⟩
    rcases (mem_hat_iff D).1 x.2 with hx | hx
    · have h3 := S.autField_rho_of_mem_S₁ hle hκ D E x hx
      rw [fieldHom_apply, h3] at h1
      exact (S.φ_eq_one_iff x hx).1 h1
    · exfalso
      have hmul : x = ⟨δ, delta_mem_hat D⟩ * ⟨δ⁻¹ * x, S₁_le_hat D hx⟩ :=
        Subtype.ext (by simp)
      have hδ := S.autSwap_rho_delta hle hκ D E
      have ha := S.autSwap_rho_of_mem_S₁ hle hκ D E ⟨δ⁻¹ * x, S₁_le_hat D hx⟩ hx
      rw [hmul, map_mul, map_mul, (swapHom_eq_one_iff _).2 ha, mul_one,
        swapHom_eq_one_iff] at h2
      rw [hδ] at h2
      exact Bool.noConfusion h2


omit [Finite G] in
theorem card_inf_centralizer_le_of_rho (hle : conjSub δ W ≤ S₀)
    (hκ : ∀ b : F, ∃ w ∈ conjSub δ W, κ w = b) (D : Delta S₁ T δ)
    {e : ↥S₀ ≃* ↥(unipAll F)} (y : ↥(hat D)) (hy2 : (y : G) * y = 1)
    (hψ : fieldHom (conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ) y) = 1)
    (hε : swapHom (conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ) y) ≠ 1) :
    Nat.card ↥(S₀ ⊓ centralizer ({(y : G)} : Set G)) ≤ 16 := by
  set α := conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ) y with hα
  have hsw : autSwap α = true := by
    by_contra h
    exact hε ((swapHom_eq_one_iff α).2 (by simpa using h))
  have hα2 : ∀ g, α (α g) = g := by
    intro g
    obtain ⟨s, rfl⟩ := e.surjective g
    rw [hα, conjAutHom_apply, conjAutHom_apply]
    congr 1
    refine Subtype.ext ?_
    show (y : G) * ((y : G) * s * (y : G)⁻¹) * (y : G)⁻¹ = s
    calc (y : G) * ((y : G) * s * (y : G)⁻¹) * (y : G)⁻¹
        = ((y : G) * y) * s * ((y : G) * y)⁻¹ := by group
      _ = s := by rw [hy2]; group
  have hfield : autField α = 1 := hψ
  obtain ⟨-, β, hβ⟩ := exists_conj_graphField_of_swap α hα2 hsw
  rw [hfield] at hβ
  have hgr : ∀ g, graphFieldAut (1 : RingAut F) g = graphAut g := by
    intro g
    obtain ⟨a, b, c, rfl⟩ := exists_uelt g
    rw [graphFieldAut_uelt, graphAut_uelt]
    simp
  have e1 : ↥(S₀ ⊓ centralizer ({(y : G)} : Set G)) ≃ ↥(fixSubgroup α) :=
    { toFun := fun s => ⟨e ⟨s.1, s.2.1⟩, by
        show α (e ⟨s.1, s.2.1⟩) = e ⟨s.1, s.2.1⟩
        rw [hα, conjAutHom_apply]
        congr 1
        refine Subtype.ext ?_
        show (y : G) * s.1 * (y : G)⁻¹ = s.1
        rw [mul_inv_eq_iff_eq_mul]
        exact (mem_centralizer_singleton_iff.mp s.2.2).symm⟩
      invFun := fun u => ⟨(e.symm u : G), (e.symm u).2, by
        show (e.symm u : G) ∈ centralizer ({(y : G)} : Set G)
        rw [mem_centralizer_singleton_iff]
        have h1 : α (e (e.symm u)) = e (e.symm u) := by
          rw [MulEquiv.apply_symm_apply]
          exact u.2
        have h1' : conjAutHom e (hat D) (S.hat_norm_S₀ D hle hκ) y (e (e.symm u)) =
            e (e.symm u) := h1
        rw [conjAutHom_apply] at h1'
        have h2 := e.injective h1'
        have h3 : (y : G) * (e.symm u : G) * (y : G)⁻¹ = (e.symm u : G) := congrArg Subtype.val h2
        rw [mul_inv_eq_iff_eq_mul] at h3
        exact h3.symm⟩
      left_inv := fun s => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp) }
  have e2 : ↥(fixSubgroup α) ≃ ↥(fixSubgroup (graphAut : MulAut ↥(unipAll F))) :=
    { toFun := fun u => ⟨β u.1, by
        show graphAut (β u.1) = β u.1
        rw [← hgr, ← hβ, show α u.1 = u.1 from u.2]⟩
      invFun := fun v => ⟨β.symm v.1, by
        show α (β.symm v.1) = β.symm v.1
        apply β.injective
        rw [hβ, hgr, MulEquiv.apply_symm_apply]
        exact v.2⟩
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  rw [Nat.card_congr (e1.trans e2), fixSubgroup_graphAut, card_radCenter, S.card_F]

end SylowA

end Split2

end CFSG.OddStandard.Seitz77
