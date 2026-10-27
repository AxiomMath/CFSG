module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace SpClosure

open Subgroup

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def isom (B : LinearMap.BilinForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, B (g x) (g y) = B x y}
  mul_mem' {a b} ha hb := fun x y => by
    simp only [LinearEquiv.mul_apply]; rw [ha, hb]
  one_mem' := fun x y => rfl
  inv_mem' {a} ha := fun x y => by
    have := ha (a.symm x) (a.symm y)
    simpa using this.symm

variable {B : LinearMap.BilinForm K V}

theorem mem_isom {g : V ≃ₗ[K] V} : g ∈ isom B ↔ ∀ x y, B (g x) (g y) = B x y := Iff.rfl

theorem isom_ext {g h : isom B} (H : ∀ x : V, g • x = h • x) : g = h :=
  Subtype.ext (LinearEquiv.ext H)

theorem B_smul (g : isom B) (x y : V) : B (g • x) (g • y) = B x y := g.2 x y

theorem B_inv_smul (g : isom B) (x y : V) : B (g⁻¹ • x) y = B x (g • y) := by
  rw [← B_smul g (g⁻¹ • x) y, smul_inv_smul]

theorem smul_smul_K (g : isom B) (c : K) (x : V) : g • (c • x) = c • (g • x) :=
  map_smul (g : V ≃ₗ[K] V) c x

@[expose] def stab (U : Submodule K V) : Subgroup (isom B) where
  carrier := {g | ∀ x, g • x ∈ U ↔ x ∈ U}
  mul_mem' {a b} ha hb := fun x => by rw [mul_smul, ha, hb]
  one_mem' := fun x => by simp
  inv_mem' {a} ha := fun x => by
    have := ha (a⁻¹ • x)
    rw [smul_inv_smul] at this
    exact this.symm

theorem mem_stab_of_forall {U : Submodule K V} {g : isom B} (h1 : ∀ x ∈ U, g • x ∈ U)
    (h2 : ∀ x ∈ U, g⁻¹ • x ∈ U) : g ∈ stab U := fun x =>
  ⟨fun hx => by simpa using h2 _ hx, h1 x⟩

theorem smul_mem_of_mem_stab {U : Submodule K V} {g : isom B} (hg : g ∈ stab U) {x : V}
    (hx : x ∈ U) : g • x ∈ U := (hg x).2 hx

theorem inv_smul_mem_of_mem_stab {U : Submodule K V} {g : isom B} (hg : g ∈ stab U) {x : V}
    (hx : x ∈ U) : g⁻¹ • x ∈ U := smul_mem_of_mem_stab ((stab U).inv_mem hg) hx

theorem smul_mem_orth_iff {U : Submodule K V} {g : isom B} (hg : g ∈ stab U) (y : V) :
    g • y ∈ B.orthogonal U ↔ y ∈ B.orthogonal U := by
  simp only [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h n hn
    have := h (g • n) (smul_mem_of_mem_stab hg hn)
    rwa [B_smul] at this
  · intro h n hn
    rw [← B_inv_smul]
    exact h _ (inv_smul_mem_of_mem_stab hg hn)

theorem le_stab_of_invariant {U : Submodule K V} {E : Subgroup (isom B)}
    (h : ∀ e ∈ E, ∀ x ∈ U, e • x ∈ U) : E ≤ stab U := fun e he =>
  mem_stab_of_forall (h e he) (h e⁻¹ (E.inv_mem he))

section Transvection

variable (hB : B.IsAlt)

@[expose] def tvLin (B : LinearMap.BilinForm K V) (v : V) (c : K) : V →ₗ[K] V :=
  LinearMap.id + (c • B.flip v).smulRight v

theorem tvLin_apply (v : V) (c : K) (x : V) : tvLin B v c x = x + (c * B x v) • v := by
  simp [tvLin]

theorem tvLin_comp {v : V} (hv : B v v = 0) (c c' : K) :
    tvLin B v c ∘ₗ tvLin B v c' = tvLin B v (c + c') := by
  ext x
  simp only [LinearMap.comp_apply, tvLin_apply, map_add, map_smul, hv, mul_zero]
  module

theorem tvLin_zero (v : V) : tvLin B v 0 = LinearMap.id := by
  ext x
  simp [tvLin_apply]

@[expose] def tvEquiv (B : LinearMap.BilinForm K V) {v : V} (hv : B v v = 0) (c : K) :
    V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (tvLin B v c) (tvLin B v (-c))
    (by rw [tvLin_comp hv, add_neg_cancel, tvLin_zero])
    (by rw [tvLin_comp hv, neg_add_cancel, tvLin_zero])

theorem tvEquiv_apply {v : V} (hv : B v v = 0) (c : K) (x : V) :
    tvEquiv B hv c x = x + (c * B x v) • v := tvLin_apply v c x

@[expose] def tv (v : V) (c : K) : isom B :=
  ⟨tvEquiv B (hB.self_eq_zero v) c, fun x y => by
    rw [tvEquiv_apply, tvEquiv_apply]
    have h1 : B v y = - B y v := (LinearMap.IsAlt.neg hB y v).symm
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero v, h1]
    ring⟩

theorem tv_smul (v : V) (c : K) (x : V) : tv hB v c • x = x + (c * B x v) • v := rfl

theorem tv_add (v : V) (c c' : K) : tv hB v c * tv hB v c' = tv hB v (c + c') :=
  isom_ext fun x => by
    simp only [mul_smul, tv_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hB.self_eq_zero v, smul_eq_mul, mul_zero]
    module

theorem tv_zero (v : V) : tv hB v 0 = 1 :=
  isom_ext fun x => by simp [tv_smul]

theorem tv_inv (v : V) (c : K) : (tv hB v c)⁻¹ = tv hB v (-c) :=
  inv_eq_of_mul_eq_one_right (by rw [tv_add, add_neg_cancel, tv_zero])

theorem tv_conj (g : isom B) (v : V) (c : K) : g * tv hB v c * g⁻¹ = tv hB (g • v) c :=
  isom_ext fun x => by
    rw [mul_smul, mul_smul, tv_smul, tv_smul, smul_add, smul_smul_K, B_inv_smul, smul_inv_smul]

theorem tv_ne_one (hnd : B.Nondegenerate) {w : V} (hw : w ≠ 0) {c : K} (hc : c ≠ 0) :
    tv hB w c ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ : ∃ x, B x w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw (hnd.2 w hcon)
  have := congrArg (fun g : isom B => g • x) h
  simp only [tv_smul, one_smul, add_eq_left, smul_eq_zero] at this
  rcases this with h | h
  · exact mul_ne_zero hc hx h
  · exact hw h

end Transvection

section Unipotent

variable (B)

@[expose] def Q (U : Submodule K V) : Subgroup (isom B) where
  carrier := {g | (∀ x ∈ B.orthogonal U, g • x = x) ∧ ∀ x, g • x - x ∈ U}
  mul_mem' {a b} ha hb := by
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · rw [mul_smul, hb.1 x hx, ha.1 x hx]
    · have := U.add_mem (ha.2 (b • x)) (hb.2 x)
      rw [mul_smul]
      simpa using this
  one_mem' := ⟨fun x _ => one_smul _ x, fun x => by simp⟩
  inv_mem' {a} ha := by
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · have := ha.1 x hx
      calc a⁻¹ • x = a⁻¹ • (a • x) := by rw [this]
        _ = x := inv_smul_smul a x
    · have h := ha.2 (a⁻¹ • x)
      rw [smul_inv_smul] at h
      have := U.neg_mem h
      simpa using this

variable {B}

theorem conj_mem_Q {U : Submodule K V} {h q : isom B} (hh : h ∈ stab U) (hq : q ∈ Q B U) :
    h * q * h⁻¹ ∈ Q B U := by
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · have hx' : h⁻¹ • x ∈ B.orthogonal U := (smul_mem_orth_iff ((stab U).inv_mem hh) x).2 hx
    rw [mul_smul, mul_smul, hq.1 _ hx', smul_inv_smul]
  · rw [mul_smul, mul_smul]
    have := smul_mem_of_mem_stab hh (hq.2 (h⁻¹ • x))
    rwa [smul_sub, smul_inv_smul] at this

theorem stab_le_normalizer_Q (U : Submodule K V) :
    stab U ≤ normalizer (Q B U : Set (isom B)) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro q
  constructor
  · exact fun hq => conj_mem_Q hh hq
  · intro hq
    have := conj_mem_Q ((stab U).inv_mem hh) hq
    simpa [mul_assoc] using this

theorem Q_mul_self [CharP K 2] {U : Submodule K V} (hU : U ≤ B.orthogonal U) {g : isom B}
    (hg : g ∈ Q B U) : g * g = 1 := by
  refine isom_ext fun x => ?_
  rw [mul_smul, one_smul]
  have hfix : g • (g • x - x) = g • x - x := hg.1 _ (hU (hg.2 x))
  rw [smul_sub, sub_eq_iff_eq_add] at hfix
  rw [hfix]
  generalize g • x = y
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : y - x + y = (2 : K) • y - (2 : K) • x + x := by module
  rw [this, h2]
  simp

theorem isPGroup_two_Q [CharP K 2] {U : Submodule K V} (hU : U ≤ B.orthogonal U) :
    IsPGroup 2 (Q B U) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [pow_one, sq] using Q_mul_self hU g.2

end Unipotent

section Closure

variable (hB : B.IsAlt)

include hB

theorem tv_mem_Q {U : Submodule K V} {w : V} (hw : w ∈ U) (c : K) : tv hB w c ∈ Q B U := by
  refine ⟨fun x hx => ?_, fun x => ?_⟩
  · have h1 : B w x = 0 := LinearMap.BilinForm.mem_orthogonal_iff.1 hx w hw
    have h2 : B x w = 0 := by rw [← LinearMap.IsAlt.neg hB w x, h1, neg_zero]
    rw [tv_smul, h2]
    simp
  · rw [tv_smul, add_sub_cancel_left]
    exact U.smul_mem _ hw

theorem Q_ne_bot (hnd : B.Nondegenerate) {U : Submodule K V} (hU : U ≠ ⊥) : Q B U ≠ ⊥ := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  intro h
  have hmem : tv hB w 1 ∈ Q B U := tv_mem_Q hB hw 1
  rw [h, Subgroup.mem_bot] at hmem
  exact tv_ne_one hB hnd hw0 one_ne_zero hmem

theorem stab_le_twoLocalClosure [CharP K 2] (hnd : B.Nondegenerate) {U : Submodule K V}
    (hU0 : U ≠ ⊥) (hU : U ≤ B.orthogonal U) {E : Subgroup (isom B)} (hE : E ≤ stab U) :
    stab U ≤ twoLocalClosure E :=
  le_iSup₂_of_le (normalizer (Q B U : Set (isom B)))
    ⟨⟨Q B U, Q_ne_bot hB hnd hU0, isPGroup_two_Q hU, rfl⟩, hE.trans (stab_le_normalizer_Q U)⟩
    (stab_le_normalizer_Q U)

theorem tv_mem_stab_of_mem {U : Submodule K V} {w : V} (hw : w ∈ U) (c : K) :
    tv hB w c ∈ stab U := by
  apply mem_stab_of_forall
  · intro x hx
    rw [tv_smul]
    exact U.add_mem hx (U.smul_mem _ hw)
  · intro x hx
    rw [tv_inv, tv_smul]
    exact U.add_mem hx (U.smul_mem _ hw)

theorem tv_mem_stab_of_orth {U : Submodule K V} {a : V} (ha : a ∈ B.orthogonal U) (c : K) :
    tv hB a c ∈ stab U := by
  have key : ∀ (c : K), ∀ x ∈ U, tv hB a c • x ∈ U := by
    intro c x hx
    have : B x a = 0 := LinearMap.BilinForm.mem_orthogonal_iff.1 ha x hx
    rw [tv_smul, this]
    simpa using hx
  exact mem_stab_of_forall (key c) (fun x hx => by rw [tv_inv]; exact key (-c) x hx)

theorem tv_mem_of_stab_le {W X : Submodule K V} (hW0 : W ≤ B.orthogonal W)
    (hc : IsCompl X (B.orthogonal W)) {C : Subgroup (isom B)} (hWC : stab W ≤ C)
    (hXC : stab X ≤ C) (v : V) (c : K) : tv hB v c ∈ C := by
  have hv : v ∈ X ⊔ B.orthogonal W := by rw [hc.sup_eq_top]; trivial
  obtain ⟨x, hx, a, ha, rfl⟩ := Submodule.mem_sup.1 hv
  by_cases hx0 : x = 0
  · subst hx0
    rw [zero_add]
    exact hWC (tv_mem_stab_of_orth hB ha c)
  have hxW : x ∉ B.orthogonal W := fun h => hx0 (by
    have : x ∈ X ⊓ B.orthogonal W := ⟨hx, h⟩
    rwa [hc.inf_eq_bot, Submodule.mem_bot] at this)
  obtain ⟨w, hw, hBw⟩ : ∃ w ∈ W, B w x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hxW (LinearMap.BilinForm.mem_orthogonal_iff.2 hcon)
  have hBxw : B x w ≠ 0 := by
    rw [← LinearMap.IsAlt.neg hB w x]
    exact neg_ne_zero.2 hBw
  have hBaw : B a w = 0 := by
    have h1 : B w a = 0 := LinearMap.BilinForm.mem_orthogonal_iff.1 ha w hw
    rw [← LinearMap.IsAlt.neg hB w a, h1, neg_zero]
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : K, B a x - c₁ * (B x w * B x w) ≠ 0 := by
    by_cases h : B a x = 0
    · exact ⟨1, by simpa [h] using hBxw⟩
    · exact ⟨0, by simpa using h⟩
  set a' : V := a + (c₁ * B x w) • w with ha'
  have ha'W : a' ∈ B.orthogonal W :=
    (B.orthogonal W).add_mem ha ((B.orthogonal W).smul_mem _ (hW0 hw))
  have hBa'x : B a' x = B a x - c₁ * (B x w * B x w) := by
    have h1 : B w x = - B x w := (LinearMap.IsAlt.neg hB x w).symm
    simp only [ha', map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1]
    ring
  set h₁ : isom B := tv hB w c₁ with hh₁
  set h₂ : isom B := tv hB x (-(B a' x)⁻¹) with hh₂
  have hh₁C : h₁ ∈ C := hWC (tv_mem_stab_of_mem hB hw c₁)
  have hh₂C : h₂ ∈ C := hXC (tv_mem_stab_of_mem hB hx _)
  have hne : B a' x ≠ 0 := by rw [hBa'x]; exact hc₁
  have hkey : (h₂ * h₁) • (x + a) = a' := by
    have e1 : h₁ • (x + a) = x + a' := by
      rw [hh₁, tv_smul]
      simp only [ha', map_add, LinearMap.add_apply, hBaw, add_zero]
      module
    rw [mul_smul, e1, hh₂, tv_smul]
    simp only [map_add, LinearMap.add_apply, hB.self_eq_zero x, zero_add]
    have : (-(B a' x)⁻¹ * B a' x) = -1 := by field_simp
    rw [this]
    module
  have hconj := tv_conj hB (h₂ * h₁) (x + a) c
  rw [hkey] at hconj
  have hmem : tv hB a' c ∈ C := hWC (tv_mem_stab_of_orth hB ha'W c)
  have hhC : h₂ * h₁ ∈ C := C.mul_mem hh₂C hh₁C
  have : tv hB (x + a) c = (h₂ * h₁)⁻¹ * tv hB a' c * (h₂ * h₁) := by
    rw [← hconj]; group
  rw [this]
  exact C.mul_mem (C.mul_mem (C.inv_mem hhC) hmem) hhC

theorem eq_top_of_tv_mem [IsSimpleGroup (isom B)] (hnd : B.Nondegenerate) {v₀ : V}
    (hv₀ : v₀ ≠ 0) {C : Subgroup (isom B)} (hC : ∀ v c, tv hB v c ∈ C) : C = ⊤ := by
  set S : Set (isom B) := {g | ∃ v c, g = tv hB v c} with hS
  have hN : (Subgroup.normalClosure S).Normal := Subgroup.normalClosure_normal
  have hne : Subgroup.normalClosure S ≠ ⊥ := by
    intro h
    have hmem : tv hB v₀ 1 ∈ Subgroup.normalClosure S :=
      Subgroup.subset_normalClosure ⟨v₀, 1, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact tv_ne_one hB hnd hv₀ one_ne_zero hmem
  have htop := (IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.normalClosure S)).resolve_left hne
  have hle : Subgroup.normalClosure S ≤ C := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro g hg
    rw [Group.mem_conjugatesOfSet_iff] at hg
    obtain ⟨b, ⟨v, c, rfl⟩, hbg⟩ := hg
    rw [isConj_iff] at hbg
    obtain ⟨d, rfl⟩ := hbg
    rw [tv_conj]
    exact hC _ _
  exact top_le_iff.mp (htop ▸ hle)

end Closure

end SpClosure

end CFSG.LocalAnalysis.RankThreeUC
