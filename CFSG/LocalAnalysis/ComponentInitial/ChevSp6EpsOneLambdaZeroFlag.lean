module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricTwoFlagQuadratic
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricTwoFlag

open Module Matrix

def flagP1Sub : Submodule (ZMod 2) FlagW where
  carrier := {v | v.1.1 = 0 ∧ v.2.2 = 0}
  add_mem' := by
    rintro v w ⟨hv1, hv2⟩ ⟨hw1, hw2⟩
    exact ⟨by simp [hv1, hw1], by simp [hv2, hw2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := by
    rintro c v ⟨hv1, hv2⟩
    exact ⟨by simp [hv1], by simp [hv2]⟩

theorem mem_flagP1Sub {v : FlagW} : v ∈ flagP1Sub ↔ v.1.1 = 0 ∧ v.2.2 = 0 :=
  Iff.rfl

def flagPolar (v w : FlagW) : Fin 2 → ZMod 2 :=
  symMat v.1.1 *ᵥ w.2.1 + symMat w.1.1 *ᵥ v.2.1 + v.2.2 • w.1.2 + w.2.2 • v.1.2

theorem flagQuad_add (v w : FlagW) :
    flagQuad (v + w) = flagQuad v + flagQuad w + flagPolar v w := by
  simp only [flagQuad, flagPolar, Prod.fst_add, Prod.snd_add, symMat_add, Matrix.add_mulVec,
    Matrix.mulVec_add, add_smul, smul_add]
  abel

theorem flagPolar_eq_zero {L : Submodule (ZMod 2) FlagW} (hL : ∀ v ∈ L, flagQuad v = 0)
    {v w : FlagW} (hv : v ∈ L) (hw : w ∈ L) : flagPolar v w = 0 := by
  have h := flagQuad_add v w
  rw [hL _ (L.add_mem hv hw), hL v hv, hL w hw, zero_add, zero_add] at h
  exact h.symm

theorem flagLine_abc_coords : ∀ z₀ z₁ a b c : ZMod 2, ¬(z₀ = 0 ∧ z₁ = 0) →
    a * z₀ + b * z₁ = 0 → b * z₀ + c * z₁ = 0 →
    (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = z₁ ∧ b = z₀ * z₁ ∧ c = z₀) := by
  decide

theorem pairing_line_coords (y₀ y₁ z₀ z₁ a b c k₀ k₁ : ZMod 2) (hz : ¬(z₀ = 0 ∧ z₁ = 0))
    (h1 : a * y₀ + b * y₁ + k₀ = 0) (h2 : b * y₀ + c * y₁ + k₁ = 0)
    (h3 : a * z₀ + b * z₁ = 0) (h4 : b * z₀ + c * z₁ = 0) :
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ k₀ = 0 ∧ k₁ = 0) ∨
      (a = z₁ ∧ b = z₀ * z₁ ∧ c = z₀ ∧ k₀ = z₁ * y₀ + z₀ * z₁ * y₁ ∧
        k₁ = z₀ * z₁ * y₀ + z₀ * y₁) := by
  have h2' : (2 : ZMod 2) = 0 := rfl
  have hk₀ : k₀ = a * y₀ + b * y₁ := by linear_combination h1 - (a * y₀ + b * y₁) * h2'
  have hk₁ : k₁ = b * y₀ + c * y₁ := by linear_combination h2 - (b * y₀ + c * y₁) * h2'
  rcases flagLine_abc_coords z₀ z₁ a b c hz h3 h4 with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · subst ha hb hc
    left
    exact ⟨rfl, rfl, rfl, by rw [hk₀]; ring, by rw [hk₁]; ring⟩
  · subst ha hb hc
    right
    exact ⟨rfl, rfl, rfl, hk₀, hk₁⟩

theorem flagGraph_coords (a b c a' b' c' : ZMod 2) (h1 : a = 0) (h2 : b = 0) (h3 : b' = 0)
    (h4 : c' = 0) (h5 : b + a' = 0) (h6 : c + b' = 0) :
    (a = 0 ∧ b = 0 ∧ c = 0) ∧ (a' = 0 ∧ b' = 0 ∧ c' = 0) := by
  subst h1 h2 h3 h4
  rw [zero_add] at h5
  rw [add_zero] at h6
  exact ⟨⟨rfl, rfl, h6⟩, ⟨h5, rfl, rfl⟩⟩

theorem symMat_mulVec_apply (a : Fin 3 → ZMod 2) (y : Fin 2 → ZMod 2) :
    symMat a *ᵥ y = ![a 0 * y 0 + a 1 * y 1, a 1 * y 0 + a 2 * y 1] := by
  ext i
  fin_cases i <;> simp [symMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def flagLine (y y' : Fin 2 → ZMod 2) : FlagU :=
  (![y' 1, y' 0 * y' 1, y' 0],
    ![y' 1 * y 0 + y' 0 * y' 1 * y 1, y' 0 * y' 1 * y 0 + y' 0 * y 1])

theorem mem_span_flagLine {y y' : Fin 2 → ZMod 2} (hy' : y' ≠ 0) {u : FlagU}
    (h1 : pairWith (y, 1) u = 0) (h2 : pairWith (y', 0) u = 0) :
    u ∈ Submodule.span (ZMod 2) {flagLine y y'} := by
  have hy'' : ¬(y' 0 = 0 ∧ y' 1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hy'
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have e1 := (pairWith_eq_zero_iff _ u).1 h1
  have e2 := (pairWith_eq_zero_iff _ u).1 h2
  simp only [one_mul, zero_mul, add_zero] at e1 e2
  rcases pairing_line_coords (y 0) (y 1) (y' 0) (y' 1) (u.1 0) (u.1 1) (u.1 2) (u.2 0) (u.2 1)
    hy'' e1.1 e1.2 e2.1 e2.2 with ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩
  · have hu : u = 0 := flagU_ext h0 h1 h2 h3 h4
    rw [hu]
    exact Submodule.zero_mem _
  · have hu : u = flagLine y y' := flagU_ext h0 h1 h2 h3 h4
    rw [hu]
    exact Submodule.mem_span_singleton_self _

theorem finrank_ker_snd_flagY :
    finrank (ZMod 2) (LinearMap.ker (LinearMap.snd (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2))) = 2 := by
  rw [LinearMap.ker_snd, LinearMap.finrank_range_of_inj LinearMap.inl_injective,
    Module.finrank_fin_fun]

theorem le_flagP1Sub_of_singular (L : Submodule (ZMod 2) FlagW) (hL : ∀ v ∈ L, flagQuad v = 0)
    (h4 : 4 ≤ finrank (ZMod 2) L) (h7 : 7 ≤ finrank (ZMod 2) ↥(L ⊔ flagUSub)) :
    L ≤ flagP1Sub := by
  set f := (LinearMap.snd (ZMod 2) FlagU FlagY).comp L.subtype with hf
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hker2 : ∀ x : LinearMap.ker f, ((x : L) : FlagW).2 = 0 := fun x =>
    LinearMap.mem_ker.mp x.2
  set g := (LinearMap.fst (ZMod 2) FlagU FlagY).comp (L.subtype.comp (LinearMap.ker f).subtype)
    with hg
  have hginj : Function.Injective g := fun x y hxy =>
    Subtype.ext (Subtype.ext (Prod.ext hxy ((hker2 x).trans (hker2 y).symm)))
  have hkerg : finrank (ZMod 2) (LinearMap.ker f) = finrank (ZMod 2) (LinearMap.range g) :=
    (LinearMap.finrank_range_of_inj hginj).symm
  have hpair : ∀ v ∈ LinearMap.range f, LinearMap.range g ≤ LinearMap.ker (pairWith v) := by
    rintro v ⟨l, rfl⟩ _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have hxL : (((x : L) : FlagW).1, (0 : FlagY)) ∈ L := by
      have hx : ((x : L) : FlagW) = (((x : L) : FlagW).1, 0) := Prod.ext rfl (hker2 x)
      rw [← hx]
      exact (x : L).2
    have h1 := hL _ (L.add_mem l.2 hxL)
    rw [flagQuad_add_inl, hL _ l.2, zero_add] at h1
    exact h1
  have hkerle : finrank (ZMod 2) (LinearMap.ker f) ≤ finrank (ZMod 2) ↥(L ⊓ flagUSub) := by
    let k : LinearMap.ker f →ₗ[ZMod 2] ↥(L ⊓ flagUSub) :=
      { toFun := fun x => ⟨((x : L) : FlagW),
          Submodule.mem_inf.2 ⟨(x : L).2, mem_flagUSub.2 (hker2 x)⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine LinearMap.finrank_le_finrank_of_injective (f := k) ?_
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq L flagUSub
  rw [finrank_flagUSub] at hsup
  have hY : finrank (ZMod 2) (LinearMap.range f) ≤ 3 := by
    have h := Submodule.finrank_le (LinearMap.range f)
    rwa [finrank_flagY] at h
  have hr2 : 2 ≤ finrank (ZMod 2) (LinearMap.range f) := by omega
  have hr3 : finrank (ZMod 2) (LinearMap.range f) ≠ 3 := by
    intro hr3
    have htop : LinearMap.range f = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [finrank_flagY]; exact hr3)
    have hk0 : finrank (ZMod 2) (LinearMap.ker f) = 0 := by
      rw [hkerg, Submodule.finrank_eq_zero, eq_bot_iff]
      intro u hu
      rw [Submodule.mem_bot]
      exact eq_zero_of_forall_pairWith fun v => hpair v (htop ▸ Submodule.mem_top) hu
    omega
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have ht : ∀ v ∈ LinearMap.range f, v.2 = 0 := by
    intro v₁ hv₁
    by_contra ht1
    have ht1' : v₁.2 = 1 := (h01 v₁.2).resolve_left ht1
    have hv₁0 : v₁ ≠ 0 := fun h => ht1 (by rw [h]; rfl)
    have hspan : Submodule.span (ZMod 2) {v₁} < LinearMap.range f := by
      refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr hv₁) fun heq => ?_
      have h1 := finrank_span_singleton (K := ZMod 2) hv₁0
      rw [heq] at h1
      omega
    obtain ⟨v₂, hv₂, hv₂n⟩ := IsConcreteLE.exists_of_lt hspan
    have hv₂0 : v₂ ≠ 0 := fun h => hv₂n (h ▸ Submodule.zero_mem _)
    have hv₁₂ : v₁ ≠ v₂ := fun h => hv₂n (h ▸ Submodule.mem_span_singleton_self v₁)
    obtain ⟨v₃, hv₃, hv₃0, hv₃t⟩ : ∃ v₃ ∈ LinearMap.range f, v₃ ≠ 0 ∧ v₃.2 = 0 := by
      rcases h01 v₂.2 with h | h
      · exact ⟨v₂, hv₂, hv₂0, h⟩
      · refine ⟨v₁ + v₂, Submodule.add_mem _ hv₁ hv₂, fun h0 => hv₁₂ ?_, ?_⟩
        · have h2 : v₂ = -v₁ := eq_neg_of_add_eq_zero_right h0
          rw [h2]
          ext i
          · simp [ZMod.neg_eq_self_mod_two]
          · simp [ZMod.neg_eq_self_mod_two]
        · rw [Prod.snd_add, ht1', h]
          rfl
    have hv₃1 : v₃.1 ≠ 0 := fun h => hv₃0 (Prod.ext h hv₃t)
    have hk1 : finrank (ZMod 2) (LinearMap.ker f) ≤ 1 := by
      rw [hkerg]
      have hle : LinearMap.range g ≤ Submodule.span (ZMod 2) {flagLine v₁.1 v₃.1} := by
        intro u hu
        have e1 := hpair v₁ hv₁ hu
        have e3 := hpair v₃ hv₃ hu
        rw [LinearMap.mem_ker] at e1 e3
        have hv₁' : v₁ = (v₁.1, 1) := Prod.ext rfl ht1'
        have hv₃' : v₃ = (v₃.1, 0) := Prod.ext rfl hv₃t
        rw [hv₁'] at e1
        rw [hv₃'] at e3
        exact mem_span_flagLine hv₃1 e1 e3
      exact (Submodule.finrank_mono hle).trans
        (by simpa using finrank_span_le_card ({flagLine v₁.1 v₃.1} : Set FlagU))
    omega
  set T₀ := LinearMap.ker (LinearMap.snd (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2)) with hT₀
  have hfT : LinearMap.range f ≤ T₀ := fun v hv => LinearMap.mem_ker.2 (ht v hv)
  have hfeq : LinearMap.range f = T₀ :=
    Submodule.eq_of_le_of_finrank_eq hfT (by rw [finrank_ker_snd_flagY]; omega)
  have hmemf : ∀ y : Fin 2 → ZMod 2, ∃ w ∈ L, w.2 = (y, 0) := by
    intro y
    have hy : ((y, 0) : FlagY) ∈ LinearMap.range f := by
      rw [hfeq]
      exact LinearMap.mem_ker.2 rfl
    obtain ⟨w, hw⟩ := hy
    exact ⟨w, w.2, hw⟩
  obtain ⟨w₁, hw₁L, hw₁⟩ := hmemf ![1, 0]
  obtain ⟨w₂, hw₂L, hw₂⟩ := hmemf ![0, 1]
  have hq₁ := hL w₁ hw₁L
  have hq₂ := hL w₂ hw₂L
  have hp₁₂ := flagPolar_eq_zero hL hw₁L hw₂L
  simp only [flagQuad, hw₁, hw₂, zero_smul, add_zero, symMat_mulVec_apply] at hq₁ hq₂
  simp only [flagPolar, hw₁, hw₂, zero_smul, add_zero, symMat_mulVec_apply] at hp₁₂
  have hS := flagGraph_coords (w₁.1.1 0) (w₁.1.1 1) (w₁.1.1 2) (w₂.1.1 0) (w₂.1.1 1) (w₂.1.1 2)
    (by simpa using congrFun hq₁ 0) (by simpa using congrFun hq₁ 1)
    (by simpa using congrFun hq₂ 0) (by simpa using congrFun hq₂ 1)
    (by simpa using congrFun hp₁₂ 0) (by simpa using congrFun hp₁₂ 1)
  have hS₁ : w₁.1.1 = 0 := by
    ext i
    fin_cases i
    · exact hS.1.1
    · exact hS.1.2.1
    · exact hS.1.2.2
  have hS₂ : w₂.1.1 = 0 := by
    ext i
    fin_cases i
    · exact hS.2.1
    · exact hS.2.2.1
    · exact hS.2.2.2
  intro v hv
  have hvt : v.2.2 = 0 := ht v.2 ⟨⟨v, hv⟩, rfl⟩
  have hp₁ := flagPolar_eq_zero hL hv hw₁L
  have hp₂ := flagPolar_eq_zero hL hv hw₂L
  simp only [flagPolar, hw₁, hS₁, hvt, zero_smul, add_zero, symMat_mulVec_apply] at hp₁
  simp only [flagPolar, hw₂, hS₂, hvt, zero_smul, add_zero, symMat_mulVec_apply] at hp₂
  refine ⟨?_, hvt⟩
  ext i
  fin_cases i
  · simpa using congrFun hp₁ 0
  · simpa using congrFun hp₁ 1
  · simpa using congrFun hp₂ 1

end CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricTwoFlag
