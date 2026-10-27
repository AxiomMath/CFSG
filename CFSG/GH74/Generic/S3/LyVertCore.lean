module

public import CFSG.GH74.Generic.S3.LyVertSL2
public import CFSG.GH74.Generic.S3.LyVertRank
public import CFSG.GH74.Generic.S3.LyDiagA
public import CFSG.GH74.Generic.S3.Lem610
public import CFSG.GH74.Generic.S3.SL2Out

public section

open CFSG CFSG.GH74 CFSG.GH74.Generic Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.Generic.S3

section Aut

variable {H : Type} [Group H] {L : Subgroup H} {F : Type} [Field F] (e : ↥L ≃* SL(2, F))

@[expose] noncomputable def autOf {t : H} (ht : t ∈ normalizer (L : Set H)) : MulAut SL(2, F) :=
  MulAut.congr e (L.normalizerMonoidHom ⟨t, ht⟩)

theorem autOf_coe {t : H} (ht : t ∈ normalizer (L : Set H)) (x : ↥L) :
    ((e.symm (autOf e ht (e x)) : ↥L) : H) = t * (x : H) * t⁻¹ := by
  simp [autOf, MulAut.congr_apply]

@[expose] def fixL (β : MulAut SL(2, F)) : Subgroup H :=
  ((fixSub β).map e.symm.toMonoidHom).map L.subtype

theorem fixL_le (β : MulAut SL(2, F)) : fixL e β ≤ L := by
  rintro _ ⟨_, _, rfl⟩
  exact Subtype.property _

theorem fixL_comm {t : H} (ht : t ∈ normalizer (L : Set H)) {a : H}
    (ha : a ∈ fixL e (autOf e ht)) : t * a = a * t := by
  obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := ha
  have hx' : autOf e ht x = x := hx
  have h1 : autOf e ht (e (e.symm x)) = e (e.symm x) := by simpa using hx'
  have h2 := autOf_coe e ht (e.symm x)
  rw [h1] at h2
  simp only [MulEquiv.apply_symm_apply] at h2
  change t * ((e.symm x : ↥L) : H) = ((e.symm x : ↥L) : H) * t
  calc t * ((e.symm x : ↥L) : H) = (t * ((e.symm x : ↥L) : H) * t⁻¹) * t := by group
    _ = _ := by rw [← h2]

theorem autOf_sq {t : H} (ht : t ∈ normalizer (L : Set H)) (ht2 : t * t = 1) :
    autOf e ht * autOf e ht = 1 := by
  have h : (⟨t, ht⟩ : ↥(normalizer (L : Set H))) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
  rw [autOf, ← map_mul, ← map_mul, h, map_one, map_one]

theorem exists_sl2_equiv_fixL [Finite F] {σ : F ≃+* F} {P : GL (Fin 2) F} {β : MulAut SL(2, F)}
    (hβ : ∀ a, β a = glConj P (sl2Map σ (glConj P⁻¹ a))) (h2F : (2 : F) ≠ 0) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), ringChar F₀ ≠ 2 ∧
      Nonempty (SL(2, F₀) ≃* ↥(fixL e β)) := by
  obtain ⟨F₀, _, _, ι, hι, ⟨φ⟩⟩ := exists_sl2_equiv_fixSub (β := β) hβ
  refine ⟨F₀, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · intro h
    have h0 : (2 : F₀) = 0 := (ringChar.spec F₀ 2).2 (by rw [h])
    apply h2F
    have h1 : ι (2 : F₀) = 0 := by rw [h0, map_zero]
    have h2 : ι (2 : F₀) = 2 := map_ofNat ι 2
    rw [h2] at h1
    exact h1
  · exact φ.trans (((fixSub β).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((fixSub β).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective))

end Aut

section Normalizer

variable {H : Type} [Group H] {L : Subgroup H}

theorem mem_normalizer_iff_conjSub (t : H) : t ∈ normalizer (L : Set H) ↔ conjSub t L = L := by
  constructor
  · intro ht
    ext h
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp ht l).mp hl
    · intro hh
      refine ⟨t⁻¹ * h * t, ?_, by show t * (t⁻¹ * h * t) * t⁻¹ = h; group⟩
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set H)).inv_mem ht) h).mp hh
      simpa using this
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← h] at hx
      obtain ⟨l, hl, hlx⟩ := hx
      have : l = x := by
        have h1 : t * l * t⁻¹ = t * x * t⁻¹ := hlx
        calc l = t⁻¹ * (t * l * t⁻¹) * t := by group
          _ = t⁻¹ * (t * x * t⁻¹) * t := by rw [h1]
          _ = x := by group
      rw [← this]
      exact hl

end Normalizer


section Core

variable {H : Type} [Group H] [Finite H]

theorem vert_false (hgen : Gen4 H) {L : Subgroup H} (hL : CFSG.IsComponent L) {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (e : ↥L ≃* SL(2, F)) {s : H}
    (hs2 : s * s = 1) (hsN : s ∈ normalizer (L : Set H))
    (hout : autOf e hsN ∉ (glConjHom (F := F)).range) (hcomm : s ∈ commutator H) : False := by
  classical
  have hF2 : ringChar F ≠ 2 := CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hodd
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  set N₁ : Subgroup (MulAut ↥L) :=
    (glConjHom (F := F)).range.comap (MulAut.congr e).toMonoidHom with hN₁
  have hInn : (MulAut.conj : ↥L →* MulAut ↥L).range ≤ N₁ := by
    rintro _ ⟨a, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.toGL (e a), ?_⟩
    refine MulEquiv.ext fun x => ?_
    rw [glConjHom_apply, glConj_toGL]
    simp [MulAut.congr_apply]
  have hN₁c : commutator (MulAut ↥L) ≤ N₁ := (b_SL2_outAbelian F inferInstance inferInstance hodd ↥L inferInstance ⟨e.symm⟩).trans hInn
  have hout' : L.normalizerMonoidHom ⟨s, hsN⟩ ∉ N₁ := fun h => hout h
  have hsL : conjSub s L = L := (mem_normalizer_iff_conjSub s).mp hsN
  have hsL' : conjSub s⁻¹ L = L := by
    have := (mem_normalizer_iff_conjSub s⁻¹).mp ((normalizer (L : Set H)).inv_mem hsN)
    exact this
  have hx : ∀ c : H, c⁻¹ * s * c ∈ normalizer (L : Set H) := by
    intro c
    rw [mem_normalizer_iff_conjSub, conjSub_mul, conjSub_mul]
    by_cases hcL : conjSub c L = L
    · rw [hcL, hsL]
      have := conjSub_inv_conjSub c L
      rwa [hcL] at this
    · have hJc : CFSG.IsComponent (conjSub c L) := isComponent_conjSub hL c
      have hcomp : ∀ M : Subgroup H, CFSG.IsComponent M → M = L ∨ M = conjSub c L := by
        intro M hM
        have hLs : conjSub (c⁻¹)⁻¹ L ≠ L := by rwa [inv_inv]
        have := eq_or_eq_conj_of_gen4 hgen hL hLs hM
        rwa [inv_inv] at this
      have hsJ : conjSub s (conjSub c L) = conjSub c L := by
        rcases hcomp _ (isComponent_conjSub hJc s) with h | h
        · exfalso
          apply hcL
          have := conjSub_inv_conjSub s (conjSub c L)
          rw [h, hsL'] at this
          exact this.symm
        · exact h
      rw [hsJ]
      exact conjSub_inv_conjSub c L
  have hxi_false : ¬ (∀ (c : H) (hc : c⁻¹ * s * c ∈ normalizer (L : Set H)),
      c ∉ normalizer (L : Set H) → L.normalizerMonoidHom ⟨c⁻¹ * s * c, hc⟩ ∈ N₁) := fun hxi =>
    (not_mem_commutator_of_conj_actions L N₁ hN₁c s hx hsN hout' hxi) hcomm
  push Not at hxi_false
  obtain ⟨c, hc, hcn, hcout⟩ := hxi_false
  have hcL : conjSub c L ≠ L := fun h => hcn ((mem_normalizer_iff_conjSub c).mpr h)
  have hJ : CFSG.IsComponent (conjSub c L) := isComponent_conjSub hL c
  have hu2 : (c⁻¹ * s * c) * (c⁻¹ * s * c) = 1 := by
    calc c⁻¹ * s * c * (c⁻¹ * s * c) = c⁻¹ * (s * s) * c := by group
      _ = 1 := by rw [hs2]; group
  have hcout' : autOf e hc ∉ (glConjHom (F := F)).range := fun h => hcout h
  obtain ⟨σ, P, hσ1, hσσ, hβs⟩ :=
    sl2_involution_normal_form hodd h3 (autOf e hsN) (autOf_sq e hsN hs2) hout
  obtain ⟨σ', P', hσ1', hσσ', hβu⟩ :=
    sl2_involution_normal_form hodd h3 (autOf e hc) (autOf_sq e hc hu2) hcout'
  obtain ⟨F₀, _, _, hF₀, ⟨e0⟩⟩ := exists_sl2_equiv_fixL e hβs h2F
  obtain ⟨F₀', _, _, hF₀', ⟨e2''⟩⟩ := exists_sl2_equiv_fixL e hβu h2F
  let e2 : SL(2, F₀') ≃* ↥(conjSub c (fixL e (autOf e hc))) :=
    e2''.trans ((fixL e (autOf e hc)).equivMapOfInjective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective)
  have hLJ : ∀ a ∈ L, ∀ b ∈ conjSub c L, a * b = b * a := by
    rcases CFSG.LocalCores.distinct_components_commute hL hJ with h | h
    · exact absurd h.symm hcL
    · exact fun a ha b hb => mul_comm_of_commutator_eq_bot' h ha hb
  have hY0L : fixL e (autOf e hsN) ≤ L := fixL_le e _
  have hY2J : conjSub c (fixL e (autOf e hc)) ≤ conjSub c L := Subgroup.map_mono (fixL_le e _)
  have hcomm02 : ∀ a ∈ fixL e (autOf e hsN), ∀ b ∈ conjSub c (fixL e (autOf e hc)),
      a * b = b * a := fun a ha b hb => hLJ a (hY0L ha) b (hY2J hb)
  have hw0 : ∀ a ∈ fixL e (autOf e hsN), a * s = s * a := fun a ha => (fixL_comm e hsN ha).symm
  have hw2 : ∀ b ∈ conjSub c (fixL e (autOf e hc)), b * s = s * b := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := fixL_comm e hc ha
    show c * a * c⁻¹ * s = s * (c * a * c⁻¹)
    calc c * a * c⁻¹ * s = c * (a * (c⁻¹ * s * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * s * c) * a) * c⁻¹ := by rw [← h1]
      _ = s * (c * a * c⁻¹) := by group
  have hind : ∀ a ∈ fixL e (autOf e hsN), ∀ b ∈ conjSub c (fixL e (autOf e hc)), s ≠ a * b := by
    intro a ha b hb hab
    have haL : a ∈ L := hY0L ha
    have hbJ : b ∈ conjSub c L := hY2J hb
    apply hout'
    have hconj : L.normalizerMonoidHom ⟨s, hsN⟩ = MulAut.conj (⟨a, haL⟩ : ↥L) := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      show s * (x : H) * s⁻¹ = a * (x : H) * a⁻¹
      have hxb : (x : H) * b = b * (x : H) := hLJ x x.2 b hbJ
      rw [hab]
      calc a * b * (x : H) * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
        _ = a * x * a⁻¹ := by rw [← hxb]; group
    rw [hconj]
    exact hInn ⟨⟨a, haL⟩, rfl⟩
  exact not_gen4_of_sl2_pair_inv₂ hF₀ hF₀' e0 e2 hcomm02 hw0 hw2 hs2 hind hgen

end Core

end CFSG.GH74.Generic.S3
