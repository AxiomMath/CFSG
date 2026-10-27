module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.IVK.Lifted.QuatAut

public section

open Subgroup CFSG
open scoped commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

variable {G : Type} [Group G]

theorem mem_sup_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
        one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
          have := h a' ha' b hb
          calc a * a' * (b * b') = a * (a' * b) * b' := by group
            _ = a * (b * a') * b' := by rw [this]
            _ = a * b * (a' * b') := by group
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
          have := h a ha b hb
          calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
            _ = (a * b)⁻¹ := by rw [← this] }
    have hA : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
    have hB : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩
    exact sup_le hA hB hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem mem_sup_of_normalizes {E L : Subgroup G} (h : ∀ l ∈ L, ∀ e ∈ E, l * e * l⁻¹ ∈ E) {x : G}
    (hx : x ∈ E ⊔ L) : ∃ e ∈ E, ∃ l ∈ L, x = e * l := by
  let S : Subgroup G :=
    { carrier := {x | ∃ e ∈ E, ∃ l ∈ L, x = e * l}
      one_mem' := ⟨1, E.one_mem, 1, L.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨e, he, l, hl, rfl⟩ ⟨e', he', l', hl', rfl⟩
        refine ⟨e * (l * e' * l⁻¹), E.mul_mem he (h l hl e' he'), l * l', L.mul_mem hl hl', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨e, he, l, hl, rfl⟩
        refine ⟨l⁻¹ * e⁻¹ * l⁻¹⁻¹, h l⁻¹ (L.inv_mem hl) e⁻¹ (E.inv_mem he), l⁻¹, L.inv_mem hl, ?_⟩
        group }
  have hE : E ≤ S := fun e he => ⟨e, he, 1, L.one_mem, by simp⟩
  have hL : L ≤ S := fun l hl => ⟨1, E.one_mem, l, hl, by simp⟩
  exact sup_le hE hL hx

theorem commutator_mul_mul_of_commute {b b' l l' : G} (hbl : Commute b l) (hbb' : Commute b b')
    (hbl' : Commute b l') (hb'l : Commute b' l) (hb'l' : Commute b' l') :
    ⁅b * l, b' * l'⁆ = ⁅l, l'⁆ := by
  simp only [commutatorElement_def]
  have hw : Commute b (l * b' * l' * l⁻¹) :=
    (((hbl.mul_right hbb'.symm.symm)).mul_right hbl').mul_right hbl.inv_right
  have h1 : b * (l * b' * l' * l⁻¹) * b⁻¹ = l * b' * l' * l⁻¹ := hw.mul_inv_cancel
  have hQ : Commute b' (l * l' * l⁻¹ * l'⁻¹) :=
    ((hb'l.mul_right hb'l').mul_right hb'l.inv_right).mul_right hb'l'.inv_right
  have h2 : b' * (l * l' * l⁻¹ * l'⁻¹) * b'⁻¹ = l * l' * l⁻¹ * l'⁻¹ := hQ.mul_inv_cancel
  calc b * l * (b' * l') * (b * l)⁻¹ * (b' * l')⁻¹
      = (b * (l * b' * l' * l⁻¹) * b⁻¹) * l'⁻¹ * b'⁻¹ := by group
    _ = (l * b' * l' * l⁻¹) * l'⁻¹ * b'⁻¹ := by rw [h1]
    _ = (l * b') * l' * l⁻¹ * l'⁻¹ * b'⁻¹ := by group
    _ = (b' * l) * l' * l⁻¹ * l'⁻¹ * b'⁻¹ := by rw [← hb'l.eq]
    _ = b' * (l * l' * l⁻¹ * l'⁻¹) * b'⁻¹ := by group
    _ = l * l' * l⁻¹ * l'⁻¹ := h2

theorem perfect_le_complement {E L' M B : Subgroup G} {c : G}
    (hnorm : ∀ l ∈ L', ∀ e ∈ E, l * e * l⁻¹ ∈ E) (hdisj : ∀ x ∈ E, x ∈ L' → x = 1)
    (hM : M ≤ E ⊔ L') (hMp : ⁅M, M⁆ = M) (hc : c ∈ L') (hMc : ∀ m ∈ M, m * c = c * m)
    (hB : ∀ e ∈ E, c * e * c⁻¹ = e → e ∈ B) (hBab : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hBM : ∀ b ∈ B, ∀ m ∈ M, b * m = m * b) : M ≤ L' := by
  have hdec : ∀ m ∈ M, ∃ b ∈ B, ∃ l ∈ L', m = b * l := by
    intro m hm
    obtain ⟨e, he, l, hl, rfl⟩ := mem_sup_of_normalizes hnorm (hM hm)
    refine ⟨e, hB e he ?_, l, hl, rfl⟩
    have he' : c * e * c⁻¹ ∈ E := hnorm c hc e he
    have hl' : c * l * c⁻¹ ∈ L' := L'.mul_mem (L'.mul_mem hc hl) (L'.inv_mem hc)
    have h1 : (c * e * c⁻¹) * (c * l * c⁻¹) = e * l := by
      have := hMc (e * l) hm
      calc (c * e * c⁻¹) * (c * l * c⁻¹) = c * (e * l) * c⁻¹ := by group
        _ = (e * l * c) * c⁻¹ := by rw [← this]
        _ = e * l := by group
    have h2 : e⁻¹ * (c * e * c⁻¹) = l * (c * l * c⁻¹)⁻¹ := by
      have : c * e * c⁻¹ = e * l * (c * l * c⁻¹)⁻¹ := by
        rw [← h1]; group
      rw [this]; group
    have hx1 : e⁻¹ * (c * e * c⁻¹) ∈ E := E.mul_mem (E.inv_mem he) he'
    have hx2 : e⁻¹ * (c * e * c⁻¹) ∈ L' := by
      rw [h2]; exact L'.mul_mem hl (L'.inv_mem hl')
    have hx := hdisj _ hx1 hx2
    have h3 : e * (e⁻¹ * (c * e * c⁻¹)) = e * 1 := by rw [hx]
    simpa using h3
  have hcomm : ∀ m ∈ M, ∀ m' ∈ M, ⁅m, m'⁆ ∈ L' := by
    intro m hm m' hm'
    obtain ⟨b, hb, l, hl, rfl⟩ := hdec m hm
    obtain ⟨b', hb', l', hl', rfl⟩ := hdec m' hm'
    have hbb' : Commute b b' := hBab b hb b' hb'
    have hbm : Commute b (b * l) := hBM b hb _ hm
    have hbl : Commute b l := by simpa using (Commute.refl b).inv_right.mul_right hbm
    have hbm' : Commute b (b' * l') := hBM b hb _ hm'
    have hbl' : Commute b l' := by simpa using hbb'.inv_right.mul_right hbm'
    have hb'm : Commute b' (b * l) := hBM b' hb' _ hm
    have hb'l : Commute b' l := by simpa using hbb'.symm.inv_right.mul_right hb'm
    have hb'm' : Commute b' (b' * l') := hBM b' hb' _ hm'
    have hb'l' : Commute b' l' := by simpa using (Commute.refl b').inv_right.mul_right hb'm'
    rw [commutator_mul_mul_of_commute hbl hbb' hbl' hb'l hb'l']
    simp only [commutatorElement_def]
    exact L'.mul_mem (L'.mul_mem (L'.mul_mem hl hl') (L'.inv_mem hl)) (L'.inv_mem hl')
  have := Subgroup.commutator_le.mpr hcomm
  rwa [hMp] at this

end CFSG.GH74.GLS.LU.Local.Five
