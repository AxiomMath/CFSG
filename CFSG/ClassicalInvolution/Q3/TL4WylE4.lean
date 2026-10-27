module

public import CFSG.ClassicalInvolution.Q3.TL4WylE3
public import CFSG.ClassicalInvolution.Q3.TL4SecClqE2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Wyl

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent AEIdentOn ThmDHyp)

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem false_of_triangle_of_labels (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 5 ≤ m) (hm7 : m ≤ 7)
    (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    (hlabel : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ (α : Finset (Fin m))
      (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α h b)
    {B₁ B₂ : Subgroup Y}
    (hB₁ : B₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hB₂ : B₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) B₁)
    (hB₂K : B₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) : False := by
  have hK := CoreAssembly.mem_conjClass_self (tightCore R)
  obtain ⟨α₀, h₀, b₀, hl₀⟩ := hlabel _ hK
  obtain ⟨α₁, h₁, b₁, hl₁⟩ := hlabel _ hB₁.1
  obtain ⟨α₂, h₂, b₂, hl₂⟩ := hlabel _ hB₂K.1
  have ht := hd.isUniqueInvolution_core
  have heq : ∀ {M : Subgroup Y}, M ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
      ∀ {β : Finset (Fin m)} {h' : β.card = 4} {b' : Bool},
        (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar β h' b' →
          α₀ = β := fun {M} hM {β h' b'} hl => by
    rcases AlphaFr.E2A.eq_or_disjoint_of_commutes hd hc hO2 hm φ hK
      (AlphaFr.E2A.commutes_of_mem_omegaNbr hd hc hO2 hK hM) hl₀ hl ht with e | hdisj
    · exact e
    · exact absurd (AlphaFr.E2A.eight_le_of_disjoint h₀ h' hdisj) (by omega)
  have e₁ := heq hB₁ hl₁
  have e₂ := heq hB₂K hl₂
  subst e₁ e₂
  have hsame : ∀ {L M : Subgroup Y}, L ∈ CoreAssembly.conjClass (tightCore R) →
      M ∈ CoreAssembly.conjClass (tightCore R) → ∀ {b b' : Bool},
        (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
          AE.memBar α₀ h₀ b →
        (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
          AE.memBar α₀ h₀ b' → b = b' → L = M := fun {L M} hL hM {b b'} hl hl' e => by
    subst e
    exact SecClq.eq_of_label_eq' hd hc hO2 hm φ hker hlabel hL hM hl hl'
  have hbool : ∀ x y z : Bool, x = y ∨ x = z ∨ y = z := by decide
  rcases hbool b₀ b₁ b₂ with e | e | e
  · exact hB₁.2.1 (hsame hK hB₁.1 hl₀ hl₁ e).symm
  · exact hB₂K.2.1 (hsame hK hB₂K.1 hl₀ hl₂ e).symm
  · exact hB₂.2.1 (hsame hB₁.1 hB₂K.1 hl₁ hl₂ e).symm

theorem ncard_omegaNbr_of_labels8 (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ 8)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    (hlabel : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ (α : Finset (Fin 8))
      (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α h b)
    {α : Finset (Fin 8)} {hα : α.card = 4} {b : Bool}
    (hl₀ : ((tightCore R).subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α hα b)
    (hs₁ : ∃ M ∈ CoreAssembly.conjClass (tightCore R),
      (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α hα (!b))
    (hs₂ : ∀ (h' : αᶜ.card = 4) (x : Bool), ∃ M ∈ CoreAssembly.conjClass (tightCore R),
      (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar αᶜ h' x) :
    (omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard = 3 := by
  have hD := thmDHyp_of hd hc hO2
  have hK := CoreAssembly.mem_conjClass_self (tightCore R)
  have ht := hd.isUniqueInvolution_core
  have hc4 : αᶜ.card = 4 := by rw [Finset.card_compl, Fintype.card_fin, hα]
  obtain ⟨N₁, hN₁, hl₁⟩ := hs₁
  obtain ⟨N₂, hN₂, hl₂⟩ := hs₂ hc4 true
  obtain ⟨N₃, hN₃, hl₃⟩ := hs₂ hc4 false
  have hdisj : Disjoint α αᶜ := disjoint_compl_right
  have hne₁ : tightCore R ≠ N₁ := fun e => by
    rw [← e] at hl₁
    cases b
    · exact AE.memBar_true_ne_false (by norm_num) α hα (hl₁.symm.trans hl₀)
    · exact AE.memBar_true_ne_false (by norm_num) α hα (hl₀.symm.trans hl₁)
  have hn₁ : N₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    refine mem_omegaNbr_of_commutes hN₁ (Ne.symm hne₁) ?_
    cases b
    · intro x hx y hy
      exact (commutes_of_true_false_labels hD φ hker hN₁ hK (Ne.symm hne₁) hl₁ hl₀ y hy x hx).symm
    · exact commutes_of_true_false_labels hD φ hker hK hN₁ hne₁ hl₀ hl₁
  have hn₂ := LinkE2.mem_omegaNbr_of_disjoint_labels hD φ hker hK hN₂ hl₀ hl₂ hdisj
  have hn₃ := LinkE2.mem_omegaNbr_of_disjoint_labels hD φ hker hK hN₃ hl₀ hl₃ hdisj
  have h12 : N₁ ≠ N₂ := LinkE2.ne_of_disjoint_labels φ hl₁ hl₂ hdisj
  have h13 : N₁ ≠ N₃ := LinkE2.ne_of_disjoint_labels φ hl₁ hl₃ hdisj
  have h23 : N₂ ≠ N₃ := fun e => by
    rw [e] at hl₂
    exact AE.memBar_true_ne_false (by norm_num) αᶜ hc4 (hl₂.symm.trans hl₃)
  have hall : omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {N₁, N₂, N₃} := by
    ext M
    refine ⟨fun hM => ?_, fun hM => ?_⟩
    · obtain ⟨β, h', b', hl⟩ := hlabel M hM.1
      rcases AlphaFr.E2A.eq_or_disjoint_of_commutes hd hc hO2 (by norm_num) φ hK
        (AlphaFr.E2A.commutes_of_mem_omegaNbr hd hc hO2 hK hM) hl₀ hl ht with e | hd'
      · subst e
        by_cases hb : b' = b
        · subst hb
          exact absurd (SecClq.eq_of_label_eq' hd hc hO2 (by norm_num) φ hker hlabel hK hM.1 hl₀
            hl).symm hM.2.1
        · have hb' : b' = !b := by cases b <;> cases b' <;> simp_all
          subst hb'
          exact Or.inl (SecClq.eq_of_label_eq' hd hc hO2 (by norm_num) φ hker hlabel hM.1 hN₁ hl
            hl₁)
      · obtain rfl := AlphaFr.E2A.eq_compl_of_disjoint hα h' hd'
        cases b'
        · exact Or.inr (Or.inr (SecClq.eq_of_label_eq' hd hc hO2 (by norm_num) φ hker hlabel hM.1
            hN₃ hl hl₃))
        · exact Or.inr (Or.inl (SecClq.eq_of_label_eq' hd hc hO2 (by norm_num) φ hker hlabel hM.1
            hN₂ hl hl₂))
    · rcases hM with rfl | rfl | rfl
      · exact hn₁
      · exact hn₂
      · exact hn₃
  rw [hall]
  exact Set.ncard_eq_three.mpr ⟨N₁, N₂, N₃, h12, h13, h23, rfl⟩

end CFSG.ClassicalInvolution.Q3.TL4.Wyl
