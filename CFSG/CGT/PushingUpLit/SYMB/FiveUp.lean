module

public import CFSG.CGT.PushingUpLit.SYMB.FiveMem

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {V₁ : Subgroup Γ}

@[expose] def Up (φ : ↥G →* Equiv.Perm (Fin 5)) (ψ : ↥V →* ↥(G6.coreMod 5)) (V₁ A : Subgroup Γ)
    (P : Subgroup (Equiv.Perm (Fin 5))) : Subgroup Γ :=
  Cfix ψ V₁ P ⊔ (A ⊓ preimG G φ P)

omit [Finite Γ] in
theorem V1Iso.comm_Cfix_preimG (hV : V1Iso S V₁) {P : Subgroup (Equiv.Perm (Fin 5))} {c w : Γ}
    (hc : c ∈ Cfix ψ V₁ P) (hw : w ∈ preimG G φ P) : c * w = w * c := by
  obtain ⟨hcV, hc1, hfix⟩ := mem_Cfix.1 hc
  obtain ⟨hwG, hwP⟩ := mem_preimG.1 hw
  have h1 := hV.psi_conj hwG hc1
  have h2 : G6.coreAct 5 (φ ⟨w, hwG⟩) (ψ ⟨c, hcV⟩) = ψ ⟨c, hcV⟩ :=
    Delta5Swaps.mem_Fixed.1 hfix _ hwP
  rw [h2] at h1
  have h3 : w * c * w⁻¹ = c :=
    hV.eq_of_psi_eq (hV.normal hwG |> fun h => (Subgroup.mem_normalizer_iff.mp h c).mp hc1) hc1 h1
  calc c * w = (w * c * w⁻¹) * w := by rw [h3]
    _ = w * c := by group

omit [Finite Γ] in
theorem Cfix_le_kerG (hV : V1Iso S V₁) (P : Subgroup (Equiv.Perm (Fin 5))) :
    Cfix ψ V₁ P ≤ kerG G φ := (Cfix_le P).trans (hV.le.trans (V_le_kerG S))

omit [Finite Γ] in
theorem Cfix_anti {P Q : Subgroup (Equiv.Perm (Fin 5))} (h : P ≤ Q) :
    Cfix ψ V₁ Q ≤ Cfix ψ V₁ P := by
  intro x hx
  obtain ⟨hxV, hx1, hfix⟩ := mem_Cfix.1 hx
  exact mem_Cfix.2 ⟨hxV, hx1, Delta5Swaps.Fixed_anti h hfix⟩

omit [Finite Γ] in
theorem imgG_preimG_le (P : Subgroup (Equiv.Perm (Fin 5))) :
    imgG G φ (preimG G φ P) ≤ P := by
  intro σ hσ
  obtain ⟨g, hg, hgP, rfl⟩ := mem_imgG.1 hσ
  obtain ⟨hg', hP⟩ := mem_preimG.1 hgP
  exact hP

omit [Finite Γ] in
theorem imgG_inf_preimG {A : Subgroup Γ} {P : Subgroup (Equiv.Perm (Fin 5))}
    (hP : P ≤ imgG G φ A) : imgG G φ (A ⊓ preimG G φ P) = P := by
  refine le_antisymm ((imgG_mono G φ inf_le_right).trans (imgG_preimG_le P)) fun σ hσ => ?_
  obtain ⟨a, haG, haA, rfl⟩ := mem_imgG.1 (hP hσ)
  exact mem_imgG.2 ⟨a, haG, ⟨haA, mem_preimG.2 ⟨haG, hσ⟩⟩, rfl⟩

omit [Finite Γ] in
theorem Cfix_sup_le_preimG (hV : V1Iso S V₁) {A : Subgroup Γ}
    (P : Subgroup (Equiv.Perm (Fin 5))) : Up φ ψ V₁ A P ≤ preimG G φ P := by
  refine sup_le (fun x hx => ?_) inf_le_right
  obtain ⟨hxG, hx1⟩ := mem_kerG.1 (Cfix_le_kerG hV P hx)
  exact mem_preimG_of_map_eq_one hxG hx1

omit [Finite Γ] in
theorem imgG_Up (hV : V1Iso S V₁) {A : Subgroup Γ} {P : Subgroup (Equiv.Perm (Fin 5))}
    (hP : P ≤ imgG G φ A) : imgG G φ (Up φ ψ V₁ A P) = P := by
  refine le_antisymm ((imgG_mono G φ (Cfix_sup_le_preimG hV P)).trans (imgG_preimG_le P)) ?_
  calc P = imgG G φ (A ⊓ preimG G φ P) := (imgG_inf_preimG (φ := φ) hP).symm
    _ ≤ imgG G φ (Up φ ψ V₁ A P) :=
      imgG_mono G φ (show A ⊓ preimG G φ P ≤ Up φ ψ V₁ A P from le_sup_right)

omit [Finite Γ] in
theorem Up_elemAbelian (hV : V1Iso S V₁) {A : Subgroup Γ} (hA : IsElemAbelian 2 A)
    (P : Subgroup (Equiv.Perm (Fin 5))) : IsElemAbelian 2 (Up φ ψ V₁ A P) :=
  isElemAbelian_sup_of_commute
    (isElemAbelian_of_le' (V₁_elemAbelian S hV) (Cfix_le P))
    (isElemAbelian_of_le' hA inf_le_left)
    fun _ hc _ hw => hV.comm_Cfix_preimG hc (Subgroup.mem_inf.1 hw).2

omit [Finite Γ] in
theorem exists_mem_Up (hV : V1Iso S V₁) {A : Subgroup Γ} {P : Subgroup (Equiv.Perm (Fin 5))}
    {u : Γ} (hu : u ∈ Up φ ψ V₁ A P) :
    ∃ c ∈ Cfix ψ V₁ P, ∃ w ∈ A ⊓ preimG G φ P, u = c * w := by
  have hn : Cfix ψ V₁ P ≤ Subgroup.normalizer ((A ⊓ preimG G φ P : Subgroup Γ) : Set Γ) :=
    le_normalizer_of_commute fun c hc d hd => hV.comm_Cfix_preimG hc (Subgroup.mem_inf.1 hd).2
  have hu' : u ∈ ((Cfix ψ V₁ P ⊔ (A ⊓ preimG G φ P) : Subgroup Γ) : Set Γ) := hu
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hu'
  obtain ⟨c, hc, w, hw, rfl⟩ := hu'
  exact ⟨c, hc, w, hw, rfl⟩

omit [Finite Γ] in
theorem Up_le_T (hV : V1Iso S V₁) {A : Subgroup Γ} (hAT : A ≤ T)
    (P : Subgroup (Equiv.Perm (Fin 5))) : Up φ ψ V₁ A P ≤ T :=
  sup_le ((Cfix_le P).trans (hV.le.trans (V_le_T S))) (inf_le_left.trans hAT)

theorem Up_isMax (hV : V1Iso S V₁) {A : Subgroup Γ} (hA : IsMaxElemAbelian T A)
    {P : Subgroup (Equiv.Perm (Fin 5))} (hP : P ≤ imgG G φ A)
    (hP16 : Nat.card ↥P * Nat.card ↥(Delta5Swaps.Fixed P) = 16)
    (hA16 : Nat.card ↥(imgG G φ A) * Nat.card ↥(Delta5Swaps.Fixed (imgG G φ A)) = 16) :
    IsMaxElemAbelian T (Up φ ψ V₁ A P) := by
  have hAG : A ≤ G := hA.1.trans S.sylow.1
  refine isMaxElemAbelian_of_card_eq hA (Up_le_T hV hA.1 P) (Up_elemAbelian hV hA.2.1 P) ?_
  set D : Subgroup Γ := A ⊓ preimG G φ P with hD
  set C : Subgroup Γ := Cfix ψ V₁ P with hC
  have hCD : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c := fun c hc d hd =>
    hV.comm_Cfix_preimG hc (Subgroup.mem_inf.1 hd).2
  have hprod := card_sup_mul_card_inf_of_commute hCD
  have hinf : C ⊓ D = Cfix ψ V₁ (imgG G φ A) := by
    apply le_antisymm
    · intro x hx
      have hxC : x ∈ C := hx.1
      have hxA : x ∈ A := (Subgroup.mem_inf.1 hx.2).1
      have : x ∈ V₁ ⊓ A := ⟨Cfix_le P hxC, hxA⟩
      rwa [V₁_inf_eq S hV hA] at this
    · intro x hx
      have hx' : x ∈ V₁ ⊓ A := by rw [V₁_inf_eq S hV hA]; exact hx
      refine ⟨Cfix_anti hP hx, hx'.2, ?_⟩
      obtain ⟨hxG, hx1⟩ := mem_kerG.1 (Cfix_le_kerG hV _ hx)
      exact mem_preimG_of_map_eq_one hxG hx1
  rw [hinf] at hprod
  have hDcard : Nat.card ↥D = Nat.card ↥P * Nat.card ↥(A ⊓ kerG G φ) := by
    have h1 := card_eq_img_mul_ker φ (inf_le_left.trans hAG : D ≤ G)
    rw [imgG_inf_preimG (φ := φ) hP] at h1
    have h2 : D ⊓ kerG G φ = A ⊓ kerG G φ := by
      apply le_antisymm (inf_le_inf_right _ inf_le_left)
      refine le_inf (le_inf inf_le_left ?_) inf_le_right
      intro x hx
      obtain ⟨hxG, hx1⟩ := mem_kerG.1 (Subgroup.mem_inf.1 hx).2
      exact mem_preimG_of_map_eq_one hxG hx1
    rw [h2] at h1
    exact h1
  have hAcard := card_eq_img_mul_ker φ hAG
  have hCcard : Nat.card ↥C = Nat.card ↥(Delta5Swaps.Fixed P) := hV.card_Cfix P
  have hFc : Nat.card ↥(Cfix ψ V₁ (imgG G φ A)) = Nat.card ↥(Delta5Swaps.Fixed (imgG G φ A)) :=
    hV.card_Cfix _
  rw [hFc, hDcard, hCcard] at hprod
  have hpos : 0 < Nat.card ↥(Delta5Swaps.Fixed (imgG G φ A)) := Nat.card_pos
  have key : Nat.card ↥(Up φ ψ V₁ A P) * Nat.card ↥(Delta5Swaps.Fixed (imgG G φ A)) =
      Nat.card ↥A * Nat.card ↥(Delta5Swaps.Fixed (imgG G φ A)) := by
    have e1 : Nat.card ↥(Up φ ψ V₁ A P) * Nat.card ↥(Delta5Swaps.Fixed (imgG G φ A)) =
        16 * Nat.card ↥(A ⊓ kerG G φ) := by
      have : Nat.card ↥(C ⊔ D) = Nat.card ↥(Up φ ψ V₁ A P) := rfl
      rw [← this, hprod]
      calc Nat.card ↥(Delta5Swaps.Fixed P) * (Nat.card ↥P * Nat.card ↥(A ⊓ kerG G φ))
          = (Nat.card ↥P * Nat.card ↥(Delta5Swaps.Fixed P)) * Nat.card ↥(A ⊓ kerG G φ) := by ring
        _ = 16 * Nat.card ↥(A ⊓ kerG G φ) := by rw [hP16]
    rw [e1, hAcard]
    calc 16 * Nat.card ↥(A ⊓ kerG G φ)
        = (Nat.card ↥(imgG G φ A) * Nat.card ↥(Delta5Swaps.Fixed (imgG G φ A))) *
            Nat.card ↥(A ⊓ kerG G φ) := by rw [hA16]
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos key

end CFSG.CGT.PushingUpLit.SYMB
