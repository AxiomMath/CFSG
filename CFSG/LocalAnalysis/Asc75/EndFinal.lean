module

public import CFSG.LocalAnalysis.Asc75.Interface
public import CFSG.LocalAnalysis.Asc75.EndZ
public import CFSG.LocalAnalysis.Asc75.EndBender

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

theorem asc75Endgame_of_ZD
    (hZD : CFSG.GH74.Uniqueness.S_ZD) : Asc75Endgame := by
  intro G _ _ S A₁ A₂ H h hdisj hne hf hg
  have hinv := isInvariantInvolutionSet_zInvSet (A₁ := A₁) (A₂ := A₂)
  have hpd := isProductDisconnected_zInvSet h hdisj hne hf hg
  have hconcl := hZD G (zInvSet A₁ A₂) H hinv hpd
  set L : Subgroup G := Subgroup.closure (zInvSet A₁ A₂) with hL
  have hmemL : ∀ a ∈ uSet A₁ A₂, a ≠ 1 → a * a = 1 → a ∈ L := fun a ha ha1 ha2 =>
    Subgroup.subset_closure (mem_zInvSet_of_involution ha ha1 ha2)
  rcases hconcl with hrank | ⟨u, -, -, hDu, hDinf, -, -, -, hBender, -, hZe⟩
  ·
    exfalso
    obtain ⟨E, hEA, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two A₁
    have hEL : E ≤ L := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]; exact L.one_mem
      · exact hmemL x (Or.inl (hEA hx)) hx1 (by rw [← sq]; exact hE.2 x hx)
    have h2 : CFSG.Open.pRank 2 A₁ ≤ 1 := (le_twoRank_of_elemAbelian_le hEL hE hcard).trans hrank
    have h1 := h.rank₁
    omega
  · exfalso
    obtain ⟨a, haA, b, hbA, ha1, hb1, hab, ha2, hb2, habc⟩ := exists_involution_pair h.rank₁
    have hab1 : a * b ≠ 1 := fun e => hab (by
      calc a = a * b * b⁻¹ := by group
        _ = b⁻¹ := by rw [e]; group
        _ = b := inv_eq_of_mul_eq_one_right hb2)
    have hab2 : (a * b) * (a * b) = 1 := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [habc]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2]; simp
    have haU : a ∈ uSet A₁ A₂ := Or.inl haA
    have hbU : b ∈ uSet A₁ A₂ := Or.inl hbA
    have habU : a * b ∈ uSet A₁ A₂ := Or.inl (A₁.mul_mem haA hbA)
    have haZ : a ∈ zInvSet A₁ A₂ := mem_zInvSet_of_involution haU ha1 ha2
    have hbZ : b ∈ zInvSet A₁ A₂ := mem_zInvSet_of_involution hbU hb1 hb2
    have habZ : a * b ∈ zInvSet A₁ A₂ := mem_zInvSet_of_involution habU hab1 hab2
    let aL : ↥L := ⟨a, Subgroup.subset_closure haZ⟩
    let bL : ↥L := ⟨b, Subgroup.subset_closure hbZ⟩
    let abL : ↥L := ⟨a * b, Subgroup.subset_closure habZ⟩
    obtain ⟨⟨da, hda, hada⟩, -⟩ := hZe aL haZ
    obtain ⟨⟨db, hdb, hbdb⟩, -⟩ := hZe bL hbZ
    obtain ⟨⟨dab, hdab, habdab⟩, -⟩ := hZe abL habZ
    have eab : aL * bL = abL := Subtype.ext rfl
    have key : (u * da) * (u * db) = u * dab := by
      calc (u * da) * (u * db) = aL * bL := by rw [← hada, ← hbdb]
        _ = abL := eab
        _ = u * dab := habdab
    have h1 : da * u * db = dab := by
      refine mul_left_cancel (a := u) ?_
      calc u * (da * u * db) = (u * da) * (u * db) := by group
        _ = u * dab := key
    have hu : u ∈ commutator ↥L := by
      have e : u = da⁻¹ * dab * db⁻¹ := by
        calc u = da⁻¹ * (da * u * db) * db⁻¹ := by group
          _ = da⁻¹ * dab * db⁻¹ := by rw [h1]
      rw [e]
      exact (commutator ↥L).mul_mem ((commutator ↥L).mul_mem ((commutator ↥L).inv_mem hda) hdab)
        ((commutator ↥L).inv_mem hdb)
    have hu1 : u = 1 := by
      have : u ∈ commutator ↥L ⊓ Subgroup.zpowers u := ⟨hu, Subgroup.mem_zpowers u⟩
      rw [hDinf, Subgroup.mem_bot] at this
      exact this
    have hDtop : commutator ↥L = ⊤ := by
      rw [hu1, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hDu
      exact hDu
    obtain ⟨c, hcA, hc1, hc2⟩ := exists_involution_of_one_lt_pRank h.rank₂
    have hcZ : c ∈ zInvSet A₁ A₂ := mem_zInvSet_of_involution (Or.inr hcA) hc1 hc2
    let cL : ↥L := ⟨c, Subgroup.subset_closure hcZ⟩
    have hac : a * c = c * a := h.comm a haA c hcA
    have hacc1 : a * c ≠ 1 := by
      intro e
      have hcA₁ : c ∈ A₁ := by
        have : c = a⁻¹ := by
          calc c = a⁻¹ * (a * c) := by group
            _ = a⁻¹ := by rw [e]; group
        rw [this]; exact A₁.inv_mem haA
      have : c ∈ A₁ ⊓ A₂ := ⟨hcA₁, hcA⟩
      rw [hdisj, Subgroup.mem_bot] at this
      exact hc1 this
    have hacc2 : (a * c) * (a * c) = 1 := by
      calc (a * c) * (a * c) = a * (c * a) * c := by group
        _ = a * (a * c) * c := by rw [hac]
        _ = (a * a) * (c * c) := by group
        _ = 1 := by rw [ha2, hc2]; simp
    have hwZ : (aL * cL : ↥L) ∈ {l : ↥L | (l : G) ∈ zInvSet A₁ A₂} := by
      refine mem_of_involution_of_perfect_bender hDtop hBender
        (Z' := {l : ↥L | (l : G) ∈ zInvSet A₁ A₂}) (fun z hz g => zInvSet_conj hz (g : G))
        (z₀ := aL) haZ (fun e => ha1 (congrArg Subtype.val e))
        (Subtype.ext ha2) (w := aL * cL) (fun e => hacc1 (congrArg Subtype.val e))
        (Subtype.ext hacc2)
    have hwZ' : a * c ∈ zInvSet A₁ A₂ := hwZ
    obtain ⟨a', ha', ha'1, ha'2, g, hg'⟩ := hwZ'
    have hacS : a * c ∈ S := S.mul_mem (h.le₁ haA) (h.le₂ hcA)
    have hacU : a * c ∈ uSet A₁ A₂ := by
      have hgS : g⁻¹ * a' * g ∈ S := by rw [← hg']; exact hacS
      have := h.closed_G hdisj ha' hgS
      rwa [← hg'] at this
    rcases hacU with hA | hA
    · have hcA₁ : c ∈ A₁ := by
        have := A₁.mul_mem (A₁.inv_mem haA) hA
        simpa using this
      have : c ∈ A₁ ⊓ A₂ := ⟨hcA₁, hcA⟩
      rw [hdisj, Subgroup.mem_bot] at this
      exact hc1 this
    · have haA₂ : a ∈ A₂ := by
        have := A₂.mul_mem hA (A₂.inv_mem hcA)
        simpa using this
      have : a ∈ A₁ ⊓ A₂ := ⟨haA, haA₂⟩
      rw [hdisj, Subgroup.mem_bot] at this
      exact ha1 this

end CFSG.Asc75
