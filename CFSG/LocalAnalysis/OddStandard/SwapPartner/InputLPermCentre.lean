module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLPermCentreAux

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm Subgroup

theorem eq_one_or_eq_of_forall_commute {π : Perm (Fin 12)} (hπ : π * π = 1)
    (hf : Fintype.card {x : Fin 12 // π x = x} = 8) {c : Perm (Fin 12)}
    (hc : c ∈ alternatingGroup (Fin 12) ⊓ centralizer ({π} : Set (Perm (Fin 12))))
    (hcc : ∀ g ∈ alternatingGroup (Fin 12) ⊓ centralizer ({π} : Set (Perm (Fin 12))),
      g * c = c * g) :
    c = 1 ∨ c = π := by
  classical
  have hcπ : c * π = π * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have hcfix : ∀ x, π x = x → c x = x := by
    intro x hx
    exact apply_eq_self_of_forall_commute
      (by omega : 5 ≤ Fintype.card {x : Fin 12 // π x = x})
      (fun g hgA hgmoved =>
        hcc g ⟨hgA, Subgroup.mem_centralizer_singleton_iff.mpr
          (commute_of_fixes_moved hgmoved)⟩) hx
  have hfixed : (Finset.univ.filter (fun w : Fin 12 => π w = w)).card = 8 :=
    (Fintype.card_subtype (fun w : Fin 12 => π w = w)).symm.trans hf
  have hsupp : π.support.card = 4 := by
    have hcompl : (π.support)ᶜ = Finset.univ.filter (fun w : Fin 12 => π w = w) := by
      ext w
      simp [Equiv.Perm.mem_support]
    have hcard : (π.support)ᶜ.card = Fintype.card (Fin 12) - π.support.card :=
      Finset.card_compl _
    rw [hcompl, hfixed, Fintype.card_fin] at hcard
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < π.support.card)
  have hπa : π a ≠ a := Equiv.Perm.mem_support.mp ha
  set a' : Fin 12 := π a with ha'def
  have hπa' : π a' = a := by rw [ha'def]; exact perm_mul_self_apply hπ a
  have ha' : a' ∈ π.support := by
    rw [Equiv.Perm.mem_support, hπa']
    exact fun h => hπa h.symm
  have hsub_pair : ({a, a'} : Finset (Fin 12)) ⊆ π.support := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ha
    · exact ha'
  have hcard_comp : (π.support \ {a, a'}).card = 2 := by
    have h2 := Finset.card_sdiff_of_subset hsub_pair
    rw [Finset.card_pair (fun h => hπa h.symm), hsupp] at h2
    simpa using h2
  obtain ⟨b, hbcomp⟩ := Finset.card_pos.mp (by rw [hcard_comp]; norm_num :
    0 < (π.support \ {a, a'}).card)
  have hbS : b ∈ π.support := (Finset.mem_sdiff.mp hbcomp).1
  have hbne : b ∉ ({a, a'} : Finset (Fin 12)) := (Finset.mem_sdiff.mp hbcomp).2
  have hb_ne_a : b ≠ a := fun h => hbne (by simp [h])
  have hb_ne_a' : b ≠ a' := fun h => hbne (by simp [h])
  have hπb : π b ≠ b := Equiv.Perm.mem_support.mp hbS
  set b' : Fin 12 := π b with hb'def
  have hπb' : π b' = b := by rw [hb'def]; exact perm_mul_self_apply hπ b
  have hb'S : b' ∈ π.support := by
    rw [Equiv.Perm.mem_support, hπb']
    exact fun h => hπb h.symm
  have haa' : a ≠ a' := fun h => hπa h.symm
  have hab : a ≠ b := hb_ne_a.symm
  have hab' : a ≠ b' := by
    intro h
    have h1 : π a = π b' := by rw [h]
    rw [hπb'] at h1
    exact hb_ne_a' (ha'def.symm.trans h1).symm
  have ha'b : a' ≠ b := hb_ne_a'.symm
  have ha'b' : a' ≠ b' := by
    intro h
    have h1 : π a' = π b' := by rw [h]
    rw [hπa', hπb'] at h1
    exact hab h1
  have hbb' : b ≠ b' := fun h => hπb (h.trans hb'def).symm
  have hπa'_ne : π a' ≠ a' := by rw [hπa']; exact haa'
  have hπb'_ne : π b' ≠ b' := by rw [hπb']; exact hbb'
  have hSsub : ({a, a', b, b'} : Finset (Fin 12)) ⊆ π.support := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ha
    · exact ha'
    · exact hbS
    · exact hb'S
  have hcard4 : ({a, a', b, b'} : Finset (Fin 12)).card = 4 :=
    Finset.card_eq_four.mpr ⟨a, a', b, b', haa', hab, hab', ha'b, ha'b', hbb', rfl⟩
  have hS_eq : π.support = ({a, a', b, b'} : Finset (Fin 12)) :=
    (Finset.eq_of_subset_of_card_le hSsub (by rw [hcard4, hsupp])).symm
  have hcover : ∀ w : Fin 12, π w = w ∨ w = a ∨ w = a' ∨ w = b ∨ w = b' := by
    intro w
    by_cases hw : π w = w
    · exact Or.inl hw
    · have hwS : w ∈ π.support := Equiv.Perm.mem_support.mpr hw
      have : w ∈ ({a, a', b, b'} : Finset (Fin 12)) := by
        rw [← hS_eq]
        exact hwS
      exact Or.inr (by simpa only [Finset.mem_insert, Finset.mem_singleton] using this)
  obtain ⟨x, hxmem', y, hymem', hxy⟩ :=
    Finset.one_lt_card.mp (by rw [hfixed]; norm_num :
      1 < (Finset.univ.filter (fun w : Fin 12 => π w = w)).card)
  have hxπ : π x = x := (Finset.mem_filter.mp hxmem').2
  have hyπ : π y = y := (Finset.mem_filter.mp hymem').2
  have hne_of_fixed : ∀ {u v : Fin 12}, π u ≠ u → π v = v → u ≠ v :=
    fun hu hv h => hu (by rw [h]; exact hv)
  have hax : a ≠ x := hne_of_fixed hπa hxπ
  have hay : a ≠ y := hne_of_fixed hπa hyπ
  have ha'x : a' ≠ x := hne_of_fixed hπa'_ne hxπ
  have ha'y : a' ≠ y := hne_of_fixed hπa'_ne hyπ
  have hbx : b ≠ x := hne_of_fixed hπb hxπ
  have hby : b ≠ y := hne_of_fixed hπb hyπ
  have hb'x : b' ≠ x := hne_of_fixed hπb'_ne hxπ
  have hb'y : b' ≠ y := hne_of_fixed hπb'_ne hyπ
  have hga_mem : swap a a' * swap x y ∈
      alternatingGroup (Fin 12) ⊓ centralizer ({π} : Set (Perm (Fin 12))) :=
    swap_mul_swap_mem_inf_centralizer_fixed ha'def.symm hπa' hxπ hyπ haa' hxy
  have hgb_mem : swap b b' * swap x y ∈
      alternatingGroup (Fin 12) ⊓ centralizer ({π} : Set (Perm (Fin 12))) :=
    swap_mul_swap_mem_inf_centralizer_fixed hb'def.symm hπb' hxπ hyπ hbb' hxy
  have hgab_mem : swap a b * swap a' b' ∈
      alternatingGroup (Fin 12) ⊓ centralizer ({π} : Set (Perm (Fin 12))) :=
    swap_mul_swap_mem_inf_centralizer_moved ha'def hb'def hπa' hπb' hab haa' hab' ha'b ha'b' hbb'
  have hga_a : swap a a' (swap x y a) = a' := by
    rw [Equiv.swap_apply_of_ne_of_ne hax hay, Equiv.swap_apply_left]
  have hga_b : swap a a' (swap x y b) = b := by
    rw [Equiv.swap_apply_of_ne_of_ne hbx hby,
      Equiv.swap_apply_of_ne_of_ne hb_ne_a hb_ne_a']
  have hga_b' : swap a a' (swap x y b') = b' := by
    rw [Equiv.swap_apply_of_ne_of_ne hb'x hb'y,
      Equiv.swap_apply_of_ne_of_ne hab'.symm ha'b'.symm]
  have hgb_a : swap b b' (swap x y a) = a := by
    rw [Equiv.swap_apply_of_ne_of_ne hax hay,
      Equiv.swap_apply_of_ne_of_ne hab hab']
  have hgb_a' : swap b b' (swap x y a') = a' := by
    rw [Equiv.swap_apply_of_ne_of_ne ha'x ha'y,
      Equiv.swap_apply_of_ne_of_ne ha'b ha'b']
  have hgb_b : swap b b' (swap x y b) = b' := by
    rw [Equiv.swap_apply_of_ne_of_ne hbx hby, Equiv.swap_apply_left]
  have hgab_a : swap a b (swap a' b' a) = b := by
    rw [Equiv.swap_apply_of_ne_of_ne haa' hab', Equiv.swap_apply_left]
  have hgab_a' : swap a b (swap a' b' a') = b' := by
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hab'.symm hbb'.symm]
  have hca_supp : c a ∈ π.support := by
    rw [Equiv.Perm.mem_support]
    intro h
    have h1 : c (c a) = c a := hcfix (c a) h
    have h2 : c a = a := c.injective h1
    exact hπa (by
      calc π a = π (c a) := by rw [h2]
        _ = c a := h
        _ = a := h2)
  have hca_mem : c a ∈ ({a, a', b, b'} : Finset (Fin 12)) := by
    rw [← hS_eq]
    exact hca_supp
  have hca_cases : c a = a ∨ c a = a' ∨ c a = b ∨ c a = b' := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hca_mem
  have hca_pair : c a = a ∨ c a = a' := by
    rcases hca_cases with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hcomm := congrArg (fun f : Perm (Fin 12) => f a) (hcc _ hga_mem)
      simp only [Equiv.Perm.mul_apply] at hcomm
      rw [h, hga_a, hga_b] at hcomm
      exact haa' (c.injective (h.trans hcomm))
    · exfalso
      have hcomm := congrArg (fun f : Perm (Fin 12) => f a) (hcc _ hga_mem)
      simp only [Equiv.Perm.mul_apply] at hcomm
      rw [h, hga_a, hga_b'] at hcomm
      exact haa' (c.injective (h.trans hcomm))
  have hcb_supp : c b ∈ π.support := by
    rw [Equiv.Perm.mem_support]
    intro h
    have h1 : c (c b) = c b := hcfix (c b) h
    have h2 : c b = b := c.injective h1
    exact hπb (by
      calc π b = π (c b) := by rw [h2]
        _ = c b := h
        _ = b := h2)
  have hcb_mem : c b ∈ ({a, a', b, b'} : Finset (Fin 12)) := by
    rw [← hS_eq]
    exact hcb_supp
  have hcb_cases : c b = a ∨ c b = a' ∨ c b = b ∨ c b = b' := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hcb_mem
  have hcb_pair : c b = b ∨ c b = b' := by
    rcases hcb_cases with h | h | h | h
    · exfalso
      have hcomm := congrArg (fun f : Perm (Fin 12) => f b) (hcc _ hgb_mem)
      simp only [Equiv.Perm.mul_apply] at hcomm
      rw [h, hgb_b, hgb_a] at hcomm
      exact hbb' (c.injective (h.trans hcomm))
    · exfalso
      have hcomm := congrArg (fun f : Perm (Fin 12) => f b) (hcc _ hgb_mem)
      simp only [Equiv.Perm.mul_apply] at hcomm
      rw [h, hgb_b, hgb_a'] at hcomm
      exact hbb' (c.injective (h.trans hcomm))
    · exact Or.inl h
    · exact Or.inr h
  rcases hca_pair with hca | hca
  ·
    have hca' : c a' = a' := by
      have h : c (π a) = π (c a) := by rw [← Equiv.Perm.mul_apply, hcπ, Equiv.Perm.mul_apply]
      rw [ha'def, h, hca]
    have hcb : c b = b := by
      have hcomm := congrArg (fun f : Perm (Fin 12) => f a) (hcc _ hgab_mem)
      simp only [Equiv.Perm.mul_apply] at hcomm
      rw [hca, hgab_a] at hcomm
      exact hcomm.symm
    have hcb' : c b' = b' := by
      have h : c (π b) = π (c b) := by rw [← Equiv.Perm.mul_apply, hcπ, Equiv.Perm.mul_apply]
      rw [hb'def, h, hcb]
    left
    apply Equiv.ext
    intro w
    rcases hcover w with hw | hw | hw | hw | hw
    · exact hcfix w hw
    · rw [hw]; exact hca
    · rw [hw]; exact hca'
    · rw [hw]; exact hcb
    · rw [hw]; exact hcb'
  ·
    have hca' : c a' = a := by
      have h : c (π a) = π (c a) := by rw [← Equiv.Perm.mul_apply, hcπ, Equiv.Perm.mul_apply]
      rw [ha'def, h, hca, hπa']
    have hcb : c b = b' := by
      have hcomm := congrArg (fun f : Perm (Fin 12) => f a) (hcc _ hgab_mem)
      simp only [Equiv.Perm.mul_apply] at hcomm
      rw [hca, hgab_a, hgab_a'] at hcomm
      exact hcomm.symm
    have hcb' : c b' = b := by
      have h : c (π b) = π (c b) := by rw [← Equiv.Perm.mul_apply, hcπ, Equiv.Perm.mul_apply]
      rw [hb'def, h, hcb, hπb']
    right
    apply Equiv.ext
    intro w
    rcases hcover w with hw | hw | hw | hw | hw
    · rw [hcfix w hw, hw]
    · rw [hw]; exact hca.trans ha'def
    · rw [hw]; exact hca'.trans hπa'.symm
    · rw [hw]; exact hcb.trans hb'def
    · rw [hw]; exact hcb'.trans hπb'.symm

end CFSG.OddStandard.AltStdSec.SwapPartner
