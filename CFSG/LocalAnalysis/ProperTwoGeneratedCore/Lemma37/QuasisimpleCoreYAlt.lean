module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYAltFour
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CyclicQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYSzEight
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneT1

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open Equiv

variable {X : Type} [Group X] [Finite X]

namespace OneComponent

variable {Y : Subgroup X} {e v : X} {L : Subgroup X}

theorem mem_sup_centralizer_of_mem_alternating (hL : OneComponent Y e v L)
    (hc : BaseConfig Y e) (hv : v * v = e) (hvn : (Subgroup.zpowers v).Normal)
    (hZ : Nat.card (Subgroup.center L) = 2)
    (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) {x : X} (hxY : x ∈ Y)
    (hx : orderOf x = 2) : x ∈ L ⊔ Subgroup.centralizer (L : Set X) := by
  have := hL.normal
  by_cases hxe : x = e
  · rw [hxe]
    exact Subgroup.mem_sup_left hL.mem
  set φ := quotientConj L x with hφdef
  obtain ⟨σ, hσ'⟩ := exists_perm_of_mulEquiv eA φ
  have hσ : ∀ y, permOf eA (φ y) = σ * permOf eA y * σ⁻¹ := hσ'
  by_cases hsign : Perm.sign σ = 1
  ·
    have hinner : φ = MulAut.conj (eA.symm ⟨σ, Perm.mem_alternatingGroup.mpr hsign⟩) := by
      ext y
      apply permOf_injective eA
      rw [hσ y, MulAut.conj_apply, permOf_mul, permOf_mul, permOf_inv]
      simp [permOf]
    obtain ⟨l, hl⟩ := exists_mul_mem_centralizer_of_quotientConj_eq hL.perfect hinner
    rw [show x = l * ((l : X)⁻¹ * x) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left l.2) (Subgroup.mem_sup_right hl)
  exfalso
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hφφ : ∀ y, φ (φ y) = y := fun y => by
    rw [← MulAut.mul_apply, hφdef, ← map_mul, hxx, map_one, MulAut.one_apply]
  have hσσ : σ * σ = 1 := by
    apply perm_eq_one_of_forall_conj
    intro a
    have h1 := hσ (φ (eA.symm a))
    rw [hσ (eA.symm a), hφφ] at h1
    simp only [permOf, MulEquiv.apply_symm_apply] at h1
    rw [mul_inv_rev]
    calc σ * σ * (a : Perm (Fin 5)) * (σ⁻¹ * σ⁻¹) = σ * (σ * a * σ⁻¹) * σ⁻¹ := by group
      _ = a := h1.symm
  obtain ⟨a, ha, b, hb⟩ := s5_exists_invariant_four σ ⟨hσσ, hsign⟩
  obtain ⟨c, hc1, -, -, hσc, hcnot⟩ := s5_exists_three_not_normalizing σ ⟨hσσ, hsign⟩ a ha b hb
  obtain ⟨d, hd1, hd3, hd0, hdA, hdB⟩ := s5_exists_three_normalizing a ha b
    ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1⟩
  set a' := eA.symm ⟨a, Perm.mem_alternatingGroup.mpr ha.1⟩ with ha'def
  set b' := eA.symm ⟨b, Perm.mem_alternatingGroup.mpr hb.1⟩ with hb'def
  set c' := eA.symm ⟨c, Perm.mem_alternatingGroup.mpr hc1⟩ with hc'def
  set d' := eA.symm ⟨d, Perm.mem_alternatingGroup.mpr hd1⟩ with hd'def
  have ha'a : permOf eA a' = a := by simp [ha'def, permOf]
  have hb'b : permOf eA b' = b := by simp [hb'def, permOf]
  have hc'c : permOf eA c' = c := by simp [hc'def, permOf]
  have hd'd : permOf eA d' = d := by simp [hd'def, permOf]
  have ha'a' : a' * a' = 1 := permOf_injective eA (by rw [permOf_mul, ha'a, ha.2.1, permOf_one])
  have hb'b' : b' * b' = 1 := permOf_injective eA (by rw [permOf_mul, hb'b, hb.2.1, permOf_one])
  have hab' : Commute a' b' := permOf_injective eA (by
    rw [permOf_mul, permOf_mul, ha'a, hb'b]
    exact hb.2.2.2.2.1)
  have ha'1 : a' ≠ 1 := fun h => ha.2.2 (by rw [← ha'a, h, permOf_one])
  have hb'1 : b' ≠ 1 := fun h => hb.2.2.1 (by rw [← hb'b, h, permOf_one])
  have ha'b' : a' ≠ b' := fun h => hb.2.2.2.1 (by rw [← ha'a, ← hb'b, h])
  set F := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions a' b' ha'a' hb'b' hab'
    with hFdef
  have hmemF : ∀ y, y ∈ F ↔ y = a' * b' ∨ y = a' ∨ y = b' ∨ y = 1 := fun y => by
    change y ∈ ({a' * b', a', b', 1} : Set (L ⧸ Subgroup.center L)) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hFsq : ∀ y ∈ F, y * y = 1 := by
    intro y hy
    rcases (hmemF y).mp hy with rfl | rfl | rfl | rfl
    · calc a' * b' * (a' * b') = a' * (b' * a') * b' := by group
        _ = a' * (a' * b') * b' := by rw [hab'.eq]
        _ = 1 := by rw [← mul_assoc, ha'a', one_mul, hb'b']
    · exact ha'a'
    · exact hb'b'
    · exact mul_one 1
  have hfrom : ∀ y, (permOf eA y = a ∨ permOf eA y = b ∨ permOf eA y = a * b) → y ∈ F := by
    intro y hy
    rw [hmemF]
    rcases hy with h | h | h
    · exact Or.inr (Or.inl (permOf_injective eA (h.trans ha'a.symm)))
    · exact Or.inr (Or.inr (Or.inl (permOf_injective eA (h.trans hb'b.symm))))
    · exact Or.inl (permOf_injective eA (by rw [h, permOf_mul, ha'a, hb'b]))
  have hto : ∀ y ∈ F, y ≠ 1 →
      (permOf eA y = a ∨ permOf eA y = b ∨ permOf eA y = a * b) := by
    intro y hy hy1
    rcases (hmemF y).mp hy with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (by rw [permOf_mul, ha'a, hb'b]))
    · exact Or.inl ha'a
    · exact Or.inr (Or.inl hb'b)
    · exact absurd rfl hy1
  have hstable : ∀ f : (L ⧸ Subgroup.center L) →* (L ⧸ Subgroup.center L),
      (permOf eA (f a') = a ∨ permOf eA (f a') = b ∨ permOf eA (f a') = a * b) →
      (permOf eA (f b') = a ∨ permOf eA (f b') = b ∨ permOf eA (f b') = a * b) →
      ∀ y ∈ F, f y ∈ F := by
    intro f hfa hfb y hy
    rcases (hmemF y).mp hy with rfl | rfl | rfl | rfl
    · rw [map_mul]
      exact F.mul_mem (hfrom _ hfa) (hfrom _ hfb)
    · exact hfrom _ hfa
    · exact hfrom _ hfb
    · rw [map_one]
      exact F.one_mem
  have hconj : ∀ g y : L ⧸ Subgroup.center L,
      permOf eA ((MulAut.conj g).toMonoidHom y) = permOf eA g * permOf eA y * (permOf eA g)⁻¹ :=
    fun g y => by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, permOf_mul, permOf_mul, permOf_inv]
  have hφF : ∀ y ∈ F, φ y ∈ F := hstable φ.toMonoidHom
    (by rw [MulEquiv.coe_toMonoidHom, hσ, ha'a]; exact hb.2.2.2.2.2.1)
    (by rw [MulEquiv.coe_toMonoidHom, hσ, hb'b]; exact hb.2.2.2.2.2.2)
  have hQY := hL.map_comap_le_of_stable hc hxY hx hxe hFsq hφF
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective a'
  have ha'F : a' ∈ F := (hmemF a').mpr (Or.inr (Or.inl rfl))
  have hNB : Subgroup.normalizer (F : Set (L ⧸ Subgroup.center L)) ≤
      (Y.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L)) := by
    intro n hn
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective n
    refine ⟨l, Subgroup.mem_subgroupOf.mpr (hL.mem_of_normalizes hc hv hvn hZ hFsq hQY
      (hq ▸ ha'F) (hq ▸ ha'1) fun y hy => (Subgroup.mem_normalizer_iff.mp hn y).mp hy), rfl⟩
  have hd'N : d' ∈ Subgroup.normalizer (F : Set (L ⧸ Subgroup.center L)) :=
    mem_normalizer_of_conj_mem fun y hy => hstable (MulAut.conj d').toMonoidHom
      (by rw [hconj, hd'd, ha'a]; exact hdA) (by rw [hconj, hd'd, hb'b]; exact hdB) y hy
  have hd'3 : d' * d' * d' = 1 :=
    permOf_injective eA (by rw [permOf_mul, permOf_mul, hd'd, hd3, permOf_one])
  have hd'1 : d' ≠ 1 := fun h => hd0 (by rw [← hd'd, h, permOf_one])
  have hK : Nat.card (L ⧸ Subgroup.center L) = 60 := by
    rw [Nat.card_congr eA.toEquiv, card_alternatingGroup_fin_five]
  have hF4 : Nat.card F = 4 :=
    (CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a' b' ha'a' hb'b' ha'1
      hb'1 ha'b' hab').card_four
  have hker : (QuotientGroup.mk' (Subgroup.center L)).ker ≤ Y.subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    exact hL.center_le_subgroupOf hc
  have hBN := eq_normalizer_of_le hK hF4 hNB
    (CyclicCase.map_ne_top_of_ker_le _ hker hL.subgroupOf_ne_top) hd'N hd'3 hd'1
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective c'
  have hfix : φ (l : L ⧸ Subgroup.center L) = (l : L ⧸ Subgroup.center L) := by
    rw [hl]
    apply permOf_injective eA
    rw [hσ, hc'c, hσc, mul_inv_cancel_right]
  have hc'B : c' ∈ (Y.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L)) :=
    ⟨l, Subgroup.mem_subgroupOf.mpr (hL.mem_of_fixed hc hxY hx hxe hfix), hl⟩
  rw [hBN, Subgroup.mem_normalizer_iff] at hc'B
  have hcF : ∀ y ∈ F, y ≠ 1 → (c * permOf eA y * c⁻¹ = a ∨ c * permOf eA y * c⁻¹ = b ∨
      c * permOf eA y * c⁻¹ = a * b) := by
    intro y hy hy1
    have h := hto _ ((hc'B y).mp hy) fun h1 => hy1 (mul_eq_left.mp (mul_inv_eq_one.mp h1))
    rwa [permOf_mul, permOf_mul, permOf_inv, hc'c] at h
  have h1 := hcF a' ha'F ha'1
  have h2 := hcF b' ((hmemF b').mpr (Or.inr (Or.inr (Or.inl rfl)))) hb'1
  rw [ha'a] at h1
  rw [hb'b] at h2
  exact hcnot ⟨h1, h2⟩

theorem mem_sup_centralizer_of_alternating (hL : OneComponent Y e v L) (hc : BaseConfig Y e)
    (hv : v * v = e) (hvn : (Subgroup.zpowers v).Normal) (hZ : Nat.card (Subgroup.center L) = 2)
    (eA : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) {x : X} (hx : orderOf x = 2) :
    x ∈ L ⊔ Subgroup.centralizer (L : Set X) := by
  have := hL.normal
  have := hL.centralizer_normal
  obtain ⟨g, hg⟩ := hc.exists_conj_mem hx
  have hg2 : orderOf (g⁻¹ * x * g) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv, hx] using (MulAut.conj g⁻¹).orderOf_eq x
  have h := hL.mem_sup_centralizer_of_mem_alternating hc hv hvn hZ eA hg hg2
  have hN : (L ⊔ Subgroup.centralizer (L : Set X)).Normal := inferInstance
  have h' := hN.conj_mem _ h g
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h'

end OneComponent

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
