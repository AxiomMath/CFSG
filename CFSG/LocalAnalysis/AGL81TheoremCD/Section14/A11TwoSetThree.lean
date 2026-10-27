module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoSetup
import CFSG.Permutation.OrderThreeCentralizer
import CFSG.HardMathSupport.RichardWeiss.Proving.OrderThreeCycleType

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm Subgroup

variable {σ τ : alternatingGroup (Fin 11)}

theorem apply_nine_ten_of_mem_a11TwoSetStab (hσS : σ ∈ a11TwoSetStab 9 10)
    (hσ : orderOf σ = 3) :
    (σ : Equiv.Perm (Fin 11)) 9 = 9 ∧ (σ : Equiv.Perm (Fin 11)) 10 = 10 := by
  have h3 : (σ : Equiv.Perm (Fin 11)) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one σ
    rw [hσ] at h
    simpa using congrArg (fun x : alternatingGroup (Fin 11) => (x : Equiv.Perm (Fin 11))) h
  rcases hσS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exfalso
    have hcycle : ((σ : Equiv.Perm (Fin 11)) ^ 3) 9 = 10 := by
      simp only [pow_succ, pow_zero, one_apply, Equiv.Perm.mul_apply, h1, h2]
    rw [h3] at hcycle
    norm_num at hcycle

private lemma card_fixedPoints_a11 (u : alternatingGroup (Fin 11)) :
    Nat.card (Function.fixedPoints (u : Equiv.Perm (Fin 11))) =
      11 - (u : Equiv.Perm (Fin 11)).support.card := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Function.fixedPoints (u : Equiv.Perm (Fin 11))) = _
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType, Fintype.card_fin]

private def fixedNine (u : alternatingGroup (Fin 11))
    (h : (u : Equiv.Perm (Fin 11)) 9 = 9) : Function.fixedPoints (u : Equiv.Perm (Fin 11)) :=
  ⟨9, h⟩

private def fixedTen (u : alternatingGroup (Fin 11))
    (h : (u : Equiv.Perm (Fin 11)) 10 = 10) : Function.fixedPoints (u : Equiv.Perm (Fin 11)) :=
  ⟨10, h⟩

private lemma coe_fixedNine (u : alternatingGroup (Fin 11))
    (h : (u : Equiv.Perm (Fin 11)) 9 = 9) : (fixedNine u h : Fin 11) = 9 := rfl

private lemma coe_fixedTen (u : alternatingGroup (Fin 11))
    (h : (u : Equiv.Perm (Fin 11)) 10 = 10) : (fixedTen u h : Fin 11) = 10 := rfl

private lemma fixedNine_ne_fixedTen (u : alternatingGroup (Fin 11))
    (h9 : (u : Equiv.Perm (Fin 11)) 9 = 9) (h10 : (u : Equiv.Perm (Fin 11)) 10 = 10) :
    fixedNine u h9 ≠ fixedTen u h10 := by
  intro h
  have h' : (9 : Fin 11) = 10 := congrArg Subtype.val h
  exact (by decide : (9 : Fin 11) ≠ 10) h'

private def fixedPointsPairFinset (u : alternatingGroup (Fin 11))
    (h9 : (u : Equiv.Perm (Fin 11)) 9 = 9) (h10 : (u : Equiv.Perm (Fin 11)) 10 = 10) :
    Finset (Function.fixedPoints (u : Equiv.Perm (Fin 11))) :=
  (Finset.univ.erase (fixedNine u h9)).erase (fixedTen u h10)

private lemma card_fixedPointsPairFinset (u : alternatingGroup (Fin 11))
    (h9 : (u : Equiv.Perm (Fin 11)) 9 = 9) (h10 : (u : Equiv.Perm (Fin 11)) 10 = 10) :
    (fixedPointsPairFinset u h9 h10).card =
      Nat.card (Function.fixedPoints (u : Equiv.Perm (Fin 11))) - 2 := by
  have hmem : fixedTen u h10 ∈ (Finset.univ : Finset _).erase (fixedNine u h9) := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm (fixedNine_ne_fixedTen u h9 h10), Finset.mem_univ _⟩
  dsimp only [fixedPointsPairFinset]
  rw [Finset.card_erase_of_mem hmem,
    Finset.card_erase_of_mem (Finset.mem_univ (fixedNine u h9)), Finset.card_univ,
    ← Nat.card_eq_fintype_card]
  omega

private lemma mem_fixedPointsPairFinset_ne (u : alternatingGroup (Fin 11))
    (h9 : (u : Equiv.Perm (Fin 11)) 9 = 9) (h10 : (u : Equiv.Perm (Fin 11)) 10 = 10)
    {c : Function.fixedPoints (u : Equiv.Perm (Fin 11))}
    (hc : c ∈ fixedPointsPairFinset u h9 h10) :
    c ≠ fixedNine u h9 ∧ c ≠ fixedTen u h10 := by
  dsimp only [fixedPointsPairFinset] at hc
  rw [Finset.mem_erase, Finset.mem_erase] at hc
  exact ⟨hc.2.1, hc.1⟩

private lemma exists_threeCycle_centralizer_not_stab (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10)
    (c : Function.fixedPoints (σ : Equiv.Perm (Fin 11)))
    (hc9 : c ≠ fixedNine σ h9) (hc10 : c ≠ fixedTen σ h10) :
    ∃ g ∈ Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))),
      g ∉ a11TwoSetStab 9 10 := by
  classical
  let X := Function.fixedPoints (σ : Equiv.Perm (Fin 11))
  let a : X := fixedNine σ h9
  let b : X := fixedTen σ h10
  have hab : a ≠ b := fixedNine_ne_fixedTen σ h9 h10
  have hca : c ≠ a := hc9
  have hcb : c ≠ b := hc10
  have hbc : b ≠ c := Ne.symm hcb
  have hca' : a ≠ c := Ne.symm hca
  let u : Perm X := Equiv.swap a b * Equiv.swap b c
  have hu3 : u.IsThreeCycle := by
    have h3c : (Equiv.swap b a * Equiv.swap b c).IsThreeCycle :=
      Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := b) (b := a) (c := c) (Ne.symm hab) hbc
        hca'
    simpa [u, Equiv.swap_comm] using h3c
  have hu_even : Equiv.Perm.sign u = 1 := hu3.sign
  let g : alternatingGroup (Fin 11) :=
    ⟨Equiv.Perm.ofSubtype u, by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype, hu_even]⟩
  have hcomm : g ∈ Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hd : (Equiv.Perm.ofSubtype u).Disjoint (σ : Equiv.Perm (Fin 11)) :=
      Equiv.Perm.disjoint_ofSubtype_of_memFixedPoints_self u
    exact hd.commute.eq
  refine ⟨g, hcomm, ?_⟩
  have hg10 : (g : Equiv.Perm (Fin 11)) 10 = (c : Fin 11) := by
    change (Equiv.Perm.ofSubtype u) (b : Fin 11) = (c : Fin 11)
    rw [Equiv.Perm.ofSubtype_apply_coe]
    have hub : u b = c := by
      change (Equiv.swap a b * Equiv.swap b c) b = c
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hca hcb]
    rw [hub]
  intro hgS
  rcases hgS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : (c : Fin 11) = 10 := by rw [← hg10, h2]
    exact hcb (Subtype.ext this)
  · have : (c : Fin 11) = 9 := by rw [← hg10, h2]
    exact hca (Subtype.ext this)

theorem exists_mem_centralizer_not_mem_a11TwoSetStab (hσS : σ ∈ a11TwoSetStab 9 10)
    (hσ : orderOf σ = 3)
    (hs : (σ : Equiv.Perm (Fin 11)).support.card ≤ 6) :
    ∃ g ∈ Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))),
      g ∉ a11TwoSetStab 9 10 := by
  obtain ⟨h9, h10⟩ := apply_nine_ten_of_mem_a11TwoSetStab hσS hσ
  have hpos : 0 < (fixedPointsPairFinset σ h9 h10).card := by
    rw [card_fixedPointsPairFinset, card_fixedPoints_a11]
    omega
  obtain ⟨c, hcF⟩ := Finset.card_pos.mp hpos
  exact exists_threeCycle_centralizer_not_stab h9 h10 c
    (mem_fixedPointsPairFinset_ne σ h9 h10 hcF).1
    (mem_fixedPointsPairFinset_ne σ h9 h10 hcF).2

theorem card_support_eq_nine_of_centralizer_le (hσS : σ ∈ a11TwoSetStab 9 10)
    (hσ : orderOf σ = 3)
    (hC : Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) ≤ a11TwoSetStab 9 10) :
    (σ : Equiv.Perm (Fin 11)).support.card = 9 := by
  have hσ' : orderOf (σ : Equiv.Perm (Fin 11)) = 3 := by
    rwa [Subgroup.orderOf_coe]
  rcases CFSG.Permutation.card_support_eq_three_or_six_or_nine hσ' with h3 | h6 | h9
  · obtain ⟨g, hgC, hgS⟩ :=
      exists_mem_centralizer_not_mem_a11TwoSetStab hσS hσ (by omega)
    exact absurd (hC hgC) hgS
  · obtain ⟨g, hgC, hgS⟩ :=
      exists_mem_centralizer_not_mem_a11TwoSetStab hσS hσ (by omega)
    exact absurd (hC hgC) hgS
  · exact h9

private def sixPointFinset (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10) :
    Finset (Function.fixedPoints (σ : Equiv.Perm (Fin 11))) :=
  fixedPointsPairFinset σ h9 h10

private lemma card_sixPointFinset (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10)
    (hs : (σ : Equiv.Perm (Fin 11)).support.card = 3) : (sixPointFinset h9 h10).card = 6 := by
  rw [sixPointFinset, card_fixedPointsPairFinset, card_fixedPoints_a11, hs]

private noncomputable def sixPointHom (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10) :
    alternatingGroup ↥(sixPointFinset h9 h10) →* alternatingGroup (Fin 11) :=
  let F := sixPointFinset h9 h10
  (Equiv.Perm.ofSubtype.comp (Equiv.Perm.ofSubtype.comp (alternatingGroup ↥F).subtype)).codRestrict
    (alternatingGroup (Fin 11)) (fun u => by
      rw [Equiv.Perm.mem_alternatingGroup, MonoidHom.comp_apply, MonoidHom.comp_apply,
        Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_ofSubtype]
      exact Equiv.Perm.mem_alternatingGroup.mp u.2)

private noncomputable def sixPointPerfect (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10) : Subgroup (alternatingGroup (Fin 11)) :=
  (sixPointHom h9 h10).range

private lemma sixPointHom_injective (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10) :
    Function.Injective (sixPointHom (σ := σ) h9 h10) := by
  intro u v h
  have h1 : (Equiv.Perm.ofSubtype (Equiv.Perm.ofSubtype
        (u : Perm ↥(sixPointFinset h9 h10))) : Perm (Fin 11)) =
      Equiv.Perm.ofSubtype (Equiv.Perm.ofSubtype
        (v : Perm ↥(sixPointFinset h9 h10))) := by
    simpa [sixPointHom] using
      congrArg (fun x : alternatingGroup (Fin 11) => (x : Perm (Fin 11))) h
  exact Subtype.ext (Equiv.Perm.ofSubtype_injective
    (Equiv.Perm.ofSubtype_injective h1))

private lemma sixPointPerfect_le_stab (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10) :
    sixPointPerfect (σ := σ) h9 h10 ≤ a11TwoSetStab 9 10 := by
  intro p hp
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hp
  have ha : fixedNine σ h9 ∉ sixPointFinset h9 h10 := by
    dsimp only [sixPointFinset, fixedPointsPairFinset]
    simp
  have hb : fixedTen σ h10 ∉ sixPointFinset h9 h10 := by
    dsimp only [sixPointFinset, fixedPointsPairFinset]
    simp
  refine Or.inl ⟨?_, ?_⟩
  · change (Equiv.Perm.ofSubtype (Equiv.Perm.ofSubtype
        (u : Perm ↥(sixPointFinset h9 h10))) : Perm (Fin 11))
        (fixedNine σ h9 : Fin 11) = 9
    rw [Equiv.Perm.ofSubtype_apply_coe,
      Equiv.Perm.ofSubtype_apply_of_not_mem (u : Perm ↥(sixPointFinset h9 h10)) ha]
    rfl
  · change (Equiv.Perm.ofSubtype (Equiv.Perm.ofSubtype
        (u : Perm ↥(sixPointFinset h9 h10))) : Perm (Fin 11))
        (fixedTen σ h10 : Fin 11) = 10
    rw [Equiv.Perm.ofSubtype_apply_coe,
      Equiv.Perm.ofSubtype_apply_of_not_mem (u : Perm ↥(sixPointFinset h9 h10)) hb]
    rfl

private lemma sixPointPerfect_le_centralizer (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10) :
    sixPointPerfect (σ := σ) h9 h10 ≤
      Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) := by
  intro p hp
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hp
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have hd : (Equiv.Perm.ofSubtype (Equiv.Perm.ofSubtype
      (u : Perm ↥(sixPointFinset h9 h10))) : Perm (Fin 11)).Disjoint
      (σ : Perm (Fin 11)) :=
    Equiv.Perm.disjoint_ofSubtype_of_memFixedPoints_self
      (Equiv.Perm.ofSubtype (u : Perm ↥(sixPointFinset h9 h10)))
  exact hd.commute.eq

private lemma sixPointPerfect_card (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10)
    (hs : (σ : Equiv.Perm (Fin 11)).support.card = 3) :
    Nat.card (sixPointPerfect (σ := σ) h9 h10) = 360 := by
  have hFcard := card_sixPointFinset (σ := σ) h9 h10 hs
  haveI : Nontrivial ↥(sixPointFinset h9 h10) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe, hFcard]; norm_num)
  have hcardEq : Nat.card (sixPointPerfect (σ := σ) h9 h10) =
      Nat.card ↥(alternatingGroup ↥(sixPointFinset h9 h10)) := by
    dsimp only [sixPointPerfect]
    exact Nat.card_congr (Equiv.ofInjective (sixPointHom h9 h10)
      (sixPointHom_injective (σ := σ) h9 h10)).symm
  rw [hcardEq, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_coe, hFcard]
  norm_num

private lemma sixPointPerfect_ne_bot (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10)
    (hs : (σ : Equiv.Perm (Fin 11)).support.card = 3) :
    sixPointPerfect (σ := σ) h9 h10 ≠ ⊥ := by
  have hcard := sixPointPerfect_card (σ := σ) h9 h10 hs
  intro hbot
  have h1 : Nat.card (sixPointPerfect (σ := σ) h9 h10) = 1 := by
    rw [hbot, Subgroup.card_bot]
  omega

private lemma sixPointPerfect_perfect (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10)
    (hs : (σ : Equiv.Perm (Fin 11)).support.card = 3) :
    ⁅sixPointPerfect (σ := σ) h9 h10, sixPointPerfect (σ := σ) h9 h10⁆ =
      sixPointPerfect (σ := σ) h9 h10 := by
  have hFcard := card_sixPointFinset (σ := σ) h9 h10 hs
  haveI : Group.IsPerfect ↥(alternatingGroup ↥(sixPointFinset h9 h10)) :=
    ⟨commutator_alternatingGroup_eq_top (by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hFcard]; norm_num)⟩
  letI : Group.IsPerfect ↥(sixPointPerfect (σ := σ) h9 h10) := by
    dsimp only [sixPointPerfect]
    exact Group.IsPerfect.range (sixPointHom h9 h10)
  exact Subgroup.commutator_eq_self

private lemma exists_sixPoint_data (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10)
    (hs : (σ : Equiv.Perm (Fin 11)).support.card = 3)
    {u : alternatingGroup ↥(sixPointFinset h9 h10)}
    (hu1 : sixPointHom (σ := σ) h9 h10 u ≠ 1) :
    ∃ (y z c : Function.fixedPoints (σ : Equiv.Perm (Fin 11))),
      (Equiv.Perm.ofSubtype (u : Perm ↥(sixPointFinset h9 h10))) y = z ∧
      y ≠ z ∧ y ≠ c ∧ z ≠ c ∧
      y ≠ fixedNine σ h9 ∧ c ≠ fixedNine σ h9 ∧ c ≠ fixedTen σ h10 := by
  classical
  let F := sixPointFinset (σ := σ) h9 h10
  let X := Function.fixedPoints (σ : Equiv.Perm (Fin 11))
  let w : Perm X := Equiv.Perm.ofSubtype (u : Perm ↥F)
  have hψu : ((sixPointHom (σ := σ) h9 h10 u : alternatingGroup (Fin 11)) :
      Perm (Fin 11)) = Equiv.Perm.ofSubtype w := rfl
  have hw1 : w ≠ 1 := by
    intro hw
    apply hu1
    apply Subtype.ext
    rw [hψu, hw]
    simp
  have hwF : w.support ⊆ F := by
    intro z hz
    have hz' : z ∈ (Equiv.Perm.ofSubtype (u : Perm ↥F)).support := by
      rwa [show w = Equiv.Perm.ofSubtype (u : Perm ↥F) from rfl] at hz
    exact ((Equiv.Perm.mem_support_ofSubtype z (u : Perm ↥F)).mp hz').1
  have hwpos : 0 < w.support.card := by
    have := Equiv.Perm.one_lt_card_support_of_ne_one hw1
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hwpos
  have hwy : w y ≠ y := Equiv.Perm.mem_support.mp hy
  have hyF : y ∈ F := hwF hy
  let z : X := w y
  have hzF : z ∈ F := hwF (Equiv.Perm.apply_mem_support.mpr hy)
  have hzy : z ≠ y := hwy
  have hmemz : z ∈ F.erase y := Finset.mem_erase.mpr ⟨hzy, hzF⟩
  have hFcard : F.card = 6 := card_sixPointFinset (σ := σ) h9 h10 hs
  have hcard : ((F.erase y).erase z).card = 4 := by
    rw [Finset.card_erase_of_mem hmemz, Finset.card_erase_of_mem hyF, hFcard]
  have hcardpos : 0 < ((F.erase y).erase z).card := by rw [hcard]; norm_num
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hcardpos
  rw [Finset.mem_erase, Finset.mem_erase] at hc
  obtain ⟨hcz, hcy, hcF⟩ := hc
  have haF : fixedNine σ h9 ∉ F := by
    dsimp only [F, sixPointFinset, fixedPointsPairFinset]
    simp
  have hbF : fixedTen σ h10 ∉ F := by
    dsimp only [F, sixPointFinset, fixedPointsPairFinset]
    simp
  refine ⟨y, z, c, ?_, Ne.symm hzy, Ne.symm hcy, Ne.symm hcz,
    fun h => haF (h ▸ hyF), fun h => haF (h ▸ hcF), fun h => hbF (h ▸ hcF)⟩
  change (Equiv.Perm.ofSubtype (u : Perm ↥F)) y = w y
  rfl

private lemma exists_conj_apply_nine (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10)
    {u : alternatingGroup ↥(sixPointFinset h9 h10)}
    {y z c : Function.fixedPoints (σ : Equiv.Perm (Fin 11))}
    (hwy : (Equiv.Perm.ofSubtype (u : Perm ↥(sixPointFinset h9 h10))) y = z)
    (hyz : y ≠ z) (hyc : y ≠ c) (hzc : z ≠ c)
    (hya : y ≠ fixedNine σ h9) (hca : c ≠ fixedNine σ h9) :
    ∃ g ∈ Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))),
      ((g * sixPointHom (σ := σ) h9 h10 u * g⁻¹ : alternatingGroup (Fin 11)) :
        Perm (Fin 11)) 9 = (c : Fin 11) := by
  classical
  let F := sixPointFinset (σ := σ) h9 h10
  let X := Function.fixedPoints (σ : Equiv.Perm (Fin 11))
  let u2 : Perm X := Equiv.swap y (fixedNine σ h9) * Equiv.swap z c
  have hu2sign : Equiv.Perm.sign u2 = 1 := by
    change Equiv.Perm.sign (Equiv.swap y (fixedNine σ h9) * Equiv.swap z c) = 1
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hya, Equiv.Perm.sign_swap hzc]
    norm_num
  let g : alternatingGroup (Fin 11) :=
    ⟨Equiv.Perm.ofSubtype u2, by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype, hu2sign]⟩
  have hgC : g ∈ Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hd : (Equiv.Perm.ofSubtype u2 : Perm (Fin 11)).Disjoint (σ : Perm (Fin 11)) :=
      Equiv.Perm.disjoint_ofSubtype_of_memFixedPoints_self u2
    exact hd.commute.eq
  have hgy : (Equiv.Perm.ofSubtype u2) (y : Fin 11) = (9 : Fin 11) := by
    rw [Equiv.Perm.ofSubtype_apply_coe]
    have huy : u2 y = fixedNine σ h9 := by
      change (Equiv.swap y (fixedNine σ h9) * Equiv.swap z c) y = fixedNine σ h9
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hyz hyc,
        Equiv.swap_apply_left]
    rw [huy]
    rfl
  have hgz : (Equiv.Perm.ofSubtype u2) (z : Fin 11) = (c : Fin 11) := by
    rw [Equiv.Perm.ofSubtype_apply_coe]
    have huz : u2 z = c := by
      change (Equiv.swap y (fixedNine σ h9) * Equiv.swap z c) z = c
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hyc) hca]
    rw [huz]
  have hinv : (Equiv.Perm.ofSubtype u2)⁻¹ (9 : Fin 11) = (y : Fin 11) := by
    have h := (Equiv.Perm.eq_inv_iff_eq (f := Equiv.Perm.ofSubtype u2)
      (x := (y : Fin 11)) (y := (9 : Fin 11))).mpr hgy
    exact h.symm
  have hxPy : ((sixPointHom (σ := σ) h9 h10 u : alternatingGroup (Fin 11)) :
      Perm (Fin 11)) (y : Fin 11) = (z : Fin 11) := by
    rw [show ((sixPointHom (σ := σ) h9 h10 u : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
      Equiv.Perm.ofSubtype (Equiv.Perm.ofSubtype (u : Perm ↥F)) from rfl]
    rw [Equiv.Perm.ofSubtype_apply_coe]
    exact congrArg Subtype.val hwy
  refine ⟨g, hgC, ?_⟩
  have hcoe : ((g * sixPointHom (σ := σ) h9 h10 u * g⁻¹ : alternatingGroup (Fin 11)) :
      Perm (Fin 11)) = (g : Perm (Fin 11)) *
        ((sixPointHom (σ := σ) h9 h10 u : alternatingGroup (Fin 11)) : Perm (Fin 11)) *
        ((g : Perm (Fin 11))⁻¹) := by
    simp
  rw [hcoe, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv, hxPy, hgz]

private lemma sixPointPerfect_inf_normalizer_eq_bot
    (h9 : (σ : Equiv.Perm (Fin 11)) 9 = 9) (h10 : (σ : Equiv.Perm (Fin 11)) 10 = 10)
    (hs : (σ : Equiv.Perm (Fin 11)).support.card = 3)
    (N : Subgroup (alternatingGroup (Fin 11))) (hNle : N ≤ a11TwoSetStab 9 10)
    (hCN : Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) ≤
      Subgroup.normalizer (N : Set (alternatingGroup (Fin 11)))) :
    sixPointPerfect (σ := σ) h9 h10 ⊓ N = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨hxP, hxN⟩ := Subgroup.mem_inf.mp hx
  change x ∈ (sixPointHom (σ := σ) h9 h10).range at hxP
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hxP
  obtain ⟨y, z, c, hwy, hyz, hyc, hzc, hya, hca, hcb⟩ :=
    exists_sixPoint_data (σ := σ) h9 h10 hs hx1
  obtain ⟨g, hgC, hgval⟩ := exists_conj_apply_nine h9 h10 hwy hyz hyc hzc hya hca
  have hgN : g * sixPointHom (σ := σ) h9 h10 u * g⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hCN hgC) (sixPointHom (σ := σ) h9 h10 u)).mp hxN
  have hgS := hNle hgN
  rcases hgS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : (c : Fin 11) = 9 := by rw [← hgval, h1]
    exact hca (Subtype.ext this)
  · have : (c : Fin 11) = 10 := by rw [← hgval, h1]
    exact hcb (Subtype.ext this)

theorem exists_perfect_inf_eq_bot_of_card_support_eq_three (hσS : σ ∈ a11TwoSetStab 9 10)
    (hσ : orderOf σ = 3)
    (hs : (σ : Equiv.Perm (Fin 11)).support.card = 3) :
    ∃ P : Subgroup (alternatingGroup (Fin 11)),
      P ≤ a11TwoSetStab 9 10 ⊓ Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) ∧
      P ≠ ⊥ ∧ ⁅P, P⁆ = P ∧
      ∀ N : Subgroup (alternatingGroup (Fin 11)), N ≤ a11TwoSetStab 9 10 →
        Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) ≤
          Subgroup.normalizer (N : Set (alternatingGroup (Fin 11))) →
        P ⊓ N = ⊥ := by
  obtain ⟨h9, h10⟩ := apply_nine_ten_of_mem_a11TwoSetStab hσS hσ
  refine ⟨sixPointPerfect (σ := σ) h9 h10, ?_,
    sixPointPerfect_ne_bot (σ := σ) h9 h10 hs,
    sixPointPerfect_perfect (σ := σ) h9 h10 hs, ?_⟩
  · exact le_inf (sixPointPerfect_le_stab (σ := σ) h9 h10)
      (sixPointPerfect_le_centralizer (σ := σ) h9 h10)
  · exact sixPointPerfect_inf_normalizer_eq_bot (σ := σ) h9 h10 hs

private lemma maps_fixedPoints_of_conj {c : alternatingGroup (Fin 11)}
    (hc_conj : (c : Equiv.Perm (Fin 11)) * (σ : Equiv.Perm (Fin 11)) *
      (c : Equiv.Perm (Fin 11))⁻¹ = (τ : Equiv.Perm (Fin 11))) :
    ∀ x : Fin 11, (σ : Equiv.Perm (Fin 11)) x = x →
      (τ : Equiv.Perm (Fin 11)) ((c : Equiv.Perm (Fin 11)) x) =
        (c : Equiv.Perm (Fin 11)) x := by
  intro x hx
  have hconj : (c : Equiv.Perm (Fin 11)) * (σ : Equiv.Perm (Fin 11)) =
      (τ : Equiv.Perm (Fin 11)) * (c : Equiv.Perm (Fin 11)) := by
    calc (c : Equiv.Perm (Fin 11)) * (σ : Equiv.Perm (Fin 11)) =
        ((c : Equiv.Perm (Fin 11)) * (σ : Equiv.Perm (Fin 11)) *
          (c : Equiv.Perm (Fin 11))⁻¹) * (c : Equiv.Perm (Fin 11)) := by group
      _ = (τ : Equiv.Perm (Fin 11)) * (c : Equiv.Perm (Fin 11)) := by rw [hc_conj]
  have hval := congrArg (fun p : Equiv.Perm (Fin 11) => p x) hconj
  simpa [Equiv.Perm.mul_apply, hx] using hval.symm

private lemma mem_a11TwoSetStab_of_support_nine {c : alternatingGroup (Fin 11)}
    (h9σ : (σ : Equiv.Perm (Fin 11)) 9 = 9) (h10σ : (σ : Equiv.Perm (Fin 11)) 10 = 10)
    (h9τ : (τ : Equiv.Perm (Fin 11)) 9 = 9) (h10τ : (τ : Equiv.Perm (Fin 11)) 10 = 10)
    (hc_conj : (c : Equiv.Perm (Fin 11)) * (σ : Equiv.Perm (Fin 11)) *
      (c : Equiv.Perm (Fin 11))⁻¹ = (τ : Equiv.Perm (Fin 11)))
    (hst : (σ : Equiv.Perm (Fin 11)).support.card =
      (τ : Equiv.Perm (Fin 11)).support.card)
    (hs9 : (σ : Equiv.Perm (Fin 11)).support.card = 9) :
    c ∈ a11TwoSetStab 9 10 := by
  classical
  have hmaps := maps_fixedPoints_of_conj hc_conj
  have hc9X : (τ : Equiv.Perm (Fin 11)) ((c : Equiv.Perm (Fin 11)) 9) =
      (c : Equiv.Perm (Fin 11)) 9 := hmaps 9 h9σ
  have hc10X : (τ : Equiv.Perm (Fin 11)) ((c : Equiv.Perm (Fin 11)) 10) =
      (c : Equiv.Perm (Fin 11)) 10 := hmaps 10 h10σ
  let Xτ := Function.fixedPoints (τ : Equiv.Perm (Fin 11))
  let aτ : Xτ := fixedNine τ h9τ
  let bτ : Xτ := fixedTen τ h10τ
  have habτ : aτ ≠ bτ := fixedNine_ne_fixedTen τ h9τ h10τ
  have hXcard : Nat.card Xτ = 2 := by
    rw [card_fixedPoints_a11, ← hst, hs9]
  let G : Finset Xτ := {aτ, bτ}
  have hGcard : G.card = 2 := by
    dsimp only [G]
    rw [Finset.card_pair habτ]
  have hGuniv : G = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hGcard, ← Nat.card_eq_fintype_card, hXcard]
  have hpair : ∀ z : Xτ, z = aτ ∨ z = bτ := by
    intro z
    have hz : z ∈ G := by
      rw [hGuniv]
      exact Finset.mem_univ z
    dsimp only [G] at hz
    simpa using hz
  let c9 : Xτ := ⟨(c : Equiv.Perm (Fin 11)) 9, hc9X⟩
  let c10 : Xτ := ⟨(c : Equiv.Perm (Fin 11)) 10, hc10X⟩
  have hval9 : (c : Equiv.Perm (Fin 11)) 9 = (c9 : Fin 11) := rfl
  have hval10 : (c : Equiv.Perm (Fin 11)) 10 = (c10 : Fin 11) := rfl
  rcases hpair c9 with h9 | h9 <;> rcases hpair c10 with h10 | h10
  · exfalso
    have h9v : (c : Equiv.Perm (Fin 11)) 9 = 9 := by
      rw [hval9, congrArg (fun x : Xτ => (x : Fin 11)) h9, coe_fixedNine]
    have h10v : (c : Equiv.Perm (Fin 11)) 10 = 9 := by
      rw [hval10, congrArg (fun x : Xτ => (x : Fin 11)) h10, coe_fixedNine]
    exact (by decide : (9 : Fin 11) ≠ 10)
      ((c : Equiv.Perm (Fin 11)).injective (h9v.trans h10v.symm))
  · left
    exact ⟨by rw [hval9, congrArg (fun x : Xτ => (x : Fin 11)) h9, coe_fixedNine],
      by rw [hval10, congrArg (fun x : Xτ => (x : Fin 11)) h10, coe_fixedTen]⟩
  · right
    exact ⟨by rw [hval9, congrArg (fun x : Xτ => (x : Fin 11)) h9, coe_fixedTen],
      by rw [hval10, congrArg (fun x : Xτ => (x : Fin 11)) h10, coe_fixedNine]⟩
  · exfalso
    have h9v : (c : Equiv.Perm (Fin 11)) 9 = 10 := by
      rw [hval9, congrArg (fun x : Xτ => (x : Fin 11)) h9, coe_fixedTen]
    have h10v : (c : Equiv.Perm (Fin 11)) 10 = 10 := by
      rw [hval10, congrArg (fun x : Xτ => (x : Fin 11)) h10, coe_fixedTen]
    exact (by decide : (9 : Fin 11) ≠ 10)
      ((c : Equiv.Perm (Fin 11)).injective (h9v.trans h10v.symm))

private lemma exists_even_correction (h9τ : (τ : Equiv.Perm (Fin 11)) 9 = 9)
    (h10τ : (τ : Equiv.Perm (Fin 11)) 10 = 10)
    {c9 c10 : Function.fixedPoints (τ : Equiv.Perm (Fin 11))}
    (hX4 : 4 ≤ Nat.card (Function.fixedPoints (τ : Equiv.Perm (Fin 11))))
    (hc9c10 : c9 ≠ c10) :
    ∃ k : alternatingGroup (Function.fixedPoints (τ : Equiv.Perm (Fin 11))),
      (k : Perm (Function.fixedPoints (τ : Equiv.Perm (Fin 11)))) c9 =
        fixedNine τ h9τ ∧
      (k : Perm (Function.fixedPoints (τ : Equiv.Perm (Fin 11)))) c10 =
        fixedTen τ h10τ := by
  classical
  let Xτ := Function.fixedPoints (τ : Equiv.Perm (Fin 11))
  have hX4' : 4 ≤ Nat.card Xτ := hX4
  haveI : MulAction.IsMultiplyPretransitive (alternatingGroup Xτ) Xτ (Nat.card Xτ - 2) :=
    alternatingGroup.isMultiplyPretransitive Xτ
  haveI : MulAction.IsMultiplyPretransitive (alternatingGroup Xτ) Xτ 2 :=
    MulAction.isMultiplyPretransitive_of_le (m := 2) (n := Nat.card Xτ - 2)
      (by omega) (Nat.sub_le _ _)
  let aτ : Xτ := fixedNine τ h9τ
  let bτ : Xτ := fixedTen τ h10τ
  have habτ : aτ ≠ bτ := fixedNine_ne_fixedTen τ h9τ h10τ
  let x : Fin 2 ↪ Xτ := Function.Embedding.embFinTwo (a := c9) (b := c10) hc9c10
  let y : Fin 2 ↪ Xτ := Function.Embedding.embFinTwo (a := aτ) (b := bτ) habτ
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (alternatingGroup Xτ) x y
  have hk0 : (k : Equiv.Perm Xτ) c9 = aτ := by
    have h0 := congrArg (fun e : Fin 2 ↪ Xτ => e 0) hk
    simpa [x, y, Function.Embedding.embFinTwo_apply_zero, Function.Embedding.smul_apply,
      Subgroup.smul_def, Equiv.Perm.smul_def] using h0
  have hk1 : (k : Equiv.Perm Xτ) c10 = bτ := by
    have h1 := congrArg (fun e : Fin 2 ↪ Xτ => e 1) hk
    simpa [x, y, Function.Embedding.embFinTwo_apply_one, Function.Embedding.smul_apply,
      Subgroup.smul_def, Equiv.Perm.smul_def] using h1
  exact ⟨k, hk0, hk1⟩

private lemma exists_conj_mem_stab_of_correction {c : alternatingGroup (Fin 11)}
    (h9τ : (τ : Equiv.Perm (Fin 11)) 9 = 9) (h10τ : (τ : Equiv.Perm (Fin 11)) 10 = 10)
    (hc_conj : (c : Equiv.Perm (Fin 11)) * (σ : Equiv.Perm (Fin 11)) *
      (c : Equiv.Perm (Fin 11))⁻¹ = (τ : Equiv.Perm (Fin 11)))
    {c9 c10 : Function.fixedPoints (τ : Equiv.Perm (Fin 11))}
    (hc9 : (c : Equiv.Perm (Fin 11)) 9 = (c9 : Fin 11))
    (hc10 : (c : Equiv.Perm (Fin 11)) 10 = (c10 : Fin 11))
    {k : alternatingGroup (Function.fixedPoints (τ : Equiv.Perm (Fin 11)))}
    (hk0 : (k : Perm (Function.fixedPoints (τ : Equiv.Perm (Fin 11)))) c9 =
      fixedNine τ h9τ)
    (hk1 : (k : Perm (Function.fixedPoints (τ : Equiv.Perm (Fin 11)))) c10 =
      fixedTen τ h10τ) :
    ∃ g ∈ a11TwoSetStab 9 10, g * σ * g⁻¹ = τ := by
  classical
  let Xτ := Function.fixedPoints (τ : Equiv.Perm (Fin 11))
  let kP : Perm (Fin 11) := Equiv.Perm.ofSubtype (k : Perm Xτ)
  have hkP : kP.Disjoint (τ : Perm (Fin 11)) :=
    Equiv.Perm.disjoint_ofSubtype_of_memFixedPoints_self (k : Perm Xτ)
  have hkcomm : kP * (τ : Perm (Fin 11)) = (τ : Perm (Fin 11)) * kP := hkP.commute.eq
  have hsign : (kP * (c : Perm (Fin 11))) ∈ alternatingGroup (Fin 11) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_ofSubtype,
      Equiv.Perm.mem_alternatingGroup.mp k.2, Equiv.Perm.mem_alternatingGroup.mp c.2]
    norm_num
  let g : alternatingGroup (Fin 11) := ⟨kP * (c : Perm (Fin 11)), hsign⟩
  refine ⟨g, ?_, ?_⟩
  · refine Or.inl ⟨?_, ?_⟩
    · change kP ((c : Perm (Fin 11)) 9) = 9
      rw [hc9, Equiv.Perm.ofSubtype_apply_coe, hk0, coe_fixedNine]
    · change kP ((c : Perm (Fin 11)) 10) = 10
      rw [hc10, Equiv.Perm.ofSubtype_apply_coe, hk1, coe_fixedTen]
  · apply Subtype.ext
    change kP * (c : Perm (Fin 11)) * (σ : Perm (Fin 11)) *
        (kP * (c : Perm (Fin 11)))⁻¹ = (τ : Perm (Fin 11))
    calc kP * (c : Perm (Fin 11)) * (σ : Perm (Fin 11)) *
          (kP * (c : Perm (Fin 11)))⁻¹ =
        kP * ((c : Perm (Fin 11)) * (σ : Perm (Fin 11)) *
          (c : Perm (Fin 11))⁻¹) * kP⁻¹ := by group
      _ = kP * (τ : Perm (Fin 11)) * kP⁻¹ := by rw [hc_conj]
      _ = (τ : Perm (Fin 11)) := by rw [hkcomm]; group

private lemma exists_conj_mem_stab_of_fixed_four {c : alternatingGroup (Fin 11)}
    (h9σ : (σ : Equiv.Perm (Fin 11)) 9 = 9) (h10σ : (σ : Equiv.Perm (Fin 11)) 10 = 10)
    (h9τ : (τ : Equiv.Perm (Fin 11)) 9 = 9) (h10τ : (τ : Equiv.Perm (Fin 11)) 10 = 10)
    (hc_conj : (c : Equiv.Perm (Fin 11)) * (σ : Equiv.Perm (Fin 11)) *
      (c : Equiv.Perm (Fin 11))⁻¹ = (τ : Equiv.Perm (Fin 11)))
    (hX4 : 4 ≤ Nat.card (Function.fixedPoints (τ : Equiv.Perm (Fin 11)))) :
    ∃ g ∈ a11TwoSetStab 9 10, g * σ * g⁻¹ = τ := by
  classical
  have hmaps := maps_fixedPoints_of_conj hc_conj
  have hc9X : (τ : Equiv.Perm (Fin 11)) ((c : Equiv.Perm (Fin 11)) 9) =
      (c : Equiv.Perm (Fin 11)) 9 := hmaps 9 h9σ
  have hc10X : (τ : Equiv.Perm (Fin 11)) ((c : Equiv.Perm (Fin 11)) 10) =
      (c : Equiv.Perm (Fin 11)) 10 := hmaps 10 h10σ
  let Xτ := Function.fixedPoints (τ : Equiv.Perm (Fin 11))
  let c9 : Xτ := ⟨(c : Equiv.Perm (Fin 11)) 9, hc9X⟩
  let c10 : Xτ := ⟨(c : Equiv.Perm (Fin 11)) 10, hc10X⟩
  have hc9c10 : c9 ≠ c10 := by
    intro h
    have h' : (c : Equiv.Perm (Fin 11)) 9 = (c : Equiv.Perm (Fin 11)) 10 :=
      congrArg (fun x : Xτ => (x : Fin 11)) h
    exact (by decide : (9 : Fin 11) ≠ 10) ((c : Equiv.Perm (Fin 11)).injective h')
  obtain ⟨k, hk0, hk1⟩ := exists_even_correction h9τ h10τ hX4 hc9c10
  exact exists_conj_mem_stab_of_correction h9τ h10τ hc_conj rfl rfl hk0 hk1

theorem exists_conj_eq_of_card_support_eq (hσS : σ ∈ a11TwoSetStab 9 10)
    (hτS : τ ∈ a11TwoSetStab 9 10) (hσ : orderOf σ = 3) (hτ : orderOf τ = 3)
    (hst : (σ : Equiv.Perm (Fin 11)).support.card = (τ : Equiv.Perm (Fin 11)).support.card) :
    ∃ g ∈ a11TwoSetStab 9 10, g * σ * g⁻¹ = τ := by
  classical
  obtain ⟨h9σ, h10σ⟩ := apply_nine_ten_of_mem_a11TwoSetStab hσS hσ
  obtain ⟨h9τ, h10τ⟩ := apply_nine_ten_of_mem_a11TwoSetStab hτS hτ
  have hσ' : orderOf (σ : Equiv.Perm (Fin 11)) = 3 := by
    rwa [Subgroup.orderOf_coe]
  have hτ' : orderOf (τ : Equiv.Perm (Fin 11)) = 3 := by
    rwa [Subgroup.orderOf_coe]
  have hct : (σ : Equiv.Perm (Fin 11)).cycleType = (τ : Equiv.Perm (Fin 11)).cycleType := by
    rw [CFSG.HardMathSupport.RichardWeiss.Proving.cycleType_eq_replicate_three hσ',
      CFSG.HardMathSupport.RichardWeiss.Proving.cycleType_eq_replicate_three hτ']
    congr 1
    have hsumσ := Equiv.Perm.sum_cycleType (σ : Equiv.Perm (Fin 11))
    have hsumτ := Equiv.Perm.sum_cycleType (τ : Equiv.Perm (Fin 11))
    rw [CFSG.HardMathSupport.RichardWeiss.Proving.cycleType_eq_replicate_three hσ',
      Multiset.sum_replicate, smul_eq_mul] at hsumσ
    rw [CFSG.HardMathSupport.RichardWeiss.Proving.cycleType_eq_replicate_three hτ',
      Multiset.sum_replicate, smul_eq_mul] at hsumτ
    omega
  have hcases : (σ : Equiv.Perm (Fin 11)).support.card = 3 ∨
      (σ : Equiv.Perm (Fin 11)).support.card = 6 ∨
      (σ : Equiv.Perm (Fin 11)).support.card = 9 :=
    CFSG.Permutation.card_support_eq_three_or_six_or_nine hσ'
  have hsle : (σ : Equiv.Perm (Fin 11)).support.card + 2 ≤ Fintype.card (Fin 11) := by
    rw [Fintype.card_fin]
    rcases hcases with h | h | h <;> omega
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (alternatingGroup.isConj_of (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct) hsle)
  have hc_conj : (c : Equiv.Perm (Fin 11)) * (σ : Equiv.Perm (Fin 11)) *
      (c : Equiv.Perm (Fin 11))⁻¹ = (τ : Equiv.Perm (Fin 11)) := by
    simpa using congrArg (fun x : alternatingGroup (Fin 11) => (x : Equiv.Perm (Fin 11))) hc
  by_cases hs9 : (σ : Equiv.Perm (Fin 11)).support.card = 9
  · exact ⟨c, mem_a11TwoSetStab_of_support_nine h9σ h10σ h9τ h10τ hc_conj hst hs9, hc⟩
  · have hX4 : 4 ≤ Nat.card (Function.fixedPoints (τ : Equiv.Perm (Fin 11))) := by
      rw [card_fixedPoints_a11, ← hst]
      rcases hcases with h | h | h
      · omega
      · omega
      · exact absurd h hs9
    exact exists_conj_mem_stab_of_fixed_four h9σ h10σ h9τ h10τ hc_conj hX4

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
