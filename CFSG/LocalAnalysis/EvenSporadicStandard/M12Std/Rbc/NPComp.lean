module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPLayer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPCompTwist
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPCompQuasi
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPCompDbar

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.EvenSporadicStandard.HSStd

theorem layerIn_eq_of_unique {H : Type} [Group H] {E : Subgroup H} (hE : IsCompIn E ⊤)
    (hall : ∀ E' : Subgroup H, IsCompIn E' ⊤ → E' = E) : layerIn (⊤ : Subgroup H) = E := by
  have h : {M : Subgroup H | IsCompIn M ⊤} = {E} :=
    Set.ext fun M => ⟨fun hM => hall M hM, fun hM => by
      rw [Set.mem_singleton_iff] at hM
      rw [Set.mem_setOf_eq, hM]
      exact hE⟩
  unfold layerIn
  rw [h, sSup_singleton]

namespace NPSetting

variable {G : Type} [Group G] [Finite G] {X : Subgroup G} {u x : G} {T₀ : Subgroup G} {s₀ : G}

theorem ubar_conj_mem (hS : NPSetting G X u x T₀ s₀) {E : Subgroup (OddQuot (npD X x))}
    (hE : IsCompIn E ⊤) : ∀ g ∈ E, hS.ubar * g * hS.ubar⁻¹ ∈ E := by
  intro g hg
  have h : hS.ubar * g * hS.ubar⁻¹ ∈ E.map (MulAut.conj hS.ubar).toMonoidHom := ⟨g, hg, rfl⟩
  rwa [(hS.comp_invariant hE).1] at h

theorem ubar_mem_centralizer (hS : NPSetting G X u x T₀ s₀) :
    hS.ubar ∈ centralizer ({hS.ubar} : Set (OddQuot (npD X x))) :=
  mem_centralizer_singleton_iff.2 rfl

theorem nonempty_Abar_equiv (hS : NPSetting G X u x T₀ s₀) :
    Nonempty (↥(oddBar (npD X x) (npA X x s₀)) ≃* alternatingGroup (Fin 5)) := by
  have hc : ∀ h : ↥(npA X x s₀), (∀ h', h * h' = h' * h) → h = 1 := by
    intro h hh
    have h1 : h ∈ center ↥(npA X x s₀) := mem_center_iff.2 fun g => (hh g).symm
    rw [hS.center_A_eq_bot] at h1
    exact Subgroup.mem_bot.1 h1
  obtain ⟨e⟩ := PropA.nonempty_alt5_of_quasisimple hS.isCompIn_A.isQuasisimple hc hS.card_A
  exact ⟨hS.oddBarEquivA.symm.trans e⟩

theorem comp_typeI (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀)
    {E : Subgroup (OddQuot (npD X x))} (hE : IsCompIn E ⊤) :
    Nonempty ((↥E ⧸ center ↥E) ≃* alternatingGroup (Fin 5)) ∧
      Nat.card ↥(E ⊓ centralizer ({hS.ubar} : Set (OddQuot (npD X x)))) = 4 := by
  rcases hS.kdnp_comp hNP hE with h | hcard
  · exact h
  · exfalso
    have hCE : E ⊓ centralizer ({hS.ubar} : Set (OddQuot (npD X x))) =
        centralizer ({hS.ubar} : Set (OddQuot (npD X x))) :=
      Subgroup.eq_of_le_of_card_ge inf_le_right
        (le_of_eq (by rw [hcard, hS.card_fixed_bar]))
    have hu : hS.ubar ∈ E := by
      have h1 : hS.ubar ∈ E ⊓ centralizer ({hS.ubar} : Set (OddQuot (npD X x))) := by
        rw [hCE]
        exact hS.ubar_mem_centralizer
      exact h1.1
    have hall : ∀ E' : Subgroup (OddQuot (npD X x)), IsCompIn E' ⊤ → E' = E := by
      intro E' hE'
      by_contra hne
      refine (hS.comp_invariant hE').2 fun a ha => ?_
      rw [mem_centralizer_singleton_iff]
      exact hE'.commute_of_ne hE hne a ha _ hu
    have h1 : oddBar (npD X x) (npA X x s₀) ≤ E := by
      have h1 := hS.Abar_le_layer h15
      rwa [layerIn_eq_of_unique hE hall] at h1
    obtain ⟨e⟩ := hS.nonempty_Abar_equiv
    have hCle : centralizer ({hS.ubar} : Set (OddQuot (npD X x))) ≤ E := hCE ▸ inf_le_left
    have hcent : centralizer ({(⟨hS.ubar, hu⟩ : ↥E)} : Set ↥E) =
        (centralizer ({hS.ubar} : Set (OddQuot (npD X x)))).subgroupOf E :=
      centralizer_singleton_subgroupOf hu
    refine hNP.2 ↥E hE.isQuasisimple.1.commutator_eq_top ⟨hS.ubar, hu⟩ ?_ ?_ ?_
      ((oddBar (npD X x) (npA X x s₀)).subgroupOf E)
      ⟨(Subgroup.subgroupOfEquivOfLe h1).trans e⟩
    · rw [Subgroup.orderOf_mk]
      exact hS.orderOf_ubar
    · intro a ha b hb
      rw [hcent, Subgroup.mem_subgroupOf] at ha hb
      exact Subtype.ext (hS.fixed_bar_comm _ ha _ hb)
    · rw [hcent, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCle).toEquiv]
      exact hS.card_fixed_bar

theorem comp_unique (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀)
    {E₁ E₂ : Subgroup (OddQuot (npD X x))} (h₁ : IsCompIn E₁ ⊤) (h₂ : IsCompIn E₂ ⊤) :
    E₁ = E₂ := by
  by_contra hne
  obtain ⟨⟨e₁⟩, -⟩ := hS.comp_typeI hNP h15 h₁
  obtain ⟨⟨e₂⟩, -⟩ := hS.comp_typeI hNP h15 h₂
  have h16 := sixteen_le_card_centralizer_of_alt5_pair hS.ubar_mul_self
    (hS.ubar_conj_mem h₁) (hS.ubar_conj_mem h₂) (h₁.commute_of_ne h₂ hne) e₁ e₂
  rw [hS.card_fixed_bar] at h16
  omega

theorem exists_comp (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀) :
    ∃ E : Subgroup (OddQuot (npD X x)), IsCompIn E ⊤ := by
  by_contra h
  have hempty : {M : Subgroup (OddQuot (npD X x)) | IsCompIn M ⊤} = ∅ := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hM => h ⟨M, hM⟩
  have h1 := hS.Abar_le_layer h15
  rw [layerIn, hempty, sSup_empty, le_bot_iff] at h1
  have h2 := hS.card_Abar
  rw [h1, Subgroup.card_bot] at h2
  omega

theorem layer_eq (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀) :
    layerIn (⊤ : Subgroup (OddQuot (npD X x))) = oddBar (npD X x) (npA X x s₀) ∧
      Nonempty (↥(oddBar (npD X x) (npA X x s₀)) ≃* alternatingGroup (Fin 5)) ∧
      ∃ ebar ∈ oddBar (npD X x) (npA X x s₀), ebar * ebar = 1 ∧ ebar ≠ 1 ∧
        ∀ a ∈ oddBar (npD X x) (npA X x s₀), hS.ubar * a * hS.ubar⁻¹ = ebar * a * ebar⁻¹ := by
  obtain ⟨E, hE⟩ := hS.exists_comp h15
  have hlayer := layerIn_eq_of_unique hE fun E' hE' => hS.comp_unique hNP h15 hE' hE
  obtain ⟨⟨eE⟩, hcard4⟩ := hS.comp_typeI hNP h15 hE
  obtain ⟨eA⟩ := hS.nonempty_Abar_equiv
  have hAE : oddBar (npD X x) (npA X x s₀) ≤ E := hlayer ▸ hS.Abar_le_layer h15
  have hAE' : oddBar (npD X x) (npA X x s₀) = E :=
    eq_of_le_of_quasisimple_alt5 hE.isQuasisimple hAE eA eE
  subst hAE'
  have hfix : Nat.card {h : ↥(oddBar (npD X x) (npA X x s₀)) // hS.compAut hE h = h} = 4 := by
    have h1 := hS.card_fixedSubgroup_compAut hE
    rw [hcard4] at h1
    exact h1
  obtain ⟨c, hc2, hc1, hcα⟩ :=
    exists_inner_of_card_fixedPoints_eq_four eA (hS.compAut hE) (hS.compAut_compAut hE) hfix
  refine ⟨hlayer, ⟨eA⟩, (c : OddQuot (npD X x)), c.2, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hc2
  · intro h
    exact hc1 (Subtype.ext h)
  · intro a ha
    have h1 := congrArg Subtype.val (hcα ⟨a, ha⟩)
    rw [hS.coe_compAut] at h1
    simpa using h1

theorem isCompIn_Abar_top (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀) :
    IsCompIn (oddBar (npD X x) (npA X x s₀)) ⊤ := by
  obtain ⟨E, hE⟩ := hS.exists_comp h15
  have h1 := (hS.layer_eq hNP h15).1
  rw [layerIn_eq_of_unique hE fun E' hE' => hS.comp_unique hNP h15 hE' hE] at h1
  rw [← h1]
  exact hE

theorem normal_Abar (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀) :
    (oddBar (npD X x) (npA X x s₀)).Normal := by
  have hA := hS.isCompIn_Abar_top hNP h15
  refine ⟨fun a ha g => ?_⟩
  have hc := hA.map_conj (Subgroup.mem_top g)
  have heq : (oddBar (npD X x) (npA X x s₀)).map (MulAut.conj g).toMonoidHom =
      oddBar (npD X x) (npA X x s₀) := hS.comp_unique hNP h15 hc hA
  have h1 : g * a * g⁻¹ ∈
      (oddBar (npD X x) (npA X x s₀)).map (MulAut.conj g).toMonoidHom := ⟨a, ha, rfl⟩
  rwa [heq] at h1

theorem Dbar_eq (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀) :
    ∃ hbar : OddQuot (npD X x), orderOf hbar = 2 ∧
      center (OddQuot (npD X x)) = zpowers hbar ∧
      centralizer ((oddBar (npD X x) (npA X x s₀) : Subgroup (OddQuot (npD X x))) :
        Set (OddQuot (npD X x))) = zpowers hbar ∧
      oddBar (npD X x) (npA X x s₀) ⊔ zpowers hbar = ⊤ ∧
      oddBar (npD X x) (npA X x s₀) ⊓ zpowers hbar = ⊥ ∧
      centralizer ({hS.ubar} : Set (OddQuot (npD X x))) =
        (oddBar (npD X x) (npA X x s₀) ⊓ centralizer ({hS.ubar} : Set (OddQuot (npD X x)))) ⊔
          zpowers hbar ∧
      Nat.card ↥(oddBar (npD X x) (npA X x s₀) ⊓
        centralizer ({hS.ubar} : Set (OddQuot (npD X x)))) = 4 ∧
      (∀ y ∈ centralizer ({hS.ubar} : Set (OddQuot (npD X x))), y * y = 1) ∧
      ∃! y : ↥(npY X u x), oddProj (npD X x) ⟨y, npY_le_npD X u x y.2⟩ = hbar := by
  haveI := hS.normal_Abar hNP h15
  obtain ⟨-, ⟨eA⟩, ebar, hmem, hsq, hne, hconj⟩ := hS.layer_eq hNP h15
  obtain ⟨hbar, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_involution_of_normal_alt5
    (oddCore_oddQuot (npD X x)) eA hS.ubar_mul_self hmem hsq hne hconj hS.fixed_bar_comm
    hS.card_fixed_bar
  have hcen : hbar ∈ center (OddQuot (npD X x)) := by
    rw [h3]
    exact Subgroup.mem_zpowers hbar
  have hC : hbar ∈ centralizer ({hS.ubar} : Set (OddQuot (npD X x))) :=
    mem_centralizer_singleton_iff.2 (mem_center_iff.1 hcen hS.ubar).symm
  obtain ⟨y, hy⟩ := hS.fixedBarEquiv.surjective ⟨hbar, hC⟩
  refine ⟨hbar, h1, h3, h2, h4, h5, h6, h7, h8, y,
    (hS.coe_fixedBarEquiv y).symm.trans (congrArg Subtype.val hy), fun y' hy' => ?_⟩
  apply hS.fixedBarEquiv.injective
  rw [hy]
  exact Subtype.ext ((hS.coe_fixedBarEquiv y').trans hy')

theorem Y_exp_two (hNP : KDNP) (h15 : FS79Lemma15Sec G) (hS : NPSetting G X u x T₀ s₀) :
    ∀ y ∈ npY X u x, y * y = 1 := by
  intro y hy
  obtain ⟨-, -, -, -, -, -, -, -, hsq, -⟩ := hS.Dbar_eq hNP h15
  have h1 := hsq _ (hS.fixedBarEquiv ⟨y, hy⟩).2
  have h2 : hS.fixedBarEquiv (⟨y, hy⟩ * ⟨y, hy⟩) = hS.fixedBarEquiv 1 := by
    rw [map_one]
    exact Subtype.ext (by rw [map_mul, Subgroup.coe_mul]; exact h1)
  have h3 := hS.fixedBarEquiv.injective h2
  exact congrArg Subtype.val h3

end NPSetting

end CFSG.EvenSporadicStandard.M12Std.Rbc
