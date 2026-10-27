module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyCoreGen
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultThreeAux
public import CFSG.Sporadic.Recognition.LyonsAS44Cert
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyCoreMain

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore

open Subgroup Equiv Equiv.Perm CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.Sporadic.Recognition.LyonsSims

theorem eq_bot_of_conj_core {Y : Type} [Group Y] {g g' c : Y} (hc : c * g * c⁻¹ = g')
    (H : ∀ W' : Subgroup Y, W' ≤ centralizer ({g'} : Set Y) →
      (∀ d : Y, d * g' = g' * d → ∀ w ∈ W', d * w * d⁻¹ ∈ W') →
        Nat.Coprime (Nat.card ↥W') 3 → W' = ⊥)
    {W : Subgroup Y} (hWC : W ≤ centralizer ({g} : Set Y))
    (hWn : ∀ d : Y, d * g = g * d → ∀ w ∈ W, d * w * d⁻¹ ∈ W)
    (hcop : Nat.Coprime (Nat.card ↥W) 3) : W = ⊥ := by
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have key := H (W.map (MulAut.conj c).toMonoidHom) ?_ ?_ ?_
  · exact Subgroup.map_injective hinj (by rw [key, Subgroup.map_bot])
  · rintro _ ⟨w, hw, rfl⟩
    have hw' := mem_centralizer_singleton_iff.mp (hWC hw)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hc]
    calc c * w * c⁻¹ * (c * g * c⁻¹) = c * (w * g) * c⁻¹ := by group
      _ = c * (g * w) * c⁻¹ := by rw [hw']
      _ = c * g * c⁻¹ * (c * w * c⁻¹) := by group
  · intro d hd w' hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    have hd' : c⁻¹ * d * c * g = g * (c⁻¹ * d * c) := by
      rw [← hc] at hd
      calc c⁻¹ * d * c * g = c⁻¹ * (d * (c * g * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * g * c⁻¹) * d) * c := by rw [hd]
        _ = g * (c⁻¹ * d * c) := by group
    refine ⟨(c⁻¹ * d * c) * w * (c⁻¹ * d * c)⁻¹, hWn _ hd' w hw, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [Subgroup.card_map_of_injective hinj]
    exact hcop

theorem three_a_core
    {Y : Type} [Group Y] [Finite Y] {t : Y}
    {ρ : ↥(centralizer ({t} : Set Y)) →* Perm (Fin 11)}
    {x₁ x₂ x₃ : ↥(centralizer ({t} : Set Y))} (D : LyData Y t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∀ W' : Subgroup Y, W' ≤ centralizer ({(x₁ : Y)} : Set Y) →
      (∀ d : Y, d * (x₁ : Y) = (x₁ : Y) * d → ∀ w ∈ W', d * w * d⁻¹ ∈ W') →
        Nat.Coprime (Nat.card ↥W') 3 → W' = ⊥ := by
  intro W' hWC hWn hcop
  have hperf := D.isPerfect_centralizer S
  have hcen := D.center_centralizer S
  have hc3 := D.card_center_centralizer S
  obtain ⟨eM⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  have e : ↥(centralizer ({(x₁ : Y)} : Set Y)) ⧸ center ↥(centralizer ({(x₁ : Y)} : Set Y)) ≃*
      NativeSporadic.McL := (QuotientGroup.quotientMulEquivOfEq hcen).trans eM
  have hsimple : IsSimpleGroup (↥(centralizer ({(x₁ : Y)} : Set Y)) ⧸
      center ↥(centralizer ({(x₁ : Y)} : Set Y))) :=
    @MulEquiv.isSimpleGroup _ _ NativeSporadic.McL _ CFSG.Sporadic.McL.isSimpleGroup_McL e
  have hnab : ∃ a b : ↥(centralizer ({(x₁ : Y)} : Set Y)) ⧸
      center ↥(centralizer ({(x₁ : Y)} : Set Y)), a * b ≠ b * a :=
    LyMult.exists_noncomm_of_simple
      (by rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL]; norm_num)
  have hquasi : IsQuasisimple ↥(centralizer ({(x₁ : Y)} : Set Y)) := ⟨hperf, hsimple, hnab⟩
  have hZp : IsPGroup 3 (center ↥(centralizer ({(x₁ : Y)} : Set Y))) :=
    IsPGroup.of_card (n := 1) (by rw [hc3, pow_one])
  have h3 : 3 ∣ Nat.card (center ↥(centralizer ({(x₁ : Y)} : Set Y))) := by rw [hc3]
  have hcard : Nat.card (W'.subgroupOf (centralizer ({(x₁ : Y)} : Set Y))) = Nat.card W' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv
  have hbot := eq_bot_of_normal_coprime hquasi hZp h3
    (W := W'.subgroupOf (centralizer ({(x₁ : Y)} : Set Y)))
    (fun c w hw => by
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      exact hWn _ (mem_centralizer_singleton_iff.mp c.2) _ hw)
    (by rw [hcard]; exact hcop)
  rw [hbot, Subgroup.card_bot] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard.symm

@[expose] def LyThreeBCore : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], NativeSporadic.IsSporadic Y .Ly →
    ∀ (t : Y) (ρ : ↥(centralizer ({t} : Set Y)) →* Perm (Fin 11)), LyData Y t ρ →
      ∀ x₁ x₂ x₃ : ↥(centralizer ({t} : Set Y)), LyStd ρ x₁ x₂ x₃ →
        ∀ W : Subgroup Y, W ≤ centralizer ({(x₁ : Y) * (x₂ : Y)} : Set Y) →
          (∀ c : Y, c * ((x₁ : Y) * (x₂ : Y)) = ((x₁ : Y) * (x₂ : Y)) * c →
            ∀ w ∈ W, c * w * c⁻¹ ∈ W) →
            Nat.Coprime (Nat.card ↥W) 3 → W = ⊥

theorem lyCoreAt_three_of_threeB
    (h3B : LyThreeBCore) : LyCoreAt 3 := by
  intro Y _ _ hLy V hV hVc
  have := hV
  obtain ⟨eT⟩ := hLy
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly ⟨eT⟩)
  obtain ⟨x₁, x₂, x₃, S⟩ := D.exists_lyStd
  have hne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hVc
    omega
  obtain ⟨⟨g, hgV⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hg3 : g ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian g hgV
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1'
  refine ⟨g, hgV, hg1', fun W hWC hWn hcop => ?_⟩
  rcases (lemma45_classes_of_certificate D S).1 g hord with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    exact eq_bot_of_conj_core hc (three_a_core D S) hWC hWn hcop
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    exact eq_bot_of_conj_core hc (h3B Y ⟨eT⟩ t ρ D x₁ x₂ x₃ S) hWC hWn hcop

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore
