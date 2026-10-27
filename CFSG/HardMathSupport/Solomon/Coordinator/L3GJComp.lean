module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3GJLift

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

theorem layer_of_fixData' {Y : Type} [Group Y] [Finite Y] {α : MulAut Y} (h : FixData Y α) :
    ∃ S : Subgroup Y, (∀ J : Subgroup Y, GLAPComponent 3 (fixSub α) J ↔ J = S) ∧
      GLAPPrimeCore 3 ↥S = ⊥ ∧ 3 ∣ Nat.card ↥S := by
  obtain ⟨S, hSF, hcomm, hpow, hqS, -, hz3, h3d, -, -, -⟩ := h
  have hO := glaPPrimeCore_eq_bot_of_quasisimple hqS hz3 h3d
  obtain ⟨-, comp, -⟩ := layer_of_normal_quasisimple hSF hcomm hpow hqS hO
  exact ⟨S, comp, hO, h3d⟩

theorem exists_layer_data {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (hL : GLAPComponent 3 X L) (hty : IsExtremalType (barOf 3 L)) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (hfld : IsFieldAutThree (barAut 3 L ⟨x, hxN⟩)) :
    ∃ J₁ : Subgroup ↥L,
      GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) = J₁.map L.subtype ∧
      GLAPComponent 3 ((L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf L) J₁ ∧
      GLAPComponent 3 (fixSub (barAut 3 L ⟨x, hxN⟩))
        (J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) ∧
      GLAPPrimeCore 3 ↥(J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) = ⊥ ∧
      3 ∣ Nat.card ↥(J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hq := isQuasisimple_quotient_of_glaPComponent hL
  have hfd := fixData_of_type hq (Or.inl hty) (barAut_pow_three hxN hx3) hfld
  obtain ⟨S₀, comp, hO, h3d⟩ := layer_of_fixData' hfd
  obtain ⟨J₁, hJ₁, hJ₁S⟩ := exists_comp_of_fixSub hxN hx3 ((comp S₀).2 rfl)
  have hSc := comp_map_fixSub hxN hx3 hJ₁
  subst hJ₁S
  have hker := coprime_ker_mk L ((L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf L)
  have huniq : ∀ K₁ : Subgroup ↥L,
      GLAPComponent 3 ((L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf L) K₁ → K₁ = J₁ := by
    intro K₁ hK₁
    have himg : K₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) =
        J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) :=
      (comp _).1 (comp_map_fixSub hxN hx3 hK₁)
    have hb₁ := lcEquiv_barX hp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) _ hker hK₁.1
    have hb₂ := lcEquiv_barX hp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) _ hker hJ₁.1
    have hbar : barX 3 ((L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf L) K₁ =
        barX 3 ((L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf L) J₁ := by
      apply Subgroup.map_injective (lcEquiv hp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) _ hker).injective
      show (barX 3 _ K₁).map (lcMonoidHom hp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) _ hker) =
        (barX 3 _ J₁).map (lcMonoidHom hp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) _ hker)
      rw [hb₁, hb₂, himg]
    exact glaPComponent_uniqueAux hK₁ hJ₁ hbar
  refine ⟨J₁, ?_, hJ₁, hSc, hO, h3d⟩
  apply le_antisymm
  · refine sSup_le fun K hK => ?_
    obtain ⟨K₁, hK₁, rfl⟩ := exists_comp_subgroupOf
      (inf_le_left : L ⊓ Subgroup.centralizer ({x} : Set G) ≤ L) hK
    rw [huniq K₁ hK₁]
  · exact le_sSup (comp_map_subgroupOf (inf_le_left : L ⊓ Subgroup.centralizer ({x} : Set G) ≤ L) hJ₁)

theorem layer_lift_core {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (hL : GLAPComponent 3 X L) {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : x ^ 3 = 1) (hfld : IsFieldAutThree (barAut 3 L ⟨x, hxN⟩)) {J₁ : Subgroup ↥L}
    (hS : GLAPComponent 3 (fixSub (barAut 3 L ⟨x, hxN⟩))
      (J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))))
    (hO : GLAPPrimeCore 3 ↥(J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) = ⊥)
    (j : ↥L) (hj : j ∈ J₁) (hj3 : (j : G) ^ 3 = 1) (hj1 : (j : G) ≠ 1)
    (hlift : HasOrderThreeLift (barOf 3 L) (QuotientGroup.mk j)) :
    HasOrderThreeLift (barOf 3 (J₁.map L.subtype))
      (QuotientGroup.mk (⟨(j : G), ⟨j, hj, rfl⟩⟩ : ↥(J₁.map L.subtype))) := by
  have hq := isQuasisimple_quotient_of_glaPComponent hL
  have hsS : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) j ∈
      J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) := ⟨j, hj, rfl⟩
  have hs1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) j ≠ 1 := by
    intro h
    exact hj1 (eq_one_of_mem_core j.2 hj3 ((QuotientGroup.eq_one_iff j).1 h))
  have h1 := hasOrderThreeLift_of_comp_fixSub hq (barAut_pow_three hxN hx3) hfld hS hO hsS hs1 hlift
  have h2 := hasOrderThreeLift_of_mulEquiv (liftEquiv J₁).symm h1
  have e : (liftEquiv J₁).symm (QuotientGroup.mk
      (⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) j, hsS⟩ :
        ↥(J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))))) =
      QuotientGroup.mk (⟨(j : G), ⟨j, hj, rfl⟩⟩ : ↥(J₁.map L.subtype)) := by
    rw [MulEquiv.symm_apply_eq]
    exact (liftEquiv_apply J₁ j hj).symm
  rwa [e] at h2

theorem three_dvd_card_layer {G : Type} [Group G] [Finite G] {L : Subgroup G} {J₁ : Subgroup ↥L}
    (hO : GLAPPrimeCore 3 ↥(J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) = ⊥)
    (h3d : 3 ∣ Nat.card ↥(J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)))) :
    3 ∣ Nat.card ↥(J₁.map L.subtype) := by
  have h1 : Nat.card (barOf 3 (J₁.map L.subtype)) =
      Nat.card ↥(J₁.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) := by
    rw [Nat.card_congr (liftEquiv J₁).toEquiv, Nat.card_congr (barEquivOfCore hO).toEquiv.symm]
  have h2 : Nat.card (barOf 3 (J₁.map L.subtype)) ∣ Nat.card ↥(J₁.map L.subtype) :=
    Subgroup.card_quotient_dvd_card _
  have h3 : 3 ∣ Nat.card (barOf 3 (J₁.map L.subtype)) := by
    rw [h1]
    exact h3d
  exact h3.trans h2

end CFSG.HardMathSupport.Solomon.Coordinator
