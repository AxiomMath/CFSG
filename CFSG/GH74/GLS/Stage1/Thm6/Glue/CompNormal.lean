module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Conv
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG
open scoped commutatorElement

theorem four_le_pRank_of_commuting_fours {X : Type} [Group X] [Finite X] {V W : Subgroup X}
    (hV4 : Nat.card V = 4) (hW4 : Nat.card W = 4) (hVsq : ∀ v ∈ V, v * v = 1)
    (hWsq : ∀ w ∈ W, w * w = 1) (hcomm : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v) (hd : V ⊓ W = ⊥) :
    4 ≤ CFSG.pRank 2 X := by
  let φ : ↥V × ↥W →* X :=
    MonoidHom.noncommCoprod V.subtype W.subtype (fun v w => hcomm v v.2 w w.2)
  have hφ : ∀ p : ↥V × ↥W, φ p = (p.1 : X) * (p.2 : X) := fun p => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨v, w⟩ h
    have h1 : (v : X) * (w : X) = 1 := h
    have hvw : (v : X) = ((w : X))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmem : (v : X) ∈ V ⊓ W :=
      ⟨v.2, by rw [hvw]; exact W.inv_mem w.2⟩
    rw [hd, Subgroup.mem_bot] at hmem
    have hw : (w : X) = 1 := by rw [hmem, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hw)
  have hcard : Nat.card φ.range = 2 ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hV4, hW4]
    norm_num
  have hsq : ∀ e ∈ φ.range, e * e = 1 := by
    rintro _ ⟨⟨v, w⟩, rfl⟩
    rw [hφ]
    have hvw : (v : X) * (w : X) = (w : X) * (v : X) := hcomm v v.2 w w.2
    calc (v : X) * w * ((v : X) * w) = v * (w * v) * w := by group
      _ = v * (v * w) * w := by rw [← hvw]
      _ = v * v * (w * w) := by group
      _ = 1 := by rw [hVsq v v.2, hWsq w w.2, mul_one]
  have hEA : CFSG.Open.IsElemAbelian 2 φ.range := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have hab := eq_inv_of_mul_eq_one_left (hsq _ (φ.range.mul_mem a.2 b.2))
      have ha := eq_inv_of_mul_eq_one_left (hsq _ a.2)
      have hb := eq_inv_of_mul_eq_one_left (hsq _ b.2)
      change (a : X) * b = b * a
      calc (a : X) * b = ((a : X) * b)⁻¹ := hab
        _ = (b : X)⁻¹ * (a : X)⁻¹ := mul_inv_rev _ _
        _ = b * a := by rw [← ha, ← hb]
    · rw [pow_two]
      exact hsq x hx
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank one_lt_two le_top hEA hcard

theorem normal_of_pRank_le_three {G : Type} [Group G] [Finite G] {x : G}
    (h3 : pRank 2 ↥(centralizer ({x} : Set G)) ≤ 3) {Kb : Subgroup (CentralizerBar x)}
    (hc : IsComponent Kb) (hcen : center ↥Kb = ⊥) : Kb.Normal := by
  refine ⟨fun n hn g => ?_⟩
  by_contra hg
  set L : Subgroup (CentralizerBar x) := Kb.map (MulAut.conj g).toMonoidHom with hLdef
  have hL : IsComponent L := LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hc
  have hne : Kb ≠ L := by
    intro h
    apply hg
    have : g * n * g⁻¹ ∈ L := ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rwa [← h] at this
  have hcom : ⁅Kb, L⁆ = ⊥ := (LocalCores.distinct_components_commute hc hL).resolve_left hne
  have hcomm : ∀ a : CentralizerBar x, a ∈ Kb → ∀ b : CentralizerBar x, b ∈ L → a * b = b * a := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ ⁅Kb, L⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [hcom, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have e : ↥Kb ≃* ↥L := Subgroup.equivMapOfInjective Kb (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  have hcenL : Nat.card ↥(center ↥L) = 1 := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, hcen, Subgroup.card_bot]
  have h2K : 2 ≤ pRank 2 ↥Kb :=
    LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hc.1
      (by rw [hcen, Subgroup.card_bot]; exact odd_one)
  have h2L : 2 ≤ pRank 2 ↥L :=
    LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hL.1
      (by rw [hcenL]; exact odd_one)
  obtain ⟨A, hAel, hA4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank h2K
  obtain ⟨B, hBel, hB4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank h2L
  set V : Subgroup (CentralizerBar x) := A.map Kb.subtype with hV
  set W : Subgroup (CentralizerBar x) := B.map L.subtype with hW
  have hV4 : Nat.card ↥V = 4 := by
    rw [hV, Subgroup.card_map_of_injective Kb.subtype_injective, hA4]
  have hW4 : Nat.card ↥W = 4 := by
    rw [hW, Subgroup.card_map_of_injective L.subtype_injective, hB4]
  have hVsq : ∀ v ∈ V, v * v = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h2 : a * a = 1 := by rw [← pow_two]; exact hAel.2 a ha
    exact congrArg Subtype.val h2
  have hWsq : ∀ w ∈ W, w * w = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    have h2 : b * b = 1 := by rw [← pow_two]; exact hBel.2 b hb
    exact congrArg Subtype.val h2
  have hVK : ∀ v ∈ V, v ∈ Kb := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hWL : ∀ w ∈ W, w ∈ L := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hVW : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v := fun v hv w hw => hcomm v (hVK v hv) w (hWL w hw)
  have hd : V ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzV, hzW⟩
    have hz1 : (⟨z, hVK z hzV⟩ : ↥Kb) ∈ center ↥Kb := by
      rw [Subgroup.mem_center_iff]
      intro g'
      exact Subtype.ext (hcomm g'.1 g'.2 z (hWL z hzW))
    rw [hcen, Subgroup.mem_bot] at hz1
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hz1)
  have h4 := four_le_pRank_of_commuting_fours hV4 hW4 hVsq hWsq hVW hd
  have hN : ¬ 2 ∣ Nat.card ↥(pPrimeCore 2 ↥(centralizer ({x} : Set G))) := fun h2 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥(centralizer ({x} : Set G)))) h2
  have hq : CFSG.pRank 2 (CentralizerBar x) = CFSG.pRank 2 ↥(centralizer ({x} : Set G)) :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hN
  omega

theorem center_eq_bot_of_isL2Model {K : Type} [Group K] (h : IsL2Model K) : center K = ⊥ := by
  obtain ⟨F, _, _, -, ⟨e⟩⟩ := h
  let e' : K ≃* CFSG.GorensteinWalter.PSL2 F := e.trans (IVK.L2.equivPSL F)
  have hP : center (CFSG.GorensteinWalter.PSL2 F) = ⊥ := CFSG.GorensteinWalter.psl2_center_eq_bot F
  rw [eq_bot_iff]
  intro z hz
  have hz' : e' z ∈ center (CFSG.GorensteinWalter.PSL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := e'.surjective g
    have hk := Subgroup.mem_center_iff.1 hz k
    rw [← map_mul, ← map_mul, hk]
  rw [hP, Subgroup.mem_bot] at hz'
  exact Subgroup.mem_bot.2 (e'.injective (by rw [hz', map_one]))

theorem center_eq_bot_of_isA7Model {K : Type} [Group K] (h : IsA7Model K) : center K = ⊥ := by
  obtain ⟨e⟩ := h
  have hP : center (alternatingGroup (Fin 7)) = ⊥ := alternatingGroup.center_eq_bot (by simp)
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := e.surjective g
    have hk := Subgroup.mem_center_iff.1 hz k
    rw [← map_mul, ← map_mul, hk]
  rw [hP, Subgroup.mem_bot] at hz'
  exact Subgroup.mem_bot.2 (e.injective (by rw [hz', map_one]))

theorem normal_of_isL2Model {G : Type} [Group G] [Finite G] {x : G}
    (h3 : pRank 2 ↥(centralizer ({x} : Set G)) ≤ 3) {Kb : Subgroup (CentralizerBar x)}
    (hc : IsComponent Kb) (hm : IsL2Model ↥Kb) : Kb.Normal :=
  normal_of_pRank_le_three h3 hc (center_eq_bot_of_isL2Model hm)

theorem normal_of_isA7Model {G : Type} [Group G] [Finite G] {x : G}
    (h3 : pRank 2 ↥(centralizer ({x} : Set G)) ≤ 3) {Kb : Subgroup (CentralizerBar x)}
    (hc : IsComponent Kb) (hm : IsA7Model ↥Kb) : Kb.Normal :=
  normal_of_pRank_le_three h3 hc (center_eq_bot_of_isA7Model hm)

theorem normal_of_hasL2Model {G : Type} [Group G] [Finite G] {x : G}
    (h3 : pRank 2 ↥(centralizer ({x} : Set G)) ≤ 3) {Kb : Subgroup (CentralizerBar x)}
    (hc : IsComponent Kb) (hm : HasL2Model ↥Kb (fun q => Odd q ∧ 3 < q)) : Kb.Normal :=
  normal_of_isL2Model h3 hc (isL2Model_of_hasL2Model hm)

end CFSG.GH74.GLS.Stage1.Thm6.Glue
