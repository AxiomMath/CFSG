module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxRank
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxFaith
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxBridge
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxBridgeB
public import CFSG.HardMathSupport.Solomon.Coordinator.I713OuterDefs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Basic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem not_dvd_card_qt {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hY : ¬ p ∣ Nat.card Y)
    (K : Subgroup (Qt Y)) : ¬ p ∣ Nat.card K := by
  intro h
  apply hY
  refine (h.trans (Subgroup.card_subgroup_dvd_card K)).trans ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 2 Y)]
  exact Dvd.intro _ rfl

theorem le_of_pow_le_mul {p m k : ℕ} (hp : 3 ≤ p) (hm : 4 ≤ m) (h : p ^ m ≤ p * k) :
    m + 1 ≤ k ∧ 5 ≤ k := by
  have key : ∀ n : ℕ, 3 ≤ n → n + 2 ≤ 3 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih => rw [pow_succ]; omega
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h1 : p ^ n ≤ k := by
    rw [pow_succ'] at h
    exact Nat.le_of_mul_le_mul_left h (by omega)
  have h2 : 3 ^ n ≤ p ^ n := Nat.pow_le_pow_left hp n
  have h3 := key n (by omega)
  omega

theorem lemma84 (i7 : Coordinator.I_7_13_1_OuterPPrime) (i10 : Input10_20_3) (iodd : InputOddTwoLocal)
    (hS : GLStanding G m p) {B M₀ : Subgroup G} (hB : IsBOneMax p B)
    (hM : IsPreUniquenessSubgroup p B M₀)
    (h82 : ∀ N : Subgroup G, IsTwoLocal N → B ≤ N → ∀ J : Subgroup G,
      GLAPComponent 2 (GLAPPrimeCoreOf p M₀) J →
        ¬ J ≤ (N ⊓ GLAPPrimeCoreOf p M₀) ⊔ GLAPPrimeCoreOf 2 (GLAPPrimeCoreOf p M₀))
    (h83 : ∀ b ∈ B, (∀ y ∈ layerPreimage (GLAPPrimeCoreOf p M₀),
      b * y * b⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 2 (GLAPPrimeCoreOf p M₀)) → b = 1) :
    GLAPLayer 2 (GLAPPrimeCoreOf p M₀) = ⊥ := by
  classical
  by_contra hne
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set X := GLAPPrimeCoreOf p M₀ with hXdef
  have hBM : B ≤ M₀ := hM.le hS hB
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := hBM.trans (le_normalizer_glaPPrimeCoreOf p M₀)
  have hXp : ¬ p ∣ Nat.card X := not_dvd_card_glaPPrimeCoreOf hp M₀
  have hXtop : X ≠ ⊤ := by
    intro h
    apply hXp
    rw [h, Subgroup.card_top]
    exact hS.beta.2.2.1
  obtain ⟨K₀, hK₀⟩ := exists_isComponentOf_of_glaPLayer_ne_bot hne
  have hBel : IsElemAbelian p B := hB.1.1
  have := hBel.1
  have hΓ : IsPGroup p ↥B := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hBel.2 g g.2)⟩
  have hcomm : ∀ a b : ↥B, a * b = b * a := fun a b => mul_comm' a b
  have hexp : ∀ a : ↥B, a ^ p = 1 := fun a => Subtype.ext (by simpa using hBel.2 a a.2)
  have hS2 := hS2_of_h82 hBX h82
  have hFaith := hFaith_of_h83 hBX h83
  have hOut : ∀ K : Subgroup (Qt ↥X), IsComponentOf K ⊤ → IsSimpleGroup ↥K →
      (∃ a b : ↥K, a * b ≠ b * a) →
        CFSG.Open.pRank p (⊤ : Subgroup
          (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K)) ≤ 1 := by
    intro K _ hKs hKn
    have hcat := isCatalogGroup_of_component hS.kProper hXtop hKs hKn
    exact i7 p hp hp2 ↥K hKs hKn hcat (not_dvd_card_qt hXp K)
  obtain ⟨hsimple, hnab, hcard, hinv, ⟨e1⟩, ⟨e2⟩, hcent, hL₂L, hL₂n⟩ :=
    structure_theorem hΓ hcomm hexp (actB hBX) hXp hS2 hFaith hOut hK₀
  have hcat := isCatalogGroup_of_component hS.kProper hXtop hsimple hnab
  have hK₀p : ¬ p ∣ Nat.card ↥K₀ := not_dvd_card_qt hXp K₀
  set ℒ := orbitSet (actB hBX) K₀ with hℒ
  set k := Nat.card ↥ℒ with hkdef
  set Lb : Subgroup (Qt ↥X) := ⨆ K ∈ ℒ, K with hLb
  set Lb₂ : Subgroup (Qt ↥X) := ⨆ K ∈ ℒ \ {K₀}, K with hLb₂
  have hBcard : Nat.card ↥B = p ^ m := hS.card_eq hB
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨hk1, hk5⟩ := le_of_pow_le_mul hp3 hS.four_le (hBcard ▸ hcard)
  set O : Subgroup G := GLAPPrimeCoreOf 2 X with hO
  set L : Subgroup G := (preimQ Lb).map X.subtype with hL
  set L₂ : Subgroup G := (preimQ Lb₂).map X.subtype with hL₂
  have hLX : L ≤ X := Subgroup.map_subtype_le _
  have hL₂X : L₂ ≤ X := Subgroup.map_subtype_le _
  have hL₂L' : L₂ ≤ L := Subgroup.map_mono (Subgroup.comap_mono hL₂L)
  have hOL₂ : O ≤ L₂ := Subgroup.map_mono (ker_le_preimQ Lb₂)
  have hOL : O ≤ L := hOL₂.trans hL₂L'
  have hLinv : ∀ γ : ↥B, (preimQ Lb).map (actB hBX γ).toMonoidHom = preimQ Lb :=
    fun γ => map_preimQ (actB hBX) γ (hinv γ)
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := le_normalizer_map_subtype hBX hLinv
  have hL₂n' : (L₂.subgroupOf L).Normal :=
    normal_subgroupOf_map_subtype (Subgroup.comap_mono hL₂L) (normal_subgroupOf_preimQ hL₂L hL₂n)
  have hnL : (O.subgroupOf L).Normal := normal_subgroupOf_glaPPrimeCoreOf X hLX
  have hnL₂ : (O.subgroupOf L₂).Normal := normal_subgroupOf_glaPPrimeCoreOf X hL₂X
  obtain ⟨e3⟩ := exists_mulEquiv_quot_preimQ X Lb
  obtain ⟨e4⟩ := exists_mulEquiv_quot_preimQ X Lb₂
  obtain ⟨r, hr, hr2, hr1⟩ := iodd ↥K₀ hsimple hnab hcat
  have hi := i10 ↥L (O.subgroupOf L) ↥K₀ k hsimple hnab ⟨e3.trans e1⟩ r hr hr2
  have hi' := i10 ↥L₂ (O.subgroupOf L₂) ↥K₀ (k - 1) hsimple hnab ⟨e4.trans e2⟩ r hr hr2
  obtain ⟨H, hH2, hBH, hcover⟩ : ∃ H : Subgroup G, IsTwoLocal H ∧ B ≤ H ∧
      ∀ j ∈ X, (∀ t ∈ L₂, j * t * j⁻¹ * t⁻¹ ∈ O) → j ∈ (H ⊓ X) ⊔ O := by
    obtain ⟨H₁, hH₁, hrk⟩ := exists_isTwoLocal_pRank_pos hr.one_lt hr1
    have hr1' : 1 ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥K₀) :=
      hrk.trans (CFSG.SectionRank.pRank_mono hr.one_lt le_top)
    have hrd : r ∣ Nat.card ↥K₀ := by
      have := dvd_card_of_one_le_pRank hr hr1'
      rwa [Subgroup.card_top] at this
    have hrp : r ≠ p := by
      rintro rfl
      exact hK₀p hrd
    exact exists_twoLocal_covering hS (B := B) (X := X) (L := L) (L₂ := L₂) hΓ hBL hXp hLX hL₂L'
      hOL₂ hL₂n' hr hr2 hrp (hk1.trans (hi.1 hr1)) (by have := hi.2 hr1'; omega)
      (by have := hi'.2 hr1'; omega)
  obtain ⟨J, hJ, hJK⟩ := exists_glaPComponent_barX_eq (p := 2) X hK₀
  refine h82 H hH2 hBH J hJ fun j hj => hcover j (hJ.1 hj) fun t ht => ?_
  obtain ⟨htX, htL⟩ := mem_map_preimQ_iff.1 ht
  refine commutator_mem_glaPPrimeCoreOf_of_commute (hJ.1 hj) htX ?_
  have h1 : mkQ ↥X ⟨j, hJ.1 hj⟩ ∈ K₀ := hJK ▸ mkQ_mem_barX hJ.1 hj
  exact ((Subgroup.mem_centralizer_iff.1 (hcent h1)) _ htL).symm

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
