module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Section
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFFamilies

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_isBestOffender_le {H A : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : A ≠ ⊥)
    (hAel : IsElemAbelian2 A) (hAoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    ∃ B : Subgroup (MulAut V), B ≤ A ∧ Family.IsBestOffender H B := by
  classical
  have hex : ∃ n, ∃ B : Subgroup (MulAut V), B ≤ A ∧ B ≠ ⊥ ∧
      Nat.card V ≤ Nat.card B * Nat.card (fixV B) ∧ Nat.card B = n :=
    ⟨_, A, le_rfl, hA, hAoff, rfl⟩
  obtain ⟨B, hBA, hBne, hBoff, hBn⟩ := Nat.find_spec hex
  refine ⟨B, hBA, hBA.trans hAH, hBne,
    ⟨fun a ha b hb => hAel.1 a (hBA ha) b (hBA hb), fun a ha => hAel.2 a (hBA ha)⟩, hBoff, ?_⟩
  intro C hCB hCne hCB'
  by_contra hcon
  have hmin := Nat.find_min' hex ⟨C, hCB.trans hBA, hCne, hBoff.trans (not_lt.1 hcon), rfl⟩
  rw [← hBn] at hmin
  have hlt : Nat.card C < Nat.card B := Subgroup.card_lt_of_lt (lt_of_le_of_ne hCB hCB')
  omega

theorem commutator_ne_bot_of_elemAbelian {H L B : Subgroup (MulAut V)}
    (hLF : L = quasithinGenFitting H) (hO2 : CFSG.pCore 2 ↥H = ⊥) (hBH : B ≤ H) (hBne : B ≠ ⊥)
    (hBel : IsElemAbelian2 B) :
    ⁅L, B⁆ ≠ ⊥ := by
  intro hc
  have hLH : L ≤ H := hLF ▸ quasithinGenFitting_le H
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting H
  have hBC : B ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
    rw [Subgroup.commutator_comm] at hc
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
  have hBL : B ≤ L := by
    have h1 := centralizer_quasithinGenFitting_le H
    rw [← hLF] at h1
    exact fun b hb => h1 ⟨hBH hb, hBC hb⟩
  let N : Subgroup (MulAut V) :=
    { carrier := {z | z ∈ L ∧ z ∈ Subgroup.centralizer (L : Set (MulAut V)) ∧ z ^ 2 = 1}
      one_mem' := ⟨L.one_mem, Subgroup.one_mem _, one_pow 2⟩
      mul_mem' := by
        rintro a b ⟨haL, haC, ha2⟩ ⟨hbL, hbC, hb2⟩
        refine ⟨L.mul_mem haL hbL, Subgroup.mul_mem _ haC hbC, ?_⟩
        have hab : Commute a b := (Subgroup.mem_centralizer_iff.1 haC b hbL).symm
        rw [hab.mul_pow, ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨haL, haC, ha2⟩
        exact ⟨L.inv_mem haL, Subgroup.inv_mem _ haC, by rw [inv_pow, ha2, inv_one]⟩ }
  have hNn : (N.subgroupOf H).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnL, hnC, hn2⟩ := hn
    have hg := hHN g.2
    have hg' := hHN (H.inv_mem g.2)
    refine ⟨?_, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hg _).1 hnL
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : (g : MulAut V)⁻¹ * l * ((g : MulAut V)⁻¹)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 hg' l).1 hl
      rw [inv_inv] at hl'
      have hc := Subgroup.mem_centralizer_iff.1 hnC _ hl'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc l * ((g : MulAut V) * (n : MulAut V) * (g : MulAut V)⁻¹)
          = (g : MulAut V) * (((g : MulAut V)⁻¹ * l * (g : MulAut V)) * (n : MulAut V)) *
              (g : MulAut V)⁻¹ := by group
        _ = (g : MulAut V) * ((n : MulAut V) * ((g : MulAut V)⁻¹ * l * (g : MulAut V))) *
              (g : MulAut V)⁻¹ := by rw [hc]
        _ = (g : MulAut V) * (n : MulAut V) * (g : MulAut V)⁻¹ * l := by group
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [conj_pow, hn2, mul_one, mul_inv_cancel]
  have hNp : IsPGroup 2 ↥(N.subgroupOf H) := fun x => ⟨1, by
    have hx : ((x : ↥H) : MulAut V) ^ 2 = 1 := (Subgroup.mem_subgroupOf.1 x.2).2.2
    apply Subtype.ext
    apply Subtype.ext
    simpa using hx⟩
  have hNle : N.subgroupOf H ≤ CFSG.pCore 2 ↥H := le_sSup ⟨hNn, hNp⟩
  rw [hO2] at hNle
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
  have hbN : (⟨b, hBH hb⟩ : ↥H) ∈ N.subgroupOf H :=
    Subgroup.mem_subgroupOf.2 ⟨hBL hb, hBC hb, hBel.2 b hb⟩
  have hb' := hNle hbN
  rw [Subgroup.mem_bot] at hb'
  have hb'' : b = 1 := congrArg Subtype.val hb'
  exact hb1 (Subtype.ext hb'')

theorem noFFModule_of_noIrrFFOffender {Y : Type} [Group Y] (h : NoIrrFFOffender Y) :
    NoFFModule Y := by
  intro V _ _ hV H L hhyp ⟨e⟩ hFF
  obtain ⟨hLF, hLq, hO2, -⟩ := hhyp
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨A, hAH, hAne, hAel, hAoff⟩ := hFF
  obtain ⟨B, -, hB⟩ := exists_isBestOffender_le hAH hAne hAel hAoff
  have hLH : L ≤ H := hLF ▸ quasithinGenFitting_le H
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting H
  have hLcomp : Family.IsComp L H :=
    ⟨hLH, IsSubnormal.step hLH ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN)
      (IsSubnormal.refl H), ⟨hLq.1.commutator_eq_top, hLq.2.1⟩⟩
  have hLB : ⁅L, B⁆ ≠ ⊥ := commutator_ne_bot_of_elemAbelian hLF hO2 hB.1 hB.2.1 hB.2.2.1
  obtain ⟨hBN, -, ⟨sec⟩⟩ := Layer.Actor.irreducibleSectionProp V hV' H L B hLcomp hB hLB
  set ρ : ↥L →* MulAut sec.W := sec.τW.comp (Subgroup.inclusion le_sup_left) with hρ
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hφ : ∃ k, ρ.rangeRestrict k ≠ 1 := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 sec.lbar_ne_bot
    obtain ⟨k, hk⟩ := hsurj a
    exact ⟨k, hk ▸ ha⟩
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hLq hφ
  let eL := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hLq hsurj hker
  have hlt := h sec.W (Meierfrankenfeld.GeneralFF.irrSection_sq hV' sec) ρ.range
    (sec.τW.comp (Subgroup.inclusion le_sup_right)).range sec.lbar_quasisimple
    (Meierfrankenfeld.GeneralFF.irrSection_isIrrOn sec) ⟨eL.symm.trans e⟩
    (Meierfrankenfeld.GeneralFF.irrSection_range_le_normalizer sec hBN) sec.abar_ne_bot
    sec.abar_elem sec.abar_quadratic
  exact absurd sec.abar_offender (not_le.2 hlt)

end CFSG.HardMathSupport.Cooperstein.Coordinator
