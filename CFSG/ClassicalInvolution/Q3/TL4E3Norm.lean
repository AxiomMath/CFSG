module

public import CFSG.ClassicalInvolution.Q3.TL4E3Plus
import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.Blueprint
open scoped commutatorElement

theorem acts3_of_good {Y : Type} [Group Y] {R : Subgroup Y} {t : Y}
    (h : GoodThreeElement R t) : TightActs3 R t := by
  obtain ⟨x, k, hx, hx3, hxR, -⟩ := h
  exact ⟨x, k, hx, hx3, hxR⟩

theorem center_eq_bot_of_isSimpleGroup {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hQ
    have hb : b ∈ Subgroup.center Q := h ▸ Subgroup.mem_top b
    exact absurd (Subgroup.mem_center_iff.mp hb a) hab

theorem exists_ne_comm_of_not_prime {Q : Type} [Group Q] [IsSimpleGroup Q]
    (h : ¬ (Nat.card Q).Prime) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have : IsMulCommutative Q := ⟨⟨hc⟩⟩
  exact h (Group.is_simple_iff_prime_card.mp inferInstance)

theorem card_of_lieModel_psp_three_two_one {X : Type} [Group X] (h : LieModel X .PSp 3 2 1) :
    Nat.card X = 1451520 :=
  CFSG.Blueprint.LieModel.card_psp_three_two h

theorem card_of_lieModel_pomegaPlus_four_two_one {X : Type} [Group X]
    (h : LieModel X .POmegaPlus 4 2 1) : Nat.card X = 174182400 := by
  rcases h with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl]
    decide
  all_goals exact absurd h0 (by norm_num)

section Member

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem ker_eq_center_of_datum (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hE2 : ¬ TightInO2 t) {Q : Type} [Group Q] (hQ : Subgroup.center Q = ⊥) (f : Y →* Q)
    (hf : Function.Surjective f) (hk : IsPGroup 2 ↥f.ker) : f.ker = Subgroup.center Y := by
  apply le_antisymm
  · exact hd.le_center_of_normal_two hc (MonoidHom.normal_ker f) hk
      fun h => hE2 ⟨_, MonoidHom.normal_ker f, hk, h⟩
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hfx : f x ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := hf q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
    rw [hQ, Subgroup.mem_bot] at hfx
    exact hfx

theorem nonempty_mulEquiv_of_datum (hd : TightDatum R S t)
    (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t) {Q : Type} [Group Q]
    (hQ : Subgroup.center Q = ⊥) (f : Y →* Q) (hf : Function.Surjective f)
    (hk : IsPGroup 2 ↥f.ker) : Nonempty (Y ⧸ Subgroup.center Y ≃* Q) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (ker_eq_center_of_datum hd hc hE2 hQ f hf hk).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end Member

namespace E3

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem exists_secCls (hd : TightDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) :
    ∃ Sq : Sylow 2 ↥(secR R u), TightDatum (secR R u) Sq (secT htu ht) ∧
      TightCls (SecQ R u) (secR R u) Sq (secT htu ht) := by
  obtain ⟨-, hu2, hut, -, huK, -⟩ := hd.edge_involution hJ hu
  have hcomm : ∀ r ∈ R, ⁅u, r⁆ ∈ oddCoreImg R := (hd.act_eq_one_iff hut).mp huK
  have huN : u ∈ Subgroup.normalizer (R : Set Y) := hd.le_normalizer hut
  have huC : u ∈ centralizerModOdd ⊤ R :=
    ⟨Subgroup.mem_top u, huN, mem_normalizer_oddCore_of_mem_normalizer huN, hcomm⟩
  obtain ⟨S', hS'⟩ := hd.exists_sylow_le_centralizer
    (Balance.isPGroup_zpowers_of_mul_self_eq_one hu2) (Subgroup.zpowers_le.mpr huC)
  have hS'u : (S' : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({u} : Set Y) :=
    hS'.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers u)))
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := (hd.ofSylow S').restrict hS'u
  have hq8' : Nonempty (↥(S₁ : Subgroup (R.subgroupOf (Subgroup.centralizer ({u} : Set Y)))) ≃*
      QuaternionGroup 2) := ⟨e₁.trans ((Sylow.equiv S' S).trans hq8.some)⟩
  obtain ⟨_ht, S₂, hd₂, -, hcls⟩ := hd₁.exists_cls_subnormalClosure hq8'
  exact ⟨_, OddQ.datum hd₂ (CFSG.ComponentClassification.OddCore.odd_card _), hcls⟩

end E3

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.exists_secCls (hF : E3Frame n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) :
    ∃ Sq : Sylow 2 ↥(secR R u), TightDatum (secR R u) Sq (E3.secT htu ht) ∧
      TightCls (SecQ R u) (secR R u) Sq (E3.secT htu ht) :=
  E3.exists_secCls hF.large.datum hF.large.cls.1 hF.maxAdj.1.2 hF.inv htu ht

theorem E3Frame.card_secQ_lt (hF : E3Frame n R S t J u) : Nat.card (SecQ R u) < n := by
  have hd := hF.large.datum
  have hJnbr := hF.maxAdj.1.2
  obtain ⟨-, hu2, -, -, -, -⟩ := hd.edge_involution hJnbr hF.inv
  obtain ⟨g, hgJ'⟩ := hJnbr.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hgu : g * t * g⁻¹ = u := by
    have h1 := hd.isUniqueInvolution_core.conj g
    rw [hgJ] at h1
    exact h1.eq hF.inv
  have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hF.inv.ne_one
  have hE2u : ¬ TightInO2 u := hgu ▸ not_tightInO2_conj hF.large.notInO2 g
  have h3 := card_centralizer_lt hu2' hE2u
  have h1 : Nat.card (SecQ R u) ≤ Nat.card ↥(secH R u) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card ↥(secH R u) ≤ Nat.card ↥(Subgroup.centralizer ({u} : Set Y)) :=
    Subgroup.card_le_card_group _
  rw [← hF.large.card]
  omega

theorem E3Frame.sec_dich (hF : E3Frame n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) :
    TightInO2 (E3.secT htu ht) ∨ TightFStarQuasisimple (SecQ R u) ∨
      TightTwisted (SecQ R u) (E3.secT htu ht) := by
  obtain ⟨Sq, hd, hc⟩ := hF.exists_secCls htu ht
  exact tightDichotomy_of hd hc

end Cit3

section ExitList


variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightEx.reduce (hd : TightDatum R S t) (hc : TightCls Y R S t) {S' : Sylow 2 R}
    (hex : TightEx Y R S' t) (hE2 : ¬ TightInO2 t) :
    (TightEdgeless R ∧ ¬ TightActs3 R t) ∨
      (TightEdgeless R ∧ Nonempty (Y ⧸ Subgroup.center Y ≃* NativeSporadic.Carrier .M12)) ∨
      (Subgroup.center Y ≠ ⊥ ∧ (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1)) := by
  rcases hex with h | h | ⟨he, f, hfs, hfk⟩ | ⟨Q, _, f, hfs, hfk, hf1, hQ⟩
  · exact absurd h hE2
  · exact Or.inl h
  · have hs : IsSimpleGroup (NativeSporadic.Carrier .M12) :=
      CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    have hcard : Nat.card (NativeSporadic.Carrier .M12) = 95040 :=
      CFSG.Sporadic.Mathieu.card_M12
    have hZ := center_eq_bot_of_isSimpleGroup
      (exists_ne_comm_of_not_prime (by rw [hcard]; norm_num))
    exact Or.inr (Or.inl ⟨he, nonempty_mulEquiv_of_datum hd hc hE2 hZ f hfs hfk⟩)
  · have hs : IsSimpleGroup Q := by
      rcases hQ with h | h <;> exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
    have hcard : ¬ (Nat.card Q).Prime := by
      rcases hQ with h | h
      · rw [card_of_lieModel_psp_three_two_one h]
        norm_num
      · rw [card_of_lieModel_pomegaPlus_four_two_one h]
        norm_num
    have hZ := center_eq_bot_of_isSimpleGroup (exists_ne_comm_of_not_prime hcard)
    have hk := ker_eq_center_of_datum hd hc hE2 hZ f hfs hfk
    obtain ⟨e⟩ := nonempty_mulEquiv_of_datum hd hc hE2 hZ f hfs hfk
    refine Or.inr (Or.inr ⟨fun h0 => hf1 (hk.trans h0), ?_⟩)
    rcases hQ with h | h
    · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
    · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)

theorem inO2_of_exit_ident (hd : TightDatum R S t) (hc : TightCls Y R S t) {S' : Sylow 2 R}
    (hex : TightEx Y R S' t) (h3 : TightActs3 R t)
    (hM12 : IsEmpty (Y ⧸ Subgroup.center Y ≃* NativeSporadic.Carrier .M12))
    (hSp : ¬ LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1)
    (hOm : ¬ LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) : TightInO2 t := by
  by_contra hE2
  rcases TightEx.reduce hd hc hex hE2 with ⟨-, hn⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, h | h⟩
  · exact hn h3
  · exact hM12.false e
  · exact hSp h
  · exact hOm h

end ExitList

section E4


@[expose] def TightC17_11R (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
      ¬ TightEdgeless (secR R u) → Subgroup.center (SecQ R u) ≠ ⊥ →
        LieModel (SecQ R u ⧸ Subgroup.center (SecQ R u)) .PSp 3 2 1 →
          TightInO2 (E3.secT htu ht)

@[expose] def TightC17_11'R (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
      ¬ TightEdgeless (secR R u) → Subgroup.center (SecQ R u) ≠ ⊥ →
        LieModel (SecQ R u ⧸ Subgroup.center (SecQ R u)) .POmegaPlus 4 2 1 →
          TightInO2 (E3.secT htu ht)

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.e4_cases (hF : E3Frame n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    {Sb : Sylow 2 ↥(secR R u)} (hex : TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht))
    (hedge : ¬ TightEdgeless (secR R u)) :
    TightInO2 (E3.secT htu ht) ∨ (Subgroup.center (SecQ R u) ≠ ⊥ ∧
      (LieModel (SecQ R u ⧸ Subgroup.center (SecQ R u)) .PSp 3 2 1 ∨
        LieModel (SecQ R u ⧸ Subgroup.center (SecQ R u)) .POmegaPlus 4 2 1)) := by
  by_cases hE2 : TightInO2 (E3.secT htu ht)
  · exact Or.inl hE2
  · obtain ⟨Sq, hd, hc⟩ := hF.exists_secCls htu ht
    rcases TightEx.reduce hd hc hex hE2 with ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact absurd h hedge
    · exact absurd h hedge
    · exact Or.inr h

theorem tightE3E4F_of_leaves (h1 : TightC17_11R n) (h2 : TightC17_11'R n) : TightE3E4F n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge
  rcases hF.e4_cases htu ht hex hedge with h | ⟨hZ, h | h⟩
  · exact h
  · exact h1 Y R S t J u hF htu ht hedge hZ h
  · exact h2 Y R S t J u hF htu ht hedge hZ h

end E4

end CFSG.ClassicalInvolution.Q3.TL4
