module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResDD

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

section Conj

variable {G : Type} [Group G]

theorem conj_mem_centralizer {a b : G} (h : a ∈ centralizer ({b} : Set G)) (c : G) :
    c * a * c⁻¹ ∈ centralizer ({c * b * c⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  calc c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
    _ = c * (b * a) * c⁻¹ := by rw [h]
    _ = c * b * c⁻¹ * (c * a * c⁻¹) := by group

theorem map_centralizer_pair_conj (a b c : G) :
    (centralizer ({a, b} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * a * c⁻¹, c * b * c⁻¹} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hy
    rw [Subgroup.mem_centralizer_iff]
    have hya : a * y = y * a := hy a (Set.mem_insert _ _)
    have hyb : b * y = y * b := hy b (Set.mem_insert_of_mem _ rfl)
    intro g hg
    have e : (MulAut.conj c).toMonoidHom y = c * y * c⁻¹ := rfl
    rw [e]
    rcases hg with hg | hg
    · rw [hg]
      calc c * a * c⁻¹ * (c * y * c⁻¹) = c * (a * y) * c⁻¹ := by group
        _ = c * (y * a) * c⁻¹ := by rw [hya]
        _ = c * y * c⁻¹ * (c * a * c⁻¹) := by group
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      calc c * b * c⁻¹ * (c * y * c⁻¹) = c * (b * y) * c⁻¹ := by group
        _ = c * (y * b) * c⁻¹ := by rw [hyb]
        _ = c * y * c⁻¹ * (c * b * c⁻¹) := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have hxa : c * a * c⁻¹ * x = x * (c * a * c⁻¹) := hx _ (Set.mem_insert _ _)
    have hxb : c * b * c⁻¹ * x = x * (c * b * c⁻¹) := hx _ (Set.mem_insert_of_mem _ rfl)
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro g hg
      rcases hg with hg | hg
      · rw [hg]
        calc a * (c⁻¹ * x * c) = c⁻¹ * ((c * a * c⁻¹) * x) * c := by group
          _ = c⁻¹ * (x * (c * a * c⁻¹)) * c := by rw [hxa]
          _ = c⁻¹ * x * c * a := by group
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        calc b * (c⁻¹ * x * c) = c⁻¹ * ((c * b * c⁻¹) * x) * c := by group
          _ = c⁻¹ * (x * (c * b * c⁻¹)) * c := by rw [hxb]
          _ = c⁻¹ * x * c * b := by group
    · show c * (c⁻¹ * x * c) * c⁻¹ = x
      group

theorem map_conj_inv_map_conj (Y : Subgroup G) (c : G) :
    (Y.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = Y := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id Y
  ext x
  simp
  group

variable [Finite G]

theorem pLayerOf_conj_le (X : Subgroup G) (c : G) :
    (pLayerOf 2 X).map (MulAut.conj c).toMonoidHom ≤
      pLayerOf 2 (X.map (MulAut.conj c).toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (CFSG.GH74.GLS.Stage1.Thm2.Recip.isPCompIn_map_conj hK c)

theorem pLayerOf_map_conj (X : Subgroup G) (c : G) :
    pLayerOf 2 (X.map (MulAut.conj c).toMonoidHom) =
      (pLayerOf 2 X).map (MulAut.conj c).toMonoidHom := by
  apply le_antisymm
  · have h1 := pLayerOf_conj_le (X.map (MulAut.conj c).toMonoidHom) c⁻¹
    rw [map_conj_inv_map_conj] at h1
    have h2 := Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom) h1
    have e := map_conj_inv_map_conj (pLayerOf 2 (X.map (MulAut.conj c).toMonoidHom)) c⁻¹
    rw [inv_inv] at e
    rwa [e] at h2
  · exact pLayerOf_conj_le X c

omit [Finite G] in
theorem cover_of_surj {L I : Subgroup G}
    (hsurj : (I.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) = ⊤) :
    ∀ l ∈ L, ∃ i ∈ I, ∃ o ∈ pPrimeCoreOf 2 L, l = i * o := by
  intro l hl
  have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨l, hl⟩ ∈
      (I.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) := by
    rw [hsurj]
    trivial
  obtain ⟨i, hi, hie⟩ := hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hie
  exact ⟨(i : G), hi, (i : G)⁻¹ * l, ⟨i⁻¹ * ⟨l, hl⟩, hie, rfl⟩, by group⟩

theorem exists_perfect_lift_barIn {H : Subgroup G} {w : G} (hwH : w ∈ H) (hw2 : orderOf w = 2)
    {D : Subgroup (HBar H)} (hD : ⁅D, D⁆ = D)
    (hDw : D ≤ centralizer (barIn H (zpowers w) : Set (HBar H))) :
    ∃ D₁ : Subgroup G, D₁ ≤ H ∧ D₁ ≤ centralizer ({w} : Set G) ∧ ⁅D₁, D₁⁆ = D₁ ∧
      barIn H D₁ = D := by
  have hN : Odd (Nat.card ↥(pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have ha : orderOf (⟨w, hwH⟩ : ↥H) = 2 := by rw [Subgroup.orderOf_mk]; exact hw2
  have hDa : D ≤ centralizer
      ({QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨w, hwH⟩} : Set (HBar H)) := by
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨w, hwH⟩ ∈ barIn H (zpowers w) :=
      ⟨⟨w, hwH⟩, Subgroup.mem_zpowers w, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hDw hd) _ hmem).symm
  obtain ⟨P, hPc, hPp, hPm⟩ := exists_perfect_lift_centralizer hN ha hD hDa
  refine ⟨P.map H.subtype, Subgroup.map_subtype_le P, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hPc hx))
  · rw [← Subgroup.map_commutator, hPp]
  · have e : (P.map H.subtype).subgroupOf H = P :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective P
    unfold barIn
    rw [e, hPm]

omit [Finite G] in
theorem comm_mem_pPrimeCoreOf {H A B : Subgroup G} (hAH : A ≤ H) (hBH : B ≤ H)
    (hAB : barIn H A ≤ centralizer (barIn H B : Set (HBar H))) :
    ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ pPrimeCoreOf 2 H := by
  intro a ha b hb
  have hab : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨a, hAH ha⟩ ∈
      centralizer (barIn H B : Set (HBar H)) := hAB ⟨⟨a, hAH ha⟩, ha, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp hab _ ⟨⟨b, hBH hb⟩, hb, rfl⟩
  have hk : ⁅(⟨a, hAH ha⟩ : ↥H), ⟨b, hBH hb⟩⁆ ∈ pPrimeCore 2 ↥H := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥H), MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hc.symm
  exact ⟨_, hk, rfl⟩

end Conj

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD
