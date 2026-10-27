module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2Abs
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt17
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Closed

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1

section Conj

variable {G : Type} [Group G]

theorem mem_conj_iff {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold conjugate
  rw [Subgroup.mem_map_equiv]
  simp

theorem card_conj (H : Subgroup G) (g : G) : Nat.card ↥(conjugate H g) = Nat.card ↥H :=
  (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj g⁻¹).injective).toEquiv).symm

theorem centralizer_conj' (z g : G) :
    centralizer ({g⁻¹ * z * g} : Set G) = conjugate (centralizer ({z} : Set G)) g := by
  ext x
  rw [mem_conj_iff, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [h]
      _ = z * (g * x * g⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * z * g) = g⁻¹ * (g * x * g⁻¹ * z) * g := by group
      _ = g⁻¹ * (z * (g * x * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * z * g) * x := by group

theorem normalizer_eq_of_coatom [IsSimpleGroup G] {M D : Subgroup G} (hM : IsCoatom M)
    (hD : D ≠ ⊥) (hDM : D ≤ M) (hn : ∀ m ∈ M, ∀ d ∈ D, m * d * m⁻¹ ∈ D) :
    normalizer (D : Set G) = M := by
  have hle : M ≤ normalizer (D : Set G) := fun m hm => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => hn m hm y hy, fun hy => by
      have := hn m⁻¹ (M.inv_mem hm) _ hy
      simpa [mul_assoc] using this⟩
  by_contra hne
  have hlt : M < normalizer (D : Set G) := lt_of_le_of_ne hle (Ne.symm hne)
  have htop := hM.2 _ hlt
  have hnorm : D.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with h | h
  · exact hD h
  · exact hM.1 (top_le_iff.mp (h ▸ hDM))

theorem mem_of_conj_eq [IsSimpleGroup G] {M : Subgroup G} (hM : IsCoatom M) (hM1 : M ≠ ⊥)
    {g : G} (hg : conjugate M g = M) : g ∈ M := by
  have hgN : g ∈ normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← mem_conj_iff (H := M) (g := g), hg]
  have hle : M ≤ normalizer (M : Set G) := Subgroup.le_normalizer
  by_cases heq : normalizer (M : Set G) = M
  · rw [← heq]; exact hgN
  · have hlt : M < normalizer (M : Set G) := lt_of_le_of_ne hle (Ne.symm heq)
    have htop := hM.2 _ hlt
    have hnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
    · exact absurd h hM1
    · exact absurd h hM.1

end Conj

theorem prop17_8_of (h177 : Lemma17_7) (h171 : Prop17_1) (hAB : IG_11_7) : Prop17_8 := by
  intro G _ _ z k S M h t htc htD
  have hz2 : orderOf z = 2 := h.ctx.ctx.central.1
  obtain ⟨hMC, hD1⟩ := h171 G z k S M h.ctx h.fail
  have hcoat : IsCoatom M := h.ctx.mem.1
  have hsimp : IsSimpleGroup G := (isKProperSimple_iff.1 h.ctx.ctx.std.kps).1
  obtain ⟨c, hc⟩ := isConj_iff.1 htc
  have ht2 : orderOf t = 2 := by
    rw [← hc, ← hz2]
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective z
    simpa using this
  by_cases hL : pLayerOf 2 M = ⊥
  · have hDM : pPrimeCoreOf 2 M ≤ M := Subgroup.map_subtype_le _
    have hDn : ∀ m ∈ M, ∀ d ∈ pPrimeCoreOf 2 M, m * d * m⁻¹ ∈ pPrimeCoreOf 2 M :=
      fun m hm d hd => pPrimeCoreOf_norm hm hd
    have hNorm : normalizer (pPrimeCoreOf 2 M : Set G) = M :=
      normalizer_eq_of_coatom hcoat hD1 hDM hDn
    have htM : t ∈ M := hNorm ▸ Subgroup.centralizer_le_normalizer _ htD
    have hMmem : ∀ y : G, y ∈ M ↔ y * z = z * y := fun y => by
      rw [hMC]; exact Subgroup.mem_centralizer_singleton_iff
    have htz : t * z = z * t := (hMmem t).1 htM
    set g : G := c⁻¹ with hg
    have htg : t = g⁻¹ * z * g := by rw [← hc, hg]; group
    have hNt : centralizer ({t} : Set G) = conjugate M g := by
      rw [htg, centralizer_conj' z g, hMC]
    have hzN : z ∈ conjugate M g :=
      hNt ▸ Subgroup.mem_centralizer_singleton_iff.mpr htz.symm
    have hDN : pPrimeCoreOf 2 M ≤ conjugate M g := fun d hd =>
      hNt ▸ Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp htD d hd)
    have hMc : IsTwoConstrained ↥M := isTwoConstrained_of_pLayerOf_eq_bot hL
    let e : ↥M ≃* ↥(conjugate M g) :=
      Subgroup.equivMapOfInjective M (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    have hNc : IsTwoConstrained ↥(conjugate M g) := isTwoConstrained_of_mulEquiv e hMc
    have hDo : Odd (Nat.card ↥(pPrimeCoreOf 2 M)) := odd_card_pPrimeCoreOf' M
    have hDo' : Odd (Nat.card ↥((pPrimeCoreOf 2 M).subgroupOf (conjugate M g))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv]
      exact hDo
    have hzord : orderOf (⟨z, hzN⟩ : ↥(conjugate M g)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hz2
    have hle : pPrimeCoreOf 2 M ≤ pPrimeCoreOf 2 (conjugate M g) := by
      have key := odd_le_pPrimeCore_of_twoConstrained hAB hNc hDo' hzord
        (fun d hd => by
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply Subtype.ext
          exact (hMmem d).1 (hDM hd))
        (fun x hx d hd => by
          have hxz := Subgroup.mem_centralizer_singleton_iff.mp hx
          exact hDn x ((hMmem x).2 (congrArg Subtype.val hxz)) d hd)
      intro d hd
      exact ⟨⟨d, hDN hd⟩, key hd, rfl⟩
    have hcard : Nat.card ↥(pPrimeCoreOf 2 (conjugate M g)) = Nat.card ↥(pPrimeCoreOf 2 M) := by
      have h1 : Nat.card ↥(pPrimeCoreOf 2 (conjugate M g)) =
          Nat.card ↥(pPrimeCore 2 ↥(conjugate M g)) :=
        Subgroup.card_map_of_injective (conjugate M g).subtype_injective
      have h2 : Nat.card ↥(pPrimeCoreOf 2 M) = Nat.card ↥(pPrimeCore 2 ↥M) :=
        Subgroup.card_map_of_injective M.subtype_injective
      have h3 : (pPrimeCore 2 ↥M).map e.toMonoidHom = pPrimeCore 2 ↥(conjugate M g) :=
        pPrimeCore_map_iso 2 e
      rw [h1, h2, ← h3, Subgroup.card_map_of_injective e.injective]
    have hDeq : pPrimeCoreOf 2 M = pPrimeCoreOf 2 (conjugate M g) :=
      Subgroup.eq_of_le_of_card_ge hle hcard.le
    have hNM : conjugate M g ≤ M := by
      intro n hn
      have : n ∈ normalizer (pPrimeCoreOf 2 (conjugate M g) : Set G) :=
        le_normalizer_pPrimeCoreOf _ hn
      rwa [← hDeq, hNorm] at this
    have hNeqM : conjugate M g = M :=
      Subgroup.eq_of_le_of_card_ge hNM (card_conj M g).ge
    have hM1 : M ≠ ⊥ := fun hbot => by
      have hzM : z ∈ M := (hMmem z).2 rfl
      rw [hbot, Subgroup.mem_bot] at hzM
      rw [hzM, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    have hgM : g ∈ M := mem_of_conj_eq hcoat hM1 hNeqM
    have hgz : g * z = z * g := (hMmem g).1 hgM
    rw [htg]
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hgz]
      _ = z := by group
  · exact h177 G z k S M h hL t ht2 htD

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
