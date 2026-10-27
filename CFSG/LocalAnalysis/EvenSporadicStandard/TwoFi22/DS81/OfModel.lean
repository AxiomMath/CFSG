module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFacts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Quasithin CFSG.EvenSmallLie CFSG.EvenSmallLie.UnitarySix

variable {G : Type} [Group G] {L : Subgroup G}

theorem mem_map_subtype_iff {E' : Subgroup L} (y : L) :
    (y : G) ∈ E'.map L.subtype ↔ y ∈ E' :=
  Subgroup.mem_map_iff_mem L.subtype_injective

theorem mem_normalizer_map_subtype_iff {E' : Subgroup L} (x : L) :
    (x : G) ∈ normalizer ((E'.map L.subtype : Subgroup G) : Set G) ↔
      x ∈ normalizer (E' : Set L) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h y
    have := h (y : G)
    rw [mem_map_subtype_iff] at this
    have e : (x : G) * (y : G) * (x : G)⁻¹ = ((x * y * x⁻¹ : L) : G) := by simp
    rw [e, mem_map_subtype_iff] at this
    exact this
  · intro h y
    by_cases hy : y ∈ L
    · have := h ⟨y, hy⟩
      have e : (x : G) * y * (x : G)⁻¹ = ((x * ⟨y, hy⟩ * x⁻¹ : L) : G) := by simp
      rw [e]
      have h1 := mem_map_subtype_iff (E' := E') ⟨y, hy⟩
      have h2 := mem_map_subtype_iff (E' := E') (x * ⟨y, hy⟩ * x⁻¹)
      exact h1.trans (this.trans h2.symm)
    · have hy' : y ∉ (E'.map L.subtype : Subgroup G) := fun hm => hy (by
        obtain ⟨z, -, rfl⟩ := hm
        exact z.2)
      have hxy : (x : G) * y * (x : G)⁻¹ ∉ (E'.map L.subtype : Subgroup G) := fun hm => by
        have hL : (x : G) * y * (x : G)⁻¹ ∈ L := by
          obtain ⟨z, -, hz⟩ := hm
          rw [← hz]
          exact z.2
        apply hy
        have : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem x.2) hL) x.2
      exact iff_of_false hy' hxy

theorem normalizer_subgroupOf_map_subtype (E' : Subgroup L) :
    (normalizer ((E'.map L.subtype : Subgroup G) : Set G)).subgroupOf L =
      normalizer (E' : Set L) := by
  ext x
  rw [mem_subgroupOf]
  exact mem_normalizer_map_subtype_iff x


theorem rank_of_localModel [Finite G] {t : G} {E' : Subgroup L} (M : LocalModel L E')
    (hN : centralizer ({t} : Set G) = normalizer (L : Set G))
    (hout : (L ⊔ centralizer (L : Set G)).relIndex (centralizer {t}) ≤ 2)
    (hinv : ∀ y ∈ L ⊔ centralizer (L : Set G), y ^ 2 = 1 → y ∈ L) :
    ∀ τ ∈ centralizer {t}, orderOf τ = 2 → τ ∉ L ⊔ centralizer (L : Set G) →
      ∀ B : Subgroup G, B ≤ centralizer {t} ⊓ centralizer {τ} → (∀ b ∈ B, b ^ 2 = 1) →
        Nat.card B ≤ 2 ^ 9 := by
  intro τ hτ hτ2 hτF B hB hBsq
  set F := L ⊔ centralizer (L : Set G) with hF
  have hτN : τ ∈ normalizer (L : Set G) := hN ▸ hτ
  have hτsq : τ * τ = 1 := by rw [← sq, ← hτ2, pow_orderOf_eq_one]
  have hBH : B ≤ centralizer {t} := hB.trans inf_le_left
  have hcard := card_le_two_mul_card_inf hBH hout
  have hFB : F ⊓ B ≤ L := fun y hy => hinv y hy.1 (hBsq y hy.2)
  let σ : MulAut L := L.normalizerMonoidHom ⟨τ, hτN⟩
  have hσ : ∀ x : L, ((σ x : L) : G) = τ * x * τ⁻¹ := fun x => rfl
  have hσσ : σ * σ = 1 := by
    have : (⟨τ, hτN⟩ * ⟨τ, hτN⟩ : normalizer (L : Set G)) = 1 := Subtype.ext hτsq
    show L.normalizerMonoidHom ⟨τ, hτN⟩ * L.normalizerMonoidHom ⟨τ, hτN⟩ = 1
    rw [← map_mul, this, map_one]
  have hσout : ∀ l : L, σ ≠ MulAut.conj l := by
    intro l hl
    apply hτF
    have hc : (l : G)⁻¹ * τ ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      have := congrArg (fun f : MulAut L => ((f ⟨x, hx⟩ : L) : G)) hl
      simp only [hσ, MulAut.conj_apply, coe_mul, coe_inv] at this
      calc x * ((l : G)⁻¹ * τ) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * τ := by group
        _ = (l : G)⁻¹ * (τ * x * τ⁻¹) * τ := by rw [← this]
        _ = (l : G)⁻¹ * τ * x := by group
    have : τ = (l : G) * ((l : G)⁻¹ * τ) := by group
    rw [this]
    exact mul_mem_sup l.2 hc
  set B₁ : Subgroup L := (F ⊓ B).subgroupOf L with hB₁
  have hB₁sq : ∀ b ∈ B₁, b ^ 2 = 1 := fun b hb => by
    have := hBsq _ (mem_subgroupOf.1 hb).2
    exact Subtype.ext (by simpa using this)
  have hB₁fix : ∀ b ∈ B₁, σ b = b := fun b hb => by
    have hbB : (b : G) ∈ centralizer {τ} := (hB (mem_subgroupOf.1 hb).2).2
    have hbτ : (b : G) * τ = τ * (b : G) := mem_centralizer_singleton_iff.1 hbB
    refine Subtype.ext ?_
    rw [hσ]
    calc τ * (b : G) * τ⁻¹ = (b : G) * τ * τ⁻¹ := by rw [← hbτ]
      _ = b := by group
  have hB₁card : Nat.card B₁ = Nat.card (F ⊓ B : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFB).toEquiv
  have h8 := M.rank σ hσσ hσout B₁ hB₁sq hB₁fix
  rw [hB₁card] at h8
  omega

theorem Facts.of_localModel [Finite G] (h : StdHyp G L) {t : G} (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) {E' : Subgroup L} (M : LocalModel L E')
    (hout : (L ⊔ centralizer (L : Set G)).relIndex (centralizer {t}) ≤ 2) :
    Facts G t L (E'.map L.subtype) := by
  obtain ⟨htC, hCc, hC2, huniq, hN, hLt, hCt⟩ := std_center_facts h.toStandardSetting ht htZ
  have hZ : Even (Nat.card (center L)) := by
    obtain ⟨z, hzZ, rfl⟩ := htZ
    have h2 : orderOf (⟨z, hzZ⟩ : center L) = 2 := by
      rw [Subgroup.orderOf_mk]
      simpa using ht
    exact even_iff_two_dvd.2 (h2 ▸ orderOf_dvd_natCard _)
  have hinv : ∀ y ∈ L ⊔ centralizer (L : Set G), y ^ 2 = 1 → y ∈ L := fun y hy hy2 =>
    mem_of_sq_eq_one_of_mem_sup_centralizer hCc hZ M.sq hy hy2
  refine ⟨hLt, hN.le, Subgroup.map_subtype_le E', ?_, ?_, rank_of_localModel M hN hout hinv, hinv,
    ?_, ?_, ?_, ?_, hout⟩
  · rintro _ ⟨e, he, rfl⟩
    rw [coe_subtype, ← Subgroup.coe_pow, M.E_sq e he]
    rfl
  · rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact M.card_E
  · intro s hs hs2
    have hs'2 : orderOf (⟨s, hs⟩ : L) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hs2
    obtain ⟨l, hl⟩ := M.fuse ⟨s, hs⟩ hs'2
    exact ⟨(l : G), l.2, ⟨l⁻¹ * ⟨s, hs⟩ * l, hl, by simp⟩⟩
  · intro x hx
    obtain ⟨hxN, hxL⟩ := hx
    have hx'N : (⟨x, hxL⟩ : L) ∈ normalizer (E' : Set L) :=
      (mem_normalizer_map_subtype_iff ⟨x, hxL⟩).1 hxN
    have h1 := M.gen hx'N
    have h2 : x ∈ (E' ⊔ closure {y | y ∈ normalizer (E' : Set L) ∧ Odd (orderOf y)}).map
        L.subtype := ⟨⟨x, hxL⟩, h1, rfl⟩
    rw [Subgroup.map_sup, MonoidHom.map_closure] at h2
    refine sup_le_sup_left (Subgroup.closure_mono ?_) _ h2
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨⟨(mem_normalizer_map_subtype_iff y).2 hy1, y.2⟩, ?_⟩
    simpa [Subgroup.orderOf_coe] using hy2
  · have : (normalizer ((E'.map L.subtype : Subgroup G) : Set G)).relIndex L =
        (normalizer (E' : Set L)).index := by
      rw [Subgroup.relIndex, normalizer_subgroupOf_map_subtype]
    rw [this]
    exact M.odd_index
  · intro B hB hBsq hBc
    have hBL : B ≤ L := hB.trans inf_le_right
    have hB' : B.subgroupOf L ≤ normalizer (E' : Set L) := by
      intro y hy
      rw [mem_subgroupOf] at hy
      exact (mem_normalizer_map_subtype_iff y).1 (hB hy).1
    have hsq' : ∀ b ∈ B.subgroupOf L, b ^ 2 = 1 := fun b hb =>
      Subtype.ext (by simpa using hBsq _ (mem_subgroupOf.1 hb))
    have hc' : Nat.card (B.subgroupOf L) = 2 ^ 11 := by
      rw [← hBc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
    have := M.unique _ hB' hsq' hc'
    rw [← Subgroup.map_subgroupOf_eq_of_le hBL, this]

theorem centralizer_le_of_localModel [Finite G] (h : StdHyp G L) {t : G} (ht : orderOf t = 2)
    (htZ : t ∈ (center L).map L.subtype) {E' : Subgroup L} (M : LocalModel L E') :
    centralizer ((E'.map L.subtype : Subgroup G) : Set G) ≤
      E'.map L.subtype ⊔ centralizer (L : Set G) := by
  obtain ⟨htC, hCc, hC2, huniq, hN, hLt, hCt⟩ := std_center_facts h.toStandardSetting ht htZ
  intro c hc
  have htE : t ∈ E'.map L.subtype := by
    obtain ⟨z, hz, rfl⟩ := htZ
    exact ⟨z, M.center_le hz, rfl⟩
  have hct : c ∈ centralizer {t} := by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hc t htE).symm
  have hcN : c ∈ normalizer (L : Set G) := hN ▸ hct
  let σ : MulAut L := L.normalizerMonoidHom ⟨c, hcN⟩
  have hσ : ∀ x : L, ((σ x : L) : G) = c * x * c⁻¹ := fun x => rfl
  have hfix : ∀ e ∈ E', σ e = e := by
    intro e he
    refine Subtype.ext ?_
    rw [hσ]
    have := mem_centralizer_iff.1 hc (e : G) ⟨e, he, rfl⟩
    calc c * (e : G) * c⁻¹ = (e : G) * c * c⁻¹ := by rw [this]
      _ = e := by group
  obtain ⟨x, hx, hxσ⟩ := M.aut_cent σ hfix
  have hxc : (x : G)⁻¹ * c ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have := congrArg (fun f : MulAut L => ((f ⟨y, hy⟩ : L) : G)) hxσ
    simp only [hσ, MulAut.conj_apply, coe_mul, coe_inv] at this
    calc y * ((x : G)⁻¹ * c) = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * c := by group
      _ = (x : G)⁻¹ * (c * y * c⁻¹) * c := by rw [this]
      _ = (x : G)⁻¹ * c * y := by group
  have : c = (x : G) * ((x : G)⁻¹ * c) := by group
  rw [this]
  exact mul_mem_sup ⟨x, hx, rfl⟩ hxc

end CFSG.EvenSporadicStandard.TwoFi22.DS81
