module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.ZStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LAssemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LHConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23LOrbit
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

theorem fi23_isSporadic_map_conj {H : Type} [Group H] {s : TauCeti.SporadicName}
    {L : Subgroup H} (h : IsSporadic ↥L s) (g : H) :
    IsSporadic ↥(L.map (MulAut.conj g).toMonoidHom) s := by
  obtain ⟨e⟩ := h
  exact ⟨(L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans
    e⟩

variable {H : Type} [Group H] [Finite H] {N L : Subgroup H} {t : H}

theorem fi23_exists_fused (hN : FStarSimple N) (h : Setting612 H L t) :
    ∃ a ∈ L, orderOf a = 2 ∧ IsConj t (t * a) := by
  obtain ⟨g, hne, hcomm⟩ := Closing.exists_fused_commuting_involution_of_fStar hN h.t_order
  have hs : g * t * g⁻¹ ∈ centralizer ({t} : Set H) :=
    mem_centralizer_singleton_iff.2 hcomm
  obtain ⟨a, ha, hsa⟩ := h.exists_eq_mul hs
  have hs2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [h.t_sq]; group
  rcases hsa with hsa | hsa
  · exact absurd (hsa ▸ ha) (h.conj_not_mem g)
  · have hata : a * a = 1 := by
      have h1 : (a * t) * (a * t) = 1 := hsa ▸ hs2
      have hc : t * a = a * t := (h.comm_of_mem ha).symm
      calc a * a = a * a * (t * t) := by rw [h.t_sq, mul_one]
        _ = a * (a * t) * t := by simp only [mul_assoc]
        _ = a * (t * a) * t := by rw [hc]
        _ = (a * t) * (a * t) := by simp only [mul_assoc]
        _ = 1 := h1
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hne (by rw [hsa, one_mul])
    refine ⟨a, ha, orderOf_eq_prime (by rw [pow_two]; exact hata) ha1, ?_⟩
    refine isConj_iff.2 ⟨g, ?_⟩
    rw [hsa, h.comm_of_mem ha]

theorem fi23_isConj_mul_of_claim (hN : FStarSimple N) (h : Setting612 H L t) {u : H}
    (hE : ∀ a ∈ L, orderOf a = 2 → (¬ ∃ l ∈ L, a = l * u * l⁻¹) → ¬ IsConj t (t * a)) :
    IsConj t (t * u) := by
  obtain ⟨a, ha, ha2, hconj⟩ := fi23_exists_fused hN h
  by_cases hex : ∃ l ∈ L, a = l * u * l⁻¹
  · obtain ⟨l, hl, rfl⟩ := hex
    refine hconj.trans (isConj_iff.2 ⟨l⁻¹, ?_⟩)
    calc l⁻¹ * (t * (l * u * l⁻¹)) * l⁻¹⁻¹ = (l⁻¹ * t * l) * u := by group
      _ = t * u := by rw [h.inv_mul_mul_of_mem hl]
  · exact absurd hconj (hE a ha ha2 hex)

theorem fi23_exists_out_of_setting (hN : FStarSimple N) (hs : Setting612 H L t) {u : H}
    (hu : Fi23Transposition L u) (hLoc : Fi23Local612 H L)
    (hLocg : ∀ g : H, Fi23Local612 H (L.map (MulAut.conj g).toMonoidHom))
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (h65 : Balance.Sol78Lemma65KP)
    (hE : ∀ a ∈ L, orderOf a = 2 → (¬ ∃ l ∈ L, a = l * u * l⁻¹) → ¬ IsConj t (t * a)) :
    ∃ W : Subgroup H, Sol78Lemma612Out H L t W := by
  obtain ⟨WL, hWLle, huWL, hWLab, hWLcard, hWLcent, ⟨hNnorm, ⟨iso23⟩⟩, hP, htrans⟩ :=
    hLoc.frame u hu
  have hfus : ∀ a ∈ L, orderOf a = 2 → IsConj t (t * a) → ∃ l ∈ L, a = l * u * l⁻¹ :=
    fun a ha ha2 hc => by_contra fun hex => hE a ha ha2 hex hc
  have hconjtu : IsConj t (t * u) := fi23_isConj_mul_of_claim hN hs hE
  obtain ⟨g, hg⟩ := isConj_iff.1 hconjtu
  have hW : WSupHyp L WL t := ⟨hs.t_mem, hs.t_sq, hs.t_ne, hs.disjoint, hWLle⟩
  obtain ⟨m, hm, hmt⟩ := hW.exists_mem_normalizer_of_fusion hs.cent hWLab hWLcard huWL hg
    (hLocg g).conj_elemAbelian
  have h24 := ncard_orbit hs hW hWLab hu.2.1 hfus ⟨m, hm, hmt⟩ htrans hs.cent hP
  have htW : t ∈ WL ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hWab : IsElemAbelian 2 (WL ⊔ zpowers t) := hW.isElemAbelian hWLab
  have hWcard : Nat.card (WL ⊔ zpowers t : Subgroup H) = 2 ^ 12 := by
    rw [hW.card, hWLcard]
    norm_num
  have hcW : centralizer ((WL ⊔ zpowers t : Subgroup H) : Set H) = WL ⊔ zpowers t :=
    hW.centralizer_eq hs.cent hWLcent
  have hWN : (WL ⊔ zpowers t : Subgroup H) ≤
      normalizer ((WL ⊔ zpowers t : Subgroup H) : Set H) := Subgroup.le_normalizer
  have hNC := hW.normalizer_inf_centralizer hs.cent
  have hH₁N : normalizer (WL : Set H) ⊓ L ≤
      normalizer ((WL ⊔ zpowers t : Subgroup H) : Set H) := by
    intro x hx
    have : x ∈ normalizer ((WL ⊔ zpowers t : Subgroup H) : Set H) ⊓
        centralizer ({t} : Set H) := by
      rw [hNC]
      exact Subgroup.mem_sup_left hx
    exact this.1
  have hdisjH : Disjoint (normalizer (WL : Set H) ⊓ L) (zpowers t) :=
    hs.disjoint.mono_left inf_le_right
  have hsub : (WL ⊔ zpowers t : Subgroup H).subgroupOf (normalizer (WL : Set H) ⊓ L) =
      WL.subgroupOf (normalizer (WL : Set H) ⊓ L) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hxW
      have : (x : H) ∈ (WL ⊔ zpowers t : Subgroup H) ⊓ L := ⟨hxW, x.2.2⟩
      rwa [hW.sup_inf_left] at this
    · intro hxWL
      exact Subgroup.mem_sup_left hxWL
  have hNW : ((WL ⊔ zpowers t : Subgroup H).subgroupOf
      (normalizer (WL : Set H) ⊓ L)).Normal := by
    rw [hsub]
    exact hNnorm
  have iso23' : Nonempty ((normalizer (WL : Set H) ⊓ L : Subgroup H) ⧸
      (WL ⊔ zpowers t : Subgroup H).subgroupOf (normalizer (WL : Set H) ⊓ L) ≃*
        Carrier .M23) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hsub).trans iso23⟩
  have hne : normalizer ((WL ⊔ zpowers t : Subgroup H) : Set H) ≠ ⊤ :=
    Balance.normalizer_ne_top_of_card_eq hN hWab hWcard
  obtain ⟨⟨iso24⟩, ⟨N₀, hN₀le, hN₀norm, hN₀idx, htN₀⟩, huniq⟩ :=
    h65 H hKP (normalizer ((WL ⊔ zpowers t : Subgroup H) : Set H)) (WL ⊔ zpowers t)
      (normalizer (WL : Set H) ⊓ L) t hne hWN inferInstance hWab hWcard
      (by rw [hcW]; exact inf_eq_left.2 hWN) htW hs.t_order h24
      (by rw [inf_comm, hNC]) hH₁N hdisjH hNW iso23'
  refine ⟨WL ⊔ zpowers t, hs.t_order, hs.t_mem, hWab, hWcard, htW, ?_, ?_, ?_⟩
  · intro h hle
    exact huniq _ hle (isElemAbelian_map_conj hWab h) (by rw [card_map_conj, hWcard])
  · have hcW' : (centralizer ((WL ⊔ zpowers t : Subgroup H) : Set H)).subgroupOf
        (normalizer ((WL ⊔ zpowers t : Subgroup H) : Set H)) =
        (WL ⊔ zpowers t : Subgroup H).subgroupOf
          (normalizer ((WL ⊔ zpowers t : Subgroup H) : Set H)) := by
      rw [hcW]
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hcW').trans iso24⟩
  · refine ⟨N₀.subgroupOf (normalizer ((WL ⊔ zpowers t : Subgroup H) : Set H)), hN₀norm,
      hN₀idx, ?_⟩
    rw [Subgroup.mem_subgroupOf]
    exact htN₀

end CFSG.EvenSporadicStandard.Induction
