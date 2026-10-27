module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Cover
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

section Bar

variable {G : Type} [Group G]

theorem mem_pPrimeCoreOf_iff {H : Subgroup G} {x : G} :
    x ∈ pPrimeCoreOf 2 H ↔ ∃ hx : x ∈ H, (⟨x, hx⟩ : ↥H) ∈ CFSG.pPrimeCore 2 ↥H := by
  unfold pPrimeCoreOf
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem isPGroup_barIn {H V : Subgroup G} {p : ℕ} (hV : IsPGroup p ↥V) :
    IsPGroup p ↥(barIn H V) :=
  (hV.comap_subtype (K := H)).map _

theorem barIn_le_normalizer {H S V : Subgroup G} (hSV : S ≤ normalizer (V : Set G)) :
    barIn H S ≤ normalizer ((barIn H V : Subgroup (HBar H)) : Set (HBar H)) := by
  have h1 : S.subgroupOf H ≤ normalizer ((V.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro w
    have hs' : (s : G) ∈ normalizer (V : Set G) := hSV (Subgroup.mem_subgroupOf.1 hs)
    have := mem_normalizer_iff.1 hs' (w : G)
    simpa [Subgroup.mem_subgroupOf] using this
  exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)

theorem barIn_eq_bot_iff {H V : Subgroup G} (hVH : V ≤ H) :
    barIn H V = ⊥ ↔ V ≤ pPrimeCoreOf 2 H := by
  unfold barIn
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  constructor
  · intro h v hv
    exact mem_pPrimeCoreOf_iff.2 ⟨hVH hv, h (Subgroup.mem_subgroupOf.2 hv)⟩
  · intro h x hx
    obtain ⟨hx', hxO⟩ := mem_pPrimeCoreOf_iff.1 (h (Subgroup.mem_subgroupOf.1 hx))
    exact hxO

theorem relIndex_eq_card_barIn {H V : Subgroup G} (hVH : V ≤ H) :
    (V ⊓ pPrimeCoreOf 2 H).relIndex V = Nat.card ↥(barIn H V) := by
  have h1 : (pPrimeCoreOf 2 H).relIndex V = (CFSG.pPrimeCore 2 ↥H).relIndex (V.subgroupOf H) := by
    have := Subgroup.relIndex_map_map_of_injective (f := H.subtype) (CFSG.pPrimeCore 2 ↥H)
      (V.subgroupOf H) H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hVH] at this
    exact this
  rw [inf_comm, Subgroup.inf_relIndex_right, h1]
  unfold barIn
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']

theorem card_barIn_two [Finite G] {H S : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup 2 ↥S) :
    Nat.card ↥(barIn H S) = Nat.card ↥S := by
  rw [← relIndex_eq_card_barIn hSH]
  have hbot : S ⊓ pPrimeCoreOf 2 H = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (hS.to_le (inf_le_left : S ⊓ pPrimeCoreOf 2 H ≤ S)).exists_card_eq
    have hdvd : Nat.card ↥(S ⊓ pPrimeCoreOf 2 H) ∣ Nat.card ↥(pPrimeCoreOf 2 H) :=
      Subgroup.card_dvd_of_le inf_le_right
    have hcard : Nat.card ↥(pPrimeCoreOf 2 H) = Nat.card ↥(CFSG.pPrimeCore 2 ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    have hcop : Nat.Coprime 2 (Nat.card ↥(CFSG.pPrimeCore 2 ↥H)) :=
      CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥H)
    rw [hn, hcard] at hdvd
    have h1 : 2 ^ n = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n hcop) hdvd
    rw [← Subgroup.card_eq_one, hn, h1]
  rw [hbot, Subgroup.relIndex_bot_left]

theorem sup_eq_of_barIn_eq {H V V' : Subgroup G} (hVH : V ≤ H) (hV'H : V' ≤ H)
    (h : barIn H V = barIn H V') : pPrimeCoreOf 2 H ⊔ V' = pPrimeCoreOf 2 H ⊔ V := by
  have key : ∀ {A B : Subgroup G}, A ≤ H → barIn H A ≤ barIn H B → A ≤ pPrimeCoreOf 2 H ⊔ B := by
    intro A B hAH hAB v hv
    have hm : (QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥H) ⟨v, hAH hv⟩ : HBar H) ∈ barIn H A :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hv)
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.1 (hAB hm)
    have hO : w⁻¹ * ⟨v, hAH hv⟩ ∈ CFSG.pPrimeCore 2 ↥H := QuotientGroup.eq.1 hwe
    have hOG : ((w⁻¹ * ⟨v, hAH hv⟩ : ↥H) : G) ∈ pPrimeCoreOf 2 H :=
      mem_pPrimeCoreOf_iff.2 ⟨(w⁻¹ * ⟨v, hAH hv⟩ : ↥H).2, hO⟩
    have hwB : (w : G) ∈ B := Subgroup.mem_subgroupOf.1 hw
    have hv' : v = (w : G) * ((w⁻¹ * ⟨v, hAH hv⟩ : ↥H) : G) := by simp
    rw [hv', sup_comm]
    exact Subgroup.mul_mem_sup hwB hOG
  exact le_antisymm (sup_le le_sup_left (key hV'H h.symm.le)) (sup_le le_sup_left (key hVH h.le))

theorem clauses_of_bar_unique {H S : Subgroup G}
    (huniq : ∀ W W' : Subgroup (HBar H), IsPGroup 3 ↥W → IsPGroup 3 ↥W' → W ≠ ⊥ → W' ≠ ⊥ →
      barIn H S ≤ normalizer (W : Set (HBar H)) → barIn H S ≤ normalizer (W' : Set (HBar H)) →
      W = W' ∧ Nat.card ↥W = 3)
    {V V' : Subgroup G} (hV : V ≤ H) (hV3 : IsPGroup 3 ↥V) (hVS : S ≤ normalizer (V : Set G))
    (hVO : ¬ V ≤ pPrimeCoreOf 2 H) (hV' : V' ≤ H) (hV3' : IsPGroup 3 ↥V')
    (hVS' : S ≤ normalizer (V' : Set G)) (hVO' : ¬ V' ≤ pPrimeCoreOf 2 H) :
    (V ⊓ pPrimeCoreOf 2 H).relIndex V = 3 ∧ pPrimeCoreOf 2 H ⊔ V' = pPrimeCoreOf 2 H ⊔ V := by
  obtain ⟨hWW, hW3⟩ := huniq (barIn H V) (barIn H V') (isPGroup_barIn hV3) (isPGroup_barIn hV3')
    (fun h => hVO ((barIn_eq_bot_iff hV).1 h)) (fun h => hVO' ((barIn_eq_bot_iff hV').1 h))
    (barIn_le_normalizer hVS) (barIn_le_normalizer hVS')
  exact ⟨by rw [relIndex_eq_card_barIn hV, hW3], sup_eq_of_barIn_eq hV hV' hWW⟩

theorem branch_two_a11 [Finite G] {H S : Subgroup G} (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ 8)
    (h11 : IsDoubleCoverOfAlt (HBar H) 11)
    {V V' : Subgroup G} (hV : V ≤ H) (hV3 : IsPGroup 3 ↥V) (hVS : S ≤ normalizer (V : Set G))
    (hVO : ¬ V ≤ pPrimeCoreOf 2 H) (hV' : V' ≤ H) (hV3' : IsPGroup 3 ↥V')
    (hVS' : S ≤ normalizer (V' : Set G)) (hVO' : ¬ V' ≤ pPrimeCoreOf 2 H) :
    (V ⊓ pPrimeCoreOf 2 H).relIndex V = 3 ∧ pPrimeCoreOf 2 H ⊔ V' = pPrimeCoreOf 2 H ⊔ V := by
  refine clauses_of_bar_unique ?_ hV hV3 hVS hVO hV' hV3' hVS' hVO'
  intro W W' hW hW' hW1 hW1' hn hn'
  obtain ⟨-, hc, ⟨e⟩⟩ := h11
  let ρ : HBar H →* Equiv.Perm (Fin 11) :=
    (alternatingGroup (Fin 11)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (center (HBar H))))
  have hker : ρ.ker = center (HBar H) := by
    ext x
    simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [← Subgroup.coe_one, Subtype.coe_inj, MulEquiv.coe_toMonoidHom, e.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hrange : ρ.range ≤ alternatingGroup (Fin 11) := by
    rintro _ ⟨x, rfl⟩
    exact (e (QuotientGroup.mk' (center (HBar H)) x)).2
  have hA : Nat.card ↥(barIn H S) = 2 ^ 8 := by
    rw [card_barIn_two hSH (IsPGroup.of_card hS), hS]
  exact cover_unique ρ hrange hker.le (by rw [hker]; exact hc) hA hW hW' hW1 hW1' hn hn'

end Bar

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
