module

public import CFSG.Adapters.Involutions

public section

namespace CFSG.GH74.GLS.SP.Local

theorem zstar_odd_card_oddCore {C : Type*} [Group C] [Finite C] :
    Odd (Nat.card (CFSG.oddCore C)) := by
  have hle : CFSG.oddCore C ≤ CFSG.pPrimeCore 2 C :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.mp
    (Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hle)
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := C)))

theorem zstar_odd_card_sup {C : Type*} [Group C] (K L : Subgroup C) [K.Normal]
    (hK : Odd (Nat.card K)) (hL : Odd (Nat.card L)) :
    Odd (Nat.card (K ⊔ L : Subgroup C)) := by
  have hindexOdd : Odd (K.relIndex (K ⊔ L)) := by
    rw [Subgroup.relIndex_sup_left]
    exact hL.of_dvd_nat (K.relIndex_dvd_card L)
  have hwithin : Nat.card (K.subgroupOf (K ⊔ L)) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ L)).toEquiv
  have hproduct := (K.subgroupOf (K ⊔ L)).index_mul_card
  have hindex : (K.subgroupOf (K ⊔ L)).index = K.relIndex (K ⊔ L) := rfl
  rw [hindex, hwithin] at hproduct
  rw [← hproduct]
  exact hindexOdd.mul hK

theorem zstar_decomposition {C : Type} [Group C] [Finite C] (T N : Subgroup C) (t : C)
    (hT2 : IsPGroup 2 ↥T)
    (hmax : ∀ S : Subgroup C, IsPGroup 2 ↥S → T ≤ S → S = T)
    (htT : t ∈ T) (ht2 : orderOf t = 2) (hTt : ∀ s ∈ T, s * t = t * s)
    (hweak : ∀ g : C, g⁻¹ * t * g ∈ T → g⁻¹ * t * g = t)
    (hNodd : Odd (Nat.card ↥N))
    (hNnorm : ∀ q : C, q * t = t * q → ∀ n ∈ N, q * n * q⁻¹ ∈ N)
    (hQ : ∀ q : C, q * t = t * q → ∃ n ∈ N, ∃ s ∈ T, q = n * s) :
    N ≤ CFSG.oddCore C ∧ (∀ g : C, Odd (orderOf g) → g ∈ CFSG.oddCore C) ∧
      (∀ g : C, ∃ v ∈ CFSG.oddCore C, ∃ s ∈ T, g = v * s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S₀ : Sylow 2 C :=
    { toSubgroup := T
      isPGroup' := hT2
      is_maximal' := fun {Q} hQ hle => hmax Q hQ hle }
  let z0 : (S₀ : Subgroup C) := ⟨t, htT⟩
  have hzZ : z0 ∈ Subgroup.center (S₀ : Subgroup C) := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hTt s s.2)
  have hz : orderOf z0 = 2 := (Subgroup.orderOf_coe z0).symm.trans ht2
  obtain ⟨hdec, -⟩ := CFSG.Adapters.glauberman_zStar S₀ z0 hzZ hz (fun g hg => hweak g hg)
  have hNK : N ≤ CFSG.oddCore C := by
    have hMn : (CFSG.oddCore C ⊔ N).Normal := by
      refine ⟨fun m hm g => ?_⟩
      obtain ⟨c, hc, k, hk, rfl⟩ := hdec g
      have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      have hconj : ∀ x ∈ CFSG.oddCore C ⊔ N, c * x * c⁻¹ ∈ CFSG.oddCore C ⊔ N := by
        intro x hx
        have hle : CFSG.oddCore C ⊔ N ≤
            (CFSG.oddCore C ⊔ N).comap (MulAut.conj c).toMonoidHom :=
          sup_le (fun y hy => Subgroup.mem_sup_left ((CFSG.oddCore_normal C).conj_mem y hy c))
            (fun y hy => Subgroup.mem_sup_right (hNnorm c hct y hy))
        exact hle hx
      have hkm : k * m * k⁻¹ ∈ CFSG.oddCore C ⊔ N :=
        mul_mem (mul_mem (Subgroup.mem_sup_left hk) hm) (inv_mem (Subgroup.mem_sup_left hk))
      have e : c * k * m * (c * k)⁻¹ = c * (k * m * k⁻¹) * c⁻¹ := by group
      rw [e]
      exact hconj _ hkm
    have hModd : Odd (Nat.card (CFSG.oddCore C ⊔ N : Subgroup C)) :=
      zstar_odd_card_sup _ _ zstar_odd_card_oddCore hNodd
    exact le_sup_right.trans (le_sSup ⟨hMn, hModd⟩)
  have hdec2 : ∀ g : C, ∃ v ∈ CFSG.oddCore C, ∃ s ∈ T, g = v * s := by
    intro g
    obtain ⟨c, hc, k, hk, rfl⟩ := hdec g
    have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    obtain ⟨n, hn, s, hs, rfl⟩ := hQ c hct
    exact ⟨n * (s * k * s⁻¹), mul_mem (hNK hn) ((CFSG.oddCore_normal C).conj_mem k hk s), s, hs,
      by group⟩
  refine ⟨hNK, ?_, hdec2⟩
  intro g hg
  obtain ⟨v, hv, s, hs, rfl⟩ := hdec2 g
  obtain ⟨k, hk⟩ := hT2 ⟨s, hs⟩
  have hk' : s ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hπv : QuotientGroup.mk' (CFSG.oddCore C) v = 1 := (QuotientGroup.eq_one_iff v).mpr hv
  have hπeq : QuotientGroup.mk' (CFSG.oddCore C) (v * s) =
      QuotientGroup.mk' (CFSG.oddCore C) s := by
    rw [map_mul, hπv, one_mul]
  have hπs : orderOf (QuotientGroup.mk' (CFSG.oddCore C) s) ∣ 2 ^ k :=
    (orderOf_map_dvd _ s).trans (orderOf_dvd_of_pow_eq_one hk')
  have hπg : orderOf (QuotientGroup.mk' (CFSG.oddCore C) s) ∣ orderOf (v * s) := by
    rw [← hπeq]
    exact orderOf_map_dvd _ _
  have hone : orderOf (QuotientGroup.mk' (CFSG.oddCore C) s) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hg)) hπs hπg
  have hs1 : QuotientGroup.mk' (CFSG.oddCore C) (v * s) = 1 := by
    rw [hπeq]
    exact orderOf_eq_one_iff.mp hone
  exact (QuotientGroup.eq_one_iff _).mp hs1

theorem sylow2_of_isolated {G : Type} [Group G] [Finite G] (C₀ T₀ : Subgroup G) (t z : G)
    (hTC : T₀ ≤ C₀) (hT2 : IsPGroup 2 ↥T₀) (htT : t ∈ T₀) (ht2 : t * t = 1)
    (hTt : ∀ s ∈ T₀, s * t = t * s)
    (hSylQ : ∀ S : Subgroup G, S ≤ C₀ → IsPGroup 2 ↥S → T₀ ≤ S →
      (∀ s ∈ S, s * t = t * s) → S = T₀)
    (hinv : ∀ s ∈ T₀, s * s = 1 → s ≠ t → s ≠ 1 → IsConj z s) (hnc : ¬ IsConj z t) :
    ∀ S : Subgroup G, S ≤ C₀ → IsPGroup 2 ↥S → T₀ ≤ S → S = T₀ := by
  intro S hSC hS2 hTS
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS2.isNilpotent
  have hlt : T₀.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne ?_
    refine le_antisymm (fun x hx => ?_) hTS
    have hx' : (⟨x, hx⟩ : S) ∈ T₀.subgroupOf S := by rw [h]; exact Subgroup.mem_top _
    exact hx'
  obtain ⟨n, hn, hnH⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (T₀.subgroupOf S) hlt)
  have htS : (⟨t, hTS htT⟩ : S) ∈ T₀.subgroupOf S := htT
  have hs : (n : G) * t * (n : G)⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.mp hn _).mp htS
  have hss : ((n : G) * t * (n : G)⁻¹) * ((n : G) * t * (n : G)⁻¹) = 1 := by
    calc ((n : G) * t * (n : G)⁻¹) * ((n : G) * t * (n : G)⁻¹)
        = (n : G) * (t * t) * (n : G)⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hcomm : (n : G) * t = t * n := by
    by_contra hcomm
    have hst : (n : G) * t * (n : G)⁻¹ ≠ t := fun h => hcomm (by
      calc (n : G) * t = ((n : G) * t * (n : G)⁻¹) * n := by group
        _ = t * n := by rw [h])
    have hs1 : (n : G) * t * (n : G)⁻¹ ≠ 1 := fun h => hst (by
      have ht1 : t = 1 := by
        calc t = (n : G)⁻¹ * ((n : G) * t * (n : G)⁻¹) * n := by group
          _ = 1 := by rw [h]; group
      rw [h, ht1])
    exact hnc ((hinv _ hs hss hst hs1).trans (isConj_iff.mpr ⟨(n : G)⁻¹, by group⟩))
  have hS'le : T₀ ⊔ Subgroup.zpowers (n : G) ≤ S :=
    sup_le hTS (Subgroup.zpowers_le.mpr n.2)
  have hcen : T₀ ⊔ Subgroup.zpowers (n : G) ≤ Subgroup.centralizer {t} :=
    sup_le (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hTt s hs))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcomm))
  have hS'C : T₀ ⊔ Subgroup.zpowers (n : G) ≤ C₀ :=
    sup_le hTC (Subgroup.zpowers_le.mpr (hSC n.2))
  have hS'eq := hSylQ (T₀ ⊔ Subgroup.zpowers (n : G)) hS'C (hS2.to_le hS'le) le_sup_left
    (fun s hs => Subgroup.mem_centralizer_singleton_iff.mp (hcen hs))
  have hnT : (n : G) ∈ T₀ := hS'eq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (n : G))
  have _ := hT2
  exact hnH hnT

theorem normal_twoComplement_of_zstar {G : Type} [Group G] [Finite G] (C₀ T₀ : Subgroup G) (t : G)
    (hTC : T₀ ≤ C₀) (hT2 : IsPGroup 2 ↥T₀)
    (hmax : ∀ S : Subgroup G, S ≤ C₀ → IsPGroup 2 ↥S → T₀ ≤ S → S = T₀)
    (htT : t ∈ T₀) (ht2 : orderOf t = 2) (hTt : ∀ s ∈ T₀, s * t = t * s)
    (hweak : ∀ g ∈ C₀, g⁻¹ * t * g ∈ T₀ → g⁻¹ * t * g = t)
    (N : Subgroup G) (hNC : N ≤ C₀) (hNt : ∀ n ∈ N, n * t = t * n) (hNodd : Odd (Nat.card ↥N))
    (hNnorm : ∀ q ∈ C₀, q * t = t * q → ∀ n ∈ N, q * n * q⁻¹ ∈ N)
    (hQ : ∀ q ∈ C₀, q * t = t * q → ∃ n ∈ N, ∃ s ∈ T₀, q = n * s) :
    ∃ V : Subgroup G, V ≤ C₀ ∧ (∀ g ∈ C₀, ∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧ Odd (Nat.card ↥V) ∧
      N ≤ V ∧ (∀ g ∈ C₀, Odd (orderOf g) → g ∈ V) ∧
      (∀ g ∈ C₀, ∃ v ∈ V, ∃ s ∈ T₀, g = v * s) := by
  have _ := hNt
  have htC : t ∈ C₀ := hTC htT
  have hT2' : IsPGroup 2 ↥(T₀.subgroupOf C₀) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  have hmax' : ∀ S : Subgroup ↥C₀, IsPGroup 2 ↥S → T₀.subgroupOf C₀ ≤ S →
      S = T₀.subgroupOf C₀ := by
    intro S hS hle
    have hT : T₀ ≤ S.map C₀.subtype := fun x hx => ⟨⟨x, hTC hx⟩, hle hx, rfl⟩
    have heq := hmax (S.map C₀.subtype) (Subgroup.map_subtype_le S) (hS.map C₀.subtype) hT
    calc S = (S.map C₀.subtype).comap C₀.subtype :=
          (Subgroup.comap_map_eq_self_of_injective C₀.subtype_injective S).symm
      _ = T₀.subgroupOf C₀ := by rw [heq]; rfl
  obtain ⟨hNK, hodd, hdec⟩ := zstar_decomposition (C := ↥C₀) (T₀.subgroupOf C₀)
    (N.subgroupOf C₀) ⟨t, htC⟩ hT2' hmax' htT (by rw [Subgroup.orderOf_mk]; exact ht2)
    (fun s hs => Subtype.ext (hTt s hs))
    (fun g hg => Subtype.ext (hweak g g.2 hg))
    (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv])
    (fun q hq n hn => hNnorm q q.2 (congrArg Subtype.val hq) n hn)
    (fun q hq => by
      obtain ⟨n, hn, s, hs, hqns⟩ := hQ q q.2 (congrArg Subtype.val hq)
      exact ⟨⟨n, hNC hn⟩, hn, ⟨s, hTC hs⟩, hs, Subtype.ext hqns⟩)
  refine ⟨(CFSG.oddCore ↥C₀).map C₀.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨k, hk, rfl⟩
    exact ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, (CFSG.oddCore_normal ↥C₀).conj_mem k hk _, rfl⟩
  · rw [Subgroup.card_map_of_injective C₀.subtype_injective]
    exact zstar_odd_card_oddCore
  · intro n hn
    exact ⟨⟨n, hNC hn⟩, hNK hn, rfl⟩
  · intro g hg hgodd
    exact ⟨⟨g, hg⟩, hodd ⟨g, hg⟩ (by rwa [Subgroup.orderOf_mk]), rfl⟩
  · intro g hg
    obtain ⟨v, hv, s, hs, hgvs⟩ := hdec ⟨g, hg⟩
    exact ⟨v, ⟨v, hv, rfl⟩, s, hs, congrArg Subtype.val hgvs⟩

end CFSG.GH74.GLS.SP.Local
