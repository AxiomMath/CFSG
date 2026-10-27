module

public import CFSG.GH74.GLS.C3.Layer1.Th2P85AltSE

public section

namespace CFSG.GH74.GLS.Th2.P85.Alt

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85
  CFSG.GH74.GLS.TwoThin

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
theorem card_centralizer_M_dvd {t : G} (htM : t ∈ M) :
    Nat.card ↥(centralizer ({(⟨t, htM⟩ : ↥M)} : Set ↥M)) ∣
      Nat.card ↥(centralizer ({t} : Set G)) := by
  let ι : ↥(centralizer ({(⟨t, htM⟩ : ↥M)} : Set ↥M)) →* ↥(centralizer ({t} : Set G)) :=
    ((M.subtype.comp (centralizer ({(⟨t, htM⟩ : ↥M)} : Set ↥M)).subtype).codRestrict
      (centralizer ({t} : Set G)) fun c => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 c.2))
  have hinj : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(centralizer ({t} : Set G)) => (z : G)) hab
  exact Subgroup.card_dvd_of_injective ι hinj

theorem not_isConj_of_two_adic' {x t : G} (hxM : x ∈ M) (htM : t ∈ M) (hx2 : orderOf x = 2)
    (ht2 : orderOf t = 2) (hCx : centralizer ({x} : Set G) ≤ M) {k : ℕ}
    (hk1 : 2 ^ k ∣ Nat.card ↥(centralizer ({barMk ↥M (⟨t, htM⟩ : ↥M)} : Set (Mb M))))
    (hk2 : ¬ 2 ^ k ∣ Nat.card ↥(centralizer ({barMk ↥M (⟨x, hxM⟩ : ↥M)} : Set (Mb M)))) :
    ¬ IsConj x t := by
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have hcard : Nat.card ↥(centralizer ({t} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
    have h := Stage1.Thm2.Recip.map_centralizer_singleton_conj x g
    rw [hg] at h
    rw [← h, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  obtain ⟨rt, hrt, ht⟩ := card_centralizer_barMk (M := M)
    (show orderOf (⟨t, htM⟩ : ↥M) = 2 from (Subgroup.orderOf_mk t htM).trans ht2)
  obtain ⟨rx, hrx, hx⟩ := card_centralizer_barMk (M := M)
    (show orderOf (⟨x, hxM⟩ : ↥M) = 2 from (Subgroup.orderOf_mk x hxM).trans hx2)
  have h1 : 2 ^ k ∣ Nat.card ↥(centralizer ({(⟨t, htM⟩ : ↥M)} : Set ↥M)) := by
    rw [ht]
    exact hk1.mul_left rt
  have h2 := h1.trans (card_centralizer_M_dvd htM)
  rw [hcard, card_centralizer_of_le hxM hCx, hx] at h2
  have hcop : Nat.Coprime (2 ^ k) rx := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hrx)
  exact hk2 (hcop.dvd_of_dvd_mul_left h2)

theorem fusion_control {m : ℕ} (hm : m = 9 ∨ m = 10 ∨ m = 11)
    (e : Mb M ≃* alternatingGroup (Fin m)) {x v : G} (hxM : x ∈ M) (hvM : v ∈ M)
    (hx2 : orderOf x = 2) (hv2 : orderOf v = 2)
    (h5 : 5 ∣ Nat.card ↥(centralizer ({barMk ↥M (⟨x, hxM⟩ : ↥M)} : Set (Mb M))))
    {W : Subgroup G} (hW : IsSylowOf 2 W M) (hvc : ∀ w ∈ W, w * v = v * w)
    (hCx : centralizer ({x} : Set G) ≤ M) :
    ∀ g : G, g * x * g⁻¹ ∈ M → g ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg
  have hxb2 : orderOf (barMk ↥M ⟨x, hxM⟩) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk x hxM).trans hx2)
  have hvb2 : orderOf (barMk ↥M ⟨v, hvM⟩) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk v hvM).trans hv2)
  have hMM : imgM M M = ⊤ := by
    unfold imgM
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ barMk_surjective
  have hWb := (isSylowOf_imgM_of_le (le_refl M) hW).card_eq
  rw [hMM, Subgroup.card_top] at hWb
  have hvcb : ∀ w ∈ imgM M W, w * barMk ↥M ⟨v, hvM⟩ = barMk ↥M ⟨v, hvM⟩ * w := by
    intro w hw
    obtain ⟨m', hm', rfl⟩ := mem_imgM_iff.1 hw
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hvc _ hm')
  obtain ⟨-, hcls, k, hk1, hk2⟩ := Th2.AltInv.alt_facts hm e hxb2 h5 hWb hvb2 hvcb
  have ht2 : orderOf (g * x * g⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) x
    simpa [MulAut.conj_apply] using this.trans hx2
  have ht2M : orderOf (⟨g * x * g⁻¹, hg⟩ : ↥M) = 2 :=
    (Subgroup.orderOf_mk _ hg).trans ht2
  have hx2M : orderOf (⟨x, hxM⟩ : ↥M) = 2 := (Subgroup.orderOf_mk x hxM).trans hx2
  rcases hcls _ (orderOf_barMk ht2M) with h | h
  · obtain ⟨m', hm'⟩ := exists_conj_of_barMk_conj ht2M hx2M h
    have hm'' : (m' : G) * x * (m' : G)⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hm'
    have hc : (m' : G)⁻¹ * g ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc (m' : G)⁻¹ * g * x = (m' : G)⁻¹ * (g * x * g⁻¹) * g := by group
        _ = (m' : G)⁻¹ * ((m' : G) * x * (m' : G)⁻¹) * g := by rw [hm'']
        _ = x * ((m' : G)⁻¹ * g) := by group
    have h1 := hCx hc
    have h2 : g = (m' : G) * ((m' : G)⁻¹ * g) := by group
    rw [h2]
    exact M.mul_mem m'.2 h1
  · exfalso
    have hcardt : Nat.card ↥(centralizer ({barMk ↥M (⟨g * x * g⁻¹, hg⟩ : ↥M)} : Set (Mb M))) =
        Nat.card ↥(centralizer ({barMk ↥M (⟨v, hvM⟩ : ↥M)} : Set (Mb M))) := by
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      have h3 := Stage1.Thm2.Recip.map_centralizer_singleton_conj
        (barMk ↥M (⟨g * x * g⁻¹, hg⟩ : ↥M)) c
      rw [hc] at h3
      rw [← h3, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    refine not_isConj_of_two_adic' hxM hg hx2 ht2 hCx (k := k) (by rw [hcardt]; exact hk1) hk2
      (isConj_iff.2 ⟨g, rfl⟩)

theorem isSylowOf_top_of_fusion {x : G} {W : Subgroup G} (hW : IsSylowOf 2 W M) (hxW : x ∈ W)
    (hF : ∀ g : G, g * x * g⁻¹ ∈ M → g ∈ M) : IsSylowOf 2 W ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hWP⟩ := hW.isPGroup.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup G) = 2 ^ (Nat.card (⊤ : Subgroup G)).factorization 2 := by
    rw [Subgroup.card_top]
    exact Sylow.card_eq_multiplicity P
  have hWeq : W = (P : Subgroup G) := by
    by_contra hne
    have hnil : Group.IsNilpotent ↥(P : Subgroup G) := (P.isPGroup').isNilpotent
    set W' : Subgroup ↥(P : Subgroup G) := W.subgroupOf (P : Subgroup G) with hW'
    have hlt : W' < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hne ?_
      apply le_antisymm hWP
      intro p hp
      have : (⟨p, hp⟩ : ↥(P : Subgroup G)) ∈ W' := by rw [htop]; exact Subgroup.mem_top _
      exact this
    obtain ⟨g, hgN, hgW⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent W' hlt)
    have hxW' : (⟨x, hWP hxW⟩ : ↥(P : Subgroup G)) ∈ W' := hxW
    have h1 := (Subgroup.mem_normalizer_iff.1 hgN _).1 hxW'
    have h2 : (g : G) * x * (g : G)⁻¹ ∈ W := h1
    have hgM : (g : G) ∈ M := hF _ (hW.le h2)
    have h3 : W ⊔ zpowers (g : G) ≤ (P : Subgroup G) := sup_le hWP (zpowers_le.2 g.2)
    have h4 : IsPGroup 2 ↥(W ⊔ zpowers (g : G)) := P.isPGroup'.to_le h3
    have h5 := hW.eq_of_le (le_sup_left : W ≤ W ⊔ zpowers (g : G))
      (sup_le hW.le (zpowers_le.2 hgM)) h4
    apply hgW
    have : (g : G) ∈ W := by
      rw [← h5]
      exact Subgroup.mem_sup_right (mem_zpowers _)
    exact this
  rw [hWeq]
  exact isSylowOf_of_card le_top hPcard

end CFSG.GH74.GLS.Th2.P85.Alt
