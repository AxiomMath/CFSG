module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootOdd
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupCons
public import CFSG.LocalAnalysis.OddStandard.AltStdSecHer

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal CFSG.ComponentClassification.RestrictedStd.Spor

section Abstract

variable {H : Type} [Group H] [Finite H]

theorem exists_fusion_of_wreath {t β : H} {B : Subgroup (H ⧸ CFSG.oddCore H)} {m : ℕ}
    (hm : 5 ≤ m) (ht : t * t = 1) (hβ : β * β = 1) (hcomm : β * t = t * β)
    (hW : WreathOutcome (QuotientGroup.mk t : H ⧸ CFSG.oddCore H) B m)
    (hβB : (QuotientGroup.mk β : H ⧸ CFSG.oddCore H) ∈ B) :
    ∃ h' : H, h' * t * h'⁻¹ = t * β := by
  obtain ⟨K, hKc, hKne, -, ⟨eK⟩, hdiag⟩ := hW
  set P := CFSG.oddCore H with hP
  set tb : H ⧸ P := QuotientGroup.mk t with htb
  set K' : Subgroup (H ⧸ P) := K.map (MulAut.conj tb).toMonoidHom with hK'
  have hK'c : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv _ hKc
  have hKK' : ⁅K, K'⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hKc hK'c with h1 | h1
    · exact absurd h1.symm hKne
    · exact h1
  have hKle : K ≤ centralizer (K' : Set (H ⧸ P)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKK'
  have htb2 : tb * tb = 1 := by
    rw [htb, ← QuotientGroup.mk_mul, ht]; rfl
  have htb1 : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right htb2
  have hβB' : (QuotientGroup.mk β : H ⧸ P) ∈ (B : Set (H ⧸ P)) := hβB
  rw [hdiag] at hβB'
  obtain ⟨k, hkK, hk⟩ := hβB'
  set k' : H ⧸ P := tb * k * tb⁻¹ with hk'def
  have hk'K' : k' ∈ K' := ⟨k, hkK, by simp [hk'def, MulAut.conj_apply]⟩
  have hkk' : k * k' = k' * k := (mem_centralizer_iff.1 (hKle hkK) k' hk'K').symm
  have hcenter : center K = ⊥ := center_eq_bot_of_alt (by omega) eK
  have hKinf : ∀ x : H ⧸ P, x ∈ K → x ∈ K' → x = 1 := by
    intro x hxK hxK'
    have hx : (⟨x, hxK⟩ : K) ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro a
      apply Subtype.ext
      exact (mem_centralizer_iff.1 (hKle a.2) x hxK').symm
    rw [hcenter, Subgroup.mem_bot] at hx
    exact congrArg Subtype.val hx
  have hβ2 : (QuotientGroup.mk β : H ⧸ P) * QuotientGroup.mk β = 1 := by
    rw [← QuotientGroup.mk_mul, hβ]; rfl
  have hkk2 : k * k = 1 := by
    have h1 : (k * k') * (k * k') = 1 := by rw [← hk]; exact hβ2
    have h2 : (k * k) * (k' * k') = 1 := by
      calc (k * k) * (k' * k') = k * (k * k') * k' := by group
        _ = k * (k' * k) * k' := by rw [hkk']
        _ = (k * k') * (k * k') := by group
        _ = 1 := h1
    have hk'k'K' : k' * k' ∈ K' := mul_mem hk'K' hk'K'
    have h3 : k * k = (k' * k')⁻¹ := eq_inv_of_mul_eq_one_left h2
    exact hKinf _ (mul_mem hkK hkK) (by rw [h3]; exact inv_mem hk'k'K')
  have hk1 : k⁻¹ = k := inv_eq_of_mul_eq_one_right hkk2
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective k
  have hu2 : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
    calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have hv2 : (t * β) * (t * β) = 1 := by
    calc (t * β) * (t * β) = t * (β * t) * β := by group
      _ = t * (t * β) * β := by rw [hcomm]
      _ = (t * t) * (β * β) := by group
      _ = 1 := by rw [ht, hβ, one_mul]
  have hπ : (QuotientGroup.mk (t * β) : H ⧸ P) = QuotientGroup.mk (x * t * x⁻¹) := by
    have e1 : (QuotientGroup.mk (t * β) : H ⧸ P) = (QuotientGroup.mk β : H ⧸ P) * tb := by
      rw [← hcomm, QuotientGroup.mk_mul]
    have e2 : (QuotientGroup.mk (x * t * x⁻¹) : H ⧸ P) = k * tb * k⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx]
    rw [e1, e2, hk, hk1, hk'def, htb1]
    calc k * (tb * k * tb) * tb = k * tb * k * (tb * tb) := by group
      _ = k * tb * k := by rw [htb2, mul_one]
  have hvu : (t * β)⁻¹ * (x * t * x⁻¹) ∈ P := QuotientGroup.eq.1 hπ
  have hv1 : (t * β)⁻¹ = t * β := inv_eq_of_mul_eq_one_right hv2
  rw [hv1] at hvu
  obtain ⟨r, -, hr⟩ := exists_conj_of_involutions_of_mul_mem
    (fun y hy => orderOf_odd_of_mem_oddCore hy) hu2 hv2 hvu
  refine ⟨r * x, ?_⟩
  calc r * x * t * (r * x)⁻¹ = r * (x * t * x⁻¹) * r⁻¹ := by group
    _ = t * β := hr

end Abstract

section Root

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

@[expose] def secImage (R B : Subgroup G) : Subgroup (Sec G R) :=
  (B.subgroupOf (centralizer (R : Set G))).map
    (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (R : Set G))))

structure RootData (L : Subgroup G) (z : G) (R B : Subgroup G) (m : ℕ) : Prop where
  hz : z ∈ centralizer (R : Set G)
  shape : ExactShape (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer (R : Set G))) : Sec G R)
    (secImage R B) m
  cent : ∀ c : ↥(centralizer (R : Set G)), (c : G) ∈ L →
    c ∈ B.subgroupOf (centralizer (R : Set G)) ⊔ CFSG.oddCore ↥(centralizer (R : Set G))

variable {R B : Subgroup G} {m : ℕ}

omit [Finite G] in
theorem RootData.mk_mem (hRD : RootData L z R B m) (c : ↥(centralizer (R : Set G)))
    (hc : (c : G) ∈ L) : (QuotientGroup.mk c : Sec G R) ∈ secImage R B := by
  have h1 := Subgroup.mem_map_of_mem
    (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (R : Set G)))) (hRD.cent c hc)
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h1
  exact h1

theorem centralizer_sec_le (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (hRD : RootData L z R B m) :
    centralizer ({(QuotientGroup.mk ⟨z, hRD.hz⟩ : Sec G R)} : Set (Sec G R)) ≤
      secImage R B ⊔ zpowers (QuotientGroup.mk ⟨z, hRD.hz⟩ : Sec G R) := by
  intro x hx
  set t₀ : ↥(centralizer (R : Set G)) := ⟨z, hRD.hz⟩ with ht₀
  have ht₀2 : t₀ * t₀ = 1 := Subtype.ext d.mul_self
  obtain ⟨c, hc, rfl⟩ := exists_centralizer_preimage
    (P := CFSG.oddCore ↥(centralizer (R : Set G)))
    (fun y hy => orderOf_odd_of_mem_oddCore hy) ht₀2 hx
  have hcz : (c : G) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hc ⊢
    exact congrArg Subtype.val hc
  obtain ⟨l, hl, q, hq, hlq⟩ := (mem_sup_iff_mul d).1 (hE hcz)
  rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with rfl | rfl
  · rw [mul_one] at hlq
    exact mem_sup_left (hRD.mk_mem c (by rw [← hlq]; exact hl))
  · have hc₀ : ((c * t₀⁻¹ : ↥(centralizer (R : Set G))) : G) ∈ L := by
      have : ((c * t₀⁻¹ : ↥(centralizer (R : Set G))) : G) = l := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hlq]
        simp [ht₀]
      rw [this]
      exact hl
    have hmk : (QuotientGroup.mk c : Sec G R) =
        QuotientGroup.mk (c * t₀⁻¹) * QuotientGroup.mk t₀ := by
      rw [← QuotientGroup.mk_mul]
      congr 1
      group
    rw [hmk]
    exact mul_mem_sup (hRD.mk_mem _ hc₀) (mem_zpowers _)

omit [Finite G] in
theorem center_eq_bot_of_simple_nonabelian (hs : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a) :
    center G = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm

theorem centralizer_ne_top_of_ne_one (h : Setting G L n) (hR : ∃ r ∈ R, r ≠ 1) :
    centralizer (R : Set G) ≠ ⊤ := by
  intro htop
  obtain ⟨r, hr, hr1⟩ := hR
  have hc : r ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer (R : Set G) := htop ▸ Subgroup.mem_top g
    exact (mem_centralizer_iff.1 this r hr).symm
  rw [center_eq_bot_of_simple_nonabelian h.std.simple h.std.nonab, Subgroup.mem_bot] at hc
  exact hr1 hc

theorem zstar_or_wreath_of_rootData (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (hRD : RootData L z R B m) (hm : 9 ≤ m)
    (hR1 : ∃ r ∈ R, r ≠ 1) :
    IsZStar R z ∨ WreathOutcome (QuotientGroup.mk ⟨z, hRD.hz⟩ : Sec G R) (secImage R B) m := by
  have hKcat : CFSG.SectionRank.IsKGroupCat (Sec G R) :=
    isKGroupCat_sec (isKGroupCat_of_kProper h.std.kProper) (centralizer_ne_top_of_ne_one h hR1)
  have hO : CFSG.oddCore (Sec G R) = ⊥ := oddCore_sec_eq_bot R
  rcases section_dichotomy hO hRD.shape (by omega) with h1 | h2 | h3
  · exact Or.inl (isZStar_iff_mem_center.2 ⟨hRD.hz, h1⟩)
  · exact Or.inr h2
  · exact (false_of_almostSimple_shape_one hlookup hHN hFour hKcat hO hRD.shape hm h3
      (centralizer_sec_le d hQ2 hE hRD)).elim

theorem wreath_fusion_of_rootData (h : Setting G L n) (d : Cyc L Q z) (hRD : RootData L z R B m)
    (hm : 5 ≤ m)
    (hW : WreathOutcome (QuotientGroup.mk ⟨z, hRD.hz⟩ : Sec G R) (secImage R B) m)
    {b : G} (hbL : b ∈ L) (hbC : b ∈ centralizer (R : Set G)) (hb2 : orderOf b = 2) :
    ∃ h' ∈ centralizer (R : Set G), h' * z * h'⁻¹ = z * b := by
  have hbz : b * z = z * b := mem_centralizer_singleton_iff.1 (le_centralizer_single h d hbL)
  have hb2' : b * b = 1 := by rw [← sq, ← hb2]; exact pow_orderOf_eq_one b
  obtain ⟨h', hh'⟩ := exists_fusion_of_wreath
    (t := (⟨z, hRD.hz⟩ : ↥(centralizer (R : Set G)))) (β := ⟨b, hbC⟩) hm
    (Subtype.ext d.mul_self) (Subtype.ext hb2') (Subtype.ext hbz) hW
    (hRD.mk_mem ⟨b, hbC⟩ hbL)
  exact ⟨h', h'.2, congrArg Subtype.val hh'⟩

end Root

end CFSG.OddStandard.AltStdSec
