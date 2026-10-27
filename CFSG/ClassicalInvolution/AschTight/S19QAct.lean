module

public import CFSG.ClassicalInvolution.AschTight.S1911P3g

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

@[expose] def oddPart (K : Subgroup G) (a : G) :
    Subgroup ↥(S1911.conjGen (S1911.perfectCoreIn K a)) :=
  (S1911.perfectCoreIn K a).subgroupOf (S1911.conjGen (S1911.perfectCoreIn K a)) ⊓
    (oddCoreOf K).comap ((Subgroup.centralizer ({a} : Set G)).subtype.comp
      (S1911.conjGen (S1911.perfectCoreIn K a)).subtype)

theorem odd_natCard_oddPart (K : Subgroup G) (a : G) : Odd (Nat.card (oddPart K a)) := by
  set φ := (Subgroup.centralizer ({a} : Set G)).subtype.comp
    (S1911.conjGen (S1911.perfectCoreIn K a)).subtype with hφ
  have hinj : Function.Injective φ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have hle : (oddPart K a).map φ ≤ oddCoreOf K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  have hcard : Nat.card ((oddPart K a).map φ) = Nat.card (oddPart K a) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ _ hinj).toEquiv).symm
  rw [← hcard]
  exact (oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_dvd_of_le hle)

omit [Finite G] in
theorem conj_mem_oddCoreOf {K : Subgroup G} {k x : G} (hk : k ∈ K) (hx : x ∈ oddCoreOf K) :
    k * x * k⁻¹ ∈ oddCoreOf K := by
  obtain ⟨hxK, hxO⟩ := mem_oddCoreOf_iff.mp hx
  refine mem_oddCoreOf_iff.mpr ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), ?_⟩
  have := (classicalInvolutionOddCore_normal ↥K).conj_mem _ hxO ⟨k, hk⟩
  convert this using 1

theorem map_oddPart_le_oddCoreOf (K : Subgroup G) (a : G) :
    (oddPart K a).map (QuotientGroup.mk'
        (classicalInvolutionOddCore ↥(S1911.conjGen (S1911.perfectCoreIn K a)))) ≤
      oddCoreOf (S1911.secImg (S1911.conjGen (S1911.perfectCoreIn K a))
        (S1911.perfectCoreIn K a)) := by
  set Y₁ := S1911.conjGen (S1911.perfectCoreIn K a) with hY₁
  set N := (oddPart K a).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₁)) with hN
  set H := S1911.secImg Y₁ (S1911.perfectCoreIn K a) with hH
  have hNH : N ≤ H := Subgroup.map_mono inf_le_left
  have hnorm : (N.subgroupOf H).Normal := by
    constructor
    intro n hn h
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨x, hx, hxn⟩ := hn
    obtain ⟨y, hy, hyh⟩ := h.2
    have hyK : (((y : ↥(Subgroup.centralizer ({a} : Set G))) : G)) ∈ K :=
      (S1911.perfectResidualOf_le _ (Subgroup.mem_subgroupOf.mp
        (Subgroup.mem_subgroupOf.mp hy))).1
    refine ⟨y * x * y⁻¹, ⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hx.1) (Subgroup.inv_mem _ hy)
    · exact conj_mem_oddCoreOf hyK hx.2
    · rw [map_mul, map_mul, map_inv, hxn, hyh]
      rfl
  have hodd : Odd (Nat.card (N.subgroupOf H)) := by
    have h1 : Nat.card (N.subgroupOf H) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
    rw [h1]
    exact (odd_natCard_oddPart K a).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hle : N.subgroupOf H ≤ classicalInvolutionOddCore ↥H := le_sSup ⟨hnorm, hodd⟩
  intro n hn
  exact mem_oddCoreOf_iff.mpr ⟨hNH hn, hle (Subgroup.mem_subgroupOf.mpr hn)⟩

section Fix

variable {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W : Subgroup G}

open scoped commutatorElement

theorem secAct_fixes_of_mem_cStar (hd : Sec19Data p f K z S W) {a : G}
    (hO : oddCoreOf (S1911.secImg (S1911.conjGen (S1911.perfectCoreIn K a))
      (S1911.perfectCoreIn K a)) = ⊥)
    {y : ↥(Subgroup.centralizer ({a} : Set G))} (hyz : (y : G) * z = z * (y : G))
    (hyK : (y : G) ∈ centralizerModOdd ⊤ K) :
    ∀ x ∈ S1911.secImg (S1911.conjGen (S1911.perfectCoreIn K a)) (S1911.perfectCoreIn K a),
      @S1911.secAct _ _ (S1911.conjGen (S1911.perfectCoreIn K a)) (S1911.conjGen_normal _) y x =
        x := by
  have := S1911.conjGen_normal (S1911.perfectCoreIn K a)
  have hyN := S1911.mem_normalizer_perfectCoreIn hd hyz
  rintro _ ⟨k, hk, rfl⟩
  rw [QuotientGroup.mk'_apply, S1911.secAct_mk]
  set c : ↥(S1911.conjGen (S1911.perfectCoreIn K a)) := MulAut.conjNormal y k * k⁻¹ with hc
  have hkL : (k : ↥(Subgroup.centralizer ({a} : Set G))) ∈ S1911.perfectCoreIn K a :=
    Subgroup.mem_subgroupOf.mp hk
  have hkK : ((k : ↥(Subgroup.centralizer ({a} : Set G))) : G) ∈ K :=
    (S1911.perfectResidualOf_le _ (Subgroup.mem_subgroupOf.mp hkL)).1
  have hc1 : c ∈ (S1911.perfectCoreIn K a).subgroupOf
      (S1911.conjGen (S1911.perfectCoreIn K a)) := by
    rw [Subgroup.mem_subgroupOf]
    have h1 : ((MulAut.conjNormal y k : ↥(S1911.conjGen (S1911.perfectCoreIn K a))) :
        ↥(Subgroup.centralizer ({a} : Set G))) = y * k * y⁻¹ := MulAut.conjNormal_apply y k
    change ((MulAut.conjNormal y k : ↥(S1911.conjGen (S1911.perfectCoreIn K a))) :
        ↥(Subgroup.centralizer ({a} : Set G))) * (k : ↥(Subgroup.centralizer ({a} : Set G)))⁻¹ ∈
      S1911.perfectCoreIn K a
    rw [h1]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hyN _).mp hkL)
      (Subgroup.inv_mem _ hkL)
  have hc2 : c ∈ (oddCoreOf K).comap ((Subgroup.centralizer ({a} : Set G)).subtype.comp
      (S1911.conjGen (S1911.perfectCoreIn K a)).subtype) := by
    change ((((MulAut.conjNormal y k : ↥(S1911.conjGen (S1911.perfectCoreIn K a))) :
        ↥(Subgroup.centralizer ({a} : Set G))) : G) *
        ((k : ↥(Subgroup.centralizer ({a} : Set G))) : G)⁻¹) ∈ oddCoreOf K
    rw [MulAut.conjNormal_apply]
    have h2 := hyK.2.2.2 _ hkK
    rw [commutatorElement_def] at h2
    simpa [mul_assoc] using h2
  have hcO : c ∈ oddPart K a := Subgroup.mem_inf.mpr ⟨hc1, hc2⟩
  have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥(S1911.conjGen
      (S1911.perfectCoreIn K a))) c) ∈ oddCoreOf (S1911.secImg (S1911.conjGen
        (S1911.perfectCoreIn K a)) (S1911.perfectCoreIn K a)) :=
    map_oddPart_le_oddCoreOf K a ⟨c, hcO, rfl⟩
  rw [hO, Subgroup.mem_bot, QuotientGroup.mk'_apply, hc, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, mul_inv_eq_one] at h1
  exact h1

end Fix

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
