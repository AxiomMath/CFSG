module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7NoSplit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLSecV
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTri
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Cov
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
open scoped MatrixGroups

section Transport

variable {G : Type} [Group G]

theorem conjSub_inv_mem_twinSet {R : Subgroup G} (g : G) {J : Subgroup G}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R))) :
    conjSub g⁻¹ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
  rw [← conjSub_tightCore] at hJ
  obtain ⟨⟨h, rfl⟩, z, hz, hzJ⟩ := hJ
  refine ⟨⟨g⁻¹ * h * g, ?_⟩, g⁻¹ * z * g⁻¹⁻¹, ?_, hzJ.conj g⁻¹⟩
  · show conjSub (g⁻¹ * h * g) (tightCore R) = conjSub g⁻¹ (conjSub h (conjSub g (tightCore R)))
    rw [conjSub_mul, conjSub_mul]
  · have := hz.conj g⁻¹
    rwa [conjSub_inv_conjSub] at this

theorem longFundSetE3_conjSub {R : Subgroup G} {t : G} (h : LongFundSetE3 R t) (g : G) :
    LongFundSetE3 (conjSub g R) (g * t * g⁻¹) := by
  obtain ⟨Λ, hΛ, hcomm, heqv⟩ := h
  refine ⟨fun J => conjSub g (Λ (conjSub g⁻¹ J)), fun J hJ => ?_, fun J hJ J' hJ' hne => ?_,
    fun J hJ c hc => ?_⟩
  · obtain ⟨h1, h2⟩ := hΛ _ (conjSub_inv_mem_twinSet g hJ)
    refine ⟨?_, h2.conj g⟩
    have := conjSub_mono (n := g) h1
    rwa [conjSub_conjSub_inv] at this
  · intro x hx y hy
    have hne' : conjSub g⁻¹ J ≠ conjSub g⁻¹ J' := fun h => hne (conjSub_injective g⁻¹ h)
    rw [mem_conjSub_iff] at hx hy
    have h1 := conjSub_inv_mem_twinSet g hJ
    have h2 := conjSub_inv_mem_twinSet g hJ'
    have := hcomm _ h1 _ h2 hne' _ hx _ hy
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = y * x := by group
  · have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      calc g⁻¹ * c * g * t = g⁻¹ * (c * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * c) * g := by rw [hc]
        _ = t * (g⁻¹ * c * g) := by group
    have key := heqv _ (conjSub_inv_mem_twinSet g hJ) _ hc'
    show conjSub c (conjSub g (Λ (conjSub g⁻¹ J))) = conjSub g (Λ (conjSub g⁻¹ (conjSub c J)))
    calc conjSub c (conjSub g (Λ (conjSub g⁻¹ J)))
        = conjSub g (conjSub (g⁻¹ * c * g) (Λ (conjSub g⁻¹ J))) := by
          rw [← conjSub_mul, ← conjSub_mul, show g * (g⁻¹ * c * g) = c * g by group]
      _ = conjSub g (Λ (conjSub (g⁻¹ * c * g) (conjSub g⁻¹ J))) := by rw [key]
      _ = conjSub g (Λ (conjSub g⁻¹ (conjSub c J))) := by
          rw [← conjSub_mul, ← conjSub_mul, show g⁻¹ * c * g * g⁻¹ = g⁻¹ * c by group]

end Transport

section Split

theorem sl2Three_eq_of_conj_eq : ∀ a b : SL(2, ZMod 3), a ^ 3 = 1 → b ^ 3 = 1 →
    (∀ q : SL(2, ZMod 3), q ^ 4 = 1 → a * q * a⁻¹ = b * q * b⁻¹) → a = b := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : conjSub g H ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine Generic.mem_normalizer_of_conjSub_eq (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem exists_split_of_classical {P L : Subgroup G} {z c : G} (hP8 : Nat.card P = 8)
    (hPL : P ≤ L) (hL : IsClassicalMember3 L z) (hc2 : c * c = 1) (hcP : ∀ x ∈ P, c * x = x * c)
    (hcL : conjSub c L = L) :
    ∃ w ∈ L, Odd (orderOf w) ∧ (∀ x ∈ P, w * x * w⁻¹ ∈ P) ∧ (∃ x ∈ P, w * x ≠ x * w) ∧
      w * c = c * w := by
  obtain ⟨ψ, hψs, hψk⟩ := hL.exists_hom
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥L)) := hL.odd_card_oddCore
  have hP2 : IsPGroup 2 ↥P := IsPGroup.of_card (n := 3) (by rw [hP8]; norm_num)
  set A : Subgroup ↥L := P.subgroupOf L
  have hAP : ↥A ≃* ↥P := Subgroup.subgroupOfEquivOfLe hPL
  have hA2 : IsPGroup 2 ↥A := hP2.of_equiv hAP.symm
  have hAcard : Nat.card ↥A = 8 := by rw [Nat.card_congr hAP.toEquiv, hP8]
  have hAN : A ⊓ classicalInvolutionOddCore ↥L = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd _ hA2 le_rfl
      (hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hψinj : ∀ y₁ ∈ A, ∀ y₂ ∈ A, ψ y₁ = ψ y₂ → y₁ = y₂ := by
    intro y₁ h₁ y₂ h₂ h
    have h1 : y₁⁻¹ * y₂ ∈ A ⊓ classicalInvolutionOddCore ↥L :=
      ⟨A.mul_mem (A.inv_mem h₁) h₂, (hψk _).mp (by rw [map_mul, map_inv, h, inv_mul_cancel])⟩
    rw [hAN, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  have hψAcard : Nat.card ↥(A.map ψ) = 8 := by
    have : Nat.card ↥(A.map ψ) = Nat.card ↑(ψ '' (A : Set ↥L)) := by
      rw [← Subgroup.coe_map]
      rfl
    rw [this, Nat.card_image_of_injOn (fun a ha a' ha' h => hψinj a ha a' ha' h)]
    exact hAcard
  have hψA' : A.map ψ = sl2ThreeQ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hψAcard, natCard_sl2ThreeQ])
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_sl2ThreeQ_iff]
    refine TwinSecXg.sl2_pow_eight_imp_pow_four _ ?_
    have h1 : (⟨a, ha⟩ : ↥A) ^ Nat.card ↥A = 1 := pow_card_eq_one'
    rw [hAcard] at h1
    have h2 : a ^ 8 = 1 := by simpa using congrArg Subtype.val h1
    rw [← map_pow, h2, map_one]
  have hψA : ∀ q : SL(2, ZMod 3), q ∈ A.map ψ ↔ q ^ 4 = 1 := fun q => by
    rw [hψA', mem_sl2ThreeQ_iff]
  obtain ⟨g₀, hg₀⟩ := sl2Three_exists_orderOf_three
  have hg₀3 : g₀ ^ 3 = 1 := by
    have := pow_orderOf_eq_one g₀
    rwa [hg₀] at this
  obtain ⟨q₀, hq₀4, hgq⟩ : ∃ q : SL(2, ZMod 3), q ^ 4 = 1 ∧ g₀ * q ≠ q * g₀ := by
    by_contra hcon
    push Not at hcon
    have h1 : g₀ = 1 := sl2Three_eq_of_conj_eq _ _ hg₀3 (one_pow 3) fun q hq => by
      rw [hcon q hq]
      group
    rw [h1, orderOf_one] at hg₀
    exact absurd hg₀ (by norm_num)
  obtain ⟨y₀, hy₀⟩ := hψs g₀
  have hcL' : ∀ x ∈ L, c * x * c⁻¹ ∈ L := fun x hx => by
    have := conj_mem_conjSub (n := c) hx
    rwa [hcL] at this
  let φ : ↥L →* ↥L :=
    ((MulAut.conj c).toMonoidHom.comp L.subtype).codRestrict L (fun x => hcL' x x.2)
  have hφ : ∀ x : ↥L, (φ x : G) = c * x * c⁻¹ := fun _ => rfl
  have hOc : conjSub c (oddCoreOf L) = oddCoreOf L := by
    rw [← Asc77.Thompson.oddCoreOf_conjSub_eq, hcL]
  have hker : ψ.ker ≤ (ψ.comp φ).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : (x : G) ∈ oddCoreOf L := mem_oddCoreOf_iff.mpr ⟨x.2, (hψk x).mp hx⟩
    have h2 : c * (x : G) * c⁻¹ ∈ oddCoreOf L := by
      have := conj_mem_conjSub (n := c) h1
      rwa [hOc] at this
    obtain ⟨_, h4⟩ := mem_oddCoreOf_iff.mp h2
    exact (hψk (φ x)).mpr h4
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SL(2, ZMod 3) →* SL(2, ZMod 3), ∀ x : ↥L, ρ (ψ x) = ψ (φ x) :=
    ⟨_, MonoidHom.liftOfRightInverse_comp_apply ψ _ (Function.rightInverse_surjInv hψs)
      ⟨ψ.comp φ, hker⟩⟩
  have hρQ : ∀ q : SL(2, ZMod 3), q ^ 4 = 1 → ρ q = q := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := (hψA q).mpr hq
    rw [hρ]
    congr 1
    apply Subtype.ext
    rw [hφ]
    have := hcP _ (Subgroup.mem_subgroupOf.mp ha)
    calc c * (a : G) * c⁻¹ = (a : G) * c * c⁻¹ := by rw [this]
      _ = a := by group
  have hρg : ρ g₀ = g₀ := by
    refine sl2Three_eq_of_conj_eq _ _ (by rw [← map_pow, hg₀3, map_one]) hg₀3 fun q hq => ?_
    have h1 : (g₀ * q * g₀⁻¹) ^ 4 = 1 := by rw [conj_pow, hq, mul_one, mul_inv_cancel]
    calc ρ g₀ * q * (ρ g₀)⁻¹ = ρ g₀ * ρ q * (ρ g₀)⁻¹ := by rw [hρQ q hq]
      _ = ρ (g₀ * q * g₀⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = g₀ * q * g₀⁻¹ := hρQ _ h1
  have hy₀c : ψ (φ y₀) = ψ y₀ := by rw [← hρ, hy₀, hρg]
  set H : Subgroup G := Subgroup.normalizer ((oddCoreOf L : Subgroup G) : Set G)
  have hLH : L ≤ H := fun _ hg =>
    Disconnected.AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hg)
  have hcH : c ∈ H := Generic.mem_normalizer_of_conjSub_eq hOc
  have hMH : oddCoreOf L ≤ H := Subgroup.le_normalizer
  set N : Subgroup ↥H := (oddCoreOf L).subgroupOf H with hNdef
  haveI : N.Normal := Subgroup.normal_in_normalizer
  have hNodd : Odd (Nat.card N) := by
    rw [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv]
    exact oddCoreOf_odd_natCard L
  have hmk : ∀ a b : ↥L, ψ a = ψ b →
      QuotientGroup.mk' N ⟨(a : G), hLH a.2⟩ = QuotientGroup.mk' N ⟨(b : G), hLH b.2⟩ := by
    intro a b hab
    refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    have h1 : a⁻¹ * b ∈ classicalInvolutionOddCore ↥L :=
      (hψk _).mp (by rw [map_mul, map_inv, hab, inv_mul_cancel])
    exact mem_oddCoreOf_iff.mpr ⟨(a⁻¹ * b).2, h1⟩
  set A' : Subgroup ↥H := P.subgroupOf H
  set B' : Subgroup ↥H := (Subgroup.zpowers c).subgroupOf H
  have hA'2 : IsPGroup 2 ↥A' := hP2.comap_subtype
  have hB'2 : IsPGroup 2 ↥B' := (ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2).comap_subtype
  have hA'B' : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hb)
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← hk]
    exact (Commute.zpow_right
      (show Commute (a : G) c from (hcP _ (Subgroup.mem_subgroupOf.mp ha)).symm) k).eq
  set xb : ↥H ⧸ N := QuotientGroup.mk' N ⟨(y₀ : G), hLH y₀.2⟩ with hxbdef
  have hxbodd : Odd (orderOf xb) := by
    have h1 : xb ^ 3 = 1 := by
      have h2 : y₀ ^ 3 ∈ classicalInvolutionOddCore ↥L :=
        (hψk _).mp (by rw [map_pow, hy₀, hg₀3])
      have h3 := mem_oddCoreOf_iff.mpr ⟨(y₀ ^ 3).2, h2⟩
      have h4 : (⟨(y₀ : G), hLH y₀.2⟩ : ↥H) ^ 3 ∈ N := by
        rw [Subgroup.mem_subgroupOf]
        simpa using h3
      rw [hxbdef, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr h4
    exact (by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  have hxA : xb ∈ Subgroup.normalizer
      ((A'.map (QuotientGroup.mk' N) : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N)) := by
    refine mem_normalizer_of_conj_mem ?_
    rintro _ ⟨a, ha, rfl⟩
    have ha' : (a : G) ∈ P := Subgroup.mem_subgroupOf.mp ha
    obtain ⟨a', ha'A, ha'eq⟩ : ψ (y₀ * ⟨(a : G), hPL ha'⟩ * y₀⁻¹) ∈ A.map ψ := by
      rw [hψA, map_mul, map_mul, map_inv, hy₀, conj_pow,
        (hψA _).mp ⟨⟨(a : G), hPL ha'⟩, Subgroup.mem_subgroupOf.mpr ha', rfl⟩]
      group
    refine ⟨⟨(a' : G), hLH a'.2⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp ha'A), ?_⟩
    rw [hmk a' _ ha'eq]
    show _ = xb * QuotientGroup.mk' N a * xb⁻¹
    rw [hxbdef, ← map_mul, ← map_inv, ← map_mul]
    rfl
  have hxc : xb * QuotientGroup.mk' N ⟨c, hcH⟩ = QuotientGroup.mk' N ⟨c, hcH⟩ * xb := by
    have h1 : QuotientGroup.mk' N ⟨c, hcH⟩ * xb * (QuotientGroup.mk' N ⟨c, hcH⟩)⁻¹ = xb := by
      rw [hxbdef, ← map_inv, ← map_mul, ← map_mul]
      exact hmk (φ y₀) y₀ hy₀c
    calc xb * QuotientGroup.mk' N ⟨c, hcH⟩
        = (QuotientGroup.mk' N ⟨c, hcH⟩ * xb * (QuotientGroup.mk' N ⟨c, hcH⟩)⁻¹) *
          QuotientGroup.mk' N ⟨c, hcH⟩ := by rw [h1]
      _ = QuotientGroup.mk' N ⟨c, hcH⟩ * xb := by group
  have hxB : ∀ b ∈ B', xb * QuotientGroup.mk' N b = QuotientGroup.mk' N b * xb := by
    intro b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hb)
    have hb' : b = (⟨c, hcH⟩ : ↥H) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [hb', map_zpow]
    exact (Commute.zpow_right (show Commute xb _ from hxc) k).eq
  obtain ⟨x, hxodd, hxπ, hxA', hxB'⟩ :=
    Fus.lift_odd_normalizing N hNodd hA'2 hB'2 hA'B' hxbodd hxA hxB
  have hxN : x⁻¹ * ⟨(y₀ : G), hLH y₀.2⟩ ∈ N := QuotientGroup.eq.mp (hxπ.trans hxbdef)
  have hxM : (x : G)⁻¹ * y₀ ∈ oddCoreOf L := Subgroup.mem_subgroupOf.mp hxN
  obtain ⟨hxL', hxO⟩ := mem_oddCoreOf_iff.mp hxM
  have hxL : (x : G) ∈ L := by
    have e : (x : G) = y₀ * ((x : G)⁻¹ * y₀)⁻¹ := by group
    rw [e]
    exact L.mul_mem y₀.2 (L.inv_mem hxL')
  have hψx : ψ ⟨(x : G), hxL⟩ = g₀ := by
    have h1 : ψ (⟨(x : G), hxL⟩⁻¹ * y₀) = 1 := (hψk _).mpr hxO
    rw [map_mul, map_inv, hy₀] at h1
    exact inv_mul_eq_one.mp h1
  refine ⟨(x : G), hxL, ?_, fun p hp => ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hxodd
  · exact Subgroup.mem_subgroupOf.mp (hxA' ⟨p, hLH (hPL hp)⟩ (Subgroup.mem_subgroupOf.mpr hp))
  · obtain ⟨a, ha, haq⟩ := (hψA q₀).mpr hq₀4
    refine ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, fun h => hgq ?_⟩
    have h2 : (⟨(x : G), hxL⟩ : ↥L) * a = a * ⟨(x : G), hxL⟩ := Subtype.ext h
    have h3 := congrArg ψ h2
    rwa [map_mul, map_mul, hψx, haq] at h3
  · exact congrArg Subtype.val
      (hxB' ⟨c, hcH⟩ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers c)))

theorem exists_split_sec {Φ : Set (Subgroup G)} (F : Q8Pre G Φ) {K₀ K₁ : Subgroup G}
    (hK₀ : K₀ ∈ Φ) (hK₁ : K₁ ∈ Φ) (hne : K₁ ≠ K₀) {z : G} (hz₀ : IsUniqueInvolution K₀ z)
    (hz₁ : IsUniqueInvolution K₁ z) {c : G} (hc2 : c * c = 1) (hcK₀ : ∀ x ∈ K₀, c * x = x * c)
    {K : Subgroup G} (hK : K ∈ Φ) {τ : G} (hτ : IsUniqueInvolution K τ)
    (hlong : LongFundSetE3 K τ) :
    ∃ w : G, Odd (orderOf w) ∧ (∀ x ∈ K₀, w * x * w⁻¹ ∈ K₀) ∧ (∃ x ∈ K₀, w * x ≠ x * w) ∧
      (∀ y ∈ K₁, w * y = y * w) ∧ w * c = c * w := by
  obtain ⟨y, hy⟩ := F.trans K₀ hK₀ K hK
  subst hy
  have hτy : τ = y * z * y⁻¹ := hτ.eq (hz₀.conj y)
  subst hτy
  have hlong₀ : LongFundSetE3 K₀ z := by
    have h := longFundSetE3_conjSub hlong y⁻¹
    rwa [conjSub_inv_conjSub, show y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z by group] at h
  have htc : tightCore K₀ = K₀ := Frame.tightCore_eq_self_of_isPGroup (F.two K₀ hK₀)
  have hcc : CoreAssembly.conjClass K₀ = Φ := LemL.conjClass_eq F hK₀
  obtain ⟨Λ, hΛ, hcomm, heqv⟩ := hlong₀
  rw [htc, hcc] at hΛ hcomm heqv
  have hK₀tw : K₀ ∈ twinSet Φ K₀ := ⟨hK₀, z, hz₀, hz₀⟩
  have hK₁tw : K₁ ∈ twinSet Φ K₀ := ⟨hK₁, z, hz₀, hz₁⟩
  obtain ⟨hK₀Λ, hΛ₀⟩ := hΛ K₀ hK₀tw
  obtain ⟨hK₁Λ, -⟩ := hΛ K₁ hK₁tw
  have hcz : c ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcK₀ z hz₀.mem)
  have hcK₀' : conjSub c K₀ = K₀ :=
    conjSub_eq_of_mem_normalizer (Fus.mem_normalizer_of_comm K₀ c fun s hs => (hcK₀ s hs).symm)
  have hcΛ : conjSub c (Λ K₀) = Λ K₀ := by rw [heqv K₀ hK₀tw c hcz, hcK₀']
  have hK₀8 : Nat.card K₀ = 8 := by
    obtain ⟨eQ⟩ := F.q8 K₀ hK₀
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨w, hwΛ, hwodd, hwK₀, hwnt, hwc⟩ :=
    exists_split_of_classical hK₀8 hK₀Λ hΛ₀ hc2 hcK₀ hcΛ
  exact ⟨w, hwodd, hwK₀, hwnt,
    fun y' hy' => hcomm K₀ hK₀tw K₁ hK₁tw hne.symm w hwΛ y' (hK₁Λ hy'), hwc⟩

theorem oddCoreOf_inf_le_of_cover {X E E₀ : Subgroup G} (hE₀E : E₀ ≤ E) (hE₀X : E₀ ≤ X)
    (hcov : E ≤ oddCoreOf E ⊔ E₀) : oddCoreOf X ⊓ E ≤ oddCoreOf E := by
  have hD : E₀ ≤ Subgroup.normalizer ((oddCoreOf X ⊓ E : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Disconnected.AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer
        (Subgroup.le_normalizer (hE₀X hg)), Subgroup.le_normalizer (hE₀E hg)⟩
  exact F7L.le_oddCoreOf_of_cover (H := oddCoreOf X ⊓ E ⊔ E₀) (sup_le inf_le_right hE₀E)
    (hcov.trans (sup_le_sup_left le_sup_right _)) le_sup_left (sup_le Subgroup.le_normalizer hD)
    ((oddCoreOf_odd_natCard X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))

end Split

section Lift

variable {Y : Type} [Group Y] [Finite Y]

theorem rLayerSub_sup_zpowers_le {Ω : Set (Subgroup Y)} (V : Subgroup Y) (c : Y) :
    rLayerSub Ω (V ⊔ Subgroup.zpowers c) ≤ rLayer Ω c := by
  unfold rLayerSub
  refine iSup₂_le fun R hR => iSup_le fun hC => F7C.le_rLayer hR fun x hx => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (hC hx) c
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))).symm

theorem exists_split_of_longFund_of_cover {X E E₀ : Subgroup Y} {Φ : Set (Subgroup (SecQuot X))}
    (F : Q8Pre (SecQuot X) Φ) {P₀ P₀' : Subgroup Y} (hP₀X : P₀ ≤ X) (hP₀'X : P₀' ≤ X)
    (hP₀2 : IsPGroup 2 ↥P₀) (hK₀ : secImage X P₀ ∈ Φ) (hK₁ : secImage X P₀' ∈ Φ)
    (hne : secImage X P₀' ≠ secImage X P₀) {zb : SecQuot X}
    (hz₀ : IsUniqueInvolution (secImage X P₀) zb) (hz₁ : IsUniqueInvolution (secImage X P₀') zb)
    {c : Y} (hcX : c ∈ X) (hc2 : c * c = 1) (hP₀c : P₀ ≤ Subgroup.centralizer ({c} : Set Y))
    (hEc : Subgroup.centralizer ({c} : Set Y) ≤ Subgroup.normalizer (E : Set Y))
    (hP₀'E : P₀' ≤ E) (hE₀E : E₀ ≤ E) (hE₀X : E₀ ≤ X) (hcov : E ≤ oddCoreOf E ⊔ E₀)
    {K : Subgroup (SecQuot X)} (hK : K ∈ Φ) {τ : SecQuot X} (hτ : IsUniqueInvolution K τ)
    (hlong : LongFundSetE3 K τ) :
    ∃ w ∈ Subgroup.centralizer ({c} : Set Y), Odd (orderOf w) ∧ (∀ x ∈ P₀, w * x * w⁻¹ ∈ P₀) ∧
      (∃ x ∈ P₀, w * x ≠ x * w) ∧ ∀ x ∈ P₀', w * x * w⁻¹ * x⁻¹ ∈ oddCoreOf E := by
  have hcb2 : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨c, hcX⟩ *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨c, hcX⟩ = 1 := by
    rw [← map_mul]
    have : (⟨c, hcX⟩ * ⟨c, hcX⟩ : ↥X) = 1 := Subtype.ext hc2
    rw [this, map_one]
  have hcbK₀ : ∀ x ∈ secImage X P₀,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨c, hcX⟩ * x =
        x * QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨c, hcX⟩ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hP₀c (Subgroup.mem_subgroupOf.mp hy))).symm
  obtain ⟨wb, hwbodd, hwbK₀, hwbnt, hwbK₁, hwbc⟩ :=
    exists_split_sec F hK₀ hK₁ hne hz₀ hz₁ hcb2 hcbK₀ hK hτ hlong
  set A : Subgroup ↥X := P₀.subgroupOf X
  set B : Subgroup ↥X := (Subgroup.zpowers c).subgroupOf X
  have hA2 : IsPGroup 2 ↥A := hP₀2.comap_subtype
  have hB2 : IsPGroup 2 ↥B := (ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2).comap_subtype
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hb)
    apply Subtype.ext
    show (a : Y) * b = b * a
    rw [← hk]
    exact (Commute.zpow_right (show Commute (a : Y) c from
      Subgroup.mem_centralizer_singleton_iff.mp (hP₀c (Subgroup.mem_subgroupOf.mp ha))) k).eq
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hxA : wb ∈ Subgroup.normalizer
      ((A.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) : Subgroup (SecQuot X)) :
        Set (SecQuot X)) :=
    mem_normalizer_of_conj_mem hwbK₀
  have hxB : ∀ b ∈ B, wb * QuotientGroup.mk' (classicalInvolutionOddCore ↥X) b =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥X) b * wb := by
    intro b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hb)
    have hb' : b = (⟨c, hcX⟩ : ↥X) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [hb', map_zpow]
    exact (Commute.zpow_right (show Commute wb _ from hwbc) k).eq
  obtain ⟨w, hwodd, hwπ, hwA, hwB⟩ :=
    Fus.lift_odd_normalizing _ hNodd hA2 hB2 hAB hwbodd hxA hxB
  have hwc : (w : Y) * c = c * (w : Y) :=
    congrArg Subtype.val (hwB ⟨c, hcX⟩ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers c)))
  refine ⟨(w : Y), Subgroup.mem_centralizer_singleton_iff.mpr hwc, ?_, fun x hx => ?_, ?_,
    fun x hx => ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hwodd
  · exact Subgroup.mem_subgroupOf.mp (hwA ⟨x, hP₀X hx⟩ (Subgroup.mem_subgroupOf.mpr hx))
  · obtain ⟨_, ⟨y, hy, rfl⟩, hwy⟩ := hwbnt
    refine ⟨(y : Y), Subgroup.mem_subgroupOf.mp hy, fun h => hwy ?_⟩
    rw [← hwπ, ← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) (Subtype.ext h)
  ·
    have hxX := hP₀'X hx
    have hcomm : wb * QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨x, hxX⟩ =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨x, hxX⟩ * wb :=
      hwbK₁ _ ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have h1 : (w : Y) * x * (w : Y)⁻¹ * x⁻¹ ∈ oddCoreOf X := by
      refine mem_oddCoreOf_iff.mpr ⟨(w * ⟨x, hxX⟩ * w⁻¹ * ⟨x, hxX⟩⁻¹ : ↥X).2, ?_⟩
      have h2 : QuotientGroup.mk' (classicalInvolutionOddCore ↥X)
          (w * ⟨x, hxX⟩ * w⁻¹ * ⟨x, hxX⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hwπ, hcomm]
        group
      exact (QuotientGroup.eq_one_iff _).mp h2
    have h2 : (w : Y) * x * (w : Y)⁻¹ * x⁻¹ ∈ E := by
      have hwN := hEc (Subgroup.mem_centralizer_singleton_iff.mpr hwc)
      have hxE := hP₀'E hx
      exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp hwN x).mp hxE) (E.inv_mem hxE)
    exact oddCoreOf_inf_le_of_cover hE₀E hE₀X hcov ⟨h1, h2⟩

theorem exists_split_of_longFund_core {R V : Subgroup Y} (hΩ : HypOmegaGen (Om R))
    (F : Q8Pre (SecQuot (rLayerSub (Om R) V)) (p23SecFamV R V)) {P₀ P₀' : Subgroup Y}
    (hP₀R : P₀ ∈ RSet (Om R)) (hP₀'R : P₀' ∈ RSet (Om R))
    (hP₀V : P₀ ≤ Subgroup.centralizer (V : Set Y))
    (hP₀'V : P₀' ≤ Subgroup.centralizer (V : Set Y))
    (hne : secImage (rLayerSub (Om R) V) P₀' ≠ secImage (rLayerSub (Om R) V) P₀)
    {zb : SecQuot (rLayerSub (Om R) V)}
    (hz₀ : IsUniqueInvolution (secImage (rLayerSub (Om R) V) P₀) zb)
    (hz₁ : IsUniqueInvolution (secImage (rLayerSub (Om R) V) P₀') zb) {c : Y} (hc2 : c * c = 1)
    (hcX : c ∈ rLayerSub (Om R) V) (hP₀c : P₀ ≤ Subgroup.centralizer ({c} : Set Y))
    (hP₀'c : P₀' ≤ Subgroup.centralizer ({c} : Set Y))
    (hcov : rLayer (Om R) c ≤
      oddCoreOf (rLayer (Om R) c) ⊔ rLayerSub (Om R) (V ⊔ Subgroup.zpowers c))
    {K : Subgroup (SecQuot (rLayerSub (Om R) V))} (hK : K ∈ p23SecFamV R V)
    {τ : SecQuot (rLayerSub (Om R) V)} (hτ : IsUniqueInvolution K τ)
    (hlong : LongFundSetE3 K τ) :
    ∃ w ∈ Subgroup.centralizer ({c} : Set Y), Odd (orderOf w) ∧ (∀ x ∈ P₀, w * x * w⁻¹ ∈ P₀) ∧
      (∃ x ∈ P₀, w * x ≠ x * w) ∧
      ∀ x ∈ P₀', w * x * w⁻¹ * x⁻¹ ∈ oddCoreOf (rLayer (Om R) c) :=
  exists_split_of_longFund_of_cover F (le_rLayerSub_of_mem hP₀R hP₀V)
    (le_rLayerSub_of_mem hP₀'R hP₀'V) (F7C.isPGroup_of_mem_RSet hP₀R) ⟨P₀, hP₀R, hP₀V, rfl⟩
    ⟨P₀', hP₀'R, hP₀'V, rfl⟩ hne hz₀ hz₁ hcX hc2 hP₀c
    (fun _ hg => F7C.mem_normalizer_rLayer hΩ hg) (F7C.le_rLayer hP₀'R hP₀'c)
    (rLayerSub_sup_zpowers_le V c) (F7L.rLayerSub_mono le_sup_left) hcov hK hτ hlong

end Lift


section Main

theorem exists_split_of_longFund {n : ℕ}
    (hT : Thm4RTwinBelow 3 n) {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} {K' W : Subgroup Y} {u e g : Y} {Z : Subgroup Y} {f : Y}
    (ctx : L7Ctx n Y R S t K' W u e g Z f)
    (hL : SecCoresTwoGroup (Om R) (aSub R Z e ⊓ aSub R Z f))
    {K : Subgroup (SecQuot (rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f)))}
    (hK : K ∈ p23SecFamV R (aSub R Z e ⊓ aSub R Z f))
    {τ : SecQuot (rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f))} (hτ : IsUniqueInvolution K τ)
    (hlong : LongFundSetE3 K τ) :
    ∃ P₀ P₀' : Subgroup Y, IsSylow2In P₀ (tightCore R) ∧ IsSylow2In P₀' K' ∧
      P₀ ≤ Subgroup.centralizer ({e} : Set Y) ∧ P₀' ≤ Subgroup.centralizer ({e} : Set Y) ∧
      ∃ w ∈ Subgroup.centralizer ({e} : Set Y), Odd (orderOf w) ∧ (∀ x ∈ P₀, w * x * w⁻¹ ∈ P₀) ∧
        (∃ x ∈ P₀, w * x ≠ x * w) ∧
        (∀ x ∈ P₀', w * x * w⁻¹ * x⁻¹ ∈ oddCoreOf (rLayer (Om R) e)) := by
  obtain ⟨hc, -, -, hA6, hZd, -, -, hV1⟩ := ctx
  obtain ⟨D⟩ := ZTwo.exists_cover hc hA6
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  have hVe : aSub R Z e ⊓ aSub R Z f ≤ aSub R Z e := inf_le_left
  have hVZ : aSub R Z e ⊓ aSub R Z f ≤ Z := hVe.trans (aSub_le R Z e)
  have heO : e ∈ p23Orb Z t e := e_mem_orb Z t e
  obtain ⟨heX, -, -, hcov⟩ := LemL.p23_cover_V hc hZd hVZ heO hVe
  have hVeZ : aSub R Z e ⊓ aSub R Z f ⊔ Subgroup.zpowers e ≤ Z :=
    sup_le hVZ (Subgroup.zpowers_le.mpr hZd.he)
  obtain ⟨⟨P₀, hP₀, hP₀C'⟩, ⟨P₀', hP₀', hP₀'C'⟩⟩ := exists_sylow_cent_twins hc hZd hVeZ
  have heV' : ({e} : Set Y) ⊆ ((aSub R Z e ⊓ aSub R Z f ⊔ Subgroup.zpowers e : Subgroup Y) :
      Set Y) := Set.singleton_subset_iff.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
  have hVV' : ((aSub R Z e ⊓ aSub R Z f : Subgroup Y) : Set Y) ⊆
      ((aSub R Z e ⊓ aSub R Z f ⊔ Subgroup.zpowers e : Subgroup Y) : Set Y) :=
    SetLike.coe_subset_coe.mpr le_sup_left
  have hP₀C := hP₀C'.trans (Subgroup.centralizer_le hVV')
  have hP₀'C := hP₀'C'.trans (Subgroup.centralizer_le hVV')
  have hP₀e := hP₀C'.trans (Subgroup.centralizer_le heV')
  have hP₀'e := hP₀'C'.trans (Subgroup.centralizer_le heV')
  have hK₀ : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  obtain ⟨hKb, hKb', hne', ⟨zb, hzb, hzb'⟩, hperp, hperp'⟩ :=
    p23_twin_pair_of_sylow hc hL hP₀ hP₀' hP₀C hP₀'C
  have hna := not_isSolvable_Ea hc hZd hVZ D heO hVe heX
  have hlt := card_secQuot_lt hc hV1
  have hΦΩ := p23SecFamV_hypOmegaGen hc hZd hVZ hL
  have F : Q8Pre (SecQuot (rLayerSub (Om R) (aSub R Z e ⊓ aSub R Z f)))
      (p23SecFamV R (aSub R Z e ⊓ aSub R Z f)) :=
    { hyp := hΦΩ
      two := p23SecFamV_isPGroup hL
      q8 := p23SecFamV_q8 hc hL
      aEmpty := p23SecFamV_aEmpty hc hZd hVZ hL
      gen := p23SecFamV_pSpan R _
      trans := trans_of_twin' hT hlt hΦΩ (p23SecFamV_isPGroup hL) (p23SecFamV_q8 hc hL)
        (p23SecFamV_aEmpty hc hZd hVZ hL)
        (CFSG.ComponentClassification.OddCore.quotient_corefree _) hKb
        ⟨hKb', zb, hzb, hzb'⟩ hne' hperp hperp' (not_isPGroup_of_not_isSolvable hna)
      oddFree := CFSG.ComponentClassification.OddCore.quotient_corefree _ }
  exact ⟨P₀, P₀', hP₀, hP₀', hP₀e, hP₀'e,
    exists_split_of_longFund_core hΩ F (mem_RSet_of_isSylow2In hK₀ hP₀)
      (mem_RSet_of_isSylow2In hK'Ω hP₀') hP₀C hP₀'C hne' hzb hzb' (hZd.sq e hZd.he) heX hP₀e
      hP₀'e hcov hK hτ hlong⟩

theorem l7NoLong_of_coreTwo {n : ℕ} (hT : Thm4RTwinBelow 3 n)
    (hL1 : L7CoreTwo n) : L7NoLong n := by
  intro hcit hP Y _ _ R S t K' W u e g Z f ctx K hK τ hτ hlong
  obtain ⟨P₀, P₀', hP₀, hP₀', hP₀e, hP₀'e, w, hwe, hwodd, hwP, hwnt, hwP'⟩ :=
    exists_split_of_longFund hT ctx (hL1 hcit hP Y R S t K' W u e g Z f ctx) hK hτ hlong
  exact no_split_e ctx.cfg ctx.ae6 hP₀ hP₀' hP₀e hP₀'e hwe hwodd hwP hwnt hwP'

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
