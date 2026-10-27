module

public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
public import CFSG.GroupTheory.QuasiDihedralFusion.Quotient

public section

namespace CFSG.ABGTheoremB.IV9DGroups

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

variable {G : Type*} [Group G]

@[expose] def quotImage (H X : Subgroup G) : Subgroup (H ⧸ CFSG.oddCore H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.oddCore H))

@[expose] def quotPreimage (H : Subgroup G) (M : Subgroup (H ⧸ CFSG.oddCore H)) : Subgroup G :=
  (M.comap (QuotientGroup.mk' (CFSG.oddCore H))).map H.subtype

variable {H X Y : Subgroup G}

theorem mk_mem_quotImage {g : G} (hgH : g ∈ H) (hgX : g ∈ X) :
    QuotientGroup.mk' (CFSG.oddCore H) (⟨g, hgH⟩ : H) ∈ quotImage H X :=
  ⟨⟨g, hgH⟩, hgX, rfl⟩

theorem exists_of_mem_quotImage {y : H ⧸ CFSG.oddCore H} (hy : y ∈ quotImage H X) :
    ∃ g ∈ X, ∃ hgH : g ∈ H, QuotientGroup.mk' (CFSG.oddCore H) (⟨g, hgH⟩ : H) = y := by
  obtain ⟨⟨g, hgH⟩, hgX, rfl⟩ := hy
  exact ⟨g, hgX, hgH, rfl⟩

theorem mem_quotPreimage {M : Subgroup (H ⧸ CFSG.oddCore H)} {g : G} :
    g ∈ quotPreimage H M ↔
      ∃ hgH : g ∈ H, QuotientGroup.mk' (CFSG.oddCore H) (⟨g, hgH⟩ : H) ∈ M := by
  constructor
  · rintro ⟨⟨g, hgH⟩, hg, rfl⟩
    exact ⟨hgH, hg⟩
  · rintro ⟨hgH, hg⟩
    exact ⟨⟨g, hgH⟩, hg, rfl⟩

theorem mem_oddCoreIn_iff {g : G} (hgH : g ∈ H) :
    g ∈ oddCoreIn H ↔ (⟨g, hgH⟩ : H) ∈ CFSG.oddCore H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨⟨g, hgH⟩, h, rfl⟩

theorem mk_eq_one_iff {g : G} (hgH : g ∈ H) :
    QuotientGroup.mk' (CFSG.oddCore H) (⟨g, hgH⟩ : H) = 1 ↔ g ∈ oddCoreIn H := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_oddCoreIn_iff hgH]

theorem quotPreimage_le (M : Subgroup (H ⧸ CFSG.oddCore H)) : quotPreimage H M ≤ H :=
  Subgroup.map_subtype_le _

theorem quotImage_mono (hXY : X ≤ Y) : quotImage H X ≤ quotImage H Y :=
  Subgroup.map_mono fun _ hx => hXY hx

theorem quotImage_le_iff (hX : X ≤ H) {M : Subgroup (H ⧸ CFSG.oddCore H)} :
    quotImage H X ≤ M ↔ X ≤ quotPreimage H M := by
  constructor
  · intro h g hg
    exact mem_quotPreimage.mpr ⟨hX hg, h (mk_mem_quotImage (hX hg) hg)⟩
  · intro h y hy
    obtain ⟨g, hgX, hgH, rfl⟩ := exists_of_mem_quotImage hy
    obtain ⟨_, hg⟩ := mem_quotPreimage.mp (h hgX)
    exact hg

theorem mk_mem_normalizer_quotImage {g : G} (hgH : g ∈ H)
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    QuotientGroup.mk' (CFSG.oddCore H) (⟨g, hgH⟩ : H) ∈
      Subgroup.normalizer (quotImage H X : Set (H ⧸ CFSG.oddCore H)) := by
  have hg' : (⟨g, hgH⟩ : H) ∈ Subgroup.normalizer ((X.subgroupOf H : Subgroup H) : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    exact Subgroup.mem_normalizer_iff.mp hg a
  exact Subgroup.le_normalizer_map _ ⟨_, hg', rfl⟩

theorem quotImage_le_normalizer (hYX : Y ≤ Subgroup.normalizer (X : Set G)) :
    quotImage H Y ≤ Subgroup.normalizer (quotImage H X : Set (H ⧸ CFSG.oddCore H)) := by
  intro y hy
  obtain ⟨g, hgY, hgH, rfl⟩ := exists_of_mem_quotImage hy
  exact mk_mem_normalizer_quotImage hgH (hYX hgY)

theorem mem_normalizer_quotPreimage {M : Subgroup (H ⧸ CFSG.oddCore H)} {g : G} (hgH : g ∈ H)
    (hg : QuotientGroup.mk' (CFSG.oddCore H) (⟨g, hgH⟩ : H) ∈
      Subgroup.normalizer (M : Set (H ⧸ CFSG.oddCore H))) :
    g ∈ Subgroup.normalizer (quotPreimage H M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  rw [mem_quotPreimage, mem_quotPreimage]
  constructor
  · rintro ⟨haH, haM⟩
    refine ⟨H.mul_mem (H.mul_mem hgH haH) (H.inv_mem hgH), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp haM
  · rintro ⟨haH', haM⟩
    have haH : a ∈ H := by
      have h1 := H.mul_mem (H.mul_mem (H.inv_mem hgH) haH') hgH
      simpa [mul_assoc] using h1
    refine ⟨haH, (Subgroup.mem_normalizer_iff.mp hg _).mpr ?_⟩
    exact haM

theorem mk_mem_centralizer_singleton {g x : G} (hgH : g ∈ H) (hxH : x ∈ H)
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) :
    QuotientGroup.mk' (CFSG.oddCore H) (⟨g, hgH⟩ : H) ∈
      Subgroup.centralizer ({QuotientGroup.mk' (CFSG.oddCore H) (⟨x, hxH⟩ : H)} :
        Set (H ⧸ CFSG.oddCore H)) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hg

theorem card_quotImage_dvd (X : Subgroup G) : Nat.card (quotImage H X) ∣ Nat.card X := by
  refine (Subgroup.card_map_dvd _ _).trans ?_
  rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype]
  exact Subgroup.card_dvd_of_le inf_le_left

theorem odd_card_quotImage (hX : Odd (Nat.card X)) : Odd (Nat.card (quotImage H X)) :=
  hX.of_dvd_nat (card_quotImage_dvd X)

section Finite

variable [Finite G]

theorem odd_card_ker_mk' : Odd (Nat.card (QuotientGroup.mk' (CFSG.oddCore H)).ker) :=
  odd_card_ker_mk'_oddCore

theorem odd_card_quotPreimage {M : Subgroup (H ⧸ CFSG.oddCore H)} (hM : Odd (Nat.card M)) :
    Odd (Nat.card (quotPreimage H M)) := by
  rw [quotPreimage, Subgroup.card_map_of_injective H.subtype_injective, card_comap_mk']
  exact (CFSG.ABGLocalTools.odd_card_oddCore (H := H)).mul hM

@[expose] noncomputable def quotImageEquiv (hX : X ≤ H) (h2 : IsPGroup 2 X) :
    X ≃* quotImage H X :=
  (Subgroup.subgroupOfEquivOfLe hX).symm.trans
    (equivMapOfIsPGroup _ odd_card_ker_mk' (X.subgroupOf H)
      (h2.of_equiv (Subgroup.subgroupOfEquivOfLe hX).symm))

theorem card_quotImage_of_isPGroup (hX : X ≤ H) (h2 : IsPGroup 2 X) :
    Nat.card (quotImage H X) = Nat.card X :=
  (Nat.card_congr (quotImageEquiv hX h2).toEquiv).symm

theorem isPGroup_quotImage (hX : X ≤ H) (h2 : IsPGroup 2 X) : IsPGroup 2 (quotImage H X) :=
  h2.of_equiv (quotImageEquiv hX h2)

theorem isKleinFour_quotImage (hX : X ≤ H) (h4 : IsKleinFour X) : IsKleinFour (quotImage H X) :=
  have h2 : IsPGroup 2 X := IsPGroup.of_card (n := 2) (by rw [h4.card_four]; norm_num)
  ⟨by rw [card_quotImage_of_isPGroup hX h2]; exact h4.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv (quotImageEquiv hX h2)]; exact h4.exponent_two⟩

theorem le_sup_oddCoreIn_of_quotImage_le {x : G} (hxH : x ∈ H) (hx : orderOf x = 2)
    {W : Subgroup (H ⧸ CFSG.oddCore H)} (hW : Odd (Nat.card W))
    (hWx : W ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.oddCore H) (⟨x, hxH⟩ : H)} : Set (H ⧸ CFSG.oddCore H)))
    (hCW : Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.oddCore H) (⟨x, hxH⟩ : H)} : Set (H ⧸ CFSG.oddCore H)) ≤
        Subgroup.normalizer (W : Set (H ⧸ CFSG.oddCore H)))
    {Z : Subgroup G} (hZH : Z ≤ H) (hZW : quotImage H Z ≤ W) :
    Z ≤ oddCoreIn H ⊔ oddCoreIn (H ⊓ Subgroup.centralizer ({x} : Set G)) := by
  set π := QuotientGroup.mk' (CFSG.oddCore H)
  set V := quotPreimage H W with hVdef
  have hVodd : Odd (Nat.card V) := odd_card_quotPreimage hW
  have hNV : H ⊓ Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    rintro g ⟨hgH, hgx⟩
    exact mem_normalizer_quotPreimage hgH (hCW (mk_mem_centralizer_singleton hgH hxH hgx))
  have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
    hNV ⟨hxH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hCV : V ⊓ Subgroup.centralizer ({x} : Set G) ≤
      oddCoreIn (H ⊓ Subgroup.centralizer ({x} : Set G)) := by
    refine le_oddCoreIn (inf_le_inf_right _ (quotPreimage_le W)) ?_
      (hVodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hNV hg, Subgroup.le_normalizer hg.2⟩
  have hZV : Z ≤ V := (quotImage_le_iff hZH).mp hZW
  intro z hz
  have hzV : z ∈ (V : Set G) := hZV hz
  rw [(odd_fixed_mul_inverted hVodd hx hxN).1] at hzV
  obtain ⟨f, hf, i, ⟨hiV, hix⟩, rfl⟩ := hzV
  obtain ⟨hiH, hiW⟩ := mem_quotPreimage.mp hiV
  have hiO : i ∈ oddCoreIn H := by
    rw [← mk_eq_one_iff hiH]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hWx hiW)
    have hinv : π ⟨x, hxH⟩ * π ⟨i, hiH⟩ * (π ⟨x, hxH⟩)⁻¹ = (π ⟨i, hiH⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
      congr 1
      exact Subtype.ext hix
    rw [← hc, mul_inv_cancel_right] at hinv
    have hsq : π ⟨i, hiH⟩ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hinv]
      exact mul_inv_cancel _
    have hodd : Odd (orderOf (π ⟨i, hiH⟩)) :=
      hW.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hiW)
    have h2 : orderOf (π ⟨i, hiH⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [sup_comm]
  exact Subgroup.mul_mem_sup (hCV hf) hiO

end Finite

end CFSG.ABGTheoremB.IV9DGroups
