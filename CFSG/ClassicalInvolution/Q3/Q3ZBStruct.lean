module

public import CFSG.ClassicalInvolution.Q3.Q3ZBLocQ
public import CFSG.ClassicalInvolution.Q3.Q3ZBCentral

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z
  CFSG.ClassicalInvolution.Q3.Q3ZA CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup stdPlane IsHyperbolicPlane
  longBlock planeGroup_stdPlane longInv isHyperbolicPlane_stdPlane)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

section Swap

variable {G : Type} [Group G]

@[expose] noncomputable def swapLayer (A : StatedSp 2 F3 →* G) : StatedSp 2 F3 →* G :=
  A.comp (MulAut.conj swapElt).toMonoidHom

theorem swapLayer_apply (A : StatedSp 2 F3 →* G) (s : StatedSp 2 F3) :
    swapLayer A s = A (swapElt * s * swapElt⁻¹) := rfl

theorem swapLayer_lb0 (A : StatedSp 2 F3 →* G) (x : SL(2, F3)) :
    swapLayer A (longBlock F3 2 0 x) = A (longBlock F3 2 1 x) := by
  rw [swapLayer_apply, mul_inv_eq_iff_eq_mul.2 (swap_mul_lb x)]

theorem swapLayer_lb1 (A : StatedSp 2 F3 →* G) (x : SL(2, F3)) :
    swapLayer A (longBlock F3 2 1 x) = A (longBlock F3 2 0 x) := by
  rw [swapLayer_apply, swapElt_inv]
  congr 1
  calc swapElt * longBlock F3 2 1 x * swapElt
      = swapElt * (longBlock F3 2 1 x * swapElt) := by rw [mul_assoc]
    _ = swapElt * (swapElt * longBlock F3 2 0 x) := by rw [swap_mul_lb]
    _ = longBlock F3 2 0 x := by rw [← mul_assoc, swapElt_mul_self, one_mul]

theorem swapLayer_range (A : StatedSp 2 F3 →* G) : (swapLayer A).range = A.range := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨swapElt⁻¹ * s * swapElt, ?_⟩
    rw [swapLayer_apply]
    congr 1
    group

theorem swapLayer_injective {A : StatedSp 2 F3 →* G} (h : Function.Injective A) :
    Function.Injective (swapLayer A) :=
  h.comp (MulAut.conj swapElt).injective

theorem map_planeGroup0_swapLayer (A : StatedSp 2 F3 →* G) :
    (planeGroup (stdPlane F3 2 0)).map (swapLayer A) = (planeGroup (stdPlane F3 2 1)).map A := by
  rw [planeGroup_stdPlane, planeGroup_stdPlane]
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, rfl⟩, (swapLayer_lb0 A y).symm⟩
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, rfl⟩, (swapLayer_lb0 A y)⟩

theorem swapLayer_tHub (A : StatedSp 2 F3 →* G) :
    swapLayer A tHub = A (longBlock F3 2 1 uSL) := by
  rw [swapLayer_apply, swap_tHub_conj]

theorem swapLayer_sbU (A : StatedSp 2 F3 →* G) : swapLayer A sbU = A sbL := by
  rw [swapLayer_apply, swap_sbU_conj]

theorem swapLayer_qSp (A : StatedSp 2 F3 →* G) : swapLayer A qSp = A qSp := by
  rw [swapLayer_apply, swap_qSp_conj]

theorem swapLayer_longInv0 (A : StatedSp 2 F3 →* G) :
    swapLayer A (longInv F3 2 0) = A (longInv F3 2 1) :=
  swapLayer_lb0 A (-1)

theorem swapLayer_a_mem (A : StatedSp 2 F3 →* G) :
    A (longBlock F3 2 1 uSL) ∈ Qexp.map (swapLayer A) :=
  ⟨tHub, tHub_mem_Qexp, swapLayer_tHub A⟩

end Swap

section TripleBasic

variable {G : Type} [Group G] {K : Subgroup G} {A B X : StatedSp 2 F3 →* G}
  {Kp Kh Kr : Subgroup G}

theorem TripleMem.B_tHub {Ω : Set (Subgroup G)} (hT : TripleMem Ω A B X Kp Kh Kr) :
    B tHub = A (longBlock F3 2 1 uSL) := (hT.hub uSL).symm

theorem TripleMem.Kp_le_centralizer {Ω : Set (Subgroup G)} (hT : TripleMem Ω A B X Kp Kh Kr) :
    Kp ≤ Subgroup.centralizer ({A (longBlock F3 2 1 uSL)} : Set G) := fun k hk => by
  rw [Subgroup.mem_centralizer_singleton_iff, ← hT.B_tHub]
  exact (hT.cB (B tHub) ⟨tHub, rfl⟩ k hk).symm

theorem TripleMem.Kr_le_centralizer {Ω : Set (Subgroup G)} (hT : TripleMem Ω A B X Kp Kh Kr) :
    Kr ≤ Subgroup.centralizer ({A (longBlock F3 2 1 uSL)} : Set G) := fun k hk => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hT.cA _ ⟨_, rfl⟩ k hk).symm

theorem TripleMem.Kp_le_locN (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    Kp ≤ locN K (A (longBlock F3 2 1 uSL)) := le_locN hT.mem_p hT.Kp_le_centralizer

theorem TripleMem.Kr_le_locN (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    Kr ≤ locN K (A (longBlock F3 2 1 uSL)) := le_locN hT.mem_r hT.Kr_le_centralizer

theorem TripleMem.zp_mem_Kp (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    A (longInv F3 2 0) ∈ Kp :=
  hT.A0 ▸ ⟨longInv F3 2 0, by rw [planeGroup_stdPlane]; exact ⟨-1, rfl⟩, rfl⟩

theorem TripleMem.zr_mem_Kr (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    B (longInv F3 2 1) ∈ Kr :=
  hT.B1 ▸ ⟨longInv F3 2 1, by rw [planeGroup_stdPlane]; exact ⟨-1, rfl⟩, rfl⟩

theorem TripleMem.hubA' (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    IsHubLayer (conjClass3 K) Kr (swapLayer A) :=
  ⟨swapLayer_injective hT.injA, hT.mem_r, by
    rw [map_planeGroup0_swapLayer, hT.A1]
    exact hT.mem_h, by
    rintro _ ⟨s, rfl⟩ k hk
    rw [swapLayer_apply]
    exact hT.cA _ ⟨_, rfl⟩ k hk⟩

theorem TripleMem.B_longInv0 {Ω : Set (Subgroup G)} (hT : TripleMem Ω A B X Kp Kh Kr) :
    B (longInv F3 2 0) = A (longInv F3 2 1) := (hT.hub (-1)).symm

end TripleBasic

section Triple

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {A B X : StatedSp 2 F3 →* G} {Kp Kh Kr : Subgroup G}

theorem TripleMem.zh_mem_locN (hctx : Ctx G K z) (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    A (longInv F3 2 1) ∈ locN K (A (longBlock F3 2 1 uSL)) := by
  have hd := hT.dependent hctx
  have hsq : ∀ (Λ : StatedSp 2 F3 →* G) (k : Fin 2),
      (Λ (longInv F3 2 k))⁻¹ = Λ (longInv F3 2 k) := fun Λ k => by
    rw [← map_inv, longInv_inv]
  have h1 : A (longInv F3 2 1) = A (longInv F3 2 0) * B (longInv F3 2 1) := by
    calc A (longInv F3 2 1)
        = (A (longInv F3 2 0))⁻¹ * (A (longInv F3 2 0) * A (longInv F3 2 1) *
          B (longInv F3 2 1)) * (B (longInv F3 2 1))⁻¹ := by group
      _ = _ := by rw [hd, hsq, hsq]; group
  rw [h1]
  exact (locN K _).mul_mem (hT.Kp_le_locN hT.zp_mem_Kp) (hT.Kr_le_locN hT.zr_mem_Kr)

theorem TripleMem.Q_B_le_locR (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    Qexp.map B ≤ locR K (A (longBlock F3 2 1 uSL)) := by
  have hwC : IsCentralInvolution Kp (A (longInv F3 2 0)) :=
    hT.A0 ▸ isCentralInvolution_longInv hT.injA 0
  have h := map_Qexp_le_locR hctx hO hT.hubB hwC
    (by rw [hT.B_tHub]; exact hT.Kp_le_locN hT.zp_mem_Kp)
  rwa [hT.B_tHub] at h

theorem TripleMem.Q_A_le_locR (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    Qexp.map (swapLayer A) ≤ locR K (A (longBlock F3 2 1 uSL)) := by
  have hwC : IsCentralInvolution Kr (B (longInv F3 2 1)) :=
    hT.B1 ▸ isCentralInvolution_longInv hT.injB 1
  have h := map_Qexp_le_locR hctx hO hT.hubA' hwC
    (by rw [swapLayer_tHub]; exact hT.Kr_le_locN hT.zr_mem_Kr)
  rwa [swapLayer_tHub] at h

theorem TripleMem.a_mem_locR (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    A (longBlock F3 2 1 uSL) ∈ locR K (A (longBlock F3 2 1 uSL)) := by
  have := hT.Q_B_le_locR hctx hO ⟨tHub, tHub_mem_Qexp, rfl⟩
  rwa [hT.B_tHub] at this

theorem TripleMem.map_DHub_B_le_locN (hctx : Ctx G K z)
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    DHub.map B ≤ locN K (A (longBlock F3 2 1 uSL)) := by
  have h := hT.hubB.map_DHub_le_locN (by
    rw [hT.B_tHub, hT.B_longInv0]
    exact hT.zh_mem_locN hctx)
  rwa [hT.B_tHub] at h

theorem TripleMem.map_DHub_A_le_locN (hctx : Ctx G K z)
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    DHub.map (swapLayer A) ≤ locN K (A (longBlock F3 2 1 uSL)) := by
  have h := hT.hubA'.map_DHub_le_locN (by
    rw [swapLayer_tHub, swapLayer_longInv0]
    exact hT.zh_mem_locN hctx)
  rwa [swapLayer_tHub] at h

theorem TripleMem.mem_Q_B_of_mem_locR (hctx : Ctx G K z)
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) {c : G}
    (hc : c ∈ locR K (A (longBlock F3 2 1 uSL))) (hcB : c ∈ B.range) : c ∈ Qexp.map B := by
  obtain ⟨s, rfl⟩ := hcB
  refine ⟨s, mem_Qexp_of_mem_locR (K := K) hT.injB ?_ ?_, rfl⟩
  · rw [hT.B_tHub]
    exact hT.map_DHub_B_le_locN hctx
  · rw [hT.B_tHub]
    exact hc

theorem TripleMem.mem_Q_A_of_mem_locR (hctx : Ctx G K z)
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) {c : G}
    (hc : c ∈ locR K (A (longBlock F3 2 1 uSL))) (hcA : c ∈ A.range) :
    c ∈ Qexp.map (swapLayer A) := by
  rw [← swapLayer_range] at hcA
  obtain ⟨s, rfl⟩ := hcA
  refine ⟨s, mem_Qexp_of_mem_locR (K := K) (swapLayer_injective hT.injA) ?_ ?_, rfl⟩
  · rw [swapLayer_tHub]
    exact hT.map_DHub_A_le_locN hctx
  · rw [swapLayer_tHub]
    exact hc

theorem TripleMem.zh_eq (hctx : Ctx G K z) (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    A (longInv F3 2 1) = A (longInv F3 2 0) * B (longInv F3 2 1) := by
  have hd := hT.dependent hctx
  have hsq : ∀ (Λ : StatedSp 2 F3 →* G) (k : Fin 2),
      (Λ (longInv F3 2 k))⁻¹ = Λ (longInv F3 2 k) := fun Λ k => by
    rw [← map_inv, longInv_inv]
  calc A (longInv F3 2 1)
      = (A (longInv F3 2 0))⁻¹ * (A (longInv F3 2 0) * A (longInv F3 2 1) *
        B (longInv F3 2 1)) * (B (longInv F3 2 1))⁻¹ := by group
    _ = _ := by rw [hd, hsq, hsq]; group

theorem TripleMem.R_inverted (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    (∀ r ∈ locR K (A (longBlock F3 2 1 uSL)), ∃ j : ℤ,
      A (longInv F3 2 1) * r * (A (longInv F3 2 1))⁻¹ = r⁻¹ * A (longBlock F3 2 1 uSL) ^ j) ∧
    ∀ r ∈ locR K (A (longBlock F3 2 1 uSL)), ∀ s ∈ locR K (A (longBlock F3 2 1 uSL)),
      ∃ j : ℤ, r * s = s * r * A (longBlock F3 2 1 uSL) ^ j := by
  have haR := hT.a_mem_locR hctx hO
  refine inverts_mod_of_fixed (odd_card_oddCoreIn (locN K _)) haR
    (fun r hr => commutes_of_mem_locR hr) ?_ (fun r hr => conj_mem_locR (hT.zh_mem_locN hctx) hr)
    ?_ ?_
  · rw [← map_mul, longInv_mul_self, map_one]
  · rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, longInv_comm_lb]
  · intro c hc h
    exact hT.eq_pow_of_commutes hctx haR hc (mul_inv_eq_iff_eq_mul.1 h).symm

theorem TripleMem.R_decomp (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) {r : G}
    (hr : r ∈ locR K (A (longBlock F3 2 1 uSL))) :
    ∃ r₁ ∈ locR K (A (longBlock F3 2 1 uSL)), ∃ r₂ ∈ locR K (A (longBlock F3 2 1 uSL)), ∃ j : ℤ,
      A (longInv F3 2 0) * r₁ * (A (longInv F3 2 0))⁻¹ = r₁ ∧
      B (longInv F3 2 1) * r₂ * (B (longInv F3 2 1))⁻¹ = r₂ ∧
      r = r₁ * r₂ * A (longBlock F3 2 1 uSL) ^ j := by
  have haR := hT.a_mem_locR hctx hO
  have hsq : ∀ (Λ : StatedSp 2 F3 →* G) (k : Fin 2),
      Λ (longInv F3 2 k) * Λ (longInv F3 2 k) = 1 := fun Λ k => by
    rw [← map_mul, longInv_mul_self, map_one]
  have hcomm : ∀ {w : G}, w ∈ Subgroup.centralizer ({A (longBlock F3 2 1 uSL)} : Set G) →
      w * A (longBlock F3 2 1 uSL) * w⁻¹ = A (longBlock F3 2 1 uSL) := fun {w} hw => by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 hw
  refine exists_decomp_in_subgroup (odd_card_oddCoreIn (locN K _)) haR
    (fun r hr => commutes_of_mem_locR hr) (hsq A 0) (hsq B 1)
    (fun r hr => conj_mem_locR (hT.Kp_le_locN hT.zp_mem_Kp) hr)
    (fun r hr => conj_mem_locR (hT.Kr_le_locN hT.zr_mem_Kr) hr)
    (hcomm (hT.Kp_le_centralizer hT.zp_mem_Kp)) (hcomm (hT.Kr_le_centralizer hT.zr_mem_Kr))
    ?_ hr
  intro r hr
  rw [← hT.zh_eq hctx]
  exact (hT.R_inverted hctx hO).1 r hr

theorem TripleMem.mem_B_of_commutes_zp (hctx : Ctx G K z)
    (hO : LocalOddCentralizer3 (conjClass3 K)) (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr)
    {c : G} (hc : c ∈ locR K (A (longBlock F3 2 1 uSL)))
    (hcz : A (longInv F3 2 0) * c * (A (longInv F3 2 0))⁻¹ = c) : c ∈ B.range := by
  have hwC : IsCentralInvolution Kp (A (longInv F3 2 0)) :=
    hT.A0 ▸ isCentralInvolution_longInv hT.injA 0
  have hcKp : conjSub c Kp = Kp :=
    conjSub_eq_of_centralizes hctx hT.mem_p hwC (mul_inv_eq_iff_eq_mul.1 hcz).symm
  have hcB : ∀ s, c * B s * c⁻¹ ∈ B.range := hT.hubB.conj_mem_range hctx hcKp
  obtain ⟨j, hj⟩ := (hT.R_inverted hctx hO).1 c hc
  refine mem_of_inverted (odd_orderOf_of_mem_locR hc) ⟨longInv F3 2 0, hT.B_longInv0⟩
    ⟨tHub, hT.B_tHub⟩ (commutes_of_mem_locR hc) ?_ hj
  have := hcB (longInv F3 2 0)⁻¹
  rwa [map_inv, hT.B_longInv0] at this

theorem TripleMem.mem_A_of_commutes_zr (hctx : Ctx G K z)
    (hO : LocalOddCentralizer3 (conjClass3 K)) (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr)
    {c : G} (hc : c ∈ locR K (A (longBlock F3 2 1 uSL)))
    (hcz : B (longInv F3 2 1) * c * (B (longInv F3 2 1))⁻¹ = c) : c ∈ A.range := by
  have hwC : IsCentralInvolution Kr (B (longInv F3 2 1)) :=
    hT.B1 ▸ isCentralInvolution_longInv hT.injB 1
  have hcKr : conjSub c Kr = Kr :=
    conjSub_eq_of_centralizes hctx hT.mem_r hwC (mul_inv_eq_iff_eq_mul.1 hcz).symm
  have hcA : ∀ s, c * A s * c⁻¹ ∈ A.range := hT.hubA.conj_mem_range hctx hcKr
  obtain ⟨j, hj⟩ := (hT.R_inverted hctx hO).1 c hc
  refine mem_of_inverted (odd_orderOf_of_mem_locR hc) ⟨_, rfl⟩ ⟨_, rfl⟩
    (commutes_of_mem_locR hc) ?_ hj
  have := hcA (longInv F3 2 1)⁻¹
  rwa [map_inv] at this

theorem TripleMem.R_eq_mul (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) {r : G}
    (hr : r ∈ locR K (A (longBlock F3 2 1 uSL))) :
    ∃ q₁ ∈ Qexp.map B, ∃ q₂ ∈ Qexp.map (swapLayer A), r = q₁ * q₂ := by
  obtain ⟨r₁, hr₁, r₂, hr₂, j, h1, h2, rfl⟩ := hT.R_decomp hctx hO hr
  refine ⟨r₁, hT.mem_Q_B_of_mem_locR hctx hr₁ (hT.mem_B_of_commutes_zp hctx hO hr₁ h1),
    r₂ * A (longBlock F3 2 1 uSL) ^ j, ?_, by group⟩
  exact (Qexp.map (swapLayer A)).mul_mem
    (hT.mem_Q_A_of_mem_locR hctx hr₂ (hT.mem_A_of_commutes_zr hctx hO hr₂ h2))
    ((Qexp.map (swapLayer A)).zpow_mem (swapLayer_a_mem A) j)

theorem TripleMem.A_qSp_mem_locR (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    A qSp ∈ locR K (A (longBlock F3 2 1 uSL)) :=
  hT.Q_A_le_locR hctx hO ⟨qSp, qSp_mem_Qexp, swapLayer_qSp A⟩

theorem TripleMem.A_sbL_mem_locR (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    A sbL ∈ locR K (A (longBlock F3 2 1 uSL)) :=
  hT.Q_A_le_locR hctx hO ⟨sbU, sbU_mem_Qexp, swapLayer_sbU A⟩

theorem TripleMem.cross_comm (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) {v : G} (hv : v ∈ Qexp.map B) :
    A qSp * v = v * A qSp ∧ A sbL * v = v * A sbL := by
  set a := A (longBlock F3 2 1 uSL) with ha
  have hvR : v ∈ locR K a := hT.Q_B_le_locR hctx hO hv
  have heR : A qSp ∈ locR K a := hT.A_qSp_mem_locR hctx hO
  have huR : A sbL ∈ locR K a := hT.A_sbL_mem_locR hctx hO
  have hK2 := (hT.R_inverted hctx hO).2
  have hvB : v ∈ B.range := by
    obtain ⟨q, -, rfl⟩ := hv
    exact ⟨q, rfl⟩
  have hcom : ∀ {w : G}, w ∈ locR K a → Commute a w := fun hw => (commutes_of_mem_locR hw).symm
  have hgp : A (longBlock F3 2 0 uSL) ∈ Kp :=
    hT.A0 ▸ ⟨longBlock F3 2 0 uSL, by rw [planeGroup_stdPlane]; exact ⟨uSL, rfl⟩, rfl⟩
  have hgp' : A (longBlock F3 2 0 lSL) ∈ Kp :=
    hT.A0 ▸ ⟨longBlock F3 2 0 lSL, by rw [planeGroup_stdPlane]; exact ⟨lSL, rfl⟩, rfl⟩
  have hga : ∀ {g : G}, g ∈ Kp → Commute a g := fun hg =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hT.Kp_le_centralizer hg)).symm
  have hgv : ∀ {g : G}, g ∈ Kp → Commute g v := fun {g} hg => (hT.cB v hvB g hg).symm
  have hu1 : swapLayer A (longBlock F3 2 1 uSL) = A (longBlock F3 2 0 uSL) :=
    swapLayer_lb1 A uSL
  have hu2 : swapLayer A (longBlock F3 2 1 lSL) = A (longBlock F3 2 0 lSL) :=
    swapLayer_lb1 A lSL
  constructor
  ·
    have hg := congrArg (swapLayer A) lb1U_sbU
    simp only [map_mul, map_inv, hu1, swapLayer_sbU, swapLayer_qSp, swapLayer_tHub] at hg
    obtain ⟨j₁, hj₁⟩ := hK2 _ huR v hvR
    obtain ⟨j₂, hj₂⟩ := hK2 _ heR v hvR
    have hj₂' := comm_data_inv (c := a ^ j₂) ((hcom heR).zpow_left j₂) hj₂
    have h1 : (A qSp)⁻¹ * v = v * (A qSp)⁻¹ := by
      refine comm_of_conj (a := a) (j₁ := j₁) (j₂ := -j₂) (k := 1) (hcom heR).inv_right
        (hcom hvR) (hga hgp) (hgv hgp) hj₁ ?_ ?_
      · rw [hj₂', zpow_neg]
      · rw [zpow_one]; exact hg
    exact (Commute.inv_left_iff.1 (show Commute (A qSp)⁻¹ v from h1)).eq
  · have hg := congrArg (swapLayer A) lb1L_qSp
    simp only [map_mul, map_inv, hu2, swapLayer_sbU, swapLayer_qSp, swapLayer_tHub] at hg
    obtain ⟨j₁, hj₁⟩ := hK2 _ heR v hvR
    obtain ⟨j₂, hj₂⟩ := hK2 _ huR v hvR
    have hj₂' := comm_data_inv (c := a ^ j₂) ((hcom huR).zpow_left j₂) hj₂
    have h1 : (A sbL)⁻¹ * v = v * (A sbL)⁻¹ := by
      refine comm_of_conj (a := a) (j₁ := j₁) (j₂ := -j₂) (k := -1) (hcom huR).inv_right
        (hcom hvR) (hga hgp') (hgv hgp') hj₁ ?_ ?_
      · rw [hj₂', zpow_neg]
      · rw [zpow_neg_one]; exact hg
    exact (Commute.inv_left_iff.1 (show Commute (A sbL)⁻¹ v from h1)).eq

theorem TripleMem.B_qSp_mem_locR (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    B qSp ∈ locR K (A (longBlock F3 2 1 uSL)) :=
  hT.Q_B_le_locR hctx hO ⟨qSp, qSp_mem_Qexp, rfl⟩

theorem TripleMem.B_sbU_mem_locR (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    B sbU ∈ locR K (A (longBlock F3 2 1 uSL)) :=
  hT.Q_B_le_locR hctx hO ⟨sbU, sbU_mem_Qexp, rfl⟩

theorem TripleMem.locR_eq_closure (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    locR K (A (longBlock F3 2 1 uSL)) = Subgroup.closure
      {A (longBlock F3 2 1 uSL), A qSp, A sbL, B qSp, B sbU} := by
  set R₀ : Subgroup G := Subgroup.closure
    {A (longBlock F3 2 1 uSL), A qSp, A sbL, B qSp, B sbU} with hR₀
  have hgen : ∀ x ∈ ({A (longBlock F3 2 1 uSL), A qSp, A sbL, B qSp, B sbU} : Set G), x ∈ R₀ :=
    fun x hx => Subgroup.subset_closure hx
  have ha : A (longBlock F3 2 1 uSL) ∈ R₀ := hgen _ (by simp)
  apply le_antisymm
  · intro r hr
    obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := hT.R_eq_mul hctx hO hr
    refine R₀.mul_mem ?_ ?_
    · have : Qexp.map B ≤ R₀ := by
        rw [Qexp_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨x, hx, rfl⟩
        rcases hx with rfl | rfl | rfl
        · exact hgen _ (by simp)
        · exact hgen _ (by simp)
        · rw [show B tHub = A (longBlock F3 2 1 uSL) from hT.B_tHub]
          exact ha
      exact this hq₁
    · have : Qexp.map (swapLayer A) ≤ R₀ := by
        rw [Qexp_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨x, hx, rfl⟩
        rcases hx with rfl | rfl | rfl
        · rw [swapLayer_sbU]
          exact hgen _ (by simp)
        · rw [swapLayer_qSp]
          exact hgen _ (by simp)
        · rw [swapLayer_tHub]
          exact ha
      exact this hq₂
  · rw [hR₀, Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hT.a_mem_locR hctx hO
    · exact hT.A_qSp_mem_locR hctx hO
    · exact hT.A_sbL_mem_locR hctx hO
    · exact hT.B_qSp_mem_locR hctx hO
    · exact hT.B_sbU_mem_locR hctx hO

theorem TripleMem.heis_inputs (hctx : Ctx G K z) (hO : LocalOddCentralizer3 (conjClass3 K))
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr) :
    Commute (A qSp) (B qSp) ∧ Commute (A sbL) (B sbU) ∧ Commute (A qSp) (B sbU) ∧
      Commute (B qSp) (A sbL) ∧
      ∀ s, ∀ r ∈ Subgroup.closure
          {A (longBlock F3 2 1 uSL), A qSp, A sbL, B qSp, B sbU},
        X s * r * (X s)⁻¹ ∈ Subgroup.closure
          {A (longBlock F3 2 1 uSL), A qSp, A sbL, B qSp, B sbU} := by
  have hq : B qSp ∈ Qexp.map B := ⟨qSp, qSp_mem_Qexp, rfl⟩
  have hs : B sbU ∈ Qexp.map B := ⟨sbU, sbU_mem_Qexp, rfl⟩
  refine ⟨(hT.cross_comm hctx hO hq).1, (hT.cross_comm hctx hO hs).2,
    (hT.cross_comm hctx hO hs).1, (hT.cross_comm hctx hO hq).2.symm, ?_⟩
  intro s r hr
  rw [← hT.locR_eq_closure hctx hO] at hr ⊢
  exact conj_mem_locR (hT.hubX.range_le_locN hT.a_mem_Kh ⟨s, rfl⟩) hr

end Triple

end CFSG.ClassicalInvolution.Q3.Q3ZB
