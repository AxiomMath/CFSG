module

public import CFSG.ClassicalInvolution.Q3.Q3ZBTriple
public import CFSG.ClassicalInvolution.Q3.Q3ZBOdd
public import CFSG.ClassicalInvolution.Q3.Q3T6FaAut
public import CFSG.ClassicalInvolution.Q3.Q3ZAModel
public import CFSG.ClassicalInvolution.Q3.Q3T6FaField

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z
  CFSG.ClassicalInvolution.Q3.Q3ZA CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup stdPlane IsHyperbolicPlane
  longBlock planeGroup_stdPlane longInv)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups
open Matrix

section Local

variable {G : Type} [Group G]

@[expose] def locN (K : Subgroup G) (a : G) : Subgroup G :=
  centralizingLayer (conjClass3 K) {a}

@[expose] def locR (K : Subgroup G) (a : G) : Subgroup G := oddCoreIn (locN K a)

variable {K : Subgroup G} {a : G}

theorem locN_le_centralizer : locN K a ≤ Subgroup.centralizer ({a} : Set G) :=
  centralizingLayer_le_centralizer _ _

theorem le_locN {L : Subgroup G} (hL : L ∈ conjClass3 K) (hLa : L ≤ Subgroup.centralizer {a}) :
    L ≤ locN K a :=
  le_centralizingLayer ⟨hL, hLa⟩

theorem conj_mem_locN {c n : G} (hc : c ∈ Subgroup.centralizer ({a} : Set G))
    (hn : n ∈ locN K a) : c * n * c⁻¹ ∈ locN K a :=
  conj_mem_centralizingLayer (conjInvariant_conjClass3 K) hc hn

theorem locR_le_locN : locR K a ≤ locN K a := oddCoreIn_le _

theorem conj_mem_locR {n r : G} (hn : n ∈ locN K a) (hr : r ∈ locR K a) :
    n * r * n⁻¹ ∈ locR K a :=
  conj_mem_oddCoreIn hn hr

theorem locR_le_centralizer : locR K a ≤ Subgroup.centralizer ({a} : Set G) :=
  locR_le_locN.trans locN_le_centralizer

theorem commutes_of_mem_locR {r : G} (hr : r ∈ locR K a) : r * a = a * r :=
  Subgroup.mem_centralizer_singleton_iff.1 (locR_le_centralizer hr)

theorem odd_orderOf_of_mem_locR [Finite G] {r : G} (hr : r ∈ locR K a) : Odd (orderOf r) := by
  have h1 := orderOf_dvd_natCard (⟨r, hr⟩ : ↥(locR K a))
  rw [Subgroup.orderOf_mk] at h1
  exact (odd_card_oddCoreIn (locN K a)).of_dvd_nat h1

theorem TripleMem.a_mem_Kh {Ω : Set (Subgroup G)} {A B X : StatedSp 2 F3 →* G}
    {Kp Kh Kr : Subgroup G} (hT : TripleMem Ω A B X Kp Kh Kr) :
    A (longBlock F3 2 1 uSL) ∈ Kh :=
  hT.A1 ▸ ⟨longBlock F3 2 1 uSL, by rw [planeGroup_stdPlane]; exact ⟨uSL, rfl⟩, rfl⟩

theorem IsHubLayer.range_le_locN {M : Subgroup G} {Λ : StatedSp 2 F3 →* G}
    (hΛ : IsHubLayer (conjClass3 K) M Λ) (ha : a ∈ M) : Λ.range ≤ locN K a := by
  have htop : (locN K a).comap Λ = ⊤ := by
    refine eq_top_of_planeGroups_le (fun P hP x hx => ?_)
    obtain ⟨y, hy, hyeq⟩ := map_planeGroup_eq_conj Λ hP
    have hmem : (planeGroup P).map Λ ∈ conjClass3 K := by
      rw [hyeq]
      exact conjInvariant_conjClass3 K y _ hΛ.mem_plane
    have hle : (planeGroup P).map Λ ≤ Subgroup.centralizer ({a} : Set G) := by
      rintro _ ⟨s, -, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hΛ.comm (Λ s) ⟨s, rfl⟩ a ha)
    exact le_locN hmem hle ⟨x, hx, rfl⟩
  rintro _ ⟨s, rfl⟩
  have : s ∈ (locN K a).comap Λ := by rw [htop]; trivial
  exact this

end Local

section Sp4

variable {G : Type} [Group G]

theorem eq_one_of_odd_normal {X : StatedSp 2 F3 →* G} (hX : Function.Injective X)
    {S : Subgroup G} (hS : S ≤ X.range) (hn : ∀ s, ∀ r ∈ S, X s * r * (X s)⁻¹ ∈ S)
    (hodd : ∀ r ∈ S, Odd (orderOf r)) : ∀ r ∈ S, r = 1 := by
  have hq := Q3T6.isQuasisimple_sp4_of_three_le (K := F3) (by rw [card_F3])
  have hperf : Group.IsPerfect (StatedSp 2 F3) := hq.1
  let S' : Subgroup (StatedSp 2 F3) := S.comap X
  have hS'n : S'.Normal := ⟨fun n hn' g => by
    show X (g * n * g⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv]
    exact hn g _ hn'⟩
  have hord2 : ∀ s : StatedSp 2 F3, s * s = 1 → s ≠ 1 → X s ∈ S → False := by
    intro s hs hs1 hsS
    have h2 : orderOf (X s) = 2 := by
      have hX1 : X s ≠ 1 := fun h => hs1 (hX (h.trans (map_one X).symm))
      have : (X s) ^ 2 = 1 := by rw [pow_two, ← map_mul, hs, map_one]
      exact orderOf_eq_prime this hX1
    have := hodd _ hsS
    rw [h2] at this
    exact absurd this (by decide)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩ S' with h | h
  · intro r hr
    obtain ⟨s, rfl⟩ := hS hr
    have hs : s ∈ S' := hr
    rcases (mem_center_iff_negOne (by norm_num)).1 (h hs) with rfl | rfl
    · exact map_one X
    · exact (hord2 _ (CFSG.ClassicalInvolution.Models.SymplecticPairs.mul_self_eq_one_of_mem_center
        (by norm_num) negOne_mem_center) (negOne_ne_one (by
          intro h2
          exact one_ne_zero (by linear_combination three_eq_zero_f3 - h2)) (by norm_num)) hr).elim
  · exfalso
    have hmem : longInv F3 2 0 ∈ S' := by rw [h]; trivial
    exact hord2 _ (longInv_mul_self 0) (longInv_ne_one 0) hmem

end Sp4

section Sl2

theorem aut_sl2_fix_uSL (φ : SL(2, F3) ≃* SL(2, F3)) (h : φ uSL = uSL) :
    ∃ t : F3, ∀ b, φ b = usl t * b * (usl t)⁻¹ := by
  obtain ⟨g, hg⟩ := Q3T6.Fa.sl2_aut_eq_conj_of_card_three (F := F3) card_F3 φ
  set M : Matrix (Fin 2) (Fin 2) F3 := (g : Matrix (Fin 2) (Fin 2) F3) with hM
  set Mi : Matrix (Fin 2) (Fin 2) F3 := ((g⁻¹ : GL (Fin 2) F3) : Matrix (Fin 2) (Fin 2) F3)
    with hMi
  have hMiM : Mi * M = 1 := by rw [hMi, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMMi : M * Mi = 1 := by rw [hMi, hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 := congrArg (fun b : SL(2, F3) => (b : Matrix (Fin 2) (Fin 2) F3))
    ((hg uSL).symm.trans h)
  simp only [Q3T6.coe_conjSL] at h1
  have hU : (uSL : Matrix (Fin 2) (Fin 2) F3) = !![1, 1; 0, 1] := rfl
  have hcomm : M * !![1, 1; 0, 1] = !![1, 1; 0, 1] * M := by
    rw [← hU]
    calc M * (uSL : Matrix (Fin 2) (Fin 2) F3)
        = (M * (uSL : Matrix (Fin 2) (Fin 2) F3) * Mi) * M := by
          rw [Matrix.mul_assoc _ Mi M, hMiM, Matrix.mul_one]
      _ = _ := by rw [← hM, ← hMi] at h1; rw [h1]
  have e00 := congrFun (congrFun hcomm 0) 0
  have e01 := congrFun (congrFun hcomm 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have h10 : M 1 0 = 0 := e00
  obtain ⟨x, hxd⟩ : ∃ x, M 0 0 = x := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y, M 0 1 = y := ⟨_, rfl⟩
  have h11 : M 1 1 = x := by rw [← hxd]; linear_combination -e01
  have hx : x ≠ 0 := by
    intro hx0
    have := congrFun (congrFun hMMi 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, hx0] at this
  obtain ⟨t, ht⟩ : ∃ t, t = y * x⁻¹ := ⟨_, rfl⟩
  have hy : y = x * t := by rw [ht]; field_simp
  refine ⟨t, fun b => ?_⟩
  apply Subtype.ext
  have hMeq : M = x • (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h11, hxd, hyd, hy]
  have hUt' : (!![1, -t; 0, 1] : Matrix (Fin 2) (Fin 2) F3) * !![1, t; 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hxMi : x • Mi = !![1, -t; 0, 1] := by
    have h2 : (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F3) * (x • Mi) = 1 := by
      rw [Matrix.mul_smul, ← Matrix.smul_mul, ← hMeq, hMMi]
    calc x • Mi = ((!![1, -t; 0, 1] : Matrix (Fin 2) (Fin 2) F3) * !![1, t; 0, 1]) * (x • Mi) := by
          rw [hUt', Matrix.one_mul]
      _ = !![1, -t; 0, 1] := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [hg b, Q3T6.coe_conjSL, usl_inv]
  show M * (b : Matrix (Fin 2) (Fin 2) F3) * Mi = (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) F3) *
    (b : Matrix (Fin 2) (Fin 2) F3) * !![1, -t; 0, 1]
  rw [← hxMi, hMeq]
  simp only [Matrix.smul_mul, Matrix.mul_smul]

end Sl2

section FixedPoints

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {A B X : StatedSp 2 F3 →* G} {Kp Kh Kr : Subgroup G}


theorem TripleMem.eq_pow_of_commutes (hctx : Ctx G K z)
    (hT : TripleMem (conjClass3 K) A B X Kp Kh Kr)
    (haR : A (longBlock F3 2 1 uSL) ∈ locR K (A (longBlock F3 2 1 uSL)))
    {c : G} (hc : c ∈ locR K (A (longBlock F3 2 1 uSL)))
    (hcz : c * A (longInv F3 2 1) = A (longInv F3 2 1) * c) :
    ∃ j : ℤ, c = A (longBlock F3 2 1 uSL) ^ j := by
  set a := A (longBlock F3 2 1 uSL) with ha_def
  set zh := A (longInv F3 2 1) with hzh_def
  have haKh : a ∈ Kh := hT.a_mem_Kh
  have hXN : X.range ≤ locN K a := hT.hubX.range_le_locN haKh
  have hzhC : IsCentralInvolution Kh zh := hT.A1 ▸ isCentralInvolution_longInv hT.injA 1
  have hcKh : conjSub c Kh = Kh := conjSub_eq_of_centralizes hctx hT.mem_h hzhC hcz
  have hcX : ∀ s, c * X s * c⁻¹ ∈ X.range := hT.hubX.conj_mem_range hctx hcKh
  have hcX' : ∀ s, X s * c = c * X s := by
    intro s
    have hu : X s * c * (X s)⁻¹ * c⁻¹ = 1 := by
      refine eq_one_of_odd_normal (S := locR K a ⊓ X.range) hT.injX inf_le_right ?_ ?_ _ ⟨?_, ?_⟩
      · rintro s' r ⟨hr1, hr2⟩
        exact ⟨conj_mem_locR (hXN ⟨s', rfl⟩) hr1,
          X.range.mul_mem (X.range.mul_mem ⟨s', rfl⟩ hr2) (X.range.inv_mem ⟨s', rfl⟩)⟩
      · rintro r ⟨hr1, -⟩
        exact odd_orderOf_of_mem_locR hr1
      · exact (locR K a).mul_mem (conj_mem_locR (hXN ⟨s, rfl⟩) hc) ((locR K a).inv_mem hc)
      · have h1 : c * X s⁻¹ * c⁻¹ ∈ X.range := hcX s⁻¹
        rw [map_inv] at h1
        have := X.range.mul_mem (⟨s, rfl⟩ : X s ∈ X.range) h1
        simpa [mul_assoc] using this
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hu))
  have hzrC : IsCentralInvolution Kr (X (longInv F3 2 1)) :=
    hT.X1 ▸ isCentralInvolution_longInv hT.injX 1
  have hcKr : conjSub c Kr = Kr := conjSub_eq_of_centralizes hctx hT.mem_r hzrC (hcX' _).symm
  have hcA : ∀ s, c * A s * c⁻¹ ∈ A.range := hT.hubA.conj_mem_range hctx hcKr
  let ψ : SL(2, F3) →* G := A.comp (longBlock F3 2 1)
  have hψ : Function.Injective ψ :=
    hT.injA.comp (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_injective 1)
  have hψKh : ∀ y, ψ y ∈ Kh := fun y =>
    hT.A1 ▸ ⟨longBlock F3 2 1 y, by rw [planeGroup_stdPlane]; exact ⟨y, rfl⟩, rfl⟩
  have hmem : ∀ y, ∃ y', ψ y' = c * ψ y * c⁻¹ := by
    intro y
    have h2 : c * ψ y * c⁻¹ ∈ conjSub c Kh := ⟨ψ y, hψKh y, rfl⟩
    rw [hcKh, ← hT.A1] at h2
    obtain ⟨g, hg, hgeq⟩ := h2
    rw [planeGroup_stdPlane] at hg
    obtain ⟨y', rfl⟩ := hg
    exact ⟨y', hgeq⟩
  choose φf hφf using hmem
  let φ : SL(2, F3) →* SL(2, F3) :=
    { toFun := φf
      map_one' := hψ (by rw [hφf, map_one]; group)
      map_mul' := fun x y => hψ (by rw [hφf, map_mul, map_mul, hφf, hφf]; group) }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hψ
    have h1 : c * ψ x * c⁻¹ = c * ψ y * c⁻¹ := by
      rw [← hφf, ← hφf]
      exact congrArg ψ hxy
    simpa using h1
  let φe : SL(2, F3) ≃* SL(2, F3) :=
    MulEquiv.ofBijective φ ⟨hφinj, Finite.injective_iff_surjective.1 hφinj⟩
  have hca : c * a = a * c := commutes_of_mem_locR hc
  have hφa : φe uSL = uSL := by
    apply hψ
    show ψ (φf uSL) = ψ uSL
    rw [hφf]
    show c * a * c⁻¹ = a
    rw [hca]
    group
  obtain ⟨t, ht⟩ := aut_sl2_fix_uSL φe hφa
  have hw : ∀ y, c * ψ y * c⁻¹ = ψ (usl t) * ψ y * (ψ (usl t))⁻¹ := by
    intro y
    rw [← hφf, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg ψ (ht y)
  set w := ψ (usl t) with hw_def
  have hwKh : w ∈ Kh := hψKh _
  have hwR : w ∈ locR K a ∧ ∃ j : ℤ, w = a ^ j := by
    rcases eq_zero_or_one_or_neg_one_f3 t with rfl | rfl | rfl
    · refine ⟨?_, 0, ?_⟩
      · rw [hw_def, usl_zero, map_one]
        exact (locR K a).one_mem
      · rw [hw_def, usl_zero, map_one, zpow_zero]
    · refine ⟨?_, 1, ?_⟩
      · rw [hw_def, usl_one]
        exact haR
      · rw [hw_def, usl_one, zpow_one]
        rfl
    · refine ⟨?_, -1, ?_⟩
      · rw [hw_def, ← inv_inv (usl (-1)), usl_inv, neg_neg, usl_one, map_inv]
        exact (locR K a).inv_mem haR
      · rw [hw_def, ← inv_inv (usl (-1)), usl_inv, neg_neg, usl_one, map_inv, _root_.zpow_neg,
          zpow_one]
        rfl
  obtain ⟨hwR, j, hwj⟩ := hwR
  have hwA : ∀ g, w * A g * w⁻¹ =
      A (longBlock F3 2 1 (usl t) * g * (longBlock F3 2 1 (usl t))⁻¹) := fun g => by
    rw [map_mul, map_mul, map_inv]
    rfl
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = w⁻¹ * c := ⟨_, rfl⟩
  have hc₁R : c₁ ∈ locR K a := by
    rw [hc₁]
    exact (locR K a).mul_mem ((locR K a).inv_mem hwR) hc
  have hwcomm0 : ∀ x, w * A (longBlock F3 2 0 x) = A (longBlock F3 2 0 x) * w := fun x => by
    have h := (CFSG.ClassicalInvolution.Models.SymplecticPairs.commute_longBlock_longBlock
      (by decide : (1 : Fin 2) ≠ 0) (usl t) x).eq
    show A (longBlock F3 2 1 (usl t)) * A (longBlock F3 2 0 x) =
      A (longBlock F3 2 0 x) * A (longBlock F3 2 1 (usl t))
    rw [← map_mul, ← map_mul, h]
  have hb : ∀ g, ∃ g', c₁ * A g * c₁⁻¹ = A g' := by
    intro g
    obtain ⟨g₂, hg₂⟩ := hcA g
    refine ⟨(longBlock F3 2 1 (usl t))⁻¹ * g₂ * longBlock F3 2 1 (usl t), ?_⟩
    rw [map_mul, map_mul, hg₂, map_inv]
    show _ = w⁻¹ * (c * A g * c⁻¹) * w
    simp [hc₁, mul_assoc]
  have h0 : ∀ x, c₁ * A (longBlock F3 2 0 x) * c₁⁻¹ = A (longBlock F3 2 0 x) := by
    intro x
    have hc0 : c * A (longBlock F3 2 0 x) * c⁻¹ = A (longBlock F3 2 0 x) := by
      rw [← hT.end_p x]
      exact mul_inv_eq_iff_eq_mul.2 (hcX' _).symm
    calc c₁ * A (longBlock F3 2 0 x) * c₁⁻¹
        = w⁻¹ * (c * A (longBlock F3 2 0 x) * c⁻¹) * w := by simp [hc₁, mul_assoc]
      _ = w⁻¹ * A (longBlock F3 2 0 x) * w := by rw [hc0]
      _ = A (longBlock F3 2 0 x) := by
          rw [mul_assoc, ← hwcomm0 x]
          group
  have h1 : ∀ y, c₁ * A (longBlock F3 2 1 y) * c₁⁻¹ = A (longBlock F3 2 1 y) := by
    intro y
    calc c₁ * A (longBlock F3 2 1 y) * c₁⁻¹
        = w⁻¹ * (c * ψ y * c⁻¹) * w := by simp [hc₁, mul_assoc, ψ]
      _ = w⁻¹ * (w * ψ y * w⁻¹) * w := by rw [hw y]
      _ = ψ y := by group
  have hX1 : ∀ s, X s * c₁ = c₁ * X s := by
    intro s
    have h1' : X s * w⁻¹ = w⁻¹ * X s := by
      have h2 := hT.cX (X s) ⟨s, rfl⟩ w hwKh
      calc X s * w⁻¹ = w⁻¹ * (w * X s) * w⁻¹ := by group
        _ = w⁻¹ * (X s * w) * w⁻¹ := by rw [h2]
        _ = w⁻¹ * X s := by group
    rw [hc₁, ← mul_assoc, h1', mul_assoc, hcX' s, mul_assoc]
  have hordzh : orderOf zh = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzhC.sq) hzhC.ne_one
  rcases eq_or_conj_longInv A hT.injA c₁ hb h0 h1 with h | h
  · have hc₁1 : c₁ = 1 := by
      refine eq_one_of_centralizes_layers hctx hT.hubX hT.X0 hT.A0 hT.A1 ?_ ?_
      · rintro _ ⟨g, rfl⟩
        exact (mul_inv_eq_iff_eq_mul.1 (h g)).symm
      · rintro _ ⟨s, rfl⟩
        exact hX1 s
    rw [hc₁] at hc₁1
    exact ⟨j, ((inv_mul_eq_one.1 hc₁1).symm.trans hwj)⟩
  · exfalso
    have hneg : longInv F3 2 0 * longInv F3 2 1 = negOne 2 F3 := negOne_two_eq.symm
    have hcen : ∀ g, negOne 2 F3 * g = g * negOne 2 F3 := fun g =>
      (Subgroup.mem_center_iff.1 negOne_mem_center g).symm
    have hzhKh : zh ∈ Kh := hzhC.mem
    have hs1 : c₁ * zh = 1 := by
      refine eq_one_of_centralizes_layers hctx hT.hubX hT.X0 hT.A0 hT.A1 ?_ ?_
      · rintro _ ⟨g, rfl⟩
        have e : c₁ * zh * A g * (c₁ * zh)⁻¹ = A g := by
          calc c₁ * zh * A g * (c₁ * zh)⁻¹
              = c₁ * (zh * A g * zh⁻¹) * c₁⁻¹ := by group
            _ = c₁ * A (longInv F3 2 1 * g * (longInv F3 2 1)⁻¹) * c₁⁻¹ := by
                simp only [hzh_def, map_mul, map_inv]
            _ = A (longInv F3 2 0 * (longInv F3 2 1 * g * (longInv F3 2 1)⁻¹) *
                (longInv F3 2 0)⁻¹) := h _
            _ = A g := by
                congr 1
                calc longInv F3 2 0 * (longInv F3 2 1 * g * (longInv F3 2 1)⁻¹) *
                      (longInv F3 2 0)⁻¹
                    = (longInv F3 2 0 * longInv F3 2 1) * g *
                      (longInv F3 2 0 * longInv F3 2 1)⁻¹ := by group
                  _ = g := by rw [hneg, hcen g]; group
        exact (mul_inv_eq_iff_eq_mul.1 e).symm
      · rintro _ ⟨s, rfl⟩
        have h2 := hT.cX (X s) ⟨s, rfl⟩ zh hzhKh
        calc X s * (c₁ * zh) = (X s * c₁) * zh := by rw [mul_assoc]
          _ = c₁ * (X s * zh) := by rw [hX1 s, mul_assoc]
          _ = c₁ * (zh * X s) := by rw [h2]
          _ = c₁ * zh * X s := by rw [mul_assoc]
    have hc₁zh : c₁ = zh⁻¹ := eq_inv_of_mul_eq_one_left hs1
    have hodd := odd_orderOf_of_mem_locR hc₁R
    rw [hc₁zh, orderOf_inv, hordzh] at hodd
    exact absurd hodd (by decide)

end FixedPoints

end CFSG.ClassicalInvolution.Q3.Q3ZB
