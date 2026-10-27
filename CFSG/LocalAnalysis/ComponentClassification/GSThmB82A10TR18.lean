module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TK
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TZStar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TR18Defs

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

private theorem mul_conj_mul_inv {G : Type*} [Group G] (σ : MulAut G) (x : G) :
    σ * MulAut.conj x * σ⁻¹ = MulAut.conj (σ x) := by
  refine MulEquiv.ext fun y => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

private theorem isSylowIn_conjugate' {S Y : Subgroup X} (hS : Seven.IsSylowIn S Y) (g : X) :
    Seven.IsSylowIn (conjugate S g) (conjugate Y g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSY, R, hR⟩ := hS
  have hle : conjugate S g ≤ conjugate Y g := map_mono hSY
  have h1 : Nat.card ↥((conjugate S g).subgroupOf (conjugate Y g)) = Nat.card ↥(conjugate S g) :=
    Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
  have h2 : Nat.card ↥(conjugate S g) = Nat.card ↥S :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have h3 : Nat.card ↥(conjugate Y g) = Nat.card ↥Y :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have h4 : Nat.card ↥(S.subgroupOf Y) = Nat.card ↥S :=
    Nat.card_congr (subgroupOfEquivOfLe hSY).toEquiv
  have h5 : Nat.card ↥(R : Subgroup ↥Y) = 2 ^ (Nat.card ↥Y).factorization 2 :=
    R.card_eq_multiplicity
  rw [hR, h4] at h5
  refine ⟨hle, Sylow.ofCard ((conjugate S g).subgroupOf (conjugate Y g)) ?_, rfl⟩
  rw [h1, h2, h3, h5]

private theorem isSimpleGroup_quot_fusionZStar {H M : Subgroup X} (hMH : M ≤ H)
    (hM : IsPComponent 2 (M.subgroupOf H)) : IsSimpleGroup (↥M ⧸ Open.fusionZStar ↥M) := by
  obtain ⟨eM⟩ := FooteLit.nonempty_fusionZStar_quotient_equiv ↥M
  have := (isQuasisimple_of_isPComponent hMH hM).2.1
  exact eM.isSimpleGroup

private theorem mem_coreActionKernel_of_sup_eq {A Y : Subgroup X} {u : X}
    (hAY : A ⊔ oddCoreIn Y = Y) (huY : u ∈ normalizer (Y : Set X))
    (huA : u ∈ coreActionKernel A) : u ∈ coreActionKernel Y := by
  have hAY' : A ≤ Y := le_sup_left.trans hAY.le
  have hOA : oddCoreIn A ≤ oddCoreIn Y := by
    have h := (restriction_quotient_mulEquiv hAY' hAY).1
    intro x hx
    have hx' : x ∈ A ⊓ (pPrimeCore 2 ↥Y).map Y.subtype := by
      rw [← h]
      exact hx
    exact (mem_inf.mp hx').2
  have huO : u ∈ normalizer (oddCoreIn Y : Set X) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Y (pPrimeCore 2 ↥Y) huY
  have hAO : A ≤ normalizer (oddCoreIn Y : Set X) := fun α hα =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Y (pPrimeCore 2 ↥Y)
      (le_normalizer (hAY' hα))
  refine mem_coreActionKernel.mpr ⟨huY, fun j hj => ?_⟩
  have hj' : j ∈ ((A ⊔ oddCoreIn Y : Subgroup X) : Set X) := by
    rw [hAY]
    exact hj
  rw [coe_mul_of_left_le_normalizer_right A (oddCoreIn Y) hAO] at hj'
  obtain ⟨α, hα, o, ho, rfl⟩ := hj'
  have h1 : α⁻¹ * u⁻¹ * α * u ∈ oddCoreIn Y := hOA ((mem_coreActionKernel.mp huA).2 α hα)
  have h2 : u⁻¹ * o * u ∈ oddCoreIn Y := by
    have h3 := (mem_normalizer_iff.mp (inv_mem huO) o).mp ho
    rwa [inv_inv] at h3
  have e1 : (α * o)⁻¹ * u⁻¹ * (α * o) * u = o⁻¹ * (α⁻¹ * u⁻¹ * α * u) * (u⁻¹ * o * u) := by
    group
  rw [e1]
  exact mul_mem (mul_mem (inv_mem ho) h1) h2

private theorem card_quot_fusionZStar_eq_of_sup_eq {A Y : Subgroup X}
    (hAY : A ⊔ oddCoreIn Y = Y) :
    Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) = Nat.card (↥A ⧸ Open.fusionZStar ↥A) := by
  obtain ⟨-, eA, -⟩ := restriction_quotient_mulEquiv (le_sup_left.trans hAY.le) hAY
  exact (card_quot_fusionZStar_eq_of_equiv eA).symm

private theorem even_orderOf_conj_a_mul_z (c : Ctx X) (m : X) :
    Even (orderOf (m⁻¹ * c.s.h.a * m * c.Z.z)) := by
  by_contra hodd
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hodd
  have h1 : (m⁻¹ * c.s.h.a * m * c.Z.z) ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have hx : m⁻¹ * c.s.h.a * m * (m⁻¹ * c.s.h.a * m) = 1 := by
    calc m⁻¹ * c.s.h.a * m * (m⁻¹ * c.s.h.a * m) = m⁻¹ * (c.s.h.a * c.s.h.a) * m := by group
      _ = 1 := by rw [Six.a_mul_a_self c.s.h]; group
  have h2 := Sporadic.LySchreier.conj_eq_of_odd_order hx c.Z.hzz h1
  refine not_conj_a_z c.Z c.s.S_sylow c.hN (m * ((m⁻¹ * c.s.h.a * m * c.Z.z) ^ k)⁻¹)
    (Eq.trans ?_ h2)
  generalize (m⁻¹ * c.s.h.a * m * c.Z.z) ^ k = p
  group

private theorem exists_pow_ne_one_two {x : X} (hx : Even (orderOf x)) :
    ∃ o k : ℕ, x ^ o ≠ 1 ∧ (x ^ o) ^ 2 ^ k = 1 := by
  obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hko
    exact Nat.not_even_iff_odd.mpr ho (hko ▸ hx)
  refine ⟨o, k, pow_ne_one_of_lt_orderOf ho.pos.ne' ?_, ?_⟩
  · have h2k : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hk0)
    rw [hko]
    nlinarith [ho.pos]
  · rw [← pow_mul, mul_comm, ← hko, pow_orderOf_eq_one]

namespace Ctx.CaseIIIp

variable {c : Ctx X} (e : c.CaseIIIp)

theorem false_of_L44_HS (hR18 : GS82R18Input)
    (hB01 : c.s.h.secB0 c.s.y ⊓ coreActionKernel e.K = ⊥) {b : X}
    (hbB : b ∈ c.s.h.secB0 c.s.y) (hb : orderOf b = 2) {Y : Subgroup X}
    (hYK : Y ≤ e.K ⊓ centralizer ({b} : Set X))
    (hY : IsPComponent 2 (Y.subgroupOf (centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X))))
    (hY8 : e.A8 ⊔ oddCoreIn Y = Y)
    (hK : Blueprint.LieModel (↥e.K ⧸ Open.fusionZStar ↥e.K) .PSL 4 2 2 ∨
      Nonempty (↥e.K ⧸ Open.fusionZStar ↥e.K ≃* Blueprint.NativeSporadic.Carrier .HS)) :
    False := by
  have hLB : Seven.Lay c.s.h c.s.y ≤ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    Seven.Lay_le_centralizer_secB0 _ _
  have hG0L : c.s.h.secG0 c.s.y ≤ normalizer (Seven.Lay c.s.h c.s.y : Set X) :=
    Seven.secG0_le_normalizer_Lay _ _
  have haH : c.s.h.a ∈ c.s.h.secSub c.s.y := c.s.secCond.a_mem_secSub
  have hzH : c.Z.z ∈ c.s.h.secSub c.s.y := c.z_mem_secSub
  have haS0 : c.s.h.a ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y :=
    mem_inf.mpr ⟨c.s.h.a_mem_S, c.s.secCond.a_mem_G0⟩
  have hzS0 : c.Z.z ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y := c.z_mem_S0
  have haw : c.s.h.a ∈ centralizer ({e.w} : Set X) :=
    mem_centralizer_singleton_iff.mpr (e.d.comm_S0 _ (Set.mem_insert_of_mem _ rfl) _ haS0)
  have hzw : c.Z.z ∈ centralizer ({e.w} : Set X) :=
    mem_centralizer_singleton_iff.mpr (e.d.comm_S0 _ (Set.mem_insert_of_mem _ rfl) _ hzS0)
  have ha'w : e.d.a' ∈ centralizer ({e.w} : Set X) :=
    mem_centralizer_singleton_iff.mpr e.d.a'_comm_z'
  have haN : c.s.h.a ∈ normalizer (e.K : Set X) :=
    e.mem_normalizer_K haw (e.mem_normalizer_A8 haH (hG0L (mem_inf.mp haS0).2) haw)
  have hzN : c.Z.z ∈ normalizer (e.K : Set X) :=
    e.mem_normalizer_K hzw (e.mem_normalizer_A8 hzH (hG0L (mem_inf.mp hzS0).2) hzw)
  have ha'N : e.d.a' ∈ normalizer (e.K : Set X) :=
    e.mem_normalizer_K ha'w
      (e.mem_normalizer_A8 e.d.a'_mem_secSub (hG0L (mem_inf.mp e.d.a'_mem_S0).2) ha'w)
  have hwN : e.w ∈ normalizer (e.K : Set X) :=
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun k hk =>
      mem_centralizer_singleton_iff.mp (e.K_le hk))
  have hτ : swap (0 : Fin 10) 4 * swap 1 5 * swap 2 6 * swap 3 7 ∈ altOn fixR := by
    rw [mem_altOn, mem_alternatingGroup]
    exact ⟨by decide, by decide⟩
  rw [← e.isRep_A8.2.1] at hτ
  obtain ⟨⟨m, hmH⟩, hmA, hmτ⟩ := mem_map.mp hτ
  replace hmA : m ∈ e.A8 := hmA
  have hmL : m ∈ Seven.Lay c.s.h c.s.y := (mem_inf.mp (e.A8_le hmA)).1
  have hmw : m ∈ centralizer ({e.w} : Set X) := (mem_inf.mp (e.A8_le hmA)).2
  have hmK : m ∈ e.K := e.A8_le_K hmA
  have hmN : m ∈ normalizer (e.K : Set X) := le_normalizer hmK
  obtain ⟨u, hu⟩ : ∃ u, u = m⁻¹ * c.s.h.a * m * c.Z.z := ⟨_, rfl⟩
  have huH : u ∈ c.s.h.secSub c.s.y := by
    rw [hu]
    exact mul_mem (mul_mem (mul_mem (inv_mem hmH) haH) hmH) hzH
  have hφu : c.φ ⟨u, huH⟩ = 1 := by
    have h1 : (⟨u, huH⟩ : ↥(c.s.h.secSub c.s.y)) =
        (⟨m, hmH⟩ : ↥(c.s.h.secSub c.s.y))⁻¹ * ⟨c.s.h.a, haH⟩ * ⟨m, hmH⟩ * ⟨c.Z.z, hzH⟩ :=
      Subtype.ext hu
    rw [h1, map_mul, map_mul, map_mul, map_inv, hmτ, c.φ_a, c.φ_z]
    decide
  have hbS : b ∈ c.s.h.S := c.s.h.B_le_S (c.s.h.secB0_le_B c.s.y hbB)
  have huL : u ∈ normalizer (Seven.Lay c.s.h c.s.y : Set X) := by
    rw [hu]
    exact mul_mem (mul_mem (mul_mem (inv_mem (le_normalizer hmL)) (hG0L (mem_inf.mp haS0).2))
      (le_normalizer hmL)) (hG0L (mem_inf.mp hzS0).2)
  have huw : u ∈ centralizer ({e.w} : Set X) := by
    rw [hu]
    exact mul_mem (mul_mem (mul_mem (inv_mem hmw) haw) hmw) hzw
  have hub : u ∈ centralizer ({b} : Set X) := by
    have hmb : m ∈ centralizer ({b} : Set X) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hLB hmL) b hbB).symm
    have hab : c.s.h.a ∈ centralizer ({b} : Set X) :=
      mem_centralizer_singleton_iff.mpr (c.s.h.comm_a hbS).symm
    have hzb : c.Z.z ∈ centralizer ({b} : Set X) :=
      mem_centralizer_singleton_iff.mpr (c.Z.hzS b hbS).symm
    rw [hu]
    exact mul_mem (mul_mem (mul_mem (inv_mem hmb) hab) hmb) hzb
  have huN : u ∈ normalizer (e.K : Set X) := by
    rw [hu]
    exact mul_mem (mul_mem (mul_mem (inv_mem hmN) haN) hmN) hzN
  have huA8 : u ∈ normalizer (e.A8 : Set X) := e.mem_normalizer_A8 huH huL huw
  have hψw : zStarAct e.K ⟨e.w, hwN⟩ = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [zStarAct_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show e.w * k * e.w⁻¹ = k
    rw [← mem_centralizer_singleton_iff.mp (e.K_le k.2), mul_inv_cancel_right]
  have hSg : Seven.IsSylowIn (conjugate c.s.h.S e.d.g) (centralizer ({e.w} : Set X)) := by
    have h := isSylowIn_conjugate' c.isSylowIn_S_centralizer_z e.d.g
    rwa [GSThmB.conjugate_centralizer_singleton] at h
  obtain ⟨-, -, hKsub, -, -⟩ := id e.isPComponent_K
  obtain ⟨T, hT⟩ := isSylow_imgZ (isSylowIn_inf_of_subnormal hSg e.K_le hKsub)
  obtain ⟨hi, hii⟩ := hR18 _ (isSimpleGroup_quot_fusionZStar e.K_le e.isPComponent_K) hK
  obtain ⟨κ, hκ⟩ := hi (zStarAct e.K ⟨e.d.a', ha'N⟩) (by
      rw [← map_mul]
      have h1 : (⟨e.d.a', ha'N⟩ : ↥(normalizer (e.K : Set X))) * ⟨e.d.a', ha'N⟩ = 1 :=
        Subtype.ext e.d.a'_mul_self
      rw [h1, map_one]) T (by
      rw [hT]
      rintro _ ⟨s, hs, rfl⟩
      rw [zStarAct_mk]
      congr 1
      apply Subtype.ext
      show e.d.g⁻¹ * c.s.h.a * e.d.g * s * (e.d.g⁻¹ * c.s.h.a * e.d.g)⁻¹ = s
      have hsS : e.d.g * s * e.d.g⁻¹ ∈ c.s.h.S :=
        mem_conjugate_iff.mp (mem_inf.mp (mem_subgroupOf.mp hs)).1
      have h1 := c.s.h.comm_a hsS
      calc e.d.g⁻¹ * c.s.h.a * e.d.g * s * (e.d.g⁻¹ * c.s.h.a * e.d.g)⁻¹
          = e.d.g⁻¹ * (c.s.h.a * (e.d.g * s * e.d.g⁻¹)) * c.s.h.a⁻¹ * e.d.g := by group
        _ = e.d.g⁻¹ * (e.d.g * s * e.d.g⁻¹ * c.s.h.a) * c.s.h.a⁻¹ * e.d.g := by rw [h1]
        _ = s := by group)
  have hψu : ∃ k₀, zStarAct e.K ⟨u, huN⟩ = MulAut.conj k₀ := by
    set μ := QuotientGroup.mk' (Open.fusionZStar ↥e.K) ⟨m, hmK⟩
    have hψm : zStarAct e.K ⟨m, hmN⟩ = MulAut.conj μ := zStarAct_of_mem e.K ⟨m, hmK⟩
    have ha : (⟨c.s.h.a, haN⟩ : ↥(normalizer (e.K : Set X))) =
        ⟨e.d.a', ha'N⟩ * ⟨e.w, hwN⟩ * (⟨c.Z.z, hzN⟩)⁻¹ := by
      apply Subtype.ext
      show c.s.h.a = e.d.a' * e.d.z' * c.Z.z⁻¹
      rw [e.d.a'_mul_z', mul_inv_cancel_right]
    have h1 : (⟨u, huN⟩ : ↥(normalizer (e.K : Set X))) =
        (⟨m, hmN⟩)⁻¹ * ⟨c.s.h.a, haN⟩ * ⟨m, hmN⟩ * ⟨c.Z.z, hzN⟩ := Subtype.ext hu
    refine ⟨μ⁻¹ * κ * (zStarAct e.K ⟨c.Z.z, hzN⟩)⁻¹ μ, ?_⟩
    rw [h1, ha, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hψw, hψm, ← hκ,
      map_mul, map_mul, map_inv, ← mul_conj_mul_inv]
    group
  have huA8k : u ∈ coreActionKernel e.A8 :=
    (e.isRep_A8.mem_coreActionKernel_iff huH huA8).mpr fun α _ => by
      rw [hφu, one_mul, mul_one]
  have hA8Y : e.A8 ≤ Y := le_sup_left.trans hY8.le
  have hYC : Y ≤ centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X) :=
    le_inf (hYK.trans (inf_le_left.trans e.K_le)) (hYK.trans inf_le_right)
  have hA8C : e.A8 ≤ centralizer ({e.w} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    le_inf (e.A8_le.trans inf_le_right) (e.A8_le.trans (inf_le_left.trans hLB))
  have hA8ns : ¬ Group.IsSolvable ↥e.A8 :=
    not_isSolvable_of_isQuasisimple (isQuasisimple_of_isPComponent hA8C e.isPComponent_A8)
  have huCC : u ∈ normalizer
      ((centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X) : Subgroup X) : Set X) :=
    le_normalizer (mem_inf.mpr ⟨huw, hub⟩)
  obtain ⟨hYu, hYupc⟩ := A10T.isPComponent_conjugate huCC hYC hY
  have hA8Yu : e.A8 ≤ conjugate Y u := fun x hx => by
    rw [mem_conjugate_iff]
    exact hA8Y ((mem_normalizer_iff.mp huA8 x).mp hx)
  have hYeq := eq_of_le_of_le_of_not_isSolvable hYC hYu hY hYupc hA8Y hA8Yu hA8ns
  have huY : u ∈ normalizer (Y : Set X) := Eight2.mem_normalizer_of_conj_mem_fin fun x hx => by
    have h1 : x ∈ conjugate Y u := hYeq ▸ hx
    exact mem_conjugate_iff.mp h1
  have huYk : u ∈ coreActionKernel Y := mem_coreActionKernel_of_sup_eq hY8 huY huA8k
  have hbw : b ∈ centralizer ({e.w} : Set X) := e.secB0_le_centralizer_w hbB
  have hbN : b ∈ normalizer (e.K : Set X) := e.secB0_le_normalizer_K hbB
  have hbP2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  have hYKK : Y ≤ e.K := hYK.trans inf_le_left
  have hTE : Y ≤ centralizer ((zpowers b : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq]
    exact hYK.trans inf_le_right
  have hTb : IsPComponent 2 (Y.subgroupOf
      (centralizer ({e.w} : Set X) ⊓ centralizer ((zpowers b : Subgroup X) : Set X))) := by
    rw [centralizer_zpowers_eq]
    exact hY
  obtain ⟨hTF, hTpc⟩ := isPComponent_imgZ e.K_le e.isPComponent_K (zpowers_le.mpr hbw)
    (zpowers_le.mpr hbN) hbP2 hYKK hTE hTb
  have hTcard := card_imgZ_eq e.K_le e.isPComponent_K (zpowers_le.mpr hbw)
    (zpowers_le.mpr hbN) hbP2 hYKK hTE hTb (isSimpleGroup_quot_fusionZStar hYC hY)
  rw [card_quot_fusionZStar_eq_of_sup_eq hY8, e.card_A8] at hTcard
  have hQ2 : ∀ q ∈ actZ e.K (zpowers b), q * q = 1 := by
    rintro _ ⟨n, hn, rfl⟩
    rw [← map_mul]
    have hn' : (n : X) ∈ zpowers b := hn
    have h2 : (n : X) * (n : X) = 1 := by
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp (hb ▸ orderOf_dvd_of_mem_zpowers hn')
    have h3 : n * n = 1 := Subtype.ext h2
    rw [h3, map_one]
  have hQcard : Nat.card (actZ e.K (zpowers b)) ≤ 2 := by
    refine (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ (zStarAct e.K))).trans ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hbN)).toEquiv, Nat.card_zpowers, hb]
  have hker := hii (actZ e.K (zpowers b)) hQ2 hQcard (imgZ e.K Y) hTF hTpc hTcard
  obtain ⟨k₀, hk₀⟩ := hψu
  have htriv := zStarAct_trivial_on_imgZ hYKK ⟨u, huN⟩ huYk
  rw [hk₀] at htriv
  have hk₀T : k₀ ∈ coreActionKernel (imgZ e.K Y) := by
    have hN : k₀ ∈ normalizer ((imgZ e.K Y : Subgroup _) : Set _) :=
      Eight2.mem_normalizer_of_conj_mem_fin fun x hx => by
        have h1 := (htriv x hx).1
        rwa [MulAut.conj_apply] at h1
    refine mem_coreActionKernel.mpr ⟨hN, fun j hj => ?_⟩
    have hj' : k₀⁻¹ * j⁻¹ * k₀ ∈ imgZ e.K Y := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hN) j⁻¹).mp (inv_mem hj)
      rwa [inv_inv] at h1
    have h1 := (htriv _ hj').2
    rw [MulAut.conj_apply] at h1
    have e1 : j⁻¹ * k₀⁻¹ * j * k₀ =
        k₀ * (k₀⁻¹ * j⁻¹ * k₀) * k₀⁻¹ * (k₀⁻¹ * j⁻¹ * k₀)⁻¹ := by group
    rw [e1]
    exact h1
  rw [hker, mem_bot] at hk₀T
  rw [hk₀T, map_one] at hk₀
  obtain ⟨o, k, ho1, hok⟩ := exists_pow_ne_one_two (hu ▸ even_orderOf_conj_a_mul_z c m)
  have hc₂B : u ^ o ∈ c.s.h.secB0 c.s.y :=
    c.mem_B0_of_φ_eq_one (w := ⟨u ^ o, pow_mem huH o⟩) hok (by
      rw [show (⟨u ^ o, pow_mem huH o⟩ : ↥(c.s.h.secSub c.s.y)) = ⟨u, huH⟩ ^ o from
        Subtype.ext (by simp), map_pow, hφu, one_pow])
  have hc₂K : u ^ o ∈ coreActionKernel e.K :=
    (zStarAct_eq_one_iff e.K_le e.isPComponent_K ⟨u ^ o, pow_mem huN o⟩).mp (by
      rw [show (⟨u ^ o, pow_mem huN o⟩ : ↥(normalizer (e.K : Set X))) = ⟨u, huN⟩ ^ o from
        Subtype.ext (by simp), map_pow, hk₀, one_pow])
  have h1 : u ^ o ∈ c.s.h.secB0 c.s.y ⊓ coreActionKernel e.K := mem_inf.mpr ⟨hc₂B, hc₂K⟩
  rw [hB01, mem_bot] at h1
  exact ho1 h1

end Ctx.CaseIIIp

end CFSG.ComponentClassification.GSThmB.A10T
