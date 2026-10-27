module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V9
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25E6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V8

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.AE (AEQ mkQ memBar Wr)
open CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL (layerX_le_centralizer conjSub_layerX_of_mem le_layerX
  mem_coreHull_of_mem_layerX layerBarHullEquiv_mk layer_twinData)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped commutatorElement MatrixGroups

section CaseB

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ c : G}

namespace KerMap

variable {B : Type} [Group B] (Kf : KerMap Ω c B)

@[expose] def img (R₀ : Subgroup G) (hR : R₀ ≤ layerX Ω c) : Subgroup B where
  carrier := {x | ∃ r ∈ R₀, Kf.f r = x}
  mul_mem' := by
    rintro _ _ ⟨r₁, h₁, rfl⟩ ⟨r₂, h₂, rfl⟩
    exact ⟨r₁ * r₂, R₀.mul_mem h₁ h₂, Kf.mul _ (hR h₁) _ (hR h₂)⟩
  one_mem' := ⟨1, R₀.one_mem, Kf.one⟩
  inv_mem' := by
    rintro _ ⟨r, h, rfl⟩
    exact ⟨r⁻¹, R₀.inv_mem h, Kf.inv (hR h)⟩

theorem f_pow {n : G} (hn : n ∈ layerX Ω c) (k : ℕ) : Kf.f (n ^ k) = Kf.f n ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Kf.one]
  | succ k ih => rw [pow_succ, pow_succ, Kf.mul _ (Subgroup.pow_mem _ hn k) _ hn, ih]

theorem card_img {P R₀ : Subgroup G} (hPX : P ≤ layerX Ω c) (hP : IsPGroup 2 ↥P) (hR₀ : R₀ ≤ P) :
    Nat.card (Kf.img R₀ (hR₀.trans hPX)) = Nat.card R₀ := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun y : R₀ => (⟨Kf.f y, y, y.2, rfl⟩ : Kf.img R₀ (hR₀.trans hPX))) ⟨?_, ?_⟩)
  · intro y₁ y₂ h
    apply Subtype.ext
    exact Kf.inj_P2 hPX hP (hR₀ y₁.2) (hR₀ y₂.2) (congrArg Subtype.val h)
  · rintro ⟨x, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

end KerMap

theorem pow_norm {P : Subgroup G} {n : G} (h : ∀ y ∈ P, n * y * n⁻¹ ∈ P) (k : ℕ) :
    ∀ y ∈ P, n ^ k * y * (n ^ k)⁻¹ ∈ P := by
  induction k with
  | zero => intro y hy; simpa using hy
  | succ k ih =>
    intro y hy
    have e : n ^ (k + 1) * y * (n ^ (k + 1))⁻¹ = n * (n ^ k * y * (n ^ k)⁻¹) * n⁻¹ := by
      rw [pow_succ']; group
    rw [e]
    exact h _ (ih y hy)

theorem pow_fix {n y : G} (h : n * y * n⁻¹ = y) (k : ℕ) : n ^ k * y * (n ^ k)⁻¹ = y := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : n ^ (k + 1) * y * (n ^ (k + 1))⁻¹ = n * (n ^ k * y * (n ^ k)⁻¹) * n⁻¹ := by
      rw [pow_succ']; group
    rw [e, ih, h]

namespace AE5Layer

variable (A : AE5Layer Ω z c)

theorem eps_pow_conj (hΩ : HypOmegaGen Ω) {n : G} (hn : n ∈ Subgroup.centralizer ({c} : Set G)) {x : AEQ 5}
    (hx : ∀ y ∈ layerX Ω c, A.ε (n * y * n⁻¹) = x * A.ε y * x⁻¹) (j : ℕ) :
    ∀ y ∈ layerX Ω c, n ^ j * y * (n ^ j)⁻¹ ∈ layerX Ω c ∧
      A.ε (n ^ j * y * (n ^ j)⁻¹) = x ^ j * A.ε y * (x ^ j)⁻¹ := by
  induction j with
  | zero => intro y hy; simpa using hy
  | succ j ih =>
    intro y hy
    obtain ⟨h1, h2⟩ := ih y hy
    have e : n ^ (j + 1) * y * (n ^ (j + 1))⁻¹ = n * (n ^ j * y * (n ^ j)⁻¹) * n⁻¹ := by
      rw [pow_succ']; group
    refine ⟨?_, ?_⟩
    · rw [e]
      exact AE5Layer.conj_mem hΩ hn h1
    · rw [e, hx _ h1, h2, pow_succ']
      group

theorem cent_trivial {x : AEQ 5} (h : ∀ y ∈ layerX Ω c, x * A.ε y = A.ε y * x) : x = 1 := by
  obtain ⟨ha0v, ha0p, hb0v, hb0p⟩ := AE5Sq.gens_spec
  obtain ⟨y, hy, hye⟩ := A.surj _ (AE5Sq.mkQ_mem_aeModel ha0v ha0p)
  obtain ⟨y', hy', hye'⟩ := A.surj _ (AE5Sq.mkQ_mem_aeModel hb0v hb0p)
  exact spec_cent x (by rw [← hye]; exact h y hy) (by rw [← hye']; exact h y' hy')

end AE5Layer

theorem odd_trivial_on_R {c₁ c₂ : G} (Λ₁ : Lay Ω K K' W S R R' z t u₁ u₂ c₁) (hc : c₂ * z = c₁)
    (A₁ : AE5Layer Ω z c₁) {n : G} (hnc₂ : n * c₂ = c₂ * n)
    (hnP : ∀ y ∈ R ⊔ R', n * y * n⁻¹ ∈ R ⊔ R') (hnR' : ∀ y ∈ R', n * y * n⁻¹ = y) {m : ℕ} (hm : Odd m)
    (hnm : n ^ m = 1) : ∀ y ∈ R, n * y * n⁻¹ = y := by
  obtain ⟨α, α', h, h', b, b', T₁⟩ := A₁.exists_labels Λ₁
  have hnz : n * z = z * n := by
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [hnR' z Λ₁.z_mem_R']
  have hnc₁ : n * c₁ = c₁ * n := by
    rw [← hc]
    calc n * (c₂ * z) = (n * c₂) * z := by group
      _ = (c₂ * n) * z := by rw [hnc₂]
      _ = c₂ * (n * z) := by group
      _ = c₂ * (z * n) := by rw [hnz]
      _ = (c₂ * z) * n := by group
  have hnC₁ : n ∈ Subgroup.centralizer ({c₁} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hnc₁
  obtain ⟨x, hx⟩ := A₁.act n hnC₁
  have hxm : x ^ m = 1 := by
    apply A₁.cent_trivial
    intro y hy
    have h1 := (A₁.eps_pow_conj Λ₁.hΩ hnC₁ hx m y hy).2
    rw [hnm] at h1
    simp only [one_mul, inv_one, mul_one] at h1
    calc x ^ m * A₁.ε y = (x ^ m * A₁.ε y * (x ^ m)⁻¹) * x ^ m := by group
      _ = A₁.ε y * x ^ m := by rw [← h1]
  have hx15 : x ^ 15 = 1 := pow_fifteen_of_odd hm hxm
  have hxc : ∀ w ∈ memBar α' h' b', x * w = w * x := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := T₁.R'_surj w hw
    have h1 := hx y (Λ₁.R'_le hy)
    rw [hnR' y hy] at h1
    calc x * A₁.ε y = (x * A₁.ε y * x⁻¹) * x := by group
      _ = A₁.ε y * x := by rw [← h1]
  have hx1 : x = 1 := spec_odd h' b' x hxc hx15
  intro y hy
  have hyP : y ∈ R ⊔ R' := Subgroup.mem_sup_left hy
  apply A₁.inj_P2 Λ₁ (hnP y hyP) hyP
  rw [hx y (Λ₁.R_le hy), hx1]
  group

theorem conj_mul_comm {B : Type} [Group B] {ω X W : B} (h : ω * W = W * ω) :
    ω * X * ω⁻¹ * W = ω * (X * W) * ω⁻¹ := by
  calc ω * X * ω⁻¹ * W = ω * X * ω⁻¹ * (ω * W * ω⁻¹) := by rw [h]; group
    _ = ω * (X * W) * ω⁻¹ := by group

namespace Lay

variable (Λ : Lay Ω K K' W S R R' z t u₁ u₂ c)
include Λ

theorem R_sylow : IsSylow2In R K :=
  Sec6Gen.isSylow2In_of_mem_RSet_of_le Λ.hyp.std.setting.stand.hyp Λ.hyp.std.1.stand.mem Λ.hyp.hR.1
    Λ.hyp.hR.2.1

theorem R'_sylow : IsSylow2In R' K' :=
  Sec6Gen.isSylow2In_of_mem_RSet_of_le Λ.hyp.std.setting.stand.hyp Λ.hyp.std.1.hK'.1 Λ.hyp.hR'.1
    Λ.hyp.hR'.2.1

theorem R_card : Nat.card ↥R = 8 := Λ.hyp.std.1.stand.card8 K Λ.hyp.std.1.stand.mem R Λ.R_sylow

theorem R'_card : Nat.card ↥R' = 8 := Λ.hyp.std.1.stand.card8 K' Λ.hyp.std.1.hK'.1 R' Λ.R'_sylow

theorem kerMap_mem_secImg {y : G} (hy : y ∈ R) : Λ.kerMap.f y ∈ secImg Ω c K := by
  have hKtq := (layer_twins_tq Λ.hyp Λ.hcA).1
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Λ.hcR x hx).symm
  obtain ⟨huC, huY, hmem⟩ := layer_mem_secImg Λ.hΩ Λ.hc2' hKtq Λ.R_sylow hRc hy
  rw [Λ.kerMap_f (Λ.R_le hy) huC huY]
  exact hmem

theorem kerMap_mem_secImg' {y : G} (hy : y ∈ R') : Λ.kerMap.f y ∈ secImg Ω c K' := by
  have hK'tq := (layer_twins_tq Λ.hyp Λ.hcA).2.1
  have hR'c : R' ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Λ.hcR' x hx).symm
  obtain ⟨huC, huY, hmem⟩ := layer_mem_secImg Λ.hΩ Λ.hc2' hK'tq Λ.R'_sylow hR'c hy
  rw [Λ.kerMap_f (Λ.R'_le hy) huC huY]
  exact hmem

end Lay

theorem caseB {c₁ c₂ : G} (Λ₁ : Lay Ω K K' W S R R' z t u₁ u₂ c₁) (Λ₂ : Lay Ω K K' W S R R' z t u₁ u₂ c₂)
    (hc : c₂ * z = c₁) (A₁ : AE5Layer Ω z c₁) (hno : SecNoExitAt Ω c₂) (hL : LayerLie Ω c₂ 5) : False := by
  classical
  obtain ⟨A, A', z', ⟨fr⟩, hKA, hK'A'⟩ := exists_frame_at Λ₂ hno hL
  have hF : Nat.card (GaloisField 3 1) = 3 := Q3T7P25.natCard_gf3
  haveI : Finite (GaloisField 3 1) := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨r⟩ := EndL.Q8.nonempty_ringEquiv hF
  have h2F : (2 : GaloisField 3 1) ≠ 0 := M.two_ne_zero_gf 1 (by norm_num)
  have hRX : R ≤ layerX Ω c₂ := Λ₂.R_le
  have hR'X : R' ≤ layerX Ω c₂ := Λ₂.R'_le
  obtain ⟨Kf, hKfmem⟩ : ∃ Kf : KerMap Ω c₂
      (↥(coreHull Ω c₂) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c₂)),
      (∀ y ∈ R, Kf.f y ∈ secImg Ω c₂ K) ∧ (∀ y ∈ R', Kf.f y ∈ secImg Ω c₂ K') :=
    ⟨Λ₂.kerMap, fun y hy => Λ₂.kerMap_mem_secImg hy, fun y hy => Λ₂.kerMap_mem_secImg' hy⟩
  have hRimg : Kf.img R hRX = (EndL.Q8.Qsub r).map (fr.ψ.comp (longBlock (GaloisField 3 1) 2 0)) := by
    refine EndL.Q8.sub_eq_map_Qsub r fr h2F 0 ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      rw [← fr.hA]
      exact hKA (hKfmem.1 y hy)
    · rw [Kf.card_img Λ₂.P_le Λ₂.P_two le_sup_left]
      exact Λ₂.R_card
  have hR'img : Kf.img R' hR'X =
      (EndL.Q8.Qsub r).map (fr.ψ.comp (longBlock (GaloisField 3 1) 2 1)) := by
    refine EndL.Q8.sub_eq_map_Qsub r fr h2F 1 ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      rw [← fr.hA']
      exact hK'A' (hKfmem.2 y hy)
    · rw [Kf.card_img Λ₂.P_le Λ₂.P_two le_sup_right]
      exact Λ₂.R'_card
  have hRq : ∀ y ∈ R, ∃ q ∈ EndL.Q8.Qsub r, fr.ψ (longBlock (GaloisField 3 1) 2 0 q) = Kf.f y := by
    intro y hy
    have : Kf.f y ∈ Kf.img R hRX := ⟨y, hy, rfl⟩
    rw [hRimg] at this
    obtain ⟨q, hq, hqe⟩ := this
    exact ⟨q, hq, hqe⟩
  have hRq' : ∀ q ∈ EndL.Q8.Qsub r, ∃ y ∈ R, Kf.f y = fr.ψ (longBlock (GaloisField 3 1) 2 0 q) := by
    intro q hq
    have : fr.ψ (longBlock (GaloisField 3 1) 2 0 q) ∈ Kf.img R hRX := by
      rw [hRimg]
      exact ⟨q, hq, rfl⟩
    exact this
  have hR'q : ∀ y ∈ R', ∃ q ∈ EndL.Q8.Qsub r, fr.ψ (longBlock (GaloisField 3 1) 2 1 q) = Kf.f y := by
    intro y hy
    have : Kf.f y ∈ Kf.img R' hR'X := ⟨y, hy, rfl⟩
    rw [hR'img] at this
    obtain ⟨q, hq, hqe⟩ := this
    exact ⟨q, hq, hqe⟩
  obtain ⟨b, -, hbk⟩ := exists_b r
  have hωR' : ∀ y ∈ R', fr.ψ (longBlock (GaloisField 3 1) 2 0 b) * Kf.f y =
      Kf.f y * fr.ψ (longBlock (GaloisField 3 1) 2 0 b) := by
    intro y hy
    obtain ⟨q', -, hq'⟩ := hR'q y hy
    rw [← hq', ← map_mul, ← map_mul,
      M.commute_L 0 (⟨b, rfl⟩ : longBlock (GaloisField 3 1) 2 0 b ∈ longRootSp2 (GaloisField 3 1) 2 0)
        (⟨q', rfl⟩ : longBlock (GaloisField 3 1) 2 1 q' ∈ longRootSp2 (GaloisField 3 1) 2 (Fin.rev 0))]
  have hnorm : ∀ y ∈ R ⊔ R', ∃ y' ∈ R ⊔ R', Kf.f y' =
      fr.ψ (longBlock (GaloisField 3 1) 2 0 b) * Kf.f y *
        (fr.ψ (longBlock (GaloisField 3 1) 2 0 b))⁻¹ := by
    intro y hy
    obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := mem_sup_comm Λ₂.RR'_comm hy
    obtain ⟨q, hq, hqe⟩ := hRq ρ hρ
    have hbq : b * q * b⁻¹ ∈ EndL.Q8.Qsub r := by
      rw [EndL.Q8.mem_Qsub, conj_pow, EndL.Q8.Qsub_one_pow r hq]
      group
    obtain ⟨ρ₁, hρ₁, hρ₁e⟩ := hRq' _ hbq
    refine ⟨ρ₁ * ρ', Subgroup.mul_mem_sup hρ₁ hρ', ?_⟩
    have hω' := hωR' ρ' hρ'
    have hconjω : fr.ψ (longBlock (GaloisField 3 1) 2 0 (b * q * b⁻¹)) =
        fr.ψ (longBlock (GaloisField 3 1) 2 0 b) * fr.ψ (longBlock (GaloisField 3 1) 2 0 q) *
          (fr.ψ (longBlock (GaloisField 3 1) 2 0 b))⁻¹ := by
      simp only [map_mul, map_inv]
    rw [Kf.mul ρ₁ (hRX hρ₁) ρ' (hR'X hρ'), Kf.mul ρ (hRX hρ) ρ' (hR'X hρ'), hρ₁e, ← hqe, hconjω]
    exact conj_mul_comm hω'
  obtain ⟨n, hnX, hnf, hnP⟩ := Kf.lift Λ₂.P_le Λ₂.P_two hnorm
  have hnR' : ∀ y ∈ R', n * y * n⁻¹ = y := by
    intro y hy
    have hyP : y ∈ R ⊔ R' := Subgroup.mem_sup_right hy
    apply Kf.inj_P2 Λ₂.P_le Λ₂.P_two (hnP y hyP) hyP
    rw [Kf.f_conj hnX (hR'X hy), hnf, hωR' y hy]
    group
  obtain ⟨s, m, hm, hord, -⟩ := exists_pow_two_part n
  have hn₁m : (n ^ 2 ^ s) ^ m = 1 := by
    rw [← pow_mul, ← hord]
    exact pow_orderOf_eq_one n
  have hn₁X : n ^ 2 ^ s ∈ layerX Ω c₂ := Subgroup.pow_mem _ hnX _
  have hn₁c₂ : n ^ 2 ^ s * c₂ = c₂ * n ^ 2 ^ s :=
    Subgroup.mem_centralizer_singleton_iff.mp (layerX_le_centralizer Ω c₂ hn₁X)
  have htriv := odd_trivial_on_R Λ₁ hc A₁ hn₁c₂ (pow_norm hnP (2 ^ s))
    (fun y hy => pow_fix (hnR' y hy) (2 ^ s)) hm hn₁m
  have hk : 2 ^ s % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ 2 ^ s := Nat.dvd_of_mod_eq_zero h0
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  obtain ⟨q, hq, hqne⟩ := hbk (2 ^ s) hk
  obtain ⟨r₀, hr₀, hr₀e⟩ := hRq' q hq
  have hconj : Kf.f (n ^ 2 ^ s * r₀ * (n ^ 2 ^ s)⁻¹) =
      fr.ψ (longBlock (GaloisField 3 1) 2 0 (b ^ 2 ^ s * q * (b ^ 2 ^ s)⁻¹)) := by
    rw [Kf.f_conj hn₁X (hRX hr₀), Kf.f_pow hnX, hnf, hr₀e]
    simp only [map_mul, map_inv, map_pow]
  rw [htriv r₀ hr₀, hr₀e] at hconj
  have hinj : q = b ^ 2 ^ s * q * (b ^ 2 ^ s)⁻¹ := M.injective_ψ_longBlock fr h2F 0 (by exact hconj)
  apply hqne
  calc b ^ 2 ^ s * q = (b ^ 2 ^ s * q * (b ^ 2 ^ s)⁻¹) * b ^ 2 ^ s := by group
    _ = q * b ^ 2 ^ s := by rw [← hinj]

end CaseB

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X
