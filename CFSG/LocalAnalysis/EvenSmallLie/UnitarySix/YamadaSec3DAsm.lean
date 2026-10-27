module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp7

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

structure HypAut {G : Type*} [Group G] (d : YamadaD.Data G) : Prop where
  NHA₄_le : normalizer (d.A₄ : Set G) ⊓ d.H ≤ normalizer (d.A₃ : Set G)
  oTwo_NA₄ : ∀ P : Subgroup G, P ≤ normalizer (d.withT d.A₄ : Set G) ⊓ d.H →
    normalizer (d.withT d.A₄ : Set G) ⊓ d.H ≤ normalizer (P : Set G) → IsPGroup 2 P →
    P ≤ d.withT d.A₃
  oTwo_CA₄ : ∀ P : Subgroup G, P ≤ centralizer (d.A₄ : Set G) ⊓ d.H →
    centralizer (d.A₄ : Set G) ⊓ d.H ≤ normalizer (P : Set G) → IsPGroup 2 P →
    P ≤ d.withT d.A₃
  Λ_comm_CA₄ : ∀ l ∈ d.Λ, ∀ n ∈ centralizer (d.A₄ : Set G) ⊓ d.H, ⁅l, n⁆ ∈ d.withT d.A₃
  center_CA₄ : ∀ n ∈ centralizer (d.A₄ : Set G) ⊓ d.H,
    (∀ m ∈ centralizer (d.A₄ : Set G) ⊓ d.H, ⁅n, m⁆ ∈ d.withT d.A₃) → n ^ 3 ∈ d.withT d.A₃
  CHz_le : centralizer ({d.z} : Set G) ⊓ d.H ≤ normalizer (d.A₁ : Set G)
  CH_A₁ : centralizer (d.A₁ : Set G) ⊓ d.H ≤ d.ZR
  oTwo_CHz : ∀ P : Subgroup G, P ≤ centralizer ({d.z} : Set G) ⊓ d.H →
    centralizer ({d.z} : Set G) ⊓ d.H ≤ normalizer (P : Set G) → IsPGroup 2 P →
    P ≤ d.withT d.A₁
  card_CHz : Nat.card (centralizer ({d.z} : Set G) ⊓ d.H : Subgroup G) ∣ 2 ^ 17 * 3 ^ 5 * 5
  CH_A₁_mod : ∀ n ∈ d.H, n ∈ normalizer (d.A₁ : Set G) →
    (∀ a ∈ d.A₁, n * a * n⁻¹ * a⁻¹ ∈ zpowers d.z) → n ∈ d.withT d.A₁
  NZ₂S : ∀ c ∈ d.H, c * d.e = d.e * c → c ∈ normalizer (d.Z₂S : Set G) →
    c ∈ normalizer (d.A₄ : Set G)

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

theorem hyp416_sec3DData : Hyp416 (sec3DData e t) where
  X₁_le_A₁ := d_X₁_le_A₁
  A₁_le_conj := d_A₁_le_conj
  A₂_closure := d_A₂_closure
  CA₁A₂ := d_CA₁A₂
  A₁A₂_le_comm := d_A₁A₂_le_comm
  card_A₁A₂ := d_card_A₁A₂

theorem hypQ_sec3DData (hNZ : ∀ c ∈ (sec3DData e t).H, c * (sec3DData e t).e =
      (sec3DData e t).e * c → c ∈ normalizer ((sec3DData e t).Z₂S : Set G) →
        c ∈ normalizer ((sec3DData e t).A₄ : Set G)) : HypQ (sec3DData e t) where
  e_mem_Sig := d_e_mem_Sig
  j₀_comm_e := d_j₀_comm_e
  w₂₃₂_sq := d_w₂₃₂_sq
  w₂₃₂_mem_K₁ := d_w₂₃₂_mem_K₁
  w₂₃₂_comm_e := d_w₂₃₂_comm_e
  w₂₃₂_comm_j₀ := d_w₂₃₂_comm_j₀
  w₂₃₂_X₈ := d_w₂₃₂_X₈
  Z₂S_inf := d_Z₂S_inf_g
  CA₁e := d_CA₁e
  NZ₂S := hNZ


end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
