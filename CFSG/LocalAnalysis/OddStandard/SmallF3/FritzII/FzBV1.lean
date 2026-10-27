module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBM1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRFu

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {c : Bool} {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau : G} {T₂ P : Subgroup G} {q s : G} {β : ℕ → G}

theorem fzb_chart_q (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β) (hF : FzbFactsGen c) :
    q ^ 2 = t ∧ q ^ 4 = 1 ∧ t ≠ 1 ∧ β 320 = q * s ∧ β 832 = q * s * lam := by
  have h64 : (64 : ℕ) < 1024 := by norm_num
  have h128 : (128 : ℕ) < 1024 := by norm_num
  have h256 : (256 : ℕ) < 1024 := by norm_num
  have h320 : (320 : ℕ) < 1024 := by norm_num
  have h512 : (512 : ℕ) < 1024 := by norm_num
  have hqq : β 128 = q * q := by
    have := hβ.mul 64 h64 64 h64
    rwa [hF.t_eq, hβ.q_eq] at this
  have hq2 : q ^ 2 = t := by rw [pow_two, ← hqq, hβ.t_eq]
  have htt : t * t = 1 := by
    have := hβ.mul 128 h128 128 h128
    rw [hF.sq_t, hβ.one, hβ.t_eq] at this
    exact this.symm
  have hq4 : q ^ 4 = 1 := by
    calc q ^ 4 = (q ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = t * t := by rw [hq2, pow_two]
      _ = 1 := htt
  have htne : t ≠ 1 := by
    intro ht1
    have h1 : β 128 = β 0 := by rw [hβ.t_eq, ht1, hβ.one]
    have := hβ.inj 128 h128 0 (by norm_num) h1
    norm_num at this
  have hqs : β 320 = q * s := by
    have := hβ.mul 64 h64 256 h256
    rwa [hF.qs_eq, hβ.q_eq, hβ.s_eq] at this
  have hqsy : β 832 = q * s * lam := by
    have := hβ.mul 320 h320 512 h512
    rwa [hF.qsy_eq, hqs, hβ.lam_eq] at this
  exact ⟨hq2, hq4, htne, hqs, hqsy⟩

theorem fzb_Z_not_conj (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    (hS : FzbStruct t S x₁ x₂ lam rho tau T₂ P q s) (hβ : FzbChart c T₂ P x₁ x₂ t q s lam β)
    (hF : FzbFactsGen c) {z : G} (hz : z ∈ fourGrp x₁ x₂) (hz1 : z ≠ 1) :
    ¬ ∃ g : G, g⁻¹ * t * g = z := by
  rintro ⟨g, hg⟩
  obtain ⟨x, hx4, hxβ⟩ := (hβ.Z_eq z).mp hz
  have hx1024 : x < 1024 := by omega
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hz1 (by rw [← hxβ, hβ.one])
  have hxpos : 0 < x := Nat.pos_of_ne_zero hx0
  have hAgt : 256 < ((Finset.range 1024).filter (fun n => fzbMul c n x = fzbMul c x n)).card :=
    hF.F3 x hxpos hx4
  have hset : ∀ n : ℕ, (n < 1024 ∧ β n ∈ invCent z) ↔
      n ∈ (Finset.range 1024).filter (fun n => fzbMul c n x = fzbMul c x n) := by
    intro n
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hmem⟩
      refine ⟨hn, ?_⟩
      have hmem' : β n * z = z * β n :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (show β n ∈ Subgroup.centralizer ({z} : Set G) from hmem)
      rw [← hxβ] at hmem'
      exact (fzb_chart_comm hβ hF.mul_lt hn hx1024).mpr hmem'
    · rintro ⟨hn, hp⟩
      refine ⟨hn, ?_⟩
      have h1 : β n * β x = β x * β n := (fzb_chart_comm hβ hF.mul_lt hn hx1024).mp hp
      rw [hxβ] at h1
      exact Subgroup.mem_centralizer_singleton_iff.mpr h1
  have hcard : Nat.card {n : ℕ // n < 1024 ∧ β n ∈ invCent z} =
      ((Finset.range 1024).filter (fun n => fzbMul c n x = fzbMul c x n)).card :=
    Nat.subtype_card _ (fun n => (hset n).symm)
  have hbig : 256 < Nat.card ↥(T₂ ⊓ invCent z) := by
    rw [← fzb_chart_card hβ (invCent z), hcard]
    exact hAgt
  have hle := fzr_card_cent_le (fzr_isSylowOf_S h.toCtx0) hS.isPGroup hS.S_le
    (⟨g, hg⟩ : ∃ k : G, k⁻¹ * t * k = z)
  have hcardS : Nat.card S = 256 := by rw [h.card_S, hK]; norm_num
  rw [hcardS] at hle
  omega

end CFSG.OddStandard.SmallF3.FritzII
