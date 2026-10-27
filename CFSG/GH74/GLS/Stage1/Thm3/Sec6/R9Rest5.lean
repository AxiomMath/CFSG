module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Rest4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Final46
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Final
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Lem64
import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx67

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem prop49_y (hII : II4_4_4_center) (hq : II4_4_quat) (hdiag : IVK_diag_unique)
    (h19 : IVK_1_9_outer) (hsd : SD_facts) (hsdq : SD_sq_not_z) (hqc : Quat_centr) (hrn : Rnormal4)
    (hshape : Bg.B_two_maximalClass_shape)
    (h : Std4r1 G z S K F) (hQF : Qz S z = F) (hquat : ∃ n, IVK.IsQuaternionTwoGroup ↥F n)
    {U : Subgroup G} (hUR : U ≤ Rz S z) (hU4 : IVK.IsFourSubgroup U)
    (hUn : ∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) {x : G}
    (hxW : x ∈ normalizer ((S ⊓ centralizer (U : Set G) : Subgroup G) : Set G))
    (hxU : x ∈ normalizer (U : Set G)) (hxz : x * z * x⁻¹ ≠ z)
    (hcard : Nat.card ↥(Pz S z) = Nat.card ↥(Qz S z)) (hidx : (Rz S z).relIndex S = 2) :
    ∃ y ∈ S, orderOf y = 2 ∧ y ∉ Rz S z ∧
      ∃ n, IVK.IsSemidihedralTwoGroup ↥(Qz S z ⊔ zpowers y) n := by
  classical
  have hcfg := cfg1K_Q hII hq hdiag h19 hsd hsdq hqc hrn h hQF
  have hF := h.F_eq hQF
  obtain ⟨nQ, hnQ⟩ : ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ cSec K) n := hF ▸ hquat
  obtain ⟨nP, hnP⟩ := h.P_quat hq
  have hzQ := h.z_mem_Q hII
  have hz2 := h.z_sq
  have hz1 := h.z_ne
  have hRP : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := h.Rz_eq
  have hUR' : U ≤ (S ⊓ K) ⊔ (S ⊓ cSec K) := hRP ▸ hUR
  have hU4' : R1.Four U := Std4r1.four_of U hU4
  have hQinv := R1.quat_invol_sub hnQ hzQ hz2 hz1
  obtain ⟨u, huU, hu1, huz⟩ : ∃ u ∈ U, u ≠ 1 ∧ u ≠ z := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ e ∈ U, e ∈ ({1, z} : Finset G) := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases he1 : e = 1
      · exact Or.inl he1
      · exact Or.inr (hcon e he he1)
    have h1 := B.card_subgroup_le_finset U _ hsub
    have h2 : ({1, z} : Finset G).card ≤ 2 := Finset.card_le_two
    have h3 := hU4'.2
    omega
  obtain ⟨u₁, hu₁P, u₂, hu₂Q, hu, hu₁sq, hu₂sq⟩ :=
    hcfg.toCfg1.decomp_four' hQinv (hUR' huU) (hU4'.1 u huU) hu1 huz
  have hnorm := fun (s : G) (hs : s ∈ S) =>
    hcfg.toCfg1.conj_comp hUR' hU4' hUn huU hu1 huz hu₁P hu₂Q hu hs
  obtain ⟨V₁, hV₁eq, hV₁c, hV₁i⟩ :=
    hcfg.toCfg1.P_centr u₁ hu₁P hu₁sq (fun s hs => (hnorm s hs).1)
  obtain ⟨hV₂c, hV₂i⟩ := hqc G (S ⊓ cSec K) z u₂ nQ hnQ hzQ hz2 hz1 hu₂Q hu₂sq
    (fun q hq => (hnorm q hq.1).2)
  have c9 : R1.Setup9 G z S (S ⊓ K) (S ⊓ cSec K) (fun s => InducesFAut s K) U x u₁ u₂ :=
    { cfg := hcfg.toCfg1
      quatP := ⟨nP, hnP⟩
      quatQ := ⟨nQ, hnQ⟩
      card_eq := by rw [← h.Pz_eq, ← h.Qz_eq]; exact hcard
      idx := by rw [← hRP]; exact hidx
      U_le := hUR'
      U_four := hU4'
      U_norm := hUn
      u₁_mem := hu₁P
      u₂_mem := hu₂Q
      u₁_sq := hu₁sq
      u₂_sq := hu₂sq
      u_mem := hu ▸ huU
      V₁_cyc := by rw [← hV₁eq]; exact hV₁c
      V₁_idx := by rw [← hV₁eq]; exact hV₁i
      V₂_cyc := hV₂c
      V₂_idx := hV₂i
      x_W := Subgroup.mem_normalizer_iff.1 hxW
      x_U := fun v hv => (Subgroup.mem_normalizer_iff.1 hxU v).1 hv
      x_z := hxz }
  obtain ⟨y, hyS, hy2, hyR, n, hn⟩ :=
    c9.exists_y_sd CFSG.GH74.Uniqueness.SU.SU1.b_maximalClass_of_small_centralizer hshape
  have hy1 : y ≠ 1 := fun e => hyR (e ▸ (one_mem _))
  refine ⟨y, hyS, orderOf_eq_prime (by rw [sq]; exact hy2) hy1, ?_, n, ?_⟩
  · rw [hRP]; exact hyR
  · rw [h.Qz_eq]; exact hn

end CFSG.GH74.GLS.Stage1.Thm3.Sec6

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

@[expose] def Prop49_local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K F : Subgroup G), Std4r1 G z S K F →
    Qz S z = F → (∃ n, IVK.IsQuaternionTwoGroup ↥F n) →
      ∀ U : Subgroup G, U ≤ Rz S z → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) →
        ∀ x : G, IsPGroup 3 ↥(zpowers x) →
          x ∈ normalizer ((S ⊓ centralizer (U : Set G) : Subgroup G) : Set G) →
          x ∈ normalizer (U : Set G) → x * z * x⁻¹ ≠ z →
          Nat.card ↥(Pz S z) = Nat.card ↥(Qz S z) → (Rz S z).relIndex S = 2 →
          (∃ y ∈ S, orderOf y = 2 ∧ y ∉ Rz S z ∧
              ∃ n, IVK.IsSemidihedralTwoGroup ↥(Qz S z ⊔ zpowers y) n) →
            Nat.card ↥(Pz S z) = 8 ∧
            HasSL2ProductOfIndexTwoStage1 (oPrimeResidual 2 (CentralizerBar z)) 3 ∧
            ∀ v ∈ Rz S z, v * v = 1 → v ≠ 1 → IsConj z v

theorem isQuat_three {G : Type} [Group G] {Y : Subgroup G} {n : ℕ} (hY : IVK.IsQuaternionTwoGroup ↥Y n)
    (h8 : Nat.card ↥Y = 8) : IVK.IsQuaternionTwoGroup ↥Y 3 := by
  have h1 := R1.card_of_quat hY
  have h2 : 2 ^ n = 2 ^ 3 := by rw [← h1, h8]; norm_num
  have := Nat.pow_right_injective (le_refl 2) h2
  rw [this] at hY
  exact hY

theorem mod8_of_two_val {q : ℕ} (hodd : Odd q) (h : (q ^ 2 - 1).factorization 2 = 3) :
    q % 8 = 3 ∨ q % 8 = 5 := by
  have hne : q ^ 2 - 1 ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  have hp : Nat.Prime 2 := Nat.prime_two
  have h8 : 2 ^ 3 ∣ q ^ 2 - 1 := (hp.pow_dvd_iff_le_factorization hne).2 (by omega)
  have h16 : ¬ 2 ^ 4 ∣ q ^ 2 - 1 := fun hd => by
    have := (hp.pow_dvd_iff_le_factorization hne).1 hd
    omega
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by rcases hodd with ⟨k, rfl⟩; omega)
  have hmod : (q ^ 2) % 16 = ((q % 16) ^ 2) % 16 := Nat.pow_mod q 2 16
  have hr : q % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hodd' : q % 2 = 1 := Nat.odd_iff.1 hodd
  norm_num at h8 h16
  generalize hr' : q % 16 = r at hmod hr
  have hq8 : q % 8 = r % 8 := by omega
  rw [hq8]
  interval_cases r <;> omega

theorem two_val_mul_odd' {a b : ℕ} (ha : a ≠ 0) (hb : Odd b) :
    (a * b).factorization 2 = a.factorization 2 := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have h2 : ¬ 2 ∣ b := fun h => (Nat.not_even_iff_odd.2 hb) (even_iff_two_dvd.2 h)
  rw [Nat.factorization_mul ha hb0]
  simp [Nat.factorization_eq_zero_of_not_dvd h2]

theorem two_val_pow_mul_odd' (e : ℕ) {m : ℕ} (hm : Odd m) : (2 ^ e * m).factorization 2 = e := by
  rw [two_val_mul_odd' (by positivity) hm]
  simp [Nat.Prime.factorization_pow Nat.prime_two]

theorem card_statedSL_two' (F : Type) [Field F] [Finite F] :
    Nat.card (StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

theorem two_val_statedSL' (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (Nat.card (StatedSL 2 F)).factorization 2 = (Nat.card F ^ 2 - 1).factorization 2 :=
  CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.two_val_statedSL F hodd

theorem two_val_hatT {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G} (h : Std4r1 G z S K F)
    {e : ℕ} (he : Nat.card ↥(S ⊓ K) = 2 ^ e) : (Nat.card (HatT K)).factorization 2 = e := by
  have hsylK : M.Syl2In (S ⊓ K) K := h.syl_C.inf_normal h.K_le_C
    (fun c hc n hn => (mem_normalizer_iff.1 (h.toStd6r1.normalizes_K hc) n).1 hn)
  obtain ⟨e', m, hPe, hm, hKc⟩ := hsylK.card_eq_pow_mul
  have hee : e' = e := Nat.pow_right_injective (le_refl 2) (hPe.symm.trans he)
  subst hee
  have h1 : Nat.card ↥K = Nat.card (HatT K) * Nat.card ↥(pPrimeCore 2 ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) := TwoThin.odd_card_pPrimeCore ↥K
  have h2 : (Nat.card ↥K).factorization 2 = e' := by rw [hKc]; exact two_val_pow_mul_odd' e' hm
  rw [h1, two_val_mul_odd' Nat.card_pos.ne' hodd] at h2
  exact h2

theorem prop49_rest_of_local (hII : II4_4_4_center) (hq : II4_4_quat) (hdiag : IVK_diag_unique)
    (h19 : IVK_1_9_outer) (hsd : SD_facts) (hsdq : SD_sq_not_z) (hqc : Quat_centr) (hrn : Rnormal4)
    (h44 : II4_44) (hshape : Bg.B_two_maximalClass_shape) (hloc : Prop49_local) : Prop49_rest := by
  intro G _ _ z S K F h hQF hquat U hUR hU4 hUn x hx3 hxW hxU hxz hcard hidx
  have hy := prop49_y hII hq hdiag h19 hsd hsdq hqc hrn hshape h hQF hquat hUR hU4 hUn hxW hxU hxz
    hcard hidx
  obtain ⟨hP8, hSL2, hRconj⟩ := hloc G z S K F h hQF hquat U hUR hU4 hUn x hx3 hxW hxU hxz hcard hidx hy
  refine ⟨hy, ?_⟩
  have hQ8 : Nat.card ↥(Qz S z) = 8 := by rw [← hcard]; exact hP8
  have hP3 : IVK.IsQuaternionTwoGroup ↥(Pz S z) 3 := by
    obtain ⟨nP, hnP⟩ := h.P_quat hq
    rw [h.Pz_eq] at hP8 ⊢
    exact isQuat_three hnP hP8
  have hQ3 : IVK.IsQuaternionTwoGroup ↥(Qz S z) 3 := by
    obtain ⟨nQ, hnQ⟩ := hquat
    rw [← hQF] at hnQ
    exact isQuat_three hnQ hQ8
  have hP8' : Nat.card ↥(S ⊓ K) = 2 ^ 3 := by rw [← h.Pz_eq, hP8]; norm_num
  have hv3 := two_val_hatT h hP8'
  have hsl : IsSL2Or2A7 (HatT K) := h44 G h.simple z h.orderOf_z K h.comp_isPCompIn h.comp_pRank
  rcases hsl.1 with ⟨Fq, hF', hfin, ⟨hodd, h5⟩, ⟨eq⟩⟩ | h2A7
  · have hcardK : Nat.card (HatT K) = Nat.card (StatedSL 2 Fq) := Nat.card_congr eq.toEquiv
    have hv : (Nat.card Fq ^ 2 - 1).factorization 2 = 3 := by
      rw [← two_val_statedSL' Fq hodd, ← hcardK]; exact hv3
    exact ⟨Nat.card Fq, mod8_of_two_val hodd hv, h5, ⟨Fq, hF', hfin, rfl, ⟨eq⟩⟩, hP3, hQ3, hSL2, hRconj⟩
  · exfalso
    have h1 := card_of_doubleCoverAlt7 h2A7
    rw [h1] at hv3
    have : (5040 : ℕ).factorization 2 = 4 := by
      have : (5040 : ℕ) = 2 ^ 4 * 315 := by norm_num
      rw [this]; exact two_val_pow_mul_odd' 4 (by decide)
    omega

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
