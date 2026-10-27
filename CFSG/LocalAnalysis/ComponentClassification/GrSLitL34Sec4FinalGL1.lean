module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGData
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Center46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndT
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddOrbitWitness
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.ComponentClassification.GrSLit.FinalG

open CFSG Subgroup

structure Data.Seven {G : Type} [Group G] [Finite G] (D : Data G) where
  h : G
  e : ℕ
  h_mem : h ∈ D.L
  h_pow : h ^ 7 ^ e = 1
  h_not : h ∉ centralizer (D.B : Set G)
  c' : G
  c'_mem : c' ∈ D.T
  c'_not : c' ∉ D.T₁
  c'_comm : h * c' = c' * h

namespace Data

variable {G : Type} [Group G] [Finite G] (D : Data G)

abbrev L₁ : Subgroup G := oddGen D.L

theorem c_not_mem_L₁ : D.c ∉ D.L₁ := by
  obtain ⟨Q, hKQ, hQS, hcQ, hQidx⟩ := exists_relIndex_two (K := D.S ⊓ withKernel D.J)
    inf_le_left (fun s hs => mem_inf.mpr ⟨mul_mem hs hs, D.sq_mem s hs⟩) D.c_mem
    (fun h => D.c_not_mem (mem_inf.mp h).2)
  have hT₁Q : D.T₁ ≤ Q := fun t ht => hKQ (mem_inf.mpr ⟨D.T₁_le_S ht,
    (le_sup_left : D.J ≤ withKernel D.J) (D.T₁_le_J ht)⟩)
  have hSidx : ¬ 2 ∣ D.S.relIndex D.L := by
    obtain ⟨-, P, hP⟩ := D.sylow_L
    have := P.not_dvd_index
    rw [hP] at this
    exact this
  obtain ⟨N, -, -, hsq, hcN⟩ := Quasithin.thompson_transfer_exists_normal_subgroup D.S_le_L
    D.isPGroup_S hSidx hQS hQidx (D.S_le_L D.c_mem) D.orderOf_c (fun x hx hmem => by
      have h1 := D.conj_c_mul_mem (inv_mem hx)
      rw [inv_inv] at h1
      apply hcQ
      have := mul_mem (inv_mem hmem) (hT₁Q h1)
      rwa [show (x⁻¹ * D.c * x)⁻¹ * (x⁻¹ * D.c * x * D.c) = D.c by group] at this)
  intro hc
  exact hcN (oddGen_le_of_sq (fun y hy => hsq y (oddGen_le _ hy)) hc)

theorem nonempty_seven : Nonempty D.Seven := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨M, hM⟩ := exists_prime_orderOf_dvd_card' (G := GL (Fin 3) (ZMod 2)) 7
    (by rw [LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits.card_GL_three_two]
        norm_num)
  obtain ⟨n, hn⟩ := D.φ_surjective M
  obtain ⟨e, q, hq, hoq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 7 (by norm_num)
  have hhL : ((n ^ q : ↥D.L) : G) ∈ D.L := (n ^ q).2
  have hpow : ((n ^ q : ↥D.L) : G) ^ 7 ^ e = 1 := by
    rw [← SubmonoidClass.coe_pow, ← pow_mul, mul_comm, ← hoq, pow_orderOf_eq_one]
    rfl
  have hnot : ((n ^ q : ↥D.L) : G) ∉ centralizer (D.B : Set G) := by
    intro hC
    have hker : n ^ q ∈ D.φ.ker := by
      rw [D.φ_ker, mem_subgroupOf]
      exact hC
    rw [MonoidHom.mem_ker, map_pow, hn] at hker
    exact hq (hM ▸ orderOf_dvd_of_pow_eq_one hker)
  set h : G := ((n ^ q : ↥D.L) : G) with hh
  set X : Set G := (fun t => D.c * t) '' (D.T₁ : Set G) with hX
  have hXinv : ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
    rintro _ ⟨t, ht, rfl⟩
    have hu := D.conj_c_mul_mem hhL
    refine ⟨(h * D.c * h⁻¹ * D.c)⁻¹ * (h * t * h⁻¹),
      mul_mem (inv_mem hu) (D.conj_mem_T₁ hhL ht), ?_⟩
    have hci := D.T₁_inv _ hu
    calc D.c * ((h * D.c * h⁻¹ * D.c)⁻¹ * (h * t * h⁻¹))
        = D.c * (D.c * (h * D.c * h⁻¹ * D.c) * D.c) * (h * t * h⁻¹) := by rw [hci]; group
      _ = (D.c * D.c) * (h * D.c * h⁻¹) * (D.c * D.c) * (h * t * h⁻¹) := by group
      _ = h * (D.c * t) * h⁻¹ := by rw [D.c_sq]; group
  have hcard : Nat.card X = 64 := by
    rw [hX, Nat.card_image_of_injective (mul_right_injective D.c), ← D.card_T₁]
    rfl
  have hmod := card_modEq_card_fixed hpow X hXinv
  rw [hcard] at hmod
  have hne : Nat.card {x : X // h * (x : G) = x * h} ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact absurd hmod (by decide)
  obtain ⟨⟨⟨x, ⟨t, ht, rfl⟩⟩, hxh⟩⟩ := (Nat.card_ne_zero.mp hne).1
  refine ⟨⟨h, e, hhL, hpow, hnot, D.c * t, mul_mem D.c_mem_T (D.T₁_le_T ht), fun hct => ?_,
    hxh⟩⟩
  apply D.c_not_mem_T₁
  have := mul_mem hct (inv_mem ht)
  rwa [mul_inv_cancel_right] at this

namespace Seven

variable {D} (H : D.Seven)

theorem h_odd : Odd (orderOf H.h) :=
  Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one H.h_pow)

theorem h_mem_L₁ : H.h ∈ D.L₁ := mem_oddGen H.h_mem H.h_odd

theorem inf_centralizer_B : D.B ⊓ centralizer ({H.h} : Set G) = ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := card_modEq_card_inf_centralizer H.h_pow (D.L_le_N_B H.h_mem)
  rw [D.eight.2] at hmod
  have hdvd : Nat.card ↥(D.B ⊓ centralizer ({H.h} : Set G)) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 from rfl, ← D.eight.2]
    exact card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hk'] at hmod
  interval_cases k
  · exact card_eq_one.mp (by rw [hk', pow_zero])
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · exfalso
    apply H.h_not
    have hle : D.B ≤ D.B ⊓ centralizer ({H.h} : Set G) :=
      le_of_eq (eq_of_le_of_card_ge inf_le_left (by rw [hk', D.eight.2]; norm_num)).symm
    rw [mem_centralizer_iff]
    intro b hb
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp (hle hb)).2

theorem fix_T₁ {t : G} (ht : t ∈ D.T₁) (hfix : H.h⁻¹ * t * H.h = t) : t = 1 := by
  by_contra ht1
  have key : ∀ u ∈ D.T₁, u * u = 1 → u ≠ 1 → H.h⁻¹ * u * H.h = u → False := by
    intro u hu huu hu1 hfu
    have huC : u ∈ centralizer ({H.h} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc u * H.h = H.h * (H.h⁻¹ * u * H.h) := by group
        _ = H.h * u := by rw [hfu]
    have h1 : u ∈ D.B ⊓ centralizer ({H.h} : Set G) := mem_inf.mpr ⟨D.T₁_omega u hu huu, huC⟩
    rw [H.inf_centralizer_B, mem_bot] at h1
    exact hu1 h1
  by_cases htt : t * t = 1
  · exact key t ht htt ht1 hfix
  · refine key (t * t) (mul_mem ht ht) ?_ htt ?_
    · have := D.T₁_pow_four ht
      rw [show t * t * (t * t) = t ^ 4 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
      exact this
    · calc H.h⁻¹ * (t * t) * H.h = (H.h⁻¹ * t * H.h) * (H.h⁻¹ * t * H.h) := by group
        _ = t * t := by rw [hfix]

include H in
theorem T₁_le_L₁ : D.T₁ ≤ D.L₁ :=
  le_oddGen_of_fixed H.h_mem H.h_odd (D.T₁_le_S.trans D.S_le_L)
    (fun t ht => by
      have := D.conj_mem_T₁ (inv_mem H.h_mem) ht
      rwa [inv_inv] at this)
    fun _ ht hfix => H.fix_T₁ ht hfix

theorem c'_sq : H.c' * H.c' = 1 := D.sq_eq_one_of_mem_T H.c'_mem H.c'_not

theorem orderOf_c' : orderOf H.c' = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact H.c'_sq) fun h1 => H.c'_not (h1 ▸ one_mem _)

end Seven

theorem T₁_le_L₁ : D.T₁ ≤ D.L₁ := by
  obtain ⟨H⟩ := D.nonempty_seven
  exact H.T₁_le_L₁

theorem map_L₁_eq_top : (D.L₁.subgroupOf D.L).map D.φ = ⊤ := by
  obtain ⟨H⟩ := D.nonempty_seven
  have hn : (D.L₁.subgroupOf D.L).Normal :=
    (normal_subgroupOf_iff_le_normalizer (oddGen_le D.L)).mpr (le_normalizer_oddGen D.L)
  have hmn := hn.map D.φ D.φ_surjective
  have := LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits.isSimpleGroup_GL_three_two
  rcases hmn.eq_bot_or_eq_top with hbot | htop
  · exfalso
    have hmem : D.φ ⟨H.h, H.h_mem⟩ ∈ (D.L₁.subgroupOf D.L).map D.φ :=
      mem_map_of_mem _ (mem_subgroupOf.mpr H.h_mem_L₁)
    rw [hbot, mem_bot, ← MonoidHom.mem_ker, D.φ_ker, mem_subgroupOf] at hmem
    exact H.h_not hmem
  · exact htop

theorem conj_mem_L₁ {x y : G} (hx : x ∈ D.L) (hy : y ∈ D.L₁) : x * y * x⁻¹ ∈ D.L₁ :=
  conj_mem_oddGen hx hy

end Data

end CFSG.ComponentClassification.GrSLit.FinalG
