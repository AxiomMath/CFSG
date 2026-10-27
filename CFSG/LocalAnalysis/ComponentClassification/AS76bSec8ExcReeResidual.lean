module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeClass
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSetup
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieF4Gen

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.ReeSec8

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (fam fam_2_eq fam_4_eq fam_6_eq fam_8_eq
  weylOne_conj_fam weylCheck1 rel_C5 generation_one center_one)

open scoped commutatorElement

section Residual

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem perfectCore_parabolic_le
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    CFSG.Quasithin.perfectCore (F4.reeLocalParabolic K m ⟨1, by decide⟩) ≤
      F4.reeGamma K m ⊓ centralizer {centralZ K m 1} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzc, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  have hscal : ∀ g ∈ F4.reeLocalParabolic K m ⟨1, by decide⟩, ∃ l : K, l ≠ 0 ∧
      ∀ c, g * centralZ K m c * g⁻¹ = centralZ K m (l * c) := by
    intro g hg
    obtain ⟨t, ⟨u, rfl⟩, s, hs, rfl⟩ := exists_mul_of_mem_reeLocalParabolic hK hg
    refine ⟨(u : K) ^ 2 ^ m, pow_ne_zero _ u.ne_zero, fun c => ?_⟩
    have hs' : s ∈ F4.reeGamma K m ⊓ centralizer {centralZ K m 1} := by
      rw [reeGamma_inf_centralizer_eq hm hK]
      exact hs
    have hsc : s * centralZ K m c * s⁻¹ = centralZ K m c := by
      rw [mem_centralizer_singleton_iff.1 ((hzc c).2 hs'), mul_inv_cancel_right]
    calc LargeReeCover.pairedTorusHom m (LargeReeCover.f4i 0) (LargeReeCover.f4i 3) u * s *
          centralZ K m c *
            (LargeReeCover.pairedTorusHom m (LargeReeCover.f4i 0) (LargeReeCover.f4i 3) u * s)⁻¹ =
        LargeReeCover.pairedTorusHom m (LargeReeCover.f4i 0) (LargeReeCover.f4i 3) u *
          (s * centralZ K m c * s⁻¹) *
            (LargeReeCover.pairedTorusHom m (LargeReeCover.f4i 0) (LargeReeCover.f4i 3) u)⁻¹ := by
          group
      _ = centralZ K m ((u : K) ^ 2 ^ m * c) := by
        rw [hsc, ← sylowH_zero_eq_centralZ, ← sylowH_zero_eq_centralZ, torusOne_conj_sylowH hK]
  have h1 : CFSG.Quasithin.perfectCore (F4.reeLocalParabolic K m ⟨1, by decide⟩) ≤
      ⁅F4.reeLocalParabolic K m ⟨1, by decide⟩, F4.reeLocalParabolic K m ⟨1, by decide⟩⁆ := by
    have := iInf_le (fun n => CFSG.Quasithin.derivedSeriesOf
      (F4.reeLocalParabolic K m ⟨1, by decide⟩) n) 1
    rwa [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero] at this
  refine h1.trans ?_
  rw [commutator_le]
  intro g hg g' hg'
  obtain ⟨l, hl, hgl⟩ := hscal g hg
  obtain ⟨l', hl', hgl'⟩ := hscal g' hg'
  refine mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2
    (commutator_conj_of_scalar hl hl' hgl hgl')⟩
  have hgΓ : g ∈ F4.reeGamma K m := (mem_inf.1 hg).1
  have hg'Γ : g' ∈ F4.reeGamma K m := (mem_inf.1 hg').1
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hgΓ hg'Γ) (inv_mem hgΓ)) (inv_mem hg'Γ)

theorem residualMem_z
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (hz : centralZ K m 1 ∈ F4.reeGamma K m) :
    ResidualMem (⟨centralZ K m 1, hz⟩ : F4.reeGamma K m) := by
  obtain ⟨hz1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  set V := F4.reeFixedOrbitComplementUnipotent K m ⟨1, by decide⟩ with hV
  have hVC : V ≤ F4.reeGamma K m ⊓ centralizer {centralZ K m 1} := by
    rw [hz1]
    exact le_sup_left
  have hVΓ : V ≤ F4.reeGamma K m := hVC.trans inf_le_left
  have hV2 : IsPGroup 2 V := by
    have h1 := (centralizerZ_kernel hm hK).2.1
    exact h1.of_equiv (subgroupOfEquivOfLe le_sup_left)
  have hP2 : IsPGroup 2 (V.subgroupOf (F4.reeGamma K m)) :=
    hV2.of_equiv (subgroupOfEquivOfLe hVΓ).symm
  have hVcomm : V ≤ ⁅F4.reeGamma K m ⊓ centralizer {centralZ K m 1},
      F4.reeGamma K m ⊓ centralizer {centralZ K m 1}⁆ :=
    (generation_one hm hK).trans (commutator_mono hVC (perfectCore_parabolic_le hm hK))
  have hPC : V.subgroupOf (F4.reeGamma K m) ≤
      ⁅cent (⟨centralZ K m 1, hz⟩ : F4.reeGamma K m), cent ⟨centralZ K m 1, hz⟩⁆ := by
    intro v hv
    have h1 := hVcomm (mem_subgroupOf.1 hv)
    rw [← map_cent (⟨centralZ K m 1, hz⟩ : F4.reeGamma K m), ← map_commutator] at h1
    exact (mem_map_iff_mem (F4.reeGamma K m).subtype_injective).1 h1
  have hzP : (⟨centralZ K m 1, hz⟩ : F4.reeGamma K m) ∈
      ⁅V.subgroupOf (F4.reeGamma K m), V.subgroupOf (F4.reeGamma K m)⁆ := by
    have h1 : centralZ K m 1 ∈ ⁅V, V⁆ := by
      refine center_one hK (mem_inf.2 ⟨centralZ_mem_complement hm hK 1, ?_⟩)
      rw [mem_centralizer_iff]
      intro v hv
      exact mem_centralizer_singleton_iff.1 (complement_le_centralizer hm hK 1 hv)
    have e : ⁅V.subgroupOf (F4.reeGamma K m), V.subgroupOf (F4.reeGamma K m)⁆.map
        (F4.reeGamma K m).subtype = ⁅V, V⁆ := by
      rw [map_commutator, subgroupOf_map_subtype, inf_eq_left.2 hVΓ]
    rw [← e] at h1
    exact (mem_map_iff_mem (x := ⟨_, hz⟩) (F4.reeGamma K m).subtype_injective).1 h1
  exact commutator_le_admResidual_of_isPGroup (hPC.trans le_sup_right) hP2 hzP

theorem residualMem_t
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1)) (ht : sylowL m K 1 ∈ F4.reeGamma K m) :
    ResidualMem (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m) := by
  have : CharP K 2 := ‹CharP K F4.prime›
  obtain ⟨-, -, -, -, -, ht1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    large_Ree_two_involution_centralizers m hm K hK
  unfold ResidualMem
  have hR₁C : rankOneGroupOne K m ≤ F4.reeGamma K m ⊓ centralizer {sylowL m K 1} := by
    rw [ht1]
    exact le_sup_right
  have hQC : tKernel K m ≤ F4.reeGamma K m ⊓ centralizer {sylowL m K 1} := by
    rw [ht1]
    exact le_sup_left
  have hmemC : ∀ g (hg : g ∈ F4.reeGamma K m ⊓ centralizer {sylowL m K 1}),
      (⟨g, (mem_inf.1 hg).1⟩ : F4.reeGamma K m) ∈ cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m) :=
    fun g hg => mem_cent_iff.2 (mem_centralizer_singleton_iff.1 (mem_inf.1 hg).2)
  obtain ⟨hR₁s, hR₁nc⟩ := isSimpleGroup_rankOneGroupOne hm hK
  have hR₁Γ : rankOneGroupOne K m ≤ F4.reeGamma K m := hR₁C.trans inf_le_left
  have hR'perf := commutator_subgroupOf_of_perfect hR₁Γ (commutator_eq_self_of_simple hR₁nc)
  have hR'C : (rankOneGroupOne K m).subgroupOf (F4.reeGamma K m) ≤
      cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m) := fun r hr =>
    hmemC _ (hR₁C (mem_subgroupOf.1 hr))
  have hR'X : (rankOneGroupOne K m).subgroupOf (F4.reeGamma K m) ≤
      oUpperTwo (cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m)) ⊔
        ⁅cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m), cent ⟨sylowL m K 1, ht⟩⁆ := by
    rw [← hR'perf]
    exact (commutator_mono hR'C hR'C).trans le_sup_right
  have hRres : ∀ r (hr : r ∈ rankOneGroupOne K m), (⟨r, hR₁Γ hr⟩ : F4.reeGamma K m) ∈
      admResidual (oUpperTwo (cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m)) ⊔
        ⁅cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m), cent ⟨sylowL m K 1, ht⟩⁆) :=
    fun r hr => CFSG.ComponentClassification.RankTwoClassical.le_admResidual_of_perfect hR'X
      hR'perf (mem_subgroupOf.2 hr)
  obtain ⟨g, hgen⟩ := exists_generator_units (K := K)
  have hTR : LargeReeCover.pairedTorusHom m (LargeReeCover.f4i 0) (LargeReeCover.f4i 3) g ∈
      rankOneGroupOne K m :=
    subset_closure (Set.mem_union_left _ (Set.mem_union_right _ ⟨g, rfl⟩))
  have hnR : weylOne K ∈ rankOneGroupOne K m := subset_closure (Set.mem_union_right _ rfl)
  have hog : orderOf g = 2 ^ (2 * m + 1) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers fun x => ?_, Nat.card_units, hK]
    obtain ⟨k, hk⟩ := hgen x
    exact mem_powers_iff_mem_zpowers.1 ⟨k, hk⟩
  have hθ : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hq : (2 : ℕ) ^ (2 * m + 1) = 2 * (2 ^ m * 2 ^ m) := by ring
  have hθθ : 2 * 2 ^ m ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_right _ hθ
  have hχB : ((g ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K) + 1 ≠ 0 := by
    intro h
    have h1 : g ^ ((-1 : ℤ) - 2 ^ m) = 1 := by
      apply Units.ext
      rw [Units.val_one, ← CharTwo.add_eq_zero]
      exact h
    have h2 : g ^ (1 + 2 ^ m) = 1 := by
      rw [show ((-1 : ℤ) - 2 ^ m) = -((1 + 2 ^ m : ℕ) : ℤ) by push_cast; ring, zpow_neg,
        inv_eq_one, zpow_natCast] at h1
      exact h1
    have h3 := Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one h2)
    rw [hog, hq] at h3
    omega
  have hχH : ((g : K) ^ 2 ^ m) + 1 ≠ 0 := by
    intro h
    have h1 : g ^ (2 ^ m) = 1 := by
      apply Units.ext
      rw [Units.val_one, Units.val_pow_eq_pow_val, ← CharTwo.add_eq_zero]
      exact h
    have h3 := Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one h1)
    rw [hog, hq] at h3
    omega
  have hQ2' : ∀ c : K, fam m K 2 c ∈ tKernel K m := fun c => by
    rw [← SetLike.mem_coe, coe_tKernel hK]
    exact ⟨![0, 0, c, 0, 0, 0, 0, 0, 0, 0, 0, 0], ⟨rfl, rfl, rfl⟩, (fam_2_eq c).symm⟩
  have hQ4 : ∀ c : K, fam m K 4 c ∈ tKernel K m := fun c => by
    rw [← SetLike.mem_coe, coe_tKernel hK]
    exact ⟨![0, 0, 0, 0, c, 0, 0, 0, 0, 0, 0, 0], ⟨rfl, rfl, rfl⟩, (fam_4_eq c).symm⟩
  have hQ6 : ∀ c : K, fam m K 6 c ∈ tKernel K m := fun c => by
    rw [← SetLike.mem_coe, coe_tKernel hK]
    exact ⟨![0, 0, 0, 0, 0, 0, c, 0, 0, 0, 0, 0], ⟨rfl, rfl, rfl⟩, (fam_6_eq c).symm⟩
  have hQ8 : ∀ c : K, fam m K 8 c ∈ tKernel K m := fun c => by
    rw [← SetLike.mem_coe, coe_tKernel hK]
    exact ⟨![0, 0, 0, 0, 0, 0, 0, 0, c, 0, 0, 0], ⟨rfl, rfl, rfl⟩, (fam_8_eq c).symm⟩
  have hQΓ : ∀ {w : ModGL F4.tag K}, w ∈ tKernel K m → w ∈ F4.reeGamma K m := fun hw =>
    (mem_inf.1 (hQC hw)).1
  have hTΓ := hR₁Γ hTR
  have hnΓ : weylOne K ∈ F4.reeGamma K m := hR₁Γ hnR
  have hcommC : ∀ {a b : ModGL F4.tag K} (ha : a ∈ rankOneGroupOne K m) (hb : b ∈ tKernel K m),
      ⁅(⟨a, hR₁Γ ha⟩ : F4.reeGamma K m), (⟨b, hQΓ hb⟩ : F4.reeGamma K m)⁆ ∈
        ⁅cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m), cent ⟨sylowL m K 1, ht⟩⁆ :=
    fun ha hb => commutator_mem_commutator (hmemC _ (hR₁C ha)) (hmemC _ (hQC hb))
  have hBval : ∀ c, ⁅LargeReeCover.pairedTorusHom m (LargeReeCover.f4i 0) (LargeReeCover.f4i 3) g,
      fam m K 2 (c / (((g ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K) + 1))⁆ = fam m K 2 c := by
    intro c
    show ⁅_, sylowB m K 0 _⁆ = sylowB m K 0 c
    rw [commutatorElement_def, torusOne_conj_sylowB hK]
    have hinv : ∀ b : K, (sylowB m K 0 b)⁻¹ = sylowB m K 0 b := fun b =>
      inv_eq_of_mul_eq_one_right (by
        rw [CFSG.Quasithin.B42F4.sylowB_zero_mul hK, CharTwo.add_self_eq_zero, sylowB_zero_zero])
    rw [hinv, CFSG.Quasithin.B42F4.sylowB_zero_mul hK]
    congr 1
    field_simp
  have hHval : ∀ c, ⁅LargeReeCover.pairedTorusHom m (LargeReeCover.f4i 0) (LargeReeCover.f4i 3) g,
      fam m K 8 (c / ((g : K) ^ 2 ^ m + 1))⁆ = fam m K 8 c := by
    intro c
    show ⁅_, sylowH m K 0 _⁆ = sylowH m K 0 c
    rw [commutatorElement_def, torusOne_conj_sylowH hK, sylowH_zero_eq_centralZ,
      sylowH_zero_eq_centralZ, sylowH_zero_eq_centralZ]
    have hinv : ∀ b : K, (centralZ K m b)⁻¹ = centralZ K m b := fun b =>
      inv_eq_of_mul_eq_one_right (by rw [centralZ_mul hK, CharTwo.add_self_eq_zero, centralZ_zero])
    rw [hinv, centralZ_mul hK]
    congr 1
    field_simp
  have hBcomm : ∀ c, (⟨fam m K 2 c, hQΓ (hQ2' c)⟩ : F4.reeGamma K m) ∈
      ⁅cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m), cent ⟨sylowL m K 1, ht⟩⁆ := by
    intro c
    have e : (⟨fam m K 2 c, hQΓ (hQ2' c)⟩ : F4.reeGamma K m) = ⁅(⟨_, hTΓ⟩ : F4.reeGamma K m),
        (⟨_, hQΓ (hQ2' (c / (((g ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K) + 1)))⟩ : F4.reeGamma K m)⁆ :=
      Subtype.ext (hBval c).symm
    rw [e]
    exact hcommC hTR (hQ2' _)
  have hHcomm : ∀ c, (⟨fam m K 8 c, hQΓ (hQ8 c)⟩ : F4.reeGamma K m) ∈
      ⁅cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m), cent ⟨sylowL m K 1, ht⟩⁆ := by
    intro c
    have e : (⟨fam m K 8 c, hQΓ (hQ8 c)⟩ : F4.reeGamma K m) = ⁅(⟨_, hTΓ⟩ : F4.reeGamma K m),
        (⟨_, hQΓ (hQ8 (c / ((g : K) ^ 2 ^ m + 1)))⟩ : F4.reeGamma K m)⁆ :=
      Subtype.ext (hHval c).symm
    rw [e]
    exact hcommC hTR (hQ8 _)
  have hnC : (⟨weylOne K, hnΓ⟩ : F4.reeGamma K m) ∈ cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m) :=
    hmemC _ (hR₁C hnR)
  have hDcomm : (⟨fam m K 4 1, hQΓ (hQ4 1)⟩ : F4.reeGamma K m) ∈
      ⁅cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m), cent ⟨sylowL m K 1, ht⟩⁆ := by
    have h1 := Exc.conj_mem_commutator_self hnC (hBcomm 1)
    have e : (⟨fam m K 4 1, hQΓ (hQ4 1)⟩ : F4.reeGamma K m) =
        ⟨weylOne K, hnΓ⟩ * ⟨fam m K 2 1, hQΓ (hQ2' 1)⟩ * (⟨weylOne K, hnΓ⟩ : F4.reeGamma K m)⁻¹ :=
      Subtype.ext (weylOne_conj_fam (n := 2) (n' := 4) (by decide) 1).symm
    rw [e]
    exact h1
  have hQ2 : IsPGroup 2 ((tKernel K m).subgroupOf (F4.reeGamma K m)) := by
    have h1 := (centralizerT_kernel hm hK).2.1
    exact (h1.of_equiv (subgroupOfEquivOfLe le_sup_left)).of_equiv
      (subgroupOfEquivOfLe fun _ hw => hQΓ hw).symm
  have hP2 : IsPGroup 2 ((tKernel K m).subgroupOf (F4.reeGamma K m) ⊓
      ⁅cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m), cent ⟨sylowL m K 1, ht⟩⁆ : Subgroup _) :=
    hQ2.to_le inf_le_left
  have hBD : ⁅(⟨fam m K 2 1, hQΓ (hQ2' 1)⟩ : F4.reeGamma K m),
        (⟨fam m K 4 1, hQΓ (hQ4 1)⟩ : F4.reeGamma K m)⁆ ∈
      admResidual (oUpperTwo (cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m)) ⊔
        ⁅cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m), cent ⟨sylowL m K 1, ht⟩⁆) :=
    commutator_le_admResidual_of_isPGroup (inf_le_right.trans le_sup_right) hP2
      (commutator_mem_commutator (mem_inf.2 ⟨mem_subgroupOf.2 (hQ2' 1), hBcomm 1⟩)
        (mem_inf.2 ⟨mem_subgroupOf.2 (hQ4 1), hDcomm⟩))
  have hzres : (⟨fam m K 8 1, hQΓ (hQ8 1)⟩ : F4.reeGamma K m) ∈
      admResidual (oUpperTwo (cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m)) ⊔
        ⁅cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m), cent ⟨sylowL m K 1, ht⟩⁆) := by
    have hwX : (⟨_, hQΓ (hQ8 (1 / ((g : K) ^ 2 ^ m + 1)))⟩ : F4.reeGamma K m) ∈
        oUpperTwo (cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m)) ⊔
          ⁅cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m), cent ⟨sylowL m K 1, ht⟩⁆ :=
      mem_sup_right (hHcomm _)
    have e : (⟨fam m K 8 1, hQΓ (hQ8 1)⟩ : F4.reeGamma K m) =
        ⟨_, hTΓ⟩ * ((⟨_, hQΓ (hQ8 (1 / ((g : K) ^ 2 ^ m + 1)))⟩ : F4.reeGamma K m) *
          (⟨_, hTΓ⟩ : F4.reeGamma K m)⁻¹ *
            (⟨_, hQΓ (hQ8 (1 / ((g : K) ^ 2 ^ m + 1)))⟩ : F4.reeGamma K m)⁻¹) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hHval 1, commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hRres _ hTR) (conj_mem_admResidual hwX (inv_mem (hRres _ hTR)))
  have hFres : (⟨fam m K 6 1, hQΓ (hQ6 1)⟩ : F4.reeGamma K m) ∈
      admResidual (oUpperTwo (cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m)) ⊔
        ⁅cent (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m), cent ⟨sylowL m K 1, ht⟩⁆) := by
    have e : (⟨fam m K 6 1, hQΓ (hQ6 1)⟩ : F4.reeGamma K m) =
        ⟨weylOne K, hnΓ⟩ * ⟨fam m K 8 1, hQΓ (hQ8 1)⟩ * (⟨weylOne K, hnΓ⟩ : F4.reeGamma K m)⁻¹ :=
      Subtype.ext (weylOne_conj_fam (n := 8) (n' := 6) (by decide) 1).symm
    rw [e]
    exact mul_mem (mul_mem (hRres _ hnR) hzres) (inv_mem (hRres _ hnR))
  have e : (⟨sylowL m K 1, ht⟩ : F4.reeGamma K m) =
      ⁅(⟨fam m K 2 1, hQΓ (hQ2' 1)⟩ : F4.reeGamma K m),
        (⟨fam m K 4 1, hQΓ (hQ4 1)⟩ : F4.reeGamma K m)⁆ *
        (⟨fam m K 8 1, hQΓ (hQ8 1)⟩ : F4.reeGamma K m)⁻¹ *
          (⟨fam m K 6 1, hQΓ (hQ6 1)⟩ : F4.reeGamma K m)⁻¹ := by
    have h5 := rel_C5 hK (1 : K) 1
    rw [mul_one, one_mul, largeReeSigma_one, commutatorElement_def] at h5
    have h5' : fam m K 2 1 * fam m K 4 1 * (fam m K 2 1)⁻¹ * (fam m K 4 1)⁻¹ =
        sylowL m K 1 * fam m K 6 1 * fam m K 8 1 := h5
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h5']
    group
  have key := mul_mem (mul_mem hBD (inv_mem hzres)) (inv_mem hFres)
  rw [← e] at key
  exact key

end Residual

end CFSG.ComponentClassification.RankTwoExceptional.ReeSec8
