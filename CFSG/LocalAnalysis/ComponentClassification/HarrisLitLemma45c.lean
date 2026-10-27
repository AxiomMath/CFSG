module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem commutator_zpowers_eq {K : Subgroup X} (hK : Group.IsPerfect ↥K)
    (hsimp : IsSimpleGroup (Bar K)) (hnonab : ∃ a b : Bar K, a * b ≠ b * a) {x : X}
    (hxK : x ∈ K) (hx : x ∉ (pPrimeCore 2 ↥K).map K.subtype) : ⁅K, zpowers x⁆ = K := by
  have hxN : zpowers x ≤ normalizer (K : Set X) := zpowers_le.mpr (le_normalizer hxK)
  have hNK : ⁅K, zpowers x⁆ ≤ K := FooteLit.commutator_le_self_of_le_normalizer hxN
  have hKN : K ≤ normalizer ((⁅K, zpowers x⁆ : Subgroup X) : Set X) :=
    FooteLit.le_normalizer_commutator_self K (zpowers x)
  have hN' : ((⁅K, zpowers x⁆ : Subgroup X).subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  have hπs : Function.Surjective (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
    QuotientGroup.mk'_surjective _
  rcases (hN'.map _ hπs).eq_bot_or_eq_top with hbot | htop
  ·
    exfalso
    apply hx
    have hcen : (QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨x, hxK⟩) ∈ center (Bar K) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨k, rfl⟩ := hπs y
      have hk : ⁅k, (⟨x, hxK⟩ : ↥K)⁆ ∈ (⁅K, zpowers x⁆ : Subgroup X).subgroupOf K :=
        commutator_mem_commutator k.2 (mem_zpowers x)
      have h1 := mem_map_of_mem (QuotientGroup.mk' (pPrimeCore 2 ↥K)) hk
      rw [hbot, mem_bot, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hcbot : center (Bar K) = ⊥ := by
      rcases (inferInstance : (center (Bar K)).Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonab
        have ha : a ∈ center (Bar K) := by rw [ht]; exact mem_top a
        exact hab ((mem_center_iff.mp ha b).symm)
    rw [hcbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
    exact ⟨_, hcen, rfl⟩
  ·
    apply le_antisymm hNK
    have hcov : ∀ k : ↥K, ∃ n ∈ (⁅K, zpowers x⁆ : Subgroup X).subgroupOf K,
        n⁻¹ * k ∈ pPrimeCore 2 ↥K := by
      intro k
      have hk : QuotientGroup.mk' (pPrimeCore 2 ↥K) k ∈
          ((⁅K, zpowers x⁆ : Subgroup X).subgroupOf K).map (QuotientGroup.mk' _) := by
        rw [htop]
        exact mem_top _
      obtain ⟨n, hn, hnk⟩ := hk
      exact ⟨n, hn, QuotientGroup.eq.mp hnk⟩
    set N := (⁅K, zpowers x⁆ : Subgroup X).subgroupOf K with hNdef
    have : N.Normal := hN'
    have : Group.IsPerfect ↥K := hK
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' N).comp (pPrimeCore 2 ↥K).subtype) := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N q
      obtain ⟨n, hn, hnk⟩ := hcov k
      refine ⟨⟨n⁻¹ * k, hnk⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      have := hN'.conj_mem n hn k⁻¹
      simpa [mul_assoc] using this
    have hodd : Odd (Nat.card (↥K ⧸ N)) := by
      have hdvd := Subgroup.card_dvd_of_surjective hsurj
      rcases Nat.even_or_odd (Nat.card (↥K ⧸ N)) with he | ho
      · exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right hdvd
          pPrimeCore_coprime_card) (even_iff_two_dvd.mp he)) (by norm_num)
      · exact ho
    have hsolv : Group.IsSolvable (↥K ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hsub : Subsingleton (↥K ⧸ N) := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isSolvable (↥K ⧸ N) hsolv
    intro k hk
    have h1 : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ N) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff (⟨k, hk⟩ : ↥K)).mp h1

omit [Finite X] in
theorem commutator_zpowers_mul_eq {K : Subgroup X} {x y : X} (hy : y ∈ centralizer (K : Set X))
    (hxK : x ∈ K) (hxy : Commute y x) : ⁅K, zpowers (y * x)⁆ = ⁅K, zpowers x⁆ := by
  have key : ∀ k ∈ K, ∀ n : ℤ, ⁅k, (y * x) ^ n⁆ = ⁅k, x ^ n⁆ := by
    intro k hk n
    have hc : ⁅k, x ^ n⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem hk (K.zpow_mem hxK n)) (K.inv_mem hk))
        (K.inv_mem (K.zpow_mem hxK n))
    have hyk : Commute (y ^ n) k :=
      Commute.zpow_left (show Commute y k from (mem_centralizer_iff.mp hy k hk).symm) n
    have hyc : Commute (y ^ n) ⁅k, x ^ n⁆ :=
      Commute.zpow_left (show Commute y ⁅k, x ^ n⁆ from (mem_centralizer_iff.mp hy _ hc).symm) n
    rw [hxy.mul_zpow]
    calc ⁅k, y ^ n * x ^ n⁆ = y ^ n * ⁅k, x ^ n⁆ * (y ^ n)⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, ← mul_assoc k (y ^ n),
            ← hyk.eq]
          group
      _ = ⁅k, x ^ n⁆ := by rw [hyc.eq, mul_inv_cancel_right]
  apply le_antisymm
  · rw [commutator_le]
    intro k hk g hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
    rw [key k hk n]
    exact commutator_mem_commutator hk (zpow_mem (mem_zpowers x) n)
  · rw [commutator_le]
    intro k hk g hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
    rw [← key k hk n]
    exact commutator_mem_commutator hk (zpow_mem (mem_zpowers _) n)

variable {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem commutator_K_z (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    ⁅centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j), zpowers z⁆ =
      centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have hL := hσ.lieModel_bar_K hFC hKC i j
  refine commutator_zpowers_eq (isPerfect_perfectResidual_map _)
    (isSimpleGroup_of_lieModel_psl2 hL) (nonabelian_of_lieModel_psl2 hL)
    (hσ.z_mem_Dstar hFC hKC i j).2 fun hz => ?_
  have hdvd := Subgroup.orderOf_dvd_natCard _ hz
  rw [hσ.z_order] at hdvd
  exact absurd (Nat.Coprime.eq_one_of_dvd (coprime_card_map_pPrimeCore _) hdvd) (by norm_num)

theorem commutator_K_mul_z (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) {y : X}
    (hy : y ∈ closure {t, w ^ (orderOf w / 2) * t ^ i * z ^ j}) :
    ⁅centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j), zpowers (y * z)⁆ =
      centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have hyX : y ∈ closure {t, w ^ (orderOf w / 2), z} := by
    refine (closure_le _).mpr ?_ hy
    rintro g (rfl | rfl)
    · exact subset_closure (by simp)
    · exact beta_mem_X i j
  have hzT : z ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := mem_sup_left (mem_sup_right hσ.z_mem)
  have hyz : Commute y z := (mem_centralizer_iff.mp (hσ.X_le_center_T hyX).2 z hzT).symm
  rw [commutator_zpowers_mul_eq (h.closure_le_centralizer_K _ hy)
    (hσ.z_mem_Dstar hFC hKC i j).2 hyz]
  exact hσ.commutator_K_z hFC hKC i j

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit
