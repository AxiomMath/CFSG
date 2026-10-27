module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutInvGL32

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem centExt_card_of_secProp_gl32 {G : Type} [Group G] [Finite G] {N K : Subgroup G}
    (hKN : K ≤ N)
    (h : SecProp N K (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))) :
    Nat.card ↥N = 168 * Nat.card ↥K := by
  obtain ⟨hN, hP⟩ := h
  letI := hN
  obtain ⟨e⟩ := hP
  have hcardquot : Nat.card (↥N ⧸ K.subgroupOf N) = 168 :=
    (Nat.card_congr e.toEquiv).trans
      CFSG.OddStandard.SmallF3.HarrisU33.Outside.card_GL32
  have hcardK : Nat.card ↥(K.subgroupOf N) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
  calc Nat.card ↥N = Nat.card (↥N ⧸ K.subgroupOf N) * Nat.card ↥(K.subgroupOf N) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ = 168 * Nat.card ↥K := by rw [hcardquot, hcardK]

theorem centExt_F_le_comm {G : Type} [Group G] [Finite G] {N Z F : Subgroup G} (hZN : Z ≤ N)
    (hFN : F ≤ N) (hZc : ∀ z ∈ Z, ∀ g ∈ N, z * g = g * z) (hZ3 : Nat.card ↥Z ∣ 3)
    (hFn : ∀ g ∈ N, ∀ f ∈ F, g * f * g⁻¹ ∈ F) (hFE : IsE 3 ↥F)
    (hCF : ∀ g ∈ N, (∀ f ∈ F, g * f = f * g) → g ∈ Z ⊔ F)
    (hQ : SecProp N (Z ⊔ F)
      (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))) :
    F ≤ ⁅N, N⁆ := by
  have hF8 : Nat.card ↥F = 8 := by simpa using hFE.2
  have hcardN : Nat.card ↥N = 168 * Nat.card ↥(Z ⊔ F) :=
    centExt_card_of_secProp_gl32 (sup_le hZN hFN) hQ
  have h7dvd : 7 ∣ Nat.card ↥N := by
    rw [hcardN]
    exact dvd_mul_of_dvd_left (by norm_num : (7 : ℕ) ∣ 168) _
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 7 h7dvd
  let g : G := x
  have hgN : g ∈ N := x.2
  have horder : orderOf g = 7 := by
    simpa [g] using (Subgroup.orderOf_coe x).trans hx
  have hg7 : g ^ 7 = 1 := by
    simpa [horder] using pow_orderOf_eq_one g
  let W : Subgroup G := F ⊓ ⁅N, N⁆
  by_contra hFcomm
  have hWF : W ≠ F := by
    intro h
    exact hFcomm (h ▸ inf_le_right)
  have hWltF : W < F := lt_of_le_of_ne inf_le_left hWF
  have hWle4 : Nat.card ↥W ≤ 4 := by
    have hWlt8 : Nat.card ↥W < 8 := by
      simpa [hF8] using Subgroup.card_lt_of_lt hWltF
    have hWdvd8 : Nat.card ↥W ∣ 8 := by
      simpa [W, hF8] using Subgroup.card_dvd_of_le (inf_le_left : W ≤ F)
    have hWdvd8' : Nat.card ↥W ∣ 2 ^ 3 := by simpa using hWdvd8
    obtain ⟨k, hk, hk2⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hWdvd8'
    rw [hk2] at hWlt8 ⊢
    have hklt : k < 3 :=
      (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp (by simpa using hWlt8)
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have hcomm_le_N : ⁅N, N⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem ha hb) (N.inv_mem ha)) (N.inv_mem hb)
  have conj_mem_W : ∀ {n w : G}, n ∈ N → w ∈ W → n * w * n⁻¹ ∈ W := by
    intro n w hn hw
    refine ⟨hFn n hn w ((inf_le_left : W ≤ F) hw), ?_⟩
    have hcw : n * w * n⁻¹ = ⁅n, w⁆ * w := by
      simpa using (conj_eq_commutatorElement_mul (g₁ := n) (g₂ := w))
    rw [hcw]
    exact ⁅N, N⁆ |>.mul_mem
      (commutator_mem_commutator hn (hcomm_le_N ((inf_le_right : W ≤ ⁅N, N⁆) hw)))
      ((inf_le_right : W ≤ ⁅N, N⁆) hw)
  have hgNorm : g ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro w
    constructor
    · exact conj_mem_W hgN
    · intro hw
      have h := conj_mem_W (N.inv_mem hgN) hw
      simpa [mul_assoc] using h
  let gN : ↥(Subgroup.normalizer (W : Set G)) := ⟨g, hgNorm⟩
  let π : MulAut ↥W := Subgroup.normalizerMonoidHom W gN
  have hπ7 : π ^ 7 = 1 := by
    have hgN7 : gN ^ 7 = 1 := by
      ext
      simpa [gN] using hg7
    change (Subgroup.normalizerMonoidHom W gN) ^ 7 = 1
    rw [← map_pow, hgN7, map_one]
  let p : Equiv.Perm ↥W := MulAut.toPerm ↥W π
  have hp7 : p ^ 7 = 1 := by
    change (MulAut.toPerm ↥W π) ^ 7 = 1
    rw [← map_pow, hπ7, map_one]
  have hord7 : orderOf p ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hp7
  have hordfact : orderOf p ∣ Nat.factorial (Nat.card ↥W) := by
    have := orderOf_dvd_natCard p
    rwa [Nat.card_perm] at this
  have h7not : ¬ 7 ∣ Nat.factorial (Nat.card ↥W) := by
    intro h7
    have hfac : Nat.factorial (Nat.card ↥W) ∣ Nat.factorial 4 := Nat.factorial_dvd_factorial hWle4
    have h724 : 7 ∣ Nat.factorial 4 := dvd_trans h7 hfac
    norm_num at h724
  have hp1 : orderOf p = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hord7 with h | h
    · exact h
    · exact absurd (h ▸ hordfact) h7not
  have hp_eq : p = 1 := orderOf_eq_one_iff.mp hp1
  have hcentW : ∀ w : ↥W, g * (w : G) * g⁻¹ = w := by
    intro w
    have h := congrArg (fun e : Equiv.Perm ↥W => e w) hp_eq
    have hπw : (π w : ↥W) = w := by
      change ((MulAut.toPerm ↥W π) w : ↥W) = w
      simpa [p] using h
    have hcoe := congrArg Subtype.val hπw
    simpa [π, gN, Subgroup.normalizerMonoidHom, HSMul.hSMul] using hcoe
  have hcommF : ∀ f ∈ F, g * f = f * g := by
    intro f hf
    have hwW : ⁅g, f⁆ ∈ W := by
      refine ⟨?_, commutator_mem_commutator hgN (hFN hf)⟩
      rw [commutatorElement_def]
      exact F.mul_mem (hFn g hgN f hf) (F.inv_mem hf)
    have hcommW : Commute g ⁅g, f⁆ := by
      have h := hcentW ⟨⁅g, f⁆, hwW⟩
      show g * ⁅g, f⁆ = ⁅g, f⁆ * g
      have := congrArg (· * g) h
      simpa [mul_assoc] using this
    have hw7 : ⁅g, f⁆ ^ 7 = 1 := by
      have := hcommW.commutatorElement_pow_left (b := f) 7
      rw [hg7, commutatorElement_one_left] at this
      simpa using this
    have hw2 : ⁅g, f⁆ ^ 2 = 1 := by
      have h := hFE.1.2 (⟨⁅g, f⁆, hwW.1⟩ : ↥F) (Subgroup.mem_top _)
      simpa using congrArg (Subtype.val) h
    have hw1 : ⁅g, f⁆ = 1 := by
      have h2 : orderOf ⁅g, f⁆ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hw2
      have h7 : orderOf ⁅g, f⁆ ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hw7
      have hg := Nat.dvd_gcd h2 h7
      simpa using orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hg))
    exact commutatorElement_eq_one_iff_mul_comm.mp hw1
  have hgZF : g ∈ Z ⊔ F := hCF g hgN hcommF
  have hNcent : N ≤ Subgroup.centralizer (Z : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hZc z hz n hn
  haveI hZnormal : (Z.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZN).mpr
      (hNcent.trans (Subgroup.centralizer_le_normalizer (Z : Set G)))
  have hsup : (Z.subgroupOf N) ⊔ (F.subgroupOf N) = (Z ⊔ F).subgroupOf N :=
    (Subgroup.subgroupOf_sup hZN hFN).symm
  have hgmem : (⟨g, hgN⟩ : ↥N) ∈ (Z.subgroupOf N) ⊔ (F.subgroupOf N) := by
    rw [hsup, Subgroup.mem_subgroupOf]
    exact hgZF
  rw [Subgroup.mem_sup_of_normal_left] at hgmem
  obtain ⟨z, hz, f, hf, hzf⟩ := hgmem
  have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
  have hfF : (f : G) ∈ F := Subgroup.mem_subgroupOf.mp hf
  have hzfG : (z : G) * (f : G) = g := congrArg Subtype.val hzf
  have hz3 : (z : G) ^ 3 = 1 := by
    have hdvd : orderOf (z : G) ∣ 3 := by
      rw [← Subgroup.orderOf_mk (z : G) hzZ]
      exact (orderOf_dvd_natCard (⟨(z : G), hzZ⟩ : ↥Z)).trans hZ3
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hf2 : (f : G) ^ 2 = 1 := by
    have h := hFE.1.2 (⟨(f : G), hfF⟩ : ↥F) (Subgroup.mem_top _)
    simpa using congrArg (Subtype.val) h
  have hcommzf : Commute (z : G) (f : G) :=
    hZc (z : G) hzZ (f : G) (hFN hfF)
  have hpow : ((z : G) * (f : G)) ^ 6 = 1 := by
    rw [hcommzf.mul_pow]
    have hz6 : (z : G) ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hz3, one_pow]
    have hf6 : (f : G) ^ 6 = 1 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hf2, one_pow]
    rw [hz6, hf6, mul_one]
  have hg6 : g ^ 6 = 1 := by
    rw [← hzfG]
    exact hpow
  have hdvd6 : orderOf g ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hg6
  rw [horder] at hdvd6
  norm_num at hdvd6

end CFSG.OddStandard.HigherRank.YamadaG23
