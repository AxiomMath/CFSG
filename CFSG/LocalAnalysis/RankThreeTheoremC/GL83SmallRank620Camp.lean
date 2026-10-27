module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620CampSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Parity
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [Finite G] {M B H S K : Subgroup G} {z b : G} {f : ↥K →* GL32}

private theorem camp_exists_orderOf_seven : ∃ g : GL32, orderOf g = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_prime_orderOf_dvd_card' 7 (by rw [L32Insp.card_GL]; norm_num)

private theorem Data620.camp_isPGroup_core (h : Data620 M B H S K z b f) :
    IsPGroup 2 (pCoreOf 2 H) :=
  h.maxInv.1.2.1.to_le h.core_le

private theorem Data620.camp_exists_seven (h : Data620 M B H S K z b f) :
    ∃ c ∈ K, c ^ 7 = 1 ∧ c ∉ pCoreOf 2 H := by
  obtain ⟨g₀, hg₀⟩ := camp_exists_orderOf_seven
  obtain ⟨k₀, hk₀⟩ := h.f_surj g₀
  have h7 : (k₀ : G) ^ 7 ∈ pCoreOf 2 H := by
    refine (h.f_ker (k₀ ^ 7)).1 ?_
    rw [map_pow, hk₀, ← hg₀]
    exact pow_orderOf_eq_one g₀
  obtain ⟨n, hn⟩ := h.camp_isPGroup_core ⟨_, h7⟩
  have hn' : ((k₀ : G) ^ 7) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  refine ⟨(k₀ : G) ^ 2 ^ n, K.pow_mem k₀.2 _, ?_, fun hc => ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]
    exact hn'
  · have h1 := (h.f_ker (k₀ ^ 2 ^ n)).2 hc
    rw [map_pow, hk₀] at h1
    have h2 : 7 ∣ 2 ^ n := hg₀ ▸ orderOf_dvd_of_pow_eq_one h1
    have h3 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h2
    omega

private theorem Data620.camp_H_le_normalizer_W (h : Data620 M B H S K z b f) :
    H ≤ normalizer ((omegaCenter (K ⊓ pCoreOf 2 H) : Subgroup G) : Set G) := fun _ hg =>
  normalizer_le_normalizer_omegaCenter (K ⊓ pCoreOf 2 H)
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨h.K_normal hg, h.eq_normalizer.le hg⟩)

private theorem Data620.camp_comm_mem (h : Data620 M B H S K z b f) {c : G} (hc : c ∈ K) :
    b * c * b⁻¹ * c⁻¹ ∈ K ⊓ pCoreOf 2 H := by
  refine ⟨K.mul_mem ((mem_normalizer_iff.1 (h.K_normal (h.B_le h.b_mem)) c).1 hc) (K.inv_mem hc),
    ?_⟩
  exact h.b_cent (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers b) hc)

private theorem Data620.camp_commute_on_W (h : Data620 M B H S K z b f) {c : G} (hc : c ∈ K)
    {w : G} (hw : w ∈ omegaCenter (K ⊓ pCoreOf 2 H)) :
    c * (b * w * b⁻¹) * c⁻¹ = b * (c * w * c⁻¹) * b⁻¹ := by
  have hbw : b * w * b⁻¹ ∈ omegaCenter (K ⊓ pCoreOf 2 H) :=
    (mem_normalizer_iff.1 (h.camp_H_le_normalizer_W (h.B_le h.b_mem)) w).1 hw
  have hw' : c * (b * w * b⁻¹) * c⁻¹ ∈ omegaCenter (K ⊓ pCoreOf 2 H) :=
    (mem_normalizer_iff.1 (h.camp_H_le_normalizer_W (h.K_le hc)) _).1 hbw
  have hd := (mem_omegaCenter.1 hw').2.1 _ (h.camp_comm_mem hc)
  have e : b * (c * w * c⁻¹) * b⁻¹ = (b * c * b⁻¹ * c⁻¹) * (c * (b * w * b⁻¹) * c⁻¹) *
      (b * c * b⁻¹ * c⁻¹)⁻¹ := by group
  rw [e, ← hd]
  group

theorem Data620.false_of_campbell (hCamp : KFactCampbell) (h : Data620 M B H S K z b f)
    {R : Subgroup G} (hSR : S ≤ R) (hRX : R ≤ K ⊔ pCoreOf 2 H) (hR2 : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ (R.subgroupOf (K ⊔ pCoreOf 2 H)).index)
    (hC : (K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter R : Subgroup G) : Set G) ≤
      normalizer (S : Set G)) : False := by
  obtain ⟨A₀, B₀, hAB, hBW, -, -, hKA, hWK, hcard, hker⟩ :=
    h.campbell_conclusion hCamp hSR hRX hR2 hRi hC
  obtain ⟨c, hcK, hc7, hcO⟩ := h.camp_exists_seven
  have hb3 : b ^ 3 = 1 := by rw [← h.b_order]; exact pow_orderOf_eq_one b
  refine parity_false_of_series (isElemAbelian_omegaCenter _)
    (h.camp_H_le_normalizer_W (h.K_le hcK)) (h.camp_H_le_normalizer_W (h.B_le h.b_mem))
    hc7 hb3 (fun w hw => h.camp_commute_on_W hcK hw)
    (fun w hw => h.b_fpf w (omegaCenter_le _ hw).2) hAB hBW
    (fun a ha => ((mem_centralizer_iff.1 (hKA hcK)) a ha).symm) (fun w hw => ?_) hcard ?_
  · have := B₀.inv_mem (hWK w hw c hcK)
    simpa [mul_assoc] using this
  · by_contra hnt
    refine hcO (hker c (Subgroup.mem_sup_left hcK) fun u hu => ?_)
    by_contra hu'
    exact hnt ⟨u, hu, hu'⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
