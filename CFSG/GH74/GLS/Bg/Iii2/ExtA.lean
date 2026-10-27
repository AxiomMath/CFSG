module

public import CFSG.GH74.GLS.Bg.Iii2.ExtBasic
public import CFSG.GH74.GLS.Bg.Iii2.Basic
public import CFSG.GH74.GLS.Bg.Iii2.Statements

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_cmap_eq {y : G} {K : Subgroup G} (h : cmap y K = K) :
    y ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have h1 : y * g * y⁻¹ ∈ cmap y K := mem_cmap.2 (by simpa [mul_assoc] using hg)
    rwa [h] at h1
  · intro hg
    rw [← h, mem_cmap] at hg
    simpa [mul_assoc] using hg

theorem rr_normalized (hquat : II4_4_quat) (hG : IsKProperSimple G) {x : G} (hx : orderOf x = 2)
    {T : Subgroup G} (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) {y : G}
    (hyx : y ∈ centralizer ({x} : Set G)) (hyT : ∀ t ∈ T, t * y = y * t) {K : Subgroup G}
    (hK : IsRigidRankOneComp x K) : y ∈ normalizer (K : Set G) := by
  by_cases h : cmap y K = K
  · exact mem_normalizer_of_cmap_eq h
  · exfalso
    have hK' : IsRigidRankOneComp x (cmap y K) := isRigidRankOneComp_cmap hK hyx
    obtain ⟨n, hn⟩ := hquat G hG x hx T K hT (rr_pcomp hK) hK.2
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hnc⟩ := quat_data ⟨n, hn⟩
    apply hnc
    intro a ha b hb
    have hb' : b ∈ T ⊓ cmap y K := by
      refine ⟨hb.1, mem_cmap.2 ?_⟩
      have e : y⁻¹ * b * y = b := by rw [mul_assoc, hyT b hb.1, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact hb.2
    exact rr_sylow_comm hK hK' (Ne.symm h) hT a ha b hb'

theorem ext_core (hPU : PU) (hCM : CM) (h43d : II4_43d) (hquat : II4_4_quat) (hG : IsKProperSimple G)
    (h3 : 3 ≤ pRank 2 G) {x : G} (hx : orderOf x = 2) (hne : ∃ K, IsRigidRankOneComp x K)
    (hmax : ∀ y : G, orderOf y = 2 → (∃ J, IsRigidRankOneComp y J) → rrNum y ≤ rrNum x)
    {T S : Subgroup G} (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hxT : x ∈ T) (hTS : T ≤ S)
    {y : G} (hy : orderOf y = 2) (hyS : ∀ s ∈ S, s * y = y * s) :
    (∃ J, IsRigidRankOneComp y J) ∧ rrNum y = rrNum x ∧
      ∃ J : Subgroup G → Subgroup G, (∀ K, IsRigidRankOneComp x K → IsRigidRankOneComp y (J K)) ∧
        ∀ K, IsRigidRankOneComp x K → ∀ P : Subgroup G, IsSylowOf 2 P K → (∀ p ∈ P, y * p = p * y) →
          P ≤ J K := by
  have hyx : y ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hyS x (hTS hxT)
  have hyT : ∀ t ∈ T, t * y = y * t := fun t ht => hyS t (hTS ht)
  have hy2 : y * y = 1 := by
    have h1 := pow_orderOf_eq_one y
    rw [hy, pow_two] at h1
    exact h1
  have hcSec : ∀ K, IsRigidRankOneComp x K → y ∈ cSec K := fun K hK =>
    h43d G hG x hx K hK y hy2 hyx (rr_normalized hquat hG hx hT hyx hyT hK) (T ⊓ K) (rr_sylow hK hT)
      (fun p hp => (hyT p hp.1).symm)
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨J₀, hJ₀⟩ := hPU G hG h3 x y K₀ hK₀ hy hyx (hcSec K₀ hK₀)
  have hle : rrNum y ≤ rrNum x := hmax y hy ⟨J₀, hJ₀⟩
  let R : Finset (Subgroup G) := (Set.toFinite {K : Subgroup G | IsRigidRankOneComp x K}).toFinset
  have hR : ∀ K, K ∈ R ↔ IsRigidRankOneComp x K := fun K => Set.Finite.mem_toFinset _
  have hRcard : R.card = rrNum x := (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
  obtain ⟨J, hinj, hJrr, himg, hsyl⟩ := hCM G hG h3 x y hx hy hyx R hR
    (fun K hK => hcSec K ((hR K).1 hK)) (by rw [hRcard]; exact hle)
  have hnum : rrNum y = rrNum x := by
    have h1 : rrNum y = (J '' (R : Set (Subgroup G))).ncard := by
      unfold rrNum
      rw [himg]
    rw [h1, Set.InjOn.ncard_image hinj, Set.ncard_coe_finset, hRcard]
  exact ⟨⟨J₀, hJ₀⟩, hnum, J, fun K hK => hJrr K ((hR K).2 hK),
    fun K hK P hP hc => hsyl K ((hR K).2 hK) P hP hc⟩

end CFSG.GH74.GLS.Bg.Iii2
