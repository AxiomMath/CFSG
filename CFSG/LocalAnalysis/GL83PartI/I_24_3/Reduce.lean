module

public import CFSG.LocalAnalysis.GL83PartI.I_22_6
public import CFSG.LocalAnalysis.PreuniquenessRankFour.RankTwo
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace GL83.I243

open CFSG CFSG.Open CFSG.PreuniquenessRankFour.Helpers Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem sc_of_maximal {p : ℕ} (hp : p.Prime) (R : Sylow p X) {B : Subgroup X}
    (hBel : IsElemAbelian p B)
    (hBcard : Nat.card B = p ^ Open.pRank p (R : Subgroup X)) :
    ∀ y ∈ Subgroup.centralizer (B : Set X), y ^ p = 1 → y ∈ B := by
  intro y hy hyp
  have : Fact p.Prime := ⟨hp⟩
  have hyel : IsElemAbelian p (Subgroup.zpowers y) := isElemAbelian_zpowers hyp
  have hBy : B ≤ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup X) : Set X) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hy)
  have hA := elementary_abelian_sup_of_commuting p hBel hyel hBy
  have hrank : Open.pRank p (B ⊔ Subgroup.zpowers y) ≤ Open.pRank p (R : Subgroup X) :=
    (pRank_mono p hp le_top).trans (CFSG.SectionRank.pRank_sylow R).1.ge
  have heq := elementary_subgroup_eq_of_rank_bound p hp hA le_sup_left _ hBcard hrank
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

theorem pRank_eq_of_max {p : ℕ} (hp : p.Prime) (R : Sylow p X) {B : Subgroup X}
    (hBR : B ≤ (R : Subgroup X)) (hBel : IsElemAbelian p B)
    (hBcard : Nat.card B = p ^ Open.pRank p (R : Subgroup X)) :
    Open.pRank p B = Open.pRank p (R : Subgroup X) :=
  le_antisymm (pRank_mono p hp hBR)
    (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hBel hBcard)

theorem normalizes_of_not_le_weakCore {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (R : Sylow p X)
    {B K : Subgroup X} (hBR : B ≤ (R : Subgroup X)) (hBel : IsElemAbelian p B)
    (hBcard : Nat.card B = p ^ Open.pRank p (R : Subgroup X))
    (h3 : 3 ≤ Open.pRank p (R : Subgroup X)) (hK : IsComponentOf K ⊤)
    (hZ : p ∣ Nat.card (Subgroup.center K))
    (hKR : ¬ K ≤ GLBWeakCore p (R : Subgroup X)) :
    B ≤ Subgroup.normalizer (K : Set X) := by
  by_contra hBK
  apply hKR
  have h1 := GL83.component_le_gamma_of_not_normalizes hp hp2 hBel
    (sc_of_maximal hp R hBel hBcard) hK hBK hZ
  have hB3 : 3 ≤ Open.pRank p B := (pRank_eq_of_max hp R hBR hBel hBcard).symm ▸ h3
  have hcomm : IsMulCommutative B := hBel.1
  rw [← weakCore_eq_fullCore_of_commutative p hp B hcomm hB3] at h1
  exact h1.trans (weakCore_mono p hp hBR)

theorem exists_mem_center_of_normalizes {p : ℕ} (hp : p.Prime) {B K : Subgroup X}
    (hBel : IsElemAbelian p B) (hSC : ∀ y ∈ Subgroup.centralizer (B : Set X), y ^ p = 1 → y ∈ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hZ : p ∣ Nat.card (Subgroup.center K)) :
    ∃ z ∈ B, z ∈ K ∧ z ∈ Subgroup.centralizer (K : Set X) ∧ orderOf z = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' p hZ
  have hz₀K : ((z₀ : K) : X) ∈ K := (z₀ : K).2
  have hz₀ord : orderOf ((z₀ : K) : X) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz₀]
  have hz₀c : ∀ y ∈ K, y * ((z₀ : K) : X) = ((z₀ : K) : X) * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 z₀.2 ⟨y, hy⟩)
  have hz₀V : ((z₀ : K) : X) ∈ GL83.CompFam.torsionCentre p K :=
    ⟨hz₀K, fun w hw => (hz₀c w hw).symm, by
      rw [← hz₀ord]
      exact pow_orderOf_eq_one _⟩
  have hVdvd : p ∣ Nat.card (GL83.CompFam.torsionCentre p K) := by
    have h := orderOf_dvd_natCard (⟨_, hz₀V⟩ : GL83.CompFam.torsionCentre p K)
    rwa [Subgroup.orderOf_mk, hz₀ord] at h
  have hBV : B ≤ Subgroup.normalizer ((GL83.CompFam.torsionCentre p K : Subgroup X) : Set X) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    have hcK : GL83.CompFam.cj c K = K :=
      GL83.CompFam.cj_eq_iff_mem_normalizer.mpr (hBN hc)
    have hcK' : GL83.CompFam.cj c⁻¹ K = K :=
      GL83.CompFam.cj_eq_iff_mem_normalizer.mpr (hBN (B.inv_mem hc))
    intro v
    refine ⟨fun hv => GL83.CompFam.conj_mem_torsionCentre hcK hv, fun hv => ?_⟩
    have h := GL83.CompFam.conj_mem_torsionCentre hcK' hv
    have e : c⁻¹ * (c * v * c⁻¹) * c⁻¹⁻¹ = v := by group
    rwa [e] at h
  obtain ⟨v, hvV, hv1, hvB⟩ :=
    GL83.CompFam.exists_ne_one_commute_of_isPGroup hBel.isPGroup hBV hVdvd
  obtain ⟨hvK, hvc, hvp⟩ := hvV
  have hvB' : v ∈ B := hSC v (Subgroup.mem_centralizer_iff.2 fun c hc => hvB c hc) hvp
  exact ⟨v, hvB', hvK, Subgroup.mem_centralizer_iff.2 fun w hw => (hvc w hw).symm,
    orderOf_eq_prime hvp hv1⟩

theorem two_le_pRank_sup_zpowers {p : ℕ} (hp : p.Prime) {z b : X} (hz : orderOf z = p)
    (hzb : z * b = b * z) (hbp : b ^ p = 1) (hb : b ∉ Subgroup.zpowers z) :
    2 ≤ Open.pRank p (Subgroup.zpowers z ⊔ Subgroup.zpowers b) := by
  have : Fact p.Prime := ⟨hp⟩
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  have hc : Commute z b := hzb
  have hzc : Subgroup.zpowers z ≤ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup X) : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hc.symm.zpow_left k).eq
  have hQ := elementary_abelian_sup_of_commuting p (isElemAbelian_zpowers hzp)
    (isElemAbelian_zpowers hbp) hzc
  obtain ⟨k, hk⟩ := hQ.isPGroup.exists_card_eq
  have hle : Subgroup.zpowers z ≤ Subgroup.zpowers z ⊔ Subgroup.zpowers b := le_sup_left
  have hcard1 : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  have hge : p ≤ p ^ k := by
    have h := Subgroup.card_le_of_le hle
    rwa [hcard1, hk] at h
  have hk1 : k ≠ 1 := by
    rintro rfl
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hk, hcard1, pow_one])
    exact hb (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := hp.one_lt
    simp at hge
    omega
  exact (show 2 ≤ k by omega).trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hQ hk)

theorem inf_centralizer_le_zpowers {p : ℕ} (hp : p.Prime) (R : Sylow p X)
    {B K : Subgroup X} (hKR : ¬ K ≤ GLBWeakCore p (R : Subgroup X))
    (hBR : B ≤ (R : Subgroup X)) (hBel : IsElemAbelian p B) (hB3 : 3 ≤ Open.pRank p B)
    {z : X} (hzB : z ∈ B) (hzc : z ∈ Subgroup.centralizer (K : Set X)) (hzp : orderOf z = p) :
    ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b ∈ Subgroup.zpowers z := by
  intro b hbB hbc
  by_contra hbz
  apply hKR
  have hbp : b ^ p = 1 := hBel.2 b hbB
  have hzbc : z * b = b * z := congrArg Subtype.val (hBel.1.is_comm.comm ⟨z, hzB⟩ ⟨b, hbB⟩)
  have hQB : Subgroup.zpowers z ⊔ Subgroup.zpowers b ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hzB) (Subgroup.zpowers_le.mpr hbB)
  have hQc : Subgroup.zpowers z ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer (K : Set X) :=
    sup_le (Subgroup.zpowers_le.mpr hzc) (Subgroup.zpowers_le.mpr hbc)
  have hKQ : K ≤ Subgroup.centralizer ((Subgroup.zpowers z ⊔ Subgroup.zpowers b : Subgroup X) :
      Set X) := Subgroup.le_centralizer_iff.mp hQc
  exact hKQ.trans ((Subgroup.centralizer_le_normalizer _).trans
    (normalizer_le_weakCore_of_commutative_overgroup p hp hBR hQB hBel.1
      (two_le_pRank_sup_zpowers hp hzp hzbc hbp hbz) hB3))

end GL83.I243
