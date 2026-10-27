module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixDiag

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem i271h_arith (r m w a c mZ z : ℕ) (hr1 : 1 ≤ r) (hm : 2 ≤ m) (hw : 2 ≤ w) (ha : a ≤ 2)
    (hc : c ≤ mZ) (hz : z = 1)
    (h : mZ + w + 3 ^ r * m ≤ r + a + c + 3 ^ r * z + m) : r = 1 ∧ mZ ≤ c := by
  subst hz
  have hr : r = 1 := by
    by_contra hne
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have hs : 1 ≤ s := by omega
    have h3s : s < 3 ^ s := Nat.lt_pow_self (by norm_num)
    obtain ⟨Q, hQ⟩ : ∃ Q, 3 ^ (s + 1) = Q + 1 := ⟨3 ^ (s + 1) - 1, by
      have := pow_pos (by norm_num : 0 < 3) (s + 1); omega⟩
    have hP : 3 ^ (s + 1) = 3 * 3 ^ s := by ring
    have hQm : Q * 2 ≤ Q * m := Nat.mul_le_mul_left Q hm
    have hexp : (Q + 1) * m = Q * m + m := by ring
    rw [hQ, hexp, mul_one] at h
    omega
  subst hr
  refine ⟨rfl, ?_⟩
  norm_num at h
  omega

section Numerics

variable {X : Type} [Group X] [Finite X] {B K : Subgroup X}

theorem i271h_hatSix_numerics (hO : GLAPPrimeCore 3 X = ⊥) (hBel : IsElemAbelian 3 B)
    (hr : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B) (hL : GLAPComponent 3 ⊤ K)
    (hnL : ¬ B ≤ Subgroup.normalizer (K : Set X)) (hHS : IsHatSix ↥K) :
    (Subgroup.normalizer (K : Set X)).relIndex B = 3 ∧
      Nat.card ↥(i112J B K ⊓ Subgroup.centralizer (i112J B K : Set X)) ≤ 3 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hLc : IsComponentOf K ⊤ := i116pI_isComponentOf hO hL
  have hZ3 : Nat.card ↥(Subgroup.center ↥K) = 3 := hHS.2.1
  have hcard : Nat.card ↥K = 1080 := i271h_card_hatSix hHS
  have h2 : ∃ t : ↥K, orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact exists_prime_orderOf_dvd_card' 2 (by rw [hcard]; norm_num)
  obtain ⟨r, a, hr1, hrel, hHa, hHr, hmaster⟩ := i112_master hp hO hBel hr hL hnL h2
  have hz1 : CFSG.Open.pRank 3 (Subgroup.center ↥K) = 1 := i112f_pRank_center_eq_one hZ3
  have hw2 : 2 ≤ GLATwoLocalRank 3 ↥K := t112m_twoLocal_hatSix hHS
  have hm2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) := by
    obtain ⟨T, -, -, hT⟩ := exists_twoLocal_attaining hp.one_lt h2
    exact hw2.trans (hT ▸ CFSG.SectionRank.pRank_mono hp.one_lt le_top)
  have ha2 : a ≤ 2 := by
    have := i112_pRank_H_le (B := B) (L := K) hp.one_lt
    rw [hHr] at this
    exact this.trans (i112f_pRank_mulAut_hatSix hHS)
  have hcZ : CFSG.Open.pRank 3 ((i112J B K ⊓ Subgroup.centralizer (i112J B K : Set X)) ⊓ B) ≤
      CFSG.Open.pRank 3 (i112J B K ⊓ Subgroup.centralizer (i112J B K : Set X)) :=
    CFSG.SectionRank.pRank_mono hp.one_lt inf_le_left
  obtain ⟨hr_eq, hmZc⟩ := i271h_arith r _ _ a _ _ _ hr1 hm2 hw2 ha2 hcZ hz1 hmaster
  subst hr_eq
  have hidx : (Subgroup.normalizer (K : Set X)).relIndex B = 3 := by rw [hrel, pow_one]
  refine ⟨hidx, ?_⟩
  have hc1 := i112_pRank_Z_inf_B_le_one hp rfl hO hBel hL hnL hidx hZ3
  have hE : IsElemAbelian 3 (i112J B K ⊓ Subgroup.centralizer (i112J B K : Set X)) :=
    i112_isElemAbelian_Z hLc (Or.inr hZ3)
  obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian hp hE
  have hk1 := pRank_eq_of_card hp.one_lt hE hk
  have : k ≤ 1 := by omega
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    _ = 3 := by norm_num

end Numerics

section Center

variable {X : Type} [Group X] [Finite X] {B K : Subgroup X}

theorem i271h_norm_eq_one {Zs : Subgroup X} (hZc : Nat.card Zs ≤ 3)
    (hZe : ∀ w ∈ Zs, w ^ 3 = 1) (hZab : ∀ u ∈ Zs, ∀ v ∈ Zs, u * v = v * u)
    {b z : X} (hb3 : b ^ 3 = 1) (hz0 : z ∈ Zs) (hz1 : b * z * b⁻¹ ∈ Zs)
    (hz2 : b * b * z * (b * b)⁻¹ ∈ Zs) : i271dFun b z = 1 := by
  have : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  have hbbb : b * b * b = 1 := by rw [← pow_three']; exact hb3
  set e : X := i271dFun b z with he
  have heZ : e ∈ Zs := Zs.mul_mem (Zs.mul_mem hz0 hz1) hz2
  have he3 : e ^ 3 = 1 := hZe e heZ
  have hbe : b * e * b⁻¹ = e := by
    have h1 : b * e * b⁻¹ = (b * z * b⁻¹) * (b * b * z * (b * b)⁻¹) *
        (b * b * b * z * (b * b * b)⁻¹) := by
      rw [he]; unfold i271dFun; group
    rw [hbbb] at h1
    simp only [inv_one, mul_one, one_mul] at h1
    rw [h1, he]
    unfold i271dFun
    have := hZab z hz0 _ (Zs.mul_mem hz1 hz2)
    rw [mul_assoc z (b * z * b⁻¹), this]
  by_contra he1
  have heo : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hle : Subgroup.zpowers e ≤ Zs := Subgroup.zpowers_le.2 heZ
  have heq : Subgroup.zpowers e = Zs :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, heo]; exact hZc)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (heq ▸ hz0 : z ∈ Subgroup.zpowers e)
  have hzfix : b * z * b⁻¹ = z := by
    rw [← hk]
    have := map_zpow (MulAut.conj b) e k
    simpa [MulAut.conj_apply, hbe] using this
  have hz2' : b * b * z * (b * b)⁻¹ = z := by
    calc b * b * z * (b * b)⁻¹ = b * (b * z * b⁻¹) * b⁻¹ := by group
      _ = z := by rw [hzfix, hzfix]
  apply he1
  rw [he]
  unfold i271dFun
  rw [hzfix, hz2']
  calc z * z * z = z ^ 3 := (pow_three' z).symm
    _ = 1 := hZe z hz0

theorem i271h_dFun_center (hO : GLAPPrimeCore 3 X = ⊥) (hL : GLAPComponent 3 ⊤ K)
    (hBel : IsElemAbelian 3 B) {b : X} (hb : b ∈ B)
    (hZ3 : Nat.card ↥(Subgroup.center ↥K) = 3)
    (hZJ : Nat.card ↥(i112J B K ⊓ Subgroup.centralizer (i112J B K : Set X)) ≤ 3) :
    ∀ z ∈ centreIn K, i271dFun b z = 1 := by
  intro z hz
  have hLc : IsComponentOf K ⊤ := i116pI_isComponentOf hO hL
  have hb3 : b ^ 3 = 1 := hBel.2 b hb
  have hE : IsElemAbelian 3 (i112J B K ⊓ Subgroup.centralizer (i112J B K : Set X)) :=
    i112_isElemAbelian_Z hLc (Or.inr hZ3)
  have hZab : ∀ u ∈ i112J B K ⊓ Subgroup.centralizer (i112J B K : Set X),
      ∀ v ∈ i112J B K ⊓ Subgroup.centralizer (i112J B K : Set X), u * v = v * u :=
    fun u hu v hv => Subgroup.mem_centralizer_iff.1 hv.2 u hu.1
  refine i271h_norm_eq_one hZJ hE.2 hZab hb3 ?_ ?_ ?_
  · exact i112_centreIn_le_Z hLc i112_self_mem_orbit hz
  · have hmem : b * z * b⁻¹ ∈ centreIn (GLBConj b⁻¹ K) := by
      rw [centreIn_gLBConj, mem_gLBConj]
      convert hz using 1
      group
    exact i112_centreIn_le_Z hLc (i112_gLBConj_mem_orbit (B.inv_mem hb)) hmem
  · have hbb : b * b ∈ B := B.mul_mem hb hb
    have hmem : b * b * z * (b * b)⁻¹ ∈ centreIn (GLBConj (b * b)⁻¹ K) := by
      rw [centreIn_gLBConj, mem_gLBConj]
      convert hz using 1
      group
    exact i112_centreIn_le_Z hLc (i112_gLBConj_mem_orbit (B.inv_mem hbb)) hmem

theorem i271h_autOrderIn_eq_card_H (hBel : IsElemAbelian 3 B) :
    autOrderIn B K = Nat.card (i112H B K) := by
  have hA := i112_card_A (B := B) (L := K) hBel
  have hBc : i112Bc B K = Subgroup.centralizer (K : Set X) ⊓ (B ⊓ Subgroup.normalizer (K : Set X)) := by
    rw [i112_Bc_eq hBel]
    ext y
    simp only [i112A, Subgroup.mem_inf]
    tauto
  have hAA : i112A B K = B ⊓ Subgroup.normalizer (K : Set X) := by
    unfold i112A
    exact inf_comm _ _
  have hrel := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (K : Set X))
    (K := B ⊓ Subgroup.normalizer (K : Set X))
  rw [← hBc] at hrel
  have hpos : 0 < Nat.card ↥(i112Bc B K) := Nat.card_pos
  have hAcard : Nat.card ↥(i112A B K) = Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) := by
    rw [hAA]
  have : autOrderIn B K * Nat.card ↥(i112Bc B K) = Nat.card (i112H B K) * Nat.card ↥(i112Bc B K) := by
    unfold autOrderIn
    rw [hrel, ← hAcard, hA]
  exact Nat.eq_of_mul_eq_mul_right hpos this

end Center

theorem i271NNHatSixRank_holds : I271NNHatSixRank := by
  intro X _ _ hXK K B hH hnN hHS
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  have hLc : IsComponentOf K ⊤ := i116pI_isComponentOf hH.core hH.comp
  obtain ⟨hidx, hZJ⟩ := i271h_hatSix_numerics hH.core hBel hH.rank_local hH.comp hnN hHS
  obtain ⟨b, hbB, hbN⟩ : ∃ b ∈ B, b ∉ Subgroup.normalizer (K : Set X) := by
    by_contra h
    exact hnN fun b hb => by_contra fun hb' => h ⟨b, hb, hb'⟩
  have hz := i271h_dFun_center hH.core hH.comp hBel hbB hHS.2.1 hZJ
  have hcl : ∀ x : ↥K, x ^ 3 = 1 → (∀ φ ∈ i112H B K, φ x * x⁻¹ ∈ Subgroup.center ↥K) →
      (MulAut.conj x : MulAut ↥K) ∈ i112H B K := by
    intro x hx3 hfix
    have hxK : (x : X) ∈ K := x.2
    have hx3X : (x : X) ^ 3 = 1 := by
      have := congrArg Subtype.val hx3
      simpa using this
    have hfix' : ∀ a ∈ B ⊓ Subgroup.normalizer (K : Set X),
        a * (x : X) * a⁻¹ * (x : X)⁻¹ ∈ centreIn K := by
      intro a ha
      have hmem : (⟨a, ha.2, ha.1⟩ : ↥(i112A B K)) = ⟨a, ha.2, ha.1⟩ := rfl
      have h1 := hfix (i112Act B K ⟨a, ha.2, ha.1⟩) ⟨_, rfl⟩
      rw [mem_centreIn]
      have h2 : ((i112Act B K ⟨a, ha.2, ha.1⟩ x * x⁻¹ : ↥K) : X) =
          a * (x : X) * a⁻¹ * (x : X)⁻¹ := by
        simp [i112Act_apply]
      refine ⟨?_, fun g hg => ?_⟩
      · rw [← h2]
        exact (i112Act B K ⟨a, ha.2, ha.1⟩ x * x⁻¹ : ↥K).2
      · have := Subgroup.mem_center_iff.1 h1 ⟨g, hg⟩
        have h3 := congrArg Subtype.val this
        rw [← h2]
        simpa using h3
    obtain ⟨y, hy, hact⟩ := i271h_diag hLc hBel hH.scp hbB hbN hidx hz hxK hx3X hfix'
    refine ⟨⟨y, hy.2, hy.1⟩, ?_⟩
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [i112Act_apply]
    have := hact k k.2
    simpa [MulAut.conj_apply] using this
  have hH3 : ∀ φ ∈ i112H B K, φ ^ 3 = 1 := (i112_isElemAbelian_H hBel).2
  have h9 := i271h_hatSix_core hHS (i112H B K) hH3 hcl
  rw [i271h_autOrderIn_eq_card_H hBel]
  simpa using h9

end CFSG.HardMathSupport.Solomon.Coordinator
