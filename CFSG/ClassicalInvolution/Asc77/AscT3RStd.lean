module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIISetup
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC3
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate8A
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate9A
public import CFSG.ClassicalInvolution.Asc77.AscT3RPsi

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution.Asc77.T3CII.T3R
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement Pointwise

section StdFacts

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}



theorem Std20.r9_cStar_S (d : Std20 p f K K' J S R R' W V z t) (c8 : Concl20_8 S K' R) {u : G}
    (hu : u ∈ (S : Subgroup G)) (huK : conjSub u K = K') {y : G} (hy : y ∈ (S : Subgroup G))
    (hyc : y ∈ cStar K) : y ∈ R' := by
  have c8' : centralizerModOdd (S : Subgroup G) K' = R := c8
  have h1 : y ∈ centralizerModOdd (S : Subgroup G) K := by
    obtain ⟨-, hN, hNO, hcomm⟩ := (mem_centralizerModOdd_top_iff (L := K)).mpr hyc
    exact ⟨hy, hN, hNO, hcomm⟩
  have h2 := late_cmo_conj_mem h1 u
  rw [conjSub_eq_self_of_mem hu, huK, c8'] at h2
  have h3 : u * y * u⁻¹ ∈ K := d.hR.1 h2
  have hK' : conjSub u K' = K := (d.late_swap_data hu huK).1
  have h4 : conjSub u⁻¹ K = K' := by rw [← hK', conjSub_inv_conjSub]
  have h5 : y ∈ K' := by
    rw [← h4, mem_conjSub_iff]
    simpa using h3
  rw [d.late_R'_eq]
  exact ⟨h5, hy⟩


theorem Std20.r9_JW_sq (d : Std20 p f K K' J S R R' W V z t) {b : G} (hb : b ∈ J ⊓ W) :
    b * b ∈ K ⊔ K' := by
  have hp := d.branch.odd
  have hq := d.branch.five
  obtain ⟨v₀, Ks, -, -, hSyl, hKs, htw, hvv⟩ := exists_hexagon_data hp hq d.hyp d.late_mem_K
    d.late_mem_J d.viol.hzK d.viol.hzJ d.viol.star d.viol.not_nbr d.viol.no_conj
  have hKsK' : Ks = K' := by
    have hm : Ks ∈ twinSet (CoreAssembly.conjClass K) K := by rw [htw]; exact Or.inr rfl
    rw [d.twins] at hm
    rcases hm with h1 | h1
    · exact absurd h1 hKs
    · exact h1
  rw [hKsK'] at hvv
  have hJW := d.late_isSylow2In_JW d.late_JW
  obtain ⟨c, hc, hcP⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hJW hSyl
  have hb' : c * b * c⁻¹ ∈ Subgroup.zpowers v₀ := by
    rw [← hcP, mem_conjSub_iff]
    have e : c⁻¹ * (c * b * c⁻¹) * c = b := by group
    rw [e]
    exact hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
  have hbk : b = c⁻¹ * v₀ ^ k * c := by
    rw [hk]
    group
  have hcN : c⁻¹ ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ (d.late_cent_le_normalizer_sup hc.2)
  have e1 : v₀ ^ k * v₀ ^ k = (v₀ * v₀) ^ k := ((Commute.refl v₀).mul_zpow k).symm
  have hsq : b * b = c⁻¹ * (v₀ * v₀) ^ k * c := by
    rw [← e1, hbk]
    group
  rw [hsq]
  have hz : (v₀ * v₀) ^ k ∈ K ⊔ K' := Subgroup.zpow_mem _ hvv k
  simpa using (Subgroup.mem_normalizer_iff.mp hcN _).mp hz

theorem Std20.r9_V_sq (d : Std20 p f K K' J S R R' W V z t) {x : G} (hx : x ∈ V) :
    x * x ∈ K ⊔ K' := by
  have hWc := d.late_hWc
  have hJWK : W ⊓ J ≤ Subgroup.normalizer ((W ⊓ K : Subgroup G) : Set G) :=
    AscL62.le_normalizer_of_commutes fun x hx y hy => hWc x hx.1 y hy.1
  have hxW : x ∈ (W ⊓ K) ⊔ (W ⊓ J) := d.late_hW ▸ d.hVW hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (W ⊓ K) (W ⊓ J) hJWK]
    at hxW
  obtain ⟨a, ha, b, hb, rfl⟩ := hxW
  have hab : a * b = b * a := hWc a ha.1 b hb.1
  have h1 : a * b * (a * b) = (a * a) * (b * b) := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
  rw [h1]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.mul_mem ha.2 ha.2))
    (d.r9_JW_sq ⟨hb.2, hb.1⟩)


theorem Std20.r9_K'_le_cStar (d : Std20 p f K K' J S R R' W V z t) : K' ≤ cStar K := by
  intro y hy
  have hcomm := d.hyp.comm_le_oddCore_of_twin d.late_mem_K d.late_mem_K' d.ne.symm d.viol.hzK
    d.late_hzK'
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := d.late_K'_le hy
  refine (mem_centralizerModOdd_top_iff (L := K)).mp ⟨trivial, hyN,
    mem_normalizer_oddCore_of_mem_normalizer hyN, fun l hl => ?_⟩
  have h1 : ⁅y, l⁆ ∈ ⁅K', K⁆ := Subgroup.commutator_mem_commutator hy hl
  rw [Subgroup.commutator_comm] at h1
  exact (hcomm h1).1

theorem Std20.r9_vdata (d : Std20 p f K K' J S R R' W V z t) :
    ∃ v : G, V = Subgroup.zpowers v ∧ 2 * orderOf v = Nat.card R ∧
      v ∈ Subgroup.normalizer (K : Set G) := by
  have hp := d.branch.odd
  have hΩ := d.hyp
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  obtain ⟨-, -, -, -, -, -, hVcyc, -, -⟩ := hΩ.exists_data_of_mem_USet hp d.hV
  obtain ⟨g, hg⟩ := hVcyc.exists_generator
  have hVeq : V = Subgroup.zpowers (g : G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro hx
      exact (Subgroup.zpowers_le (H := V)).mpr g.2 hx
  have hord : orderOf (g : G) = Nat.card V := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hc := Sec7.natCard_eq_two_mul_of_mem_USet hp hΩ d.hV hKΩ d.hR
  refine ⟨(g : G), hVeq, by rw [hord, hc], ?_⟩
  exact d.late_W_le_N_K (d.hVW g.2)

theorem Std20.r9_hinj (d : Std20 p f K K' J S R R' W V z t) (c8 : Concl20_8 S K' R) {u : G}
    (hu : u ∈ (S : Subgroup G)) (huK : conjSub u K = K') {v : G} (hv : V = Subgroup.zpowers v)
    (n : ℕ) (hn : v ^ n ∈ cStar K) : v ^ n = 1 := by
  by_contra h1
  have hvV : v ∈ V := hv ▸ Subgroup.mem_zpowers v
  have hxV : v ^ n ∈ V := V.pow_mem hvV n
  have hxS : v ^ n ∈ (S : Subgroup G) := d.hVS hxV
  have hxR' : v ^ n ∈ R' := d.r9_cStar_S c8 hu huK hxS hn
  have hxK' : v ^ n ∈ K' := d.hR'.1 hxR'
  have hx2 : IsPGroup 2 ↥(Subgroup.zpowers (v ^ n)) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)
  obtain ⟨m, hm2, hm1⟩ := late_exists_pow_invol hx2 h1
  have hmV : (v ^ n) ^ m ∈ V := V.pow_mem hxV m
  have hmK' : (v ^ n) ^ m ∈ K' := K'.pow_mem hxK' m
  have ht : (v ^ n) ^ m = t := d.eq_t_of_invol_mem_V hmV hm2 hm1
  rcases d.late_hzK'.unique _ hmK' hm2 with h | h
  · exact hm1 h
  · exact d.late_ne_inv (ht.symm.trans h)

theorem Std20.r9_eps_v (d : Std20 p f K K' J S R R' W V z t) (c8 : Concl20_8 S K' R) {u : G}
    (hu : u ∈ (S : Subgroup G)) (huK : conjSub u K = K') {F : Type} [Field F] [Finite F]
    (eK : ↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, F)) (hF : Odd (Nat.card F))
    (hK : IsOddPrimePower (Nat.card F)) (h4 : 4 ≤ Nat.card F) {v : G}
    (hv : V = Subgroup.zpowers v) (hord : 2 * orderOf v = Nat.card R)
    (hvN : v ∈ Subgroup.normalizer (K : Set G)) :
    epsG hK K eK v ≠ 1 ∧ rhoG K eK v * rhoG K eK v = 1 := by
  have hvV : v ∈ V := hv ▸ Subgroup.mem_zpowers v
  have hsq : ∃ k ∈ K, ∃ y ∈ cStar K, v * v = k * y := by
    have h1 := d.r9_V_sq hvV
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K K' d.late_K'_le] at h1
    obtain ⟨k, hk, y, hy, hky⟩ := h1
    exact ⟨k, hk, y, d.r9_K'_le_cStar hy, hky.symm⟩
  refine ⟨epsG_ne_one_of_cyclic hF h4 d.hR hvN hsq hord (d.r9_hinj c8 hu huK hv), ?_⟩
  obtain ⟨k, hk, y, hy, hky⟩ := hsq
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := cStar_le_normalizer K hy
  rw [← rhoG_mul hvN hvN, hky, rhoG_mul hkN hyN, rhoG_of_mem_L hk,
    rhoG_of_phiG_eq_one ((phiG_eq_one_iff hyN).mpr hy), mul_one]

end StdFacts

end CFSG.ClassicalInvolution.Asc77.T3CII
