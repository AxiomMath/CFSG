module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A5W1618e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5V1367d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

local notation "StSL" => Assembly.LowTwoRank.StatedSL

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_sl2_ge_eight_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h56 : AsB56)
    (hH : S.Hyp1367) {K : Subgroup G} (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥(S.plus K) ≃* ↥(StSL 2 F)) : False := by
  have hF' := hH.hF
  have hq := S.isQuasisimple_plus_F4 h1222 h517 hF' hK hT
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF' hK.1 hT
  have : IsMulCommutative ↥(S.WK K) := hR.2.2.1.1
  have hWT := (S.WK_le_Tv_F4 h1222 h517 hF' hK.1 hT).1
  have hSQ := S.sqtkGroup_HK_F4 h1222 h517 hF' hK.1 hT
  have hKJ := S.plus_le_jStar_F4 h1222 h517 hF' hK hT
  have hJne : autOn (thompsonJ S.Tv) (S.WK K) ≠ ⊥ := by
    intro h
    have h1 := S.plus_eq_commutator_F4 h1222 h517 hF' hK hT
    rw [h, Subgroup.commutator_bot_right] at h1
    exact (qs_perfect_ne_bot hq).2 h1.symm
  have hcases := b56Cases_jStar h56 hWT (S.Tv_le_HK K) hR hSQ hJne
  have hb := b53Hyp_jStar hWT (S.Tv_le_HK K) hR hSQ
  have hHKW : S.HK K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hR.2.1
  have hNn : ∀ x ∈ jStar (S.HK K) S.Tv (S.WK K), ∀ m ∈ S.plus K, x * m * x⁻¹ ∈ S.plus K :=
    fun x hx m hm => (Subgroup.mem_normalizer_iff.mp
      (S.HK_le_normalizer_plus_F4 h1222 h517 hF' hK hT (jStar_le (S.Tv_le_HK K) hx)) m).mp hm
  have hV2 : ∀ v : ↥(S.WK K), v ^ 2 = 1 := fun v =>
    Subtype.ext (by rw [Subgroup.coe_pow, hR.2.2.1.2 _ v.2, Subgroup.coe_one])
  set W := S.WK K with hWdef
  set J := jStar (S.HK K) S.Tv W with hJdef
  set N := S.plus K with hNdef
  obtain ⟨G₂, U, C, K', _, _, π, hK', hsup, hinf, hc, hπ, hCfix, hUV⟩ :=
    sl2_natural_of_b56 hV2 hb hcases hKJ hNn hq hn hF e
  have hcharK : CharP K' 2 := R3c.charP_two_of_natCard_eq_two_pow hK'
  have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
  have hKHK : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer ((W : Subgroup G) : Set G) := hKHK.trans hHKW

  have hzW : S.z ∈ W := le_conjClosure _ _ (Subgroup.mem_zpowers _)
  set zW : ↥W := ⟨S.z, hzW⟩ with hzWdef
  have hTz : ∀ q ∈ autOn S.Tv W, q zW = zW := by
    intro q hq
    obtain ⟨⟨t, htN⟩, ht, rfl⟩ := Setup.mem_autOn_iff.1 hq
    exact Subtype.ext (by
      rw [InternalSec.coe_conjAct_apply]
      exact S.conj_z_of_mem_T (Subgroup.mem_inf.mp ht).1)

  have hNz : ¬ ∀ g ∈ N, g zW = zW := by
    intro hfix
    apply S.not_le_centralizer_z_of_inYz hK hT
    intro k hk
    have h1 := hfix _ (Setup.mem_autOn_iff.2 ⟨⟨k, hKW hk⟩, hk, rfl⟩)
    have h2 : k * S.z * k⁻¹ = S.z := by
      have := congrArg Subtype.val h1
      rwa [InternalSec.coe_conjAct_apply] at this
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * S.z = k * S.z * k⁻¹ * k := by group
      _ = S.z * k := by rw [h2]

  have hTvHK : IsSylowTwoOf (autOn S.Tv W) (autOn (S.HK K) W) :=
    Setup.isSylowTwoOf_autOn (S.isSylowTwoOf_Tv_HK_F4 h1222 h517 hK.1) hHKW
  have hJHK : J ≤ autOn (S.HK K) W := jStar_le (S.Tv_le_HK K)
  have hsylJ : IsSylowTwoOf (autOn S.Tv W ⊓ J) J :=
    A4.isSylowTwoOf_inf_normal hTvHK hJHK le_normalizer_jStar
  set Q := autOn S.Tv W ⊓ J with hQ
  have hQ₁syl : IsSylowTwoOf (Q ⊓ N) N :=
    A4.isSylowTwoOf_inf_normal hsylJ hKJ (normal_left_of_commute hsup hc)
  have hQQQ : (Q ⊓ N) ⊔ (Q ⊓ G₂) = Q := by
    have h1 := card_sylow_eq_mul hsup hinf hc hsylJ
    have hinfP : (Q ⊓ N) ⊓ (Q ⊓ G₂) = ⊥ := le_bot_iff.mp (hinf ▸ inf_le_inf inf_le_right
      inf_le_right)
    have h2 := card_sup_eq_mul_of_commute hinfP fun a ha b hb => hc a ha.2 b hb.2
    refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
    rw [h2, h1]

  have hπinj := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  obtain ⟨s, hsU, hsT⟩ := exists_conj_unitriangular hπinj hπ.1 hQ₁syl
  obtain ⟨μ, hμgen⟩ := IsCyclic.exists_generator (α := K'ˣ)
  have hμord : 7 ≤ orderOf μ := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμgen, Nat.card_units, hK']
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hμm : ∀ m : ℕ, 1 ≤ m → m ≤ 3 → ((μ ^ m : K'ˣ) : K') ≠ 1 := by
    intro m hm1 hm3 h
    have h1 : μ ^ m = 1 := Units.ext (by rw [h, Units.val_one])
    exact pow_ne_one_of_lt_orderOf (by omega) (by omega) h1
  set x : MulAut ↥W := ((π (slOf (s * tor μ * s⁻¹)) : ↥N) : MulAut ↥W) with hx
  have hxN : x ∈ N := (π (slOf (s * tor μ * s⁻¹))).2
  have hxN₁ : x ∈ Subgroup.normalizer ((Q ⊓ N : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) :=
    hsT μ
  have hxN₂ : x ∈ Subgroup.normalizer ((Q ⊓ G₂ : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) :=
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact (hc x hxN p hp.2).symm)
  have hxQ : x ∈ Subgroup.normalizer ((Q : Subgroup (MulAut ↥W)) : Set (MulAut ↥W)) := by
    rw [← hQQQ, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN₁,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN₂]
  have hxHK : x ∈ autOn (S.HK K) W := A4.autOn_mono hKHK hxN

  obtain ⟨y, hyHK, hyJ, r, hr, hyr⟩ := exists_normalizer_thompsonJ_gen
    (S.isSylowTwoOf_Tv_HK_F4 h1222 h517 hK.1) hHKW
    (autOn_thompsonJ_le_jStar (S.Tv_le_HK K) hHKW) le_normalizer_jStar hxHK hxQ
  obtain ⟨c, hcE, k, ⟨hkG, hkB⟩, hyck⟩ :=
    S.exists_normalizer_baum_F4 h1222 h517 (S.HK_le_Gv hK.1 hyHK) hyJ
  have hk : k = c⁻¹ * y := by rw [hyck, inv_mul_cancel_left]
  have hzE : S.z ∈ omegaOneCenterOf (thompsonJ S.Tv) := by
    rw [show S.Tv = T ⊓ Subgroup.centralizer ({S.v12} : Set G) from rfl, S.lemma_13_6_4.2]
    exact S.V2_le_omegaOneCenter_J (S.V1_le_V2 (S.mem_V1.2 (Or.inr rfl)))
  have hyE : y ∈ Subgroup.normalizer (omegaOneCenterOf (thompsonJ S.Tv) : Set G) :=
    A4.normalizer_le_normalizer_omegaOneCenterOf _ hyJ

  have hconj : ∀ i : ℕ, k ^ i * S.z * (k ^ i)⁻¹ = ((((r * x) ^ i) zW : ↥W) : G) := by
    intro i
    rw [hk, (conj_pow_eq_of_centralizer hcE hyE hzE i).1, ← hyr, coe_conjAct_pow]

  have hQz : ∀ q ∈ Q, q zW = zW := fun q hq => hTz q hq.1
  have hfix : ∀ m : ℕ, 1 ≤ m → m ≤ 3 → ((r * x) ^ m) zW ≠ zW := by
    intro m hm1 hm3 hrx
    have hxm := fix_pow_of_fix hr hxQ hQz hrx
    have hxm' : ((π (slOf (s * tor (μ ^ m) * s⁻¹)) : ↥N) : MulAut ↥W) zW = zW := by
      rw [tor_pow, ← conj_pow, map_pow, map_pow, Subgroup.coe_pow]
      exact hxm
    refine hNz (fix_of_fix_conj_borel hπ hCfix (qs_perfect_ne_bot hq).1 (fun g hg => hUV g hg zW)
      s (fun t => hQz _ (hsU t).1) (hμm m hm1 hm3) hxm')

  have hne : ∀ i j : ℕ, i < j → j ≤ 3 → ((r * x) ^ i) zW ≠ ((r * x) ^ j) zW := by
    intro i j hij hj h
    apply hfix (j - i) (by omega) (by omega)
    have e : (r * x) ^ j = (r * x) ^ i * (r * x) ^ (j - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hij.le]
    rw [e, MulAut.mul_apply] at h
    have := congrArg (((r * x) ^ i)⁻¹ ·) h
    simpa only [MulAut.inv_apply_self] using this.symm
  have hB : baum S.Tv = baum T := S.lemma_13_6_4.1
  have hMV : ∀ i : ℕ, k ^ i ∈ Subgroup.normalizer (V : Set G) ⊓
      Subgroup.centralizer ({S.v12} : Set G) := fun i =>
    S.lemma_13_6_5_F4 h1222 h517 ⟨Subgroup.pow_mem _ hkG i, hB ▸ Subgroup.pow_mem _ hkB i⟩
  refine S.false_of_four_conj (a := fun i => k ^ (i : ℕ)) (fun i => (hMV i).1) (fun i => (hMV i).2)
    fun i j hij h => ?_
  rw [hconj, hconj] at h
  have h' := Subtype.ext h
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
  · exact hne i j hlt (by omega) h'
  · exact hne j i hlt (by omega) h'.symm

theorem false_of_sl2_two_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hH : S.Hyp1367) {K : Subgroup G} (hK : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (e : ↥(S.plus K) ≃* ↥(StSL 2 F)) : False := by
  have hq := S.isQuasisimple_plus_F4 h1222 h517 hH.hF hK hT
  have h6 : Nat.card ↥(StSL 2 F) = 6 := by
    rw [R3c.card_statedSL_two_pow (n := 1) (by rw [hF]; norm_num)]
    norm_num
  have hsolv : Group.IsSolvable ↥(StSL 2 F) := by
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    rw [h6]
    have h23 : Nat.primeFactors 6 = {2, 3} := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
      rfl
    rw [h23]
    decide
  have : Group.IsSolvable ↥(S.plus K) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact not_qs_of_le_solvable le_rfl this hq

end Setting

theorem lemma13618_of_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h56 : AsB56)
    (h4 : Lemma13618Four_F4) : Lemma13618_F4 := by
  intro G _ _ T L V S hH K hK hT n F _ _ hF ⟨e⟩
  have hn := two_le_of_field hF
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      exact S.false_of_sl2_two_F4 h1222 h517 hH hK hT (by rw [hF]; norm_num) e
    · have hn2 : n = 2 := by omega
      subst hn2
      exact h4 G T L V S hH K hK hT F (by rw [hF]; norm_num) ⟨e⟩
  · exact S.false_of_sl2_ge_eight_F4 h1222 h517 h56 hH hK hT h3 hF e

end CFSG.Quasithin.H13.A5
