module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111WeakCore
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFixedPoints
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace RankOne

theorem card_sup_of_le_normalizer_of_inf_eq_bot {N T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (N : Set G)) (hNT : N ⊓ T = ⊥) :
    Nat.card ↥(N ⊔ T) = Nat.card N * Nat.card T := by
  let f : N × T → ↥(N ⊔ T) := fun q =>
    ⟨q.1 * q.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨n, t⟩ ⟨n', t'⟩ heq
      have e : (n : G) * t = n' * t' := congrArg Subtype.val heq
      have h1 : (n' : G)⁻¹ * n = t' * (t : G)⁻¹ := by
        calc (n' : G)⁻¹ * n = (n' : G)⁻¹ * (n * t) * (t : G)⁻¹ := by group
          _ = (n' : G)⁻¹ * (n' * t') * (t : G)⁻¹ := by rw [e]
          _ = t' * (t : G)⁻¹ := by group
      have hmem : (n' : G)⁻¹ * n ∈ N ⊓ T :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ n'.2) n.2,
          h1 ▸ Subgroup.mul_mem _ t'.2 (Subgroup.inv_mem _ t.2)⟩
      rw [hNT, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have hn : n = n' := Subtype.ext hmem.symm
      subst hn
      have ht : t = t' := Subtype.ext (mul_left_cancel e)
      rw [ht]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ ((N ⊔ T : Subgroup G) : Set G) := hx
      rw [Subgroup.coe_mul_of_right_le_normalizer_left N T hT] at hx'
      obtain ⟨n, hn, t, ht, rfl⟩ := hx'
      exact ⟨(⟨n, hn⟩, ⟨t, ht⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem elemAbelian_pair {p : ℕ} (hp : p.Prime) {u v : G} (hu : orderOf u = p)
    (hv : orderOf v = p) (hvu : v ∉ Subgroup.zpowers u) (hc : u * v = v * u) :
    IsElemAbelian p (Subgroup.zpowers u ⊔ Subgroup.zpowers v) ∧
      Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set S := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hS
  have h1 : S ≤ Subgroup.centralizer ({u, v} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_) <;>
      rw [Subgroup.mem_centralizer_iff] <;> rintro w (rfl | rfl)
    · rfl
    · exact hc.symm
    · exact hc
    · rfl
  have h2 : S ≤ Subgroup.centralizer (S : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_) <;>
      rw [Subgroup.mem_centralizer_iff] <;> intro w hw
    · exact ((Subgroup.mem_centralizer_iff.mp (h1 hw)) u (by simp)).symm
    · exact ((Subgroup.mem_centralizer_iff.mp (h1 hw)) v (by simp)).symm
  have hcomm : ∀ x ∈ S, ∀ w ∈ S, x * w = w * x := fun x hx w hw =>
    (Subgroup.mem_centralizer_iff.mp (h2 hw)) x hx
  let T : Subgroup G :=
    { carrier := {x | x ∈ S ∧ x ^ p = 1}
      mul_mem' := fun {x w} hx hw => ⟨Subgroup.mul_mem _ hx.1 hw.1, by
        rw [(Commute.mul_pow (hcomm x hx.1 w hw.1) p), hx.2, hw.2, one_mul]⟩
      one_mem' := ⟨Subgroup.one_mem _, one_pow p⟩
      inv_mem' := fun {x} hx => ⟨Subgroup.inv_mem _ hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hST : S ≤ T := sup_le
    (Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers u),
      by rw [← hu, pow_orderOf_eq_one]⟩)
    (Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers v),
      by rw [← hv, pow_orderOf_eq_one]⟩)
  refine ⟨⟨⟨⟨fun x w => Subtype.ext (hcomm x x.2 w w.2)⟩⟩, fun x hx => (hST hx).2⟩, ?_⟩
  have hcv : ∀ k : ℤ, u ^ k * v = v * u ^ k := fun k => (Commute.zpow_left hc k).eq
  have hnorm : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [← hcv k, mul_inv_cancel_right]
      exact hg
    · intro hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have : g = u ^ k := by
        have e : g = v⁻¹ * (v * g * v⁻¹) * v := by group
        rw [e, ← hk, mul_assoc, hcv k, inv_mul_cancel_left]
      rw [this]
      exact Subgroup.zpow_mem_zpowers u k
  have hinf : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    rw [Subgroup.mem_bot] at hx1
    have hxp : ∃ k : ℕ, x ^ (p ^ k) = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx.2
      exact ⟨1, by rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        ← hv, pow_orderOf_eq_one, one_zpow]⟩
    have := mem_zpowers_of_isCyclic_of_orderOf_eq (A := Subgroup.zpowers v)
      (Subgroup.mem_zpowers v) hx.2 hv hx1 hxp
    exact hvu ((Subgroup.zpowers_le.mpr hx.1) this)
  rw [card_sup_of_le_normalizer_of_inf_eq_bot hnorm hinf, Nat.card_zpowers, Nat.card_zpowers, hu,
    hv, sq]

theorem conj_pow_facts {p : ℕ} [hp : Fact p.Prime] {a y : G} (hy : orderOf y = p ^ 2)
    (ha : a ^ p = 1) (hconj : a * y * a⁻¹ ∈ Subgroup.zpowers y) :
    a * y * a⁻¹ * y⁻¹ ∈ Subgroup.zpowers (y ^ p) ∧ a * y ^ p * a⁻¹ = y ^ p := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj
  have hpow : ∀ n : ℕ, a ^ n * y * (a ^ n)⁻¹ = y ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a ^ (n + 1) * y * (a ^ (n + 1))⁻¹ = a * (a ^ n * y * (a ^ n)⁻¹) * a⁻¹ := by group
        _ = a * y ^ (k ^ n) * a⁻¹ := by rw [ih]
        _ = (a * y * a⁻¹) ^ (k ^ n) := (conj_zpow).symm
        _ = (y ^ k) ^ (k ^ n) := by rw [hk]
        _ = y ^ (k ^ (n + 1)) := by rw [← zpow_mul, pow_succ, mul_comm]
  have h1 : y ^ (k ^ p - 1) = 1 := by
    have := hpow p
    rw [ha, one_mul, inv_one, mul_one] at this
    rw [zpow_sub, ← this, zpow_one, mul_inv_cancel]
  have h2 : ((p : ℤ) ^ 2) ∣ k ^ p - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hy, Nat.cast_pow] at this
  have h3 : (p : ℤ) ∣ k - 1 := by
    have h4 : (p : ℤ) ∣ k ^ p - 1 := (dvd_pow_self (p : ℤ) two_ne_zero).trans h2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h4 ⊢
    push_cast at h4 ⊢
    rwa [ZMod.pow_card] at h4
  obtain ⟨m, hm⟩ := h3
  have hk' : k = 1 + p * m := by omega
  have hyp2 : y ^ ((p : ℤ) ^ 2) = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    exact_mod_cast h
  constructor
  · rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, ?_⟩
    rw [← hk, ← zpow_neg_one, ← zpow_add, ← zpow_natCast, ← zpow_mul, hk']
    congr 1
    ring
  · rw [← zpow_natCast, conj_zpow.symm, ← hk, ← zpow_mul, hk']
    have e : (1 + (p : ℤ) * m) * p = p + (p : ℤ) ^ 2 * m := by ring
    rw [e, zpow_add, zpow_mul, hyp2, one_zpow, mul_one]

theorem isCyclic_of_le_of_pRank_le_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {X S : Subgroup G} (hSX : S ≤ X) (hS : IsPGroup p S) (hX : Open.pRank p X ≤ 1) :
    IsCyclic S := by
  by_contra hnc
  haveI : Fact (IsPGroup p S) := ⟨hS⟩
  obtain ⟨E, -, hEc, hEel⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hE := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mp hEel
  have h2 := CFSG.SectionRank.le_pRank hp.out.one_lt (le_top : E ≤ ⊤) hE hEc
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h2
  have := CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono p hp.out.one_lt hSX
  omega

theorem conj_mem_d1LiftX {p : ℕ} {H R : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKn : K.Normal) {g x : G} (hgR : g ∈ R)
    (hgH : g ∈ H) (hx : x ∈ d1LiftX p H R K) : g * x * g⁻¹ ∈ d1LiftX p H R K := by
  obtain ⟨x', hx', rfl⟩ := hx
  have hx'R : (x' : G) ∈ R := hx'.1
  have hx'K : QuotientGroup.mk' (primeComplementCore (G := H) p) x' ∈ K := hx'.2
  refine ⟨⟨g, hgH⟩ * x' * ⟨g, hgH⟩⁻¹, ⟨?_, ?_⟩, rfl⟩
  · show ((⟨g, hgH⟩ * x' * ⟨g, hgH⟩⁻¹ : H) : G) ∈ R
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact R.mul_mem (R.mul_mem hgR hx'R) (R.inv_mem hgR)
  · show QuotientGroup.mk' (primeComplementCore (G := H) p) (⟨g, hgH⟩ * x' * ⟨g, hgH⟩⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv]
    exact hKn.conj_mem _ hx'K _

theorem d1LiftX_le_hyp111Pre (p : ℕ) (H R : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : d1LiftX p H R K ≤ hyp111Pre p H K :=
  Subgroup.map_mono inf_le_right

end RankOne

variable {p : ℕ} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
  {W : Subgroup G} {y z : G}

theorem RankOneSylowData.y_mem (hW : RankOneSylowData p M H Q K W y z) : y ∈ W :=
  d1LiftX_le p H W K (hW.y_lift ▸ Subgroup.mem_zpowers y)

theorem RankOneSylowData.isAGLQ (hS : Setting G) {P : Sylow p G}
    (hd : AGL81CfgData p P M H Q K) (hnc : ¬ HasPrimeConstraint (G := H) p)
    (hshape : IsCaseTwoGroup p ↥K) (hKn : K.Normal) (hH3 : 3 ≤ Open.pRank p H)
    (hXM : d1PlusCore p H K ≤ M) (hW : RankOneSylowData p M H Q K W y z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal)
    (hno : ¬ AGL81ElevenFiveOne p H K L) (hJX : jZero H L ≤ d1PlusCore p H K)
    (hX1 : Open.pRank p (d1PlusCore p H K) = 1) (hpJ : p ∣ Nat.card (jZero H L))
    (hzJ : z ∈ jZero H L)
    (hz2 : ¬ ∀ x ∈ jZero H L, z * x * z⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) {a : G}
    (haW : a ∈ W) (hap : orderOf a = p) (hao : a ∉ hyp111Pre p H K ⊔ d1PlusCore p H K)
    (hAJ : ∀ b ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers a, ∀ x ∈ jZero H L,
      b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L))
    (h1033 : AGL81TenThreeThreeCfg G) (hPC : AGL81ElevenElevenParabolicComm G)
    (h1014 : AGL81TenFourteenThreeCfgGen G) (hC : AGL81ElevenElevenRankOneCent G) :
    IsAGLQ p M (Subgroup.zpowers y ⊔ Subgroup.zpowers a) := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  haveI : Fact p.Prime := ⟨hesc.prime⟩
  have hp : p.Prime := hesc.prime
  set A := Subgroup.zpowers y ⊔ Subgroup.zpowers a with hAdef
  have hyW : y ∈ W := hW.y_mem
  have hAW : A ≤ W := sup_le (Subgroup.zpowers_le.mpr hyW) (Subgroup.zpowers_le.mpr haW)
  have hAHM : A ≤ H ⊓ M := hAW.trans hW.le
  have hAp : IsPGroup p A := hW.pgroup.to_le hAW
  have hyA : y ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have haA : a ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hconj : a * y * a⁻¹ ∈ Subgroup.zpowers y := by
    rw [← hW.y_lift]
    exact RankOne.conj_mem_d1LiftX hKn haW (hW.le haW).1 (hW.y_lift ▸ Subgroup.mem_zpowers y)
  have hap1 : a ^ p = 1 := hap ▸ pow_orderOf_eq_one a
  obtain ⟨hcy, hyp⟩ := RankOne.conj_pow_facts hW.y_order hap1 hconj
  have hyp_ord : orderOf (y ^ p) = p := by
    rw [orderOf_pow_of_dvd hp.ne_zero (by rw [hW.y_order]; exact dvd_pow_self p two_ne_zero),
      hW.y_order, sq, Nat.mul_div_cancel _ hp.pos]
  have hyp_le : Subgroup.zpowers (y ^ p) ≤ Subgroup.zpowers y :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) p)
  have hypre : Subgroup.zpowers (y ^ p) ≤ hyp111Pre p H K := hyp_le.trans
    (hW.y_lift ▸ RankOne.d1LiftX_le_hyp111Pre p H W K)
  have ha_notin : a ∉ Subgroup.zpowers (y ^ p) := fun h => hao (Subgroup.mem_sup_left (hypre h))
  have hcomm : y ^ p * a = a * y ^ p := by
    calc y ^ p * a = a * y ^ p * a⁻¹ * a := by rw [hyp]
      _ = a * y ^ p := by group
  set E := Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers a with hEdef
  obtain ⟨hE, hEc⟩ := RankOne.elemAbelian_pair hp hyp_ord hap ha_notin hcomm
  have hEA : E ≤ A := sup_le (hyp_le.trans le_sup_left) le_sup_right
  have hEW : E ≤ W := hEA.trans hAW
  have hzc : ∀ e ∈ E, z * e = e * z := fun e he => (hW.z_central e (hEW he)).symm
  have hzX : z ∈ d1PlusCore p H K := hW.z_mem.2
  have hz1 : z ≠ 1 := by
    intro h
    have hzo := hW.z_order
    rw [h, orderOf_one] at hzo
    exact hp.one_lt.ne hzo
  have hypE : y ^ p ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hzE : z ∉ E := by
    intro hzE
    by_cases hzy : z ∈ Subgroup.zpowers (y ^ p)
    · have : z ∈ Subgroup.zpowers y ⊓ d1PlusCore p H K := ⟨hyp_le hzy, hzX⟩
      rw [hW.y_X, Subgroup.mem_bot] at this
      exact hz1 this
    · have hcz : y ^ p * z = z * y ^ p := hW.z_central _ (hEW hypE)
      obtain ⟨-, hc2⟩ := RankOne.elemAbelian_pair hp hyp_ord hW.z_order hzy hcz
      have hle : Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers z ≤ E :=
        sup_le le_sup_left (Subgroup.zpowers_le.mpr hzE)
      have heq : Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers z = E :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hEc, hc2])
      have haE : a ∈ Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers z :=
        heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
      exact hao ((sup_le_sup hypre (Subgroup.zpowers_le.mpr hzX)) haE)
  have hML : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hypp : ∃ k : ℕ, (a * y * a⁻¹ * y⁻¹) ^ (p ^ k) = 1 := ⟨1, by
    rw [pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_mem_zpowers hcy).trans (by rw [hyp_ord]))⟩
  have hstep1 : ⁅Subgroup.zpowers (y ^ p), L⁆ ≤ pCoreOf 2 L := by
    rcases h1033 hS p P M H Q K hd L hL hLn A hAHM hAp hAJ with hc | hpar
    · rw [Subgroup.commutator_le]
      intro b hb l hl
      have hbA : b ∈ A := (hyp_le.trans le_sup_left) hb
      have hbl : b * l * b⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hML (hAHM hbA).2) l).mp hl
      rw [commutatorElement_def]
      exact Hyp111.inf_pCoreOf_le hL.le ⟨L.mul_mem hbl (L.inv_mem hl), hc b hbA l hl⟩
    · refine (Subgroup.commutator_mono ?_ le_rfl).trans
        (hPC hS p P M H Q K hd L hL hLn A hAHM hAp hAJ hpar)
      rw [Subgroup.zpowers_le]
      have hne : a * y * a⁻¹ * y⁻¹ ≠ 1 := by
        intro h1
        apply hW.noncomm a haW hao
        calc a * y = a * y * a⁻¹ * y⁻¹ * y * a := by group
          _ = y * a := by rw [h1, one_mul]
      have hmem := mem_zpowers_of_isCyclic_of_orderOf_eq (A := Subgroup.zpowers (y ^ p))
        (Subgroup.mem_zpowers _) hcy hyp_ord hne hypp
      have hcA : a * y * a⁻¹ * y⁻¹ ∈ ⁅A, A⁆ := by
        have := Subgroup.commutator_mem_commutator haA hyA
        rwa [commutatorElement_def] at this
      exact (Subgroup.zpowers_le.mpr hcA) hmem
  have hpL : p ∣ Nat.card L :=
    hpJ.trans (Subgroup.card_dvd_of_le ((jZero_le H L).trans inf_le_right))
  have hypM : y ^ p ∈ M := (hAHM (hEA hypE)).2
  have hzp : z ^ p = 1 := hW.z_order ▸ pow_orderOf_eq_one z
  have hstep2 : Subgroup.centralizer ({y ^ p} : Set G) ≤ M := by
    by_contra hnot
    obtain ⟨hE3, hE3c⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers hp hEc hE.2 hzp hzE
      (fun e he => (hzc e he).symm)
    have hEC : E ≤ Subgroup.centralizer ({y ^ p} : Set G) := fun e he => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨y ^ p, hypE⟩)
    have hzC : z ∈ Subgroup.centralizer ({y ^ p} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hW.z_central _ (hEW hypE)).symm
    have hU : ∃ U : Subgroup G, U ≤ Subgroup.centralizer ({y ^ p} : Set G) ∧ IsAGLQ p M U :=
      ⟨E ⊔ Subgroup.zpowers z, sup_le hEC (Subgroup.zpowers_le.mpr hzC),
        sup_le (hEW.trans (hW.le.trans inf_le_right))
          (Subgroup.zpowers_le.mpr (hW.le hW.z_mem.1).2),
        hW.pgroup.to_le (sup_le hEW (Subgroup.zpowers_le.mpr hW.z_mem.1)),
        Or.inl (by
          rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
          exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE3 hE3c)⟩
    exact h1014 hS p P M H Q K hd L hL hpL (y ^ p) hypM hyp_ord hnot hU hstep1
  have hcent : ∀ b ∈ E, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ M := by
    intro b hb hb1
    by_cases hbZ : b ∈ Subgroup.zpowers (y ^ p)
    · refine le_trans (fun g hg => ?_) hstep2
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      have hbp : ∃ k : ℕ, b ^ (p ^ k) = 1 := ⟨1, by
        rw [pow_one]
        exact orderOf_dvd_iff_pow_eq_one.mp
          ((orderOf_dvd_of_mem_zpowers hbZ).trans (by rw [hyp_ord]))⟩
      have hyb := mem_zpowers_of_isCyclic_of_orderOf_eq (A := Subgroup.zpowers (y ^ p))
        (Subgroup.mem_zpowers _) hbZ hyp_ord hb1 hbp
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyb
      rw [← hk]
      exact (Commute.zpow_right (hg : Commute g b) k).eq
    · exact hC hS p P M H Q K hd hnc hshape hH3 hXM hKn L hL hLn hno hJX hX1 hpJ W y a z
        hW.pgroup hW.le hW.max hW.z_mem hW.z_order hW.z_central hzJ hz2 hW.y_lift hW.y_order
        hW.noncomm haW hap hao hAJ hstep1 hstep2 b hb hbZ
  exact isAGLQ_of_centralizers hesc.weakCore_le (hAHM.trans inf_le_right) hAp hEA hE hEc
    hW.z_order hzE hzc hcent

end CFSG.LocalAnalysis.RankThreeTheoremC
