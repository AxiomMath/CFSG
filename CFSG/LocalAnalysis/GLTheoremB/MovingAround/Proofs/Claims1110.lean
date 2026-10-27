module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1110
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed4

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut IsFiTwentyTwo Fi22Facts)

section Basic

variable {G : Type} [Group G]

theorem isPGroup_of_elemAb {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) : IsPGroup p E :=
  fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩

theorem le_centralizer_of_le {p : ℕ} {E H K : Subgroup G} (hE : IsElemAbelian p E) (hH : H ≤ E)
    (hK : K ≤ E) : H ≤ Subgroup.centralizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact elemAbelian_comm hE (hK hy) (hH hx)

theorem card_conj (g : G) (H : Subgroup G) : Nat.card (GLBConj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem isPGroup_conj {p : ℕ} (g : G) {H : Subgroup G} (hH : IsPGroup p H) :
    IsPGroup p (GLBConj g H) :=
  hH.map (MulAut.conj g⁻¹).toMonoidHom

theorem isElemAbelian_conj {p : ℕ} (g : G) {H : Subgroup G} (hH : IsElemAbelian p H) :
    IsElemAbelian p (GLBConj g H) :=
  CFSG.SectionRank.isElemAbelian_map hH _

theorem comm_of_mem_centerOf {R : Subgroup G} {z : G} (hz : z ∈ centerOf R) {r : G} (hr : r ∈ R) :
    r * z = z * r := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨r, hr⟩)

theorem centerOf_le' (R : Subgroup G) : centerOf R ≤ R := Subgroup.map_subtype_le _

theorem omegaOne_le' (p : ℕ) (H : Subgroup G) : omegaOne p H ≤ H :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem le_centralizer_omegaOne_centerOf (p : ℕ) (R : Subgroup G) :
    R ≤ Subgroup.centralizer ((omegaOne p (centerOf R) : Subgroup G) : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (comm_of_mem_centerOf (omegaOne_le' p _ hz) hr).symm

theorem normal_subgroupOf_of_central {Z R : Subgroup G}
    (hZc : R ≤ Subgroup.centralizer (Z : Set G)) : (Z.subgroupOf R).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 : (n : G) * g = g * n := Subgroup.mem_centralizer_iff.1 (hZc g.2) n hn
  have h2 : ((g * n * g⁻¹ : ↥R) : G) = n := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← h1]
    group
  rw [h2]
  exact hn

theorem orderOf_eq_of_pow {p : ℕ} [Fact p.Prime] {x : G} (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    orderOf x = p :=
  orderOf_eq_prime hx hx1

end Basic

section Conn

variable {G : Type} [Group G]

theorem isKConnStep_symm {p k : ℕ} {X U V : Subgroup G} (h : IsKConnStep p k X U V) :
    IsKConnStep p k X V U :=
  ⟨h.2.1, h.1, Subgroup.le_centralizer_iff.1 h.2.2⟩

theorem isEkIn_top {p k : ℕ} {X U : Subgroup G} (h : IsEkIn p k X U) : IsEkIn p k ⊤ U :=
  ⟨le_top, h.2⟩

theorem rtg_top {p k : ℕ} {X U V : Subgroup G}
    (h : Relation.ReflTransGen (IsKConnStep p k X) U V) :
    Relation.ReflTransGen (IsKConnStep p k ⊤) U V :=
  Relation.ReflTransGen.mono (fun _ _ hs => ⟨isEkIn_top hs.1, isEkIn_top hs.2.1, hs.2.2⟩) U V h

theorem rtg_symm {p k : ℕ} {X U V : Subgroup G}
    (h : Relation.ReflTransGen (IsKConnStep p k X) U V) :
    Relation.ReflTransGen (IsKConnStep p k X) V U := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (isKConnStep_symm hbc)).trans ih

variable [Finite G]

theorem exists_isEkIn_le {p k : ℕ} [Fact p.Prime] {X E : Subgroup G} (hEX : E ≤ X)
    (hE : IsElemAbelian p E) (hk : p ^ k ≤ Nat.card E) :
    ∃ E₀ : Subgroup G, IsEkIn p k X E₀ ∧ E₀ ≤ E := by
  obtain ⟨r, hr⟩ := exists_card_eq_pow (isPGroup_of_elemAb hE)
  have hkr : k ≤ r := by
    rw [hr] at hk
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hk
  obtain ⟨E₀, hE₀E, hE₀, hE₀c⟩ :=
    exists_le_isElemAbelian_card hE (n := k) (by rw [hr]; exact pow_dvd_pow p hkr)
  exact ⟨E₀, ⟨hE₀E.trans hEX, hE₀, hE₀c⟩, hE₀E⟩

theorem chain_of_conn {p k : ℕ} [Fact p.Prime] {X F W : Subgroup G} (h : IsKConnectedIn p k X F W) :
    ∃ U V : Subgroup G, IsEkIn p k X U ∧ IsEkIn p k X V ∧ F ≤ Subgroup.centralizer (U : Set G) ∧
      Relation.ReflTransGen (IsKConnStep p k X) U V ∧ V ≤ Subgroup.centralizer (W : Set G) := by
  obtain ⟨-, -, -, hWX, hW, hWc, hc⟩ := h
  rcases hc with hc | hc
  · obtain ⟨W₀, hW₀, hW₀W⟩ := exists_isEkIn_le hWX hW hWc
    exact ⟨W₀, W₀, hW₀, hW₀, hc.trans (Subgroup.centralizer_le hW₀W), Relation.ReflTransGen.refl,
      le_centralizer_of_le hW hW₀W le_rfl⟩
  · exact hc

theorem conn_top {p k : ℕ} [Fact p.Prime] {R F F₁ W Es B₁ : Subgroup G}
    (h1 : IsKConnectedIn p k R F W) (h2 : IsKConnectedIn p k R F₁ W)
    (hEs : IsElemAbelian p Es) (hFEs : F ≤ Es) (hB₁ : IsElemAbelian p B₁) (hF₁B₁ : F₁ ≤ B₁) :
    IsKConnectedIn p k ⊤ Es B₁ := by
  obtain ⟨U₁, V₁, hU₁, hV₁, hFU₁, h1c, hV₁W⟩ := chain_of_conn h1
  obtain ⟨U₂, V₂, hU₂, hV₂, hF₁U₂, h2c, hV₂W⟩ := chain_of_conn h2
  obtain ⟨hFR, hF, hFc, hWR, hW, hWc, -⟩ := h1
  obtain ⟨hF₁R, hF₁, hF₁c, -, -, -, -⟩ := h2
  obtain ⟨F₀, hF₀, hF₀F⟩ := exists_isEkIn_le hFR hF hFc
  obtain ⟨F₁₀, hF₁₀, hF₁₀F₁⟩ := exists_isEkIn_le hF₁R hF₁ hF₁c
  obtain ⟨W₀, hW₀, hW₀W⟩ := exists_isEkIn_le hWR hW hWc
  have s1 : IsKConnStep p k R F₀ U₁ := ⟨hF₀, hU₁, hF₀F.trans hFU₁⟩
  have s2 : IsKConnStep p k R V₁ W₀ := ⟨hV₁, hW₀, hV₁W.trans (Subgroup.centralizer_le hW₀W)⟩
  have s3 : IsKConnStep p k R W₀ V₂ := ⟨hW₀, hV₂, hW₀W.trans (Subgroup.le_centralizer_iff.1 hV₂W)⟩
  have s4 : IsKConnStep p k R U₂ F₁₀ :=
    ⟨hU₂, hF₁₀, (Subgroup.le_centralizer_iff.1 hF₁U₂).trans (Subgroup.centralizer_le hF₁₀F₁)⟩
  have hchain : Relation.ReflTransGen (IsKConnStep p k R) F₀ F₁₀ :=
    (Relation.ReflTransGen.single s1).trans (h1c.trans ((Relation.ReflTransGen.single s2).trans
      ((Relation.ReflTransGen.single s3).trans ((rtg_symm h2c).trans
        (Relation.ReflTransGen.single s4)))))
  refine ⟨le_top, hEs, hFc.trans (Subgroup.card_le_of_le hFEs), le_top, hB₁,
    hF₁c.trans (Subgroup.card_le_of_le hF₁B₁),
    Or.inr ⟨F₀, F₁₀, isEkIn_top hF₀, isEkIn_top hF₁₀, ?_, rtg_top hchain, ?_⟩⟩
  · exact le_centralizer_of_le hEs le_rfl (hF₀F.trans hFEs)
  · exact le_centralizer_of_le hB₁ (hF₁₀F₁.trans hF₁B₁) le_rfl

end Conn

section Step3

variable {G : Type} [Group G] [Finite G]

theorem exists_isSCp_top_above' {p : ℕ} {Y : Subgroup G} (hY : IsElemAbelian p Y) :
    ∃ H : Subgroup G, IsSCp p ⊤ H ∧ Y ≤ H := by
  obtain ⟨H, hYH, hHmax⟩ :=
    (Set.toFinite {X : Subgroup G | IsElemAbelian p X}).exists_le_maximal
      (show Y ∈ {X : Subgroup G | IsElemAbelian p X} from hY)
  exact ⟨H, ⟨le_top, hHmax.1, fun E _ hE hHE => le_antisymm (hHmax.2 hE hHE) hHE⟩, hYH⟩

theorem e4_subset_D0 (h31 : Input31_7_3) {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 5 B M E A a K) (hrk : CFSG.Open.pRank 5 (E ⊓ A) = 2)
    {R : Subgroup G} (hR : IsSylowIn 5 M R)
    (hZ : omegaOne 5 (centerOf R) = E ⊓ A) {U : Subgroup G} (hU : IsEkIn 5 2 R U)
    (hUn : (U.subgroupOf R).Normal) (hUZ : U ≠ omegaOne 5 (centerOf R)) :
    ∀ F : Subgroup G, IsEkIn 5 4 R F → inD0 5 M F := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hEsc := (lemma104_ii_holds hS h.pair).1
  have hA0el : IsElemAbelian 5 (E ⊓ A) := l1110_isElemAbelian_of_le hEsc.2.1 inf_le_left
  have hZel : IsElemAbelian 5 (omegaOne 5 (centerOf R)) := by rw [hZ]; exact hA0el
  have hZcard : Nat.card (omegaOne 5 (centerOf R)) = 5 ^ 2 := by
    rw [hZ, l1110_card_eq_pow_pRank hA0el, hrk]
  have hZR : omegaOne 5 (centerOf R) ≤ R := (omegaOne_le' 5 _).trans (centerOf_le' R)
  have hZek : IsEkIn 5 2 R (omegaOne 5 (centerOf R)) := ⟨hZR, hZel, hZcard⟩
  have hZn : ((omegaOne 5 (centerOf R)).subgroupOf R).Normal :=
    normal_subgroupOf_of_central (le_centralizer_omegaOne_centerOf 5 R)
  have hUc : U ≤ Subgroup.centralizer ((omegaOne 5 (centerOf R) : Subgroup G) : Set G) :=
    hU.1.trans (le_centralizer_omegaOne_centerOf 5 R)
  have hconn := h31 G 5 (by norm_num) R hR.2.1 U _ hU hZek hUn hZn hUZ hUc
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS.standing hS.bOne hS.pre
  have hBel : IsElemAbelian 5 B := hS.bOne.1.1
  obtain ⟨y, hyM, T, hTp, hTM, hRT, hBT⟩ :=
    exists_conj_le_pGroup' hR.1 hR.2.1 hBM (isPGroup_of_elemAb hBel)
  have hTR : T = R := hR.2.2 T hTM hTp hRT
  rw [hTR] at hBT
  have hB₁D : inD 5 M (GLBConj y B) :=
    (lemma101_i_holds hS hyM (lemma101_ii_holds hS) h.pair.1.2.1).1
  have hB₁el : IsElemAbelian 5 (GLBConj y B) := isElemAbelian_conj y hBel
  have hB₁card : Nat.card (GLBConj y B) = 5 ^ m := by
    rw [card_conj, hS.standing.card_eq hS.bOne]
  have hm4 : 4 ≤ m := hS.standing.four_le
  obtain ⟨F₁, hF₁, hF₁B₁⟩ := exists_isEkIn_le hBT hB₁el (k := 4)
    (by rw [hB₁card]; exact Nat.pow_le_pow_right (by norm_num) hm4)
  intro F hF
  obtain ⟨Es, hEs, hFEs⟩ := exists_isSCp_top_above' hF.2.1
  have hc := conn_top (hconn F hF) (hconn F₁ hF₁) hEs.2.1 hFEs hB₁el hF₁B₁
  have hk : CFSG.Open.pRank 5 (E ⊓ A) + 1 = 3 := by rw [hrk]
  rw [← hk] at hc
  have hEsD : inD 5 M Es := lemma104_iii_holds hS h.pair hEs hB₁D hc
  exact ⟨hF.1.trans hR.1, hF.2.1, Es, hEsD, hFEs⟩

theorem a_not_mem_E {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m p B M E A a K) : a ∉ E := fun haE => h.notD ⟨E, h.pair.1.1, haE⟩

theorem orderOf_a {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 5 B M E A a K) : orderOf a = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hAel := (lemma104_ii_holds h.toCex117Base.toSec11.toSec10Fails h.pair).2.2.1
  exact orderOf_eq_of_pow (hAel.2 a h.ha.1) h.ha.2

theorem card_A {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 5 B M E A a K) {R : Subgroup G} (hEAR : E ⊔ A ≤ R)
    (hD0 : ∀ F : Subgroup G, IsEkIn 5 4 R F → inD0 5 M F) : Nat.card A = 5 ^ 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hAel := (lemma104_ii_holds hS h.pair).2.2.1
  have hA3 : 3 ≤ CFSG.Open.pRank 5 A := h.pair.1.2.1.1.2
  have hAcard := l1110_card_eq_pow_pRank hAel
  have hA4 : CFSG.Open.pRank 5 A < 4 := by
    by_contra hge'
    have hge : 4 ≤ CFSG.Open.pRank 5 A := not_lt.1 hge'
    have hdvd : 5 ^ 4 ∣ Nat.card A := by rw [hAcard]; exact pow_dvd_pow 5 hge
    have hzA : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).2 h.ha.1
    have hHc : Nat.card ((Subgroup.zpowers a).subgroupOf A) = 5 ^ 1 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzA).toEquiv, Nat.card_zpowers,
        orderOf_a h, pow_one]
    obtain ⟨F', hF'c, hHF'⟩ :=
      Sylow.exists_subgroup_card_pow_prime_le 5 hdvd _ hHc (by norm_num : 1 ≤ 4)
    have hFA : F'.map A.subtype ≤ A := Subgroup.map_subtype_le F'
    have haF : a ∈ F'.map A.subtype :=
      ⟨⟨a, h.ha.1⟩, hHF' (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers a)), rfl⟩
    have hFek : IsEkIn 5 4 R (F'.map A.subtype) :=
      ⟨hFA.trans (le_sup_right.trans hEAR), l1110_isElemAbelian_of_le hAel hFA,
        by rw [Subgroup.card_map_of_injective A.subtype_injective, hF'c]⟩
    obtain ⟨-, -, A1, hA1, hFA1⟩ := hD0 _ hFek
    exact h.notD ⟨A1, hA1, hFA1 haF⟩
  rw [hAcard]
  congr 1
  omega

theorem A_eq_sup {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 5 B M E A a K) (hrk : CFSG.Open.pRank 5 (E ⊓ A) = 2)
    (hA : Nat.card A = 5 ^ 3) : A = (E ⊓ A) ⊔ Subgroup.zpowers a := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  have hAel := hsc.2.2.1
  have hA0el : IsElemAbelian 5 (E ⊓ A) := l1110_isElemAbelian_of_le hsc.1.2.1 inf_le_left
  have hzA : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).2 h.ha.1
  have hle : (E ⊓ A) ⊔ Subgroup.zpowers a ≤ A := sup_le inf_le_right hzA
  have hcomm : ∀ x ∈ E ⊓ A, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := fun x hx y hy =>
    elemAbelian_comm hAel (Subgroup.mem_inf.1 hx).2 (hzA hy)
  have hbot : (E ⊓ A) ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxo : orderOf x = 5 :=
      orderOf_eq_of_pow (hAel.2 x (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2) hx1
    have hzz : Subgroup.zpowers x = Subgroup.zpowers a := by
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 (Subgroup.mem_inf.1 hx).2) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hxo, orderOf_a h]
    have haE : a ∈ E := by
      have : a ∈ Subgroup.zpowers x := hzz ▸ Subgroup.mem_zpowers a
      exact (Subgroup.mem_inf.1 (((Subgroup.zpowers_le).2 (Subgroup.mem_inf.1 hx).1) this)).1
    exact a_not_mem_E h haE
  have hcard : Nat.card ↥((E ⊓ A) ⊔ Subgroup.zpowers a) = 5 ^ 3 := by
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_eq_mul_of_commute hcomm hbot,
      l1110_card_eq_pow_pRank hA0el, hrk, Nat.card_zpowers, orderOf_a h]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hA, hcard])).symm

end Step3

section Bar

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut_mk coprime_card_gLAPPrimeCore_aux)

theorem eq_one_of_dvd_coprime {H : Type*} [Group H] {x : H} {m n : ℕ} (hmn : Nat.Coprime m n)
    (h1 : orderOf x ∣ m) (h2 : orderOf x ∣ n) : x = 1 := by
  have h : Nat.Coprime (orderOf x) (orderOf x) :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.coprime_dvd_right h2 hmn)
  exact orderOf_eq_one_iff.1 (Nat.coprime_self _ |>.1 h)

theorem fi22_facts (hF : Fi22Facts) {K : Subgroup G} (hK : IsFiTwentyTwo (barOf 5 K)) :
    Subgroup.center (barOf 5 K) = ⊥ ∧
      (∀ Q : Sylow 5 (barOf 5 K), IsElemAbelian 5 (Q : Subgroup (barOf 5 K))) ∧
      (∀ φ : MulAut (barOf 5 K), IsPGroup 5 (Subgroup.zpowers φ) → ∃ k, φ = MulAut.conj k) ∧
      (Nat.card (barOf 5 K)).factorization 5 = 2 ∧ (Nat.card K).factorization 5 = 2 := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨hZ, hv, hord, hInn⟩ := hF (barOf 5 K) hK
  have hSyl : ∀ Q : Sylow 5 (barOf 5 K), IsElemAbelian 5 (Q : Subgroup (barOf 5 K)) := by
    intro Q
    have hcard : Nat.card (Q : Subgroup (barOf 5 K)) = 5 ^ 2 := by
      rw [Sylow.card_eq_multiplicity, hv]
    refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard, fun x hx => ?_⟩
    have hdvd : orderOf (x : barOf 5 K) ∣ 5 ^ 2 := by
      rw [← hcard]
      have h := orderOf_dvd_natCard (⟨x, hx⟩ : (Q : Subgroup (barOf 5 K)))
      rwa [← Subgroup.orderOf_coe] at h
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hk2 : k ≠ 2 := fun h => hord x (by rw [hk', h]; norm_num)
    have hk1 : k ≤ 1 := by omega
    exact orderOf_dvd_iff_pow_eq_one.1 (hk' ▸ (pow_dvd_pow 5 hk1))
  have hKcard : Nat.card K = Nat.card (barOf 5 K) * Nat.card (GLAPPrimeCore 5 ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 5 ↥K)
  have hfac : (Nat.card K).factorization 5 = 2 := by
    rw [hKcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hv,
      Nat.factorization_eq_zero_of_not_dvd
        ((hp.coprime_iff_not_dvd).1 (coprime_card_gLAPPrimeCore_aux 5 ↥K))]
  exact ⟨hZ, hSyl, hInn, hv, hfac⟩

theorem barAut_of_mem {p : ℕ} {K : Subgroup G} {k : G} (hk : k ∈ K) :
    barAut p K ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : K) : barOf p K) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [barAut_mk, MulAut.conj_apply]
    rfl

theorem barAut_eq_one_of_comm {p : ℕ} {K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) (hc : ∀ y ∈ K, c * y = y * c) :
    barAut p K ⟨c, hcN⟩ = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [barAut_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show c * (y : G) * c⁻¹ = y
    rw [hc y y.2]
    group

theorem eq_one_of_mem_of_trivial {K : Subgroup G} (hZ : Subgroup.center (barOf 5 K) = ⊥) {x : G}
    (hx : x ∈ K) (hx5 : x ^ 5 = 1) (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (htriv : barAut 5 K ⟨x, hxN⟩ = 1) : x = 1 := by
  have htriv' : barAut 5 K ⟨x, Subgroup.le_normalizer hx⟩ = 1 := htriv
  rw [barAut_of_mem hx] at htriv'
  have hc : (QuotientGroup.mk (⟨x, hx⟩ : K) : barOf 5 K) ∈ Subgroup.center (barOf 5 K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun φ : MulAut (barOf 5 K) => φ z) htriv'
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  have hxp : (⟨x, hx⟩ : K) ^ 5 = 1 := Subtype.ext (by simpa using hx5)
  have h1 : (⟨x, hx⟩ : K) = 1 :=
    eq_one_of_dvd_coprime (coprime_card_gLAPPrimeCore_aux 5 ↥K) (orderOf_dvd_of_pow_eq_one hxp)
      (Subgroup.orderOf_dvd_natCard _ hc)
  exact congrArg Subtype.val h1

theorem mem_normalizer_of_le_cg {c : G} {K : Subgroup G} (hK : K ≤ Cg c) :
    c ∈ Subgroup.normalizer (K : Set G) := by
  have hcomm : ∀ y ∈ K, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hK hy)).symm
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hcomm y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := hcomm _ hy
    have h2 : c * y * c⁻¹ = y := by
      have h1' : c * (c * y * c⁻¹) = c * y := by rw [h1]; group
      exact mul_left_cancel h1'
    rw [h2] at hy
    exact hy

theorem mem_centBar_iff' {p : ℕ} {X L : Subgroup G} {v : G} :
    v ∈ centBar p X L ↔ v ∈ X ∧ ∃ hv : v ∈ Subgroup.normalizer (L : Set G), barAut p L ⟨v, hv⟩ = 1 := by
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hX⟩
    exact ⟨hX, w.2, hw⟩
  · rintro ⟨hX, hv, h1⟩
    exact ⟨⟨⟨v, hv⟩, h1, rfl⟩, hX⟩

theorem card_le_of_pGroup_le {p : ℕ} [Fact p.Prime] {X S : Subgroup G} (hSX : S ≤ X)
    (hS : IsPGroup p S) : Nat.card S ≤ p ^ (Nat.card X).factorization p := by
  obtain ⟨r, hr⟩ := exists_card_eq_pow hS
  have hdvd : p ^ r ∣ Nat.card X := hr ▸ Subgroup.card_dvd_of_le hSX
  have hle : r ≤ (Nat.card X).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').1 hdvd
  rw [hr]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hle

theorem exists_conj_eq_of_card {p : ℕ} [Fact p.Prime] {X P Q : Subgroup G} (hPX : P ≤ X)
    (hQX : Q ≤ X) (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (hPc : Nat.card P = p ^ (Nat.card X).factorization p)
    (hQc : Nat.card Q = p ^ (Nat.card X).factorization p) : ∃ x ∈ X, GLBConj x Q = P := by
  obtain ⟨x, hxX, S, hSp, hSX, hPS, hQS⟩ := exists_conj_le_pGroup' hPX hP hQX hQ
  have hSP : P = S :=
    Subgroup.eq_of_le_of_card_ge hPS (by rw [hPc]; exact card_le_of_pGroup_le hSX hSp)
  rw [← hSP] at hQS
  exact ⟨x, hxX, Subgroup.eq_of_le_of_card_ge hQS (by rw [hPc, card_conj, hQc])⟩

end Bar

section Eps

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut_mk coprime_card_gLAPPrimeCore_aux)

theorem zpowers_eq_of_mem {p : ℕ} [Fact p.Prime] {x a : G} (hx : x ∈ Subgroup.zpowers a)
    (hxp : x ^ p = 1) (hx1 : x ≠ 1) (ha : orderOf a = p) :
    Subgroup.zpowers x = Subgroup.zpowers a :=
  Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hx)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_of_pow hxp hx1, ha])

theorem A_inf_K (hF : Fi22Facts) {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 5 B M E A a K) (hK : IsFiTwentyTwo (barOf 5 K))
    (hA0N : E ⊓ A ≤ Subgroup.normalizer (K : Set G)) (hAeq : A = (E ⊓ A) ⊔ Subgroup.zpowers a)
    (hAc : Nat.card A = 5 ^ 3) :
    A ≤ Subgroup.normalizer (K : Set G) ∧ Nat.card ↥(A ⊓ K) = 5 ^ 2 ∧ IsElemAbelian 5 (A ⊓ K) ∧
      a ∉ K ∧ A = (A ⊓ K) ⊔ Subgroup.zpowers a := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hAsc := (lemma104_ii_holds hS h.pair).2
  have hAel := hAsc.2.1
  obtain ⟨hZ, hSyl, hInn, -, hfac⟩ := fi22_facts hF hK
  have hKa : K ≤ Cg a := h.hK.1
  have haN : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_le_cg hKa
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := by
    rw [hAeq]
    exact sup_le hA0N ((Subgroup.zpowers_le).2 haN)
  obtain ⟨-, -, hel, hcard⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.lemma43_one_core hp hAsc hAN hZ hSyl hInn
  rw [hfac] at hcard
  have haK : a ∉ K := by
    intro haK
    have h1 : barAut 5 K ⟨a, haN⟩ = 1 := barAut_eq_one_of_comm haN
      (fun y hy => (Subgroup.mem_centralizer_singleton_iff.1 (hKa hy)).symm)
    exact h.ha.2 (eq_one_of_mem_of_trivial hZ haK (hAel.2 a h.ha.1) haN h1)
  have hzA : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).2 h.ha.1
  have hcomm : ∀ x ∈ A ⊓ K, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := fun x hx y hy =>
    elemAbelian_comm hAel (Subgroup.mem_inf.1 hx).1 (hzA hy)
  have hbot : (A ⊓ K) ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxA : x ∈ A := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1
    have hzz := zpowers_eq_of_mem (Subgroup.mem_inf.1 hx).2 (hAel.2 x hxA) hx1 (orderOf_a h)
    have : a ∈ Subgroup.zpowers x := hzz ▸ Subgroup.mem_zpowers a
    exact haK (Subgroup.mem_inf.1 (((Subgroup.zpowers_le).2 (Subgroup.mem_inf.1 hx).1) this)).2
  have hle : (A ⊓ K) ⊔ Subgroup.zpowers a ≤ A := sup_le inf_le_left hzA
  have hc2 : Nat.card ↥((A ⊓ K) ⊔ Subgroup.zpowers a) = 5 ^ 3 := by
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_eq_mul_of_commute hcomm hbot, hcard,
      Nat.card_zpowers, orderOf_a h]
    norm_num
  exact ⟨hAN, hcard, hel, haK, (Subgroup.eq_of_le_of_card_ge hle (by rw [hAc, hc2])).symm⟩

theorem zpowers_le_centralizer {a : G} {K : Subgroup G} (hKa : K ≤ Cg a) :
    Subgroup.zpowers a ≤ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.1 (hKa hy)

theorem mem_zpowers_of_trivial {A K : Subgroup G} {a : G} (hZ : Subgroup.center (barOf 5 K) = ⊥)
    (hAel : IsElemAbelian 5 A) (hAK : A = (A ⊓ K) ⊔ Subgroup.zpowers a) (hKa : K ≤ Cg a)
    {x : G} (hxA : x ∈ A) (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (htriv : barAut 5 K ⟨x, hxN⟩ = 1) : x ∈ Subgroup.zpowers a := by
  have hzA : Subgroup.zpowers a ≤ A := by
    rw [hAK]
    exact le_sup_right
  have hc : A ⊓ K ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
    le_centralizer_of_le hAel inf_le_left hzA
  obtain ⟨s, hs, t, ht, rfl⟩ := exists_mul_of_mem_sup hc (hAK.le hxA)
  have hsN : s ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer (Subgroup.mem_inf.1 hs).2
  have haN : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_le_cg hKa
  have htN : t ∈ Subgroup.normalizer (K : Set G) := ((Subgroup.zpowers_le).2 haN) ht
  have ht1 : barAut 5 K ⟨t, htN⟩ = 1 := barAut_eq_one_of_comm htN (fun y hy =>
    (Subgroup.mem_centralizer_iff.1 (zpowers_le_centralizer hKa ht) y hy).symm)
  have hsplit : (⟨s * t, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨s, hsN⟩ * ⟨t, htN⟩ :=
    Subtype.ext rfl
  rw [hsplit, map_mul, ht1, mul_one] at htriv
  have hs1 : s = 1 := eq_one_of_mem_of_trivial hZ (Subgroup.mem_inf.1 hs).2
    (hAel.2 s (Subgroup.mem_inf.1 hs).1) hsN htriv
  rw [hs1, one_mul]
  exact ht

theorem card_le_five_of_centBar (hF : Fi22Facts) {A K : Subgroup G} {a : G}
    (hK : IsFiTwentyTwo (barOf 5 K)) (hAsc : IsSCp 5 ⊤ A) (hAKc : Nat.card ↥(A ⊓ K) = 5 ^ 2)
    (hAK : A = (A ⊓ K) ⊔ Subgroup.zpowers a) (hKa : K ≤ Cg a)
    {V : Subgroup G} (hV : V ≤ centBar 5 (Cg a) K) (hVel : IsElemAbelian 5 V) : Nat.card V ≤ 5 := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨hZ, hSyl, hInn, hv, hfac⟩ := fi22_facts hF hK
  have hAel := hAsc.2.1
  have hVN : V ≤ Subgroup.normalizer (K : Set G) := fun v hv => (mem_centBar_iff'.1 (hV hv)).2.1
  have hVa : V ≤ Cg a := fun v hv => (mem_centBar_iff'.1 (hV hv)).1
  let ψ : ↥V →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hVN)
  let φ : ↥V →* MulAut (barOf 5 K) := (barAut 5 K).comp (Subgroup.inclusion hVN)
  have hφ : ∀ (v : ↥V) (x : ↥K), φ v (QuotientGroup.mk x) = QuotientGroup.mk (ψ v x) :=
    fun v x => barAut_mk 5 K _ x
  obtain ⟨S, -, hSψ, -, hSel, hScard⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.exists_fixed_section_of_inner hp (GLAPPrimeCore 5 ↥K)
      (coprime_card_gLAPPrimeCore_aux 5 ↥K) (isPGroup_of_elemAb hVel) ψ φ hφ hSyl hInn hZ
  set S' : Subgroup G := S.map K.subtype with hS'def
  have hS'K : S' ≤ K := Subgroup.map_subtype_le S
  have hS'c : Nat.card S' = 5 ^ 2 := by
    rw [hS'def, Subgroup.card_map_of_injective K.subtype_injective, hScard]
    exact congrArg (5 ^ ·) hv
  have hS'el : IsElemAbelian 5 S' := CFSG.SectionRank.isElemAbelian_map hSel _
  have hVS' : ∀ v ∈ V, ∀ s ∈ S', v * s * v⁻¹ = s := by
    rintro v hv _ ⟨s, hs, rfl⟩
    exact congrArg Subtype.val (hSψ ⟨v, hv⟩ s hs)
  obtain ⟨x, hxK, hx⟩ := exists_conj_eq_of_card (X := K) (P := A ⊓ K) (Q := S') inf_le_right hS'K
    (isPGroup_of_elemAb (l1110_isElemAbelian_of_le hAel inf_le_left)) (isPGroup_of_elemAb hS'el)
    (by rw [hAKc, hfac]) (by rw [hS'c, hfac])
  have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 (hKa hxK)
  set V' := GLBConj x V with hV'def
  have hV'el : IsElemAbelian 5 V' := isElemAbelian_conj x hVel
  have hV'A2 : A ⊓ K ≤ Subgroup.centralizer (V' : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyV : x * y * x⁻¹ ∈ V := mem_gLBConj.1 hy
    have htS : x * t * x⁻¹ ∈ S' := by
      rw [← hx] at ht
      exact mem_gLBConj.1 ht
    have h1 := hVS' _ hyV _ htS
    have h2 : x * (y * t * y⁻¹) * x⁻¹ = x * t * x⁻¹ := by
      rw [← h1]
      group
    have h3 : y * t * y⁻¹ = t := by
      have := congrArg (fun z => x⁻¹ * z * x) h2
      simpa [mul_assoc] using this
    calc y * t = (y * t * y⁻¹) * y := by group
      _ = t * y := by rw [h3]
  have hV'a : Subgroup.zpowers a ≤ Subgroup.centralizer (V' : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    have hyV : x * y * x⁻¹ ∈ V := mem_gLBConj.1 hy
    have h1 : (x * y * x⁻¹) * a = a * (x * y * x⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hVa hyV)
    have hxa' : x⁻¹ * a = a * x⁻¹ := (Commute.inv_left (show Commute x a from hxa)).eq
    calc y * a = x⁻¹ * ((x * y * x⁻¹) * a) * x := by
          rw [show (x * y * x⁻¹) * a = x * y * (x⁻¹ * a) by group, hxa']
          group
      _ = x⁻¹ * (a * (x * y * x⁻¹)) * x := by rw [h1]
      _ = a * y := by
          rw [show x⁻¹ * (a * (x * y * x⁻¹)) * x = (x⁻¹ * a) * x * y by group, hxa']
          group
  have hAV' : A ≤ Subgroup.centralizer (V' : Set G) := by
    rw [hAK]
    exact sup_le hV'A2 hV'a
  have hV'le : V' ≤ A := by
    have hsup := hAsc.2.2 (V' ⊔ A) le_top
      (isElemAbelian_sup_of_commute hV'el hAel (Subgroup.le_centralizer_iff.1 hAV')) le_sup_right
    rw [← hsup]
    exact le_sup_left
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hxK
  have hV'z : V' ≤ Subgroup.zpowers a := by
    intro y hy
    have hyV : x * y * x⁻¹ ∈ V := mem_gLBConj.1 hy
    have hvN := hVN hyV
    have hvt : barAut 5 K ⟨x * y * x⁻¹, hvN⟩ = 1 := (mem_centBar_iff'.1 (hV hyV)).2.2
    have hyN : y ∈ Subgroup.normalizer (K : Set G) := by
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxN) hvN) hxN
      simpa [mul_assoc] using this
    have hsplit : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ * ⟨x * y * x⁻¹, hvN⟩ * ⟨x, hxN⟩ :=
      Subtype.ext (by simp [mul_assoc])
    have hyt : barAut 5 K ⟨y, hyN⟩ = 1 := by
      rw [hsplit, map_mul, map_mul, hvt, mul_one, map_inv, inv_mul_cancel]
    exact mem_zpowers_of_trivial hZ hAel hAK hKa (hV'le hy) hyN hyt
  have hVc : Nat.card V' ≤ 5 := by
    calc Nat.card V' ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le hV'z
      _ = orderOf a := Nat.card_zpowers a
      _ ≤ 5 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one
          (hAel.2 a (hAK ▸ (le_sup_right : Subgroup.zpowers a ≤ (A ⊓ K) ⊔ Subgroup.zpowers a)
            (Subgroup.mem_zpowers a))))
  rwa [hV'def, card_conj] at hVc

theorem mem_centBar_iff_forall' {p : ℕ} {X L : Subgroup G} {c : G} :
    c ∈ centBar p X L ↔ c ∈ X ∧ ∃ _ : c ∈ Subgroup.normalizer (L : Set G),
      ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf p L := by
  have key : ∀ γ : ↥(Subgroup.normalizer (L : Set G)), barAut p L γ = 1 ↔
      ∀ l ∈ L, (γ : G) * l * (γ : G)⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf p L := by
    intro γ
    have hN := GLAPPrimeCore.normal p ↥L
    constructor
    · intro h l hl
      have h1 : barAut p L γ (QuotientGroup.mk ⟨l, hl⟩) = QuotientGroup.mk ⟨l, hl⟩ := by
        rw [h]; rfl
      rw [barAut_mk, QuotientGroup.eq] at h1
      have h2 := hN.conj_mem _ (Subgroup.inv_mem _ h1) ⟨l, hl⟩
      refine ⟨_, h2, ?_⟩
      show ((⟨l, hl⟩ : ↥L) : G) * (((L.normalizerMonoidHom γ ⟨l, hl⟩ : ↥L) : G)⁻¹ * l)⁻¹ * l⁻¹ = _
      have e : ((L.normalizerMonoidHom γ ⟨l, hl⟩ : ↥L) : G) = (γ : G) * l * (γ : G)⁻¹ := rfl
      rw [e]
      group
    · intro h
      ext q
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [barAut_mk, MulAut.one_apply, QuotientGroup.eq]
        obtain ⟨y, hy, hyx⟩ := h (x : G) x.2
        simp only [Subgroup.coe_subtype] at hyx
        have h3 := hN.conj_mem _ (Subgroup.inv_mem _ hy) x⁻¹
        convert h3 using 1
        apply Subtype.ext
        have e : ((L.normalizerMonoidHom γ x : ↥L) : G) = (γ : G) * x * (γ : G)⁻¹ := rfl
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, e, hyx]
        group
  constructor
  · rintro ⟨⟨γ, hγ, rfl⟩, hX⟩
    exact ⟨hX, γ.2, (key γ).1 hγ⟩
  · rintro ⟨hX, hN, h⟩
    exact ⟨⟨⟨c, hN⟩, (key ⟨c, hN⟩).2 h, rfl⟩, hX⟩

theorem mem_normalizer_of_subgroupOf' {K S : Subgroup G} (hSK : S ≤ K) {n : ↥K}
    (hn : n ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K)) :
    (n : G) ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨z, hSK hz⟩).1 (Subgroup.mem_subgroupOf.2 hz)
    exact Subgroup.mem_subgroupOf.1 h1
  · intro hz
    have hzK : z ∈ K := by
      have := K.mul_mem (K.mul_mem (K.inv_mem n.2) (hSK hz)) n.2
      simpa [mul_assoc] using this
    have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨z, hzK⟩).2
      (Subgroup.mem_subgroupOf.2 (by simpa using hz))
    exact Subgroup.mem_subgroupOf.1 h1

theorem le_centBar_of_ne' {p : ℕ} (hp : p.Prime) {X L J : Subgroup G} (hL : GLAPComponent p X L)
    (hJ : GLAPComponent p X J) (hne : J ≠ L) : J ≤ centBar p X L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hLs := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hL
  have hJs := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hJ
  have hne' : J.subgroupOf X ≠ L.subgroupOf X := by
    intro h
    apply hne
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_of_le_left hJ.1, inf_of_le_left hL.1] at this
  obtain ⟨-, hn2, hcomm, -⟩ :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation p
      hp _ _ hJs.2 hLs.2).2 hne'
  intro j hj
  have hjX : j ∈ X := hJ.1 hj
  have hjs : (⟨j, hjX⟩ : ↥X) ∈ J.subgroupOf X := Subgroup.mem_subgroupOf.2 hj
  have hjN : j ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_subgroupOf' hL.1 (n := ⟨j, hjX⟩) (hn2 hjs)
  refine mem_centBar_iff_forall'.2 ⟨hjX, hjN, fun l hl => ?_⟩
  have hls : (⟨l, hL.1 hl⟩ : ↥X) ∈ L.subgroupOf X := Subgroup.mem_subgroupOf.2 hl
  have h1 := hcomm (Subgroup.commutator_mem_commutator hjs hls)
  obtain ⟨z, hz, hzc⟩ := (Subgroup.mem_inf.1 h1).2
  let e : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  have hez : e z ∈ GLAPPrimeCore p ↥L := by
    have := glaPPrimeCore_map_iso p e
    rw [← this]
    exact ⟨z, hz, rfl⟩
  refine ⟨e z, hez, ?_⟩
  have : ((e z : ↥L) : G) = ((z : ↥X) : G) := rfl
  show ((e z : ↥L) : G) = j * l * j⁻¹ * l⁻¹
  rw [this]
  have h2 := congrArg (fun w : ↥X => (w : G)) hzc
  simpa [commutatorElement_def] using h2

theorem cg_le_normalizer (hF : Fi22Facts) {A K : Subgroup G} {a : G}
    (hK : IsFiTwentyTwo (barOf 5 K)) (hKc : GLAPComponent 5 (Cg a) K) (hAsc : IsSCp 5 ⊤ A)
    (hAKc : Nat.card ↥(A ⊓ K) = 5 ^ 2) (hAKel : IsElemAbelian 5 (A ⊓ K))
    (hAK : A = (A ⊓ K) ⊔ Subgroup.zpowers a) : Cg a ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  by_contra hne
  have hX : GLBConj g (Cg a) = Cg a :=
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg)
  have hK' : GLAPComponent 5 (Cg a) (GLBConj g K) := by
    have := glaPComponent_gLBConj hKc g
    rwa [hX] at this
  have hle := le_centBar_of_ne' (by norm_num) hKc hK' hne
  have h1 := card_le_five_of_centBar hF hK hAsc hAKc hAK hKc.1
    ((gLBConj_mono g (inf_le_right : A ⊓ K ≤ K)).trans hle) (isElemAbelian_conj g hAKel)
  rw [card_conj, hAKc] at h1
  norm_num at h1

theorem sylow_facts (hF : Fi22Facts) {A K : Subgroup G} {a : G}
    (hK : IsFiTwentyTwo (barOf 5 K)) (hKa : K ≤ Cg a) (hCaN : Cg a ≤ Subgroup.normalizer (K : Set G))
    (hAKc : Nat.card ↥(A ⊓ K) = 5 ^ 2) (hAK : A = (A ⊓ K) ⊔ Subgroup.zpowers a)
    {As : Subgroup G} (hAs : IsSylowIn 5 (Cg a) As) (hAAs : A ≤ As) :
    As ≤ Subgroup.centralizer (A : Set G) ∧
      ∀ x ∈ As, ∃ f ∈ A ⊓ K, ∃ hfx : f⁻¹ * x ∈ Subgroup.normalizer (K : Set G),
        barAut 5 K ⟨f⁻¹ * x, hfx⟩ = 1 := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨hZ, hSyl, hInn, hv, hfac⟩ := fi22_facts hF hK
  have hAsN : As ≤ Subgroup.normalizer (K : Set G) := hAs.1.trans hCaN
  let ψ : ↥As →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hAsN)
  let φ : ↥As →* MulAut (barOf 5 K) := (barAut 5 K).comp (Subgroup.inclusion hAsN)
  have hφ : ∀ (v : ↥As) (x : ↥K), φ v (QuotientGroup.mk x) = QuotientGroup.mk (ψ v x) :=
    fun v x => barAut_mk 5 K _ x
  obtain ⟨S, -, hSψ, hSf, hSel, hScard⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.exists_fixed_section_of_inner hp (GLAPPrimeCore 5 ↥K)
      (coprime_card_gLAPPrimeCore_aux 5 ↥K) hAs.2.1 ψ φ hφ hSyl hInn hZ
  set S' : Subgroup G := S.map K.subtype with hS'def
  have hS'K : S' ≤ K := Subgroup.map_subtype_le S
  have hS'c : Nat.card S' = 5 ^ 2 := by
    rw [hS'def, Subgroup.card_map_of_injective K.subtype_injective, hScard]
    exact congrArg (5 ^ ·) hv
  have hS'el : IsElemAbelian 5 S' := CFSG.SectionRank.isElemAbelian_map hSel _
  have hAsS' : As ≤ Subgroup.centralizer (S' : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have h1 : x * (s : G) * x⁻¹ = s := congrArg Subtype.val (hSψ ⟨x, hx⟩ s hs)
    calc (s : G) * x = (x * (s : G) * x⁻¹) * x := by rw [h1]
      _ = x * s := by group
  have hsup : S' ⊔ As = As := by
    refine hAs.2.2 _ (sup_le (hS'K.trans hKa) hAs.1)
      (IsPGroup.to_sup_of_normal_left' (isPGroup_of_elemAb hS'el) hAs.2.1
        (hAsS'.trans (Subgroup.centralizer_le_normalizer _))) le_sup_right
  have hS'As : S' ≤ As := by
    rw [← hsup]
    exact le_sup_left
  have hcK : Nat.card ↥(As ⊓ K) ≤ 5 ^ 2 := by
    rw [← hfac]
    exact card_le_of_pGroup_le inf_le_right (hAs.2.1.to_le inf_le_left)
  have hAKeq : A ⊓ K = As ⊓ K :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf_right K hAAs) (by rw [hAKc]; exact hcK)
  have hS'eq : S' = As ⊓ K :=
    Subgroup.eq_of_le_of_card_ge (le_inf hS'As hS'K) (by rw [hS'c]; exact hcK)
  have hS'A : S' = A ⊓ K := by rw [hS'eq, hAKeq]
  refine ⟨?_, fun x hx => ?_⟩
  ·
    refine Subgroup.le_centralizer_iff.1 ?_
    rw [hAK]
    refine sup_le ?_ ?_
    · rw [← hS'A]
      exact Subgroup.le_centralizer_iff.1 hAsS'
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hAs.1 hy))
  · obtain ⟨f, hfS, hfx⟩ := hSf ⟨x, hx⟩
    have hf' : (f : G) ∈ A ⊓ K := by
      rw [← hS'A]
      exact ⟨f, hfS, rfl⟩
    have hfN : (f : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer f.2
    have hxN : x ∈ Subgroup.normalizer (K : Set G) := hAsN hx
    have hfxN : (f : G)⁻¹ * x ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hfN) hxN
    refine ⟨f, hf', hfxN, ?_⟩
    have hsplit : (⟨(f : G)⁻¹ * x, hfxN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        (⟨(f : G), hfN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ * ⟨x, hxN⟩ := Subtype.ext rfl
    have hfconj : barAut 5 K ⟨(f : G), hfN⟩ = MulAut.conj (QuotientGroup.mk f : barOf 5 K) :=
      barAut_of_mem f.2
    have hxconj : barAut 5 K ⟨x, hxN⟩ = MulAut.conj (QuotientGroup.mk f : barOf 5 K) := hfx
    rw [hsplit, map_mul, map_inv, hfconj, hxconj, inv_mul_cancel]

theorem card_le_of_le_sylow (hF : Fi22Facts) {A K : Subgroup G} {a : G}
    (hK : IsFiTwentyTwo (barOf 5 K)) (hAsc : IsSCp 5 ⊤ A) (hKa : K ≤ Cg a)
    (hAKc : Nat.card ↥(A ⊓ K) = 5 ^ 2) (hAK : A = (A ⊓ K) ⊔ Subgroup.zpowers a)
    {As : Subgroup G} (hAs : IsSylowIn 5 (Cg a) As) (hAAs : A ≤ As)
    (hcen : As ≤ Subgroup.centralizer (A : Set G))
    (hdec : ∀ x ∈ As, ∃ f ∈ A ⊓ K, ∃ hfx : f⁻¹ * x ∈ Subgroup.normalizer (K : Set G),
        barAut 5 K ⟨f⁻¹ * x, hfx⟩ = 1)
    {F : Subgroup G} (hFAs : F ≤ As) (hFel : IsElemAbelian 5 F) : Nat.card F ≤ 5 ^ 3 := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨hZ, -, -, -, -⟩ := fi22_facts hF hK
  have hAKel : IsElemAbelian 5 (A ⊓ K) := l1110_isElemAbelian_of_le hAsc.2.1 inf_le_left
  have hFA2 : F ≤ Subgroup.centralizer ((A ⊓ K : Subgroup G) : Set G) :=
    (hFAs.trans hcen).trans (Subgroup.centralizer_le (fun x hx => (Subgroup.mem_inf.1 hx).1))
  set F₂ := F ⊔ (A ⊓ K) with hF₂
  have hF₂el : IsElemAbelian 5 F₂ := isElemAbelian_sup_of_commute hFel hAKel hFA2
  have hF₂As : F₂ ≤ As := sup_le hFAs (inf_le_left.trans hAAs)
  set C₂ := F₂ ⊓ centBar 5 (Cg a) K with hC₂
  have hC₂c : Nat.card C₂ ≤ 5 := card_le_five_of_centBar hF hK hAsc hAKc hAK hKa inf_le_right
    (l1110_isElemAbelian_of_le hF₂el inf_le_left)
  have hcomm : ∀ x ∈ A ⊓ K, ∀ y ∈ C₂, x * y = y * x := fun x hx y hy =>
    elemAbelian_comm hF₂el (Subgroup.mem_sup_right hx) (Subgroup.mem_inf.1 hy).1
  have hbot : (A ⊓ K) ⊓ C₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨hzAK, hzC⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨-, hzN, hzt⟩ := mem_centBar_iff'.1 (Subgroup.mem_inf.1 hzC).2
    exact eq_one_of_mem_of_trivial hZ (Subgroup.mem_inf.1 hzAK).2
      (hAKel.2 z hzAK) hzN hzt
  have hF₂le : F₂ ≤ (A ⊓ K) ⊔ C₂ := by
    intro x hx
    obtain ⟨f, hf, hfxN, hfx⟩ := hdec x (hF₂As hx)
    have hfF₂ : f ∈ F₂ := Subgroup.mem_sup_right hf
    have hfxF₂ : f⁻¹ * x ∈ F₂ := Subgroup.mul_mem _ (Subgroup.inv_mem _ hfF₂) hx
    have hfa : f ∈ Cg a := hKa (Subgroup.mem_inf.1 hf).2
    have hxa : x ∈ Cg a := hAs.1 (hF₂As hx)
    have hfxC : f⁻¹ * x ∈ C₂ := Subgroup.mem_inf.2 ⟨hfxF₂, mem_centBar_iff'.2
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hfa) hxa, hfxN, hfx⟩⟩
    have : x = f * (f⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hf hfxC
  calc Nat.card F ≤ Nat.card F₂ := Subgroup.card_le_of_le le_sup_left
    _ ≤ Nat.card ↥((A ⊓ K) ⊔ C₂) := Subgroup.card_le_of_le hF₂le
    _ = Nat.card ↥(A ⊓ K) * Nat.card C₂ :=
        CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_eq_mul_of_commute hcomm hbot
    _ ≤ 5 ^ 2 * 5 := by rw [hAKc]; exact Nat.mul_le_mul_left _ hC₂c
    _ = 5 ^ 3 := by norm_num

end Eps

@[expose] def InputFi22OneClassFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSporType .Fi22 X → ∀ x y : X, orderOf x = 5 → orderOf y = 5 →
    ∃ g : X, g * x * g⁻¹ = y

section Zeta1

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut_mk coprime_card_gLAPPrimeCore_aux)

theorem exists_conj_of_conj_mod {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    (O : Subgroup Y) [O.Normal] (hO : Nat.Coprime p (Nat.card O)) {x y : Y}
    (hx : orderOf x = p) (hy : orderOf y = p)
    (h : ∃ g : Y ⧸ O, g * (x : Y ⧸ O) * g⁻¹ = (y : Y ⧸ O)) : ∃ k : Y, k * x * k⁻¹ = y := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective g
  set z := k₀ * x * k₀⁻¹ with hzdef
  have hz : (z : Y ⧸ O) = y := by
    rw [hzdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hg
  have hzo : orderOf z = p := by
    have := orderOf_injective (MulAut.conj k₀).toMonoidHom (MulAut.conj k₀).injective x
    rw [hzdef, ← hx, ← this]
    rfl
  have hyO : ∀ w ∈ Subgroup.zpowers y, w ∈ O → w = 1 := fun w hw hwO =>
    eq_one_of_dvd_coprime hO (by rw [← hy]; exact orderOf_dvd_of_mem_zpowers hw)
      (Subgroup.orderOf_dvd_natCard O hwO)
  have hybar : orderOf (y : Y ⧸ O) = p := by
    refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, ← hy, pow_orderOf_eq_one,
      QuotientGroup.mk_one]) ?_
    intro h1
    have hyO' : y ∈ O := (QuotientGroup.eq_one_iff y).1 h1
    have := hyO y (Subgroup.mem_zpowers y) hyO'
    rw [this, orderOf_one] at hy
    exact hp.out.one_lt.ne hy
  set H : Subgroup Y := (Subgroup.zpowers (y : Y ⧸ O)).comap (QuotientGroup.mk' O) with hHdef
  have hHc : Nat.card H = p * Nat.card O := by
    rw [hHdef, card_comap_mk, Nat.card_zpowers, hybar]
  have hfac : (Nat.card H).factorization p = 1 := by
    rw [hHc, Nat.factorization_mul hp.out.ne_zero Nat.card_pos.ne', Finsupp.add_apply,
      hp.out.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp.out).1 hO)]
  have hyH : Subgroup.zpowers y ≤ H := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_zpowers _
  have hzH : Subgroup.zpowers z ≤ H := by
    rw [Subgroup.zpowers_le]
    show ((QuotientGroup.mk' O) z) ∈ Subgroup.zpowers (y : Y ⧸ O)
    rw [QuotientGroup.mk'_apply, hz]
    exact Subgroup.mem_zpowers _
  have hcy : Nat.card (Subgroup.zpowers y) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_zpowers, hy, hfac, pow_one]
  have hcz : Nat.card (Subgroup.zpowers z) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_zpowers, hzo, hfac, pow_one]
  have hpy : IsPGroup p (Subgroup.zpowers y) := IsPGroup.of_card hcy
  have hpz : IsPGroup p (Subgroup.zpowers z) := IsPGroup.of_card hcz
  obtain ⟨c, hcH, hc⟩ := exists_conj_eq_of_card hyH hzH hpy hpz hcy hcz
  have hw : c⁻¹ * z * c ∈ Subgroup.zpowers y := by
    rw [← hc, mem_gLBConj]
    simpa [mul_assoc] using Subgroup.mem_zpowers z
  have hcbar : (c : Y ⧸ O) ∈ Subgroup.zpowers (y : Y ⧸ O) := hcH
  have hwbar : ((c⁻¹ * z * c : Y) : Y ⧸ O) = y := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hcbar
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hz, ← hj]
    group
  have hweq : c⁻¹ * z * c = y := by
    have h1 : (c⁻¹ * z * c)⁻¹ * y ∈ O := QuotientGroup.eq.1 hwbar
    have h2 : (c⁻¹ * z * c)⁻¹ * y ∈ Subgroup.zpowers y :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hw) (Subgroup.mem_zpowers y)
    have := hyO _ h2 h1
    rw [inv_mul_eq_one] at this
    exact this
  refine ⟨c⁻¹ * k₀, ?_⟩
  rw [← hweq, hzdef]
  group

theorem exists_conj_in_K (hI : InputFi22OneClassFive) {K : Subgroup G}
    (hK : IsSporType .Fi22 (barOf 5 K)) {x y : G} (hxK : x ∈ K) (hyK : y ∈ K)
    (hx : orderOf x = 5) (hy : orderOf y = 5) : ∃ k ∈ K, k * x * k⁻¹ = y := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcop := coprime_card_gLAPPrimeCore_aux 5 ↥K
  have hx' : orderOf (⟨x, hxK⟩ : K) = 5 := by rw [Subgroup.orderOf_mk, hx]
  have hy' : orderOf (⟨y, hyK⟩ : K) = 5 := by rw [Subgroup.orderOf_mk, hy]
  have hbar : ∀ w : K, orderOf w = 5 → orderOf (QuotientGroup.mk w : barOf 5 K) = 5 := by
    intro w hw
    refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, ← hw, pow_orderOf_eq_one,
      QuotientGroup.mk_one]) ?_
    intro h1
    have hwO : w ∈ GLAPPrimeCore 5 ↥K := (QuotientGroup.eq_one_iff w).1 h1
    have := eq_one_of_dvd_coprime hcop (by rw [hw]) (Subgroup.orderOf_dvd_natCard _ hwO)
    rw [this, orderOf_one] at hw
    norm_num at hw
  obtain ⟨k, hk⟩ := exists_conj_of_conj_mod (GLAPPrimeCore 5 ↥K) hcop hx' hy'
    (hI (barOf 5 K) hK _ _ (hbar _ hx') (hbar _ hy'))
  exact ⟨k, k.2, congrArg Subtype.val hk⟩

theorem card_of_isSylowIn {p : ℕ} [Fact p.Prime] {X R : Subgroup G} (hR : IsSylowIn p X R) :
    Nat.card R = p ^ (Nat.card X).factorization p := by
  have hRp : IsPGroup p ↥(R.subgroupOf X) :=
    hR.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hR.1).symm
  obtain ⟨Q, hQ⟩ := hRp.exists_le_sylow
  have hQp : IsPGroup p ↥((Q : Subgroup X).map X.subtype) := Q.isPGroup'.map X.subtype
  have hRQ : R ≤ (Q : Subgroup X).map X.subtype := fun x hx =>
    ⟨⟨x, hR.1 hx⟩, hQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have heq := hR.2.2 _ (Subgroup.map_subtype_le _) hQp hRQ
  rw [← heq, Subgroup.card_map_of_injective X.subtype_injective]
  exact Sylow.card_eq_multiplicity Q

theorem card_le_of_isSylowIn {p : ℕ} [Fact p.Prime] {X R Q : Subgroup G} (hR : IsSylowIn p X R)
    (hQX : Q ≤ X) (hQ : IsPGroup p Q) : Nat.card Q ≤ Nat.card R := by
  rw [card_of_isSylowIn hR]
  exact card_le_of_pGroup_le hQX hQ

theorem isSylowIn_of_card {p : ℕ} [Fact p.Prime] {X R : Subgroup G} (hRX : R ≤ X) (hR : IsPGroup p R)
    (hc : Nat.card R = p ^ (Nat.card X).factorization p) : IsSylowIn p X R :=
  ⟨hRX, hR, fun R' hR'X hR'p hle =>
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hc]; exact card_le_of_pGroup_le hR'X hR'p)).symm⟩

end Zeta1

section Zeta2

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut_mk coprime_card_gLAPPrimeCore_aux)

theorem comm_of_comm_pow {a x : G} (ha : orderOf a = 5) {i : ℕ} (hi : ¬ 5 ∣ i)
    (h : x * a ^ i = a ^ i * x) : x * a = a * x := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hai1 : a ^ i ≠ 1 := fun h1 => hi (ha ▸ orderOf_dvd_of_pow_eq_one h1)
  have hai5 : (a ^ i) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ← ha, pow_orderOf_eq_one, one_pow]
  have hz := zpowers_eq_of_mem (Subgroup.npow_mem_zpowers a i) hai5 hai1 ha
  have haz : a ∈ Subgroup.zpowers (a ^ i) := hz ▸ Subgroup.mem_zpowers a
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 haz
  have hc : Commute x (a ^ i) := h
  rw [← hj]
  exact (hc.zpow_right j).eq

theorem conj_le_cg {a g : G} (ha : orderOf a = 5) {i : ℕ} (hi : ¬ 5 ∣ i) {T : Subgroup G}
    (hT : ∀ t ∈ T, t * (g * a ^ i * g⁻¹) = (g * a ^ i * g⁻¹) * t) : GLBConj g T ≤ Cg a := by
  intro y hy
  have hyT : g * y * g⁻¹ ∈ T := mem_gLBConj.1 hy
  have h1 := hT _ hyT
  have h2 : y * a ^ i = a ^ i * y := by
    have := congrArg (fun z => g⁻¹ * z * g) h1
    simp only [mul_assoc, inv_mul_cancel_left] at this
    simpa [mul_assoc] using this
  exact Subgroup.mem_centralizer_singleton_iff.2 (comm_of_comm_pow ha hi h2)

theorem exists_T {A As : Subgroup G} (hAs : IsPGroup 5 As) (hnot : ¬ IsSylowIn 5 ⊤ As)
    (hcen : As ≤ Subgroup.centralizer (A : Set G)) (hAAs : A ≤ As) (hAsc : IsSCp 5 ⊤ A) :
    ∃ T : Subgroup G, IsPGroup 5 T ∧ As < T ∧ T ≤ Subgroup.normalizer (A : Set G) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨S, hS⟩ := hAs.exists_le_sylow
  have hne : As ≠ (S : Subgroup G) := by
    intro h
    apply hnot
    rw [h]
    exact ⟨le_top, S.isPGroup', fun _ _ hR'p hle => S.is_maximal' hR'p hle⟩
  haveI : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  have hlt : As.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne (le_antisymm hS ?_)
    intro x hx
    have : (⟨x, hx⟩ : ↥(S : Subgroup G)) ∈ As.subgroupOf S := htop ▸ Subgroup.mem_top _
    exact this
  have hnlt := normalizerCondition_of_isNilpotent (As.subgroupOf S) hlt
  obtain ⟨t, htN, htA⟩ := SetLike.exists_of_lt hnlt
  have htNG : (t : G) ∈ Subgroup.normalizer (As : Set G) := mem_normalizer_of_subgroupOf' hS htN
  have htAs : (t : G) ∉ As := fun h => htA (Subgroup.mem_subgroupOf.2 h)
  have hzt : IsPGroup 5 (Subgroup.zpowers (t : G)) :=
    S.isPGroup'.to_le ((Subgroup.zpowers_le).2 t.2)
  refine ⟨As ⊔ Subgroup.zpowers (t : G),
    IsPGroup.to_sup_of_normal_left' hAs hzt ((Subgroup.zpowers_le).2 htNG), ?_, ?_⟩
  · exact SetLike.lt_iff_le_and_exists.2 ⟨le_sup_left, (t : G), Subgroup.mem_sup_right
      (Subgroup.mem_zpowers _), htAs⟩
  · refine sup_le (hcen.trans (Subgroup.centralizer_le_normalizer _)) ?_
    rw [Subgroup.zpowers_le]
    set A' : Subgroup G := GLBConj (t : G) A with hA'
    have h1 : A' ≤ As :=
      (gLBConj_mono _ hAAs).trans (le_of_eq (gLBConj_eq_of_mem_normalizer htNG))
    have h2 : A ≤ Subgroup.centralizer (A' : Set G) :=
      (Subgroup.le_centralizer_iff.1 hcen).trans (Subgroup.centralizer_le h1)
    have hA'el : IsElemAbelian 5 A' := isElemAbelian_conj (t : G) hAsc.2.1
    have hel : IsElemAbelian 5 (A' ⊔ A) :=
      isElemAbelian_sup_of_commute hA'el hAsc.2.1 (Subgroup.le_centralizer_iff.1 h2)
    have hsup : A' ⊔ A = A := hAsc.2.2 (A' ⊔ A) le_top hel le_sup_right
    have hle : A' ≤ A := by
      rw [← hsup]
      exact le_sup_left
    have hcA : Nat.card A ≤ Nat.card A' := by rw [hA', card_conj]
    exact mem_normalizer_iff_gLBConj_eq.2 (Subgroup.eq_of_le_of_card_ge hle hcA)

abbrev conjActSet (T : Subgroup G) (X : Set G) (hTX : ∀ t ∈ T, ∀ b ∈ X, t * b * t⁻¹ ∈ X) :
    MulAction ↥T ↥X where
  smul t b := ⟨(t : G) * b * (t : G)⁻¹, hTX t t.2 b b.2⟩
  one_smul b := by
    apply Subtype.ext
    show (1 : G) * (b : G) * (1 : G)⁻¹ = b
    simp
  mul_smul g h b := by
    apply Subtype.ext
    show ((g : G) * (h : G)) * (b : G) * ((g : G) * (h : G))⁻¹ =
      (g : G) * ((h : G) * (b : G) * (h : G)⁻¹) * (g : G)⁻¹
    group

theorem exists_decomp {A K : Subgroup G} {a : G} (hAel : IsElemAbelian 5 A)
    (hAK : A = (A ⊓ K) ⊔ Subgroup.zpowers a) {b : G} (hbA : b ∈ A) :
    ∃ x ∈ A ⊓ K, ∃ j : ℕ, b = x * a ^ j := by
  have hzA : Subgroup.zpowers a ≤ A := by
    rw [hAK]
    exact le_sup_right
  have hc : A ⊓ K ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
    le_centralizer_of_le hAel inf_le_left hzA
  obtain ⟨x, hx, t, ht, rfl⟩ := exists_mul_of_mem_sup hc (hAK.le hbA)
  obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 ht)
  exact ⟨x, hx, j, rfl⟩

theorem pow_eq_one_of_dvd {a : G} (ha : orderOf a = 5) {i : ℕ} (h : 5 ∣ i) : a ^ i = 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [pow_mul, ← ha, pow_orderOf_eq_one, one_pow]

theorem fused (hI : InputFi22OneClassFive) {A K As T : Subgroup G} {a : G}
    (hK : IsSporType .Fi22 (barOf 5 K)) (hKa : K ≤ Cg a) (hAel : IsElemAbelian 5 A)
    (hAKc : Nat.card ↥(A ⊓ K) = 5 ^ 2) (hAK : A = (A ⊓ K) ⊔ Subgroup.zpowers a) (haK : a ∉ K)
    (ha : orderOf a = 5) (hAs : IsSylowIn 5 (Cg a) As)
    (hT : IsPGroup 5 T) (hAsT : As < T) (hTN : T ≤ Subgroup.normalizer (A : Set G)) :
    ∀ b ∈ A, b ∉ K → ∃ g : G, ∃ i : ℕ, ¬ 5 ∣ i ∧ b = g * a ^ i * g⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set X : Set G := {b | b ∈ A ∧ ∃ g : G, ∃ i : ℕ, ¬ 5 ∣ i ∧ b = g * a ^ i * g⁻¹} with hXdef
  have hzA : Subgroup.zpowers a ≤ A := by
    rw [hAK]
    exact le_sup_right
  have hX1 : ∀ b ∈ X, b ≠ 1 := by
    rintro b ⟨-, g, i, hi, rfl⟩ h1
    have h2 : a ^ i = 1 := by
      have := congrArg (fun z => g⁻¹ * z * g) h1
      simpa [mul_assoc] using this
    exact hi (ha ▸ orderOf_dvd_of_pow_eq_one h2)
  have hXconj : ∀ b ∈ X, ∀ k : G, k * b * k⁻¹ ∈ A → k * b * k⁻¹ ∈ X := by
    rintro b ⟨-, g, i, hi, rfl⟩ k hk
    exact ⟨hk, k * g, i, hi, by group⟩
  have hXpow : ∀ b ∈ X, ∀ e : ℕ, ¬ 5 ∣ e → b ^ e ∈ X := by
    rintro b ⟨hbA, g, i, hi, rfl⟩ e he
    refine ⟨Subgroup.pow_mem _ hbA e, g, i * e, ?_, ?_⟩
    · intro h
      rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
      · exact hi h
      · exact he h
    · rw [conj_pow, pow_mul]
  have hXa : ∀ i : ℕ, ¬ 5 ∣ i → a ^ i ∈ X := fun i hi =>
    ⟨hzA (Subgroup.npow_mem_zpowers a i), 1, i, hi, by group⟩
  have hTX : ∀ t ∈ T, ∀ b ∈ X, t * b * t⁻¹ ∈ X := fun t ht b hb =>
    hXconj b hb t ((Subgroup.mem_normalizer_iff.1 (hTN ht) b).1 hb.1)
  letI := conjActSet T X hTX
  have hmod := hT.card_modEq_card_fixedPoints ↥X
  have hfix : Nat.card (MulAction.fixedPoints ↥T ↥X) = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨⟨b, hbX⟩, hb⟩
    obtain ⟨-, g, i, hi, hbeq⟩ := id hbX
    have hcomm : ∀ t ∈ T, t * (g * a ^ i * g⁻¹) = (g * a ^ i * g⁻¹) * t := by
      intro t ht
      have h1 := congrArg Subtype.val (hb ⟨t, ht⟩)
      change t * b * t⁻¹ = b at h1
      rw [← hbeq]
      calc t * b = (t * b * t⁻¹) * t := by group
        _ = b * t := by rw [h1]
    have hle := conj_le_cg ha hi hcomm
    have hc := card_le_of_isSylowIn hAs hle (isPGroup_conj g hT)
    rw [card_conj] at hc
    exact absurd hc (not_le.2 (card_lt_of_lt' hAsT))
  have hcard5 : Nat.card ↥X % 5 = 0 := by
    have h := hmod
    rw [hfix] at h
    exact h
  have hXK : (∃ x ∈ X, x ∈ K) → ∀ y ∈ A ⊓ K, y ≠ 1 → y ∈ X := by
    rintro ⟨x, hxX, hxK⟩ y hy hy1
    have hxo : orderOf x = 5 := orderOf_eq_of_pow (hAel.2 x hxX.1) (hX1 x hxX)
    have hyo : orderOf y = 5 := orderOf_eq_of_pow (hAel.2 y (Subgroup.mem_inf.1 hy).1) hy1
    obtain ⟨k, hkK, hk⟩ := exists_conj_in_K hI hK hxK (Subgroup.mem_inf.1 hy).2 hxo hyo
    have h1 := hXconj x hxX k (by rw [hk]; exact (Subgroup.mem_inf.1 hy).1)
    rwa [hk] at h1
  have hXY : (∃ b₀ ∈ X, b₀ ∉ K ∧ b₀ ∉ Subgroup.zpowers a) → ∀ b ∈ A, b ∉ K → b ∈ X := by
    rintro ⟨b₀, hb₀X, hb₀K, hb₀a⟩ b hbA hbK
    obtain ⟨s, hs, j, rfl⟩ := exists_decomp hAel hAK hb₀X.1
    obtain ⟨s', hs', j', rfl⟩ := exists_decomp hAel hAK hbA
    have hj : ¬ 5 ∣ j := by
      intro h5
      apply hb₀K
      rw [pow_eq_one_of_dvd ha h5, mul_one]
      exact (Subgroup.mem_inf.1 hs).2
    have hj' : ¬ 5 ∣ j' := by
      intro h5
      apply hbK
      rw [pow_eq_one_of_dvd ha h5, mul_one]
      exact (Subgroup.mem_inf.1 hs').2
    have hs1 : s ≠ 1 := by
      intro h
      apply hb₀a
      rw [h, one_mul]
      exact Subgroup.npow_mem_zpowers a j
    by_cases hs'1 : s' = 1
    · rw [hs'1, one_mul]
      exact hXa j' hj'
    · set e := j' * j ^ 3 with he
      have he5 : ¬ 5 ∣ e := by
        intro h
        rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
        · exact hj' h
        · exact hj (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
      have hpow := hXpow _ hb₀X e he5
      have hcomm' : Commute s (a ^ j) :=
        elemAbelian_comm hAel (Subgroup.mem_inf.1 hs).1 (hzA (Subgroup.npow_mem_zpowers a j))
      rw [hcomm'.mul_pow] at hpow
      have hmodj : j * e ≡ j' [MOD 5] := by
        have hcop : Nat.Coprime j 5 :=
          ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).2 hj).symm
        have hf : j ^ 4 ≡ 1 [MOD 5] := by
          have := Nat.ModEq.pow_totient hcop
          rwa [Nat.totient_prime (by norm_num : Nat.Prime 5)] at this
        have h1 : j * e = j' * j ^ 4 := by rw [he]; ring
        rw [h1]
        calc j' * j ^ 4 ≡ j' * 1 [MOD 5] := Nat.ModEq.mul_left _ hf
          _ = j' := mul_one j'
      have haj : (a ^ j) ^ e = a ^ j' := by
        rw [← pow_mul]
        exact pow_eq_pow_iff_modEq.2 (ha ▸ hmodj)
      rw [haj] at hpow
      have hse : s ^ e ∈ A ⊓ K := Subgroup.pow_mem _ hs e
      have hso : orderOf s = 5 := orderOf_eq_of_pow (hAel.2 s (Subgroup.mem_inf.1 hs).1) hs1
      have hse1 : s ^ e ≠ 1 := fun h1 => he5 (hso ▸ orderOf_dvd_of_pow_eq_one h1)
      have hseo : orderOf (s ^ e) = 5 :=
        orderOf_eq_of_pow (hAel.2 _ (Subgroup.mem_inf.1 hse).1) hse1
      have hs'o : orderOf s' = 5 := orderOf_eq_of_pow (hAel.2 s' (Subgroup.mem_inf.1 hs').1) hs'1
      obtain ⟨k, hkK, hk⟩ := exists_conj_in_K hI hK (Subgroup.mem_inf.1 hse).2
        (Subgroup.mem_inf.1 hs').2 hseo hs'o
      have hka : k * a ^ j' * k⁻¹ = a ^ j' := by
        have hc : Commute k a := Subgroup.mem_centralizer_singleton_iff.1 (hKa hkK)
        rw [(hc.pow_right j').eq]
        group
      have hconj : k * (s ^ e * a ^ j') * k⁻¹ = s' * a ^ j' := by
        rw [show k * (s ^ e * a ^ j') * k⁻¹ = (k * s ^ e * k⁻¹) * (k * a ^ j' * k⁻¹) by group,
          hk, hka]
      have h1 := hXconj _ hpow k (by rw [hconj]; exact hbA)
      rwa [hconj] at h1
  intro b hbA hbK
  by_contra hbX
  have hbX' : b ∉ X := fun h => hbX h.2
  have hno : ∀ b₀ ∈ X, b₀ ∉ K → b₀ ∈ Subgroup.zpowers a := by
    intro b₀ hb₀ hb₀K
    by_contra hza
    exact hbX' (hXY ⟨b₀, hb₀, hb₀K, hza⟩ b hbA hbK)
  set S₁ : Set G := X ∩ ((A ⊓ K : Subgroup G) : Set G) with hS₁def
  set S₂ : Set G := ((Subgroup.zpowers a : Subgroup G) : Set G) \ {1} with hS₂def
  have hXeq : X = S₁ ∪ S₂ := by
    ext x
    constructor
    · intro hx
      by_cases hxK : x ∈ K
      · exact Or.inl ⟨hx, Subgroup.mem_inf.2 ⟨hx.1, hxK⟩⟩
      · exact Or.inr ⟨hno x hx hxK, hX1 x hx⟩
    · rintro (hx | ⟨hxa, hx1⟩)
      · exact hx.1
      · obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hxa)
        exact hXa i fun h5 => hx1 (pow_eq_one_of_dvd ha h5)
  have hdisj : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hxAK⟩ ⟨hxa, hx1⟩
    apply haK
    have hz := zpowers_eq_of_mem hxa (hAel.2 x (Subgroup.mem_inf.1 hxAK).1) hx1 ha
    have h1 : a ∈ Subgroup.zpowers x := hz ▸ Subgroup.mem_zpowers a
    exact ((Subgroup.zpowers_le).2 (Subgroup.mem_inf.1 hxAK).2) h1
  have hcoe : ∀ H : Subgroup G, ((H : Set G)).ncard = Nat.card H := fun H =>
    (Nat.card_coe_set_eq (H : Set G)).symm
  have hS₂ : S₂.ncard = 4 := by
    rw [hS₂def, Set.ncard_diff_singleton_of_mem (Subgroup.one_mem _), hcoe, Nat.card_zpowers, ha]
  have hS₁ : S₁.ncard = 0 ∨ S₁.ncard = 24 := by
    by_cases hne : S₁.Nonempty
    · right
      obtain ⟨x, hxX, hxAK⟩ := hne
      have hS₁eq : S₁ = ((A ⊓ K : Subgroup G) : Set G) \ {1} := by
        ext y
        constructor
        · rintro ⟨hyX, hyAK⟩
          exact ⟨hyAK, hX1 y hyX⟩
        · rintro ⟨hyAK, hy1⟩
          exact ⟨hXK ⟨x, hxX, (Subgroup.mem_inf.1 hxAK).2⟩ y hyAK hy1, hyAK⟩
      rw [hS₁eq, Set.ncard_diff_singleton_of_mem (Subgroup.one_mem _), hcoe, hAKc]
      norm_num
    · left
      rw [Set.not_nonempty_iff_eq_empty.1 hne, Set.ncard_empty]
  have hXc : Nat.card ↥X = S₁.ncard + S₂.ncard := by
    rw [Nat.card_coe_set_eq, hXeq, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  rw [hXc, hS₂] at hcard5
  rcases hS₁ with h | h <;> rw [h] at hcard5 <;> norm_num at hcard5

theorem A0_eq_A2 {A K As A0 R : Subgroup G} {a : G} (ha : orderOf a = 5)
    (hAs : IsSylowIn 5 (Cg a) As) (hnot : ¬ IsSylowIn 5 ⊤ As) (hR : IsSylowIn 5 ⊤ R)
    (hA0R : ∀ e ∈ A0, ∀ r ∈ R, r * e = e * r) (hA0A : A0 ≤ A) (hA0c : Nat.card A0 = 5 ^ 2)
    (hAKc : Nat.card ↥(A ⊓ K) = 5 ^ 2)
    (hfus : ∀ b ∈ A, b ∉ K → ∃ g : G, ∃ i : ℕ, ¬ 5 ∣ i ∧ b = g * a ^ i * g⁻¹) :
    A0 = A ⊓ K := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hle : A0 ≤ A ⊓ K := by
    intro e he
    refine Subgroup.mem_inf.2 ⟨hA0A he, ?_⟩
    by_contra heK
    obtain ⟨g, i, hi, hge⟩ := hfus _ (hA0A he) heK
    have hcomm : ∀ t ∈ R, t * (g * a ^ i * g⁻¹) = (g * a ^ i * g⁻¹) * t := fun t ht => by
      rw [← hge]
      exact hA0R e he t ht
    have hc := card_le_of_isSylowIn hAs (conj_le_cg ha hi hcomm) (isPGroup_conj g hR.2.1)
    rw [card_conj] at hc
    apply hnot
    have hRc := card_of_isSylowIn hR
    have hAsR : Nat.card As ≤ Nat.card R := card_le_of_isSylowIn hR le_top hAs.2.1
    exact isSylowIn_of_card le_top hAs.2.1 (by rw [← hRc]; omega)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hAKc, hA0c])

theorem A_eq_As (hF : Fi22Facts) {A K As : Subgroup G} {a : G}
    (hK : IsFiTwentyTwo (barOf 5 K)) (hAsc : IsSCp 5 ⊤ A) (hKa : K ≤ Cg a)
    (hAKc : Nat.card ↥(A ⊓ K) = 5 ^ 2) (hAK : A = (A ⊓ K) ⊔ Subgroup.zpowers a) (haK : a ∉ K)
    (ha : orderOf a = 5) (hAs : IsSylowIn 5 (Cg a) As) (hAAs : A ≤ As)
    (hcen : As ≤ Subgroup.centralizer (A : Set G))
    (hdec : ∀ x ∈ As, ∃ f ∈ A ⊓ K, ∃ hfx : f⁻¹ * x ∈ Subgroup.normalizer (K : Set G),
        barAut 5 K ⟨f⁻¹ * x, hfx⟩ = 1)
    (hfus : ∀ b ∈ A, b ∉ K → ∃ g : G, ∃ i : ℕ, ¬ 5 ∣ i ∧ b = g * a ^ i * g⁻¹) : A = As := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨hZ, -, -, -, -⟩ := fi22_facts hF hK
  have hAel := hAsc.2.1
  have hzA : Subgroup.zpowers a ≤ A := by
    rw [hAK]
    exact le_sup_right
  have haA : a ∈ A := hzA (Subgroup.mem_zpowers a)
  have haN : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_le_cg hKa
  have haC : a ∈ centBar 5 (Cg a) K := mem_centBar_iff'.2
    ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, haN, barAut_eq_one_of_comm haN
      (fun y hy => (Subgroup.mem_centralizer_singleton_iff.1 (hKa hy)).symm)⟩
  set C := As ⊓ centBar 5 (Cg a) K with hCdef
  have hC5 : ∀ c ∈ C, c ^ 5 = 1 → c ∈ Subgroup.zpowers a := by
    intro c hc hc5
    have hca : c * a = a * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (hAs.1 (Subgroup.mem_inf.1 hc).1)
    have hzc : IsElemAbelian 5 (Subgroup.zpowers c) := by
      rw [Subgroup.zpowers_eq_closure]
      exact l1110_isElemAbelian_closure_singleton hc5
    have hza : IsElemAbelian 5 (Subgroup.zpowers a) := by
      rw [Subgroup.zpowers_eq_closure]
      exact l1110_isElemAbelian_closure_singleton (ha ▸ pow_orderOf_eq_one a)
    have hcomm : Subgroup.zpowers c ≤
        Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact ((Commute.zpow_left (show Commute a c from hca.symm) j)).eq
    have hel := isElemAbelian_sup_of_commute hzc hza hcomm
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers a ≤ centBar 5 (Cg a) K :=
      sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_inf.1 hc).2) ((Subgroup.zpowers_le).2 haC)
    have hcard := card_le_five_of_centBar hF hK hAsc hAKc hAK hKa hle hel
    have heq : Subgroup.zpowers a = Subgroup.zpowers c ⊔ Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [Nat.card_zpowers, ha]; exact hcard)
    rw [heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hAsdec : ∀ x ∈ As, ∃ f ∈ A ⊓ K, f⁻¹ * x ∈ C := by
    intro x hx
    obtain ⟨f, hf, hfxN, hfx⟩ := hdec x hx
    have hfAs : f ∈ As := hAAs (Subgroup.mem_inf.1 hf).1
    refine ⟨f, hf, Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hfAs) hx,
      mem_centBar_iff'.2 ⟨?_, hfxN, hfx⟩⟩⟩
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKa (Subgroup.mem_inf.1 hf).2)) (hAs.1 hx)
  by_contra hne
  have hex : ∃ c ∈ C, c ^ 5 ≠ 1 := by
    by_contra hall
    apply hne
    refine le_antisymm hAAs ?_
    intro x hx
    obtain ⟨f, hf, hfx⟩ := hAsdec x hx
    have h5 : (f⁻¹ * x) ^ 5 = 1 := by
      by_contra h5
      exact hall ⟨_, hfx, h5⟩
    have h1 : f⁻¹ * x ∈ A := hzA (hC5 _ hfx h5)
    have h2 : x = f * (f⁻¹ * x) := by group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_inf.1 hf).1 h1
  obtain ⟨c, hcC, hc5⟩ := hex
  have hcAs : c ∈ As := (Subgroup.mem_inf.1 hcC).1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf c = 5 ^ k := by
    obtain ⟨k, hk⟩ := hAs.2.1 ⟨c, hcAs⟩
    have h1 : orderOf c ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hk
      simpa using this)
    obtain ⟨k', -, hk'⟩ := (Nat.dvd_prime_pow hp).1 h1
    exact ⟨k', hk'⟩
  have hk2 : 2 ≤ k := by
    by_contra h
    apply hc5
    have h1 : orderOf c ∣ 5 := by
      rw [hk]
      calc 5 ^ k ∣ 5 ^ 1 := pow_dvd_pow 5 (by omega)
        _ = 5 := pow_one 5
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  set d := c ^ (5 ^ (k - 1)) with hd
  have hdC : d ∈ C := Subgroup.pow_mem _ hcC _
  have hd5 : d ^ 5 = 1 := by
    rw [hd, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k), ← hk,
      pow_orderOf_eq_one]
  have hd1 : d ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hk] at h1
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 5)).1 h1
    omega
  have hzd := zpowers_eq_of_mem (hC5 d hdC hd5) hd5 hd1 ha
  have had : a ∈ Subgroup.zpowers d := hzd ▸ Subgroup.mem_zpowers a
  have hdc5 : d ∈ Subgroup.zpowers (c ^ 5) := by
    have he : 5 ^ (k - 1) = 5 * 5 ^ (k - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hd, he, pow_mul]
    exact Subgroup.npow_mem_zpowers _ _
  have hac5 : a ∈ Subgroup.zpowers (c ^ 5) := ((Subgroup.zpowers_le).2 hdc5) had
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hac5
  set w := c ^ j with hw
  have hwAs : w ∈ As := Subgroup.zpow_mem _ hcAs j
  have hw5 : w ^ 5 = a := by
    rw [hw, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hj]
  obtain ⟨x, hxAK, hx1⟩ : ∃ x ∈ A ⊓ K, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : A ⊓ K = ⊥ := eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (h y hy)
    rw [hbot, Subgroup.card_bot] at hAKc
    norm_num at hAKc
  have hbA : x * a ∈ A := Subgroup.mul_mem _ (Subgroup.mem_inf.1 hxAK).1 haA
  have hbK : x * a ∉ K := fun h => haK (by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_inf.1 hxAK).2) h
    simpa using this)
  obtain ⟨g, i, hi, hgb⟩ := hfus _ hbA hbK
  have hcomm : ∀ t ∈ As, t * (g * a ^ i * g⁻¹) = (g * a ^ i * g⁻¹) * t := by
    intro t ht
    rw [← hgb]
    exact (Subgroup.mem_centralizer_iff.1 (hcen ht) _ hbA).symm
  have hle := conj_le_cg ha hi hcomm
  have hSyl' : IsSylowIn 5 (Cg a) (GLBConj g As) :=
    isSylowIn_of_card hle (isPGroup_conj g hAs.2.1) (by rw [card_conj, card_of_isSylowIn hAs])
  obtain ⟨c₁, hc₁, hc₁eq⟩ := exists_conj_eq_of_card hAs.1 hle hAs.2.1 (isPGroup_conj g hAs.2.1)
    (card_of_isSylowIn hAs) (card_of_isSylowIn hSyl')
  rw [gLBConj_gLBConj] at hc₁eq
  have hn : g * c₁ ∈ Subgroup.normalizer (As : Set G) := mem_normalizer_iff_gLBConj_eq.2 hc₁eq
  have hc₁a : c₁ * a ^ i * c₁⁻¹ = a ^ i := by
    have hc : Commute c₁ a := Subgroup.mem_centralizer_singleton_iff.1 hc₁
    rw [(hc.pow_right i).eq]
    group
  have hb' : x * a = (g * c₁) * (w ^ i) ^ 5 * (g * c₁)⁻¹ := by
    rw [hgb, ← pow_mul, mul_comm, pow_mul, hw5,
      show (g * c₁) * a ^ i * (g * c₁)⁻¹ = g * (c₁ * a ^ i * c₁⁻¹) * g⁻¹ by group, hc₁a]
  set u := (g * c₁) * w ^ i * (g * c₁)⁻¹ with hu
  have hu5' : (g * c₁) * (w ^ i) ^ 5 * (g * c₁)⁻¹ = u ^ 5 := by rw [hu, conj_pow]
  have huAs : u ∈ As := (Subgroup.mem_normalizer_iff.1 hn _).1 (Subgroup.pow_mem _ hwAs i)
  obtain ⟨f, hf, hfu⟩ := hAsdec u huAs
  have hfc : Commute f (f⁻¹ * u) :=
    (Subgroup.mem_centralizer_iff.1 (hcen (Subgroup.mem_inf.1 hfu).1) f
      (Subgroup.mem_inf.1 hf).1)
  have hkey : (f * (f⁻¹ * u)) ^ 5 = (f⁻¹ * u) ^ 5 := by
    rw [hfc.mul_pow, hAel.2 f (Subgroup.mem_inf.1 hf).1, one_mul]
  have hfu' : f * (f⁻¹ * u) = u := by group
  rw [hfu'] at hkey
  have hxaC : x * a ∈ C := by
    rw [hb', hu5', hkey]
    exact Subgroup.pow_mem _ hfu 5
  have haCC : a ∈ C := Subgroup.mem_inf.2 ⟨hAAs haA, haC⟩
  have hxC : x ∈ C := by
    have := Subgroup.mul_mem _ hxaC (Subgroup.inv_mem _ haCC)
    simpa using this
  obtain ⟨-, hxN, hxt⟩ := mem_centBar_iff'.1 (Subgroup.mem_inf.1 hxC).2
  exact hx1 (eq_one_of_mem_of_trivial hZ (Subgroup.mem_inf.1 hxAK).2
    (hAel.2 x (Subgroup.mem_inf.1 hxAK).1) hxN hxt)

end Zeta2

section Step4

variable {G : Type} [Group G] [Finite G]

theorem sylow_fusion' {p : ℕ} [Fact p.Prime] {R : Subgroup G} (hR : IsSylowIn p ⊤ R) {x g : G}
    (hx : x ∈ centerOf R) (hgx : g * x * g⁻¹ ∈ centerOf R) :
    ∃ n ∈ Subgroup.normalizer (R : Set G), n * x * n⁻¹ = g * x * g⁻¹ := by
  set y := g * x * g⁻¹ with hy
  have hRy : R ≤ Cg y := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.2 (comm_of_mem_centerOf hgx hr)
  have hR'y : GLBConj g⁻¹ R ≤ Cg y := by
    intro r hr
    rw [mem_gLBConj, inv_inv] at hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := comm_of_mem_centerOf hx hr
    calc r * y = g * ((g⁻¹ * r * g) * x) * g⁻¹ := by simp only [hy]; group
      _ = g * (x * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
      _ = y * r := by simp only [hy]; group
  obtain ⟨c, hcC, S, hSp, -, hRS, hcS⟩ :=
    exists_conj_le_pGroup' hRy hR.2.1 hR'y (isPGroup_conj g⁻¹ hR.2.1)
  have hSR : S = R := hR.2.2 S le_top hSp hRS
  rw [hSR] at hcS
  have hcR : GLBConj c (GLBConj g⁻¹ R) = R :=
    Subgroup.eq_of_le_of_card_ge hcS (by rw [card_conj, card_conj])
  rw [gLBConj_gLBConj] at hcR
  have hn : g⁻¹ * c ∈ Subgroup.normalizer (R : Set G) := mem_normalizer_iff_gLBConj_eq.2 hcR
  refine ⟨(g⁻¹ * c)⁻¹, Subgroup.inv_mem _ hn, ?_⟩
  have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  calc (g⁻¹ * c)⁻¹ * x * (g⁻¹ * c)⁻¹⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := by group
    _ = c⁻¹ * y * c := rfl
    _ = y := by rw [mul_assoc, ← hcy]; group

theorem conj_mem_commutator_omegaOne {p : ℕ} {R : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (R : Set G)) {y : G}
    (hy : y ∈ ⁅omegaOne p R, omegaOne p R⁆) : n * y * n⁻¹ ∈ ⁅omegaOne p R, omegaOne p R⁆ := by
  have hmap : (omegaOne p R).map (MulAut.conj n).toMonoidHom = omegaOne p R := by
    unfold omegaOne
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨z, ⟨hzR, hz⟩, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 hn z).1 hzR, ?_⟩
      show (n * z * n⁻¹) ^ p = 1
      rw [conj_pow, hz]
      group
    · rintro ⟨hxR, hx⟩
      refine ⟨n⁻¹ * x * n, ⟨?_, ?_⟩, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) x).1 hxR
        simpa using this
      · rw [show n⁻¹ * x * n = n⁻¹ * x * n⁻¹⁻¹ by group, conj_pow, hx]
        group
      · show n * (n⁻¹ * x * n) * n⁻¹ = x
        group
  have h2 : ⁅omegaOne p R, omegaOne p R⁆.map (MulAut.conj n).toMonoidHom =
      ⁅omegaOne p R, omegaOne p R⁆ := by
    rw [Subgroup.map_commutator, hmap]
  rw [← h2]
  exact ⟨y, hy, rfl⟩

theorem exists_pow_of_order_p {p : ℕ} [hp : Fact p.Prime] {z : G} {k : ℕ} (hk : z ^ (p ^ k) = 1)
    (hz1 : z ≠ 1) : ∃ n : ℕ, (z ^ n) ^ p = 1 ∧ z ^ n ≠ 1 := by
  obtain ⟨k', -, hk'⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hk)
  have hk'0 : k' ≠ 0 := by
    intro h0
    rw [h0, pow_zero, orderOf_eq_one_iff] at hk'
    exact hz1 hk'
  refine ⟨p ^ (k' - 1), ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk'0), ← hk',
      pow_orderOf_eq_one]
  · intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hk'] at h1
    have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h1
    omega

theorem ke_le_M (hI : InputFi22OneClassFive) {m : ℕ} {B M E A : Subgroup G} {a : G}
    {K : Subgroup G} (h : Cex117 G m 5 B M E A a K) (hK : IsSporType .Fi22 (barOf 5 K))
    {R : Subgroup G} (hR : IsSylowIn 5 ⊤ R) (hEAR : E ⊔ A ≤ R)
    (hZ : omegaOne 5 (centerOf R) = E ⊓ A) (hA2 : E ⊓ A = A ⊓ K)
    (h4 : ∀ e ∈ E ⊓ A, e ≠ 1 → ¬ GLAPLayer 5 (K ⊓ Cg e) ≤ M →
      e ∉ ⁅omegaOne 5 R, omegaOne 5 R⁆) :
    ∀ e ∈ E ⊓ A, e ≠ 1 → GLAPLayer 5 (K ⊓ Cg e) ≤ M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro e he he1
  by_contra hKe
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  have hA0el : IsElemAbelian 5 (E ⊓ A) := l1110_isElemAbelian_of_le hsc.1.2.1 inf_le_left
  have heW := h4 e he he1 hKe
  have hcenter : ∀ x ∈ E ⊓ A, x ∈ centerOf R := fun x hx => by
    rw [← hZ] at hx
    exact omegaOne_le' 5 _ hx
  have hnone : ∀ e' ∈ E ⊓ A, e' ≠ 1 → e' ∉ ⁅omegaOne 5 R, omegaOne 5 R⁆ := by
    intro e' he' he'1 he'W
    have heo : orderOf e = 5 := orderOf_eq_of_pow (hA0el.2 e he) he1
    have he'o : orderOf e' = 5 := orderOf_eq_of_pow (hA0el.2 e' he') he'1
    have heK : e ∈ K := (Subgroup.mem_inf.1 (hA2 ▸ he)).2
    have he'K : e' ∈ K := (Subgroup.mem_inf.1 (hA2 ▸ he')).2
    obtain ⟨k, -, hk⟩ := exists_conj_in_K hI hK heK he'K heo he'o
    obtain ⟨n, hn, hne⟩ := sylow_fusion' hR (hcenter e he) (by rw [hk]; exact hcenter e' he')
    apply heW
    have h1 := conj_mem_commutator_omegaOne (Subgroup.inv_mem _ hn) he'W
    rw [← hk, ← hne] at h1
    simpa [mul_assoc] using h1
  set W := ⁅omegaOne 5 R, omegaOne 5 R⁆ with hW
  have hWO : W ≤ omegaOne 5 R := by
    rw [hW, Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  have hWR : W ≤ R := hWO.trans (omegaOne_le' 5 R)
  have hWbot : W = ⊥ := by
    by_contra hWne
    haveI : Group.IsNilpotent ↥R := (hR.2.1).isNilpotent
    have hWn : (W.subgroupOf R).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact conj_mem_commutator_omegaOne (Subgroup.le_normalizer g.2) hn
    have hW' : W.subgroupOf R ≠ ⊥ := by
      intro hb
      apply hWne
      rw [eq_bot_iff]
      intro w hw
      have : (⟨w, hWR hw⟩ : ↥R) ∈ W.subgroupOf R := hw
      rw [hb, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hW'
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    obtain ⟨k, hk⟩ := hR.2.1 z
    have hk' : (z : G) ^ (5 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hz1' : (z : G) ≠ 1 := fun h1 => hz1 (Subtype.ext (Subtype.ext h1))
    obtain ⟨j, hj5, hj1⟩ := exists_pow_of_order_p hk' hz1'
    have hzW : (z : G) ^ j ∈ W :=
      Subgroup.pow_mem _ (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hz).1) j
    have hzc : (z : G) ∈ centerOf R := Subgroup.mem_map.2 ⟨z, (Subgroup.mem_inf.1 hz).2, rfl⟩
    have hzZ : (z : G) ^ j ∈ centerOf R := Subgroup.pow_mem _ hzc j
    have hzA0 : (z : G) ^ j ∈ E ⊓ A := by
      rw [← hZ]
      exact Subgroup.subset_closure ⟨hzZ, hj5⟩
    exact hnone _ hzA0 hj1 hzW
  have hab : omegaOne 5 R ≤ Subgroup.centralizer ((omegaOne 5 R : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hWbot
  have hEO : E ≤ omegaOne 5 R := fun x hx =>
    Subgroup.subset_closure ⟨le_sup_left.trans hEAR hx, hsc.1.2.1.2 x hx⟩
  have hAO : A ≤ omegaOne 5 R := fun x hx =>
    Subgroup.subset_closure ⟨le_sup_right.trans hEAR hx, hsc.2.2.1.2 x hx⟩
  have hEA : E ≤ Subgroup.centralizer (A : Set G) :=
    (hEO.trans hab).trans (Subgroup.centralizer_le hAO)
  have hel := isElemAbelian_sup_of_commute hsc.1.2.1 hsc.2.2.1 hEA
  have h1 : E ⊔ A = E := hsc.1.2.2 _ le_top hel le_sup_left
  have h2 : E ⊔ A = A := hsc.2.2.2 _ le_top hel le_sup_right
  have hEeq : E = A := h1.symm.trans h2
  exact h.pair.1.2.1.2 (hEeq ▸ h.pair.1.1.2)

end Step4

section Lines

variable {G : Type} [Group G] [Finite G]

abbrev conjActOn' (P U : Subgroup G) (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    MulAction P U where
  smul g u := ⟨(g : G) * u * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hPU g.2) u).1 u.2⟩
  one_smul u := by
    apply Subtype.ext
    show (1 : G) * (u : G) * (1 : G)⁻¹ = u
    simp
  mul_smul g h u := by
    apply Subtype.ext
    show ((g : G) * (h : G)) * (u : G) * ((g : G) * (h : G))⁻¹ =
      (g : G) * ((h : G) * (u : G) * (h : G)⁻¹) * (g : G)⁻¹
    group

theorem card_le_mul_inf_centralizer {p : ℕ} [hp : Fact p.Prime] {P U : Subgroup G}
    (hP : IsPGroup p P) (hU : Nat.card U = p ^ 2) (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card P ≤ p * Nat.card ↥(P ⊓ Subgroup.centralizer (U : Set G)) := by
  classical
  letI := conjActOn' P U hPU
  set S := U ⊓ Subgroup.centralizer (P : Set G) with hSdef
  have hSU : S ≤ U := inf_le_left
  have hfix : Nat.card (MulAction.fixedPoints P U) = Nat.card S := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x.1 : U) : G), ?_⟩
        invFun := fun s => ⟨⟨s.1, (Subgroup.mem_inf.1 s.2).1⟩, ?_⟩
        left_inv := fun x => ?_
        right_inv := fun s => ?_ }
    · refine Subgroup.mem_inf.2 ⟨x.1.2, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
      have h1 : h * ((x.1 : U) : G) * h⁻¹ = (x.1 : U) := congrArg Subtype.val (x.2 ⟨h, hh⟩)
      calc h * ((x.1 : U) : G) = (h * ((x.1 : U) : G) * h⁻¹) * h := by group
        _ = ((x.1 : U) : G) * h := by rw [h1]
    · intro g
      apply Subtype.ext
      have hs := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 s.2).2 (g : G) g.2
      show (g : G) * s.1 * (g : G)⁻¹ = s.1
      calc (g : G) * s.1 * (g : G)⁻¹ = (s.1 * (g : G)) * (g : G)⁻¹ := by rw [← hs]
        _ = s.1 := by group
    · apply Subtype.ext
      apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  have hmod := hP.card_modEq_card_fixedPoints U
  rw [hfix, hU] at hmod
  have hpS : p ∣ Nat.card S :=
    (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).2
      (dvd_pow_self p two_ne_zero)))
  have hSdvd : Nat.card S ∣ p ^ 2 := hU ▸ Subgroup.card_dvd_of_le hSU
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp.out).1 hSdvd
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    rw [hk] at hpS
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 hpS)
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  ·
    rw [pow_one] at hk
    obtain ⟨v₀, hv₀U, hv₀S⟩ : ∃ v₀ ∈ U, v₀ ∉ S := by
      by_contra hcon
      push Not at hcon
      have hUS : U ≤ S := fun v hv => hcon v hv
      have := Subgroup.card_le_of_le hUS
      rw [hU, hk] at this
      have h2 : p < p ^ 2 := by nlinarith [hp.out.two_le]
      omega
    set v₀' : U := ⟨v₀, hv₀U⟩ with hv₀'
    have hnotfix : ¬ ∀ g : P, g • v₀' = v₀' := by
      intro hfx
      apply hv₀S
      refine Subgroup.mem_inf.2 ⟨hv₀U, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
      have h1 : h * v₀ * h⁻¹ = v₀ := congrArg Subtype.val (hfx ⟨h, hh⟩)
      calc h * v₀ = (h * v₀ * h⁻¹) * h := by group
        _ = v₀ * h := by rw [h1]
    have hone : (1 : U) ∉ MulAction.orbit P v₀' := by
      rintro ⟨g, hg⟩
      have h1 : (g : G) * v₀ * (g : G)⁻¹ = 1 := congrArg Subtype.val hg
      have h2 : v₀ = 1 := by
        calc v₀ = (g : G)⁻¹ * ((g : G) * v₀ * (g : G)⁻¹) * (g : G) := by group
          _ = 1 := by rw [h1]; group
      exact hv₀S (h2 ▸ Subgroup.one_mem _)
    have hlt : Set.ncard (MulAction.orbit P v₀') < Set.ncard (Set.univ : Set U) := by
      apply Set.ncard_lt_ncard _ Set.finite_univ
      rw [Set.ssubset_univ_iff]
      intro heq
      apply hone
      rw [heq]
      exact Set.mem_univ _
    rw [Set.ncard_univ, hU] at hlt
    obtain ⟨n, hn⟩ := hP.card_orbit v₀'
    rw [← Nat.card_coe_set_eq, hn] at hlt
    have hn1 : n = 1 := by
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · interval_cases n
        · exfalso
          have hsing : Set.ncard (MulAction.orbit P v₀') = 1 := by
            rw [← Nat.card_coe_set_eq, hn, pow_zero]
          obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 hsing
          apply hnotfix
          intro g
          have hmem : g • v₀' ∈ MulAction.orbit P v₀' := MulAction.mem_orbit _ _
          have hmem' : v₀' ∈ MulAction.orbit P v₀' := MulAction.mem_orbit_self _
          rw [hx] at hmem hmem'
          rw [Set.mem_singleton_iff] at hmem hmem'
          rw [hmem, hmem']
        · rfl
      · exfalso
        have : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos h2
        omega
    rw [hn1, pow_one] at hn
    have hclaim : ∀ g : P, g • v₀' = v₀' → (g : G) ∈ Subgroup.centralizer (U : Set G) := by
      intro g hg
      have hgv : (g : G) * v₀ * (g : G)⁻¹ = v₀ := congrArg Subtype.val hg
      have hgv' : (g : G) * v₀ = v₀ * (g : G) := by
        calc (g : G) * v₀ = ((g : G) * v₀ * (g : G)⁻¹) * (g : G) := by group
          _ = v₀ * (g : G) := by rw [hgv]
      set T := S ⊔ Subgroup.zpowers v₀ with hT
      have hTle : T ≤ Subgroup.centralizer ({(g : G)} : Set G) := by
        refine sup_le ?_ ?_
        · intro x hx
          refine Subgroup.mem_centralizer_singleton_iff.2 ?_
          exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 _ g.2).symm
        · rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.2 hgv'.symm
      have hTU : T ≤ U := sup_le hSU ((Subgroup.zpowers_le).2 hv₀U)
      have hv₀T : v₀ ∈ T := Subgroup.mem_sup_right (Subgroup.mem_zpowers v₀)
      have hTdvd : Nat.card T ∣ p ^ 2 := hU ▸ Subgroup.card_dvd_of_le hTU
      obtain ⟨j, hj2, hj⟩ := (Nat.dvd_prime_pow hp.out).1 hTdvd
      have hpT : p ∣ Nat.card T := hk ▸ Subgroup.card_dvd_of_le (le_sup_left : S ≤ T)
      have hj2' : j = 2 := by
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with h0 | h1 | h2
        · rw [h0, pow_zero] at hj
          rw [hj] at hpT
          exact absurd (Nat.dvd_one.1 hpT) hp.out.one_lt.ne'
        · exfalso
          rw [h1, pow_one] at hj
          have hST : S = T := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hj, hk])
          exact hv₀S (hST ▸ hv₀T)
        · exact h2
      have hTeq : T = U := Subgroup.eq_of_le_of_card_ge hTU (by rw [hU, hj, hj2'])
      refine Subgroup.mem_centralizer_iff.2 (fun u hu => ?_)
      have huT : u ∈ T := by rw [hTeq]; exact hu
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hTle huT))
    have hstab : Nat.card ↥(MulAction.stabilizer P v₀') ≤
        Nat.card ↥(P ⊓ Subgroup.centralizer (U : Set G)) := by
      refine Nat.card_le_card_of_injective
        (fun x => ⟨((x.1 : P) : G), Subgroup.mem_inf.2 ⟨x.1.2,
          hclaim x.1 (MulAction.mem_stabilizer_iff.1 x.2)⟩⟩) ?_
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hxy
    have horb := Subgroup.card_mul_index (MulAction.stabilizer P v₀')
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hn] at horb
    nlinarith
  ·
    have hSeq : S = U := Subgroup.eq_of_le_of_card_ge hSU (by rw [hk, hU])
    have hPC : P ≤ Subgroup.centralizer (U : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have huS : u ∈ S := by rw [hSeq]; exact hu
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 huS).2 g hg).symm
    rw [inf_eq_left.2 hPC]
    have := Nat.card_pos (α := P)
    nlinarith [hp.out.one_lt]

theorem card_sup_zpowers {p : ℕ} [Fact p.Prime] {H : Subgroup G} {u : G} (hu : u ∉ H)
    (hup : u ^ p = 1) (hc : ∀ x ∈ H, x * u = u * x) :
    Nat.card ↥(H ⊔ Subgroup.zpowers u) = Nat.card H * p := by
  have hu1 : u ≠ 1 := fun h1 => hu (h1 ▸ H.one_mem)
  have huo : orderOf u = p := orderOf_eq_of_pow hup hu1
  have hbot : H ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxp : x ^ p = 1 := orderOf_dvd_iff_pow_eq_one.1
      ((orderOf_dvd_of_mem_zpowers (Subgroup.mem_inf.1 hx).2).trans
        (orderOf_dvd_of_pow_eq_one hup))
    have hz := zpowers_eq_of_mem (Subgroup.mem_inf.1 hx).2 hxp hx1 huo
    have : u ∈ Subgroup.zpowers x := hz ▸ Subgroup.mem_zpowers u
    exact hu (((Subgroup.zpowers_le).2 (Subgroup.mem_inf.1 hx).1) this)
  have hcomm : ∀ x ∈ H, ∀ y ∈ Subgroup.zpowers u, x * y = y * x := by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (show Commute x u from hc x hx) j).eq
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_eq_mul_of_commute hcomm hbot,
    Nat.card_zpowers, huo]

theorem absorb {p : ℕ} [hp : Fact p.Prime] {R B U : Subgroup G} (hR : IsPGroup p R)
    (hBR : B ≤ R) (hB : IsElemAbelian p B) (hB4 : p ^ 4 ≤ Nat.card B)
    (hU : IsEkIn p 2 R U) (hUn : (U.subgroupOf R).Normal) (hUB : ¬ U ≤ B) :
    p ^ 3 ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (U : Set G)) ∧
      IsElemAbelian p (U ⊔ (B ⊓ Subgroup.centralizer (U : Set G))) ∧
      U ⊔ (B ⊓ Subgroup.centralizer (U : Set G)) ≤ R ∧
      p ^ 4 ≤ Nat.card ↥(U ⊔ (B ⊓ Subgroup.centralizer (U : Set G))) := by
  set C := B ⊓ Subgroup.centralizer (U : Set G) with hCdef
  have hRN : R ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU.1).1 hUn
  have hlines := card_le_mul_inf_centralizer (hR.to_le hBR) hU.2.2 (hBR.trans hRN)
  have hC3 : p ^ 3 ≤ Nat.card C := by
    have h1 : p * p ^ 3 ≤ p * Nat.card C := by
      calc p * p ^ 3 = p ^ 4 := by ring
        _ ≤ Nat.card B := hB4
        _ ≤ p * Nat.card C := hlines
    exact Nat.le_of_mul_le_mul_left h1 hp.out.pos
  have hCel : IsElemAbelian p C := l1110_isElemAbelian_of_le hB inf_le_left
  have hUC : U ≤ Subgroup.centralizer (C : Set G) :=
    Subgroup.le_centralizer_iff.1 inf_le_right
  have hel : IsElemAbelian p (U ⊔ C) := isElemAbelian_sup_of_commute hU.2.1 hCel hUC
  refine ⟨hC3, hel, sup_le hU.1 (inf_le_left.trans hBR), ?_⟩
  obtain ⟨u, huU, huB⟩ : ∃ u ∈ U, u ∉ B := by
    by_contra h
    push Not at h
    exact hUB h
  have huC : u ∉ C := fun h => huB (Subgroup.mem_inf.1 h).1
  have hc : ∀ x ∈ C, x * u = u * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 u huU).symm
  have hcard := card_sup_zpowers huC (hU.2.1.2 u huU) hc
  calc p ^ 4 = p ^ 3 * p := by ring
    _ ≤ Nat.card C * p := Nat.mul_le_mul_right _ hC3
    _ = Nat.card ↥(C ⊔ Subgroup.zpowers u) := hcard.symm
    _ ≤ Nat.card ↥(U ⊔ C) := Subgroup.card_le_of_le
        (sup_le le_sup_right ((Subgroup.zpowers_le).2 (Subgroup.mem_sup_left huU)))

theorem chain_transfer {p k : ℕ} [Fact p.Prime] {R X B B' C : Subgroup G}
    (h : ∃ U V : Subgroup G, IsEkIn p k R U ∧ IsEkIn p k R V ∧ X ≤ Subgroup.centralizer (U : Set G) ∧
      Relation.ReflTransGen (IsKConnStep p k R) U V ∧ V ≤ Subgroup.centralizer (B : Set G))
    (hCB : C ≤ B) (hCB' : C ≤ B') (hB' : IsElemAbelian p B') (hCR : C ≤ R)
    (hCel : IsElemAbelian p C) (hCc : p ^ k ≤ Nat.card C) :
    ∃ U V : Subgroup G, IsEkIn p k R U ∧ IsEkIn p k R V ∧ X ≤ Subgroup.centralizer (U : Set G) ∧
      Relation.ReflTransGen (IsKConnStep p k R) U V ∧ V ≤ Subgroup.centralizer (B' : Set G) := by
  obtain ⟨U, V, hU, hV, hXU, hUV, hVB⟩ := h
  obtain ⟨C₀, hC₀, hC₀C⟩ := exists_isEkIn_le hCR hCel hCc
  have hs : IsKConnStep p k R V C₀ :=
    ⟨hV, hC₀, hVB.trans (Subgroup.centralizer_le (hC₀C.trans hCB))⟩
  exact ⟨U, C₀, hU, hC₀, hXU, hUV.tail hs, le_centralizer_of_le hB' (hC₀C.trans hCB') le_rfl⟩

theorem input31_7_3_holds : Input31_7_3 := by
  intro G _ _ p hp R hR U₁ U₂ hU₁ hU₂ hU₁n hU₂n hne hcomm A hA
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : p ^ 3 ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos (by norm_num)
  let Ch : Subgroup G → Prop := fun B => ∃ U V : Subgroup G, IsEkIn p 3 R U ∧ IsEkIn p 3 R V ∧
    A ≤ Subgroup.centralizer (U : Set G) ∧ Relation.ReflTransGen (IsKConnStep p 3 R) U V ∧
    V ≤ Subgroup.centralizer (B : Set G)
  have hChA : Ch A := by
    obtain ⟨A₀, hA₀, hA₀A⟩ := exists_isEkIn_le (k := 3) hA.1 hA.2.1 (by rw [hA.2.2]; exact hp3)
    exact ⟨A₀, A₀, hA₀, hA₀, le_centralizer_of_le hA.2.1 le_rfl hA₀A, Relation.ReflTransGen.refl,
      le_centralizer_of_le hA.2.1 hA₀A le_rfl⟩
  have hstep : ∀ (B U : Subgroup G), B ≤ R → IsElemAbelian p B → p ^ 4 ≤ Nat.card B → Ch B →
      IsEkIn p 2 R U → (U.subgroupOf R).Normal →
      ∃ B' : Subgroup G, B' ≤ R ∧ IsElemAbelian p B' ∧ p ^ 4 ≤ Nat.card B' ∧ Ch B' ∧ U ≤ B' ∧
        B ⊓ Subgroup.centralizer (U : Set G) ≤ B' := by
    intro B U hBR hB hB4 hChB hU hUn
    by_cases hUB : U ≤ B
    · exact ⟨B, hBR, hB, hB4, hChB, hUB, inf_le_left⟩
    · obtain ⟨hC3, hel, hle, h4⟩ := absorb hR hBR hB hB4 hU hUn hUB
      refine ⟨_, hle, hel, h4, chain_transfer hChB inf_le_left le_sup_right hel
        (inf_le_left.trans hBR) (l1110_isElemAbelian_of_le hB inf_le_left) hC3, le_sup_left,
        le_sup_right⟩
  obtain ⟨B₁, hB₁R, hB₁, hB₁4, hChB₁, hU₁B₁, -⟩ :=
    hstep A U₁ hA.1 hA.2.1 (by rw [hA.2.2]) hChA hU₁ hU₁n
  obtain ⟨B₂, -, -, -, hChB₂, hU₂B₂, hB₁B₂⟩ := hstep B₁ U₂ hB₁R hB₁ hB₁4 hChB₁ hU₂ hU₂n
  have hU₁B₂ : U₁ ≤ B₂ := le_trans (le_inf hU₁B₁ hcomm) hB₁B₂
  obtain ⟨U, V, hU, hV, hAU, hUV, hVB₂⟩ := hChB₂
  have hel12 : IsElemAbelian p (U₁ ⊔ U₂) := isElemAbelian_sup_of_commute hU₁.2.1 hU₂.2.1 hcomm
  obtain ⟨u, huU₂, huU₁⟩ : ∃ u ∈ U₂, u ∉ U₁ := by
    by_contra h
    push Not at h
    exact hne (Subgroup.eq_of_le_of_card_ge h (by rw [hU₁.2.2, hU₂.2.2])).symm
  have hc : ∀ x ∈ U₁, x * u = u * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 (hcomm hx) u huU₂).symm
  have hcard := card_sup_zpowers huU₁ (hU₂.2.1.2 u huU₂) hc
  have h12 : p ^ 3 ≤ Nat.card ↥(U₁ ⊔ U₂) := by
    calc p ^ 3 = Nat.card U₁ * p := by rw [hU₁.2.2]; ring
      _ = Nat.card ↥(U₁ ⊔ Subgroup.zpowers u) := hcard.symm
      _ ≤ Nat.card ↥(U₁ ⊔ U₂) := Subgroup.card_le_of_le
          (sup_le le_sup_left ((Subgroup.zpowers_le).2 (Subgroup.mem_sup_right huU₂)))
  refine ⟨hA.1, hA.2.1, by rw [hA.2.2]; exact hp3, sup_le hU₁.1 hU₂.1, hel12, h12,
    Or.inr ⟨U, V, hU, hV, hAU, hUV, hVB₂.trans (Subgroup.centralizer_le (sup_le hU₁B₂ hU₂B₂))⟩⟩

end Lines

@[expose] def Step12Claim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m p B M E A a K → Type117b p K →
    ∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R →
      omegaOne 5 (centerOf R) = E ⊓ A ∧
        ∃ U : Subgroup G, IsEkIn 5 2 R U ∧ (U.subgroupOf R).Normal ∧ U ≠ omegaOne 5 (centerOf R)

@[expose] def Step4Claim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m p B M E A a K → Type117b p K →
    ∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R → IsSylowIn 5 ⊤ R →
      omegaOne 5 (centerOf R) = E ⊓ A → A = (E ⊓ A) ⊔ Subgroup.zpowers a → E ⊓ A = A ⊓ K →
      IsSylowIn 5 (Cg a) A → Cg a ≤ Subgroup.normalizer (K : Set G) →
      ∀ e ∈ E ⊓ A, e ≠ 1 → ¬ GLAPLayer 5 (K ⊓ Cg e) ≤ M → e ∉ ⁅omegaOne 5 R, omegaOne 5 R⁆

@[expose] def Step56Claim : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G},
    Cex117 G m p B M E A a K → Type117b p K →
    ∀ R : Subgroup G, IsSylowIn 5 M R → E ⊔ A ≤ R → IsSylowIn 5 ⊤ R →
      omegaOne 5 (centerOf R) = E ⊓ A → A = (E ⊓ A) ⊔ Subgroup.zpowers a → E ⊓ A = A ⊓ K →
      IsSylowIn 5 (Cg a) A → Cg a ≤ Subgroup.normalizer (K : Set G) →
      Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M →
      (∀ e ∈ E ⊓ A, e ≠ 1 → GLAPLayer 5 (K ⊓ Cg e) ≤ M) → False

section Main

variable {G : Type} [Group G] [Finite G]

theorem exists_sylowIn_above'' {p : ℕ} [Fact p.Prime] {X P : Subgroup G} (hPX : P ≤ X)
    (hP : IsPGroup p P) : ∃ R : Subgroup G, IsSylowIn p X R ∧ P ≤ R := by
  have hP' : IsPGroup p ↥(P.subgroupOf X) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  refine ⟨(Q : Subgroup X).map X.subtype, isSylowIn_of_card (Subgroup.map_subtype_le _)
    (Q.isPGroup'.map X.subtype) ?_, fun x hx => ⟨⟨x, hPX hx⟩, hQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩⟩
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  exact Sylow.card_eq_multiplicity Q

end Main

theorem false_of_typeB (h119 : Lemma119Statement) (hF : Fi22Facts)
    (hI : InputFi22OneClassFive) (h12 : Step12Claim) (h4 : Step4Claim) (h56 : Step56Claim)
    {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m p B M E A a K) (hb : Type117b p K) : False := by
  obtain ⟨rfl, hfi⟩ := hb
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  obtain ⟨hrk, hA0N, -, -⟩ := h119 h
  have hEAp : IsPGroup 5 ↥(E ⊔ A) := lemma104_i_holds hS h.pair
  have hEAM : E ⊔ A ≤ M := sup_le h.pair.1.1.1.1.1 h.pair.1.2.1.1.1.1
  obtain ⟨R, hR, hEAR⟩ := exists_sylowIn_above'' hEAM hEAp
  obtain ⟨hZ, U, hU, hUn, hUZ⟩ := h12 h ⟨rfl, hfi⟩ R hR hEAR
  have hD0 := e4_subset_D0 input31_7_3_holds h hrk hR hZ hU hUn hUZ
  have hAc := card_A h hEAR hD0
  have hAeq := A_eq_sup h hrk hAc
  obtain ⟨-, hAKc, hAKel, haK, hAK⟩ := A_inf_K hF h hfi hA0N hAeq hAc
  have hCaN := cg_le_normalizer hF hfi h.hK hsc.2 hAKc hAKel hAK
  have hAp : IsPGroup 5 A := isPGroup_of_elemAb hsc.2.2.1
  have hACa : A ≤ Cg a := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hsc.2.2.1 hx h.ha.1)
  obtain ⟨As, hAs, hAAs⟩ := exists_sylowIn_above'' hACa hAp
  obtain ⟨hcen, hdec⟩ := sylow_facts hF hfi h.hK.1 hCaN hAKc hAK hAs hAAs
  have hnot : ¬ IsSylowIn 5 ⊤ As := by
    intro hAsG
    have hBel : IsElemAbelian 5 B := hS.bOne.1.1
    obtain ⟨x, -, S, hSp, -, hAsS, hBS⟩ :=
      exists_conj_le_pGroup' (le_top : As ≤ ⊤) hAs.2.1 (le_top : B ≤ ⊤) (isPGroup_of_elemAb hBel)
    have hSAs : S = As := hAsG.2.2 S le_top hSp hAsS
    rw [hSAs] at hBS
    have hc := card_le_of_le_sylow hF hfi hsc.2 h.hK.1 hAKc hAK hAs hAAs hcen hdec hBS
      (isElemAbelian_conj x hBel)
    rw [card_conj, hS.standing.card_eq hS.bOne] at hc
    have hm4 := hS.standing.four_le
    have : 5 ^ 4 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
    omega
  obtain ⟨T, hT, hAsT, hTN⟩ := exists_T hAs.2.1 hnot hcen hAAs hsc.2
  have hfus := fused hI hfi h.hK.1 hsc.2.2.1 hAKc hAK haK (orderOf_a h) hAs hT hAsT hTN
  have hRG : IsSylowIn 5 ⊤ R := (lemma104_iv_holds hS h.pair hrk hR).2.2
  have hA0el : IsElemAbelian 5 (E ⊓ A) := l1110_isElemAbelian_of_le hsc.1.2.1 inf_le_left
  have hA0R : ∀ e ∈ E ⊓ A, ∀ r ∈ R, r * e = e * r := fun e he r hr => by
    rw [← hZ] at he
    exact comm_of_mem_centerOf (omegaOne_le' 5 _ he) hr
  have hA0c : Nat.card ↥(E ⊓ A) = 5 ^ 2 := by rw [l1110_card_eq_pow_pRank hA0el, hrk]
  have hA2 : E ⊓ A = A ⊓ K :=
    A0_eq_A2 (orderOf_a h) hAs hnot hRG hA0R inf_le_right hA0c hAKc hfus
  have hAAs' : A = As :=
    A_eq_As hF hfi hsc.2 h.hK.1 hAKc hAK haK (orderOf_a h) hAs hAAs hcen hdec hfus
  have hASyl : IsSylowIn 5 (Cg a) A := by rw [hAAs']; exact hAs
  have hKe := ke_le_M hI h hfi hRG hEAR hZ hA2
    (h4 h ⟨rfl, hfi⟩ R hR hEAR hRG hZ hAeq hA2 hASyl hCaN)
  exact h56 h ⟨rfl, hfi⟩ R hR hEAR hRG hZ hAeq hA2 hASyl hCaN
    (l1110_normalizer_A0_le h.pair.1.1 hrk) hKe

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110
