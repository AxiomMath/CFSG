module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63ArrowAux
public import CFSG.LocalAnalysis.ComponentClassification.SubgroupFixedInvolution
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G]

private theorem sec63P_elem_sup_ge_four [Finite G] {a b : G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hcomm : a * b = b * a) (h : a ∉ Subgroup.zpowers b) :
    CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∧
      4 ≤ Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  have ha2 : a ^ 2 = 1 := by simpa [ha] using pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := by simpa [hb] using pow_orderOf_eq_one b
  have hElem : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers (p := 2) ha2)
      (CFSG.Open.isElemAbelian_zpowers (p := 2) hb2) ?_
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute a b from hcomm).zpow_zpow m n).eq
  have hne : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) ≠ 2 := by
    intro h2
    have heq : Subgroup.zpowers b = Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h2, Nat.card_zpowers, hb])
    exact h (by rw [heq]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  exact ⟨hElem,
    sec63_card_ge_four hElem.isPGroup hb (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) hne⟩

private theorem sec63P_exists_elem_two_sq_of_mem [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 S) (hSrank : 2 ≤ CFSG.Open.pRank 2 S) {e : G}
    (he : orderOf e = 2) (heS : e ∈ S) :
    ∃ E : Subgroup G, E ≤ S ∧ e ∈ E ∧ CFSG.Open.IsElemAbelian 2 E ∧ 4 ≤ Nat.card E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₁, hE₁S, hE₁el, hE₁card⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := 2) Nat.prime_two hSrank
  have he2 : e ^ 2 = 1 := by simpa [he] using pow_orderOf_eq_one e
  have he1 : e ≠ 1 := by
    intro h
    rw [h, orderOf_one] at he
    exact absurd he (by norm_num)
  by_cases hcen : ∀ x ∈ S, x * e = e * x
  ·
    have hnot : ¬ E₁ ≤ Subgroup.zpowers e := by
      intro hsub
      have hcard := Subgroup.card_le_of_le hsub
      rw [hE₁card, Nat.card_zpowers, he] at hcard
      norm_num at hcard
    obtain ⟨t, htE₁, ht⟩ := Set.not_subset.1 hnot
    have ht2 : t ^ 2 = 1 := hE₁el.2 t htE₁
    have ht1 : t ≠ 1 := fun h => ht (by rw [h]; exact Subgroup.one_mem _)
    have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
    have het : t * e = e * t := hcen t (hE₁S htE₁)
    obtain ⟨hElem, hcard4⟩ := sec63P_elem_sup_ge_four (a := t) (b := e) hto he het ht
    exact ⟨_, sup_le (Subgroup.zpowers_le.mpr (hE₁S htE₁)) (Subgroup.zpowers_le.mpr heS),
      Subgroup.mem_sup_right (Subgroup.mem_zpowers e), hElem, hcard4⟩
  ·
    push Not at hcen
    obtain ⟨x, hxS, hxe⟩ := hcen
    haveI : Nontrivial S :=
      ⟨⟨⟨e, heS⟩, 1, fun h => he1 (congrArg (fun z : ↥S => (z : G)) h)⟩⟩
    haveI : Nontrivial (Subgroup.center (S : Subgroup G)) := hS.center_nontrivial
    have hZpg : IsPGroup 2 (Subgroup.center (S : Subgroup G)) :=
      hS.to_subgroup (Subgroup.center (S : Subgroup G))
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZpg
    have hn0 : n ≠ 0 := by
      rintro rfl
      have h1 : 1 < Nat.card (Subgroup.center (S : Subgroup G)) :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      rw [hn, pow_zero] at h1
      exact lt_irrefl _ h1
    have hdvd : 2 ∣ Nat.card (Subgroup.center (S : Subgroup G)) := by
      rw [hn]; exact dvd_pow_self 2 hn0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    set ze : G := ((z : (S : Subgroup G)) : G) with hze
    have hzeo : orderOf ze = 2 := by
      rw [hze, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hz
    have hzeS : ze ∈ S := by rw [hze]; exact (z : (S : Subgroup G)).2
    have hzc : ∀ y ∈ S, y * ze = ze * y := fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩)
    have heze : e ∉ Subgroup.zpowers ze := by
      intro hmem
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
      apply hxe
      rw [← hm]
      exact ((Commute.zpow_right (show Commute x ze from hzc x hxS) m).eq)
    obtain ⟨hElem, hcard4⟩ := sec63P_elem_sup_ge_four (a := e) (b := ze) he hzeo
      (hzc e heS) heze
    exact ⟨_, sup_le (Subgroup.zpowers_le.mpr heS) (Subgroup.zpowers_le.mpr hzeS),
      Subgroup.mem_sup_left (Subgroup.mem_zpowers e), hElem, hcard4⟩

private theorem sec63P_smul_conjAct (J : Subgroup G) (g : G) :
    ConjAct.toConjAct g • J = CFSG.conjugate J g⁻¹ := by
  rw [Subgroup.pointwise_smul_def, CFSG.conjugate, inv_inv]
  rfl

theorem sec63P_rank_ge_three [Finite G] {E : Subgroup G} {v : G}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : 4 ≤ Nat.card E) (hv : orderOf v = 2)
    (hcomm : ∀ e ∈ E, e * v = v * e) (hvE : v ∉ E) :
    CFSG.Open.IsElemAbelian 2 (E ⊔ zpowers v) ∧ 3 ≤ CFSG.Open.pRank 2 (E ⊔ zpowers v) := by
  have hv2 : v ^ 2 = 1 := by simpa [hv] using pow_orderOf_eq_one v
  have hzv : Subgroup.zpowers v ≤ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr (fun e he => hcomm e he)
  have hAB : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers v, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hzv hb) a ha
  have hEsup : CFSG.Open.IsElemAbelian 2 (E ⊔ Subgroup.zpowers v) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE
      (CFSG.Open.isElemAbelian_zpowers (p := 2) hv2) hAB
  have hlt : E < E ⊔ Subgroup.zpowers v :=
    lt_of_le_of_ne le_sup_left fun hEq =>
      hvE (hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  obtain ⟨m, hEm⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card Nat.prime_two hE
  obtain ⟨k, hEk⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card Nat.prime_two hEsup
  have hm2 : 2 ≤ m := by
    have h4 : (2 : ℕ) ^ 2 ≤ 2 ^ m := by
      rw [← hEm]
      simpa using hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  have hmk : m < k := by
    have hcl := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hlt
    rw [hEm, hEk] at hcl
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hcl
  have hk3 : 3 ≤ k := by omega
  refine ⟨hEsup, ?_⟩
  exact hk3.trans
    (CFSG.SectionRank.le_pRank (p := 2) (by norm_num) le_rfl hEsup hEk)

theorem sec63P_exists_E4 [Finite G] {H : Subgroup G} (hH : 2 ≤ CFSG.Open.pRank 2 H) {e : G}
    (he : orderOf e = 2) (heH : e ∈ H) :
    ∃ E : Subgroup G, E ≤ H ∧ e ∈ E ∧ CFSG.Open.IsElemAbelian 2 E ∧ 4 ≤ Nat.card E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Subgroup ↥H) :=
    Finite.of_injective (fun K : Subgroup ↥H => (K : Set ↥H)) SetLike.coe_injective
  haveI : Finite (Sylow 2 ↥H) :=
    Finite.of_injective (fun P : Sylow 2 ↥H => (P : Subgroup ↥H)) (fun _ _ h => Sylow.ext h)
  let j : ↥H := ⟨e, heH⟩
  have hj : orderOf j = 2 := (Subgroup.orderOf_mk e heH).trans he
  have hranktop : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥H) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 2) H]
    exact hH
  obtain ⟨E₀, _, hE₀el, hE₀card⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := 2) Nat.prime_two
      (H := (⊤ : Subgroup ↥H)) (k := 2) hranktop
  have hE₀p : IsPGroup 2 E₀ := IsPGroup.of_card (n := 2) hE₀card
  obtain ⟨P₀, hP₀⟩ := hE₀p.exists_le_sylow
  have hjp : IsPGroup 2 (Subgroup.zpowers j) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hj, pow_one])
  obtain ⟨P₁, hP₁⟩ := hjp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H P₀ P₁
  set E₁ : Subgroup ↥H := E₀.map (MulAut.conj g).toMonoidHom with hE₁
  have hE₁P : E₁ ≤ (P₁ : Subgroup ↥H) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (P₀ : Subgroup ↥H) (hP₀ hy)
  have hE₁el : CFSG.Open.IsElemAbelian 2 E₁ := CFSG.SectionRank.isElemAbelian_map hE₀el _
  have hE₁card : Nat.card E₁ = 2 ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀card]
  have hjP : j ∈ (P₁ : Subgroup ↥H) := hP₁ (Subgroup.mem_zpowers j)
  have hrankP : 2 ≤ CFSG.Open.pRank 2 (P₁ : Subgroup ↥H) :=
    CFSG.SectionRank.le_pRank (p := 2) (by norm_num) hE₁P hE₁el hE₁card
  obtain ⟨F, _, hjF, hFel, hFcard⟩ :=
    sec63P_exists_elem_two_sq_of_mem (G := ↥H) (S := (P₁ : Subgroup ↥H))
      P₁.isPGroup' hrankP hj hjP
  refine ⟨F.map H.subtype, Subgroup.map_subtype_le F, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨j, hjF, rfl⟩
  · exact CFSG.SectionRank.isElemAbelian_map hFel H.subtype
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hFcard

theorem sec63P_not_quot_z4 {R K : Subgroup G}
    (hR : R = Subgroup.closure {r : G | r ∈ R ∧ orderOf r = 2}) :
    ¬ QuotEquivTo R K (Multiplicative (ZMod 4)) := by
  rintro ⟨φ, hsurj, -⟩
  let S₂ : Subgroup (Multiplicative (ZMod 4)) := (powMonoidHom 2).ker
  have hS₂ : ∀ z, z ∈ S₂ ↔ z ^ 2 = 1 := fun z => MonoidHom.mem_ker
  have hgen : {r : G | r ∈ R ∧ orderOf r = 2} ⊆ (S₂.comap φ).map R.subtype := by
    rintro r ⟨hrR, hr2⟩
    have hr2' : r ^ 2 = 1 := by simpa [hr2] using pow_orderOf_eq_one r
    refine Subgroup.mem_map.mpr ⟨⟨r, hrR⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [hS₂, ← map_pow, show (⟨r, hrR⟩ : ↥R) ^ 2 = 1 from Subtype.ext hr2', map_one]
  have hRle : R ≤ (S₂.comap φ).map R.subtype := by
    have hcl : Subgroup.closure {r : G | r ∈ R ∧ orderOf r = 2} ≤
        (S₂.comap φ).map R.subtype :=
      (Subgroup.closure_le (K := (S₂.comap φ).map R.subtype)).mpr hgen
    exact hR.le.trans hcl
  have htop : (⊤ : Subgroup ↥R) ≤ S₂.comap φ := by
    intro x _
    have hx : (x : G) ∈ (S₂.comap φ).map R.subtype := hRle x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  have h2 : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 ≠ 1 := by decide
  obtain ⟨x, hx⟩ := hsurj (Multiplicative.ofAdd (1 : ZMod 4))
  have hmem : Multiplicative.ofAdd (1 : ZMod 4) ∈ S₂ := by
    rw [← hx]
    exact Subgroup.mem_comap.mp (htop (Subgroup.mem_top x))
  exact h2 ((hS₂ _).mp hmem)

theorem sec63P_relIndex_le_two [Finite G] {R J K : Subgroup G}
    (h : ∀ g ∈ R, CFSG.conjugate J g = J ∨ CFSG.conjugate J g = K) :
    (normalizer (J : Set G)).relIndex R ≤ 2 := by
  classical
  letI : MulAction ↥R (Subgroup G) :=
    MulAction.compHom (Subgroup G) (ConjAct.toConjAct.toMonoidHom.comp R.subtype)
  have hstab : MulAction.stabilizer ↥R J = (normalizer (J : Set G)).subgroupOf R := by
    ext r
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hr
      have hr' : CFSG.conjugate J (r : G)⁻¹ = J := by
        change ConjAct.toConjAct (r : G) • J = J at hr
        rwa [sec63P_smul_conjAct] at hr
      have hmem : (r : G)⁻¹ ∈ normalizer (J : Set G) := (sec63P_conjugate_eq_iff).mp hr'
      simpa using (normalizer (J : Set G)).inv_mem hmem
    · intro hr
      have hmem : (r : G)⁻¹ ∈ normalizer (J : Set G) := (normalizer (J : Set G)).inv_mem hr
      have hr' : CFSG.conjugate J (r : G)⁻¹ = J := (sec63P_conjugate_eq_iff).mpr hmem
      show r • J = J
      change ConjAct.toConjAct (r : G) • J = J
      rwa [sec63P_smul_conjAct]
  have horb : MulAction.orbit ↥R J ⊆ ({J, K} : Set (Subgroup G)) := by
    rintro L ⟨r, rfl⟩
    change ConjAct.toConjAct (r : G) • J ∈ ({J, K} : Set (Subgroup G))
    rw [sec63P_smul_conjAct]
    rcases h (r : G)⁻¹ (R.inv_mem r.2) with hJ | hK
    · exact Or.inl hJ
    · exact Or.inr hK
  have hindex := MulAction.index_stabilizer ↥R J
  rw [hstab] at hindex
  rw [Subgroup.relIndex, hindex]
  calc (MulAction.orbit ↥R J).ncard ≤ ({J, K} : Set (Subgroup G)).ncard :=
        Set.ncard_le_ncard horb
    _ ≤ 2 := by
        have h2 := Set.ncard_insert_le J ({K} : Set (Subgroup G))
        simpa [Set.ncard_singleton] using h2

theorem sec63P_card_inf_ge_four [Finite G] {R H : Subgroup G} (h8 : Nat.card R = 8)
    (hrel : H.relIndex R ≤ 2) : 4 ≤ Nat.card ↥(R ⊓ H) := by
  have hmul := Subgroup.relIndex_mul_card (H := H) (K := R)
  rw [h8, inf_comm] at hmul
  by_contra hlt
  push Not at hlt
  have hb := Nat.mul_le_mul hrel (show Nat.card ↥(R ⊓ H) ≤ 3 by omega)
  omega

theorem sec63P_mem_sup_zpowers {a c x : G} (ha : orderOf a = 2) (hc : orderOf c = 2)
    (hac : a * c = c * a) (hx : x ∈ zpowers a ⊔ zpowers c) :
    x = 1 ∨ x = a ∨ x = c ∨ x = a * c := by
  classical
  have hcomm : ∀ u ∈ zpowers a, ∀ v ∈ zpowers c, u * v = v * u := by
    intro u hu v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute a c from hac).zpow_zpow m n).eq
  obtain ⟨u, hu, v, hv, rfl⟩ := sec63P_mem_sup_of_comm hcomm hx
  have hpow : ∀ {d : G}, orderOf d = 2 → ∀ w ∈ zpowers d, w = 1 ∨ w = d := by
    intro d hd w hw
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hm2 : m % (orderOf d : ℤ) = 0 ∨ m % (orderOf d : ℤ) = 1 := by
      simpa [hd] using Int.emod_two_eq_zero_or_one m
    have h := zpow_mod_orderOf d m
    rcases hm2 with h0 | h1
    · left; rw [← hm, ← h]; simp [h0]
    · right; rw [← hm, ← h]; simp [h1]
  rcases hpow ha u hu with rfl | rfl <;> rcases hpow hc v hv with rfl | rfl <;>
    simp [mul_one, one_mul]

theorem sec63P_exists_fixed_involution [Finite G] {J : Subgroup G} {y : G} (hy : orderOf y = 2)
    (hJ : y ∈ normalizer (J : Set G)) (heven : Even (Nat.card J)) :
    ∃ e ∈ J, orderOf e = 2 ∧ e * y = y * e := by
  obtain ⟨e, heJ, heo, hcen⟩ :=
    CFSG.ComponentClassification.SubgroupFixedInvolution.involution_normalizing J heven y hy hJ
  exact ⟨e, heJ, heo, Subgroup.mem_centralizer_singleton_iff.mp hcen⟩

end CFSG.OddStandard.SmallF3.Omega
