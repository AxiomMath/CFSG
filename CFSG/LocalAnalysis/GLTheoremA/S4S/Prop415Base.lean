module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Lemma413
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure D3Data (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (L : Subgroup G) : Prop where
  p_eq : p = 3
  isS0 : IsS0 p B x L
  bnormL : B ≤ Subgroup.normalizer (L : Set G)
  lev : fullCoverLevel p (PQuot p L) = 3
  hd : dLevel G p = 3
  noG : ¬ IsGStar p B L
  maxRank : IsMaxRankIn p B (L ⊔ B)
  evenX : Even (Nat.card (⁅L, GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))⁆ :
    Subgroup G))
  sc : IsSC p B

theorem D3Data.of_core {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2) (hp3 : p = 3) {B : Subgroup G}
    {x : G} {L : Subgroup G} (hB : GLAIsBmax p B) (hess : IsEssential p B x)
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hlev : fullCoverLevel p (PQuot p L) = 3)
    (hd : dLevel G p = 3)
    (hev : Even (Nat.card (⁅L, GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))⁆ :
      Subgroup G))) : D3Data G p B x L := by
  have hSt : IsSTriple p B x L := ⟨hB, hess, hL⟩
  have hnoG : ¬ IsGStar p B L := by
    intro hG
    have h1 := tripleLevel_le_dLevel hSt
    unfold tripleLevel at h1
    rw [if_pos hG, hd] at h1
    omega
  have hS0 : IsS0 p B x L := by
    refine ⟨hSt, ?_⟩
    unfold tripleLevel
    rw [if_neg hnoG, hlev, hd]
    omega
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCx
  set Ox : Subgroup G := GLAPPrimeCoreOf p Cx with hOx
  have hxB : x ∈ B := hess.1
  have hBCx : B ≤ Cx := isElemAbelian_le_centralizer hB.1 hxB
  have hLCx : L ≤ Cx := hL.1
  have hXle : (⁅L, Ox⁆ : Subgroup G) ≤ Ox := by
    rw [Subgroup.commutator_le]
    intro k hk o ho
    rw [commutatorElement_def]
    have h1 : k * o * k⁻¹ ∈ Ox :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p Cx (hLCx hk)) o).1 ho
    exact Ox.mul_mem h1 (Ox.inv_mem ho)
  have hevOx : Even (Nat.card Ox) :=
    even_iff_two_dvd.2 ((even_iff_two_dvd.1 hev).trans (Subgroup.card_dvd_of_le hXle))
  have hcop : Nat.Coprime p (Nat.card Ox) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hpp Cx
  have hLBN : L ⊔ B ≤ Subgroup.normalizer (Ox : Set G) :=
    sup_le (hLCx.trans (le_normalizer_glaPPrimeCoreOf p Cx))
      (hBCx.trans (le_normalizer_glaPPrimeCoreOf p Cx))
  refine ⟨hp3, hS0, hBL, hlev, hd, hnoG, isMaxRankIn_of_even hpp hp2 hB hevOx hcop hLBN, hev, ?_⟩
  refine i326UsedAt_holds p hpp hp2 B (Subgroup.zpowers x) hB (Subgroup.zpowers_le.2 hxB)
    (mt Subgroup.zpowers_eq_bot.1 hess.2.1) ?_
  have hCz : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) = Cx := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hCz]
  exact hevOx

theorem isGStar_of_isGB {p : ℕ} {B L : Subgroup G} (h : IsGB p B L)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) : IsGStar p B L := by
  obtain ⟨E, hEB, hEel, hEc, -, hE⟩ := h
  exact ⟨E, hEB, hEel, hEc, by rwa [closureIn_eq_self hBL]⟩

theorem component_cent_of_two {p : ℕ} (hp : p.Prime) {x y : G} {L L₀ : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    (hL₀ : GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) L₀) :
    GLAPComponent p (Subgroup.centralizer
      ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) L₀ := by
  have hsn : IsSubnormal (L ⊓ Subgroup.centralizer ({y} : Set G))
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) := hL.2.1.inf _
  have hC : Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · refine le_inf (Subgroup.centralizer_le ?_) (Subgroup.centralizer_le ?_)
      · intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
      · intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    · rintro g ⟨hgx, hgy⟩
      have hxg : x ∈ Subgroup.centralizer ({g} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hgx).symm
      have hyg : y ∈ Subgroup.centralizer ({g} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hgy).symm
      have hP : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ≤
          Subgroup.centralizer ({g} : Set G) :=
        sup_le (Subgroup.zpowers_le.2 hxg) (Subgroup.zpowers_le.2 hyg)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.1 (hP hh)
  rw [hC]
  exact glaPComponent_of_isSubnormal' hp hsn hL₀

private theorem inducesInnerMod_of_centMod_mul {p : ℕ} {L : Subgroup G} {k g : G}
    (hk : k ∈ centModSubgroup p L) (hg : g ∈ L) : InducesInnerMod p L (k * g) := by
  have hkN : k ∈ Subgroup.normalizer (L : Set G) := (mem_centModSubgroup.1 hk).1
  have hkO : ∀ l ∈ L, ⁅l, k⁆ ∈ GLAPPrimeCoreOf p L := (mem_centModSubgroup.1 hk).2
  have hN : ∀ n ∈ Subgroup.normalizer (L : Set G), ∀ z ∈ GLAPPrimeCoreOf p L,
      n * z * n⁻¹ ∈ GLAPPrimeCoreOf p L := fun n hn z hz =>
    (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf p L hn) z).1 hz
  refine ⟨g, hg, fun w hw => ?_⟩
  have hk' : k⁻¹ * w * k * w⁻¹ ∈ GLAPPrimeCoreOf p L := by
    have h := hN k⁻¹ (Subgroup.inv_mem _ hkN) _ (hkO w hw)
    rw [inv_inv] at h
    convert h using 1
    simp only [commutatorElement_def]
    group
  have hu : g⁻¹ * w * g ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hg) hw) hg
  have hz : g⁻¹ * (k⁻¹ * w * k * w⁻¹) * g ∈ GLAPPrimeCoreOf p L := by
    have h := hN g⁻¹ (Subgroup.inv_mem _ (Subgroup.le_normalizer hg)) _ hk'
    rw [inv_inv] at h
    exact h
  have h := hN (g⁻¹ * w * g)⁻¹ (Subgroup.inv_mem _ (Subgroup.le_normalizer hu)) _ hz
  rw [inv_inv] at h
  have e : (g⁻¹ * w * g)⁻¹ * ((k * g)⁻¹ * w * (k * g)) =
      (g⁻¹ * w * g)⁻¹ * (g⁻¹ * (k⁻¹ * w * k * w⁻¹) * g) * (g⁻¹ * w * g) := by
    group
  rw [e]
  exact h

private theorem inducesInnerMod_of_mem_centModSubgroup {p : ℕ} {L : Subgroup G} {k : G}
    (hk : k ∈ centModSubgroup p L) : InducesInnerMod p L k := by
  have h := inducesInnerMod_of_centMod_mul hk (Subgroup.one_mem L)
  rwa [mul_one] at h

private theorem mem_center_mk_of_forall_commute {p : ℕ} {L₀ : Subgroup G} {a : G} (ha : a ∈ L₀)
    (hc : ∀ l ∈ L₀, l * a = a * l) :
    (QuotientGroup.mk (⟨a, ha⟩ : L₀) : PQuot p L₀) ∈ Subgroup.center (PQuot p L₀) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hc l hl)

private theorem eq_one_of_mem_glaPPrimeCoreOf' {p : ℕ} (hp : p.Prime) {L : Subgroup G} {a : G}
    (hO : a ∈ GLAPPrimeCoreOf p L) (hap : a ^ p = 1) : a = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hap
  have hdvd : orderOf a ∣ Nat.card ↥(GLAPPrimeCoreOf p L) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hO)
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p L)) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp L
  have hg : orderOf a ∣ Nat.gcd p (Nat.card ↥(GLAPPrimeCoreOf p L)) := Nat.dvd_gcd hord hdvd
  rw [hcop.gcd_eq_one] at hg
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hg)

private theorem not_isCyclic_of_card_nine {D : Subgroup G} (hD : IsElemAbelian 3 D)
    (hc : Nat.card D = 9) : ¬ IsCyclic D := by
  intro hcyc
  have h1 := card_le_of_isCyclic_of_pow Nat.prime_three hcyc (fun d hd => hD.2 d hd)
  omega

theorem exists_B0_elem {x y : G} {L L₀ D₀ : Subgroup G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hL : L ≤ Subgroup.centralizer ({x} : Set G))
    (hy : y ∈ Subgroup.centralizer ({x} : Set G)) (hy3 : y ^ 3 = 1)
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyout : ¬ InducesInnerMod 3 L y)
    (hx0 : CentMod 3 L x) (hL₀ : L₀ ≤ L ⊓ Subgroup.centralizer ({y} : Set G))
    (hZ0 : Subgroup.center (PQuot 3 L₀) = ⊥) (hD₀ : D₀ ≤ L₀) (hD₀el : IsElemAbelian 3 D₀)
    (hD₀c : Nat.card D₀ = 9) {z : G} (hz : z ∈ D₀) (hz1 : z ≠ 1) :
    ∃ B₀ D E : Subgroup G, IsElemAbelian 3 B₀ ∧ Nat.card B₀ = 3 ^ 4 ∧ x ∈ B₀ ∧
      D = Subgroup.zpowers x ⊔ Subgroup.zpowers y ∧ D ≤ E ∧ E ≤ B₀ ∧ ¬ IsCyclic D ∧
      IsElemAbelian 3 D ∧ Nat.card D = 9 ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      E = D ⊔ Subgroup.zpowers z ∧ B₀ ≤ Subgroup.normalizer (L₀ : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hx0' : x ∈ centModSubgroup 3 L := centMod_iff.1 hx0
  have hxL : ∀ l ∈ L, l * x = x * l := fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hL hl)
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 hy).symm
  have hxL₀ : ∀ l ∈ L₀, l * x = x * l := fun l hl => hxL l (hL₀ hl).1
  have hyL₀ : ∀ l ∈ L₀, l * y = y * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hL₀ hl).2
  have hy3z : ∀ t : ℤ, y ^ (3 * t) = 1 := by
    intro t
    have h3 : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy3
    rw [zpow_mul, h3, one_zpow]
  have hx3z : ∀ t : ℤ, x ^ (3 * t) = 1 := by
    intro t
    have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
    rw [zpow_mul, h3, one_zpow]
  have hy1 : y ≠ 1 := by
    intro h
    apply hyout
    rw [h]
    exact inducesInnerMod_of_mem_centModSubgroup (Subgroup.one_mem _)
  have hxy_not : x ∉ Subgroup.zpowers y := by
    intro hxy'
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := Subgroup.zpowers_le.2 hxy'
    have hc : Nat.card (Subgroup.zpowers x) = Nat.card (Subgroup.zpowers y) := by
      rw [card_zpowers_eq_of_pow hp3 hx3 hx1, card_zpowers_eq_of_pow hp3 hy3 hy1]
    have heq : Subgroup.zpowers x = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge hle hc.ge
    have hyc : y ∈ centModSubgroup 3 L := by
      have hymem : y ∈ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers y
      exact Subgroup.zpowers_le.2 hx0' hymem
    exact hyout (inducesInnerMod_of_mem_centModSubgroup hyc)
  obtain ⟨hDel0, hDc0⟩ := Prop53.isElemAbelian_card_sup_zpowers hp3 hxy hx3 hy3 hy1 hxy_not
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup G, D = Subgroup.zpowers x ⊔ Subgroup.zpowers y := ⟨_, rfl⟩
  rw [← hDdef] at hDel0 hDc0
  have hDel : IsElemAbelian 3 D := hDel0
  have hDc9 : Nat.card D = 9 := by rw [hDc0]; norm_num
  have hDnc : ¬ IsCyclic D := not_isCyclic_of_card_nine hDel hDc9
  have hxC₀ : x ∈ Subgroup.centralizer (D₀ : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => hxL₀ h (hD₀ hh)
  have hyC₀ : y ∈ Subgroup.centralizer (D₀ : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => hyL₀ h (hD₀ hh)
  have hDD₀ : D ≤ Subgroup.centralizer (D₀ : Set G) := by
    rw [hDdef]
    exact sup_le (Subgroup.zpowers_le.2 hxC₀) (Subgroup.zpowers_le.2 hyC₀)
  have hD₀C : D₀ ≤ Subgroup.centralizer (D : Set G) := fun d₀ hd₀ =>
    Subgroup.mem_centralizer_iff.2 fun d hd =>
      ((Subgroup.mem_centralizer_iff.1 (hDD₀ hd)) d₀ hd₀).symm
  have hD₀N : D₀ ≤ Subgroup.normalizer (D : Set G) :=
    hD₀C.trans (Subgroup.centralizer_le_normalizer _)
  have hXC : Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
    refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((show Commute y x from hxy.symm).zpow_left k).eq
  have hDD₀0 : D ⊓ D₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgD, hgD₀⟩
    rw [Subgroup.mem_bot]
    have hgD' : g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by rw [← hDdef]; exact hgD
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hXC hgD'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hgL : x ^ i * y ^ j ∈ L := (hL₀ (hD₀ hgD₀)).1
    have h3j : (3 : ℤ) ∣ j := by
      by_contra hj
      obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd Int.prime_three.irreducible).2 hj
      have hyv : (y ^ j) ^ v = y := by
        rw [← zpow_mul]
        have e : j * v = 1 + 3 * (-u) := by linear_combination huv
        rw [e, zpow_add, hy3z, mul_one, zpow_one]
      have hyj : x ^ (-i) * (x ^ i * y ^ j) = y ^ j := by
        rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
      have hxg : Commute x (x ^ i * y ^ j) :=
        Commute.mul_right ((Commute.refl x).zpow_right i) ((show Commute x y from hxy).zpow_right j)
      have hcg : Commute (x ^ (-i)) (x ^ i * y ^ j) := hxg.zpow_left (-i)
      have hyeq : (y ^ j) ^ v = x ^ (-i * v) * (x ^ i * y ^ j) ^ v := by
        calc (y ^ j) ^ v = (x ^ (-i) * (x ^ i * y ^ j)) ^ v := by rw [hyj]
          _ = (x ^ (-i)) ^ v * (x ^ i * y ^ j) ^ v := hcg.mul_zpow v
          _ = x ^ (-i * v) * (x ^ i * y ^ j) ^ v := by rw [← zpow_mul]
      have hmain := inducesInnerMod_of_centMod_mul
        (Subgroup.zpow_mem _ hx0' (-i * v)) (L.zpow_mem hgL v)
      rw [← hyeq, hyv] at hmain
      exact hyout hmain
    obtain ⟨t, rfl⟩ := h3j
    have hxiD : x ^ i ∈ D₀ := by
      have h := hgD₀
      rw [hy3z t, mul_one] at h
      exact h
    have hcen := mem_center_mk_of_forall_commute (p := 3) (hD₀ hxiD)
      (fun l hl => (Commute.zpow_right (show Commute l x from hxL₀ l hl) i).eq)
    rw [hZ0] at hcen
    have hcore : (⟨x ^ i, hD₀ hxiD⟩ : ↥L₀) ∈ GLAPPrimeCore 3 ↥L₀ :=
      (QuotientGroup.eq_one_iff _).1 (Subgroup.mem_bot.1 hcen)
    have hxi3 : (x ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    have hxi1 : x ^ i = 1 :=
      eq_one_of_mem_glaPPrimeCoreOf' hp3 (Subgroup.mem_map.2 ⟨⟨x ^ i, hD₀ hxiD⟩, hcore, rfl⟩) hxi3
    rw [hy3z t, mul_one, hxi1]
  have hDD₀card : Nat.card (D ⊔ D₀ : Subgroup G) = 3 ^ 4 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hD₀N
    rw [hDD₀0, Subgroup.card_bot, mul_one, hDc9, hD₀c] at h
    rw [h]
    norm_num
  have hB₀el : IsElemAbelian 3 (D ⊔ D₀ : Subgroup G) := isElemAbelian_sup_of_commute hDel hD₀el hDD₀
  have hxD : x ∈ D := by
    rw [hDdef]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hz3 : z ^ 3 = 1 := hD₀el.2 z hz
  have hzD₀ : Subgroup.zpowers z ≤ D₀ := Subgroup.zpowers_le.2 hz
  have hzel : IsElemAbelian 3 (Subgroup.zpowers z) := isElemAbelian_mono hD₀el hzD₀
  have hzC : z ∈ Subgroup.centralizer (D : Set G) := hD₀C hz
  have hDz : D ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G) :=
    hDD₀.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hzD₀))
  have hEel : IsElemAbelian 3 (D ⊔ Subgroup.zpowers z : Subgroup G) :=
    isElemAbelian_sup_of_commute hDel hzel hDz
  have hDz0 : D ⊓ Subgroup.zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hg' : g ∈ D ⊓ D₀ := ⟨hg.1, hzD₀ hg.2⟩
    rw [hDD₀0, Subgroup.mem_bot] at hg'
    rw [Subgroup.mem_bot]
    exact hg'
  have hzN : Subgroup.zpowers z ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ hzC)
  have hEc : Nat.card (D ⊔ Subgroup.zpowers z : Subgroup G) = 27 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hzN
    rw [hDz0, Subgroup.card_bot, mul_one, hDc9, card_zpowers_eq_of_pow hp3 hz3 hz1] at h
    rw [h]
  have hxN₀ : x ∈ Subgroup.normalizer (L₀ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hxL₀)
  have hyN₀ : y ∈ Subgroup.normalizer (L₀ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hyL₀)
  have hDN₀ : D ≤ Subgroup.normalizer (L₀ : Set G) := by
    rw [hDdef]
    exact sup_le (Subgroup.zpowers_le.2 hxN₀) (Subgroup.zpowers_le.2 hyN₀)
  have hB₀N : D ⊔ D₀ ≤ Subgroup.normalizer (L₀ : Set G) :=
    sup_le hDN₀ (hD₀.trans Subgroup.le_normalizer)
  refine ⟨D ⊔ D₀, D, D ⊔ Subgroup.zpowers z, hB₀el, hDD₀card, Subgroup.mem_sup_left hxD, hDdef,
    le_sup_left, sup_le le_sup_left (Subgroup.zpowers_le.2 ((le_sup_right : D₀ ≤ D ⊔ D₀) hz)),
    hDnc, hDel, hDc9, hEel, hEc, rfl, hB₀N⟩

theorem exists_isGStar_pump (h183 : Input18_3_4) {p : ℕ} (hp : p.Prime)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Open.IsKProper G)
    {B D E J : Subgroup G} {a : G} (hB : GLAIsBmax p B) (hDE : D ≤ E) (hEB : E ≤ B)
    (hDel : IsElemAbelian p D) (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (ha : a ∈ D) (ha1 : a ≠ 1) (hess : IsEssential p B a)
    (hJ : GLAPComponent p (Subgroup.centralizer (D : Set G)) J)
    (hlay : GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥) :
    ∃ L₁ : Subgroup G, IsSTriple p B a L₁ ∧ IsGStar p B L₁ := by
  have hK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) :=
    hkp.isKGroup _ (centralizer_ne_top_of_ne_one hsimple hnonab ha1)
  have hDa : D ≤ Subgroup.centralizer ({a} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact isElemAbelian_commute hDel hg ha
  have hCD : Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer (D : Set G) :=
    inf_eq_right.2 (Subgroup.centralizer_le (by
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact ha))
  obtain ⟨𝒞, hcomp, hsup, -, htr⟩ := h183 G _ hK p hp D hDa hDel J (by rw [hCD]; exact hJ)
  have hJsup : J ≤ ⨆ L ∈ 𝒞, L := by
    rw [hsup]
    exact le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (by rw [gLBConj_one])
  have hne : 𝒞.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hJsup
    simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot] at hJsup
    exact glaPComponent_ne_bot' hJ (le_bot_iff.1 hJsup)
  obtain ⟨L₁, hL₁⟩ := hne
  have hJK : J ≤ closureIn L₁ B := by
    refine hJsup.trans (iSup₂_le fun L hL => ?_)
    obtain ⟨e, he, rfl⟩ := htr L₁ hL₁ L hL
    rw [closureIn_eq_iSup_gLBConj L₁ B]
    exact le_iSup₂_of_le e (hEB (hDE he)) le_rfl
  refine ⟨L₁, ⟨hB, hess, hcomp L₁ hL₁⟩, E, hEB, hEel, hEc, ?_⟩
  intro hbot
  apply hlay
  have hsn : IsSubnormal (J ⊓ Subgroup.centralizer (E : Set G)) (Subgroup.centralizer (E : Set G)) := by
    have := hJ.2.1.inf (Subgroup.centralizer (E : Set G))
    rwa [inf_eq_right.2 (Subgroup.centralizer_le hDE)] at this
  have hle : GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set G)) ≤
      GLAPLayer p (closureIn L₁ B ⊓ Subgroup.centralizer (E : Set G)) := by
    unfold GLAPLayer
    refine sSup_le fun T hT => le_sSup ?_
    have hTE : GLAPComponent p (Subgroup.centralizer (E : Set G)) T :=
      glaPComponent_of_isSubnormal' hp hsn hT
    exact glaPComponent_of_le hp hTE
      (le_inf ((hT.1.trans inf_le_left).trans hJK) (hT.1.trans inf_le_right)) inf_le_right
  exact le_bot_iff.1 (hle.trans (le_of_eq hbot))

theorem not_isCyclic_of_card_sq {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hD : IsElemAbelian p D)
    (hc : Nat.card D = p ^ 2) : ¬ IsCyclic D := by
  intro hcyc
  have h1 := card_le_of_isCyclic_of_pow hp hcyc hD.2
  rw [hc] at h1
  have : p * p ≤ p := by simpa [sq] using h1
  have hp1 := hp.one_lt
  nlinarith

theorem d4_contradiction {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m)
    (hS3 : Stage3 G p) (h183 : Input18_3_4) (h264 : I264At G p) (h91 : I91At G)
    (h147 : I147At G) {B : Subgroup G} {x : G} {L : Subgroup G} (hB : GLAIsBmax p B)
    (hess : IsEssential p B x) (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hlev : fullCoverLevel p (PQuot p L) = 4)
    (hd : dLevel G p = 4) (hnoG : ¬ IsGStar p B L) (hmax : IsMaxRankIn p B (L ⊔ B))
    (hevOx : Even (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))))) :
    False := by
  have hpp : p.Prime := hp.1.1
  have hp2 : p ≠ 2 := hp.1.2.1
  have hBel : IsElemAbelian p B := hB.1
  obtain ⟨hxB, hx1, -⟩ := hess
  have hm4 : 4 ≤ GLATwoLocalRank p G := by
    rw [hp.2.1]
    exact hctx.1.four_le
  have h4 : p ^ 4 ≤ Nat.card B := by
    rw [hB.2.1]
    exact Nat.pow_le_pow_right hpp.pos hm4
  have hCx0 : Subgroup.centralizer ({x} : Set G) ≠ ⊤ :=
    centralizer_ne_top_of_ne_one hctx.1.simple hctx.1.nonabelian hx1
  have hLK : CFSG.Open.IsKGroup ↥L :=
    hctx.1.kProper.isKGroup L (fun h => hCx0 (top_le_iff.1 (h ▸ hL.1)))
  rcases h264 hpp hp2 B x L hBel hxB hx1 hL hLK hBL h4 hmax hlev with
    hGB | ⟨hp3, hB81, hCM, hcat, b, hbB, hbout⟩
  · exact hnoG (isGStar_of_isGB hGB hBL)
  · subst hp3
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBL hbB
    have hb3 : b ^ 3 = 1 := hBel.2 b hbB
    obtain ⟨y, hyLb, hy3, hyout, hL0, hcat0⟩ :=
      h91 (Subgroup.centralizer ({x} : Set G)) L b hL hcat hbN hb3 hbout
    set L₀ : Subgroup G := GLAPLayer 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) with hL₀def
    obtain ⟨⟨D₀, hD₀L, hD₀el, hD₀c⟩, hlay, hZ0⟩ :=
      h147 (L ⊓ Subgroup.centralizer ({y} : Set G)) L₀ hL0 hcat0
    have hCx : Subgroup.centralizer ({x} : Set G) ≠ ⊤ := centralizer_ne_top_of_ne_one hctx.1.simple
      hctx.1.nonabelian hx1
    have hBCx : B ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hBel hxB
    have hLbC : L ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le hL.1 (Subgroup.zpowers_le.2 (hBCx hbB))
    have hLbN : L ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set G) :=
      sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hbN)
    have hyC : y ∈ Subgroup.centralizer ({x} : Set G) := hLbC hyLb
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := hLbN hyLb
    have hx3 : x ^ 3 = 1 := hBel.2 x hxB
    have hx0 : CentMod 3 L x := (hCM x hxB).2 (Subgroup.mem_zpowers x)
    have hL₀le : L₀ ≤ L ⊓ Subgroup.centralizer ({y} : Set G) := sSup_le fun K hK => hK.1
    obtain ⟨z, hzD, hz1⟩ : ∃ z ∈ D₀, z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : D₀ = ⊥ := (Subgroup.eq_bot_iff_forall D₀).2 hcon
      rw [this, Subgroup.card_bot] at hD₀c
      omega
    obtain ⟨B₀, D, E, hB₀el, hB₀c, hxB₀, hD, hDE, hEB₀, hDnc, hDel, hDc, hEel, hEc, hEdef, hB₀L⟩ :=
      exists_B0_elem hx3 hx1 hL.1 hyC hy3 hyN hyout hx0 hL₀le hZ0 hD₀L hD₀el hD₀c hzD hz1
    have hCOx : Subgroup.centralizer ({x} : Set G) ≤
        Subgroup.normalizer (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) : Set G) :=
      le_normalizer_glaPPrimeCoreOf 3 _
    have hB₀C : B₀ ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hB₀el hxB₀
    obtain ⟨R₀, -, hR₀2, hR₀idx, hB₀R₀⟩ := exists_invariant_sylow_two hpp hp2
      (isPGroup_of_isElemAbelian hB₀el) (hB₀C.trans hCOx)
      (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hpp _)
    have hR₀1 : R₀ ≠ ⊥ := ne_bot_of_even hR₀idx hevOx
    have hB₀ : GLAIsBmax 3 B₀ := ⟨hB₀el, by rw [hB₀c, ← hB81, hB.2.1], R₀, hR₀1, hR₀2, hB₀R₀⟩
    obtain ⟨N, hN, hB₀N⟩ := GLAIsBmax.exists_maxTwoLocal hB₀
    obtain ⟨D', hD'D, hD'c, hD'ess, -⟩ := hS3.2.2.1 B₀ D N hB₀ (hDE.trans hEB₀) hDnc hN hB₀N
    obtain ⟨a, haD', ha1⟩ : ∃ a ∈ D', a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : D' = ⊥ := (Subgroup.eq_bot_iff_forall D').2 hcon
      rw [this, Subgroup.card_bot] at hD'c
      omega
    have hL₀comp : GLAPComponent 3 (Subgroup.centralizer (D : Set G)) L₀ := by
      rw [hD]
      exact component_cent_of_two hpp hL hL0
    have hlayE : GLAPLayer 3 (L₀ ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ := by
      have h1 := hlay z (hD₀L hzD) (hD₀el.2 z hzD) hz1
      have heq : L₀ ⊓ Subgroup.centralizer (E : Set G) = L₀ ⊓ Subgroup.centralizer ({z} : Set G) := by
        ext g
        simp only [Subgroup.mem_inf]
        constructor
        · rintro ⟨hg, hgE⟩
          refine ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
          have hzE : z ∈ E := by
            rw [hEdef]
            exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
          exact (Subgroup.mem_centralizer_iff.1 hgE z hzE).symm
        · rintro ⟨hg, hgz⟩
          refine ⟨hg, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
          have hgx : g ∈ Subgroup.centralizer ({x} : Set G) := hL.1 (hL₀le hg).1
          have hgy : g ∈ Subgroup.centralizer ({y} : Set G) := (hL₀le hg).2
          have hEg : E ≤ Subgroup.centralizer ({g} : Set G) := by
            rw [hEdef, hD]
            refine sup_le (sup_le ?_ ?_) ?_
            · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
                (Subgroup.mem_centralizer_singleton_iff.1 hgx).symm)
            · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
                (Subgroup.mem_centralizer_singleton_iff.1 hgy).symm)
            · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
                (Subgroup.mem_centralizer_singleton_iff.1 hgz).symm)
          exact Subgroup.mem_centralizer_singleton_iff.1 (hEg he)
      rwa [heq]
    obtain ⟨L₁, hL₁S, hL₁G⟩ := exists_isGStar_pump h183 hpp hctx.1.simple hctx.1.nonabelian
      hctx.1.kProper hB₀ hDE hEB₀ hDel hEel hEc (hD'D haD') ha1 (hD'ess a haD' ha1) hL₀comp hlayE
    have h5 := tripleLevel_le_dLevel hL₁S
    unfold tripleLevel at h5
    rw [if_pos hL₁G, hd] at h5
    omega

private theorem mem_oPPrimeP_413 {p : ℕ} {X : Subgroup G} {y : G} :
    y ∈ oPPrimeP p X ↔ ∃ h : y ∈ X,
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, h⟩ ∈ CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := by
  unfold oPPrimeP
  simp [Subgroup.mem_map]

private theorem glaPPrimeCoreOf_le_oPPrimeP_413 (p : ℕ) (X : Subgroup G) :
    GLAPPrimeCoreOf p X ≤ oPPrimeP p X := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
  unfold oPPrimeP
  refine Subgroup.mem_map.2 ⟨z, ?_, rfl⟩
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hz]
  exact Subgroup.one_mem _

theorem exists_not_centralize {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y L B R X : Subgroup G}
    (hL : GLAPComponent p Y L) (hBel : IsElemAbelian p B)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hmax : IsMaxRankIn p B (L ⊔ B))
    (hXL : X ≤ L) (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hXO : X ≤ GLAPPrimeCoreOf p L)
    (hR2 : IsPGroup 2 R) (hRX : R ≤ X) (hRidx : ¬ 2 ∣ R.relIndex X)
    (hBR : B ≤ Subgroup.normalizer (R : Set G))
    (hC : L ⊓ Subgroup.centralizer (R : Set G) ≤ oPPrimeP p L) : (⁅B, R⁆ : Subgroup G) ≠ ⊥ := by
  intro hBR0
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBC : B ≤ Subgroup.centralizer (R : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hBR0
  have hmax' : ∀ E : Subgroup G, IsElemAbelian p E → B ≤ E → E ≤ L ⊔ B → E = B :=
    fun E hE hBE hEL => (Subgroup.eq_of_le_of_card_ge hBE (hmax E hEL hE)).symm
  have hLB : L ≤ ⁅L, B⁆ := P51.le_commutator_of_maximal hp hp2 hL hBel hBL hmax'
  have hcomm : ⁅L, B⁆ ≤ oPPrimeP p L := by
    rw [Subgroup.commutator_le]
    intro l hl b hb
    obtain ⟨x, hx, hn⟩ :=
      CFSG.AGLEmbedding.exists_mem_inv_mul_mem_normalizer_of_not_dvd_index hRX hR2 hRidx (hLX hl)
    set n : G := x⁻¹ * l with hn_def
    have hl_eq : l = x * n := by rw [hn_def]; group
    have hnL : n ∈ L := L.mul_mem (L.inv_mem (hXL hx)) hl
    have hbn : b * n⁻¹ * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hBL hb) n⁻¹).1 (L.inv_mem hnL)
    have hnbL : ⁅n, b⁆ ∈ L := by
      have e1 : ⁅n, b⁆ = n * (b * n⁻¹ * b⁻¹) := by simp only [commutatorElement_def, mul_assoc]
      rw [e1]
      exact L.mul_mem hnL hbn
    have hnbC : n * b * n⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hs : n⁻¹ * r * n ∈ R := (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * r * n)).2 (by
        have e2 : n * (n⁻¹ * r * n) * n⁻¹ = r := by group
        rw [e2]
        exact hr)
      have hsb : (n⁻¹ * r * n) * b = b * (n⁻¹ * r * n) :=
        (Subgroup.mem_centralizer_iff.1 (hBC hb)) _ hs
      calc r * (n * b * n⁻¹) = n * ((n⁻¹ * r * n) * b) * n⁻¹ := by group
        _ = n * (b * (n⁻¹ * r * n)) * n⁻¹ := by rw [hsb]
        _ = n * b * n⁻¹ * r := by group
    have hnbC' : ⁅n, b⁆ ∈ Subgroup.centralizer (R : Set G) := by
      have e3 : ⁅n, b⁆ = (n * b * n⁻¹) * b⁻¹ := by simp only [commutatorElement_def]
      rw [e3]
      exact Subgroup.mul_mem _ hnbC (Subgroup.inv_mem _ (hBC hb))
    have hnb : ⁅n, b⁆ ∈ oPPrimeP p L := hC ⟨hnbL, hnbC'⟩
    have hxO : x ∈ oPPrimeP p L := glaPPrimeCoreOf_le_oPPrimeP_413 p L (hXO hx)
    have hxb : ⁅x, b⁆ ∈ oPPrimeP p L := by
      have hbx : b * x⁻¹ * b⁻¹ ∈ GLAPPrimeCoreOf p L :=
        (Subgroup.mem_normalizer_iff.1
          (normalizer_le_normalizer_glaPPrimeCoreOf p L (hBL hb)) x⁻¹).1 (Subgroup.inv_mem _ (hXO hx))
      have e4 : ⁅x, b⁆ = x * (b * x⁻¹ * b⁻¹) := by simp only [commutatorElement_def, mul_assoc]
      rw [e4]
      exact glaPPrimeCoreOf_le_oPPrimeP_413 p L (Subgroup.mul_mem _ (hXO hx) hbx)
    have e5 : ⁅l, b⁆ = x * ⁅n, b⁆ * x⁻¹ * ⁅x, b⁆ := by
      rw [hl_eq]
      simp only [commutatorElement_def]
      group
    rw [e5]
    exact (oPPrimeP p L).mul_mem ((oPPrimeP p L).mul_mem ((oPPrimeP p L).mul_mem hxO hnb)
      ((oPPrimeP p L).inv_mem hxO)) hxb
  have hLO : L ≤ oPPrimeP p L := hLB.trans hcomm
  have hQ := isQuasisimple_pQuot_of_glaPComponent hp hL
  haveI := isQuasisimple_nontrivial hQ
  haveI : Group.IsPerfect (PQuot p L) := Group.isPerfect_def.2 hQ.1
  have hall : ∀ q : PQuot p L, q ∈ CFSG.pCore p (PQuot p L) := by
    intro q
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨_, hmem⟩ := mem_oPPrimeP_413.1 (hLO hl)
    exact hmem
  have hpgrp : IsPGroup p (PQuot p L) := fun q => by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := PQuot p L)) ⟨q, hall q⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  exact Group.IsPerfect.not_isNilpotent (PQuot p L) (IsPGroup.isNilpotent hpgrp)

theorem exists_R_data {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2) (h1810 : I1810UsedAt G p)
    {B : Subgroup G} {x : G} {L : Subgroup G} (hBel : IsElemAbelian p B) (hxB : x ∈ B)
    (hYK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)))
    (hL : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hev : Even (Nat.card (⁅L, GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))⁆ :
      Subgroup G))) :
    ∃ X R : Subgroup G, X ≤ L ∧ L ≤ Subgroup.normalizer (X : Set G) ∧
      X ≤ GLAPPrimeCoreOf p L ∧ X ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) ∧
      B ≤ Subgroup.normalizer (X : Set G) ∧ Nat.Coprime p (Nat.card X) ∧ R ≤ X ∧
      IsPGroup 2 R ∧ ¬ 2 ∣ R.relIndex X ∧ B ≤ Subgroup.normalizer (R : Set G) ∧ R ≠ ⊥ ∧
      L ⊓ Subgroup.centralizer (R : Set G) ≤ oPPrimeP p L := by
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCx
  set Ox : Subgroup G := GLAPPrimeCoreOf p Cx with hOx
  have hBCx : B ≤ Cx := isElemAbelian_le_centralizer hBel hxB
  have hLCx : L ≤ Cx := hL.1
  have hOnC : Cx ≤ Subgroup.normalizer (Ox : Set G) := le_normalizer_glaPPrimeCoreOf p Cx
  have hXle : (⁅L, Ox⁆ : Subgroup G) ≤ Ox := by
    rw [Subgroup.commutator_le]
    intro k hk o ho
    rw [commutatorElement_def]
    have h1 : k * o * k⁻¹ ∈ Ox := (Subgroup.mem_normalizer_iff.1 (hOnC (hLCx hk)) o).1 ho
    exact Ox.mul_mem h1 (Ox.inv_mem ho)
  obtain ⟨hXL, hXOL, hLX, hBX, hXO', hcopX⟩ :=
    commutator_oPrime_facts hpp hL (hBCx.trans Subgroup.le_normalizer)
  rw [closureIn_eq_self hBL] at hXL hXOL hLX hBX hXO' hcopX
  obtain ⟨R, hRX, hR2, hRidx, hBR⟩ :=
    exists_invariant_sylow_two hpp hp2 (isPGroup_of_isElemAbelian hBel) hBX hcopX
  have hR1 : R ≠ ⊥ := ne_bot_of_even hRidx hev
  have hCR : L ⊓ Subgroup.centralizer (R : Set G) ≤ oPPrimeP p L := by
    have h := h1810 hpp hp2 Cx L B R hYK hL (isPGroup_of_isElemAbelian hBel)
      (hBCx.trans (Subgroup.le_normalizer)) hR1 hR2 (by rwa [closureIn_eq_self hBL])
      (by rwa [closureIn_eq_self hBL]) hBR
    rwa [closureIn_eq_self hBL] at h
  exact ⟨⁅L, Ox⁆, R, hXL, hLX, hXO', hXle, hBX, hcopX, hRX, hR2, hRidx, hBR, hR1, hCR⟩

theorem prop415_d3 {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m) (hS3 : Stage3 G p)
    (hS4o : Stage4Order G p) (h413 : Lemma413At G p) (h414 : Lemma414At G p) (h183 : Input18_3_4)
    (h1810 : I1810UsedAt G p) (h264 : I264At G p) (h91 : I91At G) (h147 : I147At G)
    {B : Subgroup G} {x : G} {L : Subgroup G} (hS0 : IsS0 p B x L)
    (hev : Even (Nat.card (⁅L, GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))⁆ :
      Subgroup G))) : D3Data G p B x L := by
  have hpp : p.Prime := hp.1.1
  have hp2 : p ≠ 2 := hp.1.2.1
  obtain ⟨hSt, hlev0⟩ := hS0
  have hS0' : IsS0 p B x L := ⟨hSt, hlev0⟩
  obtain ⟨hB, hess, hL⟩ := hSt
  have hSt' : IsSTriple p B x L := ⟨hB, hess, hL⟩
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  obtain ⟨-, -, -, -, -, -, -, h412⟩ := hS4o
  have hBel : IsElemAbelian p B := hB.1
  set Cx : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCx
  set Ox : Subgroup G := GLAPPrimeCoreOf p Cx with hOx
  have hBCx : B ≤ Cx := isElemAbelian_le_centralizer hBel hxB
  have hLCx : L ≤ Cx := hL.1
  have hOnC : Cx ≤ Subgroup.normalizer (Ox : Set G) := le_normalizer_glaPPrimeCoreOf p Cx
  have hXle : (⁅L, Ox⁆ : Subgroup G) ≤ Ox := by
    rw [Subgroup.commutator_le]
    intro k hk o ho
    rw [commutatorElement_def]
    have h1 : k * o * k⁻¹ ∈ Ox := (Subgroup.mem_normalizer_iff.1 (hOnC (hLCx hk)) o).1 ho
    exact Ox.mul_mem h1 (Ox.inv_mem ho)
  have hevOx : Even (Nat.card Ox) :=
    even_iff_two_dvd.2 ((even_iff_two_dvd.1 hev).trans (Subgroup.card_dvd_of_le hXle))
  have hcopOx : Nat.Coprime p (Nat.card Ox) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hpp Cx
  have hnoG : ¬ IsGStar p B L := by
    intro hG
    have hodd := h413 B x L hB hxB hx1 hL hG
    have hle : (⁅L, Ox⁆ : Subgroup G) ≤ ⁅closureIn L B, Ox⁆ :=
      Subgroup.commutator_mono (le_closureIn_self L B) le_rfl
    have hdvd := Subgroup.card_dvd_of_le hle
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 ((even_iff_two_dvd.1 hev).trans hdvd))
  have hlev : fullCoverLevel p (PQuot p L) = dLevel G p := fullCoverLevel_eq_dLevel hS0' hnoG
  have hd4 : dLevel G p ≤ 4 := hlev ▸ fullCoverLevel_le_four p _
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := h412 hd4 B x L hSt'
  have hmax : IsMaxRankIn p B (L ⊔ B) :=
    isMaxRankIn_of_even hpp hp2 hB hevOx hcopOx
      (sup_le (hLCx.trans hOnC) (hBCx.trans hOnC))
  have hd3 : dLevel G p ≤ 3 := by
    by_contra hcon
    have hd4' : dLevel G p = 4 := by omega
    exact d4_contradiction hctx hp hS3 h183 h264 h91 h147 hB hess hL hBL (hlev.trans hd4') hd4'
      hnoG hmax hevOx
  have hYK : CFSG.Open.IsKGroup ↥Cx :=
    hctx.1.kProper.isKGroup Cx (centralizer_ne_top_of_ne_one hctx.1.simple hctx.1.nonabelian hx1)
  obtain ⟨X, R, hXL, hLX, hXO', hXOx, hBX, hcopX, hRX, hR2, hRidx, hBR, hR1, hCR⟩ :=
    exists_R_data hpp hp2 h1810 hBel hxB hYK hL hBL hev
  have hBR' : (⁅B, R⁆ : Subgroup G) ≠ ⊥ :=
    exists_not_centralize hpp hp2 hL hBel hBL hmax hXL hLX hXO' hR2 hRX hRidx hBR hCR
  have hd2 : ¬ dLevel G p ≤ 2 := by
    intro h2
    have hRO : R ≤ Ox := hRX.trans hXOx
    exact hBR' (by
      have := h414 h2 B x R hB hxB hx1 hRO hR2 hBR
      rwa [Subgroup.commutator_comm] at this)
  have hd3' : dLevel G p = 3 := by omega
  exact D3Data.of_core hpp hp2
    (eq_three_of_k3Cover (k3Cover_of_fullCoverLevel_eq_three (hlev.trans hd3'))) hB hess hL hBL
    (hlev.trans hd3') hd3' hev

end CFSG.LocalAnalysis.GLTheoremA
