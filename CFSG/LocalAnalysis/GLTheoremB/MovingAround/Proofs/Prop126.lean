module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop115

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open scoped MatrixGroups

namespace Prop126

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem cex117_false_of_base {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hF : Prop117_cex_falseStatement) (h : Cex117Base G m p B M E A a K) : False := by
  classical
  by_cases hex : ∃ (E' A' : Subgroup G) (a' : G) (K' : Subgroup G),
      Cex117Base G m p B M E' A' a' K' ∧ ¬ NormalizesCyc M A' a'
  · obtain ⟨E', A', a', K', hb, hn⟩ := hex
    exact hF (G := G) (m := m) (p := p) (B := B) (M := M) (E := E') (A := A') (a := a')
      (K := K') { toCex117Base := hb, choice := fun _ => hn }
  · exact hF (G := G) (m := m) (p := p) (B := B) (M := M) (E := E) (A := A) (a := a)
      (K := K) { toCex117Base := h, choice := fun hx => (hex hx).elim }

theorem of_mem_inD {A₁ M : Subgroup G} {a : G} (hA₁ : inD 3 M A₁) (haA₁ : a ∈ A₁) (ha1 : a ≠ 1)
    {J : Subgroup G} (hJ : IsTwoPrimeComp (alphaOf 3 M ⊓ Subgroup.centralizer ({a} : Set G)) J) :
    IsTwoPrimeComp (Subgroup.centralizer ({a} : Set G)) J :=
  hA₁.2.clause_f rfl a haA₁ ha1 J hJ

theorem exists_order_three_central_mem {R N : Subgroup G} (hR : IsPGroup 3 ↥R)
    (hNR : ∀ r ∈ R, ∀ x ∈ N, r * x * r⁻¹ ∈ N) (hne : N ⊓ R ≠ ⊥) :
    ∃ z : G, z ∈ N ∧ z ∈ centerOf R ∧ orderOf z = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent ↥R := hR.isNilpotent
  let H : Subgroup ↥R := N.subgroupOf R
  have hHn : H.Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have := hNR (g : G) g.2 (x : G) hx
      simpa using this⟩
  have hH : H ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff]
    rintro y ⟨hyN, hyR⟩
    have hmem : (⟨y, hyR⟩ : ↥R) ∈ H := Subgroup.mem_subgroupOf.2 hyN
    rw [h0, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val hmem
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal (H := H) hH)
  have hwH : (w : ↥R) ∈ H := w.2.1
  have hwc : (w : ↥R) ∈ Subgroup.center ↥R := w.2.2
  have hw1' : (w : ↥R) ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := hR (w : ↥R)
  have hfin : IsOfFinOrder (w : ↥R) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨3 ^ k, pow_pos (by norm_num) _, hk⟩
  have hord_ne : orderOf (w : ↥R) ≠ 0 := hfin.orderOf_pos.ne'
  have hdvd : orderOf (w : ↥R) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, _, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hw1'
    exact orderOf_eq_one_iff.1 (by simpa using hj')
  have h3 : 3 ∣ orderOf (w : ↥R) := by
    rw [hj']
    exact dvd_pow_self 3 hj0
  have hz0ord : orderOf ((w : ↥R) ^ (orderOf (w : ↥R) / 3)) = 3 :=
    orderOf_pow_orderOf_div hord_ne h3
  refine ⟨((w : ↥R) ^ (orderOf (w : ↥R) / 3) : ↥R), ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact N.pow_mem (Subgroup.mem_subgroupOf.1 hwH) _
  · exact ⟨(w : ↥R) ^ (orderOf (w : ↥R) / 3), Subgroup.pow_mem _ hwc _, rfl⟩
  · rw [Subgroup.orderOf_coe, hz0ord]

theorem sylow_ne_bot_of_three_dvd {M R : Subgroup G} (hR : IsSylowIn 3 M R)
    (h3 : 3 ∣ Nat.card ↥M) : R ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hR0
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 3 h3
  have hgM : (g : G) ∈ M := g.2
  have hord : orderOf (g : G) = 3 := by rw [Subgroup.orderOf_coe, hg]
  have hP : IsPGroup 3 ↥(Subgroup.zpowers (g : G)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hord]
    norm_num
  have hle : Subgroup.zpowers (g : G) ≤ M := by
    rw [Subgroup.zpowers_le]
    exact hgM
  have heq := hR.2.2 (Subgroup.zpowers (g : G)) hle hP (by rw [hR0]; exact bot_le)
  have hg1 : (g : G) = 1 := by
    have : (g : G) ∈ Subgroup.zpowers (g : G) := Subgroup.mem_zpowers _
    rw [heq, hR0, Subgroup.mem_bot] at this
    exact this
  rw [hg1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem inf_sylow_ne_bot {M N R : Subgroup G} (hR : IsSylowIn 3 M R) (hR1 : R ≠ ⊥)
    (hNM : N ≤ M) (hN : ∀ g ∈ M, ∀ x ∈ N, g * x * g⁻¹ ∈ N) (h3 : 3 ∣ Nat.card ↥N) :
    N ⊓ R ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h0
  have hNn : (N.subgroupOf M).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have := hN (g : G) g.2 (x : G) hx
      simpa using this⟩
  obtain ⟨k, hk, hk3⟩ := Lemma113c.isSylowIn_card_index hR hR1
  let φ : ↥R →* (M ⧸ N.subgroupOf M) :=
    (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hR.1)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    rw [MonoidHom.mem_ker] at hr
    have hrN : (r : G) ∈ N := by
      have := (QuotientGroup.eq_one_iff (Subgroup.inclusion hR.1 r)).1 hr
      exact Subgroup.mem_subgroupOf.1 this
    have hrbot : (r : G) ∈ N ⊓ R := ⟨hrN, r.2⟩
    rw [h0, Subgroup.mem_bot] at hrbot
    rw [Subgroup.mem_bot]
    exact Subtype.ext hrbot
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_injective φ hφ
  have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf M)
  have hNcard : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  rw [hNcard] at hL
  have hMR : Nat.card ↥M = Nat.card ↥R * k := hk
  have hRpos : 0 < Nat.card ↥R := Nat.card_pos
  have hkey : Nat.card ↥R * k = Nat.card ↥R * (t * Nat.card ↥N) := by
    rw [← hMR, hL, ht]
    ring
  have hkN : k = t * Nat.card ↥N := Nat.eq_of_mul_eq_mul_left hRpos hkey
  apply hk3
  rw [hkN]
  exact Dvd.dvd.mul_left h3 t

theorem an_branch_false {m : ℕ} {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A)
    (hF : Prop117_cex_falseStatement) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnD : ∀ A₁ : Subgroup G, inD 3 M A₁ → a ∉ A₁)
    {K : Subgroup G} (hK : GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) K) (hKM : ¬ K ≤ M)
    {n : ℕ} (hn : IsAltType n (barOf 3 K)) (hn7 : 7 < n) (hn3 : n % 3 = 1)
    (hdiv : 3 ^ CFSG.Open.pRank 3 (E ⊓ A) ∣ n - 7) : False := by
  obtain ⟨k, hk⟩ := hdiv
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk
      omega
    · exact h0
  have hgt : 3 ^ CFSG.Open.pRank 3 (E ⊓ A) < n := by
    have h1 : 3 ^ CFSG.Open.pRank 3 (E ⊓ A) ≤ 3 ^ CFSG.Open.pRank 3 (E ⊓ A) * k :=
      Nat.le_mul_of_pos_right _ hk1
    omega
  have hnot3 : ¬ 3 ∣ n := by omega
  exact cex117_false_of_base hF
    { toSec11 := h, ha := ⟨ha, ha1⟩, hK := hK,
      ht := Or.inl ⟨n, hn, hgt, hnot3⟩, notM := hKM,
      notD := fun ⟨A₁, hA₁, haA₁⟩ => hnD A₁ hA₁ haA₁ }

@[expose] def autFixSub {K : Type} [Group K] (x : MulAut K) : Subgroup K where
  carrier := {k | x k = k}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

@[expose] def Input14_15_3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → CFSG.Open.IsKGroup K →
    GLAPPrimeCore 3 K = ⊥ → ∀ x : MulAut K, orderOf x = 3 →
      ∀ J₁ : Subgroup K, GLAPComponent 3 (autFixSub x) J₁ →
        (IsAltType 7 (barOf 3 J₁) ∨ IsHatSeven (barOf 3 J₁)) →
          IsSporType .He (K ⧸ Subgroup.center K) ∨
            ∃ k : ℕ, 1 ≤ k ∧ IsAltType (7 + 3 * k) (K ⧸ Subgroup.center K)

@[expose] def Input18_3_2 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → ∀ x y : G, orderOf x = p → orderOf y = p →
      x * y = y * x → ∀ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x, y} : Set G)) J →
        GLAPComponent p ((⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({y} : Set G)), GLBConj g J) ⊓
          Subgroup.centralizer ({x} : Set G)) J

@[expose] def jstar3 {G : Type} [Group G] (a : G) (J : Subgroup G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)), GLBConj g J

theorem jstar3_dichotomy {G : Type} [Group G] [Finite G] (hsimp : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hkp : CFSG.Open.IsKProper G)
    (hI1 : Prop115.Input18_3Gen) (hI2 : Input18_3_2) {z a : G} (hz : orderOf z = 3)
    (ha : orderOf a = 3) (hza : z * a = a * z) {J₀ : Subgroup G}
    (hJ₀ : GLAPComponent 3 (Subgroup.centralizer ({z, a} : Set G)) J₀) :
    (∃ L : Subgroup G, GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) L ∧ jstar3 a J₀ = L ∧
        GLBConj z L = L ∧ GLAPComponent 3 (jstar3 a J₀ ⊓ Subgroup.centralizer ({z} : Set G)) J₀) ∨
      (∃ L : ZMod 3 → Subgroup G, (∀ i, GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) (L i)) ∧
        Function.Injective L ∧ (∀ i, GLBConj z (L i) = L (i + 1)) ∧ jstar3 a J₀ = ⨆ i, L i ∧
          GLAPComponent 3 (jstar3 a J₀ ⊓ Subgroup.centralizer ({z} : Set G)) J₀) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 := hI2 3 Nat.prime_three (by decide) G hsimp hnab hkp z a hz ha hza J₀ hJ₀
  have h1 := hI1 3 Nat.prime_three (by decide) G hsimp hnab hkp z a hz ha hza J₀ hJ₀
  rcases h1 with ⟨L, hL, hJL, hzL⟩ | ⟨L, hL, hLinj, hLcyc, hJL⟩
  · left
    exact ⟨L, hL, hJL, hzL, h2⟩
  · right
    exact ⟨L, hL, hLinj, hLcyc, hJL, h2⟩

theorem glaPComponent_up {p : ℕ} (hp : p.Prime) {T H K : Subgroup G}
    (hK : GLAPComponent p H K) (hHT : IsSubnormal H T) : GLAPComponent p T K := by
  obtain ⟨hKH, hsnKH, hcompH, hminH⟩ := hK
  have hHT' : H ≤ T := isSubnormal_le' hHT
  have hKT : IsSubnormal K T := isSubnormal_trans' hsnKH hHT
  have hKT' : K ≤ T := hKH.trans hHT'
  have hcore : H ⊓ GLAPPrimeCoreOf p T = GLAPPrimeCoreOf p H :=
    glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hHT
  have key : ∀ J K' : Subgroup G, J ≤ H → K' ≤ H → barX p T J ≤ barX p T K' →
      barX p H J ≤ barX p H K' := by
    intro J K' hJH hK'H hle
    refine barX_le_of_forall hK'H (fun j hj => ?_)
    obtain ⟨k, hk, hkj⟩ := exists_of_barX_le (X := T) (J := K') (K := J) hle hj (hHT' (hJH hj))
    refine ⟨k, hk, ?_⟩
    rw [← hcore]
    exact ⟨H.mul_mem (H.inv_mem (hK'H hk)) (hJH hj), hkj⟩
  refine ⟨hKT', hKT, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := T) p hKT
    rwa [barX_self] at this
  · have e : ↥(barX p T K) ≃* ↥(barX p H K) :=
      (quotEquivBarX hp hKT' hKT).symm.trans (quotEquivBarX hp hKH hsnKH)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hcompH.2.2
  · intro J hJK hJsnT heq
    have hJH : J ≤ H := hJK.le.trans hKH
    have hJsnH : IsSubnormal J H := isSubnormal_of_le_of_le hJsnT hJH hHT'
    exact hminH J hJK hJsnH (le_antisymm (key J K hJH hKH heq.le) (key K J hKH hJH heq.ge))

end Helpers

end Prop126

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
