module

public import CFSG.CGT.PushingUpLit.E3A.ThreeBase
public import CFSG.CGT.PushingUpLit.E3A.Prime
public import CFSG.CGT.Timmesfeld75.ListWCAlt

public section

namespace CFSG.CGT.PushingUpLit.E3A

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit.SolK CFSG.RankThree.PartOne.SolD3
  CFSG.CGT.Timmesfeld75
open CFSG.Assembly (pCoreOf)

theorem perm3_eq_one_of_pow_seven {α : Type} [Finite α] (hα : Nat.card α = 3)
    (σ : Equiv.Perm α) (h : σ ^ 7 = 1) : σ = 1 := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hc3 : Fintype.card α = 3 := by rw [← Nat.card_eq_fintype_card]; exact hα
  have hcard : Nat.card (Equiv.Perm α) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hc3]
    rfl
  have h1 : orderOf σ ∣ 7 := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf σ ∣ 6 := hcard ▸ orderOf_dvd_natCard σ
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 7 6) h1 h2)

theorem orderOf_ne_twenty_one {k : ℕ} (hk : k ≤ 9) (σ : Equiv.Perm (Fin k)) :
    orderOf σ ≠ 21 := by
  intro h
  have hl := Equiv.Perm.lcm_cycleType σ
  have hs := Equiv.Perm.sum_cycleType_le σ
  rw [Fintype.card_fin] at hs
  rw [h] at hl
  have hmem : ∀ x ∈ σ.cycleType, x = 1 ∨ x = 3 ∨ x = 7 := by
    intro x hx
    have h1 : x ∣ 21 := hl ▸ Multiset.dvd_lcm hx
    have h2 : x ≤ 9 := (Multiset.le_sum_of_mem hx).trans (hs.trans hk)
    interval_cases x <;> omega
  have h7 : 7 ∈ σ.cycleType := by
    by_contra h7
    have h3 : σ.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.2 fun x hx => by
      rcases hmem x hx with rfl | rfl | rfl
      · exact one_dvd _
      · exact dvd_rfl
      · exact absurd hx h7
    rw [hl] at h3
    omega
  have h3 : 3 ∈ σ.cycleType := by
    by_contra h3
    have h4 : σ.cycleType.lcm ∣ 7 := Multiset.lcm_dvd.2 fun x hx => by
      rcases hmem x hx with rfl | rfl | rfl
      · exact one_dvd _
      · exact absurd hx h3
      · exact dvd_rfl
    rw [hl] at h4
    omega
  obtain ⟨s, hs3⟩ := Multiset.exists_cons_of_mem h3
  have h7' : 7 ∈ s := by
    have : 7 ∈ (3 ::ₘ s) := hs3 ▸ h7
    rcases Multiset.mem_cons.1 this with h | h
    · omega
    · exact h
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h7'
  have hsum : σ.cycleType.sum = 3 + (7 + t.sum) := by
    rw [hs3, ht]
    simp
  omega

theorem card_sub_one_dvd_card_normalizer {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (hR : 1 < Nat.card R)
    (htrans : ∀ x ∈ R, x ≠ 1 → ∀ y ∈ R, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (R : Set G), g * x * g⁻¹ = y) :
    Nat.card R - 1 ∣ Nat.card (Subgroup.normalizer (R : Set G)) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (R : Set G) with hN
  obtain ⟨r, hrR, hr1⟩ : ∃ r ∈ R, r ≠ 1 := by
    by_contra h
    push Not at h
    have : R = ⊥ := (Subgroup.eq_bot_iff_forall R).2 h
    rw [this, Subgroup.card_bot] at hR
    omega
  let _ : MulAction N G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp N.subtype)
  have hsmul : ∀ (n : N) (x : G), n • x = (n : G) * x * (n : G)⁻¹ := fun n x => rfl
  have horb : MulAction.orbit N r = {y | y ∈ R ∧ y ≠ 1} := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      show n • r ∈ {y | y ∈ R ∧ y ≠ 1}
      rw [hsmul]
      refine ⟨(Subgroup.mem_normalizer_iff.1 n.2 r).1 hrR, fun h => hr1 ?_⟩
      have := congrArg (fun z => (n : G)⁻¹ * z * (n : G)) h
      simpa [mul_assoc] using this
    · rintro ⟨hyR, hy1⟩
      obtain ⟨g, hg, hgy⟩ := htrans r hrR hr1 y hyR hy1
      exact ⟨⟨g, hg⟩, by show (⟨g, hg⟩ : N) • r = y; rw [hsmul]; exact hgy⟩
  have hcard_orb : Nat.card (MulAction.orbit N r) = Nat.card R - 1 := by
    rw [horb]
    exact card_ne_one R
  have hprod := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N r)
  rw [Nat.card_prod] at hprod
  rw [← hprod, ← hcard_orb]
  exact dvd_mul_right _ _

section Block

variable {G : Type} [Group G] [Finite G] {R X : Subgroup G} {a : G}

omit [Finite G] in
theorem false_of_alt_small {k : ℕ} (hk6 : 6 ≤ k) (hk7 : k ≤ 7)
    (e : G ≃* alternatingGroup (Fin k)) (hR : Nat.card R = 4) (hb : Blk3 X a)
    (hXC : X ≤ Subgroup.centralizer (R : Set G)) : False := by
  obtain ⟨m, hm, hcard⟩ := exists_card_alt_eq_eight_mul hk6 hk7
  have hcomm : ∀ (w : ↥(pCoreOf 2 X)) (r : ↥R),
      Commute ((pCoreOf 2 X).subtype w) (R.subtype r) := fun w r =>
    (Subgroup.mem_centralizer_iff.1 (hXC (pCoreOf_le_self X w.2)) r r.2).symm
  let φ : ↥(pCoreOf 2 X) × ↥R →* G :=
    MonoidHom.noncommCoprod (pCoreOf 2 X).subtype R.subtype hcomm
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨w, r⟩ h
    have h1 : (w : G) * (r : G) = 1 := by simpa [φ] using h
    have hwR : (w : G) ∈ R := by
      have : (w : G) = (r : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact R.inv_mem r.2
    have hw1 : (w : G) = 1 := W_inf_R_eq_one hb hXC w.2 hwR
    have hr1 : (r : G) = 1 := by
      rw [hw1, one_mul] at h1
      exact h1
    exact Prod.ext (Subtype.ext hw1) (Subtype.ext hr1)
  have hdvd := Subgroup.card_dvd_of_injective φ hinj
  rw [Nat.card_prod, hb.card, hR, Nat.card_congr e.toEquiv, hcard] at hdvd
  obtain ⟨j, hj⟩ := hm
  omega

theorem false_of_alt_big {k : ℕ} (hk9 : k ≤ 9)
    (e : G ≃* alternatingGroup (Fin k)) (hR : Nat.card R = 8)
    (htrans : ∀ x ∈ R, x ≠ 1 → ∀ y ∈ R, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (R : Set G), g * x * g⁻¹ = y)
    (h : Hyp3 G (Subgroup.normalizer (R : Set G)) X) (hb : Blk3 X a) : False := by
  set N : Subgroup G := Subgroup.normalizer (R : Set G) with hN
  have h7 : 7 ∣ Nat.card N := by
    have := card_sub_one_dvd_card_normalizer (R := R) (by omega) htrans
    rw [hR] at this
    exact this
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy7⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 7 h7
  have hyo : orderOf (y : G) = 7 := by rw [Subgroup.orderOf_coe]; exact hy7
  have hy1 : (y : G) ^ 7 = 1 := by
    have := pow_orderOf_eq_one (y : G)
    rwa [hyo] at this
  have hNW : ∀ g ∈ N, ∀ w ∈ pCoreOf 2 X, g * w * g⁻¹ ∈ pCoreOf 2 X :=
    fun g hg w hw => h.W_normalized hg hw
  have hyW : ∀ w ∈ pCoreOf 2 X, (y : G) * w * (y : G)⁻¹ = w := by
    have hσ : (wnPerm X N hNW y) ^ 7 = 1 := by
      rw [← map_pow]
      have : y ^ 7 = 1 := by
        have := pow_orderOf_eq_one y
        rwa [hy7] at this
      rw [this, map_one]
    exact (wnPerm_eq_one_iff X N hNW y).1 (perm3_eq_one_of_pow_seven (card_Wn hb) _ hσ)
  obtain ⟨w, hw, hk⟩ := h.exists_mul_centralizer hb y.2 hyW
  set k' : G := w⁻¹ * (y : G) with hk'
  have hy_eq : (y : G) = w * k' := by rw [hk']; group
  have hcomm' : Commute w k' := Subgroup.mem_centralizer_iff.1 hk w (pCoreOf_le_self X hw)
  have h7' : w * k' ^ 7 = 1 := by
    have h1 : (w * k') ^ 7 = w ^ 7 * k' ^ 7 := hcomm'.mul_pow 7
    have hw2 : w ^ 7 = w := by
      have hw2' : w ^ 2 = 1 := by
        rw [sq]
        exact hb.sq w hw
      rw [show (7 : ℕ) = 2 * 3 + 1 from rfl, pow_succ, pow_mul, hw2', one_pow, one_mul]
    rw [← hy_eq, hy1, hw2] at h1
    exact h1.symm
  have hwC : w ∈ Subgroup.centralizer (X : Set G) := by
    have : w = (k' ^ 7)⁻¹ := eq_inv_of_mul_eq_one_left h7'
    rw [this]
    exact (Subgroup.centralizer (X : Set G)).inv_mem
      ((Subgroup.centralizer (X : Set G)).pow_mem hk 7)
  have hw1 : w = 1 := Hyp3.W_inf_C hb hw hwC
  have hyC : (y : G) ∈ Subgroup.centralizer (X : Set G) := by
    rw [hy_eq, hw1, one_mul]
    exact hk
  have ha1 : a ≠ 1 := by
    intro ha
    obtain ⟨w, hw, hw1⟩ := hb.exists_ne_one
    exact hw1 (hb.fix w hw (by rw [ha]; group))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : orderOf a = 3 := orderOf_eq_prime hb.cube ha1
  have hcay : Commute a (y : G) := Subgroup.mem_centralizer_iff.1 hyC a hb.mem
  have hord21 : orderOf (a * (y : G)) = 21 := by
    rw [hcay.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ha3, hyo]; norm_num), ha3, hyo]
  have hord : orderOf ((e (a * (y : G)) : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) = 21 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hord21]
  exact orderOf_ne_twenty_one hk9 _ hord

theorem false_of_alt_three {k : ℕ} (hk6 : 6 ≤ k) (hk9 : k ≤ 9)
    (e : G ≃* alternatingGroup (Fin k)) (hR : Nat.card R = if k ≤ 7 then 4 else 8)
    (htrans : ∀ x ∈ R, x ≠ 1 → ∀ y ∈ R, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (R : Set G), g * x * g⁻¹ = y)
    (h : Hyp3 G (Subgroup.normalizer (R : Set G)) X) (hb : Blk3 X a)
    (hXC : X ≤ Subgroup.centralizer (R : Set G)) : False := by
  by_cases hk7 : k ≤ 7
  · exact false_of_alt_small hk6 hk7 e (by simpa [hk7] using hR) hb hXC
  · exact false_of_alt_big hk9 e (by simpa [hk7] using hR) htrans h hb

end Block

end CFSG.CGT.PushingUpLit.E3A
