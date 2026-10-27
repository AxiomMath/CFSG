module

public import CFSG.GroupTheory.FrobeniusNormalComplement
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Cyclic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

section LemmaQ

variable {G : Type*} [Group G]

theorem exists_commute_mul_of_comm_mem {p : ℕ} [Fact p.Prime] {N : Subgroup G} {a g : G}
    (ha : IsPGroup p (zpowers a)) (hN : Nat.Coprime (Nat.card N) p)
    (haN : a ∈ normalizer (N : Set G)) (hgN : g ∈ normalizer (N : Set G))
    (hc : a * g * a⁻¹ * g⁻¹ ∈ N) : ∃ n ∈ N, Commute (g * n) a := by
  have hM : ∀ z ∈ normalizer (N : Set G), ∀ n ∈ N, z * n * z⁻¹ ∈ N :=
    fun z hz n hn => (mem_normalizer_iff.mp hz n).mp hn
  have hM' : ∀ z ∈ normalizer (N : Set G), ∀ n ∈ N, z⁻¹ * n * z ∈ N := fun z hz n hn => by
    simpa using hM z⁻¹ (inv_mem hz) n hn
  let C : Subgroup G :=
    { carrier := {x | x ∈ normalizer (N : Set G) ∧ x * g * x⁻¹ * g⁻¹ ∈ N}
      one_mem' := ⟨one_mem _, by simpa using N.one_mem⟩
      mul_mem' := fun {x y} hx hy => by
        refine ⟨mul_mem hx.1 hy.1, ?_⟩
        have e : x * y * g * (x * y)⁻¹ * g⁻¹ =
            (x * (y * g * y⁻¹ * g⁻¹) * x⁻¹) * (x * g * x⁻¹ * g⁻¹) := by group
        rw [e]
        exact N.mul_mem (hM x hx.1 _ hy.2) hx.2
      inv_mem' := fun {x} hx => by
        refine ⟨inv_mem hx.1, ?_⟩
        have e : x⁻¹ * g * x⁻¹⁻¹ * g⁻¹ = x⁻¹ * (x * g * x⁻¹ * g⁻¹)⁻¹ * x := by group
        rw [e]
        exact hM' x hx.1 _ (N.inv_mem hx.2) }
  have hzC : zpowers a ≤ C := zpowers_le.mpr ⟨haN, hc⟩
  have hxg : ∀ x ∈ zpowers a, x * g * x⁻¹ * g⁻¹ ∈ N := fun x hx => (hzC hx).2
  have hxM : ∀ x ∈ zpowers a, x ∈ normalizer (N : Set G) := fun x hx => (hzC hx).1
  let F : Type _ := {y : G // y⁻¹ * g ∈ N}
  have hF : ∀ x ∈ zpowers a, ∀ y : G, y⁻¹ * g ∈ N → (x * y * x⁻¹)⁻¹ * g ∈ N := by
    intro x hx y hy
    have e : (x * y * x⁻¹)⁻¹ * g =
        (x * (y⁻¹ * g) * x⁻¹) * (g⁻¹ * (x * g * x⁻¹ * g⁻¹)⁻¹ * g) := by group
    rw [e]
    exact N.mul_mem (hM x (hxM x hx) _ hy) (hM' g hgN _ (N.inv_mem (hxg x hx)))
  let act : MulAction (zpowers a) F :=
    { smul := fun x y => ⟨x.1 * y.1 * x.1⁻¹, hF x.1 x.2 y.1 y.2⟩
      one_smul := fun y => Subtype.ext (by
        change (1 : zpowers a).1 * y.1 * (1 : zpowers a).1⁻¹ = y.1
        simp)
      mul_smul := fun x x' y => Subtype.ext (by
        change (x * x' : zpowers a).1 * y.1 * (x * x' : zpowers a).1⁻¹ =
          x.1 * (x'.1 * y.1 * x'.1⁻¹) * x.1⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card F = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1⁻¹ * g, y.2⟩
        invFun := fun n => ⟨g * (n : G)⁻¹, by simpa using n.2⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have hndvd : ¬ p ∣ Nat.card F := by
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hN.symm
  letI := act
  obtain ⟨y, hy⟩ := ha.nonempty_fixed_point_of_prime_not_dvd_card F hndvd
  have h1 : a * y.1 * a⁻¹ = y.1 :=
    congrArg Subtype.val (hy ⟨a, mem_zpowers a⟩)
  refine ⟨g⁻¹ * y.1, ?_, ?_⟩
  · simpa using N.inv_mem y.2
  · rw [mul_inv_cancel_left]
    change y.1 * a = a * y.1
    calc y.1 * a = a * y.1 * a⁻¹ * a := by rw [h1]
      _ = a * y.1 := by group

end LemmaQ

section LemmaP

variable {Y : Type*} [Group Y]

theorem eq_one_of_commutator_pElement {p m : ℕ} (hm : Nat.Coprime p m) {x q r : Y}
    (hxm : x ^ m = 1) (hr : r = x * q * x⁻¹ * q⁻¹) (hrx : x * r * x⁻¹ = r)
    (hrp : ∃ k : ℕ, r ^ (p ^ k) = 1) : r = 1 := by
  have hxq : x * q * x⁻¹ = r * q := by rw [hr]; group
  have h1 : ∀ k : ℕ, x ^ k * q * (x ^ k)⁻¹ = r ^ k * q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : x ^ (k + 1) * q * (x ^ (k + 1))⁻¹ = x * (x ^ k * q * (x ^ k)⁻¹) * x⁻¹ := by group
      have e2 : x * (r ^ k * q) * x⁻¹ = (x * r * x⁻¹) ^ k * (x * q * x⁻¹) := by
        rw [conj_pow]; group
      rw [e, ih, e2, hrx, hxq, pow_succ, mul_assoc]
  have h2 := h1 m
  rw [hxm] at h2
  have h3 : r ^ m * q = 1 * q := by rw [← h2]; simp
  have h4 : r ^ m = 1 := mul_right_cancel h3
  obtain ⟨k, hk⟩ := hrp
  have h5 := pow_gcd_eq_one.mpr ⟨hk, h4⟩
  rwa [(Nat.Coprime.pow_left k hm).gcd_eq_one, pow_one] at h5

theorem mem_centralizer_of_isPGroup_automizer {p : ℕ} [Fact p.Prime] {H : Type*} [Group H]
    {Q : Subgroup H}
    (h : IsPGroup p (normalizer (Q : Set H) ⧸
      (centralizer (Q : Set H)).subgroupOf (normalizer (Q : Set H))))
    {x : H} (hx : x ∈ normalizer (Q : Set H)) {m : ℕ} (hm : Nat.Coprime p m) (hxm : x ^ m = 1) :
    x ∈ centralizer (Q : Set H) := by
  set z : normalizer (Q : Set H) ⧸
      (centralizer (Q : Set H)).subgroupOf (normalizer (Q : Set H)) := QuotientGroup.mk ⟨x, hx⟩
  have hzm : z ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    simp [hxm]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h z
  have hdvd : p ^ k ∣ m := hk ▸ orderOf_dvd_of_pow_eq_one hzm
  have hk0 : p ^ k = 1 := (Nat.Coprime.pow_left k hm).eq_one_of_dvd hdvd
  rw [hk0, orderOf_eq_one_iff] at hk
  have := (QuotientGroup.eq_one_iff (N := (centralizer (Q : Set H)).subgroupOf
    (normalizer (Q : Set H))) ⟨x, hx⟩).mp hk
  simpa [mem_subgroupOf] using this

theorem hasNormalPComplement_of_cyclic_pSubgroups {p : ℕ} [Fact p.Prime] [Finite Y]
    (N : Subgroup Y) [N.Normal] (hcyc : ∀ R : Subgroup Y, R ≤ N → IsPGroup p R → IsCyclic R)
    (hcen : ∀ x ∈ N, orderOf x = p → x ∈ center Y)
    (hq : CFSG.HasNormalPComplement p (Y ⧸ N)) : CFSG.HasNormalPComplement p Y := by
  rw [CFSG.GroupTheory.hasNormalPComplement_iff_isPGroup_automizer]
  intro Q hQ
  have hqQ := (CFSG.GroupTheory.hasNormalPComplement_iff_isPGroup_automizer p).mp hq
    (Q.map (QuotientGroup.mk' N)) (hQ.map _)
  have key : ∀ x ∈ normalizer (Q : Set Y), ∀ m : ℕ, Nat.Coprime p m → x ^ m = 1 →
      x ∈ centralizer (Q : Set Y) := by
    intro x hx m hm hxm
    have hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := fun q hq => (mem_normalizer_iff.mp hx q).mp hq
    have hxbar : QuotientGroup.mk' N x ∈ centralizer
        ((Q.map (QuotientGroup.mk' N) : Subgroup (Y ⧸ N)) : Set (Y ⧸ N)) := by
      refine mem_centralizer_of_isPGroup_automizer hqQ ?_ hm (by rw [← map_pow, hxm, map_one])
      have hmem : QuotientGroup.mk' N x ∈ (normalizer (Q : Set Y)).map (QuotientGroup.mk' N) :=
        mem_map_of_mem _ hx
      exact le_normalizer_map _ hmem
    have hcomm : ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ N := by
      intro q hq
      have h := mem_centralizer_iff.mp hxbar (QuotientGroup.mk' N q) ⟨q, hq, rfl⟩
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk'_apply] at h
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact h.symm
    have hRp : IsPGroup p (Q ⊓ N : Subgroup Y) := hQ.to_inf_left
    haveI : IsCyclic (Q ⊓ N : Subgroup Y) := hcyc _ inf_le_right hRp
    have hRfix : ∀ r ∈ (Q ⊓ N : Subgroup Y), x * r * x⁻¹ = r := by
      by_cases hR : (Q ⊓ N : Subgroup Y) = ⊥
      · intro r hr
        rw [hR, mem_bot] at hr
        simp [hr]
      · have hdvd : p ∣ Nat.card (Q ⊓ N : Subgroup Y) :=
          (hRp.card_eq_or_dvd).resolve_left (mt Subgroup.card_eq_one.mp hR)
        obtain ⟨x₀', hx₀'⟩ := exists_prime_orderOf_dvd_card' (G := (Q ⊓ N : Subgroup Y)) p hdvd
        have hx₀R : (x₀' : Y) ∈ (Q ⊓ N : Subgroup Y) := x₀'.2
        have hx₀c := mem_center_iff.mp (hcen _ (Subgroup.mem_inf.mp hx₀R).2
          (by rw [← hx₀', Subgroup.orderOf_coe]))
        have hgx : x * (x₀' : Y) * x⁻¹ = x₀' := by rw [hx₀c x]; group
        exact Generic49U3.cyclic_coprime_aut_trivial (Fact.out : p.Prime) (D := Q ⊓ N)
          (fun d hd => by
            obtain ⟨k, hk⟩ := hRp ⟨d, hd⟩
            exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
          hx₀R ((Subgroup.orderOf_coe x₀').trans hx₀')
          (fun d hd => ⟨hxQ d hd.1, ‹N.Normal›.conj_mem d hd.2 x⟩) hgx hm
          (fun d _ => by simp [hxm])
    intro q hq
    have hrR : x * q * x⁻¹ * q⁻¹ ∈ (Q ⊓ N : Subgroup Y) :=
      mem_inf.mpr ⟨Q.mul_mem (hxQ q hq) (Q.inv_mem hq), hcomm q hq⟩
    have hr1 : x * q * x⁻¹ * q⁻¹ = 1 := by
      refine eq_one_of_commutator_pElement hm hxm rfl (hRfix _ hrR) ?_
      obtain ⟨k, hk⟩ := hRp ⟨_, hrR⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have h2 : x * q * x⁻¹ = q := mul_inv_eq_one.mp hr1
    calc q * x = (x * q * x⁻¹) * x := by rw [h2]
      _ = x * q := by group
  refine IsPGroup.iff_orderOf.mpr fun z => ?_
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective z
  set x' : normalizer (Q : Set Y) := ⟨x, hx⟩ with hx'
  obtain ⟨e, b, hb, hxe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x').ne' p
    (Fact.out : p.Prime).ne_one
  have hord : orderOf x = p ^ e * b := (Subgroup.orderOf_coe x').trans hxe
  have hy : x ^ (p ^ e) ∈ centralizer (Q : Set Y) :=
    key _ (pow_mem hx _) b ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hb)
      (by rw [← pow_mul, ← hord]; exact pow_orderOf_eq_one x)
  have hz : (QuotientGroup.mk x' :
      normalizer (Q : Set Y) ⧸ (centralizer (Q : Set Y)).subgroupOf (normalizer (Q : Set Y))) ^
      (p ^ e) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hy
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hz)
  exact ⟨k, hk⟩

theorem isCyclic_of_isPGroup_of_le {p : ℕ} [Fact p.Prime] [Finite Y] {N : Subgroup Y}
    (hcyc : ∀ P : Sylow p N, IsCyclic P) {R : Subgroup Y} (hR : IsPGroup p R) (hRN : R ≤ N) :
    IsCyclic R := by
  have hR' : IsPGroup p (R.subgroupOf N) := hR.comap_subtype
  obtain ⟨P, hP⟩ := hR'.exists_le_sylow
  haveI := hcyc P
  haveI : IsCyclic (R.subgroupOf N) := Subgroup.isCyclic_of_le hP
  exact isCyclic_of_surjective (subgroupOfEquivOfLe hRN).toMonoidHom
    (subgroupOfEquivOfLe hRN).surjective

theorem hasNormalPComplement_of_cyclic_sylow_central_quotient {p : ℕ} [Fact p.Prime] [Finite Y]
    (N : Subgroup Y) [N.Normal] (hcyc : ∀ P : Sylow p N, IsCyclic P)
    (hcen : ∀ x ∈ N, orderOf x = p → x ∈ center Y)
    (hq : CFSG.HasNormalPComplement p (Y ⧸ N)) : CFSG.HasNormalPComplement p Y :=
  hasNormalPComplement_of_cyclic_pSubgroups N
    (fun _ hRN hR => isCyclic_of_isPGroup_of_le hcyc hR hRN) hcen hq

theorem hasNormalPComplement_of_cyclic_sylow_central {p : ℕ} [Fact p.Prime] [Finite Y]
    (hcyc : ∀ P : Sylow p Y, IsCyclic P) (hcen : ∀ x : Y, orderOf x = p → x ∈ center Y) :
    CFSG.HasNormalPComplement p Y := by
  haveI : Subsingleton (Y ⧸ (⊤ : Subgroup Y)) := QuotientGroup.subsingleton_quotient_top
  have hq : CFSG.HasNormalPComplement p (Y ⧸ (⊤ : Subgroup Y)) :=
    ⟨⊥, inferInstance, by simp,
      (IsPGroup.of_subsingleton (p := p) (G := Y ⧸ (⊤ : Subgroup Y))).to_quotient _⟩
  refine hasNormalPComplement_of_cyclic_pSubgroups (⊤ : Subgroup Y) (fun R _ hR => ?_)
    (fun x _ hx => hcen x hx) hq
  obtain ⟨P, hP⟩ := hR.exists_le_sylow
  haveI := hcyc P
  exact Subgroup.isCyclic_of_le hP

end LemmaP

end CFSG.LocalAnalysis.RankThreeTheoremC
