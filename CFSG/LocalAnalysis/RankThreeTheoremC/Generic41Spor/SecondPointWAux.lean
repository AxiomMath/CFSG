module

import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3_core_conj card_inf_centralizer_of_nonabelian_card_p_cube
  card_center_of_nonabelian_card_p_cube)

variable {G : Type} [Group G] [Finite G]

theorem spw_mem_sup_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {s : G} (hs : s ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => h a a.2 b b.2)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := hs
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem spw_mem_zpowers_of_cyclic {p : ℕ} [Fact p.Prime] {Z : Subgroup G} (hZ : IsCyclic Z) {x z : G}
    (hxZ : x ∈ Z) (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hzZ : z ∈ Z) (hzp : z ^ p = 1) :
    z ∈ zpowers x := by
  by_cases hz1 : z = 1
  · rw [hz1]
    exact one_mem _
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
  set x' : Z := ⟨x, hxZ⟩ with hx'
  set z' : Z := ⟨z, hzZ⟩ with hz'
  have h1 : Nat.card (zpowers x') = Nat.card (zpowers z') := by
    rw [Nat.card_zpowers, Nat.card_zpowers]
    simp [hx', hz', Subgroup.orderOf_mk, hxo, hzo]
  have h2 : zpowers x' = zpowers z' := (IsCyclic.subgroup_eq_iff_card_eq).2 h1
  have h3 : z' ∈ zpowers x' := h2 ▸ mem_zpowers z'
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h3
  exact ⟨k, by simpa [hx', hz'] using congrArg Subtype.val hk⟩

theorem spw_mem_zpowers_of_mem_zpowers {p : ℕ} [Fact p.Prime] {x a : G} (hxo : orderOf x = p)
    (hao : orderOf a = p) (hxa : x ∈ zpowers a) : a ∈ zpowers x := by
  have heq : zpowers x = zpowers a :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxa) (by rw [Nat.card_zpowers, Nat.card_zpowers, hao, hxo])
  rw [heq]
  exact mem_zpowers a

theorem spw_exists_noncomm_commutator_central {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hcard : Nat.card A = p ^ 3) (hnc : ¬ IsMulCommutative A) :
    ∃ s ∈ A, ∃ t ∈ A, s * t * s⁻¹ * t⁻¹ ≠ 1 ∧
      ∀ u ∈ A, u * (s * t * s⁻¹ * t⁻¹) = (s * t * s⁻¹ * t⁻¹) * u := by
  have hpair : ∃ s t : A, s * t ≠ t * s := by
    by_contra hcon
    push Not at hcon
    exact hnc ⟨⟨fun a b => hcon a b⟩⟩
  obtain ⟨s, t, hst⟩ := hpair
  have hZc : Nat.card (center A) = p := card_center_of_nonabelian_card_p_cube hcard hnc
  have hq : Nat.card (A ⧸ center A) = p ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center A)
    rw [hcard, hZc] at h
    apply Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
    rw [← h]
    ring
  have hQcomm : IsMulCommutative (A ⧸ center A) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have hcomm : s * t * s⁻¹ * t⁻¹ ∈ center A := by
    rw [← QuotientGroup.eq_one_iff]
    have h : (QuotientGroup.mk s : A ⧸ center A) * QuotientGroup.mk t =
        QuotientGroup.mk t * QuotientGroup.mk s := hQcomm.is_comm.comm _ _
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h]
    group
  have hw1 : s * t * s⁻¹ * t⁻¹ ≠ 1 := by
    intro h
    apply hst
    calc s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
      _ = t * s := by rw [h, one_mul]
  refine ⟨(s : G), s.2, (t : G), t.2, fun h => hw1 (Subtype.ext h), ?_⟩
  intro u hu
  have := Subgroup.mem_center_iff.1 hcomm ⟨u, hu⟩
  exact (congrArg Subtype.val this)

theorem spw_central_mem_commutator {p : ℕ} [Fact p.Prime] {P T : Subgroup G} (hTP : T ≤ P)
    (hTcard : Nat.card T = p ^ 3) (hTnab : ¬ IsMulCommutative T) {t : G} (htT : t ∈ T)
    (htc : ∀ s ∈ T, t * s = s * t) : t ∈ ⁅P, P⁆ := by
  have hp : p.Prime := Fact.out
  obtain ⟨s, hs, r, hr, hw1, hwc⟩ := spw_exists_noncomm_commutator_central hTcard hTnab
  set w : G := s * r * s⁻¹ * r⁻¹ with hw
  have hwT : w ∈ T := T.mul_mem (T.mul_mem (T.mul_mem hs hr) (T.inv_mem hs)) (T.inv_mem hr)
  have hwP : w ∈ ⁅P, P⁆ := Subgroup.commutator_mem_commutator (hTP hs) (hTP hr)
  have hZc := card_inf_centralizer_of_nonabelian_card_p_cube hTcard hTnab
  have hwZ : w ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
    ⟨hwT, Subgroup.mem_centralizer_iff.2 fun u hu => hwc u hu⟩
  have htZ : t ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
    ⟨htT, Subgroup.mem_centralizer_iff.2 fun u hu => (htc u hu).symm⟩
  have hwo : orderOf w = p := by
    have hdvd : orderOf w ∣ p := by
      have := orderOf_dvd_natCard (⟨w, hwZ⟩ : ↥(T ⊓ Subgroup.centralizer (T : Set G)))
      rw [hZc] at this
      rwa [Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hw1
    · exact h1
  have hzw : zpowers w = T ⊓ Subgroup.centralizer (T : Set G) :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hwZ) (by rw [Nat.card_zpowers, hwo, hZc])
  have htw : t ∈ zpowers w := by rw [hzw]; exact htZ
  exact (zpowers_le.2 hwP) htw

theorem spw_mem_of_centralizes {p : ℕ} [Fact p.Prime] (P : Sylow p G) {x : G} (hxp : x ^ p = 1)
    (hxC : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) : x ∈ (P : Subgroup G) := by
  have hcomm : ∀ a ∈ (P : Subgroup G), ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    have h1 : Commute a x := Subgroup.mem_centralizer_singleton_iff.mp (hxC ha)
    exact (h1.zpow_right k).eq
  have hH : IsPGroup p ↥((P : Subgroup G) ⊔ zpowers x) := by
    intro g
    obtain ⟨a, ha, b, hb, hab⟩ := spw_mem_sup_of_commute hcomm g.2
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨a, ha⟩
    have hak : a ^ p ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hb
    have hbp : (x ^ i) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
    refine ⟨k + 1, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, hab, Commute.mul_pow (show Commute a (x ^ i) from hcomm a ha _ hb)]
    have e1 : a ^ p ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hak, one_pow]
    have e2 : (x ^ i) ^ p ^ (k + 1) = 1 := by
      rw [pow_succ, mul_comm, pow_mul, hbp, one_pow]
    rw [e1, e2, mul_one]
    rfl
  have heq := P.3 hH le_sup_left
  have hx : x ∈ (P : Subgroup G) ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  rwa [heq] at hx

theorem spw_inf_zpowers_eq_bot {p : ℕ} [Fact p.Prime] {T : Subgroup G} {y : G} (hyo : orderOf y = p)
    (hyT : y ∉ T) : T ⊓ zpowers y = ⊥ := by
  have hdvd : Nat.card ↥(T ⊓ zpowers y) ∣ p := by
    have := Subgroup.card_dvd_of_le (inf_le_right : T ⊓ zpowers y ≤ zpowers y)
    rwa [Nat.card_zpowers, hyo] at this
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    apply hyT
    have heq : T ⊓ zpowers y = zpowers y :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [Nat.card_zpowers, hyo, h1])
    have : y ∈ T ⊓ zpowers y := by rw [heq]; exact mem_zpowers y
    exact this.1

theorem spw_zpowers_conj (g x : G) :
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers (g * x * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

@[expose] def NormalizerPowers (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow p K, ∀ t ∈ (S : Subgroup K), t ≠ 1 → ∀ k : ℕ, ¬ p ∣ k →
    ∃ n ∈ normalizer ((S : Subgroup K) : Set K), n * t * n⁻¹ = t ^ k

private theorem spw_conj_hom (J H : Subgroup G) (hH : H ≤ Subgroup.normalizer (J : Set G)) :
    ∃ ι : H →* MulAut J, ∀ (c : H) (j : J), ((ι c j : J) : G) = (c : G) * j * (c : G)⁻¹ := by
  let f : ∀ c : G, c ∈ Subgroup.normalizer (J : Set G) → MulAut J := fun c hc =>
    { toFun := fun j => ⟨c * j * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc j).mp j.2⟩
      invFun := fun j => ⟨c⁻¹ * j * c, by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hc) j).mp j.2⟩
      left_inv := fun j => by ext; simp [mul_assoc]
      right_inv := fun j => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  refine ⟨{ toFun := fun c => f c (hH c.2), map_one' := ?_, map_mul' := ?_ }, fun c j => rfl⟩
  · ext j; simp [f]
  · intro a b; ext j; simp [f, mul_assoc]

private theorem spw_descent {J Q H : Type} [Group J] [Group Q] [Group H] (ψ : J →* Q)
    (hψ : Function.Surjective ψ) (ι : H →* MulAut J)
    (h : ∀ c j, ψ j = 1 → ψ (ι c j) = 1) :
    ∃ θ : H →* MulAut Q, ∀ c j, θ c (ψ j) = ψ (ι c j) := by
  have key : ∀ c : H, ∃ f : Q →* Q, ∀ j, f (ψ j) = ψ (ι c j) := by
    intro c
    refine ⟨ψ.liftOfSurjective hψ ⟨ψ.comp (ι c).toMonoidHom, fun j hj => h c j hj⟩, fun j => ?_⟩
    simp
  choose F hF using key
  have hmul : ∀ c d : H, ∀ q, F (c * d) q = F c (F d q) := by
    intro c d q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF, hF, hF]
    simp
  have hone : ∀ q, F 1 q = q := by
    intro q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF]
    simp
  let θ' : ∀ c : H, MulAut Q := fun c =>
    { toFun := F c
      invFun := F c⁻¹
      left_inv := fun q => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun q => by rw [← hmul, mul_inv_cancel, hone]
      map_mul' := (F c).map_mul }
  refine ⟨{ toFun := θ', map_one' := ?_, map_mul' := ?_ }, fun c j => hF c j⟩
  · ext q; exact hone q
  · intro a b; ext q; exact hmul a b q

theorem spw_exists_rho {p : ℕ} {C J : Subgroup G} (hCN : C ≤ Subgroup.normalizer (J : Set G))
    {Q : Type} [Group Q] (ψ : ↥J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) :
    ∃ ρ : ↥C →* MulAut Q, ∀ (c : ↥C) (j : ↥J) (hj : (c : G) * (j : G) * (c : G)⁻¹ ∈ J),
      ρ c (ψ j) = ψ ⟨(c : G) * (j : G) * (c : G)⁻¹, hj⟩ := by
  obtain ⟨ι, hι⟩ := spw_conj_hom J C hCN
  have hOker : ∀ j : J, ψ j = 1 ↔ (j : G) ∈ rankThreePrimeCore p J := by
    intro j
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hιker : ∀ (c : ↥C) (j : J), ψ j = 1 → ψ (ι c j) = 1 := by
    intro c j hj
    rw [hOker] at hj ⊢
    rw [hι]
    exact u3_core_conj (hCN c.2) hj
  obtain ⟨θ, hθ⟩ := spw_descent ψ hψ ι hιker
  refine ⟨θ, fun c j hj => ?_⟩
  rw [hθ]
  congr 1
  exact Subtype.ext (hι c j)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
