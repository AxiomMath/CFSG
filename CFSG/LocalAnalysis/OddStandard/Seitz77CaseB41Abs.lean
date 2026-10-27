module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.OddStandard.Seitz77WBridgeSetup
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem exists_odd_complement_of_central_two {G : Type} [Group G] [Finite G] {K W : Subgroup G}
    (hWK : W ≤ K) (hWc : ∀ w ∈ W, ∀ k ∈ K, w * k = k * w) (hW2 : IsPGroup 2 W)
    (hidx : ¬ 2 ∣ W.relIndex K) :
    ∃ O₁ : Subgroup G, O₁ ≤ K ∧ Odd (Nat.card O₁) ∧ W ⊓ O₁ = ⊥ ∧
      (∀ k ∈ K, ∃ w ∈ W, ∃ o ∈ O₁, k = w * o) ∧
      (∀ x ∈ K, Odd (orderOf x) → x ∈ O₁) ∧
      (∀ k ∈ K, ∀ o ∈ O₁, k * o * k⁻¹ ∈ O₁) := by
  have hNnormal : (W.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have h1 : (n : G) * g = g * n := hWc _ hn g g.2
    have h2 : ((g * n * g⁻¹ : K) : G) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h1, mul_inv_cancel_right]
    rw [h2]
    exact hn
  have hNp : IsPGroup 2 (W.subgroupOf K) := hW2.of_equiv (subgroupOfEquivOfLe hWK).symm
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hNp
  have hcop : Nat.Coprime (Nat.card (W.subgroupOf K)) (W.subgroupOf K).index := by
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hidx)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKinj : Function.Injective K.subtype := Subtype.coe_injective
  have hodd : Odd (Nat.card (H.map K.subtype)) := by
    rw [card_map_of_injective hKinj, ← hH.symm.index_eq_card]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hidx)
  have hinf : W ⊓ H.map K.subtype = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxO⟩
    obtain ⟨h, hh, rfl⟩ := hxO
    have h1 : h ∈ W.subgroupOf K := hxW
    have h2 : h = 1 := (Subgroup.disjoint_def.1 hH.disjoint) h1 hh
    rw [mem_bot]
    simp [h2]
  have hdecomp : ∀ k ∈ K, ∃ w ∈ W, ∃ o ∈ H.map K.subtype, k = w * o := by
    intro k hk
    obtain ⟨⟨⟨n, hn⟩, ⟨h, hh⟩⟩, hnh⟩ := hH.2 ⟨k, hk⟩
    exact ⟨(n : G), hn, (h : G), ⟨h, hh, rfl⟩, (congrArg Subtype.val hnh).symm⟩
  have he : ∀ x ∈ K, Odd (orderOf x) → x ∈ H.map K.subtype := by
    intro x hx hxodd
    obtain ⟨w, hw, o, ho, rfl⟩ := hdecomp x hx
    have hoK : o ∈ K := map_subtype_le H ho
    have hcomm : Commute w o := hWc w hw o hoK
    have hpow : (w * o) ^ orderOf (w * o) = 1 := pow_orderOf_eq_one _
    rw [hcomm.mul_pow] at hpow
    have h1 : w ^ orderOf (w * o) ∈ W ⊓ H.map K.subtype := by
      refine ⟨W.pow_mem hw _, ?_⟩
      have : w ^ orderOf (w * o) = (o ^ orderOf (w * o))⁻¹ := eq_inv_of_mul_eq_one_left hpow
      rw [this]
      exact (H.map K.subtype).inv_mem ((H.map K.subtype).pow_mem ho _)
    rw [hinf, mem_bot] at h1
    have hw1 : w = 1 := by
      obtain ⟨k, hk⟩ := hW2 ⟨w, hw⟩
      have hk' : w ^ (2 ^ k) = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hd1 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hd2 : orderOf w ∣ orderOf (w * o) := orderOf_dvd_of_pow_eq_one h1
      have hcop' : Nat.Coprime (2 ^ k) (orderOf (w * o)) := by
        apply Nat.Coprime.pow_left
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
          (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hxodd)
      have hd3 : orderOf w ∣ Nat.gcd (2 ^ k) (orderOf (w * o)) := Nat.dvd_gcd hd1 hd2
      rw [hcop'] at hd3
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd3)
    rw [hw1, one_mul]
    exact ho
  have hf : ∀ k ∈ K, ∀ o ∈ H.map K.subtype, k * o * k⁻¹ ∈ H.map K.subtype := by
    intro k hk o ho
    obtain ⟨w, hw, o', ho', rfl⟩ := hdecomp k hk
    have hc : o' * o * o'⁻¹ ∈ H.map K.subtype :=
      (H.map K.subtype).mul_mem ((H.map K.subtype).mul_mem ho' ho)
        ((H.map K.subtype).inv_mem ho')
    have hcomm : w * (o' * o * o'⁻¹) = (o' * o * o'⁻¹) * w :=
      hWc w hw _ (map_subtype_le H hc)
    have hcalc : w * o' * o * (w * o')⁻¹ = o' * o * o'⁻¹ := by
      calc w * o' * o * (w * o')⁻¹ = (w * (o' * o * o'⁻¹)) * w⁻¹ := by group
        _ = ((o' * o * o'⁻¹) * w) * w⁻¹ := by rw [hcomm]
        _ = o' * o * o'⁻¹ := by group
    rw [hcalc]
    exact hc
  exact ⟨H.map K.subtype, map_subtype_le H, hodd, hinf, hdecomp, he, hf⟩

theorem perfect_comm_mem {G : Type} [Group G] {M J Kc : Subgroup G} {g : G}
    (hM : ⁅M, M⁆ = M)
    (hJM : ∀ x ∈ M, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hJg : ∀ j ∈ J, g * j * g⁻¹ ∈ J)
    (hKc : ∀ m ∈ M, ⁅m, g⁆ ∈ Kc ∧ ⁅m, g⁻¹⁆ ∈ Kc)
    (hKcJ : ∀ k ∈ Kc, ∀ m ∈ M, ⁅k, m⁆ ∈ J) :
    ∀ m ∈ M, ⁅m, g⁆ ∈ J := by
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G, ∀ m, m ∈ E ↔ m ∈ M ∧ ⁅m, g⁆ ∈ J := by
    refine ⟨{ carrier := {m | m ∈ M ∧ ⁅m, g⁆ ∈ J}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun m => Iff.rfl⟩
    · rintro m₁ m₂ ⟨hm₁, h₁⟩ ⟨hm₂, h₂⟩
      refine ⟨M.mul_mem hm₁ hm₂, ?_⟩
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact J.mul_mem (hJM m₁ hm₁ _ h₂) h₁
    · exact ⟨M.one_mem, by rw [commutatorElement_one_left]; exact J.one_mem⟩
    · rintro m ⟨hm, h⟩
      refine ⟨M.inv_mem hm, ?_⟩
      have h' := hJM m⁻¹ (M.inv_mem hm) _ (J.inv_mem h)
      rw [inv_inv, commutatorElement_inv] at h'
      rwa [commutatorElement_inv_left]
  have hsub : ⁅M, M⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [hE]
    refine ⟨?_, ?_⟩
    · have h' := Subgroup.commutator_mem_commutator ha hb
      rwa [hM] at h'
    · have h2 : ⁅g⁻¹, a⁻¹⁆ ∈ Kc := by
        rw [← commutatorElement_inv]
        exact Kc.inv_mem (hKc _ (M.inv_mem ha)).2
      have hP2 : g * ⁅⁅g⁻¹, a⁻¹⁆, b⁆ * g⁻¹ ∈ J := hJg _ (hKcJ _ h2 b hb)
      have hP3 : b * ⁅⁅b⁻¹, g⁆, a⁻¹⁆ * b⁻¹ ∈ J :=
        hJM b hb _ (hKcJ _ (hKc _ (M.inv_mem hb)).1 a⁻¹ (M.inv_mem ha))
      have hw := conj_commutatorElement_left_commutatorElement_mul a⁻¹ b g
      rw [inv_inv] at hw
      have hP1 : a⁻¹ * ⁅⁅a, b⁆, g⁆ * a ∈ J := by
        have e : (a⁻¹ * ⁅⁅a, b⁆, g⁆ * a) *
            ((g * ⁅⁅g⁻¹, a⁻¹⁆, b⁆ * g⁻¹) * (b * ⁅⁅b⁻¹, g⁆, a⁻¹⁆ * b⁻¹)) = 1 := by
          simpa only [mul_assoc] using hw
        rw [eq_inv_of_mul_eq_one_left e]
        exact J.inv_mem (J.mul_mem hP2 hP3)
      have h' := hJM a ha _ hP1
      simpa [mul_assoc] using h'
  intro m hm
  exact ((hE m).1 (hsub (by rw [hM]; exact hm))).2

section PerfectResidual

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem prOf_le (H : Subgroup G) : perfectResidualOf H ≤ H := Subgroup.map_subtype_le _

theorem prOf_perfect (H : Subgroup G) :
    ⁅perfectResidualOf H, perfectResidualOf H⁆ = perfectResidualOf H :=
  Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect H)

omit [Finite G] in
theorem le_prOf {P H : Subgroup G} (hP : ⁅P, P⁆ = P) (hPH : P ≤ H) : P ≤ perfectResidualOf H :=
  perfect_subgroup_le_perfectResidualOf P H (Subgroup.isPerfect_iff.mpr hP) hPH

omit [Finite G] in
theorem prOf_conj_mem (H : Subgroup G) {x : G} (hx : x ∈ H) {m : G}
    (hm : m ∈ perfectResidualOf H) : x * m * x⁻¹ ∈ perfectResidualOf H :=
  (mem_normalizer_iff.mp (perfectResidualOf_normalizer_contains H (le_normalizer hx)) m).mp hm

theorem prOf_conj_le {H H' : Subgroup G} (t : G) (h : ∀ x ∈ H, t * x * t⁻¹ ∈ H')
    {m : G} (hm : m ∈ perfectResidualOf H) : t * m * t⁻¹ ∈ perfectResidualOf H' := by
  set Q : Subgroup G := (perfectResidualOf H).map (MulAut.conj t).toMonoidHom with hQ
  have hQperf : ⁅Q, Q⁆ = Q := by
    rw [hQ, ← Subgroup.map_commutator, prOf_perfect]
  have hQH : Q ≤ H' := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x (prOf_le H hx)
  exact le_prOf hQperf hQH ⟨m, hm, rfl⟩

end PerfectResidual

@[expose] def CentralOddCore {G : Type} [Group G] (M : Subgroup G) : Prop :=
  ∀ Q : Subgroup G, Q ≤ M → (∀ n ∈ M, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q) → Odd (Nat.card Q) →
    ∀ q ∈ Q, ∀ n ∈ M, q * n = n * q

variable {G : Type} [Group G] [Finite G]

structure FacSetup (K W F₁ F₂ H₁ H₂ : Subgroup G) (t : G) : Prop where
  K_le₁ : K ≤ H₁
  K_le₂ : K ≤ H₂
  inf_eq : H₁ ⊓ H₂ = K
  comm_mem : ∀ x ∈ H₁, ∀ y ∈ H₂, ⁅x, y⁆ ∈ K
  norm₁ : ∀ x ∈ H₁ ⊔ H₂, ∀ y ∈ H₁, x * y * x⁻¹ ∈ H₁
  norm₂ : ∀ x ∈ H₁ ⊔ H₂, ∀ y ∈ H₂, x * y * x⁻¹ ∈ H₂
  normK : ∀ x ∈ H₁ ⊔ H₂, ∀ k ∈ K, x * k * x⁻¹ ∈ K
  W_le : W ≤ K
  W_pgroup : IsPGroup 2 W
  W_comm : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w
  W_central : ∀ w ∈ W, ∀ k ∈ K, w * k = k * w
  W_idx : ¬ 2 ∣ W.relIndex K
  F₁_le : F₁ ≤ W
  F₂_le : F₂ ≤ W
  F_disj : F₁ ⊓ F₂ = ⊥
  F_sup : F₁ ⊔ F₂ = W
  normF₁ : ∀ x ∈ H₁ ⊔ H₂, ∀ f ∈ F₁, x * f * x⁻¹ ∈ F₁
  normF₂ : ∀ x ∈ H₁ ⊔ H₂, ∀ f ∈ F₂, x * f * x⁻¹ ∈ F₂
  cent₁ : ∀ x ∈ H₁, ∀ f ∈ F₂, x * f * x⁻¹ = f
  cent₂ : ∀ x ∈ H₂, ∀ f ∈ F₁, x * f * x⁻¹ = f
  fpf₁ : ∃ y ∈ H₁, ∀ f ∈ F₁, y * f * y⁻¹ = f → f = 1
  fpf₂ : ∃ y ∈ H₂, ∀ f ∈ F₂, y * f * y⁻¹ = f → f = 1
  perf₁ : ∀ y ∈ H₁, ∃ k ∈ K, ∃ m ∈ perfectResidualOf H₁, y = k * m
  perf₂ : ∀ y ∈ H₂, ∃ k ∈ K, ∃ m ∈ perfectResidualOf H₂, y = k * m
  t_sq : t * t = 1
  swap₁ : ∀ x ∈ H₁, t * x * t⁻¹ ∈ H₂
  swap₂ : ∀ x ∈ H₂, t * x * t⁻¹ ∈ H₁

namespace FacSetup

variable {K W F₁ F₂ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem symm (S : FacSetup K W F₁ F₂ H₁ H₂ t) : FacSetup K W F₂ F₁ H₂ H₁ t where
  K_le₁ := S.K_le₂
  K_le₂ := S.K_le₁
  inf_eq := by rw [inf_comm]; exact S.inf_eq
  comm_mem := fun x hx y hy => by
    have := K.inv_mem (S.comm_mem y hy x hx)
    rwa [commutatorElement_inv] at this
  norm₁ := fun x hx y hy => S.norm₂ x (by rwa [sup_comm]) y hy
  norm₂ := fun x hx y hy => S.norm₁ x (by rwa [sup_comm]) y hy
  normK := fun x hx k hk => S.normK x (by rwa [sup_comm]) k hk
  W_le := S.W_le
  W_pgroup := S.W_pgroup
  W_comm := S.W_comm
  W_central := S.W_central
  W_idx := S.W_idx
  F₁_le := S.F₂_le
  F₂_le := S.F₁_le
  F_disj := by rw [inf_comm]; exact S.F_disj
  F_sup := by rw [sup_comm]; exact S.F_sup
  normF₁ := fun x hx f hf => S.normF₂ x (by rwa [sup_comm]) f hf
  normF₂ := fun x hx f hf => S.normF₁ x (by rwa [sup_comm]) f hf
  cent₁ := S.cent₂
  cent₂ := S.cent₁
  fpf₁ := S.fpf₂
  fpf₂ := S.fpf₁
  perf₁ := S.perf₂
  perf₂ := S.perf₁
  t_sq := S.t_sq
  swap₁ := S.swap₂
  swap₂ := S.swap₁


section Lemmas

variable (S : FacSetup K W F₁ F₂ H₁ H₂ t)

include S

omit [Finite G] in
theorem F_comm {a b : G} (ha : a ∈ F₁) (hb : b ∈ F₂) : a * b = b * a :=
  S.W_comm a (S.F₁_le ha) b (S.F₂_le hb)

omit [Finite G] in
theorem mem_W_iff {w : G} (hw : w ∈ W) : ∃ a ∈ F₁, ∃ b ∈ F₂, w = a * b := by
  rw [← S.F_sup] at hw
  exact mem_sup_of_forall_comm (fun a ha b hb => S.F_comm ha hb) hw

theorem exists_O₁ : ∃ O₁ : Subgroup G, O₁ ≤ K ∧ Odd (Nat.card O₁) ∧ W ⊓ O₁ = ⊥ ∧
    (∀ k ∈ K, ∃ w ∈ W, ∃ o ∈ O₁, k = w * o) ∧
    (∀ x ∈ H₁ ⊔ H₂, ∀ o ∈ O₁, x * o * x⁻¹ ∈ O₁) ∧ (∀ x ∈ K, Odd (orderOf x) → x ∈ O₁) := by
  obtain ⟨O₁, hOK, hOodd, hWO, hdec, hord, -⟩ :=
    exists_odd_complement_of_central_two S.W_le S.W_central S.W_pgroup S.W_idx
  refine ⟨O₁, hOK, hOodd, hWO, hdec, fun x hx o ho => ?_, hord⟩
  refine hord _ (S.normK x hx o (hOK ho)) ?_
  have h1 : orderOf (x * o * x⁻¹) = orderOf o := by
    have := MulEquiv.orderOf_eq (MulAut.conj x) o
    simpa [MulAut.conj_apply] using this
  rw [h1]
  exact Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O₁ ho)

omit [Finite G] in
theorem exists_fpf_M₁ : ∃ m ∈ perfectResidualOf H₁, ∀ f ∈ F₁, m * f * m⁻¹ = f → f = 1 := by
  obtain ⟨y, hy, hfp⟩ := S.fpf₁
  obtain ⟨k, hk, m, hm, rfl⟩ := S.perf₁ y hy
  refine ⟨m, hm, fun f hf hfix => hfp f hf ?_⟩
  have e : k * m * f * (k * m)⁻¹ = k * (m * f * m⁻¹) * k⁻¹ := by group
  rw [e, hfix]
  have hc : f * k = k * f := S.W_central f (S.F₁_le hf) k hk
  calc k * f * k⁻¹ = (f * k) * k⁻¹ := by rw [hc]
    _ = f := by group

theorem F₁_le_M₁ : F₁ ≤ perfectResidualOf H₁ := by
  obtain ⟨m, hm, hfp⟩ := S.exists_fpf_M₁
  have hmH : m ∈ H₁ ⊔ H₂ := mem_sup_left (prOf_le H₁ hm)
  have hconj : ∀ f ∈ F₁, m * f * m⁻¹ ∈ F₁ := fun f hf => S.normF₁ m hmH f hf
  have hcomm : ∀ a ∈ F₁, ∀ b ∈ F₁, a * b = b * a := fun a ha b hb =>
    S.W_comm a (S.F₁_le ha) b (S.F₁_le hb)
  let φ : ↥F₁ →* ↥F₁ :=
    { toFun := fun f => ⟨(f : G) * (m * (f : G)⁻¹ * m⁻¹),
        F₁.mul_mem f.2 (hconj _ (F₁.inv_mem f.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hX : m * (a : G)⁻¹ * m⁻¹ ∈ F₁ := hconj _ (F₁.inv_mem a.2)
        have hY : m * (b : G)⁻¹ * m⁻¹ ∈ F₁ := hconj _ (F₁.inv_mem b.2)
        have e : m * ((a : G) * (b : G))⁻¹ * m⁻¹ =
            (m * (b : G)⁻¹ * m⁻¹) * (m * (a : G)⁻¹ * m⁻¹) := by group
        show (a : G) * (b : G) * (m * ((a : G) * (b : G))⁻¹ * m⁻¹) =
          (a : G) * (m * (a : G)⁻¹ * m⁻¹) * ((b : G) * (m * (b : G)⁻¹ * m⁻¹))
        rw [e]
        have h1 := hcomm _ hX b b.2
        have h2 := hcomm _ hX _ hY
        calc (a : G) * (b : G) * ((m * (b : G)⁻¹ * m⁻¹) * (m * (a : G)⁻¹ * m⁻¹))
            = (a : G) * (b : G) * ((m * (a : G)⁻¹ * m⁻¹) * (m * (b : G)⁻¹ * m⁻¹)) := by
              rw [← h2]
          _ = (a : G) * ((b : G) * (m * (a : G)⁻¹ * m⁻¹)) * (m * (b : G)⁻¹ * m⁻¹) := by
              simp only [mul_assoc]
          _ = (a : G) * ((m * (a : G)⁻¹ * m⁻¹) * (b : G)) * (m * (b : G)⁻¹ * m⁻¹) := by
              rw [← h1]
          _ = (a : G) * (m * (a : G)⁻¹ * m⁻¹) * ((b : G) * (m * (b : G)⁻¹ * m⁻¹)) := by
              simp only [mul_assoc]) }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have h1 : (f : G) * (m * (f : G)⁻¹ * m⁻¹) = 1 := congrArg Subtype.val hf
    have h2 : m * (f : G)⁻¹ * m⁻¹ = (f : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : m * (f : G) * m⁻¹ = (f : G) := by
      have := congrArg (fun z => z⁻¹) h2
      simpa [mul_assoc] using this
    exact Subtype.ext (hfp f f.2 h3)
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hinj
  intro f' hf'
  obtain ⟨f, hf⟩ := hsurj ⟨f', hf'⟩
  have hfeq : (f : G) * (m * (f : G)⁻¹ * m⁻¹) = f' := congrArg Subtype.val hf
  rw [← hfeq]
  have e : (f : G) * (m * (f : G)⁻¹ * m⁻¹) = ((f : G) * m * (f : G)⁻¹) * m⁻¹ := by group
  rw [e]
  have hfH : (f : G) ∈ H₁ := S.K_le₁ (S.W_le (S.F₁_le f.2))
  exact (perfectResidualOf H₁).mul_mem (prOf_conj_mem H₁ hfH hm) ((perfectResidualOf H₁).inv_mem hm)

theorem eq_one_of_mem_F₂_M₁ {f : G} (hf : f ∈ F₂) (hfM : f ∈ perfectResidualOf H₁) : f = 1 := by
  obtain ⟨O₁, hOK, -, hWO, hdec, hOnorm, -⟩ := S.exists_O₁
  obtain ⟨g, hg, hfp⟩ := S.fpf₂
  set M := perfectResidualOf H₁ with hMdef
  set J : Subgroup G := F₁ ⊔ O₁ with hJdef
  have hgN : g ∈ H₁ ⊔ H₂ := mem_sup_right hg
  have hJmem : ∀ j ∈ J, ∃ a ∈ F₁, ∃ o ∈ O₁, j = a * o := fun j hj =>
    mem_sup_of_forall_comm (fun a ha o ho => S.W_central a (S.F₁_le ha) o (hOK ho)) hj
  have hJnorm : ∀ x ∈ H₁ ⊔ H₂, ∀ j ∈ J, x * j * x⁻¹ ∈ J := by
    intro x hx j hj
    obtain ⟨a, ha, o, ho, rfl⟩ := hJmem j hj
    have e : x * (a * o) * x⁻¹ = (x * a * x⁻¹) * (x * o * x⁻¹) := by group
    rw [e]
    exact J.mul_mem (mem_sup_left (S.normF₁ x hx a ha)) (mem_sup_right (hOnorm x hx o ho))
  have hMN : ∀ x ∈ M, x ∈ H₁ ⊔ H₂ := fun x hx => mem_sup_left (prOf_le H₁ hx)
  have hKJ : ∀ k ∈ K, ∀ m ∈ M, ⁅k, m⁆ ∈ J := by
    intro k hk m hm
    obtain ⟨w, hw, o, ho, rfl⟩ := hdec k hk
    have hmN := hMN m hm
    have hwN : w ∈ H₁ ⊔ H₂ := mem_sup_left (S.K_le₁ (S.W_le hw))
    have h1 : ⁅o, m⁆ ∈ O₁ := by
      have e : ⁅o, m⁆ = o * (m * o⁻¹ * m⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact O₁.mul_mem ho (hOnorm m hmN o⁻¹ (O₁.inv_mem ho))
    have h2 : w * ⁅o, m⁆ * w⁻¹ ∈ J := mem_sup_right (hOnorm w hwN _ h1)
    obtain ⟨a, ha, b, hb, rfl⟩ := S.mem_W_iff hw
    have hbm : m * b * m⁻¹ = b := S.cent₁ m (prOf_le H₁ hm) b hb
    have h3 : ⁅a * b, m⁆ ∈ F₁ := by
      have h1 : m * b = b * m := by
        calc m * b = (m * b * m⁻¹) * m := by group
          _ = b * m := by rw [hbm]
      have hbmb : b * m * b⁻¹ = m := by
        calc b * m * b⁻¹ = (m * b) * b⁻¹ := by rw [h1]
          _ = m := by group
      have e : ⁅a * b, m⁆ = a * (m * a⁻¹ * m⁻¹) := by
        calc ⁅a * b, m⁆ = a * (b * m * b⁻¹) * a⁻¹ * m⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = a * m * a⁻¹ * m⁻¹ := by rw [hbmb]
          _ = a * (m * a⁻¹ * m⁻¹) := by group
      rw [e]
      exact F₁.mul_mem ha (S.normF₁ m hmN a⁻¹ (F₁.inv_mem ha))
    have e2 : ⁅a * b * o, m⁆ = (a * b * ⁅o, m⁆ * (a * b)⁻¹) * ⁅a * b, m⁆ := by
      simp only [commutatorElement_def]; group
    rw [e2]
    have h2' : a * b * ⁅o, m⁆ * (a * b)⁻¹ ∈ J := by
      have := h2
      simpa using this
    exact J.mul_mem h2' (mem_sup_left h3)
  have hcomm := perfect_comm_mem (M := M) (J := J) (Kc := K) (g := g) (prOf_perfect H₁)
    (fun x hx j hj => hJnorm x (hMN x hx) j hj) (fun j hj => hJnorm g hgN j hj)
    (fun m hm => ⟨S.comm_mem m (prOf_le H₁ hm) g hg,
      S.comm_mem m (prOf_le H₁ hm) g⁻¹ (H₂.inv_mem hg)⟩) hKJ f hfM
  have hF₂ : ⁅f, g⁆ ∈ F₂ := by
    have e : ⁅f, g⁆ = f * (g * f⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact F₂.mul_mem hf (S.normF₂ g hgN f⁻¹ (F₂.inv_mem hf))
  obtain ⟨a, ha, o, ho, hao⟩ := hJmem _ hcomm
  have hoW : o ∈ W := by
    have e : o = a⁻¹ * ⁅f, g⁆ := by rw [hao]; group
    rw [e]
    exact W.mul_mem (W.inv_mem (S.F₁_le ha)) (S.F₂_le hF₂)
  have ho1 : o = 1 := by
    have : o ∈ W ⊓ O₁ := ⟨hoW, ho⟩
    rw [hWO, Subgroup.mem_bot] at this
    exact this
  have hcg : ⁅f, g⁆ ∈ F₁ ⊓ F₂ := ⟨by rw [hao, ho1, mul_one]; exact ha, hF₂⟩
  rw [S.F_disj, Subgroup.mem_bot] at hcg
  have hfix : g * f * g⁻¹ = f := by
    have e : ⁅f, g⁆ = (f * g * f⁻¹ * g⁻¹) := by simp only [commutatorElement_def]
    have h0 : f * g * f⁻¹ * g⁻¹ = 1 := by rw [← e]; exact hcg
    have : f * g = g * f := by
      have h1 := mul_inv_eq_one.mp h0
      calc f * g = (f * g * f⁻¹) * f := by group
        _ = g * f := by rw [h1]
    calc g * f * g⁻¹ = (f * g) * g⁻¹ := by rw [this]
      _ = f := by group
  exact hfp f hf hfix

theorem normM₁ {x : G} (hx : x ∈ H₁ ⊔ H₂) {m : G} (hm : m ∈ perfectResidualOf H₁) :
    x * m * x⁻¹ ∈ perfectResidualOf H₁ :=
  prOf_conj_le x (fun y hy => S.norm₁ x hx y hy) hm

theorem normM₂ {x : G} (hx : x ∈ H₁ ⊔ H₂) {m : G} (hm : m ∈ perfectResidualOf H₂) :
    x * m * x⁻¹ ∈ perfectResidualOf H₂ :=
  prOf_conj_le x (fun y hy => S.norm₂ x hx y hy) hm

theorem inf_M₁_eq : W ⊓ perfectResidualOf H₁ = F₁ := by
  refine le_antisymm (fun w hw => ?_) (le_inf S.F₁_le S.F₁_le_M₁)
  obtain ⟨hwW, hwM⟩ := hw
  obtain ⟨a, ha, b, hb, rfl⟩ := S.mem_W_iff hwW
  have hbM : b ∈ perfectResidualOf H₁ := by
    have := (perfectResidualOf H₁).mul_mem ((perfectResidualOf H₁).inv_mem (S.F₁_le_M₁ ha)) hwM
    simpa using this
  have hb1 := S.eq_one_of_mem_F₂_M₁ hb hbM
  rw [hb1, mul_one]
  exact ha

theorem inf_M₂_eq : W ⊓ perfectResidualOf H₂ = F₂ := S.symm.inf_M₁_eq

omit [Finite G] in
theorem mem_W_of_two_power {x : G} (hx : x ∈ K) (h2 : ∃ k : ℕ, orderOf x = 2 ^ k) : x ∈ W := by
  obtain ⟨k, hk⟩ := h2
  have hnormal : (W.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have h1 : (n : G) * g = g * n := S.W_central _ hn g g.2
    have h2 : ((g * n * g⁻¹ : K) : G) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h1, mul_inv_cancel_right]
    rw [h2]
    exact hn
  have hmem : x ^ W.relIndex K ∈ W := by
    have := Subgroup.pow_index_mem (W.subgroupOf K) (⟨x, hx⟩ : K)
    exact mem_subgroupOf.mp this
  have hcop : (W.relIndex K).gcd (orderOf x) = 1 := by
    rw [hk]
    have : Nat.Coprime (W.relIndex K) 2 :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 S.W_idx))
    exact Nat.Coprime.pow_right k this
  exact Subgroup.zpowers_le.2 hmem (mem_zpowers_pow_iff.2 hcop)

theorem odd_card_inf_M : Odd (Nat.card ↥(perfectResidualOf H₁ ⊓ perfectResidualOf H₂)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have h2 : 2 ∣ Nat.card ↥(perfectResidualOf H₁ ⊓ perfectResidualOf H₂) := by
    rcases Nat.even_or_odd (Nat.card ↥(perfectResidualOf H₁ ⊓ perfectResidualOf H₂)) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hne
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(perfectResidualOf H₁ ⊓ perfectResidualOf H₂)) 2 h2
  have hxM := x.2
  have hxK : (x : G) ∈ K := by
    have : (x : G) ∈ H₁ ⊓ H₂ := ⟨prOf_le H₁ hxM.1, prOf_le H₂ hxM.2⟩
    rwa [S.inf_eq] at this
  have hx2 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxW : (x : G) ∈ W := S.mem_W_of_two_power hxK ⟨1, by rw [hx2]; rfl⟩
  have hF₁ : (x : G) ∈ F₁ := by rw [← S.inf_M₁_eq]; exact ⟨hxW, hxM.1⟩
  have hF₂ : (x : G) ∈ F₂ := by rw [← S.inf_M₂_eq]; exact ⟨hxW, hxM.2⟩
  have h1 : (x : G) ∈ F₁ ⊓ F₂ := ⟨hF₁, hF₂⟩
  rw [S.F_disj, Subgroup.mem_bot] at h1
  rw [h1, orderOf_one] at hx2
  omega

theorem swap_M₁ {m : G} (hm : m ∈ perfectResidualOf H₁) :
    t * m * t⁻¹ ∈ perfectResidualOf H₂ := prOf_conj_le t S.swap₁ hm

theorem swap_M₂ {m : G} (hm : m ∈ perfectResidualOf H₂) :
    t * m * t⁻¹ ∈ perfectResidualOf H₁ := prOf_conj_le t S.swap₂ hm

theorem comm_M_mem {m₁ m₂ : G} (h₁ : m₁ ∈ perfectResidualOf H₁) (h₂ : m₂ ∈ perfectResidualOf H₂) :
    ⁅m₁, m₂⁆ ∈ perfectResidualOf H₁ ⊓ perfectResidualOf H₂ := by
  have hm₁ : m₁ ∈ H₁ ⊔ H₂ := mem_sup_left (prOf_le H₁ h₁)
  have hm₂ : m₂ ∈ H₁ ⊔ H₂ := mem_sup_right (prOf_le H₂ h₂)
  constructor
  · have e : ⁅m₁, m₂⁆ = m₁ * (m₂ * m₁⁻¹ * m₂⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (perfectResidualOf H₁).mul_mem h₁
      (S.normM₁ hm₂ ((perfectResidualOf H₁).inv_mem h₁) |> fun h => by simpa [mul_assoc] using h)
  · have e : ⁅m₁, m₂⁆ = (m₁ * m₂ * m₁⁻¹) * m₂⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (perfectResidualOf H₂).mul_mem (S.normM₂ hm₁ h₂) ((perfectResidualOf H₂).inv_mem h₂)

theorem normM_sup {x : G} (hx : x ∈ H₁ ⊔ H₂) {m : G}
    (hm : m ∈ perfectResidualOf H₁ ⊔ perfectResidualOf H₂) :
    x * m * x⁻¹ ∈ perfectResidualOf H₁ ⊔ perfectResidualOf H₂ := by
  have h : perfectResidualOf H₁ ⊔ perfectResidualOf H₂ ≤
      (perfectResidualOf H₁ ⊔ perfectResidualOf H₂).comap (MulAut.conj x).toMonoidHom := by
    refine sup_le (fun m hm => ?_) (fun m hm => ?_)
    · exact mem_comap.mpr (mem_sup_left (S.normM₁ hx hm))
    · exact mem_comap.mpr (mem_sup_right (S.normM₂ hx hm))
  have := h hm
  simpa [MulAut.conj_apply] using this

theorem mem_Y_iff {y : G} (hy : y ∈ H₁ ⊔ H₂) :
    ∃ k ∈ K, ∃ m ∈ perfectResidualOf H₁ ⊔ perfectResidualOf H₂, y = k * m := by
  have hle : H₂ ≤ normalizer (H₁ : Set G) := fun x hx =>
    Subgroup.mem_normalizer_fintype fun n hn => S.norm₁ x (mem_sup_right hx) n hn
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H₁ H₂ hle] at hy
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hy
  obtain ⟨k₁, hk₁, m₁, hm₁, rfl⟩ := S.perf₁ h₁ hh₁
  obtain ⟨k₂, hk₂, m₂, hm₂, rfl⟩ := S.perf₂ h₂ hh₂
  have hm₁N : m₁ ∈ H₁ ⊔ H₂ := mem_sup_left (prOf_le H₁ hm₁)
  have hk₂' : m₁ * k₂ * m₁⁻¹ ∈ K := S.normK m₁ hm₁N k₂ hk₂
  refine ⟨k₁ * (m₁ * k₂ * m₁⁻¹), K.mul_mem hk₁ hk₂', m₁ * m₂,
    Subgroup.mul_mem_sup hm₁ hm₂, ?_⟩
  group

omit [Finite G] in
theorem pow_mem_W {k : G} (hk : k ∈ K) : ∃ n : ℕ, Odd n ∧ k ^ n ∈ W := by
  have hnormal : (W.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have h1 : (n : G) * g = g * n := S.W_central _ hn g g.2
    have h2 : ((g * n * g⁻¹ : K) : G) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h1, mul_inv_cancel_right]
    rw [h2]
    exact hn
  have hmem : k ^ W.relIndex K ∈ W := by
    have := Subgroup.pow_index_mem (W.subgroupOf K) (⟨k, hk⟩ : K)
    exact mem_subgroupOf.mp this
  exact ⟨W.relIndex K, Nat.odd_iff.mpr (by have := S.W_idx; omega), hmem⟩

theorem prOf_sup : perfectResidualOf (H₁ ⊔ H₂) = perfectResidualOf H₁ ⊔ perfectResidualOf H₂ := by
  apply le_antisymm
  · set Y : Subgroup G := H₁ ⊔ H₂ with hY
    set M : Subgroup G := perfectResidualOf H₁ ⊔ perfectResidualOf H₂ with hM
    have hMY : M ≤ Y :=
      sup_le (le_trans (prOf_le H₁) le_sup_left) (le_trans (prOf_le H₂) le_sup_right)
    have hnorm : (M.subgroupOf Y).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMY]
      exact fun x hx => Subgroup.mem_normalizer_fintype fun n hn => S.normM_sup hx hn
    let ψ : ↥Y →* ↥Y ⧸ M.subgroupOf Y := QuotientGroup.mk' (M.subgroupOf Y)
    have hWM : W ≤ M := by
      intro w hw
      obtain ⟨a, ha, b, hb, rfl⟩ := S.mem_W_iff hw
      exact M.mul_mem (mem_sup_left (S.F₁_le_M₁ ha)) (mem_sup_right (S.symm.F₁_le_M₁ hb))
    have hodd : Odd (Nat.card (↥Y ⧸ M.subgroupOf Y)) := by
      by_contra hne
      have h2 : 2 ∣ Nat.card (↥Y ⧸ M.subgroupOf Y) := by
        rcases Nat.even_or_odd (Nat.card (↥Y ⧸ M.subgroupOf Y)) with he | ho
        · exact even_iff_two_dvd.mp he
        · exact absurd ho hne
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y ⧸ M.subgroupOf Y) 2 h2
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk, m, hm, hyk⟩ := S.mem_Y_iff y.2
      obtain ⟨n, hnodd, hkn⟩ := S.pow_mem_W hk
      have hkY : k ∈ Y := S.K_le₁ hk |> fun h => mem_sup_left h
      have hmY : m ∈ Y := hMY hm
      have hy : y = ⟨k, hkY⟩ * ⟨m, hmY⟩ := Subtype.ext hyk
      have hmq : (QuotientGroup.mk (⟨m, hmY⟩ : ↥Y) : ↥Y ⧸ M.subgroupOf Y) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hm)
      have hkn' : (QuotientGroup.mk (⟨k, hkY⟩ : ↥Y) : ↥Y ⧸ M.subgroupOf Y) ^ n = 1 := by
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact mem_subgroupOf.mpr (hWM hkn)
      have hqn : (QuotientGroup.mk y : ↥Y ⧸ M.subgroupOf Y) ^ n = 1 := by
        rw [hy, QuotientGroup.mk_mul, hmq, mul_one]
        exact hkn'
      have hdvd : 2 ∣ n := hq ▸ orderOf_dvd_of_pow_eq_one hqn
      exact (Nat.not_even_iff_odd.mpr hnodd) (even_iff_two_dvd.mpr hdvd)
    have hsolv : Group.IsSolvable (↥Y ⧸ M.subgroupOf Y) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hmap := finite_perfectResidual_map_eq ψ (QuotientGroup.mk'_surjective _)
    rw [(finite_perfectResidual_eq_bot_iff_solvable).mpr hsolv] at hmap
    have hker : perfectResidual ↥Y ≤ M.subgroupOf Y := by
      intro x hx
      have : ψ x ∈ (⊥ : Subgroup (↥Y ⧸ M.subgroupOf Y)) := hmap ▸ Subgroup.mem_map_of_mem ψ hx
      exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp this)
    calc perfectResidualOf Y = (perfectResidual ↥Y).map Y.subtype := rfl
      _ ≤ (M.subgroupOf Y).map Y.subtype := Subgroup.map_mono hker
      _ = M := Subgroup.map_subgroupOf_eq_of_le hMY
  · refine sup_le (le_prOf (prOf_perfect H₁) (le_trans (prOf_le H₁) le_sup_left)) ?_
    exact le_prOf (prOf_perfect H₂) (le_trans (prOf_le H₂) le_sup_right)

theorem isSylowOf_F₁_inf_K : CFSG.ABGLocalTools.IsSylowOf 2 F₁ (perfectResidualOf H₁ ⊓ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁, hT₁⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (perfectResidualOf H₁ ⊓ K)
  have hT₁F : T₁ ≤ F₁ := by
    intro x hx
    have hxMK := hT₁.le hx
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hT₁.isPGroup ⟨x, hx⟩
    have hxW : x ∈ W := S.mem_W_of_two_power hxMK.2
      ⟨n, by rwa [Subgroup.orderOf_mk] at hn⟩
    rw [← S.inf_M₁_eq]
    exact ⟨hxW, hxMK.1⟩
  have hF₁le : F₁ ≤ perfectResidualOf H₁ ⊓ K := le_inf S.F₁_le_M₁ (S.F₁_le.trans S.W_le)
  have hF₁p : IsPGroup 2 F₁ := S.W_pgroup.to_le S.F₁_le
  have := hT₁.eq_of_le hT₁F hF₁le hF₁p
  rw [this]
  exact hT₁

theorem card_M₁ : Nat.card (perfectResidualOf H₁) =
    Nat.card ↥(perfectResidualOf H₁ ⊓ K) * K.relIndex H₁ := by
  have hMH : perfectResidualOf H₁ ≤ H₁ := prOf_le H₁
  have hKH : K ≤ H₁ := S.K_le₁
  have hKn : (K.subgroupOf H₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH]
    exact fun x hx =>
      Subgroup.mem_normalizer_fintype fun n hn => S.normK x (mem_sup_left hx) n hn
  have htop : (perfectResidualOf H₁).subgroupOf H₁ ⊔ K.subgroupOf H₁ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨k, hk, m, hm, hym⟩ := S.perf₁ y y.2
    have hy : y = ⟨k, hKH hk⟩ * ⟨m, hMH hm⟩ := Subtype.ext hym
    rw [hy, sup_comm]
    exact Subgroup.mul_mem_sup (mem_subgroupOf.mpr hk) (mem_subgroupOf.mpr hm)
  have h1 : (K.subgroupOf H₁).relIndex
        ((perfectResidualOf H₁).subgroupOf H₁ ⊔ K.subgroupOf H₁) =
      (K.subgroupOf H₁).relIndex ((perfectResidualOf H₁).subgroupOf H₁) :=
    (have := hKn; Subgroup.relIndex_sup_right _ _)
  rw [htop, Subgroup.relIndex_top_right] at h1
  have h2 := Subgroup.relIndex_mul_card (K.subgroupOf H₁) ((perfectResidualOf H₁).subgroupOf H₁)
  have hcM : Nat.card ↥((perfectResidualOf H₁).subgroupOf H₁) =
      Nat.card (perfectResidualOf H₁) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv
  have hinf : K.subgroupOf H₁ ⊓ (perfectResidualOf H₁).subgroupOf H₁ =
      (K ⊓ perfectResidualOf H₁).subgroupOf H₁ := (Subgroup.comap_inf _ _ _).symm
  have hcI : Nat.card ↥((K ⊓ perfectResidualOf H₁).subgroupOf H₁) =
      Nat.card ↥(K ⊓ perfectResidualOf H₁) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hMH)).toEquiv
  rw [hinf, hcI, hcM] at h2
  rw [inf_comm, ← h2]
  show _ = _ * (K.subgroupOf H₁).index
  rw [h1, mul_comm]

omit S in
theorem factorization_sixty_two : (60 : ℕ).factorization 2 = 2 := by
  have h : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem card_sylow_M₁ {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (perfectResidualOf H₁))
    (h60 : K.relIndex H₁ = 60) (hF : Nat.card F₁ = 16) : Nat.card T = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' := (S.isSylowOf_F₁_inf_K).card_eq
  rw [hF] at hF'
  have h4 : (Nat.card ↥(perfectResidualOf H₁ ⊓ K)).factorization 2 = 4 :=
    Nat.pow_right_injective (le_refl 2) (show 2 ^ _ = 2 ^ 4 by rw [← hF'])
  rw [hT.card_eq, S.card_M₁, h60]
  have hpos : Nat.card ↥(perfectResidualOf H₁ ⊓ K) ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_mul hpos (by norm_num), Finsupp.add_apply, h4, factorization_sixty_two]
  norm_num

theorem inf_M_normalized {n : G} (hn : n ∈ perfectResidualOf H₁ ⊔ perfectResidualOf H₂) {q : G}
    (hq : q ∈ perfectResidualOf H₁ ⊓ perfectResidualOf H₂) :
    n * q * n⁻¹ ∈ perfectResidualOf H₁ ⊓ perfectResidualOf H₂ := by
  have hnY : n ∈ H₁ ⊔ H₂ :=
    sup_le (le_trans (prOf_le H₁) le_sup_left) (le_trans (prOf_le H₂) le_sup_right) hn
  exact ⟨S.normM₁ hnY hq.1, S.normM₂ hnY hq.2⟩

theorem comm_eq_bot (hZ : CentralOddCore (perfectResidualOf H₁ ⊔ perfectResidualOf H₂)) :
    ⁅perfectResidualOf H₁, perfectResidualOf H₂⁆ = ⊥ := by
  set M₁ := perfectResidualOf H₁ with hM₁
  set M₂ := perfectResidualOf H₂ with hM₂
  have hQ := hZ (M₁ ⊓ M₂) (inf_le_left.trans le_sup_left)
    (fun n hn q hq => S.inf_M_normalized hn hq) S.odd_card_inf_M
  have hcomm_le : ⁅M₁, M₂⁆ ≤ M₁ ⊓ M₂ :=
    Subgroup.commutator_le.mpr fun a ha b hb => S.comm_M_mem ha hb
  have h1 : ⁅⁅M₁, M₂⁆, M₁⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine hcomm_le.trans fun q hq => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (hQ q hq n (mem_sup_left hn)).symm
  have h2 : ⁅⁅M₂, M₁⁆, M₁⁆ = ⊥ := by
    rw [Subgroup.commutator_comm M₂ M₁]
    exact h1
  have h3 : ⁅⁅M₁, M₁⁆, M₂⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [prOf_perfect H₁] at h3

end Lemmas

end FacSetup

end CFSG.OddStandard.Seitz77
