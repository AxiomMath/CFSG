module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporQuotE
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporGood

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

theorem GoodLocal.of_data_E {X : Type*} [Group X] {Kx : Subgroup X} [Finite ↥Kx]
    (Q : Subgroup ↥Kx) [Q.Normal] (hQ2 : IsPGroup 2 Q)
    (hcent : ∀ y : ↥Kx, (∀ q ∈ Q, y * q = q * y) → y ∈ Q)
    (hE : ∀ b : ↥Kx, orderOf b = 3 → ∃ x ∈ ⁅Q, Subgroup.zpowers b⁆,
      ∃ y ∈ ⁅Q, Subgroup.zpowers b⁆, x * y ≠ y * x ∨ x * x ≠ 1) : GoodLocal Kx := by
  intro G _ _ K φ hφ hker
  exact charTwo_noChi0_of_quotient_E φ hφ hker Q hQ2 hcent hE

theorem card_le_length_of_sub {Y : Type*} (U : Set Y) (L : List Y) (hL : L.Nodup)
    (hsub : ∀ x ∈ U, x ∈ L) : Nat.card ↥U ≤ L.length := by
  classical
  have h1 : U ⊆ (↑L.toFinset : Set Y) := fun x hx => List.mem_toFinset.2 (hsub x hx)
  have h2 := Set.ncard_le_ncard h1 (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hL, ← Nat.card_coe_set_eq] at h2
  exact h2

section Good

variable {X : Type*} [Group X] [Finite X] {E : Type*}

theorem goodLocal_of_gens_E (enc : X → E) (henc : Function.Injective enc) (Kx : Subgroup X)
    (Kl : List X) (hK : ∀ x, x ∈ Kx ↔ x ∈ Kl) (kgens : List X)
    (hKcl : ∀ x ∈ Kl, x ∈ Subgroup.closure {g | g ∈ kgens}) (Ql : List X)
    (hQK : ∀ q ∈ Ql, q ∈ Kl) (h1 : (1 : X) ∈ Ql)
    (hmul : ∀ p ∈ Ql, ∀ q ∈ Ql, enc (p * q) ∈ Ql.map enc)
    (hnorm : ∀ k ∈ kgens, ∀ q ∈ Ql,
      enc (k * q * k⁻¹) ∈ Ql.map enc ∧ enc (k⁻¹ * q * k) ∈ Ql.map enc)
    {a : ℕ} (h2 : ∀ q ∈ Ql, q ^ (2 ^ a) = 1)
    (hcent : ∀ y ∈ Kl, (∀ q ∈ Ql, enc (y * q) = enc (q * y)) → enc y ∈ Ql.map enc)
    (hE : ∀ b ∈ Kl, b ≠ 1 → b ^ 3 = 1 → ∃ p ∈ Ql, ∃ q ∈ Ql,
      enc ((p * b * p⁻¹ * b⁻¹) * (q * b * q⁻¹ * b⁻¹)) ≠
        enc ((q * b * q⁻¹ * b⁻¹) * (p * b * p⁻¹ * b⁻¹)) ∨
      enc ((p * b * p⁻¹ * b⁻¹) * (p * b * p⁻¹ * b⁻¹)) ≠ enc 1) :
    GoodLocal Kx := by
  classical
  have hmul' : ∀ p ∈ Ql, ∀ q ∈ Ql, p * q ∈ Ql := fun p hp q hq =>
    (mem_map_enc henc).1 (hmul p hp q hq)
  obtain ⟨Qx, hQx⟩ := subgroupOfList_exists Ql h1 hmul'
  have hQxK : Qx ≤ Kx := fun x hx => (hK x).2 (hQK x ((hQx x).1 hx))
  have hgen : ∀ k ∈ kgens, ∀ q ∈ Qx, k * q * k⁻¹ ∈ Qx ∧ k⁻¹ * q * k ∈ Qx := by
    intro k hk q hq
    have h := hnorm k hk q ((hQx q).1 hq)
    exact ⟨(hQx _).2 ((mem_map_enc henc).1 h.1), (hQx _).2 ((mem_map_enc henc).1 h.2)⟩
  have hall : ∀ k ∈ Subgroup.closure {g | g ∈ kgens},
      ∀ q ∈ Qx, k * q * k⁻¹ ∈ Qx ∧ k⁻¹ * q * k ∈ Qx := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem g hg => exact hgen g hg
    | one => intro q hq; simpa using hq
    | mul a b _ _ ha hb =>
      intro q hq
      refine ⟨?_, ?_⟩
      · have := (ha _ (hb q hq).1).1
        simpa [mul_assoc] using this
      · have := (hb _ (ha q hq).2).2
        simpa [mul_assoc] using this
    | inv a _ ha =>
      intro q hq
      exact ⟨by simpa using (ha q hq).2, by simpa using (ha q hq).1⟩
  let Q : Subgroup ↥Kx := Qx.subgroupOf Kx
  have hmemQ : ∀ y : ↥Kx, y ∈ Q ↔ (y : X) ∈ Ql := fun y =>
    Subgroup.mem_subgroupOf.trans (hQx _)
  have hQN : Q.Normal := ⟨fun n hn g => by
    rw [hmemQ] at hn ⊢
    exact (hQx _).1 ((hall g (hKcl g ((hK _).1 g.2)) n ((hQx n).2 hn)).1)⟩
  have hQ2 : IsPGroup 2 Q := by
    intro g
    refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
    have := h2 _ ((hmemQ _).1 g.2)
    simpa using this
  have hcent' : ∀ y : ↥Kx, (∀ q ∈ Q, y * q = q * y) → y ∈ Q := by
    intro y hy
    rw [hmemQ]
    refine (mem_map_enc henc).1 (hcent _ ((hK _).1 y.2) fun q hq => ?_)
    have hqK : q ∈ Kx := (hK q).2 (hQK q hq)
    have h := hy ⟨q, hqK⟩ ((hmemQ _).2 hq)
    have h' : (y : X) * q = q * (y : X) := congrArg Subtype.val h
    rw [h']
  have hE' : ∀ b : ↥Kx, orderOf b = 3 → ∃ x ∈ ⁅Q, Subgroup.zpowers b⁆,
      ∃ y ∈ ⁅Q, Subgroup.zpowers b⁆, x * y ≠ y * x ∨ x * x ≠ 1 := by
    intro b hb
    have hb1 : (b : X) ≠ 1 := by
      intro h
      have : b = 1 := Subtype.ext h
      rw [this, orderOf_one] at hb
      omega
    have hb3 : (b : X) ^ 3 = 1 := by
      have := pow_orderOf_eq_one b
      rw [hb] at this
      exact congrArg Subtype.val this
    obtain ⟨p, hp, q, hq, hne⟩ := hE _ ((hK _).1 b.2) hb1 hb3
    have hpK : p ∈ Kx := (hK p).2 (hQK p hp)
    have hqK : q ∈ Kx := (hK q).2 (hQK q hq)
    refine ⟨⁅(⟨p, hpK⟩ : ↥Kx), b⁆, Subgroup.commutator_mem_commutator ((hmemQ _).2 hp)
      (Subgroup.mem_zpowers b), ⁅(⟨q, hqK⟩ : ↥Kx), b⁆,
      Subgroup.commutator_mem_commutator ((hmemQ _).2 hq) (Subgroup.mem_zpowers b), ?_⟩
    rcases hne with hne | hne
    · left
      intro h
      apply hne
      have := congrArg Subtype.val h
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [this]
    · right
      intro h
      apply hne
      have := congrArg Subtype.val h
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
        at this
      rw [this]
  exact @GoodLocal.of_data_E X _ Kx _ Q hQN hQ2 hcent' hE'

end Good

end CFSG.QuasithinUnique.Vol2Native.L239
