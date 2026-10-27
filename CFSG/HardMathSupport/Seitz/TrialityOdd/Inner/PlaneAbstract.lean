module

public import CFSG.RankThree.PartOne.K1214.SylowShape
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenConsumer

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.SEITZ11.G2Seven

variable {G : Type*} [Group G]

theorem eq_of_pow_eq_one_of_sylowShape [Finite G] {p e : ℕ} [Fact p.Prime]
    (hshape : SylowShape p 2 e G) (S : Sylow p G) {E₀ : Subgroup G} (hE₀S : E₀ ≤ (S : Subgroup G))
    (hE₀c : Nat.card E₀ = p ^ 2) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) :
    ∀ x ∈ (S : Subgroup G), x ^ p = 1 → x ∈ E₀ := by
  obtain ⟨φ⟩ := hshape (S : Subgroup G) S.isPGroup' (Sylow.not_dvd_index S)
  intro x hx hxp
  have hcomm : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * b = b * a := by
    intro a ha b hb
    have h : (⟨a, ha⟩ : (S : Subgroup G)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      φ.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
    exact congrArg Subtype.val h
  let W : Subgroup G :=
    { carrier := {y | y ∈ (S : Subgroup G) ∧ y ^ p = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        refine ⟨(S : Subgroup G).mul_mem ha hb, ?_⟩
        rw [(show Commute a b from hcomm a ha b hb).mul_pow, ha1, hb1, one_mul]
      one_mem' := ⟨(S : Subgroup G).one_mem, one_pow p⟩
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        exact ⟨(S : Subgroup G).inv_mem ha, by rw [inv_pow, ha1, inv_one]⟩ }
  have hWle : Nat.card W ≤ p ^ 2 := by
    have hexp : ∀ w ∈ W.subgroupOf (S : Subgroup G), w ^ p = 1 := by
      intro w hw
      exact Subtype.ext (hw.2)
    have h1 := card_le_sq_of_exponent (Fact.out : p.Prime)
      ((W.subgroupOf (S : Subgroup G)).map φ.toMonoidHom) (by
        rintro _ ⟨w, hw, rfl⟩
        rw [← map_pow, hexp w hw, map_one])
    rw [Subgroup.card_map_of_injective φ.injective] at h1
    have h2 : Nat.card (W.subgroupOf (S : Subgroup G)) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (fun y (hy : y ∈ W) => (hy : y ∈ (S : Subgroup G) ∧ y ^ p = 1).1)).toEquiv
    omega
  have hE₀W : E₀ ≤ W := fun y hy => ⟨hE₀S hy, hE₀p y hy⟩
  have hEW : E₀ = W := by
    refine Subgroup.eq_of_le_of_card_ge hE₀W ?_
    rw [hE₀c]
    exact hWle
  have hxW : x ∈ W := ⟨hx, hxp⟩
  rw [hEW]
  exact hxW

theorem mem_zpowers_of_mem_zpowers_of_ne_one {p : ℕ} [Fact p.Prime] {v x : G}
    (hv : orderOf v = p) (hx : x ∈ zpowers v) (hx1 : x ≠ 1) : v ∈ zpowers x := by
  have hp : p.Prime := Fact.out
  have hxp : x ^ p = 1 := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hv, pow_orderOf_eq_one,
      one_zpow]
  have hox : orderOf x = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hxp) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hfin : Finite (zpowers v) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers, hv]; exact hp.ne_zero)
  have heq : zpowers x = zpowers v := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hx) (by
    rw [Nat.card_zpowers, Nat.card_zpowers, hox, hv])
  rw [heq]
  exact mem_zpowers v

theorem exists_plane_of_commute {p : ℕ} [Fact p.Prime] {b v : G} (hb : orderOf b = p)
    (hv : orderOf v = p) (hc : Commute b v) (hnot : v ∉ zpowers b) :
    ∃ E : Subgroup G, b ∈ E ∧ v ∈ E ∧ (∀ x ∈ E, x ^ p = 1) ∧ Nat.card E = p ^ 2 ∧
      ∀ H : Subgroup G, b ∈ H → v ∈ H → E ≤ H := by
  have hp : p.Prime := Fact.out
  have hcomm : ∀ (m : zpowers b) (n : zpowers v), Commute ((zpowers b).subtype m)
      ((zpowers v).subtype n) := by
    rintro ⟨m, hm⟩ ⟨n, hn⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    exact hc.zpow_zpow i j
  let ψ := (zpowers b).subtype.noncommCoprod (zpowers v).subtype hcomm
  have hψ : ∀ m n, ψ (m, n) = (m : G) * (n : G) := fun m n => by
    simp [ψ]
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m, n⟩ h
    rw [hψ] at h
    have hn : (n : G) = (m : G)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hn1 : (n : G) = 1 := by
      by_contra hne
      refine hnot (zpowers_le.2 ?_ (mem_zpowers_of_mem_zpowers_of_ne_one hv n.2 hne))
      rw [hn]
      exact inv_mem m.2
    have hm1 : (m : G) = 1 := by
      rw [hn1, mul_one] at h
      exact h
    exact Prod.ext (Subtype.ext hm1) (Subtype.ext hn1)
  have hpow : ∀ (g : G), orderOf g = p → ∀ x ∈ zpowers g, x ^ p = 1 := by
    intro g hg x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hg, pow_orderOf_eq_one,
      one_zpow]
  refine ⟨ψ.range, ⟨(⟨b, mem_zpowers b⟩, 1), by simp [hψ]⟩, ⟨(1, ⟨v, mem_zpowers v⟩), by simp [hψ]⟩,
    ?_, ?_, ?_⟩
  · rintro _ ⟨⟨m, n⟩, rfl⟩
    rw [hψ]
    have h := (hcomm m n).mul_pow p
    simp only [Subgroup.coe_subtype] at h
    rw [h, hpow b hb m m.2, hpow v hv n n.2, one_mul]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, hb, hv, sq]
  · intro H hbH hvH
    rintro _ ⟨⟨m, n⟩, rfl⟩
    rw [hψ]
    exact mul_mem (zpowers_le.2 hbH m.2) (zpowers_le.2 hvH n.2)

theorem closure_cenGen_eq_top_of_subgroup_centralizer [Finite G] {p e : ℕ} [Fact p.Prime]
    (hshape : SylowShape p 2 e G) (J A E₀ : Subgroup G)
    (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2)
    (hJgen : closure (cenGen (E₀.subgroupOf J)) = ⊤)
    (b : G) (hb : b ∈ E₀) (hb1 : b ≠ 1) (hAb : ∀ a ∈ A, a * b = b * a) (hJA : J ⊔ A = ⊤)
    (F : Subgroup G) (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    closure (cenGen F) = ⊤ := by
  have hp : p.Prime := Fact.out
  have hJle : J ≤ closure (cenGen E₀) := by
    have h1 : (closure (cenGen (E₀.subgroupOf J))).map J.subtype ≤ closure (cenGen E₀) := by
      rw [MonoidHom.map_closure]
      refine closure_mono ?_
      rintro _ ⟨k, ⟨x, hx, hx1, hk⟩, rfl⟩
      refine ⟨(x : G), hx, fun h => hx1 (Subtype.ext h), ?_⟩
      exact congrArg Subtype.val hk
    rw [hJgen, Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1
  have hAle : A ≤ closure (cenGen E₀) := fun a ha => subset_closure ⟨b, hb, hb1, hAb a ha⟩
  have htop : closure (cenGen E₀) = ⊤ := by
    rw [eq_top_iff, ← hJA]
    exact sup_le hJle hAle
  have hE₀p' : IsPGroup p E₀ := IsPGroup.of_card (n := 2) hE₀c
  obtain ⟨S, hS⟩ := hE₀p'.exists_le_sylow
  obtain ⟨g, hg⟩ := plane_conj S (T := (S : Subgroup G)) le_rfl
    (E := E₀) (eq_of_pow_eq_one_of_sylowShape hshape S hS hE₀c hE₀p) hE₀c hFp hFc
  rw [hg, closure_cenGen_cj, htop, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
