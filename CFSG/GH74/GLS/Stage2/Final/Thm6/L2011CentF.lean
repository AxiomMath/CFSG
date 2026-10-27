module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012NFOdd
public import CFSG.GH74.GLS.Stage2.Final.Thm4.L193Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72a

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
  CFSG.GH74.GLS.Stage2.Final.Thm4.L193
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (Op_le Op_Fm_eq Fm_le_of_forall)
open CFSG.GH74.GLS.Stage2.Final.Thm6.L20 (Fm_isNilpotent odd_orderOf_of_mem_pPrimeCoreOf Op_conj_mem)

section PartA

variable {G : Type} [Group G] [Finite G]

theorem mem_Op_of_pow_eq_one {F : Subgroup G} (hF : Group.IsNilpotent ↥F) {r : ℕ} [Fact r.Prime] {e : G}
    (he : e ∈ F) {k : ℕ} (hk : e ^ (r ^ k) = 1) : e ∈ Op r F := by
  set e' : ↥F := ⟨e, he⟩ with he'
  have hord : orderOf e' ∣ r ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext hk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : r.Prime)).1 hord
  have hz : IsPGroup r (Subgroup.zpowers e') := IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨P, hP⟩ := hz.exists_le_sylow
  have hnormal := Group.IsNilpotent.sylow_normal hF r P
  have hle : (P : Subgroup ↥F) ≤ pCore r ↥F := le_sSup ⟨hnormal, P.isPGroup'⟩
  exact ⟨e', hle (hP (Subgroup.mem_zpowers e')), rfl⟩

theorem orderOf_eq_pow_of_mem_Op (r : ℕ) [Fact r.Prime] {B : Subgroup G} {d : G} (hd : d ∈ Op r B) :
    ∃ j, orderOf d = r ^ j := by
  obtain ⟨k, hk⟩ := (L20.isPGroup_Op r B) ⟨d, hd⟩
  have : orderOf d ∣ r ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : r.Prime)).1 this
  exact ⟨j, hj⟩

theorem commute_of_part {F F₀ : Subgroup G} (hF : Group.IsNilpotent ↥F) (hF₀ : F₀ ≤ F) {q : ℕ} [Fact q.Prime]
    {d : G} (hd : d ∈ Op q F) (hdB : ∀ x ∈ F₀ ⊓ Op q F, d * x = x * d) : ∀ f ∈ F₀, d * f = f * d := by
  intro f hf
  have hfF : f ∈ F := hF₀ hf
  have hdF : d ∈ F := Op_le q F hd
  obtain ⟨j, hj⟩ := orderOf_eq_pow_of_mem_Op q hd
  have hn : orderOf f ≠ 0 := (orderOf_pos f).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q (Fact.out : q.Prime).ne_one
  have hcop : IsCoprime ((q ^ a : ℕ) : ℤ) (m : ℤ) := by
    have : Nat.Coprime (q ^ a) m := Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 hm)
    exact Nat.isCoprime_iff_coprime.2 this
  obtain ⟨s, t, hst⟩ := hcop
  set fq : G := f ^ (t * (m : ℤ)) with hfq
  set fq' : G := f ^ (s * ((q ^ a : ℕ) : ℤ)) with hfq'
  have hsplit : f = fq * fq' := by
    rw [hfq, hfq', ← zpow_add]
    have : t * (m : ℤ) + s * ((q ^ a : ℕ) : ℤ) = 1 := by linarith
    rw [this, zpow_one]
  have hfqF₀ : fq ∈ F₀ := Subgroup.zpow_mem _ hf _
  have hfq'F₀ : fq' ∈ F₀ := Subgroup.zpow_mem _ hf _
  have hfqpow : fq ^ (q ^ a) = 1 := by
    rw [hfq, ← zpow_natCast, ← zpow_mul]
    have : t * (m : ℤ) * ((q ^ a : ℕ) : ℤ) = (orderOf f : ℤ) * t := by
      rw [hnm]; push_cast; ring
    rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hfq'pow : fq' ^ m = 1 := by
    rw [hfq', ← zpow_natCast, ← zpow_mul]
    have : s * ((q ^ a : ℕ) : ℤ) * (m : ℤ) = (orderOf f : ℤ) * s := by
      rw [hnm]; push_cast; ring
    rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hfqOp : fq ∈ Op q F := mem_Op_of_pow_eq_one hF (hF₀ hfqF₀) hfqpow
  have hdfq : d * fq = fq * d := hdB fq ⟨hfqF₀, hfqOp⟩
  have hcomm : d * fq' = fq' * d := by
    have hord' : orderOf fq' ∣ m := orderOf_dvd_of_pow_eq_one hfq'pow
    have hcop' : Nat.Coprime (orderOf d) (orderOf fq') := by
      rw [hj]
      exact Nat.Coprime.pow_left j (Nat.Coprime.coprime_dvd_right hord'
        ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 hm))
    have := Group.IsNilpotent.commute_of_orderOf_coprime (G := ↥F) (x := ⟨d, hdF⟩) (y := ⟨fq', hF₀ hfq'F₀⟩)
      (by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
        exact hcop')
    exact congrArg Subtype.val this.eq
  rw [hsplit]
  calc d * (fq * fq') = (d * fq) * fq' := by group
    _ = (fq * d) * fq' := by rw [hdfq]
    _ = fq * (d * fq') := by group
    _ = fq * (fq' * d) := by rw [hcomm]
    _ = fq * fq' * d := by group


theorem l2011_centralizes_A (z : G) {F₀ : Subgroup G} (hF₀ : F₀ ≤ F20 z) {y : G} (hyC : y ∈ Cen z)
    (hy2 : y * y = 1) (hy0 : ∀ f ∈ F₀, y * f = f * y)
    (hyN : ∀ f ∈ F20 z ⊓ normalizer (F₀ : Set G), y * f = f * y) :
    ∀ a ∈ OddCore z, y * a = a * y := by
  by_cases hy1 : y = 1
  · intro a _
    rw [hy1]; simp
  have hFnil : Group.IsNilpotent ↥(F20 z) := Fm_isNilpotent (OddCore z)
  have hOq : ∀ q : ℕ, q.Prime → Op q (OddCore z) ≤ centralizer ({y} : Set G) := by
    intro q hq
    have hfact : Fact q.Prime := ⟨hq⟩
    by_cases hq2 : q = 2
    · subst hq2
      intro x hx
      obtain ⟨j, hj⟩ := orderOf_eq_pow_of_mem_Op 2 hx
      have hodd : Odd (orderOf x) := odd_orderOf_of_mem_pPrimeCoreOf (Op_le 2 _ hx)
      have hj0 : j = 0 := by
        by_contra hne
        rw [hj] at hodd
        have : Even (2 ^ j) := (Nat.even_pow.2 ⟨even_two, hne⟩)
        exact (Nat.not_even_iff_odd.2 hodd) this
      have hx1 : x = 1 := orderOf_eq_one_iff.1 (by rw [hj, hj0]; rfl)
      rw [hx1]
      exact Subgroup.one_mem _
    ·
      rw [show Op q (OddCore z) = Op q (F20 z) from (Op_Fm_eq hq (OddCore z)).symm]
      have hD : IsPGroup q ↥(Op q (F20 z)) := L20.isPGroup_Op q (F20 z)
      have hFnorm : ∀ c ∈ F20 z, ∀ b ∈ F20 z, c * b * c⁻¹ ∈ F20 z := fun c hc b hb =>
        (F20 z).mul_mem ((F20 z).mul_mem hc hb) ((F20 z).inv_mem hc)
      have key := axb_helper (p := q) hq2 hy2 hy1 (D := Op q (F20 z)) (X := F₀ ⊓ Op q (F20 z)) hD
        hD.to_inf_right
        (fun d hd => Op_conj_mem q (fun c hc b hb => F20_conj_mem z hc hb) hyC hd)
        (fun x hx d hd => Op_conj_mem q hFnorm (hF₀ hx.1) hd)
        (fun x hx => hy0 x hx.1)
        (fun d hd hdB => by
          have hdF : d ∈ F20 z := Op_le q _ hd
          have hcomm := commute_of_part hFnil hF₀ hd (fun x hx => hdB x hx)
          have hc : ∀ g ∈ F₀, d * g * d⁻¹ = g := fun g hg => by
            rw [hcomm g hg]; group
          have hc' : ∀ g ∈ F₀, d⁻¹ * g * d = g := fun g hg => by
            have := hc g hg
            calc d⁻¹ * g * d = d⁻¹ * (d * g * d⁻¹) * d := by rw [this]
              _ = g := by group
          have hdN : d ∈ normalizer (F₀ : Set G) := by
            rw [Subgroup.mem_normalizer_iff]
            intro f
            constructor
            · intro hf
              rw [hc f hf]; exact hf
            · intro h
              have h1 := hc' _ h
              have h2 : d⁻¹ * (d * f * d⁻¹) * d = f := by group
              rw [h2] at h1
              rw [h1]; exact h
          exact hyN d ⟨hdF, hdN⟩)
      intro d hd
      exact (Subgroup.mem_centralizer_singleton_iff.2 (key d hd).symm)
  have hF' : F20 z ≤ centralizer ({y} : Set G) := Fm_le_of_forall hOq
  exact centralizes_oddCore_of_F hyC hy2 fun f hf =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hF' hf)).symm

end PartA

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
