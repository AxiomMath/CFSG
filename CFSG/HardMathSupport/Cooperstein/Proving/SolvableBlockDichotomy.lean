module

public import CFSG.Assembly.Subnormal

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H]

theorem exists_order_three_sup [Finite H] (Q : Subgroup H) [Q.Normal]
    (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1) (hidx : Q.index = 3) :
    ∃ t : H, t ∉ Q ∧ Q ⊔ zpowers t = ⊤ := by
  classical
  have := Fintype.ofFinite H
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3dvd : 3 ∣ Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, ← index_mul_card (H := Q), hidx]
    exact dvd_mul_right 3 _
  obtain ⟨t, ht3⟩ := exists_prime_orderOf_dvd_card 3 h3dvd
  have htQ : t ∉ Q := by
    intro h
    obtain ⟨k, hk⟩ := hQ2 t h
    have h1 : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [ht3] at h1
    have h2 : 3 ∣ 2 ^ k := h1
    have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    norm_num at h3
  refine ⟨t, htQ, ?_⟩
  have hle : Q ≤ Q ⊔ zpowers t := le_sup_left
  have hrel := relIndex_mul_index hle
  rw [hidx] at hrel
  have hdvd : Q.relIndex (Q ⊔ zpowers t) ∣ 3 := Dvd.intro _ hrel
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exfalso
    exact htQ (relIndex_eq_one.mp h1 (mem_sup_right (mem_zpowers t)))
  · have h4 : (Q ⊔ zpowers t).index = 1 := by
      rw [h3] at hrel; omega
    exact index_eq_one.mp h4

theorem isSubnormal_inf_of_le {G : Type} [Group G] {H K : Subgroup G}
    (h : CFSG.Open.IsSubnormal H K) :
    ∀ L : Subgroup G, L ≤ K → CFSG.Open.IsSubnormal (H ⊓ L) L :=
  fun _ hL => h.inf_of_le hL

theorem reflTransGen_of_isSubnormal {G : Type} [Group G] {H K : Subgroup G}
    (h : CFSG.Open.IsSubnormal H K) :
    Relation.ReflTransGen (fun A B : Subgroup G => A ≤ B ∧ (A.subgroupOf B).Normal) H K := by
  induction h with
  | refl A => exact Relation.ReflTransGen.refl
  | @step A M K' hAM hn _ ih => exact Relation.ReflTransGen.head ⟨hAM, hn⟩ ih

theorem commMap_mul_eq (P : Subgroup H) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (t : H)
    {x y : H} (hx : x ∈ P) (hy : y ∈ P) (ha : t * x * t⁻¹ ∈ P) :
    (x * y)⁻¹ * (t * (x * y) * t⁻¹) =
      (x⁻¹ * (t * x * t⁻¹)) * (y⁻¹ * (t * y * t⁻¹)) := by
  have hyc : y⁻¹ * (x⁻¹ * (t * x * t⁻¹)) = (x⁻¹ * (t * x * t⁻¹)) * y⁻¹ :=
    hab _ (P.inv_mem hy) _ (P.mul_mem (P.inv_mem hx) ha)
  rw [show (x * y)⁻¹ * (t * (x * y) * t⁻¹) =
      y⁻¹ * (x⁻¹ * (t * x * t⁻¹)) * (t * y * t⁻¹) by group, hyc]
  simp only [mul_assoc]

theorem central_eq_one_of_commutator_eq [Finite H] (P : Subgroup H) [P.Normal]
    (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (t : H) (htP : P ⊔ zpowers t = ⊤)
    (hcomm : ⁅P, (⊤ : Subgroup H)⁆ = P) (z : H) (hz : z ∈ P)
    (hzc : ∀ h : H, h * z = z * h) : z = 1 := by
  classical
  have htc : ∀ x ∈ P, t * x * t⁻¹ ∈ P := fun x hx => Normal.conj_mem inferInstance x hx t
  have hmem : ∀ x ∈ P, x⁻¹ * (t * x * t⁻¹) ∈ P :=
    fun x hx => P.mul_mem (P.inv_mem hx) (htc x hx)
  let f : P →* P := MonoidHom.mk'
    (fun x : P => (⟨(x : H)⁻¹ * (t * (x : H) * t⁻¹), hmem _ x.2⟩ : P))
    (fun x y => Subtype.ext (commMap_mul_eq P hab t x.2 y.2 (htc _ x.2)))
  have hf : ∀ x : P, (f x : H) = (x : H)⁻¹ * (t * (x : H) * t⁻¹) := fun x => rfl
  have hPcomm : ∀ p ∈ P, ∀ y ∈ P, p * y * p⁻¹ = y := by
    intro p hp y hy
    rw [hab p hp y hy]
    group
  obtain ⟨I, hI⟩ : ∃ I : Subgroup H, I = (f.range).map P.subtype := ⟨_, rfl⟩
  have hIdef : ∀ y : H, y ∈ I ↔ ∃ u : P, (f u : H) = y := by
    intro y
    rw [hI, Subgroup.mem_map]
    constructor
    · rintro ⟨u', hu', hy⟩
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hu'
      exact ⟨u, by simpa using hy⟩
    · rintro ⟨u, hu⟩
      exact ⟨f u, MonoidHom.mem_range.mpr ⟨u, rfl⟩, by simpa using hu⟩
  have hfI : ∀ x : P, (f x : H) ∈ I := fun x => (hIdef _).mpr ⟨x, rfl⟩
  have hA_t : ∀ x ∈ P, x⁻¹ * (t * x * t⁻¹) ∈ I := by
    intro x hx
    have h := hfI ⟨x, hx⟩
    rw [hf] at h
    exact h
  have hA_q : ∀ q ∈ P, ∀ x ∈ P, x⁻¹ * (q * x * q⁻¹) ∈ I := by
    intro q hq x hx
    rw [hPcomm q hq x hx, inv_mul_cancel]
    exact I.one_mem
  have hA_mul : ∀ g h : H, (∀ x ∈ P, x⁻¹ * (g * x * g⁻¹) ∈ I) →
      (∀ x ∈ P, x⁻¹ * (h * x * h⁻¹) ∈ I) → ∀ x ∈ P, x⁻¹ * (g * h * x * (g * h)⁻¹) ∈ I := by
    intro g h hg hh x hx
    have hw : h * x * h⁻¹ ∈ P := Normal.conj_mem inferInstance x hx h
    have e : x⁻¹ * (g * h * x * (g * h)⁻¹)
        = (x⁻¹ * (h * x * h⁻¹)) * ((h * x * h⁻¹)⁻¹ * (g * (h * x * h⁻¹) * g⁻¹)) := by
      group
    rw [e]
    exact I.mul_mem (hh x hx) (hg _ hw)
  have hA_pow : ∀ n : ℕ, ∀ x ∈ P, x⁻¹ * (t ^ n * x * (t ^ n)⁻¹) ∈ I := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      rw [pow_succ]
      exact hA_mul (t ^ k) t ih hA_t x hx
  have hdec : ∀ g : H, ∃ q ∈ P, ∃ n : ℕ, q * t ^ n = g := by
    intro g
    have hg : g ∈ P ⊔ zpowers t := by rw [htP]; exact mem_top g
    obtain ⟨q, hq, s, hs, rfl⟩ := mem_sup_of_normal_left.mp hg
    have hs' : s ∈ Submonoid.powers t := mem_powers_iff_mem_zpowers.mpr hs
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff s t).mp hs'
    exact ⟨q, hq, n, rfl⟩
  have hA_all : ∀ g : H, ∀ x ∈ P, x⁻¹ * (g * x * g⁻¹) ∈ I := by
    intro g
    obtain ⟨q, hq, n, rfl⟩ := hdec g
    exact hA_mul q (t ^ n) (hA_q q hq) (hA_pow n)
  have hcomm_le : ⁅P, (⊤ : Subgroup H)⁆ ≤ I := by
    refine commutator_le.mpr ?_
    intro x hx y _
    have e : ⁅x, y⁆ = (x⁻¹)⁻¹ * (y * x⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact hA_all y x⁻¹ (P.inv_mem hx)
  have hPI : P ≤ I := (le_of_eq hcomm.symm).trans hcomm_le
  have hsurj : Function.Surjective f := by
    intro p
    obtain ⟨u, hu⟩ := (hIdef (p : H)).mp (hPI p.2)
    exact ⟨u, Subtype.ext hu⟩
  have hinj : Function.Injective f := Finite.injective_iff_surjective.mpr hsurj
  have htz : t * z * t⁻¹ = z := by
    rw [hzc t]
    group
  have hfz : f ⟨z, hz⟩ = 1 := Subtype.ext (by rw [hf]; simp [htz])
  have h1 : (⟨z, hz⟩ : P) = 1 := hinj (hfz.trans (map_one f).symm)
  have h2 := congrArg Subtype.val h1
  simpa using h2

end CFSG.HardMathSupport.Cooperstein.Proving

end
