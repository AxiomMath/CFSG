module

public import CFSG.CGT.Foote82.T66.CaseIClimb
public import CFSG.CGT.Foote82.T66.CaseIS2
public import CFSG.CGT.Foote82.T66.CaseIS6D8

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm CaseIHeart CaseIS6D8 CaseIClimbAux

section Groups

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem mem_map_center_iff {A : Subgroup Γ} {x : Γ} :
    x ∈ (Subgroup.center ↥A).map A.subtype ↔ x ∈ A ∧ ∀ a ∈ A, a * x = x * a := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun a ha => congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨a, ha⟩)⟩
  · rintro ⟨hxA, hx⟩
    exact ⟨⟨x, hxA⟩, Subgroup.mem_center_iff.2 fun a => Subtype.ext (hx a a.2), rfl⟩

theorem card_le_two_mul_of_conj_mem {Y Z : Subgroup Γ} (hY : IsPGroup 2 Y)
    (hZ : Nat.card Z = 4) {c : Γ} (hcZ : c ∈ Z) (hc1 : c ≠ 1)
    (hYZ : ∀ y ∈ Y, y * c * y⁻¹ ∈ Z) :
    Nat.card Y ≤ 2 * Nat.card ↥(Y ⊓ Subgroup.centralizer {c}) := by
  set C : Subgroup ↥Y := (Subgroup.centralizer {c}).subgroupOf Y with hC
  let f : ↥Y → {x : Γ // x ∈ Z ∧ x ≠ 1} := fun y =>
    ⟨y * c * y⁻¹, hYZ y y.2, fun h1 => hc1 (by
      have := congrArg (fun t => (y : Γ)⁻¹ * t * y) h1
      simpa [mul_assoc] using this)⟩
  have hf : ∀ a b : ↥Y, a⁻¹ * b ∈ C ↔ f a = f b := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hab
      apply Subtype.ext
      show (a : Γ) * c * (a : Γ)⁻¹ = (b : Γ) * c * (b : Γ)⁻¹
      have e : ((a⁻¹ * b : ↥Y) : Γ) = (a : Γ)⁻¹ * b := rfl
      rw [e] at hab
      set a' : Γ := (a : Γ)
      set b' : Γ := (b : Γ)
      calc a' * c * a'⁻¹ = a' * (c * (a'⁻¹ * b')) * b'⁻¹ := by group
        _ = a' * ((a'⁻¹ * b') * c) * b'⁻¹ := by rw [hab]
        _ = b' * c * b'⁻¹ := by group
    · intro hab
      have h1 : (a : Γ) * c * (a : Γ)⁻¹ = (b : Γ) * c * (b : Γ)⁻¹ := congrArg Subtype.val hab
      show (a : Γ)⁻¹ * b * c = c * ((a : Γ)⁻¹ * b)
      set a' : Γ := (a : Γ)
      set b' : Γ := (b : Γ)
      calc a'⁻¹ * b' * c = a'⁻¹ * (b' * c * b'⁻¹) * b' := by group
        _ = a'⁻¹ * (a' * c * a'⁻¹) * b' := by rw [h1]
        _ = c * (a'⁻¹ * b') := by group
  let F : ↥Y ⧸ C → {x : Γ // x ∈ Z ∧ x ≠ 1} :=
    Quotient.lift f fun a b hab => (hf a b).1 (QuotientGroup.leftRel_apply.1 hab)
  have hFinj : Function.Injective F := by
    intro p q hpq
    induction p using QuotientGroup.induction_on
    induction q using QuotientGroup.induction_on
    exact QuotientGroup.eq.2 ((hf _ _).2 hpq)
  have hcard3 : Nat.card {x : Γ // x ∈ Z ∧ x ≠ 1} ≤ 3 := by
    have e : Nat.card {x : Γ // x ∈ Z ∧ x ≠ 1} = ((Z : Set Γ) \ {1}).ncard := by
      rw [← Nat.card_coe_set_eq]
      rfl
    rw [e, Set.ncard_diff_singleton_of_mem (Z.one_mem), ← Nat.card_coe_set_eq]
    have : Nat.card ↥(Z : Set Γ) = 4 := hZ
    omega
  have hidx : C.index ≤ 3 :=
    (Nat.card_le_card_of_injective F hFinj).trans hcard3
  have hdvd : C.index ∣ Nat.card ↥Y := Subgroup.index_dvd_card C
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hY
  rw [hk] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hidx2 : C.index ≤ 2 := by
    rw [hj] at hidx ⊢
    rcases j with _ | _ | j
    · norm_num
    · norm_num
    · exfalso
      have h4 : 4 ≤ 2 ^ (j + 1 + 1) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have h1 := Subgroup.card_mul_index C
  have h2 : Nat.card C = Nat.card ↥(Y ⊓ Subgroup.centralizer {c}) := by
    rw [hC, ← Subgroup.inf_subgroupOf_right]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      Subgroup.centralizer {c} ⊓ Y ≤ Y)).toEquiv, inf_comm]
  rw [← h1, h2]
  nlinarith

end Groups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}
variable {S : Subgroup (GLV V)}

theorem SBad.card_le_64 (h : Hyp G L z v H₁ m ψ) (hS : SBad G L z ψ S) (h4 : Nat.card S = 4)
    (hm : m ≤ 1) {Q : Subgroup (GLV V)} (hQG : Q ≤ G) (hQz : ∀ q ∈ Q, q * z = z * q)
    (hQ2 : IsPGroup 2 Q) : Nat.card Q ≤ 64 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, -, hθ1, -⟩ := h.exists_thetaL
  have hQN : Q ≤ NN G L := fun q hq => h.centralizer_z_le (hQG hq) (hQz q hq)
  let g : ↥Q →* Perm (Fin (m + 6)) := θ.comp (Subgroup.inclusion hQN)
  have hker : Nat.card g.ker ≤ 4 := by
    have hk : g.ker.map Q.subtype ≤ KK G L := by
      rintro _ ⟨q, hq, rfl⟩
      exact h.mem_K_of_theta hθ1 _ hq
    have := hS.max _ hk ((hQ2.to_subgroup g.ker).map Q.subtype)
    rwa [Subgroup.card_map_of_injective Q.subtype_injective, h4] at this
  have hrange : Nat.card g.range ≤ 16 := by
    have hR2 : IsPGroup 2 g.range := hQ2.of_surjective g.rangeRestrict g.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR2
    have hdvd : Nat.card g.range ∣ Nat.card (Perm (Fin (m + 6))) :=
      Subgroup.card_subgroup_dvd_card _
    rw [hk, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at hdvd
    rw [hk]
    by_contra hc
    push Not at hc
    have h5 : 5 ≤ k := by
      by_contra h5
      push Not at h5
      interval_cases k <;> norm_num at hc
    have h32 : 2 ^ 5 ∣ (m + 6).factorial :=
      (Nat.pow_dvd_pow 2 h5).trans hdvd
    interval_cases m <;> exact absurd h32 (by decide)
  have := Subgroup.card_ker_mul_card_range g
  rw [← this]
  nlinarith

end CaseIAux

end CFSG.CGT.Foote82
