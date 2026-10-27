module

public import CFSG.CGT.Foote82.T66.CaseIU

public section

namespace CFSG.CGT.Foote82

namespace CaseIAux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open Equiv Equiv.Perm CaseIPerm

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L H₁ : Subgroup (GLV V)} {z : GLV V} {v : V} {m : ℕ}
  {ψ : ↥H₁ ≃* Equiv.Perm (Fin (m + 6 + 2))}

theorem isPGroup_zpowers_of_mul_self {Γ : Type*} [Group Γ] {a : Γ} (ha : a * a = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show a ^ ((2 : ℕ) : ℤ) = 1 by
    rw [zpow_natCast, sq, ha], one_zpow]

theorem exists_sylow_T₀ :
    ∃ T₀ : Sylow 2 (Perm (Fin (m + 6 + 2))), swap 0 1 ∈ T₀ ∧ swap 2 3 ∈ T₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : swap (0 : Fin (m + 6 + 2)) 1 * swap 2 3 = swap 2 3 * swap 0 1 := by
    refine (Equiv.Perm.Disjoint.commute ?_).eq
    intro x
    by_cases h0 : x = 0
    · right; rw [h0]; exact swap_apply_of_ne_of_ne ne02 ne03
    by_cases h1 : x = 1
    · right; rw [h1]; exact swap_apply_of_ne_of_ne ne12 ne13
    · left; exact swap_apply_of_ne_of_ne h0 h1
  have hle : Subgroup.zpowers (swap (0 : Fin (m + 6 + 2)) 1) ≤
      Subgroup.normalizer (Subgroup.zpowers (swap (2 : Fin (m + 6 + 2)) 3) : Set _) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ((Commute.zpow_left (show Commute (swap (2 : Fin (m + 6 + 2)) 3) (swap 0 1)
      from hc.symm) k)).eq
  have hK := IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_mul_self (swap_mul_self 0 1))
    (isPGroup_zpowers_of_mul_self (swap_mul_self 2 3)) hle
  obtain ⟨T₀, hT₀⟩ := hK.exists_le_sylow
  exact ⟨T₀, hT₀ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)),
    hT₀ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))⟩

theorem Hyp.H₁_le_NH (h : Hyp G L z v H₁ m ψ) :
    H₁ ≤ G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V)) := by
  intro x hx
  refine ⟨h.H₁_le_G hx, Subgroup.mem_normalizer_iff.2 fun y => ?_⟩
  obtain ⟨σ, rfl⟩ := (mem_H₁_iff (ψ := ψ)).1 hx
  rw [h.H_eq]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨σ * τ * σ⁻¹, (inferInstance : (alternatingGroup (Fin (m + 6 + 2))).Normal).conj_mem _ hτ σ, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨τ, hτ, hτy⟩
    refine ⟨σ⁻¹ * τ * σ, ?_, ?_⟩
    · have := (inferInstance : (alternatingGroup (Fin (m + 6 + 2))).Normal).conj_mem _ hτ σ⁻¹
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, map_inv, hτy]
      group

theorem exists_conj_swap01 {σ : Perm (Fin (m + 6 + 2))} (hσ : σ.IsSwap) :
    ∃ π : Perm (Fin (m + 6 + 2)), π * swap 0 1 * π⁻¹ = σ := by
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  exact isConj_iff.1 (Equiv.Perm.isConj_swap ne01 hxy)

theorem Hyp.conj_z_of_swap (h : Hyp G L z v H₁ m ψ) {σ : Perm (Fin (m + 6 + 2))}
    (hσ : σ.IsSwap) : ∃ c ∈ H₁, pe ψ σ = c * z * c⁻¹ := by
  obtain ⟨π, rfl⟩ := exists_conj_swap01 hσ
  refine ⟨pe ψ π, pe_mem π, ?_⟩
  rw [map_mul, map_mul, map_inv, ← h.z_eq]

theorem Hyp.U_le_of_swap (h : Hyp G L z v H₁ m ψ) {σ : Perm (Fin (m + 6 + 2))}
    (hσ : σ.IsSwap) {w : V} (hw : w ∈ UU z ψ) :
    w ∈ commSpace (Subgroup.zpowers (pe ψ σ)) ⊤ := by
  obtain ⟨c, hc, hσc⟩ := h.conj_z_of_swap hσ
  rw [hσc]
  have := mem_commSpace_conj (g := c) hw.1
  rwa [h.fixes_U hc hw] at this

theorem Hyp.syl_criterion (h : Hyp G L z v H₁ m ψ) (T₀ : Sylow 2 (Perm (Fin (m + 6 + 2))))
    (hzT : swap 0 1 ∈ T₀) (hyT : swap 2 3 ∈ T₀)
    (hT : ∀ σ ∈ T₀, (∃ c ∈ G, pe ψ σ = c * z * c⁻¹) → σ.IsSwap)
    {Q : Subgroup (GLV V)} (hQG : Q ≤ G) (hQ2 : IsPGroup 2 Q)
    (hTQ : (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).map (pe ψ) ≤ Q) :
    Q = (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).map (pe ψ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup (GLV V) := (T₀ : Subgroup (Perm (Fin (m + 6 + 2)))).map (pe ψ) with hTdef
  by_contra hne
  have hlt : T < Q := lt_of_le_of_ne hTQ (Ne.symm hne)
  haveI : Group.IsNilpotent ↥Q := hQ2.isNilpotent
  set T' : Subgroup ↥Q := T.subgroupOf Q with hT'
  have hT'lt : T' < ⊤ := by
    refine lt_of_le_of_ne le_top fun he => ?_
    apply hne
    apply le_antisymm _ hTQ
    intro q hq
    have : (⟨q, hq⟩ : ↥Q) ∈ T' := by rw [he]; trivial
    exact Subgroup.mem_subgroupOf.1 this
  obtain ⟨x, hxN, hxT⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent T' hT'lt)
  set x₀ : GLV V := (x : GLV V) with hx₀
  have hx₀G : x₀ ∈ G := hQG x.2
  have hx₀T : x₀ ∉ T := fun h' => hxT (Subgroup.mem_subgroupOf.2 h')
  have hnorm : ∀ t ∈ T, x₀⁻¹ * t * x₀ ∈ T := by
    intro t ht
    have h1 := (Subgroup.mem_normalizer_iff.1 hxN (x⁻¹ * ⟨t, hTQ ht⟩ * x)).2
    have h2 : x * (x⁻¹ * ⟨t, hTQ ht⟩ * x) * x⁻¹ = ⟨t, hTQ ht⟩ := by group
    rw [h2] at h1
    exact Subgroup.mem_subgroupOf.1 (h1 (Subgroup.mem_subgroupOf.2 ht))
  have hswap : ∀ a ∈ T, (∃ c ∈ G, a = c * z * c⁻¹) → ∃ σ, σ.IsSwap ∧ a = pe ψ σ := by
    rintro a ⟨σ, hσ, rfl⟩ hc
    exact ⟨σ, hT σ hσ hc, rfl⟩
  have hzT' : z ∈ T := ⟨swap 0 1, hzT, h.z_eq.symm⟩
  have hyT' : yy ψ ∈ T := ⟨swap 2 3, hyT, rfl⟩
  have hU : ∀ w ∈ UU z ψ, x₀ w ∈ UU z ψ := by
    intro w hw
    have key : ∀ t ∈ T, (∃ c ∈ G, t = c * z * c⁻¹) → x₀ w ∈ commSpace (Subgroup.zpowers t) ⊤ := by
      intro t ht htc
      obtain ⟨c, hcG, rfl⟩ := htc
      obtain ⟨σ, hσ, hσe⟩ := hswap _ (hnorm _ ht)
        ⟨x₀⁻¹ * c, G.mul_mem (G.inv_mem hx₀G) hcG, by group⟩
      have h1 := h.U_le_of_swap hσ hw
      rw [← hσe] at h1
      have h2 := mem_commSpace_conj (g := x₀) h1
      have e : x₀ * (x₀⁻¹ * (c * z * c⁻¹) * x₀) * x₀⁻¹ = c * z * c⁻¹ := by group
      rwa [e] at h2
    refine ⟨?_, ?_⟩
    · have := key z hzT' ⟨1, G.one_mem, by group⟩
      exact this
    · exact key (yy ψ) hyT' ⟨gg ψ, h.gg_mem_G, h.yy_eq⟩
  have hxNH : x₀ ∈ Subgroup.normalizer (HH G L v : Set (GLV V)) := h.normalizer_U_le hx₀G hU
  set Q₁ : Subgroup (GLV V) := T ⊔ Subgroup.zpowers x₀ with hQ₁
  have hQ₁Q : Q₁ ≤ Q := sup_le hTQ (Subgroup.zpowers_le.2 x.2)
  have hQ₁N : Q₁ ≤ G ⊓ Subgroup.normalizer (HH G L v : Set (GLV V)) := by
    refine sup_le ?_ (Subgroup.zpowers_le.2 ⟨hx₀G, hxNH⟩)
    rintro _ ⟨σ, -, rfl⟩
    exact h.H₁_le_NH (pe_mem σ)
  have hcard := h.card_le_of_isPGroup hQ₁N (hQ2.to_le hQ₁Q) T₀
  have hTcard : Nat.card T = Nat.card T₀ := Subgroup.card_map_of_injective pe_injective
  have hlt₁ : T < Q₁ := lt_of_le_of_ne le_sup_left fun he =>
    hx₀T (he ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x₀))
  have := Subgroup.card_lt_of_lt hlt₁
  omega

end CaseIAux

end CFSG.CGT.Foote82
