module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Basic
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Gen

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue.A7

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

variable {G : Type} [Group G] [Finite G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]

theorem exists_sylow_bar {T : Subgroup G} (hT : IsSylow2In T (Cx x)) :
    ∃ Tb : Sylow 2 (CentralizerBar x), (Tb : Subgroup (CentralizerBar x)) =
      (T.subgroupOf (Cx x)).map (QuotientGroup.mk' (Ox x)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(T.subgroupOf (Cx x)) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  let Ts : Sylow 2 ↥(Cx x) := hp.toSylow hT.2.2
  exact ⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective (Ox x)) Ts, rfl⟩

theorem card_Pg_eight (eK : ↥Kb ≃* A₇) {T : Subgroup G} (hT : IsSylow2In T (Cx x)) :
    Nat.card (Pg x Kb T) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Tb, hTb⟩ := exists_sylow_bar hT
  obtain ⟨Q, hQ⟩ := exists_sylow_subgroupOf Tb Kb
  have hQcard : Nat.card ((Tb : Subgroup (CentralizerBar x)).subgroupOf Kb) = 8 := by
    rw [← hQ]
    exact card_sylow_two_of_card_A7 (Nat.card_congr eK.toEquiv) Q
  have hprT : ∀ g : G, g ∈ T → ∀ hgC : g ∈ Cx x, pr x g ∈ (Tb : Subgroup (CentralizerBar x)) := by
    intro g hg hgC
    rw [hTb, pr_of_mem x hgC]
    exact ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
  let φ : ↥(Pg x Kb T) → ↥((Tb : Subgroup (CentralizerBar x)).subgroupOf Kb) := fun g =>
    ⟨⟨pr x g, ((mem_Kg x Kb).1 g.2.2).2⟩, hprT g g.2.1 ((mem_Kg x Kb).1 g.2.2).1⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro g g' hgg'
      have h1 : pr x g = pr x g' := congrArg (fun y => ((y.1 : ↥Kb) : CentralizerBar x)) hgg'
      apply Subtype.ext
      have hgC := ((mem_Kg x Kb).1 g.2.2).1
      have hg'C := ((mem_Kg x Kb).1 g'.2.2).1
      have hmem : (g : G)⁻¹ * g' = 1 := by
        apply eq_one_of_pr_eq_one x hT (T.mul_mem (T.inv_mem g.2.1) g'.2.1)
          (mul_mem (inv_mem hgC) hg'C)
        rw [pr_mul x (inv_mem hgC) hg'C, pr_inv x hgC, h1, inv_mul_cancel]
      exact inv_mul_eq_one.1 hmem
    · rintro ⟨⟨k, hkK⟩, hkT⟩
      have hkT' : k ∈ (Tb : Subgroup (CentralizerBar x)) := hkT
      rw [hTb] at hkT'
      obtain ⟨t', ht', rfl⟩ := hkT'
      have hgC := t'.2
      have hgK : (t' : G) ∈ Kg x Kb :=
        (mem_Kg x Kb).2 ⟨hgC, by rw [pr_of_mem x hgC]; exact hkK⟩
      refine ⟨⟨t', Subgroup.mem_subgroupOf.1 ht', hgK⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      show pr x t' = QuotientGroup.mk' (Ox x) t'
      rw [pr_of_mem x hgC]
      rfl
  rw [Nat.card_congr (Equiv.ofBijective φ hφ), hQcard]

theorem rho_inj_P (eK : ↥Kb ≃* A₇) {T : Subgroup G} (hT : IsSylow2In T (Cx x)) {p₁ p₂ : G}
    (h₁ : p₁ ∈ Pg x Kb T) (h₂ : p₂ ∈ Pg x Kb T) (heq : rho x Kb eK p₁ = rho x Kb eK p₂) :
    p₁ = p₂ := by
  have hphi := rho_inj x Kb eK heq
  have hC₁ : p₁ ∈ Cx x := hT.1 h₁.1
  have hC₂ : p₂ ∈ Cx x := hT.1 h₂.1
  have hmem : p₁⁻¹ * p₂ ∈ Pg x Kb T ⊓ Qg x Kb T := by
    refine ⟨(Pg x Kb T).mul_mem ((Pg x Kb T).inv_mem h₁) h₂, ?_⟩
    refine ⟨T.mul_mem (T.inv_mem h₁.1) h₂.1, mul_mem (inv_mem hC₁) hC₂, ?_⟩
    rw [phig_mul x Kb (inv_mem hC₁) hC₂, phig_inv x Kb hC₁, hphi, inv_mul_cancel]
  rw [Pg_inf_Qg x Kb (conj_injective eK) hT, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.1 hmem

theorem exists_abs (hIVK : IVKA7Facts) (eK : ↥Kb ≃* A₇) {T : Subgroup G}
    (hT : IsSylow2In T (Cx x)) :
    ∃ (Tp : Subgroup S₇) (f : S₇),
      Abs (Cx x) T (Pg x Kb T) (Qg x Kb T) (Rd7 x Kb T) (rho x Kb eK) Tp f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC : T ≤ Cx x := hT.1
  have hpT : IsPGroup 2 ↥T := hT.2.1
  let ρT : ↥T →* S₇ := (rhoC x Kb eK).comp (Subgroup.inclusion hTC)
  have hpρ : IsPGroup 2 ↥ρT.range :=
    hpT.of_surjective ρT.rangeRestrict ρT.rangeRestrict_surjective
  obtain ⟨Tpsyl, hTpsyl⟩ := hpρ.exists_le_sylow
  obtain ⟨f, hsplit⟩ := sylowSplit_of_IVK hIVK Tpsyl
  have hTN : ∀ g ∈ T, rho x Kb eK g ∈ (Tpsyl : Subgroup S₇) := by
    intro g hg
    rw [rho_of_mem x Kb eK (hTC hg)]
    exact hTpsyl ⟨⟨g, hg⟩, rfl⟩
  have hρmem : ∀ g ∈ Pg x Kb T, rho x Kb eK g ∈ (Tpsyl : Subgroup S₇) ⊓ A₇ := fun g hg =>
    ⟨hTN g hg.1, rho_mem_A_of_Kg x Kb eK hg.2⟩
  have hρP : ∀ a, a ∈ (Tpsyl : Subgroup S₇) ⊓ A₇ → ∃ g ∈ Pg x Kb T, rho x Kb eK g = a := by
    let ψ : ↥(Pg x Kb T) → ↥((Tpsyl : Subgroup S₇) ⊓ A₇) := fun g =>
      ⟨rho x Kb eK g, hρmem g g.2⟩
    have hinj : Function.Injective ψ := by
      intro a b hab
      exact Subtype.ext (rho_inj_P eK hT a.2 b.2 (congrArg Subtype.val hab))
    have hcardB : Nat.card ↥((Tpsyl : Subgroup S₇) ⊓ A₇) = 8 := by
      rw [Nat.card_congr hsplit.eB.toEquiv, DihedralGroup.nat_card]
    have hcard : Nat.card ↥((Tpsyl : Subgroup S₇) ⊓ A₇) ≤ Nat.card (Pg x Kb T) := by
      rw [card_Pg_eight eK hT, hcardB]
    have hbij := hinj.bijective_of_nat_card_le hcard
    intro a ha
    obtain ⟨g, hg⟩ := hbij.2 ⟨a, ha⟩
    exact ⟨g, g.2, congrArg Subtype.val hg⟩
  refine ⟨(Tpsyl : Subgroup S₇), f, ?_⟩
  exact
    { sp := hsplit
      T_le_C := hTC
      rho_mul := fun g hg h hh => rho_mul x Kb eK hg hh
      rho_one := rho_one x Kb eK
      rho_inv := fun g hg => rho_inv x Kb eK hg
      P_le_T := inf_le_left
      rho_T := hTN
      rho_P := fun a => ⟨hρP a, fun ⟨g, hg, hga⟩ => by rw [← hga]; exact hρmem g hg⟩
      P_inj := fun p₁ h₁ p₂ h₂ e => rho_inj_P eK hT h₁ h₂ e
      P_normal := (Pg_normal x Kb hTC).2
      mem_Q := fun g => by
        rw [mem_Qg x Kb]
        exact ⟨fun ⟨hgT, _, h1⟩ => ⟨hgT, (rho_eq_one_iff x Kb eK g).2 h1⟩,
          fun ⟨hgT, h1⟩ => ⟨hgT, hTC hgT, (rho_eq_one_iff x Kb eK g).1 h1⟩⟩
      mem_Rd := fun g => by
        rw [mem_Rd7]
        exact ⟨fun ⟨hgT, _, h1⟩ => ⟨hgT, (rho_mem_A_iff x Kb eK g).2 h1⟩,
          fun ⟨hgT, h1⟩ => ⟨hgT, hTC hgT, (rho_mem_A_iff x Kb eK g).1 h1⟩⟩ }

end CFSG.GH74.GLS.Stage1.Thm6.Glue.A7
