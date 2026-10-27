module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryHigher
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.LieType.Steinberg.CentralExt.UnitaryPerfect
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.BorelTits

theorem card_scalars_SU_four_le {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) :
    Nat.card ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K)) ≤ 2 := by
  obtain ⟨hcyc, hexp⟩ :=
    CFSG.LieType.Steinberg.isCyclic_scalars_statedSU hK (n := 4) (by norm_num)
  have hg : Nat.gcd 4 (p ^ f + 1) = 2 := by
    rw [Nat.gcd_rec, show (p ^ f + 1) % 4 = 2 by omega]
    rfl
  obtain ⟨z, hz⟩ := hcyc.exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers hz]
  exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (by rw [← hg]; exact hexp z))

theorem exists_equiv_statedSU_four {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (hZ2 : IsPGroup 2 (Subgroup.center Y)) (hZ : Subgroup.center Y ≠ ⊥) {p f : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSU 4 (p ^ f) K)) :
    ∃ ψ : Y ≃* StatedSU 4 (p ^ f) K, ∀ y : Y,
      e (QuotientGroup.mk y) = QuotientGroup.mk (ψ y) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  set ι := equivStatedSU hK 4 with hι
  set Z := (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K) with hZdef
  set β : SU (unitaryInvolution K p f) 4 →* StatedProj (StatedSU 4 (p ^ f) K) :=
    (QuotientGroup.mk' Z).comp ι.toMonoidHom with hβ
  set η : Y →* StatedProj (StatedSU 4 (p ^ f) K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)) with hη
  have hβs : Function.Surjective β := (QuotientGroup.mk'_surjective _).comp ι.surjective
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = Subgroup.center Y := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SU (unitaryInvolution K p f) 4),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker →
        ∃ σ : SU (unitaryInvolution K p f) 4 →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hker h2
    obtain ⟨σ, hσ, -, -⟩ :=
      LieType.Steinberg.su_central_two_extension_splitting hK hp2 (n := 4) (by norm_num) hπ
        hker h2
    exact ⟨σ, hσ⟩
  obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβs hηs
    (hηker ▸ le_rfl) (hηker ▸ hZ2)
  have hβker : β.ker = Z.comap ι.toMonoidHom := by
    rw [hβ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hβcard : Nat.card β.ker ≤ 2 := by
    have : Nat.card β.ker = Nat.card Z := by
      rw [hβker]
      exact Nat.card_congr (ι.toEquiv.subtypeEquiv fun x => Iff.rfl)
    rw [this]
    exact card_scalars_SU_four_le hK hq
  have hαβ : α.ker ≤ β.ker := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA ⊢
    rw [← hα, hA, map_one]
  have hne : α.ker ≠ β.ker := by
    intro h1
    apply hZ
    rw [← hηker, hker, ← h1, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hdvd : Nat.card α.ker ∣ Nat.card β.ker := Subgroup.card_dvd_of_le hαβ
  have hpos : 0 < Nat.card α.ker := Nat.card_pos
  have h1 : Nat.card α.ker = 1 := by
    by_contra h1
    have h2 : 2 ≤ Nat.card α.ker := by omega
    have hle : Nat.card β.ker ≤ Nat.card α.ker := by
      have := Nat.le_of_dvd Nat.card_pos hdvd
      omega
    exact hne (Subgroup.eq_of_le_of_card_ge hαβ hle)
  have hbot : α.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  have hinj : Function.Injective α := (MonoidHom.ker_eq_bot_iff α).1 hbot
  refine ⟨(MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm.trans ι, fun y => ?_⟩
  set A := (MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm y with hA
  have hy : α A = y := MulEquiv.ofBijective_apply_symm_apply α ⟨hinj, hαs⟩
  have h3 : η (α A) = β A := hα A
  rw [hy] at h3
  exact h3

end CFSG.ComponentClassification.CatFactsL4U4
