module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialBinaryActionCounterexample
public import CFSG.GroupTheory.AutomorphismAction.CentralDeviation
public import CFSG.GroupTheory.CoprimeActionSupport.InvolutiveAutomorphismInvertedElement

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

namespace InvertedSubgroup

theorem exists_subgroup {G : Type} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)
    (hp2 : p ≠ 2) {P : Subgroup G} (hP : CFSG.IsExtraspecialPGroup p ↥P)
    (hexp : Monoid.exponent ↥P = p) {t : G} (ht : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (P : Set G)) (hPt : ⁅P, Subgroup.zpowers t⁆ ≠ ⊥) :
    ∃ X ≤ P, Nat.card ↥X = p ∧ X ≠ centerP P ∧ ∀ x ∈ X, t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨-, hcomm, -, -⟩ := hP
  set α : MulAut P := P.normalizerMonoidHom ⟨t, htN⟩ with hα
  have hαy : ∀ y : P, ((α y : P) : G) = t * y * t⁻¹ := fun y => by
    simp [hα]
  have ht2 : t * t = 1 := by rw [← pow_two]; exact ht ▸ pow_orderOf_eq_one t
  have hinv : ∀ y, α (α y) = y := fun y => by
    apply Subtype.ext
    rw [hαy, hαy]
    calc t * (t * (y : G) * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
      _ = y := by rw [ht2]; simp
  have hnt : ∃ y : P, α y * y⁻¹ ∉ Subgroup.center P := by
    by_contra hcon
    push Not at hcon
    have hfix := CFSG.GroupTheory.AutomorphismAction.fixes_center_of_derived_eq α hcon hcomm
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have hpe : ∀ x : P, x ^ p = 1 := fun x => by
      rw [← hexp]; exact Monoid.pow_exponent_eq_one x
    have h1 := CFSG.GroupTheory.AutomorphismAction.eq_one_of_involutive_centralizing
      hodd hpe α hinv hfix hcon
    apply hPt
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := congrArg (fun f : MulAut P => ((f ⟨y, hy⟩ : P) : G)) h1
    simp only [hαy] at this
    simp at this
    have h2 : t * y = y * t := by
      rw [mul_inv_eq_iff_eq_mul] at this; exact this
    exact h2.symm
  obtain ⟨x, hx, hax, hord, hcardx, hnc⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.InvolutiveAutomorphismInvertedElement.exists_cyclic_inverted α hinv hnt hp hexp
  refine ⟨(Subgroup.zpowers x).map P.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩; exact z.2
  · rw [Subgroup.card_map_of_injective P.subtype_injective]; exact hcardx
  · intro h
    apply hnc
    have := Subgroup.map_injective P.subtype_injective h
    rw [this]
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have : α (x ^ k) = (x ^ k)⁻¹ := by rw [map_zpow, hax, inv_zpow]
    have h2 := hαy (x ^ k)
    rw [this] at h2
    simpa using h2.symm

end InvertedSubgroup

end Section5

end CFSG.LocalAnalysis.RankThreeUC
