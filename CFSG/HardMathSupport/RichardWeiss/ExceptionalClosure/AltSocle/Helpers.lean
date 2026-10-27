module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ModuleRestrict
public import CFSG.HardMathSupport.Cooperstein.Proving.EvenWeightCard

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

theorem allOnes_mem_evenWeight {n : ℕ} (he : Even n) : allOnes n ∈ evenWeight n := by
  simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, allOnes]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact (ZMod.natCast_eq_zero_iff_even).mpr he

theorem one_lt_card_evenWeightOnes {n : ℕ} (hn : 1 ≤ n) (he : Even n) :
    1 < Nat.card (evenWeightOnes n) := by
  rw [Finite.one_lt_card_iff_nontrivial]
  refine ⟨⟨⟨⟨allOnes n, allOnes_mem_evenWeight he⟩, ?_⟩, 0, ?_⟩⟩
  · exact AddSubgroup.mem_addSubgroupOf.mpr (AddSubgroup.mem_zmultiples _)
  · intro h
    have h1 := congrArg (fun z : evenWeightOnes n => ((z : evenWeight n) : Fin n → ZMod 2)
      ⟨0, hn⟩) h
    simp [allOnes] at h1

theorem card_altHeart_le_of_even {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    Nat.card (altHeart n) ≤ 2 ^ (n - 2) := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (evenWeightOnes n)
  rw [CFSG.HardMathSupport.Cooperstein.Proving.card_evenWeight n (by omega)] at h1
  have h2 := one_lt_card_evenWeightOnes (by omega : 1 ≤ n) he
  have h3 : Nat.card (altHeart n) * 2 ≤ 2 ^ (n - 1) := by
    rw [h1]
    exact Nat.mul_le_mul_left _ h2
  have h4 : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
    rw [← pow_succ]; congr 1; omega
  omega

variable {G : Type} [Group G]

theorem socleLE_of_surjective [Finite G] {L V : Subgroup G} {A : Type} [AddGroup A]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (π : ↥⁅V, L⁆ →* Multiplicative A) (hπ : Function.Surjective π)
    (hker : π.ker = (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅V, L⁆) :
    SocleLE L V (Nat.card A) := by
  have hUV : ⁅V, L⁆ ≤ V := commutator_le_of_le_normalizer hLV
  have hUC : ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) =
      ⁅V, L⁆ ⊓ (V ⊓ Subgroup.centralizer (L : Set G)) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, hUV h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have hcard : Nat.card A = (⁅V, L⁆ ⊓ (V ⊓ Subgroup.centralizer (L : Set G))).relIndex ⁅V, L⁆ := by
    have h1 := Subgroup.index_ker π
    rw [hker, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top, hUC] at h1
    have h2 : Nat.card (Multiplicative A) = Nat.card A := Nat.card_congr Multiplicative.toAdd
    rw [h2] at h1
    exact h1.symm
  unfold SocleLE
  rw [hcard]
  have hcomm : ∀ a ∈ ⁅V, L⁆, ∀ b ∈ V ⊓ Subgroup.centralizer (L : Set G), a * b = b * a :=
    fun a ha b hb => hVc a (hUV ha) b hb.1
  let f : ↥⁅V, L⁆ ⧸ ((⁅V, L⁆ ⊓ (V ⊓ Subgroup.centralizer (L : Set G))).subgroupOf ⁅V, L⁆) →
      ↥(⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G))) ⧸
        ((V ⊓ Subgroup.centralizer (L : Set G)).subgroupOf
          (⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)))) :=
    Quotient.map'
      (fun u : ↥⁅V, L⁆ =>
        (⟨(u : G), Subgroup.mem_sup_left u.2⟩ :
          ↥(⁅V, L⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)))))
      (fun u v huv => by
        rw [QuotientGroup.leftRel_apply] at huv ⊢
        have := Subgroup.mem_subgroupOf.mp huv
        exact Subgroup.mem_subgroupOf.mpr (by simpa using this.2))
  have hf : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      obtain ⟨a, ha, b, hb, hx⟩ := (mem_sup_iff_of_commute hcomm).mp x.2
      refine ⟨Quotient.mk'' ⟨a, ha⟩, ?_⟩
      show Quotient.mk'' _ = Quotient.mk'' _
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
      change (a : G)⁻¹ * (x : G) ∈ V ⊓ Subgroup.centralizer (L : Set G)
      rw [show (x : G) = a * b from hx]
      have : a⁻¹ * (a * b) = b := by group
      rw [this]
      exact hb
  have := Nat.card_le_card_of_surjective f hf
  simpa [Subgroup.relIndex, Subgroup.index] using this

theorem perm_mem_alternatingGroup_of_perfect {L : Subgroup G} (hL : ⁅L, L⁆ = L) {N : ℕ}
    (ρ : ↥L →* Equiv.Perm (Fin N)) (l : ↥L) : ρ l ∈ alternatingGroup (Fin N) := by
  set ψ : ↥L →* ℤˣ := Equiv.Perm.sign.comp ρ with hψ
  have hle : ⁅L, L⁆ ≤ ψ.ker.map L.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨⁅(⟨x, hx⟩ : ↥L), ⟨y, hy⟩⁆, ?_, rfl⟩
    show ψ ⁅(⟨x, hx⟩ : ↥L), ⟨y, hy⟩⁆ = 1
    simp only [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hl : (l : G) ∈ ψ.ker.map L.subtype := hle (by rw [hL]; exact l.2)
  obtain ⟨k, hk, hkl⟩ := hl
  have hkl' : k = l := Subtype.ext hkl
  subst hkl'
  have hk' : ψ k = 1 := hk
  exact Equiv.Perm.mem_alternatingGroup.mpr hk'

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle

end
