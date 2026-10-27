module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Bg.Thompson

variable {G : Type} [Group G] [Finite G]

theorem involution_quot_cyclic {S M₀ : Subgroup G} (hn : ∀ s ∈ S, ∀ q ∈ M₀, s * q * s⁻¹ ∈ M₀)
    (hM₀S : M₀ ≤ S) (hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ M₀) {t t' : G}
    (ht : t ∈ S) (ht' : t' ∈ S) (ht2 : t * t ∈ M₀) (ht'2 : t' * t' ∈ M₀) (hn1 : t ∉ M₀)
    (hn2 : t' ∉ M₀) : t⁻¹ * t' ∈ M₀ := by
  classical
  set N : Subgroup ↥S := M₀.subgroupOf S with hN
  have hmemN : ∀ y : ↥S, y ∈ N ↔ (y : G) ∈ M₀ := fun y => Subgroup.mem_subgroupOf
  have : N.Normal := ⟨fun y hy w => by
    rw [hmemN] at hy ⊢
    have := hn (w : G) w.2 (y : G) hy
    simpa using this⟩
  have : Fintype ↥S := Fintype.ofFinite _
  have : Fintype (↥S ⧸ N) := Fintype.ofFinite _
  have hcycQ : IsCyclic (↥S ⧸ N) := by
    obtain ⟨b, hbS, hb⟩ := hcyc
    refine ⟨⟨QuotientGroup.mk ⟨b, hbS⟩, fun y => ?_⟩⟩
    induction y using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨k, hk⟩ := hb (y : G) y.2
      refine ⟨k, ?_⟩
      show (QuotientGroup.mk (⟨b, hbS⟩ : ↥S) : ↥S ⧸ N) ^ k = QuotientGroup.mk y
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, hmemN]
      have : ((⟨b, hbS⟩ : ↥S) ^ k)⁻¹ * y = ⟨(b ^ k)⁻¹ * (y : G), S.mul_mem (S.inv_mem (S.zpow_mem hbS k)) y.2⟩ := by
        apply Subtype.ext; simp
      rw [this]
      exact hk
  have h2 : (Finset.univ.filter fun a : ↥S ⧸ N => a ^ 2 = 1).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  by_contra hcon
  set a : ↥S ⧸ N := QuotientGroup.mk ⟨t, ht⟩
  set a' : ↥S ⧸ N := QuotientGroup.mk ⟨t', ht'⟩
  have ha2 : a ^ 2 = 1 := by
    rw [sq, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hmemN]; exact ht2
  have ha'2 : a' ^ 2 = 1 := by
    rw [sq, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hmemN]; exact ht'2
  have ha1 : a ≠ 1 := fun h => hn1 ((hmemN _).mp ((QuotientGroup.eq_one_iff _).mp h))
  have ha'1 : a' ≠ 1 := fun h => hn2 ((hmemN _).mp ((QuotientGroup.eq_one_iff _).mp h))
  have haa' : a ≠ a' := by
    intro h
    apply hcon
    have := QuotientGroup.eq.mp h
    rw [hmemN] at this
    simpa using this
  have hsub : ({1, a, a'} : Finset (↥S ⧸ N)) ⊆ Finset.univ.filter fun a : ↥S ⧸ N => a ^ 2 = 1 := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with rfl | rfl | rfl
    · simp
    · exact ha2
    · exact ha'2
  have hcard : ({1, a, a'} : Finset (↥S ⧸ N)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair haa']
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ha1.symm, ha'1.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem exists_conj_mem_of_cyclic_quot (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {S M₀ : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hM₀S : M₀ ≤ S)
    (hn : ∀ s ∈ S, ∀ q ∈ M₀, s * q * s⁻¹ ∈ M₀)
    (hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ M₀) {t : G} (htS : t ∈ S)
    (ht2 : orderOf t = 2) : ∃ g : G, g⁻¹ * t * g ∈ M₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases htM : t ∈ M₀
  · exact ⟨1, by simpa using htM⟩
  obtain ⟨hSle, hSp, hSdvd⟩ := isSylowOf_iff.mp hS
  have hSdvd' : ¬ 2 ∣ S.index := by rwa [Subgroup.relIndex_top_right] at hSdvd
  have ht1 : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have key := thompson_transfer_1515 (p := 2) (X := G) (P := S) (Q := M₀) (u := t) hSp hSdvd'
    (fun s hs q hq => hn s hs q hq) hcyc htS htM
    (fun g k _ => by
      have : t ^ (2 * k) = 1 := by rw [pow_mul, ht1, one_pow]
      rw [this]
      simp)
    (fun g hgS _ => by
      have hgsq : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
        have : (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        rw [this, show t * t = 1 by rw [← sq]; exact ht1]
        group
      by_cases hmem : g⁻¹ * t * g ∈ M₀
      · exact Or.inl hmem
      · right
        have htt : t * t ∈ M₀ := by
          rw [← sq, ht1]; exact M₀.one_mem
        have := involution_quot_cyclic hn hM₀S hcyc htS hgS htt (by rw [hgsq]; exact M₀.one_mem) htM hmem
        exact this)
  rcases key with ⟨N, hN, hcycN, -, htN⟩ | ⟨g, hgQ, -, -⟩
  · exfalso
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · subst h
      have hcycG : IsCyclic G := by
        exact isCyclic_of_surjective (QuotientGroup.quotientBot (G := G)).toMonoidHom
          (QuotientGroup.quotientBot (G := G)).surjective
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (mul_comm' a b)
    · exact htN (h ▸ Subgroup.mem_top t)
  · exact ⟨g, hgQ⟩

end CFSG.GH74.GLS.C3.Layer1.P89
