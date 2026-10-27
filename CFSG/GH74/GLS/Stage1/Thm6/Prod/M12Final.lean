module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12Stage1
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.RnBar

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.M12Facts
  CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.Stage1.Thm6.Sec14 CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn
  CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Final

variable {G : Type} [Group G] [Finite G] {S T V : Subgroup G} {a b y x : G}

theorem exists_barImg (h91 : IVK_9_1) (hK : IsKProperSimple G) (o : Out13 G x T V S a b y) :
    ∃ (S' : Subgroup (CentralizerBar (a ^ 2 * b ^ 2))) (a' b' y' x' : CentralizerBar (a ^ 2 * b ^ 2)),
      BarImg o.data S' a' b' y' x' := by
  have h := o.data
  have hS := o.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf3, hf, -, v, hv, hfv⟩ := o.f3
  have hvU : v ∈ nfSub h pU closed_pU := by rw [← U_eq h, ← o.V_eq]; exact hv
  have hF1 : ∀ c ∈ S, c * c = a ^ 2 * b ^ 2 →
      ∃ g ∈ centralizer ({a ^ 2 * b ^ 2} : Set G), g * c * g⁻¹ ∈ closure ({a, b} : Set G) ∧
        (g * c * g⁻¹) * (g * c * g⁻¹) = a ^ 2 * b ^ 2 := by
    intro c hc hcz
    obtain ⟨g, hg1, hg2, hg3⟩ := lemma14_2c o hf3 hf hvU hfv hc hcz
    refine ⟨g, ?_, hg2, hg3⟩
    rw [mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    calc (a ^ 2 * b ^ 2) * g = (g * (a ^ 2 * b ^ 2) * g⁻¹) * g := by rw [hg1]
      _ = g * (a ^ 2 * b ^ 2) := by group
  have hUH : closure ({a * a, b * b} : Set G) ≤ closure ({a, b} : Set G) := by
    rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hF2 : ∀ g ∈ Cz a b, g * x * g⁻¹ ∉ closure ({a * a, b * b} : Set G) :=
    fun g _ hm => o.fusion g (hUH hm)
  have hKC : IsKGroupNative ↥(Cz a b) := hK.isKGroupNative_of_ne_top (Cz_ne_top h hK)
  obtain ⟨S', a', b', y', x', h', hS', hz', himg, ha, hb, hy, hx, hc⟩ :=
    lemma14_3_bar h91 h hKC hS hF1 hF2
  have hnu : ∀ p : NF, toBar (a ^ 2 * b ^ 2) (νC h p) = nu a' b' y' x' p := by
    intro p
    have e : νC h p = (⟨a, S_le_Cz h (a_mem h)⟩ : ↥(Cz a b)) ^ p.1.val *
        (⟨b, S_le_Cz h (b_mem h)⟩ : ↥(Cz a b)) ^ p.2.1.val *
        ((⟨y, S_le_Cz h (y_mem h)⟩ : ↥(Cz a b)) ^ p.2.2.1.val *
          (⟨x, S_le_Cz h (x_mem h)⟩ : ↥(Cz a b)) ^ p.2.2.2.val) :=
      Subtype.ext (by simp [νC, nu])
    rw [e]
    simp only [map_mul, map_pow]
    rw [show toBar (a ^ 2 * b ^ 2) ⟨a, S_le_Cz h (a_mem h)⟩ = a' from ha _ rfl,
      show toBar (a ^ 2 * b ^ 2) ⟨b, S_le_Cz h (b_mem h)⟩ = b' from hb _ rfl,
      show toBar (a ^ 2 * b ^ 2) ⟨y, S_le_Cz h (y_mem h)⟩ = y' from hy _ rfl,
      show toBar (a ^ 2 * b ^ 2) ⟨x, S_le_Cz h (x_mem h)⟩ = x' from hx _ rfl]
    rfl
  exact ⟨S', a', b', y', x', ⟨h', hS', hz', hnu, hc⟩⟩

end Final

end CFSG.GH74.GLS.Stage1.Thm6.Prod
