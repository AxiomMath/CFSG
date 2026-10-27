module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutKSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutBadKFalse
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutDich

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G]

structure KStructure (z : G) (F L1 : Subgroup G) : Prop where
  le_K : L1 ≤ Ksub z F
  F_le : F ≤ L1
  card : Nat.card L1 = 256
  sq : ∀ x ∈ L1, x * x = 1
  comm : ∀ x ∈ L1, ∀ y ∈ L1, x * y = y * x
  z_not_mem : z ∉ L1
  K_eq : Ksub z F = L1 ⊔ zpowers z
  inf_E : ∀ x ∈ L1, x ∈ F ⊔ zpowers z → x ∈ F
  cent_z : ∀ x ∈ L1, z * x = x * z → x ∈ F
  normalized : ∀ n : G, (∀ x, x ∈ F ⊔ zpowers z ↔ n * x * n⁻¹ ∈ F ⊔ zpowers z) →
    ∀ x, x ∈ L1 ↔ n * x * n⁻¹ ∈ L1
  not_conj : ∀ x ∈ L1, ¬ IsConj z x
  K_pgroup : IsPGroup 2 (Ksub z F)
  K_sylow : ¬ 2 ∣ (Ksub z F).relIndex (centralizer (F : Set G))
  L1_sylow : ¬ 2 ∣ L1.relIndex (centralizer (L1 : Set G))
  complement : ∃ N : Subgroup G, N ≤ centralizer (L1 : Set G) ∧
    (∀ c ∈ centralizer (L1 : Set G), ∀ x ∈ N, c * x * c⁻¹ ∈ N) ∧ ¬ 2 ∣ Nat.card N ∧
    Disjoint N L1 ∧ N ⊔ L1 = centralizer (L1 : Set G)
  char : ∀ n : G, (∀ x, x ∈ Ksub z F ↔ n * x * n⁻¹ ∈ Ksub z F) →
    ∀ x, x ∈ L1 ↔ n * x * n⁻¹ ∈ L1
  fusion : ∀ k ∈ Ksub z F, IsConj z k → ∃ f ∈ F, k = z * f

namespace OutOne

variable [Finite G] {L : Subgroup G} {z : G} {F : Subgroup G}

theorem goodK (h : OutOne L z F) (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) (hlift : LiftData L F) : GoodK z F := by
  rcases h.goodK_or_badK_of_fixed hsq X htrans with hgood | hbad
  · exact hgood
  · exact (h.badK_false hsq X htrans hbad hlift).elim

theorem kStructure (h : OutOne L z F) (hsq : ∀ g : G, g * g ≠ z) (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) (hlift : LiftData L F) (hcr : CentRank z) :
    ∃ L1 : Subgroup G, KStructure z F L1 := by
  have hgood := h.goodK hsq X htrans hlift
  obtain ⟨hK2, hK3⟩ := h.Ksub_sylow hsq hgood X htrans hcr
  obtain ⟨-, hL3⟩ := h.L1_sylow hsq hgood X htrans hcr
  have hBu := h.exists_normal_two_complement hsq hgood X htrans hcr
  exact ⟨h.L1sub hgood, ⟨h.L1sub_le_K hgood, h.F_le_L1sub hgood, h.card_L1sub hsq hgood X htrans,
    fun x hx => h.L1sub_sq hgood hx, fun x hx y hy => h.L1sub_comm hgood hx hy,
    h.z_not_mem_L1sub hgood, h.Ksub_eq_L1_sup hsq hgood X,
    fun x hx hxE => h.L1sub_inf_E hgood hx hxE,
    fun x hx hxz => h.L1sub_centralizer_z hgood hx hxz,
    fun n hn => h.L1_normalized hgood hn,
    fun x hx => h.L1_not_isConj hsq hgood X htrans hcr hx, hK2, hK3, hL3, hBu,
    fun n hn => h.L1_normalized_of_normalizes_K hsq hgood X htrans hn,
    fun k hk hconj => h.eq_mul_of_isConj_of_mem_Ksub hsq hgood X htrans hcr hk hconj⟩⟩

end OutOne

end CFSG.EvenSporadicStandard.M22Std
