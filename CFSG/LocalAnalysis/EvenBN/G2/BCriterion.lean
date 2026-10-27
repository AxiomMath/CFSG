module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYFourFacts

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint

theorem le_of_inf_centralizer_le_of_le_normalizer {G : Type*} [Group G] [Finite G]
    {A B J : Subgroup G} (hAB : A ≤ normalizer (B : Set G)) (hJB : J ≤ B)
    (hJA : J ≤ normalizer (A : Set G)) (hsolv : Group.IsSolvable A)
    (hcop : (Nat.card J).Coprime (Nat.card A)) (hfix : A ⊓ centralizer (J : Set G) ≤ B) :
    A ≤ B := by
  intro a ha
  obtain ⟨c, hc, n, hn, rfl⟩ := Common.exists_mem_inf_centralizer_mul_of_coprime
    (M := A) (N := A ⊓ B) (S := J) inf_le_left
    (fun y hy => Common.mem_normalizer_inf (Subgroup.le_normalizer hy) (hAB hy)) hJA
    (fun j hj => Common.mem_normalizer_inf (hJA hj) (Subgroup.le_normalizer (hJB hj))) hsolv hcop ha
    fun j hj => Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha) ((mem_normalizer_iff.1 (hJA hj) a).1 ha),
      by
        rw [show a⁻¹ * (j * a * j⁻¹) = (a⁻¹ * j * a⁻¹⁻¹) * j⁻¹ by group]
        exact mul_mem ((mem_normalizer_iff.1 (hAB (inv_mem ha)) j).1 (hJB hj))
          (inv_mem (hJB hj))⟩
  exact mul_mem (hfix hc) (Subgroup.mem_inf.1 hn).2

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section BCriterion

variable {K : Type} [Field K]
  [Finite K]

theorem le_yamadaB_of_four (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {A : Subgroup G} (hA2 : IsPGroup 2 A) (hAH : A ≤ centralizer (d.J₁ : Set G))
    (hJ₃A : d.J₃ ≤ normalizer (A : Set G))
    (hfix : A ⊓ centralizer (d.J₃ : Set G) ≤ yamadaB d) : A ≤ yamadaB d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ₃K : d.J₃ ≤ L ⊓ centralizer (d.J₁ : Set G) := fun j hj =>
    ⟨d.image_le _ hj, mem_centralizer_iff.2 fun j' hj' => d.J₁_comm_J₃ hj' hj⟩
  have hBN : ∀ {x : G}, x ∈ centralizer (d.J₁ : Set G) →
      x ∈ normalizer ((yamadaB d : Subgroup G) : Set G) := fun {x} hx =>
    mem_normalizer_iff.2 fun b => ⟨fun hb => conj_mem_yamadaB d hx hb, fun hb => by
      have := conj_mem_yamadaB d (inv_mem hx) hb
      rwa [inv_inv, show x⁻¹ * (x * b * x⁻¹) * x = b by group] at this⟩
  have hsolv : Group.IsSolvable A := by
    have := hA2.isNilpotent
    infer_instance
  have hcop : (Nat.card d.J₃).Coprime (Nat.card A) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA2
    rw [hk, d.card_J₃, hK]
    exact (odd_two_pow_sub_one (by have := h.two_le; omega)).coprime_two_right.pow_right k
  exact le_of_inf_centralizer_le_of_le_normalizer (fun x hx => hBN (hAH hx))
    (hJ₃K.trans (inf_centralizer_J₁_le_yamadaB d)) hJ₃A hsolv hcop hfix

end BCriterion

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
