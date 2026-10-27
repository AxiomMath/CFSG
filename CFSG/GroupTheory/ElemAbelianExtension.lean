module

public import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.GroupTheory

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem exists_isElemAbelian_card_pow_three_ne_of_lt {p : ℕ} [Fact p.Prime] {A E : Subgroup G}
    (hAE : A ≤ E) (hE : IsElemAbelian p E) (hAcard : Nat.card A = p ^ 3)
    (hlt : Nat.card A < Nat.card E) :
    ∃ B : Subgroup G, B ≤ E ∧ IsElemAbelian p B ∧ Nat.card B = p ^ 3 ∧ B ≠ A := by
  classical
  have hp := (Fact.out : p.Prime)
  have hAlt : A < E := lt_of_le_of_ne hAE fun h => absurd hlt (by rw [h]; exact lt_irrefl _)
  obtain ⟨-, x, hxE, hxA⟩ := SetLike.lt_iff_le_and_exists.mp hAlt
  have hx1 : x ≠ 1 := fun h => hxA (h ▸ A.one_mem)
  have hxpow : x ^ p = 1 := hE.2 x hxE
  have hxord : orderOf x = p := orderOf_eq_prime hxpow hx1
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) p (n := 2)
    (by rw [hAcard]; exact pow_dvd_pow p (by norm_num))
  let C : Subgroup G := K.map A.subtype
  have hCA : C ≤ A := Subgroup.map_subtype_le K
  have hCcard : Nat.card C = p ^ 2 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hKcard
  have hCea : IsElemAbelian p C := hE.mono (hCA.trans hAE)
  have hxA' : x ∉ C := fun h => hxA (hCA h)
  have hdisj : Disjoint C (Subgroup.zpowers x) := by
    rw [disjoint_iff]
    have hdvd : Nat.card (C ⊓ Subgroup.zpowers x : Subgroup G) ∣ p := by
      have := Subgroup.card_dvd_of_le
        (inf_le_right : C ⊓ Subgroup.zpowers x ≤ Subgroup.zpowers x)
      rwa [Nat.card_zpowers, hxord] at this
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : C ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [Nat.card_zpowers, hxord, h2])
      have hxmem : x ∈ C ⊓ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxA' hxmem.1
  have hcommE : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hcommEx : a * x = x * a := by
      simpa using hE.1.is_comm.comm ⟨a, ha⟩ ⟨x, hxE⟩
    exact (Commute.zpow_right hcommEx n).eq
  have hcomm : ∀ a ∈ C, ∀ b ∈ Subgroup.zpowers x, a * b = b * a :=
    fun a ha b hb => hcommE a (hAE (hCA ha)) b hb
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (C : Set G) := by
    intro b hb
    have hbE : b ∈ E := (Subgroup.zpowers_le.mpr hxE) hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have hconj : b * a * b⁻¹ = a := by
        have hba : b * a = a * b := (hcomm a ha b hb).symm
        rw [hba, mul_assoc, mul_inv_cancel, mul_one]
      rw [hconj]
      exact ha
    · intro ha
      have hcE : b * a * b⁻¹ ∈ E := hAE (hCA ha)
      have haE : a ∈ E := by
        have h1 : b⁻¹ * (b * a * b⁻¹) ∈ E := E.mul_mem (E.inv_mem hbE) hcE
        have h2 : b⁻¹ * (b * a * b⁻¹) * b ∈ E := E.mul_mem h1 hbE
        simpa [mul_assoc] using h2
      have hconj : b * a * b⁻¹ = a := by
        have hba : b * a = a * b := (hcommE a haE b hb).symm
        rw [hba, mul_assoc, mul_inv_cancel, mul_one]
      rwa [hconj] at ha
  have hBcard : Nat.card (C ⊔ Subgroup.zpowers x : Subgroup G) = p ^ 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer C
      (Subgroup.zpowers x) hnorm hdisj, hCcard, Nat.card_zpowers, hxord]
    ring
  have hBea : IsElemAbelian p (C ⊔ Subgroup.zpowers x) :=
    IsElemAbelian.sup_of_commute hCea (isElemAbelian_zpowers hxpow) hcomm
  refine ⟨C ⊔ Subgroup.zpowers x, sup_le (hCA.trans hAE) (Subgroup.zpowers_le.mpr hxE),
    hBea, hBcard, ?_⟩
  intro heq
  exact hxA (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

end CFSG.GroupTheory
