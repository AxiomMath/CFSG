module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

variable {G : Type*} [Group G]

theorem relIndex_centralizer_normalizer_dvd_totient' [Finite G] (Q : Subgroup G) [IsCyclic Q] :
    (Subgroup.centralizer (Q : Set G)).relIndex (Subgroup.normalizer (Q : Set G)) ∣
      (Nat.card Q).totient := by
  have key := Subgroup.card_dvd_of_injective _ (QuotientGroup.kerLift_injective
    Q.normalizerMonoidHom)
  rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex,
    IsCyclic.card_mulAut] at key
  exact key

theorem card_div_card_inf_normalizer_modEq [Finite G] {p : ℕ} [Fact p.Prime] {S L : Subgroup G}
    (hSL : S ≤ L) (hS : IsPGroup p S) (hidx : ¬ p ∣ S.relIndex L) :
    Nat.card L / Nat.card (L ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) % p = 1 := by
  let S' : Sylow p L := (hS.comap_subtype (K := L)).toSylow hidx
  have h1 := card_sylow_modEq_one p L
  rw [Sylow.card_eq_index_normalizer S'] at h1
  have hS' : (S' : Set L) = ((S.subgroupOf L : Subgroup L) : Set L) := rfl
  rw [hS', ← Subgroup.subgroupOf_normalizer_eq hSL] at h1
  have hcard : Nat.card ((Subgroup.normalizer (S : Set G)).subgroupOf L) =
      Nat.card (L ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) := by
    have : (Subgroup.normalizer (S : Set G)).subgroupOf L =
        (L ⊓ Subgroup.normalizer (S : Set G) : Subgroup G).subgroupOf L := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hidx' := ((Subgroup.normalizer (S : Set G)).subgroupOf L).card_mul_index
  rw [hcard] at hidx'
  have hpos : 0 < Nat.card (L ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) := Nat.card_pos
  rw [← hidx', Nat.mul_div_cancel_left _ hpos]
  have h2 : _ % p = 1 % p := h1
  rw [h2]
  exact Nat.one_mod_eq_one.mpr (Fact.out : p.Prime).ne_one

theorem exists_sylow_test {Γ : Type*} [Group Γ] [Finite Γ] (M : Subgroup Γ) {p X : ℕ}
    [hp : Fact p.Prime] (hpM : p ∣ Nat.card M) (hpK : ¬ p ^ 2 ∣ Nat.card Γ)
    (hX : ∀ w : Γ, orderOf w = p → Nat.card (Subgroup.centralizer ({w} : Set Γ)) ∣ X) :
    ∃ c r m : ℕ, p ∣ c ∧ c ∣ X ∧ r ∣ p - 1 ∧ c * r ∣ Nat.card Γ ∧
      Nat.card Γ / (c * r) % p = 1 ∧ p ∣ m ∧ m ∣ c * r ∧ m ∣ Nat.card M ∧
      Nat.card M / m % p = 1 := by
  obtain ⟨w', hw'⟩ := exists_prime_orderOf_dvd_card' (G := M) p hpM
  set w : Γ := (w' : Γ) with hw
  have hwo : orderOf w = p := by rw [hw, Subgroup.orderOf_coe, hw']
  have hwM : w ∈ M := w'.2
  set S := Subgroup.zpowers w with hS
  have hScard : Nat.card S = p := by rw [hS, Nat.card_zpowers, hwo]
  have hSM : S ≤ M := (Subgroup.zpowers_le).mpr hwM
  have hSp : IsPGroup p S := IsPGroup.of_card (n := 1) (by rw [hScard, pow_one])
  have hidxΓ : ¬ p ∣ S.index := by
    intro h
    apply hpK
    rw [← S.card_mul_index, hScard, pow_two]
    exact Nat.mul_dvd_mul_left p h
  have hidxM : ¬ p ∣ S.relIndex M := by
    intro h
    apply hidxΓ
    rw [← Subgroup.relIndex_mul_index hSM]
    exact Dvd.dvd.mul_right h _
  have hidxT : ¬ p ∣ S.relIndex ⊤ := by rwa [Subgroup.relIndex_top_right]
  set C := Subgroup.centralizer (S : Set Γ) with hC
  set N := Subgroup.normalizer (S : Set Γ) with hN
  have hCw : C = Subgroup.centralizer ({w} : Set Γ) := by
    rw [hC, hS, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hSC : S ≤ C := by
    rw [hCw, hS, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  have : IsCyclic S := by rw [hS]; exact Subgroup.isCyclic_zpowers w
  have hr := relIndex_centralizer_normalizer_dvd_totient' S
  rw [hScard, Nat.totient_prime hp.out] at hr
  have hcr : Nat.card C * C.relIndex N = Nat.card N := by
    have h := C.relIndex_mul_card (K := N)
    rw [inf_eq_left.mpr hCN, mul_comm] at h
    exact h
  refine ⟨Nat.card C, C.relIndex N, Nat.card (M ⊓ N : Subgroup Γ), ?_, ?_, hr, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [← hScard]; exact Subgroup.card_dvd_of_le hSC
  · rw [hCw]; exact hX w hwo
  · rw [hcr]; exact Subgroup.card_subgroup_dvd_card N
  · have h := card_div_card_inf_normalizer_modEq (le_top : S ≤ ⊤) hSp hidxT
    rwa [Subgroup.card_top, top_inf_eq, ← hN, ← hcr] at h
  · rw [← hScard]
    exact Subgroup.card_dvd_of_le (le_inf hSM Subgroup.le_normalizer)
  · rw [hcr]; exact Subgroup.card_dvd_of_le inf_le_right
  · exact Subgroup.card_dvd_of_le inf_le_left
  · exact card_div_card_inf_normalizer_modEq hSM hSp hidxM

end CFSG.HardMathSupport.Malle.Coordinator
