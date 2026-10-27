module

public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem card_dvd_of_center_quotient {K B : Subgroup G} (hBK : B ≤ K)
    (hZ : ∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → ∀ x ∈ K, z * x = x * z) :
    Nat.card (↥B ⧸ center ↥B) ∣ Nat.card (↥K ⧸ center ↥K) := by
  have hle : center ↥B ≤ (center ↥K).comap (Subgroup.inclusion hBK) := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y
    have hzc : ∀ b ∈ B, (z : G) * b = b * (z : G) := fun b hb =>
      congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨b, hb⟩).symm
    exact Subtype.ext (hZ z z.2 hzc y y.2).symm
  let f : ↥B ⧸ center ↥B →* ↥K ⧸ center ↥K :=
    QuotientGroup.map (center ↥B) (center ↥K) (Subgroup.inclusion hBK) hle
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with | H b => ?_
    rw [QuotientGroup.eq_one_iff]
    have hb : Subgroup.inclusion hBK b ∈ center ↥K := by
      rw [← QuotientGroup.eq_one_iff]
      exact hq
    rw [Subgroup.mem_center_iff]
    intro b'
    have := (Subgroup.mem_center_iff.1 hb) (Subgroup.inclusion hBK b')
    apply Subtype.ext
    simpa using congrArg Subtype.val this
  exact Subgroup.card_dvd_of_injective f hf

theorem doubleCover_of_alt [Finite G] {k m : ℕ} (hk : 8 ≤ k) (hm : 5 ≤ m) {K B : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) (hK2 : IsPGroup 2 ↥(center ↥K)) (hBK : B ≤ K)
    (hB : IsDoubleCoverOfAlt ↥B k)
    (hZ : ∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → ∀ x ∈ K, z * x = x * z) {u : G} (huB : u ∈ B)
    (hu2 : orderOf u = 2) (huK : ∀ x ∈ K, u * x = x * u)
    (e : ↥K ⧸ center ↥K ≃* alternatingGroup (Fin m)) :
    k ≤ m ∧ IsDoubleCoverOfAlt ↥K m := by
  obtain ⟨-, -, ⟨eB⟩⟩ := hB
  have hkm : k ≤ m := by
    have hdvd := card_dvd_of_center_quotient hBK hZ
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [Nat.card_congr eB.toEquiv, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_fin, Fintype.card_fin] at hdvd
    have hk2 : 2 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have hm2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have hle : k.factorial / 2 ≤ m.factorial / 2 :=
      Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos m) hm2) (by norm_num)) hdvd
    have h1 := Nat.mul_div_cancel' hk2
    have h2 := Nat.mul_div_cancel' hm2
    by_contra hlt
    push Not at hlt
    have := (Nat.factorial_lt (by omega : 0 < m)).2 hlt
    omega
  refine ⟨hkm, ?_⟩
  have : Group.IsPerfect ↥K := hq.1
  let η : ↥K →* alternatingGroup (Fin m) := e.toMonoidHom.comp (QuotientGroup.mk' (center ↥K))
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center ↥K) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hK2' : IsPGroup 2 ↥η.ker := by
    rw [hker]
    exact hK2
  have hcard : Nat.card ↥η.ker ≤ 2 :=
    CFSG.LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
      hm η hη hker.le hK2'
  rw [hker] at hcard
  have huKmem : u ∈ K := hBK huB
  have huc : (⟨u, huKmem⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (huK y y.2).symm
  have hord : orderOf (⟨⟨u, huKmem⟩, huc⟩ : ↥(center ↥K)) = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hu2
  have hdvd : 2 ∣ Nat.card ↥(center ↥K) := hord ▸ orderOf_dvd_natCard _
  have hcard2 : Nat.card ↥(center ↥K) = 2 :=
    le_antisymm hcard (Nat.le_of_dvd Nat.card_pos hdvd)
  exact ⟨hq, hcard2, ⟨e⟩⟩

end CFSG.EvenSporadicStandard.Induction.Balance
