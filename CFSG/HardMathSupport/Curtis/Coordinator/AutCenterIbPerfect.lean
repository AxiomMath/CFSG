module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages
import CFSG.HardMathSupport.Curtis.Proving.NineDvdCentralizer
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.RankThreeCoreUniqueness.Helpers

variable {Y : Type*} [Group Y] [Finite Y]

theorem not_nine_dvd_card_of_surjective_of_perfect {X : Type*} [Group X] {J : Subgroup Y}
    (hJ : IbPerfectSections 3 J) (ψ : ↥J →* X) (hψ : Function.Surjective ψ) (B : Subgroup X)
    (hB : ⁅B, B⁆ = B) : ¬ 9 ∣ Nat.card B := by
  have hBp : Group.IsPerfect B := Subgroup.isPerfect_iff.mpr hB
  set R₀ := perfectResidualOf (B.comap ψ)
  have hR₀ : R₀.map ψ = B := finite_canonical_perfect_preimage_image_eq ψ hψ B hBp
  have hR₀p : ⁅R₀, R₀⁆ = R₀ :=
    Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect (B.comap ψ))
  have hV := hJ _ (Subgroup.map_subtype_le R₀) (by rw [← Subgroup.map_commutator, hR₀p])
  rw [Subgroup.card_map_of_injective J.subtype_injective] at hV
  intro h9
  rw [← hR₀] at h9
  exact hV ((show (3 : ℕ) ^ 2 = 9 by norm_num) ▸ h9.trans (Subgroup.card_map_dvd R₀ ψ))

theorem nine_dvd_card_alternatingGroup {n : ℕ} (hn : 6 ≤ n) :
    9 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hn
  rw [hk, show Nat.factorial 6 = 2 * 360 by rfl, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  exact Dvd.dvd.mul_right (by norm_num) k

theorem nine_dvd_card_of_fix {L J : Subgroup Y} {u : Y} (hu : u ∈ L) (hu3 : u ^ 3 = 1)
    (hu1 : u ≠ 1) (h9 : 9 ∣ Nat.card L) (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) :
    9 ∣ Nat.card J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set l' : ↥L := ⟨u, hu⟩ with hl'
  have hl'3 : orderOf l' = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hu3)) (fun h => hu1 (congrArg Subtype.val h))
  have hC9 := CFSG.HardMathSupport.Curtis.Proving.nine_dvd_card_centralizer_of_orderOf_eq_three
    h9 hl'3
  have hmap : (Subgroup.centralizer ({l'} : Set ↥L)).map L.subtype ≤ J := by
    rintro _ ⟨x, hx, rfl⟩
    refine hfix x x.2 ?_
    have hxl : (x : Y) * u = u * x := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx)
    calc u * (x : Y) * u⁻¹ = (x * u) * u⁻¹ := by rw [← hxl]
      _ = x := by group
  rw [← Subgroup.card_map_of_injective L.subtype_injective] at hC9
  exact hC9.trans (Subgroup.card_dvd_of_le hmap)

theorem false_of_surjective_perm_of_nine {J : Subgroup Y} {n : ℕ} (hn : 6 ≤ n)
    (hJ : IbPerfectSections 3 J) (ψ : ↥J →* Equiv.Perm (Fin n)) (hψ : Function.Surjective ψ) :
    False := by
  have h5 : 5 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  exact not_nine_dvd_card_of_surjective_of_perfect hJ ψ hψ (alternatingGroup (Fin n))
    (commutator_alternatingGroup_eq_self h5) (nine_dvd_card_alternatingGroup hn)

theorem not_nine_dvd_card_of_quotient_perm_ib {J : Subgroup Y} {n : ℕ}
    (hJ : IbPerfectSections 3 J) (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n)) :
    ¬ 9 ∣ Nat.card J := by
  have hn : n ≤ 5 := by
    by_contra h
    exact false_of_surjective_perm_of_nine (by omega) hJ
      (e.toMonoidHom.comp (QuotientGroup.mk' _))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥J),
    Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
  rw [hk]
  intro h9
  have h9' : 9 ∣ n.factorial :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right _ (by norm_num)) h9
  interval_cases n <;> revert h9' <;> decide

theorem false_of_quotient_sp_of_nine {J : Subgroup Y} {k : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hk : 3 ≤ k) (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q)
    (hJ : IbPerfectSections 3 J)
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  have hQ := kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds k d hk hd
  have h := not_nine_dvd_card_of_surjective_of_perfect hJ
    (e.toMonoidHom.comp (QuotientGroup.mk' _))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ⊤ (by rw [← commutator_def, hQ])
  rw [Subgroup.card_top] at h
  obtain ⟨q, hq2, hdq⟩ := hd
  have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
  have hqp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp
    (hpe ▸ dvd_pow_self q.p q.exponent_pos.ne')
  have hqe : q.exponent = 1 := by
    rw [hqp] at hpe
    exact Nat.pow_right_injective le_rfl (by simpa using hpe)
  have hN : Nat.card (CatGroup d) = CFSG.Open.ordBC k (2 ^ q.exponent) :=
    card_catGroup_B_even hk hqp hdq
  have h9 : 9 ∣ CFSG.Open.ordBC k 2 := by
    unfold CFSG.Open.ordBC
    rw [show Nat.gcd 2 (2 - 1) = 1 by norm_num, Nat.div_one]
    refine Dvd.dvd.mul_left ?_ _
    have hsub : Finset.Icc 1 3 ⊆ Finset.Icc 1 k := Finset.Icc_subset_Icc_right hk
    refine Dvd.dvd.trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    decide
  change ¬ 9 ∣ Nat.card (CatGroup d) at h
  rw [hN, hqe, pow_one] at h
  exact h h9

end CFSG.HardMathSupport.Curtis.Coordinator
