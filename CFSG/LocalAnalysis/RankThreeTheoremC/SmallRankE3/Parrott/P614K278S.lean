module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreAlmost
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.L34Exp3
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K278Cent
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmComp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K278

open CFSG.Open Subgroup
open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq (k1Core_exists_action)

variable {X : Type} [Group X] [Finite X]

theorem card_mul_card_le_of_inf_eq_bot {R A B : Subgroup X} (hAR : A ≤ R) (hBR : B ≤ R)
    (h : B ⊓ A = ⊥) : Nat.card B * Nat.card A ≤ Nat.card R := by
  let f : B × A → R := fun p => ⟨(p.1 : X) * p.2, mul_mem (hBR p.1.2) (hAR p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨b, a⟩ ⟨b', a'⟩ hba
    have h1 : (b : X) * a = b' * a' := congrArg Subtype.val hba
    have h2 : (b' : X)⁻¹ * b = a' * (a : X)⁻¹ := by
      calc (b' : X)⁻¹ * b = (b' : X)⁻¹ * (b * a) * (a : X)⁻¹ := by group
        _ = (b' : X)⁻¹ * (b' * a') * (a : X)⁻¹ := by rw [h1]
        _ = a' * (a : X)⁻¹ := by group
    have h3 : (b' : X)⁻¹ * b ∈ B ⊓ A :=
      mem_inf.mpr ⟨B.mul_mem (B.inv_mem b'.2) b.2, h2 ▸ A.mul_mem a'.2 (A.inv_mem a.2)⟩
    rw [h, mem_bot] at h3
    have hb : b = b' := Subtype.ext (inv_mul_eq_one.mp h3).symm
    have ha : a = a' := by
      rw [hb] at h1
      exact Subtype.ext (mul_left_cancel h1)
    rw [hb, ha]
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective f hf

theorem card_le_27_of_dvd {P : Subgroup X} (hP : IsPGroup 3 P) (hdvd : Nat.card P ∣ 241920) :
    Nat.card P ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk] at hdvd ⊢
  have hk3 : k ≤ 3 := by
    by_contra h
    have h81 : 3 ^ 4 ∣ 241920 := (pow_dvd_pow 3 (not_le.mp h)).trans hdvd
    norm_num at h81
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 27 := by norm_num

theorem eq_one_of_mem_of_mem {S U : Subgroup X} (hS : IsPGroup 2 S) (hU : ∀ u ∈ U, u ^ 3 = 1)
    {w : X} (hwS : w ∈ S) (hwU : w ∈ U) : w = 1 := by
  obtain ⟨m, hm⟩ := hS ⟨w, hwS⟩
  have hm' : w ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hcop : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 3)
  have : w ^ Nat.gcd (2 ^ m) 3 = 1 := pow_gcd_eq_one.mpr ⟨hm', hU w hwU⟩
  rwa [hcop, pow_one] at this

theorem card_le_two_of_l34 (hO : KFactL34Outer) (hI : KFactL34Inner) {R : Sylow 3 X}
    {A X₀ K B S : Subgroup X} (h : D2AlmostSimple 3 X R A X₀ K) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hBR : B ≤ R)
    (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 9) (hBA : B ≠ A) (hS : IsPGroup 2 S)
    (hBS : B ≤ normalizer (S : Set X)) (hSX₀ : X₀ ⊔ S ≠ ⊤) : Nat.card S ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.normal
  have hA9 : Nat.card A = 9 := by rw [h.card_A]; norm_num
  have hAK : A ≤ K := h.le_of_l34 hO hd ⟨e⟩
  have hX₀ : X₀ = normalizer (A : Set X) := h.eq_normalizer_of_l34 hI hd ⟨e⟩ hAK
  have hSN : S ≤ normalizer (A : Set X) := by
    rcases hI d hd X K h.normal h.centralizer_eq_bot ⟨e⟩ A h.elem h.card_A hAK (X₀ ⊔ S)
        (hX₀ ▸ le_sup_left) with h1 | h1
    · exact h1 ▸ le_sup_right
    · exact absurd h1 hSX₀
  have hRN : (R : Subgroup X) ≤ normalizer (A : Set X) := hX₀ ▸ h.sylow_le
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ := Tits.S3AmalgamBound.exists_equiv_projectiveSL_of_l34Index hd e
  obtain ⟨ι, hι, -, hιk⟩ := k1Core_exists_action h.centralizer_eq_bot ψ
  have hR27 : Nat.card (R : Subgroup X) ≤ 27 := by
    refine card_le_27_of_dvd R.isPGroup' ?_
    rw [← CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut hF,
      ← card_map_of_injective hι]
    exact card_subgroup_dvd_card _
  obtain ⟨z, hzBA, hz1⟩ : ∃ z ∈ B ⊓ A, z ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : B ⊓ A = ⊥ := (eq_bot_iff_forall _).mpr hno
    have := card_mul_card_le_of_inf_eq_bot h.A_le hBR hbot
    rw [hBc, hA9] at this
    omega
  obtain ⟨b, hbB, hbnc⟩ : ∃ b ∈ B, ∃ u ∈ A, b * u ≠ u * b := by
    by_contra hno
    push Not at hno
    obtain ⟨w, hwB, hwA⟩ : ∃ w ∈ B, w ∉ A := by
      by_contra hno'
      push Not at hno'
      exact hBA (eq_of_le_of_card_ge hno' (by rw [hA9, hBc]))
    obtain ⟨hEel, hEc⟩ :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm.isElemAbelian_card_sup_zpowers_of_card
        Nat.prime_three h.elem h.card_A (hB.2 w hwB) hwA fun u hu => (hno w hwB u hu).symm
    have hER : A ⊔ zpowers w ≤ R := sup_le h.A_le (zpowers_le.mpr (hBR hwB))
    have h3 := CFSG.GH74.Uniqueness.SU.SU1.le_pRank (by norm_num) hER hEel hEc
    rw [h.pRank_eq] at h3
    omega
  have hzB : z ∈ B := hzBA.1
  have hzA : z ∈ A := hzBA.2
  have hSz : ∀ s ∈ S, s * z = z * s := by
    intro s hs
    have h1 : s * z * s⁻¹ * z⁻¹ ∈ S := by
      have : z * s⁻¹ * z⁻¹ ∈ S := (mem_normalizer_iff.mp (hBS hzB) s⁻¹).mp (inv_mem hs)
      have h2 := mul_mem hs this
      rwa [← mul_assoc, ← mul_assoc] at h2
    have h2 : s * z * s⁻¹ * z⁻¹ ∈ A :=
      mul_mem ((mem_normalizer_iff.mp (hSN hs) z).mp hzA) (inv_mem hzA)
    have h3 := eq_one_of_mem_of_mem hS h.elem.2 h1 h2
    calc s * z = s * z * s⁻¹ * z⁻¹ * (z * s) := by group
      _ = z * s := by rw [h3, one_mul]
  have hcomm := commute_of_transvection h.elem hA9 hzA hz1 (hRN (hBR hbB))
    (commute_of_isMulCommutative hB.1 hbB hzB) (hB.2 b hbB) hbnc hS hSN hSz (hBS hbB)
  have hE : Nat.card ((A.subgroupOf K).map ψ.toMonoidHom) = 9 := by
    rw [card_map_of_injective ψ.injective,
      Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv, hA9]
  have hW3 : ¬ 3 ∣ Nat.card (S.map ι) := by
    rw [card_map_of_injective hι]
    intro h3
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    rw [hk] at h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)) h3
  have hEW : ∀ x ∈ (A.subgroupOf K).map ψ.toMonoidHom,
      MulAut.conj x ∈ normalizer ((S.map ι : Subgroup (MulAut (projectiveSL 3 F))) :
        Set (MulAut (projectiveSL 3 F))) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← hιk a]
    refine le_normalizer_map ι ⟨(a : X), (?_ : (a : X) ∈ normalizer (S : Set X)), rfl⟩
    rw [mem_normalizer_iff]
    intro s
    have haA : (a : X) ∈ A := mem_subgroupOf.mp ha
    constructor
    · intro hs
      rw [← hcomm s hs _ haA, mul_inv_cancel_right]
      exact hs
    · intro hs
      have hc := hcomm _ hs _ haA
      have h1 : s = (a : X) * s * (a : X)⁻¹ := by
        calc s = (a : X)⁻¹ * ((a : X) * s * (a : X)⁻¹ * (a : X)) := by group
          _ = (a : X)⁻¹ * ((a : X) * ((a : X) * s * (a : X)⁻¹)) := by rw [hc]
          _ = (a : X) * s * (a : X)⁻¹ := by group
      rw [h1]
      exact hs
  rcases CFSG.RankThree.PartTwo.KFacts.L34.eq_bot_or_eq_zpowers_graphField hF hE hW3 hEW with
    h0 | ⟨τ, hτ, hτ1, hτ2, -, -⟩
  · rw [(map_eq_bot_iff_of_injective S hι).mp h0, card_bot]
    norm_num
  · have hτo : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
    have h2 : Nat.card (S.map ι) = 2 := by rw [hτ, Nat.card_zpowers, hτo]
    rw [card_map_of_injective hι] at h2
    exact h2.le

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K278
