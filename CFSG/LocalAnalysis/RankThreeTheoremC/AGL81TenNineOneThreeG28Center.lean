module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCG28
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalSylow
public import Certificates.Certificate5174
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeG28Rank
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcCensus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup CFSG.AGLEmbedding.KFactProofs.G28 CFSG.RankThree.PartTwo.Sec4.Item434G28
open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti CFSG.Open
open CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

section Center


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem commCode_of_comm {g h : adjointGroup .G2 K} {A B : Array ℕ} (hA : Valid A) (hB : Valid B)
    (hg : M.rho g = decode A) (hh : M.rho h = decode B) (hc : g * h = h * g) :
    commCode A B = true := by
  have := (M.eq_iff_codes (valid_mulCode hA hB) (valid_mulCode hB hA)
    (M.rho_mul_code hA hB hg hh) (M.rho_mul_code hB hA hh hg)).1 hc
  simp [commCode, this]

theorem center_TX {a : adjointGroup .G2 K} (ha : a ∈ TX M)
    (hc : ∀ t ∈ TX M, t * a = a * t) : a = 1 ∨ a = zE M ∨ a = zE M * zE M := by
  obtain ⟨n, hn, hrho⟩ := ha
  have hv := valid_txL hn
  have h1 := commCode_of_comm M hv valid_tU hrho (rho_tuE M) (hc _ (tuE_mem_TX M)).symm
  have h2 := commCode_of_comm M hv valid_tZ hrho (rho_tzE M) (hc _ (tzE_mem_TX M)).symm
  have h3 := commCode_of_comm M hv valid_tO hrho (rho_toE M) (hc _ (toE_mem_TX M)).symm
  have h := List.all_eq_true.1 Certificates.certificate5174 n (List.mem_range.2 hn)
  simp only [h1, h2, h3, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h with (h | h) | h
  · exact Or.inl ((M.eq_one_iff_code hv hrho).2 h)
  · exact Or.inr (Or.inl ((M.eq_iff_codes hv valid_tzc hrho (rho_zE M)).2 h))
  · exact Or.inr (Or.inr ((M.eq_iff_codes hv (valid_mulCode valid_tzc valid_tzc) hrho
      (M.rho_mul_code valid_tzc valid_tzc (rho_zE M) (rho_zE M))).2 h))

theorem mem_zpowers_of_center_cases {G : Type*} [Group G] {z a b : G} (hz : z ^ 3 = 1)
    (ha : a = 1 ∨ a = z ∨ a = z * z) (hb : b = 1 ∨ b = z ∨ b = z * z) (ha1 : a ≠ 1) :
    b ∈ zpowers a := by
  have h3 : z * z * z = 1 := by rw [← hz, pow_succ, pow_two]
  have hzz : (z * z) * (z * z) = z := by
    calc (z * z) * (z * z) = (z * z * z) * z := by simp only [mul_assoc]
      _ = z := by rw [h3, one_mul]
  rcases ha with rfl | rfl | rfl
  · exact absurd rfl ha1
  · rcases hb with rfl | rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
    · exact mul_mem (mem_zpowers _) (mem_zpowers _)
  · rcases hb with rfl | rfl | rfl
    · exact one_mem _
    · exact mem_zpowers_iff.mpr ⟨2, by rw [zpow_two]; exact hzz⟩
    · exact mem_zpowers _

end Center

theorem kFactG28SylowCenter_holds :
    KFactG28SylowCenter := by
  intro Y _ _ hY T a b haT hbT ha3 hb3 hca hcb
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := hY
  have hY8 : Nat.card Y = ordG2 8 := G28Rank.card_of_isGTwoEightIndex d hd e
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, hqp, hqe, hd1⟩ := hd
  subst hd1
  obtain ⟨F, _, _, _, hF⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Census.exists_field_card 2
    3 Nat.prime_two (by norm_num)
  obtain ⟨bb⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv F
    (by rw [hF, PrimePower.card_def, hqp, hqe])
  have hZX : Subgroup.center (adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  set e' : Y ≃* adjointGroup .G2 F := e.trans (bb.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot))
  obtain ⟨M⟩ := exists_model (K := F) (by rw [hF]; norm_num)
  have hX : Nat.card (adjointGroup .G2 F) = ordG2 8 := by
    rw [← Nat.card_congr e'.toEquiv, hY8]
  have hTX : Nat.card (TX M) = 3 ^ (Nat.card (adjointGroup .G2 F)).factorization 3 := by
    rw [card_TX, hX, factorization_ordG2_eight]
    norm_num
  set T' : Subgroup (adjointGroup .G2 F) := (T : Subgroup Y).map e'.toMonoidHom
  have hT'p : IsPGroup 3 T' := T.isPGroup'.map e'.toMonoidHom
  obtain ⟨g, hg⟩ := exists_conj_le_of_card hTX hT'p
  have hcardT' : Nat.card T' = 243 := by
    rw [Subgroup.card_map_of_injective e'.injective, T.card_eq_multiplicity, hY8,
      factorization_ordG2_eight]
    norm_num
  have hle : T'.map (MulAut.conj g⁻¹).toMonoidHom ≤ TX M := by
    rintro _ ⟨t, ht, rfl⟩
    simpa using hg t ht
  have heq : T'.map (MulAut.conj g⁻¹).toMonoidHom = TX M :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_TX, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcardT'])
  have hcen : ∀ x : Y, x ∈ (T : Subgroup Y) → (∀ t ∈ (T : Subgroup Y), t * x * t⁻¹ = x) →
      g⁻¹ * e' x * g ∈ TX M ∧ ∀ t ∈ TX M, t * (g⁻¹ * e' x * g) = (g⁻¹ * e' x * g) * t := by
    intro x hx hcx
    refine ⟨hg _ ⟨x, hx, rfl⟩, fun t ht => ?_⟩
    rw [← heq] at ht
    obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := ht
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h := congrArg e' (hcx s hs)
    rw [map_mul, map_mul, map_inv] at h
    have h' : e' s * e' x = e' x * e' s := by
      calc e' s * e' x = (e' s * e' x * (e' s)⁻¹) * e' s := by group
        _ = e' x * e' s := by rw [h]
    calc g⁻¹ * e' s * g⁻¹⁻¹ * (g⁻¹ * e' x * g) = g⁻¹ * (e' s * e' x) * g := by group
      _ = g⁻¹ * (e' x * e' s) * g := by rw [h']
      _ = g⁻¹ * e' x * g * (g⁻¹ * e' s * g⁻¹⁻¹) := by group
  obtain ⟨haX, haC⟩ := hcen a haT hca
  obtain ⟨hbX, hbC⟩ := hcen b hbT hcb
  have hca' := center_TX M haX haC
  have hcb' := center_TX M hbX hbC
  have ha1 : g⁻¹ * e' a * g ≠ 1 := by
    intro h
    have : a = 1 := e'.injective (by
      rw [map_one]
      calc e' a = g * (g⁻¹ * e' a * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group)
    rw [this, orderOf_one] at ha3
    omega
  have hmem := mem_zpowers_of_center_cases (zE_pow_three M) hca' hcb' ha1
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  refine mem_zpowers_iff.mpr ⟨k, e'.injective ?_⟩
  rw [map_zpow]
  have hk' : g⁻¹ * e' a ^ k * g = g⁻¹ * e' b * g := by
    rw [← hk]
    have h := conj_zpow (a := g⁻¹) (b := e' a) (i := k)
    rw [inv_inv] at h
    exact h.symm
  have := congrArg (fun w => g * w * g⁻¹) hk'
  simpa [mul_assoc] using this

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
