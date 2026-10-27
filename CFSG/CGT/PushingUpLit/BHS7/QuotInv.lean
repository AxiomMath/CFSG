module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.CGT.PushingUpLit.BHS.Prelim
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.LieType.BorelTits
  CFSG.CGT.PushingUpLit.BHS

section Generic

variable {Y : Type*} [Group Y]

theorem eq_empty_of_conj_closed [Finite Y] {K P E R : Subgroup Y} (hK2 : pCoreOf 2 K = ⊥)
    (hKPE : K ≤ P ⊔ E) {𝒮 : Set (Subgroup Y)} (hP : ∀ g ∈ P, ∀ B ∈ 𝒮, conjSub g B ∈ 𝒮)
    (hE : ∀ g ∈ E, ∀ B ∈ 𝒮, conjSub g B ∈ 𝒮)
    (hmem : ∀ B ∈ 𝒮, B ≤ K ∧ B ≤ R ∧ B ≠ ⊥) (hR2 : IsPGroup 2 ↥R) : 𝒮 = ∅ := by
  let Cl : Subgroup Y :=
    { carrier := {g | (∀ B ∈ 𝒮, conjSub g B ∈ 𝒮) ∧ ∀ B ∈ 𝒮, conjSub g⁻¹ B ∈ 𝒮}
      one_mem' := ⟨fun B hB => by rwa [conjSub_one], fun B hB => by rwa [inv_one, conjSub_one]⟩
      mul_mem' := by
        rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
        refine ⟨fun B hB => ?_, fun B hB => ?_⟩
        · rw [conjSub_mul]
          exact hg1 _ (hh1 B hB)
        · rw [mul_inv_rev, conjSub_mul]
          exact hh2 _ (hg2 B hB)
      inv_mem' := by
        rintro g ⟨hg1, hg2⟩
        exact ⟨fun B hB => by simpa using hg2 B hB, fun B hB => by simpa using hg1 B hB⟩ }
  have hPCl : P ≤ Cl := fun g hg => ⟨hP g hg, hP g⁻¹ (P.inv_mem hg)⟩
  have hECl : E ≤ Cl := fun g hg => ⟨hE g hg, hE g⁻¹ (E.inv_mem hg)⟩
  have hKCl : K ≤ Cl := hKPE.trans (sup_le hPCl hECl)
  set N : Subgroup Y := ⨆ B : ↥𝒮, (B : Subgroup Y) with hN
  have hNK : N ≤ K := iSup_le fun B => (hmem B B.2).1
  have hNR : N ≤ R := iSup_le fun B => (hmem B B.2).2.1
  have hkey : ∀ g ∈ K, conjSub g N ≤ N := by
    intro g hg
    rw [hN, conjSub_iSup]
    exact iSup_le fun B =>
      le_iSup (fun B : ↥𝒮 => (B : Subgroup Y)) ⟨conjSub g B, (hKCl hg).1 B B.2⟩
  have hKN : K ≤ Subgroup.normalizer (N : Set Y) := fun g hg =>
    BHS.mem_normalizer_of_conjSub_le (hkey g hg) (hkey g⁻¹ (K.inv_mem hg))
  have hN2 : IsPGroup 2 ↥N := hR2.to_le hNR
  have hNbot : N ≤ ⊥ := hK2 ▸ le_pCoreOf_of_le_normalizer 2 hNK hKN hN2
  refine Set.eq_empty_iff_forall_notMem.mpr fun B hB => (hmem B hB).2.2 ?_
  exact le_bot_iff.mp ((le_iSup (fun B : ↥𝒮 => (B : Subgroup Y)) ⟨B, hB⟩).trans hNbot)

theorem conjSub_eq_of_commute {g : Y} {B : Subgroup Y} (h : ∀ b ∈ B, g * b = b * g) :
    conjSub g B = B := by
  ext x
  rw [mem_conjSub_iff]
  have key : ∀ b ∈ B, g⁻¹ * b * g = b := fun b hb => by
    have := h b hb
    calc g⁻¹ * b * g = g⁻¹ * (b * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * b) := by rw [this]
      _ = b := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  constructor
  · intro hx
    have h1 := h _ hx
    have e : x = g⁻¹ * x * g := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = (g⁻¹ * x * g) * g * g⁻¹ := by rw [h1]
        _ = g⁻¹ * x * g := by group
    exact e ▸ hx
  · intro hx
    rwa [key x hx]

end Generic

section Residual

variable {Γ : Type*} [Group Γ]

theorem opResidual_le_of_le_sup {G N T : Subgroup Γ} (hT2 : IsPGroup 2 ↥T)
    (hTn : T ≤ Subgroup.normalizer (N : Set Γ)) (hG : G ≤ T ⊔ N) : opResidual 2 G ≤ N := by
  refine opResidual_le_of_pow_mem fun x hx => ?_
  have hx' : x ∈ ((T ⊔ N : Subgroup Γ) : Set Γ) := hG hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T N hTn] at hx'
  obtain ⟨t, ht, n, hn, hxe⟩ := hx'
  have hxe' : t * n = x := hxe
  subst hxe'
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨y', hy', h⟩ := pow_mul_mem_of_mem_normalizer (hTn ht) hn (2 ^ k)
  exact ⟨k, by rw [h, hk', one_mul]; exact hy'⟩

end Residual

end CFSG.CGT.PushingUpLit.BHS7
