module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X]

private theorem isComplement'_of_isCompl_of_isMulCommutative
    {G : Type*} [Group G] [IsMulCommutative G] {B C : Subgroup G}
    (h : IsCompl B C) : Subgroup.IsComplement' B C := by
  change Function.Bijective fun x : B × C => (x.1 : G) * (x.2 : G)
  refine ⟨?_, ?_⟩
  · rintro ⟨b₁, c₁⟩ ⟨b₂, c₂⟩ hxy
    change (b₁ : G) * (c₁ : G) = (b₂ : G) * (c₂ : G) at hxy
    have hkey : (b₁ : G)⁻¹ * b₂ = (c₁ : G) * (c₂ : G)⁻¹ := by
      apply mul_left_cancel (a := (b₁ : G))
      calc
        (b₁ : G) * ((b₁ : G)⁻¹ * b₂) = b₂ := by group
        _ = ((b₂ : G) * c₂) * (c₂ : G)⁻¹ := by group
        _ = ((b₁ : G) * c₁) * (c₂ : G)⁻¹ := by rw [hxy]
        _ = (b₁ : G) * ((c₁ : G) * (c₂ : G)⁻¹) := by group
    have hB : (b₁ : G)⁻¹ * b₂ ∈ B := B.mul_mem (B.inv_mem b₁.2) b₂.2
    have hC : (b₁ : G)⁻¹ * b₂ ∈ C := by
      rw [hkey]
      exact C.mul_mem c₁.2 (C.inv_mem c₂.2)
    have h1 : (b₁ : G)⁻¹ * b₂ = 1 := by
      have hmem : (b₁ : G)⁻¹ * b₂ ∈ B ⊓ C := by
        rw [Subgroup.mem_inf]
        exact ⟨hB, hC⟩
      rw [h.inf_eq_bot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hb : b₁ = b₂ := by
      apply Subtype.ext
      exact inv_mul_eq_one.mp h1
    have hc : c₁ = c₂ := by
      apply Subtype.ext
      have : (b₁ : G) * (c₁ : G) = (b₁ : G) * (c₂ : G) := by
        rw [hxy, hb]
      exact mul_left_cancel this
    exact Prod.ext hb hc
  · intro g
    have hg : g ∈ B ⊔ C := by
      rw [h.sup_eq_top]
      trivial
    rw [Subgroup.mem_sup_of_normal_right] at hg
    obtain ⟨b, hb, c, hc, hbc⟩ := hg
    exact ⟨(⟨b, hb⟩, ⟨c, hc⟩), hbc⟩

theorem exists_complement_of_isElemAbelian {E F : Subgroup X} (hE : IsElemAbelian 2 E)
    (hF : F ≤ E) :
    ∃ D : Subgroup X, D ≤ E ∧ D ⊓ F = ⊥ ∧ Nat.card D * Nat.card F = Nat.card E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hEA : IsElementaryAbelian 2 E :=
    { is_comm := hE.1.is_comm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hE.2 x x.2) }
  obtain ⟨C, hcompl⟩ := IsElementaryAbelian.exists_isCompl 2 E (F.subgroupOf E)
  have hcompl' : Subgroup.IsComplement' (F.subgroupOf E) C :=
    isComplement'_of_isCompl_of_isMulCommutative hcompl
  refine ⟨C.map E.subtype, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact c.2
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxD, hxF⟩ := hx
    obtain ⟨c, hcC, hcx⟩ := Subgroup.mem_map.mp hxD
    have hcF : c ∈ F.subgroupOf E := by
      rw [Subgroup.mem_subgroupOf]
      have hcx' : (c : X) = x := by simpa only [Subgroup.subtype_apply] using hcx
      rw [hcx']
      exact hxF
    have hcbot : c ∈ (⊥ : Subgroup E) := by
      rw [← hcompl.inf_eq_bot, Subgroup.mem_inf]
      exact ⟨hcF, hcC⟩
    have hc1 : c = 1 := Subgroup.mem_bot.mp hcbot
    rw [Subgroup.mem_bot]
    calc
      x = E.subtype c := hcx.symm
      _ = 1 := by rw [hc1]; rfl
  · have hcardD : Nat.card (C.map E.subtype) = Nat.card C :=
      Subgroup.card_map_of_injective (K := C) (f := E.subtype) E.subtype_injective
    have hcardB : Nat.card (F.subgroupOf E) = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv
    rw [hcardD, ← hcardB, mul_comm]
    exact hcompl'.card_mul_card

end CFSG.EvenSporadicStandard.HNRecog.Harada
