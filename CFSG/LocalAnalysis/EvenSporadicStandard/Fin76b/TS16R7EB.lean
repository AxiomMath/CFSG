module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Beta

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem card_of_mulEquiv_alternatingGroup {G : Type} [Group G] {B : Subgroup G}
    (e : ↥B ≃* alternatingGroup (Fin 5)) : Nat.card ↥B = 60 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem eq_one_of_mem_E_of_mem_B {G : Type} [Group G] {E B : Subgroup G}
    (eB : ↥B ≃* alternatingGroup (Fin 5)) (hcardE : Nat.card ↥E = 32)
    (hnorm : ∀ b ∈ B, ∀ e ∈ E, b * e * b⁻¹ ∈ E) {x : G} (hxE : x ∈ E) (hxB : x ∈ B) :
    x = 1 := by
  have hsimple : IsSimpleGroup ↥B := eB.isSimpleGroup
  have hN : ((E ⊓ B).subgroupOf B).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨hnorm (g : G) g.2 (n : G) hn.1, B.mul_mem (B.mul_mem g.2 hn.2) (B.inv_mem g.2)⟩⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top ((E ⊓ B).subgroupOf B) with h | h
  · have hmem : (⟨x, hxB⟩ : ↥B) ∈ (E ⊓ B).subgroupOf B := Subgroup.mem_subgroupOf.2 ⟨hxE, hxB⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    have hBE : B ≤ E := fun b hb => by
      have hmem : (⟨b, hb⟩ : ↥B) ∈ (E ⊓ B).subgroupOf B := by
        rw [h]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hmem).1
    have hdvd := Subgroup.card_dvd_of_le hBE
    rw [hcardE, card_of_mulEquiv_alternatingGroup eB] at hdvd
    exact absurd hdvd (by norm_num)

theorem EB_eq_sup {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E B : Subgroup G}
    {β : G} (hW : WFacts L t E) (hB : OuterB L t B β) (hEt : ∀ e ∈ E, e * t = t * e) :
    L ⊓ Subgroup.centralizer ({t} : Set G) = E ⊔ B := by
  obtain ⟨eB⟩ := hB.B_iso
  have hcardB : Nat.card ↥B = 60 := card_of_mulEquiv_alternatingGroup eB
  have hnorm : ∀ b ∈ B, ∀ e ∈ E, b * e * b⁻¹ ∈ E := fun b hb e he =>
    hW.normal b (hB.B_le hb) (mem_centralizer_singleton_iff.1 (hB.B_cent hb)) e he
  have hinf : ∀ x ∈ E, x ∈ B → x = 1 := fun x hxE hxB =>
    eq_one_of_mem_E_of_mem_B eB hW.card_E hnorm hxE hxB
  let f : ↥E × ↥B → ↥(E ⊔ B) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨e₁, b₁⟩ ⟨e₂, b₂⟩ hfe
    have hmul : (e₁ : G) * (b₁ : G) = (e₂ : G) * (b₂ : G) := congrArg Subtype.val hfe
    have hkey : (e₂ : G)⁻¹ * (e₁ : G) = (b₂ : G) * (b₁ : G)⁻¹ := by
      calc (e₂ : G)⁻¹ * (e₁ : G)
          = (e₂ : G)⁻¹ * ((e₁ : G) * (b₁ : G)) * (b₁ : G)⁻¹ := by group
        _ = (e₂ : G)⁻¹ * ((e₂ : G) * (b₂ : G)) * (b₁ : G)⁻¹ := by rw [hmul]
        _ = (b₂ : G) * (b₁ : G)⁻¹ := by group
    have hB' : (e₂ : G)⁻¹ * (e₁ : G) ∈ B := by
      rw [hkey]
      exact B.mul_mem b₂.2 (B.inv_mem b₁.2)
    have h1 : (e₂ : G)⁻¹ * (e₁ : G) = 1 :=
      hinf _ (E.mul_mem (E.inv_mem e₂.2) e₁.2) hB'
    have he : (e₂ : G) = (e₁ : G) := inv_mul_eq_one.1 h1
    have hmul' : (e₂ : G) * (b₁ : G) = (e₂ : G) * (b₂ : G) := by
      rw [← he] at hmul
      exact hmul
    have hb : (b₁ : G) = (b₂ : G) := mul_left_cancel hmul'
    exact Prod.ext (Subtype.ext he.symm) (Subtype.ext hb)
  have hcardEB : 1920 ≤ Nat.card ↥(E ⊔ B) := by
    have h := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, hW.card_E, hcardB] at h
    exact h
  have hsub : E ⊔ B ≤ L ⊓ Subgroup.centralizer ({t} : Set G) :=
    sup_le (fun e he => ⟨hW.E_le he, mem_centralizer_singleton_iff.2 (hEt e he)⟩)
      (fun b hb => ⟨hB.B_le hb, hB.B_cent hb⟩)
  exact (Subgroup.eq_of_le_of_card_ge hsub (by rw [hW.card_cent]; exact hcardEB)).symm

end CFSG.EvenSporadicStandard.Fin76b
