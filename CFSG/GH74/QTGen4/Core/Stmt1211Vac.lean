module

public import CFSG.GH74.QTGen4.Stmt1317
public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Background.BlueprintB2Defs

public section

namespace CFSG.GH74.QTGen4

open CFSG.Quasithin CFSG.Open CFSG.GH74 CFSG.Quasithin.H13 CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative

theorem stmt12_1_11_gen4 :
    ∀ (G : Type) [Group G] [Finite G], Gen4 G →
      ∀ (T L : Subgroup G), IsSimpleGroup G →
      (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
      quasithinIsSylowTwo T → quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
      ∀ n : ℕ, (n = 4 ∨ n = 5) →
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) →
      ∀ V V₁ V₂ : Subgroup G, V ≤ Subgroup.normalizer (L : Set G) →
        IsPrimeReduced 2 (V.subgroupOf (Subgroup.normalizer (L : Set G))) →
        Nonempty (↥(autOn (Subgroup.normalizer (L : Set G)) V) ≃*
          MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) →
        V₁ ⊓ V₂ = ⊥ → V₁ ⊔ V₂ = V →
        L ≤ Subgroup.normalizer (V₁ : Set G) → L ≤ Subgroup.normalizer (V₂ : Set G) →
        (∃ _ : IsMulCommutative ↥V₁, BinaryNaturalSL (V := ↥V₁) (autOn L V₁) ⊤ ⊥ n 1) →
        (∃ _ : IsMulCommutative ↥V₂, BinaryNaturalSL (V := ↥V₂) (autOn L V₂) ⊤ ⊥ n 1) →
        ¬ IsXSectionIso₂ L V₁ ⊥ V₂ ⊥ → False := by
  intro G _ _ hG T L hs hnab hQ hT hmax hf n hn e V V₁ V₂ hVN hred hiso h12 hsup hL1 hL2 hnat1 hnat2
    hnx
  obtain ⟨_, hb1⟩ := hnat1
  obtain ⟨_, hb2⟩ := hnat2
  have c1 : Nat.card ↥V₁ = 2 ^ n := G64.BinaryNaturalSL.card_eq hb1
  have c2 : Nat.card ↥V₂ = 2 ^ n := G64.BinaryNaturalSL.card_eq hb2
  obtain ⟨_, hE, _⟩ := hred
  have helem : IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have := hE.toIsMulCommutative.is_comm.comm
        (⟨⟨a, hVN a.2⟩, a.2⟩ : ↥(V.subgroupOf (Subgroup.normalizer (L : Set G))))
        ⟨⟨b, hVN b.2⟩, b.2⟩
      exact congrArg (fun z : ↥(V.subgroupOf (Subgroup.normalizer (L : Set G))) =>
        (⟨(z : ↥(Subgroup.normalizer (L : Set G))).1, z.2⟩ : ↥V)) this
    · have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := V.subgroupOf (Subgroup.normalizer (L : Set G)))
        (⟨x, hVN hx⟩ : ↥(Subgroup.normalizer (L : Set G))) (Subgroup.mem_subgroupOf.mpr hx)
      simpa using congrArg (fun z : ↥(Subgroup.normalizer (L : Set G)) => (z : G)) h2
  have h1V : V₁ ≤ V := hsup ▸ le_sup_left
  have h2V : V₂ ≤ V := hsup ▸ le_sup_right
  let f : ↥V₁ × ↥V₂ → ↥V := fun q => ⟨(q.1 : G) * q.2, V.mul_mem (h1V q.1.2) (h2V q.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : G) * b = a' * b' := congrArg (fun z : ↥V => (z : G)) h
    have hrel : (a'⁻¹ * a : G) = b' * b⁻¹ := by
      have := congrArg (fun z => (a' : G)⁻¹ * z * (b : G)⁻¹) h'
      simpa [mul_assoc] using this
    have hmem : (a'⁻¹ * a : G) ∈ V₁ ⊓ V₂ := by
      refine ⟨V₁.mul_mem (V₁.inv_mem a'.2) a.2, ?_⟩
      rw [hrel]
      exact V₂.mul_mem b'.2 (V₂.inv_mem b.2)
    rw [h12, Subgroup.mem_bot] at hmem
    have hab : (a : G) = a' := (inv_mul_eq_one.mp hmem).symm
    have hbb : (b : G) = b' := by
      have := h'
      rw [hab] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext hab) (Subtype.ext hbb)
  have hcard : 2 ^ n * 2 ^ n ≤ Nat.card ↥V := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, c1, c2] at this
  have hS : SectionalTwoRankLE G 4 := hG
  have hle := hS.card_le_of_elementary V helem
  rcases hn with rfl | rfl <;> norm_num at hcard hle <;> omega

theorem stmt13_1_7_gen4 :
    ∀ (G : Type) [Group G] [Finite G], Gen4 G →
      ∀ (T : Subgroup G), IsSimpleGroup G →
      (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
      quasithinIsSylowTwo T → ¬ QT13Excluded G →
      ∀ K : Subgroup G, quasithinIsFaithfulLocal T K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
  fun G _ _ hc T _ _ hqtke hT _ K hK => by
    obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
    have hKc : K ∈ cComp (K ⊔ (S : Subgroup G)) := mem_cComp_iff.2 hK.1.2.1
    have hInH : CFSG.Quasithin.InH (S : Subgroup G) (K ⊔ (S : Subgroup G)) :=
      ⟨le_sup_right, hK.1.2.2.2⟩
    have hd := modO2_dvd_of_inH hc hqtke.2.1 S hInH (le_sup_left : K ≤ K ⊔ (S : Subgroup G))
    exact isQuasisimple_quot_of_cComp hKc hd

end CFSG.GH74.QTGen4
