module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Layers
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderHoff
public import CFSG.HardMathSupport.RichardWeiss.Proving.OffenderLayers

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open
  CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender (IsExp2 orbitStab)
open CFSG.HardMathSupport.RichardWeiss.Proving CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_mem_commutator {V L : Subgroup G} {g : G}
    (hgV : ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hgL : ∀ l ∈ L, g * l * g⁻¹ ∈ L) :
    ∀ u ∈ ⁅V, L⁆, g * u * g⁻¹ ∈ ⁅V, L⁆ := by
  have hle : ⁅V, L⁆ ≤ ⁅V, L⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj g).toMonoidHom ⁅x, y⁆ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator (hgV x hx) (hgL y hy)
  intro u hu
  exact hle hu

theorem isMax_le_layerTriv [Finite G] {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    {d : ℕ} (hd : d = 7 ∨ 9 ≤ d)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π) (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hπker : π.ker = (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf
      ⁅blockV S L, L⁆)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hnf : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      ¬ ((¬ ∃ p, ∀ g ∈ (A.subgroupOf (L ⊔ S)).map θ, g p = p) ∧
        (∀ i : Fin d, Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) i) = 2) ∧
        Nat.card (orbitStab ((A.subgroupOf (L ⊔ S)).map θ)) =
          Nat.card ((A.subgroupOf (L ⊔ S)).map θ))) :
    ∀ A : Subgroup G, IsMaxElemAbelian S A →
      A ≤ layerTriv (blockV S L) ⁅blockV S L, L⁆
        (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)) := by
  intro A hAmax
  have hSM : S ≤ L ⊔ S := le_sup_right
  have hLM : L ≤ L ⊔ S := le_sup_left
  have hVel : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have hVn : ∀ m ∈ L ⊔ S, ∀ v ∈ blockV S L, m * v * m⁻¹ ∈ blockV S L := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.1 (hMV hm) v).1 hv
  have hVS : blockV S L ≤ S :=
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _).trans hA.twoCore_le
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have := hVn l (hLM hl) v⁻¹ ((blockV S L).inv_mem hv)
    simpa [mul_assoc] using (blockV S L).mul_mem hv this
  have hAM : A ≤ L ⊔ S := hAmax.1.trans hSM
  have hAS : A ≤ S := hAmax.1
  have hoffA := hoff_of_not_full hA hd π θ hπ hequiv hθV hnf A hAmax
  have h3 := relIndex_le_of_isMaxElemAbelian hAmax hVel hVS
  have h4 := relIndex_le_card_image hAM θ hθV
  have heq : (Subgroup.centralizer (A : Set G)).relIndex (blockV S L) ≤
      (altFix d ((A.subgroupOf (L ⊔ S)).map θ)).index := by
    rw [index_altFix] at hoffA ⊢
    exact h3.trans (h4.trans hoffA)
  have hVab : ∀ a ∈ blockV S L, ∀ b ∈ blockV S L, a * b = b * a := fun a ha b hb =>
    isElemAbelian_comm' hVel ha hb
  have hAU : ∀ a ∈ A, ∀ u ∈ ⁅blockV S L, L⁆, a * u * a⁻¹ ∈ ⁅blockV S L, L⁆ := fun a ha u hu =>
    conj_mem_commutator (V := blockV S L) (L := L) (g := a)
      (fun v hv => hVn a (hAM ha) v hv)
      (fun l hl => by
        have := (Subgroup.mem_normalizer_iff.1 (hSL (hAS ha)) l).1 hl
        exact this) u hu
  obtain ⟨hK, hL⟩ := outer_layers_trivial_of_relIndex_le (A := A) (M := L ⊔ S)
    hUV inf_le_left hVab hAM (fun a ha v hv => hVn a (hAM ha) v hv) hAU hπ hπker hequiv heq
  refine fun a ha => ⟨hMV (hAM ha), ?_, hK a ha, hL a ha⟩
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact hAU a ha u
  · intro h
    have := hAU a⁻¹ (inv_mem ha) _ h
    simpa [mul_assoc] using this

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
