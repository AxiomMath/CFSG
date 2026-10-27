module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactGL
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotLeviFactSwap

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll blockSpecialLinear centralizerPerfectCore_eq_map_of_le)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Swap

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F]
  {n : ℕ} (e : L ≃* StatedSp n K) (ι : K →+* F)

@[expose] def TorusEquivariantProd (N : Finset (Fin n)) (P : Subgroup (Fin n → Kˣ))
    (Ψ : spBlock F N × spBlock F N →* G) : Prop :=
  ∀ t ∈ P, ∀ x : spBlock F N × spBlock F N,
    Ψ (conjDiagSp N (liftParam ι t) x.1, conjDiagSp N (liftParam ι t) x.2) =
      ((e.symm (diagSp K n t) : L) : G) * Ψ x * ((e.symm (diagSp K n t) : L) : G)⁻¹

theorem TorusEquivariantProd.mono {N : Finset (Fin n)} {P Q : Subgroup (Fin n → Kˣ)}
    (hQP : Q ≤ P) {Ψ : spBlock F N × spBlock F N →* G} (hΨ : TorusEquivariantProd e ι N P Ψ) :
    TorusEquivariantProd e ι N Q Ψ :=
  fun t ht x => hΨ t (hQP ht) x

variable [Finite G] [Finite F]

theorem torusCore_eq_map_of_conjDiagSp_prod {P : Subgroup (Fin n → Kˣ)} {N : Finset (Fin n)}
    {H : Subgroup (StatedSp n F)} (hHN : H ≤ spBlock F N)
    (hLevi : perfectCore (spBlock F N ⊓
      centralizer (diagSp F n '' (liftParam ι '' (P : Set (Fin n → Kˣ))))) = H)
    {X : Subgroup G} (hXP : X ≤ modelToG e (diagTorusSp K P))
    (Ψ : spBlock F N × spBlock F N →* G) (hker : Ψ.ker ≤ center (spBlock F N × spBlock F N))
    (hrange : Ψ.range = centralizerPerfectCore X) (hΨ : TorusEquivariantProd e ι N P Ψ) :
    torusCore e P = ((H.subgroupOf (spBlock F N)).prod (H.subgroupOf (spBlock F N))).map Ψ := by
  set T := modelToG e (diagTorusSp K P)
  let τ : T → Fin n → Kˣ := fun d => (exists_param_of_mem_modelToG_diagTorusSp e d.2).choose
  have hτ : ∀ d : T, τ d ∈ P ∧ ((e.symm (diagSp K n (τ d)) : L) : G) = d :=
    fun d => (exists_param_of_mem_modelToG_diagTorusSp e d.2).choose_spec
  set β : T → MulAut (spBlock F N) := fun d => conjDiagSp N (liftParam ι (τ d)) with hβ
  have hα : ∀ (d : T) (x : spBlock F N × spBlock F N),
      Ψ (((β d).prodCongr (β d)) x) = (d : G) * Ψ x * (d : G)⁻¹ := by
    intro d x
    rw [UnitaryPilot.prodCongr_apply_eq, hβ]
    rw [hΨ _ (hτ d).1 x, (hτ d).2]
  have hfix : perfectCore (fixAll β) = H.subgroupOf (spBlock F N) := by
    apply Subgroup.map_injective (spBlock F N).subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, hβ, map_fixAll_conjDiagSp_eq e ι τ hτ, hLevi,
      subgroupOf_map_subtype, inf_of_le_left hHN]
  rw [torusCore, centralizerPerfectCore_eq_map_of_le Ψ hker hXP hrange
    (fun d => (β d).prodCongr (β d)) hα, UnitaryPilot.fixAll_prodCongr,
    UnitaryPilot.perfectCore_prod, hfix]

theorem planeCore_eq_map_of_conjDiagSp_prod (hK : 4 ≤ Nat.card K) {N I : Finset (Fin n)}
    (hIN : I ⊆ N) {X : Subgroup G} (hXI : X ≤ modelToG e (planeTorusSp K I))
    (Ψ : spBlock F N × spBlock F N →* G) (hker : Ψ.ker ≤ center (spBlock F N × spBlock F N))
    (hrange : Ψ.range = centralizerPerfectCore X)
    (hΨ : TorusEquivariantProd e ι N (planeTorusParam K I) Ψ) :
    planeCore e I = (((spBlock F I).subgroupOf (spBlock F N)).prod
      ((spBlock F I).subgroupOf (spBlock F N))).map Ψ := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  exact torusCore_eq_map_of_conjDiagSp_prod e ι (spBlock_mono hIN)
    (perfectCore_spBlock_inf_centralizer_planeTorus ι hκ hIN
      (commutator_spBlock_eq (le_card_of_ringHom ι hK) I)) hXI Ψ hker hrange hΨ

theorem stringCore_eq_map_of_conjDiagSp_prod (hK : 4 ≤ Nat.card K) {N B : Finset (Fin n)}
    (hBN : B ⊆ N) (hB : 2 ≤ B.card) {X : Subgroup G} (hXB : X ≤ modelToG e (stringTorusSp K B))
    (Ψ : spBlock F N × spBlock F N →* G) (hker : Ψ.ker ≤ center (spBlock F N × spBlock F N))
    (hrange : Ψ.range = centralizerPerfectCore X)
    (hΨ : TorusEquivariantProd e ι N (stringTorusParam K B) Ψ) :
    stringCore e B = (((siegelBlock F B).subgroupOf (spBlock F N)).prod
      ((siegelBlock F B).subgroupOf (spBlock F N))).map Ψ := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  exact torusCore_eq_map_of_conjDiagSp_prod e ι
    ((siegelBlock_le_spBlock B).trans (spBlock_mono hBN))
    (perfectCore_spBlock_inf_centralizer_stringTorus ι hκ hBN
      (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le hB (le_card_of_ringHom ι hK)))
    hXB Ψ hker hrange hΨ

theorem planeCore_eq_map_of_neighbourCore_prod (hK : 4 ≤ Nat.card K) {k : Fin n}
    {I : Finset (Fin n)} (hk : k ∉ I)
    (Ψ : spBlock F ({k}ᶜ : Finset (Fin n)) × spBlock F ({k}ᶜ : Finset (Fin n)) →* G)
    (hker : Ψ.ker ≤ center (spBlock F ({k}ᶜ : Finset (Fin n)) ×
      spBlock F ({k}ᶜ : Finset (Fin n))))
    (hrange : Ψ.range = neighbourCore e k)
    (hΨ : TorusEquivariantProd e ι {k}ᶜ (planeTorusParam K I) Ψ) :
    planeCore e I = (((spBlock F I).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n)))).prod
      ((spBlock F I).subgroupOf (spBlock F ({k}ᶜ : Finset (Fin n))))).map Ψ :=
  planeCore_eq_map_of_conjDiagSp_prod e ι hK (subset_compl_singleton_of_notMem hk)
    (modelToG_rootTorusSp_le_planeTorusSp e hk) Ψ hker hrange hΨ

theorem pieceCore_string_eq_map_of_neighbourCore_prod (hK : 4 ≤ Nat.card K) {a b : ℕ}
    (hab : a < b) (hb : b < n) {k : Fin n}
    (hk : k ∉ Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)
    (Ψ : spBlock F ({k}ᶜ : Finset (Fin n)) × spBlock F ({k}ᶜ : Finset (Fin n)) →* G)
    (hker : Ψ.ker ≤ center (spBlock F ({k}ᶜ : Finset (Fin n)) ×
      spBlock F ({k}ᶜ : Finset (Fin n))))
    (hrange : Ψ.range = neighbourCore e k)
    (hΨ : TorusEquivariantProd e ι {k}ᶜ
      (stringTorusParam K (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)) Ψ) :
    pieceCore e (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val < b) =
      (((siegelBlock F (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)).subgroupOf
          (spBlock F ({k}ᶜ : Finset (Fin n)))).prod
        ((siegelBlock F (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b)).subgroupOf
          (spBlock F ({k}ᶜ : Finset (Fin n))))).map Ψ := by
  have hB : 2 ≤ (Finset.univ.filter fun j : Fin n => a ≤ j.val ∧ j.val ≤ b).card := by
    refine Finset.one_lt_card.2 ⟨⟨a, by omega⟩, by simp; omega, ⟨b, hb⟩, by simp; omega, ?_⟩
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [pieceCore_string_eq e hb]
  exact stringCore_eq_map_of_conjDiagSp_prod e ι hK (subset_compl_singleton_of_notMem hk) hB
    (modelToG_rootTorusSp_le_stringTorusSp e hk) Ψ hker hrange hΨ

end Swap

end CFSG.SeitzReduction.SymplecticPilot
