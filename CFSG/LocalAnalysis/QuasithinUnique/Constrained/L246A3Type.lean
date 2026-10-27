
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A3Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Kernel

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

namespace L246

variable {G : Type} [Group G] [Finite G]

theorem isAltType_three {L : Subgroup G} (hL : IsShort2 L)
    (h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) : IsAltType L 3 := by
  have hV : IsElemAbelian 2 (blockU L) := C5.isElemAbelian_two_iff.2 (C1.elemAb2_blockU hL)
  have T : TrData (blockU L) L hV := ⟨hL, C1.le_normalizer_blockU L, le_rfl⟩
  have hpc : ∀ l : ↥L, (l : G) ∈ Subgroup.centralizer (blockU L : Set G) ↔
      l ∈ CFSG.pCore 2 ↥L := by
    intro l
    rw [← mem_blockQ_iff]
    constructor
    · intro h
      exact C1.inf_centralizer_blockU_le hL ⟨l.2, h⟩
    · intro h
      exact Subgroup.mem_centralizer_iff.2 fun u hu => C1.blockU_comm hL u hu l h
  have hcardL : Nat.card ↥(autI hV L) = 3 := by
    have hker : (rho1 hV T.norm).ker = CFSG.pCore 2 ↥L := by
      ext l
      rw [mem_ker_rho1, hpc]
    have e := QuotientGroup.quotientKerEquivOfSurjective (rho1 hV T.norm)
      (rho1_surjective hV T.norm)
    rw [← Nat.card_congr e.toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv]
    exact h3
  have hV2 : ∀ v : IntMod (blockU L) hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hS : ∀ s : Sec (intSub hV (blockU L)) (intSub hV (blockZ L)), s ^ 2 = 1 :=
    Bridge.sec_sq_eq_one hV2 _ _
  have hinj : Function.Injective (Bridge.secRestrict (autI_le_stab hV L)) := by
    have : Fact (Nat.card ↥(autI hV L)).Prime := ⟨by rw [hcardL]; exact Nat.prime_three⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Bridge.secRestrict (autI_le_stab hV L)).ker with
      h | h
    · exact (MonoidHom.ker_eq_bot_iff _).1 h
    · exfalso
      have hall : ∀ ℓ : ↥L, T.rhoSec ℓ = 1 := fun ℓ => by
        have hmem : rho1 hV T.norm ℓ ∈ (Bridge.secRestrict (autI_le_stab hV L)).ker := by rw [h]; trivial
        exact hmem
      have hcomm : ⁅blockU L, L⁆ ≤ blockZ L := by
        rw [Subgroup.commutator_le]
        intro u hu l hl
        have hmem : l * u * l⁻¹ ∈ blockU L :=
          (Subgroup.mem_normalizer_iff.1 (C1.le_normalizer_blockU L hl) u).1 hu
        have h1 := T.rhoSec_smul ⟨l, hl⟩ ⟨u, hu⟩ ⟨l * u * l⁻¹, hmem⟩ rfl
        rw [hall] at h1
        have h2 : T.qHom (⟨l * u * l⁻¹, hmem⟩ * (⟨u, hu⟩ : ↥(blockU L))⁻¹) = 1 := by
          rw [map_mul, map_inv, ← h1]
          exact mul_inv_cancel _
        have h4 := (T.qHom_eq_one_iff _).1 h2
        have h5 : ⁅u, l⁆ = (l * u * l⁻¹ * u⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [h5]
        exact (blockZ L).inv_mem h4
      rw [C1.commutator_blockU hL] at hcomm
      exact absurd hL.2.2.2.2.1 (not_lt_of_ge hcomm)
  have hcardΓ : Nat.card ↥(autSec (autI hV L) (intSub hV (blockU L)) (intSub hV (blockZ L))) = 3 := by
    rw [← hcardL]
    exact (Nat.card_congr (Equiv.ofBijective _
      ⟨hinj, Bridge.secRestrict_surjective (autI_le_stab hV L)⟩)).symm
  have hnt : Nontrivial (Sec (intSub hV (blockU L)) (intSub hV (blockZ L))) := by
    obtain ⟨u, huU, huZ⟩ := IsConcreteLE.exists_of_lt hL.2.2.2.2.1
    exact ⟨⟨T.qHom ⟨u, huU⟩, 1, fun h => huZ ((T.qHom_eq_one_iff _).1 h)⟩⟩
  have hirr : ∀ J : Subgroup (Sec (intSub hV (blockU L)) (intSub hV (blockZ L))),
      (∀ γ ∈ autSec (autI hV L) (intSub hV (blockU L)) (intSub hV (blockZ L)),
        ∀ x ∈ J, γ x ∈ J) → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    let W : Subgroup G := (J.comap T.qHom).map (blockU L).subtype
    have hmemW : ∀ g : G, g ∈ W ↔ ∃ u : ↥(blockU L), T.qHom u ∈ J ∧ (u : G) = g := by
      intro g
      simp [W, Subgroup.mem_map, Subgroup.mem_comap]
    have hZW : blockZ L ≤ W := by
      intro z hz
      refine (hmemW z).2 ⟨⟨z, (inf_le_left : blockZ L ≤ blockU L) hz⟩, ?_, rfl⟩
      rw [(T.qHom_eq_one_iff _).2 hz]
      exact J.one_mem
    have hWU : W ≤ blockU L := by
      intro g hg
      obtain ⟨u, -, rfl⟩ := (hmemW g).1 hg
      exact u.2
    have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
      refine le_normalizer_of_forall_conj fun l hl w hw => ?_
      obtain ⟨u, huJ, rfl⟩ := (hmemW w).1 hw
      have hmem : l * u * l⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.1 (C1.le_normalizer_blockU L hl) u).1 u.2
      refine (hmemW _).2 ⟨⟨l * u * l⁻¹, hmem⟩, ?_, rfl⟩
      rw [← T.rhoSec_smul ⟨l, hl⟩ u ⟨l * u * l⁻¹, hmem⟩ rfl]
      exact hJ _ (T.rhoSec ⟨l, hl⟩).2 _ huJ
    rcases hL.2.2.2.2.2 W hZW hWU hLW with h | h
    · left
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨u, rfl⟩ := T.qHom_surjective s
      have hu : (u : G) ∈ W := (hmemW _).2 ⟨u, hs, rfl⟩
      rw [h] at hu
      rw [Subgroup.mem_bot]
      exact (T.qHom_eq_one_iff u).2 hu
    · right
      rw [eq_top_iff]
      intro s _
      obtain ⟨u, rfl⟩ := T.qHom_surjective s
      have hu : (u : G) ∈ W := by rw [h]; exact u.2
      obtain ⟨u', hu'J, hu'⟩ := (hmemW _).1 hu
      have : u' = u := Subtype.ext hu'
      rw [← this]
      exact hu'J
  obtain ⟨π, hπinj, hπ⟩ := exists_altDn_three hS _ hcardΓ hirr
  exact T.isAltType_of_altDn ⟨1, rfl⟩ hinj hpc hπ hπinj

end L246

end CFSG.QuasithinUnique
