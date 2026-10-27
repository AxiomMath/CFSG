module

public import CFSG.RankThree.GF2n.Tim78a.GriessSpMultiplier
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Assembly.LowTwoRank

theorem exists_mulEquiv_statedSp_of_component_B2
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {f : ℕ} (hf : 2 <= f) {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hQexp : Q.exponent = f)
    {hv : (TauCeti.LieTypeIndex.B 2 Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.B 2 Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group) :
    Nonempty (L ≃* StatedSp 2 (GaloisField 2 f)) := by
  classical
  let F := GaloisField 2 f
  haveI : CharP F 2 := inferInstance
  have hcardF : Nat.card F = Q.card := by
    rw [show Nat.card F = 2 ^ f from GaloisField.card 2 f (by omega),
      TauCeti.PrimePower.card_def, hQ, hQexp]
  obtain ⟨eB⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj
      (q := Q) hv hcardF
  have hcenter : (StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F) = ⊥ := by
    have h := center_statedSp_eq_bot_of_charP_two (m := 2) (F := F) (by norm_num)
    rwa [show Subgroup.center (StatedSp 2 F) =
        (StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F) from by
      rw [show StatedSp 2 F = TauCeti.GLSymplectic (Fin 2) F from
        statedSp_eq_GLSymplectic (n := 2) (K := F)]
      exact center_GLSymplectic_eq (n := 2) (K := F)] at h
  let eProj : StatedProj (StatedSp 2 F) ≃* StatedSp 2 F :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientBot (G := StatedSp 2 F))
  let ρL : L →* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.B 2 Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  let φ : L →* StatedSp 2 F := eProj.toMonoidHom.comp (eB.symm.toMonoidHom.comp ρL)
  have hφsurj : Function.Surjective φ :=
    eProj.surjective.comp
      (eB.symm.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _)))
  have hkerφ : φ.ker = Subgroup.center L := by
    have h1 : φ.ker = (eB.symm.toMonoidHom.comp ρL).ker :=
      MonoidHom.ker_comp_of_injective _ _ eProj.injective
    rw [h1, MonoidHom.ker_comp_of_injective _ _ eB.symm.injective]
    show (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hcen : φ.ker ≤ Subgroup.center L := le_of_eq hkerφ
  have hcom : φ.ker ≤ commutator L := by
    rw [hL.1]
    exact le_top
  have h21 : (2, f) ≠ (2, 1) := by
    rintro ⟨-, h⟩
    omega
  have hkerbot : φ.ker = ⊥ :=
    CFSG.RankThree.GF2n.Tim79a.griessSpMultiplierStatement_holds
      2 f (by norm_num) (by omega) (by simp) (by simp) h21 (by simp)
      L φ hφsurj hcen hcom
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hkerbot
  exact ⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩⟩

end CFSG.ClassicalGroups.Symplectic

end
