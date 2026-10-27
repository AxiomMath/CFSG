module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Coc
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Mdl117

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117
open CFSG.ComponentClassification.PresentationLocal

@[expose] def Model117Gen : Prop :=
  ∀ n : ℕ, 5 ≤ n → n ≠ 8 → ∀ β : MulAut ↥((AE.aeSub n).map (AE.mkQ n)),
    (∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      ∃ (α' : Finset (Fin n)) (h' : α'.card = 4) (b' : Bool),
        ((AE.memBar α h b).subgroupOf ((AE.aeSub n).map (AE.mkQ n))).map β.toMonoidHom =
          (AE.memBar α' h' b').subgroupOf ((AE.aeSub n).map (AE.mkQ n))) →
      ∃ x : AE.AEQ n, ∀ g : ↥((AE.aeSub n).map (AE.mkQ n)), ((β g : _) : AE.AEQ n) = x * g * x⁻¹

variable {n : ℕ}

@[expose] def altHom (n : ℕ) : ↥(alternatingGroup (Fin n)) →* ↥(GBar n) :=
  ((mkQ n).comp ((ofPermHom n).comp (alternatingGroup (Fin n)).subtype)).codRestrict (GBar n)
    fun σ => ofPerm_mem_GBar σ.2

theorem coe_altHom (σ : ↥(alternatingGroup (Fin n))) :
    ((altHom n σ : ↥(GBar n)) : AEQ n) = mkQ n (ofPerm (σ : Equiv.Perm (Fin n))) := rfl

theorem eq_of_agree_carmichael (hn : 3 ≤ n) {β γ : MulAut ↥(GBar n)}
    (hgen : ∀ k : CarmichaelIndex n, β (altHom n (carmichaelCycle k)) =
      γ (altHom n (carmichaelCycle k)))
    (hvec : ∀ v : Fin n → ZMod 2, ∑ i, v i = 0 → ∀ g : ↥(GBar n),
      (g : AEQ n) = mkQ n (ofVec v) → β g = γ g) : β = γ := by
  have hK : β.toMonoidHom.comp (altHom n) = γ.toMonoidHom.comp (altHom n) :=
    hom_ext_carmichaelCycle hn fun k => hgen k
  refine MulEquiv.ext fun g => ?_
  obtain ⟨x, w, hw, rfl⟩ := g
  have hp : w.perm ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.mpr hw.2
  have hv : ∑ i, w.vec i = 0 := hw.1
  have hsplit : (⟨mkQ n w, ⟨w, hw, rfl⟩⟩ : ↥(GBar n)) =
      ⟨mkQ n (ofVec w.vec), ofVec_mem_GBar hv⟩ * altHom n ⟨w.perm, hp⟩ :=
    Subtype.ext (by rw [Subgroup.coe_mul, coe_altHom, ← map_mul, ofVec_mul_ofPerm])
  rw [hsplit, map_mul, map_mul, hvec w.vec hv _ rfl]
  congr 1
  exact DFunLike.congr_fun hK ⟨w.perm, hp⟩

end CFSG.ClassicalInvolution.Q3.TL4.Mdl117
