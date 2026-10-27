module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank

public section

namespace CFSG

variable {H : Type*} [Group H]

theorem isCyclic_of_inf_eq_bot_of_sup_cyclic_right
    {Q C Y : Subgroup H} [Q.Normal]
    (hQC : Q ⊔ C = ⊤) (hC : IsCyclic C) (hYQ : Y ⊓ Q = ⊥) :
    IsCyclic Y := by
  classical
  haveI : IsCyclic (H ⧸ Q) := quotient_isCyclic_of_sup_cyclic_right hQC hC
  let φ : ↥Y →* H ⧸ Q := (QuotientGroup.mk' Q).comp Y.subtype
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    constructor
    · intro hx
      have hx1 : φ x = 1 := MonoidHom.mem_ker.mp hx
      have hxQ : (x : H) ∈ Q := by
        have h2 : QuotientGroup.mk' Q (x : H) = 1 := hx1
        exact (QuotientGroup.eq_one_iff (N := Q) (x := (x : H))).mp h2
      have hxY : (x : H) ∈ Y := x.2
      have hbot : (x : H) ∈ (⊥ : Subgroup H) := by
        rw [← hYQ]
        exact ⟨hxY, hxQ⟩
      have hx1' : (x : H) = 1 := by simpa using hbot
      exact Subtype.ext hx1'
    · intro hx
      rw [MonoidHom.mem_ker]
      have hx1 : (x : H) = 1 := by simpa using hx
      simp [φ, hx1]
  exact isCyclic_of_injective φ hinj

end CFSG
