module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI9
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CII
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Case

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem card_cent_Qhat_ge {y : G} (hy : y ∈ c.Qs) :
    256 ≤ Nat.card ↥(c.Rhat c.Qs ⊓ centralizer
      ({c.rho ⟨y, c.Qs_le_N1 hy⟩} : Set (MulAut ↥E × MulAut ↥E))) := by
  obtain ⟨f₁, f₂, hf⟩ := c.rho_Qs_mem hy
  have hmem : ∀ p : ↥(innAutE E) × ↥(innAutE E),
      (((p.1 : MulAut ↥E), (p.2 : MulAut ↥E)) : MulAut ↥E × MulAut ↥E) ∈
        c.Rhat c.Qs ⊓ centralizer ({c.rho ⟨y, c.Qs_le_N1 hy⟩} : Set (MulAut ↥E × MulAut ↥E)) := by
    rintro ⟨⟨i₁, e₁, he₁⟩, ⟨i₂, e₂, he₂⟩⟩
    obtain ⟨q, hq, hρq⟩ := c.exists_rho_Qs e₁ e₂
    refine ⟨c.mem_Rhat.2 ⟨⟨q, c.Qs_le_N1 hq⟩, hq, ?_⟩, mem_centralizer_singleton_iff.2 ?_⟩
    · rw [hρq]
      exact Prod.ext he₁ he₂
    · rw [hf]
      have c1 := c.innAutE_comm (a := i₁) (b := MulAut.conj f₁) ⟨e₁, he₁⟩ ⟨f₁, rfl⟩
      have c2 := c.innAutE_comm (a := i₂) (b := MulAut.conj f₂) ⟨e₂, he₂⟩ ⟨f₂, rfl⟩
      exact Prod.ext c1 c2
  have hle : Nat.card (↥(innAutE E) × ↥(innAutE E)) ≤ Nat.card ↥(c.Rhat c.Qs ⊓ centralizer
      ({c.rho ⟨y, c.Qs_le_N1 hy⟩} : Set (MulAut ↥E × MulAut ↥E))) := by
    refine Nat.card_le_card_of_injective
      (fun p => (⟨(((p.1 : MulAut ↥E), (p.2 : MulAut ↥E)) : MulAut ↥E × MulAut ↥E), hmem p⟩ :
        ↥(c.Rhat c.Qs ⊓ centralizer
          ({c.rho ⟨y, c.Qs_le_N1 hy⟩} : Set (MulAut ↥E × MulAut ↥E))))) ?_
    intro p p' hpp'
    have h1 := congrArg Subtype.val hpp'
    have h2 : ((p.1 : MulAut ↥E), (p.2 : MulAut ↥E)) = ((p'.1 : MulAut ↥E), (p'.2 : MulAut ↥E)) :=
      h1
    obtain ⟨h3, h4⟩ := Prod.mk.inj h2
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  rw [Nat.card_prod, c.card_inn] at hle
  exact hle

theorem not_conj_z_of_mem_Qs {y : G} (hy : y ∈ c.Qs) (hyz : ∃ g : G, y = g * z * g⁻¹) :
    False := by
  by_cases hyZ : y ∈ c.Zs
  · exact c.not_conj_z_of_mem_Zs hyZ hyz
  exact c.false_of_big_cent c.Qs_pgroup c.Qs_le_N1 c.Zs_le_Qs c.Qs_inf_KR_le hy hyZ hyz
    (c.card_cent_Qhat_ge hy)

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
