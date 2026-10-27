module

public import CFSG.CGT.PushingUpLit.SYMB.Delta5Swaps
public import CFSG.CGT.PushingUpLit.SYMB.FiveCoho

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {V₁ : Subgroup Γ}

@[expose] def Cfix (ψ : ↥V →* ↥(G6.coreMod 5)) (V₁ : Subgroup Γ)
    (P : Subgroup (Equiv.Perm (Fin 5))) : Subgroup Γ :=
  ((V₁.subgroupOf V) ⊓ (Delta5Swaps.Fixed P).comap ψ).map V.subtype

theorem mem_Cfix {P : Subgroup (Equiv.Perm (Fin 5))} {x : Γ} :
    x ∈ Cfix ψ V₁ P ↔ ∃ hx : x ∈ V, x ∈ V₁ ∧ ψ ⟨x, hx⟩ ∈ Delta5Swaps.Fixed P := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, Subgroup.mem_subgroupOf.1 hv.1, hv.2⟩
  · rintro ⟨hx, hx1, hx2⟩
    exact ⟨⟨x, hx⟩, ⟨Subgroup.mem_subgroupOf.2 hx1, hx2⟩, rfl⟩

theorem Cfix_le (P : Subgroup (Equiv.Perm (Fin 5))) : Cfix ψ V₁ P ≤ V₁ := by
  intro x hx
  obtain ⟨hxV, hx1, -⟩ := mem_Cfix.1 hx
  exact hx1

namespace V1Iso

theorem inf_centralizer_eq_Cfix (hV : V1Iso S V₁) {A : Subgroup Γ} (hAG : A ≤ G) :
    V₁ ⊓ Subgroup.centralizer (A : Set Γ) = Cfix ψ V₁ (imgG G φ A) := by
  ext v
  rw [Subgroup.mem_inf, mem_Cfix, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hv, hc⟩
    refine ⟨hV.le hv, hv, ?_⟩
    rw [Delta5Swaps.mem_Fixed]
    intro σ hσ
    obtain ⟨a, haG, haA, rfl⟩ := mem_imgG.1 hσ
    have hav : a * v * a⁻¹ = v := by
      have := hc a haA
      rw [this]
      group
    have h1 := hV.psi_conj haG hv
    have h2 : ψ ⟨a * v * a⁻¹, S.data.conj_mem haG (hV.le hv)⟩ = ψ ⟨v, hV.le hv⟩ := by
      congr 1
      exact Subtype.ext hav
    rw [h2] at h1
    exact h1.symm
  · rintro ⟨hvV, hv1, hfix⟩
    refine ⟨hv1, fun a haA => ?_⟩
    have haG : a ∈ G := hAG haA
    have h1 := hV.psi_conj haG hv1
    have h2 : G6.coreAct 5 (φ ⟨a, haG⟩) (ψ ⟨v, hV.le hv1⟩) = ψ ⟨v, hV.le hv1⟩ :=
      Delta5Swaps.mem_Fixed.1 hfix _ (mem_imgG.2 ⟨a, haG, haA, rfl⟩)
    rw [h2] at h1
    have h3 : a * v * a⁻¹ = v := by
      apply hV.eq_of_psi_eq (hV.normal haG |> fun h => (Subgroup.mem_normalizer_iff.mp h v).mp hv1) hv1
      exact h1
    calc a * v = (a * v * a⁻¹) * a := by group
      _ = v * a := by rw [h3]

noncomputable def toEquiv (hV : V1Iso S V₁) : ↥V₁ ≃* G6.coreMod 5 :=
  MulEquiv.ofBijective (ψ.comp (Subgroup.inclusion hV.le))
    ⟨fun a b h => by
      apply Subtype.ext
      apply hV.eq_of_psi_eq a.2 b.2
      exact h,
     fun w => by
      obtain ⟨v, hv, hψ⟩ := hV.surj w
      exact ⟨⟨v, hv⟩, hψ⟩⟩

theorem card_Cfix (hV : V1Iso S V₁) (P : Subgroup (Equiv.Perm (Fin 5))) :
    Nat.card ↥(Cfix ψ V₁ P) = Nat.card ↥(Delta5Swaps.Fixed P) := by
  classical
  refine Nat.card_eq_of_bijective
    (fun x => ⟨ψ ⟨x.1, (mem_Cfix.1 x.2).1⟩, (mem_Cfix.1 x.2).2.2⟩) ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply hV.eq_of_psi_eq (mem_Cfix.1 x.2).2.1 (mem_Cfix.1 y.2).2.1
    exact congrArg Subtype.val hxy
  · intro w
    obtain ⟨v, hv, hψ⟩ := hV.surj w.1
    have hmem : (v : Γ) ∈ Cfix ψ V₁ P := mem_Cfix.2 ⟨v.2, hv, by simp [hψ]⟩
    refine ⟨⟨v, hmem⟩, Subtype.ext ?_⟩
    simpa using hψ

end V1Iso

end CFSG.CGT.PushingUpLit.SYMB
