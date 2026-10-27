module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabOrderFour
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Model

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

namespace MuTab

section G2

variable {p e : ℕ} [Fact p.Prime]

theorem g2_exists_commuting_charts (hp2 : p ≠ 2) (he : 1 ≤ e) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot Tag.G2 γ) :
    ∃ Φ Ψ : SL(2, GaloisField p e) →* ↥(adjointGroup Tag.G2 (GaloisField p e)),
      Function.Injective Φ ∧ (∀ A B, Φ A * Ψ B = Ψ B * Φ A) ∧ Φ (-1) = Ψ (-1) ∧
        Φ.range = rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
          rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ) := by
  set F := GaloisField p e with hF
  have hodd : Odd (Nat.card F) := by
    rw [GaloisField.card p e (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  obtain ⟨a, ha, hne1, hγa⟩ := exists_signKernel_g2 hK2 hγ
  obtain ⟨α, β, -, hker, -, hcomm, -⟩ := g2_toral_data hodd ha hne1
  have hγmem : γ ∈ ({α, -α, β, -β} : Set (Fin Tag.G2.rank → ℤ)) := hker ▸ hγa
  obtain ⟨γ', hγ'a, hcommγ⟩ : ∃ γ', γ' ∈ rootCharKernel a ∧
      ⁅rootPair Tag.G2 F γ, rootPair Tag.G2 F γ'⁆ = ⊥ := by
    have hα : α ∈ rootCharKernel a := by rw [hker]; simp
    have hβ : β ∈ rootCharKernel a := by rw [hker]; simp
    have hc1 : ⁅rootPair Tag.G2 F α, rootPair Tag.G2 F β⁆ = ⊥ := hcomm
    have hc2 : ⁅rootPair Tag.G2 F β, rootPair Tag.G2 F α⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hc1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγmem
    rcases hγmem with rfl | rfl | rfl | rfl
    · exact ⟨β, hβ, hc1⟩
    · exact ⟨β, hβ, by rw [rootPair_neg]; exact hc1⟩
    · exact ⟨α, hα, hc2⟩
    · exact ⟨α, hα, by rw [rootPair_neg]; exact hc2⟩
  obtain ⟨w, i, φ, hw, hφinj, hφrange, hφneg⟩ := exists_hom_of_isRoot hK2 hγ
  obtain ⟨w', i', ψ, hw', hψinj, hψrange, hψneg⟩ := exists_hom_of_isRoot hK2 hγ'a.1
  have hφa : φ (-1) = rootDiagUnit Tag.G2 a :=
    hφneg.trans (torusElt_neg_one_conj_eq_rootDiagUnit hodd ha hne1 hγa hw)
  have hψa : ψ (-1) = rootDiagUnit Tag.G2 a :=
    hψneg.trans (torusElt_neg_one_conj_eq_rootDiagUnit hodd ha hne1 hγ'a hw')
  have hφmem : ∀ A, φ A ∈ adjointGroup Tag.G2 F := fun A => by
    have : φ A ∈ φ.range := ⟨A, rfl⟩
    rw [hφrange] at this
    exact (sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ))) this
  have hψmem : ∀ B, ψ B ∈ adjointGroup Tag.G2 F := fun B => by
    have : ψ B ∈ ψ.range := ⟨B, rfl⟩
    rw [hψrange] at this
    exact (sup_le (rootSubgroup_le_adjointGroup γ') (rootSubgroup_le_adjointGroup (-γ'))) this
  set ι : ↥(adjointGroup Tag.G2 F) →* ModGL Tag.G2 F := (adjointGroup Tag.G2 F).subtype with hι
  have hιinj : Function.Injective ι := Subtype.val_injective
  let Φ : SL(2, F) →* ↥(adjointGroup Tag.G2 F) := φ.codRestrict _ hφmem
  let Ψ : SL(2, F) →* ↥(adjointGroup Tag.G2 F) := ψ.codRestrict _ hψmem
  have hιΦ : ι.comp Φ = φ := MonoidHom.ext fun _ => rfl
  refine ⟨Φ, Ψ, fun A B h => hφinj (congrArg Subtype.val h), fun A B => ?_,
    Subtype.ext (hφa.trans hψa.symm), ?_⟩
  · apply Subtype.ext
    have h1 : φ A ∈ rootPair Tag.G2 F γ := by
      rw [rootPair, ← hφrange]
      exact ⟨A, rfl⟩
    have h2 : ψ B ∈ rootPair Tag.G2 F γ' := by
      rw [rootPair, ← hψrange]
      exact ⟨B, rfl⟩
    have h3 := Subgroup.commutator_mem_commutator h1 h2
    rw [hcommγ, Subgroup.mem_bot, commutatorElement_def] at h3
    show φ A * ψ B = ψ B * φ A
    calc φ A * ψ B = φ A * ψ B * (φ A)⁻¹ * (ψ B)⁻¹ * (ψ B * φ A) := by group
      _ = ψ B * φ A := by rw [h3, one_mul]
  · apply Subgroup.map_injective hιinj
    have hQ : (rootGroup (rootOperatorFamily Tag.G2) F γ ⊔
        rootGroup (rootOperatorFamily Tag.G2) F (-γ)).map ι = rootPair Tag.G2 F γ := by
      rw [← ModelFacts.subgroupOf_rootSubgroup_sup_eq (rootOperatorFamily Tag.G2) hγ, hι,
        Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.2 (sup_le (rootSubgroup_le_adjointGroup γ)
        (rootSubgroup_le_adjointGroup (-γ)))
    rw [hQ, ← MonoidHom.range_comp, hιΦ, hφrange]
    rfl

theorem g2_exists_orderFour (hp2 : p ≠ 2) (he : 1 ≤ e)
    {R : Subgroup ↥(adjointGroup Tag.G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum (GaloisField p e))) :
    ∃ c j d : ↥(adjointGroup Tag.G2 (GaloisField p e)), IsUniqueInvolution R c ∧ j ∈ R ∧
      orderOf j = 4 ∧ d * d = 1 ∧ d ≠ 1 ∧ d ≠ c ∧ j * d = d * j := by
  obtain ⟨g₀, γ, hγ, rfl⟩ := hR
  have hγroot : IsRoot Tag.G2 γ := by
    rcases hγ with h | ⟨-, h⟩ | ⟨h, -⟩
    · exact mem_adjDatum_roots.1 h.1
    · exact mem_adjDatum_roots.1 h
    · exact absurd h (by decide)
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨Φ, Ψ, hΦ, hcomm, hneg, hrange⟩ := g2_exists_commuting_charts hp2 he hγroot
  rw [← hrange]
  exact exists_orderFour_of_charts hodd hΦ hcomm hneg g₀

end G2

end MuTab

section G2Datum

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem MuTab.g2_omegaStarNbr_nonempty (M : Ih8Model p f Ω .G2 0 e) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) :
    ∃ K ∈ Ω, (omegaStarNbr Ω K).Nonempty := by
  have he : 1 ≤ e := M.admissible.2.1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 (Or.inl rfl) 0 he M.ψ M.ker_le_center
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨R, hR, -⟩ := (M.mem_iff K₀).mp hK₀
  obtain ⟨c, j, d, hc, hj, hj4, hd, hd1, hdc, hjd⟩ :=
    MuTab.g2_exists_orderFour hp2 he (M.cls_sub hR)
  exact M.muTab_omegaStarNbr_of_orderFour hΩ hp2 hq hinj
    (fun u u' hu hu' hu1 hu1' => g2_involutions_conj hodd hu hu' hu1 hu1') hR hc hj hj4 hd hd1 hdc
    hjd

end G2Datum

end CFSG.ClassicalInvolution.Asc77
