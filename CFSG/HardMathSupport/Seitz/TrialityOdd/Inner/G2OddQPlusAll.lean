module

public import CFSG.RankThree.PartOne.SEITZ11.G2SevenConsumer

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ11.G2Seven

theorem closure_cenGen_adjointG2_odd_qplus_eq_top_all
    (X : Type) [Field X] [Finite X] (hX : Odd (Nat.card X))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card X + 1)
    (E₁ : Subgroup (adjointGroup Tag.G2 X)) (hE₁p : ∀ x ∈ E₁, x ^ p = 1)
    (hE₁c : Nat.card E₁ = p ^ 2) :
    Subgroup.closure (cenGen E₁) = ⊤ := by
  classical
  have hq5 : 5 ≤ Nat.card X := by
    have h1 : p ≤ Nat.card X + 1 := Nat.le_of_dvd (Nat.succ_pos _) hpq
    obtain ⟨m, hm⟩ := hX
    omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₂, hF₂, hfin₂, hAlg, σ, hdeg, hσ⟩ := exists_quadratic_ext (K := X)
  obtain ⟨g, z, hg, -, hzdef, ⟨hz, hw⟩, hΓ, -, -, ⟨S₀, hS₀⟩, ⟨E, hEmem, hEle, hEcard, -, -⟩,
      -, -, hcent⟩ :=
    odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers X hX hp (by omega) hpq K₂ hdeg σ hσ
  have hGEN := g2_qplus_generation hX (by omega) K₂ hdeg σ hσ hg hzdef hz hw
  have : Finite (ModGL Tag.G2 K₂) := finite_modGL
  let Γ : Subgroup (ModGL Tag.G2 K₂) := conjEntrywiseImage X g
  have hEΓ : E ≤ Γ := fun x hx => (hEle hx).2
  have hmapE : (torsionParams K₂ p).map (rootDiagUnitHom Tag.G2 K₂) = E := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine (hEmem _).2 ⟨rootDiagUnit_mem_torusGroup_G2 a, ?_⟩
      show rootDiagUnit Tag.G2 a ^ p = 1
      have hap : a ^ p = 1 := funext fun i => mem_torsionParams.1 ha i
      rw [rootDiagUnit_pow, hap, rootDiagUnit_one]
    · intro hx
      obtain ⟨hxT, hxp⟩ := (hEmem x).1 hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
      refine ⟨a, ?_, rfl⟩
      have h1 : rootDiagUnit Tag.G2 (a ^ p) = rootDiagUnit Tag.G2 (1 : Fin Tag.G2.rank → K₂ˣ) := by
        rw [← rootDiagUnit_pow, hxp, rootDiagUnit_one]
      have h2 : a ^ p = 1 := rootDiagUnit_injective h1
      exact mem_torsionParams.2 fun i => congrFun h2 i
  have hcardAp : Nat.card (torsionParams K₂ p) = p ^ 2 := by
    rw [← hEcard, ← hmapE]
    exact (Subgroup.card_map_of_injective rootDiagUnit_injective).symm
  have hroot : ∀ β, IsRoot Tag.G2 β → ∀ r ∈ rootRankOneGroup Tag.G2 K₂ β ⊓ Γ,
      ∃ hrΓ : r ∈ Γ, (⟨r, hrΓ⟩ : Γ) ∈ cenGen (E.subgroupOf Γ) := by
    intro β hβ r hr
    obtain ⟨a, haT, ha1, hachar⟩ := exists_ker hp hcardAp β
    have hxE : rootDiagUnit Tag.G2 a ∈ E := hmapE ▸ ⟨a, haT, rfl⟩
    have hxTΓ := hEle hxE
    have hxp : rootDiagUnit Tag.G2 a ^ p = 1 := ((hEmem _).1 hxE).2
    have hx1 : rootDiagUnit Tag.G2 a ≠ 1 := fun h =>
      ha1 (rootDiagUnit_injective (h.trans rootDiagUnit_one.symm))
    have hord : orderOf (rootDiagUnit Tag.G2 a) = p := orderOf_eq_prime hxp hx1
    obtain ⟨-, hne⟩ := hcent a hxTΓ hord
    have hker : rootCharKernel a ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨β, hβ, hachar⟩
    obtain ⟨α, hα, hkerα, hcomm, -⟩ := hne hker
    have hβα : β = α ∨ β = -α := by
      have : β ∈ rootCharKernel a := ⟨hβ, hachar⟩
      rw [hkerα] at this
      simpa using this
    have hRβ : rootRankOneGroup Tag.G2 K₂ β = rootRankOneGroup Tag.G2 K₂ α := by
      rcases hβα with rfl | rfl
      · rfl
      · exact CFSG.RankThree.PartOne.KE.rootRankOneGroup_neg hα
    have hrD : r ∈ ⁅Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.G2 a},
        Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.G2 a}⁆ := by
      rw [hcomm, ← hRβ]
      exact hr
    obtain ⟨hrΓ, hrc⟩ := commutator_self_le _ hrD
    refine ⟨hrΓ, ⟨_, hxTΓ.2⟩, hxE, ?_, ?_⟩
    · intro h
      exact hx1 (congrArg Subtype.val h)
    · exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hrc _ rfl).symm)
  have hC : closure (cenGen (E.subgroupOf Γ)) = ⊤ := by
    set C := closure (cenGen (E.subgroupOf Γ)) with hCdef
    have hRle : ⨆ α : {α : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 α},
        rootRankOneGroup Tag.G2 K₂ α.1 ⊓ Γ ≤ C.map Γ.subtype := by
      refine iSup_le fun α => ?_
      intro r hr
      obtain ⟨hrΓ, hrc⟩ := hroot α.1 α.2 r hr
      exact ⟨⟨r, hrΓ⟩, subset_closure hrc, rfl⟩
    rw [eq_top_iff]
    intro γ _
    have h1 : (γ : ModGL Tag.G2 K₂) ∈ ⨆ α : {α : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 α},
        rootRankOneGroup Tag.G2 K₂ α.1 ⊓ Γ := by
      rw [hGEN]
      exact γ.2
    obtain ⟨c, hc, hcγ⟩ := hRle h1
    have : c = γ := Subtype.ext hcγ
    exact this ▸ hc
  let ψ : ModGL Tag.G2 X →* ModGL Tag.G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap X K₂))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := Tag.G2) (algebraMap X K₂))
  let ε : adjointGroup Tag.G2 X ≃* Γ := Subgroup.equivMapOfInjective (adjointGroup Tag.G2 X) ψ hψ
  refine closure_cenGen_eq_top_of_map ε E₁ ?_
  have hF : ∀ y ∈ E₁.map ε.toMonoidHom, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₁p x hx, map_one]
  have hFc : Nat.card (E₁.map ε.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective ε.injective]
    exact hE₁c
  have hEc : Nat.card (E.subgroupOf Γ) = p ^ 2 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv
  obtain ⟨h, hFh⟩ := plane_conj S₀ hS₀ (E := E.subgroupOf Γ) (fun x hxT hxp => by
    have h1 : (x : ModGL Tag.G2 K₂) ∈ torusGroup Tag.G2 K₂ ⊓ Γ := hxT
    have h2 : (x : ModGL Tag.G2 K₂) ^ p = 1 := by
      have := congrArg Subtype.val hxp
      simpa using this
    exact (hEmem _).2 ⟨h1.1, h2⟩) hEc hF hFc
  rw [hFh, closure_cenGen_cj, hC, Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
