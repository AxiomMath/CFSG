module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.Inner
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.Reduce
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.SuN
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFour

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.Assembly.LowTwoRank CFSG.StandardType.RecipeExcLang
open scoped commutatorElement

section Residuals


@[expose] def SsExcTwoD (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (S : LangSetup τ L 3), (2 : L) ≠ 0 →
    ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ a ^ 3 = 1 →
      rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        twistKind S.ρ (rootCharHom a) i = .twoD →
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ¬ IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

@[expose] def SsExcExc (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (S : LangSetup τ L 3), (2 : L) ≠ 0 →
    ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ a ^ 3 = 1 →
      rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        twistKind S.ρ (rootCharHom a) i = .exc →
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ¬ IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

theorem ssExcTwoD_g2 : SsExcTwoD Tag.G2 := by
  intro L _ _ S _ a _ _ _ i hk _
  exfalso
  have h4 := (twoD_kind_unpack hk).2.1
  have h2 := compRank_le_rank (τ := Tag.G2) (componentRoots (rootCharHom a) i)
  have : Tag.G2.rank = 2 := rfl
  omega

theorem ssExcExc_g2 : SsExcExc Tag.G2 := by
  intro L _ _ S _ a _ _ _ i hk _
  exfalso
  obtain ⟨-, h⟩ := exc_kind hk
  have h2 := compRank_le_rank (τ := Tag.G2) (componentRoots (rootCharHom a) i)
  have : Tag.G2.rank = 2 := rfl
  rcases h with ⟨h6, -⟩ | ⟨h4, -, -⟩ <;> omega

end Residuals

section Core


theorem noL34Layer_exc_inner_untw_of {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hTwoD : SsExcTwoD τ) (hExc : SsExcExc τ)
    {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hperf : commutator ↥(adjointGroup τ K) = ⊤)
    (β : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹) (hp1 : h ^ 3 = 1) (hh1 : h ≠ 1) :
    NoL34Layer β := by
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h3
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 this
    omega
  have h2K : ¬ 2 ∣ Nat.card K := by
    rw [hK]
    intro h2
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 this
    omega
  have h4K : 4 ≤ Nat.card K := by
    rw [hK]
    exact (by omega : 4 ≤ ℓ).trans (Nat.le_self_pow (by omega) ℓ)
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h | h <;> simp [h]) Nat.prime_three (by norm_num)
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ := exists_langSetup_of_inner_untw hτ
    Nat.prime_three h3K (Or.inr h4K) hmon hperf β h hhL hβ hp1 hh1
  have h2L : (2 : AlgebraicClosure K) ≠ 0 := by
    have := natCast_ne_zero_algebraicClosure Nat.prime_two h2K
    simpa using this
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  haveI : Finite ↥(adjointGroup τ K) := inferInstance
  refine noL34Layer_of_langSetup S Nat.prime_three ι hinj hrange β hconj hT hap h1
    (langSetup_hTame S hT hap h1) ?_
  intro i hq
  cases hk : twistKind S.ρ (rootCharHom a) i with
  | inner => exact ssexc_not_L34_inner S h2L hT i hk
  | suN => exact ssexc_not_L34_suN S h2L hT hTp h1 i hk hq
  | twoD => exact hTwoD _ S h2L a hT hTp h1 i hk hq
  | exc => exact hExc _ S h2L a hT hTp h1 i hk hq

end Core

section Glue


theorem ssexc_noL34Layer_one {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hL34 : ¬ IsLThreeFour X) :
    NoL34Layer (1 : MulAut X) := by
  have htop : fixSubgroup (1 : MulAut X) = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun x => by simp [mem_fixSubgroup]
  exact noL34Layer_of_fixed_equiv (1 : MulAut X)
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) hs hnab hL34

theorem ssexc_noL34_inn_adjoint {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hTwoD : SsExcTwoD τ) (hExc : SsExcExc τ)
    {F : Type} [Field F] [Finite F] {ℓ f : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    (hF : Nat.card F = ℓ ^ f) (hperf : commutator ↥(adjointGroup τ F) = ⊤)
    {ψ : MulAut ↥(adjointGroup τ F)} (hψ3 : ψ ^ 3 = 1) (hψ : ψ ∈ inner ↥(adjointGroup τ F))
    (hψ1 : ψ ≠ 1) : NoL34Layer ψ := by
  obtain ⟨x, rfl⟩ := hψ
  have hZ : Subgroup.center ↥(adjointGroup τ F) = ⊥ := center_adjointGroup_eq_bot
  have hx3 : x ^ 3 = 1 := by
    have h1 : (MulAut.conj (x ^ 3) : MulAut ↥(adjointGroup τ F)) = MulAut.conj 1 := by
      rw [map_pow, map_one]
      exact hψ3
    have h2 : x ^ 3 ∈ Subgroup.center ↥(adjointGroup τ F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun h1 g
      simp only [MulAut.conj_apply, MulAut.one_apply, inv_one, mul_one, one_mul] at this
      calc g * x ^ 3 = x ^ 3 * g * (x ^ 3)⁻¹ * x ^ 3 := by rw [this]
        _ = x ^ 3 * g := by group
    rwa [hZ, Subgroup.mem_bot] at h2
  have hx1 : (x : ModGL τ F) ≠ 1 := fun h1 => hψ1 (by
    have : x = 1 := Subtype.ext h1
    rw [this, map_one])
  exact noL34Layer_exc_inner_untw_of hτ hTwoD hExc hℓ h5 hf hF hperf (MulAut.conj x) (x : ModGL τ F)
    (baseChange_mem_adjointGroup_of_mem_inndiag (adjointGroup_le_inndiagGroup x.2))
    (fun c => by simp [MulAut.conj_apply]) (by rw [← Subgroup.coe_pow, hx3]; rfl) hx1


theorem ssexc_commutator_eq_top_of_simple {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hm : ⁅a, b⁆ ∈ commutator G := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hab hm
  · exact h


section G2


theorem noL34InnAt_g2 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34InnAt FamG2 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .G2 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∈ inner ↥(adjointGroup Tag.G2 F) :=
    (congr_mem_inner_iff_of_equiv θ ψ).2 hψ
  have h3 : 3 ≤ p ^ f := by
    have h2 := hadm.1.two_le
    have : 3 ≤ p := by omega
    exact this.trans (Nat.le_self_pow (by omega) p)
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.G2 F) .G2 p f :=
    ⟨⟨hadm.1, hf, rfl, h3⟩, untwisted_adjointGroup hFcard⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_g2_simplicity _ p f hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.G2 F) = ⊥ := center_adjointGroup_eq_bot
  have hnab := exists_noncomm_of_center_bot hZ
  refine noL34Layer_congr θ ?_
  by_cases h1 : MulAut.congr θ ψ = 1
  · rw [h1]
    exact ssexc_noL34Layer_one hsimp hnab (not_isLThreeFour_of_lieModel_odd hO hp2
      (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)))
  · have hperf : commutator ↥(adjointGroup Tag.G2 F) = ⊤ := ssexc_commutator_eq_top_of_simple hsimp hnab
    exact ssexc_noL34_inn_adjoint (Or.inl rfl) ssExcTwoD_g2 ssExcExc_g2 hadm.1 hp5 hf hFcard hperf
      hβ3 hβinn h1

end G2

section F4


theorem noL34InnAt_f4 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hTwoD : SsExcTwoD Tag.F4) (hExc : SsExcExc Tag.F4) : NoL34InnAt FamF4 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .F4 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∈ inner ↥(adjointGroup Tag.F4 F) :=
    (congr_mem_inner_iff_of_equiv θ ψ).2 hψ
  
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.F4 F) .F4 p f :=
    ⟨⟨hadm.1, hf, rfl⟩, untwisted_adjointGroup hFcard⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_f4_simplicity _ p f hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.F4 F) = ⊥ := center_adjointGroup_eq_bot
  have hnab := exists_noncomm_of_center_bot hZ
  refine noL34Layer_congr θ ?_
  by_cases h1 : MulAut.congr θ ψ = 1
  · rw [h1]
    exact ssexc_noL34Layer_one hsimp hnab (not_isLThreeFour_of_lieModel_odd hO hp2
      (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)))
  · have hperf : commutator ↥(adjointGroup Tag.F4 F) = ⊤ := single_edge_perfect Tag.F4 F (Or.inl rfl)
    exact ssexc_noL34_inn_adjoint (Or.inr (Or.inl rfl)) hTwoD hExc hadm.1 hp5 hf hFcard hperf hβ3 hβinn h1

end F4

section E6


theorem noL34InnAt_e6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hTwoD : SsExcTwoD Tag.E6) (hExc : SsExcExc Tag.E6) : NoL34InnAt FamE6 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E6 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∈ inner ↥(adjointGroup Tag.E6 F) :=
    (congr_mem_inner_iff_of_equiv θ ψ).2 hψ
  
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E6 F) .E6 p f :=
    ⟨⟨hadm.1, hf, rfl⟩, untwisted_adjointGroup hFcard⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e6_simplicity _ p f hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E6 F) = ⊥ := center_adjointGroup_eq_bot
  have hnab := exists_noncomm_of_center_bot hZ
  refine noL34Layer_congr θ ?_
  by_cases h1 : MulAut.congr θ ψ = 1
  · rw [h1]
    exact ssexc_noL34Layer_one hsimp hnab (not_isLThreeFour_of_lieModel_odd hO hp2
      (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)))
  · have hperf : commutator ↥(adjointGroup Tag.E6 F) = ⊤ := single_edge_perfect Tag.E6 F (Or.inr (Or.inr (Or.inl rfl)))
    exact ssexc_noL34_inn_adjoint (Or.inr (Or.inr (Or.inl rfl))) hTwoD hExc hadm.1 hp5 hf hFcard hperf hβ3 hβinn h1

end E6

section E7


theorem noL34InnAt_e7 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hTwoD : SsExcTwoD Tag.E7) (hExc : SsExcExc Tag.E7) : NoL34InnAt FamE7 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E7 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∈ inner ↥(adjointGroup Tag.E7 F) :=
    (congr_mem_inner_iff_of_equiv θ ψ).2 hψ
  
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E7 F) .E7 p f :=
    ⟨⟨hadm.1, hf, rfl⟩, untwisted_adjointGroup hFcard⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e7_simplicity _ p f hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E7 F) = ⊥ := center_adjointGroup_eq_bot
  have hnab := exists_noncomm_of_center_bot hZ
  refine noL34Layer_congr θ ?_
  by_cases h1 : MulAut.congr θ ψ = 1
  · rw [h1]
    exact ssexc_noL34Layer_one hsimp hnab (not_isLThreeFour_of_lieModel_odd hO hp2
      (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)))
  · have hperf : commutator ↥(adjointGroup Tag.E7 F) = ⊤ := single_edge_perfect Tag.E7 F (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    exact ssexc_noL34_inn_adjoint (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hTwoD hExc hadm.1 hp5 hf hFcard hperf hβ3 hβinn h1

end E7

section E8


theorem noL34InnAt_e8 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hTwoD : SsExcTwoD Tag.E8) (hExc : SsExcExc Tag.E8) : NoL34InnAt FamE8 := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain rfl := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E8 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∈ inner ↥(adjointGroup Tag.E8 F) :=
    (congr_mem_inner_iff_of_equiv θ ψ).2 hψ
  
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E8 F) .E8 p f :=
    ⟨⟨hadm.1, hf, rfl⟩, untwisted_adjointGroup hFcard⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e8_simplicity _ p f hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E8 F) = ⊥ := center_adjointGroup_eq_bot
  have hnab := exists_noncomm_of_center_bot hZ
  refine noL34Layer_congr θ ?_
  by_cases h1 : MulAut.congr θ ψ = 1
  · rw [h1]
    exact ssexc_noL34Layer_one hsimp hnab (not_isLThreeFour_of_lieModel_odd hO hp2
      (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)))
  · have hperf : commutator ↥(adjointGroup Tag.E8 F) = ⊤ := single_edge_perfect Tag.E8 F (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    exact ssexc_noL34_inn_adjoint (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hTwoD hExc hadm.1 hp5 hf hFcard hperf hβ3 hβinn h1

end E8

section E6Diag

theorem up34DiagE6_holds_of (hTwoD : SsExcTwoD Tag.E6) (hExc : SsExcExc Tag.E6) :
    Up34DiagE6 := by
  intro ℓ f hℓ h5 hf K _ _ hK x hx3 hxinn hxd
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact (by omega : 4 ≤ ℓ).trans (Nat.le_self_pow (by omega) ℓ)
  rw [← range_e6InndiagConj K] at hxd
  obtain ⟨g, rfl⟩ := hxd
  have hg3 : g ^ 3 = 1 := e6InndiagConj_injective K hK4 (by rw [map_pow, map_one]; exact hx3)
  have hg1 : (g : ModGL Tag.E6 K) ≠ 1 := fun h1 => hxinn (by
    have : g = 1 := Subtype.ext h1
    rw [this, map_one]
    exact (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  set L := AlgebraicClosure K
  set ι : K →+* L := algebraMap K L
  have hroot : ∀ c : Kˣ, ∃ u : Lˣ, u ^ 3 = Units.map ι.toMonoidHom c := by
    intro c
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι c) (n := 3) (by norm_num)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hz
      exact c.ne_zero (ι.injective (hz.symm.trans (map_zero ι).symm))
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  have hgL : baseChangeGL ι (g : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 L :=
    map_e6InndiagGL_le ι hroot (Subgroup.mem_map_of_mem _ g.2)
  exact noL34Layer_exc_inner_untw_of (Or.inr (Or.inr (Or.inl rfl))) hTwoD hExc hℓ h5 hf hK
    (single_edge_perfect Tag.E6 K (Or.inr (Or.inr (Or.inl rfl)))) (e6InndiagConj K g)
    (g : ModGL Tag.E6 K) hgL (fun c => e6InndiagConj_apply g c)
    (by rw [← Subgroup.coe_pow, hg3]; rfl) hg1

end E6Diag

end Glue

end CFSG.HardMathSupport.Dickson.Sec6
