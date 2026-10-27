module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFourCocycle
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFourModel
public import CFSG.HardMathSupport.Cooperstein.Proving.TwoCoreInf
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.NaturalSectionLS

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open Equiv Equiv.Perm CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM blockV)
open CFSG.QuasithinUnique (IsShort2)
open CFSG.RankThree.PartTwo (IsTypeScriptL)

theorem nonempty_quotientCenter_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : Subgroup.center B = ⊥) : Nonempty (A ⧸ Subgroup.center A ≃* B) := by
  have hA : Subgroup.center A = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center B := by
      rw [Subgroup.mem_center_iff]
      intro b
      obtain ⟨a, rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz a]
    rw [hB, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hz', map_one])
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hA).trans (QuotientGroup.quotientBot.trans e)⟩

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem eightBlockData_four_false (hnat : GF2NaturalLSL) (hX : CFSG.Open.IsKGroup ↥X)
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    {N s : ℕ} (hs : 1 ≤ s) (hNs : N = 8 + s) (D : EightBlockData X S L 4 s) : False := by
  classical
  obtain ⟨ψ, hψN, -⟩ := D
  have hcardΩ : Fintype.card (OmegaE 4 s) = N := by
    simp only [OmegaE, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  have hcore := inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL
  have he : Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
      ↥(alternatingGroup (Fin N))) :=
    nonempty_quotientCenter_equiv
      (((Proving.barMEquiv hL.le le_sup_left hcore).symm.trans ψ).trans
        (Equiv.altCongrHom (Fintype.equivFinOfCardEq hcardΩ)))
      (alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega))
  rcases hnat G X S L hX hA hL hSL N (Or.inr (by omega)) he with hns | ⟨h7, -⟩
  swap
  · omega
  obtain ⟨π, θ, hπ, hker, hAθ, hequiv, hf⟩ := hns
  set ι : ↥L →* ↥(L ⊔ S) := Subgroup.inclusion le_sup_left with hι
  have hAθ' : ∀ σ ∈ alternatingGroup (Fin N), ∃ l : ↥L, θ (ι l) = σ := hAθ
  have hLA : ∀ l : ↥L, θ (ι l) ∈ alternatingGroup (Fin N) := theta_mem_alternatingGroup hL.perfect θ
  set θA : ↥L →* ↥(alternatingGroup (Fin N)) := (θ.comp ι).codRestrict _ hLA with hθA
  have hkerA : (Proving.barMHomSub hL.le).ker ≤ θA.ker := by
    intro l hl
    rw [Proving.ker_barMHomSub, Subgroup.mem_subgroupOf] at hl
    have hlc : ((ι l : ↥(L ⊔ S)) : G) ∈ Subgroup.centralizer (blockV S L : Set G) :=
      pCoreOf_le_centralizer_blockV hA hL (hL.toIsTwoPrimeComponent.inf_twoCore.le ⟨l.2, hl⟩)
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (theta_eq_one_of_centralizes (by omega) hπ hequiv hlc)
  let q := QuotientGroup.quotientKerEquivOfSurjective _ (Proving.barMHomSub_surjective hL.le)
  let θbar : ↥(barM X L) →* ↥(alternatingGroup (Fin N)) :=
    (QuotientGroup.lift _ θA hkerA).comp q.symm.toMonoidHom
  have hθbar : ∀ l : ↥L, θbar (Proving.barMHomSub hL.le l) = θA l := by
    intro l
    have h1 : q.symm (Proving.barMHomSub hL.le l) =
        (QuotientGroup.mk l : ↥L ⧸ (Proving.barMHomSub hL.le).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift _ θA hkerA (q.symm (Proving.barMHomSub hL.le l)) = θA l
    rw [h1, QuotientGroup.lift_mk]
  have hsurj : Function.Surjective θbar := by
    intro σ
    obtain ⟨l, hl⟩ := hAθ' σ σ.2
    exact ⟨Proving.barMHomSub hL.le l, by rw [hθbar]; exact Subtype.ext hl⟩
  have hbij : Function.Bijective θbar := hsurj.bijective_of_nat_card_le
    (Nat.card_congr (ψ.toEquiv.trans
      (Equiv.altCongrHom (Fintype.equivFinOfCardEq hcardΩ)).toEquiv)).le
  obtain ⟨ε, hε⟩ := exists_equiv_of_altEquiv (by omega) (by omega) hcardΩ
    (ψ.symm.trans (MulEquiv.ofBijective θbar hbij))
  have hkey : ∀ (l : ↥L) (ω : OmegaE 4 s),
      θ (ι l) (ε ω) = ε (((ψ (Proving.barMHomSub hL.le l) : AltE 4 s) : Perm (OmegaE 4 s)) ω) := by
    intro l ω
    have h1 := hε (ψ (Proving.barMHomSub hL.le l)) ω
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.ofBijective_apply, hθbar] at h1
    exact h1
  let Δ' : Finset (Fin N) := Finset.univ.image (fun x : Fin 4 × Bool => ε (Sum.inl x))
  have hΔcard : Δ'.card = 8 := by
    rw [Finset.card_image_of_injective _ (fun x y h => Sum.inl_injective (ε.injective h))]
    simp
  have hout : ∀ i : Fin N, i ∉ Δ' → ∃ j : Fin s, i = ε (Sum.inr j) := by
    intro i hi
    rcases h : ε.symm i with x | j
    · exact absurd (Finset.mem_image.2 ⟨x, Finset.mem_univ _, by rw [← h, ε.apply_symm_apply]⟩) hi
    · exact ⟨j, by rw [← h, ε.apply_symm_apply]⟩
  have hin : ∀ i ∈ Δ', ∃ x : Fin 4 × Bool, i = ε (Sum.inl x) := by
    intro i hi
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hi
    exact ⟨x, rfl⟩
  have hΓ : ∃ k : Fin N, k ∉ Δ' := by
    refine ⟨ε (Sum.inr ⟨0, by omega⟩), fun h => ?_⟩
    obtain ⟨x, hx⟩ := hin _ h
    exact Sum.inr_ne_inl (ε.injective hx)
  have hBC : barM X (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM X L := barM_mono inf_le_right
  let Ψ : ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* ↥(pTilde (Fin 4) (Fin s)) :=
    (sectionEquiv hBC ψ (eightN 4 s) hψN).trans (eightEquiv 4 s)
  have hspec : ∀ b : ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L)),
      Perm.sumCongr (Ψ b).1.1 (Ψ b).1.2 = ((ψ ⟨b.1, hBC b.2⟩ : AltE 4 s) : Perm (OmegaE 4 s)) :=
    fun b => eightEquiv_spec (sectionEquiv hBC ψ (eightN 4 s) hψN b)
  have hpc : barM X (S ⊓ L) =
      (CFSG.pCore 2 ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L))).map
        (barM X (Subgroup.normalizer (S : Set G) ⊓ L)).subtype := by
    rw [Proving.barM_inf_eq_pCoreOf_barM hA hL.toIsTwoPrimeComponent]
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
  let f : ↥(pTilde (Fin 4) (Fin s)) →* Perm (Fin N) :=
    ε.permCongrHom.toMonoidHom.comp ((Perm.sumCongrHom _ _).comp (pTilde (Fin 4) (Fin s)).subtype)
  have hf_apply : ∀ (p : ↥(pTilde (Fin 4) (Fin s))) (ω : OmegaE 4 s),
      f p (ε ω) = ε (Perm.sumCongr p.1.1 p.1.2 ω) := by
    intro p ω
    show ε ((Perm.sumCongr p.1.1 p.1.2) (ε.symm (ε ω))) = _
    rw [ε.symm_apply_apply]
  set P : Subgroup (Perm (Fin N)) := (pTildeKlein (Fin s)).map f with hP
  have hPS : ∀ p ∈ P, ∃ l : ↥L, (l : G) ∈ S ∧ θ (ι l) = p := by
    rintro _ ⟨p, hp, rfl⟩
    have hb : Ψ.symm p ∈ CFSG.pCore 2 ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L)) := by
      rw [← CFSG.pCore_map_iso 2 Ψ.symm]
      exact ⟨p, pTildeKlein_le_pCore hp, rfl⟩
    have hbS : ((Ψ.symm p : ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L))) :
        ↥X ⧸ CFSG.pCore 2 ↥X) ∈ barM X (S ⊓ L) := by
      rw [hpc]
      exact ⟨_, hb, rfl⟩
    have hmem : (⟨(Ψ.symm p).1, hBC (Ψ.symm p).2⟩ : ↥(barM X L)) ∈
        (barM X (S ⊓ L)).subgroupOf (barM X L) := hbS
    rw [Proving.subgroupOf_barM_eq_map hL.le inf_le_right] at hmem
    obtain ⟨m, hmSL, hbl⟩ := hmem
    refine ⟨m, (Subgroup.mem_subgroupOf.1 hmSL).1, ?_⟩
    refine Equiv.ext fun i => ?_
    obtain ⟨ω, rfl⟩ := ε.surjective i
    rw [hkey, hbl, ← hspec, Ψ.apply_symm_apply, hf_apply]
  have hPfix : ∀ p ∈ P, ∀ i : Fin N, i ∉ Δ' → p i = i := by
    rintro _ ⟨p, hp, rfl⟩ i hi
    obtain ⟨j, rfl⟩ := hout i hi
    rw [hf_apply, ((mem_pTildeKlein_iff p).1 hp).2]
    rfl
  have hPtrans : ∀ i ∈ Δ', ∀ j ∈ Δ', ∃ p ∈ P, p i = j := by
    intro i hi j hj
    obtain ⟨x, rfl⟩ := hin i hi
    obtain ⟨y, rfl⟩ := hin j hj
    obtain ⟨p, hp, hpxy⟩ := exists_mem_pTildeKlein_apply (Γ := Fin s) x y
    refine ⟨f p, ⟨p, hp, rfl⟩, ?_⟩
    rw [hf_apply, Perm.sumCongr_apply, Sum.map_inl, hpxy]
  obtain ⟨l, hl⟩ := Proving.barMHomSub_surjective hL.le (ψ.symm (cycE s))
  have hlfix : ∀ i : Fin N, i ∉ Δ' → θ (ι l) i = i := by
    intro i hi
    obtain ⟨j, rfl⟩ := hout i hi
    rw [hkey, hl, MulEquiv.apply_symm_apply, cycE_apply_inr]
  have hvS : ∀ v ∈ CFSG.Quasithin.omegaOneCenterOf S, ∀ t ∈ S, t * v = v * t := by
    intro v hv t ht
    have hvC : v ∈ Subgroup.centralizer (S : Set G) :=
      ((Subgroup.closure_le _).2 (fun x hx => hx.1.2) :
        CFSG.Quasithin.omegaOneCenterOf S ≤ Subgroup.centralizer (S : Set G)) hv
    exact Subgroup.mem_centralizer_iff.1 hvC t ht
  have hcent : ∀ v ∈ CFSG.Quasithin.omegaOneCenterOf S, (l : G) * v * (l : G)⁻¹ = v :=
    fun v hv => conj_eq_of_fix (by omega) hker hAθ' hequiv hf hLA Δ' (by omega) hΓ P hPS hPfix
      hPtrans (omegaOneCenterOf_le_blockV hA hL hSL hv) (hvS v hv) l hlfix
  have hlN : (l : G) ∈ Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hcent h hh]
      exact hh
    · intro hh
      have h2 := hcent _ hh
      have h3 : (l : G) * h * (l : G)⁻¹ = h := by
        calc (l : G) * h * (l : G)⁻¹ =
            (l : G)⁻¹ * ((l : G) * ((l : G) * h * (l : G)⁻¹) * (l : G)⁻¹) * (l : G) := by group
          _ = (l : G)⁻¹ * ((l : G) * h * (l : G)⁻¹) * (l : G) := by rw [h2]
          _ = h := by group
      rwa [h3] at hh
  have hlNS : (l : G) ∈ Subgroup.normalizer (S : Set G) := by
    have hle : X ⊓ Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf S : Set G) ≤
        CFSG.Quasithin.cgsIn X S :=
      le_iSup_of_le (CFSG.Quasithin.omegaOneCenterOf S)
        (le_iSup_of_le (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le S)
          (le_iSup_of_le (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot
            hA.twoRadical.isPGroup hA.twoRadical.2.1)
            (le_iSup_of_le (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf S) le_rfl)))
    rw [hA.cgs] at hle
    exact (hle ⟨hL.le l.2, hlN⟩).2
  apply cycE_not_mem_eightN s
  rw [← hψN]
  refine ⟨ψ.symm (cycE s), ?_, by simp⟩
  rw [← hl, Proving.subgroupOf_barM_eq_map hL.le inf_le_right]
  exact ⟨l, ⟨hlNS, l.2⟩, rfl⟩

theorem eightFourExcluded_of_pos (hnat : GF2NaturalLSL) :
    ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
      Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
      ∀ N : ℕ, 1 ≤ N - 2 * 4 →
        ¬ (EightBlockData X S L 4 (N - 2 * 4) ∧ IsShort2 L ∧ IsTypeScriptL L) := by
  intro G _ _ X S L hX hA hL hSL N hN h
  exact eightBlockData_four_false (N := N) hnat hX hA hL hSL hN (by omega) h.1

theorem eightFourExcluded_large (hnat : AlternatingGeometry.GF2NaturalLSL) :
    ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
      Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
      ∀ N : ℕ, 6 ≤ N - 2 * 4 →
        ¬ (AlternatingGeometry.EightBlockData X S L 4 (N - 2 * 4) ∧ IsShort2 L ∧
          IsTypeScriptL L) := by
  intro G _ _ X S L hX hA hL hSL N hN
  exact eightFourExcluded_of_pos hnat G X S L hX hA hL hSL N (by omega)

end CFSG.HardMathSupport.Cooperstein.Coordinator
