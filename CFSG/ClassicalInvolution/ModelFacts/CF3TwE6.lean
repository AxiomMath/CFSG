module

public import CFSG.ClassicalInvolution.ModelFacts.CF3TwE6A
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairF4
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedE6Frame
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwE6Comm
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwE6Roots

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Asc77.T3CII (ne_two_of_pow_eq_three)


section Main

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Adjoint CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {p e : ℕ} [Fact p.Prime]

section Group

variable {G : Type*} [Group G]

theorem conj_mul_conj_eq3 (g x c : G) (hx : x * (g⁻¹ * c * g) = (g⁻¹ * c * g) * x) :
    (g * x)⁻¹ * c * (g * x) = g⁻¹ * c * g := by
  calc (g * x)⁻¹ * c * (g * x) = x⁻¹ * ((g⁻¹ * c * g) * x) := by group
    _ = x⁻¹ * (x * (g⁻¹ * c * g)) := by rw [hx]
    _ = g⁻¹ * c * g := by group

theorem conj_triple_eq3 (g y x : G) :
    g * (y * x * y⁻¹) * g⁻¹ = g * y * x * (g * y)⁻¹ := by group

theorem conj_mul_mul_eq3 (g c₁ c₂ : G) :
    g⁻¹ * (c₁ * c₂) * g = (g⁻¹ * c₁ * g) * (g⁻¹ * c₂ * g) := by group

end Group

theorem rankOneRoot_le_of_signs_twistedE63 (hp2 : p ≠ 2) (he : 1 ≤ e) (hq3 : p ^ e = 3)
    {g : twistedE6Group p e} {cs : Fin 3 → twistedE6Group p e}
    {bs : Fin 3 → Fin (Tag.rank .F4) → (AlgebraicClosure (GaloisField p (2 * e)))ˣ}
    (hbs : ∀ i j, bs i j = 1 ∨ bs i j = -1)
    (hcs : ∀ i, twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) (g⁻¹ * cs i * g) =
      rootDiagUnit TwistTag.E6.tag (fun l => bs i (orbitMap l)))
    (htri : ∀ γ : Fin (Tag.rank .F4) → ℤ, ∃ i, rootChar (bs i) γ = 1)
    {H : Subgroup (twistedE6Group p e)}
    (hgood : ∀ R ∈ Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e),
      (∃ i, R ≤ Subgroup.centralizer ({cs i} : Set (twistedE6Group p e))) → R ≤ H)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    rankOneRoot (twistedE6Datum p e) g γ ≤ H := by
  have hθ : ∀ c, frobQ p e (frobQ p e c) = c := frobQ_frobQ p e he
  have hchar : CharP (AlgebraicClosure (GaloisField p (2 * e))) p :=
    charP_of_injective_algebraMap (algebraMap (GaloisField p (2 * e))
      (AlgebraicClosure (GaloisField p (2 * e)))).injective p
  have hF2 : ringChar (AlgebraicClosure (GaloisField p (2 * e))) ≠ 2 := by
    rw [ringChar.eq (AlgebraicClosure (GaloisField p (2 * e))) p]
    exact hp2
  have hcent : ∀ (i : Fin 3) (x : twistedE6Group p e) (δ : Fin (Tag.rank .F4) → ℤ),
      IsRoot .F4 δ → rootChar (bs i) δ = 1 → x * (g⁻¹ * cs i * g) = (g⁻¹ * cs i * g) * x →
        rankOneRoot (twistedE6Datum p e) (g * x) δ ≤
          Subgroup.centralizer ({cs i} : Set (twistedE6Group p e)) := by
    intro i x δ hδ hχ hx
    refine map_conj_le_centralizer fun r hr => ?_
    have hu : (g * x)⁻¹ * cs i * (g * x) = g⁻¹ * cs i * g := conj_mul_conj_eq3 g x (cs i) hx
    rw [hu]
    exact twistedE6_commute_of_phi_sign3 he hq3 (hcs i) hδ hχ r hr
  have hmemF : ∀ (x : twistedE6Group p e) (δ : Fin (Tag.rank .F4) → ℤ), IsRoot .F4 δ →
      iform δ δ = 4 → rankOneRoot (twistedE6Datum p e) x δ ∈
        Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e) :=
    fun x δ hδ h => ⟨x, δ, Or.inl (isLongestRoot_twistedDatum_of_iform_eq_four (frobQ p e) hδ h),
      rfl⟩
  have hlong : ∀ δ, IsRoot .F4 δ → iform δ δ = 4 → rankOneRoot (twistedE6Datum p e) g δ ≤ H := by
    intro δ hδ hl
    obtain ⟨i, hi⟩ := htri δ
    have h1 := hcent i 1 δ hδ hi (by rw [one_mul, mul_one])
    rw [mul_one] at h1
    exact hgood _ (hmemF g δ hδ hl) ⟨i, h1⟩
  set N : Subgroup (twistedE6Group p e) := H.comap (MulAut.conj g).toMonoidHom with hN
  have hlongN : ∀ δ, IsRoot .F4 δ → iform δ δ = 4 →
      ∀ x ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) δ, x ∈ N := by
    intro δ hδ hl x hx
    exact hlong δ hδ hl (Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hx))
  have hshortN : ∀ s', IsRoot .F4 s' → iform s' s' ≠ 4 →
      ∀ x ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) s', x ∈ N := by
    intro s' hs' hl x hx
    obtain ⟨i, hi⟩ := htri s'
    have hi' : maskPairing (signTupleBits (bs i)) s' % 2 = 0 :=
      (rootChar_eq_one_iff_mod_two hF2 (hbs i) s').1 hi
    obtain ⟨a, b, ha, hb, hρb, hρa, hproj, hmb, hab, hγ⟩ := exists_e6_lift_of_short_root hs' hl hi'
    have hχb : rootChar (bs i) (proj b) = 1 :=
      (rootChar_eq_one_iff_mod_two hF2 (hbs i) _).2 hmb
    have hχa : rootChar (bs i) (proj a) = 1 := by
      have h := rootChar_add (bs i) (proj a) (proj b)
      rw [← map_add, hproj, hi, hχb, mul_one] at h
      exact h.symm
    have hlb : iform (proj b) (proj b) = 4 := iform_proj_eq_four_of_rho_eq hb hρb
    have hργ := twistedE6_rho_add_rho_add_of_fixed (a := a) hρb
    have hlγ : iform (proj (a + rho a + b)) (proj (a + rho a + b)) = 4 :=
      iform_proj_eq_four_of_rho_eq hγ hργ
    have hχγ : rootChar (bs i) (proj (a + rho a + b)) = 1 := by
      rw [map_add, map_add, proj_rho, rootChar_add, rootChar_add, hχa, hχb]
      simp
    have hX : xFixed (frobQ p e) hb hρb 1 (map_one _) ∈ N :=
      hlongN (proj b) (isRoot_proj hb) hlb _ (xFixed_mem (frobQ p e) hb hρb _ _)
    have hγN : ∀ (g₀ : GaloisField p (2 * e)) (hg₀ : frobQ p e g₀ = g₀),
        xFixed (frobQ p e) hγ hργ g₀ hg₀ ∈ N := fun g₀ hg₀ =>
      hlongN (proj (a + rho a + b)) (isRoot_proj hγ) hlγ _ (xFixed_mem (frobQ p e) hγ hργ _ _)
    have hconj : ∀ t : GaloisField p (2 * e), xPair (frobQ p e) hθ ha hρa t *
        xFixed (frobQ p e) hb hρb 1 (map_one _) * (xPair (frobQ p e) hθ ha hρa t)⁻¹ ∈ N := by
      intro t
      set yA := xPair (frobQ p e) hθ ha hρa t with hyA
      set xB := xFixed (frobQ p e) hb hρb 1 (map_one _) with hxB
      have hyX : yA ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj a) :=
        xPair_mem (frobQ p e) hθ ha hρa t
      have hxX : xB ∈ twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (proj b) :=
        xFixed_mem (frobQ p e) hb hρb _ _
      have hcomm := (twistedE6_commute_of_phi_sign3 he hq3 (hcs i) (isRoot_proj ha) hχa yA
        (Subgroup.mem_sup_left hyX)).symm
      have h1 := hcent i yA (proj b) (isRoot_proj hb) hχb hcomm
      have h2 := hgood _ (hmemF (g * yA) (proj b) (isRoot_proj hb) hlb) ⟨i, h1⟩
      have h3 := h2 (Subgroup.mem_map_of_mem (MulAut.conj (g * yA)).toMonoidHom
        (Subgroup.mem_sup_left hxX))
      show g * (yA * xB * yA⁻¹) * g⁻¹ ∈ H
      have e' : g * (yA * xB * yA⁻¹) * g⁻¹ = (MulAut.conj (g * yA)).toMonoidHom xB :=
        conj_triple_eq3 g yA xB
      rw [e']
      exact h3
    have key := xPair_mem_of_commutator (frobQ p e) hθ ha hb hρb hρa hab hγ hX hγN hconj
    rw [← hproj] at hx
    obtain ⟨w, hw⟩ := (mem_twistedRootGroup_iff_of_pair (frobQ p e) hab rfl
      (twistedE6_rho_add_ne_of_fixed hρb hρa) x).1 hx
    have hxw : x = xPair (frobQ p e) hθ hab (twistedE6_rho_add_ne_of_fixed hρb hρa) w :=
      Subtype.ext (hw.trans (xPair_val (frobQ p e) hθ hab _ w).symm)
    rw [hxw]
    exact key w
  by_cases hl : iform γ γ = 4
  · exact hlong γ hγ hl
  · show ((twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) γ ⊔
      twistedRootGroup (GaloisField p (2 * e)) (frobQ p e) (-γ))).map
        (MulAut.conj g).toMonoidHom ≤ H
    rw [Subgroup.map_le_iff_le_comap]
    exact sup_le (hshortN γ hγ hl) (hshortN (-γ) (IsRoot.neg hγ) (by rwa [iform_neg_self]))

theorem twistedE6_commutingGeneration3 (hp2 : p ≠ 2) (hq3 : p ^ e = 3)
    (hadm : StatedLieAdmissible .twistedE6 0 p e) :
    ∀ R₁ ∈ Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e),
      ∀ R₂ ∈ Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e),
      ∀ c₁ ∈ R₁, ∀ c₂ ∈ R₂, (∀ r ∈ R₁, c₁ * r = r * c₁) → (∀ r ∈ R₂, c₂ * r = r * c₂) →
        (∀ r ∈ R₁, c₂ * r = r * c₂) → (∀ r ∈ R₂, c₁ * r = r * c₁) →
        (⊤ : Subgroup (twistedE6Group p e)) ≤
          ⨆ R ∈ Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e),
            ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set (twistedE6Group p e)) ∨
              R ≤ Subgroup.centralizer ({c₂} : Set (twistedE6Group p e)) ∨
              R ≤ Subgroup.centralizer ({c₁ * c₂} : Set (twistedE6Group p e))), R := by
  have he : 1 ≤ e := hadm.2.1
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₁₂ hx₂₁
  have hframe : PairFrame (K := twistedE6Group p e) (twistedE6SignGroup 0 p e)
      (Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e)) :=
    twistedE6_pairFrame hadm hp2
  obtain ⟨g, hg₁, hg₂⟩ := hframe R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₁₂ hx₂₁
  obtain ⟨b₁, hb₁, e₁⟩ := hg₁
  obtain ⟨b₂, hb₂, e₂⟩ := hg₂
  have e₁' : twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) (g⁻¹ * c₁ * g) =
      rootDiagUnit TwistTag.E6.tag (fun l => b₁ (orbitMap l)) := e₁
  have e₂' : twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) (g⁻¹ * c₂ * g) =
      rootDiagUnit TwistTag.E6.tag (fun l => b₂ (orbitMap l)) := e₂
  have hchar : CharP (AlgebraicClosure (GaloisField p (2 * e))) p :=
    charP_of_injective_algebraMap (algebraMap (GaloisField p (2 * e))
      (AlgebraicClosure (GaloisField p (2 * e)))).injective p
  have hF2 : ringChar (AlgebraicClosure (GaloisField p (2 * e))) ≠ 2 := by
    rw [ringChar.eq (AlgebraicClosure (GaloisField p (2 * e))) p]
    exact hp2
  let cs : Fin 3 → twistedE6Group p e := ![c₁, c₂, c₁ * c₂]
  let bs : Fin 3 → Fin (Tag.rank .F4) → (AlgebraicClosure (GaloisField p (2 * e)))ˣ :=
    ![b₁, b₂, b₁ * b₂]
  have hbs : ∀ i j, bs i j = 1 ∨ bs i j = -1 := by
    intro i j
    fin_cases i
    · exact hb₁ j
    · exact hb₂ j
    · show (b₁ * b₂) j = 1 ∨ (b₁ * b₂) j = -1
      rcases hb₁ j with h | h <;> rcases hb₂ j with h' | h' <;> simp [h, h']
  have hcs : ∀ i, twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e)))
      (g⁻¹ * cs i * g) = rootDiagUnit TwistTag.E6.tag (fun l => bs i (orbitMap l)) := by
    intro i
    fin_cases i
    · exact e₁'
    · exact e₂'
    · show twistedE6Phi p e (AlgebraicClosure (GaloisField p (2 * e))) (g⁻¹ * (c₁ * c₂) * g) =
        rootDiagUnit TwistTag.E6.tag (fun l => (b₁ * b₂) (orbitMap l))
      rw [conj_mul_mul_eq3 g c₁ c₂, map_mul, e₁', e₂', ← rootDiagUnit_mul]
      rfl
  have htri : ∀ γ : Fin (Tag.rank .F4) → ℤ, ∃ i : Fin 3, rootChar (bs i) γ = 1 := by
    intro γ
    by_cases h1 : rootChar b₁ γ = 1
    · exact ⟨0, h1⟩
    by_cases h2 : rootChar b₂ γ = 1
    · exact ⟨1, h2⟩
    refine ⟨2, ?_⟩
    show rootChar (b₁ * b₂) γ = 1
    rw [rootChar_mul_tuple', (rootChar_eq_one_or_eq_neg_one hF2 hb₁ γ).resolve_left h1,
      (rootChar_eq_one_or_eq_neg_one hF2 hb₂ γ).resolve_left h2]
    simp
  have hgood : ∀ R ∈ Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e),
      (∃ i, R ≤ Subgroup.centralizer ({cs i} : Set (twistedE6Group p e))) →
        R ≤ ⨆ R ∈ Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum p e),
          ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set (twistedE6Group p e)) ∨
            R ≤ Subgroup.centralizer ({c₂} : Set (twistedE6Group p e)) ∨
            R ≤ Subgroup.centralizer ({c₁ * c₂} : Set (twistedE6Group p e))), R := by
    rintro R hR ⟨i, hi⟩
    fin_cases i
    · exact le_iSup₂_of_le R hR (le_iSup_of_le (Or.inl hi) le_rfl)
    · exact le_iSup₂_of_le R hR (le_iSup_of_le (Or.inr (Or.inl hi)) le_rfl)
    · exact le_iSup₂_of_le R hR (le_iSup_of_le (Or.inr (Or.inr hi)) le_rfl)
  have hgen := iSup_rankOneRoot_simple_eq_top .twistedE6 0 p e Fact.out trivial hadm g
  refine (le_of_eq hgen.symm).trans (iSup_le fun k => ?_)
  exact rankOneRoot_le_of_signs_twistedE63 hp2 he hq3 hbs hcs htri hgood
    (isRoot_single .F4 k)

theorem commutingFundamentalGeneration3_twistedE6 {n : ℕ} (hq3 : p ^ e = 3)
    (hadm : StatedLieAdmissible .twistedE6 n p e) :
    CommutingFundamentalGeneration p .twistedE6 n e := by
  obtain rfl : n = 0 := hadm.2.2
  exact twistedE6_commutingGeneration3 (ne_two_of_pow_eq_three hq3) hq3 hadm

end Main

end CFSG.ClassicalInvolution.ModelFacts
