module

public import CFSG.GH74.Filter.Lie.OddSeries
public import CFSG.LieType.Chevalley.OddRootPairSL2
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels

public section

namespace CFSG.GH74.Filter.Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

theorem sl2_vSL_eq_conj {K : Type} [Field K] (c : K) : vSL c = WSL * uSL (-c) * WSL⁻¹ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  change !![1, 0; c, 1] = !![0, 1; -1, 0] * !![1, -c; 0, 1] * Matrix.adjugate !![0, 1; -1, 0]
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_map_uSL {R S : Type} [Field R] [Field S] (f : R →+* S) (c : R) :
    Matrix.SpecialLinearGroup.map f (uSL c) = uSL (f c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL]

theorem sl2_map_WSL {R S : Type} [Field R] [Field S] (f : R →+* S) :
    Matrix.SpecialLinearGroup.map f (WSL : SL2 R) = WSL := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [WSL]

theorem sl2_map_injective {R S : Type} [Field R] [Field S] (f : R →+* S) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) f) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have := congrArg (fun M : SL2 S => (M : Matrix (Fin 2) (Fin 2) S) i j) h
  simpa [Matrix.SpecialLinearGroup.map] using f.injective this

section Prime

variable {K : Type} [Field K]

noncomputable def primeRootSL2
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    SL2 (ZMod p) →* adjointGroup TwistTag.E6.tag K :=
  ((simpleRootSL2 TwistTag.E6.tag K e6Fix).comp
    (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl p) K))).codRestrict _
    fun _ => simpleRootSL2_mem_adjointGroup e6Fix _

theorem primeRootSL2_uSL
    (p : ℕ) [Fact p.Prime] [CharP K p] (c : ZMod p) :
    primeRootSL2 (K := K) p (uSL c) = xElement e6Fix (ZMod.castHom (dvd_refl p) K c) := by
  apply Subtype.ext
  change simpleRootSL2 _ K e6Fix (Matrix.SpecialLinearGroup.map _ (uSL c)) = _
  rw [sl2_map_uSL, simpleRootSL2_uSL]
  rfl

theorem primeRootSL2_WSL
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    primeRootSL2 (K := K) p WSL = weylElement TwistTag.E6.tag K e6Fix := by
  apply Subtype.ext
  change simpleRootSL2 _ K e6Fix (Matrix.SpecialLinearGroup.map _ WSL) = _
  rw [sl2_map_WSL, simpleRootSL2_WSL]
  rfl

theorem primeRootSL2_injective
    (p : ℕ) [Fact p.Prime] [CharP K p] (hK : ringChar K ≠ 2) :
    Function.Injective (primeRootSL2 (K := K) p) := fun _ _ h =>
  sl2_map_injective (ZMod.castHom (dvd_refl p) K)
    (simpleRootSL2_injective hK e6Fix (congrArg Subtype.val h))

theorem primeRootSL2_mem_twistDerived
    {p : ℕ} [Fact p.Prime] [CharP K p] (σ : K →+* K)
    (A : SL2 (ZMod p)) : primeRootSL2 p A ∈ twistDerived .E6 K σ := by
  have hu : ∀ c, primeRootSL2 (K := K) p (uSL c) ∈ twistDerived .E6 K σ := fun c => by
    rw [primeRootSL2_uSL]
    exact e6_xElement_three_mem (ringHom_zmod_cast σ c)
  have hn : weylElement TwistTag.E6.tag K e6Fix ∈ twistFixed .E6 K σ := by
    rw [mem_twistFixed, twistC_weylElement, e6Fix_perm]
  have hv : ∀ c, primeRootSL2 (K := K) p (vSL c) ∈ twistDerived .E6 K σ := fun c => by
    rw [sl2_vSL_eq_conj, map_mul, map_mul, map_inv, primeRootSL2_WSL]
    exact conj_mem_twistDerived hn (hu (-c))
  have hle : (⊤ : Subgroup (SL2 (ZMod p))) ≤
      (twistDerived .E6 K σ).comap (primeRootSL2 (K := K) p) := by
    rw [← sl2_closure_upper_lower]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hu c
    · exact hv c
  exact hle (Subgroup.mem_top A)

end Prime

section Q8

variable {K : Type} [Field K]

noncomputable def e6w
    (k : Fin 4) : WeylGroup TwistTag.E6.tag :=
  (coxeterSystem TwistTag.E6.tag).wordProd (e6FixWords k)

theorem e6w_fixed
    (k : Fin 4) : weylTwist .E6 (e6w k) = e6w k :=
  weylTwist_wordProd_eq (e6_fixWords_check k)

theorem e6w_smul
    (k : Fin 4) :
    e6w k • (Pi.single e6Fix 1 : Fin TwistTag.E6.tag.rank → ℤ) = e6Vec k := by
  rw [e6w, wordProd_smul]

noncomputable def q8E6
    {p : ℕ} [Fact p.Prime] [CharP K p] {a b : ZMod p}
    (h : a ^ 2 + b ^ 2 = -1) (k : Fin 4) : QuaternionGroup 2 →* adjointGroup TwistTag.E6.tag K :=
  (MulAut.conj (nrep TwistTag.E6.tag K (e6w k))).toMonoidHom.comp
    ((primeRootSL2 p).comp (quatHom h))

theorem q8E6_mem_twistDerived
    {p : ℕ} [Fact p.Prime] [CharP K p] {a b : ZMod p}
    (h : a ^ 2 + b ^ 2 = -1) (σ : K →+* K) (k : Fin 4) (g : QuaternionGroup 2) :
    q8E6 (K := K) h k g ∈ twistDerived .E6 K σ :=
  conj_mem_twistDerived (nrep_mem_twistFixed' (e6w_fixed k))
    (primeRootSL2_mem_twistDerived σ _)

theorem q8E6_injective
    {p : ℕ} [Fact p.Prime] [CharP K p] {a b : ZMod p} (h : a ^ 2 + b ^ 2 = -1)
    (hZ : ringChar (ZMod p) ≠ 2) (hK : ringChar K ≠ 2) (k : Fin 4) :
    Function.Injective (q8E6 (K := K) h k) :=
  (MulAut.conj (nrep TwistTag.E6.tag K (e6w k))).injective.comp
    ((primeRootSL2_injective p hK).comp (quatHom_injective hZ h))

theorem q8E6_mem_rootRankOneGroup
    {p : ℕ} [Fact p.Prime] [CharP K p] {a b : ZMod p}
    (h : a ^ 2 + b ^ 2 = -1) (k : Fin 4) (hk : IsRoot TwistTag.E6.tag (e6Vec k))
    (g : QuaternionGroup 2) :
    (q8E6 (K := K) h k g).1 ∈ rootRankOneGroup TwistTag.E6.tag K (e6Vec k) := by
  set B := Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl p) K) (quatHom h g)
  have h1 : simpleRootSL2 TwistTag.E6.tag K e6Fix B ∈ Subgroup.closure
      (Set.range (xUnit TwistTag.E6.tag K e6Fix) ∪ Set.range (yUnit TwistTag.E6.tag K e6Fix)) := by
    rw [← range_simpleRootSL2]
    exact ⟨B, rfl⟩
  have h2 := Subgroup.mem_map_of_mem
    (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K (e6w k))).toMonoidHom h1
  rw [map_conj_canonicalRep_closure_xUnit_yUnit (e6w_smul k)] at h2
  rw [(exceptional_Lang_root_rank_one_torus_transport TwistTag.E6.tag K hk).1]
  exact h2

theorem e6Vec_stronglyOrth : ∀ k l : Fin 3, k ≠ l →
    stronglyOrthB TwistTag.E6.tag (e6Vec k.castSucc) (e6Vec l.castSucc) = true := by
  decide +kernel

theorem q8E6_commute
    {p : ℕ} [Fact p.Prime] [CharP K p] {a b : ZMod p} (h : a ^ 2 + b ^ 2 = -1)
    {k l : Fin 3} (hkl : k ≠ l) (x y : QuaternionGroup 2) :
    Commute (q8E6 (K := K) h k.castSucc x) (q8E6 (K := K) h l.castSucc y) := by
  obtain ⟨hβ, hγ, h0, hp, hm⟩ := stronglyOrthB_spec (e6Vec_stronglyOrth k l hkl)
  refine Subtype.ext ?_
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation TwistTag.E6.tag K hβ hγ
    h0 hp hm _ (q8E6_mem_rootRankOneGroup h k.castSucc hβ x) _
    (q8E6_mem_rootRankOneGroup h l.castSucc hγ y)

end Q8

theorem exists_hom_commutator
    {t : TwistTag} {K : Type} [Field K] {σ : K →+* K} {A : Type*}
    [Group A] (Ψ : A →* adjointGroup t.tag K) (hrange : ∀ a, Ψ a ∈ twistDerived t K σ) :
    ∃ Ψ₂ : A →* commutator (twistFixed t K σ),
      ∀ a, ((Ψ₂ a : twistFixed t K σ) : adjointGroup t.tag K) = Ψ a := by
  have hΓ : ∀ a, Ψ a ∈ twistFixed t K σ := fun a => Subgroup.map_subtype_le _ (hrange a)
  set Ψ₁ : A →* twistFixed t K σ := Ψ.codRestrict _ hΓ
  have hΓ' : ∀ a, Ψ₁ a ∈ commutator (twistFixed t K σ) := fun a => by
    obtain ⟨h, hh, he⟩ := hrange a
    have : Ψ₁ a = h := Subtype.ext he.symm
    rw [this]
    exact hh
  exact ⟨Ψ₁.codRestrict _ hΓ', fun a => rfl⟩

theorem not_gen4_derivedQuotient_twistedE6_odd
    {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (σ : K →+* K) :
    ¬ Gen4 (commutator (twistFixed .E6 K σ) ⧸
      Subgroup.center (commutator (twistFixed .E6 K σ))) := by
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hZ : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  choose ψ hψ using fun k : Fin 3 =>
    exists_hom_commutator (σ := σ) (q8E6 (K := K) hab k.castSucc)
      (q8E6_mem_twistDerived hab σ k.castSucc)
  refine not_gen4_quotient_of_Q8_cube (Subgroup.center _) le_rfl ψ (fun k x y hxy => ?_)
    (fun k l hkl x y => ?_)
  · apply q8E6_injective hab hZ hK k.castSucc
    rw [← hψ k x, ← hψ k y, hxy]
  · have h1 := (q8E6_commute (K := K) hab hkl x y).eq
    rw [← hψ k x, ← hψ l y] at h1
    exact Subtype.ext (Subtype.ext h1)

end CFSG.GH74.Filter.Lie

namespace CFSG.GH74.Filter

open CFSG.GH74.Filter.Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

theorem t_2E6_odd :
    S_2E6_odd := by
  intro G _ _ p f hp2 h
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, _, σ, hK, hσ, hσc, hfr, ⟨u, hu⟩, ⟨e⟩⟩ := twistedModel_data hf hm
  exact not_gen4_of_mulEquiv
    (e.trans (derivedCentralQuotientEquiv _ (twistedFixedGroupEquiv .E6 K σ))).symm
    (not_gen4_derivedQuotient_twistedE6_odd hp2 σ)

end CFSG.GH74.Filter
