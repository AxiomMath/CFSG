module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwWeyl
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.E8Tw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHigh.E8Layer CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {K L : Type} [Field K] [Field L]

@[expose] def twN (b : Fin Tag.E8.rank → Lˣ) : ModGL Tag.E8 L :=
  rootDiagUnit Tag.E8 b * canonicalRep (coxeterSystem Tag.E8) L tw8W

theorem twN_conj (b : Fin Tag.E8.rank → Lˣ) (X : ModGL Tag.E8 L) :
    twN b * X * (twN b)⁻¹ =
      rootDiagUnit Tag.E8 b * (canonicalRep (coxeterSystem Tag.E8) L tw8W * X *
        (canonicalRep (coxeterSystem Tag.E8) L tw8W)⁻¹) * (rootDiagUnit Tag.E8 b)⁻¹ := by
  simp only [twN, mul_inv_rev, mul_assoc]

theorem rootChar_single_E8 (b : Fin Tag.E8.rank → Lˣ) (j : Fin Tag.E8.rank) :
    rootChar b (Pi.single j 1) = b j := by
  simpa using rootChar_nsmul_single b j 1

theorem exists_sign_e8Par (ι : K →+* L) :
    ∃ s : (Fin Tag.E8.rank → ℤ) → L, (∀ α, s α * s α = 1) ∧ (∀ (Fr : L →+* L) α, Fr (s α) = s α) ∧
      ∀ {α : Fin Tag.E8.rank → ℤ}, IsRoot Tag.E8 α → ∀ c : K,
        baseChangeGL ι ((e8Par K α c : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K) =
          pinnedX Tag.E8 L α (s α * ι c) :=
  ⟨fun α => ((rootOperatorFamily Tag.E8).pinnedFamilySign α : L),
    fun α => (rootOperatorFamily Tag.E8).pinnedFamilySign_mul_self L α,
    fun Fr _ => map_intCast Fr _,
    fun hα c => by
      rw [CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hα, baseChangeGL_pinnedX, map_mul,
        map_intCast]⟩

theorem exists_twN_equivariant (ι : K →+* L) (θ : K →+* K) (Fr : L →+* L)
    (hFr : ∀ c, Fr (ι c) = ι (θ c))
    (Ψ : ↥(e6Data_valid.minGroup K) →* ↥(adjointGroup Tag.E8 K))
    (hΨ : ∀ (k : Fin 6) (c : K),
      Ψ (e6Data_valid.xm K (Pi.single k 1) c) = e8Par K (Pi.single (e8E6Node k) 1) c ∧
      Ψ (e6Data_valid.xm K (-Pi.single k 1) c) = e8Par K (-Pi.single (e8E6Node k) 1) c) :
    ∃ b : Fin Tag.E8.rank → Lˣ, ∀ x : ↥(e6Data_valid.minGroup K),
      baseChangeGL ι ((Ψ (CFSG.LieType.Steinberg.TwistedE6.sigma K θ x) : ↥(adjointGroup Tag.E8 K)) :
          ModGL Tag.E8 K) =
        twN b * Units.map (entrywiseHom Fr)
          (baseChangeGL ι ((Ψ x : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K)) * (twN b)⁻¹ := by
  classical
  obtain ⟨s, hs, hsF, hsc⟩ := exists_sign_e8Par (K := K) ι
  have hΨ' : ∀ (k : Fin (Tag.rank .E6)) (c : K),
      Ψ (e6Data_valid.xm K (Pi.single k 1) c) = e8Par K (Pi.single (e8E6Node k) 1) c ∧
      Ψ (e6Data_valid.xm K (-Pi.single k 1) c) = e8Par K (-Pi.single (e8E6Node k) 1) c :=
    fun k c => hΨ k c
  have htw : ∀ k : Fin (Tag.rank .E6),
      tw8W • (Pi.single (e8E6Node k) 1 : Fin Tag.E8.rank → ℤ) =
        Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1 :=
    fun k => tw8W_smul_e6 k
  have htw' : ∀ k : Fin (Tag.rank .E6),
      tw8W • (-Pi.single (e8E6Node k) 1 : Fin Tag.E8.rank → ℤ) =
        -Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1 :=
    fun k => tw8W_smul_neg_e6 k
  have hF : ∀ {α : Fin Tag.E8.rank → ℤ}, IsRoot Tag.E8 α → ∀ c : K,
      Units.map (entrywiseHom Fr) (baseChangeGL ι
        ((e8Par K α c : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K)) =
        pinnedX Tag.E8 L α (s α * ι (θ c)) := fun hα c => by
    rw [hsc hα, units_map_entrywiseHom_pinnedX, map_mul, hsF, hFr]
  choose ε hε hεc using fun k : Fin (Tag.rank .E6) =>
    exists_canonicalRep_mul_pinnedX_mul_inv L tw8W (isRoot_single Tag.E8 (e8E6Node k))
  choose ε' hε' hε'c using fun k : Fin (Tag.rank .E6) =>
    exists_canonicalRep_mul_pinnedX_mul_inv L tw8W (isRoot_neg_single Tag.E8 (e8E6Node k))
  let v : Fin (Tag.rank .E6) → L := fun k =>
    s (Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1) * ε k *
      s (Pi.single (e8E6Node k) 1)
  have hv : ∀ k, v k * v k = 1 := fun k => by
    have h1 := hs (Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1)
    have h2 := hs (Pi.single (e8E6Node k) 1)
    have h3 := hε k
    simp only [v]
    linear_combination (ε k * ε k * (s (Pi.single (e8E6Node k) 1) *
      s (Pi.single (e8E6Node k) 1))) * h1 + (s (Pi.single (e8E6Node k) 1) *
        s (Pi.single (e8E6Node k) 1)) * h3 + h2
  let u : Fin (Tag.rank .E6) → Lˣ := fun k => Units.mkOfMulEqOne (v k) (v k) (hv k)
  have hinj : Function.Injective
      (fun k : Fin (Tag.rank .E6) => e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) := by
    decide
  let b : Fin Tag.E8.rank → Lˣ :=
    Function.extend (fun k : Fin (Tag.rank .E6) => e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) u 1
  have hb : ∀ k, b (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) = u k :=
    fun k => hinj.extend_apply u 1 k
  refine ⟨b, fun x => ?_⟩
  let G₁ : ↥(e6Data_valid.minGroup K) →* ModGL Tag.E8 L :=
    (baseChangeGL ι).comp ((adjointGroup Tag.E8 K).subtype.comp
      (Ψ.comp (CFSG.LieType.Steinberg.TwistedE6.sigma K θ)))
  let G₂ : ↥(e6Data_valid.minGroup K) →* ModGL Tag.E8 L :=
    (MulAut.conj (twN b)).toMonoidHom.comp ((Units.map (entrywiseHom Fr)).comp
      ((baseChangeGL ι).comp ((adjointGroup Tag.E8 K).subtype.comp Ψ)))
  have hG₁ : ∀ y, G₁ y = baseChangeGL ι ((Ψ (CFSG.LieType.Steinberg.TwistedE6.sigma K θ y) :
      ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K) := fun _ => rfl
  have hG₂ : ∀ y, G₂ y = twN b * Units.map (entrywiseHom Fr)
      (baseChangeGL ι ((Ψ y : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K)) * (twN b)⁻¹ :=
    fun _ => rfl
  have e0 : ∀ (k : Fin (Tag.rank .E6)) (c : K), G₁ (e6Data_valid.xm K (Pi.single k 1) c) =
      pinnedX Tag.E8 L (Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1)
        (s (Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1) * ι (θ c)) := by
    intro k c
    rw [hG₁, CFSG.LieType.Steinberg.TwistedE6.sigma_xm_single, (hΨ' _ _).1,
      hsc (isRoot_single _ _)]
  have hpos : ∀ (k : Fin (Tag.rank .E6)) (c : K), G₁ (e6Data_valid.xm K (Pi.single k 1) c) =
      G₂ (e6Data_valid.xm K (Pi.single k 1) c) := by
    intro k c
    rw [e0, hG₂, (hΨ' _ _).1, hF (isRoot_single _ _), twN_conj, hεc, htw,
      rootDiagUnit_conj_pinnedX b (isRoot_single _ _), rootChar_single_E8, hb]
    congr 1
    simp only [u, v, Units.val_mkOfMulEqOne]
    linear_combination (-(s (Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1) *
      ι (θ c) * (s (Pi.single (e8E6Node k) 1) * s (Pi.single (e8E6Node k) 1)))) * hε k +
      (-(s (Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1) * ι (θ c))) *
        hs (Pi.single (e8E6Node k) 1)
  let B : Fin (Tag.rank .E6) → L := fun k =>
    (rootChar b (-Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1) : L) *
      ε' k * s (-Pi.single (e8E6Node k) 1)
  have e1 : ∀ (k : Fin (Tag.rank .E6)) (c : K), G₁ (e6Data_valid.xm K (-Pi.single k 1) c) =
      pinnedX Tag.E8 L (-Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1)
        (s (-Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1) * ι (θ c)) := by
    intro k c
    rw [hG₁, CFSG.LieType.Steinberg.TwistedE6.sigma_xm_neg_single, (hΨ' _ _).2,
      hsc (isRoot_neg_single _ _)]
  have e2 : ∀ (k : Fin (Tag.rank .E6)) (c : K), G₂ (e6Data_valid.xm K (-Pi.single k 1) c) =
      pinnedX Tag.E8 L (-Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1)
        (B k * ι (θ c)) := by
    intro k c
    rw [hG₂, (hΨ' _ _).2, hF (isRoot_neg_single _ _), twN_conj, hε'c, htw',
      rootDiagUnit_conj_pinnedX b (isRoot_neg_single _ _)]
    congr 1
    simp only [B]
    ring
  have hB : ∀ k : Fin (Tag.rank .E6),
      s (-Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1) = B k := by
    intro k
    obtain ⟨jk, -, hju, hjl⟩ := e6Data_valid.exists_sl2Hom K k
    have hR := simpleRootSL2_injective_E8 L (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k))
    have ha : s (Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1) ≠ 0 := by
      intro h
      have h' := hs (Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1)
      rw [h, zero_mul] at h'
      exact zero_ne_one h'
    have r1 := sl2_rigid hR (G₁.comp jk) (ι.comp θ) ha
      (fun c => by
        rw [MonoidHom.comp_apply, hju, e0, simpleRootSL2_uSL, ← pinnedX_single,
          RingHom.comp_apply])
      (fun c => by
        rw [MonoidHom.comp_apply, hjl, e1, simpleRootSL2_vSL, ← pinnedX_neg_single,
          RingHom.comp_apply])
    have r2 := sl2_rigid hR (G₂.comp jk) (ι.comp θ) ha
      (fun c => by
        rw [MonoidHom.comp_apply, hju, ← hpos, e0, simpleRootSL2_uSL, ← pinnedX_single,
          RingHom.comp_apply])
      (fun c => by
        rw [MonoidHom.comp_apply, hjl, e2, simpleRootSL2_vSL, ← pinnedX_neg_single,
          RingHom.comp_apply])
    exact mul_left_cancel₀ ha (r1.trans r2.symm)
  have key : G₁ = G₂ := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LieType.Steinberg.Isogeny.closure_xm_simple_eq_top e6Data_valid K) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · exact hpos i c
    · rw [e1 i c, e2 i c, hB i]
  exact DFunLike.congr_fun key x

end CFSG.LieType.SeitzGeneration.ExcHigh.E8Tw
