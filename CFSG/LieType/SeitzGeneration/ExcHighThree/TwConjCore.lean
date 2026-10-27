module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.ConjLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwConj
public import CFSG.RankThree.PartOne.KE.CTLang

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix

section TorusLang


theorem exists_torus_lang_tw {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) (w : WeylGroup TwistTag.E6.tag)
    {k : ModGL TwistTag.E6.tag L} (hk : k ∈ torusGroup TwistTag.E6.tag L) :
    ∃ h ∈ torusGroup TwistTag.E6.tag L, h * (canonicalRep (coxeterSystem TwistTag.E6.tag) L w *
      twistHom TwistTag.E6 L Fr h *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)⁻¹)⁻¹ = k := by
  classical
  obtain ⟨γ, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hk
  set M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    LinearMap.toMatrix' (CFSG.LieType.RootSystem.weylAction
      (isFiniteType_cartan TwistTag.E6.tag) w⁻¹) with hM
  have hMw : ∀ u : Fin TwistTag.E6.tag.rank → ℤ, w⁻¹ • u = M *ᵥ u := fun u => by
    rw [smul_def, hM, LinearMap.toMatrix'_mulVec]
  set N : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    Matrix.of fun i => (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) -
      (q : ℤ) • permLattice TwistTag.E6.perm.symm (M *ᵥ Pi.single i 1) with hN
  have hNdet : N.det ≠ 0 := by
    refine det_ne_zero_of_mapMatrix_eq_one hq ?_
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hN, Matrix.of_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, map_sub, map_mul, map_natCast, ZMod.natCast_self, zero_mul,
      sub_zero, Matrix.one_apply, Pi.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  obtain ⟨a, ha⟩ := exists_rootChar_rows_eq hNdet γ
  refine ⟨rootDiagUnit TwistTag.E6.tag a, rootDiagUnit_mem_torusGroup a, ?_⟩
  rw [twistHom_rootDiagUnit_eq, canonicalRep_conj_rootDiagUnit]
  change rootDiagUnitHom TwistTag.E6.tag L a * (rootDiagUnitHom TwistTag.E6.tag L _)⁻¹ =
    rootDiagUnitHom TwistTag.E6.tag L γ
  rw [← map_inv, ← map_mul]
  congr 1
  funext i
  rw [Pi.mul_apply, Pi.inv_apply, ← ha i]
  simp only [weylTuple]
  rw [hMw]
  have e1 := rootChar_units_map_pow (L := L) hFr (fun j => a (TwistTag.E6.perm.symm j))
    (M *ᵥ Pi.single i 1)
  have e2 := rootChar_permLattice a TwistTag.E6.perm.symm ((q : ℤ) • (M *ᵥ Pi.single i 1))
  have e3 : N i = (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) -
      permLattice TwistTag.E6.perm.symm ((q : ℤ) • (M *ᵥ Pi.single i 1)) := rfl
  rw [e1, ← e2, e3, rootChar_sub, CTTorus.rootChar_single]

end TorusLang

section Core


theorem canonicalRep_inv_mul_conj_mem_tw {L : Type} [Field L] [IsAlgClosed L]
    (v u w : WeylGroup TwistTag.E6.tag) :
    ∃ k₀ ∈ torusGroup TwistTag.E6.tag L,
      (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ *
        canonicalRep (coxeterSystem TwistTag.E6.tag) L (v * w * u⁻¹) *
          canonicalRep (coxeterSystem TwistTag.E6.tag) L u =
        k₀ * canonicalRep (coxeterSystem TwistTag.E6.tag) L w := by
  obtain ⟨k₁, hk₁, h₁⟩ := canonicalRep_mul_mem (τ := TwistTag.E6.tag) (R := L) v w
  obtain ⟨k₂, hk₂, h₂⟩ := canonicalRep_mul_mem (τ := TwistTag.E6.tag) (R := L) (v * w * u⁻¹) u
  rw [show v * w * u⁻¹ * u = v * w by group] at h₂
  refine ⟨(canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹ * (k₂ * k₁⁻¹) *
      canonicalRep (coxeterSystem TwistTag.E6.tag) L v,
    canonicalRep_inv_conj_mem_torusGroup v (mul_mem hk₂ (inv_mem hk₁)), ?_⟩
  have h₃ : canonicalRep (coxeterSystem TwistTag.E6.tag) L (v * w) =
      k₁⁻¹ * (canonicalRep (coxeterSystem TwistTag.E6.tag) L v *
        canonicalRep (coxeterSystem TwistTag.E6.tag) L w) := by
    rw [h₁]
    group
  rw [mul_assoc, h₂, h₃]
  group

theorem exists_fixed_conj_into_graphFixed_tw {L : Type} [Field L] [IsAlgClosed L] (p : ℕ)
    [Fact p.Prime] [CharP L p] (e : ℕ) (he : 1 ≤ e) (w v : WeylGroup TwistTag.E6.tag)
    (g0 : ModGL TwistTag.E6.tag L) (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag L)
    (hg0 : twistHom TwistTag.E6 L (iterateFrobenius L p e) g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
    (hw : weylTwist TwistTag.E6 (v * w * (weylTwist TwistTag.E6 v)⁻¹) =
      v * w * (weylTwist TwistTag.E6 v)⁻¹)
    {ι : Type} (d : ι → ModGL TwistTag.E6.tag L) (hd : ∀ s, d s ∈ torusGroup TwistTag.E6.tag L)
    (hv : ∀ s, diagramMap TwistTag.E6 L *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v * d s *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) * (diagramMap TwistTag.E6 L)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L v * d s *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) :
    ∃ h ∈ adjointGroup TwistTag.E6.tag L,
      twistHom TwistTag.E6 L (iterateFrobenius L p e) h = h ∧
      ∀ s, h⁻¹ * (g0 * d s * g0⁻¹) * h ∈
        graphCentralizer TwistTag.E6.tag L (diagramMap TwistTag.E6 L) := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L,
      F = twistHom TwistTag.E6 L (iterateFrobenius L p e) := ⟨_, rfl⟩
  rw [← hF] at hg0 ⊢
  have hpp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq2 : 2 ≤ p ^ e := by
    calc 2 ≤ p := hpp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  have hFr : ∀ c, iterateFrobenius L p e c = c ^ (p ^ e) := fun c => rfl
  set u := weylTwist TwistTag.E6 v with hu
  set nw := canonicalRep (coxeterSystem TwistTag.E6.tag) L w with hnw
  set nv := canonicalRep (coxeterSystem TwistTag.E6.tag) L v with hnv
  set nu := canonicalRep (coxeterSystem TwistTag.E6.tag) L u with hnu
  set n' := canonicalRep (coxeterSystem TwistTag.E6.tag) L (v * w * u⁻¹) with hn'
  obtain ⟨k₀, hk₀, hrel⟩ := canonicalRep_inv_mul_conj_mem_tw (L := L) v u w
  obtain ⟨h₀, hh₀T, hh₀⟩ := exists_torus_lang_tw (L := L) hq2 hFr w hk₀
  have hFnv : F nv = nu := by
    rw [hF, hnv, twistHom_canonicalRep]
  have hcommT : ∀ x ∈ torusGroup TwistTag.E6.tag L, ∀ y ∈ torusGroup TwistTag.E6.tag L,
      x * y = y * x := fun x hx y hy => by
    obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hx
    obtain ⟨b, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hy
    rw [← map_mul, ← map_mul, mul_comm]
  set g1 := g0 * h₀⁻¹ * nv⁻¹ with hg1def
  have hFh₀ : nw * F h₀ * nw⁻¹ = k₀⁻¹ * h₀ := by
    have h1 : h₀ * (nw * F h₀ * nw⁻¹)⁻¹ = k₀ := by rw [hF]; exact hh₀
    rw [← h1]
    group
  have hg1 : F g1 = g1 * n' := by
    have hn'nv : nv⁻¹ * n' = k₀ * nw * nu⁻¹ := by
      calc nv⁻¹ * n' = (nv⁻¹ * n' * nu) * nu⁻¹ := (mul_inv_cancel_right _ _).symm
        _ = k₀ * nw * nu⁻¹ := by rw [hrel]
    have h3 : nw * (F h₀)⁻¹ = h₀⁻¹ * k₀ * nw := by
      have : nw * (F h₀)⁻¹ * nw⁻¹ = (nw * F h₀ * nw⁻¹)⁻¹ := by group
      rw [hFh₀] at this
      calc nw * (F h₀)⁻¹ = (nw * (F h₀)⁻¹ * nw⁻¹) * nw := by group
        _ = (k₀⁻¹ * h₀)⁻¹ * nw := by rw [this]
        _ = h₀⁻¹ * k₀ * nw := by group
    calc F g1 = F g0 * (F h₀)⁻¹ * (F nv)⁻¹ := by rw [hg1def, map_mul, map_mul, map_inv, map_inv]
      _ = g0 * nw * (F h₀)⁻¹ * nu⁻¹ := by rw [hg0, hFnv]
      _ = g0 * (nw * (F h₀)⁻¹) * nu⁻¹ := by group
      _ = g0 * (h₀⁻¹ * k₀ * nw) * nu⁻¹ := by rw [h3]
      _ = g0 * h₀⁻¹ * (k₀ * nw * nu⁻¹) := by group
      _ = g0 * h₀⁻¹ * (nv⁻¹ * n') := by rw [hn'nv]
      _ = g1 * n' := by rw [hg1def]; group
  have hg1C : g1 ∈ adjointGroup TwistTag.E6.tag L :=
    mul_mem (mul_mem hg0C (inv_mem (torusGroup_le_adjointGroup' hh₀T)))
      (inv_mem (canonicalRep_mem_adjointGroup _ L v))
  have hn'Γ : n' ∈ graphCentralizer TwistTag.E6.tag L (diagramMap TwistTag.E6 L) := by
    have h := canonicalRep_mem_twistedFixedGroup (t := TwistTag.E6) (K := L)
      (σ := RingHom.id L) hw
    rwa [twistedFixedGroup_id_eq] at h
  obtain ⟨f, hfΓ, hf⟩ := lang_graphFixed_E6 p L e he 1 n' hn'Γ
  have hFf : F f = f * n' := by
    rw [pow_one] at hf
    have h1 : F f = diagramMap TwistTag.E6 L * Units.map (entrywiseHom (iterateFrobenius L p e)) f *
        (diagramMap TwistTag.E6 L)⁻¹ := by rw [hF]; rfl
    rw [h1]
    calc diagramMap TwistTag.E6 L * Units.map (entrywiseHom (iterateFrobenius L p e)) f *
          (diagramMap TwistTag.E6 L)⁻¹ = f * (f⁻¹ * (diagramMap TwistTag.E6 L *
            Units.map (entrywiseHom (iterateFrobenius L p e)) f *
              (diagramMap TwistTag.E6 L)⁻¹)) := by group
      _ = f * n' := by rw [hf]
  have hfC : f ∈ adjointGroup TwistTag.E6.tag L := (Subgroup.mem_inf.1 hfΓ).1
  refine ⟨g1 * f⁻¹, mul_mem hg1C (inv_mem hfC), ?_, fun s => ?_⟩
  · calc F (g1 * f⁻¹) = F g1 * (F f)⁻¹ := by rw [map_mul, map_inv]
      _ = g1 * n' * (f * n')⁻¹ := by rw [hg1, hFf]
      _ = g1 * f⁻¹ := by group
  · have hdΓ : nv * d s * nv⁻¹ ∈
        graphCentralizer TwistTag.E6.tag L (diagramMap TwistTag.E6 L) := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ L v)
          (torusGroup_le_adjointGroup' (hd s))) (inv_mem (canonicalRep_mem_adjointGroup _ L v))
      · rw [mem_centralizer_singleton_iff_conj_eq]
        exact hv s
    have hconj : (g1 * f⁻¹)⁻¹ * (g0 * d s * g0⁻¹) * (g1 * f⁻¹) =
        f * (nv * d s * nv⁻¹) * f⁻¹ := by
      calc (g1 * f⁻¹)⁻¹ * (g0 * d s * g0⁻¹) * (g1 * f⁻¹)
          = f * (nv * (h₀ * d s * h₀⁻¹) * nv⁻¹) * f⁻¹ := by rw [hg1def]; group
        _ = f * (nv * d s * nv⁻¹) * f⁻¹ := by
          rw [show h₀ * d s * h₀⁻¹ = d s by
            rw [hcommT _ hh₀T _ (hd s)]; group]
    rw [hconj]
    exact mul_mem (mul_mem hfΓ hdΓ) (inv_mem hfΓ)

end Core

end CFSG.LieType.SeitzGeneration.ExcHighThree
