module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.ConjLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwConj
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic
public import CFSG.RankThree.PartOne.KE.CTLang

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Core


theorem exists_fixed_conj_into_graphFixed {L : Type} [Field L] [IsAlgClosed L] (p : ℕ)
    [Fact p.Prime] [CharP L p] (e : ℕ) (he : 1 ≤ e) (w v : WeylGroup TwistTag.E6.tag)
    (g0 : ModGL TwistTag.E6.tag L) (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L p e)) g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
    (hw : weylTwist TwistTag.E6 (v * w * v⁻¹) = v * w * v⁻¹)
    {ι : Type} (d : ι → ModGL TwistTag.E6.tag L) (hd : ∀ s, d s ∈ torusGroup TwistTag.E6.tag L)
    (hv : ∀ s, diagramMap TwistTag.E6 L *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v * d s *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) * (diagramMap TwistTag.E6 L)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) L v * d s *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)⁻¹) :
    ∃ h ∈ adjointGroup TwistTag.E6.tag L,
      Units.map (entrywiseHom (iterateFrobenius L p e)) h = h ∧
      ∀ s, h⁻¹ * (g0 * d s * g0⁻¹) * h ∈
        graphCentralizer TwistTag.E6.tag L (diagramMap TwistTag.E6 L) := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L,
      F = Units.map (entrywiseHom (iterateFrobenius L p e)) := ⟨_, rfl⟩
  rw [← hF] at hg0 ⊢
  have hpp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq2 : 2 ≤ p ^ e := by
    calc 2 ≤ p := hpp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  have hFr : ∀ c, iterateFrobenius L p e c = c ^ (p ^ e) := fun c => rfl
  set nw := canonicalRep (coxeterSystem TwistTag.E6.tag) L w with hnw
  set nv := canonicalRep (coxeterSystem TwistTag.E6.tag) L v with hnv
  set n' := canonicalRep (coxeterSystem TwistTag.E6.tag) L (v * w * v⁻¹) with hn'
  obtain ⟨k₀, hk₀, hrel⟩ := canonicalRep_inv_mul_conj_mem (L := L) v w
  obtain ⟨h₀, hh₀T, hh₀⟩ := exists_torus_lang (L := L) hq2 hFr w hk₀
  have hFnv : F nv = nv := by
    rw [hF, CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self, hnv,
      CFSG.RankThree.Chevalley.baseChangeGL_canonicalRep]
  have hcommT : ∀ x ∈ torusGroup TwistTag.E6.tag L, ∀ y ∈ torusGroup TwistTag.E6.tag L,
      x * y = y * x :=
    fun x hx y hy => by
      obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hx
      obtain ⟨b, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hy
      rw [← map_mul, ← map_mul, mul_comm]
  set g1 := g0 * h₀⁻¹ * nv⁻¹ with hg1def
  have hFh₀ : nw * F h₀ * nw⁻¹ = k₀⁻¹ * h₀ := by
    have h1 : h₀ * (nw * F h₀ * nw⁻¹)⁻¹ = k₀ := by rw [hF]; exact hh₀
    rw [← h1]
    group
  have hg1 : F g1 = g1 * n' := by
    have hn'nv : nv⁻¹ * n' = k₀ * nw * nv⁻¹ := by
      calc nv⁻¹ * n' = (nv⁻¹ * n' * nv) * nv⁻¹ := (mul_inv_cancel_right _ _).symm
        _ = k₀ * nw * nv⁻¹ := by rw [hrel]
    have h3 : nw * (F h₀)⁻¹ = h₀⁻¹ * k₀ * nw := by
      have : nw * (F h₀)⁻¹ * nw⁻¹ = (nw * F h₀ * nw⁻¹)⁻¹ := by group
      rw [hFh₀] at this
      calc nw * (F h₀)⁻¹ = (nw * (F h₀)⁻¹ * nw⁻¹) * nw := by group
        _ = (k₀⁻¹ * h₀)⁻¹ * nw := by rw [this]
        _ = h₀⁻¹ * k₀ * nw := by group
    calc F g1 = F g0 * (F h₀)⁻¹ * (F nv)⁻¹ := by rw [hg1def, map_mul, map_mul, map_inv, map_inv]
      _ = g0 * nw * (F h₀)⁻¹ * nv⁻¹ := by rw [hg0, hFnv]
      _ = g0 * (nw * (F h₀)⁻¹) * nv⁻¹ := by group
      _ = g0 * (h₀⁻¹ * k₀ * nw) * nv⁻¹ := by rw [h3]
      _ = g0 * h₀⁻¹ * (k₀ * nw * nv⁻¹) := by group
      _ = g0 * h₀⁻¹ * (nv⁻¹ * n') := by rw [hn'nv]
      _ = g1 * n' := by rw [hg1def]; group
  have hg1C : g1 ∈ adjointGroup TwistTag.E6.tag L :=
    mul_mem (mul_mem hg0C (inv_mem (torusGroup_le_adjointGroup' hh₀T)))
      (inv_mem (canonicalRep_mem_adjointGroup _ L v))
  have hn'Γ : n' ∈ graphCentralizer TwistTag.E6.tag L (diagramMap TwistTag.E6 L) := by
    have h := canonicalRep_mem_twistedFixedGroup (t := TwistTag.E6) (K := L)
      (σ := RingHom.id L) hw
    rwa [twistedFixedGroup_id_eq] at h
  obtain ⟨f, hfΓ, hf⟩ := lang_graphFixed_E6 p L e he 0 n' hn'Γ
  have hFf : F f = f * n' := by
    rw [pow_zero, one_mul, inv_one, mul_one, ← hF] at hf
    calc F f = f * (f⁻¹ * F f) := by group
      _ = f * n' := by rw [hf]
  have hfC : f ∈ adjointGroup TwistTag.E6.tag L := (Subgroup.mem_inf.1 hfΓ).1
  refine ⟨g1 * f⁻¹, mul_mem hg1C (inv_mem hfC), ?_, fun s => ?_⟩
  · calc F (g1 * f⁻¹) = F g1 * (F f)⁻¹ := by rw [map_mul, map_inv]
      _ = g1 * n' * (f * n')⁻¹ := by rw [hg1, hFf]
      _ = g1 * f⁻¹ := by group
  ·
    have hdΓ : nv * d s * nv⁻¹ ∈ graphCentralizer TwistTag.E6.tag L (diagramMap TwistTag.E6 L) := by
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
