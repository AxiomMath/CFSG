module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QX7S
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Row

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.Burgoyne.E2 CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem rootDiagUnit_eq_of_pair
    {τ : Tag} {M : Type} [Field M] {i₁ i₂ : Fin τ.rank}
    {b b' : Fin τ.rank → Mˣ} (hb : ∀ j, j ≠ i₁ → j ≠ i₂ → b j = 1) (hb12 : b i₁ * b i₂ = 1)
    (hb' : ∀ j, j ≠ i₁ → j ≠ i₂ → b' j = 1) (hb12' : b' i₁ * b' i₂ = 1)
    (h2 : rootDiagUnit τ b * rootDiagUnit τ b = 1)
    (h2' : rootDiagUnit τ b' * rootDiagUnit τ b' = 1) (h1 : rootDiagUnit τ b ≠ 1)
    (h1' : rootDiagUnit τ b' ≠ 1) : rootDiagUnit τ b = rootDiagUnit τ b' := by
  classical
  have key : ∀ m : Fin τ.rank → Mˣ, (∀ j, j ≠ i₁ → j ≠ i₂ → m j = 1) → m i₁ * m i₂ = 1 →
      rootDiagUnit τ m * rootDiagUnit τ m = 1 → rootDiagUnit τ m ≠ 1 →
        m = fun j => if j = i₁ ∨ j = i₂ then -1 else 1 := by
    intro m hm hm12 hm2 hm1
    have hmm : m * m = 1 := eq_one_of_rootDiagUnit_eq_one (by rw [rootDiagUnit_mul]; exact hm2)
    have hm0 : m i₁ * m i₁ = 1 := congrFun hmm i₁
    have hm21 : m i₂ = m i₁ :=
      (eq_inv_of_mul_eq_one_right hm12).trans (eq_inv_of_mul_eq_one_left hm0).symm
    have hm0' : (m i₁ : M) * m i₁ = 1 := by
      have h3 := congrArg Units.val hm0
      simpa using h3
    rcases mul_self_eq_one_iff.1 hm0' with h | h
    · refine absurd ?_ hm1
      have hm' : m = 1 := funext fun j => by
        by_cases hj1 : j = i₁
        · rw [hj1]
          exact Units.ext h
        · by_cases hj2 : j = i₂
          · rw [hj2, hm21]
            exact Units.ext h
          · exact hm j hj1 hj2
      rw [hm', rootDiagUnit_one]
    · funext j
      by_cases hj1 : j = i₁
      · rw [hj1]
        simp only [true_or, ↓reduceIte]
        exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
      · by_cases hj2 : j = i₂
        · rw [hj2, hm21]
          simp only [or_true, ↓reduceIte]
          exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
        · simp only [hj1, hj2, or_self, ↓reduceIte]
          exact hm j hj1 hj2
  rw [key b hb hb12 h2 h1, key b' hb' hb12' h2' h1']

variable {p : ℕ} [Fact p.Prime]

theorem centModel_twE6_t1
    {f : ℕ} {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L p] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    {g₀ : ModGL TwistTag.E6.tag L} (hg₀G : g₀ ∈ adjointGroup TwistTag.E6.tag L)
    (hg₀F : frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L) g₀ = g₀)
    (hg₀t : g₀ * baseChangeGL (algebraMap K L) (t : ModGL TwistTag.E6.tag K) * g₀⁻¹ =
      rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20))) :
    CentModel (fixedSubgroup (MulAut.conj t)) := by
  classical
  have hp : p.Prime := Fact.out
  have : CharP K p := finite_field_prime_power_characteristic hp (show 1 ≤ f * 2 by omega)
    (by rw [hK, ← pow_mul])
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hk := isAlgebraic_zmod_of_isAlgClosure p K L
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag L)
    (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) with hR
  set d := rootDiagUnit TwistTag.E6.tag
    (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) with hd
  have hg₀R : g₀ ∈ R := mem_fixedPointsIn.2 ⟨hg₀G, hg₀F⟩
  set Φ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g₀).toMonoidHom.comp ((baseChangeGL (algebraMap K L)).comp
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype) with hΦ
  have hΦapp : ∀ s, Φ s =
      g₀ * baseChangeGL (algebraMap K L) (s : ModGL TwistTag.E6.tag K) * g₀⁻¹ := fun s => rfl
  have hΦinj : Function.Injective Φ :=
    (MulAut.conj g₀).injective.comp ((baseChangeGL_injective _).comp Subtype.val_injective)
  have hΦt : Φ t = d := hg₀t
  have hmap : (fixedSubgroup (MulAut.conj t)).map Φ = ⁅R, R⁆ ⊓ Subgroup.centralizer {d} := by
    ext v
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : t * s * t⁻¹ = s := hs
      have hst : t * s = s * t := by
        calc t * s = t * s * t⁻¹ * t := by group
          _ = s * t := by rw [hs']
      refine Subgroup.mem_inf.2 ⟨(t1_preimage hp2 hf hK σ hσ hg₀R).2 ⟨s, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hΦt, ← map_mul, ← map_mul, hst]
    · intro hv
      obtain ⟨hvH, hvd⟩ := Subgroup.mem_inf.1 hv
      obtain ⟨s, rfl⟩ := (t1_preimage hp2 hf hK σ hσ hg₀R).1 hvH
      refine ⟨s, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hΦapp s, ← hΦt, ← map_mul, ← map_mul] at hvd
      have hst := hΦinj hvd
      change t * s * t⁻¹ = s
      rw [← hst]
      group
  obtain ⟨D, u, hDe, hDχ, hDθ, hsub, hqs, hu, hCH, hCn⟩ :=
    exists_twenty_layer (k := L) hp2 hf hk
  set H := fixedSubgroup (MulAut.conj t) with hHdef
  set ψ : H →* ModGL TwistTag.E6.tag L := Φ.comp H.subtype with hψ
  have hψinj : Function.Injective ψ := hΦinj.comp Subtype.val_injective
  have hψrange : ψ.range = ⁅R, R⁆ ⊓ Subgroup.centralizer {d} := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  set C' := D.orbitGroup.map (MulAut.conj u).toMonoidHom with hC'
  have hC'ψ : C' ≤ ψ.range := hψrange ▸ hCH
  have hqC' : IsQuasisimple C' := LocalCores.isQuasisimple_of_mulEquiv
    (D.orbitGroup.equivMapOfInjective _ (MulAut.conj u).injective) hqs
  let eQ : C'.comap ψ ≃* C' := ((C'.comap ψ).equivMapOfInjective ψ hψinj).trans
    (MulEquiv.subgroupCongr (map_comap_eq_self hC'ψ))
  have hψR : ∀ y : H, ψ y ∈ R ⊓ Subgroup.centralizer {d} := fun y =>
    inf_le_inf_right _ (Subgroup.commutator_le_of_le le_rfl le_rfl)
      (hψrange ▸ (⟨y, rfl⟩ : ψ y ∈ ψ.range))
  have hQn : (C'.comap ψ).Normal := ⟨fun q hq y => by
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have h := Subgroup.mem_map_of_mem (MulAut.conj (ψ y)).toMonoidHom (Subgroup.mem_comap.1 hq)
    rw [hCn (ψ y) (hψR y)] at h
    exact h⟩
  have hQ : IsComponent (C'.comap ψ) :=
    ⟨(isQuasisimple_congr eQ).2 hqC', hQn.isSubnormal⟩
  have huG : u ∈ adjointGroup TwistTag.E6.tag L :=
    sup_le torusGroup_le_adjointGroup (rootSpan_le_adjointGroup L _) hu
  have hψG : ∀ y : H, ψ y ∈ adjointGroup TwistTag.E6.tag L := fun y =>
    (mem_fixedPointsIn.1 (Subgroup.mem_inf.1 (hψR y)).1).1
  have hdiag : ∀ y : H, (∀ s ∈ C'.comap ψ, s * y = y * s) →
      ∃ b : Fin TwistTag.E6.tag.rank → Lˣ, u⁻¹ * ψ y * u = rootDiagUnit TwistTag.E6.tag b ∧
        (∀ j, j ≠ t1Node 2 → j ≠ t1Node 4 → b j = 1) ∧ b (t1Node 2) * b (t1Node 4) = 1 := by
    intro y hy
    have hcC : ∀ w ∈ D.orbitGroup, (u⁻¹ * ψ y * u) * w = w * (u⁻¹ * ψ y * u) := by
      intro w hw
      obtain ⟨q, hq⟩ := hC'ψ ⟨w, hw, rfl⟩
      have hq' : q ∈ C'.comap ψ := by
        rw [Subgroup.mem_comap, hq]
        exact ⟨w, hw, rfl⟩
      have h := congrArg ψ (hy q hq')
      rw [map_mul, map_mul, hq] at h
      change (u * w * u⁻¹) * ψ y = ψ y * (u * w * u⁻¹) at h
      calc u⁻¹ * ψ y * u * w = u⁻¹ * (ψ y * (u * w * u⁻¹)) * u := by group
        _ = u⁻¹ * ((u * w * u⁻¹) * ψ y) * u := by rw [h]
        _ = w * (u⁻¹ * ψ y * u) := by group
    have := hsub
    obtain ⟨b, hb, h0, h1, h3, h5, h24⟩ := eq_of_commute_orbitGroup_twenty D (three_le_q_e6 D)
      hDχ hDθ (mul_mem (mul_mem (inv_mem huG) (hψG y)) huG) hcC
    refine ⟨b, hb, fun j hj2 hj4 => ?_, h24⟩
    have hj : j = t1Node 0 ∨ j = t1Node 1 ∨ j = t1Node 3 ∨ j = t1Node 5 := by
      revert j
      decide
    rcases hj with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h3
    · exact h5
  have hback : ∀ (y : H) (b : Fin TwistTag.E6.tag.rank → Lˣ),
      u⁻¹ * ψ y * u = rootDiagUnit TwistTag.E6.tag b →
        ψ y = u * rootDiagUnit TwistTag.E6.tag b * u⁻¹ := fun y b hb => by
    rw [← hb]
    group
  refine ⟨Unit, fun _ => C'.comap ψ, fun _ => hQ,
    fun _ => Burgoyne.even_card_of_isQuasisimple hQ.1, fun y y' hy hy' => ?_,
    fun y y' hy hy' hy2 hy2' hy1 hy1' => ?_⟩
  · obtain ⟨b, hb, -⟩ := hdiag y (hy ())
    obtain ⟨b', hb', -⟩ := hdiag y' (hy' ())
    refine hψinj ?_
    rw [map_mul, map_mul, hback y b hb, hback y' b' hb']
    have hc : rootDiagUnit TwistTag.E6.tag b * rootDiagUnit TwistTag.E6.tag b' =
        rootDiagUnit TwistTag.E6.tag b' * rootDiagUnit TwistTag.E6.tag b := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    calc u * rootDiagUnit TwistTag.E6.tag b * u⁻¹ * (u * rootDiagUnit TwistTag.E6.tag b' * u⁻¹) =
        u * (rootDiagUnit TwistTag.E6.tag b * rootDiagUnit TwistTag.E6.tag b') * u⁻¹ := by group
      _ = u * (rootDiagUnit TwistTag.E6.tag b' * rootDiagUnit TwistTag.E6.tag b) * u⁻¹ := by
        rw [hc]
      _ = u * rootDiagUnit TwistTag.E6.tag b' * u⁻¹ *
          (u * rootDiagUnit TwistTag.E6.tag b * u⁻¹) := by group
  · obtain ⟨b, hb, hPb, hPb'⟩ := hdiag y (hy ())
    obtain ⟨b', hb', hQb, hQb'⟩ := hdiag y' (hy' ())
    have hsq : ∀ (x : H) (c : Fin TwistTag.E6.tag.rank → Lˣ),
        u⁻¹ * ψ x * u = rootDiagUnit TwistTag.E6.tag c → x * x = 1 →
          rootDiagUnit TwistTag.E6.tag c * rootDiagUnit TwistTag.E6.tag c = 1 := by
      intro x c hc hx
      rw [← hc]
      have hψx : ψ x * ψ x = 1 := by rw [← map_mul, hx, map_one]
      calc u⁻¹ * ψ x * u * (u⁻¹ * ψ x * u) = u⁻¹ * (ψ x * ψ x) * u := by group
        _ = 1 := by rw [hψx]; group
    have hne : ∀ (x : H) (c : Fin TwistTag.E6.tag.rank → Lˣ),
        u⁻¹ * ψ x * u = rootDiagUnit TwistTag.E6.tag c → x ≠ 1 →
          rootDiagUnit TwistTag.E6.tag c ≠ 1 := by
      intro x c hc hx h1
      apply hx
      have hψx : ψ x = 1 := by
        rw [hback x c hc, h1]
        group
      exact hψinj (hψx.trans (map_one ψ).symm)
    have h := rootDiagUnit_eq_of_pair hPb hPb' hQb hQb' (hsq y b hb hy2)
      (hsq y' b' hb' hy2') (hne y b hb hy1) (hne y' b' hb' hy1')
    refine hψinj ?_
    rw [hback y b hb, hback y' b' hb', h]

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
