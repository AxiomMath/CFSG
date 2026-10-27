module

public import CFSG.Adapters.TauCetiExceptional.MinusculePeel
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
public import CFSG.LieType.Steinberg.Bruhat
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import CFSG.Adapters.TauCetiExceptional.BigCellCore

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg
  CFSG.TauCetiBridge.BigCell CFSG.LieType.Universal CFSG.LieType.RootSystem MinData

section Mono

variable {d : ℕ} {K : Type*} [Field K]

@[expose] def IsMono (f : Module.End K (Fin d →₀ K)) : Prop :=
  ∀ a, ∃ b, ∃ c : K, f (Finsupp.single a 1) = c • Finsupp.single b 1

theorem IsMono.mul {f g : Module.End K (Fin d →₀ K)} (hf : IsMono f) (hg : IsMono g) :
    IsMono (f * g) := fun a => by
  obtain ⟨b, c, hb⟩ := hg a
  obtain ⟨b', c', hb'⟩ := hf b
  exact ⟨b', c * c', by rw [Module.End.mul_apply, hb, map_smul, hb', smul_smul]⟩

theorem isMono_one : IsMono (1 : Module.End K (Fin d →₀ K)) := fun a => ⟨a, 1, by simp⟩

theorem isMono_diagOp
    (μ : Fin d → K) : IsMono (diagOp μ) := fun a => ⟨a, μ a, diagOp_single μ a⟩

theorem natMat_apply_eq_zero_of_bigCellDet_ne_zero
    {f : (Module.End K (Fin d →₀ K))ˣ}
    {σ : Fin d → Fin d} {c : Fin d → K}
    (hσ : ∀ a, (f : Module.End K (Fin d →₀ K)) (Finsupp.single a 1) = c a • Finsupp.single (σ a) 1)
    (hinj : Function.Injective σ)
    (hΔ : bigCellDet (natMat K (f : Module.End K (Fin d →₀ K))) ≠ 0) (s : Fin d) : σ s = s := by
  suffices H : ∀ m : ℕ, ∀ s : Fin d, s.val = m → σ s = s from H s.val s rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro s hs
  by_contra hne
  have hgt : s < σ s := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd (hinj (ih (σ s).val (hs ▸ Fin.lt_def.1 h) (σ s) rfl)) hne
    · exact h
  apply hΔ
  refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
  refine Matrix.det_eq_zero_of_column_eq_zero ⟨s, by simp⟩ fun r => ?_
  rw [Matrix.toBlock_apply, natMat_apply, hσ, Finsupp.smul_apply,
    Finsupp.single_eq_of_ne, smul_zero]
  intro e
  have hr := r.2
  rw [← e] at hgt
  exact absurd (Fin.lt_def.1 hgt) (by omega)

theorem natMat_eq_zero_of_isMono {f : (Module.End K (Fin d →₀ K))ˣ}
    (hf : IsMono (f : Module.End K (Fin d →₀ K)))
    (hΔ : bigCellDet (natMat K (f : Module.End K (Fin d →₀ K))) ≠ 0) {r s : Fin d}
    (hrs : r ≠ s) : natMat K (f : Module.End K (Fin d →₀ K)) r s = 0 := by
  choose σ c hσ using hf
  have hc : ∀ a, c a ≠ 0 := fun a h => by
    have e := congrArg (f⁻¹ : (Module.End K (Fin d →₀ K))ˣ).val (hσ a)
    rw [h, zero_smul, map_zero, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
      at e
    simpa using congrArg (fun v => v a) e
  have hinj : Function.Injective σ := fun a a' h => by
    by_contra hne
    have e : (f : Module.End K (Fin d →₀ K)) (c a' • Finsupp.single a 1 -
        c a • Finsupp.single a' 1) = 0 := by
      rw [map_sub, map_smul, map_smul, hσ, hσ, h, smul_smul, smul_smul, mul_comm, sub_self]
    have e' := congrArg (f⁻¹ : (Module.End K (Fin d →₀ K))ˣ).val e
    rw [map_zero, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] at e'
    have := congrArg (fun v => v a) e'
    simp [Ne.symm hne] at this
    exact hc a' this
  rw [natMat_apply, hσ, natMat_apply_eq_zero_of_bigCellDet_ne_zero hσ hinj hΔ s,
    Finsupp.smul_apply, Finsupp.single_eq_of_ne hrs, smul_zero]

theorem apply_single_eq_of_diag {f : Module.End K (Fin d →₀ K)}
    (hdiag : ∀ r s, r ≠ s → natMat K f r s = 0) (s : Fin d) :
    f (Finsupp.single s 1) = natMat K f s s • Finsupp.single s 1 := by
  ext r
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  by_cases h : s = r
  · subst h
    rw [natMat_apply, ite_eq_left rfl, mul_one]
  · rw [ite_eq_right h, mul_zero, ← natMat_apply, hdiag r s (Ne.symm h)]

end Mono

section Group

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (hA : TauCeti.IsFiniteType τ.cartan)
  (K : Type*) [Field K]

include hV in
theorem isMono_nOp
    (i : Fin τ.rank) : IsMono (D.nOp K i) := fun a => by
  rw [hV.nOp_single]
  split_ifs
  · exact ⟨_, -1, by rw [neg_one_smul]⟩
  · exact ⟨_, 1, by rw [one_smul]⟩

include hA in
theorem isMono_of_mem_weylN
    {x : hV.minGroup K} (hx : x ∈ weylN (hV.nm K) (hV.torus K)) :
    IsMono (hV.endo K x) := by
  obtain ⟨t, ht, ω, rfl⟩ := (mem_weylN_iff (hV.minDatum_isCTGroupDatum hA K)).1 hx
  rw [hV.endo_mul]
  obtain ⟨μ, hμ⟩ := hV.exists_diagOp_of_mem_iSup_torus K ht
  refine hμ ▸ (isMono_diagOp μ).mul ?_
  clear hx
  induction ω with
  | nil => exact isMono_one
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, hV.endo_mul, hV.endo_nm]
    exact (isMono_nOp hV K i).mul ih

include hA in
theorem mem_iSup_torus_of_diag
    (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {m : hV.minGroup K} (hm : m ∈ weylN (hV.nm K) (hV.torus K))
    (hdiag : ∀ r s, r ≠ s → natMat K (hV.endo K m) r s = 0) : m ∈ ⨆ i, hV.torus K i := by
  set hct := hV.minDatum_isCTGroupDatum hA K
  have hext := hV.minDatum_steinbergExtras hA K hpd
  obtain ⟨v, hv⟩ := exists_actsAs hct hm
  refine mem_iSup_of_actsAs_one hct hext hm fun γ hγ => ?_
  rw [hv γ hγ, map_one, Module.End.one_apply]
  have hγ' : IsRoot τ γ := (hV.mem_minDatum_roots hA K).1 hγ
  have hvγ : IsRoot τ (weylAction hA v γ) :=
    (hV.mem_minDatum_roots hA K).1 (weylAction_mem_roots hA v hγ)
  suffices e : weylAction hA v γ = γ by rw [e]
  have hmx : m * hV.xm K γ 1 * m⁻¹ ∈ hV.rootGroup K (weylAction hA v γ) := by
    rw [show hV.rootGroup K (weylAction hA v γ) = _ from (hv γ hγ).symm]
    exact ⟨_, hV.xm_mem_rootGroup K γ 1, rfl⟩
  obtain ⟨c, hc⟩ := (hV.mem_rootGroup K).1 hmx
  set μ := fun s => natMat K (hV.endo K m) s s
  have hscale : ∀ s, hV.endo K m (Finsupp.single s 1) = μ s • Finsupp.single s 1 :=
    apply_single_eq_of_diag hdiag
  have hmm : hV.endo K m⁻¹ * hV.endo K m = 1 := hV.endo_inv_mul K m
  have hμ : ∀ s, μ s ≠ 0 := fun s h0 => by
    have e1 := congrArg (fun f : Module.End K (Fin D.d →₀ K) => f (Finsupp.single s 1)) hmm
    simp only [Module.End.mul_apply, hscale, h0, zero_smul, map_zero, Module.End.one_apply] at e1
    simpa using congrArg (fun v => v s) e1
  have hinv : ∀ s, hV.endo K m⁻¹ (Finsupp.single s 1) = (μ s)⁻¹ • Finsupp.single s 1 := by
    intro s
    have e1 := congrArg (fun f : Module.End K (Fin D.d →₀ K) => f
      ((μ s)⁻¹ • Finsupp.single s 1)) hmm
    simp only [Module.End.mul_apply, map_smul, hscale, smul_smul, inv_mul_cancel₀ (hμ s),
      one_smul, Module.End.one_apply] at e1
    exact e1
  obtain ⟨a, ha⟩ : ∃ a, D.rootOp K γ (Finsupp.single a 1) ≠ 0 := by
    by_contra h
    push Not at h
    exact hV.rootOp_ne_zero (R := K) hγ' (ext_single fun a => by rw [h a, LinearMap.zero_apply])
  obtain ⟨b, hab, hs⟩ := (hV.isSignedMap_rootOp (R := K) hγ' a).resolve_left ha
  obtain ⟨σ, hσ, hEa⟩ : ∃ σ : K, σ ≠ 0 ∧
      D.rootOp K γ (Finsupp.single a 1) = σ • Finsupp.single b 1 := by
    rcases hs with h | h
    · exact ⟨1, one_ne_zero, by rw [h, one_smul]⟩
    · exact ⟨-1, neg_ne_zero.2 one_ne_zero, by rw [h, neg_one_smul]⟩
  have hL : hV.endo K (hV.xm K (weylAction hA v γ) c) (Finsupp.single a 1) b =
      Finsupp.single a (1 : K) b + c * D.rootOp K (weylAction hA v γ) (Finsupp.single a 1) b := by
    rw [hV.endo_xm]
    simp
  have hR : hV.endo K (m * hV.xm K γ 1 * m⁻¹) (Finsupp.single a 1) b =
      Finsupp.single a (1 : K) b + (μ a)⁻¹ * σ * μ b := by
    rw [hV.endo_mul, hV.endo_mul, Module.End.mul_apply, Module.End.mul_apply, hinv, hV.endo_xm,
      map_smul,
      LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, one_smul, hEa, map_smul,
      map_add, map_smul, hscale, hscale]
    simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul]
    rw [Finsupp.single_eq_same]
    field_simp [hμ a]
  rw [hc, hR] at hL
  have hne : D.rootOp K (weylAction hA v γ) (Finsupp.single a 1) b ≠ 0 := fun h0 => by
    rw [h0, mul_zero, add_zero, add_eq_left] at hL
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (hμ a)) hσ) (hμ b) hL
  exact toWeight_injective hpd (add_left_cancel
    ((wt_eq_of_rootOp_single_apply_ne_zero hV hvγ hne).symm.trans hab))

end Group

end CFSG.TauCetiBridge.Minuscule
