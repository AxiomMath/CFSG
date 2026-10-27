module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBStated

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Module CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm ker range)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def fixSub (g : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) V :=
  ker (g.toLinearMap - LinearMap.id)

theorem mem_fixSub {g : V ≃ₗ[ZMod 2] V} {v : V} : v ∈ fixSub g ↔ g v = v := by
  rw [fixSub, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

theorem neg_eq_self_of_zmod_two (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem sub_eq_add_of_zmod_two (v w : V) : v - w = v + w := by
  rw [sub_eq_add_neg, neg_eq_self_of_zmod_two]

theorem finrank_ker_pow_succ [FiniteDimensional (ZMod 2) V] (N : V →ₗ[ZMod 2] V) (i : ℕ) :
    finrank (ZMod 2) (ker (N ^ (i + 1))) =
      finrank (ZMod 2) (ker (N ^ i)) + finrank (ZMod 2) ↥(range (N ^ i) ⊓ ker N) := by
  set K := ker (N ^ (i + 1))
  set f : K →ₗ[ZMod 2] V := (N ^ i).domRestrict K
  have hle : ker (N ^ i) ≤ K := fun v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [pow_succ', Module.End.mul_apply, hv, map_zero]
  have hker : finrank (ZMod 2) (ker f) = finrank (ZMod 2) (ker (N ^ i)) := by
    rw [LinearMap.ker_domRestrict]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hrange : range f = range (N ^ i) ⊓ ker N := by
    ext w
    simp only [LinearMap.mem_range, Submodule.mem_inf, LinearMap.mem_ker]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨v, rfl⟩, ?_⟩
      have hv := v.2
      rw [LinearMap.mem_ker, pow_succ', Module.End.mul_apply] at hv
      exact hv
    · rintro ⟨⟨v, rfl⟩, hv⟩
      refine ⟨⟨v, ?_⟩, rfl⟩
      rw [LinearMap.mem_ker, pow_succ', Module.End.mul_apply]
      exact hv
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, hrange] at h
  omega

theorem range_pow_inf_ker_le (N : V →ₗ[ZMod 2] V) {i : ℕ} (hi : 1 ≤ i) :
    range (N ^ i) ⊓ ker N ≤ range N ⊓ ker N := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  refine inf_le_inf_right _ ?_
  rw [pow_succ']
  exact LinearMap.range_comp_le_range _ _

theorem add_self_eq_zero_of_zmod_two' (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem zmod_two_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

abbrev nilp (g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V := g.toLinearMap - LinearMap.id

theorem nilp_apply (g : V ≃ₗ[ZMod 2] V) (v : V) : nilp g v = g v - v := rfl

theorem apply_eq_add_nilp (g : V ≃ₗ[ZMod 2] V) (v : V) : g v = v + nilp g v := by
  rw [nilp_apply]
  abel

theorem nilp_sq (g : V ≃ₗ[ZMod 2] V) : nilp g ^ 2 = nilp (g ^ 2) := by
  ext v
  rw [pow_two, Module.End.mul_apply, nilp_apply, nilp_apply, nilp_apply, map_sub, pow_two,
    LinearEquiv.mul_apply, sub_eq_add_of_zmod_two, sub_eq_add_of_zmod_two,
    sub_eq_add_of_zmod_two, sub_eq_add_of_zmod_two, add_assoc, ← add_assoc (g v) (g v),
    add_self_eq_zero_of_zmod_two', zero_add]

theorem fixSub_eq_ker (g : V ≃ₗ[ZMod 2] V) : fixSub g = ker (nilp g) := rfl

theorem form_nilp_eq_zero {B : BilinForm (ZMod 2) V} {c : V ≃ₗ[ZMod 2] V}
    (hc : ∀ x y, B (c x) (c y) = B x y) {f : V} (hf : nilp c f = 0) (y : V) :
    B f (nilp c y) = 0 := by
  have hcf : c f = f := by rw [apply_eq_add_nilp, hf, add_zero]
  rw [nilp_apply, LinearMap.BilinForm.sub_right, ← hcf, hc, hcf, sub_self]

section Chain

variable {c : V ≃ₗ[ZMod 2] V}

theorem exists_ker_add_of_nilp_mem_span {k : ℕ} {w z : Fin k → V}
    (hzw : ∀ i, nilp c (z i) = w i) {v : V}
    (hv : nilp c v ∈ Submodule.span (ZMod 2) (Set.range w)) :
    ∃ (g : Fin k → ZMod 2), nilp c (v - ∑ i, g i • z i) = 0 := by
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hv
  refine ⟨g, ?_⟩
  rw [map_sub, map_sum, ← hg]
  simp [hzw]

theorem linearIndependent_chain {x : V} (h0 : nilp c (nilp c (nilp c (nilp c x))) = 0)
    (hx : nilp c (nilp c (nilp c x)) ≠ 0) :
    LinearIndependent (ZMod 2)
      ![nilp c (nilp c (nilp c x)), nilp c (nilp c x), nilp c x, x] := by
  set N := nilp c
  rw [Fintype.linearIndependent_iff]
  intro g hg'
  have hg : g 0 • N (N (N x)) + g 1 • N (N x) + g 2 • N x + g 3 • x = 0 := by
    simpa [Fin.sum_univ_four] using hg'
  have e3 := congrArg (fun v => N (N (N v))) hg
  simp only [map_add, map_smul, h0, smul_zero, zero_add, map_zero] at e3
  have g3 : g 3 = 0 := (smul_eq_zero.1 e3).resolve_right hx
  rw [g3, zero_smul, add_zero] at hg
  have e2 := congrArg (fun v => N (N v)) hg
  simp only [map_add, map_smul, h0, smul_zero, zero_add, map_zero] at e2
  have g2 : g 2 = 0 := (smul_eq_zero.1 e2).resolve_right hx
  rw [g2, zero_smul, add_zero] at hg
  have e1 := congrArg (fun v => N v) hg
  simp only [map_add, map_smul, h0, smul_zero, zero_add, map_zero] at e1
  have g1 : g 1 = 0 := (smul_eq_zero.1 e1).resolve_right hx
  rw [g1, zero_smul, add_zero] at hg
  have g0 : g 0 = 0 := (smul_eq_zero.1 hg).resolve_right hx
  intro i
  fin_cases i
  exacts [g0, g1, g2, g3]

end Chain

theorem restrict_nondegenerate_of_gram {B : BilinForm (ZMod 2) V} (hB : B.IsAlt)
    {e : Fin 4 → V} {L : Submodule (ZMod 2) V} (hL : L = Submodule.span (ZMod 2) (Set.range e))
    (h03 : B (e 0) (e 3) = 1) (h12 : B (e 1) (e 2) = 1) (h01 : B (e 0) (e 1) = 0)
    (h02 : B (e 0) (e 2) = 0) : (B.restrict L).Nondegenerate := by
  have hsymm : ∀ x y, B x y = B y x := fun x y => by
    rw [← hB.neg_eq x y, ZMod.neg_eq_self_mod_two]
  have hmem : ∀ i, e i ∈ L := fun i => by rw [hL]; exact Submodule.subset_span ⟨i, rfl⟩
  have hleft : ∀ y : L, (∀ z : L, B.restrict L y z = 0) → y = 0 := by
    intro y hy
    have hyL : (y : V) ∈ Submodule.span (ZMod 2) (Set.range e) := hL ▸ y.2
    rw [Submodule.mem_span_range_iff_exists_fun] at hyL
    obtain ⟨g, hg⟩ := hyL
    have hval : ∀ j, B (y : V) (e j) = ∑ i, g i * B (e i) (e j) := fun j => by
      rw [← hg]
      simp [map_sum]
    have hz : ∀ j, B (y : V) (e j) = 0 := fun j => hy ⟨e j, hmem j⟩
    have h10 : B (e 1) (e 0) = 0 := by rw [hsymm, h01]
    have h20 : B (e 2) (e 0) = 0 := by rw [hsymm, h02]
    have h30 : B (e 3) (e 0) = 1 := by rw [hsymm, h03]
    have h21 : B (e 2) (e 1) = 1 := by rw [hsymm, h12]
    have s0 := (hval 0).symm.trans (hz 0)
    have s1 := (hval 1).symm.trans (hz 1)
    have s2 := (hval 2).symm.trans (hz 2)
    have s3 := (hval 3).symm.trans (hz 3)
    simp only [Fin.sum_univ_four, hB.self_eq_zero, h01, h02, h03, h12, h10, h20, h30, h21,
      mul_zero, mul_one] at s0 s1 s2 s3
    have g3 : g 3 = 0 := by linear_combination s0
    have g2 : g 2 = 0 := by linear_combination s1 - B (e 3) (e 1) * g3
    have g1 : g 1 = 0 := by linear_combination s2 - B (e 3) (e 2) * g3
    have g0 : g 0 = 0 := by linear_combination s3 - B (e 1) (e 3) * g1 - B (e 2) (e 3) * g2
    apply Subtype.ext
    rw [← hg]
    simp [Fin.sum_univ_four, g0, g1, g2, g3]
  refine ⟨hleft, fun y hy => hleft y fun z => ?_⟩
  change B (y : V) (z : V) = 0
  rw [hsymm]
  exact hy z

theorem symplectic_order_four_almost_fixed_square_compression [FiniteDimensional (ZMod 2) V]
    {B : BilinForm (ZMod 2) V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    {H : Subgroup (V ≃ₗ[ZMod 2] V)} (hH : H ≤ TauCeti.BilinForm.isometryGroup B)
    {c : V ≃ₗ[ZMod 2] V} (hcH : c ∈ H) (hc4 : orderOf c = 4) {U : Submodule (ZMod 2) V}
    (hU : ∀ h ∈ H, ∀ u ∈ U, h u = u) (_hUc : U ≤ fixSub (c ^ 2))
    (hdim : finrank (ZMod 2) (fixSub (c ^ 2)) ≤ finrank (ZMod 2) U + 1) :
    U = fixSub c ∧ 4 ≤ finrank (ZMod 2) V ∧
    ∃ L : Submodule (ZMod 2) V, finrank (ZMod 2) L = 4 ∧ (∀ x ∈ L, c x ∈ L) ∧
      (B.restrict L).Nondegenerate ∧ IsCompl L (B.orthogonal L) ∧
      (∃ e : Fin 4 → V, LinearIndependent (ZMod 2) e ∧
        Submodule.span (ZMod 2) (Set.range e) = L ∧ c (e 0) = e 0 ∧ c (e 1) = e 1 + e 0 ∧
        c (e 2) = e 2 + e 1 ∧ c (e 3) = e 3 + e 2) ∧
      (∀ h ∈ H, ∀ x ∈ B.orthogonal L, h x = x) ∧ (∀ h ∈ H, ∀ x ∈ L, h x ∈ L) ∧
      ∃ ρ : H →* TauCeti.BilinForm.isometryGroup (B.restrict L),
        Function.Injective ρ ∧
        (∀ (h : H) (x : L), (((ρ h : L ≃ₗ[ZMod 2] L) x : L) : V) = (h : V ≃ₗ[ZMod 2] V) x) ∧
        Nonempty (TauCeti.BilinForm.isometryGroup (B.restrict L) ≃* StatedSp 2 (ZMod 2)) ∧
        Nat.card (TauCeti.BilinForm.isometryGroup (B.restrict L)) = 720 ∧
        Nat.card H ∣ 720 ∧ (IsPGroup 2 H → Nat.card H ∣ 16) := by
  classical
  set N := nilp c with hN
  have hc : ∀ x y, B (c x) (c y) = B x y :=
    TauCeti.BilinForm.mem_isometryGroup_iff.1 (hH hcH)
  have hc4' : c ^ 4 = 1 := by rw [← hc4]; exact pow_orderOf_eq_one c
  have hN4 : ∀ v, N (N (N (N v))) = 0 := by
    intro v
    have h : N ^ 4 = 0 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, nilp_sq, nilp_sq, ← pow_mul, hc4']
      ext v
      simp
    have := LinearMap.congr_fun h v
    simpa [pow_succ, Module.End.mul_apply] using this
  have hN2 : ∃ x, N (N x) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsq : c ^ 2 = 1 := LinearEquiv.ext fun v => by
      have h := hcon v
      rw [← Module.End.mul_apply, ← pow_two, nilp_sq, nilp_apply, sub_eq_zero] at h
      exact h
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [hc4] at this
    norm_num at this
  have hj := finrank_ker_pow_succ N
  set k1 := finrank (ZMod 2) (ker N) with hk1
  set j1 := finrank (ZMod 2) ↥(range N ⊓ ker N) with hj1def
  have hj2le : finrank (ZMod 2) ↥(range (N ^ 2) ⊓ ker N) ≤ j1 :=
    Submodule.finrank_mono (range_pow_inf_ker_le N (by norm_num))
  have hj3le : finrank (ZMod 2) ↥(range (N ^ 3) ⊓ ker N) ≤ j1 :=
    Submodule.finrank_mono (range_pow_inf_ker_le N (by norm_num))
  have hk2 : finrank (ZMod 2) (ker (N ^ 2)) = k1 + j1 := by
    have := hj 1
    rwa [pow_one] at this
  have hk3 : finrank (ZMod 2) (ker (N ^ 3)) =
      k1 + j1 + finrank (ZMod 2) ↥(range (N ^ 2) ⊓ ker N) := by rw [hj 2, hk2]
  have hk4 : finrank (ZMod 2) (ker (N ^ 4)) =
      finrank (ZMod 2) (ker (N ^ 3)) + finrank (ZMod 2) ↥(range (N ^ 3) ⊓ ker N) := hj 3
  have hkV : finrank (ZMod 2) (ker (N ^ 4)) = finrank (ZMod 2) V := by
    have : ker (N ^ 4) = ⊤ := by
      ext v
      simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
      simpa [pow_succ, Module.End.mul_apply] using hN4 v
    rw [this, finrank_top]
  have hrank := LinearMap.finrank_range_add_finrank_ker N
  have hUN : U ≤ ker N := fun u hu => mem_fixSub.2 (hU c hcH u hu)
  have hUk : finrank (ZMod 2) U ≤ k1 := Submodule.finrank_mono hUN
  have hdim' : k1 + j1 ≤ finrank (ZMod 2) U + 1 := by
    rw [← hk2, hN, nilp_sq, ← fixSub_eq_ker]
    exact hdim
  have hj1pos : 1 ≤ j1 := by
    by_contra h0
    have hkN : finrank (ZMod 2) (ker N) = finrank (ZMod 2) V := by omega
    have htop : ker N = ⊤ := Submodule.eq_top_of_finrank_eq hkN
    obtain ⟨x, hx⟩ := hN2
    apply hx
    have h1 : N x ∈ ker N := htop ▸ Submodule.mem_top
    exact h1
  have hUeq : U = fixSub c := by
    rw [fixSub_eq_ker]
    exact Submodule.eq_of_le_of_finrank_eq hUN (by rw [← hk1]; omega)
  have hrank3 : finrank (ZMod 2) (range N) ≤ 3 := by omega
  have hkey : ∀ f, N f = 0 → ∀ y, B f (N y) = 0 := fun f hf y => form_nilp_eq_zero hc hf y
  have hsymm : ∀ x y, B x y = B y x := fun x y => by
    rw [← hB.neg_eq x y, ZMod.neg_eq_self_mod_two]
  have hN3 : ∃ x, N (N (N x)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hk3V : finrank (ZMod 2) (ker (N ^ 3)) = finrank (ZMod 2) V := by
      have : ker (N ^ 3) = ⊤ := by
        ext v
        simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
        simpa [pow_succ, Module.End.mul_apply] using hcon v
      rw [this, finrank_top]
    have hrank2 : finrank (ZMod 2) (range N) ≤ 2 := by omega
    obtain ⟨x, hx⟩ := hN2
    set e1 := N (N x)
    set e2 := N x
    have he1 : N e1 = 0 := hcon x
    have hli : LinearIndependent (ZMod 2) ![e1, e2] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg N hst
      rw [map_add, map_smul, map_smul, he1, smul_zero, zero_add, map_zero] at h1
      have ht : t = 0 := (smul_eq_zero.1 h1).resolve_right hx
      rw [ht, zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right hx, ht⟩
    have hspan : Submodule.span (ZMod 2) (Set.range ![e1, e2]) = range N := by
      refine Submodule.eq_of_le_of_finrank_le ?_ ?_
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact ⟨N x, rfl⟩
        · exact ⟨x, rfl⟩
      · rw [finrank_span_eq_card hli, Fintype.card_fin]
        exact hrank2
    have h13 : B e1 x = 0 := by
      have h := hc e2 x
      rw [apply_eq_add_nilp c e2, apply_eq_add_nilp c x] at h
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right] at h
      rw [hB.self_eq_zero, hkey e1 he1 x] at h
      linear_combination h
    have horth : ∀ v, B e1 v = 0 := by
      intro v
      obtain ⟨g, hg⟩ := exists_ker_add_of_nilp_mem_span (c := c) (w := ![e1, e2]) (z := ![e2, x])
        (fun i => by fin_cases i <;> rfl) (hspan ▸ LinearMap.mem_range_self N v)
      have hw := hkey _ hg
      have hv : v = (v - ∑ i, g i • ![e2, x] i) + ∑ i, g i • ![e2, x] i := by rw [sub_add_cancel]
      have h12 : B e1 e2 = 0 := hkey e1 he1 x
      rw [hv, LinearMap.BilinForm.add_right, hsymm e1, hkey _ hg]
      simp [Fin.sum_univ_two, h12, h13]
    exact hx (hnd.1 _ horth)
  obtain ⟨x, hx⟩ := hN3
  set e0 := N (N (N x)) with he0
  set e1 := N (N x) with he1
  set e2 := N x with he2
  have hNe0 : N e0 = 0 := hN4 x
  set e : Fin 4 → V := ![e0, e1, e2, x] with he
  have hli : LinearIndependent (ZMod 2) e := linearIndependent_chain (hN4 x) hx
  have hli3 : LinearIndependent (ZMod 2) ![e0, e1, e2] := by
    have h := hli.comp (Fin.castSucc : Fin 3 → Fin 4) (Fin.castSucc_injective 3)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hc0 : c e0 = e0 := by rw [apply_eq_add_nilp c e0, hNe0, add_zero]
  have hc1 : c e1 = e1 + e0 := apply_eq_add_nilp c e1
  have hc2 : c e2 = e2 + e1 := apply_eq_add_nilp c e2
  have hc3 : c x = x + e2 := apply_eq_add_nilp c x
  have hspan3 : Submodule.span (ZMod 2) (Set.range ![e0, e1, e2]) = range N := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact ⟨e1, rfl⟩
      · exact ⟨e2, rfl⟩
      · exact ⟨x, rfl⟩
    · rw [finrank_span_eq_card hli3, Fintype.card_fin]
      exact hrank3
  have h01 : B e0 e1 = 0 := hkey e0 hNe0 e2
  have h02 : B e0 e2 = 0 := hkey e0 hNe0 x
  have h03 : B e0 x = 1 := by
    apply zmod_two_eq_one_of_ne_zero
    intro h03
    apply hx
    apply hnd.1
    intro v
    obtain ⟨g, hg⟩ := exists_ker_add_of_nilp_mem_span (c := c) (w := ![e0, e1, e2])
      (z := ![e1, e2, x]) (fun i => by fin_cases i <;> rfl)
      (hspan3 ▸ LinearMap.mem_range_self N v)
    have hv : v = (v - ∑ i, g i • ![e1, e2, x] i) + ∑ i, g i • ![e1, e2, x] i := by
      rw [sub_add_cancel]
    have hw : B (v - ∑ i, g i • ![e1, e2, x] i) e0 = 0 := hkey _ hg e1
    rw [hv, LinearMap.BilinForm.add_right, hsymm e0, hw]
    simp [Fin.sum_univ_three, h01, h02, h03]
  have h12 : B e1 e2 = 1 := by
    have h := hc e1 x
    rw [hc1, hc3] at h
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right] at h
    rw [h03, h02] at h
    have htwo : (2 : ZMod 2) = 0 := rfl
    linear_combination h - htwo
  set L := Submodule.span (ZMod 2) (Set.range e) with hL
  have hLdim : finrank (ZMod 2) L = 4 := by rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hmemL : ∀ i, e i ∈ L := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hNL : ∀ v ∈ L, N v ∈ L := by
    intro v hv
    have hle : L.map N ≤ L := by
      rw [Submodule.map_span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · change N e0 ∈ L
        rw [hNe0]
        exact L.zero_mem
      · exact hmemL 0
      · exact hmemL 1
      · exact hmemL 2
    exact hle (Submodule.mem_map_of_mem hv)
  have hcL : ∀ v ∈ L, c v ∈ L := fun v hv => by
    rw [apply_eq_add_nilp]
    exact L.add_mem hv (hNL v hv)
  have hrangeL : range N ≤ L := by
    rw [← hspan3]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hnd' : (B.restrict L).Nondegenerate :=
    restrict_nondegenerate_of_gram hB hL h03 h12 h01 h02
  have halt : (B.restrict L).IsAlt := fun v => hB.self_eq_zero v
  have hcompl : IsCompl L (B.orthogonal L) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hnd'
  have hc4v : ∀ v, c (c (c (c v))) = v := fun v => by
    have := LinearEquiv.congr_fun hc4' v
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  have hcperp : ∀ v ∈ B.orthogonal L, c v ∈ B.orthogonal L := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
    intro l hl
    have hm : c (c (c l)) ∈ L := hcL _ (hcL _ (hcL l hl))
    change B l (c v) = 0
    rw [← hc4v l, hc]
    exact hv _ hm
  have hNperp : ∀ v ∈ B.orthogonal L, N v = 0 := by
    intro v hv
    have h1 : N v ∈ L := hrangeL (LinearMap.mem_range_self N v)
    have h2 : N v ∈ B.orthogonal L := by
      rw [nilp_apply]
      exact Submodule.sub_mem _ (hcperp v hv) hv
    have h3 : N v ∈ L ⊓ B.orthogonal L := Submodule.mem_inf.2 ⟨h1, h2⟩
    rwa [hcompl.inf_eq_bot, Submodule.mem_bot] at h3
  have hfixperp : ∀ h ∈ H, ∀ v ∈ B.orthogonal L, h v = v := fun h hh v hv =>
    hU h hh v (hUeq ▸ (hNperp v hv : v ∈ ker N))
  have hpres : ∀ h ∈ H, ∀ v ∈ L, h v ∈ L := by
    intro h hh v hv
    have hiso := TauCeti.BilinForm.mem_isometryGroup_iff.1 (hH hh)
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl L,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    change B w (h v) = 0
    rw [← hfixperp h hh w hw, hiso, hsymm]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.1 hw) v hv
  have hmap : ∀ h : H, L.map (h : V ≃ₗ[ZMod 2] V).toLinearMap = L := fun h =>
    le_antisymm (Submodule.map_le_iff_le_comap.2 fun v hv => hpres h h.2 v hv)
      fun v hv => ⟨((h⁻¹ : H) : V ≃ₗ[ZMod 2] V) v, hpres _ (inv_mem h.2) v hv,
        (h : V ≃ₗ[ZMod 2] V).apply_symm_apply v⟩
  let ρ : H →* TauCeti.BilinForm.isometryGroup (B.restrict L) :=
    { toFun := fun h => ⟨(h : V ≃ₗ[ZMod 2] V).ofSubmodules L L (hmap h),
        TauCeti.BilinForm.mem_isometryGroup_iff.2 fun u w =>
          TauCeti.BilinForm.mem_isometryGroup_iff.1 (hH h.2) u w⟩
      map_one' := Subtype.ext (LinearEquiv.ext fun _ => Subtype.ext rfl)
      map_mul' := fun _ _ => Subtype.ext (LinearEquiv.ext fun _ => Subtype.ext rfl) }
  have hρ : ∀ (h : H) (v : L), (((ρ h : L ≃ₗ[ZMod 2] L) v : L) : V) =
      (h : V ≃ₗ[ZMod 2] V) v := fun _ _ => rfl
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro h h1
    have hL1 : ∀ v ∈ L, (h : V ≃ₗ[ZMod 2] V) v = v := fun v hv => by
      have := congrArg (fun φ : TauCeti.BilinForm.isometryGroup (B.restrict L) =>
        (((φ : L ≃ₗ[ZMod 2] L) ⟨v, hv⟩ : L) : V)) h1
      simpa [hρ] using this
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have hv : v ∈ L ⊔ B.orthogonal L := hcompl.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨l, hl, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, hL1 l hl, hfixperp h h.2 w hw]
    rfl
  have hLV : finrank (ZMod 2) L = 2 * 2 := hLdim
  have hcardSp : Nat.card (TauCeti.BilinForm.isometryGroup (B.restrict L)) = 720 := by
    rw [card_isometryGroup 2 (B.restrict L) halt hnd' hLV, Nat.card_zmod]
    decide
  have hiso : Nonempty (TauCeti.BilinForm.isometryGroup (B.restrict L) ≃* StatedSp 2 (ZMod 2)) := by
    obtain ⟨bL, hbL, -⟩ := exists_completeIsotropicFlag halt hnd' hLV (W := ⊥)
      (fun u hu w _ => by rw [(Submodule.mem_bot _).1 hu, LinearMap.BilinForm.zero_left])
    have hmat : LinearMap.BilinForm.toMatrix bL (B.restrict L) =
        LinearMap.BilinForm.toMatrix (Pi.basisFun (ZMod 2) (Fin 2 ⊕ Fin 2))
          (CFSG.LocalAnalysis.ComponentInitial.pairedSympForm (ZMod 2) 2) :=
      hbL.trans toMatrix_pairedSympForm.symm
    set φ := bL.isometryEquivOfToMatrixEq (Pi.basisFun (ZMod 2) (Fin 2 ⊕ Fin 2)) hmat
    have hcong : LinearMap.BilinForm.congr φ.toLinearEquiv (B.restrict L) =
        CFSG.LocalAnalysis.ComponentInitial.pairedSympForm (ZMod 2) 2 := by
      refine LinearMap.BilinForm.ext fun u w => ?_
      rw [LinearMap.BilinForm.congr_apply, ← φ.map_app (φ.toLinearEquiv.symm w)
        (φ.toLinearEquiv.symm u)]
      exact congrArg₂ (fun a b => CFSG.LocalAnalysis.ComponentInitial.pairedSympForm (ZMod 2) 2 a b)
        (φ.toLinearEquiv.apply_symm_apply u) (φ.toLinearEquiv.apply_symm_apply w)
    exact ⟨(TauCeti.BilinForm.isometryGroupCongr (B.restrict L) φ.toLinearEquiv).trans
      ((MulEquiv.subgroupCongr (congrArg TauCeti.BilinForm.isometryGroup hcong)).trans
        CFSG.ComponentClassification.CatalogueBSymplecticB.statedSpIsometryEquiv.symm)⟩
  have hcardH : Nat.card H ∣ 720 := hcardSp ▸ Subgroup.card_dvd_of_injective ρ hρinj
  have hfinV : Finite V := Module.finite_of_finite (ZMod 2)
  have hfinG : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  refine ⟨hUeq, hLdim ▸ Submodule.finrank_le L, L, hLdim, hcL, hnd', hcompl,
    ⟨e, hli, rfl, hc0, hc1, hc2, hc3⟩, hfixperp, hpres, ρ, hρinj, hρ, hiso, hcardSp, hcardH,
    fun hp => ?_⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := H)).1 hp
  rw [hk] at hcardH ⊢
  exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 45)).dvd_of_dvd_mul_left
    (by simpa using hcardH)

end CFSG.LocalAnalysis.GorensteinLyons
