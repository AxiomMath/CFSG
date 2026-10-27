module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBlock

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.BCDEven

open Polynomial Module Submodule CFSG.LocalAnalysis.RankFourTheoremC
open LinearMap (BilinForm)

section Form

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}
  {y : Module.End K V}

theorem orthogonal_invt {p : ℕ} (hp : 0 < p) (hyp : y ^ p = 1)
    (hy : ∀ u v, B (y u) (y v) = B u v) {W : Submodule K V} (hW : ∀ x ∈ W, y x ∈ W) :
    ∀ x ∈ B.orthogonal W, y x ∈ B.orthogonal W := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
  intro w hw
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have h1 : y ((y ^ n) w) = w := by
    rw [← Module.End.mul_apply, ← pow_succ', hyp, Module.End.one_apply]
  have h2 : (y ^ n) w ∈ W := pow_apply_mem hW n hw
  have h3 := hx _ h2
  calc B w (y x) = B (y ((y ^ n) w)) (y x) := by rw [h1]
    _ = B ((y ^ n) w) x := hy _ _
    _ = 0 := h3

theorem disjoint_sup_orthogonal (hrefl : B.IsRefl) {D P : Submodule K V}
    (hDP : ∀ d ∈ D, ∀ x ∈ P, B d x = 0) (hD : Disjoint D (B.orthogonal D))
    (hP : Disjoint P (B.orthogonal P)) : Disjoint (D ⊔ P) (B.orthogonal (D ⊔ P)) := by
  rw [Submodule.disjoint_def] at hD hP ⊢
  intro x hx hx'
  obtain ⟨d, hd, p', hp', rfl⟩ := Submodule.mem_sup.1 hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx'
  have hdD : d ∈ B.orthogonal D := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    have := hx' z (Submodule.mem_sup_left hz)
    rw [map_add, hDP z hz p' hp', add_zero] at this
    exact this
  have hpP : p' ∈ B.orthogonal P := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    have := hx' z (Submodule.mem_sup_right hz)
    rw [map_add, hrefl _ _ (hDP d hd z hz), zero_add] at this
    exact this
  rw [hD d hd hdD, hP p' hp' hpP, add_zero]

variable [Module.Finite K V]

theorem exists_nondeg_invt_le {p e : ℕ} (hyp : y ^ p = 1) (hp0 : (p : K) ≠ 0) (hp : 0 < p)
    (hdeg : ∀ f : K[X], Irreducible f → f ∣ X ^ p - 1 → f.natDegree ≤ e)
    (hrefl : B.IsRefl) (hnd : B.Nondegenerate) (hy : ∀ u v, B (y u) (y v) = B u v)
    {N : Submodule K V} (hN : ∀ x ∈ N, y x ∈ N) (hNd : Disjoint N (B.orthogonal N))
    (hN0 : N ≠ ⊥) :
    ∃ P : Submodule K V, (∀ x ∈ P, y x ∈ P) ∧ P ≤ N ∧ P ≠ ⊥ ∧
      Disjoint P (B.orthogonal P) ∧ Module.finrank K P ≤ 2 * e := by
  obtain ⟨S, hS, hSN, hS0, hSe⟩ := exists_invt_le hyp hp hdeg hN hN0
  set R := S ⊓ B.orthogonal S with hR
  have hSperp := orthogonal_invt hp hyp hy hS
  have hRinv : ∀ x ∈ R, y x ∈ R := fun x hx => ⟨hS x hx.1, hSperp x hx.2⟩
  by_cases hR0 : R = ⊥
  · exact ⟨S, hS, hSN, hS0, disjoint_iff.2 hR0, by omega⟩
  have hRiso : ∀ r ∈ R, ∀ r' ∈ R, B r r' = 0 := fun r hr r' hr' =>
    (LinearMap.BilinForm.mem_orthogonal_iff.1 hr'.2) r hr.1
  have hRN : R ≤ N := inf_le_left.trans hSN
  set A := B.orthogonal R ⊓ N with hA
  have hAinv : ∀ x ∈ A, y x ∈ A := fun x hx =>
    ⟨orthogonal_invt hp hyp hy hRinv x hx.1, hN x hx.2⟩
  have hAN : A ≤ N := inf_le_right
  have hRA : R ≤ A := fun r hr => ⟨LinearMap.BilinForm.mem_orthogonal_iff.2 fun z hz =>
    hRiso z hz r hr, hRN hr⟩
  have hsemi := isSemisimple_of_pow_eq_one hyp hp0
  obtain ⟨T', hT', hAT'⟩ := Module.End.isSemisimple_iff.1 hsemi A
    ((Module.End.mem_invtSubmodule y).2 hAinv)
  have hT'inv : ∀ x ∈ T', y x ∈ T' := fun x hx => (Module.End.mem_invtSubmodule y).1 hT' hx
  set T := T' ⊓ N with hT
  have hTinv : ∀ x ∈ T, y x ∈ T := fun x hx => ⟨hT'inv x hx.1, hN x hx.2⟩
  have hTN : T ≤ N := inf_le_right
  have hNsup : A ⊔ T = N := by
    rw [hT, ← sup_inf_assoc_of_le T' hAN, hAT'.sup_eq_top, top_inf_eq]
  have hAT : A ⊓ T = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have : x ∈ A ⊓ T' := ⟨hx.1, hx.2.1⟩
    rw [hAT'.inf_eq_bot] at this
    exact this
  have hcompl : IsCompl N (B.orthogonal N) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).2 hNd
  have hperp_sup : B.orthogonal R ⊔ N = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hcompl.sup_eq_top]
    exact sup_le le_sup_right
      ((LinearMap.BilinForm.orthogonal_le hRN).trans le_sup_left)
  have hdimR := LinearMap.BilinForm.finrank_orthogonal hnd R
  have hd1 := Submodule.finrank_sup_add_finrank_inf_eq (B.orthogonal R) N
  rw [hperp_sup, finrank_top] at hd1
  have hRV : Module.finrank K R ≤ Module.finrank K V := Submodule.finrank_le R
  have hdimA : Module.finrank K A + Module.finrank K R = Module.finrank K N := by
    have h' : Module.finrank K (B.orthogonal R ⊓ N : Submodule K V) = Module.finrank K A := rfl
    have hNA : Module.finrank K N ≤ Module.finrank K V := Submodule.finrank_le N
    omega
  have hd2 := Submodule.finrank_sup_add_finrank_inf_eq A T
  rw [hNsup, hAT, finrank_bot] at hd2
  have hdimT : Module.finrank K T = Module.finrank K R := by omega
  have hRT : R ⊓ T = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have : x ∈ A ⊓ T := ⟨hRA hx.1, hx.2⟩
    rw [hAT] at this
    exact this
  have hd3 := Submodule.finrank_sup_add_finrank_inf_eq R T
  rw [hRT, finrank_bot] at hd3
  have hRS : Module.finrank K R ≤ Module.finrank K S := Submodule.finrank_mono inf_le_left
  refine ⟨R ⊔ T, ?_, sup_le hRN hTN, ?_, ?_, by omega⟩
  · intro x hx
    obtain ⟨r, hr, t, ht, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hRinv r hr) (hTinv t ht)
  · intro h
    exact hR0 (eq_bot_iff.2 (le_sup_left.trans h.le))
  ·
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨r, hr, t, ht, rfl⟩ := Submodule.mem_sup.1 hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx'
    have htA : t ∈ A := by
      refine ⟨LinearMap.BilinForm.mem_orthogonal_iff.2 fun z hz => ?_, hTN ht⟩
      have := hx' z (Submodule.mem_sup_left hz)
      rw [map_add, hRiso z hz r hr, zero_add] at this
      exact this
    have ht0 : t = 0 := by
      have : t ∈ A ⊓ T := ⟨htA, ht⟩
      rw [hAT] at this
      exact (Submodule.mem_bot K).1 this
    subst ht0
    have hrperp : r ∈ B.orthogonal N := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have hn' : n ∈ A ⊔ T := hNsup ▸ hn
      obtain ⟨a, ha, t', ht', rfl⟩ := Submodule.mem_sup.1 hn'
      rw [map_add, LinearMap.add_apply]
      have h1 : B a r = 0 :=
        hrefl r a ((LinearMap.BilinForm.mem_orthogonal_iff.1 ha.1) r hr)
      have h2 : B t' r = 0 := by
        have := hx' t' (Submodule.mem_sup_right ht')
        rwa [add_zero] at this
      rw [h1, h2, add_zero]
    have hr0 : r = 0 := (Submodule.disjoint_def.1 hNd) r (hRN hr) hrperp
    rw [hr0, add_zero]

theorem exists_nondeg_window {p e c : ℕ} (hyp : y ^ p = 1) (hp0 : (p : K) ≠ 0) (hp : 0 < p)
    (he : 0 < e) (hdeg : ∀ f : K[X], Irreducible f → f ∣ X ^ p - 1 → f.natDegree ≤ e)
    (hrefl : B.IsRefl) (hnd : B.Nondegenerate) (hy : ∀ u v, B (y u) (y v) = B u v)
    (hc : c * e ≤ Module.finrank K V) :
    ∃ W : Submodule K V, (∀ x ∈ W, y x ∈ W) ∧ Disjoint W (B.orthogonal W) ∧
      c * e ≤ Module.finrank K W ∧ Module.finrank K W < (c + 2) * e := by
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · refine ⟨⊥, fun x hx => by simp [(Submodule.mem_bot K).1 hx], disjoint_bot_left, ?_, ?_⟩
    · simp
    · simp only [finrank_bot, zero_add]
      omega
  have hce : 0 < c * e := Nat.mul_pos hc0 he
  let S : Set ℕ := {m | ∃ W : Submodule K V, (∀ x ∈ W, y x ∈ W) ∧
    Disjoint W (B.orthogonal W) ∧ Module.finrank K W = m ∧ m < c * e}
  have hS0 : S.Nonempty :=
    ⟨0, ⊥, fun x hx => by simp [(Submodule.mem_bot K).1 hx], disjoint_bot_left, by simp, hce⟩
  have hSb : BddAbove S := ⟨c * e, fun m ⟨_, _, _, _, hm⟩ => hm.le⟩
  obtain ⟨W, hW, hWd, hWm, hWlt⟩ := Nat.sSup_mem hS0 hSb
  set N := B.orthogonal W with hN
  have hNinv : ∀ x ∈ N, y x ∈ N := orthogonal_invt hp hyp hy hW
  have hNd : Disjoint N (B.orthogonal N) := by
    rw [hN, LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]
    exact hWd.symm
  have hdimN : Module.finrank K N = Module.finrank K V - Module.finrank K W :=
    LinearMap.BilinForm.finrank_orthogonal hnd W
  have hN0 : N ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdimN
    omega
  obtain ⟨P, hP, hPN, hP0, hPd, hPe⟩ :=
    exists_nondeg_invt_le hyp hp0 hp hdeg hrefl hnd hy hNinv hNd hN0
  have hWP : ∀ d ∈ W, ∀ x ∈ P, B d x = 0 := fun d hd x hx =>
    LinearMap.BilinForm.mem_orthogonal_iff.1 (hPN hx) d hd
  have hWPdis : Disjoint W P := hWd.mono_right hPN
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq W P
  rw [hWPdis.eq_bot, finrank_bot] at hfin
  have hP1 : 1 ≤ Module.finrank K P := Submodule.one_le_finrank_iff.2 hP0
  have hWPinv : ∀ x ∈ W ⊔ P, y x ∈ W ⊔ P := by
    intro x hx
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hW w hw) (hP u hu)
  have hlt : c * e ≤ Module.finrank K ↥(W ⊔ P) := by
    by_contra hlt
    rw [not_le] at hlt
    have hmem : Module.finrank K ↥(W ⊔ P) ∈ S :=
      ⟨W ⊔ P, hWPinv, disjoint_sup_orthogonal hrefl hWP hWd hPd, rfl, hlt⟩
    have := le_csSup hSb hmem
    omega
  refine ⟨W ⊔ P, hWPinv, disjoint_sup_orthogonal hrefl hWP hWd hPd, hlt, ?_⟩
  have : (c + 2) * e = c * e + 2 * e := by ring
  omega

end Form

end CFSG.LocalAnalysis.RankFourTheoremC.BCDEven
