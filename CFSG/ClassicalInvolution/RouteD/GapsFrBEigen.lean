module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain
public import CFSG.ClassicalInvolution.RouteD.GapsOrthD4Centralizer

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

section Eigen

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem frame_eigen_of_commute_La (h2 : (2 : K) ≠ 0)
    (F : CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame Q) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hcomm : ∀ A : SL(2, K), g * F.La A = F.La A * g) :
    (∀ x ∈ F.span, g x = x) ∨ (∀ x ∈ F.span, g x = -x) := by
  have hg : g * F.La (-1) = F.La (-1) * g := hcomm (-1)
  have hT : ∀ (A : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K),
      F.transport g ((A : Matrix (Fin 2) (Fin 2) K) * X) =
        (A : Matrix (Fin 2) (Fin 2) K) * F.transport g X := by
    intro A X
    rw [transport_apply, transport_apply, ← La_apply_incl, ← LinearEquiv.mul_apply, hcomm A,
      LinearEquiv.mul_apply, coords_La]
  have hT2 : ∀ X, F.transport g (F.transport g X) = X := by
    intro X
    have := LinearMap.congr_fun (transport_mul (F := F) (g := g) (h := g) h2 hg) X
    rw [hg2, transport_one] at this
    simpa using this.symm
  have hdet : ∀ X, (F.transport g X).det = X.det := by
    intro X
    have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (transportEquiv_mem_orthogonalGroup h2 hgO hg) X
    simpa [detQ_apply, transportEquiv_apply] using this
  rcases eq_one_or_eq_neg_one_of_commute_left h2 hT hT2 hdet with h | h
  · left
    intro x hx
    rw [mem_span_iff] at hx
    rw [hx, ← incl_transport h2 hg, h]
    rfl
  · right
    intro x hx
    rw [mem_span_iff] at hx
    rw [hx, ← incl_transport h2 hg, h]
    simp

theorem negSpace_le_eigenspace_of_commute (h2 : (2 : K) ≠ 0) {L : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (hL : IsFundamental Q L i) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hcomm : ∀ l ∈ L, g * l = l * g) :
    negSpace i ≤ Module.End.eigenspace (g : Module.End K V) 1 ∨
      negSpace i ≤ Module.End.eigenspace (g : Module.End K V) (-1) := by
  obtain ⟨F, rfl, rfl⟩ := hL
  rw [negSpace_La_neg_one h2]
  rcases frame_eigen_of_commute_La h2 F hgO hg2 (fun A => hcomm _ ⟨A, rfl⟩) with h | h
  · left
    intro x hx
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact h x hx
  · right
    intro x hx
    rw [Module.End.mem_eigenspace_iff, neg_smul, one_smul]
    exact h x hx

theorem polar_eigenspace_orth (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x y : V} (hx : g x = x) (hy : g y = -y) :
    polar Q x y = 0 := by
  have h1 : polar Q (g x) (g y) = polar Q x y := by
    simp only [polar, ← map_add g, map_of_mem hgO]
  rw [hx, hy, polar_neg_right] at h1
  have : (2 : K) * polar Q x y = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp this).resolve_left h2

end Eigen

section Chain

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem polar_negSpace_of_distinguish (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {Li Lj D : Subgroup (V ≃ₗ[K] V)} {ii ij id : V ≃ₗ[K] V} (hi : IsFundamental Q Li ii)
    (hj : IsFundamental Q Lj ij) (hd : IsFundamental Q D id) (hk : Commutes Li Lj)
    (hne_i : D ≠ Li) (hne_j : D ≠ Lj) (hinv_i : ModelInvComm (scalars K V) D Li)
    (hinv_j : ModelInvComm (scalars K V) D Lj) (hdist : ¬ (Commutes D Li ↔ Commutes D Lj)) :
    ∀ x ∈ negSpace ii, ∀ y ∈ negSpace ij, polar Q x y = 0 := by
  rcases orth_or_twin hodd hi hj hk with h | h
  · exact h
  · exact absurd h (ne_of_distinguish hodd hdim hi hj hd hne_i hne_j hinv_i hinv_j hdist)

theorem polar_chainSpan_of_commutes (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {r s : ℕ} (hs : 2 ≤ s) (hsr : s ≤ r) {c : ℕ → Subgroup (V ≃ₗ[K] V)}
    (hc : IsChain (scalars K V) (fundSet Q) r c) {i : ℕ → V ≃ₗ[K] V}
    (hi : ∀ a < r, IsFundamental Q (c a) (i a)) {X : Subgroup (V ≃ₗ[K] V)} {iX : V ≃ₗ[K] V}
    (hX : IsFundamental Q X iX) (hXc : ∀ a < s, Commutes X (c a)) :
    ∀ x ∈ negSpace iX, ∀ y ∈ chainSpan i s, polar Q x y = 0 := by
  have nc : ∀ a', a' + 1 < r → ¬ Commutes (c a') (c (a' + 1)) := fun a' h' => (hc.adj a' h').2.1
  intro x hx
  refine polar_chainSpan (fun a ha => ?_)
  rcases orth_or_twin hodd hX (hi a (by omega)) (hXc a ha) with h | h
  · exact h x hx
  · exfalso
    by_cases h1 : a + 1 < s
    · refine ne_of_distinguish hodd hdim hX (hi a (by omega)) (hi (a + 1) (by omega)) ?_ ?_ ?_ ?_
        ?_ h
      · intro e
        apply nc a (by omega)
        have := hXc a ha
        rw [← e] at this
        exact this.symm
      · exact fun e => (hc.adj a (by omega)).1 e.symm
      · exact modelInvComm_of_commutes hodd (hi (a + 1) (by omega)) hX (hXc (a + 1) h1).symm
      · exact (ModelInvComm.of_adj (hc.adj a (by omega))).symm'
      · intro hiff
        exact nc a (by omega) (hiff.mp (hXc (a + 1) h1).symm).symm
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      refine ne_of_distinguish hodd hdim hX (hi (a' + 1) (by omega)) (hi a' (by omega)) ?_ ?_ ?_ ?_
        ?_ h
      · intro e
        have := hXc (a' + 1) ha
        rw [← e] at this
        exact nc a' (by omega) this
      · exact fun e => (hc.adj a' (by omega)).1 e
      · exact modelInvComm_of_commutes hodd (hi a' (by omega)) hX (hXc a' (by omega)).symm
      · exact ModelInvComm.of_adj (hc.adj a' (by omega))
      · intro hiff
        exact nc a' (by omega) (hiff.mp (hXc a' (by omega)).symm)

omit [Finite K] in
theorem finrank_eigen_inf_orth_le (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0)
    {g : V ≃ₗ[K] V} {S : Submodule K V}
    (hS : ∀ s ∈ S, ∀ y ∈ Module.End.eigenspace (g : Module.End K V) 1, polar Q y s = 0) :
    Module.finrank K ↥(Module.End.eigenspace (g : Module.End K V) (-1) ⊓
        LinearMap.BilinForm.orthogonal (polarBilin Q) S) +
      Module.finrank K ↥(Module.End.eigenspace (g : Module.End K V) 1) +
      Module.finrank K ↥S ≤ Module.finrank K V := by
  set Em := Module.End.eigenspace (g : Module.End K V) (-1) with hEm
  set Ep := Module.End.eigenspace (g : Module.End K V) 1 with hEp
  set P := Em ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) S with hP
  have hEp_orth : Ep ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) S := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    show polarBilin Q y x = 0
    rw [polarBilin_apply_apply, polar_comm]
    exact hS y hy x hx
  have hdisj : Disjoint P Ep := by
    rw [Submodule.disjoint_def]
    intro x hxP hxE
    have hx1 : g x = -x := by
      have := (Submodule.mem_inf.mp hxP).1
      rwa [hEm, Module.End.mem_eigenspace_iff, neg_smul, one_smul] at this
    have hx2 : g x = x := by
      rwa [hEp, Module.End.mem_eigenspace_iff, one_smul] at hxE
    have : (2 : K) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hx2]
      rw [hx1]
      exact neg_add_cancel x
    exact (smul_eq_zero.mp this).resolve_left h2
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq P Ep
  rw [hdisj.eq_bot, finrank_bot] at hsup
  have hle : P ⊔ Ep ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) S :=
    sup_le inf_le_right hEp_orth
  have h1 := Submodule.finrank_mono hle
  have h2' := LinearMap.BilinForm.finrank_orthogonal hQ S
  have h3 : Module.finrank K ↥S ≤ Module.finrank K V := Submodule.finrank_le _
  omega

end Chain

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem eq_zero_of_polar_negSpace (h2 : (2 : K) ≠ 0) {L : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (hL : IsFundamental Q L i) {x : V} (hx : x ∈ negSpace i)
    (h : ∀ y ∈ negSpace i, polar Q x y = 0) : x = 0 := by
  obtain ⟨F, rfl, rfl⟩ := hL
  rw [negSpace_La_neg_one h2] at hx h
  have hp : x ∈ F.perp := by
    rw [mem_perp_iff_forall_incl]
    intro Y
    exact h _ ⟨Y, rfl⟩
  exact Submodule.disjoint_def.mp (isCompl_span_perp (F := F)).disjoint x hx hp

theorem model_contradiction (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate) {m : ℕ}
    (hm : 8 ≤ m) (hdimV : Module.finrank K V = 2 * m + 1) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hdimE : Module.finrank K ↥(Module.End.eigenspace (g : Module.End K V) 1) = 3)
    {c : ℕ → Subgroup (V ≃ₗ[K] V)} (hc : IsChain (scalars K V) (fundSet Q) (m - 4) c)
    {LM : Subgroup (V ≃ₗ[K] V)} (hLM : LM ∈ fundSet Q) {Y : Fin 3 → Subgroup (V ≃ₗ[K] V)}
    (hY : ∀ k, Y k ∈ fundSet Q) (hYinj : Function.Injective Y)
    (hfixc : ∀ a < m - 6, ∀ l ∈ c a, g * l = l * g) (hfixM : ∀ l ∈ LM, g * l = l * g)
    (hfixY : ∀ k, ∀ l ∈ Y k, g * l = l * g) (hMc : ∀ a < m - 6, Commutes LM (c a))
    (hYc : ∀ k, ∀ a < m - 6, Commutes (Y k) (c a)) (hYM : ∀ k, Commutes (Y k) LM)
    (hD : ∀ k, ModelAdj (scalars K V) (c (m - 6)) (Y k)) (hDM : Commutes (c (m - 6)) LM) :
    False := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hdim : 9 ≤ Module.finrank K V := by omega
  obtain ⟨i, hi⟩ := exists_chain_inv hc
  obtain ⟨iM, hiM⟩ := hLM
  choose iY hiY using hY
  set Em := Module.End.eigenspace (g : Module.End K V) (-1) with hEm
  have hneg : ∀ {X : Subgroup (V ≃ₗ[K] V)} {iX : V ≃ₗ[K] V}, IsFundamental Q X iX →
      (∀ l ∈ X, g * l = l * g) → negSpace iX ≤ Em := by
    intro X iX hX hfix
    rcases negSpace_le_eigenspace_of_commute h2 hX hgO hg2 hfix with h | h
    · exfalso
      have h1 := Submodule.finrank_mono h
      rw [hdimE, finrank_negSpace hodd hX] at h1
      omega
    · exact h
  have hSig : ∀ x ∈ negSpace iM ⊔ chainSpan i (m - 6), ∀ y ∈ Module.End.eigenspace
      (g : Module.End K V) 1, polar Q y x = 0 := by
    intro x hx y hy
    have hy' : g y = y := by
      rwa [Module.End.mem_eigenspace_iff, one_smul] at hy
    have horth : ∀ {X : Subgroup (V ≃ₗ[K] V)} {iX : V ≃ₗ[K] V}, IsFundamental Q X iX →
        (∀ l ∈ X, g * l = l * g) → ∀ z ∈ negSpace iX, polar Q y z = 0 := by
      intro X iX hX hfix z hz
      have := hneg hX hfix hz
      rw [hEm, Module.End.mem_eigenspace_iff, neg_smul, one_smul] at this
      exact polar_eigenspace_orth h2 hgO hy' this
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    rw [polar_add_right, horth hiM hfixM u hu, zero_add]
    refine polar_chainSpan (fun a ha => ?_) w hw
    exact horth (hi a (by omega)) (hfixc a ha)
  have hMorth : ∀ x ∈ negSpace iM, ∀ y ∈ chainSpan i (m - 6), polar Q x y = 0 :=
    polar_chainSpan_of_commutes hodd hdim (by omega) (by omega) hc hi hiM hMc
  have hdisj : Disjoint (negSpace iM) (chainSpan i (m - 6)) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    refine eq_zero_of_polar_negSpace h2 hiM hx fun y hy => ?_
    rw [polar_comm]
    exact hMorth y hy x hx'
  have hspan := finrank_chainSpan hodd hdim (by omega : 4 ≤ m - 4) hc hi (m - 6) (by omega)
    (by omega)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (negSpace iM) (chainSpan i (m - 6))
  rw [hdisj.eq_bot, finrank_bot, finrank_negSpace hodd hiM] at hsup
  have hdimSig : 2 * m - 6 ≤ Module.finrank K ↥(negSpace iM ⊔ chainSpan i (m - 6)) := by omega
  have hcount := finrank_eigen_inf_orth_le hQ h2 hSig
  rw [hdimE, hdimV] at hcount
  set P := Em ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q)
    (negSpace iM ⊔ chainSpan i (m - 6)) with hP
  have hP4 : Module.finrank K ↥P ≤ 4 := by omega
  have hDne : c (m - 6) ≠ LM := by
    intro e
    have h1 := hMc (m - 7) (by omega)
    have h2'' := hc.adj (m - 7) (by omega)
    have h3 : c (m - 7 + 1) = c (m - 6) := by rw [show m - 7 + 1 = m - 6 by omega]
    refine h2''.2.1 ?_
    rw [h3, e]
    exact h1.symm
  have hYP : ∀ k, negSpace (iY k) = P := by
    intro k
    have hle : negSpace (iY k) ≤ P := by
      refine le_inf (hneg (hiY k) (hfixY k)) ?_
      intro y hy
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro s hs
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hs
      show polarBilin Q _ y = 0
      rw [polarBilin_apply_apply, polar_add_left]
      have h1 : polar Q u y = 0 :=
        polar_negSpace_of_distinguish hodd hdim hiM (hiY k) (hi (m - 6) (by omega))
          (hYM k).symm hDne (hD k).1 (modelInvComm_of_commutes hodd (hi (m - 6) (by omega)) hiM hDM)
          (ModelInvComm.of_adj (hD k)) (fun hiff => (hD k).2.1 (hiff.mp hDM)) u hu y hy
      have h2' : polar Q w y = 0 := by
        rw [polar_comm]
        exact polar_chainSpan_of_commutes hodd hdim (by omega) (by omega) hc hi (hiY k)
          (hYc k) y hy w hw
      rw [h1, h2', add_zero]
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [finrank_negSpace hodd (hiY k)]
    exact hP4
  have hii : ∀ k, iY k = iY 0 := fun k =>
    involution_eq_of_negSpace_eq h2 (hiY k) (hiY 0) (by rw [hYP k, hYP 0])
  obtain ⟨L', hL', hne, -, huniq⟩ := IsFundamental.exists_twin hodd (hiY 0)
  have h1 : Y 1 = Y 0 ∨ Y 1 = L' := huniq _ (by rw [← hii 1]; exact hiY 1)
  have h2'' : Y 2 = Y 0 ∨ Y 2 = L' := huniq _ (by rw [← hii 2]; exact hiY 2)
  have n10 : Y 1 ≠ Y 0 := fun h => by have := hYinj h; simp at this
  have n20 : Y 2 ≠ Y 0 := fun h => by have := hYinj h; simp at this
  have n21 : Y 2 ≠ Y 1 := fun h => by have := hYinj h; simp at this
  rcases h1 with h1 | h1
  · exact n10 h1
  · rcases h2'' with h2'' | h2''
    · exact n20 h2''
    · exact n21 (h2''.trans h1.symm)

end Model

end CFSG.ClassicalInvolution.RouteD.Gaps
