module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson
import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeN
public import CFSG.RankThree.GF2n.Smith81.OrthRootInvol
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.GF2n.Smith81
open CFSG.RankThree.OrthogonalInvolutions QuadraticMap Module

variable {K : Type} [Field K] [CharP K 2] [Finite K] {N : Type} [AddCommGroup N] [Module K N]
  [FiniteDimensional K N] {Q : QuadraticForm K N}

section Aux

private structure HypPairs (Q : QuadraticForm K N) (e f a a' : N) : Prop where
  e_sing : Q e = 0
  f_sing : Q f = 0
  a_sing : Q a = 0
  a'_sing : Q a' = 0
  ef : polar Q e f = 1
  aa' : polar Q a a' = 1
  ea : polar Q e a = 0
  ea' : polar Q e a' = 0
  fa : polar Q f a = 0
  fa' : polar Q f a' = 0

omit [CharP K 2] [Finite K] [FiniteDimensional K N] in
private theorem HypPairs.linearIndependent_five {e f a a' x : N} (hP : HypPairs Q e f a a')
    (hx0 : x ≠ 0) (hxe : polar Q e x = 0) (hxf : polar Q f x = 0) (hxa : polar Q a x = 0)
    (hxa' : polar Q a' x = 0) : LinearIndependent K ![e, f, a, a', x] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  replace hg : g 0 • e + g 1 • f + g 2 • a + g 3 • a' + g 4 • x = 0 := by
    simpa [Fin.sum_univ_five] using hg
  have hR : ∀ z : N, g 0 * polar Q e z + g 1 * polar Q f z + g 2 * polar Q a z +
      g 3 * polar Q a' z + g 4 * polar Q x z = 0 := fun z => by
    have := congrArg (fun w => polar Q w z) hg
    simpa only [polar_add_left, polar_smul_left_eq, polar_zero_left] using this
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hP.ef
  have ha'a : polar Q a' a = 1 := by rw [polar_comm]; exact hP.aa'
  have hae : polar Q a e = 0 := by rw [polar_comm]; exact hP.ea
  have ha'e : polar Q a' e = 0 := by rw [polar_comm]; exact hP.ea'
  have haf : polar Q a f = 0 := by rw [polar_comm]; exact hP.fa
  have ha'f : polar Q a' f = 0 := by rw [polar_comm]; exact hP.fa'
  have hxe' : polar Q x e = 0 := by rw [polar_comm]; exact hxe
  have hxf' : polar Q x f = 0 := by rw [polar_comm]; exact hxf
  have hxa'' : polar Q x a = 0 := by rw [polar_comm]; exact hxa
  have hxa''' : polar Q x a' = 0 := by rw [polar_comm]; exact hxa'
  have g0 : g 0 = 0 := by
    have := hR f
    simp only [hP.ef, polar_self_eq_zero hP.f_sing, haf, ha'f, hxf'] at this
    linear_combination this
  have g1 : g 1 = 0 := by
    have := hR e
    simp only [polar_self_eq_zero hP.e_sing, hfe, hae, ha'e, hxe'] at this
    linear_combination this
  have g2 : g 2 = 0 := by
    have := hR a'
    simp only [hP.ea', hP.fa', hP.aa', polar_self_eq_zero hP.a'_sing, hxa'''] at this
    linear_combination this
  have g3 : g 3 = 0 := by
    have := hR a
    simp only [hP.ea, hP.fa, polar_self_eq_zero hP.a_sing, ha'a, hxa''] at this
    linear_combination this
  have g4 : g 4 = 0 := by
    rw [g0, g1, g2, g3] at hg
    simpa [hx0] using hg
  intro i
  fin_cases i <;> assumption

omit [CharP K 2] [Finite K] [FiniteDimensional K N] in
private theorem MinusThreeFrame.hypPairs {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) : HypPairs Q e f p p' :=
  ⟨hF.e_sing, hF.f_sing, hF.p_sing, hF.p'_sing, hF.ef, hF.pp', hF.ep, hF.ep', hF.fp, hF.fp'⟩

omit [CharP K 2] [Finite K] in
private theorem MinusThreeFrame.five_le_finrank {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) : 5 ≤ finrank K N := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    have := hF.Qu
    rw [QuadraticMap.map_zero] at this
    exact zero_ne_one this
  obtain ⟨hue, huf, hup, hup'⟩ := hF.u_perp
  have hli := hF.hypPairs.linearIndependent_five hu0 (by rw [polar_comm]; exact hue)
    (by rw [polar_comm]; exact huf) (by rw [polar_comm]; exact hup)
    (by rw [polar_comm]; exact hup')
  have h5 := finrank_span_eq_card hli
  rw [Fintype.card_fin] at h5
  have := Submodule.finrank_le (Submodule.span K (Set.range ![e, f, p, p', u]))
  omega

omit [CharP K 2] [Finite K] [FiniteDimensional K N] in
private theorem MinusThreeFrame.finrank_le_six {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) : finrank K N ≤ 6 := by
  have hx : ∀ x : N, x ∈ Submodule.span K (Set.range ![e, f, p, p', u, v]) := fun x => by
    simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
      using hF.span x
  have htop : Submodule.span K (Set.range ![e, f, p, p', u, v]) = ⊤ :=
    eq_top_iff.mpr fun x _ => hx x
  have h1 : finrank K (Submodule.span K (Set.range ![e, f, p, p', u, v])) = finrank K N := by
    rw [htop]
    exact finrank_top K N
  have h2 := finrank_range_le_card (R := K) ![e, f, p, p', u, v]
  rw [Fintype.card_fin] at h2
  unfold Set.finrank at h2
  omega

omit [CharP K 2] [Finite K] in
private theorem le_finrank_ker_add {M : Type} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (Φ : N →ₗ[K] M) : finrank K N ≤ finrank K (LinearMap.ker Φ) + finrank K M := by
  have h1 := LinearMap.finrank_range_add_finrank_ker Φ
  have h2 : finrank K (LinearMap.range Φ) ≤ finrank K M := Submodule.finrank_le _
  omega

omit [CharP K 2] [Finite K] in
private theorem finrank_perp_inf_ge (P : HypPair Q) (w : N) :
    finrank K N ≤ finrank K ↥(P.perp ⊓ LinearMap.ker (polarBilin Q w)) + 3 := by
  have h := le_finrank_ker_add
    (((polarBilin Q P.e).prod (polarBilin Q P.f)).prod (polarBilin Q w))
  rw [LinearMap.ker_prod, LinearMap.ker_prod] at h
  change finrank K N ≤
    finrank K ↥(P.perp ⊓ LinearMap.ker (polarBilin Q w)) + finrank K ((K × K) × K) at h
  simpa using h

private theorem exists_fixed_mod_line (P : HypPair Q) (h5 : 5 ≤ finrank K N)
    {B : Subgroup (N ≃ₗ[K] N)} (hB2 : IsPGroup 2 B)
    (hBO : B ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hBe : ∀ b ∈ B, b P.e = P.e)
    (hBf : ∀ b ∈ B, b P.f = P.f) {w₀ : N} (hw₀H : w₀ ∈ P.perp) (hw₀0 : w₀ ≠ 0)
    (hw₀Q : Q w₀ = 0) (hBw₀ : ∀ b ∈ B, b w₀ = w₀) :
    ∃ x₀ ∈ P.perp, polar Q w₀ x₀ = 0 ∧ x₀ ∉ Submodule.span K {w₀} ∧
      ∀ b ∈ B, b x₀ - x₀ ∈ Submodule.span K {w₀} := by
  have : Finite N := Module.finite_of_finite K
  let Pw : Submodule K N := P.perp ⊓ LinearMap.ker (polarBilin Q w₀)
  have hPw2 : 2 ≤ finrank K Pw := by
    have h1 : finrank K N ≤ finrank K Pw + 3 := finrank_perp_inf_ge P w₀
    omega
  have hLP : Submodule.span K {w₀} ≤ Pw := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨hw₀H, by
      rw [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply]
      exact polar_self_eq_zero hw₀Q⟩
  have hLne : Submodule.span K {w₀} ≠ Pw := by
    intro h
    have h1 : finrank K Pw = 1 := by rw [← h]; exact finrank_span_singleton hw₀0
    omega
  have hmapsPw : ∀ t ∈ B, ∀ x ∈ Pw, t x ∈ Pw := by
    intro t ht x hx
    obtain ⟨hxH, hxw⟩ := Submodule.mem_inf.mp hx
    obtain ⟨hx1, hx2⟩ := HypPair.mem_perp.mp hxH
    refine Submodule.mem_inf.mpr ⟨HypPair.mem_perp.mpr ⟨?_, ?_⟩, ?_⟩
    · have := polar_map_of_mem (hBO ht) P.e x
      rwa [hBe t ht, hx1] at this
    · have := polar_map_of_mem (hBO ht) P.f x
      rwa [hBf t ht, hx2] at this
    · rw [LinearMap.mem_ker, polarBilin_apply_apply] at hxw ⊢
      have := polar_map_of_mem (hBO ht) w₀ x
      rwa [hBw₀ t ht, hxw] at this
  have hmapsL : ∀ t ∈ B, ∀ x ∈ Submodule.span K {w₀}, t x ∈ Submodule.span K {w₀} := by
    intro t ht x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hBw₀ t ht]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w₀)
  have hlin : PCoreSection.IsLinearAction K (fun (g : N ≃ₗ[K] N) (x : N) => g x) :=
    ⟨fun x => rfl, fun g h x => rfl, fun g x y => map_add g x y, fun g c x => map_smul g c x⟩
  obtain ⟨x₀, hx₀P, hx₀L, hx₀B⟩ :=
    PCoreSection.exists_fixed_mem_of_isPGroup hlin hB2 hLP hmapsPw hmapsL hLne
  obtain ⟨hx₀H, hx₀w⟩ := Submodule.mem_inf.mp hx₀P
  rw [LinearMap.mem_ker, polarBilin_apply_apply] at hx₀w
  exact ⟨x₀, hx₀H, hx₀w, hx₀L, hx₀B⟩

omit [CharP K 2] [Finite K] [FiniteDimensional K N] in
private theorem exists_levi {e f a a' : N} (hP : HypPairs Q e f a a') {b : N ≃ₗ[K] N}
    (hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hbe : b e = e) (hbf : b f = f)
    (hba : b a = a) :
    ∃ y : N, ∃ h : N ≃ₗ[K] N, polar Q a y = 0 ∧ polar Q e y = 0 ∧ polar Q f y = 0 ∧
      h ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ h a = a ∧ h a' = a' ∧ h e = e ∧ h f = f ∧
      b = eichler Q a y * h := by
  have haa' : polar Q a a' ≠ 0 := by rw [hP.aa']; exact one_ne_zero
  obtain ⟨s, hs, h, hhO, hha, hha', hbsh⟩ :=
    exists_mem_rootGroup_mul_eq hP.a_sing hP.a'_sing haa' hbO hba
  obtain ⟨y, hy, rfl⟩ := mem_rootGroup.mp hs
  have hsa' : eichler Q a y a' = b a' := by rw [hbsh, LinearEquiv.mul_apply, hha']
  have ha'a : polar Q a' a = 1 := by rw [polar_comm]; exact hP.aa'
  have key : ∀ z : N, b z = z → polar Q z a = 0 → polar Q z a' = 0 → polar Q z y = 0 := by
    intro z hbz hza hza'
    have h1 := polar_map_of_mem hbO z a'
    rw [hbz, ← hsa', eichler_apply hP.a_sing hy] at h1
    simp only [polar_add_right, polar_sub_right, polar_smul_right_eq] at h1
    rw [hza, hza', ha'a] at h1
    linear_combination h1
  have hye : polar Q e y = 0 := key e hbe hP.ea hP.ea'
  have hyf : polar Q f y = 0 := key f hbf hP.fa hP.fa'
  have hinj : ∀ z : N, b z = z → eichler Q a y z = z → h z = z := by
    intro z hbz hsz
    apply (eichler Q a y).injective
    rw [hsz, ← LinearEquiv.mul_apply, ← hbsh, hbz]
  refine ⟨y, h, hy, hye, hyf, hhO, hha, hha', hinj e hbe
    (eichler_apply_of_polar_eq_zero hP.ea hye), hinj f hbf
    (eichler_apply_of_polar_eq_zero hP.fa hyf), hbsh⟩

omit [CharP K 2] [Finite K] [FiniteDimensional K N] in
private theorem apply_eq_of_eichler_mul {a a' x y : N} (haQ : Q a = 0) (haa' : polar Q a' a = 1)
    (hy : polar Q a y = 0) {b h : N ≃ₗ[K] N} (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hha : h a = a) (hha' : h a' = a') (hxa : polar Q a x = 0) (hxa' : polar Q a' x = 0)
    (hbsh : b = eichler Q a y * h) {c : K} (hbx : b x = x + c • a) : h x = x := by
  have hax : polar Q (h x) a = 0 := by
    have := polar_map_of_mem hhO a x
    rw [hha, hxa] at this
    rw [polar_comm]
    exact this
  have ha'x : polar Q a' (h x) = 0 := by
    have := polar_map_of_mem hhO a' x
    rwa [hha', hxa'] at this
  have hs : eichler Q a y (h x) = x + c • a := by
    rw [← LinearEquiv.mul_apply, ← hbsh, hbx]
  rw [eichler_apply haQ hy, hax, zero_smul, add_zero, mul_zero, add_zero] at hs
  obtain ⟨d, hd⟩ : ∃ d : K, d = polar Q (h x) y := ⟨_, rfl⟩
  rw [← hd] at hs
  have h2 : h x = x + (c + d) • a := by
    linear_combination (norm := module) hs
  have h3 : polar Q a' (h x) = c + d := by
    rw [h2, polar_add_right, polar_smul_right_eq, hxa', haa']
    ring
  have h4 : c + d = 0 := h3.symm.trans ha'x
  rw [h2, h4, zero_smul, add_zero]

omit [CharP K 2] [Finite K] in
private theorem eq_one_of_fix_five {e f a a' x : N} (hdim : finrank K N ≤ 6)
    (hP : HypPairs Q e f a a') (hx0 : x ≠ 0) (hxe : polar Q e x = 0) (hxf : polar Q f x = 0)
    (hxa : polar Q a x = 0) (hxa' : polar Q a' x = 0) {h : N ≃ₗ[K] N} (he : h e = e)
    (hf : h f = f) (ha : h a = a) (ha' : h a' = a') (hx : h x = x)
    (hev : Even (finrank K (commSpace h))) : h = 1 := by
  by_contra hne
  have h1 := one_le_finrank_commSpace hne
  have h2 := finrank_commSpace_add_finrank_fixSpace h
  have hli := hP.linearIndependent_five hx0 hxe hxf hxa hxa'
  have h5 := finrank_span_eq_card hli
  rw [Fintype.card_fin] at h5
  have hle : Submodule.span K (Set.range ![e, f, a, a', x]) ≤ fixSpace h := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [he, hf, ha, ha', hx]
  have h6 := Submodule.finrank_mono hle
  obtain ⟨r, hr⟩ := hev
  omega

omit [Finite K] in
private theorem exists_eq_eichler {e f a a' x : N} (hdim : finrank K N ≤ 6)
    (hnd : (polarBilin Q).Nondegenerate) (hP : HypPairs Q e f a a') (hx0 : x ≠ 0)
    (hxe : polar Q e x = 0) (hxf : polar Q f x = 0) (hxa : polar Q a x = 0)
    (hxa' : polar Q a' x = 0) {b : N ≃ₗ[K] N}
    (hbO : b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hbe : b e = e) (hbf : b f = f)
    (hba : b a = a) (hbeven : Even (finrank K (commSpace b))) (hbx : ∃ c : K, b x = x + c • a) :
    ∃ y : N, polar Q e y = 0 ∧ polar Q f y = 0 ∧ polar Q a y = 0 ∧ polar Q a' y = 0 ∧
      b = eichler Q a y := by
  obtain ⟨y, h, hy, hye, hyf, hhO, hha, hha', hhe, hhf, hbsh⟩ := exists_levi hP hbO hbe hbf hba
  obtain ⟨c, hc⟩ := hbx
  have ha'a : polar Q a' a = 1 := by rw [polar_comm]; exact hP.aa'
  have hhx : h x = x := apply_eq_of_eichler_mul hP.a_sing ha'a hy hhO hha hha' hxa hxa' hbsh hc
  have hpar : Even (finrank K (commSpace h)) := by
    have hmul := natCast_finrank_commSpace_mul hnd (eichler_mem_orthogonalGroup Q a y) hhO
    rw [← hbsh] at hmul
    have h0b : ((finrank K (commSpace b) : ℕ) : ZMod 2) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr hbeven
    have h0s : ((finrank K (commSpace (eichler Q a y)) : ℕ) : ZMod 2) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr (even_finrank_commSpace_eichler hnd a y)
    rw [h0b, h0s, zero_add] at hmul
    exact ZMod.natCast_eq_zero_iff_even.mp hmul.symm
  have h1 : h = 1 := eq_one_of_fix_five hdim hP hx0 hxe hxf hxa hxa' hhe hhf hha hha' hhx hpar
  have hb : b = eichler Q a y := by rw [hbsh, h1, mul_one]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨y + polar Q a' y • a, ?_, ?_, ?_, ?_, ?_⟩
  · rw [polar_add_right, polar_smul_right_eq, hye, hP.ea]
    ring
  · rw [polar_add_right, polar_smul_right_eq, hyf, hP.fa]
    ring
  · rw [polar_add_right, polar_smul_right_eq, hy, polar_self_eq_zero hP.a_sing]
    ring
  · rw [polar_add_right, polar_smul_right_eq, ha'a]
    linear_combination (polar Q a' y) * h2
  · rw [eichler_add_smul_self hP.a_sing, hb]

end Aux

theorem MinusThreeFrame.exists_eq_eichler_of_fixed {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) (hnd : (polarBilin Q).Nondegenerate)
    {B : Subgroup (N ≃ₗ[K] N)} (hB2 : IsPGroup 2 B)
    (hBO : B ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hBeven : ∀ b ∈ B, Even (finrank K (commSpace b))) (hBe : ∀ b ∈ B, b e = e)
    (hBf : ∀ b ∈ B, b f = f) {w₀ w₁ : N} (hw₀Q : Q w₀ = 0) (hw₁Q : Q w₁ = 0)
    (hw₀w₁ : polar Q w₀ w₁ = 1) (hw₀e : polar Q e w₀ = 0) (hw₀f : polar Q f w₀ = 0)
    (hw₁e : polar Q e w₁ = 0) (hw₁f : polar Q f w₁ = 0) (hBw₀ : ∀ b ∈ B, b w₀ = w₀) :
    ∀ b ∈ B, ∃ y : N, polar Q e y = 0 ∧ polar Q f y = 0 ∧ polar Q w₀ y = 0 ∧
      polar Q w₁ y = 0 ∧ b = eichler Q w₀ y := by
  let P : HypPair Q := ⟨e, f, hF.e_sing, hF.f_sing, hF.ef⟩
  have hw₀H : w₀ ∈ P.perp := HypPair.mem_perp.mpr ⟨hw₀e, hw₀f⟩
  have hw₀0 : w₀ ≠ 0 := by
    rintro rfl
    rw [polar_zero_left] at hw₀w₁
    exact zero_ne_one hw₀w₁
  obtain ⟨x₀, hx₀H, hx₀w, hx₀L, hx₀B⟩ :=
    exists_fixed_mod_line P hF.five_le_finrank hB2 hBO hBe hBf hw₀H hw₀0 hw₀Q hBw₀
  obtain ⟨hx₀e, hx₀f⟩ := HypPair.mem_perp.mp hx₀H
  have hw₁w₀ : polar Q w₁ w₀ = 1 := by rw [polar_comm]; exact hw₀w₁
  have hP : HypPairs Q e f w₀ w₁ :=
    ⟨hF.e_sing, hF.f_sing, hw₀Q, hw₁Q, hF.ef, hw₀w₁, hw₀e, hw₁e, hw₀f, hw₁f⟩
  set x := x₀ + polar Q w₁ x₀ • w₀ with hxdef
  have hx0 : x ≠ 0 := by
    intro hx
    apply hx₀L
    have : x₀ = (-polar Q w₁ x₀) • w₀ := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left hx
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w₀)
  have hxe : polar Q e x = 0 := by
    rw [hxdef, polar_add_right, polar_smul_right_eq, hx₀e, hw₀e]
    ring
  have hxf : polar Q f x = 0 := by
    rw [hxdef, polar_add_right, polar_smul_right_eq, hx₀f, hw₀f]
    ring
  have hxw₀ : polar Q w₀ x = 0 := by
    rw [hxdef, polar_add_right, polar_smul_right_eq, hx₀w, polar_self_eq_zero hw₀Q]
    ring
  have hxw₁ : polar Q w₁ x = 0 := by
    rw [hxdef, polar_add_right, polar_smul_right_eq, hw₁w₀]
    linear_combination (polar Q w₁ x₀) * (CharTwo.two_eq_zero : (2 : K) = 0)
  intro b hb
  have hbx : ∃ c : K, b x = x + c • w₀ := by
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hx₀B b hb)
    have hd' : b x₀ - x₀ = d • w₀ := hd.symm
    refine ⟨d, ?_⟩
    rw [hxdef, map_add, map_smul, hBw₀ b hb, show b x₀ = x₀ + d • w₀ by rw [← hd']; abel]
    abel
  exact exists_eq_eichler hF.finrank_le_six hnd hP hx0 hxe hxf hxw₀ hxw₁ (hBO hb) (hBe b hb)
    (hBf b hb) (hBw₀ b hb) (hBeven b hb) hbx

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
