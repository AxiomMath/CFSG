module

public import CFSG.LocalAnalysis.AGLEmbedding.OddCorePiecesAux
import CFSG.LocalAnalysis.AGLEmbedding.OddCorePieces

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding Polynomial

section LinearAlgebra

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M]

theorem mul_aeval_eq_aeval_pow_mul {c T : Module.End k M} {lam : ℕ} (hTc : T * c = c ^ lam * T)
    (q : k[X]) : T * aeval c q = aeval (c ^ lam) q * T := by
  have hn : ∀ n : ℕ, T * c ^ n = (c ^ lam) ^ n * T := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hTc, ← mul_assoc, ← pow_succ]
  induction q using Polynomial.induction_on' with
  | add q r hq hr => rw [map_add, map_add, mul_add, add_mul, hq, hr]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hn,
      mul_assoc]

theorem orderOf_le_finrank_of_conj [FiniteDimensional k M] [Nontrivial M] {p lam : ℕ}
    (hp : p.Prime) {c T : Module.End k M} (hcp : c ^ p = 1) (hfix : ∀ v, c v = v → v = 0)
    (hT : Function.Surjective T) (hTc : T * c = c ^ lam * T) :
    orderOf (lam : ZMod p) ≤ Module.finrank k M := by
  classical
  have := Fact.mk hp
  have hint : IsIntegral k c := LinearMap.isIntegral c
  set f := minpoly k c with hf
  have hf0 : f ≠ 0 := minpoly.ne_zero hint
  have hfc : aeval c f = 0 := minpoly.aeval k c
  have hdvd : f ∣ f.comp (X ^ lam) := by
    refine minpoly.dvd k c ?_
    rw [aeval_comp, map_pow, aeval_X]
    have h := mul_aeval_eq_aeval_pow_mul hTc f
    rw [hfc, mul_zero] at h
    refine LinearMap.ext fun v => ?_
    obtain ⟨u, rfl⟩ := hT v
    simpa using (LinearMap.congr_fun h u).symm
  set K := AlgebraicClosure k
  have hroot_pow : ∀ ρ : K, aeval ρ f = 0 → aeval (ρ ^ lam) f = 0 := by
    intro ρ hρ
    obtain ⟨g, hg⟩ := hdvd
    have := congrArg (aeval ρ) hg
    rw [aeval_comp, map_mul, hρ, zero_mul, map_pow, aeval_X] at this
    exact this
  have hrp : ∀ ρ : K, aeval ρ f = 0 → ρ ^ p = 1 := by
    intro ρ hρ
    obtain ⟨g, hg⟩ : f ∣ X ^ p - 1 := minpoly.dvd k c (by simp [hcp])
    have := congrArg (aeval ρ) hg
    rw [map_mul, hρ, zero_mul, map_sub, map_pow, aeval_X, map_one] at this
    exact sub_eq_zero.mp this
  have hr1 : ∀ ρ : K, aeval ρ f = 0 → ρ ≠ 1 := by
    intro ρ hρ h1
    subst h1
    have h : f.eval 1 = 0 := by
      have h1 : aeval (1 : K) f = algebraMap k K (f.eval 1) := by
        rw [← map_one (algebraMap k K), aeval_algebraMap_apply]
        simp
      rw [h1] at hρ
      exact (map_eq_zero (algebraMap k K)).mp hρ
    obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr h
    have hgc : aeval c g = 0 := by
      have h0 := congrArg (aeval c) hg
      rw [hfc, map_mul, map_sub, aeval_X, aeval_C, map_one] at h0
      refine LinearMap.ext fun v => hfix _ ?_
      have := LinearMap.congr_fun h0.symm v
      simpa [sub_eq_zero] using this
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hf0 (by simpa using hg)
    have h2 : f.natDegree ≤ g.natDegree := natDegree_le_of_dvd (minpoly.dvd k c hgc) hg0
    have h3 : f.natDegree = g.natDegree + 1 := by
      rw [hg, natDegree_mul (X_sub_C_ne_zero 1) hg0, natDegree_X_sub_C]
      ring
    omega
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero K f
    (natDegree_pos_iff_degree_pos.mp (minpoly.natDegree_pos hint)).ne'
  have hr0 : r ≠ 0 := by
    rintro rfl
    have := hrp 0 hr
    rw [zero_pow hp.ne_zero] at this
    exact zero_ne_one this
  set u : Kˣ := Units.mk0 r hr0 with hu
  have hord_u : orderOf u = p := orderOf_eq_prime (Units.ext (by simpa [hu] using hrp r hr))
    (fun h => hr1 r hr (by simpa [hu] using congrArg Units.val h))
  have hiter : ∀ i : ℕ, aeval (r ^ lam ^ i) f = 0 := by
    intro i
    induction i with
    | zero => simpa using hr
    | succ i ih => rw [pow_succ, pow_mul]; exact hroot_pow _ ih
  have hinj : Set.InjOn (fun i : ℕ => r ^ lam ^ i)
      (Finset.range (orderOf (lam : ZMod p)) : Set ℕ) := by
    intro i hi j hj hij
    have hij' : u ^ lam ^ i = u ^ lam ^ j := Units.ext (by simpa [hu] using hij)
    have h1 : lam ^ i ≡ lam ^ j [MOD p] := by
      rw [← hord_u]
      exact pow_eq_pow_iff_modEq.mp hij'
    have h2 : (lam : ZMod p) ^ i = (lam : ZMod p) ^ j := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
      push_cast at this
      exact this
    exact pow_injOn_Iio_orderOf (Finset.mem_range.mp (Finset.mem_coe.mp hi))
      (Finset.mem_range.mp (Finset.mem_coe.mp hj)) h2
  have hmap_ne : f.map (algebraMap k K) ≠ 0 := Polynomial.map_ne_zero hf0
  have hcard : orderOf (lam : ZMod p) ≤ ((f.map (algebraMap k K)).roots.toFinset).card := by
    have := Finset.card_le_card_of_injOn (fun i : ℕ => r ^ lam ^ i)
      (s := Finset.range (orderOf (lam : ZMod p)))
      (t := (f.map (algebraMap k K)).roots.toFinset) (fun i _ => ?_) hinj
    · simpa using this
    · rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hmap_ne, IsRoot, eval_map, ← aeval_def]
      exact hiter i
  have hdeg : f.natDegree ≤ Module.finrank k M := by
    have h1 : f ∣ c.charpoly := LinearMap.minpoly_dvd_charpoly c
    have := natDegree_le_of_dvd h1 (LinearMap.charpoly_monic c).ne_zero
    rwa [LinearMap.charpoly_natDegree] at this
  calc orderOf (lam : ZMod p) ≤ _ := hcard
    _ ≤ (f.map (algebraMap k K)).roots.card := Multiset.toFinset_card_le _
    _ ≤ (f.map (algebraMap k K)).natDegree := card_roots' _
    _ = f.natDegree := natDegree_map _
    _ ≤ _ := hdeg

end LinearAlgebra

section Piece

variable {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]

theorem eq_one_of_smul_eq_of_mem_fixedPiece [Finite A] [Finite V] {p : ℕ} (hp : p.Prime)
    {F : Subgroup A} (hF : F.index = p) (hcop : Nat.Coprime (Nat.card A) (Nat.card V)) {x : A}
    (hx : x ∉ F) {w : V} (hw : w ∈ (fixedPiece F : Subgroup V)) (hxw : x • w = w) : w = 1 := by
  have hsup : F ⊔ Subgroup.zpowers x = ⊤ :=
    sup_eq_top_of_index_eq_prime_of_not_le hp hF fun h => hx (h (Subgroup.mem_zpowers x))
  have htop : Nat.Coprime (Nat.card (⊤ : Subgroup A)) (Nat.card V) := by
    rwa [Subgroup.card_top]
  have hstab : (⊤ : Subgroup A) ≤ MulAction.stabilizer A w := by
    rw [← hsup]
    exact sup_le (fun b hb => fixedPiece_le_fixedBy F hw b hb) (Subgroup.zpowers_le.mpr hxw)
  have hmem : w ∈ actCommutator (⊤ : Subgroup V) (⊤ : Subgroup A) ⊓
      fixedBy (⊤ : Subgroup A) :=
    ⟨actCommutator_mono le_top le_rfl hw, fun a _ => hstab (Subgroup.mem_top a)⟩
  rwa [actCommutator_top_inf_fixedBy htop, Subgroup.mem_bot] at hmem

private def restrictEnd (W : Subgroup V) (φ : V →* V) (hφ : ∀ w ∈ W, φ w ∈ W) : W →* W where
  toFun w := ⟨φ (w : V), hφ w w.2⟩
  map_one' := Subtype.ext (map_one φ)
  map_mul' a b := Subtype.ext (map_mul φ (a : V) (b : V))

theorem pow_orderOf_le_card_fixedPiece [Finite A] [Finite V] {p s : ℕ} (hp : p.Prime)
    (hs : s.Prime) (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hV : ∀ v : V, v ^ s = 1)
    {α : MulAut A} {β : MulAut V} (hαβ : ∀ a v, β (a • v) = α a • β v) (m lam : ℕ)
    (hα : ∀ a, (α ^ m) a = a ^ lam) {F : Subgroup A} (hF : F.index = p)
    (hne : (fixedPiece F : Subgroup V) ≠ ⊥) :
    s ^ orderOf (lam : ZMod p) ≤ Nat.card (fixedPiece F : Subgroup V) := by
  have := Fact.mk hp
  have := Fact.mk hs
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    have hAp : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hA a⟩
    have hVp : IsPGroup s V := fun v => ⟨1, by rw [pow_one]; exact hV v⟩
    obtain ⟨a, ha⟩ := hAp.exists_card_eq
    obtain ⟨b, hb⟩ := hVp.exists_card_eq
    rw [ha, hb]
    exact Nat.coprime_pow_primes a b hp hs hsp.symm
  set W : Subgroup V := fixedPiece F with hWdef
  have hFmap : F.map (α ^ m).toMonoidHom = F := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      change (α ^ m) a ∈ F
      rw [hα]
      exact pow_mem ha lam
    · rw [Subgroup.card_map_of_injective (α ^ m).injective]
  have hθW : ∀ w ∈ W, (β ^ m).toMonoidHom w ∈ W := fun w hw => by
    have h := map_fixedPiece_le (pow_apply_smul hαβ m) F ⟨w, hw, rfl⟩
    rwa [hFmap] at h
  obtain ⟨x, hx⟩ : ∃ x : A, x ∉ F := by
    by_contra hall
    push Not at hall
    have hFtop : F = ⊤ := eq_top_iff.mpr fun a _ => hall a
    rw [hFtop, Subgroup.index_top] at hF
    exact hp.one_lt.ne hF
  have hxW : ∀ w ∈ W, (MulDistribMulAction.toMonoidHom V x) w ∈ W := fun w hw =>
    smul_mem_fixedPiece x hw
  have : NeZero s := ⟨hs.ne_zero⟩
  have : Module (ZMod s) (Additive W) := AddCommGroup.zmodModule (n := s) fun w => by
    rw [← ofMul_toMul w, ← ofMul_pow, ofMul_eq_zero]
    exact Subtype.ext (hV _)
  let c : Module.End (ZMod s) (Additive W) := AddMonoidHom.toZModLinearMap s
    (MonoidHom.toAdditive (restrictEnd W (MulDistribMulAction.toMonoidHom V x) hxW))
  let T : Module.End (ZMod s) (Additive W) := AddMonoidHom.toZModLinearMap s
    (MonoidHom.toAdditive (restrictEnd W (β ^ m).toMonoidHom hθW))
  have hc : ∀ v : Additive W,
      ((Additive.toMul (c v) : W) : V) = x • ((Additive.toMul v : W) : V) := fun v => rfl
  have hT : ∀ v : Additive W,
      ((Additive.toMul (T v) : W) : V) = (β ^ m) ((Additive.toMul v : W) : V) := fun v => rfl
  have hcn : ∀ (n : ℕ) (v : Additive W), ((Additive.toMul ((c ^ n) v) : W) : V) =
      (x ^ n) • ((Additive.toMul v : W) : V) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih => intro v; rw [pow_succ', Module.End.mul_apply, hc, ih, pow_succ', mul_smul]
  have hcp : c ^ p = 1 := LinearMap.ext fun v => by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hcn, hA x, one_smul]
    rfl
  have hfix : ∀ v : Additive W, c v = v → v = 0 := by
    intro v hv
    have h1 : x • ((Additive.toMul v : W) : V) = ((Additive.toMul v : W) : V) := by
      rw [← hc, hv]
    have h2 := eq_one_of_smul_eq_of_mem_fixedPiece hp hF hcop hx (Additive.toMul v).2 h1
    exact Additive.toMul.injective (Subtype.ext h2)
  have hTinj : Function.Injective T := by
    intro v v' h
    apply Additive.toMul.injective
    apply Subtype.ext
    have := congrArg (fun u => ((Additive.toMul u : W) : V)) h
    simp only [hT] at this
    exact (β ^ m).injective this
  have hTc : T * c = c ^ lam * T := LinearMap.ext fun v => by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [Module.End.mul_apply, Module.End.mul_apply, hT, hc, hcn, hT, pow_apply_smul hαβ m x,
      hα x]
  have : Nontrivial (Additive W) := by
    have : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hne
    infer_instance
  have hdim := orderOf_le_finrank_of_conj hp hcp hfix (Finite.injective_iff_surjective.mp hTinj)
    hTc
  calc s ^ orderOf (lam : ZMod p)
      ≤ s ^ Module.finrank (ZMod s) (Additive W) := Nat.pow_le_pow_right hs.pos hdim
    _ = Nat.card (Additive W) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod s), Nat.card_zmod]
    _ = Nat.card W := Nat.card_congr Additive.toMul

theorem pow_pred_le_card_fixedPiece [Finite A] [Finite V] {p s : ℕ} (hp : p.Prime)
    (hs : s.Prime) (hsp : s ≠ p) (hA : ∀ a : A, a ^ p = 1) (hV : ∀ v : V, v ^ s = 1)
    {α : MulAut A} {β : MulAut V} (hαβ : ∀ a v, β (a • v) = α a • β v) (m lam : ℕ)
    (hα : ∀ a, (α ^ m) a = a ^ lam) (hord : orderOf (lam : ZMod p) = p - 1)
    {F : Subgroup A} (hF : F.index = p) (hne : (fixedPiece F : Subgroup V) ≠ ⊥) :
    s ^ (p - 1) ≤ Nat.card (fixedPiece F : Subgroup V) := by
  have h := pow_orderOf_le_card_fixedPiece hp hs hsp hA hV hαβ m lam hα hF hne
  rwa [hord] at h

end Piece

end CFSG.AGLEmbeddingD2
