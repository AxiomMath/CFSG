module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Lattice
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjOrbit
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Reduce
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwConj
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwo
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.RankThree.PartOne.KE

section Pairing

theorem d4t2c_triPairing_zsmul (x : Fin Tag.E6.rank → ZMod 3) (c : ℤ) (v : Fin Tag.E6.rank → ℤ) :
    triPairing x (c • v) = (c : ZMod 3) * triPairing x v := by
  simp only [triPairing, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem d4t2c_triPairing_add_left (x y : Fin Tag.E6.rank → ZMod 3) (v : Fin Tag.E6.rank → ℤ) :
    triPairing (x + y) v = triPairing x v + triPairing y v := by
  simp only [triPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem d4t2c_triPairing_smul_left (c : ZMod 3) (x : Fin Tag.E6.rank → ZMod 3)
    (v : Fin Tag.E6.rank → ℤ) : triPairing (c • x) v = c * triPairing x v := by
  simp only [triPairing, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem d4t2c_triPairing_eq_zero_of_mem_span {s : Set (Fin Tag.E6.rank → ZMod 3)}
    {α : Fin Tag.E6.rank → ℤ} (hs : ∀ x ∈ s, triPairing x α = 0) {x : Fin Tag.E6.rank → ZMod 3}
    (hx : x ∈ Submodule.span (ZMod 3) s) : triPairing x α = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs y hy
  | zero => simp [triPairing]
  | add y z _ _ hy hz => rw [d4t2c_triPairing_add_left, hy, hz, add_zero]
  | smul c y _ hy => rw [d4t2c_triPairing_smul_left, hy, mul_zero]

theorem d4t2c_linearIndependent {f e₁ e₂ : Fin Tag.E6.rank → ZMod 3} (hf : f ≠ 0)
    (h₁ : e₁ ∉ Submodule.span (ZMod 3) {f}) (h₂ : e₂ ∉ Submodule.span (ZMod 3) {f, e₁}) :
    LinearIndependent (ZMod 3) ![f, e₁, e₂] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have hfs : f ∈ Submodule.span (ZMod 3) {f, e₁} := Submodule.subset_span (Set.mem_insert _ _)
  have he₁s : e₁ ∈ Submodule.span (ZMod 3) {f, e₁} :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have hg2 : g 2 = 0 := by
    by_contra h
    apply h₂
    have h' : g 2 • e₂ = -(g 0 • f + g 1 • e₁) := eq_neg_of_add_eq_zero_right hg
    rw [← inv_smul_smul₀ h e₂, h']
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ hfs) (Submodule.smul_mem _ _ he₁s)))
  rw [hg2, zero_smul, add_zero] at hg
  have hg1 : g 1 = 0 := by
    by_contra h
    apply h₁
    have h' : g 1 • e₁ = -(g 0 • f) := eq_neg_of_add_eq_zero_right hg
    rw [← inv_smul_smul₀ h e₁, h']
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f)))
  rw [hg1, zero_smul, add_zero] at hg
  have hg0 : g 0 = 0 := (smul_eq_zero.1 hg).resolve_right hf
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

end Pairing

section Coords


variable {L : Type} [Field L]

theorem d4t2c_exists_dV_eq {ω : Lˣ} (hω : orderOf ω = 3) {x : ModGL Tag.E6 L}
    (hx : x ∈ torusGroup .E6 L) (hx3 : x ^ 3 = 1) :
    ∃ k : Fin Tag.E6.rank → ZMod 3, dV ω k = x := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  have hω3 : ω ^ 3 = 1 := by
    rw [← hω]
    exact pow_orderOf_eq_one ω
  have hb : ∀ i, b i ^ 3 = 1 := by
    have h : rootDiagUnit .E6 (b ^ 3) = rootDiagUnit .E6 1 := by
      rw [rootDiagUnit_one]
      exact (map_pow (rootDiagUnitHom .E6 L) b 3).trans hx3
    intro i
    simpa using congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) i
  choose m hm using fun i => exists_eq_pow_of_pow_three hω (hb i)
  refine ⟨fun i => (m i : ZMod 3), ?_⟩
  show rootDiagUnit .E6 (torV ω fun i => (m i : ZMod 3)) = rootDiagUnit .E6 b
  congr 1
  funext i
  rw [hm i, torV, ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div (m i) 3]
  rw [pow_add, pow_mul, hω3, one_pow, mul_one]

theorem d4t2c_dV_smul {ω : Lˣ} (hω3 : ω ^ 3 = 1) (c : ZMod 3) (x : Fin Tag.E6.rank → ZMod 3) :
    dV ω (c • x) = dV ω x ^ c.val := by
  have h : c • x = c.val • x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  rw [h, ← dVHom_ofAdd hω3, ofAdd_nsmul, map_pow, dVHom_ofAdd]

theorem d4t2c_rootChar_torV_eq_iff {ω : Lˣ} (hω : orderOf ω = 3) (x : Fin Tag.E6.rank → ZMod 3)
    (u v : Fin Tag.E6.rank → ℤ) :
    rootChar (torV ω x) u = rootChar (torV ω x) v ↔ triPairing x u = triPairing x v := by
  rw [rootChar_torV, rootChar_torV, zpow_eq_zpow_iff_modEq, hω, ← ZMod.intCast_eq_intCast_iff]
  simp only [triPairing, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem d4t2c_dV_mem_of_mem_span {ω : Lˣ} (hω3 : ω ^ 3 = 1) {B : Subgroup (ModGL Tag.E6 L)}
    {s : Set (Fin Tag.E6.rank → ZMod 3)} (hs : ∀ x ∈ s, dV ω x ∈ B)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ Submodule.span (ZMod 3) s) : dV ω x ∈ B := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs y hy
  | zero =>
    rw [dV_zero]
    exact one_mem B
  | add y z _ _ hy hz =>
    rw [dV_add hω3]
    exact mul_mem hy hz
  | smul c y _ hy =>
    rw [d4t2c_dV_smul hω3]
    exact pow_mem hy _

theorem d4t2c_exists_mem_of_mem_closure {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (V : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3)) {y : ModGL Tag.E6 L}
    (hy : y ∈ Subgroup.closure (dV ω '' (V : Set (Fin Tag.E6.rank → ZMod 3)))) :
    ∃ x ∈ V, dV ω x = y := by
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hx, rfl⟩
  | one => exact ⟨0, V.zero_mem, dV_zero ω⟩
  | mul z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨x₁, hx₁, rfl⟩ := h₁
    obtain ⟨x₂, hx₂, rfl⟩ := h₂
    exact ⟨x₁ + x₂, V.add_mem hx₁ hx₂, dV_add hω3 x₁ x₂⟩
  | inv z _ h =>
    obtain ⟨x, hx, rfl⟩ := h
    refine ⟨-x, V.neg_mem hx, ?_⟩
    have h1 : dV ω (-x) * dV ω x = 1 := by rw [← dV_add hω3, neg_add_cancel, dV_zero]
    exact eq_inv_of_mul_eq_one_left h1

theorem d4t2c_rootChar_frob {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (π : Equiv.Perm (Fin Tag.E6.rank)) (b : Fin Tag.E6.rank → Lˣ) (x : Fin Tag.E6.rank → ℤ) :
    rootChar (fun i => Units.map Fr.toMonoidHom (b (π.symm i))) (permLattice π x) =
      rootChar b ((q : ℤ) • x) := by
  rw [rootChar_permLattice]
  simp only [Equiv.symm_apply_apply]
  exact rootChar_units_map_pow hFr b x

end Coords

section Weyl

set_option linter.unusedSectionVars false


theorem d4t2c_toral_weyl {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {l f : ℕ} (hq : S.D.q = l ^ f) (h3q : 3 ∣ l ^ f + 1)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (hall : (kernelRoots (rootCharHom a)).ncard = 24)
    {A : Subgroup (ModGL Tag.E6 L)} (hAT : A ≤ S.D.torus) (hab : IsElemAbelian 3 A)
    (hcard : Nat.card A = 3 ^ 3) (hdA : rootDiagUnit .E6 a ∈ A)
    (hroot : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ →
      ¬ ∀ b : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 b ∈ A → rootChar b γ = 1)
    {w : WeylGroup .E6} (hw : S.D.n = canonicalRep (coxeterSystem Tag.E6) L w) :
    ∃ ε ∈ A, ε ∉ Subgroup.zpowers (rootDiagUnit .E6 a) ∧ ∃ M : WeylGroup .E6,
      canonicalRep (coxeterSystem Tag.E6) L M * rootDiagUnit .E6 a =
          rootDiagUnit .E6 a * canonicalRep (coxeterSystem Tag.E6) L M ∧
        canonicalRep (coxeterSystem Tag.E6) L M * ε =
          ε * canonicalRep (coxeterSystem Tag.E6) L M ∧
        canonicalRep (coxeterSystem Tag.E6) L M ∉ toralRootGroup .E6 L a ∧
        ∀ x : Fin Tag.E6.rank → ℤ, M • (w • permLattice (τ := .E6) TwistTag.E6.perm x) =
          w • permLattice (τ := .E6) TwistTag.E6.perm (M • x) := by
  classical
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  have ht' : t = TwistTag.E6 := by
    cases t
    · rfl
    · exact absurd ht (by decide)
  subst ht'
  have hΦF : ∀ y, S.D.Φ y = twistHom TwistTag.E6 L Fr y := fun y => (hΦ y).trans rfl
  have hΦd : ∀ b : Fin Tag.E6.rank → Lˣ, S.D.Φ (rootDiagUnit .E6 b) =
      rootDiagUnit .E6 (fun i => Units.map Fr.toMonoidHom (b (TwistTag.E6.perm.symm i))) :=
    fun b => by
      rw [hΦF]
      exact twistHom_rootDiagUnit_eq (t := TwistTag.E6) (σ := Fr) b
  have hq3 : ((S.D.q : ℤ) : ZMod 3) = -1 := by
    have h := (ZMod.natCast_eq_zero_iff (l ^ f + 1) 3).2 h3q
    rw [hq]
    push_cast at h ⊢
    linear_combination h
  have hd1 : rootDiagUnit .E6 a ≠ 1 := d4t2_rootDiagUnit_ne_one hall
  obtain ⟨ω, hω⟩ : ∃ ω : Lˣ, orderOf ω = 3 := by
    obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 1 := not_forall.1 fun hcon =>
      hd1 (by rw [show a = 1 from funext hcon, rootDiagUnit_one])
    exact ⟨a i₀, orderOf_eq_prime (hap i₀) hi₀⟩
  have hω3 : ω ^ 3 = 1 := by
    rw [← hω]
    exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    norm_num at hω
  have hAH : ∀ x ∈ A, x ∈ torusGroup .E6 L := fun x hx => (Subgroup.mem_inf.1 (hAT hx)).1
  obtain ⟨f₀, hf₀⟩ := d4t2c_exists_dV_eq hω (hAH _ hdA) (hab.2 _ hdA)
  have ha : torV ω f₀ = a := CFSG.LieType.Chevalley.rootDiagUnit_injective hf₀
  subst ha
  have hd3 : dV ω f₀ ^ 3 = 1 := hab.2 _ hdA
  have hod : orderOf (dV ω f₀) = 3 := orderOf_eq_prime hd3 hd1
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨ε₁, hε₁A, hε₁Z⟩ : ∃ ε₁ ∈ A, ε₁ ∉ Subgroup.zpowers (dV ω f₀) := by
    refine SetLike.not_le_iff_exists.1 fun hcon => ?_
    have hZ : Nat.card (Subgroup.zpowers (dV ω f₀)) = 3 := by rw [Nat.card_zpowers, hod]
    haveI : Finite (Subgroup.zpowers (dV ω f₀)) :=
      Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
    have h := Subgroup.card_le_of_le (H := A) (K := Subgroup.zpowers (dV ω f₀)) hcon
    rw [hcard, hZ] at h
    norm_num at h
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (ModGL Tag.E6 L),
      N = Subgroup.zpowers (dV ω f₀) ⊔ Subgroup.zpowers ε₁ := ⟨_, rfl⟩
  have hN : Nat.card N = 3 ^ 2 := by
    rw [hNdef]
    exact KSNotAll24.card_zpowers_sup_zpowers (hab.comm hdA hε₁A) hd1 hd3 (hab.2 _ hε₁A) hε₁Z
  have hNA : N ≤ A := by
    rw [hNdef]
    exact sup_le (Subgroup.zpowers_le.2 hdA) (Subgroup.zpowers_le.2 hε₁A)
  obtain ⟨ε₂, hε₂A, hε₂N⟩ : ∃ ε₂ ∈ A, ε₂ ∉ N := by
    refine SetLike.not_le_iff_exists.1 fun hcon => ?_
    haveI : Finite N := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
    have h := Subgroup.card_le_of_le (H := A) (K := N) hcon
    rw [hcard, hN] at h
    norm_num at h
  obtain ⟨N₃, hN₃def⟩ : ∃ N₃ : Subgroup (ModGL Tag.E6 L), N₃ = N ⊔ Subgroup.zpowers ε₂ :=
    ⟨_, rfl⟩
  have hNN₃ : N ≤ N₃ := by
    rw [hN₃def]
    exact le_sup_left
  have hN₃A : N₃ ≤ A := by
    rw [hN₃def]
    exact sup_le hNA (Subgroup.zpowers_le.2 hε₂A)
  have hε₂N₃ : ε₂ ∈ N₃ := by
    rw [hN₃def]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ε₂)
  have hN₃eq : N₃ = A := by
    haveI : Finite N₃ :=
      Finite.of_injective (Subgroup.inclusion hN₃A) (Subgroup.inclusion_injective hN₃A)
    have h9 : 3 ^ 2 ∣ Nat.card N₃ := hN ▸ Subgroup.card_dvd_of_le hNN₃
    have h27 : Nat.card N₃ ∣ 3 ^ 3 := hcard ▸ Subgroup.card_dvd_of_le hN₃A
    have hne : Nat.card N₃ ≠ 3 ^ 2 := by
      intro h
      have hNe : N = N₃ := Subgroup.eq_of_le_of_card_ge hNN₃ (h.trans hN.symm).le
      exact hε₂N (hNe ▸ hε₂N₃)
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h27
    have hi2 : 2 ≤ i := by
      rw [hi'] at h9
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h9
    have hcard₃ : Nat.card N₃ = 3 ^ 3 := by
      interval_cases i
      · exact absurd hi' hne
      · exact hi'
    exact Subgroup.eq_of_le_of_card_ge hN₃A (hcard.trans hcard₃.symm).le
  obtain ⟨e₁, he₁⟩ := d4t2c_exists_dV_eq hω (hAH _ hε₁A) (hab.2 _ hε₁A)
  obtain ⟨e₂, he₂⟩ := d4t2c_exists_dV_eq hω (hAH _ hε₂A) (hab.2 _ hε₂A)
  subst he₁ he₂
  have hf0 : f₀ ≠ 0 := by
    rintro rfl
    exact hd1 (dV_zero ω)
  have he₁f : e₁ ∉ Submodule.span (ZMod 3) {f₀} := fun h => hε₁Z
    (d4t2c_dV_mem_of_mem_span hω3 (fun x hx => by
      rw [Set.mem_singleton_iff.1 hx]
      exact Subgroup.mem_zpowers _) h)
  have he₂N : e₂ ∉ Submodule.span (ZMod 3) {f₀, e₁} := fun h => hε₂N
    (d4t2c_dV_mem_of_mem_span hω3 (fun x hx => by
      rw [hNdef]
      rcases hx with hx | hx
      · rw [hx]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · rw [Set.mem_singleton_iff.1 hx]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) h)
  have hli := d4t2c_linearIndependent hf0 he₁f he₂N
  have hvk : ∀ k : Fin Tag.E6.rank → ZMod 3, dV ω k ∈ S.D.torus → ∀ x : Fin Tag.E6.rank → ℤ,
      triPairing k (w • permLattice (τ := .E6) TwistTag.E6.perm x) = - triPairing k x := by
    intro k hk x
    have h1 : S.D.n * S.D.Φ (dV ω k) * S.D.n⁻¹ = dV ω k := (mem_twistedTorusOf.1 hk).2
    rw [hw] at h1
    have h2 : rootDiagUnit .E6 (torV ω k) = canonicalRep (coxeterSystem Tag.E6) L w *
        rootDiagUnit .E6
          (fun i => Units.map Fr.toMonoidHom (torV ω k (TwistTag.E6.perm.symm i))) *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ := by
      rw [← hΦd (torV ω k)]
      exact h1.symm
    have h3 : rootChar (torV ω k) (w • permLattice (τ := .E6) TwistTag.E6.perm x) =
        rootChar (torV ω k) ((S.D.q : ℤ) • x) :=
      ((rootDiagUnit_eq_conj_canonicalRep_iff _ _ w).1 h2
        (permLattice (τ := .E6) TwistTag.E6.perm x)).trans
        (d4t2c_rootChar_frob hFr TwistTag.E6.perm (torV ω k) x)
    rw [(d4t2c_rootChar_torV_eq_iff hω k _ _).1 h3, d4t2c_triPairing_zsmul, hq3, neg_one_mul]
  have hv : ∀ b ∈ ({f₀, e₁, e₂} : Set (Fin Tag.E6.rank → ZMod 3)), ∀ x : Fin Tag.E6.rank → ℤ,
      triPairing b (w • permLattice (τ := .E6) TwistTag.E6.perm x) = - triPairing b x := by
    intro b hb
    rcases hb with hb | hb | hb
    · rw [hb]
      exact hvk _ (hAT hdA)
    · rw [hb]
      exact hvk _ (hAT hε₁A)
    · rw [Set.mem_singleton_iff.1 hb]
      exact hvk _ (hAT hε₂A)
  have h24 : (kernelRoots (triChar f₀)).ncard = 24 := by
    have e : kernelRoots (triChar f₀) = kernelRoots (rootCharHom (torV ω f₀)) := by
      ext α
      rw [mem_kernelRoots_triChar, kernelRoots_rootCharHom]
      exact and_congr_right fun _ => (rootChar_torV_eq_one_iff hω3 hω1 f₀ α).symm
    rw [e]
    exact hall
  have hA3 : A ≤ Subgroup.closure (dV ω '' (Submodule.span (ZMod 3) {f₀, e₁, e₂} :
      Set (Fin Tag.E6.rank → ZMod 3))) := by
    have hmem : ∀ k ∈ ({f₀, e₁, e₂} : Set (Fin Tag.E6.rank → ZMod 3)),
        dV ω k ∈ Subgroup.closure (dV ω '' (Submodule.span (ZMod 3) {f₀, e₁, e₂} :
          Set (Fin Tag.E6.rank → ZMod 3))) :=
      fun k hk => Subgroup.subset_closure ⟨k, Submodule.subset_span hk, rfl⟩
    rw [← hN₃eq, hN₃def, hNdef]
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact hmem f₀ (Set.mem_insert _ _)
    · exact hmem e₁ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · exact hmem e₂ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hSE : ∀ α, IsRoot .E6 α → triPairing f₀ α = 0 → triPairing e₁ α = 0 →
      triPairing e₂ α ≠ 0 := by
    intro α hα h0 h1 h2
    apply hroot α hα
    intro b hb
    obtain ⟨k, hk, hkb⟩ := d4t2c_exists_mem_of_mem_closure hω3 _ (hA3 hb)
    rw [← CFSG.LieType.Chevalley.rootDiagUnit_injective hkb]
    refine (rootChar_torV_eq_one_iff hω3 hω1 k α).2 ?_
    refine d4t2c_triPairing_eq_zero_of_mem_span (fun x hx => ?_) hk
    rcases hx with hx | hx | hx
    · rw [hx]
      exact h0
    · rw [hx]
      exact h1
    · rw [Set.mem_singleton_iff.1 hx]
      exact h2
  obtain ⟨e, he, hne, M, hMf, hMe, hMs, hcomm⟩ := d4t2_alpha_lattice w f₀ e₁ e₂ hli hv h24 hSE
  have heA : dV ω e ∈ A := by
    refine d4t2c_dV_mem_of_mem_span hω3 (fun x hx => ?_) he
    rcases hx with hx | hx | hx
    · rw [hx]
      exact hdA
    · rw [hx]
      exact hε₁A
    · rw [Set.mem_singleton_iff.1 hx]
      exact hε₂A
  have heZ : dV ω e ∉ Subgroup.zpowers (rootDiagUnit .E6 (torV ω f₀)) := by
    intro h
    have hle : Subgroup.zpowers (rootDiagUnit .E6 (torV ω f₀)) ≤
        Subgroup.closure (dV ω '' (Submodule.span (ZMod 3) {f₀} :
          Set (Fin Tag.E6.rank → ZMod 3))) :=
      Subgroup.zpowers_le.2
        (Subgroup.subset_closure ⟨f₀, Submodule.mem_span_singleton_self f₀, rfl⟩)
    obtain ⟨k, hk, hke⟩ := d4t2c_exists_mem_of_mem_closure hω3 _ (hle h)
    exact hne (dV_injective hω hke ▸ hk)
  have hcommk : ∀ k : Fin Tag.E6.rank → ZMod 3, M ∈ charStabilizer (triChar k) →
      canonicalRep (coxeterSystem Tag.E6) L M * dV ω k =
        dV ω k * canonicalRep (coxeterSystem Tag.E6) L M := by
    intro k hk
    have h := (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) (torV ω k) (torV ω k) M).2
      fun v => (d4t2c_rootChar_torV_eq_iff hω k _ _).2 (twMem_charStabilizer_triChar.1 hk v)
    show canonicalRep (coxeterSystem Tag.E6) L M * rootDiagUnit .E6 (torV ω k) =
      rootDiagUnit .E6 (torV ω k) * canonicalRep (coxeterSystem Tag.E6) L M
    calc canonicalRep (coxeterSystem Tag.E6) L M * rootDiagUnit .E6 (torV ω k)
        = (canonicalRep (coxeterSystem Tag.E6) L M * rootDiagUnit .E6 (torV ω k) *
            (canonicalRep (coxeterSystem Tag.E6) L M)⁻¹) *
          canonicalRep (coxeterSystem Tag.E6) L M := by group
      _ = rootDiagUnit .E6 (torV ω k) * canonicalRep (coxeterSystem Tag.E6) L M := by rw [← h]
  have hMM : canonicalRep (coxeterSystem Tag.E6) L M ∉ toralRootGroup .E6 L (torV ω f₀) := by
    intro h
    have h1 : M ∈ kernelReflectionGroup (torV ω f₀) :=
      mem_kernelReflectionGroup_of_canonicalRep_mem_gen h
    have hker : ∀ x, rootCharHom3 (torV ω f₀) x = 1 ↔ triChar f₀ x = 1 := fun x => by
      show rootChar (torV ω f₀) (Multiplicative.toAdd x) = 1 ↔
        triChar f₀ (Multiplicative.ofAdd (Multiplicative.toAdd x)) = 1
      rw [triChar_apply, Z3.ofAdd_eq_one]
      exact rootChar_torV_eq_one_iff hω3 hω1 f₀ _
    have h2 : M ∈ kernelWeylGroup (triChar f₀) := by
      rw [← kernelWeylGroup_congr_ker hker]
      exact h1
    exact hMs (triPairing_e6Shift_of_mem_kernelWeylGroup h2)
  exact ⟨dV ω e, heA, heZ, M, hcommk f₀ hMf, hcommk e hMe, hMM, hcomm⟩

end Weyl

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
