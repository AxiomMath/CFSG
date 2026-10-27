module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSyl
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalGenW
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Polynomial
open scoped Pointwise

theorem card_le_finrank_of_normalizing {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (f g : Module.End (ZMod 2) V) (hg : Function.Surjective g) (hf : f ^ p = 1) (hf1 : f ≠ 1)
    {k : ℕ} (hgf : g * f = f ^ k * g) (T : Finset (ZMod p))
    (hT : ∀ x ∈ T, ∃ a b : ℕ, x = 2 ^ a * (k : ZMod p) ^ b) :
    T.card ≤ Module.finrank (ZMod 2) V := by
  classical
  let K := AlgebraicClosure (ZMod 2)
  let μ : (ZMod 2)[X] := minpoly (ZMod 2) f
  have hint : IsIntegral (ZMod 2) f := Algebra.IsIntegral.isIntegral f
  have hmon : μ.Monic := minpoly.monic hint
  have hμ0 : μ ≠ 0 := hmon.ne_zero
  have hμf : aeval f μ = 0 := minpoly.aeval (ZMod 2) f
  have hdvdp : μ ∣ (X ^ p - C 1 : (ZMod 2)[X]) := by
    apply minpoly.dvd (ZMod 2) f
    simp [hf]
  have hnot2 : ¬ 2 ∣ p := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp h).symm
  have hsep : (X ^ p - C (1 : ZMod 2)).Separable :=
    Polynomial.separable_X_pow_sub_C' 2 p 1 hnot2 one_ne_zero
  have hμsep : μ.Separable := hsep.of_dvd hdvdp
  have hR : ∀ ζ : K, ζ ∈ μ.rootSet K ↔ aeval ζ μ = 0 := fun ζ => mem_rootSet_of_ne hμ0
  have hsq : ∀ ζ : K, aeval ζ μ = 0 → aeval (ζ ^ 2) μ = 0 := by
    intro ζ hζ
    have key : Polynomial.eval (ζ ^ 2) (μ.map (algebraMap (ZMod 2) K)) =
        (Polynomial.eval ζ (μ.map (algebraMap (ZMod 2) K))) ^ 2 := by
      rw [← expand_eval, ← map_expand, ZMod.expand_card, Polynomial.map_pow, eval_pow]
    rw [aeval_def, ← eval_map] at hζ ⊢
    rw [key, hζ]
    norm_num
  have hgn : ∀ m : ℕ, g * f ^ m = (f ^ k) ^ m * g := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hgf, ← mul_assoc, ← pow_succ]
  have hconj : ∀ q : (ZMod 2)[X], g * aeval f q = aeval (f ^ k) q * g := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q r hq hr => rw [map_add, map_add, mul_add, add_mul, hq, hr]
    | monomial n a =>
      rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hgn,
        ← mul_assoc]
  have hfk : aeval (f ^ k) μ = 0 := by
    have h := hconj μ
    rw [hμf, mul_zero] at h
    ext v
    obtain ⟨u, rfl⟩ := hg v
    have h' := congrArg (fun T : Module.End (ZMod 2) V => T u) h
    simpa using h'.symm
  have hμk : μ ∣ μ.comp (X ^ k) := by
    apply minpoly.dvd (ZMod 2) f
    rw [aeval_comp, aeval_X_pow]
    exact hfk
  have hkc : ∀ ζ : K, aeval ζ μ = 0 → aeval (ζ ^ k) μ = 0 := by
    intro ζ hζ
    obtain ⟨q, hq⟩ := hμk
    have h : aeval ζ (μ.comp (X ^ k)) = 0 := by rw [hq, map_mul, hζ, zero_mul]
    rwa [aeval_comp, aeval_X_pow] at h
  have hex : ∃ ζ : K, aeval ζ μ = 0 ∧ ζ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hμK0 : μ.map (algebraMap (ZMod 2) K) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap (ZMod 2) K).injective).mpr hμ0
    have hsplit : (μ.map (algebraMap (ZMod 2) K)).Splits := IsAlgClosed.splits _
    have hnodup : (μ.map (algebraMap (ZMod 2) K)).roots.Nodup :=
      Polynomial.nodup_roots hμsep.map
    have hsub : (μ.map (algebraMap (ZMod 2) K)).roots ⊆ (X - C (1 : K)).roots := by
      intro ζ hζ
      have h1 := (Polynomial.mem_roots hμK0).mp hζ
      have h2 : aeval ζ μ = 0 := by
        rw [aeval_def, ← eval_map]
        exact h1
      rw [hcon ζ h2, roots_X_sub_C]
      exact Multiset.mem_singleton_self _
    have hle := (Multiset.le_iff_subset hnodup).mpr hsub
    have hdvdK := hsplit.dvd_of_roots_le_roots hμK0 hle
    have hdvd1 : μ ∣ (X - C 1 : (ZMod 2)[X]) := by
      refine (Polynomial.map_dvd_map' (algebraMap (ZMod 2) K)).mp ?_
      simpa [Polynomial.map_sub] using hdvdK
    obtain ⟨r, hr⟩ := hdvd1
    have h : aeval f (X - C 1 : (ZMod 2)[X]) = 0 := by rw [hr, map_mul, hμf, zero_mul]
    simp only [map_sub, aeval_X, aeval_C, map_one, sub_eq_zero] at h
    exact hf1 h
  obtain ⟨ζ₀, hζ₀, hζ₀1⟩ := hex
  have hζ₀p : ζ₀ ^ p = 1 := by
    obtain ⟨r, hr⟩ := hdvdp
    have h : aeval ζ₀ (X ^ p - C 1 : (ZMod 2)[X]) = 0 := by rw [hr, map_mul, hζ₀, zero_mul]
    simpa [sub_eq_zero] using h
  have hord : orderOf ζ₀ = p := orderOf_eq_prime hζ₀p hζ₀1
  have hkpow : ∀ b : ℕ, aeval (ζ₀ ^ (k ^ b)) μ = 0 := by
    intro b
    induction b with
    | zero => simpa using hζ₀
    | succ b ih => rw [pow_succ, pow_mul]; exact hkc _ ih
  have h2pow : ∀ a b : ℕ, aeval (ζ₀ ^ (2 ^ a * k ^ b)) μ = 0 := by
    intro a b
    induction a with
    | zero => simpa using hkpow b
    | succ a ih =>
      have h : ζ₀ ^ (2 ^ (a + 1) * k ^ b) = (ζ₀ ^ (2 ^ a * k ^ b)) ^ 2 := by
        rw [← pow_mul]; congr 1; ring
      rw [h]
      exact hsq _ ih
  let F : ZMod p → K := fun x => ζ₀ ^ x.val
  have hFmap : ∀ x ∈ (T : Set (ZMod p)), F x ∈ μ.rootSet K := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := hT x hx
    rw [hR]
    have hval : ((2 : ZMod p) ^ a * (k : ZMod p) ^ b).val = (2 ^ a * k ^ b) % p := by
      have h : ((2 : ZMod p) ^ a * (k : ZMod p) ^ b) = ((2 ^ a * k ^ b : ℕ) : ZMod p) := by
        push_cast; rfl
      rw [h, ZMod.val_natCast]
    have hmod := pow_mod_orderOf ζ₀ (2 ^ a * k ^ b)
    rw [hord] at hmod
    show aeval (ζ₀ ^ ((2 : ZMod p) ^ a * (k : ZMod p) ^ b).val) μ = 0
    rw [hval, hmod]
    exact h2pow a b
  have hprim : IsPrimitiveRoot ζ₀ p := hord ▸ IsPrimitiveRoot.orderOf ζ₀
  have hFinj : Set.InjOn F (T : Set (ZMod p)) := by
    intro x _ y _ hxy
    have hxy' : ζ₀ ^ x.val = ζ₀ ^ y.val := hxy
    exact ZMod.val_injective p (hprim.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) hxy')
  calc T.card = (T : Set (ZMod p)).ncard := (Set.ncard_coe_finset T).symm
    _ ≤ (μ.rootSet K).ncard :=
        Set.ncard_le_ncard_of_injOn F hFmap hFinj (Polynomial.rootSet_finite μ K)
    _ ≤ μ.natDegree := ncard_rootSet_le μ K
    _ ≤ f.charpoly.natDegree :=
        Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f)
          (LinearMap.charpoly_monic f).ne_zero
    _ = Module.finrank (ZMod 2) V := LinearMap.charpoly_natDegree f

theorem two_pow_card_le_of_normalizing {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {E : Type} [CommGroup E] [Finite E] (hE : ∀ w : E, w * w = 1)
    (φ ψ : MulAut E) (hφ : φ ^ p = 1) (hφ1 : φ ≠ 1) {k : ℕ} (hψφ : ψ * φ = φ ^ k * ψ)
    (T : Finset (ZMod p)) (hT : ∀ x ∈ T, ∃ a b : ℕ, x = 2 ^ a * (k : ZMod p) ^ b) :
    2 ^ T.card ≤ Nat.card E := by
  have h2 : ∀ x : Additive E, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [two_nsmul, toMul_add, toMul_zero]
    exact hE _
  letI : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule h2
  haveI : Module.Finite (ZMod 2) (Additive E) := Module.Finite.of_finite
  let lin : MulAut E →* Module.End (ZMod 2) (Additive E) :=
    { toFun := fun σ => AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive σ.toMonoidHom)
      map_one' := by ext v; rfl
      map_mul' := fun σ τ => by ext v; rfl }
  have hlin : ∀ σ : MulAut E, ∀ x : E,
      lin σ (Additive.ofMul x) = Additive.ofMul (σ x) := fun σ x => rfl
  have hsurj : Function.Surjective (lin ψ) := by
    intro v
    refine ⟨Additive.ofMul (ψ.symm (Additive.toMul v)), ?_⟩
    rw [hlin]
    simp
  have hf1 : lin φ ≠ 1 := by
    intro h
    apply hφ1
    ext x
    have h' := congrArg (fun T : Module.End (ZMod 2) (Additive E) => T (Additive.ofMul x)) h
    simpa [hlin] using h'
  have hcard := card_le_finrank_of_normalizing hp2 (lin φ) (lin ψ) hsurj
    (by rw [← map_pow, hφ, map_one]) hf1 (by rw [← map_mul, hψφ, map_mul, map_pow]) T hT
  have hNat : Nat.card E = 2 ^ Module.finrank (ZMod 2) (Additive E) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    rw [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive E ≃ E)] at h
    exact h
  rw [hNat]
  exact Nat.pow_le_pow_right (by norm_num) hcard

theorem two_pow_card_le_card_frattini_quot_of_normalizing {A : Type} [Group A] [Finite A] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {z : A} (hz : orderOf z = p) {Y : Subgroup A}
    (hY : IsPGroup 2 Y) (hzY : z ∈ normalizer (Y : Set A)) (hnc : ∃ y ∈ Y, z * y ≠ y * z)
    {n : A} (hnY : n ∈ normalizer (Y : Set A)) {k : ℕ} (hnz : n * z * n⁻¹ = z ^ k)
    (T : Finset (ZMod p)) (hT : ∀ x ∈ T, ∃ a b : ℕ, x = 2 ^ a * (k : ZMod p) ^ b) :
    2 ^ T.card ≤ Nat.card (↥Y ⧸ frattini ↥Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq := frattini_quot_mul_self_eq_one hY
  obtain ⟨φ, hφdef⟩ : ∃ φ, CFSG.Quasithin.H13.Ch4.L4316.conjFrattini Y ⟨z, hzY⟩ = φ :=
    ⟨_, rfl⟩
  have hφ1 : φ ≠ 1 := by
    intro h
    obtain ⟨y, hyY, hyz⟩ := hnc
    have hodd : Odd (orderOf z) := by
      rw [hz]
      exact hp.odd_of_ne_two hp2
    have hle := CFSG.Quasithin.H13.Ch4.L4316.le_centralizer_of_conjFrattini_eq_one hY hzY hodd
      (hφdef.trans h)
    exact hyz (Subgroup.mem_centralizer_iff.mp (hle hyY) z (Set.mem_singleton z))
  have hzN : (⟨z, hzY⟩ : ↥(normalizer (Y : Set A))) ^ p = 1 := by
    apply Subtype.ext
    show z ^ p = 1
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hφpow : φ ^ p = 1 := by
    rw [← hφdef, ← map_pow (CFSG.Quasithin.H13.Ch4.L4316.conjFrattini Y), hzN, map_one]
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, CFSG.Quasithin.H13.Ch4.L4316.conjFrattini Y ⟨n, hnY⟩ = ψ :=
    ⟨_, rfl⟩
  have hψφ : ψ * φ = φ ^ k * ψ := by
    have h : (⟨n, hnY⟩ : ↥(normalizer (Y : Set A))) * ⟨z, hzY⟩ =
        (⟨z, hzY⟩ : ↥(normalizer (Y : Set A))) ^ k * ⟨n, hnY⟩ := by
      apply Subtype.ext
      show n * z = z ^ k * n
      calc n * z = (n * z * n⁻¹) * n := by group
        _ = z ^ k * n := by rw [hnz]
    rw [← hψdef, ← hφdef, ← map_mul, h, map_mul, map_pow]
  have hcomm : ∀ a b : ↥Y ⧸ frattini ↥Y, a * b = b * a := by
    intro a b
    have hab : (a * b) * (a * b) = 1 := hsq _
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
      _ = b * a := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq a), inv_eq_of_mul_eq_one_right (hsq b)]
  let _ : CommGroup (↥Y ⧸ frattini ↥Y) :=
    { (inferInstance : Group (↥Y ⧸ frattini ↥Y)) with mul_comm := hcomm }
  haveI : Finite (↥Y ⧸ frattini ↥Y) := inferInstance
  exact two_pow_card_le_of_normalizing hp2 hsq φ ψ hφpow hφ1 hψφ T hT

theorem card_le_of_normalizing {A : Type} [Group A] [Finite A] (L K₀ : Subgroup A) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {z : A} (hz : orderOf z = p) (hK₀L : K₀ ≤ L) (hzK : z ∈ K₀)
    (hy : ∃ y ∈ pCoreOf 2 K₀, z * y ≠ y * z) {n : A} (hnK : n ∈ K₀) {k : ℕ}
    (hnz : n * z * n⁻¹ = z ^ k) {e m : ℕ} (hn : Nat.card L = 2 ^ e * m) (hm : Odd m)
    (T : Finset (ZMod p)) (hT : ∀ x ∈ T, ∃ a b : ℕ, x = 2 ^ a * (k : ZMod p) ^ b) :
    T.card ≤ e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := pCoreOf 2 K₀ with hYdef
  have hYP : IsPGroup 2 Y := pCoreOf_isPGroup 2 K₀
  have hYL : Y ≤ L := (pCoreOf_le 2 K₀).trans hK₀L
  have hzY : z ∈ normalizer (Y : Set A) := localGroup_le_normalizer_pCoreOf 2 K₀ hzK
  have hnY : n ∈ normalizer (Y : Set A) := localGroup_le_normalizer_pCoreOf 2 K₀ hnK
  have hbound := two_pow_card_le_card_frattini_quot_of_normalizing hp hp2 hz hYP hzY hy hnY hnz T hT
  have hQY : Nat.card (↥Y ⧸ frattini ↥Y) ≤ Nat.card ↥Y := by
    rw [← Subgroup.card_mul_index (frattini ↥Y)]
    exact Nat.le_mul_of_pos_left _ Nat.card_pos
  obtain ⟨j, hj⟩ := hYP.exists_card_eq
  have hdvd : 2 ^ j ∣ 2 ^ e * m := by
    rw [← hj, ← hn]
    exact Subgroup.card_dvd_of_le hYL
  have hcop : Nat.Coprime (2 ^ j) m := by
    refine Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
    obtain ⟨k, hk⟩ := hm
    omega
  have hjd : j ≤ e :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  have h2 : 2 ^ T.card ≤ 2 ^ j := by
    rw [← hj]
    exact hbound.trans hQY
  exact ((Nat.pow_le_pow_iff_right (by norm_num)).mp h2).trans hjd

theorem mem_normalizer_zpowers_of_conj_pow {G : Type*} [Group G] [Finite G] {z n : G} {k : ℕ}
    (h : n * z * n⁻¹ = z ^ k) : n ∈ normalizer (zpowers z : Set G) := by
  have hfwd : ∀ x ∈ zpowers z, n * x * n⁻¹ ∈ zpowers z := by
    intro x hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    have h1 : n * z ^ i * n⁻¹ = (n * z * n⁻¹) ^ i := (conj_zpow).symm
    rw [h1, h]
    exact zpow_mem (pow_mem (mem_zpowers z) k) i
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hfwd x hx, fun hx => ?_⟩
  let c : zpowers z → zpowers z := fun s => ⟨n * s * n⁻¹, hfwd s s.2⟩
  have hcinj : Function.Injective c := by
    intro s t hst
    have h2 : n * (s : G) * n⁻¹ = n * (t : G) * n⁻¹ := congrArg Subtype.val hst
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h2))
  obtain ⟨s, hs⟩ := Finite.injective_iff_surjective.mp hcinj ⟨n * x * n⁻¹, hx⟩
  have h3 : n * (s : G) * n⁻¹ = n * x * n⁻¹ := congrArg Subtype.val hs
  have h4 : (s : G) = x := mul_left_cancel (mul_right_cancel h3)
  rw [← h4]
  exact s.2

theorem exists_normalizing_of_model {X G : Type} [Group X] [Group G] [Finite G] (φ : G ≃* X)
    {p k : ℕ} (hp : p.Prime) (hsyl : ¬ p ^ 2 ∣ Nat.card G) {z₀ n₀ : X} (hz₀ : orderOf z₀ = p)
    (hn₀ : n₀ * z₀ * n₀⁻¹ = z₀ ^ k) {z : G} (hz : orderOf z = p) :
    ∃ n : G, n * z * n⁻¹ = z ^ k := by
  set z' : G := φ.symm z₀ with hz'
  set n' : G := φ.symm n₀ with hn'
  have hz'ord : orderOf z' = p := by rw [hz', MulEquiv.orderOf_eq]; exact hz₀
  have hn'z' : n' * z' * n'⁻¹ = z' ^ k := by
    apply φ.injective
    simp only [hz', hn', map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply]
    exact hn₀
  obtain ⟨g, hg⟩ := exists_conj_zpowers hp hsyl hz hz'ord
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hg
  have hw : n' * (g * z * g⁻¹) * n'⁻¹ = (g * z * g⁻¹) ^ k := by
    rw [← hj, ← conj_zpow, hn'z', ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm]
  refine ⟨g⁻¹ * n' * g, ?_⟩
  calc g⁻¹ * n' * g * z * (g⁻¹ * n' * g)⁻¹
      = g⁻¹ * (n' * (g * z * g⁻¹) * n'⁻¹) * g := by group
    _ = g⁻¹ * (g * z * g⁻¹) ^ k * g := by rw [hw]
    _ = z ^ k := by
      rw [conj_pow]
      group

theorem row_of_normalizing {s : TauCeti.SporadicName} {p : ℕ} (X : Type) [Group X]
    (hX : ∀ (G : Type) [Group G],
      Nonempty (G ≃* (TauCeti.CFSGIndex.sporadic s).Group) → Nonempty (G ≃* X)) {e m : ℕ}
    (hcard : Nat.card X = 2 ^ e * m) (hm : Odd m) (hsyl : ¬ p ^ 2 ∣ m)
    {z₀ n₀ : X} {k : ℕ} (hz₀ : orderOf z₀ = p) (hn₀ : n₀ * z₀ * n₀⁻¹ = z₀ ^ k)
    (T : Finset (ZMod p)) (hT : ∀ x ∈ T, ∃ a b : ℕ, x = 2 ^ a * (k : ZMod p) ^ b)
    (hTe : e < T.card) : KFactSporLocalRow s p := by
  apply row_of_model
  intro G _ _ ⟨e'⟩ hp hp5 K z hz hK hzK hN hcl hy hNN
  obtain ⟨φ⟩ := hX G ⟨e'⟩
  have hGX : Nat.card G = 2 ^ e * m := by
    rw [Nat.card_congr φ.toEquiv]
    exact hcard
  have hsylG : ¬ p ^ 2 ∣ Nat.card G := by
    rw [hGX]
    intro hd
    have hcop : Nat.Coprime (p ^ 2) (2 ^ e) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    exact hsyl (hcop.dvd_of_dvd_mul_left hd)
  obtain ⟨n, hnz⟩ := exists_normalizing_of_model φ hp hsylG hz₀ hn₀ hz
  have hnK : n ∈ K := hN (mem_normalizer_zpowers_of_conj_pow hnz)
  have hbound := card_le_of_normalizing ⊤ K hp (by omega) hz le_top hzK hy hnK hnz
    (by rw [Subgroup.card_top]; exact hGX) hm T hT
  exact absurd hbound (not_le.mpr hTe)


@[expose] def resGenSet (p k : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.filter fun x => ∃ a ∈ Finset.range p, ∃ b ∈ Finset.range p,
    x = 2 ^ a * (k : ZMod p) ^ b

theorem mem_resGenSet {p k : ℕ} [NeZero p] {x : ZMod p} (h : x ∈ resGenSet p k) :
    ∃ a b : ℕ, x = 2 ^ a * (k : ZMod p) ^ b := by
  obtain ⟨-, a, -, b, -, hx⟩ := Finset.mem_filter.mp h
  exact ⟨a, b, hx⟩

theorem false_of_frattini_quot_sylow {A : Type} [Group A] [Finite A] (L : Subgroup A)
    {Y : Subgroup A} (hY : IsPGroup 2 Y) (hYL : Y ≤ L) {e m : ℕ} (hn : Nat.card L = 2 ^ e * m)
    (hm : Odd m) (hbound : 2 ^ e ≤ Nat.card (↥Y ⧸ frattini ↥Y)) {g : A} (hgL : g ∈ L)
    (hg : orderOf g = 4) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hY.exists_card_eq
  have hdvd : 2 ^ j ∣ 2 ^ e * m := by
    rw [← hj, ← hn]
    exact Subgroup.card_dvd_of_le hYL
  have hcop : Nat.Coprime (2 ^ j) m := by
    refine Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
    obtain ⟨k, hk⟩ := hm
    omega
  have hjd : j ≤ e :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  have hQY : Nat.card (↥Y ⧸ frattini ↥Y) ≤ Nat.card ↥Y := by
    rw [← Subgroup.card_mul_index (frattini ↥Y)]
    exact Nat.le_mul_of_pos_left _ Nat.card_pos
  have hQeq : Nat.card (↥Y ⧸ frattini ↥Y) = Nat.card ↥Y := by
    refine le_antisymm hQY ?_
    rw [hj]
    exact (Nat.pow_le_pow_right (by norm_num) hjd).trans hbound
  have hdj : e ≤ j := by
    have h2 : 2 ^ e ≤ 2 ^ j := by
      rw [← hj, ← hQeq]
      exact hbound
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  have hcardY : Nat.card ↥Y = 2 ^ e := by
    rw [hj, le_antisymm hjd hdj]
  have hΦ : frattini ↥Y = ⊥ := by
    have hmul := Subgroup.card_mul_index (frattini ↥Y)
    have hidx : (frattini ↥Y).index = Nat.card (↥Y ⧸ frattini ↥Y) := rfl
    rw [hidx, hQeq] at hmul
    rw [Subgroup.eq_bot_iff_card]
    refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥Y)) ?_
    rw [one_mul]
    exact hmul
  have hsqY : ∀ a ∈ Y, a * a = 1 := by
    intro a ha
    have h1 : ((⟨a, ha⟩ * ⟨a, ha⟩ : ↥Y) : ↥Y ⧸ frattini ↥Y) = 1 := by
      rw [QuotientGroup.mk_mul]
      exact frattini_quot_mul_self_eq_one hY _
    have hmem : (⟨a, ha⟩ * ⟨a, ha⟩ : ↥Y) ∈ frattini ↥Y := (QuotientGroup.eq_one_iff _).mp h1
    rw [hΦ, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  have hcardLy : Nat.card ↥(Y.subgroupOf L) = 2 ^ e := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYL).toEquiv, hcardY]
  have hLy : IsPGroup 2 (Y.subgroupOf L) := IsPGroup.of_card hcardLy
  have hidx : (Y.subgroupOf L).index = m := by
    have h1 := Subgroup.card_mul_index (Y.subgroupOf L)
    rw [hcardLy, hn] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hnd : ¬ 2 ∣ (Y.subgroupOf L).index := by
    rw [hidx]
    obtain ⟨k, hk⟩ := hm
    omega
  obtain ⟨YS, hYS⟩ : ∃ YS : Sylow 2 ↥L, (YS : Subgroup ↥L) = Y.subgroupOf L :=
    ⟨IsPGroup.toSylow hLy hnd, rfl⟩
  haveI : Finite (Sylow 2 ↥L) := Sylow.finite_of_finiteIndex YS
  obtain ⟨x, hxg⟩ : ∃ x : ↥L, (x : A) = g := ⟨⟨g, hgL⟩, rfl⟩
  have hxord : orderOf x = 4 := by
    rw [← Subgroup.orderOf_coe, hxg, hg]
  have hxz : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hxord] <;> norm_num)
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hxz
  have hxP : x ∈ (P : Subgroup ↥L) := hP (Subgroup.mem_zpowers x)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥L YS P
  have hxh : x ∈ MulAut.conj h • (YS : Subgroup ↥L) := by
    have hxh' : x ∈ ((h • YS : Sylow 2 ↥L) : Subgroup ↥L) := by
      rw [hh]
      exact hxP
    exact hxh'
  obtain ⟨s, hs, hsx⟩ :=
    (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj h) (YS : Subgroup ↥L)).mp hxh
  rw [hYS] at hs
  have hss : s * s = 1 := by
    apply Subtype.ext
    simpa using hsqY (s : A) (Subgroup.mem_subgroupOf.mp hs)
  have hxeq : x = h * s * h⁻¹ := hsx.symm
  have hxx : x * x = 1 := by
    rw [hxeq]
    calc h * s * h⁻¹ * (h * s * h⁻¹) = h * (s * s) * h⁻¹ := by group
      _ = 1 := by rw [hss, mul_one, mul_inv_cancel]
  have hgg : g * g = 1 := by
    simpa [hxg] using congrArg Subtype.val hxx
  have hdvd4 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
  rw [hg] at hdvd4
  norm_num at hdvd4

theorem row_of_normalizing_sylow {s : TauCeti.SporadicName} {p : ℕ} (X : Type) [Group X]
    (hX : ∀ (G : Type) [Group G],
      Nonempty (G ≃* (TauCeti.CFSGIndex.sporadic s).Group) → Nonempty (G ≃* X)) {e m : ℕ}
    (hcard : Nat.card X = 2 ^ e * m) (hm : Odd m) (hsyl : ¬ p ^ 2 ∣ m)
    {z₀ n₀ : X} {k : ℕ} (hz₀ : orderOf z₀ = p) (hn₀ : n₀ * z₀ * n₀⁻¹ = z₀ ^ k)
    (T : Finset (ZMod p)) (hT : ∀ x ∈ T, ∃ a b : ℕ, x = 2 ^ a * (k : ZMod p) ^ b)
    (hTe : e ≤ T.card) {g₀ : X} (hg₀ : orderOf g₀ = 4) : KFactSporLocalRow s p := by
  apply row_of_model
  intro G _ _ ⟨e'⟩ hp hp5 K z hz hK hzK hN hcl hy hNN
  obtain ⟨φ⟩ := hX G ⟨e'⟩
  have hGX : Nat.card G = 2 ^ e * m := by
    rw [Nat.card_congr φ.toEquiv]
    exact hcard
  have hsylG : ¬ p ^ 2 ∣ Nat.card G := by
    rw [hGX]
    intro hd
    have hcop : Nat.Coprime (p ^ 2) (2 ^ e) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    exact hsyl (hcop.dvd_of_dvd_mul_left hd)
  obtain ⟨n, hnz⟩ := exists_normalizing_of_model φ hp hsylG hz₀ hn₀ hz
  have hnK : n ∈ K := hN (mem_normalizer_zpowers_of_conj_pow hnz)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYP : IsPGroup 2 (pCoreOf 2 K) := pCoreOf_isPGroup 2 K
  have hzY : z ∈ normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 K hzK
  have hnY : n ∈ normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 K hnK
  have hbound := two_pow_card_le_card_frattini_quot_of_normalizing hp (by omega) hz hYP hzY hy hnY
    hnz T hT
  have hbound' : 2 ^ e ≤ Nat.card (↥(pCoreOf 2 K) ⧸ frattini ↥(pCoreOf 2 K)) :=
    (Nat.pow_le_pow_right (by norm_num) hTe).trans hbound
  have hg : orderOf (φ.symm g₀) = 4 := by rw [MulEquiv.orderOf_eq]; exact hg₀
  exact (false_of_frattini_quot_sylow ⊤ hYP le_top (by rw [Subgroup.card_top]; exact hGX) hm
    hbound' (Subgroup.mem_top _) hg).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
