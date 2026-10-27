module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcF4Kernel

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley

theorem mem_span_of_det_eq_zero {K : Type} [Field K] {x a b c : Fin 4 → K}
    (hind : LinearIndependent K ![a, b, c])
    (h : (Matrix.of ![x, a, b, c] : Matrix (Fin 4) (Fin 4) K).det = 0) :
    x ∈ Submodule.span K (Set.range ![a, b, c]) := by
  by_contra hx
  have hli : LinearIndependent K (Fin.cons x ![a, b, c]) :=
    linearIndependent_fin_cons.2 ⟨hind, by simpa using hx⟩
  have hrow : LinearIndependent K (Matrix.of ![x, a, b, c] : Matrix (Fin 4) (Fin 4) K).row := by
    simpa using hli
  have hunit : IsUnit (Matrix.of ![x, a, b, c] : Matrix (Fin 4) (Fin 4) K) :=
    (Matrix.linearIndependent_rows_iff_isUnit).1 hrow
  have hdetunit : IsUnit (Matrix.of ![x, a, b, c] : Matrix (Fin 4) (Fin 4) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 hunit
  exact hdetunit.ne_zero h

theorem exists_linearIndependent_triple {K : Type} [Field K] {ι : Type} [Finite ι]
    (r : ι → Fin 4 → K) (c : Fin 4 → K)
    (hann : ∀ v : Fin 4 → K, (∀ i, r i ⬝ᵥ v = 0) → ∃ t : K, v = t • c) :
    ∃ i j k : ι, LinearIndependent K ![r i, r j, r k] := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let M : Matrix ι (Fin 4) K := Matrix.of r
  let L : (Fin 4 → K) →ₗ[K] (ι → K) := M.mulVecLin
  have hkerle : L.ker ≤ Submodule.span K ({c} : Set (Fin 4 → K)) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have hv' : ∀ i, r i ⬝ᵥ v = 0 := by
      intro i
      have := congrFun hv i
      simpa [M, L, Matrix.mulVecLin, Matrix.mulVec, Matrix.of_apply, dotProduct] using this
    obtain ⟨t, ht⟩ := hann v hv'
    exact Submodule.mem_span_singleton.2 ⟨t, by rw [ht]⟩
  have hkerdim : Module.finrank K L.ker ≤ 1 := by
    refine (Submodule.finrank_mono hkerle).trans ?_
    by_cases hc : c = 0
    · rw [hc, Set.singleton_zero, Submodule.span_zero, finrank_bot]
      norm_num
    · rw [finrank_span_singleton hc]
  have hrange : 3 ≤ Module.finrank K (LinearMap.range L) := by
    have hV : Module.finrank K (Fin 4 → K) = 4 := by
      rw [Module.finrank_pi]
      simp
    have h := LinearMap.finrank_range_add_finrank_ker L
    omega
  have hspan : 3 ≤ Module.finrank K (Submodule.span K (Set.range r)) := by
    have hrow : Set.range M.row = Set.range r := by
      change Set.range (fun i => r i) = Set.range r
      rfl
    have hrank : M.rank = Module.finrank K (Submodule.span K (Set.range r)) := by
      rw [Matrix.rank_eq_finrank_span_row M, hrow]
    have hdef : M.rank = Module.finrank K (LinearMap.range L) := rfl
    omega
  obtain ⟨κ, a, ha_inj, hspan_eq, hli⟩ := exists_linearIndependent' K r
  letI : Fintype κ := Fintype.ofInjective a ha_inj
  have hcard : 3 ≤ Fintype.card κ := by
    have h1 : Module.finrank K (Submodule.span K (Set.range (r ∘ a))) = Fintype.card κ :=
      finrank_span_eq_card hli
    rw [hspan_eq] at h1
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 3) (β := κ) (by simpa using hcard)
  let f : Fin 3 → κ := e
  have hcomp : LinearIndependent K ((r ∘ a) ∘ f) := hli.comp f e.injective
  refine ⟨a (e 0), a (e 1), a (e 2), ?_⟩
  have hfun : ((r ∘ a) ∘ f) = ![r (a (e 0)), r (a (e 1)), r (a (e 2))] := by
    funext i
    fin_cases i <;> rfl
  rwa [hfun] at hcomp

lemma rootChar_eq_zeta_pow {F : Type} [Field F] {p : ℕ} [NeZero p] {ζ : Fˣ}
    (hζ : orderOf ζ = p) {x : Fin Tag.F4.rank → Fˣ} {v : Fin Tag.F4.rank → ZMod p}
    (hv : ∀ i, ζ ^ (v i).val = x i) (α : Fin Tag.F4.rank → ℤ) :
    rootChar x α = ζ ^ ((∑ i, v i * (α i : ZMod p)).val) := by
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have h1 : rootChar x α = ζ ^ (∑ i, (v i).val * α i) := by
    rw [rootChar]
    trans ∏ i, ζ ^ ((v i).val * α i)
    · exact Finset.prod_congr rfl fun i _ => by rw [← hv i, ← zpow_natCast, zpow_mul]
    · rw [Finset.prod_zpow_eq_zpow_sum]
  have hcast : ((∑ i, (v i).val * α i : ℤ) : ZMod p) =
      ∑ i, v i * (α i : ZMod p) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [ZMod.natCast_zmod_val]
  rw [h1, ← pow_val_eq_zpow_of_pow_eq_one hζp (∑ i, v i * (α i : ZMod p))
    (∑ i, (v i).val * α i) hcast]

lemma rootChar_eq_one_iff {F : Type} [Field F] {p : ℕ} [NeZero p] {ζ : Fˣ}
    (hζ : orderOf ζ = p) {a : Fin Tag.F4.rank → Fˣ} {c : Fin Tag.F4.rank → ZMod p}
    (hc : ∀ i, ζ ^ (c i).val = a i) (α : Fin Tag.F4.rank → ℤ) :
    rootChar a α = 1 ↔ (∑ i, c i * (α i : ZMod p)) = 0 := by
  rw [rootChar_eq_zeta_pow hζ hc α]
  rw [← orderOf_dvd_iff_pow_eq_one, hζ]
  rw [← ZMod.natCast_eq_zero_iff (∑ i, c i * (α i : ZMod p)).val p,
    ZMod.natCast_zmod_val]

lemma neg_mem_rootCharKernel {F : Type} [Field F] {a : Fin Tag.F4.rank → Fˣ}
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ rootCharKernel (τ := .F4) a) :
    -α ∈ rootCharKernel (τ := .F4) a := by
  rcases hα with ⟨hroot, hchar⟩
  refine ⟨IsRoot.neg hroot, ?_⟩
  have h0 : rootChar a (α + -α) = 1 := by rw [add_neg_cancel, rootChar_zero]
  rw [rootChar_add, hchar, one_mul] at h0
  exact h0

theorem hker_annihilator {F : Type} [Field F] {p : ℕ} [NeZero p] [Fact p.Prime]
    {a : Fin Tag.F4.rank → Fˣ} {ζ : Fˣ} (hζ : orderOf ζ = p)
    {c : Fin Tag.F4.rank → ZMod p} (hc : ∀ i, ζ ^ (c i).val = a i)
    (hker : ∀ b : Fin Tag.F4.rank → Fˣ, (∀ i, b i ^ p = 1) →
      (∀ α ∈ rootCharKernel (τ := .F4) a, rootChar b α = 1) →
      rootDiagUnit .F4 b ∈ Subgroup.zpowers (rootDiagUnit .F4 a)) :
    ∀ v : Fin Tag.F4.rank → ZMod p,
      (∀ i : {α : Fin Tag.F4.rank → ℤ // α ∈ f4PosRoots ∧ α ∈ rootCharKernel (τ := .F4) a},
        (fun k => (i.1 k : ZMod p)) ⬝ᵥ v = 0) →
      ∃ t : ZMod p, v = t • c := by
  intro v hv
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  let b : Fin Tag.F4.rank → Fˣ := fun i => ζ ^ (v i).val
  have hb : ∀ i, b i ^ p = 1 := by
    intro i
    have h1 : (ζ ^ ((v i).val : ℤ)) ^ (p : ℤ) = 1 := by
      rw [← zpow_mul, mul_comm, zpow_mul]
      rw [show ζ ^ (p : ℤ) = 1 by simpa using hζp]
      simp
    simpa only [b, zpow_natCast] using h1
  have hchar : ∀ α ∈ rootCharKernel (τ := .F4) a, rootChar b α = 1 := by
    intro α hα
    have hdot : (∑ i, v i * (α i : ZMod p)) = 0 := by
      have hcomm : (∑ i, v i * (α i : ZMod p)) =
          ∑ i, (α i : ZMod p) * v i :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rcases pos_or_neg_mem_f4PosRoots hα.1 with hp | hn
      · have h := hv ⟨α, hp, hα⟩
        rw [hcomm]
        simpa [dotProduct] using h
      · have hαn : -α ∈ rootCharKernel (τ := .F4) a := neg_mem_rootCharKernel hα
        have h := hv ⟨-α, hn, hαn⟩
        have hsum' : (∑ i, (((-α) i : ZMod p)) * v i) = 0 := by
          simpa [dotProduct] using h
        have hsum : (∑ i, (α i : ZMod p) * v i) = 0 := by
          have h1 : (∑ i, -((α i : ZMod p) * v i)) =
              -(∑ i, (α i : ZMod p) * v i) := by
            exact Finset.sum_neg_distrib (s := Finset.univ)
              (f := fun i => (α i : ZMod p) * v i)
          have hneg : (∑ i, (((-α) i : ZMod p)) * v i) =
              -(∑ i, (α i : ZMod p) * v i) := by
            calc (∑ i, (((-α) i : ZMod p)) * v i) =
                ∑ i, -((α i : ZMod p) * v i) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  simp [Pi.neg_apply, neg_mul]
                  rfl
              _ = -(∑ i, (α i : ZMod p) * v i) := h1
          rw [hneg] at hsum'
          exact neg_eq_zero.mp hsum'
        rw [hcomm]
        exact hsum
    exact (rootChar_eq_one_iff hζ (fun i => rfl) α).2 hdot
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hker b hb hchar)
  have hpow : rootDiagUnit .F4 a ^ k = rootDiagUnit .F4 (a ^ k) := by
    change rootDiagUnitHom .F4 F a ^ k = rootDiagUnitHom .F4 F (a ^ k)
    rw [map_zpow]
  have hb_eq : b = a ^ k := by
    apply rootDiagUnit_injective (τ := .F4)
    rw [← hk, hpow]
  refine ⟨(k : ZMod p), ?_⟩
  funext i
  have hbi : b i = (a i) ^ k := by
    rw [hb_eq]
    rfl
  have h1 : ζ ^ (v i).val = ζ ^ ((c i).val * k) := by
    calc ζ ^ (v i).val = b i := rfl
      _ = (a i) ^ k := hbi
      _ = (ζ ^ (c i).val) ^ k := by rw [hc i]
      _ = ζ ^ ((c i).val * k) := by rw [← zpow_natCast, zpow_mul]
  have h2 : ζ ^ (((k : ZMod p) * c i).val) = ζ ^ ((c i).val * k) := by
    exact pow_val_eq_zpow_of_pow_eq_one hζp (k * c i) ((c i).val * k)
      (by push_cast; rw [ZMod.natCast_zmod_val]; ring)
  have hv_i : v i = (k : ZMod p) * c i := by
    apply eq_of_pow_val_eq_pow_val hζ
    rw [h2]
    exact h1
  simpa [Pi.smul_apply] using hv_i

abbrev F4PosKernel {F : Type} [Field F] (a : Fin Tag.F4.rank → Fˣ) :=
  {α : Fin Tag.F4.rank → ℤ // α ∈ f4PosRoots ∧ α ∈ rootCharKernel (τ := .F4) a}

noncomputable instance f4PosKernelFintype {F : Type} [Field F]
    (a : Fin Tag.F4.rank → Fˣ) : Fintype (F4PosKernel a) := by
  classical
  haveI : Fintype {α : Fin Tag.F4.rank → ℤ // α ∈ f4PosRoots} :=
    Fintype.ofFinset f4PosRoots.toFinset (by intro x; exact List.mem_toFinset)
  haveI : Finite (F4PosKernel a) :=
    Finite.of_injective (fun i => (⟨i.1, i.2.1⟩ : {α : Fin Tag.F4.rank → ℤ // α ∈ f4PosRoots}))
      (by intro x y h; exact Subtype.ext (congrArg (fun z => z.1) h))
  exact Fintype.ofFinite (F4PosKernel a)

lemma exists_long_short_of_eq_one {F : Type} [Field F] {p : ℕ}
    {a : Fin Tag.F4.rank → Fˣ} (ha1 : a = 1) :
    (∃ α ∈ rootCharKernel (τ := .F4) a, IsLongRoot α) ∧
      ∃ β ∈ rootCharKernel (τ := .F4) a, IsShortRoot β := by
  have hLmem : Pi.single i0 1 ∈ rootCharKernel (τ := .F4) a := by
    refine ⟨IsRoot.basis i0, ?_⟩
    have h := rootChar_nsmul_single a i0 1
    simpa [ha1] using h
  have hSmem : Pi.single i3 1 ∈ rootCharKernel (τ := .F4) a := by
    refine ⟨IsRoot.basis i3, ?_⟩
    have h := rootChar_nsmul_single a i3 1
    simpa [ha1] using h
  have hL : IsLongRoot (Pi.single i0 1) := ⟨1, by simp⟩
  have hS : IsShortRoot (Pi.single i3 1) := ⟨1, by simp⟩
  exact ⟨⟨Pi.single i0 1, hLmem, hL⟩, ⟨Pi.single i3 1, hSmem, hS⟩⟩

lemma det_map_intCast_eq_zero {p : ℕ} [NeZero p] {x a b c : Fin Tag.F4.rank → ℤ}
    (h : (Matrix.of ![x, a, b, c] : Matrix (Fin 4) (Fin 4) ℤ).det = 0) :
    (Matrix.of ![fun i => (x i : ZMod p), fun i => (a i : ZMod p),
      fun i => (b i : ZMod p), fun i => (c i : ZMod p)] :
      Matrix (Fin 4) (Fin 4) (ZMod p)).det = 0 := by
  have h' := congrArg (Int.castRingHom (ZMod p)) h
  rw [RingHom.map_det] at h'
  convert h' using 2
  · ext i j
    fin_cases i <;> simp [Matrix.map_apply, Matrix.of_apply]
  · simp

lemma rootChar_eq_one_iff_dot {F : Type} [Field F] {p : ℕ} [NeZero p] {ζ : Fˣ}
    (hζ : orderOf ζ = p) {a : Fin Tag.F4.rank → Fˣ} {c : Fin Tag.F4.rank → ZMod p}
    (hc : ∀ i, ζ ^ (c i).val = a i) (α : Fin Tag.F4.rank → ℤ) :
    rootChar a α = 1 ↔ (fun k => (α k : ZMod p)) ⬝ᵥ c = 0 := by
  rw [rootChar_eq_one_iff hζ hc α, dotProduct]
  constructor
  · intro h
    rw [show (∑ i, (α i : ZMod p) * c i) =
        ∑ i, c i * (α i : ZMod p) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    exact h
  · intro h
    rw [← show (∑ i, (α i : ZMod p) * c i) =
        ∑ i, c i * (α i : ZMod p) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    exact h

def dotCLin {p : ℕ} [NeZero p] (c : Fin 4 → ZMod p) :
    (Fin 4 → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun x := x ⬝ᵥ c
  map_add' x y := add_dotProduct x y c
  map_smul' a x := smul_dotProduct a x c

lemma dot_eq_zero_of_mem_span {p : ℕ} [NeZero p] {c α β γ : Fin 4 → ZMod p}
    (hα : α ⬝ᵥ c = 0) (hβ : β ⬝ᵥ c = 0) (hγ : γ ⬝ᵥ c = 0) :
    ∀ x ∈ Submodule.span (ZMod p) (Set.range ![α, β, γ]), x ⬝ᵥ c = 0 := by
  intro x hx
  have hle : Submodule.span (ZMod p) (Set.range ![α, β, γ]) ≤
      LinearMap.ker (dotCLin c) := by
    refine Submodule.span_le.2 ?_
    intro v hv
    rcases hv with ⟨w, rfl⟩
    fin_cases w <;> simp [dotCLin, hα, hβ, hγ]
  have hxker : x ∈ LinearMap.ker (dotCLin c) := hle hx
  simpa [dotCLin, LinearMap.mem_ker] using hxker

lemma exists_long_short_of_ne_one {F : Type} [Field F] [CharP F 2] {p : ℕ}
    {a : Fin Tag.F4.rank → Fˣ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : ∀ i, a i ^ p = 1)
    (hker : ∀ b : Fin Tag.F4.rank → Fˣ, (∀ i, b i ^ p = 1) →
      (∀ α ∈ rootCharKernel (τ := .F4) a, rootChar b α = 1) →
      rootDiagUnit .F4 b ∈ Subgroup.zpowers (rootDiagUnit .F4 a))
    (hne : a ≠ 1) :
    (∃ α ∈ rootCharKernel (τ := .F4) a, IsLongRoot α) ∧
      ∃ β ∈ rootCharKernel (τ := .F4) a, IsShortRoot β := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ 1 := by
    by_contra h
    apply hne
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  let ζ := a i0
  have hdvd : orderOf ζ ∣ p := orderOf_dvd_iff_pow_eq_one.2 (ha i0)
  have hne1 : orderOf ζ ≠ 1 := by
    intro h
    exact hi0 (orderOf_eq_one_iff.1 h)
  have hζ : orderOf ζ = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf ζ) hdvd with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  choose c hc using fun i => exists_pow_val_eq_of_pow_eq_one hζ (ha i)
  have hann := hker_annihilator (a := a) (ζ := ζ) (c := c) hζ hc hker
  let r : F4PosKernel a → Fin 4 → ZMod p := fun i => fun q => (i.1 q : ZMod p)
  obtain ⟨i, j, l, hli⟩ :=
    exists_linearIndependent_triple (K := ZMod p) (ι := F4PosKernel a) r c hann
  have hcheck : goodNormalZ (cofactorZ i.1 j.1 l.1) = true :=
    f4TripleCheck i.2.1 j.2.1 l.2.1
  obtain ⟨⟨x, hxP, hxorth⟩, ⟨y, hyP, hyorth⟩⟩ := goodNormalZ_spec hcheck
  let αm : Fin 4 → ZMod p := fun q => (i.1 q : ZMod p)
  let βm : Fin 4 → ZMod p := fun q => (j.1 q : ZMod p)
  let γm : Fin 4 → ZMod p := fun q => (l.1 q : ZMod p)
  have hgen : ∀ w : F4PosKernel a, (fun q => (w.1 q : ZMod p)) ⬝ᵥ c = 0 := by
    intro w
    exact (rootChar_eq_one_iff_dot hζ hc w.1).1 w.2.2.2
  have hα : αm ⬝ᵥ c = 0 := by
    change (fun q => (i.1 q : ZMod p)) ⬝ᵥ c = 0
    exact hgen i
  have hβ : βm ⬝ᵥ c = 0 := by
    change (fun q => (j.1 q : ZMod p)) ⬝ᵥ c = 0
    exact hgen j
  have hγ : γm ⬝ᵥ c = 0 := by
    change (fun q => (l.1 q : ZMod p)) ⬝ᵥ c = 0
    exact hgen l
  have hli' : LinearIndependent (ZMod p) ![αm, βm, γm] := by
    simpa [r, αm, βm, γm] using hli
  have hxlong : IsLongRoot x.1 := x.2
  have hxroot : IsRoot .F4 x.1 := IsLongRoot.isRoot hxlong
  have hxdetZ : (Matrix.of ![x.1, i.1, j.1, l.1] : Matrix (Fin 4) (Fin 4) ℤ).det = 0 := by
    rw [← dot4Z_cofactorZ x.1 i.1 j.1 l.1, hxorth]
  have hxdetP : (Matrix.of ![fun q => (x.1 q : ZMod p), αm, βm, γm] :
      Matrix (Fin 4) (Fin 4) (ZMod p)).det = 0 := by
    simpa [αm, βm, γm] using det_map_intCast_eq_zero hxdetZ
  have hxspan : (fun q => (x.1 q : ZMod p)) ∈
      Submodule.span (ZMod p) (Set.range ![αm, βm, γm]) :=
    mem_span_of_det_eq_zero hli' hxdetP
  have hxorthc : (fun q => (x.1 q : ZMod p)) ⬝ᵥ c = 0 :=
    dot_eq_zero_of_mem_span hα hβ hγ _ hxspan
  have hxchar : rootChar a x.1 = 1 := (rootChar_eq_one_iff_dot hζ hc x.1).2 hxorthc
  have hxker : x.1 ∈ rootCharKernel (τ := .F4) a := ⟨hxroot, hxchar⟩
  have hylong : IsShortRoot y.1 := y.2
  have hyroot : IsRoot .F4 y.1 := IsShortRoot.isRoot hylong
  have hydetZ : (Matrix.of ![y.1, i.1, j.1, l.1] : Matrix (Fin 4) (Fin 4) ℤ).det = 0 := by
    rw [← dot4Z_cofactorZ y.1 i.1 j.1 l.1, hyorth]
  have hydetP : (Matrix.of ![fun q => (y.1 q : ZMod p), αm, βm, γm] :
      Matrix (Fin 4) (Fin 4) (ZMod p)).det = 0 := by
    simpa [αm, βm, γm] using det_map_intCast_eq_zero hydetZ
  have hyspan : (fun q => (y.1 q : ZMod p)) ∈
      Submodule.span (ZMod p) (Set.range ![αm, βm, γm]) :=
    mem_span_of_det_eq_zero hli' hydetP
  have hyorthc : (fun q => (y.1 q : ZMod p)) ⬝ᵥ c = 0 :=
    dot_eq_zero_of_mem_span hα hβ hγ _ hyspan
  have hychar : rootChar a y.1 = 1 := (rootChar_eq_one_iff_dot hζ hc y.1).2 hyorthc
  have hyker : y.1 ∈ rootCharKernel (τ := .F4) a := ⟨hyroot, hychar⟩
  exact ⟨⟨x.1, hxker, hxlong⟩, ⟨y.1, hyker, hylong⟩⟩

theorem exists_long_short_mem_rootCharKernel_F4 {F : Type} [Field F] [CharP F 2]
    {p : ℕ}
    {a : Fin Tag.F4.rank → Fˣ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : ∀ i, a i ^ p = 1)
    (hker : ∀ b : Fin Tag.F4.rank → Fˣ, (∀ i, b i ^ p = 1) →
      (∀ α ∈ rootCharKernel (τ := .F4) a, rootChar b α = 1) →
      rootDiagUnit .F4 b ∈ Subgroup.zpowers (rootDiagUnit .F4 a)) :
    (∃ α ∈ rootCharKernel (τ := .F4) a, IsLongRoot α) ∧
      ∃ β ∈ rootCharKernel (τ := .F4) a, IsShortRoot β := by
  by_cases ha1 : a = 1
  · exact exists_long_short_of_eq_one (p := p) ha1
  · exact exists_long_short_of_ne_one hp hp2 ha hker ha1

end CFSG.LocalAnalysis.GLTheoremA.T173O
