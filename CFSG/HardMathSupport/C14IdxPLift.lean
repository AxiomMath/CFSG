module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdx
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5TorusGen

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple coordHom_apply)

namespace CFSG.HardMathSupport.C14Idx

private def corootMat {τ : Tag} (Δ : Finset (Fin τ.rank → ℤ)) :
    Matrix (Fin τ.rank) Δ ℤ := fun i β => corootVec (β : Fin τ.rank → ℤ) i

private def gram {τ : Tag} (Δ : Finset (Fin τ.rank → ℤ)) : Matrix Δ Δ ℤ :=
  Matrix.transpose (corootMat Δ) * corootMat Δ

private noncomputable def cLin {τ : Tag} (Δ : Finset (Fin τ.rank → ℤ)) :
    (Δ → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ) := Matrix.toLin' (corootMat Δ)

private noncomputable def latD {τ : Tag} (Δ : Finset (Fin τ.rank → ℤ)) :
    Matrix Δ (Fin τ.rank) ℤ := (gram Δ).adjugate * Matrix.transpose (corootMat Δ)

private lemma cLin_apply {τ : Tag} (Δ : Finset (Fin τ.rank → ℤ)) (x : Δ → ℤ) :
    cLin Δ x = ∑ β : Δ, x β • corootVec (β : Fin τ.rank → ℤ) := by
  ext i
  simp [cLin, corootMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm]

private lemma cLin_injective {τ : Tag} {Δ : Finset (Fin τ.rank → ℤ)}
    (hind : LinearIndependent ℤ fun β : Δ => corootVec (β : Fin τ.rank → ℤ)) :
    Function.Injective (cLin Δ) := by
  intro x y hxy
  have h0 : cLin Δ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hz := (Fintype.linearIndependent_iff.mp hind) (x - y) (by rwa [cLin_apply] at h0)
  funext β
  exact sub_eq_zero.mp (hz β)

private lemma mem_closure_corootVec_iff {τ : Tag} (Δ : Finset (Fin τ.rank → ℤ))
    (y : Fin τ.rank → ℤ) :
    y ∈ AddSubgroup.closure (corootVec '' (Δ : Set (Fin τ.rank → ℤ))) ↔
      ∃ x : Δ → ℤ, cLin Δ x = y := by
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_image_finset_iff_exists_fun]
  exact exists_congr fun x => by rw [cLin_apply]

private lemma exists_generator_representation {τ : Tag} {k : Type} [Field k] {p N : ℕ}
    (hp : p.Prime) {Δ : Finset (Fin τ.rank → ℤ)}
    {d : (Fin τ.rank → ℤ) → kˣ} (hN : ∀ β : Δ, d (β : Fin τ.rank → ℤ) ^ p ^ N = 1) :
    ∃ (m : ℕ) (x : Δ → ℤ) (ζ : kˣ), orderOf ζ = p ^ m ∧
      ∀ β : Δ, d (β : Fin τ.rank → ℤ) = ζ ^ x β := by
  classical
  have hNe : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  have hCyc : IsCyclic (rootsOfUnity (p ^ N) k) :=
    @rootsOfUnity.isCyclic k (p ^ N) hNe _ _
  obtain ⟨ζ, hζ⟩ := hCyc.exists_generator
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp
    (orderOf_dvd_iff_pow_eq_one.mpr ζ.2)
  choose x hx using fun β : Δ =>
    Subgroup.mem_zpowers_iff.mp (hζ ⟨d (β : Fin τ.rank → ℤ), by
      rw [mem_rootsOfUnity]; exact hN β⟩)
  exact ⟨m, x, (ζ : kˣ), hm, fun β => by
    simpa using congrArg Subtype.val (hx β).symm⟩

private lemma mem_closure_of_pow_smul_mem {τ : Tag} {p : ℕ}
    {Ψ : Set (Fin τ.rank → ℤ)} (hsat : CorootPSaturated p Ψ) :
    ∀ (m : ℕ) (y : Fin τ.rank → ℤ),
      (p ^ m : ℤ) • y ∈ AddSubgroup.closure (corootVec '' Ψ) →
        y ∈ AddSubgroup.closure (corootVec '' Ψ) := by
  intro m
  induction m with
  | zero => intro y hy; simpa using hy
  | succ m ih =>
      intro y hy
      have hpow : (p ^ (m + 1) : ℤ) • y = p • ((p ^ m : ℤ) • y) := by
        rw [pow_succ, mul_comm (↑p ^ m : ℤ) (↑p), mul_smul, Nat.cast_smul_eq_nsmul]
      have h1 : p • ((p ^ m : ℤ) • y) ∈ AddSubgroup.closure (corootVec '' Ψ) := by
        rwa [← hpow]
      exact ih y (hsat _ h1)

private lemma eq_one_of_dvd_cLin {τ : Tag} {k : Type} [Field k] {p : ℕ}
    {Δ : Finset (Fin τ.rank → ℤ)}
    (hind : LinearIndependent ℤ fun β : Δ => corootVec (β : Fin τ.rank → ℤ))
    (hsat : CorootPSaturated p (Δ : Set (Fin τ.rank → ℤ)))
    {d : (Fin τ.rank → ℤ) → kˣ} {m : ℕ} {x : Δ → ℤ} {ζ : kˣ}
    (horder : orderOf ζ = p ^ m)
    (hxval : ∀ β : Δ, d (β : Fin τ.rank → ℤ) = ζ ^ x β)
    (hd1 : coordTuple Δ d = 1) :
    ∀ β ∈ Δ, d β = 1 := by
  have hdvd : ∀ i, (p ^ m : ℤ) ∣ cLin Δ x i := by
    intro i
    have h2 : (∏ β : Δ, d (β : Fin τ.rank → ℤ) ^ corootVec (β : Fin τ.rank → ℤ) i) = 1 := by
      rw [Finset.prod_coe_sort Δ (fun β : Fin τ.rank → ℤ =>
        d β ^ corootVec β i)]
      simpa [coordTuple, corootVec] using congrFun hd1 i
    have h3 : ζ ^ cLin Δ x i = 1 := by
      rw [cLin_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← Finset.prod_zpow_eq_zpow_sum (Finset.univ : Finset Δ) ζ
        (fun β => x β * corootVec (β : Fin τ.rank → ℤ) i), ← h2]
      exact Finset.prod_congr rfl fun β _ => by rw [hxval β, zpow_mul]
    have h := orderOf_dvd_iff_zpow_eq_one.mpr h3
    rwa [horder] at h
  set y : Fin τ.rank → ℤ := fun i => cLin Δ x i / (p ^ m : ℤ)
  have hxy : cLin Δ x = (p ^ m : ℤ) • y := by
    funext i
    simpa [y, Pi.smul_apply, smul_eq_mul, mul_comm] using
      (Int.ediv_mul_cancel (hdvd i)).symm
  have hy : y ∈ AddSubgroup.closure (corootVec '' (Δ : Set (Fin τ.rank → ℤ))) := by
    refine mem_closure_of_pow_smul_mem hsat m y ?_
    rw [← hxy]
    exact (mem_closure_corootVec_iff Δ (cLin Δ x)).mpr ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := (mem_closure_corootVec_iff Δ y).mp hy
  have hxz : x = (p ^ m : ℤ) • z := by
    refine cLin_injective hind ?_
    rw [hxy, map_smul, hz]
  have hζp : ζ ^ p ^ m = 1 := by simpa [horder] using pow_orderOf_eq_one ζ
  intro β hβ
  have hxβ : x ⟨β, hβ⟩ = (p ^ m : ℤ) * z ⟨β, hβ⟩ := by
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hxz ⟨β, hβ⟩
  calc
    d β = ζ ^ x ⟨β, hβ⟩ := hxval ⟨β, hβ⟩
    _ = ζ ^ ((p ^ m : ℤ) * z ⟨β, hβ⟩) := by rw [hxβ]
    _ = (ζ ^ (p ^ m : ℤ)) ^ z ⟨β, hβ⟩ := zpow_mul _ _ _
    _ = (ζ ^ p ^ m) ^ z ⟨β, hβ⟩ := by rw [← Nat.cast_pow, zpow_natCast]
    _ = 1 := by rw [hζp, one_zpow]

private lemma eq_one_of_coordTuple_eq_one {τ : Tag} {k : Type} [Field k] {p : ℕ}
    (hp : p.Prime) {Δ : Finset (Fin τ.rank → ℤ)}
    (hind : LinearIndependent ℤ fun β : Δ => corootVec (β : Fin τ.rank → ℤ))
    (hsat : CorootPSaturated p (Δ : Set (Fin τ.rank → ℤ)))
    {d : (Fin τ.rank → ℤ) → kˣ} (hd : ∀ β ∈ Δ, ∃ n : ℕ, d β ^ p ^ n = 1)
    (hd1 : coordTuple Δ d = 1) :
    ∀ β ∈ Δ, d β = 1 := by
  classical
  choose n hn using fun β : Δ => hd β β.2
  let N : ℕ := ∑ γ : Δ, n γ
  have hN : ∀ β : Δ, d (β : Fin τ.rank → ℤ) ^ p ^ N = 1 := by
    intro β
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_iff_pow_eq_one.mpr (hn β)).trans (Nat.pow_dvd_pow p
        (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ β))))
  obtain ⟨m, x, ζ, horder, hxval⟩ := exists_generator_representation hp hN
  exact eq_one_of_dvd_cLin hind hsat horder hxval hd1

theorem eqOn_of_coordTuple_eq {τ : Tag} {k : Type} [Field k] {p : ℕ} (hp : p.Prime)
    {Δ : Finset (Fin τ.rank → ℤ)}
    (hind : LinearIndependent ℤ fun β : Δ => corootVec (β : Fin τ.rank → ℤ))
    (hsat : CorootPSaturated p (Δ : Set (Fin τ.rank → ℤ)))
    {c c' : (Fin τ.rank → ℤ) → kˣ} (hc : ∀ β ∈ Δ, ∃ n : ℕ, c β ^ p ^ n = 1)
    (hc' : ∀ β ∈ Δ, ∃ n : ℕ, c' β ^ p ^ n = 1) (h : coordTuple Δ c = coordTuple Δ c') :
    ∀ β ∈ Δ, c β = c' β := by
  classical
  let d : (Fin τ.rank → ℤ) → kˣ := c / c'
  have hd : ∀ β ∈ Δ, ∃ n : ℕ, d β ^ p ^ n = 1 := by
    intro β hβ
    obtain ⟨a, ha⟩ := hc β hβ
    obtain ⟨b, hb⟩ := hc' β hβ
    refine ⟨max a b, ?_⟩
    have hca : c β ^ p ^ max a b = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_iff_pow_eq_one.mpr ha).trans
        (Nat.pow_dvd_pow p (le_max_left a b)))
    have hcb : c' β ^ p ^ max a b = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_iff_pow_eq_one.mpr hb).trans
        (Nat.pow_dvd_pow p (le_max_right a b)))
    simp only [d, Pi.div_apply, div_pow]
    rw [hca, hcb, div_one]
  have hd1 : coordTuple Δ d = 1 := by
    rw [show d = c / c' from rfl, ← coordHom_apply, map_div, coordHom_apply,
      coordHom_apply, h, div_self']
  intro β hβ
  exact div_eq_one.mp (by simpa [d] using eq_one_of_coordTuple_eq_one hp hind hsat hd hd1 β hβ)

private lemma prod_coordTuple_zpow {τ : Tag} {k : Type} [Field k]
    {Δ : Finset (Fin τ.rank → ℤ)} (c : (Fin τ.rank → ℤ) → kˣ) (β : Δ) :
    (∏ i, coordTuple Δ c i ^ latD Δ β i) = c (β : Fin τ.rank → ℤ) ^ (gram Δ).det := by
  classical
  have hDC : latD Δ * corootMat Δ = (gram Δ).det • (1 : Matrix Δ Δ ℤ) := by
    simp [latD, gram, Matrix.mul_assoc, Matrix.adjugate_mul]
  have hcoord : ∀ i, coordTuple Δ c i =
      ∏ γ : Δ, c (γ : Fin τ.rank → ℤ) ^ corootMat Δ i γ := by
    intro i
    rw [coordTuple, ← Finset.prod_coe_sort]
    rfl
  have hexp : ∀ γ : Δ, (∑ i, corootMat Δ i γ * latD Δ β i) =
      if γ = β then (gram Δ).det else 0 := by
    intro γ
    have h1 : (∑ i, corootMat Δ i γ * latD Δ β i) = (latD Δ * corootMat Δ) β γ := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h1, hDC]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : γ = β
    · rw [if_pos h.symm, if_pos h, mul_one]
    · rw [if_neg (fun hb => h hb.symm), if_neg h, mul_zero]
  have hstep : (∏ i, coordTuple Δ c i ^ latD Δ β i) =
      ∏ i, ∏ γ : Δ, c (γ : Fin τ.rank → ℤ) ^ (corootMat Δ i γ * latD Δ β i) := by
    simp only [hcoord, Finset.prod_zpow, zpow_mul]
  rw [hstep, Finset.prod_comm]
  simp only [Finset.prod_zpow_eq_zpow_sum]
  rw [Finset.prod_eq_single β]
  · rw [hexp β, if_pos rfl]
  · intro γ _ hγ; rw [hexp γ, if_neg hγ, zpow_zero]
  · intro h; exact absurd (Finset.mem_univ β) h

private lemma gram_det_ne_zero {τ : Tag} {Δ : Finset (Fin τ.rank → ℤ)}
    (hind : LinearIndependent ℤ fun β : Δ => corootVec (β : Fin τ.rank → ℤ)) :
    (gram Δ).det ≠ 0 := by
  intro hdet
  obtain ⟨z, hz_ne, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hC : cLin Δ z = (corootMat Δ).mulVec z := by rw [cLin, Matrix.toLin'_apply]
  have hquad : dotProduct ((corootMat Δ).mulVec z) ((corootMat Δ).mulVec z) = 0 := by
    calc
      dotProduct ((corootMat Δ).mulVec z) ((corootMat Δ).mulVec z)
          = dotProduct z ((gram Δ).mulVec z) := by
              rw [gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
      _ = 0 := by rw [hz]; simp
  have hCz : (corootMat Δ).mulVec z = 0 := by rwa [dotProduct_self_eq_zero] at hquad
  exact hz_ne (cLin_injective hind (by rw [hC, hCz, map_zero]))

theorem exists_coordTuple_eq_of_pow_eq_one {τ : Tag} {k : Type} [Field k] {p : ℕ}
    (hp : p.Prime) {Δ : Finset (Fin τ.rank → ℤ)}
    (hind : LinearIndependent ℤ fun β : Δ => corootVec (β : Fin τ.rank → ℤ))
    {c : (Fin τ.rank → ℤ) → kˣ} (hx : ∃ n : ℕ, coordTuple Δ c ^ p ^ n = 1) :
    ∃ c' : (Fin τ.rank → ℤ) → kˣ, (∀ β ∈ Δ, ∃ n : ℕ, c' β ^ p ^ n = 1) ∧
      coordTuple Δ c' = coordTuple Δ c := by
  classical
  obtain ⟨n, hn⟩ := hx
  let x : Fin τ.rank → kˣ := coordTuple Δ c
  let d : (Fin τ.rank → ℤ) → kˣ := c ^ p ^ n
  have hd1 : coordTuple Δ d = 1 := by
    rw [show d = c ^ p ^ n from rfl, ← coordHom_apply, map_pow, coordHom_apply, hn]
  have hcm : ∀ β : Δ, c (β : Fin τ.rank → ℤ) ^ (p ^ n * (gram Δ).det.natAbs) = 1 := by
    intro β
    have hmul := prod_coordTuple_zpow d β
    have hleft : (∏ i, coordTuple Δ d i ^ latD Δ β i) = 1 := by rw [hd1]; simp
    have hright : d β ^ (gram Δ).det = 1 := by rw [hleft] at hmul; exact hmul.symm
    have h1 : c (β : Fin τ.rank → ℤ) ^ ((p ^ n : ℤ) * (gram Δ).det) = 1 := by
      rw [show d β = c (β : Fin τ.rank → ℤ) ^ ((p ^ n : ℕ) : ℤ) from by
        rw [zpow_natCast]; rfl, ← zpow_mul] at hright
      simpa using hright
    have h2 : c (β : Fin τ.rank → ℤ) ^ (((p ^ n : ℤ) * (gram Δ).det).natAbs) = 1 :=
      (pow_natAbs_eq_one).mpr h1
    have h3 : (((p ^ n : ℤ) * (gram Δ).det).natAbs) = p ^ n * (gram Δ).det.natAbs := by
      rw [Int.natAbs_mul]; simp
    simpa [h3] using h2
  have hM0 : (gram Δ).det.natAbs ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Int.natAbs_pos.mpr (gram_det_ne_zero hind))
  obtain ⟨a, q, hq, hM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM0 p hp.one_lt.ne'
  have hcop : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr hq
  have hcopP : Nat.Coprime (p ^ (n + a)) q := hcop.pow_left (n + a)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcopP
  let c' : (Fin τ.rank → ℤ) → kˣ := fun γ => c γ ^ (v * (q : ℤ))
  have hxP : x ^ p ^ (n + a) = 1 := by rw [pow_add, pow_mul, hn, one_pow]
  have hxq : x ^ (v * (q : ℤ)) = x := by
    have h1 : v * (q : ℤ) = 1 - u * (p ^ (n + a) : ℤ) := by
      have h : u * (↑p : ℤ) ^ (n + a) + v * (q : ℤ) = 1 := by
        simpa [Nat.cast_pow] using huv
      have h' : v * (q : ℤ) = 1 - u * (↑p : ℤ) ^ (n + a) := by linarith
      simpa [Nat.cast_pow] using h'
    rw [h1, zpow_sub, zpow_one, mul_comm u (p ^ (n + a) : ℤ), zpow_mul,
      ← Nat.cast_pow, zpow_natCast, hxP, one_zpow, inv_one, mul_one]
  have hcp : ∀ β ∈ Δ, c' β ^ p ^ (n + a) = 1 := by
    intro β hβ
    have hExp : (v * (q : ℤ)) * (p ^ (n + a) : ℤ) =
        v * ((p ^ n * (gram Δ).det.natAbs : ℕ) : ℤ) := by
      rw [show (p ^ (n + a) : ℤ) = (p ^ n : ℤ) * (p ^ a : ℤ) by rw [pow_add]]
      rw [hM]
      push_cast
      ring
    rw [show c' β = c β ^ (v * (q : ℤ)) from rfl, ← zpow_natCast, ← zpow_mul,
      Nat.cast_pow, hExp,
      mul_comm v ((p ^ n * (gram Δ).det.natAbs : ℕ) : ℤ), zpow_mul, zpow_natCast,
      hcm ⟨β, hβ⟩, one_zpow]
  refine ⟨c', fun β hβ => ⟨n + a, hcp β hβ⟩, ?_⟩
  calc
    coordTuple Δ c' = x ^ (v * (q : ℤ)) := by
      rw [show c' = c ^ (v * (q : ℤ)) from rfl, ← coordHom_apply, map_zpow,
        coordHom_apply]
    _ = x := hxq

end CFSG.HardMathSupport.C14Idx
