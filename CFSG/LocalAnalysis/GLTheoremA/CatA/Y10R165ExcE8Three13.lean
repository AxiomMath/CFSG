module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8QTorus3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three9

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)

open scoped Matrix MatrixGroups

section Certs

theorem ncard_rootCharKernel_e8T3XColumn {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) {L : Type}
    [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    (rootCharKernel (fun i => ζ ^ (e8T3XColumn ε q i).val)).ncard = 72 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [CFSG.RankThree.PartOne.KLR.rootCharKernel_zetaPow_eq hζ,
    ncard_rootKernel_e8T3XColumn hp hp3 hε hq]

theorem ncard_rootCharKernel_e8T3ZColumn {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ZMod p} (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) {L : Type}
    [Field L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    (rootCharKernel (fun i => ζ ^ (e8T3ZColumn ε q i).val)).ncard = 30 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [CFSG.RankThree.PartOne.KLR.rootCharKernel_zetaPow_eq hζ,
    ncard_rootKernel_e8T3ZColumn hp hp3 hε hq]

variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}

private lemma rootDiagPoint_centralizes_conj (g0 : ModGL Tag.E8 L)
    {T : Subgroup (ModGL Tag.E8 L)} {A : Set (adjointGroup Tag.E8 K)}
    {c : adjointGroup Tag.E8 K}
    (hconj : ∀ a : adjointGroup Tag.E8 K, a ∈ A →
      c * a * c⁻¹ ∈ subtorusImage (adjEmb Tag.E8 K L) g0 T)
    (hcommT : ∀ u ∈ T, ∀ v ∈ T, u * v = v * u)
    {y₀ : adjointGroup Tag.E8 K} {d : ModGL Tag.E8 L} (hd : d ∈ T)
    (hy₀ : adjEmb Tag.E8 K L y₀ = g0 * d * g0⁻¹) :
    ∀ a : adjointGroup Tag.E8 K, a ∈ A → y₀ * (c * a * c⁻¹) = (c * a * c⁻¹) * y₀ := by
  intro a ha
  obtain ⟨d', hd', hxd'⟩ : ∃ d' ∈ T,
      adjEmb Tag.E8 K L (c * a * c⁻¹) = g0 * d' * g0⁻¹ := by
    have h := (mem_subtorusImage_iff (adjEmb Tag.E8 K L) g0 T (c * a * c⁻¹)).1 (hconj a ha)
    refine ⟨g0⁻¹ * adjEmb Tag.E8 K L (c * a * c⁻¹) * g0, h, ?_⟩
    show adjEmb Tag.E8 K L (c * a * c⁻¹) = g0 * (g0⁻¹ *
      adjEmb Tag.E8 K L (c * a * c⁻¹) * g0) * g0⁻¹
    group
  apply adjEmb_injective (K := K) (L := L)
  calc adjEmb Tag.E8 K L (y₀ * (c * a * c⁻¹))
      = adjEmb Tag.E8 K L y₀ * adjEmb Tag.E8 K L (c * a * c⁻¹) := map_mul _ _ _
    _ = (g0 * d * g0⁻¹) * (g0 * d' * g0⁻¹) := by rw [hy₀, hxd']
    _ = g0 * (d * d') * g0⁻¹ := by group
    _ = g0 * (d' * d) * g0⁻¹ := by rw [hcommT _ hd _ hd']
    _ = (g0 * d' * g0⁻¹) * (g0 * d * g0⁻¹) := by group
    _ = adjEmb Tag.E8 K L (c * a * c⁻¹) * adjEmb Tag.E8 K L y₀ := by rw [hy₀, hxd']
    _ = adjEmb Tag.E8 K L ((c * a * c⁻¹) * y₀) := (map_mul _ _ _).symm

private lemma rootCharKernel_zpow_eq {p : ℕ} [NeZero p] (hp : p.Prime)
    {b : Fin Tag.E8.rank → Lˣ} (hb : ∀ i, b i ^ p = 1) {m : ℤ} (hm : ¬ (p : ℤ) ∣ m) :
    rootCharKernel (fun i => b i ^ m) = rootCharKernel b := by
  ext α
  simp only [rootCharKernel, Set.mem_ofPred_eq]
  refine and_congr_right fun hα => ?_
  have hpow : rootChar (fun i => b i ^ m) α = (rootChar b α) ^ m := by
    rw [rootChar, rootChar, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_mul, ← zpow_mul, mul_comm]
  rw [hpow]
  constructor
  · intro h1
    have hdvdm : (orderOf (rootChar b α) : ℤ) ∣ m :=
      orderOf_dvd_iff_zpow_eq_one.mpr h1
    have hdvdp : orderOf (rootChar b α) ∣ p := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rw [rootChar, ← Finset.prod_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      have hbpz : b i ^ (p : ℤ) = 1 := by
        rw [zpow_natCast]
        exact hb i
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hbpz, one_zpow]
    have h1o : orderOf (rootChar b α) = 1 := by
      rcases (Nat.dvd_prime hp).1 hdvdp with h | h
      · exact h
      · exfalso
        exact hm (h ▸ hdvdm)
    exact orderOf_eq_one_iff.mp h1o
  · intro h1
    rw [h1, one_zpow]

private lemma exists_selection_points {p : ℕ} (hp : p.Prime)
    {A : Set (adjointGroup Tag.E8 K)}
    (hΩ : ∀ g : adjointGroup Tag.E8 K, g ∈ Subgroup.centralizer A → orderOf g = p → g ∈ A)
    {c x₀ z₀ : adjointGroup Tag.E8 K} (hx₀ord : orderOf x₀ = p)
    (hz₀ord : orderOf z₀ = p)
    (hcentX : ∀ a : adjointGroup Tag.E8 K, a ∈ A →
      x₀ * (c * a * c⁻¹) = (c * a * c⁻¹) * x₀)
    (hcentZ : ∀ a : adjointGroup Tag.E8 K, a ∈ A →
      z₀ * (c * a * c⁻¹) = (c * a * c⁻¹) * z₀) :
    ∃ x z : adjointGroup Tag.E8 K,
      x ∈ A ∧ z ∈ A ∧ orderOf x = p ∧ orderOf z = p ∧
      c * x * c⁻¹ = x₀ ∧ c * z * c⁻¹ = z₀ := by
  classical
  let x : adjointGroup Tag.E8 K := c⁻¹ * x₀ * c
  let z : adjointGroup Tag.E8 K := c⁻¹ * z₀ * c
  have hxcent : x ∈ Subgroup.centralizer A := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := hcentX a ha
    symm
    calc x * a = c⁻¹ * x₀ * c * a := by rw [show x = c⁻¹ * x₀ * c from rfl]
      _ = c⁻¹ * (x₀ * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * x₀) * c := by rw [h]
      _ = a * (c⁻¹ * x₀ * c) := by group
      _ = a * x := by rw [show x = c⁻¹ * x₀ * c from rfl]
  have hzcent : z ∈ Subgroup.centralizer A := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := hcentZ a ha
    symm
    calc z * a = c⁻¹ * z₀ * c * a := by rw [show z = c⁻¹ * z₀ * c from rfl]
      _ = c⁻¹ * (z₀ * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * z₀) * c := by rw [h]
      _ = a * (c⁻¹ * z₀ * c) := by group
      _ = a * z := by rw [show z = c⁻¹ * z₀ * c from rfl]
  have hxord : orderOf x = p := by
    have h := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
      (c⁻¹ * x₀ * c)
    rw [show x = c⁻¹ * x₀ * c from rfl, ← h]
    have h2 : (MulAut.conj c) (c⁻¹ * x₀ * c) = x₀ := by
      rw [MulAut.conj_apply]; group
    simp only [MulEquiv.coe_toMonoidHom]
    rw [h2, hx₀ord]
  have hzord : orderOf z = p := by
    have h := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
      (c⁻¹ * z₀ * c)
    rw [show z = c⁻¹ * z₀ * c from rfl, ← h]
    have h2 : (MulAut.conj c) (c⁻¹ * z₀ * c) = z₀ := by
      rw [MulAut.conj_apply]; group
    simp only [MulEquiv.coe_toMonoidHom]
    rw [h2, hz₀ord]
  refine ⟨x, z, hΩ x hxcent hxord, hΩ z hzcent hzord, hxord, hzord, ?_, ?_⟩
  · change c * (c⁻¹ * x₀ * c) * c⁻¹ = x₀
    group
  · change c * (c⁻¹ * z₀ * c) * c⁻¹ = z₀
    group

private lemma selection_points_not_zpowers {p : ℕ} [NeZero p] {q : ZMod p}
    (hp : p.Prime) (hp3 : 3 < p)
    (g0 : ModGL Tag.E8 L) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    {c x₀ z₀ x z : adjointGroup Tag.E8 K}
    (hx₀ : adjEmb Tag.E8 K L x₀ = g0 *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε q i).val) * g0⁻¹)
    (hz₀ : adjEmb Tag.E8 K L z₀ = g0 *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε q i).val) * g0⁻¹)
    (hx : c * x * c⁻¹ = x₀) (hz : c * z * c⁻¹ = z₀)
    (hx₀ord : orderOf x₀ = p) :
    z ∉ Subgroup.zpowers x := by
  intro hzmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzmem
  have hconjpow : c * x ^ m * c⁻¹ = (c * x * c⁻¹) ^ m := by
    simpa [MulAut.conj_apply] using
      (map_zpow (MulAut.conj c).toMonoidHom x m).symm
  have hz₀pow : z₀ = x₀ ^ m := by
    calc z₀ = c * z * c⁻¹ := by rw [← hz]
      _ = c * x ^ m * c⁻¹ := by rw [hm]
      _ = (c * x * c⁻¹) ^ m := hconjpow
      _ = x₀ ^ m := by rw [hx]
  have hm0 : ¬ (p : ℤ) ∣ m := by
    intro hdvd
    have h1 : x₀ ^ m = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by simpa [hx₀ord] using hdvd)
    have hz1 : z₀ = 1 := by rw [hz₀pow, h1]
    have h1o : orderOf z₀ = 1 := by rw [hz1, orderOf_one]
    have hz₀ord : orderOf z₀ = p := by
      rw [← orderOf_injective (adjEmb Tag.E8 K L) adjEmb_injective z₀, hz₀]
      have hcong : orderOf (g0 * rootDiagUnit Tag.E8
          (fun i => ζ ^ (e8T3ZColumn ε q i).val) * g0⁻¹) =
          orderOf (rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε q i).val)) := by
        have h := orderOf_injective (MulAut.conj g0).toMonoidHom (MulAut.conj g0).injective
          (rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε q i).val))
        simpa [MulAut.conj_apply] using h
      rw [hcong, orderOf_rootDiagUnit_e8T3ZColumn_zetaPow hζ hp]
    omega
  have hdZ : rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε q i).val) =
      (rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε q i).val)) ^ m := by
    have h1 : adjEmb Tag.E8 K L z₀ = adjEmb Tag.E8 K L (x₀ ^ m) := by rw [hz₀pow]
    have hpow : adjEmb Tag.E8 K L (x₀ ^ m) = (adjEmb Tag.E8 K L x₀) ^ m :=
      map_zpow (adjEmb Tag.E8 K L) x₀ m
    rw [hpow, hx₀, hz₀] at h1
    have h2 := congrArg (MulAut.conj g0⁻¹) h1
    simpa [MulAut.conj_apply, map_zpow] using h2
  have hbX : ∀ i, (ζ ^ (e8T3XColumn ε q i).val) ^ p = 1 := fun i => by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hbZ : (fun i => ζ ^ (e8T3ZColumn ε q i).val) =
      (fun i => (ζ ^ (e8T3XColumn ε q i).val) ^ m) := by
    apply rootDiagUnit_injective
    rw [hdZ]
    exact (map_zpow (rootDiagUnitHom Tag.E8 L)
      (fun i => ζ ^ (e8T3XColumn ε q i).val) m).symm
  have hker : rootCharKernel (fun i => ζ ^ (e8T3ZColumn ε q i).val) =
      rootCharKernel (fun i => ζ ^ (e8T3XColumn ε q i).val) := by
    rw [hbZ]
    exact rootCharKernel_zpow_eq hp hbX hm0
  have h72 := ncard_rootCharKernel_e8T3XColumn hp hp3 hε hq hζ
  have h30 := ncard_rootCharKernel_e8T3ZColumn hp hp3 hε hq hζ
  rw [hker] at h30
  omega

theorem exists_selection_pair (hE6 : E6Layer Tag.E8) (hε : ε = 1 ∨ ε = -1)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (hq2 : ε = -1 → 2 < ℓ ^ f)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    (hconj : ∀ Q : Subgroup (adjointGroup Tag.E8 K), IsPGroup p Q →
      ∃ c : adjointGroup Tag.E8 K, ∀ y ∈ Q,
        c * y * c⁻¹ ∈ subtorusImage (adjEmb Tag.E8 K L) g0
          (twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))))
    {A : Subgroup (adjointGroup Tag.E8 K)} (hAe : IsElemAbelian p A)
    (hΩ : ∀ g ∈ Subgroup.centralizer (A : Set (adjointGroup Tag.E8 K)),
      orderOf g = p → g ∈ A)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ (x z c x₀ z₀ : adjointGroup Tag.E8 K),
      x ∈ A ∧ z ∈ A ∧ orderOf x = p ∧ orderOf z = p ∧ z ∉ Subgroup.zpowers x ∧
      c * x * c⁻¹ = x₀ ∧ c * z * c⁻¹ = z₀ ∧
      adjEmb Tag.E8 K L x₀ = g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val) *
        g0⁻¹ ∧
      adjEmb Tag.E8 K L z₀ = g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε (Nat.card K : ZMod p) i).val) *
        g0⁻¹ := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set T : Subgroup (ModGL Tag.E8 L) :=
    twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) with hTdef
  set q : ZMod p := (Nat.card K : ZMod p) with hqdef
  have hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) p).2 hpf
    simpa [hqdef] using h
  obtain ⟨x₀, hx₀⟩ := exists_adjointGroup_e8T3XPoint hf hK hp hp3 hε hq2 hpf n hnm hnW
    g0 hg0C hg0 hperf hζ
  obtain ⟨z₀, hz₀⟩ := exists_adjointGroup_e8T3ZPoint hf hK hp hp3 hε hq2 hpf n hnm hnW
    g0 hg0C hg0 hperf hζ
  have hconjOrd : ∀ d : ModGL Tag.E8 L,
      orderOf (g0 * d * g0⁻¹) = orderOf d := fun d => by
    have h := orderOf_injective (MulAut.conj g0).toMonoidHom
      (MulAut.conj g0).injective d
    simpa [MulAut.conj_apply] using h
  have hx₀ord : orderOf x₀ = p := by
    rw [← orderOf_injective (adjEmb Tag.E8 K L) adjEmb_injective x₀, hx₀]
    rw [hconjOrd, orderOf_rootDiagUnit_e8T3XColumn_zetaPow hζ hp]
  have hz₀ord : orderOf z₀ = p := by
    rw [← orderOf_injective (adjEmb Tag.E8 K L) adjEmb_injective z₀, hz₀]
    rw [hconjOrd, orderOf_rootDiagUnit_e8T3ZColumn_zetaPow hζ hp]
  obtain ⟨c, hc⟩ := hconj A hAe.isPGroup
  have hmemX : rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε q i).val) ∈ T :=
    e8T3XColumn_mem_twistedTorus hζ (fun y => by rw [iterateFrobenius_def, hK]) hε hq
      (e8T3_twistedTorus n hnm hnW (iterateFrobenius L ℓ f))
  have hmemZ : rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε q i).val) ∈ T :=
    e8T3ZColumn_mem_twistedTorus hζ (fun y => by rw [iterateFrobenius_def, hK]) hε hq
      (e8T3_twistedTorus n hnm hnW (iterateFrobenius L ℓ f))
  have hcommT : ∀ u ∈ T, ∀ v ∈ T, u * v = v * u := by
    intro u hu v hv
    exact (CFSG.LieType.Chevalley.mul_comm_of_mem_diagonalGroup
      (torusGroup_le_diagonalGroup (mem_twistedTorusOf.1 hu).1)
      (torusGroup_le_diagonalGroup (mem_twistedTorusOf.1 hv).1))
  have hcentX : ∀ a : adjointGroup Tag.E8 K, a ∈ (A : Set (adjointGroup Tag.E8 K)) →
      x₀ * (c * a * c⁻¹) = (c * a * c⁻¹) * x₀ :=
    rootDiagPoint_centralizes_conj g0 hc hcommT hmemX hx₀
  have hcentZ : ∀ a : adjointGroup Tag.E8 K, a ∈ (A : Set (adjointGroup Tag.E8 K)) →
      z₀ * (c * a * c⁻¹) = (c * a * c⁻¹) * z₀ :=
    rootDiagPoint_centralizes_conj g0 hc hcommT hmemZ hz₀
  obtain ⟨x, z, hxA, hzA, hxord, hzord, hx, hz⟩ :=
    exists_selection_points hp hΩ hx₀ord hz₀ord hcentX hcentZ
  have hzx : z ∉ Subgroup.zpowers x :=
    selection_points_not_zpowers hp hp3 g0 hε hq hζ hx₀ hz₀ hx hz hx₀ord
  exact ⟨x, z, c, x₀, z₀, hxA, hzA, hxord, hzord, hzx, hx, hz, hx₀, hz₀⟩

theorem exists_rank_three_qTorus_centralizer_normalizer (hE6 : E6Layer Tag.E8)
    (hε : ε = 1 ∨ ε = -1) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    {x : adjointGroup Tag.E8 K} (hx : orderOf x = p) (c : adjointGroup Tag.E8 K)
    (hxframe : adjEmb Tag.E8 K L (c * x * c⁻¹) = g0 *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val) *
      g0⁻¹)
    {J : Subgroup (adjointGroup Tag.E8 K)}
    (hJx : J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))
    (hJn : (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))).Normal)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) (hqK : q ∣ Nat.card K - 1) :
    ∃ F : Subgroup (adjointGroup Tag.E8 K),
      F ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)) ∧
      F ≤ Subgroup.normalizer (J : Set (adjointGroup Tag.E8 K)) ∧
      IsElemAbelian q F ∧ 3 ≤ CFSG.Open.pRank q F := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set r : ZMod p := (Nat.card K : ZMod p) with hrdef
  have hr : r ^ 2 + (ε : ZMod p) * r + 1 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) p).2 hpf
    simpa [hrdef] using h
  have hS : ∃ u : WeylGroup Tag.E8, (fun γ => u • γ) '' rootCharKernel
      (fun i => ζ ^ (e8T3XColumn ε r i).val) = parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
    obtain ⟨u, hu⟩ := exists_conj_rootKernel_e8T3XColumn_eq_e6Nodes hp hp3 hε hpf
    exact ⟨u, by rwa [CFSG.RankThree.PartOne.KLR.rootCharKernel_zetaPow_eq hζ]⟩
  have hh : g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hxframe]
    have h : g0⁻¹ * (g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε r i).val) * g0⁻¹) * g0 =
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε r i).val) := by group
    rw [h]
    exact e8T3XColumn_mem_twistedTorus hζ (fun y => by rw [iterateFrobenius_def, hK]) hε hr
      (e8T3_twistedTorus n hnm hnW (iterateFrobenius L ℓ f))
  have hb : rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε r i).val) =
      g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 := by
    rw [hxframe]
    group
  obtain ⟨F, hFx, hFel, hF3⟩ := exists_rank_three_qTorus_centralizer hE6 hε K hf hK hp hp3
    hpf L n hnm hnW g0 hg0C hg0 hperf
    (e8T3_twistedTorus n hnm hnW (iterateFrobenius L ℓ f)) hx c hh
    (fun i => ζ ^ (e8T3XColumn ε r i).val) hb hS hq hq2 hqp hqK
  refine ⟨F, hFx, ?_, hFel, hF3⟩
  exact hFx.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJx).mp hJn)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
