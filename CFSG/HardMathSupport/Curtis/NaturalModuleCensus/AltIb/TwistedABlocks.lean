module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PairedBlock
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagUnitary
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.DualPoly

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open scoped commutatorElement

section Abstract

private theorem not_sixteen_dvd_card_alt' {p : ℕ} (hp : p = 5 ∨ p = 7) :
    ¬ 16 ∣ Nat.card (alternatingGroup (Fin p)) := by
  rcases hp with rfl | rfl
  · rw [CFSG.AGLEmbedding.LieOut.nat_card_alt_five]; norm_num
  · rw [CFSG.AGLEmbedding.LieOut.nat_card_alt_seven]; norm_num

private theorem iSupIndep_comap {Γ A : Type*} [Group Γ] [Group A] {ι : Type*} (Ψ : Γ →* A)
    (hΨ : Function.Injective Ψ) {D : ι → Subgroup A} (h : iSupIndep D) :
    iSupIndep (fun i => (D i).comap Ψ) := by
  intro i
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  have h1 : Ψ x ∈ D i := hx
  have h2 : Ψ x ∈ ⨆ (j) (_ : j ≠ i), D j := by
    have : (⨆ (j) (_ : j ≠ i), (D j).comap Ψ) ≤ (⨆ (j) (_ : j ≠ i), D j).comap Ψ :=
      iSup₂_le fun j hj => Subgroup.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => D j) j hj)
    exact this hx'
  have := Subgroup.disjoint_def.1 (h i) h1 h2
  exact hΨ (by rw [this, map_one])

theorem mem_iSup_comap_of_pow {Γ A : Type*} [Group Γ] [Group A] {ι : Type*} [Fintype ι]
    (Ψ : Γ →* A) (hΨ : Function.Injective Ψ) (D : ι → Subgroup A)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ D i, ∀ b ∈ D j, Commute a b) (hind : iSupIndep D) {p : ℕ}
    (hrange : ∀ i, ∀ d ∈ D i, d ^ p = 1 → d ∈ Ψ.range) {g : Γ} (hg : Ψ g ∈ ⨆ i, D i)
    (hgp : g ^ p = 1) : g ∈ ⨆ i, (D i).comap Ψ := by
  classical
  let ψ : (∀ i, D i) →* A := Subgroup.noncommPiCoprod (H := D)
    (fun i j hij x y hx hy => hcomm i j hij x hx y hy)
  have hψ : Function.Injective ψ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hψr : ψ.range = ⨆ i, D i := Subgroup.noncommPiCoprod_range
  obtain ⟨u, hu⟩ : Ψ g ∈ ψ.range := hψr ▸ hg
  have hup : u ^ p = 1 := hψ (by rw [map_pow, hu, ← map_pow, hgp, map_one, map_one])
  have hui : ∀ i, (u i : A) ^ p = 1 := fun i => congrArg Subtype.val (congrFun hup i)
  choose s hs using fun i => hrange i (u i) (u i).2 (hui i)
  have hsmem : ∀ i, s i ∈ (D i).comap Ψ := fun i => by
    rw [Subgroup.mem_comap, hs i]
    exact (u i).2
  have hscomm : ∀ i j, i ≠ j → Commute (s i) (s j) := fun i j hij => hΨ (by
    simp only [map_mul, hs]
    exact (hcomm i j hij _ (u i).2 _ (u j).2).eq)
  have hcs : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Commute s) :=
    fun i _ j _ h => hscomm i j h
  have hg' : g = Finset.univ.noncommProd s hcs := by
    apply hΨ
    rw [Finset.map_noncommProd]
    have : ψ u = Finset.univ.noncommProd (fun i => (u i : A))
        (fun i _ j _ h => hcomm i j h _ (u i).2 _ (u j).2) := Subgroup.noncommPiCoprod_apply _ u
    rw [← hu, this]
    exact (Finset.noncommProd_congr rfl (fun i _ => hs i) _).symm
  rw [hg']
  exact Subgroup.noncommProd_mem _ _ fun i _ =>
    (le_iSup (fun i => (D i).comap Ψ) i) (hsmem i)

private theorem noAp_of_sixteen_dvd {R : Type} [Group R] [Finite R] {p : ℕ} (hp : p = 5 ∨ p = 7)
    (h16 : 16 ∣ Nat.card R) (hZ : ∀ z ∈ Subgroup.center R, z ^ 2 = 1 → z = 1) :
    CFSG.AGLEmbedding.LieOut.NoAp p (R ⧸ Subgroup.center R) := by
  have hodd : ¬ 2 ∣ Nat.card (Subgroup.center R) := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R) 2 h2
    have hz2 : (z : R) ^ 2 = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this
    have : z = 1 := Subtype.ext (hZ z z.2 hz2)
    rw [this, orderOf_one] at hz
    omega
  have hcop : Nat.Coprime 16 (Nat.card (Subgroup.center R)) :=
    Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center R)
  have : 16 ∣ Nat.card (R ⧸ Subgroup.center R) :=
    hcop.dvd_of_dvd_mul_right (hcard ▸ h16)
  exact CFSG.AGLEmbedding.LieOut.NoAp.of_dvd (not_sixteen_dvd_card_alt' hp) this

private theorem noAp_seven_of_card_eq_of_center {R : Type} [Group R] [Finite R] (hc : Nat.card R = 504)
    (hZ : ∀ z ∈ Subgroup.center R, z = 1) :
    CFSG.AGLEmbedding.LieOut.NoAp 7 (R ⧸ Subgroup.center R) := by
  have hbot : Subgroup.center R = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hZ
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center R)
  have h1 : Nat.card (Subgroup.center R) = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [h1, mul_one] at hcard
  exact CFSG.AGLEmbedding.LieOut.noAp_seven_of_card_eq (hcard ▸ hc)

private noncomputable def comapEquivOfLeRange {Γ A : Type*} [Group Γ] [Group A] (Ψ : Γ →* A)
    (hΨ : Function.Injective Ψ) (S : Subgroup A) (h : S ≤ Ψ.range) : S.comap Ψ ≃* S :=
  MulEquiv.ofBijective (Ψ.subgroupComap S)
    ⟨fun a b hab => Subtype.ext (hΨ (congrArg Subtype.val hab)), fun g => by
      obtain ⟨s, hs⟩ := h g.2
      exact ⟨⟨s, by rw [Subgroup.mem_comap, hs]; exact g.2⟩, Subtype.ext hs⟩⟩

private noncomputable def centerQuotEquivOfMulEquiv' {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) :
    P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q :=
  QuotientGroup.congr _ _ e (by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      show e z * e x = e x * e z
      rw [← map_mul, ← map_mul, hx z]
    · intro hq
      refine ⟨e.symm q, ?_, by simp⟩
      rw [Subgroup.mem_center_iff] at hq
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro y
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hq (e y)])

end Abstract

section Arithmetic

open Polynomial

private theorem sixteen_dvd_card_adjoinRoot {K : Type} [Field K] [Finite K] {f p : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hp57 : p = 5 ∨ p = 7) {a : K[X]}
    (ha : Irreducible a) (hmon : a.Monic) (hdvd : a ∣ X ^ p - 1) (hne : a ≠ X - C 1) :
    16 ∣ Nat.card (AdjoinRoot a) := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Irreducible a) := ⟨ha⟩
  have : Module.Finite K (AdjoinRoot a) := (AdjoinRoot.powerBasis ha.ne_zero).finite
  have : Finite (AdjoinRoot a) := Module.finite_of_finite K
  have hrank : Module.finrank K (AdjoinRoot a) = a.natDegree := by
    rw [(AdjoinRoot.powerBasis ha.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  have hcard : Nat.card (AdjoinRoot a) = (2 ^ f) ^ (2 * a.natDegree) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hK, hrank, pow_mul]
  have hd1 : 1 ≤ a.natDegree := ha.natDegree_pos
  have hζp : (AdjoinRoot.root a) ^ p = 1 := by
    have h0 : AdjoinRoot.mk a (X ^ p - 1) = 0 := AdjoinRoot.mk_eq_zero.2 hdvd
    simpa [sub_eq_zero] using h0
  have hζ1 : AdjoinRoot.root a ≠ 1 := by
    intro h1
    have h0 : AdjoinRoot.mk a (X - C 1) = 0 := by simp [h1]
    have hdv : a ∣ X - C 1 := AdjoinRoot.mk_eq_zero.1 h0
    exact hne (eq_of_monic_of_dvd_of_natDegree_le hmon (monic_X_sub_C 1) hdv
      (by rw [natDegree_X_sub_C]; exact hd1)).symm
  have hζ0 : AdjoinRoot.root a ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  let ζ : (AdjoinRoot a)ˣ := Units.mk0 _ hζ0
  have hζ'p : ζ ^ p = 1 := Units.ext (by simpa [ζ] using hζp)
  have hζ'1 : ζ ≠ 1 := fun h => hζ1 (by simpa [ζ] using congrArg Units.val h)
  have hord : orderOf ζ = p := orderOf_eq_prime hζ'p hζ'1
  have hpdvd : p ∣ Nat.card (AdjoinRoot a) - 1 := by
    have := orderOf_dvd_natCard ζ
    rwa [hord, Nat.card_units] at this
  by_cases hk : f * a.natDegree = 1
  · exfalso
    have hf1 : f = 1 := Nat.eq_one_of_mul_eq_one_right hk
    have hd : a.natDegree = 1 := Nat.eq_one_of_mul_eq_one_left hk
    rw [hcard, hf1, hd] at hpdvd
    norm_num at hpdvd
    have := Nat.le_of_dvd (by norm_num) hpdvd
    rcases hp57 with rfl | rfl <;> omega
  · have h4 : 4 ≤ f * (2 * a.natDegree) := by
      have : 2 ≤ f * a.natDegree := by
        have := Nat.mul_pos (by omega : 0 < f) (by omega : 0 < a.natDegree)
        omega
      nlinarith
    rw [hcard, ← pow_mul]
    exact (pow_dvd_pow 2 h4 : 2 ^ 4 ∣ _)

end Arithmetic

section Center

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.AGLEmbedding.LieOut

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

private theorem finite_gl {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Finite (LinearMap.GeneralLinearGroup K V) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V →ₗ[K] V) := DFunLike.finite _
  exact instFiniteUnits

private theorem eq_one_of_mul_self_eq_one_char_two {E : Type*} [Field E] [CharP E 2] {c : E}
    (h : c * c = 1) : c = 1 := by
  have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have : (c - 1) ^ 2 = 0 := by
    calc (c - 1) ^ 2 = c * c - 2 * c + 1 := by ring
      _ = 1 - 0 * c + 1 := by rw [h, h2]
      _ = 2 := by ring
      _ = 0 := h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

private theorem charP_adjoinRoot {K : Type*} [Field K] [CharP K 2] {a : K[X]} (ha : Irreducible a) :
    CharP (AdjoinRoot a) 2 := by
  have : Fact (Irreducible a) := ⟨ha⟩
  exact charP_of_injective_algebraMap (algebraMap K (AdjoinRoot a)).injective 2

private theorem exists_scalar_of_mem_center_specialBlock (H : UnitaryPrimaryData hK.bar B x)
    (hq : 2 ≤ 2 ^ f) (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a)
    {z : LinearMap.GeneralLinearGroup K V} (hz : z ∈ specialBlock B x (a : K[X]))
    (hzc : ∀ g ∈ specialBlock B x (a : K[X]), Commute z g) :
    ∃ c : AdjoinRoot (a : K[X]),
      (∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
        (z : Module.End K V) (v : V) =
          ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V)) ∧
      c ^ primaryMultiplicity (x : Module.End K V) (a : K[X]) = 1 := by
  obtain ⟨c, hc⟩ := (specialBlockFacts_of_good H hq a ha).scalar z
    (specialBlock_le_unitaryCentralizer hz) (fun _ g hg => hzc g hg)
  refine ⟨c, hc, ?_⟩
  obtain ⟨-, hgc, hdet⟩ := mem_specialBlock.mp hz
  have hres : ((blockRestrict x (a : K[X]) ⟨z, hgc⟩ : blockGL (x : Module.End K V) (a : K[X])) :
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) =
        c • LinearMap.id := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    have := blockApply_blockRestrict x (a : K[X]) ⟨z, hgc⟩ (w : V) w.2
    exact this.trans (hc w)
  have h1 : LinearMap.det ((blockRestrict x (a : K[X]) ⟨z, hgc⟩ : blockGL (x : Module.End K V)
      (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))) = 1 := by
    have := congrArg Units.val hdet
    simpa [blockDetHom, blockGLDet] using this
  rw [hres, LinearMap.det_smul, LinearMap.det_id, mul_one] at h1
  exact h1

private theorem eq_one_of_scalar_one (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) {z : LinearMap.GeneralLinearGroup K V}
    (hz : z ∈ specialBlock B x (a : K[X]))
    (h1 : ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
      (z : Module.End K V) (v : V) = (v : V)) : z = 1 :=
  eq_one_of_paired H a.2 (specialBlock_le_orbitFactor hz) fun v hv => h1 ⟨v, hv⟩

private theorem eq_one_of_mem_center_specialBlock_sq (H : UnitaryPrimaryData hK.bar B x)
    (hq : 2 ≤ 2 ^ f) (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a)
    {z : LinearMap.GeneralLinearGroup K V} (hz : z ∈ specialBlock B x (a : K[X]))
    (hzc : ∀ g ∈ specialBlock B x (a : K[X]), Commute z g) (hz2 : z ^ 2 = 1) : z = 1 := by
  obtain ⟨c, hc, -⟩ := exists_scalar_of_mem_center_specialBlock H hq a ha hz hzc
  have hzx : Commute (z : Module.End K V) (x : Module.End K V) :=
    (mem_unitaryCentralizer.mp (specialBlock_le_unitaryCentralizer hz)).2
  have hirr : Irreducible (a : K[X]) := irreducible_of_mem_primaryFactors a.2
  have : CharP K 2 := hK.charP
  have : CharP (AdjoinRoot (a : K[X])) 2 := charP_adjoinRoot hirr
  obtain ⟨v, hv⟩ : ∃ v : primaryComponent (x : Module.End K V) (a : K[X]), v ≠ 0 := by
    obtain ⟨w, hw, hw0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot H.squarefree a.2)
    exact ⟨⟨w, hw⟩, fun h => hw0 (congrArg Subtype.val h)⟩
  have hcc : c * c = 1 := by
    have h2 : (z : Module.End K V) ((z : Module.End K V) (v : V)) = (v : V) := by
      have := congrArg (fun T : LinearMap.GeneralLinearGroup K V => (T : Module.End K V) (v : V))
        hz2
      simpa [pow_two] using this
    have h3 := apply_smul_primaryComponent hzx c v
    rw [hc v, h3] at h2
    have h4 : ((c • (⟨(z : Module.End K V) (v : V), apply_mem_primaryComponent hzx v.2⟩ :
        primaryComponent (x : Module.End K V) (a : K[X])) : primaryComponent
          (x : Module.End K V) (a : K[X])) : V) = (v : V) := h2
    have h5 : (⟨(z : Module.End K V) (v : V), apply_mem_primaryComponent hzx v.2⟩ :
        primaryComponent (x : Module.End K V) (a : K[X])) = c • v := Subtype.ext (hc v)
    rw [h5, smul_smul] at h4
    have h6 : (c * c) • v = v := Subtype.ext h4
    by_contra hne
    have : (c * c - 1) • v = 0 := by rw [sub_smul, h6, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact hne (sub_eq_zero.1 h)
    · exact hv h
  have hc1 : c = 1 := eq_one_of_mul_self_eq_one_char_two hcc
  exact eq_one_of_scalar_one H a hz fun w => by rw [hc w, hc1, one_smul]

theorem exists_specialBlock_selfDual_equiv (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a) :
    ∃ (hE : UnitaryFieldData 2 (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X])))
      (Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
        primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
          AdjoinRoot (a : K[X])),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧
        Nonempty (specialBlock B x (a : K[X]) ≃* sesqSpecialUnitaryGroup Hf) := by
  obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, -⟩ :=
    exists_selfDualFactor hself (selfDualPrimaryBlock H a hself)
  let D : sesqUnitaryGroup Hf →* (AdjoinRoot (a : K[X]))ˣ :=
    (blockGLDet (x : Module.End K V) (a : K[X])).comp (sesqUnitaryGroup Hf).subtype
  have hcompat : ∀ s : orbitFactor B x (a : K[X]),
      ((φ s : sesqUnitaryGroup Hf) : blockGL (x : Module.End K V) (a : K[X])) =
        blockRestrict x (a : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩ :=
    fun s => blockGL_ext fun v hv => hφ s v hv
  have hspec : specialBlock B x (a : K[X]) = kerImage (orbitFactor B x (a : K[X])) φ D := by
    ext g
    rw [mem_specialBlock, mem_kerImage]
    constructor
    · rintro ⟨hs, hg, h⟩
      refine ⟨hs, ?_⟩
      change blockGLDet (x : Module.End K V) (a : K[X]) ((φ ⟨g, hs⟩ : sesqUnitaryGroup Hf) :
        blockGL (x : Module.End K V) (a : K[X])) = 1
      rw [hcompat ⟨g, hs⟩]
      exact h
    · rintro ⟨hs, h⟩
      refine ⟨hs, orbitFactor_le_gl_centralizer hs, ?_⟩
      change blockGLDet (x : Module.End K V) (a : K[X]) ((φ ⟨g, hs⟩ : sesqUnitaryGroup Hf) :
        blockGL (x : Module.End K V) (a : K[X])) = 1 at h
      rw [hcompat ⟨g, hs⟩] at h
      exact h
  have hker : D.ker = (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    constructor
    · intro h
      refine ⟨δ.2, ?_⟩
      have := congrArg Units.val h
      simpa [D, blockGLDet] using this
    · rintro ⟨-, h⟩
      apply Units.ext
      simpa [D, blockGLDet] using h
  obtain ⟨e⟩ := nonempty_kerImage_mulEquiv (orbitFactor B x (a : K[X])) φ D
  exact ⟨hE, Hf, hHf, hHfl, ⟨(MulEquiv.subgroupCongr hspec).trans (e.trans
    ((MulEquiv.subgroupCongr hker).trans
      (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf))))⟩⟩

omit [FiniteDimensional K V] in
private theorem selfDual_numerics {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) (h2 : m = 2 → 4 ≤ 2 ^ k)
    (h3 : m = 3 → 3 ≤ 2 ^ k) :
    4 ≤ k * (m * (m - 1) / 2) ∨ (m = 2 ∧ k = 2) ∨ (m = 2 ∧ k = 3) := by
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · interval_cases m
    · have := h2 rfl
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have : k = 1 := by omega
        subst this
        norm_num at this
      by_cases hk3 : k ≤ 3
      · right
        interval_cases k
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · left
        norm_num
        omega
    · have := h3 rfl
      have hk2 : 2 ≤ k := by
        by_contra hlt
        have : k = 1 := by omega
        subst this
        norm_num at this
      left
      norm_num
      omega
  · left
    have : 6 ≤ m * (m - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul hm4 (by omega)
      omega
    nlinarith

private theorem center_specialBlock_noInvolution (H : UnitaryPrimaryData hK.bar B x) (hq : 2 ≤ 2 ^ f)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a) :
    ∀ z ∈ Subgroup.center ↥(specialBlock B x (a : K[X])), z ^ 2 = 1 → z = 1 := by
  intro z hz hz2
  refine Subtype.ext (eq_one_of_mem_center_specialBlock_sq H hq a ha z.2 (fun g hg => ?_) ?_)
  · exact (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨g, hg⟩)).symm
  · exact congrArg Subtype.val hz2

private theorem noAp_specialBlock_selfDual (H : UnitaryPrimaryData hK.bar B x) (hq : 2 ≤ 2 ^ f)
    {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hpq : ¬ p ∣ 2 ^ f + 1)
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a)
    (ha : IsGoodBlock hK x a) (hpd : p ∣ Nat.card (specialBlock B x (a : K[X]))) :
    NoAp p (↥(specialBlock B x (a : K[X])) ⧸ Subgroup.center ↥(specialBlock B x (a : K[X]))) := by
  have : Finite K := hK.finite
  have : Finite (LinearMap.GeneralLinearGroup K V) := finite_gl
  have hS := selfDualPrimaryBlock H a hself
  obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ := exists_specialBlock_selfDual_equiv H a hself
  set m := primaryMultiplicity (x : Module.End K V) (a : K[X]) with hmdef
  set d := (a : K[X]).natDegree with hd
  have hm2 : 2 ≤ m := ha.1
  have hd1 : 1 ≤ d := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have hnum := isGoodBlock_numeric (hK := hK) hq hself ha
  obtain ⟨-, hcardSU, -, -, -, -, hpart⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
    (n := m) rfl (one_le_primaryMultiplicity H a)
  have hcard : Nat.card (specialBlock B x (a : K[X])) =
      Nat.card (sesqSpecialUnitaryGroup Hf) := Nat.card_congr e.toEquiv
  generalize Nat.card (sesqSpecialUnitaryGroup Hf) = N at hcardSU hpart hcard
  have hZ1 := center_specialBlock_noInvolution H hq a ha
  have hf1 : 1 ≤ f := hK.one_le
  have hk1 : 1 ≤ f * d := Nat.mul_pos hf1 hd1
  have hdvdQ : (2 ^ (f * d)) ^ (m * (m - 1) / 2) ∣ N := by
    rw [← hpart]
    exact Nat.ordProj_dvd _ _
  rcases selfDual_numerics hm2 hk1 hnum.1 hnum.2 with h4 | ⟨hm, hk⟩ | ⟨hm, hk⟩
  ·
    have h16 : 16 ∣ Nat.card (specialBlock B x (a : K[X])) := by
      rw [hcard]
      refine Dvd.dvd.trans ?_ hdvdQ
      rw [← pow_mul]
      exact (pow_dvd_pow 2 h4 : 2 ^ 4 ∣ _)
    exact noAp_of_sixteen_dvd hp57 h16 hZ1
  ·
    exfalso
    rw [hm, hk] at hcardSU
    have e60 : ((2 ^ 2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 2, (((2 ^ 2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 60 := by decide +kernel
    have hc60 : Nat.card (specialBlock B x (a : K[X])) = 60 := by
      rw [hcard]
      exact_mod_cast hcardSU.trans e60
    rw [hc60] at hpd
    have hp5 : p = 5 := by
      rcases hp57 with h | h
      · exact h
      · rw [h] at hpd
        omega
    have hodd : Odd d := hS.odd_natDegree
    obtain ⟨r, hr⟩ := hodd
    have hfd : f * d = 2 := hk
    have hd2 : d ≤ 2 := by nlinarith
    have hd1' : d = 1 := by omega
    rw [hd1'] at hfd
    have hf2 : f = 2 := by omega
    exact hpq (by rw [hp5, hf2]; norm_num)
  ·
    rw [hm, hk] at hcardSU
    have e504 : ((2 ^ 3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 2, (((2 ^ 3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 504 := by decide +kernel
    have hc504 : Nat.card (specialBlock B x (a : K[X])) = 504 := by
      rw [hcard]
      exact_mod_cast hcardSU.trans e504
    rw [hc504] at hpd
    have hp7 : p = 7 := by
      rcases hp57 with h | h
      · rw [h] at hpd
        omega
      · exact h
    subst hp7
    refine noAp_seven_of_card_eq_of_center hc504 fun z hz => ?_
    refine Subtype.ext (eq_one_of_scalar_one H a z.2 ?_)
    obtain ⟨c, hc, hcm⟩ := exists_scalar_of_mem_center_specialBlock H hq a ha z.2 fun g hg =>
      (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨g, hg⟩)).symm
    have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
    have : CharP K 2 := hK.charP
    have : CharP (AdjoinRoot (a : K[X])) 2 := charP_adjoinRoot (irreducible_of_mem_primaryFactors a.2)
    have hcm2 : c ^ 2 = 1 := by
      rw [← hm]
      exact hcm
    have hc1 : c = 1 := eq_one_of_mul_self_eq_one_char_two (by rw [← pow_two]; exact hcm2)
    intro v
    rw [hc v, hc1, one_smul]

private theorem noAp_specialBlock_paired (H : UnitaryPrimaryData hK.bar B x) (hq : 2 ≤ 2 ^ f)
    {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hxp : x ^ p = 1)
    (a : primaryFactors (x : Module.End K V)) (hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X]))
    (ha : IsGoodBlock hK x a) :
    NoAp p (↥(specialBlock B x (a : K[X])) ⧸ Subgroup.center ↥(specialBlock B x (a : K[X]))) := by
  have : Finite K := hK.finite
  have : Finite (LinearMap.GeneralLinearGroup K V) := finite_gl
  have hirr : Irreducible (a : K[X]) := irreducible_of_mem_primaryFactors a.2
  have hmon : (a : K[X]).Monic := monic_of_mem_primaryFactors a.2
  have hdvd : (a : K[X]) ∣ X ^ p - 1 := by
    have h1 : (a : K[X]) ∣ minpoly K (x : Module.End K V) := (mem_primaryFactors.1 a.2).2.2
    refine h1.trans (minpoly.dvd K _ ?_)
    have : ((x : LinearMap.GeneralLinearGroup K V) : Module.End K V) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hxp]
      rfl
    simp [this]
  have hneX : (a : K[X]) ≠ X - C 1 := fun h => hne (by rw [h, dualPoly_X_sub_C_one])
  have hKc : Nat.card K = (2 ^ f) ^ 2 := by rw [hK.card, ← pow_mul, mul_comm]
  have h16E : 16 ∣ Nat.card (AdjoinRoot (a : K[X])) :=
    sixteen_dvd_card_adjoinRoot hKc hK.one_le hp57 hirr hmon hdvd hneX
  have hP := pairedPrimaryBlock H a hne
  obtain ⟨φ, ψ, -, -, -, -⟩ := hP.factor
  set m := primaryMultiplicity (x : Module.End K V) (a : K[X]) with hmdef
  have hm2 : 2 ≤ m := ha.1
  have : Finite (AdjoinRoot (a : K[X])) := by
    have : Fact (Irreducible (a : K[X])) := ⟨hirr⟩
    have : Module.Finite K (AdjoinRoot (a : K[X])) :=
      (AdjoinRoot.powerBasis hirr.ne_zero).finite
    exact Module.finite_of_finite K
  have : Fintype (AdjoinRoot (a : K[X])) := Fintype.ofFinite _
  have hF : Nat.card (orbitFactor B x (a : K[X])) =
      ∏ i : Fin m, (Nat.card (AdjoinRoot (a : K[X])) ^ m -
        Nat.card (AdjoinRoot (a : K[X])) ^ (i : ℕ)) := by
    have e : Nat.card (orbitFactor B x (a : K[X])) =
        Nat.card (Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot (a : K[X]))) :=
      Nat.card_congr ψ.toEquiv
    rw [e, Matrix.card_GL_field, Nat.card_eq_fintype_card]
  have hF16 : 16 ∣ Nat.card (orbitFactor B x (a : K[X])) := by
    rw [hF]
    refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨1, by omega⟩ : Fin m)))
    refine h16E.trans (Nat.dvd_sub ?_ ?_)
    · exact dvd_pow_self _ (by omega)
    · simp
  let Dm : orbitFactor B x (a : K[X]) →* (AdjoinRoot (a : K[X]))ˣ :=
    (blockDetHom x (a : K[X])).comp (Subgroup.inclusion orbitFactor_le_gl_centralizer)
  have hker : Dm.ker = (specialBlock B x (a : K[X])).subgroupOf (orbitFactor B x (a : K[X])) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_specialBlock]
    constructor
    · intro h
      exact ⟨g.2, orbitFactor_le_gl_centralizer g.2, h⟩
    · rintro ⟨-, hg, h⟩
      exact h
  have hcardF := Subgroup.card_ker_mul_card_range Dm
  have hSB : Nat.card (specialBlock B x (a : K[X])) = Nat.card Dm.ker := by
    rw [hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe specialBlock_le_orbitFactor).toEquiv).symm
  have hrange : Nat.card Dm.range ∣ Nat.card (AdjoinRoot (a : K[X])) - 1 := by
    rw [← Nat.card_units]
    exact Subgroup.card_subgroup_dvd_card _
  have hcop : Nat.Coprime 16 (Nat.card Dm.range) := by
    have hodd : ¬ 2 ∣ Nat.card (AdjoinRoot (a : K[X])) - 1 := by
      have hpos : 0 < Nat.card (AdjoinRoot (a : K[X])) := Nat.card_pos
      omega
    exact Nat.Coprime.coprime_dvd_right hrange
      (Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd))
  have h16 : 16 ∣ Nat.card (specialBlock B x (a : K[X])) := by
    rw [hSB]
    exact hcop.dvd_of_dvd_mul_right (hcardF ▸ hF16)
  exact noAp_of_sixteen_dvd hp57 h16 (center_specialBlock_noInvolution H hq a ha)

theorem noAp_specialBlock (H : UnitaryPrimaryData hK.bar B x) (hq : 2 ≤ 2 ^ f)
    {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hpq : ¬ p ∣ 2 ^ f + 1) (hxp : x ^ p = 1)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a)
    (hpd : p ∣ Nat.card (specialBlock B x (a : K[X]))) :
    NoAp p (↥(specialBlock B x (a : K[X])) ⧸ Subgroup.center ↥(specialBlock B x (a : K[X]))) := by
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · exact noAp_specialBlock_selfDual H hq hp57 hpq a hself ha hpd
  · exact noAp_specialBlock_paired H hq hp57 hxp a (Ne.symm hself) ha

theorem orbitFactor_trichotomy (H : UnitaryPrimaryData hK.bar B x) (hq : 2 ≤ 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (a : primaryFactors (x : Module.End K V)) :
    ⁅orbitFactor B x (a : K[X]), orbitFactor B x (a : K[X])⁆ = ⊥ ∨
    (IsGoodBlock hK x a ∧ ⁅orbitFactor B x (a : K[X]), orbitFactor B x (a : K[X])⁆ =
      specialBlock B x (a : K[X])) ∨
    ¬ p ∣ Nat.card (orbitFactor B x (a : K[X])) := by
  by_cases hgood : IsGoodBlock hK x a
  · exact Or.inr (Or.inl ⟨hgood, (specialBlockFacts_of_good H hq a hgood).commutator_eq hgood.1⟩)
  · by_cases hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])
    · right; right
      have hself : dualPoly hK.bar (a : K[X]) = a := by
        by_contra hne
        exact hgood ⟨hm, fun h => absurd h hne⟩
      have hbad : (primaryMultiplicity (x : Module.End K V) (a : K[X]),
          2 ^ (f * (a : K[X]).natDegree)) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
        by_contra hnot
        exact hgood ⟨hm, fun _ => hnot⟩
      exact not_dvd_card_orbitFactor_exceptional H hp hp3 a hself hbad
    · left
      have hfacts : SpecialBlockFacts B x a := by
        by_cases hself : dualPoly hK.bar (a : K[X]) = a
        · exact specialBlockFacts_of_selfDual hq a hself (selfDualPrimaryBlock H a hself)
            (fun h => absurd h hm)
        · exact specialBlockFacts_of_paired hq a (pairedPrimaryBlock H a (Ne.symm hself))
      refine le_antisymm (Subgroup.commutator_le.mpr fun g hg g' hg' => ?_) bot_le
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      exact hfacts.abelian (by omega) g hg g' hg'

end Center

section Su

open Polynomial Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.AGLEmbedding.LieOut
  CFSG.AGLEmbedding.UnitaryLevi CFSG.LinearGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

omit [Finite K] [CharP K 2] in
theorem exists_blocks_su (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (t : StatedSU n (2 ^ f) K)
    (hsq : Squarefree (minpoly K (mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    {p : ℕ} (hp57 : p = 5 ∨ p = 7) (hpq : ¬ p ∣ 2 ^ f + 1) (htp : t ^ p = 1) :
    ∃ (ι : Type) (_ : Finite ι) (D : ι → Subgroup (StatedSU n (2 ^ f) K)),
      (∀ i j, i ≠ j → ∀ a ∈ D i, ∀ b ∈ D j, Commute a b) ∧ iSupIndep D ∧
      (∀ i, D i ≤ Subgroup.centralizer ({t} : Set (StatedSU n (2 ^ f) K))) ∧
      (∀ i, p ∣ Nat.card (D i) → CFSG.IsQuasisimple ↥(D i) ∧
        NoAp p (↥(D i) ⧸ Subgroup.center ↥(D i))) ∧
      ∀ V : Subgroup (StatedSU n (2 ^ f) K),
        V ≤ Subgroup.centralizer ({t} : Set (StatedSU n (2 ^ f) K)) → ⁅V, V⁆ = V →
          ∀ e ∈ V, e ^ p = 1 → e ∈ ⨆ i, D i := by
  classical
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp3 : 3 < p := by rcases hp57 with rfl | rfl <;> norm_num
  have h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  have hq : 2 ≤ 2 ^ f := by
    have : 1 < 2 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) :=
    GeneralLinearGroup.toLin (t : GL (Fin n) K) with hxdef
  have hxSU : x ∈ sesqSpecialUnitaryGroup (stdHermForm h n) := by
    rw [stdHermForm_eq_gramForm, hxdef, toLin_mem_sesqSpecialUnitaryGroup_iff,
      ← unitarySU_eq_gramSU h]
    exact t.2
  have hx : (x : Module.End K (Fin n → K)) =
      mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    GeneralLinearGroup.coe_toLin _
  rw [← hx] at hsq
  have H : UnitaryPrimaryData h.bar (stdHermForm h n) x :=
    ⟨fun c => h.bar_bar c, stdHermForm_isSymm h n, stdHermForm_separatingLeft h n,
      sesqSpecialUnitaryGroup_le _ hxSU, hsq⟩
  have hF := r3e_unitary_semisimple_primary_algebra_and_full_centralizer h (stdHermForm h n)
    (stdHermForm_isSymm h n) (stdHermForm_separatingLeft h n) x
    (sesqSpecialUnitaryGroup_le _ hxSU) hsq
  obtain ⟨hcomm, hind, hgen⟩ := hF.directProduct
  let Ψ : StatedSU n (2 ^ f) K →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
    (GeneralLinearGroup.toLin (n := Fin n) (R := K)).toMonoidHom.comp
      (StatedSU n (2 ^ f) K).subtype
  have hΨinj : Function.Injective Ψ := fun a b hab =>
    Subtype.ext ((GeneralLinearGroup.toLin (n := Fin n) (R := K)).injective hab)
  have hΨt : Ψ t = x := rfl
  have hΨSU : ∀ s, Ψ s ∈ sesqSpecialUnitaryGroup (stdHermForm h n) := by
    intro s
    have e : Ψ s = GeneralLinearGroup.toLin (s : GL (Fin n) K) := rfl
    rw [e, stdHermForm_eq_gramForm, toLin_mem_sesqSpecialUnitaryGroup_iff, ← unitarySU_eq_gramSU h]
    exact s.2
  have hSUΨ : ∀ g ∈ sesqSpecialUnitaryGroup (stdHermForm h n), g ∈ Ψ.range := by
    intro g hg
    refine ⟨⟨(GeneralLinearGroup.toLin (n := Fin n) (R := K)).symm g, toStatedSU_mem hK hf hg⟩, ?_⟩
    exact MulEquiv.apply_symm_apply (GeneralLinearGroup.toLin (n := Fin n) (R := K)) g
  set B := stdHermForm h n with hB
  have hfin : (adjointOrbits h x).Finite := by
    unfold adjointOrbits
    exact Set.Finite.image _ (Finset.finite_toSet _)
  have hιfin : Finite (adjointOrbits h x) := hfin.to_subtype
  have := Fintype.ofFinite (adjointOrbits h x)
  have hFle : ∀ O : adjointOrbits h x,
      supportedUnitary B x (O : Set K[X]) ≤ unitaryCentralizer B x := fun O =>
    supportedUnitary_le_unitaryCentralizer _
  have hcomm' : ∀ i j : adjointOrbits h x, i ≠ j → ∀ a ∈ supportedUnitary B x (i : Set K[X]),
      ∀ b ∈ supportedUnitary B x (j : Set K[X]), Commute a b := fun i j hij a ha b hb =>
    hcomm i.1 i.2 j.1 j.2 (fun e => hij (Subtype.ext e)) a ha b hb
  let D0 : adjointOrbits h x → Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)) :=
    fun O => ⁅supportedUnitary B x (O : Set K[X]), supportedUnitary B x (O : Set K[X])⁆
  have hD0F : ∀ O, D0 O ≤ supportedUnitary B x (O : Set K[X]) := fun O =>
    Subgroup.commutator_le.mpr fun g hg g' hg' => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hg')
        (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hg')
  have hcomm0 : ∀ i j : adjointOrbits h x, i ≠ j → ∀ a ∈ D0 i, ∀ b ∈ D0 j, Commute a b :=
    fun i j hij a ha b hb => hcomm' i j hij a (hD0F i ha) b (hD0F j hb)
  have hind0 : iSupIndep D0 := hind.mono hD0F
  have hxp : x ^ p = 1 := by rw [← hΨt, ← map_pow, htp, map_one]
  have key : ∀ i : adjointOrbits h x, ∃ a : primaryFactors (x : Module.End K (Fin n → K)),
      supportedUnitary B x (i : Set K[X]) = orbitFactor B x (a : K[X]) ∧
      (D0 i = ⊥ ∨ (IsGoodBlock h x a ∧ D0 i = specialBlock B x (a : K[X])) ∨
        ¬ p ∣ Nat.card (orbitFactor B x (a : K[X]))) := by
    intro i
    obtain ⟨a₀, ha₀, hO⟩ := i.2
    refine ⟨⟨a₀, ha₀⟩, by rw [← hO]; rfl, ?_⟩
    have hF : supportedUnitary B x (i : Set K[X]) = orbitFactor B x a₀ := by rw [← hO]; rfl
    have := orbitFactor_trichotomy H hq hp hp3 ⟨a₀, ha₀⟩
    simp only [D0, hF]
    exact this
  refine ⟨adjointOrbits h x, hιfin, fun O => (D0 O).comap Ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij a ha b hb
    show a * b = b * a
    apply hΨinj
    rw [map_mul, map_mul]
    exact (hcomm0 i j hij _ (Subgroup.mem_comap.1 ha) _ (Subgroup.mem_comap.1 hb)).eq
  · exact iSupIndep_comap Ψ hΨinj hind0
  · intro i a ha
    rw [Subgroup.mem_centralizer_iff]
    intro t' ht'
    rw [Set.mem_singleton_iff] at ht'
    subst ht'
    have hc := (mem_unitaryCentralizer.mp (hFle i (hD0F i (Subgroup.mem_comap.1 ha)))).2
    have h1 : x * Ψ a = Ψ a * x := Units.ext hc.eq.symm
    apply hΨinj
    rw [map_mul, map_mul, hΨt]
    exact h1
  · intro i hpd
    dsimp only at hpd ⊢
    obtain ⟨a, hFa, hcases⟩ := key i
    rcases hcases with h0 | ⟨hgood, hSB⟩ | hcop
    · exfalso
      have h1 : Nat.card ((D0 i).comap Ψ) = 1 := by
        rw [h0, MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff Ψ).2 hΨinj]
        exact Subgroup.card_bot
      rw [h1] at hpd
      exact hp.one_lt.ne' (Nat.dvd_one.1 hpd)
    · have hSBle : specialBlock B x (a : K[X]) ≤ Ψ.range := fun g hg =>
        hSUΨ g (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a hgood hg)
      let eSB : (D0 i).comap Ψ ≃* specialBlock B x (a : K[X]) :=
        (MulEquiv.subgroupCongr (congrArg (Subgroup.comap Ψ) hSB)).trans
          (comapEquivOfLeRange Ψ hΨinj _ hSBle)
      have hpd' : p ∣ Nat.card (specialBlock B x (a : K[X])) := by
        rw [← Nat.card_congr eSB.toEquiv]
        exact hpd
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eSB.symm
        ((specialBlockFacts_of_good H hq a hgood).quasisimple hgood.1), ?_⟩
      exact NoAp.of_mulEquiv (centerQuotEquivOfMulEquiv' eSB.symm)
        (noAp_specialBlock H hq hp57 hpq hxp a hgood hpd')
    · exfalso
      have h1 : Nat.card ((D0 i).comap Ψ) ∣ Nat.card (orbitFactor B x (a : K[X])) := by
        have h2 : Nat.card ((D0 i).comap Ψ) ∣ Nat.card (D0 i) :=
          Subgroup.card_dvd_of_injective (Ψ.subgroupComap (D0 i)) fun a b hab =>
            Subtype.ext (hΨinj (congrArg Subtype.val hab))
        refine h2.trans (Subgroup.card_dvd_of_le ?_)
        rw [← hFa]
        exact hD0F i
      exact hcop (hpd.trans h1)
  · intro V hVc hV e he hep
    have hrange : ∀ i : adjointOrbits h x, ∀ d ∈ D0 i, d ^ p = 1 → d ∈ Ψ.range := by
      intro i d hd hdp
      obtain ⟨a, hFa, hcases⟩ := key i
      rcases hcases with h0 | ⟨hgood, hSB⟩ | hcop
      · rw [h0, Subgroup.mem_bot] at hd
        rw [hd]
        exact Ψ.range.one_mem
      · rw [hSB] at hd
        exact hSUΨ d (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a hgood hd)
      · have hdF : d ∈ orbitFactor B x (a : K[X]) := by
          rw [← hFa]
          exact hD0F i hd
        have hord : orderOf (⟨d, hdF⟩ : orbitFactor B x (a : K[X])) = 1 := by
          have h1 : orderOf (⟨d, hdF⟩ : orbitFactor B x (a : K[X])) ∣ p :=
            orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hdp))
          rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
          · exact h2
          · exact absurd (h2 ▸ orderOf_dvd_natCard _) hcop
        have : d = 1 := congrArg Subtype.val (orderOf_eq_one_iff.1 hord)
        rw [this]
        exact Ψ.range.one_mem
    have hVM : V.map Ψ ≤ unitaryCentralizer B x := by
      rintro _ ⟨v, hv, rfl⟩
      refine mem_unitaryCentralizer.mpr ⟨sesqSpecialUnitaryGroup_le _ (hΨSU v), ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.1 (hVc hv) t (Set.mem_singleton t)
      have h2 : x * Ψ v = Ψ v * x := by rw [← hΨt, ← map_mul, ← map_mul, h1]
      exact (congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
        (g : Module.End K (Fin n → K))) h2).symm
    have hmem : Ψ e ∈ ⨆ i : adjointOrbits h x, D0 i := by
      have hperf : ⁅V.map Ψ, V.map Ψ⁆ = V.map Ψ := by rw [← Subgroup.map_commutator, hV]
      have : V.map Ψ ≤ ⨆ i : adjointOrbits h x, D0 i :=
        calc V.map Ψ = ⁅V.map Ψ, V.map Ψ⁆ := hperf.symm
          _ ≤ ⁅unitaryCentralizer B x, unitaryCentralizer B x⁆ :=
            Subgroup.commutator_mono hVM hVM
          _ = ⁅⨆ O : adjointOrbits h x, supportedUnitary B x (O : Set K[X]),
                ⨆ O : adjointOrbits h x, supportedUnitary B x (O : Set K[X])⁆ := by rw [hgen]
          _ = ⨆ i : adjointOrbits h x, D0 i := commutator_iSup_commuting _ hcomm'
      exact this ⟨e, he, rfl⟩
    exact mem_iSup_comap_of_pow Ψ hΨinj D0 hcomm0 hind0 hrange hmem hep

end Su

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
