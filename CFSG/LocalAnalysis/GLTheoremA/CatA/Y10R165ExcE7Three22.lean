module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three21
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyNormalizer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcQLayer

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.Classical2 CFSG.Open
  CFSG.RankThree.PartOne.KLR CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
  CFSG.HardMathSupport.Timmesfeld.Torality
open scoped Matrix MatrixGroups Pointwise


private theorem mem_normalizer_e7T3QLayer {K : Type} [Field K] {L : Type} [Field L]
    {n : ModGL Tag.E7 L} {Φ : ModGL Tag.E7 L →* ModGL Tag.E7 L}
    {x z : adjointGroup Tag.E7 K}
    {ψ : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K))) →* ModGL Tag.E7 L}
    {y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)))}
    (hzC : z ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)))
    {bx bz : Fin Tag.E7.rank → Lˣ}
    (hψx : ψ ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = rootDiagUnit Tag.E7 bx)
    (hψz : ψ ⟨z, hzC⟩ = rootDiagUnit Tag.E7 bz)
    (hψadj : ψ y ∈ adjointGroup Tag.E7 L)
    (hψfix : ψ y ∈ twistedFixedPoints n Φ)
    (hker : ∀ α, IsRoot Tag.E7 α →
      ((α ∈ rootCharKernel bz ∧ α ∈ rootCharKernel bx) ↔ α ∈ e7T3A5SubA2))
    (hcommz : Commute (ψ y) (ψ ⟨z, hzC⟩)) :
    ψ y ∈ Subgroup.normalizer
      (rootSpan Tag.E7 L e7T3A5SubA2 ⊓ twistedFixedPoints n Φ : Set (ModGL Tag.E7 L)) := by
  classical
  let a : Fin 2 → Fin Tag.E7.rank → Lˣ := fun i => if i = 0 then bx else bz
  have hcommx : Commute (ψ y) (ψ ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) :=
    commute_psi_of_commute (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
      (Subgroup.mem_centralizer_singleton_iff.1 y.2)
  have hfam : ψ y ∈ familyCentralizer Tag.E7 L a := by
    refine mem_familyCentralizer.2 ⟨hψadj, fun i => ?_⟩
    fin_cases i
    · show rootDiagUnit Tag.E7 bx * ψ y * (rootDiagUnit Tag.E7 bx)⁻¹ = ψ y
      have h := hcommx
      rw [hψx] at h
      rw [← h.eq]
      group
    · show rootDiagUnit Tag.E7 bz * ψ y * (rootDiagUnit Tag.E7 bz)⁻¹ = ψ y
      have h := hcommz
      rw [hψz] at h
      rw [← h.eq]
      group
  have hNspan : ψ y ∈ Subgroup.normalizer
      (rootSpan Tag.E7 L (familyKernel a) : Set (ModGL Tag.E7 L)) :=
    familyCentralizer_le_normalizer_rootSpan a hfam
  have hkernel : familyKernel a = e7T3A5SubA2 := by
    ext α
    constructor
    · rintro ⟨hα, h⟩
      have h0 := h 0
      have h1 := h 1
      simp only [a, Fin.isValue, Fin.zero_eta, if_pos, if_neg, Fin.mk_one,
        one_ne_zero, not_false_eq_true] at h0 h1
      exact (hker α hα).1 ⟨⟨hα, h1⟩, ⟨hα, h0⟩⟩
    · intro hα
      refine ⟨isRoot_of_mem_e7T3A5SubA2 hα, fun i => ?_⟩
      have h := (hker α (isRoot_of_mem_e7T3A5SubA2 hα)).2 hα
      fin_cases i
      · simpa [a] using h.2.2
      · simpa [a] using h.1.2
  rw [hkernel] at hNspan
  exact mem_normalizer_inf_twistedFixedPoints hNspan hψfix

private theorem e7T3_JQ_of_layers {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}
    (F : E7ThreeFrame K L ℓ f p ε) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (hq2 : ε = -1 → 2 < ℓ ^ f)
    {x z : adjointGroup Tag.E7 K}
    (hzC : z ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)))
    {v : WeylGroup Tag.E7} {b : Fin Tag.E7.rank → Lˣ}
    {Φ' : SL(6, L) ≃* SL(6, L)} {P : Subgroup (ModGL Tag.E7 L)}
    {ψ : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K))) →* ModGL Tag.E7 L}
    {J : Subgroup (adjointGroup Tag.E7 K)}
    (hfixq : CFSG.Open.IsQuasisimple ↥(fixSubgroup Φ'))
    (hS : rootCharKernel b = (fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7))
    (hΦ' : ∀ X : SL(6, L),
      ((canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * F.n *
          canonicalRep (coxeterSystem Tag.E7) L v) *
        Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (a5Frame L X) *
        ((canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * F.n *
          canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ = a5Frame L (Φ' X))
    (hPeq : P = (fixSubgroup Φ').map
      ((MulAut.conj (canonicalRep (coxeterSystem Tag.E7) L v)).toMonoidHom.comp (a5Frame L)))
    (hψinj : Function.Injective ψ)
    (hψeq : ∀ y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K))),
      ψ y = F.g0⁻¹ * adjEmb Tag.E7 K L (y : adjointGroup Tag.E7 K) * F.g0)
    (hψR : ∀ y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K))),
      F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ y) * F.n⁻¹ = ψ y)
    (hψadj : ∀ y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K))),
      ψ y ∈ adjointGroup Tag.E7 L)
    (hPψ : P ≤ ψ.range)
    (hJdef : J = (P.comap ψ).map
      (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K))).subtype)
    (hSsub : e7T3A5SubA2 ⊆ rootCharKernel b)
    {bz : Fin Tag.E7.rank → Lˣ} (hZLsub : e7T3A5SubA2 ⊆ rootCharKernel bz)
    (hψx : ψ ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = rootDiagUnit Tag.E7 b)
    (hψz : ψ ⟨z, hzC⟩ = rootDiagUnit Tag.E7 bz)
    (hker : ∀ α, IsRoot Tag.E7 α →
      ((α ∈ rootCharKernel bz ∧ α ∈ rootCharKernel b) ↔ α ∈ e7T3A5SubA2)) :
    ∃ Q : Subgroup (adjointGroup Tag.E7 K),
      Q ≤ J ∧ Q ≤ Subgroup.centralizer ({z} : Set (adjointGroup Tag.E7 K)) ∧
      (Q.subgroupOf (J ⊓ Subgroup.centralizer
        ({z} : Set (adjointGroup Tag.E7 K)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥Q ∧ p ∣ Nat.card Q := by
  classical
  let QL : Subgroup (ModGL Tag.E7 L) :=
    rootSpan Tag.E7 L e7T3A5SubA2 ⊓
      twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
  have hQLleP : QL ≤ P :=
    e7T3QLayer_le_model F hf hK hε hq2 hS hSsub
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥(fixSubgroup Φ')).2.2.1.mpr hfixq)
      hΦ' hPeq
  have hQLqs : CFSG.IsQuasisimple ↥QL :=
    isQuasisimple_e7T3QLayer (L := L) (p := p) hf hK hε hq2 F.n F.hnm
      (monomialSubgroup_le_adjointGroup' F.hnm) (fun x => F.hnW x)
  have hpQL : p ∣ Nat.card ↥QL :=
    dvd_card_e7T3QLayer F hf hK hp hp3 hε hpf
  have hN : ∀ y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K))),
      (y : adjointGroup Tag.E7 K) * z = z * (y : adjointGroup Tag.E7 K) →
      ψ y ∈ Subgroup.normalizer (QL : Set (ModGL Tag.E7 L)) := by
    intro y hyz
    exact mem_normalizer_e7T3QLayer (n := F.n)
      (Φ := Units.map (entrywiseHom (iterateFrobenius L ℓ f))) hzC hψx hψz (hψadj y)
      (mem_twistedFixedPoints.2 (hψR y)) hker (commute_psi_of_commute hzC hyz)
  have hQLz : QL ≤ Subgroup.centralizer
      ({ψ ⟨z, hzC⟩} : Set (ModGL Tag.E7 L)) := by
    rw [hψz]
    exact inf_le_left.trans (rootSpan_le_centralizer (K := L) bz hZLsub)
  obtain ⟨Q, hQJ, hQz, hQn, hQq, hpQ⟩ :=
    exists_qLayer_of_quasisimple (x := x) (z := z) ψ hψinj
      (P := P) (QL := QL) hQLleP (hQLleP.trans hPψ) hzC hQLz hN
      ((CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥QL)).1 hQLqs) hpQL
  refine ⟨Q, ?_, hQz, ?_, hQq, hpQ⟩
  · rw [hJdef]
    exact hQJ
  · rw [hJdef]
    exact hQn

theorem exists_e7T3_JQ_split {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p 1) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)
    {x z : adjointGroup Tag.E7 K} (hxz : Commute x z) (hx : orderOf x = p)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (hxframe : F.g0⁻¹ * adjEmb Tag.E7 K L x * F.g0 =
      rootDiagUnit Tag.E7 (fun i => ζ ^ (e7T3XColumn 1 (Nat.card K : ZMod p) i).val))
    (hzframe : F.g0⁻¹ * adjEmb Tag.E7 K L z * F.g0 =
      rootDiagUnit Tag.E7 (fun i => ζ ^ (e7T3ZColumn 1 (Nat.card K : ZMod p) i).val))
    (hker : ∀ α, IsRoot Tag.E7 α →
      ((α ∈ rootCharKernel (fun i => ζ ^ (e7T3ZColumn 1 (Nat.card K : ZMod p) i).val) ∧
        α ∈ rootCharKernel (fun i => ζ ^ (e7T3XColumn 1 (Nat.card K : ZMod p) i).val)) ↔
        α ∈ e7T3A5SubA2)) :
    ∃ (J : Subgroup (adjointGroup Tag.E7 K)) (Φ' : SL(6, L) ≃* SL(6, L))
      (Q : Subgroup (adjointGroup Tag.E7 K)),
      J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)) ∧
      (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥J ∧ p ∣ Nat.card J ∧
      (∃ H : SL(6, L), ∀ X, X ∈ fixSubgroup Φ' ↔
        ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹) ∧
      (∃ ρ : fixSubgroup Φ' →* J, Function.Surjective ρ ∧
        (∀ z ∈ ρ.ker, ∀ u : fixSubgroup Φ', z * u = u * z) ∧ Nat.card ρ.ker ∣ 6) ∧
      Q ≤ J ∧ Q ≤ Subgroup.centralizer ({z} : Set (adjointGroup Tag.E7 K)) ∧
      (Q.subgroupOf (J ⊓ Subgroup.centralizer
        ({z} : Set (adjointGroup Tag.E7 K)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥Q ∧ p ∣ Nat.card Q := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFrdef, iterateFrobenius_def, hK]
  have hq : ((Nat.card K : ZMod p)) ^ 2 + ((1 : ℤ) : ZMod p) * (Nat.card K : ZMod p) + 1 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1) p).2 hpf
    simpa using h
  set b : Fin Tag.E7.rank → Lˣ :=
    fun i => ζ ^ (e7T3XColumn 1 (Nat.card K : ZMod p) i).val with hbdef
  set bz : Fin Tag.E7.rank → Lˣ :=
    fun i => ζ ^ (e7T3ZColumn 1 (Nat.card K : ZMod p) i).val with hbzdef
  have hstab : E7StabHyp F.n Fr p :=
    e7T3_stabHyp F hK hp hp3 (Or.inl rfl) (by simpa using hpf)
  have hS : rootCharKernel b = (fun γ => e7T3A5Transport • γ) ''
      parabolicRoots Tag.E7 (a5Nodes Tag.E7) := by
    simpa [b, e7T3A5Transport] using
      rootCharKernel_e7T3XTuple (p := p) (q := (Nat.card K : ZMod p)) hp hp3 hζ (Or.inl rfl) hq
  have hcert : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        (e7T3A5Transport⁻¹ * weylQuotientHom Tag.E7 L ⟨F.n, F.hnm⟩ * e7T3A5Transport) •
          α = u • α := by
    obtain ⟨u, hu, hact⟩ := e7T3XTuple_hcert (L := L) (Or.inl rfl) F.hnW
    exact ⟨u, hu, fun α hα => by simpa [e7T3A5Transport] using hact α hα⟩
  have hb : b ∈ fixedCharTuples ((1 : ℤ) • e7T3W) Fr := by
    simpa [b, Fr] using mem_fixedCharTuples_e7T3XTuple (q₀ := Nat.card K) hFr hζ (Or.inl rfl) hq
  have hap : ∀ i, b i ^ p = 1 := fun i => e7T3XTuple_pow_eq_one hζ i
  have hb1 : b ≠ 1 := e7T3XTuple_ne_one hp hζ
  have hh : F.g0⁻¹ * adjEmb Tag.E7 K L (1 * x * 1⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom Fr)) := by
    have e1 : (1 : adjointGroup Tag.E7 K) * x * 1⁻¹ = x := by group
    rw [e1, hxframe]
    exact rootDiagUnit_mem_twistedTorus_e7T3XTuple F hK hζ (Or.inl rfl) hq
  have hbh : rootDiagUnit Tag.E7 b = F.g0⁻¹ * adjEmb Tag.E7 K L (1 * x * 1⁻¹) * F.g0 := by
    rw [show (1 : adjointGroup Tag.E7 K) * x * 1⁻¹ = x by group, ← hxframe]
  obtain ⟨J, Φ', P, ψ, hJx, hJn, hJq, hpJ, hfin, hfixq, ⟨H, hH⟩, hPeq, hψinj, hψeq,
    hψHQ, hψR, hψadj, hPψ, hJdef, hΦ', ρ, hρs, hρc, hρk⟩ :=
    exists_e7Three_a5Layer_J_split_data F hf hK hp hp3 hpf hstab hx 1 hh hb hap hb1 hbh hS hcert
  have hψeq' : ∀ y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K))),
      ψ y = F.g0⁻¹ * adjEmb Tag.E7 K L (y : adjointGroup Tag.E7 K) * F.g0 := by
    intro y
    simpa using hψeq y
  have hψx : ψ ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = rootDiagUnit Tag.E7 b := by
    rw [hψeq']
    exact hxframe
  have hzC : z ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm
  have hψz : ψ ⟨z, hzC⟩ = rootDiagUnit Tag.E7 bz := by
    rw [hψeq']
    exact hzframe
  have hSsub : e7T3A5SubA2 ⊆ rootCharKernel b := fun α hα =>
    ((hker α (isRoot_of_mem_e7T3A5SubA2 hα)).mpr hα).2
  have hZLsub : e7T3A5SubA2 ⊆ rootCharKernel bz := fun α hα =>
    ((hker α (isRoot_of_mem_e7T3A5SubA2 hα)).mpr hα).1
  obtain ⟨Q, hQJ, hQz, hQn, hQq, hpQ⟩ :=
    e7T3_JQ_of_layers F hf hK hp hp3 (Or.inl rfl) (by simpa using hpf)
      (fun h => absurd h (by norm_num)) hzC hfixq hS hΦ' hPeq hψinj hψeq' hψR hψadj hPψ hJdef
      hSsub hZLsub hψx hψz hker
  exact ⟨J, Φ', Q, hJx, hJn, hJq, hpJ, ⟨H, hH⟩, ⟨ρ, hρs, hρc, hρk⟩,
    hQJ, hQz, hQn, hQq, hpQ⟩

theorem exists_e7T3_JQ_unitary {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hq2 : 2 < ℓ ^ f)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1) * (Nat.card K : ℤ) + 1)
    {x z : adjointGroup Tag.E7 K} (hxz : Commute x z) (hx : orderOf x = p)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (hxframe : F.g0⁻¹ * adjEmb Tag.E7 K L x * F.g0 =
      rootDiagUnit Tag.E7 (fun i => ζ ^ (e7T3XColumn (-1) (Nat.card K : ZMod p) i).val))
    (hzframe : F.g0⁻¹ * adjEmb Tag.E7 K L z * F.g0 =
      rootDiagUnit Tag.E7 (fun i => ζ ^ (e7T3ZColumn (-1) (Nat.card K : ZMod p) i).val))
    (hker : ∀ α, IsRoot Tag.E7 α →
      ((α ∈ rootCharKernel (fun i => ζ ^ (e7T3ZColumn (-1) (Nat.card K : ZMod p) i).val) ∧
        α ∈ rootCharKernel (fun i => ζ ^ (e7T3XColumn (-1) (Nat.card K : ZMod p) i).val)) ↔
        α ∈ e7T3A5SubA2)) :
    ∃ (J : Subgroup (adjointGroup Tag.E7 K)) (Φ' : SL(6, L) ≃* SL(6, L))
      (Q : Subgroup (adjointGroup Tag.E7 K)),
      J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)) ∧
      (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥J ∧ p ∣ Nat.card J ∧
      (∃ H : SL(6, L), ∀ X, X ∈ fixSubgroup Φ' ↔
        ∃ Y ∈ unitarySet (ℓ ^ f) 6,
          Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL H * Y *
            (Matrix.SpecialLinearGroup.toGL H)⁻¹) ∧
      (∃ ρ : fixSubgroup Φ' →* J, Function.Surjective ρ ∧
        (∀ z ∈ ρ.ker, ∀ u : fixSubgroup Φ', z * u = u * z) ∧ Nat.card ρ.ker ∣ 6) ∧
      Q ≤ J ∧ Q ≤ Subgroup.centralizer ({z} : Set (adjointGroup Tag.E7 K)) ∧
      (Q.subgroupOf (J ⊓ Subgroup.centralizer
        ({z} : Set (adjointGroup Tag.E7 K)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥Q ∧ p ∣ Nat.card Q := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFrdef, iterateFrobenius_def, hK]
  have hq : ((Nat.card K : ZMod p)) ^ 2 + ((-1 : ℤ) : ZMod p) * (Nat.card K : ZMod p) + 1 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((Nat.card K : ℤ) ^ 2 + (-1) * (Nat.card K : ℤ) + 1) p).2 hpf
    simpa using h
  set b : Fin Tag.E7.rank → Lˣ :=
    fun i => ζ ^ (e7T3XColumn (-1) (Nat.card K : ZMod p) i).val with hbdef
  set bz : Fin Tag.E7.rank → Lˣ :=
    fun i => ζ ^ (e7T3ZColumn (-1) (Nat.card K : ZMod p) i).val with hbzdef
  have hstab : E7StabHyp F.n Fr p :=
    e7T3_stabHyp F hK hp hp3 (Or.inr rfl) hpf
  have hS : rootCharKernel b = (fun γ => e7T3A5Transport • γ) ''
      parabolicRoots Tag.E7 (a5Nodes Tag.E7) := by
    simpa [b, e7T3A5Transport] using
      rootCharKernel_e7T3XTuple (p := p) (q := (Nat.card K : ZMod p)) hp hp3 hζ (Or.inr rfl) hq
  have hcert : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        (e7T3A5Transport⁻¹ * weylQuotientHom Tag.E7 L ⟨F.n, F.hnm⟩ * e7T3A5Transport) •
          α = u • ((-1 : ℤ) • α) := by
    obtain ⟨u, hu, hact⟩ := e7T3XTuple_hcert (L := L) (Or.inr rfl) F.hnW
    exact ⟨u, hu, fun α hα => by simpa [e7T3A5Transport] using hact α hα⟩
  have hb : b ∈ fixedCharTuples ((-1 : ℤ) • e7T3W) Fr := by
    simpa [b, Fr] using mem_fixedCharTuples_e7T3XTuple (q₀ := Nat.card K) hFr hζ (Or.inr rfl) hq
  have hap : ∀ i, b i ^ p = 1 := fun i => e7T3XTuple_pow_eq_one hζ i
  have hb1 : b ≠ 1 := e7T3XTuple_ne_one hp hζ
  have hh : F.g0⁻¹ * adjEmb Tag.E7 K L (1 * x * 1⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom Fr)) := by
    have e1 : (1 : adjointGroup Tag.E7 K) * x * 1⁻¹ = x := by group
    rw [e1, hxframe]
    exact rootDiagUnit_mem_twistedTorus_e7T3XTuple F hK hζ (Or.inr rfl) hq
  have hbh : rootDiagUnit Tag.E7 b = F.g0⁻¹ * adjEmb Tag.E7 K L (1 * x * 1⁻¹) * F.g0 := by
    rw [show (1 : adjointGroup Tag.E7 K) * x * 1⁻¹ = x by group, ← hxframe]
  obtain ⟨J, Φ', P, ψ, hJx, hJn, hJq, hpJ, hfin, hfixq, ⟨H, hH⟩, hPeq, hψinj, hψeq,
    hψHQ, hψR, hψadj, hPψ, hJdef, hΦ', ρ, hρs, hρc, hρk⟩ :=
    exists_e7Three_a5Layer_J_unitary_data F hf hK hp hp3 hq2 hpf hstab hx 1 hh hb hap hb1 hbh
      hS hcert
  have hψeq' : ∀ y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K))),
      ψ y = F.g0⁻¹ * adjEmb Tag.E7 K L (y : adjointGroup Tag.E7 K) * F.g0 := by
    intro y
    simpa using hψeq y
  have hψx : ψ ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = rootDiagUnit Tag.E7 b := by
    rw [hψeq']
    exact hxframe
  have hzC : z ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E7 K)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm
  have hψz : ψ ⟨z, hzC⟩ = rootDiagUnit Tag.E7 bz := by
    rw [hψeq']
    exact hzframe
  have hSsub : e7T3A5SubA2 ⊆ rootCharKernel b := fun α hα =>
    ((hker α (isRoot_of_mem_e7T3A5SubA2 hα)).mpr hα).2
  have hZLsub : e7T3A5SubA2 ⊆ rootCharKernel bz := fun α hα =>
    ((hker α (isRoot_of_mem_e7T3A5SubA2 hα)).mpr hα).1
  obtain ⟨Q, hQJ, hQz, hQn, hQq, hpQ⟩ :=
    e7T3_JQ_of_layers F hf hK hp hp3 (Or.inr rfl) (by simpa using hpf)
      (fun _ => hq2) hzC hfixq hS hΦ'
      hPeq hψinj hψeq' hψR hψadj hPψ hJdef hSsub hZLsub hψx hψz hker
  exact ⟨J, Φ', Q, hJx, hJn, hJq, hpJ, ⟨H, hH⟩, ⟨ρ, hρs, hρc, hρk⟩,
    hQJ, hQz, hQn, hQq, hpQ⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
