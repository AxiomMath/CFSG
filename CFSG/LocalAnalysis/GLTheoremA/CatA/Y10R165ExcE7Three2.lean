module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.RankThree.PartOne.KE.E7FourPerX

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KA5L
  CFSG.RankThree.Classical2 CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups Pointwise commutatorElement

variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem exists_e7Three_a5Layer_split_compat (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hΦ : (Nat.card K : ZMod p) ^ 2 + Nat.card K + 1 = 0)
    {n : ModGL Tag.E7 L} (hnm : n ∈ monomialSubgroup Tag.E7 L)
    (hnC : n ∈ adjointGroup Tag.E7 L) {v : WeylGroup Tag.E7}
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) • α = u • α) :
    ∃ (Φ' : SL(6, L) ≃* SL(6, L)) (P : Subgroup (ModGL Tag.E7 L)),
      IsSigmaFamily n (iterateFrobenius L ℓ f)
        ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) (fun _ : Unit => P) ∧
      P = (fixSubgroup Φ').map
        ((MulAut.conj (canonicalRep (coxeterSystem Tag.E7) L v)).toMonoidHom.comp (a5Frame L)) ∧
      Finite (fixSubgroup Φ') ∧ CFSG.IsQuasisimple (fixSubgroup Φ') ∧
      (∃ H : SL(6, L), ∀ X, X ∈ fixSubgroup Φ' ↔
        ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹) ∧
      p ∣ Nat.card P ∧
      (∀ X : SL(6, L),
        ((canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * n *
            canonicalRep (coxeterSystem Tag.E7) L v) *
          Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (a5Frame L X) *
          ((canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * n *
            canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ = a5Frame L (Φ' X)) ∧
      ∃ ρ : fixSubgroup Φ' →* P, Function.Surjective ρ ∧
        (∀ z ∈ ρ.ker, ∀ u : fixSubgroup Φ', z * u = u * z) ∧ Nat.card ρ.ker ∣ 6 := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hVdef
  have hVm : V ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L v
  set n' : ModGL Tag.E7 L := V⁻¹ * n * V with hn'def
  have hn'm : n' ∈ monomialSubgroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVm) hnm) hVm
  have hπV : weylQuotientHom Tag.E7 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v := by
    have h : (⟨n', hn'm⟩ : monomialSubgroup Tag.E7 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hnm⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [h, map_mul, map_mul, map_inv, hπV]
  obtain ⟨u, hu, hact⟩ := hcert
  obtain ⟨π, hπ⟩ := CFSG.RankThree.PartOne.KA5L.exists_perm_of_mem_parabolicWeylGroup hu
  have hπ' : ∀ a b : Fin 6, a ≠ b → weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ • a5Root a b =
      a5Root (π a) (π b) := by
    intro a b hab
    rw [hπn', hact (a5Root a b) (a5Root_mem_parabolicRoots hab)]
    exact hπ a b
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_split Fr hFrbij n' hn'm π hπ'
  have hshape' : ∀ (i j : Fin 6) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(6, L)) :
        Matrix (Fin 6) (Fin 6) L) = 1 + single (π i) (π j) ((b i j : L) * t ^ ℓ ^ f) :=
    fun i j hij t => by rw [hshape i j hij t, hFr]
  obtain ⟨-, ⟨H, hH⟩, hfin, hq, -, hcenter⟩ :=
    sln_root_permuting_frobenius_fixed_split hℓ hf hK (by norm_num : 3 ≤ 6) π Φ' b hshape'
  have hcent : Nat.card (Subgroup.center (fixSubgroup Φ')) ∣ 6 := by
    rw [hcenter]
    exact Nat.gcd_dvd_left _ _
  have hcardSL : Nat.card (fixSubgroup Φ') = Nat.card (SL(6, K)) := by
    have hinj : Function.Injective (fun Y : SL(6, K) =>
        (⟨H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹, (hH _).2 ⟨Y, rfl⟩⟩ :
          fixSubgroup Φ')) := by
      intro Y Z hYZ
      have h := congrArg (fun t : fixSubgroup Φ' => (t : SL(6, L))) hYZ
      simp only [Subtype.mk.injEq] at h
      have h2 : Matrix.SpecialLinearGroup.map (algebraMap K L) Y =
          Matrix.SpecialLinearGroup.map (algebraMap K L) Z :=
        (MulAut.conj H).injective (by simpa [MulAut.conj_apply] using h)
      have h3 := congrArg (fun t : SL(6, L) => (t : Matrix (Fin 6) (Fin 6) L)) h2
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h3
      exact Subtype.ext (Matrix.map_injective (RingHom.injective (algebraMap K L)) h3)
    have hsurj : Function.Surjective (fun Y : SL(6, K) =>
        (⟨H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹, (hH _).2 ⟨Y, rfl⟩⟩ :
          fixSubgroup Φ')) := by
      intro X
      obtain ⟨Y, hY⟩ := (hH (X : SL(6, L))).1 X.2
      exact ⟨Y, Subtype.ext hY.symm⟩
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm
  have hcert' : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) • α = u • ((1 : ℤ) • α) := by
    refine ⟨u, hu, fun α hα => ?_⟩
    rw [one_zsmul]
    exact hact α hα
  obtain ⟨P, hfam, hPeq, ρ, hρs, hρc, hρk⟩ :=
    exists_a5Layer_sigma_of_aut (ε := 1) hf hK (Or.inl rfl)
      (by intro h; exact absurd h (by norm_num)) hnm hnC hcert' Φ' hΦ' hq hcent
  haveI : Finite ↥(fixSubgroup Φ') := hfin
  haveI : Finite ↥P := hfam.1 ()
  refine ⟨Φ', P, hfam, hPeq, hfin, hq, ⟨H, hH⟩, ?_, ?_, ρ, hρs, hρc, hρk⟩
  · exact dvd_card_of_surjective_of_ker_dvd_six hp hp3 ρ hρs hρk (by
      rw [hcardSL]
      exact dvd_card_SL_six hp hp3 hΦ)
  · intro X
    exact hΦ' X

section Ambient

variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem exists_e7Three_a5Layer_J_split_data (F : E7ThreeFrame K L ℓ f p 1) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p)
    {x : adjointGroup .E7 K} (hx : orderOf x = p) (c : adjointGroup .E7 K)
    (hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {b : Fin Tag.E7.rank → Lˣ}
    (hb : b ∈ fixedCharTuples ((1 : ℤ) • e7T3W) (iterateFrobenius L ℓ f))
    (hap : ∀ i, b i ^ p = 1) (hb1 : b ≠ 1)
    (hbh : rootDiagUnit .E7 b = F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0)
    {v : WeylGroup Tag.E7}
    (hS : rootCharKernel b = (fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7))
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        (v⁻¹ * weylQuotientHom Tag.E7 L ⟨F.n, F.hnm⟩ * v) • α = u • α) :
    ∃ (J : Subgroup (adjointGroup .E7 K)) (Φ' : SL(6, L) ≃* SL(6, L))
      (P : Subgroup (ModGL Tag.E7 L))
      (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL Tag.E7 L),
      J ≤ Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) ∧
      (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)))).Normal ∧
      CFSG.Open.IsQuasisimple ↥J ∧ p ∣ Nat.card J ∧
      Finite (fixSubgroup Φ') ∧ CFSG.Open.IsQuasisimple (fixSubgroup Φ') ∧
      (∃ H : SL(6, L), ∀ X, X ∈ fixSubgroup Φ' ↔
        ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹) ∧
      P = (fixSubgroup Φ').map
        ((MulAut.conj (canonicalRep (coxeterSystem Tag.E7) L v)).toMonoidHom.comp (a5Frame L)) ∧
      Function.Injective ψ ∧
      (∀ y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))),
        ψ y = F.g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * F.g0) ∧
      (∀ y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))),
        ψ y ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L (rootCharKernel b)) ∧
      (∀ y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))),
        F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ y) * F.n⁻¹ = ψ y) ∧
      (∀ y : ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))),
        ψ y ∈ adjointGroup Tag.E7 L) ∧
      P ≤ ψ.range ∧
      J = (P.comap ψ).map (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))).subtype ∧
      (∀ X : SL(6, L),
        ((canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * F.n *
            canonicalRep (coxeterSystem Tag.E7) L v) *
          Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (a5Frame L X) *
          ((canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ * F.n *
            canonicalRep (coxeterSystem Tag.E7) L v)⁻¹ = a5Frame L (Φ' X)) ∧
      ∃ ρ : fixSubgroup Φ' →* J, Function.Surjective ρ ∧
        (∀ z ∈ ρ.ker, ∀ u : fixSubgroup Φ', z * u = u * z) ∧ Nat.card ρ.ker ∣ 6 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + (Nat.card K : ℕ) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1) p).2 hpf
    simpa using this
  have hnC : F.n ∈ adjointGroup Tag.E7 L := monomialSubgroup_le_adjointGroup' F.hnm
  obtain ⟨Φ', P, hfam, hPeq, hfin, hq, ⟨H, hH⟩, hpP, hΦ'com, ρ, hρs, hρc, hρk⟩ :=
    exists_e7Three_a5Layer_split_compat (K := K) (L := L) (ℓ := ℓ) (f := f) (p := p)
      hf hK hp hp3 (by simpa using hΦ) F.hnm hnC hcert
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  have hPQ' : ∀ i, (fun _ : Unit => P) i ≤ rootSpan Tag.E7 L (rootCharKernel b) :=
    fun i => by rw [hS]; exact hPQ i
  have hPnorm' : ∀ i, ∀ y ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L (rootCharKernel b),
      y ∈ twistedFixedPoints F.n (Units.map (entrywiseHom Fr)) →
      ∀ u ∈ (fun _ : Unit => P) i, y * u * y⁻¹ ∈ (fun _ : Unit => P) i :=
    fun i y hy hyR u hu => hPnorm i y (hS ▸ hy) hyR u hu
  have hPcent' : ∀ y ∈ torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L (rootCharKernel b),
      y ∈ twistedFixedPoints F.n (Units.map (entrywiseHom Fr)) →
      (∀ i, ∀ u ∈ (fun _ : Unit => P) i, y * u = u * y) →
      y ∈ subtorusSigma F.n (Units.map (entrywiseHom Fr)) (rootCharKernel b) :=
    fun y hy hyR hc => hS ▸ hPcent y (hS ▸ hy) hyR hc
  obtain ⟨hcS, hkerZ⟩ := e7_perx_hc_hkerZ (K := K) (L := L)
    Fr F.g0 hbh hh (S := rootCharKernel b) rfl
  have hFrK : ∀ c : L, Fr c = c ^ Nat.card K := fun c => by rw [hFr, hK]
  set Cx : Subgroup (adjointGroup .E7 K) :=
    Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) with hCxdef
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [CFSG.RankThree.Chevalley.rootChar_neg', hα.2, inv_one]⟩
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψV⟩ :=
    sigma_embedding_data_of_stab (adjEmb .E7 K L) adjEmb_injective adjEmb_mem
      (Units.map (entrywiseHom Fr)) (adjEmb_frobenius Fr hFrK) F.n F.g0 F.hg0C F.hg0 F.hperf hp
      (fun a hap ha1 haT => hstab a hap ha1 haT)
      (fun α hα => hα.1) hSn (fun _ : Unit => P) hPfin hPq hPQ' hPR hPadj hPnorm' hPcent'
      hx c hcS hkerZ
  set J0 : Subgroup ↥Cx := (P).comap ψ with hJ0def
  have hJ0le : J0.map Cx.subtype ≤ Cx := Subgroup.map_subtype_le J0
  set J : Subgroup (adjointGroup .E7 K) := J0.map Cx.subtype with hJdef
  have hmap : J0.map ψ = P := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hy
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (hPψ () hy)
      exact ⟨v, by change ψ v ∈ P; rw [hv]; exact hy, hv⟩
  let e2 : ↥J0 ≃* ↥P :=
    (Subgroup.equivMapOfInjective J0 ψ hψinj).trans (MulEquiv.subgroupCongr hmap)
  let e1 : ↥J0 ≃* ↥J := Subgroup.equivMapOfInjective J0 Cx.subtype Cx.subtype_injective
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥J).2.2.1.mp
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.symm.trans e2).symm (hPq ()))
  have hcardJ : Nat.card ↥J = Nat.card ↥P := Nat.card_congr (e1.symm.trans e2).toEquiv
  have hJle : J ≤ Cx := hJ0le
  have hJn : (J.subgroupOf Cx).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJle]
    intro h k hh hk
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨⟨k * v * k⁻¹, ?_⟩, ?_, rfl⟩
    · exact Cx.mul_mem (Cx.mul_mem hk v.2) (Cx.inv_mem hk)
    · rw [Subgroup.mem_comap]
      have hk' : ψ ⟨k, hk⟩ ∈ torusGroup Tag.E7 L ⊔
          rootSpan Tag.E7 L (rootCharKernel b) := hψHQ ⟨k, hk⟩
      have hkR : ψ ⟨k, hk⟩ ∈ twistedFixedPoints F.n (Units.map (entrywiseHom Fr)) :=
        hψR ⟨k, hk⟩
      have hvP : ψ v ∈ P := hv
      have hconj := hPnorm' () (ψ ⟨k, hk⟩) hk' hkR (ψ v) hvP
      have harg : (⟨k * v * k⁻¹, Cx.mul_mem (Cx.mul_mem hk v.2) (Cx.inv_mem hk)⟩ : ↥Cx) =
          ⟨k, hk⟩ * v * ⟨k, hk⟩⁻¹ := Subtype.ext rfl
      rw [harg, map_mul, map_mul, map_inv]
      exact hconj
  haveI : Finite ↥(fixSubgroup Φ') := hfin
  haveI : Finite ↥P := hPfin ()
  haveI : Finite ↥J := Finite.of_equiv ↥P (e1.symm.trans e2).toEquiv.symm
  have hfixq : CFSG.Open.IsQuasisimple ↥(fixSubgroup Φ') :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥(fixSubgroup Φ')).2.2.1.mp hq
  refine ⟨J, Φ', P, ψ, hJ0le, hJn, hJq, hcardJ ▸ hpP, hfin, hfixq, ⟨H, hH⟩,
    hPeq, hψinj, hψ, hψHQ, hψR, hψadj, hPψ (), hJdef, hΦ'com, ?_⟩
  · refine ⟨(e1.symm.trans e2).symm.toMonoidHom.comp ρ,
      (e1.symm.trans e2).symm.surjective.comp hρs, ?_, ?_⟩
    · intro z hz u
      have hz1 : z ∈ ρ.ker := by
        have h := hz
        rw [MonoidHom.mem_ker] at h ⊢
        exact (e1.symm.trans e2).symm.injective (by simpa using h)
      exact hρc z hz1 u
    · rw [show ((e1.symm.trans e2).symm.toMonoidHom.comp ρ).ker = ρ.ker from
        MonoidHom.ker_comp_of_injective _ _ (e1.symm.trans e2).symm.injective]
      exact hρk

end Ambient

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
