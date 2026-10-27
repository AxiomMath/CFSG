module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Centralizer
public import CFSG.RankThree.PartOne.KE.FiniteFieldAlgClosure
public import CFSG.RankThree.PartOne.TCX.E.E6A2Sigma
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PlaneCyclic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Generic

theorem exists_hom_SL_of_map {G : Type*} [Group G] {R S : Type*} [Field R] [Field S] {ν : ℕ}
    {ψ : R →+* S} (hψ : Function.Injective ψ) (Λ₀ : G →* SL(ν, S))
    (h : ∀ x i j, (Λ₀ x : Matrix (Fin ν) (Fin ν) S) i j ∈ Set.range ψ) :
    ∃ Λ : G →* SL(ν, R), ∀ x, Matrix.SpecialLinearGroup.map ψ (Λ x) = Λ₀ x := by
  classical
  choose f hf using fun x =>
    CFSG.RankThree.Classical2.exists_map_eq_of_forall_mem_range hψ (Λ₀ x) (h x)
  have hinj := CFSG.RankThree.Classical2.specialLinearGroup_map_injective (n := ν) hψ
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hf⟩
  · apply hinj
    rw [hf, map_one, map_one]
  · intro a b
    apply hinj
    rw [map_mul, hf, hf, hf, map_mul]

theorem isCyclic_centralizer_of_injective_hom {G : Type*} [Group G] {F : Type*} [Field F]
    [Fintype F] {ν p : ℕ} (hp : p.Prime) (hν : 2 ≤ ν)
    (hord : orderOf ((Fintype.card F : ℕ) : ZMod p) = ν)
    (Λ : G →* SL(ν, F)) (hΛ : Function.Injective Λ) {g : G} (hg : orderOf g = p) :
    IsCyclic ↥(Subgroup.centralizer ({g} : Set G)) := by
  have h1 : orderOf (Λ g) = p := by rw [orderOf_injective Λ hΛ g, hg]
  have hc := isCyclic_centralizer_of_orderOf_eq F hp hν hord h1
  let φ : ↥(Subgroup.centralizer ({g} : Set G)) →*
      ↥(Subgroup.centralizer ({Λ g} : Set SL(ν, F))) :=
    (Λ.comp (Subgroup.centralizer ({g} : Set G)).subtype).codRestrict _ (by
      rintro ⟨x, hx⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [← map_mul, ← map_mul, hx])
  refine isCyclic_of_injective φ ?_
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply Subtype.ext
  exact hΛ (congrArg Subtype.val h)

end Generic


section Transport

open CFSG.RankThree.PartOne.KE

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}

def frameEmb (D : LangLevi τ K w) : ModGL τ K →* ModGL τ D.L :=
  (MulAut.conj D.g⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K D.L))

theorem frameEmb_injective (D : LangLevi τ K w) : Function.Injective (frameEmb D) :=
  (MulAut.conj D.g⁻¹).injective.comp (baseChangeGL_injective (algebraMap K D.L))

theorem mem_frame_iff' (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ)) (x : ModGL τ K) :
    x ∈ D.frame S ↔ x ∈ adjointGroup τ K ∧ frameEmb D x ∈ rootSpan τ D.L S := by
  unfold LangLevi.frame
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  rfl

theorem entrywise_baseChangeGL (D : LangLevi τ K w) (x : ModGL τ K) :
    Units.map (entrywiseHom D.Fr) (baseChangeGL (algebraMap K D.L) x) =
      baseChangeGL (algebraMap K D.L) x := by
  apply Units.ext
  have hfix : ∀ c : K, D.Fr (algebraMap K D.L c) = algebraMap K D.L c := fun c => by
    rw [D.hFr, ← map_pow]
    congr 1
    haveI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  change entrywise D.Fr (baseChangeEnd (algebraMap K D.L) (x : Module.End K (RootModule τ K))) =
    baseChangeEnd (algebraMap K D.L) (x : Module.End K (RootModule τ K))
  apply Finsupp.lhom_ext'
  intro b
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single, baseChangeEnd_single]
  ext l
  simp [Finsupp.mapRange_apply, hfix]

theorem frameEmb_apply (D : LangLevi τ K w) (x : ModGL τ K) :
    frameEmb D x = D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g := by
  show D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g⁻¹⁻¹ = _
  rw [inv_inv]

theorem frameEmb_twistedFixed (D : LangLevi τ K w) (x : ModGL τ K) :
    frameEmb D x ∈ twistedFixedPoints (canonicalRep (coxeterSystem τ) D.L w)
      (Units.map (entrywiseHom D.Fr)) := by
  rw [mem_twistedFixedPoints, frameEmb_apply, map_mul, map_mul, map_inv, D.lang,
    entrywise_baseChangeGL]
  group

end Transport


section UFrameSec

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2

def UFrame (τ : Tag) (L : Type) [Field L] (ν : ℕ) (S : Set (Fin τ.rank → ℤ)) (n : ModGL τ L) :
    Prop :=
  ∃ (ρ : SL(ν, L) →* ModGL τ L) (r : Fin ν → Fin ν → Fin τ.rank → ℤ) (ε : Fin ν → Fin ν → Lˣ)
    (π : Equiv.Perm (Fin ν)),
    Function.Injective ρ ∧ ρ.range = rootSpan τ L S ∧
    (∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
      ρ (Matrix.SpecialLinearGroup.transvection hij t) =
        pinnedX τ L (r i j) ((ε i j : L) * t)) ∧
    (∀ i j : Fin ν, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n * pinnedX τ L (r i j) c * n⁻¹ = pinnedX τ L (r (π j) (π i)) ((b : L) * c))

theorem UFrame.exists_embedding {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ}
    {S : Set (Fin τ.rank → ℤ)} {n : ModGL τ L} (U : UFrame τ L ν S n)
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L]
    [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) (hν : 3 ≤ ν) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    ∃ (k₂ : Type) (_ : Field k₂) (_ : Finite k₂), Nat.card k₂ = (ℓ ^ f) ^ 2 ∧
      ∃ Λ : ↥(rootSpan τ L S ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr))) →*
        SL(ν, k₂), Function.Injective Λ := by
  classical
  obtain ⟨ρ, r, ε, π, hinj, hrange, hgen, hconj⟩ := U
  have hℓ : ℓ.Prime := Fact.out
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n (τ := τ) (ν := ν) ρ hinj r ε hgen Fr
    hFrbij n (fun i j => (π j, π i)) (fun i j hij => (π.injective.ne hij).symm)
    (fun i j hij => ⟨π.symm j, π.symm i, (π.symm.injective.ne hij).symm, by simp⟩) hconj
  have hshape' : ∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(ν, L)) :
        Matrix (Fin ν) (Fin ν) L) = 1 + Matrix.single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f) :=
    fun i j hij t => by rw [hshape i j hij t, hFr]
  obtain ⟨-, ⟨H, hH⟩, -, -, -⟩ :=
    sln_root_permuting_frobenius_fixed_unitary hℓ hf hk hν π Φ' b hshape'
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  obtain ⟨k₂, hk₂F, hk₂A, hk₂C, hk₂card⟩ :=
    exists_finite_field_isAlgClosure ℓ (2 * f) (by omega) k L
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hk₂fin : Finite k₂ := Nat.finite_of_card_ne_zero (by
    rw [hk₂card]; exact (pow_pos hℓ.pos _).ne')
  have hkc : CharP k₂ ℓ := ⟨fun x => by
    rw [← (algebraMap k₂ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L ℓ x⟩
  set P := rootSpan τ L S ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) with hPdef
  have hPle : P ≤ ρ.range := by rw [hrange]; exact inf_le_left
  let e : SL(ν, L) ≃* ρ.range := MonoidHom.ofInjective hinj
  let Θ₁ : ↥P →* SL(ν, L) := e.symm.toMonoidHom.comp (Subgroup.inclusion hPle)
  have hΘ₁ : ∀ y : ↥P, ρ (Θ₁ y) = y := fun y => by
    have h := e.apply_symm_apply ⟨(y : ModGL τ L), hPle y.2⟩
    exact congrArg Subtype.val h
  have hΘ₁fix : ∀ y : ↥P, Θ₁ y ∈ fixSubgroup Φ' := fun y => by
    apply hinj
    show ρ (Φ' (Θ₁ y)) = ρ (Θ₁ y)
    rw [← hΦ', hΘ₁ y]
    exact mem_twistedFixedPoints.1 y.2.2
  have hΘ₁inj : Function.Injective Θ₁ := fun y₁ y₂ h => by
    apply Subtype.ext
    rw [← hΘ₁ y₁, ← hΘ₁ y₂, h]
  let Λ₀ : ↥P →* SL(ν, L) := (MulAut.conj H⁻¹).toMonoidHom.comp Θ₁
  have hΛ₀ : ∀ y, Λ₀ y = H⁻¹ * Θ₁ y * H := fun y => by
    show H⁻¹ * Θ₁ y * H⁻¹⁻¹ = _
    rw [inv_inv]
  have hΛ₀inj : Function.Injective Λ₀ := (MulAut.conj H⁻¹).injective.comp hΘ₁inj
  have hent : ∀ (y : ↥P) (i j : Fin ν),
      ((Λ₀ y : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) i j ∈ Set.range (algebraMap k₂ L) := by
    intro y i j
    obtain ⟨Y, hY, hXY⟩ := (hH (Θ₁ y)).1 (hΘ₁fix y)
    have h1 : Matrix.SpecialLinearGroup.toGL (Λ₀ y) = Y := by
      rw [hΛ₀, map_mul, map_mul, map_inv, hXY]; group
    have h3 : ((Λ₀ y : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) i j =
        (Y : Matrix (Fin ν) (Fin ν) L) i j := by
      rw [← h1]; rfl
    rw [h3, mem_range_algebraMap_iff hℓ (by omega : 1 ≤ 2 * f) hk₂card, ← hq2]
    exact hY.1 i j
  obtain ⟨Λ, hΛ⟩ := exists_hom_SL_of_map (algebraMap k₂ L).injective Λ₀ hent
  refine ⟨k₂, hk₂F, hk₂fin, by rw [hk₂card, hq2], Λ, fun y₁ y₂ h => hΛ₀inj ?_⟩
  rw [← hΛ y₁, ← hΛ y₂, h]

end UFrameSec


section Assembly

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2

theorem UFrame.of_data {τ : Tag} {L : Type} [Field L] {ν : ℕ} {S : Set (Fin τ.rank → ℤ)}
    (w : WeylGroup τ) (ρ : SL(ν, L) →* ModGL τ L) (hinj : Function.Injective ρ)
    (hrange : ρ.range = rootSpan τ L S) (r : Fin ν → Fin ν → Fin τ.rank → ℤ)
    (hroot : ∀ i j, i ≠ j → IsRoot τ (r i j))
    (hgen : ∀ (i j : Fin ν) (hij : i ≠ j), ∃ ε : Lˣ, ∀ t : L,
      ρ (Matrix.SpecialLinearGroup.transvection hij t) = pinnedX τ L (r i j) ((ε : L) * t))
    (π : Equiv.Perm (Fin ν)) (hπ : ∀ i j, i ≠ j → w • r i j = r (π j) (π i)) :
    UFrame τ L ν S (canonicalRep (coxeterSystem τ) L w) := by
  classical
  choose! ε hε using hgen
  refine ⟨ρ, r, ε, π, hinj, hrange, hε, fun i j hij => ?_⟩
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX (canonicalRep_mem_monomialSubgroup L w) (hroot i j hij)
  have hπw : weylQuotientHom τ L ⟨canonicalRep (coxeterSystem τ) L w,
      canonicalRep_mem_monomialSubgroup L w⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  exact ⟨μ, fun c => by rw [hμ c, hπw, hπ i j hij]⟩

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}

theorem cyclic_of_UFrame (D : LangLevi τ K w) {S : Set (Fin τ.rank → ℤ)} {ν : ℕ} (hν : 3 ≤ ν)
    (U : UFrame τ D.L ν S (canonicalRep (coxeterSystem τ) D.L w)) {p : ℕ} (hp : p.Prime)
    (hord : orderOf (((Nat.card K ^ 2 : ℕ)) : ZMod p) = ν) :
    ∀ g : ↥(D.frame S), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(D.frame S))) := by
  classical
  intro g hg
  obtain ⟨ℓ, hℓK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓp, hcard⟩ := FiniteField.card K ℓ
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  haveI : CharP D.L ℓ := charP_of_injective_algebraMap (algebraMap K D.L).injective ℓ
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hKcard : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hFr : ∀ c, D.Fr c = c ^ (ℓ ^ (f : ℕ)) := fun c => by rw [D.hFr, hKcard]
  obtain ⟨k₂, hk₂F, hk₂fin, hk₂, Λ, hΛ⟩ := U.exists_embedding (ℓ := ℓ) (f := (f : ℕ)) f.pos
    (k := K) hKcard hν D.Fr hFr
  let P := rootSpan τ D.L S ⊓ twistedFixedPoints (canonicalRep (coxeterSystem τ) D.L w)
    (Units.map (entrywiseHom D.Fr))
  let ι : ↥(D.frame S) →* ↥P :=
    ((frameEmb D).comp (D.frame S).subtype).codRestrict P (fun x =>
      ⟨((mem_frame_iff' D S x).1 x.2).2, frameEmb_twistedFixed D x⟩)
  have hι : Function.Injective ι := fun x y h => by
    apply Subtype.ext
    exact frameEmb_injective D (congrArg Subtype.val h)
  haveI := Fintype.ofFinite k₂
  have hk₂c : Fintype.card k₂ = Nat.card K ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hk₂, hKcard]
  exact isCyclic_centralizer_of_injective_hom hp (by omega) (by rw [hk₂c]; exact hord)
    (Λ.comp ι) (hΛ.comp hι) hg

end Assembly


section Classes

open Matrix CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KF4 CFSG.RankThree.E6
  CFSG.LieType.Steinberg.Adjoint

theorem f4_short_support : ∀ m : Fin 48,
    (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → f4RootVec m i = 0) →
      ∃ i j : Fin 3, i ≠ j ∧ f4RootVec m = f4ShortSigma i j := by
  decide +kernel

theorem f4_short_roots : ∀ i j : Fin 3, i ≠ j →
    (∃ m : Fin 48, f4RootVec m = f4ShortSigma i j) ∧
      ∀ k : Fin Tag.F4.rank, k.val ∉ TwClass.f4Six.J₂ → f4ShortSigma i j k = 0 := by
  decide +kernel

theorem f4Six_S₂_mem_iff {r : Fin Tag.F4.rank → ℤ} :
    r ∈ TwClass.f4Six.S₂ ↔ ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j := by
  constructor
  · rintro ⟨hr, hz⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hr
    exact f4_short_support m hz
  · rintro ⟨i, j, hij, rfl⟩
    obtain ⟨⟨m, hm⟩, hz⟩ := f4_short_roots i j hij
    exact ⟨isRoot_iff_exists_f4RootVec.2 ⟨m, hm⟩, hz⟩

theorem f4_long_orth : ∀ m : Fin 48,
    (∀ i j : Fin 3, i ≠ j → iform (τ := Tag.F4) (f4RootVec m) (f4ShortSigma i j) = 0) →
      ∃ i j : Fin 3, i ≠ j ∧
        f4RootVec m = wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong i j := by
  decide +kernel

theorem f4_long_roots : ∀ i j : Fin 3, i ≠ j →
    (∃ m : Fin 48, f4RootVec m = wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong i j) ∧
      ∀ i' j' : Fin 3, i' ≠ j' →
        iform (τ := Tag.F4) (wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong i j)
          (f4ShortSigma i' j') = 0 := by
  decide +kernel

theorem f4Six_S₁_mem_iff {r : Fin Tag.F4.rank → ℤ} :
    r ∈ TwClass.f4Six.S₁ ↔
      ∃ i j : Fin 3, i ≠ j ∧ r = wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong i j := by
  constructor
  · rintro ⟨hr, ho⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hr
    exact f4_long_orth m fun i j hij => ho _ (f4Six_S₂_mem_iff.2 ⟨i, j, hij, rfl⟩)
  · rintro ⟨i, j, hij, rfl⟩
    obtain ⟨⟨m, hm⟩, ho⟩ := f4_long_roots i j hij
    refine ⟨isRoot_iff_exists_f4RootVec.2 ⟨m, hm⟩, fun α hα => ?_⟩
    obtain ⟨i', j', hij', rfl⟩ := f4Six_S₂_mem_iff.1 hα
    exact ho i' j' hij'

theorem f4_short_graph : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.F4 TwClass.wordF4 *ᵥ f4ShortSigma i j =
      f4ShortSigma (Equiv.swap (0 : Fin 3) 2 j) (Equiv.swap (0 : Fin 3) 2 i) := by
  decide +kernel

theorem f4_long_graph : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.F4 TwClass.wordF4 *ᵥ (wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong i j) =
      wordMat Tag.F4 f4LongWord *ᵥ
        chainRoot f4chainLong (Equiv.swap (0 : Fin 3) 2 j) (Equiv.swap (0 : Fin 3) 2 i) := by
  decide +kernel

theorem f4Six_UFrame₂ (L : Type) [Field L] :
    UFrame Tag.F4 L 3 TwClass.f4Six.S₂
      (canonicalRep (coxeterSystem Tag.F4) L TwClass.f4Six.w) := by
  have hS : (TwClass.f4Six.S₂ : Set (Fin Tag.F4.rank → ℤ)) =
      {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j} :=
    Set.ext fun r => f4Six_S₂_mem_iff
  rw [hS]
  have h := f4Short_frame (L := L)
  refine UFrame.of_data TwClass.f4Six.w _ h.injective h.range f4ShortSigma h.isRoot h.transv
    (Equiv.swap 0 2) (fun i j hij => ?_)
  show (coxeterSystem Tag.F4).wordProd TwClass.wordF4 • f4ShortSigma i j =
    f4ShortSigma (Equiv.swap (0 : Fin 3) 2 j) (Equiv.swap (0 : Fin 3) 2 i)
  rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
  exact f4_short_graph i j hij

theorem f4Six_UFrame₁ (L : Type) [Field L] :
    UFrame Tag.F4 L 3 TwClass.f4Six.S₁
      (canonicalRep (coxeterSystem Tag.F4) L TwClass.f4Six.w) := by
  have hS : (TwClass.f4Six.S₁ : Set (Fin Tag.F4.rank → ℤ)) =
      {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4LongV • chainRoot f4chainLong i j} := by
    ext r
    refine f4Six_S₁_mem_iff.trans ?_
    show _ ↔ ∃ i j : Fin 3, i ≠ j ∧ r = f4LongV • chainRoot f4chainLong i j
    simp only [f4LongV_smul]
    exact Iff.rfl
  rw [hS]
  have h := (f4Long_frame (L := L)).transport f4LongV
  refine UFrame.of_data TwClass.f4Six.w _ h.injective h.range _ h.isRoot h.transv
    (Equiv.swap 0 2) (fun i j hij => ?_)
  show (coxeterSystem Tag.F4).wordProd TwClass.wordF4 •
      (f4LongV • chainRoot f4chainLong i j) =
    f4LongV • chainRoot f4chainLong (Equiv.swap (0 : Fin 3) 2 j) (Equiv.swap (0 : Fin 3) 2 i)
  rw [f4LongV_smul, f4LongV_smul, CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
  exact f4_long_graph i j hij

theorem planeCyclic_f4Six (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) {p : ℕ} (hp : p.Prime)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = TwClass.f4Six.e) :
    (∀ g : ↥(TwClass.f4Six.X₁ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.f4Six.X₁ D)))) ∧
    (∀ g : ↥(TwClass.f4Six.X₂ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.f4Six.X₂ D)))) := by
  have h2 : orderOf (((Nat.card K ^ 2 : ℕ)) : ZMod p) = 3 := by
    rw [Nat.cast_pow, orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), hord]
    change 6 / Nat.gcd 6 2 = 3
    norm_num
  exact ⟨cyclic_of_UFrame D (by norm_num) (f4Six_UFrame₁ D.L) hp h2,
    cyclic_of_UFrame D (by norm_num) (f4Six_UFrame₂ D.L) hp h2⟩


@[expose] def e6WordV : List (Fin Tag.E6.rank) := [3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3]

theorem e6_S₂_support : ∀ m : Fin 72,
    (∀ i : Fin Tag.E6.rank, i.val ∉ TwClass.e6Six.J₂ → e6RootVec m i = 0) →
      (∃ i j : Fin 3, i ≠ j ∧ e6RootVec m = chainRoot chain13 i j) ∨
        ∃ i j : Fin 3, i ≠ j ∧ e6RootVec m = chainRoot chain56 i j := by
  decide +kernel

theorem e6_S₂_roots : ∀ i j : Fin 3, i ≠ j →
    ((∃ m : Fin 72, e6RootVec m = chainRoot chain13 i j) ∧
      ∀ k : Fin Tag.E6.rank, k.val ∉ TwClass.e6Six.J₂ → chainRoot chain13 i j k = 0) ∧
    ((∃ m : Fin 72, e6RootVec m = chainRoot chain56 i j) ∧
      ∀ k : Fin Tag.E6.rank, k.val ∉ TwClass.e6Six.J₂ → chainRoot chain56 i j k = 0) := by
  decide +kernel

theorem e6Six_S₂_mem_iff {r : Fin Tag.E6.rank → ℤ} :
    r ∈ TwClass.e6Six.S₂ ↔ (∃ i j : Fin 3, i ≠ j ∧ r = chainRoot chain13 i j) ∨
      ∃ i j : Fin 3, i ≠ j ∧ r = chainRoot chain56 i j := by
  constructor
  · rintro ⟨hr, hz⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hr
    exact e6_S₂_support m hz
  · rintro (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · obtain ⟨⟨⟨m, hm⟩, hz⟩, -⟩ := e6_S₂_roots i j hij
      exact ⟨isRoot_iff_exists_e6RootVec.2 ⟨m, hm⟩, hz⟩
    · obtain ⟨-, ⟨⟨m, hm⟩, hz⟩⟩ := e6_S₂_roots i j hij
      exact ⟨isRoot_iff_exists_e6RootVec.2 ⟨m, hm⟩, hz⟩

theorem e6_S₁_orth : ∀ m : Fin 72,
    (∀ i j : Fin 3, i ≠ j → iform (τ := Tag.E6) (e6RootVec m) (chainRoot chain13 i j) = 0 ∧
      iform (τ := Tag.E6) (e6RootVec m) (chainRoot chain56 i j) = 0) →
      ∃ i j : Fin 3, i ≠ j ∧
        e6RootVec m = wordMat Tag.E6 e6WordV *ᵥ chainRoot chain13 i j := by
  decide +kernel

theorem e6_S₁_roots : ∀ i j : Fin 3, i ≠ j →
    (∃ m : Fin 72, e6RootVec m = wordMat Tag.E6 e6WordV *ᵥ chainRoot chain13 i j) ∧
      ∀ i' j' : Fin 3, i' ≠ j' →
        iform (τ := Tag.E6) (wordMat Tag.E6 e6WordV *ᵥ chainRoot chain13 i j)
          (chainRoot chain13 i' j') = 0 ∧
        iform (τ := Tag.E6) (wordMat Tag.E6 e6WordV *ᵥ chainRoot chain13 i j)
          (chainRoot chain56 i' j') = 0 := by
  decide +kernel

theorem e6Six_S₁_mem_iff {r : Fin Tag.E6.rank → ℤ} :
    r ∈ TwClass.e6Six.S₁ ↔
      ∃ i j : Fin 3, i ≠ j ∧ r = wordMat Tag.E6 e6WordV *ᵥ chainRoot chain13 i j := by
  constructor
  · rintro ⟨hr, ho⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hr
    refine e6_S₁_orth m fun i j hij => ⟨ho _ (e6Six_S₂_mem_iff.2 (Or.inl ⟨i, j, hij, rfl⟩)),
      ho _ (e6Six_S₂_mem_iff.2 (Or.inr ⟨i, j, hij, rfl⟩))⟩
  · rintro ⟨i, j, hij, rfl⟩
    obtain ⟨⟨m, hm⟩, ho⟩ := e6_S₁_roots i j hij
    refine ⟨isRoot_iff_exists_e6RootVec.2 ⟨m, hm⟩, fun α hα => ?_⟩
    rcases e6Six_S₂_mem_iff.1 hα with ⟨i', j', hij', rfl⟩ | ⟨i', j', hij', rfl⟩
    · exact (ho i' j' hij').1
    · exact (ho i' j' hij').2

theorem e6_graph : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ (wordMat Tag.E6 e6WordV *ᵥ chainRoot chain13 i j) =
      wordMat Tag.E6 e6WordV *ᵥ chainRoot chain13 (Fin.revPerm j) (Fin.revPerm i) := by
  decide +kernel

theorem e6Six_UFrame₁ (L : Type) [Field L] :
    UFrame Tag.E6 L 3 TwClass.e6Six.S₁
      (canonicalRep (coxeterSystem Tag.E6) L TwClass.e6Six.w) := by
  set e6V : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd e6WordV with he6V
  set E := CFSG.RankThree.PartOne.TCX.E.A2Std.embedding
    CFSG.RankThree.PartOne.TCX.E.a2Std₁ e6V with hE
  have hS : (TwClass.e6Six.S₁ : Set (Fin Tag.E6.rank → ℤ)) =
      (fun γ => e6V • γ) '' parabolicRoots Tag.E6 support13 := by
    ext r
    refine e6Six_S₁_mem_iff.trans ?_
    refine Iff.trans ?_ (E.mem r).symm
    show _ ↔ ∃ i j : Fin 3, i ≠ j ∧ r = e6V • chainRoot chain13 i j
    simp only [he6V, CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
    exact Iff.rfl
  rw [hS]
  refine UFrame.of_data TwClass.e6Six.w (E.ρ L) (E.inj L) (E.range L) E.r E.isRoot (E.gen L)
    Fin.revPerm (fun i j hij => ?_)
  show (coxeterSystem Tag.E6).wordProd TwClass.wordE6 • (e6V • chainRoot chain13 i j) =
    e6V • chainRoot chain13 (Fin.revPerm j) (Fin.revPerm i)
  simp only [he6V, CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
  exact e6_graph i j hij

theorem planeCyclic_e6Six_X₁ (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) {p : ℕ} (hp : p.Prime)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = TwClass.e6Six.e) :
    ∀ g : ↥(TwClass.e6Six.X₁ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e6Six.X₁ D))) := by
  have h2 : orderOf (((Nat.card K ^ 2 : ℕ)) : ZMod p) = 3 := by
    rw [Nat.cast_pow, orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), hord]
    change 6 / Nat.gcd 6 2 = 3
    norm_num
  exact cyclic_of_UFrame D (by norm_num) (e6Six_UFrame₁ D.L) hp h2

end Classes

section E8Ten

open Matrix CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 (chainRoot)


theorem sigmaSetE8A4_e8VA : sigmaSetE8A4 e8VA = {r | r ∈ e8ListA} := by
  rw [sigmaSetE8A4_eq]
  ext r
  simp only [Set.mem_ofPred_eq, sigmaRootE8A4_eq_smul, e8VA_smul]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact e8A_img i j hij
  · intro hr
    obtain ⟨i, j, hij, h⟩ := e8A_cover r hr
    exact ⟨i, j, hij, h⟩

theorem sigmaSetE8A4_e8VB : sigmaSetE8A4 e8VB = {r | r ∈ e8ListB} := by
  rw [sigmaSetE8A4_eq]
  ext r
  simp only [Set.mem_ofPred_eq, sigmaRootE8A4_eq_smul, e8VB_smul]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact e8B_img i j hij
  · intro hr
    obtain ⟨i, j, hij, h⟩ := e8B_cover r hr
    exact ⟨i, j, hij, h⟩

theorem e8Ten_S₂_support : ∀ m : Fin 240,
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → e8RootVec m i = 0) →
      e8RootVec m ∈ e8ListA := by
  decide +kernel

theorem e8Ten_S₂_roots : ∀ r ∈ e8ListA,
    (∃ m : Fin 240, e8RootVec m = r) ∧
      ∀ k : Fin Tag.E8.rank, k.val ∉ TwClass.e8Ten.J₂ → r k = 0 := by
  decide +kernel

theorem e8Ten_S₂_mem_iff {r : Fin Tag.E8.rank → ℤ} : r ∈ TwClass.e8Ten.S₂ ↔ r ∈ e8ListA := by
  constructor
  · rintro ⟨hr, hz⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    exact e8Ten_S₂_support m hz
  · intro hr
    obtain ⟨⟨m, hm⟩, hz⟩ := e8Ten_S₂_roots r hr
    exact ⟨isRoot_iff_exists_e8RootVec.2 ⟨m, hm⟩, hz⟩

theorem e8Ten_S₁_orth : ∀ m : Fin 240,
    (∀ α ∈ e8ListA, iform (τ := Tag.E8) (e8RootVec m) α = 0) → e8RootVec m ∈ e8ListB := by
  decide +kernel

theorem e8Ten_S₁_roots : ∀ β ∈ e8ListB,
    (∃ m : Fin 240, e8RootVec m = β) ∧ ∀ α ∈ e8ListA, iform (τ := Tag.E8) β α = 0 := by
  decide +kernel

theorem e8Ten_S₁_mem_iff {r : Fin Tag.E8.rank → ℤ} : r ∈ TwClass.e8Ten.S₁ ↔ r ∈ e8ListB := by
  constructor
  · rintro ⟨hr, ho⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    exact e8Ten_S₁_orth m fun α hα => ho _ (e8Ten_S₂_mem_iff.2 hα)
  · intro hr
    obtain ⟨⟨m, hm⟩, ho⟩ := e8Ten_S₁_roots r hr
    exact ⟨isRoot_iff_exists_e8RootVec.2 ⟨m, hm⟩, fun α hα => ho α (e8Ten_S₂_mem_iff.1 hα)⟩

theorem e8Ten_graphA : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 TwClass.wordE8Ten *ᵥ (wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain (Fin.revPerm j) (Fin.revPerm i) := by
  decide +kernel

theorem e8Ten_graphB : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 TwClass.wordE8Ten *ᵥ (wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain (Fin.revPerm j) (Fin.revPerm i) := by
  decide +kernel

theorem e8Ten_UFrame₂ (L : Type) [Field L] :
    UFrame Tag.E8 L 5 TwClass.e8Ten.S₂
      (canonicalRep (coxeterSystem Tag.E8) L TwClass.e8Ten.w) := by
  have hS : (TwClass.e8Ten.S₂ : Set (Fin Tag.E8.rank → ℤ)) = sigmaSetE8A4 e8VA := by
    rw [sigmaSetE8A4_e8VA]
    exact Set.ext fun r => e8Ten_S₂_mem_iff
  rw [hS]
  refine UFrame.of_data TwClass.e8Ten.w (rhoSigmaE8A4 L e8VA) (rhoSigmaE8A4_injective e8VA)
    (rhoSigmaE8A4_range e8VA) (sigmaRootE8A4 e8VA)
    (fun i j hij => isRoot_sigmaRootE8A4 e8VA hij)
    (fun i j hij => rhoSigmaE8A4_transvection (L := L) e8VA i j hij) Fin.revPerm
    (fun i j hij => ?_)
  show (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • sigmaRootE8A4 e8VA i j =
    sigmaRootE8A4 e8VA (Fin.revPerm j) (Fin.revPerm i)
  simp only [sigmaRootE8A4_eq_smul, e8VA_smul, CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
  exact e8Ten_graphA i j hij

theorem e8Ten_UFrame₁ (L : Type) [Field L] :
    UFrame Tag.E8 L 5 TwClass.e8Ten.S₁
      (canonicalRep (coxeterSystem Tag.E8) L TwClass.e8Ten.w) := by
  have hS : (TwClass.e8Ten.S₁ : Set (Fin Tag.E8.rank → ℤ)) = sigmaSetE8A4 e8VB := by
    rw [sigmaSetE8A4_e8VB]
    exact Set.ext fun r => e8Ten_S₁_mem_iff
  rw [hS]
  refine UFrame.of_data TwClass.e8Ten.w (rhoSigmaE8A4 L e8VB) (rhoSigmaE8A4_injective e8VB)
    (rhoSigmaE8A4_range e8VB) (sigmaRootE8A4 e8VB)
    (fun i j hij => isRoot_sigmaRootE8A4 e8VB hij)
    (fun i j hij => rhoSigmaE8A4_transvection (L := L) e8VB i j hij) Fin.revPerm
    (fun i j hij => ?_)
  show (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • sigmaRootE8A4 e8VB i j =
    sigmaRootE8A4 e8VB (Fin.revPerm j) (Fin.revPerm i)
  simp only [sigmaRootE8A4_eq_smul, e8VB_smul, CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
  exact e8Ten_graphB i j hij

theorem planeCyclic_e8Ten (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) {p : ℕ} (hp : p.Prime)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = TwClass.e8Ten.e) :
    (∀ g : ↥(TwClass.e8Ten.X₁ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e8Ten.X₁ D)))) ∧
    (∀ g : ↥(TwClass.e8Ten.X₂ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e8Ten.X₂ D)))) := by
  have h2 : orderOf (((Nat.card K ^ 2 : ℕ)) : ZMod p) = 5 := by
    rw [Nat.cast_pow, orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), hord]
    change 10 / Nat.gcd 10 2 = 5
    norm_num
  exact ⟨cyclic_of_UFrame D (by norm_num) (e8Ten_UFrame₁ D.L) hp h2,
    cyclic_of_UFrame D (by norm_num) (e8Ten_UFrame₂ D.L) hp h2⟩

end E8Ten

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PlaneCyclic
