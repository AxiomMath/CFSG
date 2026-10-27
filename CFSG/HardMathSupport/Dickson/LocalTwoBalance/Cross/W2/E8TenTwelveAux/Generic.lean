module

public import CFSG.RankThree.PartOne.KE.E8PerXCore
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4FourAux.Layer
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.LocalTwo
open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false


section Rigid

@[expose] def E8RigidAt (K : Type) [Field K] {L : Type} [Field L] [Algebra K L]
    (n : ModGL Tag.E8 L) (Fr : L →+* L) (p : ℕ) (b : Fin Tag.E8.rank → Lˣ) : Prop :=
  ∃ P : Subgroup (ModGL Tag.E8 L),
    IsSigmaFamily n Fr (rootCharKernel b) (fun _ : Unit => P) ∧
    P = rootSpan Tag.E8 L (rootCharKernel b) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
    (∃ (i : Fin Tag.E8.rank) (h₀ : ModGL Tag.E8 L), ∀ Y : SL2 K,
      h₀ * simpleRootSL2 Tag.E8 L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈
        P) ∧
    ¬ Nat.Coprime p (Nat.card P)


theorem e8_inner_of_fixes_derived (K : Type) [Field K] [Finite K] (M : Type) [Field M]
    [Algebra K M] {x : adjointGroup .E8 K}
    (i : Fin Tag.E8.rank) (A : GL (Fin 2) M) (h : ModGL .E8 M)
    (hU : ∀ Y : SL2 K, h * simpleRootSL2 .E8 M i (conjGL A
        (Matrix.SpecialLinearGroup.map (algebraMap K M) Y)) * h⁻¹ ∈
          (adjointGroup .E8 K).map (baseChangeGL (algebraMap K M)))
    (hmem : ∀ (u : adjointGroup .E8 K) (Y : SL2 K),
      baseChangeGL (algebraMap K M) (u : ModGL .E8 K) =
        h * simpleRootSL2 .E8 M i (conjGL A
          (Matrix.SpecialLinearGroup.map (algebraMap K M) Y)) * h⁻¹ →
        u ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
          Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))⁆ :
            Subgroup (adjointGroup .E8 K)))
    (η : MulAut (adjointGroup .E8 K))
    (hη : ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))⁆ :
          Subgroup (adjointGroup .E8 K)), η d = d) :
    η ∈ inner (adjointGroup .E8 K) := by
  let Z : Subgroup (MulAut (adjointGroup .E8 K)) :=
    { carrier := {η | ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))⁆ :
          Subgroup (adjointGroup .E8 K)), η d = d}
      mul_mem' := fun {a b} ha hb d hd => by
        rw [MulAut.mul_apply, hb d hd, ha d hd]
      one_mem' := fun d _ => rfl
      inv_mem' := fun {a} ha d hd => by
        have := ha d hd
        calc a⁻¹ d = a⁻¹ (a d) := by rw [this]
          _ = d := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl }
  have hZ : ∀ η' ∈ Z, ∀ (u : adjointGroup .E8 K) (Y : SL2 K),
      baseChangeGL (algebraMap K M) (u : ModGL .E8 K) =
        h * simpleRootSL2 .E8 M i (conjGL A
          (Matrix.SpecialLinearGroup.map (algebraMap K M) Y)) * h⁻¹ → η' u = u :=
    fun η' hη'Z u Y hu => hη'Z u (hmem u Y hu)
  exact (ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free .E8
    (Or.inr (Or.inr rfl)) K M i A h hU Z hZ).2.2.2 rfl η hη

theorem e8_inner_of_embedding (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L]
    {x : adjointGroup .E8 K} (c : adjointGroup .E8 K) (g0 : ModGL .E8 L)
    (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) →* ModGL .E8 L)
    (hψinj : Function.Injective ψ)
    (hψ : ∀ y, ψ y = g0⁻¹ * adjEmb .E8 K L (c * (y : adjointGroup .E8 K) * c⁻¹) * g0)
    {Pt : Subgroup (ModGL .E8 L)} (hPq : CFSG.IsQuasisimple Pt) (hcomm : ⁅ψ.range, ψ.range⁆ = Pt)
    (i : Fin Tag.E8.rank) (h₀ : ModGL .E8 L)
    (hh₀ : ∀ Y : SL2 K, h₀ * simpleRootSL2 .E8 L i
      (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt)
    (η : MulAut (adjointGroup .E8 K))
    (hη : ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))⁆ :
          Subgroup (adjointGroup .E8 K)), η d = d) :
    η ∈ inner (adjointGroup .E8 K) := by
  obtain ⟨hq, h2, h1⟩ := isQuasisimple_commutator_of_embedding ψ hψinj hPq hcomm
  set h'' : ModGL .E8 L := (adjEmb .E8 K L c)⁻¹ * g0 * h₀ with hh''
  have hKey : ∀ Y : SL2 K, ∃ y ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))⁆ : Subgroup (adjointGroup .E8 K)),
        adjEmb .E8 K L y = h'' * simpleRootSL2 .E8 L i
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹ := by
    intro Y
    have hmem := hh₀ Y
    rw [← h2] at hmem
    obtain ⟨y', hy', hy'ψ⟩ := hmem
    refine ⟨(y' : adjointGroup .E8 K), ?_, ?_⟩
    · rw [← h1]
      exact ⟨y', hy', rfl⟩
    · have h3 := hψ y'
      rw [hy'ψ] at h3
      have h4 : adjEmb .E8 K L (c * (y' : adjointGroup .E8 K) * c⁻¹) =
          g0 * (h₀ * simpleRootSL2 .E8 L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) *
            h₀⁻¹) * g0⁻¹ := by
        rw [h3]
        group
      rw [map_mul, map_mul, map_inv] at h4
      rw [hh'']
      calc adjEmb .E8 K L (y' : adjointGroup .E8 K)
          = (adjEmb .E8 K L c)⁻¹ * (adjEmb .E8 K L c * adjEmb .E8 K L (y' : adjointGroup .E8 K) *
              (adjEmb .E8 K L c)⁻¹) * adjEmb .E8 K L c := by group
        _ = _ := by rw [h4]; group
  refine e8_inner_of_fixes_derived K L (x := x) i 1 h'' (fun Y => ?_) (fun u Y hu => ?_) η hη
  · obtain ⟨y, -, hy⟩ := hKey Y
    rw [conjGL_one, ← hy]
    exact ⟨(y : ModGL .E8 K), y.2, rfl⟩
  · obtain ⟨y, hyD, hy⟩ := hKey Y
    rw [conjGL_one, ← hy] at hu
    have hu' : adjEmb .E8 K L u = adjEmb .E8 K L y := by rw [adjEmb_apply, hu]
    rw [adjEmb_injective hu']
    exact hyD


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem innerPlaneBalance_adjointE8_of_rigid (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E8))
    (n g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    (hconj : ∀ A : Subgroup (adjointGroup Tag.E8 K), IsPGroup p A →
      ∃ c : adjointGroup Tag.E8 K, ∀ x ∈ A, g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 ∈
        twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (β : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ) (hβroot : ∀ j, IsRoot Tag.E8 (β j))
    (hβspan : Submodule.span ℤ (Set.range β) = ⊤)
    (hrigid : ∀ b : Fin Tag.E8.rank → Lˣ,
      rootDiagUnit Tag.E8 b ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      (∀ i, b i ^ p = 1) → b ≠ 1 → (∃ j, β j ∈ rootCharKernel b) →
      E8RigidAt K n (iterateFrobenius L ℓ f) p b) :
    InnerPlaneBalance p (adjointGroup Tag.E8 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  intro E hEin hE hcard H hH
  have hC : Subgroup.center (adjointGroup Tag.E8 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup Tag.E8 K) :=
    E.comap (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup Tag.E8 K →*
      MulAut (adjointGroup Tag.E8 K)) = E := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hEin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  have hpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => hE.2 a ha
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    apply hIntinj
    rw [map_pow, map_one]
    exact hpow _ hq
  let φ : A₀ →* ModGL Tag.E8 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb Tag.E8 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * adjEmb Tag.E8 K L (c * (q : adjointGroup Tag.E8 K) * c⁻¹) * g0 := fun q => by
    simp [φ, MulAut.conj_apply]
  have hφinj : Function.Injective φ := by
    intro q q' h
    rw [hφ, hφ] at h
    have h1 := mul_left_cancel (mul_right_cancel h)
    have h2 := adjEmb_injective h1
    have h3 : (q : adjointGroup Tag.E8 K) = q' := by
      have := congrArg (fun z => c⁻¹ * z * c) h2
      simpa [mul_assoc] using this
    exact Subtype.ext h3
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf n (Units.map (entrywiseHom Fr)) := fun q => by
    rw [hφ]
    exact hc q q.2
  choose βt hβt using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E8.rank → Lˣ, φ q = rootDiagUnit Tag.E8 b)
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E8 L) := rootDiagUnit_injective
  have hβtmul : ∀ q q' : A₀, βt (q * q') = βt q * βt q' := fun q q' => by
    apply rootDiagUnit_injective (τ := Tag.E8) (K := L)
    rw [← hβt, rootDiagUnit_mul, ← hβt, ← hβt, map_mul]
  have hβtone : βt 1 = 1 := by
    apply rootDiagUnit_injective (τ := Tag.E8) (K := L)
    rw [← hβt, map_one, rootDiagUnit_one]
  have hβtp : ∀ q : A₀, ∀ i, βt q i ^ p = 1 := fun q i => by
    have h1 : rootDiagUnit Tag.E8 (βt q) ^ p = 1 := by
      rw [← hβt, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [this, map_one]
    have h2 : βt q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  have hβtne : ∀ q : A₀, q ≠ 1 → βt q ≠ 1 := fun q hq h => by
    apply hq
    apply hφinj
    rw [hβt, h, rootDiagUnit_one, map_one]
  have hcov : ∀ j : Fin Tag.E8.rank, ∃ q : A₀, q ≠ 1 ∧ β j ∈ rootCharKernel (βt q) := by
    intro j
    let χ : A₀ →* Lˣ :=
      { toFun := fun q => rootChar (βt q) (β j)
        map_one' := by rw [hβtone]; exact CTTorus.rootChar_one (β j)
        map_mul' := fun q q' => by rw [hβtmul, CTTorus.rootChar_mul] }
    have hχp : ∀ q : A₀, χ q ^ p = 1 := fun q => by
      rw [← map_pow]
      have h3 : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [h3, map_one]
    obtain ⟨q₀, hq₀1, hq₀χ⟩ := exists_ne_one_ker_of_card_sq hp hA₀card χ hχp
    exact ⟨q₀, hq₀1, hβroot j, hq₀χ⟩
  choose xj hxj1 hxjk using hcov
  have hxjC : ∀ j, (xj j : adjointGroup Tag.E8 K) ≠ 1 := fun j h => hxj1 j (Subtype.ext h)
  have hxjp : ∀ j, orderOf (xj j : adjointGroup Tag.E8 K) = p := fun j =>
    orderOf_eq_prime (hA₀exp _ (xj j).2) (hxjC j)
  have hhj : ∀ j, g0⁻¹ * adjEmb Tag.E8 K L (c * (xj j : adjointGroup Tag.E8 K) * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom Fr)) := fun j => hc _ (xj j).2
  have hbhj : ∀ j, rootDiagUnit Tag.E8 (βt (xj j)) =
      g0⁻¹ * adjEmb Tag.E8 K L (c * (xj j : adjointGroup Tag.E8 K) * c⁻¹) * g0 := fun j => by
    rw [← hβt, hφ]
  have hrj : ∀ j, E8RigidAt K n Fr p (βt (xj j)) := fun j =>
    hrigid _ (by rw [hbhj j]; exact hhj j) (hβtp _) (hβtne _ (hxj1 j)) ⟨j, hxjk j⟩
  choose P hfam hP1 hsl hpdvd using hrj
  have hS : ∀ j, ∀ α ∈ rootCharKernel (βt (xj j)), IsRoot Tag.E8 α := fun j α hα => hα.1
  have hSn : ∀ j, ∀ α ∈ rootCharKernel (βt (xj j)), -α ∈ rootCharKernel (βt (xj j)) :=
    fun j α hα => ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  have hemb := fun j => e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp hordW (hxjp j) c (hbhj j)
    (hhj j) rfl (hS j) (hSn j) (hfam j)
  choose ψ hψinj hψ hψHQ hψR hψadj hPψ hψV using hemb
  have hcomm : ∀ j, ⁅(ψ j).range, (ψ j).range⁆ = P j := fun j =>
    e8_perx_commutator Fr n (hS j) (ψ j) (hψHQ j) (hψR j) (hP1 j) (hPψ j ())
      ((hfam j).2.1 ())
  have hlayer := fun j => isQuasisimple_commutator_of_embedding (ψ j) (hψinj j) (P := P j)
    ((hfam j).2.1 ()) (hcomm j)
  have hDq : ∀ j, CFSG.IsQuasisimple (⁅Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} :
      Set (adjointGroup Tag.E8 K)), Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} :
        Set (adjointGroup Tag.E8 K))⁆ : Subgroup (adjointGroup Tag.E8 K)) := fun j =>
    (hlayer j).1
  have hDp : ∀ j, ¬ Nat.Coprime p (Nat.card (⁅Subgroup.centralizer
      ({(xj j : adjointGroup Tag.E8 K)} : Set (adjointGroup Tag.E8 K)),
      Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} :
        Set (adjointGroup Tag.E8 K))⁆ : Subgroup (adjointGroup Tag.E8 K))) := by
    intro j
    obtain ⟨-, h2, h1⟩ := hlayer j
    set T' : Subgroup (Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} :
      Set (adjointGroup Tag.E8 K))) := ⁅(⊤ : Subgroup (Subgroup.centralizer
        ({(xj j : adjointGroup Tag.E8 K)} : Set (adjointGroup Tag.E8 K)))), ⊤⁆ with hT'
    have hcPt : Nat.card (P j) = Nat.card T' := by
      rw [← h2]
      exact Subgroup.card_map_of_injective (hψinj j)
    have hcD : Nat.card (⁅Subgroup.centralizer
        ({(xj j : adjointGroup Tag.E8 K)} : Set (adjointGroup Tag.E8 K)),
        Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} :
          Set (adjointGroup Tag.E8 K))⁆ : Subgroup (adjointGroup Tag.E8 K)) = Nat.card T' := by
      rw [← h1]
      exact Subgroup.card_map_of_injective (Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} :
        Set (adjointGroup Tag.E8 K))).subtype_injective
    rw [hcD, ← hcPt]
    exact hpdvd j
  refine eq_bot_iff.2 fun z hz => ?_
  have hbE : ∀ j, (MulAut.conj (xj j : adjointGroup Tag.E8 K) : MulAut (adjointGroup Tag.E8 K)) ∈ E :=
    fun j => (xj j).2
  have hfix := fun j => fixes_of_mem_localDeltaIn hp hIntinj hH hz (hbE j) (hxjC j) (hDq j) (hDp j)
  have j0 : Fin Tag.E8.rank := ⟨0, by decide⟩
  obtain ⟨i0, h₀, hh₀⟩ := hsl j0
  have hzin := e8_inner_of_embedding K L c g0 (ψ j0) (hψinj j0) (hψ j0) ((hfam j0).2.1 ())
    (hcomm j0) i0 h₀ hh₀ z (hfix j0).2
  obtain ⟨c', hc'⟩ := hzin
  have hc'x : ∀ j, c' ∈ Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} :
      Set (adjointGroup Tag.E8 K)) := fun j => by
    have h := (hfix j).1
    rw [← hc'] at h
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' : c' * (xj j : adjointGroup Tag.E8 K) * c'⁻¹ = (xj j : adjointGroup Tag.E8 K) := h
    calc c' * (xj j : adjointGroup Tag.E8 K) = (c' * (xj j : adjointGroup Tag.E8 K) * c'⁻¹) * c' := by
          group
      _ = (xj j : adjointGroup Tag.E8 K) * c' := by rw [h']
  have hc'D : ∀ j, ∀ r ∈ (⁅Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} :
      Set (adjointGroup Tag.E8 K)), Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} :
        Set (adjointGroup Tag.E8 K))⁆ : Subgroup (adjointGroup Tag.E8 K)),
      c' * r * c'⁻¹ = r := fun j r hr => by
    have h := (hfix j).2 r hr
    rw [← hc'] at h
    exact h
  set m : ModGL Tag.E8 L := g0⁻¹ * adjEmb Tag.E8 K L (c * c' * c⁻¹) * g0 with hm
  have hψm : ∀ j, ψ j ⟨c', hc'x j⟩ = m := fun j => by
    rw [hψ j]
  have hmHQ : ∀ j, m ∈ torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (rootCharKernel (βt (xj j))) :=
    fun j => by
      rw [← hψm j]
      exact hψHQ j _
  have hmR : ∀ j, m ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) := fun j => by
    rw [mem_twistedFixedPoints, ← hψm j]
    exact hψR j _
  have hmcomm : ∀ j, ∀ i : Unit, ∀ u ∈ (fun _ : Unit => P j) i, m * u = u * m := by
    intro j _ u hu
    obtain ⟨-, h2, h1⟩ := hlayer j
    set T' : Subgroup (Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} :
      Set (adjointGroup Tag.E8 K))) := ⁅(⊤ : Subgroup (Subgroup.centralizer
        ({(xj j : adjointGroup Tag.E8 K)} : Set (adjointGroup Tag.E8 K)))), ⊤⁆ with hT'
    have hu' : u ∈ T'.map (ψ j) := by
      rw [h2]
      exact hu
    obtain ⟨d', hd', rfl⟩ := hu'
    have hdD : (d' : adjointGroup Tag.E8 K) ∈ (⁅Subgroup.centralizer
        ({(xj j : adjointGroup Tag.E8 K)} : Set (adjointGroup Tag.E8 K)),
        Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} : Set (adjointGroup Tag.E8 K))⁆ :
          Subgroup (adjointGroup Tag.E8 K)) := by
      rw [← h1]
      exact ⟨d', hd', rfl⟩
    have hcd := hc'D j _ hdD
    have hsub : (⟨c', hc'x j⟩ : Subgroup.centralizer ({(xj j : adjointGroup Tag.E8 K)} :
        Set (adjointGroup Tag.E8 K))) * d' = d' * ⟨c', hc'x j⟩ := by
      apply Subtype.ext
      show c' * (d' : adjointGroup Tag.E8 K) = (d' : adjointGroup Tag.E8 K) * c'
      calc c' * (d' : adjointGroup Tag.E8 K) = (c' * (d' : adjointGroup Tag.E8 K) * c'⁻¹) * c' := by
            group
        _ = (d' : adjointGroup Tag.E8 K) * c' := by rw [hcd]
    rw [← hψm j, ← map_mul, ← map_mul, hsub]
  have hmsub : ∀ j, m ∈ subtorusSigma n (Units.map (entrywiseHom Fr))
      (rootCharKernel (βt (xj j))) := fun j =>
    (hfam j).2.2.2.2.2.2 m (hmHQ j) (hmR j) (hmcomm j)
  obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (mem_twistedTorusOf.1 (hmsub j0).1).1
  have hroot1 : ∀ j, rootChar a' (β j) = 1 := fun j => by
    have hcent : m ∈ Subgroup.centralizer
        (rootSpan Tag.E8 L (rootCharKernel (βt (xj j))) : Set (ModGL Tag.E8 L)) := (hmsub j).2
    rw [ha'] at hcent
    exact rootChar_eq_one_of_centralizes (hβroot j) (hxjk j) hcent
  have ha1 : a' = 1 := by
    refine CTTorus.eq_one_of_rootChar_eq_one fun u => ?_
    refine CTTorus.rootChar_eq_one_of_mem_span (S := Set.range β) ?_ ?_
    · rintro _ ⟨j, rfl⟩
      exact hroot1 j
    · rw [hβspan]
      exact Submodule.mem_top
  have hm1 : m = 1 := by
    rw [ha', ha1, rootDiagUnit_one]
  have hc'1 : c' = 1 := by
    have h1 : adjEmb Tag.E8 K L (c * c' * c⁻¹) = 1 := by
      have : adjEmb Tag.E8 K L (c * c' * c⁻¹) = g0 * m * g0⁻¹ := by
        rw [hm]
        group
      rw [this, hm1]
      group
    have h2 : c * c' * c⁻¹ = 1 := adjEmb_injective (h1.trans (map_one _).symm)
    have h3 : c' = c⁻¹ * (c * c' * c⁻¹) * c := by group
    rw [h3, h2]
    group
  rw [← hc', hc'1, map_one]
  exact Subgroup.one_mem _

end Rigid

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
