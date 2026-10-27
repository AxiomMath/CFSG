module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.Ten
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.LieType.Chevalley.TorusTupleLift
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TwelveD4Order
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TwelveRigid

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
open scoped Matrix Pointwise MatrixGroups


section Rigid

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L ℓ]

theorem exists_rigid_embedding_of_plane_adjointE8
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E8))
    (n g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    (hconj : ∀ A : Subgroup (adjointGroup Tag.E8 K), IsPGroup p A →
      ∃ c : adjointGroup Tag.E8 K, ∀ x ∈ A, g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 ∈
        twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (β : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ) (hβroot : ∀ j, IsRoot Tag.E8 (β j))
    (hrigid : ∀ b : Fin Tag.E8.rank → Lˣ,
      rootDiagUnit Tag.E8 b ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      (∀ i, b i ^ p = 1) → b ≠ 1 → (∃ j, β j ∈ rootCharKernel b) →
      E8RigidAt K n (iterateFrobenius L ℓ f) p b)
    {E : Subgroup (adjointGroup Tag.E8 K)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    ∃ x ∈ E, x ≠ 1 ∧ ∃ P : Subgroup (ModGL Tag.E8 L),
      CFSG.IsQuasisimple P ∧ ¬ Nat.Coprime p (Nat.card P) ∧
      ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)) →* ModGL Tag.E8 L,
        Function.Injective ψ ∧ ⁅ψ.range, ψ.range⁆ = P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => hE.2 a ha
  obtain ⟨c, hc⟩ := hconj E (IsPGroup.of_card hcard)
  let φ : E →* ModGL Tag.E8 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((adjEmb Tag.E8 K L).comp ((MulAut.conj c).toMonoidHom.comp E.subtype))
  have hφ : ∀ q : E, φ q =
      g0⁻¹ * adjEmb Tag.E8 K L (c * (q : adjointGroup Tag.E8 K) * c⁻¹) * g0 := fun q => by
    simp [φ, MulAut.conj_apply]
  have hφinj : Function.Injective φ := (MulAut.conj g0⁻¹).injective.comp
    (adjEmb_injective.comp ((MulAut.conj c).injective.comp E.subtype_injective))
  have hφT : ∀ q : E, φ q ∈ twistedTorusOf n (Units.map (entrywiseHom Fr)) := fun q => by
    rw [hφ]
    exact hc q q.2
  obtain ⟨βt, hβt⟩ := exists_rootDiagUnitHom_comp_eq φ fun q => (mem_twistedTorusOf.1 (hφT q)).1
  have hβtq : ∀ q, rootDiagUnit Tag.E8 (βt q) = φ q := fun q => DFunLike.congr_fun hβt q
  have hβtp : ∀ q : E, ∀ i, βt q i ^ p = 1 := fun q i => by
    have h : βt q ^ p = 1 := by
      rw [← map_pow, show q ^ p = 1 from Subtype.ext (hpow q q.2), map_one]
    exact congrFun h i
  have hβtne : ∀ q : E, q ≠ 1 → βt q ≠ 1 := fun q hq h =>
    hq (hφinj (by rw [← hβtq, ← hβtq, h, map_one]))
  let j0 : Fin Tag.E8.rank := ⟨0, CFSG.LieType.Chevalley.Tag.rank_pos Tag.E8⟩
  let χ : E →* Lˣ :=
    { toFun := fun q => rootChar (βt q) (β j0)
      map_one' := by rw [map_one]; exact CTTorus.rootChar_one (β j0)
      map_mul' := fun q q' => by rw [map_mul, CTTorus.rootChar_mul] }
  have hχp : ∀ q : E, χ q ^ p = 1 := fun q => by
    rw [← map_pow]
    have h3 : q ^ p = 1 := Subtype.ext (hpow q q.2)
    rw [h3, map_one]
  obtain ⟨q₀, hq₀1, hq₀χ⟩ := exists_ne_one_ker_of_card_sq hp hcard χ hχp
  have hxjk : β j0 ∈ rootCharKernel (βt q₀) := ⟨hβroot j0, hq₀χ⟩
  have hxjC : (q₀ : adjointGroup Tag.E8 K) ≠ 1 := fun h => hq₀1 (Subtype.ext h)
  have hxjp : orderOf (q₀ : adjointGroup Tag.E8 K) = p :=
    orderOf_eq_prime (hpow q₀ q₀.2) hxjC
  have hbhj : rootDiagUnit Tag.E8 (βt q₀) =
      g0⁻¹ * adjEmb Tag.E8 K L (c * (q₀ : adjointGroup Tag.E8 K) * c⁻¹) * g0 := by
    rw [hβtq, hφ]
  have hhj : g0⁻¹ * adjEmb Tag.E8 K L (c * (q₀ : adjointGroup Tag.E8 K) * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom Fr)) := hc q₀ q₀.2
  obtain ⟨P, hfam, hP1, -, hpdvd⟩ :=
    hrigid (βt q₀) (by rw [hbhj]; exact hhj) (hβtp q₀) (hβtne q₀ hq₀1) ⟨j0, hxjk⟩
  have hS : ∀ α ∈ rootCharKernel (βt q₀), IsRoot Tag.E8 α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel (βt q₀), -α ∈ rootCharKernel (βt q₀) :=
    fun α hα => ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, -, hPψ, -⟩ :=
    e8_perx_core Fr hFr n g0 hg0C hg0 hperf hp hordW hxjp c hbhj hhj rfl hS hSn hfam
  have hcomm : ⁅ψ.range, ψ.range⁆ = P :=
    e8_perx_commutator Fr n hS ψ hψHQ hψR hP1 (hPψ ()) (hfam.2.1 ())
  exact ⟨(q₀ : adjointGroup Tag.E8 K), q₀.2, hxjC, P, hfam.2.1 (), hpdvd, ψ, hψinj, hcomm⟩

theorem exists_quasisimple_layer_of_plane_adjointE8
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E8))
    (n g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    (hconj : ∀ A : Subgroup (adjointGroup Tag.E8 K), IsPGroup p A →
      ∃ c : adjointGroup Tag.E8 K, ∀ x ∈ A, g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 ∈
        twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (β : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ) (hβroot : ∀ j, IsRoot Tag.E8 (β j))
    (hrigid : ∀ b : Fin Tag.E8.rank → Lˣ,
      rootDiagUnit Tag.E8 b ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      (∀ i, b i ^ p = 1) → b ≠ 1 → (∃ j, β j ∈ rootCharKernel b) →
      E8RigidAt K n (iterateFrobenius L ℓ f) p b)
    {E : Subgroup (adjointGroup Tag.E8 K)} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    ∃ x ∈ E, x ≠ 1 ∧
      CFSG.IsQuasisimple (⁅Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))⁆ :
          Subgroup (adjointGroup Tag.E8 K)) ∧
      p ∣ Nat.card (⁅Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))⁆ :
          Subgroup (adjointGroup Tag.E8 K)) := by
  obtain ⟨x, hxE, hx1, P, hPq, hPnc, ψ, hψinj, hcomm⟩ :=
    exists_rigid_embedding_of_plane_adjointE8 hK hp hordW n g0 hg0C hg0 hperf hconj
      β hβroot hrigid hE hcard
  obtain ⟨hDq, h2, h1⟩ := isQuasisimple_commutator_of_embedding ψ hψinj hPq hcomm
  set T' : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))) :=
    ⁅(⊤ : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))),
      ⊤⁆ with hT'
  have hcP : Nat.card P = Nat.card T' := by
    rw [← h2]
    exact Subgroup.card_map_of_injective hψinj
  have hcD : Nat.card (⁅Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))⁆ :
        Subgroup (adjointGroup Tag.E8 K)) = Nat.card T' := by
    rw [← h1]
    exact Subgroup.card_map_of_injective
      (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))).subtype_injective
  refine ⟨x, hxE, hx1, hDq, ?_⟩
  rw [hcD, ← hcP]
  exact (Nat.Prime.dvd_iff_not_coprime hp).mpr hPnc

theorem perfectCentralizerPlanes_adjointE8_of_rigid
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E8))
    (n g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    (hconj : ∀ A : Subgroup (adjointGroup Tag.E8 K), IsPGroup p A →
      ∃ c : adjointGroup Tag.E8 K, ∀ x ∈ A, g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 ∈
        twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (β : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ) (hβroot : ∀ j, IsRoot Tag.E8 (β j))
    (hrigid : ∀ b : Fin Tag.E8.rank → Lˣ,
      rootDiagUnit Tag.E8 b ∈ twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      (∀ i, b i ^ p = 1) → b ≠ 1 → (∃ j, β j ∈ rootCharKernel b) →
      E8RigidAt K n (iterateFrobenius L ℓ f) p b) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E8 K) := by
  intro E hE hcard
  obtain ⟨x, hxE, hx1, hDq, hDdvd⟩ :=
    exists_quasisimple_layer_of_plane_adjointE8 hK hp hordW n g0 hg0C hg0 hperf hconj
      β hβroot hrigid hE hcard
  have hDperf : ⁅⁅Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))⁆,
      ⁅Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))⁆⁆ =
    ⁅Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))⁆ := by
    haveI : Group.IsPerfect ↥(⁅Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))⁆ :
        Subgroup (adjointGroup Tag.E8 K)) := hDq.1
    exact Subgroup.commutator_eq_self
  exact ⟨x, hxE, hx1, ⁅Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)),
    Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K))⁆,
    Subgroup.commutator_le_self _, hDperf, hDdvd⟩

end Rigid

section Ten


theorem perfectCentralizerPlanes_adjointGroup_E8_ten (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 10) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E8 K) := by
  classical
  obtain ⟨hp7', -, -, -⟩ := e8Ten_arith hp hp7 he
  obtain ⟨ℓ, f, hℓ, hcharK, hf, hK⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := hcharK
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨F⟩ := exists_e8TenFrame K hf hK hp hp7 he L
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E8) :=
    not_dvd_card_weylGroup_E hp hp7' (Or.inr (Or.inr rfl))
  refine perfectCentralizerPlanes_adjointE8_of_rigid hK hp hordW F.n F.g0 F.hg0C F.hg0 F.hperf
    F.hconj (fun j => (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) (fun j => IsRoot.basis j) ?_
  intro b hb hbp hb1 hβ
  obtain ⟨j, hj⟩ := hβ
  exact e8Ten_rigidAt K hf hK hp hp7 he F hb hbp hb1 ⟨Pi.single j 1, hj⟩

end Ten

section Twelve

theorem perfectCentralizerPlanes_adjointGroup_E8_twelve (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 12) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E8 K) := by
  classical
  obtain ⟨ℓ, f, hℓ, hcharK, hf, hK⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := hcharK
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hp7', -, hΦ, -⟩ := e8Twelve_arith hp hp7 he
  obtain ⟨F⟩ := exists_e8TwelveFrame K hf hK hp hp7 he L
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E8) :=
    not_dvd_card_weylGroup_E hp hp7' (Or.inr (Or.inr rfl))
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hexist : E8TwelveOrderP F := fun ζ hζ c hc =>
    e8T12_exists_order_p_mem_D4 hp hp7' hζ hFr hΦ F.hT hc
  refine perfectCentralizerPlanes_adjointE8_of_rigid hK hp hordW F.n F.g0 F.hg0C F.hg0 F.hperf
    F.hconj e8T12Basis e8T12Basis_root ?_
  intro b hbT hap hb1 hβ
  exact e8Twelve_rigid hf hK hp hp7' hΦ F hexist b hbT hap hb1 hβ

end Twelve

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
