module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FourAux.PerX
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FourAux.Torus
public import CFSG.RankThree.PartOne.KE.E7FourStab
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangTorus
public import CFSG.LieType.Chevalley.TorusTupleLift
public import CFSG.RankThree.PartOne.KE.E8FiveData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
open scoped Matrix MatrixGroups

section ClassKernel


theorem exists_e7Four_classKernel_of_fixedCharTuples {A : Type*} [Group A] [Finite A]
    {L : Type} [Field L] (Fr : L →+* L) {q p : ℕ} (hFr : ∀ x, Fr x = x ^ q)
    (hp : p.Prime) (hp3 : 3 < p) (hΦ : (q : ZMod p) ^ 2 + 1 = 0) (hA : Nat.card A = p ^ 2)
    (β : A →* (Fin Tag.E7.rank → Lˣ)) (hfix : ∀ a, β a ∈ fixedCharTuples e7F4W Fr)
    (hAp : ∀ a : A, a ^ p = 1) (hβne : ∀ a, a ≠ 1 → β a ≠ 1) (j : Fin 6) :
    ∃ a : A, a ≠ 1 ∧ ∃ cert ∈ e7F4Certs, cert.cls = j.val ∧
      e7D4Set cert ⊆ rootCharKernel (β a) ∧
      rootCharKernel (β a) = e7F4S0Set ∪ classSetL7 e7F4Rows cert.cls := by
  classical
  have hβp : ∀ a : A, ∀ i, β a i ^ p = 1 := fun a i => by
    have h1 : β (a ^ p) = 1 := by rw [hAp a, map_one]
    have h2 : (β a) ^ p = 1 := by rw [← map_pow]; exact h1
    exact congrFun h2 i
  set r : Fin Tag.E7.rank → ℤ := toVec Tag.E7.rank (e7F4ClassRoots.getD j.val []) with hrdef
  have hr : IsRoot .E7 r := isRoot_toVec (e7F4_classRoots_isRoot j.val j.2)
  let χ : A →* Lˣ :=
    { toFun := fun a => rootChar (β a) r
      map_one' := by rw [map_one]; exact CTTorus.rootChar_one r
      map_mul' := fun a b => by rw [map_mul, CTTorus.rootChar_mul] }
  have hχp : ∀ a : A, χ a ^ p = 1 := fun a => by
    rw [← map_pow, hAp a, map_one]
  obtain ⟨a₀, ha₀1, ha₀χ⟩ := exists_ne_one_ker_of_card_sq hp hA χ hχp
  refine ⟨a₀, ha₀1, ?_⟩
  have hrk : r ∈ rootCharKernel (β a₀) := ⟨hr, ha₀χ⟩
  rcases e7F4_kernel_structure Fr hFr hp hp3 hΦ (hfix a₀) (hβp a₀) (hβne a₀ ha₀1) with
    hker | ⟨cert, hcert, hker, -⟩
  · exfalso
    rw [hker] at hrk
    obtain ⟨l, hl, hrl⟩ := hrk
    exact e7F4_classRoots_notS0' j.val j.2 l hl hrl
  · rw [hker] at hrk
    rcases hrk with ⟨l, hl, hrl⟩ | ⟨l, hl, hrl⟩
    · exact absurd hrl (e7F4_classRoots_notS0' j.val j.2 l hl)
    · have hjk : j.val = cert.cls := e7F4_classRoots_unique' j.val j.2 cert.cls
        (e7F4_certs_cls_lt cert hcert) l hl hrl
      obtain ⟨-, -, hSigma, -, -, -⟩ := D4A1Cert.sound (e7F4_certs_good cert hcert)
      have hker' : rootCharKernel (β a₀) = e7D4Set cert ∪
          {toVec Tag.E7.rank cert.r, -toVec Tag.E7.rank cert.r} := hker.trans hSigma
      have hD4ker : e7D4Set cert ⊆ rootCharKernel (β a₀) := by
        rw [hker']
        exact Set.subset_union_left
      exact ⟨cert, hcert, hjk.symm, hD4ker, hker⟩

end ClassKernel

section FrameWitness

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]


theorem exists_e7Four_charTuple_of_plane (F : E7FourFrame K L ℓ f p)
    (hK : Nat.card K = ℓ ^ f) {E : Subgroup (adjointGroup .E7 K)}
    (c : adjointGroup .E7 K)
    (hc : ∀ x ∈ E, F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ β : E →* (Fin Tag.E7.rank → Lˣ),
      (∀ q, β q ∈ fixedCharTuples e7F4W (iterateFrobenius L ℓ f)) ∧
      (∀ q, q ≠ 1 → β q ≠ 1) ∧
      (∀ q, rootDiagUnit .E7 (β q) =
        F.g0⁻¹ * adjEmb .E7 K L (c * (q : adjointGroup .E7 K) * c⁻¹) * F.g0) := by
  classical
  let φ : E →* ModGL .E7 L := (MulAut.conj F.g0⁻¹).toMonoidHom.comp
    ((adjEmb .E7 K L).comp ((MulAut.conj c).toMonoidHom.comp E.subtype))
  have hφ : ∀ q : E, φ q =
      F.g0⁻¹ * adjEmb .E7 K L (c * (q : adjointGroup .E7 K) * c⁻¹) * F.g0 := fun q => by
    simp [φ, MulAut.conj_apply]
  have hφinj : Function.Injective φ := (MulAut.conj F.g0⁻¹).injective.comp
    (adjEmb_injective.comp ((MulAut.conj c).injective.comp E.subtype_injective))
  have hφT : ∀ q : E, φ q ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := fun q => by
    rw [hφ]
    exact hc q q.2
  obtain ⟨β, hβ⟩ := exists_rootDiagUnitHom_comp_eq φ fun q => (mem_twistedTorusOf.1 (hφT q)).1
  have hβq : ∀ q, rootDiagUnit .E7 (β q) = φ q := fun q => DFunLike.congr_fun hβ q
  refine ⟨β, fun q => ?_, fun q hq h => hq (hφinj ?_), fun q => (hβq q).trans (hφ q)⟩
  · have h := hφT q
    rw [F.hT] at h
    obtain ⟨b, hb, hbq⟩ := h
    rwa [rootDiagUnit_injective (hbq.trans (hβq q).symm)] at hb
  · rw [← hβq, ← hβq, h, map_one]

theorem exists_perfect_le_centralizer_of_e7FourFrame (hD4 : D4TranspositionLayer Tag.E7)
    (F : E7FourFrame K L ℓ f p) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p)
    (hdiv : ∀ cert ∈ e7F4Certs, p ∣ Nat.card ↥(rootSpan .E7 L (e7D4Set cert) ⊓
      twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))))
    {E : Subgroup (adjointGroup .E7 K)} (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) :
    ∃ x ∈ E, x ≠ 1 ∧ ∃ P : Subgroup (adjointGroup .E7 K),
      P ≤ Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) ∧ ⁅P, P⁆ = P ∧
        p ∣ Nat.card P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + 1) p).2 hpf
    simpa using this
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hpg : IsPGroup p E := IsPGroup.of_card hEcard
  obtain ⟨c, hc⟩ := F.hconj E hpg
  obtain ⟨βhom, hβfix, hβne, hβeq⟩ :=
    exists_e7Four_charTuple_of_plane F hK c hc
  obtain ⟨q, hq1, cert, hcert, hcls, hD4ker, hker⟩ :=
    exists_e7Four_classKernel_of_fixedCharTuples (A := E) Fr hFr hp hp3 hΦ hEcard βhom hβfix
      (fun q => Subtype.ext (hE.2 q q.2)) hβne ⟨0, by decide⟩
  let x : adjointGroup .E7 K := q
  have hxE : x ∈ E := q.2
  have hx1 : x ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hxord : orderOf x = p := orderOf_eq_prime (hE.2 x hxE) hx1
  have hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom Fr)) := hc x hxE
  have hb : rootDiagUnit .E7 (βhom q) =
      F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 := hβeq q
  obtain ⟨ψ, hψinj, hψ, _, _, _, PD, hPD, hPψ, _, hPq, _, _, _, _, _⟩ :=
    e7_four_perx_special_def hD4 F hf hK hp hstab hxord c hh hb cert hcert hker
  let Ψ : adjointGroup .E7 K →* ModGL .E7 L :=
    (MulAut.conj F.g0⁻¹).toMonoidHom.comp
      ((adjEmb .E7 K L).comp (MulAut.conj c).toMonoidHom)
  have hΨinj : Function.Injective Ψ :=
    (MulAut.conj F.g0⁻¹).injective.comp (adjEmb_injective.comp (MulAut.conj c).injective)
  have hΨx : Ψ x = rootDiagUnit .E7 (βhom q) := (hβeq q).symm
  have hψeq : ψ = Ψ.comp
      (Subgroup.centralizer ({x} : Set (adjointGroup .E7 K))).subtype := by
    ext y
    rw [hψ y]
    simp [Ψ, MulAut.conj_apply]
  have hPDrange : PD ≤ Ψ.range := by
    intro y hy
    have hy' := hPψ hy
    rw [hψeq] at hy'
    obtain ⟨z, hz⟩ := hy'
    exact ⟨z.1, hz⟩
  have hPDroot : PD ≤ rootSpan .E7 L (e7D4Set cert) := by
    rw [hPD]
    exact inf_le_left
  have hPDcent : PD ≤ Subgroup.centralizer ({Ψ x} : Set (ModGL .E7 L)) := by
    rw [hΨx]
    exact hPDroot.trans (rootSpan_le_centralizer (K := L) (βhom q) hD4ker)
  have hPperf : ⁅PD, PD⁆ = PD := by
    haveI : Group.IsPerfect ↥PD := hPq.1
    exact Subgroup.commutator_eq_self
  have hdiv' : p ∣ Nat.card PD := by
    rw [hPD]
    exact hdiv cert hcert
  obtain ⟨P, hPcent, hPperf, hPcard⟩ :=
    exists_perfect_le_centralizer_of_injective Ψ hΨinj hPDrange hPperf hPDcent
  exact ⟨x, hxE, hx1, P, hPcent, hPperf, by rw [hPcard]; exact hdiv'⟩

end FrameWitness

section TwoFive


theorem perfectCentralizerPlanes_adjointGroup_E7_two_five (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : PerfectCentralizerPlanes 5 (adjointGroup Tag.E7 K) := by
  classical
  have hℓ : Nat.Prime 2 := Nat.prime_two
  haveI : Fact (Nat.Prime 2) := ⟨hℓ⟩
  have hf : 1 ≤ 1 := le_rfl
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; rfl
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK'
  let L := AlgebraicClosure K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpf : ((5 : ℕ) : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by rw [hK]; norm_num
  obtain ⟨F⟩ := exists_e7FourFrame K hf hK' Nat.prime_five (by norm_num) hpf L
  have hstab := e7_stabHyp F hK' Nat.prime_five (by norm_num) hpf
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf_eq_of_isAlgClosed (k := L) (n := 5)
    (NeZero.of_not_dvd L (p := 2) (by norm_num)).out
  have hFr : ∀ x : L, iterateFrobenius L 2 1 x = x ^ 2 := fun x => by
    rw [iterateFrobenius_def]; simp
  have hdiv : ∀ cert ∈ e7F4Certs, 5 ∣ Nat.card ↥(rootSpan .E7 L (e7D4Set cert) ⊓
      twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L 2 1)))) := by
    intro cert hcert
    obtain ⟨d, hd, hdord⟩ := exists_order_five_mem_D4 hζ hFr F.hT hcert
    have h1 := orderOf_dvd_natCard (⟨d, hd⟩ : ↥(rootSpan .E7 L (e7D4Set cert) ⊓
      twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L 2 1)))))
    rwa [Subgroup.orderOf_mk, hdord] at h1
  intro E hEin hEcard
  exact exists_perfect_le_centralizer_of_e7FourFrame d4TranspositionLayer_E7 F hf hK'
    Nat.prime_five (by norm_num) hpf hstab hdiv hEin hEcard

end TwoFive

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
