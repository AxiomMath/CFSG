module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.PlaneAssembly
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.CubeFrame
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.Geometry
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.Lines
public import CFSG.RankThree.PartOne.KA5L.Final
public import CFSG.RankThree.PartOne.KD4L.TrialityLayer
public import CFSG.RankThree.PartOne.KE.E7ThreeLayerProof

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice
open scoped Matrix

set_option linter.unusedSectionVars false


theorem e7SixStep3Adj_of_kinds (h3 : E7SixLinesKind [3]) (h01 : E7SixLinesKind [0, 1])
    (hR : E7SixRSub) : E7SixStep3Adj := by
  refine e7SixStep3Adj_of_lines fun K _ _ r _ _ p hp hord => ?_
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp3 := three_lt_of_orderOf_eq_six hp hord
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hrn, hcardn⟩ := FiniteField.card K r
  have hf : 1 ≤ (n : ℕ) := n.pos
  have hK : Nat.card K = r ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcardn
  let L := AlgebraicClosure K
  have : CharP L r := charP_of_injective_algebraMap (algebraMap K L).injective r
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1 := by
    have h := (CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.dvd_sq_sub_add_one_of_orderOf_eq_six
      hp hord).1
    have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow two_ne_zero _
    have h' := Int.natCast_dvd_natCast.2 h
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one] at h'
    simpa [sub_eq_add_neg] using h'
  obtain ⟨F⟩ := exists_e7ThreeFrame K hf hK hp hp3 hε hpf L
  have hFr : ∀ x, iterateFrobenius L r (n : ℕ) x = x ^ Nat.card K := fun x => by
    rw [hK]; exact iterateFrobenius_def r (n : ℕ) x
  have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 2 + (((-1 : ℤ) : ℤ) : ZMod p) * (Nat.card K : ℕ) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 2 + (-1 : ℤ) * (Nat.card K : ℤ) + 1) p).2 hpf
    simpa using this
  have hLay : E7ThreeLayers := e7ThreeLayers CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 CFSG.RankThree.PartOne.KA5L.a5Layer_E7
  obtain ⟨c, E, hE, hEc, hT0⟩ := exists_cube_in_frame F hp hord
  have hT : ∀ x ∈ E, psiC F.g0 c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L r (n : ℕ)))) := fun x hx => by
    rw [psiC_apply]; exact hT0 x hx
  have hbE : ∀ e : E, ∃ b : Fin Tag.E7.rank → Lˣ,
      rootDiagUnit .E7 b = (psiC F.g0 c).comp E.subtype e := by
    intro e
    have h := hT e e.2
    rw [F.hT] at h
    obtain ⟨b, -, hb⟩ := h
    exact ⟨b, hb⟩
  obtain ⟨χ, hχ⟩ := exists_rootCharHom ((psiC F.g0 c).comp E.subtype) hbE
    (toVec Tag.E7.rank sigma0)
  have hfinE : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hEc]; exact pow_ne_zero _ hp.ne_zero)
  have hpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hpg : IsPGroup p χ.ker := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hpE (x : E)⟩
  obtain ⟨K₁, hK₁⟩ := exists_subgroup_card_sq hpg (two_le_card_ker hE hEc χ)
  set E₁ : Subgroup (adjointGroup .E7 K) := (K₁.map χ.ker.subtype).map E.subtype with hE₁
  have hE₁E : E₁ ≤ E := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.card_map_of_injective χ.ker.subtype_injective, hK₁]
  have hE₁χ : ∀ y ∈ E₁, ∃ hyE : y ∈ E, χ ⟨y, hyE⟩ = 1 := by
    rintro _ ⟨z, ⟨w, -, hwz⟩, rfl⟩
    refine ⟨z.2, ?_⟩
    show χ z = 1
    rw [← hwz]
    exact w.2
  obtain ⟨R, hR1, hRp, hRc⟩ := hR K L F hK c
  have hE₁R : ∀ x ∈ E₁, ∀ u ∈ R, x * u = u * x := by
    intro x hx u hu
    obtain ⟨hxE, hχx⟩ := hE₁χ x hx
    obtain ⟨b, hb⟩ := hbE ⟨x, hxE⟩
    refine hRc x ⟨b, hb, ?_⟩ u hu
    rw [← hχ ⟨x, hxE⟩ b hb]
    exact hχx
  have hlines : E7SixLinesAt p E E₁ := by
    intro y hyE₁ hy1 k hk
    have hk' : k * y = y * k := Subgroup.mem_centralizer_singleton_iff.1 hk
    obtain ⟨hyE, hχy⟩ := hE₁χ y hyE₁
    obtain ⟨b, hb⟩ := hbE ⟨y, hyE⟩
    have hbpsi : rootDiagUnit .E7 b = psiC F.g0 c y := hb
    have hσb : rootChar b (toVec Tag.E7.rank sigma0) = 1 := by
      rw [← hχ ⟨y, hyE⟩ b hb]; exact hχy
    have hyo : orderOf y = p := orderOf_eq_prime (hE.2 y hyE) hy1
    have hhy : F.g0⁻¹ * adjEmb .E7 K L (c * y * c⁻¹) * F.g0 ∈
        twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L r (n : ℕ)))) := by
      simpa [psiC_apply] using hT y hyE
    obtain ⟨b', hb', hap, hb1, hbh, huniq⟩ := e7_three_prelim F hp hyo c hhy
    have hbb' : b = b' := huniq b (by rw [hbpsi, psiC_apply])
    subst hbb'
    rcases e7T3_kernel_structure (iterateFrobenius L r (n : ℕ)) hFr hp hp3 hε hΦ hb' hap hb1 with
      hempty | ⟨cert, hcert, hker, hgood⟩
    · exfalso
      have : toVec Tag.E7.rank sigma0 ∈ rootCharKernel b := ⟨sigma0_isRoot, hσb⟩
      rw [hempty] at this
      exact this
    · have hσk : toVec Tag.E7.rank sigma0 ∈ rootCharKernel b := ⟨sigma0_isRoot, hσb⟩
      rw [hker] at hσk
      obtain ⟨l, hl, hlσ⟩ := hσk
      have hlr : l ∈ Tag.E7.artifactRoots := hgood.2.2.1 l hl
      have hmem : sigma0 ∈ cert.rootList := by
        rw [eq_sigma0_of_toVec_eq l hlr hlσ.symm] at hl
        exact hl
      rcases cert_cases cert hcert hmem with ⟨-, horb⟩ | hk3 | hk01
      · refine mem_hyperClosure_of_kernel_orbit hLay F hf hK hp hp3 hpf hE hEc hT hyE hy1
          (toVec Tag.E7.rank sigma0) ?_ hk'
        intro b'' hb'' α hα
        have : b'' = b := huniq b'' (by rw [hb'', psiC_apply])
        subst this
        rw [hker] at hα
        obtain ⟨l, hl, rfl⟩ := hα
        obtain ⟨j, -, rfl⟩ := horb l hl
        exact ⟨j, toVec_negWorbit j⟩
      · exact h3 K L F hf hK hp hp3 hpf c E hE hEc hT y hyE hy1 b hbpsi cert hcert hker hk3 hmem
          k hk'
      · exact h01 K L F hf hK hp hp3 hpf c E hE hEc hT y hyE hy1 b hbpsi cert hcert hker hk01 hmem
          k hk'
  refine ⟨E, E₁, hE, hEc, hE₁E, hE₁c, ⟨R, hR1, hRp, ?_⟩, hlines⟩
  intro x hx
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    have := hE₁R x hx v hv
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [this, mul_inv_cancel_right]
    exact hv
  · intro hu
    refine ⟨u, hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hE₁R x hx u hu, mul_inv_cancel_right]


end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
