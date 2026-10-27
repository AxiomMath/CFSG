module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.RankThree.PartOne.KE

section CosetLang

set_option linter.unusedSectionVars false


theorem d4t2c_exists_conj_setup {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {l f : ℕ} (hl : l.Prime) (hf : 0 < f) (hq : S.D.q = l ^ f)
    {a : Fin Tag.E6.rank → Lˣ} {Eh : Subgroup (ModGL Tag.E6 L)} (hEhM : Eh ≤ S.D.model)
    (hdE : rootDiagUnit .E6 a ∈ Eh) {g : ModGL Tag.E6 L} (hgC : g ∈ toralCentralizer .E6 L a)
    (hgE : ∀ x ∈ Eh, g⁻¹ * x * g ∈ torusGroup .E6 L) :
    ∃ (S' : LangSetup .E6 L p₀) (c : ModGL Tag.E6 L), S'.D.Φ = S.D.Φ ∧ S'.D.q = S.D.q ∧
      c ∈ toralCentralizer .E6 L a ∧ (∀ y, y ∈ S'.Γ ↔ c * y * c⁻¹ ∈ S.Γ) ∧
      ∀ x ∈ Eh, c⁻¹ * x * c ∈ S'.D.torus := by
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  have hl0 : ((l : ℕ) : L) = 0 := by
    have h := S.hqpow.2
    rw [hq, Nat.cast_pow] at h
    exact (pow_eq_zero_iff hf.ne').1 h
  haveI : CharP L l := (CharP.charP_iff_prime_eq_zero hl).2 hl0
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  have ht' : t = TwistTag.E6 := by
    cases t
    · rfl
    · exact absurd ht (by decide)
  subst ht'
  have hFr' : Fr = iterateFrobenius L l f := RingHom.ext fun c => by
    rw [hFr, iterateFrobenius_def, hq]
  obtain ⟨F, hF⟩ : ∃ F : ModGL Tag.E6 L →* ModGL Tag.E6 L,
      F = twistHom TwistTag.E6 L (iterateFrobenius L l f) := ⟨_, rfl⟩
  have hΦF : ∀ y, S.D.Φ y = F y := fun y => by
    rw [hΦ y, hF, ← hFr']
    rfl
  have hlang : F S.D.g0 = S.D.g0 * S.D.n := by
    rw [← hΦF]
    exact S.D.lang
  have hfix : ∀ x ∈ Eh, S.D.n * F x * S.D.n⁻¹ = x := fun x hx => by
    rw [← hΦF]
    exact (S.D.mem_model.1 (hEhM hx)).2
  have hgA : g ∈ adjointGroup .E6 L := (mem_toralCentralizer.1 hgC).1
  have hgd : rootDiagUnit .E6 a * g * (rootDiagUnit .E6 a)⁻¹ = g :=
    (mem_toralCentralizer.1 hgC).2
  choose b hb using fun x : Eh => exists_rootDiagUnit_eq_of_mem_torusGroup (hgE x x.2)
  have hgR : S.D.g0 * g ∈ adjointGroup .E6 L := mul_mem S.D.g0_mem hgA
  have hn : ∀ s : Eh, ((S.D.g0 * g)⁻¹ * F (S.D.g0 * g)) * F (rootDiagUnit .E6 (b s)) *
      ((S.D.g0 * g)⁻¹ * F (S.D.g0 * g))⁻¹ = rootDiagUnit .E6 (b s) := by
    intro s
    have h1 : g⁻¹ * (s : ModGL Tag.E6 L) * g = rootDiagUnit .E6 (b s) := hb s
    rw [← h1]
    simp only [map_mul, map_inv, hlang]
    calc _ = g⁻¹ * (S.D.n * F s * S.D.n⁻¹) * g := by group
      _ = g⁻¹ * s * g := by rw [hfix s s.2]
  obtain ⟨v, z, hz, hv⟩ : ∃ (v : WeylGroup Tag.E6) (z : ModGL Tag.E6 L),
      z ∈ familyGroup (K := L) b ∧
        (S.D.g0 * g * z)⁻¹ * F (S.D.g0 * g * z) = canonicalRep (coxeterSystem Tag.E6) L v := by
    rw [hF] at hn ⊢
    exact exists_lang_datum_of_plane_twisted l TwistTag.E6 f hf b hgR hn
  have hzC : z ∈ familyCentralizer .E6 L b := familyGroup_le_familyCentralizer (K := L) b hz
  obtain ⟨hzA, hzc⟩ := mem_familyCentralizer.1 hzC
  have hlang' : F (S.D.g0 * g * z) =
      S.D.g0 * g * z * canonicalRep (coxeterSystem Tag.E6) L v :=
    inv_mul_eq_iff_eq_mul.1 hv
  have hΦc : S.D.Φ (g * z) = S.D.n⁻¹ * (g * z) * canonicalRep (coxeterSystem Tag.E6) L v := by
    have h1 : F (S.D.g0 * (g * z)) =
        S.D.g0 * (g * z) * canonicalRep (coxeterSystem Tag.E6) L v := by
      simpa only [mul_assoc] using hlang'
    rw [map_mul F S.D.g0 (g * z), hlang] at h1
    rw [hΦF]
    calc F (g * z) = S.D.n⁻¹ * S.D.g0⁻¹ * (S.D.g0 * S.D.n * F (g * z)) := by group
      _ = S.D.n⁻¹ * (g * z) * canonicalRep (coxeterSystem Tag.E6) L v := by
        rw [h1]
        group
  have hdb : rootDiagUnit .E6 (b ⟨_, hdE⟩) = rootDiagUnit .E6 a := by
    have h1 : g⁻¹ * rootDiagUnit .E6 a * g = rootDiagUnit .E6 (b ⟨_, hdE⟩) := hb ⟨_, hdE⟩
    rw [← h1]
    calc g⁻¹ * rootDiagUnit .E6 a * g
        = g⁻¹ * (rootDiagUnit .E6 a * g * (rootDiagUnit .E6 a)⁻¹) * rootDiagUnit .E6 a := by
          group
      _ = rootDiagUnit .E6 a := by
        rw [hgd]
        group
  have hzd : rootDiagUnit .E6 a * z * (rootDiagUnit .E6 a)⁻¹ = z := by
    have h := hzc ⟨_, hdE⟩
    rwa [hdb] at h
  have hcA : g * z ∈ adjointGroup .E6 L := mul_mem hgA hzA
  have hcC : g * z ∈ toralCentralizer .E6 L a := by
    refine mem_toralCentralizer.2 ⟨hcA, ?_⟩
    calc rootDiagUnit .E6 a * (g * z) * (rootDiagUnit .E6 a)⁻¹
        = (rootDiagUnit .E6 a * g * (rootDiagUnit .E6 a)⁻¹) *
          (rootDiagUnit .E6 a * z * (rootDiagUnit .E6 a)⁻¹) := by group
      _ = g * z := by rw [hgd, hzd]
  have hconj : ∀ x (hx : x ∈ Eh), (g * z)⁻¹ * x * (g * z) = rootDiagUnit .E6 (b ⟨x, hx⟩) := by
    intro x hx
    have h1 : g⁻¹ * x * g = rootDiagUnit .E6 (b ⟨x, hx⟩) := hb ⟨x, hx⟩
    have h2 := hzc ⟨x, hx⟩
    calc (g * z)⁻¹ * x * (g * z) = z⁻¹ * (g⁻¹ * x * g) * z := by group
      _ = z⁻¹ * rootDiagUnit .E6 (b ⟨x, hx⟩) * z := by rw [h1]
      _ = z⁻¹ * (rootDiagUnit .E6 (b ⟨x, hx⟩) * z * (rootDiagUnit .E6 (b ⟨x, hx⟩))⁻¹) *
            rootDiagUnit .E6 (b ⟨x, hx⟩) := by group
      _ = rootDiagUnit .E6 (b ⟨x, hx⟩) := by
        rw [h2]
        group
  obtain ⟨D', hD'Φ, hD'q, hD'n⟩ : ∃ D' : LangDatum .E6 L, D'.Φ = S.D.Φ ∧ D'.q = S.D.q ∧
      D'.n = canonicalRep (coxeterSystem Tag.E6) L v :=
    ⟨⟨S.D.Φ, S.D.q, canonicalRep (coxeterSystem Tag.E6) L v, S.D.g0 * g * z, S.D.steinberg,
      ⟨v, rfl⟩, mul_mem hgR hzA, by rw [hΦF]; exact hlang'⟩, rfl, rfl, rfl⟩
  have hmem : ∀ y, y ∈ D'.model ↔ g * z * y * (g * z)⁻¹ ∈ S.D.model := by
    intro y
    rw [LangDatum.mem_model, LangDatum.mem_model, hD'n, hD'Φ]
    have hΦy : S.D.n * S.D.Φ (g * z * y * (g * z)⁻¹) * S.D.n⁻¹ =
        g * z * (canonicalRep (coxeterSystem Tag.E6) L v * S.D.Φ y *
          (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹) * (g * z)⁻¹ := by
      rw [map_mul S.D.Φ (g * z * y) (g * z)⁻¹, map_mul S.D.Φ (g * z) y, map_inv S.D.Φ (g * z),
        hΦc]
      group
    rw [hΦy]
    constructor
    · rintro ⟨hy, hy'⟩
      exact ⟨mul_mem (mul_mem hcA hy) (inv_mem hcA), by rw [hy']⟩
    · rintro ⟨hy, hy'⟩
      refine ⟨?_, mul_left_cancel (mul_right_cancel hy')⟩
      have e : y = (g * z)⁻¹ * (g * z * y * (g * z)⁻¹) * (g * z) := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hcA) hy) hcA
  have hmodel : D'.model = S.D.model.map (MulAut.conj (g * z)⁻¹).toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    exact hmem y
  have hΓ : ∀ y, y ∈ D'.Γ ↔ g * z * y * (g * z)⁻¹ ∈ S.D.Γ := by
    intro y
    rw [LangDatum.Γ, LangDatum.Γ, hmodel, ← Subgroup.map_commutator, Subgroup.mem_map_equiv,
      MulAut.conj_symm_apply, inv_inv]
  haveI : Finite S.D.model := S.finite
  have hfin : Finite D'.model := by
    refine Finite.of_injective (β := S.D.model)
      (fun y => ⟨g * z * (y : ModGL Tag.E6 L) * (g * z)⁻¹, (hmem y).1 y.2⟩) fun y₁ y₂ h => ?_
    have h' : g * z * (y₁ : ModGL Tag.E6 L) * (g * z)⁻¹ = g * z * y₂ * (g * z)⁻¹ :=
      congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved .E6 L D'
  have hq5 : 5 ≤ p₀ ∨ 4 ≤ D'.q := by
    rw [hD'q]
    exact S.hq
  have hqpow : IsPrimePow D'.q ∧ ((D'.q : ℕ) : L) = 0 := by
    rw [hD'q]
    exact S.hqpow
  have hpq : ¬ p₀ ∣ D'.q := by
    rw [hD'q]
    exact S.hpq
  refine ⟨D'.toSetup p₀ ρ hρ S.hp hq5 hqpow hpq hfin, g * z, hD'Φ, hD'q, hcC, hΓ,
    fun x hx => ?_⟩
  show (g * z)⁻¹ * x * (g * z) ∈ D'.torus
  rw [LangDatum.torus, hD'n, hD'Φ, mem_twistedTorusOf]
  refine ⟨by rw [hconj x hx]; exact rootDiagUnit_mem_torusGroup _, ?_⟩
  rw [map_mul S.D.Φ ((g * z)⁻¹ * x) (g * z), map_mul S.D.Φ (g * z)⁻¹ x, map_inv S.D.Φ (g * z),
    hΦc, hΦF x]
  calc _ = (g * z)⁻¹ * (S.D.n * F x * S.D.n⁻¹) * (g * z) := by group
    _ = (g * z)⁻¹ * x * (g * z) := by rw [hfix x hx]

end CosetLang

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
