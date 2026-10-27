module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SporLat.Build
public import Certificates.Data.CFSGNative.SporLat.Code
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public meta import Certificates.Data.CFSGNative.SporLat.Build
public meta import Certificates.Data.CFSGNative.SporLat.Code
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRows
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24DcInputs
public import CFSG.Quasithin.EmptyFaithful.S151S9TM24Inputs
public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Vol2.Ch12Sec5KGM24Inputs
public import CFSG.Quasithin.H13.KGFactT3J4Inputs
public import Certificates.Certificate4075
public import Certificates.Certificate3017
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.M24

open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m24a m24b card_M24 m24_hyp)
open CFSG.Open (pCoreOf)

theorem m24_delta_valid : CodeSetValid 24 m24Delta := by
  have h : ∀ l ∈ m24Sets, PtValid 24 l := by decide
  refine ⟨sortN_sorted _, fun c hc => ?_⟩
  rw [m24Delta, mem_sortN] at hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, h l hl, rfl⟩

theorem m24_ta : (tab 24 m24a).toArray = m24ta.toArray := by rw [m24_tab_a]

theorem m24_tb : (tab 24 m24b).toArray = m24tb.toArray := by rw [m24_tab_b]

theorem m24_card : Nat.card ↥CFSG.Blueprint.NativeSporadic.M24 = 2 ^ 10 * 239085 := by
  rw [card_M24]; norm_num

theorem m24_cert' : BaseCertS 24 (List.range 24)
    (slpTabsA (tab 24 m24a).toArray (tab 24 m24b).toArray m24Prog) m24Qp
    162 213 216 214 217 m24Enum.1 m24Enum.2.1 m24Enum.2.2 10 := by
  rw [m24_ta, m24_tb]
  have : slpTabsA m24ta.toArray m24tb.toArray m24Prog = m24SLP := by simp [m24SLP]
  rw [this]
  exact m24_cert

@[expose] def m24Sg : List ↥CFSG.Blueprint.NativeSporadic.M24 :=
  m24Qp.map fun p => (slpElts m24a m24b m24Prog).getD p.1 1

theorem m24_sGens :
    genTabs 24 m24Sg = m24STabs ∧ Nat.card (Subgroup.closure {x | x ∈ m24Sg}) = 2 ^ 10 := by
  have := sGens_of_baseCertS (n := 24) (List.range 24) (fun b hb => List.mem_range.mp hb)
    base_of_faithful m24a m24b m24Prog m24_valid m24Qp 162 213 216 214 217 m24Enum.1 m24Enum.2.1
    m24Enum.2.2 10 m24_cert'
  refine ⟨?_, this.2⟩
  rw [m24Sg, this.1, m24_ta, m24_tb]
  have : slpTabsA m24ta.toArray m24tb.toArray m24Prog = m24SLP := by simp [m24SLP]
  rw [this]
  rfl

@[expose] def M24LatSpec : Prop :=
  MembersOK (codeSetAct 24) 24 m24ta.toArray m24tb.toArray m24Delta m24LatK ∧
    (∀ g : ↥CFSG.Blueprint.NativeSporadic.M24, lab 24 (codeSetLab 24) m24Delta g = m24Delta ↔
      g ∈ Subgroup.closure {x | x ∈ m24Sg}) ∧
    (∀ Z : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24, Subgroup.closure {x | x ∈ m24Sg} ≤ Z →
      ∃ j ≤ m24LatK.mw.size, Z = memberOrTop m24LatK.mw.size
        (fun j => Subgroup.closure {x | x ∈ m24Sg ++ (m24LatK.mw[j]!).map (wordElt m24a m24b)})
          j) ∧
    O2OK (codeSetAct 24) m24LatK m24OtK ∧
    m24LatK.Om.map (fun o => o.lbl.size) = #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9] ∧
    m24OtK.map (fun o => o.lbl.size) = #[1, 64, 16, 16, 8, 4, 8, 2, 2, 2, 4, 2, 4]

class M24Lat : Prop where
  spec : M24LatSpec

@[expose] noncomputable def m24Ctx
    [M24Lat] : LatCtx ↥CFSG.Blueprint.NativeSporadic.M24 24 (List ℕ) :=
  LatCtx.ofFacts (codeSetLab 24) (CodeSetValid 24) codeSetLab_lawful m24Delta m24_delta_valid
    m24a m24b m24ta.toArray m24tb.toArray m24_ta m24_tb m24_hyp.gen m24LatK m24Sg 10
    m24_sGens.1 m24_sGens.2 239085 (by rw [card_M24]; norm_num) M24Lat.spec.1 M24Lat.spec.2.1
    M24Lat.spec.2.2.1

section Facts


@[expose] def M24InclFact : Prop :=
  ∀ [M24Lat], ∀ j < 13, ∀ jj < 13,
    (m24Ctx.Y j ≤ m24Ctx.Y jj ↔ jj ∈ CFSG.Quasithin.S151S9T.m24Incl[j]!)

open scoped commutatorElement in
@[expose] def M24Idx3Fact : Prop :=
  ∀ [M24Lat],
    CFSG.QuasithinUnique.IsSylowTwoOf m24Ctx.S ⊤ ∧ m24Ctx.S ≤ m24Ctx.Y 8 ∧
    Nat.card ↥(m24Ctx.Y 8) = 3 * Nat.card ↥m24Ctx.S ∧
    (∃ z₀ : ↥CFSG.Blueprint.NativeSporadic.M24, orderOf z₀ = 2 ∧
      CFSG.Quasithin.centerOf m24Ctx.S = Subgroup.zpowers z₀ ∧
      ¬ m24Ctx.Y 8 ≤ Subgroup.centralizer ({z₀} : Set ↥CFSG.Blueprint.NativeSporadic.M24)) ∧
    (∃ x₀ ∈ m24Ctx.Y 8, orderOf x₀ = 3 ∧ ∃ r : Fin 5 → ↥CFSG.Blueprint.NativeSporadic.M24,
      (∀ i, r i ∈ m24Ctx.S) ∧ (∀ i, x₀⁻¹ * r i * x₀ ∈ m24Ctx.S) ∧
      (∀ i, x₀ * r i * x₀⁻¹ ∈ m24Ctx.S) ∧ Function.Injective fun i => ⁅⁅r i, x₀⁆, x₀⁆) ∧
    (∀ α : MulAut ↥CFSG.Blueprint.NativeSporadic.M24, m24Ctx.S.map α.toMonoidHom = m24Ctx.S →
      (m24Ctx.Y 8).map α.toMonoidHom = m24Ctx.Y 8)

@[expose] def M24CenFact : Prop :=
  ∀ [M24Lat], ∀ z₀ : ↥CFSG.Blueprint.NativeSporadic.M24, (tab 24 z₀).toArray = m24SLP[162]! →
    m24Ctx.Y 4 ≤ Subgroup.centralizer ({z₀} : Set ↥CFSG.Blueprint.NativeSporadic.M24)

@[expose] def M24E64Fact : Prop :=
  ∀ [M24Lat], ∀ j : ℕ, (j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6) →
    ∀ y ∈ m24Ctx.Y j, orderOf y = 7 → ∀ a ∈ pCoreOf 2 (m24Ctx.Y j),
      ∀ b ∈ pCoreOf 2 (m24Ctx.Y j), ¬ (a ≠ 1 ∧ b ≠ 1 ∧ a * a = 1 ∧ b * b = 1 ∧
        (y ^ 3 * a * (y ^ 3)⁻¹) * (y ^ 1 * a * (y ^ 1)⁻¹) * a = 1 ∧
        (y ^ 3 * b * (y ^ 3)⁻¹) * (y ^ 2 * b * (y ^ 2)⁻¹) * b = 1 ∧
        ∀ i < 3, ∀ k < 3, (y ^ i * a * (y ^ i)⁻¹) * (y ^ k * b * (y ^ k)⁻¹) =
          (y ^ k * b * (y ^ k)⁻¹) * (y ^ i * a * (y ^ i)⁻¹))

@[expose] def M24T3J4Fact : Prop :=
  ∀ [M24Lat], ∀ c : ↥CFSG.Blueprint.NativeSporadic.M24,
    tab 24 c = CFSG.Quasithin.H13.KGT3J4.starWordTab CFSG.Quasithin.H13.KGT3J4.t3cWord →
    ∀ j < 13, Nat.card (m24Ctx.Y j) = 9 * 2 ^ 10 →
      (wordElt m24a m24b CFSG.Quasithin.H13.KGT3J4.t3yWord)⁻¹ * c *
          wordElt m24a m24b CFSG.Quasithin.H13.KGT3J4.t3yWord ∈ m24Ctx.Y j →
        m24Ctx.Y j ≤ m24Ctx.Y 2

open CFSG.Quasithin.H13.S125KG.M24 in
@[expose] def M24KGFact : Prop :=
  ∀ [M24Lat],
    (wordElt m24a m24b xw ∈ m24Ctx.Y 7 ∧ wordElt m24a m24b (xw ++ xw ++ xw) = 1 ∧
      wordElt m24a m24b xw ≠ 1) ∧
    (wordElt m24a m24b (invW y3w ++ xw ++ y3w) ∉ m24Ctx.Y 2 ∧
      wordElt m24a m24b ([0] ++ xw ++ [0]) ∉ m24Ctx.Y 2) ∧
    (wordElt m24a m24b k1w ∈ m24Ctx.Y 2 ∧ wordElt m24a m24b k2w ∈ m24Ctx.Y 2 ∧
      wordElt m24a m24b k1w = wordElt m24a m24b (commW (kWord c1v) (kWord c1u)) ∧
      wordElt m24a m24b k2w = wordElt m24a m24b (commW (kWord c2v) (kWord c2u)) ∧
      wordElt m24a m24b (w6w ++ invW (kWord kw6)) ∈ m24Ctx.S) ∧
    (∃ Q : Subgroup ↥CFSG.Blueprint.NativeSporadic.M24, Nat.card Q = 64 ∧ Q ≤ m24Ctx.Y 2 ∧
      m24Ctx.Y 2 ≤ Subgroup.normalizer (Q : Set ↥CFSG.Blueprint.NativeSporadic.M24) ∧
      ∀ g ∈ Q, g = 1 ∨ (wordElt m24a m24b vw * g ≠ g * wordElt m24a m24b vw ∧
        wordElt m24a m24b ww * g ≠ g * wordElt m24a m24b ww)) ∧
    (wordElt m24a m24b vw ∈ m24Ctx.Y 2 ∧ wordElt m24a m24b ww ∈ m24Ctx.Y 2 ∧
      wordElt m24a m24b (vw ++ vw ++ vw ++ vw ++ vw ++ vw ++ vw) = 1 ∧
      wordElt m24a m24b vw ≠ 1 ∧ wordElt m24a m24b (ww ++ ww ++ ww) = 1 ∧
      wordElt m24a m24b ww ≠ 1) ∧
    (m24Ctx.gens 3 = [wordElt m24a m24b y3w] ∧ m24Ctx.gens 6 = [wordElt m24a m24b w6w])

end Facts

end CFSG.QuasithinUnique.Ch1.SporLat.M24
