module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.Helpers
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeLS
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TripleA7
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.KerThetaTwoCore
public import CFSG.HardMathSupport.Cooperstein.Proving.BlockVNormal

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle

open CFSG CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Cooperstein
open scoped commutatorElement

variable {G : Type} [Group G]

noncomputable def quotCenterOfEquiv {X : Type} [Group X] {N : ℕ} (hN : 4 ≤ N)
    (e : X ≃* alternatingGroup (Fin N)) : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin N) := by
  have hZ : Subgroup.center X = ⊥ := by
    have h1 : Nat.card (Subgroup.center X) = 1 := by
      rw [← Proving.card_center_eq_of_mulEquiv e]
      have hc : Subgroup.center (alternatingGroup (Fin N)) = ⊥ :=
        alternatingGroup.center_eq_bot (by simpa using hN)
      rw [hc]; simp
    exact Subgroup.eq_bot_of_card_eq _ h1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot)).trans e

theorem altNaturalSection_blockV [Finite G]
    (h85 : Coordinator.GF2EightFive) {M S L : Subgroup G} (hX : Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) {N : ℕ} (hN : 9 ≤ N)
    (e : ↥(barM M L) ≃* alternatingGroup (Fin N)) :
    ∃ (φ : ↥L →* alternatingGroup (Fin N)) (ι : G → altHeart N),
      Function.Surjective φ ∧ (∀ l : ↥L, φ l = 1 → (l : G) ∈ S) ∧
      (∀ a ∈ ⁅blockV S L, L⁆, ∀ b ∈ ⁅blockV S L, L⁆, ι (a * b) = ι a + ι b) ∧
      (∀ v ∈ ⁅blockV S L, L⁆, (ι v = 0 ↔ v ∈ Subgroup.centralizer (L : Set G))) ∧
      (∀ (l : ↥L), ∀ v ∈ ⁅blockV S L, L⁆,
        ι ((l : G) * v * (l : G)⁻¹) = Coordinator.altAct (φ l : Equiv.Perm (Fin N)) (ι v)) ∧
      (Even N → SocleLE L (blockV S L) (2 ^ (N - 2))) := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have e' : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin N) :=
    (Coordinator.barMSupCenterEquiv hA hL hSL).symm.trans (quotCenterOfEquiv (by omega) e)
  have hnat := Coordinator.gf2NaturalLSL_of h85 Coordinator.gf2NoFFTripleA7 G M S L hX hA hL hSL N
    (Or.inr (by omega)) ⟨e'⟩
  have hsec : AlternatingGeometry.NaturalSectionLSL S L N := by
    rcases hnat with h | ⟨h7, -⟩
    · exact h
    · omega
  obtain ⟨π, θ, hπ, hker, hAθ, hequiv, hθker⟩ := hsec
  have hLV : ∀ l ∈ L, l ∈ Subgroup.normalizer ((blockV S L : Subgroup G) : Set G) := fun l hl =>
    Coordinator.sup_le_normalizer_blockV S L (Subgroup.mem_sup_left hl)
  have hLU : ∀ (l : ↥L) (v : G), v ∈ ⁅blockV S L, L⁆ →
      (l : G) * v * (l : G)⁻¹ ∈ ⁅blockV S L, L⁆ := fun l v hv =>
    Proving.conj_mem_commutator_of_normalizes (hLV l l.2) (Subgroup.le_normalizer l.2) v hv
  have hperf : ⁅L, L⁆ = L := hL.perfect
  let θL : ↥L →* Equiv.Perm (Fin N) := θ.comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ S))
  have hθalt : ∀ l : ↥L, θL l ∈ alternatingGroup (Fin N) :=
    perm_mem_alternatingGroup_of_perfect hperf θL
  let φ : ↥L →* alternatingGroup (Fin N) := θL.codRestrict _ hθalt
  classical
  let ι : G → altHeart N := fun v =>
    if h : v ∈ ⁅blockV S L, L⁆ then Multiplicative.toAdd (π ⟨v, h⟩) else 0
  refine ⟨φ, ι, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ
    obtain ⟨l, hl⟩ := hAθ σ.1 σ.2
    exact ⟨l, Subtype.ext hl⟩
  · intro l hl
    have h1 : θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = 1 := congrArg Subtype.val hl
    have h2 := hθker _ h1
    exact AlternatingGeometry.inf_centralizer_blockV_le_of_isWeakSBlock hX hA hL (by omega) e'
      ⟨(le_sup_left : L ≤ L ⊔ S) l.2, h2⟩
  · intro a ha b hb
    have hab : a * b ∈ ⁅blockV S L, L⁆ := Subgroup.mul_mem _ ha hb
    simp only [ι, ha, hb, hab, ↓reduceDIte]
    exact congrArg Multiplicative.toAdd (map_mul π ⟨a, ha⟩ ⟨b, hb⟩)
  · intro v hv
    simp only [ι, hv, ↓reduceDIte]
    have h0 : Multiplicative.toAdd (π ⟨v, hv⟩) = 0 ↔ π ⟨v, hv⟩ = 1 := by
      constructor
      · intro h; exact Multiplicative.toAdd.injective h
      · intro h; rw [h]; rfl
    rw [h0, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  · intro l v hv
    have hv' := hLU l v hv
    simp only [ι, hv, hv', ↓reduceDIte]
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π ⟨v, hv⟩))
    have key : ((⟨(l : G) * v * (l : G)⁻¹, hv'⟩ : ↥⁅blockV S L, L⁆) : G) =
        ((⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ : ↥(L ⊔ S)) : G) * ((⟨v, hv⟩ : ↥⁅blockV S L, L⁆) : G) *
          ((⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ : ↥(L ⊔ S)) : G)⁻¹ := rfl
    have := hequiv ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ ⟨v, hv⟩ ⟨(l : G) * v * (l : G)⁻¹, hv'⟩
      key x hx.symm
    rw [this, ← hx, ← Coordinator.altAct_mk]
    rfl
  · intro hev
    have hVe : Open.IsElemAbelian 2 (blockV S L) :=
      CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _
    have hVc : ∀ a ∈ blockV S L, ∀ b ∈ blockV S L, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hLV' : L ≤ Subgroup.normalizer ((blockV S L : Subgroup G) : Set G) := fun l hl => hLV l hl
    have h : SocleLE L (blockV S L) (Nat.card (altHeart N)) :=
      socleLE_of_surjective (L := L) (V := blockV S L) (A := altHeart N) hLV' hVc π hπ hker
    unfold SocleLE at h ⊢
    exact h.trans (card_altHeart_le_of_even (by omega) hev)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle

end
