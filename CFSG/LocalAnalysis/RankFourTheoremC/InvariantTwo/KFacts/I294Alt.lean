module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294AltPerm
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.IsolatedPlanes
public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC Subgroup Equiv Equiv.Perm
open scoped commutatorElement

@[expose] def KD29Alt : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (L ≃* alternatingGroup (Fin n))) →
    ¬ IsLinearOrUnitaryAt p L → centralizer (L : Set X) = ⊥ →
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) →
    (∃ x ∈ L, orderOf x = p ∧ CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) →
    ∀ d ∈ L, d ≠ 1 → d ^ p = 1 →
      GLAPLayer p (centralizer ({d} : Set X)) = ⊥ ∧
      GLAPPrimeCoreOf p (centralizer ({d} : Set X)) = ⊥

theorem center_eq_bot_of_simple_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : center G = ⊥ := by
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b
    exact hab this.symm

theorem isPerfect_of_simple_nonabelian' {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have h1 : ⁅a, b⁆ ∈ commutator G := commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  · exact h

theorem i294Alt_false {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Type} [Group X] [Finite X]
    (L : Subgroup X) [L.Normal] [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a) {n : ℕ}
    (hn5 : 5 ≤ n) (e : L ≃* alternatingGroup (Fin n)) (hcen : centralizer (L : Set X) = ⊥)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {x : X} (hxL : x ∈ L) (hxo : orderOf x = p)
    (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  let ι : X →* MulAut L := MulAut.conjNormal
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hg ⟨h, hh⟩)
      have h2 : g * h * g⁻¹ = h := by simpa [ι, MulAut.conjNormal_apply] using h1
      calc h * g = (g * h * g⁻¹) * g := by rw [h2]
        _ = g * h := by group
    rw [hcen, Subgroup.mem_bot] at hgc
    exact hgc
  haveI : Group.IsPerfect L := isPerfect_of_simple_nonabelian' hnab
  have hcenter : center L = ⊥ := center_eq_bot_of_simple_nonabelian hnab
  let e' : (L ⧸ center L) ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans (QuotientGroup.quotientBot.trans e)
  have h1 := CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt ι hι
  have h2 := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_aut_le hn5 e' hp hp2
  have h3n : 3 ≤ n / p := h3.trans (h1.trans h2)
  set y : alternatingGroup (Fin n) := e ⟨x, hxL⟩ with hy
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hyp : ((y : Perm (Fin n))) ^ p = 1 := by
    have h4 : y ^ p = 1 := by
      rw [hy, ← map_pow]
      have : (⟨x, hxL⟩ : L) ^ p = 1 := Subtype.ext (by simpa using hxp)
      rw [this, map_one]
    simpa using congrArg Subtype.val h4
  obtain ⟨B, _, F, hcomm, hpow, hB, hFinj, hFc⟩ :=
    exists_hom_elemAbelian_commute_of_pow_eq_one hp2 n (Fin n) (Fintype.card_fin n)
      (y : Perm (Fin n)) hyp
  have hsign : ∀ b, F b ∈ alternatingGroup (Fin n) := by
    intro b
    rw [Equiv.Perm.mem_alternatingGroup]
    have h4 : sign (F b) ^ p = 1 := by rw [← map_pow, ← map_pow, hpow b, map_one, map_one]
    rcases Int.units_eq_one_or (sign (F b)) with h5 | h5
    · exact h5
    · exfalso
      rw [h5, Odd.neg_one_pow (hp.odd_of_ne_two hp2)] at h4
      exact absurd h4 (by decide)
  let F1 : B →* alternatingGroup (Fin n) := F.codRestrict _ hsign
  let F2 : B →* X := L.subtype.comp (e.symm.toMonoidHom.comp F1)
  have hF2inj : Function.Injective F2 :=
    Subtype.val_injective.comp
      (e.symm.injective.comp (fun a b hab => hFinj (congrArg Subtype.val hab)))
  have hF2range : F2.range ≤ centralizer ({x} : Set X) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h5 : Commute (F1 b) y := Subtype.ext (hFc b).eq
    have h6 : Commute (e.symm (F1 b)) (e.symm y) := h5.map e.symm
    have h7 : e.symm y = ⟨x, hxL⟩ := by rw [hy, MulEquiv.symm_apply_apply]
    rw [h7] at h6
    exact congrArg Subtype.val h6.eq
  have h9 := CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm hpow hB F2 hF2inj hF2range
  omega

theorem kd29Alt_holds : KD29Alt := by
  intro p hp hp5 X _ _ L _ hs hn _ halt _ hcen hrank hex d _ _ _
  obtain ⟨n, hn5, ⟨e⟩⟩ := halt
  obtain ⟨x, hxL, hxo, hx2⟩ := hex
  exact (i294Alt_false hp hp5 L hn hn5 e hcen hrank hxL hxo hx2).elim

end CFSG.LocalAnalysis.RankFourTheoremC
