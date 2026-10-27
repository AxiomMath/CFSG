module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MAlt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154AmbU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Chev2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Quot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped commutatorElement

section Small


theorem t158m_oddInner_of_card_two {S : Type} [Group S] [Finite S] (hz : Subgroup.center S = ⊥)
    (hA : Nat.card (MulAut S) = 2 * Nat.card S) :
    ∀ φ : MulAut S, Odd (orderOf φ) → ∃ g : S, φ = MulAut.conj g := by
  intro φ hφ
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h3 := congrArg (fun φ : MulAut S => φ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    rw [hz, Subgroup.mem_bot] at hc
    exact hc
  have hinner : Nat.card (inner S) = Nat.card S := Nat.card_range_of_injective hinj
  have hidx := (inner S).card_mul_index
  rw [hinner, hA] at hidx
  have hS0 : 0 < Nat.card S := Nat.card_pos
  have h2 : (inner S).index = 2 := by
    have h' : Nat.card S * (inner S).index = Nat.card S * 2 := by rw [hidx]; ring
    exact Nat.eq_of_mul_eq_mul_left hS0 h'
  have hsq : φ ^ 2 ∈ inner S := by
    have := Subgroup.pow_index_mem (inner S) φ
    rwa [h2] at this
  obtain ⟨k, hk⟩ := hφ
  have hpow : φ ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one φ
  have h1 : φ * (φ ^ 2) ^ k = 1 := by rw [← pow_mul, ← pow_succ']; exact hpow
  have hmem : φ ∈ inner S := by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hsq k)
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, hg.symm⟩


theorem t158m_oddInner_u42 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) :
    ∀ φ : MulAut S, Odd (orderOf φ) → ∃ g : S, φ = MulAut.conj g := by
  have hcard : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have hpq : q.p = 2 := by
    have hdvd : q.p ∣ 2 := by
      rw [← hcard]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
  have hfq : q.exponent = 1 := by
    rw [hpq] at hcard
    exact Nat.pow_right_injective (le_refl 2) (show 2 ^ q.exponent = 2 ^ 1 by simpa using hcard)
  have hmodel : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group
      CFSG.Open.StatedLieTag.PSU 4 2 1 := by
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group)
    rw [hpq, hfq] at h
    exact Or.inl ⟨by decide, h⟩
  obtain ⟨hAut, hSc⟩ := CFSG.EvenSporadicStandard.M22Std.card_mulAut_of_lieModel_psu42 hmodel
  have hAutS : Nat.card (MulAut S) = 51840 := (Nat.card_congr (MulAut.congr e).toEquiv).trans hAut
  have hSS : Nat.card S = 25920 := (Nat.card_congr e.toEquiv).trans hSc
  exact t158m_oddInner_of_card_two (chev_center_eq_bot_of_simple_nonabelian hna)
    (by rw [hAutS, hSS])

theorem t158m_chevAut_ne_one {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {X L : Subgroup G} {y : G}
    (hL : GLAPComponent p X L) (hchev : IsChevSimple 2 (PSimple p L)) (hFG : FGOn p y L) :
    chevAut p L ⟨y, t158m_fgOn_normalizer hFG⟩ ≠ 1 := by
  intro h1
  have hyN := t158m_fgOn_normalizer hFG
  have hin : InducesInnerMod p L y := by
    refine (chevAut_mem_inner_iff hp hL hyN).1 ?_
    rw [h1]
    exact Subgroup.one_mem _
  have hInn : InnDiagOn p (Subgroup.zpowers y) L := MI.inner_innDiag_any hL hchev hyN hin
  rcases hFG with hF | ⟨hNI, -, -⟩
  · exact (MI.field_nonInnDiag_any hL hF).2 hInn
  · exact hNI.2 hInn

theorem t158m_false_of_L28 {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {X L : Subgroup G} {y : G}
    (hL : GLAPComponent p X L) (hchev : IsChevSimple 2 (PSimple p L)) (hyp : y ^ p = 1) (hFG : FGOn p y L)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq : q.card = 8)
    (e : PSimple p L ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group)
    (hlayer : GLAPLayer p (L ⊓ Subgroup.centralizer ({y} : Set G)) ≠ ⊥) : False := by
  have hyN := t158m_fgOn_normalizer hFG
  have hyp' : IsPGroup p (Subgroup.zpowers y) :=
    isPGroup_of_isElemAbelian (t158m_elemAbelian_zpowers hyp)
  obtain ⟨M, hM⟩ := (CFSG.LocalAnalysis.GLTheoremA.S267.glaPLayer_ne_bot_iff p _).1 hlayer
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group := Finite.of_equiv _ e.toEquiv
  have hα1 := t158m_chevAut_ne_one hp hL hchev hFG
  have hJ' := glaPComponent_chevTransfer hp hyN hyp' hM
  obtain ⟨hLe, -⟩ := chevQ_transport hp e hJ'
  exact ambiguous_L28_noPComponent hv hq _
    (fun h => hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))) _ hLe

theorem t158m_false_of_chev2Small {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X L : Subgroup G} {y : G} (hL : GLAPComponent p X L) (hchev : IsChevSimple 2 (PSimple p L))
    (hsmall : catalogIs (PSimple p L) chev2Small) (hyp : y ^ p = 1) (hFG : FGOn p y L)
    (hlayer : GLAPLayer p (L ⊓ Subgroup.centralizer ({y} : Set G)) ≠ ⊥) : False := by
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian hp hL
  haveI := hsimple
  obtain ⟨i, hi, ⟨e⟩⟩ := hsmall
  cases i with
  | cyclic _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | alternating n hn =>
    have hamb : catalogIs (PSimple p L) l154AmbAlt :=
      ⟨TauCeti.CFSGIndex.alternating n hn,
        ⟨by rcases hi with rfl | rfl | rfl <;> simp [ambiguousChev], by simp [l154AmbU33, onLie]⟩, ⟨e⟩⟩
    exact t158m_fgOn_false_of_oddInner hp hp2 hL hchev hyp hFG (l154_oddInner_of_ambAlt hamb)
  | lie d =>
    obtain ⟨d0, hv⟩ := d
    cases d0 with
    | A r q =>
      rcases r with _ | _ | r
      · exact hi.elim
      · rcases hi with h7 | h8
        · have hamb : catalogIs (PSimple p L) l154AmbAlt :=
            ⟨TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩, ⟨by simpa [ambiguousChev] using h7, by simp [l154AmbU33, onLie]⟩, ⟨e⟩⟩
          exact t158m_fgOn_false_of_oddInner hp hp2 hL hchev hyp hFG (l154_oddInner_of_ambAlt hamb)
        · exact t158m_false_of_L28 hp hL hchev hyp hFG hv h8 e hlayer
      · exact hi.elim
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · exact hi.elim
      · exact hi.elim
      · have hamb : catalogIs (PSimple p L) l154AmbU33 := ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩, hi, ⟨e⟩⟩
        exact t158m_fgOn_false_of_oddInner hp hp2 hL hchev hyp hFG (l154_oddInner_of_u33 hamb)
      · exact t158m_fgOn_false_of_oddInner hp hp2 hL hchev hyp hFG (t158m_oddInner_u42 hna hv hi e)
      · exact hi.elim
    | _ => exact hi.elim

end Small

end CFSG.LocalAnalysis.GLTheoremA.T158

end
