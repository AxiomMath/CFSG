module

public import CFSG.GH74.Uniqueness.SU.KI1r4Parts
public import CFSG.GH74.Uniqueness.SU.KI1r4TG2a
public import CFSG.GH74.Uniqueness.SU.KI1r4TG2b
public import CFSG.GH74.Uniqueness.SU.KI1r4TKQ

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.K.R3
open CFSG.GH74.Uniqueness.SU.K.R4.L82 CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

@[expose] def Lemma85 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (x : H), Cfg H T x → 4 ≤ Open.twoRank H →
    fittingSubgroup H ≠ ⊥ → generalizedFitting H = fittingSubgroup H

@[expose] def KI1r4Q64 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (x : H) (A R : Subgroup H) (y : H),
    Cfg H T x → 4 ≤ Open.twoRank H → RData T x A R y → generalizedFitting H = R →
      Nat.card R = 64 → SU5.IsL34Type ↥R →
        Nonempty (↥(centralizer ({x} : Set H) ⊓ R) ≃* QuaternionGroup 2) → J2Structure H T

theorem card_frattini_quot_le_four_of_gen {P : Type} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (a b : P) (hgen : zpowers a ⊔ zpowers b = ⊤) : Nat.card (P ⧸ frattini P) ≤ 4 := by
  obtain ⟨hcomm, hsq⟩ := Pow.quot_comm_sq hP
  have h1 : zpowers (a : P ⧸ frattini P) ⊔ zpowers (b : P ⧸ frattini P) = ⊤ := by
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (frattini P))) hgen
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
    exact h2
  have h3 := card_sup_zpowers_le_four hcomm hsq (a : P ⧸ frattini P) (b : P ⧸ frattini P)
  rw [h1] at h3
  simpa using h3

theorem ki1r4TwoGroup_of (h85 : Lemma85) (h87 : KI1r4Q64) : KI1r4TwoGroup := by
  intro H _ _ T x h h4 hFit
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF85 := h85 H T x h h4 hFit
  have hFQ : fittingSubgroup H = CFSG.pCore 2 H := CFSG.Fitting_eq_pcore H 2 h.odd
  set Q : Subgroup H := CFSG.pCore 2 H with hQdef
  have hQn : Q.Normal := CFSG.pCore_normal
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hQne : Q ≠ ⊥ := by rw [← hFQ]; exact hFit
  have hQmax : ∀ N : Subgroup H, N.Normal → IsPGroup 2 N → N ≤ Q := fun N hN hN2 =>
    le_sSup (show N ∈ {K : Subgroup H | K.Normal ∧ IsPGroup 2 K} from ⟨hN, hN2⟩)
  have hgenQ : generalizedFitting H = Q := by rw [hF85, hFQ]
  have hCQ : centralizer (Q : Set H) ≤ Q := by
    have := centralizer_generalizedFitting_le H
    rw [hgenQ] at this
    exact this
  obtain ⟨A, hAn, hAel, hAne, hAQ, hAc⟩ := exists_normal_elemAb_central hQn hQ2 hQne
  obtain ⟨y, hR⟩ := Cfg.rdata h hAn hAel hAne
  set R : Subgroup H := (T : Subgroup H) ⊓ centralizer (A : Set H) with hRdef
  have hQT : Q ≤ (T : Subgroup H) := hQ2.le_sylow_of_normal T
  have hQR : Q ≤ R := le_inf hQT (fun q hq => by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hAc a ha q hq)
  have hRT : R ≤ (T : Subgroup H) := inf_le_left
  have hTrank : 4 ≤ Open.pRank 2 (T : Subgroup H) := by
    rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq T]; exact h4
  have hR82 := hR.lemma82 le_rfl hR.x_norm hR.y_norm
  unfold Lemma82Concl at hR82
  obtain ⟨h64, hZ4, hfr, -, hcom, hcsq, hQ8⟩ : (Nat.card R = 64 ∧ Nat.card (center ↥R) = 4 ∧
      frattini ↥R = center ↥R ∧ (∀ u : ↥R, u * u ∈ center ↥R) ∧
      (∀ u v : ↥R, ⁅u, v⁆ ∈ center ↥R) ∧ (∀ a ∈ center ↥R, a * a = 1) ∧
      Nonempty (↥(centralizer ({x} : Set H) ⊓ R) ≃* QuaternionGroup 2)) := by
    rcases hR82 with ⟨hab, c, hcR, -, hgen, -⟩ | hb
    · exfalso
      have := hR.pRank_T_le_three hab ⟨c, hcR, hgen⟩
      omega
    · exact hb
  have hQeqR : Q = R := by
    have hQ82 := hR.lemma82 hQR (fun q hq => hQn.conj_mem q hq x)
      (fun q hq => hQn.conj_mem q hq y)
    unfold Lemma82Concl at hQ82
    rcases hQ82 with ⟨hab, c, hcQ, -, hgen, -⟩ | ⟨h64Q, -⟩
    · exfalso
      have hd : y * c * y⁻¹ ∈ Q := hQn.conj_mem c hcQ y
      have hgen' : zpowers (⟨c, hcQ⟩ : ↥Q) ⊔ zpowers (⟨y * c * y⁻¹, hd⟩ : ↥Q) = ⊤ := by
        apply Subgroup.map_injective Q.subtype_injective
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
          ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        exact hgen
      have hV := card_frattini_quot_le_four_of_gen hQ2 _ _ hgen'
      have hidx := index_le_two_of_frattini_quot_le_four T Q hQn hQ2 hQmax hCQ hQT hV
      have hmul := Subgroup.relIndex_mul_relIndex Q R (T : Subgroup H) hQR hRT
      have hTR : R.relIndex (T : Subgroup H) ≠ 1 := by
        intro h1
        have := (Subgroup.relIndex_eq_one.mp h1) h.xT
        exact hR.x_not_mem this
      have hTR0 : R.relIndex (T : Subgroup H) ≠ 0 := SU1.relIndex_ne_zero_of_finite _ _
      have hQR0 : Q.relIndex R ≠ 0 := SU1.relIndex_ne_zero_of_finite _ _
      have hQRone : Q.relIndex R = 1 := by
        have h1 : Q.relIndex R * R.relIndex (T : Subgroup H) ≤ 2 := by
          rw [hmul]; exact hidx
        by_contra hne
        have : 2 ≤ Q.relIndex R := by omega
        have : 2 ≤ R.relIndex (T : Subgroup H) := by omega
        nlinarith
      have hRleQ : R ≤ Q := Subgroup.relIndex_eq_one.mp hQRone
      have hRQ : R = Q := le_antisymm hRleQ hQR
      have hcenter : Nat.card (center ↥R) = Nat.card ↥R := by
        have : center ↥R = ⊤ := by
          rw [Subgroup.eq_top_iff']
          intro u
          rw [Subgroup.mem_center_iff]
          intro v
          exact Subtype.ext (hab v (hRQ ▸ v.2) u (hRQ ▸ u.2))
        rw [this, Subgroup.card_top]
      omega
    · exact Subgroup.eq_of_le_of_card_ge hQR (by rw [h64Q, h64])
  have hgenR : generalizedFitting H = R := by rw [hgenQ, hQeqR]
  have hinv : ∃ e : ↥R, e * e = 1 ∧ e ∉ center ↥R := by
    obtain ⟨E, hET, hEel, hEcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two
      (H := (T : Subgroup H)) (k := 4) hTrank
    have hTR : ∀ e ∈ E, e ∈ R ∨ x * e ∈ R := fun e he => by
      have := hR.T_eq ▸ hET he
      exact mem_or_mul_mem_of_mem_sup_zpowers_norm hR.x_sq hR.x_norm this
    have hle := card_le_two_mul_inf_of_mul_mem hTR
    rw [hEcard] at hle
    by_contra hno
    push Not at hno
    have hEsq : ∀ e ∈ E, e * e = 1 := fun e he => by
      have := (SU1.isElemAbelian_iff.mp hEel).2 e he
      rwa [pow_two] at this
    let g : ↥(E ⊓ R) → center ↥R := fun k =>
      ⟨⟨k, (Subgroup.mem_inf.mp k.2).2⟩, hno ⟨k, (Subgroup.mem_inf.mp k.2).2⟩
        (Subtype.ext (hEsq k (Subgroup.mem_inf.mp k.2).1))⟩
    have hg : Function.Injective g := fun a b hab =>
      Subtype.ext (congrArg (fun z => ((z.1 : ↥R) : H)) hab)
    have := Nat.card_le_card_of_injective g hg
    omega
  have hL34 : SU5.IsL34Type ↥R := hR.isL34Type_of_special h64 hZ4 hfr hcom hcsq hinv
  refine ⟨?_, h87 H T x A R y h h4 hR hgenR h64 hL34 hQ8⟩
  rw [hgenR]
  exact hRT

end CFSG.GH74.Uniqueness.SU.K.R4
