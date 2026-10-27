module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Links
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Transfer

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

@[expose] def ExcType (X : Type) [Group X] : Prop :=
  Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f

@[expose] def Sol78RankOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → CFSG.pRank 2 X = 1 → ExcType X

@[expose] def Sol78ExcClosed : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), CFSG.IsQuasisimple X →
    CFSG.IsQuasisimple ↥K → ExcType X → ExcType ↥K

section

variable {H : Type} [Group H]

theorem notExc_iff {K : Subgroup H} : NotExc K ↔ ¬ ExcType ↥K := by
  unfold NotExc ExcType
  exact not_or.symm

theorem ExcType.of_cqEquiv {X Y : Type} [Group X] [Group Y]
    (e : (X ⧸ center X) ≃* (Y ⧸ center Y)) (h : ExcType Y) : ExcType X := by
  rcases h with h | ⟨p, f, hp, hp2, hmodel⟩
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.trans f⟩
  · exact Or.inr ⟨p, f, hp, hp2, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hmodel⟩

@[expose] def LConn (K M : Subgroup H) : Prop := Conn (fun _ _ _ => True) K M

theorem LConn.trans {K M N : Subgroup H} (h₁ : LConn K M) (h₂ : LConn M N) : LConn K N :=
  Conn.trans h₁ h₂

theorem LConn.refl {K T : Subgroup H} (hT : IsPGroup 2 T)
    (hK : IsCompIn K (centralizer (T : Set H))) : LConn K K :=
  ⟨0, fun _ => K, fun _ => T, fun _ => 1, ⟨fun _ _ => ⟨hT, hK⟩, fun i h1 h2 => by omega,
    fun i h1 h2 => by omega, fun i h1 h2 => by omega⟩, rfl, rfl, fun _ _ _ => trivial⟩

theorem JConn.toLConn {K M : Subgroup H} (hc : JConn K M) : LConn K M := by
  obtain ⟨m, L, T, s, hl, h0, hm, -, -⟩ := hc
  exact ⟨m, L, T, s, hl, h0, hm, fun _ _ _ => trivial⟩

variable [Finite H]

theorem notExc_of_le (hD : Sol78ExcClosed) {K X : Subgroup H} (hK : CFSG.IsQuasisimple ↥K)
    (hX : CFSG.IsQuasisimple ↥X) (hKX : K ≤ X) (h : NotExc K) : NotExc X := by
  rw [notExc_iff] at h ⊢
  intro hexc
  have hKq : CFSG.IsQuasisimple ↥(K.subgroupOf X) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKX).symm hK
  exact h (ExcType.of_cqEquiv (cqEquivOfEquiv (Subgroup.subgroupOfEquivOfLe hKX).symm)
    (hD ↥X (K.subgroupOf X) hX hKq hexc))

theorem Sol78Links.notExc (hD : Sol78ExcClosed) {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (h : Sol78Links H m L T s) (h0 : NotExc (L 0)) : ∀ i ≤ m, NotExc (L i) := by
  intro i
  induction i with
  | zero => exact fun _ => h0
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    rcases h.link (i + 1) (by omega) hi with ⟨-, ⟨e⟩⟩ | ⟨hEq, -⟩
    · exact hprev.of_cqEquiv e
    · have hincl : L i ≤ L (i + 1) ⊔ (L (i + 1)).map (MulAut.conj (s (i + 1))).toMonoidHom :=
        (h.incl (i + 1) (by omega) hi).1
      rw [← hEq, sup_idem] at hincl
      exact notExc_of_le hD (h.comp i (by omega)).2.isQuasisimple
        (h.comp (i + 1) hi).2.isQuasisimple hincl hprev

theorem LConn.notExc (hD : Sol78ExcClosed) {K M : Subgroup H} (h : LConn K M) (hK : NotExc K) :
    NotExc M := by
  obtain ⟨m, L, T, s, hl, h0, hm, -⟩ := h
  rw [← hm]
  exact Sol78Links.notExc hD hl (h0 ▸ hK) m le_rfl

end

end CFSG.EvenSporadicStandard.Induction.Junction
