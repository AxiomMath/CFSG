module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop115

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

namespace Prop115b

variable {G : Type} [Group G] [Finite G]

noncomputable def quotHomOf {p : ℕ} {C D : Subgroup G} (hDC : D ≤ C) :
    ↥D →* (↥C ⧸ GLAPPrimeCore p ↥C) :=
  (QuotientGroup.mk' (GLAPPrimeCore p ↥C)).comp (Subgroup.inclusion hDC)

theorem map_subgroupOf_quotHomOf {p : ℕ} {C D S : Subgroup G} (hDC : D ≤ C) (hSD : S ≤ D) :
    (S.subgroupOf D).map (quotHomOf (p := p) hDC) = barX p C S := by
  have e : (S.subgroupOf D).map (Subgroup.inclusion hDC) = S.subgroupOf C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx)
    · intro hy
      exact ⟨⟨y, hSD (Subgroup.mem_subgroupOf.1 hy)⟩,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hy), rfl⟩
  unfold quotHomOf barX
  rw [← e, Subgroup.map_map]

theorem coprime_card_ker_quotHomOf {p : ℕ} [Fact p.Prime] {C D : Subgroup G} (hDC : D ≤ C) :
    Nat.Coprime p (Nat.card ↥(quotHomOf (p := p) hDC).ker) := by
  have hle : (quotHomOf (p := p) hDC).ker.map (Subgroup.inclusion hDC) ≤ GLAPPrimeCore p ↥C := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hDC x)).1 (MonoidHom.mem_ker.1 hx)
  have h1 : Nat.card ↥((quotHomOf (p := p) hDC).ker.map (Subgroup.inclusion hDC)) =
      Nat.card ↥(quotHomOf (p := p) hDC).ker :=
    Subgroup.card_map_of_injective (Subgroup.inclusion_injective hDC)
  have hdvd : Nat.card ↥(quotHomOf (p := p) hDC).ker ∣ Nat.card ↥(GLAPPrimeCore p ↥C) := by
    rw [← h1]
    exact Subgroup.card_dvd_of_le hle
  exact Nat.Coprime.coprime_dvd_right hdvd (coprime_card_glaPPrimeCore C)

theorem barX_glaPComponent_of_le {p : ℕ} (hp : p.Prime) {C D J : Subgroup G} (hDC : D ≤ C)
    (hJ : GLAPComponent p D J) : GLAPComponent p (barX p C D) (barX p C J) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : GLAPComponent p (D.subgroupOf D) (J.subgroupOf D) := by
    rw [Subgroup.subgroupOf_self]
    exact glaPComponent_top hJ
  have hker : Nat.Coprime p (Nat.card ↥((D.subgroupOf D) ⊓ (quotHomOf (p := p) hDC).ker)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (coprime_card_ker_quotHomOf hDC)
  have h2 := glaPComponent_map hp (quotHomOf (p := p) hDC) hker h1
  rwa [map_subgroupOf_quotHomOf hDC le_rfl, map_subgroupOf_quotHomOf hDC hJ.1] at h2

theorem glaPComponent_layer_of_le {p : ℕ} (hp : p.Prime) {Q : Type*} [Group Q] [Finite Q]
    {Y T J : Subgroup Q} (hT : GLAPComponent p T J) (hJY : J ≤ Y) (hYT : Y ≤ T) :
    GLAPComponent p (GLAPLayer p Y) J := by
  have hP1 : GLAPComponent p Y J := glaPComponent_of_le hp hT hJY hYT
  have hJL : J ≤ GLAPLayer p Y := le_sSup (s := {L | GLAPComponent p Y L}) hP1
  have hLY : GLAPLayer p Y ≤ Y := sSup_le fun L hL => (show GLAPComponent p Y L from hL).1
  exact glaPComponent_of_le hp hP1 hJL hLY

end Prop115b

open Prop115b in
theorem Prop115b.ident_holds : Prop115.Ident := by
  intro G _ _ m p B M E A h a e ha ha1 he he1 J hJ K hK hJK haC
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, hAsc⟩ := lemma104_ii_holds h.toSec10Fails h.pair
  have hAel : CFSG.Open.IsElemAbelian p A := hAsc.2.1
  have heA : e ∈ A := (Subgroup.mem_inf.1 he).2
  have hAC : A ≤ Cg e := fun x hx => Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
    exact elemAbelian_comm hAel heA hx
  have hapg : IsPGroup p (Subgroup.zpowers a) :=
    isPGroup_of_isElemAbelian' (isElemAbelian_zpowers_of_mem hAel ha)
  have hDeq : Cg2 e a = Cg e ⊓ Subgroup.centralizer ({a} : Set G) := by
    ext x
    simp [Cg2, Cg, Subgroup.mem_centralizer_iff]
  have hcent : barX p (Cg e) (Cg2 e a) = Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨a, haC⟩ : ↥(Cg e))} :
        Set (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e))) := by
    rw [hDeq, barX_inf_centralizer hp haC le_rfl (Subgroup.le_normalizer haC) hapg, barX_self,
      top_inf_eq]
  have hDC : Cg2 e a ≤ Cg e := by
    rw [hDeq]
    exact inf_le_left
  have hPD := barX_glaPComponent_of_le hp hDC hJ
  have hJK' : barX p (Cg e) J ≤ ⨆ y ∈ barX p (Cg e) A, GLBConj y (barX p (Cg e) K) := by
    have hJle : J ≤ ⨆ g ∈ GLAPLayer p (Cg e), GLBConj g J :=
      le_iSup₂_of_le (1 : G) (GLAPLayer p (Cg e)).one_mem (le_of_eq (gLBConj_one J).symm)
    exact (barX_mono (p := p) (hJle.trans hJK)).trans (barX_iSup_conj_le p hAC hK.1)
  refine glaPComponent_layer_of_le hp hPD ?_ ?_
  · exact le_inf hJK' ((barX_mono (p := p) hJ.1).trans hcent.le)
  · rw [hcent]
    exact inf_le_right

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
