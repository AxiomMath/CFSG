module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Quot
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

theorem nonempty_pQuot_glaPLayer_of_quotient {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (N : Subgroup X) [N.Normal] (hN : ¬ p ∣ Nat.card N) (S : Subgroup (X ⧸ N))
    (hS : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hpS : p ∣ Nat.card ↥S)
    (hSn : ∀ g : X ⧸ N, ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (hc : ⁅(⊤ : Subgroup (X ⧸ N)), (⊤ : Subgroup (X ⧸ N))⁆ ≤ S) :
    Nonempty (PQuot p (GLAPLayer p (⊤ : Subgroup X)) ≃* ↥S) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set π : X →* X ⧸ N := QuotientGroup.mk' N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hNπ : ¬ p ∣ Nat.card π.ker := by
    rw [hker]
    exact hN
  have hlayer : GLAPLayer p (⊤ : Subgroup (X ⧸ N)) = S :=
    glaPLayer_eq_of_isSimple_normal_commutator_le hp le_top (fun g _ s hs => hSn g s hs) hS hnab
      hpS hc
  have hn : (S.subgroupOf (⊤ : Subgroup (X ⧸ N))).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hSn g.1 x hx⟩
  have hcomp : GLAPComponent p (⊤ : Subgroup (X ⧸ N)) S :=
    GL83.PiGen.glaPComponent_of_normal_simple hp le_top hn hnab hpS
  have htop : (⊤ : Subgroup X).map π = ⊤ :=
    Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N)
  have hcomp' : GLAPComponent p ((⊤ : Subgroup X).map π) S := by
    rw [htop]
    exact hcomp
  have hcop : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup X) ⊓ π.ker)) := by
    rw [top_inf_eq, hker]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hN
  obtain ⟨J, hJ, hJS⟩ := GLTheoremB.exists_glaPComponent_map_eq hp π hcop hcomp'
  have hlayerX : GLAPLayer p (⊤ : Subgroup X) = J :=
    S267.glaPLayer_eq_of_map hp π hNπ hJ (by rw [hJS, htop, hlayer])
  rw [hlayerX]
  obtain ⟨e₁⟩ := nonempty_pQuot_equiv_map hp hNπ J
  rw [hJS] at e₁
  have hcore : GLAPPrimeCore p ↥S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥S) with h | h
    · exact h
    · exfalso
      have hcp : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥S)) := CFSG.pPrimeCore_coprime_card
      rw [h, Subgroup.card_top] at hcp
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcp hpS
  exact ⟨e₁.trans ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot)⟩

theorem nonempty_pQuot_glaPLayer_subtype {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (Y : Subgroup G) :
    Nonempty (PQuot p (GLAPLayer p Y) ≃* PQuot p (GLAPLayer p (⊤ : Subgroup ↥Y))) := by
  have hJ : (GLAPLayer p (⊤ : Subgroup ↥Y)).map Y.subtype = GLAPLayer p Y := by
    rw [glaPLayer_map_eq_of_injective hp Y.subtype Y.subtype_injective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hN : ¬ p ∣ Nat.card Y.subtype.ker := by
    rw [Subgroup.ker_subtype, Subgroup.card_bot]
    exact fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
  obtain ⟨e⟩ := nonempty_pQuot_equiv_map hp hN (GLAPLayer p (⊤ : Subgroup ↥Y))
  rw [hJ] at e
  exact ⟨e.symm⟩

end CFSG.LocalAnalysis.GLTheoremA.H301
