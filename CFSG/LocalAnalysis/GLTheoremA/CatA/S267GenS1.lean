module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenBridge
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_PartI
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Quot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem genStep1On_of_leaves {Q : TauCeti.LieTypeIndex → Prop} (h1 : GenGood) : GenStep1On Q := by
  intro p q Ω _ _ S B H
  obtain ⟨d, -, -, hOdd⟩ := H.exists_oddLie
  have hp := H.pPrime
  have hA := isElemAbelian_range (H.le_normalizer B) H.elem
  have hA3 := H.pow_three_le_card_range
  set ψ := normalizerToCenterQuotientAut S B (H.le_normalizer B)
  have hA2 : p ^ 2 ≤ Nat.card ψ.range :=
    (Nat.pow_le_pow_right hp.pos (by norm_num)).trans hA3
  have hne : Nat.card ψ.range ≠ p ^ 2 := fun h => by
    rw [h] at hA3
    exact absurd hA3 (not_le.2 (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  rcases h1 p _ d hOdd H.dvd_card ψ.range hA hA2 with ⟨a, ha, ha1, hlay⟩ | ⟨-, hc⟩
  · obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 ha
    have hlayS : GLAPLayer p (S ⊓ Subgroup.centralizer ({(b : Ω)} : Set Ω)) ≠ ⊥ := fun h =>
      hlay ((glaPLayer_inf_centralizer_eq_bot_iff hp (H.le_normalizer B) b).1 h)
    obtain ⟨J, hJ⟩ := (S267.glaPLayer_ne_bot_iff p _).1 hlayS
    exact ⟨b, J, ⟨H.elem, H.cent, Or.inl rfl⟩, b.2,
      fun hbC => ha1 ((H.aut_eq_one_iff B b).2 hbC), hJ⟩
  · exact absurd hc hne

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem mem_centralizer_of_centMod {p : ℕ} (hp : p.Prime) {L : Subgroup Ω}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hpL : p ∣ Nat.card L) {x : Ω} (hc : CentMod p L x) :
    x ∈ Subgroup.centralizer (L : Set Ω) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcore : GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L := by
    refine le_center_of_normal_of_isQuasisimple hq (GLAPPrimeCore.normal p _) fun htop => ?_
    have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥L)) := CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpL
  set σ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hc.1⟩
  have hσm : ∀ m : ↥L, (σ m : Ω) = x * m * x⁻¹ := fun m => rfl
  have h1 : σ = 1 := by
    refine S267.automorphism_eq_one_of_center_quot hq.1 σ fun m => hcore ?_
    have hm : ⁅(m : Ω), x⁆ ∈ GLAPPrimeCoreOf p L :=
      hc.2 (Subgroup.commutator_mem_commutator m.2 (Subgroup.mem_zpowers x))
    change ⁅(m : Ω), x⁆ ∈ (GLAPPrimeCore p ↥L).map L.subtype at hm
    obtain ⟨o, ho, hoe⟩ := Subgroup.mem_map.1 hm
    have hoe' : (o : Ω) = ⁅(m : Ω), x⁆ := hoe
    have he : m * (σ m)⁻¹ = o := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hσm, hoe', commutatorElement_def]
      group
    rw [he]
    exact ho
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have h2 : (σ ⟨m, hm⟩ : Ω) = m := by
    rw [h1]
    rfl
  rw [hσm] at h2
  calc m * x = x * m * x⁻¹ * x := by rw [h2]
    _ = x * m := by group

theorem genStepCentOn_of_leaves {Q : TauCeti.LieTypeIndex → Prop} (h2 : GenCompQuasiOn Q) :
    GenStepCentOn Q := by
  intro p q Ω _ _ S B H d J hdp hdS hJ b hb
  obtain ⟨e, -, hQe, hOdd⟩ := H.exists_oddLie
  have hp := H.pPrime
  have hJ₁ := glaPComponent_fixSubgroup_of_inf_centralizer hp (H.le_normalizer ⊤)
    ⟨d, Subgroup.mem_top d⟩ hJ
  set ψ := normalizerToCenterQuotientAut S ⊤ (H.le_normalizer ⊤)
  have hxp : ψ ⟨d, Subgroup.mem_top d⟩ ^ p = 1 := by
    rw [← map_pow, show (⟨d, Subgroup.mem_top d⟩ : ↥(⊤ : Subgroup Ω)) ^ p = 1 from
      Subtype.ext hdp, map_one]
  have hx1 : ψ ⟨d, Subgroup.mem_top d⟩ ≠ 1 := fun h => hdS ((H.aut_eq_one_iff ⊤ _).1 h)
  have hqJ : CFSG.Open.IsQuasisimple ↥J :=
    isQuasisimple_of_map_mk (hJ.1.trans inf_le_left) (glaPComponent_perfect hJ)
      (h2 p _ e hOdd hQe _ hxp hx1 _ hJ₁).2.2
  exact mem_centralizer_of_centMod hp hqJ
    (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116pI_pcomp_card_dvd hp hJ) hb

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
