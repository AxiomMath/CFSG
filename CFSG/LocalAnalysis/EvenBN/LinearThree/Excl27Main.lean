module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseACommon
public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBModule
public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27Layer
public import CFSG.LocalAnalysis.EvenBN.LinearThree.Excl27Field
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseAFieldAut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6B3
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.OddStandard.Seitz77 (Datum)
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CaseBModule

noncomputable def sl2RingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (by ext A i j; simp) (by ext A i j; simp)

namespace WData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}
  {K : Type} [Field K]

noncomputable abbrev torBar (w : WData d Vi q) (D : LeviData A Vi K) (l : Kˣ) : w.Nbar :=
  w.projBar ⟨D.tor l, tor_mem_N w D l⟩

theorem torBar_comm_tbar (w : WData d Vi q) (D : LeviData A Vi K) (l : Kˣ) :
    w.torBar D l * w.tbar = w.tbar * w.torBar D l := by
  rw [show w.tbar = w.projBar w.tN from rfl, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (d.comm_t_of_mem (D.tor_mem l))

theorem torBar_pow [Finite K] (w : WData d Vi q) (D : LeviData A Vi K) (l : Kˣ) :
    w.torBar D l ^ (Nat.card K - 1) = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [← map_pow]
  have hlp : l ^ (Nat.card K - 1) = 1 := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_units]
    exact pow_card_eq_one
  have : (⟨D.tor l, tor_mem_N w D l⟩ : w.N) ^ (Nat.card K - 1) = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, ← map_pow, hlp, map_one]
    rfl
  rw [this, map_one]

theorem torBar_comm_Ltil (w : WData d Vi q) (D : LeviData A Vi K) (l : Kˣ) :
    ∀ j ∈ w.Ltil D.lev.range, w.projTil (w.torBar D l) * j = j * w.projTil (w.torBar D l) := by
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨B, hB⟩ := mem_subgroupOf.mp hz
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  change D.tor l * (z : G) = (z : G) * D.tor l
  rw [← hB]
  exact D.tor_comm l B

theorem projTil_eq_one_of_actB_eq_one [Finite G] (w : WData d Vi q) {x : w.Nbar}
    (hx : actB w x = 1) : w.projTil x = 1 := by
  obtain ⟨n', hn'⟩ := QuotientGroup.mk'_surjective w.WN x
  have hn'' : w.projBar n' = x := hn'
  have hnC : (n' : G) ∈ centralizer (w.W : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨x', rfl⟩ := exists_cW_eq w hy
    have h4 := cW_actB w n' x'
    rw [hn'', hx, Module.End.one_apply] at h4
    calc cW w x' * n' = ((n' : G) * cW w x' * (n' : G)⁻¹) * n' := by rw [← h4]
      _ = n' * cW w x' := by group
  have h5 := w.projTil_projBar_eq_one hnC
  rwa [hn''] at h5

@[expose] noncomputable def torusData {f : ℕ} (hf : 1 ≤ f) (w : WData d Vi (2 ^ f)) [Finite K]
    (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f) (l : Kˣ) : TorusData K (Additive w.WN) :=
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right d.t_mul_self
  have hcWt : ∀ x, cW w (actB w w.tbar x) = d.t * cW w x * d.t := fun x => by
    rw [cW_actB w w.tN x, htinv]
  { f := f
    one_le := hf
    card_K := hKc
    τ := actB w w.tbar
    τ_mul_self := by rw [← map_mul, tbar_mul_self w, map_one]
    ι := ιW w D
    ι_injective := fun u v huv => by
      have h1 := congrArg (cW w) huv
      rw [cW_ιW, cW_ιW] at h1
      exact Multiplicative.ofAdd.injective (D.ι_injective h1)
    τ_ι := fun v => by
      apply cW_injective w
      rw [hcWt, cW_ιW]
      have hc := mem_centralizer_singleton_iff.mp (w.le_centralizer_t (D.ι_mem_W
        (Multiplicative.ofAdd v)))
      rw [← hc, mul_assoc, d.t_mul_self, mul_one]
    exists_ι := fun m hm => by
      have h1 := congrArg (cW w) hm
      rw [hcWt] at h1
      have hmV : cW w m ∈ Vi := by
        have h2 : cW w m ∈ w.W ⊓ centralizer ({d.t} : Set G) := by
          refine ⟨cW_mem w m, mem_centralizer_singleton_iff.mpr ?_⟩
          calc cW w m * d.t = d.t * cW w m * d.t * d.t := by rw [h1]
            _ = d.t * cW w m := by rw [mul_assoc _ d.t d.t, d.t_mul_self, mul_one]
        rwa [w.fix] at h2
      have hmV' : cW w m ∈ D.ι.range := by rw [D.range_ι]; exact hmV
      obtain ⟨u, hu⟩ := hmV'
      exact ⟨Multiplicative.toAdd u, cW_injective w (by rw [cW_ιW, ofAdd_toAdd, hu])⟩
    h₀ := actB w (w.torBar D l)
    c := (l : K) ^ 3
    h₀_τ := by rw [← map_mul, w.torBar_comm_tbar D l, map_mul]
    h₀_ι := fun v => by
      apply cW_injective w
      rw [cW_actB, cW_ιW, cW_ιW]
      exact D.tor_conj l (Multiplicative.ofAdd v)
    c_ne_zero := pow_ne_zero _ l.ne_zero
    h₀_pow := by rw [← map_pow, w.torBar_pow D l, map_one] }

omit [Field K] in
theorem card_additive_WN {f : ℕ} (w : WData d Vi (2 ^ f)) [Finite K] (hKc : Nat.card K = 2 ^ f) :
    Nat.card (Additive w.WN) = Nat.card K ^ 4 := by
  change Nat.card w.WN = _
  rw [Nat.card_congr (subgroupOfEquivOfLe w.W_le_N).toEquiv, w.card, hKc]

end WData

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem not_lieModel_PSL3 (hf : 3 ≤ f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f))
    {K : Type} [Field K] [Finite K] (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f)
    (hlayer : SteinbergBV.OneOrTwoLayerConclusion (w.Ltil D.lev.range) w.ttil)
    (hmodel : LieModel (CFSG.layer w.Ntil) .PSL 3 2 f) : False := by
  classical
  have : CharP K 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hKc
  have : Fintype K := Fintype.ofFinite K
  have : (CFSG.layer w.Ntil).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨-, -, hJE, hDE, -, -, hfaith⟩ := id hlayer
  obtain ⟨K', _, _, hK', ⟨η⟩⟩ :=
    RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hmodel
  have : Fintype K' := Fintype.ofFinite K'
  have hKK : Nat.card K' = Nat.card K := by rw [hK', hKc]
  obtain ⟨lam, hlam⟩ := exists_ltilEquiv (by omega) w hKc D
  have hringK : K ≃+* K' := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hKK])
  let LD : Layer.Data w.Ntil (CFSG.layer w.Ntil) K' f :=
    { η := η
      three_le := hf
      card := hK'
      faith := fun x hx => hfaith x (hDE ▸ hx)
      t := w.ttil
      orderOf_t := w.orderOf_ttil
      J := w.Ltil D.lev.range
      J_le := hJE
      J_equiv := ⟨lam.symm.trans (sl2RingEquiv hringK)⟩
      t_comm := fun j hj => (mem_centralizer_iff.mp (w.ttil_mem_centralizer D) j hj).symm }
  have hcomm : ⁅standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥ := by
    refine Hyp.commutator_oddCore_Ebar_of_conj hf d hR hW hN w D hKc
      fun z hz htz _ => ?_
    have htz2 : (w.ttil * z) ^ 2 = 1 := by
      have h2 := pow_orderOf_eq_one (w.ttil * z)
      rwa [htz] at h2
    obtain ⟨m, -, hm⟩ := LD.exists_conj_eq_mul (hJE hz) htz2
    exact ⟨m, hm⟩
  obtain ⟨l, hl⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hlord : orderOf l = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hl, Nat.card_units]
  set hb : w.Nbar := w.torBar D l with hhb
  have hbt : hb * w.tbar = w.tbar * hb := w.torBar_comm_tbar D l
  have hbpow : hb ^ (Nat.card K - 1) = 1 := w.torBar_pow D l
  have hodd : Odd (Nat.card K - 1) := by
    rw [hKc, Nat.odd_iff]
    have h3 : 2 ^ f = 2 * 2 ^ (f - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h4 : 1 ≤ 2 ^ (f - 1) := Nat.one_le_two_pow
    omega
  have hbO : hb ∈ standardComponentOddCore w.Nbar := by
    have h1 : w.projTil hb = 1 := by
      refine LD.eq_one_of_commute ?_ ?_ ?_
      · show w.projTil hb * w.ttil = w.ttil * w.projTil hb
        rw [show w.ttil = w.projTil w.tbar from rfl, ← map_mul, hbt, map_mul]
      · exact w.torBar_comm_Ltil D l
      · exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hbpow, map_one]))
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hbE : ∀ x ∈ w.Ebar D.lev.range, hb * x = x * hb := by
    intro x hx
    have := commutator_eq_bot_iff_le_centralizer.mp hcomm hbO
    exact (mem_centralizer_iff.mp this x hx).symm
  obtain ⟨r, hrp, hrdvd, hrnot⟩ :=
    CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 3 * f) (by omega) (by omega)
  have h1 : ¬ r ∣ Nat.card K - 1 := by rw [hKc]; exact hrnot f (by omega) (by omega)
  have h2 : ¬ r ∣ Nat.card K ^ 2 - 1 := by
    rw [hKc, ← pow_mul]
    exact hrnot (f * 2) (by omega) (by omega)
  have h3 : r ∣ Nat.card K ^ 3 - 1 := by
    rw [hKc, ← pow_mul, mul_comm]
    exact hrdvd
  obtain ⟨mt, hmtE, hmtr⟩ := LD.exists_orderOf_conj_mul_eq hrp (by rwa [hKK]) (by rwa [hKK])
    (by rwa [hKK])
  have hmtE' : mt ∈ (w.Ebar D.lev.range).map w.projTil := by
    rw [map_projTil_Ebar w _ hlayer]
    exact hmtE
  obtain ⟨mb, hmbE, hmb⟩ := hmtE'
  set sb := mb * w.tbar * mb⁻¹ * w.tbar with hsb
  have hsbt : w.tbar * sb * w.tbar⁻¹ = sb⁻¹ := by
    calc w.tbar * sb * w.tbar⁻¹ = w.tbar * mb * w.tbar * mb⁻¹ := by rw [hsb]; group
      _ = w.tbar⁻¹ * mb * w.tbar⁻¹ * mb⁻¹ := by rw [tbar_inv w]
      _ = sb⁻¹ := by rw [hsb]; group
  have hcb : Commute hb sb := by
    have hm : Commute hb mb := hbE mb hmbE
    have ht : Commute hb w.tbar := hbt
    exact ((hm.mul_right ht).mul_right hm.inv_right).mul_right ht
  have hsbtil : orderOf (w.projTil sb) = r := by
    rw [hsb, map_mul, map_mul, map_mul, map_inv, hmb]
    exact hmtr
  set n := orderOf sb with hn
  have hn0 : n ≠ 0 := (orderOf_pos sb).ne'
  set a := n.factorization r with ha
  set k := n / r ^ a with hk
  set yb := sb ^ k with hyb
  have hyb_pow : yb ^ r ^ a = 1 := by
    rw [hyb, ← pow_mul, mul_comm, hk, ha, Nat.ordProj_mul_ordCompl_eq_self, hn,
      pow_orderOf_eq_one]
  have hybt : w.tbar * yb * w.tbar⁻¹ = yb⁻¹ := by
    rw [hyb, ← conj_pow, hsbt, inv_pow]
  have hyb_ne : w.projTil yb ≠ 1 := by
    intro h0
    rw [hyb, map_pow] at h0
    have := orderOf_dvd_of_pow_eq_one h0
    rw [hsbtil] at this
    exact Nat.not_dvd_ordCompl hrp hn0 this
  have hcy : Commute hb yb := hcb.pow_right k
  set TD := w.torusData (by omega) D hKc l with hTD
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hgen := card_adjoin_cube_eq hf hKc hlord
  have hM : Nat.card (Additive w.WN) = Nat.card K ^ 4 := w.card_additive_WN hKc
  have hinv : yb⁻¹ = yb ^ (r ^ a - 1) :=
    (eq_inv_of_mul_eq_one_left (by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hrp.pos), hyb_pow])).symm
  refine TD.false_of_mul_eq_pow_mul hgen hM hrp a h1 h2 h3 (s := actB w yb)
    (m := actB w w.tbar) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hyb_pow, map_one]
  · exact fun h1' => hyb_ne (w.projTil_eq_one_of_actB_eq_one h1')
  · intro v
    refine ⟨actB w w.tbar v, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, tbar_mul_self w, map_one, Module.End.one_apply]
  · have h6 : w.tbar * yb = yb ^ (r ^ a - 1) * w.tbar := by
      calc w.tbar * yb = (w.tbar * yb * w.tbar⁻¹) * w.tbar := by group
        _ = yb⁻¹ * w.tbar := by rw [hybt]
        _ = yb ^ (r ^ a - 1) * w.tbar := by rw [hinv]
    rw [← map_mul, h6, map_mul, map_pow]
  · show actB w yb * actB w hb = actB w hb * actB w yb
    rw [← map_mul, ← map_mul, hcy.eq]
  · show actB w w.tbar * actB w hb = actB w hb * actB w w.tbar
    rw [← map_mul, ← hbt, map_mul]

end Hyp

theorem linearThreeExclusion27 : LinearThreeExclusion27 :=
  fun _ _ _ _ _ h d _ _ _ hR hW w _ _ _ D hKc hlayer _ hmodel =>
    Hyp.not_lieModel_PSL3 h.three_le d hR hW (h.normalizer_adj_le d hR hW) w D hKc hlayer hmodel

end CFSG.LocalAnalysis.EvenBN.LinearThree
