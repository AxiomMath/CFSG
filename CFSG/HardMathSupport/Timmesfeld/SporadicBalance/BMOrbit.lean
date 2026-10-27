module

public import CFSG.Assembly.Defs
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Sporadic.SmallOddCore

variable {p : ℕ} {S : Type*} [Group S]

theorem dvd_card_of_forall_dvd_card_orbit {G X : Type*} [Group G] [MulAction G X] [Finite X]
    {n : ℕ} (h : ∀ x : X, n ∣ Nat.card (MulAction.orbit G x)) : n ∣ Nat.card X := by
  classical
  have : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits G X), Nat.card_sigma]
  exact Finset.dvd_sum fun ω _ => h _

theorem pow_dvd_of_le_of_dvd_pow (hp : p.Prime) {n a k : ℕ} (hn : n ∣ p ^ a) (hk : p ^ k ≤ n) :
    p ^ k ∣ n := by
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hn
  refine pow_dvd_pow p ?_
  by_contra hjk
  have : p ^ j < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

theorem gLAPPrimeCoreOf_eq_bot_of_orbit_bound [Finite S] (hp : p.Prime) {C : Subgroup S}
    {a r k : ℕ} (hC : Nat.card C = p ^ a * r) (hr : ¬ p ∣ r)
    (hd : ∀ d, d ∣ r → d ≡ 1 [MOD p ^ k] → d = 1)
    (hm : ∀ w : S, (orderOf w).Prime → orderOf w ∣ r → ∀ Q : Subgroup S, IsPGroup p Q →
      Q ≤ Subgroup.centralizer ({w} : Set S) → Nat.card Q * p ^ k ≤ p ^ a) :
    GLAPPrimeCoreOf p C = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hL
  set R := GLAPPrimeCoreOf p C with hRdef
  have hRC : R ≤ C := GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime p (Nat.card R) := coprime_card_GLAPPrimeCoreOf hp C
  have hRr : Nat.card R ∣ r := by
    have h1 : Nat.card R ∣ p ^ a * r := hC ▸ Subgroup.card_dvd_of_le hRC
    exact (Nat.Coprime.pow_left a hcop).symm.dvd_of_dvd_mul_left h1
  have hr0 : r ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := C)
    rw [hC, mul_zero] at this
    exact lt_irrefl _ this
  obtain ⟨Pc⟩ : Nonempty (Sylow p C) := inferInstance
  set P : Subgroup S := (Pc : Subgroup C).map C.subtype with hP
  have hPC : P ≤ C := Subgroup.map_subtype_le _
  have hPp : IsPGroup p P := Pc.isPGroup'.map C.subtype
  have hPcard : Nat.card P = p ^ a := by
    rw [hP, Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity, hC,
      Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hr0, hp.factorization_pow,
      Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hr, add_zero]
  by_cases hbig : ∃ w ∈ R, w ≠ 1 ∧
      p ^ a < Nat.card ↥(P ⊓ Subgroup.centralizer ({w} : Set S)) * p ^ k
  ·
    obtain ⟨w, hwR, hw1, hlt⟩ := hbig
    have hwo : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.1 h)
    obtain ⟨q, hq, hqw⟩ := Nat.exists_prime_and_dvd hwo
    have hw0 : orderOf w ≠ 0 := (orderOf_pos_iff.2 (isOfFinOrder_of_finite w)).ne'
    set y := w ^ (orderOf w / q) with hy
    have hyo : orderOf y = q := orderOf_pow_orderOf_div hw0 hqw
    have hqR : q ∣ Nat.card R := by
      have h1 : orderOf (⟨w, hwR⟩ : R) ∣ Nat.card R := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact hqw.trans h1
    have hle : P ⊓ Subgroup.centralizer ({w} : Set S) ≤ Subgroup.centralizer ({y} : Set S) := by
      intro g hg
      have hgw : g * w = w * g :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2
      exact Subgroup.mem_centralizer_singleton_iff.2
        ((Commute.pow_right (show Commute g w from hgw) _).eq)
    have := hm y (hyo ▸ hq) (hyo ▸ hqR.trans hRr) _ (hPp.to_le inf_le_left) hle
    omega
  ·
    push Not at hbig
    have hnorm : ∀ g ∈ P, ∀ x ∈ R, g * x * g⁻¹ ∈ R := fun g hg x hx =>
      GLAPPrimeCoreOf_conj_mem g (hPC hg) x hx
    let X := {x : ↥R // x ≠ 1}
    let act : MulAction ↥P X :=
      { smul := fun g x => ⟨⟨g * x.1 * (g : S)⁻¹, hnorm g g.2 x.1 x.1.2⟩, fun h => x.2 (by
          have h1 : (g : S) * x.1 * (g : S)⁻¹ = 1 := congrArg Subtype.val h
          have h2 : ((x.1 : ↥R) : S) = 1 := by
            calc ((x.1 : ↥R) : S) = (g : S)⁻¹ * ((g : S) * x.1 * (g : S)⁻¹) * g := by group
              _ = 1 := by rw [h1]; group
          exact Subtype.ext h2)⟩
        one_smul := fun x => Subtype.ext (Subtype.ext (by
          change (1 : S) * x.1 * (1 : S)⁻¹ = x.1
          simp))
        mul_smul := fun g h x => Subtype.ext (Subtype.ext (by
          change ((g : S) * h) * x.1 * ((g : S) * h)⁻¹ =
            g * ((h : S) * x.1 * (h : S)⁻¹) * (g : S)⁻¹
          group)) }
    have hsmul : ∀ (g : ↥P) (x : X), (((g • x : X) : ↥R) : S) = (g : S) * x.1 * (g : S)⁻¹ :=
      fun _ _ => rfl
    have horb : ∀ x : X, p ^ k ∣ Nat.card (MulAction.orbit ↥P x) := by
      intro x
      have hstab : Nat.card (MulAction.stabilizer ↥P x) =
          Nat.card ↥(P ⊓ Subgroup.centralizer ({((x.1 : ↥R) : S)} : Set S)) := by
        have he : MulAction.stabilizer ↥P x =
            (Subgroup.centralizer ({((x.1 : ↥R) : S)} : Set S)).subgroupOf P := by
          ext g
          rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
            Subgroup.mem_centralizer_singleton_iff]
          constructor
          · intro h
            have h1 : (g : S) * x.1 * (g : S)⁻¹ = x.1 :=
              (hsmul g x).symm.trans (congrArg (fun z : X => ((z : ↥R) : S)) h)
            calc (g : S) * x.1 = (g : S) * x.1 * (g : S)⁻¹ * g := by group
              _ = x.1 * g := by rw [h1]
          · intro h
            apply Subtype.ext
            apply Subtype.ext
            rw [hsmul g x, h, mul_inv_cancel_right]
        rw [he, ← Subgroup.inf_subgroupOf_left]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      have hos : Nat.card (MulAction.orbit ↥P x) * Nat.card (MulAction.stabilizer ↥P x) =
          p ^ a := by
        rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥P x),
          hPcard]
      have hpos : 0 < Nat.card (MulAction.stabilizer ↥P x) := Nat.card_pos
      have hb := hbig x.1 x.1.2 (fun h => x.2 (Subtype.ext h))
      rw [← hstab] at hb
      refine pow_dvd_of_le_of_dvd_pow hp (Dvd.intro _ hos) ?_
      by_contra hlt
      push Not at hlt
      have : Nat.card (MulAction.orbit ↥P x) * Nat.card (MulAction.stabilizer ↥P x) <
          p ^ k * Nat.card (MulAction.stabilizer ↥P x) :=
        Nat.mul_lt_mul_of_pos_right hlt hpos
      rw [hos] at this
      linarith
    have hX : p ^ k ∣ Nat.card X := dvd_card_of_forall_dvd_card_orbit horb
    have hRX : Nat.card ↥R = Nat.card X + 1 := by
      classical
      have : Fintype X := Fintype.ofFinite X
      rw [← Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥R)), Nat.card_eq_fintype_card,
        Fintype.card_option, ← Nat.card_eq_fintype_card]
    have hmod : Nat.card ↥R ≡ 1 [MOD p ^ k] := by
      rw [hRX]
      obtain ⟨c, hc⟩ := hX
      rw [hc]
      exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ p ^ k * c + 1)).2 (by simp)).symm
    have h1 := hd _ hRr hmod
    exact hL (Subgroup.card_eq_one.1 h1)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
