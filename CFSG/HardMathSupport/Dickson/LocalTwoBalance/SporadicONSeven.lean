module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SporadicRest
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestON
public import CFSG.RankThree.PartOne.KS.ONPointwise

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.ONSchreier CFSG.RankThree.Native CFSG.RankThree.PartOne

section Generic

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem aut_mul_conj_mul_inv (σ : MulAut K) (c : K) :
    σ * MulAut.conj c * σ⁻¹ = MulAut.conj (σ c) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem fixes_centralizer_of_mem_core (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {a : K}
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set K)) = ⊥)
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) {σ : MulAut K}
    (hσ : σ ∈ GLAPPrimeCoreOf p
      (H ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut K)))) :
    ∀ c : K, c * a = a * c → σ c = c := by
  set C : Subgroup (MulAut K) := H ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut K))
    with hC
  set R : Subgroup (MulAut K) := GLAPPrimeCoreOf p C with hR
  have hRC : R ≤ C := GLAPPrimeCoreOf_le C
  have hconjC : ∀ c : K, c * a = a * c → MulAut.conj c ∈ C := by
    intro c hc
    refine ⟨hH ⟨c, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, hc]
  intro c hc
  have hnC := hconjC c hc
  have h1 : σ * (MulAut.conj c * σ⁻¹ * (MulAut.conj c)⁻¹) ∈ R :=
    R.mul_mem hσ (GLAPPrimeCoreOf_conj_mem _ hnC σ⁻¹ (R.inv_mem hσ))
  have h2 : σ * (MulAut.conj c * σ⁻¹ * (MulAut.conj c)⁻¹) = MulAut.conj (σ c * c⁻¹) := by
    have e1 : σ * (MulAut.conj c * σ⁻¹ * (MulAut.conj c)⁻¹) =
        (σ * MulAut.conj c * σ⁻¹) * (MulAut.conj c)⁻¹ := by group
    rw [e1, aut_mul_conj_mul_inv, map_mul, map_inv]
  rw [h2] at h1
  set w : K := σ c * c⁻¹ with hw
  have hwa : w * a = a * w := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hRC h1).2
    apply hinj
    exact (map_mul (MulAut.conj : K →* MulAut K) w a).trans
      (h.trans (map_mul (MulAut.conj : K →* MulAut K) a w).symm)
  set X : Subgroup K := R.comap (MulAut.conj : K →* MulAut K) ⊓ Subgroup.centralizer ({a} : Set K)
    with hX
  have hXC : X ≤ Subgroup.centralizer ({a} : Set K) := inf_le_right
  have hXn : ∀ g ∈ Subgroup.centralizer ({a} : Set K), ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · have hgC := hconjC g hga
      have := GLAPPrimeCoreOf_conj_mem _ hgC (MulAut.conj x) hx.1
      simpa [map_mul, map_inv] using this
    · have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
      have hgc : Commute g a := hga
      have hxc : Commute x a := hxa
      exact ((hgc.mul_left hxc).mul_left hgc.inv_left).eq
  have hXcop : Nat.Coprime p (Nat.card X) := by
    have hle : X.map (MulAut.conj : K →* MulAut K) ≤ R := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    have hdvd : Nat.card (X.map (MulAut.conj : K →* MulAut K)) ∣ Nat.card R :=
      Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective hinj] at hdvd
    exact Nat.Coprime.coprime_dvd_right hdvd (coprime_card_GLAPPrimeCoreOf hp C)
  have hXle := le_GLAPPrimeCoreOf_of_normal hXC hXn hXcop
  rw [hcore] at hXle
  have hwX : w ∈ X := ⟨h1, Subgroup.mem_centralizer_singleton_iff.2 hwa⟩
  have hw1 : w = 1 := Subgroup.mem_bot.1 (hXle hwX)
  have : σ c = c := by
    have h3 : σ c * c⁻¹ = 1 := hw1
    exact mul_inv_eq_one.1 h3
  exact this

theorem core_eq_bot_of_pow (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {a : K}
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({a} : Set K)) = ⊥)
    (hpow : ∀ σ : MulAut K, (∀ c : K, c * a = a * c → σ c = c) → σ ^ p = 1)
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut K))) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun σ hσ => ?_
  have hfix := fixes_centralizer_of_mem_core hp hinj hcore hH hσ
  have hσp : σ ^ p = 1 := hpow σ hfix
  have h1 : orderOf σ ∣ p := orderOf_dvd_of_pow_eq_one hσp
  have h2 : orderOf σ ∣ Nat.card
      (GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut K)))) :=
    Subgroup.orderOf_dvd_natCard _ hσ
  have hcop := coprime_card_GLAPPrimeCoreOf hp
    (H ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut K)))
  have h3 : Nat.Coprime (orderOf σ) (Nat.card
      (GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut K))))) :=
    Nat.Coprime.coprime_dvd_left h1 hcop
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h3 h2)

end Generic

section Pv


theorem core_centralizer_onSevenX0 :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({onSevenX0} : Set Pv)) = ⊥ := by
  have hrec := CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_onSevenRecord_eq_bot 0
  have hmap := map_glaPPrimeCoreOf_of_injective 7 Pv.subtype Pv.subtype_injective
    (Subgroup.centralizer ({onSevenX0} : Set Pv))
  have hc : (Subgroup.centralizer ({onSevenX0} : Set Pv)).map Pv.subtype =
      Subgroup.centralizer ({onSevenLine (onSevenRep 0)} : Set (Equiv.Perm (Fin N))) ⊓ Pv := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨congrArg Subtype.val hz, z.2⟩
    · rintro ⟨hy, hyP⟩
      exact ⟨⟨y, hyP⟩, Subtype.ext hy, rfl⟩
  rw [hc, hrec] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ Pv.subtype_injective).1 hmap

theorem core_centralizer_conj_onSevenX0 (g : Pv) :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({g * onSevenX0 * g⁻¹} : Set Pv)) = ⊥ := by
  have h := core_centralizer_onSevenX0
  have hmap := map_glaPPrimeCoreOf_of_injective 7 (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective (Subgroup.centralizer ({g * onSevenX0 * g⁻¹} : Set Pv))
  have hc := map_inf_centralizer_of_injective (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective ⊤ (g * onSevenX0 * g⁻¹)
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective, top_inf_eq] at hc
  have hx : (MulAut.conj g⁻¹).toMonoidHom (g * onSevenX0 * g⁻¹) = onSevenX0 := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rw [hx] at hc
  rw [hc, h] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).1 hmap

theorem pow_seven_of_fixes (hin : ONPointwiseSeven) (g : Pv) (σ : MulAut Pv)
    (hσ : ∀ c : Pv, c * (g * onSevenX0 * g⁻¹) = (g * onSevenX0 * g⁻¹) * c → σ c = c) :
    σ ^ 7 = 1 := by
  obtain ⟨-, -, hC, -⟩ := R3E_ON_full_seven_centralizer_structures
  refine pow_eq_one_of_fixes_conj
    (S := {c : Pv | (c : Equiv.Perm (Fin N)) ∈ onSevenC 0})
    (fun α hα => hin α (fun c hc => hα c hc)) g ?_
  intro c hc
  apply hσ
  have hc' : (c : Equiv.Perm (Fin N)) ∈
      Subgroup.centralizer ({onSevenLine (onSevenRep 0)} : Set (Equiv.Perm (Fin N))) ⊓ Pv := by
    rw [← hC 0]
    exact hc
  have hcx : c * onSevenX0 = onSevenX0 * c :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hc'.1)
  calc g * c * g⁻¹ * (g * onSevenX0 * g⁻¹) = g * (c * onSevenX0) * g⁻¹ := by group
    _ = g * (onSevenX0 * c) * g⁻¹ := by rw [hcx]
    _ = g * onSevenX0 * g⁻¹ * (g * c * g⁻¹) := by group

theorem isLocallyBalancedAbs_seven_two_Pv (hcen : Subgroup.center ↥Pv = ⊥) :
    IsLocallyBalancedAbs 7 2 ↥Pv := by
  intro D hD hcard H hH _hDH
  have hp : Nat.Prime 7 := by norm_num
  have hin := CFSG.RankThree.PartOne.ONPw.onPointwiseSeven_holds
  have hinj : Function.Injective (MulAut.conj : ↥Pv →* MulAut ↥Pv) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center ↥Pv := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut ↥Pv => φ g) hab
      simp only [MulAut.conj_apply] at h
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h]
        _ = a⁻¹ * b * g := by group
    rw [hcen, Subgroup.mem_bot] at hc
    calc a = a * (a⁻¹ * b) := by rw [hc, mul_one]
      _ = b := by group
  have hOut : ¬ 7 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Pv) := by
    intro hd
    have e' : CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Pv ≃*
        CFSG.ComponentClassification.OuterAutomorphisms.Outer
          CFSG.Blueprint.NativeSporadic.ON :=
      CFSG.ComponentClassification.OuterAutomorphisms.equivalence onEquivPv.symm
    rw [Nat.card_congr e'.toEquiv] at hd
    rcases CFSG.Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent 7 hp hd with
      h | h <;> omega
  have hcop : Nat.Coprime 7
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Pv)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hOut
  have hDp : IsPGroup 7 D := fun d => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hD.2 d d.2)⟩
  have hDi : D ≤ innerAut ↥Pv := le_inner_of_isPGroup hcop hDp
  set E : Subgroup ↥Pv := D.comap (MulAut.conj : ↥Pv →* MulAut ↥Pv) with hE
  have hmap : E.map (MulAut.conj : ↥Pv →* MulAut ↥Pv) = D := Subgroup.map_comap_eq_self hDi
  have hEcard : Nat.card E = 7 ^ 2 := by
    rw [← hcard, ← hmap, Subgroup.card_map_of_injective hinj]
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    apply hinj
    have hab := hD.1.is_comm.comm (⟨MulAut.conj a, ha⟩ : D) ⟨MulAut.conj b, hb⟩
    have := congrArg Subtype.val hab
    simpa only [Subgroup.coe_mul, map_mul] using this
  obtain ⟨g, hg⟩ := exists_conj_onSevenX0_mem hEcard hEcomm
  have haD : MulAut.conj (g * onSevenX0 * g⁻¹) ∈ D := hg
  have ha1 : MulAut.conj (g * onSevenX0 * g⁻¹) ≠ 1 := by
    intro h1
    have h2 : g * onSevenX0 * g⁻¹ = 1 := hinj (h1.trans (map_one _).symm)
    apply onSevenX0_ne_one
    calc onSevenX0 = g⁻¹ * (g * onSevenX0 * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  exact Cross.localDeltaIn_eq_bot_of_core_bot haD ha1
    (core_eq_bot_of_pow hp hinj (core_centralizer_conj_onSevenX0 g) (pow_seven_of_fixes hin g) hH)

theorem sporadicTwoPairHolds_ONan_seven : SporadicTwoPairHolds .ONan 7 := by
  intro S _ _ _ hnab ⟨e⟩
  have hcenS : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  let φ : S ≃* Pv := e.trans onEquivPv
  have hcen : Subgroup.center ↥Pv = ⊥ := by
    have h := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ
    rw [hcenS, Subgroup.map_bot] at h
    exact h.symm
  exact IsLocallyBalancedAbs.of_mulEquiv φ (isLocallyBalancedAbs_seven_two_Pv hcen)

end Pv

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
