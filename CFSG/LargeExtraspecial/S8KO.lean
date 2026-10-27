module

public import CFSG.LargeExtraspecial.S8KK

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

section Card

variable [NQHyp S g t] {X : Subgroup S.O}

variable (S g t) in
@[expose] noncomputable def nqSubHom (X : Subgroup S.O) (hXN : X ≤ Nbar S g t) :
    X →* Multiplicative (nqSub S g t X) where
  toFun x := Multiplicative.ofAdd ⟨nqMk ⟨x, hXN x.2⟩, ⟨⟨x, hXN x.2⟩, x.2, rfl⟩⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact (nqMk_eq_zero_iff _).mpr (one_mem _)
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact nqMk_mul ⟨(a : S.O), hXN a.2⟩ ⟨(b : S.O), hXN b.2⟩

theorem coe_toAdd_nqSubHom (hXN : X ≤ Nbar S g t) (x : X) :
    ((Multiplicative.toAdd (nqSubHom S g t X hXN x) : nqSub S g t X) : NQ S g t) =
      nqMk ⟨x, hXN x.2⟩ :=
  rfl

theorem nqSubHom_surjective (hXN : X ≤ Nbar S g t) :
    Function.Surjective (nqSubHom S g t X hXN) := by
  intro w
  have hw := (Multiplicative.toAdd w).2
  refine ⟨⟨_, hw.choose_spec.1⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [coe_toAdd_nqSubHom]
  exact hw.choose_spec.2

theorem card_eq_two_mul_card_nqSub (htt : t * t = 1) (ht1 : t ≠ 1) (hXN : X ≤ Nbar S g t)
    (htX : t ∈ X) : Nat.card X = 2 * Nat.card (nqSub S g t X) := by
  have hto : orderOf (⟨t, htX⟩ : X) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hker : (nqSubHom S g t X hXN).ker = zpowers ⟨t, htX⟩ := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : nqMk ⟨(x : S.O), hXN x.2⟩ = 0 :=
        (coe_toAdd_nqSubHom hXN x).symm.trans
          (congrArg Subtype.val (congrArg Multiplicative.toAdd h))
      rcases eq_one_or_eq_of_mem_zpowers htt ((nqMk_eq_zero_iff _).mp h1) with h2 | h2
      · rw [show x = 1 from Subtype.ext h2]
        exact one_mem _
      · rw [show x = ⟨t, htX⟩ from Subtype.ext h2]
        exact mem_zpowers _
    · intro h
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact (coe_toAdd_nqSubHom hXN x).trans
        ((nqMk_eq_zero_iff _).mpr (coe_mem_zpowers_of_mem htX h))
  have h1 := Subgroup.card_ker_mul_card_range (nqSubHom S g t X hXN)
  have hk2 : Nat.card (nqSubHom S g t X hXN).ker = 2 :=
    (congrArg (fun K : Subgroup X => Nat.card ↥K) hker).trans ((Nat.card_zpowers _).trans hto)
  have hr : Nat.card (nqSubHom S g t X hXN).range = Nat.card (nqSub S g t X) :=
    (congrArg (fun K : Subgroup (Multiplicative (nqSub S g t X)) => Nat.card ↥K)
      (MonoidHom.range_eq_top.mpr (nqSubHom_surjective hXN))).trans Subgroup.card_top
  exact h1.symm.trans (congrArg₂ (· * ·) hk2 hr)

end Card

namespace Bad4

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad4 D τ)
include B

theorem finrank_sup : finrank (ZMod 2) ↥(Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 16 := by
  have hinf := B.red.inf_eq_bot B.mem B.not_mem
  have hdim := D.hdim
  have hm4 := B.red.hm4
  obtain ⟨-, -, x, -, hxτ⟩ := B.mem
  have hdimτ : finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxτ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Vt S g t)
    (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have h0 := Submodule.finrank_eq_zero.mpr hinf
  omega

theorem eleven_le_finrank_clSub_inf :
    11 ≤ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓
      (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))) := by
  have haQ := H.conj_mem
  have hinf := B.red.inf_eq_bot B.mem B.not_mem
  have hτV := B.red.fix_Vt B.mem
  have hdim := D.hdim
  have hm4 := B.red.hm4
  have hτM := B.mem.1
  obtain ⟨-, -, x, -, hxτ⟩ := B.mem
  have hdimτ : finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxτ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have hτa := hτV _ (cl_a_mem_Vt ht)
  have hτP : ∀ p ∈ S.clSub (S.QG ⊓ S.Qa g),
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa g) := fun p hp =>
    apply_mem_clSub_of_apply_cl_eq haQ H.conj_ne hτM hτa hp
  have e2 := (finrank_clSub_inf_fixSpace H C hτP).2
  have e1 := finrank_clSub_inf_Vt H C ht ht1 hVQ
  set P := S.clSub (S.QG ⊓ S.Qa g) with hP
  have hle : P ⊓ Vt S g t ⊔ P ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      P ⊓ (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
    sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
  have hdisj : P ⊓ Vt S g t ⊓ (P ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = ⊥ :=
    eq_bot_iff.mpr fun v hv => by
      have h : v ∈ Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hv.1.2, hv.2.2⟩
      rw [hinf] at h
      exact h
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ Vt S g t)
    (P ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have h0 := Submodule.finrank_eq_zero.mpr hdisj
  have hm := Submodule.finrank_mono hle
  omega

theorem finrank_clSub_inf_perp :
    S.width ≤ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓
      S2.perp S.q (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))) + 5 := by
  have h11 := B.eleven_le_finrank_clSub_inf
  have h16 := B.finrank_sup
  set P := S.clSub (S.QG ⊓ S.Qa g) with hPdef
  set Y := Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hYdef
  have hP : finrank (ZMod 2) P = S.width := by
    have := S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne C.card_QG_inf_Qa
    rw [← hPdef] at this
    omega
  have hQt := S.finrank_Qt_eq_two_mul_width
  have hPP : P ≤ S2.perp S.q P := fun u hu =>
    (S2.mem_perp).mpr fun v hv => polar_eq_zero_of_mem_clSub H.conj_ne hv hu
  have e1 := finrank_perp S.q_nondegenerate P
  have hPperp : S2.perp S.q P = P :=
    (Submodule.eq_of_le_of_finrank_eq hPP (by omega)).symm
  have e2 : P ⊓ S2.perp S.q Y = S2.perp S.q (P ⊔ Y) := by
    rw [perp_sup P Y, hPperp]
  have e3 := finrank_perp S.q_nondegenerate (P ⊔ Y)
  have e4 := Submodule.finrank_sup_add_finrank_inf_eq P Y
  have e5 : finrank (ZMod 2) ↥(P ⊓ S2.perp S.q Y) = finrank (ZMod 2) ↥(S2.perp S.q (P ⊔ Y)) := by
    rw [e2]
  omega

theorem fix_perp_of_mem_N1bar {ν : S.O} (hν : ν ∈ N1bar S g t τ) {w : S.Qt}
    (hw : w ∈ S2.perp S.q (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))) :
    (ν : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  rw [perp_sup_commSpace, ← B.red.fixSub_N1bar B.mem B.not_mem] at hw
  exact (mem_fixSub S).mp hw ν hν

theorem Lbar_inf_fix_eq :
    S.Lbar g ⊓ (S2.fixGroup (S2.perp S.q (Vt S g t ⊔
      commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)))).comap S.O.subtype = S9.Fbar S g t := by
  have := B.red.nqHyp
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  set Yp := S2.perp S.q (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) with hYp
  set K := S.Lbar g ⊓ (S2.fixGroup Yp).comap S.O.subtype with hK
  have hFK : S9.Fbar S g t ≤ K := fun f hf =>
    ⟨S9.Fbar_le_Lbar hf, S2.mem_fixGroup.mpr fun w hw => B.fix_perp_of_mem_N1bar (B.Fbar_le hf) hw⟩
  have h1 := card_mul_two_pow_finrank_fix H C (K := K) inf_le_left
  have hle : S.clSub (S.QG ⊓ S.Qa g) ⊓ Yp ≤ S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K :=
    inf_le_inf_left _ fun w hw => (mem_fixSub S).mpr fun k hk => S2.mem_fixGroup.mp hk.2 w hw
  have h2 := Submodule.finrank_mono hle
  have h3 := B.finrank_clSub_inf_perp
  rw [← hYp] at h3
  have hK5 : Nat.card K ≤ 2 ^ 5 := by
    have hpos : 0 < 2 ^ (S.width - 5) := by positivity
    have h4 : 2 ^ (S.width - 5) ≤ 2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : Nat.card K * 2 ^ (S.width - 5) ≤ 2 ^ 5 * 2 ^ (S.width - 5) := by
      calc Nat.card K * 2 ^ (S.width - 5) ≤
          Nat.card K * 2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S K) :=
            Nat.mul_le_mul_left _ h4
        _ = 2 ^ S.width := h1
        _ ≤ 2 ^ 5 * 2 ^ (S.width - 5) := by
            rw [← pow_add]
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.le_of_mul_le_mul_right h5 hpos
  have hFN : S9.Fbar S g t ≤ Nbar S g t := S9.Fbar_le_of_subset (conjL_subset_Nbar B.red.hsub)
  have hF := card_eq_two_mul_card_nqSub htt ht1 hFN (S9.self_mem_Fbar ht)
  obtain ⟨-, hτt, x, hxM, hxτ⟩ := B.mem
  have hF4 := finrank_nqSub_Fbar_of_four B.red.hCE B.red.hNo B.red.hΩ D B.red.hm4 B.red.hsub
    hxM hxτ hτt (B.red.fix_Vt B.mem) B.not_mem (t := t)
  have hF5 : Nat.card (S9.Fbar S g t) = 2 ^ 5 := by
    rw [hF, ← FiniteField.pow_finrank_eq_natCard 2 (nqSub S g t (S9.Fbar S g t)), hF4]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hFK (by omega)).symm

omit B in
theorem apply_mem_perp_map {Y : Submodule (ZMod 2) S.Qt} (y : S.O) {w : S.Qt}
    (hw : w ∈ S2.perp S.q Y) :
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈
      S2.perp S.q (Y.map ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)) := by
  refine (S2.mem_perp).mpr fun v hv => ?_
  obtain ⟨u, hu, rfl⟩ := hv
  rw [LinearEquiv.coe_coe, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup y.2]
  exact (S2.mem_perp).mp hw u hu

theorem apply_mem_perp_of_mem_Rbar {r : S.O} (hr : r ∈ Rbar S g t) {w : S.Qt}
    (hw : w ∈ S2.perp S.q (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt))) :
    (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈
      S2.perp S.q (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hrt : r * t * r⁻¹ = t := by
    rw [commute_of_mem_Rbar H.conj_mem hr, mul_inv_cancel_right]
  have hY := B.map_eq_of_commSpace_le (Rbar_le_Mbar hr) (by
    rw [hrt, (commSpace_t_eq H C ht ht1 hVQ).1]
    exact le_sup_left)
  have h := apply_mem_perp_map r hw
  rwa [hY] at h

theorem mem_N1bar_of_fix {ν : S.O} (hνN : ν ∈ Nbar S g t)
    (hν : ∀ w ∈ S2.perp S.q (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)),
      (ν : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) : ν ∈ N1bar S g t τ := by
  have := B.red.nqHyp
  have haQ := H.conj_mem
  set Yp := S2.perp S.q (Vt S g t ⊔ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) with hYp
  set X : Subgroup S.O := (S2.fixGroup Yp).comap S.O.subtype with hX
  have htX : t ∈ X := S2.mem_fixGroup.mpr fun w hw => by
    rw [hYp, perp_sup_commSpace, ← (commSpace_t_eq H C ht ht1 hVQ).2] at hw
    exact mem_fixSpace.mp hw.1
  have hνX : ν ∈ X := S2.mem_fixGroup.mpr hν
  have hinv : ∀ e : omegaGroup D.Q D.hQ, ∀ v ∈ nqSub S g t X,
      nqRep S g t D.hX e v ∈ nqSub S g t X := by
    intro e v hv
    have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resV haQ t).range := by
      rw [range_resV, D.hX]; exact e.2
    refine (MonoidHom.mem_range.mp heR).elim fun r hr => hv.elim fun n hn => ?_
    have hnX : (n : S.O) ∈ X := hn.1
    have hv' : v = nqMk n := hn.2.symm
    subst hv'
    rw [nqRep_apply D.hX hr.symm n]
    refine ⟨_, S2.mem_fixGroup.mpr fun w hw => ?_, rfl⟩
    change ((((r : S.O) * (n : S.O) * (r : S.O)⁻¹ : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w
    have hw' := B.apply_mem_perp_of_mem_Rbar (inv_mem r.2) hw
    have hfix : ((n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((((r : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
          (((r : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := S2.mem_fixGroup.mp hnX _ hw'
    rw [coe_mul_apply, coe_mul_apply, hfix, apply_inv_apply_O]
  have hD := timmesfeld_6_5_omega H B.red.hNo C ht ht1 hVQ B.red.hΩ D.hN0 D.hh D.hb D.hX D.hE
  have htwo := (dvd_and_two_mul_of_invariant (nqRep S g t D.hX) D.hm D.hdim
    (aV_ne_zero H ht) D.hQa D.Q_bV D.polar_aV_bV hD hinv).2.2
  have e1 : nqSub S g t X ⊓ S2.fixOf (nqRep S g t D.hX)
      (S2.radFix D.Q ⊥ (aV ht) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) =
        nqSub S g t (S9.Fbar S g t) :=
    (congrArg (nqSub S g t X ⊓ ·) (fixOf_nqRep_radFix_eq B.red.hNo D)).trans
      ((nqSub_inf htX ht).trans (congrArg (nqSub S g t) ((inf_comm _ _).trans B.Lbar_inf_fix_eq)))
  have e2 : finrank (ZMod 2) ↥(nqSub S g t X ⊓ S2.fixOf (nqRep S g t D.hX)
      (S2.radFix D.Q ⊥ (aV ht) : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t))) =
        finrank (ZMod 2) ↥(nqSub S g t (S9.Fbar S g t)) :=
    congrArg (fun K : Submodule (ZMod 2) (NQ S g t) => finrank (ZMod 2) ↥K) e1
  obtain ⟨-, hτt, x, hxM, hxτ⟩ := B.mem
  have hτV := B.red.fix_Vt B.mem
  have hF4 := finrank_nqSub_Fbar_of_four B.red.hCE B.red.hNo B.red.hΩ D B.red.hm4 B.red.hsub
    hxM hxτ hτt hτV B.not_mem (t := t)
  have hτK := mem_CMt_of_mem_conjCentM B.mem
  have hle1 := (B.red.N1bar_spec B.mem B.not_mem).1
  have hAS : nqSub S g t (N1bar S g t τ) ≤ nqSub S g t X :=
    nqSub_mono fun a ha => S2.mem_fixGroup.mpr fun w hw => B.fix_perp_of_mem_N1bar ha hw
  have hA8 : finrank (ZMod 2) (nqSub S g t (N1bar S g t τ)) = 8 := by
    have h1 : finrank (ZMod 2) ↥(nqSub S g t (N1bar S g t τ)) =
        finrank (ZMod 2) ↥(LinearMap.range (nqComm S g t ⟨τ, hτK⟩)) :=
      congrArg (fun K : Submodule (ZMod 2) (NQ S g t) => finrank (ZMod 2) ↥K)
        (nqSub_N1bar H hτK hle1)
    have h2 := (finrank_range_nqComm B.red.hNo B.red.hΩ D hτK hτV).2
    have h3 := finrank_map_nqComm_of_four B.red.hCE B.red.hNo B.red.hΩ D B.red.hm4 B.red.hsub
      hxM hxτ hτt hτV B.not_mem hτK
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hAS (by omega)
  have hmem : nqMk ⟨ν, hνN⟩ ∈ nqSub S g t X := ⟨⟨ν, hνN⟩, hνX, rfl⟩
  rw [← heq] at hmem
  exact (mem_nqSub t_mem_N1bar _).mp hmem

end Bad4

end CFSG.LargeExtraspecial.S8
