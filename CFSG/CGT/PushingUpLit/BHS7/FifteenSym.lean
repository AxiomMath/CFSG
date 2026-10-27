module

public import CFSG.CGT.PushingUpLit.BHS7.FiveFamily

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5 CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem symDat_inf_centSub_eq_bot {E : Subgroup (MulAut V)} {m : ℕ} (D : SymDat E m) :
    E ⊓ centSub (commV E) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun e he => ?_
  obtain ⟨heE, hecen⟩ := he
  have h1 : D.θ ⟨e, heE⟩ = 1 := by
    apply coreAct_injective D.three_le
    apply MulEquiv.ext
    intro d
    obtain ⟨p, rfl⟩ := D.surj d
    have hp : (e : MulAut V) p ∈ commV E := by
      rw [hecen p p.2]
      exact p.2
    have := D.equiv ⟨e, heE⟩ p hp
    have hp' : (⟨e p, hp⟩ : ↥(commV E)) = p := Subtype.ext (hecen p p.2)
    rw [hp'] at this
    exact this.symm
  have : (⟨e, heE⟩ : ↥E) = 1 := D.θ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val this

theorem sym_normalizer_le (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} {E : Subgroup (MulAut V)}
    (D : SymDat E m) {K : Subgroup (MulAut V)}
    (hKN : K ≤ Subgroup.normalizer (E : Set (MulAut V))) :
    autSub K (commV E) ≤ autSub E (commV E) := by
  classical
  have hEst : E ≤ stabSub (commV E) :=
    Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub E)
  obtain ⟨φE, -⟩ := exists_mulEquiv_autSub hEst (symDat_inf_centSub_eq_bot D)
  have hcardE : Nat.card ↥(autSub E (commV E)) = Nat.card (Equiv.Perm (Fin m)) :=
    (Nat.card_congr φE.symm.toEquiv).trans (Nat.card_congr D.θ.toEquiv)
  by_cases h5 : 5 ≤ m
  ·
    have hE'N : Subgroup.normalizer (E : Set (MulAut V)) ≤
        Subgroup.normalizer ((altOf D.θ : Subgroup (MulAut V)) : Set (MulAut V)) :=
      normalizer_le_normalizer_altOf h5 D.θ
    obtain ⟨-, θ', β', hβs, hβk, hβe⟩ := D.isAltNatSection_altOf
    obtain ⟨D'⟩ := exists_altNatData_autSub h5 rfl θ' β' hβs hβk hβe
    rw [← D.commV_altOf] at hcardE ⊢
    have hEst' : E ≤ stabSub (commV (altOf D.θ)) :=
      (Subgroup.le_normalizer.trans hE'N).trans (normalizer_commV_le_stabSub (altOf D.θ))
    have hKst' : K ≤ stabSub (commV (altOf D.θ)) :=
      (hKN.trans hE'N).trans (normalizer_commV_le_stabSub (altOf D.θ))
    have hEN' : autSub E (commV (altOf D.θ)) ≤ Subgroup.normalizer
        (autSub (altOf D.θ) (commV (altOf D.θ)) : Set (MulAut ↥(commV (altOf D.θ)))) :=
      autSub_le_normalizer (Subgroup.le_normalizer.trans hE'N)
    have hKN' : autSub K (commV (altOf D.θ)) ≤ Subgroup.normalizer
        (autSub (altOf D.θ) (commV (altOf D.θ)) : Set (MulAut ↥(commV (altOf D.θ)))) :=
      autSub_le_normalizer (hKN.trans hE'N)
    generalize commV (altOf D.θ) = W at *
    have hn : Odd m := D.odd
    have hinj := D'.psi_injective hn h5
    have hcardN : Nat.card ↥(Subgroup.normalizer
        (autSub (altOf D.θ) W : Set (MulAut ↥W))) ≤ Nat.card (Equiv.Perm (Fin m)) :=
      Nat.card_le_card_of_injective _ hinj
    have hEq : autSub E W = Subgroup.normalizer (autSub (altOf D.θ) W : Set (MulAut ↥W)) :=
      Subgroup.eq_of_le_of_card_ge hEN' (hcardE ▸ hcardN)
    rw [hEq]
    exact hKN'
  ·
    have hm3 : m = 3 := by
      obtain ⟨c, hc⟩ := D.odd
      have := D.three_le
      omega
    subst hm3
    have hW' : ∀ w : ↥(commV E), w ^ 2 = 1 := fun w => Subtype.ext (by simpa [sq] using hV w)
    have hcard : Nat.card ↥(commV E) = 4 := by
      rw [Nat.card_congr (Equiv.ofBijective D.β ⟨D.injective_β, D.surj⟩)]
      exact card_coreMod_three'
    have hrk : rk ↥(commV E) = 2 := by
      have h := card_eq_two_pow_rk hW'
      rw [hcard] at h
      have h2 : (2 : ℕ) ^ rk ↥(commV E) = 2 ^ 2 := by
        rw [← h]
        norm_num
      exact Nat.pow_right_injective le_rfl h2
    have hautcard : Nat.card (MulAut ↥(commV E)) = 6 := by
      rw [card_mulAut_eq hW', hrk]
      simp [Fin.prod_univ_two]
    have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    have htop : autSub E (commV E) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcardE, hperm, hautcard])
    rw [htop]
    exact le_top

end CFSG.CGT.PushingUpLit.BHS7
