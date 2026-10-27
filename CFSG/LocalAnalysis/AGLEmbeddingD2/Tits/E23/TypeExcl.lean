module

public import CFSG.Quasithin.Background.E2Three
public import CFSG.CGT.PushingUpLit.BHS5.FiveFive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.SL2NoFour

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.G6

theorem perm_rotate_fix_core3 : ∀ w : PermMod 3, (∑ i, Multiplicative.toAdd w i = 0) →
    permAct 3 (finRotate 3) w = w → w = 1 := by
  decide +kernel

theorem not_isL2Natural_of_mulEquiv_perm {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {C : Subgroup W} {n m : ℕ} (hm : 4 ≤ m) (θ : ↥L ≃* Equiv.Perm (Fin m)) :
    ¬ CFSG.Quasithin.E2.IsL2Natural L C n := by
  rintro ⟨-, F, hF, hfin, hcard, e, -, -⟩
  have hcharp : CharP F 2 := by
    obtain ⟨k, hp, hk⟩ := FiniteField.card F (ringChar F)
    have hdvd : ringChar F ∣ 2 ^ n := by
      rw [← hcard, hk]
      exact dvd_pow_self _ (PNat.ne_zero k)
    have h2 : ringChar F ∣ 2 := hp.dvd_of_dvd_pow hdvd
    have hval : ringChar F = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
    have := ringChar.charP F
    rwa [hval] at this
  have := isEmpty_mulEquiv_perm_sl2 (F := F) hm
  exact IsEmpty.false (θ.symm.trans e)

theorem not_slType2_of_mulEquiv_perm {V : Type} [CommGroup V] [Finite V]
    {D : Set (Subgroup (MulAut V))} {E : Subgroup (MulAut V)} {m : ℕ} (hm : 4 ≤ m)
    (θ : ↥E ≃* Equiv.Perm (Fin m)) : ¬ CFSG.CGT.PushingUpLit.BHS5.SLType2 D E := by
  rintro ⟨k, -, hsec, -⟩
  obtain ⟨-, φ, -⟩ := hsec
  have := isEmpty_mulEquiv_perm_sl2 (F := GaloisField 2 k) hm
  exact IsEmpty.false (θ.symm.trans φ)

theorem commV_inf_fixV_eq_bot_of_symData_three {V : Type} [CommGroup V] [Finite V]
    {E K : Subgroup (MulAut V)} (θ : ↥E ≃* Equiv.Perm (Fin 3)) (β : ↥(commV E) →* coreMod 3)
    (hinv : ∀ x ∈ E, ∀ p ∈ commV E, x p ∈ commV E) (hker : β.ker = ⊥)
    (hequiv : ∀ (x : ↥E) (p : ↥(commV E)) (hp : (x : MulAut V) p ∈ commV E),
      β ⟨(x : MulAut V) p, hp⟩ = coreAct 3 (θ x) (β p))
    (hK : ∀ x ∈ E, orderOf x = 3 → x ∈ K) :
    commV E ⊓ fixV K = ⊥ := by
  have h3 : orderOf (finRotate 3) = 3 := by
    rw [(isCycle_finRotate_of_le (by norm_num : 2 ≤ 3)).orderOf,
      support_finRotate_of_le (by norm_num : 2 ≤ 3), Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨g, hθg⟩ : ∃ g : ↥E, θ g = finRotate 3 := ⟨θ.symm (finRotate 3), θ.apply_symm_apply _⟩
  have hord : orderOf (g : MulAut V) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq θ g, hθg, h3]
  have hgK : (g : MulAut V) ∈ K := hK _ g.2 hord
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwc, hwf⟩ := Subgroup.mem_inf.1 hw
  have hwf' : (g : MulAut V) w = w := (mem_fixV.1 hwf) _ hgK
  have hgw : (g : MulAut V) w ∈ commV E := hinv _ g.2 w hwc
  have h : β ⟨w, hwc⟩ = coreAct 3 (θ g) (β ⟨w, hwc⟩) := by
    rw [← hequiv g ⟨w, hwc⟩ hgw]
    exact congrArg β (Subtype.ext hwf'.symm)
  rw [hθg] at h
  have hperm : permAct 3 (finRotate 3) ((β ⟨w, hwc⟩ : ↥(coreMod 3)) : PermMod 3) =
      ((β ⟨w, hwc⟩ : ↥(coreMod 3)) : PermMod 3) := by
    calc permAct 3 (finRotate 3) ((β ⟨w, hwc⟩ : ↥(coreMod 3)) : PermMod 3)
        = (((coreAct 3 (finRotate 3) (β ⟨w, hwc⟩) : ↥(coreMod 3))) : PermMod 3) :=
          (coreAct_coe 3 (finRotate 3) _).symm
      _ = ((β ⟨w, hwc⟩ : ↥(coreMod 3)) : PermMod 3) := by rw [← h]
  have hu1 : β ⟨w, hwc⟩ = 1 :=
    Subtype.ext (perm_rotate_fix_core3 _ (mem_coreMod.1 (β ⟨w, hwc⟩).2) hperm)
  have hker1 : (⟨w, hwc⟩ : ↥(commV E)) ∈ β.ker := (MonoidHom.mem_ker).2 hu1
  rw [hker, Subgroup.mem_bot] at hker1
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hker1

end CFSG.AGLEmbeddingD2.Tits.E23

end
