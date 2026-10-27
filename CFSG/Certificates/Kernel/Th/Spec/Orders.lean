
module

public import CFSG.Certificates.Kernel.Th.Gen.Orders
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.Kernel.Th.Spec.Big
import CFSG.Certificates.Kernel.Th.Max3S.WordsBase

public section

namespace CFSG.KC.Th.Spec.Orders

open CFSG.KC.Th CFSG.KC.Th.Gen CFSG.KC.Th.Spec

theorem dvd_card_units {M : Type*} [Monoid M] (S : Submonoid M) {g : M} (hg : g ∈ S) {p : ℕ}
    (hp : p.Prime) (h1 : g ^ p = 1) (h2 : g ≠ 1) : p ∣ Nat.card Sˣ := by
  haveI := Fact.mk hp
  set x : S := ⟨g, hg⟩
  have hx : x ^ p = 1 := Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact h1)
  have hu : IsUnit x := IsUnit.of_pow_eq_one hx hp.ne_zero
  have hxo : orderOf x = p := orderOf_eq_prime hx (fun h => h2 (congrArg Subtype.val h))
  have h3 := orderOf_dvd_natCard hu.unit
  rwa [← orderOf_units, IsUnit.unit_spec, hxo] at h3

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}

theorem pkMat_wordAB_mem (hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {S : Submonoid (Matrix (Fin 248) (Fin 248) (ZMod 2))} {A B Bi : ℕ} (hA : pkMat A ∈ S)
    (hB : pkMat B ∈ S) (hBi : pkMat Bi ∈ S) (w n : ℕ) :
    pkMat (BigS.wordAB c rm ONE A B Bi w n) ∈ S := by
  rw [CFSG.KC.Th.Max3S.pkMat_wordAB_range hk]
  refine Submonoid.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  unfold wordLetter
  split_ifs
  · exact hA
  · exact hB
  · exact hBi

theorem primeOrder_spec (hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {M p nb : ℕ} (hM : InLayout M) (hp : p < 2 ^ nb) (h : BigS.primeOrder c rm ONE M p nb = true) :
    pkMat M ^ p = 1 ∧ pkMat M ≠ 1 := by
  unfold BigS.primeOrder at h
  have h1 := andB_left h
  have h2 := andB_right h
  refine ⟨?_, fun e => ?_⟩
  · rw [← pkMat_powB hk M p nb hp, Nat.eq_of_beq_eq_true h1, pkMat_one hk]
  · have hne : Nat.beq M ONE = false := by
      cases hb : Nat.beq M ONE
      · rfl
      · rw [hb] at h2
        exact absurd h2 (by decide)
    have := pkMat_inj hM (inLayout_one hk) (e.trans (pkMat_one hk).symm)
    rw [this, Nat.beq_refl] at hne
    exact absurd hne (by decide)

theorem orders_facts (D : OrdersData) (h : ordersChk D = true) :
    13 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 (String.ofList D.ThSeed_LA)
        (String.ofList D.ThSeed_LB))ˣ ∧
      19 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 (String.ofList D.ThSeed_LA)
        (String.ofList D.ThSeed_LB))ˣ ∧
      31 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 (String.ofList D.ThSeed_LA)
        (String.ofList D.ThSeed_LB))ˣ ∧
      (CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList D.ThSeed_LA) *
        CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList D.ThSeed_LB)) ^ 19 = 1 := by
  set S := CFSG.Blueprint.NativeSporadic.seedMonoid 2 248 1 (String.ofList D.ThSeed_LA)
    (String.ofList D.ThSeed_LB) with hS
  unfold ordersChk at h
  have hX := andB_left h
  have hY := andB_right h
  have hX1 := andB_left hX
  have hX2 := andB_right hX
  have hk := andB_right (andB_left hX1)
  have hdA := andB_left (andB_right hX1)
  have hdB := andB_left (andB_right (andB_right hX1))
  have hB3 := andB_left (andB_right (andB_left hX2))
  have hR1 := CFSG.KC.Th.Max3S.eq_of_eqN (andB_left (andB_right (andB_right hX2)))
  have hR2 := CFSG.KC.Th.Max3S.eq_of_eqN (andB_right (andB_right (andB_right hX2)))
  have hY1 := andB_left hY
  have hBi := CFSG.KC.Th.Max3S.eq_of_eqN (andB_right (andB_right (andB_left hY1)))
  have hP13 := andB_left (andB_right hY1)
  have hP31 := andB_left (andB_right (andB_right hY1))
  have hP19 := andB_right (andB_right (andB_right hY1))
  have hAm : pkMat (D.ThS_RBf 1) =
      CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList D.ThSeed_LA) := by
    rw [hR1, (decOK_sound hdA).2, CFSG.Sporadic.Th.rowsMatrix_rowsOf]
  have hBm : pkMat (D.ThS_RBf 2) =
      CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList D.ThSeed_LB) := by
    rw [hR2, (decOK_sound hdB).2, CFSG.Sporadic.Th.rowsMatrix_rowsOf]
  have hB3m : pkMat (D.ThS_RBf 2) * pkMat (D.ThS_RBf 2) * pkMat (D.ThS_RBf 2) = 1 := by
    have e := congrArg pkMat (CFSG.KC.Th.Max3S.eq_of_eqN hB3)
    rw [pkMat_mulB hk, pkMat_mulB hk, pkMat_one hk, ← hR2] at e
    exact e
  have hBim : pkMat D.ThS_Bi = pkMat (D.ThS_RBf 2) * pkMat (D.ThS_RBf 2) := by
    have e := congrArg pkMat hBi
    rw [pkMat_mulB hk, pkMat_one hk] at e
    calc pkMat D.ThS_Bi = (pkMat (D.ThS_RBf 2) * pkMat (D.ThS_RBf 2) * pkMat (D.ThS_RBf 2)) *
          pkMat D.ThS_Bi := by rw [hB3m, one_mul]
      _ = pkMat (D.ThS_RBf 2) * pkMat (D.ThS_RBf 2) *
          (pkMat (D.ThS_RBf 2) * pkMat D.ThS_Bi) := by rw [mul_assoc]
      _ = pkMat (D.ThS_RBf 2) * pkMat (D.ThS_RBf 2) := by rw [e, mul_one]
  have mA : pkMat (D.ThS_RBf 1) ∈ S := by
    rw [hAm]
    exact Submonoid.subset_closure (Set.mem_insert _ _)
  have mB : pkMat (D.ThS_RBf 2) ∈ S := by
    rw [hBm]
    exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
  have mBi : pkMat D.ThS_Bi ∈ S := by
    rw [hBim]
    exact S.mul_mem mB mB
  have lw : ∀ w n, InLayout (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThS_RBf 1) (D.ThS_RBf 2)
      D.ThS_Bi w (n + 1)) := fun w n => inLayout_mulB hk _ _
  obtain ⟨h13a, h13b⟩ := primeOrder_spec hk (lw _ 20) (by norm_num) hP13
  obtain ⟨h31a, h31b⟩ := primeOrder_spec hk (lw _ 24) (by norm_num) hP31
  obtain ⟨h19a, h19b⟩ := primeOrder_spec hk (inLayout_mulB hk _ _) (by norm_num) hP19
  rw [pkMat_mulB hk] at h19a h19b
  refine ⟨dvd_card_units S (pkMat_wordAB_mem hk mA mB mBi _ _) (by norm_num) h13a h13b,
    dvd_card_units S (S.mul_mem mA mB) (by norm_num) h19a h19b,
    dvd_card_units S (pkMat_wordAB_mem hk mA mB mBi _ _) (by norm_num) h31a h31b, ?_⟩
  rw [← hAm, ← hBm]
  exact h19a

end CFSG.KC.Th.Spec.Orders

end
