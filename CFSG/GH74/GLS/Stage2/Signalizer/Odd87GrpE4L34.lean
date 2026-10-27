module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
import CFSG.GH74.Orders.LieType
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint

open scoped IsMulCommutative in
theorem inf_center_sylow_eq_bot_of_perfect {J : Type*} [Group J] [Finite J] [Group.IsPerfect J] {r : ℕ}
    [Fact r.Prime] (P : Sylow r J) (hab : ∀ x ∈ (P : Subgroup J), ∀ y ∈ (P : Subgroup J), x * y = y * x) :
    (P : Subgroup J) ⊓ center J = ⊥ := by
  have : IsMulCommutative (P : Subgroup J) := ⟨⟨fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2)⟩⟩
  rw [eq_bot_iff]
  rintro g ⟨hgP, hgZ⟩
  have hkey : ∀ (k : ℕ) (g₀ : J), g₀⁻¹ * g ^ k * g₀ ∈ (P : Subgroup J) → g₀⁻¹ * g ^ k * g₀ = g ^ k := by
    intro k g₀ _
    have hc : g ^ k ∈ center J := Subgroup.pow_mem _ hgZ k
    rw [Subgroup.mem_center_iff] at hc
    rw [mul_assoc, ← hc g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id (P : Subgroup J)) g hkey
  have h2 : MonoidHom.transfer (MonoidHom.id (P : Subgroup J)) g = 1 := by
    have : Group.IsPerfect (MonoidHom.transfer (MonoidHom.id (P : Subgroup J))).range :=
      Group.IsPerfect.range _
    have : Subsingleton (MonoidHom.transfer (MonoidHom.id (P : Subgroup J))).range :=
      Group.IsPerfect.subsingleton_of_isMulCommutative
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨_, g, rfl⟩ : (MonoidHom.transfer (MonoidHom.id (P : Subgroup J))).range) 1)
  rw [h2] at h1
  have h3 : (⟨g, hgP⟩ : (P : Subgroup J)) ^ (P : Subgroup J).index = 1 ^ (P : Subgroup J).index := by
    rw [one_pow]
    exact Subtype.ext (by simpa using h1.symm)
  have h4 := (P.2.powEquiv' P.not_dvd_index).injective h3
  have h5 : g = 1 := congrArg Subtype.val h4
  rw [h5]
  exact Subgroup.one_mem _

section L34

theorem pPrimeCore_le_center_of_isQuasisimple_abs {J : Type*} [Group J] [Finite J] (hJ : IsQuasisimple J) :
    pPrimeCore 2 J ≤ center J := by
  have hodd : Odd (Nat.card (pPrimeCore 2 J)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hJ pPrimeCore_normal with h | h
  · exfalso
    have hodd' : Odd (Nat.card J) := by
      rw [h, Subgroup.card_top] at hodd
      exact hodd
    have hsolv : Group.IsSolvable J := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
    have : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hJ
    have : Group.IsPerfect J := hJ.1
    exact Group.IsPerfect.not_isSolvable J hsolv
  · exact h

private theorem not_sq_dvd_20160 {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2) (h3 : r ≠ 3) : ¬ r ^ 2 ∣ 20160 := by
  intro h
  have hd : r ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 := dvd_trans (dvd_pow_self r two_ne_zero) h
  rcases (Nat.Prime.dvd_mul hr).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hr).mp hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hr).mp hd with hd | hd
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
      · exact h3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow hd))
    · have : r = 5 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hd
      subst this
      revert h
      norm_num
  · have : r = 7 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hd
    subst this
    revert h
    norm_num

theorem pPrimeCore_eq_bot_of_l34 {J : Type} [Group J] [Finite J] (hJ : IsQuasisimple J)
    (hL : LieModel (J ⧸ pPrimeCore 2 J) .PSL 3 2 2) (hcop3 : Nat.Coprime 3 (Nat.card (pPrimeCore 2 J))) :
    pPrimeCore 2 J = ⊥ := by
  by_contra hne
  have hcard : Nat.card (J ⧸ pPrimeCore 2 J) = 20160 := by
    rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hL]
    decide
  have : Group.IsPerfect J := hJ.1
  have hcentral := pPrimeCore_le_center_of_isQuasisimple_abs hJ
  have hN1 : Nat.card (pPrimeCore 2 J) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hN1
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact absurd (Nat.Coprime.eq_one_of_dvd pPrimeCore_coprime_card hrdvd) (by norm_num)
  have hr3 : r ≠ 3 := by
    rintro rfl
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop3 hrdvd) (by norm_num)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := pPrimeCore 2 J) r hrdvd
  have hgord : orderOf (g : J) = r := by rw [Subgroup.orderOf_coe]; exact hg
  have hpg : IsPGroup r (Subgroup.zpowers (g : J)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hgord, pow_one])
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  have hgP : (g : J) ∈ (P : Subgroup J) := hP (Subgroup.mem_zpowers _)
  have hgZ : (g : J) ∈ center J := hcentral g.2
  let f : ↥(P : Subgroup J) →* J ⧸ pPrimeCore 2 J :=
    (QuotientGroup.mk' (pPrimeCore 2 J)).comp (P : Subgroup J).subtype
  have hpgr : IsPGroup r f.range :=
    P.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcyc : IsCyclic f.range := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hpgr
    have hdvd : Nat.card f.range ∣ 20160 := hcard ▸ Subgroup.card_subgroup_dvd_card f.range
    have hk1 : k ≤ 1 := by
      by_contra hk2
      exact not_sq_dvd_20160 hr hr2 hr3
        (dvd_trans (pow_dvd_pow r (by omega : 2 ≤ k)) (hk ▸ hdvd))
    exact isCyclic_of_card_dvd_prime (p := r) (hk ▸ (pow_dvd_pow r hk1).trans (by rw [pow_one]))
  have hker : f.rangeRestrict.ker ≤ center ↥(P : Subgroup J) := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
    have hxN : (x : J) ∈ pPrimeCore 2 J := (QuotientGroup.eq_one_iff _).mp hx
    have hxZ : (x : J) ∈ center J := hcentral hxN
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxZ y)
  have hcomm : IsMulCommutative ↥(P : Subgroup J) :=
    f.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center hker
  have hab : ∀ x ∈ (P : Subgroup J), ∀ y ∈ (P : Subgroup J), x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(P : Subgroup J)) ⟨y, hy⟩)
  have hbot := inf_center_sylow_eq_bot_of_perfect P hab
  have hg1 : (g : J) = 1 := by
    have : (g : J) ∈ (P : Subgroup J) ⊓ center J := ⟨hgP, hgZ⟩
    rw [hbot] at this
    exact this
  rw [hg1, orderOf_one] at hgord
  exact hr.one_lt.ne hgord

end L34

section PGL34

theorem card_pgl_three_of_card_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card (Matrix.ProjGenLinGroup (Fin 3) F) = 60480 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) F) = 181440 := by
    rw [Matrix.card_GL_field, hq]
    decide
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 3) : Fˣ → Matrix.GeneralLinearGroup (Fin 3) F) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 3) F =>
      ((A : Matrix (Fin 3) (Fin 3) F) 0 0)) hxy
    simpa [Matrix.GeneralLinearGroup.scalar] using h
  have hcenter : Nat.card (Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F)) = 3 := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar,
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units, hF]
  let mkPGL : Matrix.GeneralLinearGroup (Fin 3) F →* Matrix.ProjGenLinGroup (Fin 3) F :=
    Matrix.ProjGenLinGroup.mk
  have hrange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hindex : (Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F)).index =
      Nat.card (Matrix.ProjGenLinGroup (Fin 3) F) := by
    calc
      (Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F)).index = mkPGL.ker.index := by
        rw [Matrix.ProjGenLinGroup.ker_mk]
      _ = Nat.card mkPGL.range := Subgroup.index_ker mkPGL
      _ = Nat.card (Matrix.ProjGenLinGroup (Fin 3) F) := by rw [hrange]; simp
  have hmul := (Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) F)).index_mul_card
  rw [hindex, hcenter, hGL] at hmul
  omega

theorem card_pgl3_four_eq {M L : Type} [Group M] [Group L] [Finite M] [Finite L] (hM : IsPGL3Four M)
    (hL : LieModel L .PSL 3 2 2) : Nat.card M = 3 * Nat.card L := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hM
  rw [Nat.card_congr e.toEquiv, card_pgl_three_of_card_four hF,
    CFSG.GH74.card_of_lieModel_PSL (by norm_num) hL]
  decide

end PGL34

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
