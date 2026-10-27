module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Red
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace LiftCommute

section Prelim

theorem mem_of_sq_mem_of_pow_odd {G : Type*} [Group G] {A : Subgroup G} {g : G} {n : ℕ}
    (hn : Odd n) (hg : g ^ n = 1) (h2 : g ^ 2 ∈ A) : g ∈ A := by
  obtain ⟨k, rfl⟩ := hn
  have hgk : g = (g ^ 2) ^ (k + 1) := by
    calc g = g ^ (2 * k + 1) * g := by rw [hg, one_mul]
      _ = g ^ (2 * k + 1 + 1) := (pow_succ g _).symm
      _ = g ^ (2 * (k + 1)) := by rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
      _ = (g ^ 2) ^ (k + 1) := pow_mul g 2 (k + 1)
  rw [hgk]
  exact A.pow_mem h2 _

theorem exists_fixed_of_involutive_odd {S : Type*} [Finite S] {f : S → S}
    (hf : Function.Involutive f) (hodd : Odd (Nat.card S)) : ∃ y, f y = y := by
  classical
  have : Fintype S := Fintype.ofFinite S
  let g : Function.End S := f
  have hg : g ^ 2 ^ 1 = 1 := by
    funext y
    show f (f y) = y
    exact hf y
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hg
  by_contra hno
  have h0 : Fintype.card (Function.fixedPoints g) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun z => hno ⟨z.1, z.2⟩⟩
  rw [h0, ← Nat.card_eq_fintype_card] at hmod
  have h2 : 2 ∣ Nat.card S := (Nat.modEq_zero_iff_dvd).mp hmod
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem eq_one_of_central_sq {N : Type*} [Group N] {J : Subgroup N} {x : N} (hx : x ∈ J)
    (hc : ∀ c ∈ J, x * c = c * x) (hxx : x * x = 1)
    (hZ : Odd (Nat.card ↥(Subgroup.center ↥J))) : x = 1 := by
  let X : ↥(Subgroup.center ↥J) :=
    ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm⟩
  have hX2 : X ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (Subtype.ext hxx)
  have h2 : orderOf X ∣ 2 := orderOf_dvd_of_pow_eq_one hX2
  have hcard : orderOf X ∣ Nat.card ↥(Subgroup.center ↥J) := orderOf_dvd_natCard X
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · have hX1 : X = 1 := orderOf_eq_one_iff.mp h
    exact congrArg (fun y : ↥(Subgroup.center ↥J) => ((y : ↥J) : N)) hX1
  · exfalso
    rw [h] at hcard
    exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr hcard)

open CFSG.ComponentClassification.PerfectAutomorphisms in
theorem actCenterQuot_of_mem {N : Type*} [Group N] (J : Subgroup N) {x : N} (hx : x ∈ J) :
    actCenterQuot J ⟨x, Subgroup.le_normalizer hx⟩ =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) ⟨x, hx⟩) := by
  ext y
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) y
  change onCenterQuotient (J.normalizerMonoidHom ⟨x, Subgroup.le_normalizer hx⟩)
    (QuotientGroup.mk' (Subgroup.center ↥J) d) = _
  rw [onCenterQuotient_apply_mk]
  simp only [MulAut.conj_apply, ← map_mul, ← map_inv]
  congr 1

theorem range_conj_normal {Y : Type*} [Group Y] :
    ((MulAut.conj : Y →* MulAut Y).range).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨g, rfl⟩ φ
  refine ⟨φ g, ?_⟩
  ext x
  simp [MulAut.conj_apply]

end Prelim

section NormalForm

theorem exists_normalForm {N : Type*} [Group N] {J V : Subgroup N} {z : N}
    (hzz : z * z = 1) (hVz : ∀ v ∈ V, v * z = z * v)
    (hVn : V ≤ normalizer (J : Set N)) (hzn : z ∈ normalizer (J : Set N))
    {h : N} (hh : h ∈ J ⊔ V ⊔ zpowers z) :
    ∃ x ∈ J, ∃ v ∈ V, h = x * v ∨ h = x * v * z := by
  have hconj : ∀ g ∈ normalizer (J : Set N), ∀ x ∈ J, g * x * g⁻¹ ∈ J := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  set T : Set N := {h | ∃ x ∈ J, ∃ v ∈ V, h = x * v ∨ h = x * v * z} with hT
  have hJT : ∀ x ∈ J, x ∈ T := fun x hx => ⟨x, hx, 1, V.one_mem, Or.inl (by simp)⟩
  have hVT : ∀ v ∈ V, v ∈ T := fun v hv => ⟨1, J.one_mem, v, hv, Or.inl (by simp)⟩
  have hzT : z ∈ T := ⟨1, J.one_mem, 1, V.one_mem, Or.inr (by simp)⟩
  have hmul : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T := by
    rintro a ⟨x, hx, v, hv, rfl | rfl⟩ b ⟨x', hx', v', hv', rfl | rfl⟩
    · exact ⟨x * (v * x' * v⁻¹), J.mul_mem hx (hconj v (hVn hv) x' hx'), v * v',
        V.mul_mem hv hv', Or.inl (by group)⟩
    · exact ⟨x * (v * x' * v⁻¹), J.mul_mem hx (hconj v (hVn hv) x' hx'), v * v',
        V.mul_mem hv hv', Or.inr (by group)⟩
    · have hzx : z * x' * z⁻¹ ∈ J := hconj z hzn x' hx'
      refine ⟨x * (v * (z * x' * z⁻¹) * v⁻¹), J.mul_mem hx (hconj v (hVn hv) _ hzx), v * v',
        V.mul_mem hv hv', Or.inr ?_⟩
      calc x * v * z * (x' * v') = x * v * (z * x' * z⁻¹) * (z * v') := by group
        _ = x * v * (z * x' * z⁻¹) * (v' * z) := by rw [← hVz v' hv']
        _ = x * (v * (z * x' * z⁻¹) * v⁻¹) * (v * v') * z := by group
    · have hzx : z * x' * z⁻¹ ∈ J := hconj z hzn x' hx'
      refine ⟨x * (v * (z * x' * z⁻¹) * v⁻¹), J.mul_mem hx (hconj v (hVn hv) _ hzx), v * v',
        V.mul_mem hv hv', Or.inl ?_⟩
      calc x * v * z * (x' * v' * z) = x * v * (z * x' * z⁻¹) * (z * v') * z := by group
        _ = x * v * (z * x' * z⁻¹) * (v' * z) * z := by rw [← hVz v' hv']
        _ = x * v * (z * x' * z⁻¹) * v' * (z * z) := by group
        _ = x * v * (z * x' * z⁻¹) * v' := by rw [hzz, mul_one]
        _ = (x * (v * (z * x' * z⁻¹) * v⁻¹)) * (v * v') := by group
  let S : Subgroup N :=
    { carrier := T
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      one_mem' := hJT 1 J.one_mem
      inv_mem' := by
        rintro a ⟨x, hx, v, hv, rfl | rfl⟩
        · rw [mul_inv_rev]
          exact hmul _ (hVT _ (V.inv_mem hv)) _ (hJT _ (J.inv_mem hx))
        · rw [mul_inv_rev, mul_inv_rev, hzi]
          exact hmul _ hzT _ (hmul _ (hVT _ (V.inv_mem hv)) _ (hJT _ (J.inv_mem hx))) }
  have hJS : J ≤ S := fun x hx => hJT x hx
  have hVS : V ≤ S := fun v hv => hVT v hv
  have hzS : zpowers z ≤ S := by
    rw [zpowers_le]
    exact hzT
  exact (sup_le (sup_le hJS hVS) hzS) hh

end NormalForm

section CaseInner

theorem commute_of_inner {N : Type*} [Group N] {J : Subgroup N} [Group.IsPerfect ↥J]
    (hZ : Odd (Nat.card ↥(Subgroup.center ↥J))) {z : N} (hzz : z * z = 1)
    (hzn : z ∈ normalizer (J : Set N)) {j : N} (hj : j ∈ J)
    (hzj : actCenterQuot J ⟨z, hzn⟩ = actCenterQuot J ⟨j, Subgroup.le_normalizer hj⟩)
    {x : N} (hx : x ∈ J)
    (hcomm : actCenterQuot J ⟨x, Subgroup.le_normalizer hx⟩ * actCenterQuot J ⟨z, hzn⟩ =
      actCenterQuot J ⟨z, hzn⟩ * actCenterQuot J ⟨x, Subgroup.le_normalizer hx⟩) :
    x * z = z * x := by
  have hjn : j ∈ normalizer (J : Set N) := Subgroup.le_normalizer hj
  have hxn : x ∈ normalizer (J : Set N) := Subgroup.le_normalizer hx
  obtain ⟨k, hkdef⟩ : ∃ k : N, k = j⁻¹ * z := ⟨_, rfl⟩
  have hzk : z = j * k := by rw [hkdef]; group
  have hkn : k ∈ normalizer (J : Set N) := by
    rw [hkdef]
    exact (normalizer (J : Set N)).mul_mem ((normalizer (J : Set N)).inv_mem hjn) hzn
  have hk1 : actCenterQuot J ⟨k, hkn⟩ = 1 := by
    have e : (⟨k, hkn⟩ : ↥(normalizer (J : Set N))) = ⟨j, hjn⟩⁻¹ * ⟨z, hzn⟩ :=
      Subtype.ext (by simp [hkdef])
    rw [e, map_mul, map_inv, ← hzj, inv_mul_cancel]
  have hkc : ∀ c ∈ J, k * c = c * k := commute_of_actCenterQuot_eq_one J ⟨k, hkn⟩ hk1
  have hkj : k * j = j * k := hkc j hj
  have hkk : ∀ c ∈ J, (k * k) * c = c * (k * k) := by
    intro c hc
    calc k * k * c = k * (k * c) := by group
      _ = k * (c * k) := by rw [hkc c hc]
      _ = (k * c) * k := by group
      _ = (c * k) * k := by rw [hkc c hc]
      _ = c * (k * k) := by group
  have hjk2 : (j * j) * (k * k) = 1 := by
    calc (j * j) * (k * k) = j * (j * k) * k := by group
      _ = j * (k * j) * k := by rw [hkj]
      _ = (j * k) * (j * k) := by group
      _ = 1 := by rw [← hzk]; exact hzz
  have hkj2 : (k * k) * (j * j) = 1 := mul_eq_one_comm.mp hjk2
  have hu : ∀ c ∈ J, (j * j) * c = c * (j * j) := by
    intro c hc
    calc j * j * c = (j * j) * c * ((k * k) * (j * j)) := by rw [hkj2, mul_one]
      _ = (j * j) * (c * (k * k)) * (j * j) := by group
      _ = (j * j) * ((k * k) * c) * (j * j) := by rw [hkk c hc]
      _ = ((j * j) * (k * k)) * c * (j * j) := by group
      _ = c * (j * j) := by rw [hjk2, one_mul]
  set κ : N := x * j * x⁻¹ * j⁻¹ with hκdef
  have hκJ : κ ∈ J :=
    J.mul_mem (J.mul_mem (J.mul_mem hx hj) (J.inv_mem hx)) (J.inv_mem hj)
  have hκn : κ ∈ normalizer (J : Set N) := Subgroup.le_normalizer hκJ
  have hκ1 : actCenterQuot J ⟨κ, hκn⟩ = 1 := by
    have e : (⟨κ, hκn⟩ : ↥(normalizer (J : Set N))) =
        ⟨x, hxn⟩ * ⟨j, hjn⟩ * ⟨x, hxn⟩⁻¹ * ⟨j, hjn⟩⁻¹ := Subtype.ext (by simp [hκdef])
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hzj, hcomm]
    group
  have hκc : ∀ c ∈ J, κ * c = c * κ := commute_of_actCenterQuot_eq_one J ⟨κ, hκn⟩ hκ1
  have hκκ : κ * κ = 1 := by
    have e1 : x * j * x⁻¹ = κ * j := by rw [hκdef]; group
    have e2 : (x * j * x⁻¹) * (x * j * x⁻¹) = x * (j * j) * x⁻¹ := by group
    have e3 : x * (j * j) * x⁻¹ = j * j := by
      rw [← hu x hx]
      group
    have e4 : (κ * j) * (κ * j) = κ * κ * (j * j) := by
      calc (κ * j) * (κ * j) = κ * (j * κ) * j := by group
        _ = κ * (κ * j) * j := by rw [← hκc j hj]
        _ = κ * κ * (j * j) := by group
    have e5 : κ * κ * (j * j) = 1 * (j * j) := by
      rw [← e4, ← e1, e2, e3, one_mul]
    exact mul_right_cancel e5
  have hκ : κ = 1 := eq_one_of_central_sq hκJ hκc hκκ hZ
  have hxj : x * j = j * x := by
    have h1 : x * j * x⁻¹ * j⁻¹ = 1 := hκ
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  rw [hzk]
  calc x * (j * k) = (x * j) * k := by group
    _ = (j * x) * k := by rw [hxj]
    _ = j * (x * k) := by group
    _ = j * (k * x) := by rw [← hkc x hx]
    _ = j * k * x := by group

end CaseInner

section CaseOuter

theorem eq_one_of_ker_sq {N : Type*} [Group N] {J : Subgroup N} [Group.IsPerfect ↥J]
    (hZ : Odd (Nat.card ↥(Subgroup.center ↥J))) {p : ℕ} (hpodd : Odd p)
    {V : Subgroup N} (hVp : IsPGroup p ↥V) {z : N} (hzz : z * z = 1)
    (hVz : ∀ v ∈ V, v * z = z * v) (hVn : V ≤ normalizer (J : Set N))
    (hzn : z ∈ normalizer (J : Set N))
    (hnot : actCenterQuot J ⟨z, hzn⟩ ∉
      (MulAut.conj : (↥J ⧸ Subgroup.center ↥J) →* MulAut (↥J ⧸ Subgroup.center ↥J)).range)
    {k : N} (hk : k ∈ J ⊔ V ⊔ zpowers z) (hkn : k ∈ normalizer (J : Set N))
    (hk1 : actCenterQuot J ⟨k, hkn⟩ = 1) (hkk : k * k = 1) : k = 1 := by
  obtain ⟨x, hx, v, hv, hkx | hkx⟩ := exists_normalForm hzz hVz hVn hzn hk
  all_goals
    have hvn : v ∈ normalizer (J : Set N) := hVn hv
    have hxn : x ∈ normalizer (J : Set N) := Subgroup.le_normalizer hx
    obtain ⟨n, hn⟩ := hVp ⟨v, hv⟩
    have hvpow : v ^ p ^ n = 1 := by
      have := congrArg (fun g : ↥V => (g : N)) hn
      simpa using this
  ·
    have hw : v * x * v⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hvn x).mp hx
    have hvv : v * v ∈ J := by
      have e : x * (v * x * v⁻¹) * (v * v) = 1 := by
        calc x * (v * x * v⁻¹) * (v * v) = (x * v) * (x * v) := by group
          _ = 1 := by rw [← hkx]; exact hkk
      have : v * v = (x * (v * x * v⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right e
      rw [this]
      exact J.inv_mem (J.mul_mem hx hw)
    have hvJ : v ∈ J := mem_of_sq_mem_of_pow_odd (hpodd.pow (n := n)) hvpow (by rwa [sq])
    have hkJ : k ∈ J := by rw [hkx]; exact J.mul_mem hx hvJ
    exact eq_one_of_central_sq hkJ (commute_of_actCenterQuot_eq_one J ⟨k, hkn⟩ hk1) hkk hZ
  ·
    exfalso
    apply hnot
    set P : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)) :=
      (MulAut.conj : (↥J ⧸ Subgroup.center ↥J) →* MulAut (↥J ⧸ Subgroup.center ↥J)).range
      with hP
    have hPn : P.Normal := range_conj_normal
    set a := actCenterQuot J ⟨v, hvn⟩ with ha
    set b := actCenterQuot J ⟨x, hxn⟩ with hb
    set c := actCenterQuot J ⟨z, hzn⟩ with hc
    have hbP : b ∈ P := by
      rw [hb, actCenterQuot_of_mem J hx]
      exact ⟨_, rfl⟩
    have hbac : b * a * c = 1 := by
      have e : (⟨k, hkn⟩ : ↥(normalizer (J : Set N))) = ⟨x, hxn⟩ * ⟨v, hvn⟩ * ⟨z, hzn⟩ :=
        Subtype.ext hkx
      rw [← hk1, e, map_mul, map_mul]
    have hcc : c * c = 1 := by
      have e : (⟨z, hzn⟩ : ↥(normalizer (J : Set N))) * ⟨z, hzn⟩ = 1 := Subtype.ext hzz
      rw [hc, ← map_mul, e, map_one]
    have hcab : c = a⁻¹ * b⁻¹ := by
      have := eq_inv_of_mul_eq_one_right hbac
      rw [this, mul_inv_rev]
    have hapow : a ^ p ^ n = 1 := by
      rw [ha, ← map_pow]
      have e : (⟨v, hvn⟩ : ↥(normalizer (J : Set N))) ^ p ^ n = 1 :=
        Subtype.ext (by simpa using hvpow)
      rw [e, map_one]
    have ha2 : a ^ 2 ∈ P := by
      have e : a ^ 2 = (a * b⁻¹ * a⁻¹) * b⁻¹ := by
        calc a ^ 2 = a * a * (c * c) := by rw [hcc, mul_one, sq]
          _ = a * a * ((a⁻¹ * b⁻¹) * (a⁻¹ * b⁻¹)) := by rw [hcab]
          _ = (a * b⁻¹ * a⁻¹) * b⁻¹ := by group
      rw [e]
      exact P.mul_mem (hPn.conj_mem _ (P.inv_mem hbP) a) (P.inv_mem hbP)
    have haP : a ∈ P := mem_of_sq_mem_of_pow_odd (hpodd.pow (n := n)) hapow ha2
    rw [hcab]
    exact P.mul_mem (P.inv_mem haP) (P.inv_mem hbP)

end CaseOuter

end LiftCommute

theorem lift_commute {N : Type} [Group N] [Finite N] {J : Subgroup N} (hJ : IsComponent J)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hZ : Odd (Nat.card ↥(Subgroup.center ↥J)))
    {V : Subgroup N} (hVp : IsPGroup p ↥V) {z : N} (hzz : z * z = 1)
    (hVz : ∀ v ∈ V, v * z = z * v)
    (hVn : V ≤ normalizer (J : Set N)) (hzn : z ∈ normalizer (J : Set N))
    {h : N} (hh : h ∈ J ⊔ V ⊔ zpowers z) (hhn : h ∈ normalizer (J : Set N))
    (hcomm : actCenterQuot J ⟨h, hhn⟩ * actCenterQuot J ⟨z, hzn⟩ =
      actCenterQuot J ⟨z, hzn⟩ * actCenterQuot J ⟨h, hhn⟩) :
    ∃ (h' : N) (hh'n : h' ∈ normalizer (J : Set N)), h' ∈ J ⊔ V ⊔ zpowers z ∧
      h' * z = z * h' ∧ actCenterQuot J ⟨h', hh'n⟩ = actCenterQuot J ⟨h, hhn⟩ := by
  classical
  have _ := hp
  have hperf : Group.IsPerfect ↥J := hJ.1.1
  by_cases hin : actCenterQuot J ⟨z, hzn⟩ ∈
      (MulAut.conj : (↥J ⧸ Subgroup.center ↥J) →* MulAut (↥J ⧸ Subgroup.center ↥J)).range
  ·
    obtain ⟨y, hy⟩ := hin
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) y
    have hj : (c : N) ∈ J := c.2
    have hzj : actCenterQuot J ⟨z, hzn⟩ =
        actCenterQuot J ⟨(c : N), Subgroup.le_normalizer hj⟩ := by
      rw [LiftCommute.actCenterQuot_of_mem J hj]
      exact hy.symm
    refine ⟨h, hhn, hh, ?_, rfl⟩
    obtain ⟨x, hx, v, hv, hxv | hxv⟩ := LiftCommute.exists_normalForm hzz hVz hVn hzn hh
    all_goals
      have hvn : v ∈ normalizer (J : Set N) := hVn hv
      have hxn : x ∈ normalizer (J : Set N) := Subgroup.le_normalizer hx
      have hvz : actCenterQuot J ⟨v, hvn⟩ * actCenterQuot J ⟨z, hzn⟩ =
          actCenterQuot J ⟨z, hzn⟩ * actCenterQuot J ⟨v, hvn⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hVz v hv)
    · have hψh : actCenterQuot J ⟨x, hxn⟩ =
          actCenterQuot J ⟨h, hhn⟩ * (actCenterQuot J ⟨v, hvn⟩)⁻¹ := by
        have e : (⟨h, hhn⟩ : ↥(normalizer (J : Set N))) = ⟨x, hxn⟩ * ⟨v, hvn⟩ :=
          Subtype.ext hxv
        rw [e, map_mul]
        group
      have hcx : actCenterQuot J ⟨x, hxn⟩ * actCenterQuot J ⟨z, hzn⟩ =
          actCenterQuot J ⟨z, hzn⟩ * actCenterQuot J ⟨x, hxn⟩ := by
        rw [hψh]
        exact Commute.mul_left (a := actCenterQuot J ⟨h, hhn⟩) hcomm
          (Commute.inv_left (a := actCenterQuot J ⟨v, hvn⟩) hvz)
      have hxz : x * z = z * x :=
        LiftCommute.commute_of_inner hZ hzz hzn hj hzj hx hcx
      rw [hxv]
      calc x * v * z = x * (v * z) := by group
        _ = x * (z * v) := by rw [hVz v hv]
        _ = (x * z) * v := by group
        _ = (z * x) * v := by rw [hxz]
        _ = z * (x * v) := by group
    · have hψh : actCenterQuot J ⟨x, hxn⟩ =
          actCenterQuot J ⟨h, hhn⟩ * (actCenterQuot J ⟨z, hzn⟩)⁻¹ *
            (actCenterQuot J ⟨v, hvn⟩)⁻¹ := by
        have e : (⟨h, hhn⟩ : ↥(normalizer (J : Set N))) = ⟨x, hxn⟩ * ⟨v, hvn⟩ * ⟨z, hzn⟩ :=
          Subtype.ext hxv
        rw [e, map_mul, map_mul]
        group
      have hcx : actCenterQuot J ⟨x, hxn⟩ * actCenterQuot J ⟨z, hzn⟩ =
          actCenterQuot J ⟨z, hzn⟩ * actCenterQuot J ⟨x, hxn⟩ := by
        rw [hψh]
        exact Commute.mul_left (a := actCenterQuot J ⟨h, hhn⟩ * (actCenterQuot J ⟨z, hzn⟩)⁻¹)
          (Commute.mul_left (a := actCenterQuot J ⟨h, hhn⟩) hcomm
            (Commute.inv_left (Commute.refl (actCenterQuot J ⟨z, hzn⟩))))
          (Commute.inv_left (a := actCenterQuot J ⟨v, hvn⟩) hvz)
      have hxz : x * z = z * x :=
        LiftCommute.commute_of_inner hZ hzz hzn hj hzj hx hcx
      rw [hxv]
      calc x * v * z * z = x * (v * z) * z := by group
        _ = x * (z * v) * z := by rw [hVz v hv]
        _ = (x * z) * v * z := by group
        _ = (z * x) * v * z := by rw [hxz]
        _ = z * (x * v * z) := by group
  ·
    set Hs : Subgroup N := J ⊔ V ⊔ zpowers z with hHs
    have hzH : z ∈ Hs := Subgroup.mem_sup_right (mem_zpowers z)
    have hHn : Hs ≤ normalizer (J : Set N) :=
      sup_le (sup_le Subgroup.le_normalizer hVn) ((zpowers_le).mpr hzn)
    let ψH : ↥Hs →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
      (actCenterQuot J).comp (Subgroup.inclusion hHn)
    let h₀ : ↥Hs := ⟨h, hh⟩
    let zH : ↥Hs := ⟨z, hzH⟩
    have hzH2 : zH * zH = 1 := Subtype.ext hzz
    have hKodd : Odd (Nat.card ↥ψH.ker) := by
      by_contra hno
      have h2 : 2 ∣ Nat.card ↥ψH.ker := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hno)
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have hg2 : g * g = 1 := by
        have := pow_orderOf_eq_one g
        rw [hg, pow_two] at this
        exact this
      have hg1 : g ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hg
        omega
      have hk1 := LiftCommute.eq_one_of_ker_sq hZ hpodd hVp hzz hVz hVn hzn hin (k := g.1.1)
        g.1.2 (hHn g.1.2) (MonoidHom.mem_ker.mp g.2)
        (by simpa using congrArg (fun t : ↥ψH.ker => ((t : ↥Hs) : N)) hg2)
      exact hg1 (Subtype.ext (Subtype.ext hk1))
    let S : Type := {y : ↥Hs // ψH y = ψH h₀}
    have hSeq : Nat.card S = Nat.card ↥ψH.ker := by
      refine Nat.card_congr
        { toFun := fun y => ⟨h₀⁻¹ * y.1, by
            rw [MonoidHom.mem_ker, map_mul, map_inv, y.2, inv_mul_cancel]⟩
          invFun := fun k => ⟨h₀ * k.1, by
            rw [map_mul, MonoidHom.mem_ker.mp k.2, mul_one]⟩
          left_inv := fun y => by apply Subtype.ext; simp
          right_inv := fun k => by apply Subtype.ext; simp }
    have hSodd : Odd (Nat.card S) := by
      rw [hSeq]
      exact hKodd
    have hc1 : ψH h₀ * ψH zH = ψH zH * ψH h₀ := hcomm
    let σ : S → S := fun y => ⟨zH * y.1 * zH⁻¹, by
      rw [map_mul, map_mul, map_inv, y.2, ← hc1, mul_inv_cancel_right]⟩
    have hσ : Function.Involutive σ := by
      intro y
      apply Subtype.ext
      show zH * (zH * y.1 * zH⁻¹) * zH⁻¹ = y.1
      have hzi : zH⁻¹ = zH := inv_eq_of_mul_eq_one_right hzH2
      rw [hzi]
      calc zH * (zH * y.1 * zH) * zH = (zH * zH) * y.1 * (zH * zH) := by group
        _ = y.1 := by rw [hzH2]; simp
    obtain ⟨y, hy⟩ := LiftCommute.exists_fixed_of_involutive_odd hσ hSodd
    have hyc : zH * y.1 = y.1 * zH := by
      have h1 : zH * y.1 * zH⁻¹ = y.1 := congrArg (fun t : S => (t.1 : ↥Hs)) hy
      exact mul_inv_eq_iff_eq_mul.mp h1
    exact ⟨(y.1 : N), hHn y.1.2, y.1.2, (congrArg (fun t : ↥Hs => (t : N)) hyc).symm, y.2⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
