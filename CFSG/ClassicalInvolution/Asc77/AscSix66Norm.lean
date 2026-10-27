module

public import CFSG.ClassicalInvolution.Asc77.AscSix66Aux
public import CFSG.ClassicalInvolution.Asc77.WP1Proofs6
public import CFSG.ClassicalInvolution.Asc77.AscSix611

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem four_prod_shift {a0 a1 a2 a3 : G} (h01 : a0 * a1 = a1 * a0) (h02 : a0 * a2 = a2 * a0)
    (h03 : a0 * a3 = a3 * a0) : a1 * a2 * a3 * a0 = a0 * a1 * a2 * a3 := by
  calc a1 * a2 * a3 * a0 = a1 * a2 * (a3 * a0) := by simp only [mul_assoc]
    _ = a1 * a2 * (a0 * a3) := by rw [← h03]
    _ = a1 * (a2 * a0) * a3 := by simp only [mul_assoc]
    _ = a1 * (a0 * a2) * a3 := by rw [← h02]
    _ = (a1 * a0) * a2 * a3 := by simp only [mul_assoc]
    _ = (a0 * a1) * a2 * a3 := by rw [← h01]

theorem pow_conj_shift (x u : G) (i : ℕ) :
    x * (x ^ i * u * (x ^ i)⁻¹) * x⁻¹ = x ^ (i + 1) * u * (x ^ (i + 1))⁻¹ := by
  rw [pow_succ', mul_inv_rev]
  simp only [mul_assoc]

theorem norm_contradiction [Finite G] (hΩ : HypOmegaMod p f Ω)
    {S A B J X : Subgroup G} (hJ : J ∈ Ω) (hBJ : IsSylow2In B J) (hS : IsPGroup 2 S)
    (hBS : B ≤ S) (hXS : X ≤ S) (hAquat : IsQuatSub A) (hBquat : IsQuatSub B)
    (hXinv : ∀ s ∈ S, ∀ g ∈ X, s⁻¹ * g * s ∈ X) (hXN : ∀ g ∈ X, conjSub g A = A)
    (hAX : ∀ g ∈ B, conjSub g A ≤ X)
    (hinj : ∀ g ∈ B, ∀ h ∈ B, conjSub g A = conjSub h A → g = h)
    (hcomm : ∀ g ∈ B, ∀ h ∈ B, g ≠ h → Commutes (conjSub g A) (conjSub h A))
    {x u : G} (hxB : x ∈ B) (hxord : orderOf x = 4) (huA : u ∈ A) (huord : orderOf u = 4) :
    False := by
  have hΩc := hΩ.conjInvariant
  have hx4 : x * x * x * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hxord] at this
    simpa [pow_succ, mul_assoc] using this
  have hinjpow : ∀ g h : ℕ, g < 4 → h < 4 → x ^ g = x ^ h → g = h := fun g h hg hh e =>
    pow_injOn_Iio_orderOf (by rw [hxord]; exact hg) (by rw [hxord]; exact hh) e
  have hxJ : x ∈ J := hBJ.1 hxB
  have hpowB : ∀ i : ℕ, x ^ i ∈ B := fun i => B.pow_mem hxB i
  obtain ⟨u1, hu1⟩ : ∃ u1 : G, u1 = x ^ 1 * u * (x ^ 1)⁻¹ := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u2 : G, u2 = x ^ 2 * u * (x ^ 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨u3, hu3⟩ : ∃ u3 : G, u3 = x ^ 3 * u * (x ^ 3)⁻¹ := ⟨_, rfl⟩
  have hu1m : u1 ∈ conjSub (x ^ 1) A := hu1 ▸ conj_mem_conjSub huA
  have hu2m : u2 ∈ conjSub (x ^ 2) A := hu2 ▸ conj_mem_conjSub huA
  have hu3m : u3 ∈ conjSub (x ^ 3) A := hu3 ▸ conj_mem_conjSub huA
  have hu0m : u ∈ conjSub (x ^ 0) A := by simpa using huA
  have hc : ∀ g h : ℕ, g < 4 → h < 4 → g ≠ h → ∀ a ∈ conjSub (x ^ g) A, ∀ b ∈ conjSub (x ^ h) A,
      a * b = b * a := by
    intro g h hg hh hgh a ha b hb
    have hne : x ^ g ≠ x ^ h := fun e => hgh (hinjpow g h hg hh e)
    exact hcomm _ (hpowB g) _ (hpowB h) hne a ha b hb
  have h01 : u * u1 = u1 * u := hc 0 1 (by norm_num) (by norm_num) (by norm_num) _ hu0m _ hu1m
  have h02 : u * u2 = u2 * u := hc 0 2 (by norm_num) (by norm_num) (by norm_num) _ hu0m _ hu2m
  have h03 : u * u3 = u3 * u := hc 0 3 (by norm_num) (by norm_num) (by norm_num) _ hu0m _ hu3m
  have h12 : u1 * u2 = u2 * u1 := hc 1 2 (by norm_num) (by norm_num) (by norm_num) _ hu1m _ hu2m
  have h13 : u1 * u3 = u3 * u1 := hc 1 3 (by norm_num) (by norm_num) (by norm_num) _ hu1m _ hu3m
  have h23 : u2 * u3 = u3 * u2 := hc 2 3 (by norm_num) (by norm_num) (by norm_num) _ hu2m _ hu3m
  have hx4' : x ^ 4 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxord] at this
  obtain ⟨w, hw⟩ : ∃ w : G, w = u * u1 * u2 * u3 := ⟨_, rfl⟩
  have hxw : x * w * x⁻¹ = w := by
    have e1 : x * u * x⁻¹ = u1 := by rw [hu1, pow_one]
    have e2 : x * u1 * x⁻¹ = u2 := by
      rw [hu1, hu2, pow_conj_shift x u 1]
    have e3 : x * u2 * x⁻¹ = u3 := by
      rw [hu2, hu3, pow_conj_shift x u 2]
    have e4 : x * u3 * x⁻¹ = u := by
      rw [hu3, show (3 : ℕ) = 3 from rfl, pow_conj_shift x u 3, hx4']
      simp
    calc x * w * x⁻¹ = (x * u * x⁻¹) * (x * u1 * x⁻¹) * (x * u2 * x⁻¹) * (x * u3 * x⁻¹) := by
          rw [hw]; group
      _ = u1 * u2 * u3 * u := by rw [e1, e2, e3, e4]
      _ = w := by rw [hw]; exact four_prod_shift h01 h02 h03
  have hxw' : x * w = w * x := by
    have := congrArg (· * x) hxw
    simpa [mul_assoc] using this
  have hAX' : ∀ i : ℕ, conjSub (x ^ i) A ≤ X := fun i => hAX _ (hpowB i)
  have hAXu : u ∈ X := by
    have := hAX' 0 hu0m
    exact this
  have hwX : w ∈ X := by
    rw [hw]
    exact X.mul_mem (X.mul_mem (X.mul_mem hAXu (hAX' 1 hu1m)) (hAX' 2 hu2m)) (hAX' 3 hu3m)
  have hwS : w ∈ S := hXS hwX
  have hwJ : J = conjSub w J := by
    have hx' : w * x * w⁻¹ = x := by
      calc w * x * w⁻¹ = x * w * w⁻¹ := by rw [← hxw']
        _ = x := by group
    have hxwJ : x ∈ conjSub w J := by
      have := conj_mem_conjSub (n := w) hxJ
      rwa [hx'] at this
    have hz2 : IsPGroup 2 ↥(Subgroup.zpowers x) :=
      hBJ.2.1.to_le (Subgroup.zpowers_le.mpr hxB)
    have h4 : 4 ≤ Nat.card (Subgroup.zpowers x) := by rw [Nat.card_zpowers, hxord]
    exact hΩ.eq_of_le_of_le hJ (hΩc w J hJ) hz2 h4 (Subgroup.zpowers_le.mpr hxJ)
      (Subgroup.zpowers_le.mpr hxwJ)
  have hwB : conjSub w B = B := by
    have hB'S : conjSub w B ≤ S := conjSub_le_of_le_of_mem hBS hwS
    have hsyl : IsSylow2In (conjSub w B) J := by
      have := hBJ.conj w
      rwa [← hwJ] at this
    have hS2 : IsPGroup 2 ↥(J ⊓ S) := hS.to_inf_right
    have h1 : J ⊓ S = B := hBJ.eq_of_le hS2 inf_le_left (le_inf hBJ.1 hBS)
    have h2 : J ⊓ S = conjSub w B := hsyl.eq_of_le hS2 inf_le_left (le_inf hsyl.1 hB'S)
    exact h2.symm.trans h1
  have hwy : ∀ y ∈ B, w * y = y * w := by
    intro y hy
    have hyS : y ∈ S := hBS hy
    have hwB' : conjSub w⁻¹ B = B := by
      calc conjSub w⁻¹ B = conjSub w⁻¹ (conjSub w B) := by rw [hwB]
        _ = B := conjSub_inv_conjSub w B
    have hgB : w⁻¹ * y⁻¹ * w * y ∈ B := by
      have h5 : w⁻¹ * y⁻¹ * w⁻¹⁻¹ ∈ conjSub w⁻¹ B := conj_mem_conjSub (B.inv_mem hy)
      rw [hwB', inv_inv] at h5
      exact B.mul_mem h5 hy
    have hgX : w⁻¹ * y⁻¹ * w * y ∈ X := by
      have h5 : y⁻¹ * w * y ∈ X := hXinv y hyS w hwX
      have := X.mul_mem (X.inv_mem hwX) h5
      simpa [mul_assoc] using this
    have hg1 : w⁻¹ * y⁻¹ * w * y = 1 :=
      hinj _ hgB 1 B.one_mem (by rw [hXN _ hgX, conjSub_one])
    have e1 : y⁻¹ * w * y = w := by
      calc y⁻¹ * w * y = w * (w⁻¹ * y⁻¹ * w * y) := by group
        _ = w := by rw [hg1, mul_one]
    calc w * y = y * (y⁻¹ * w * y) := by group
      _ = y * w := by rw [e1]
  obtain ⟨y, hyB, hyx⟩ : ∃ y ∈ B, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    have hle : B ≤ Subgroup.zpowers x := fun y hy => by
      by_contra h
      exact hcon ⟨y, hy, h⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hxord] at h1
    have := hBquat.eight_le
    omega
  set D : Set (Subgroup G) := {R | ∃ g ∈ B, R = conjSub g A} with hD
  have hDcomm : ∀ R ∈ D, ∀ R' ∈ D, R ≠ R' → Commutes R R' := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ hne
    exact hcomm g hg h hh (fun e => hne (by rw [e]))
  have hAD : A ∈ D := ⟨1, B.one_mem, (conjSub_one A).symm⟩
  have key := inf_sup_centers_eq hDcomm hAD
  set Z : Subgroup G := ⨆ R' ∈ D, centerIn R' with hZ
  set YA : Subgroup G := ⨆ R' ∈ D, ⨆ (_ : R' ≠ A), R' with hYA
  have hmemYA : ∀ g ∈ B, g ≠ 1 → ∀ t ∈ conjSub g A, t ∈ YA := by
    intro g hgB hg1 t ht
    have hne : conjSub g A ≠ A := fun e => hg1 (hinj g hgB 1 B.one_mem (by rw [e, conjSub_one]))
    have hle : conjSub g A ≤ YA :=
      le_iSup₂_of_le (conjSub g A) ⟨g, hgB, rfl⟩ (le_iSup_of_le hne le_rfl)
    exact hle ht
  have hpowne : ∀ i : ℕ, 0 < i → i < 4 → x ^ i ≠ 1 := fun i hi0 hi4 =>
    pow_ne_one_of_lt_orderOf (by omega) (by rw [hxord]; exact hi4)
  have hu1Y : u1 ∈ YA := hmemYA (x ^ 1) (hpowB 1) (hpowne 1 (by norm_num) (by norm_num)) _ hu1m
  have hu2Y : u2 ∈ YA := hmemYA (x ^ 2) (hpowB 2) (hpowne 2 (by norm_num) (by norm_num)) _ hu2m
  have hu3Y : u3 ∈ YA := hmemYA (x ^ 3) (hpowB 3) (hpowne 3 (by norm_num) (by norm_num)) _ hu3m
  have hfac : ∀ i : ℕ, y * (x ^ i * u * (x ^ i)⁻¹) * y⁻¹ ∈ YA := by
    intro i
    have hmem : (y * x ^ i) * u * (y * x ^ i)⁻¹ ∈ conjSub (y * x ^ i) A := conj_mem_conjSub huA
    have e : y * (x ^ i * u * (x ^ i)⁻¹) * y⁻¹ = (y * x ^ i) * u * (y * x ^ i)⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    rw [e]
    refine hmemYA (y * x ^ i) (B.mul_mem hyB (hpowB i)) ?_ _ hmem
    intro h
    have : y = (x ^ i)⁻¹ := eq_inv_of_mul_eq_one_left h
    apply hyx
    rw [this]
    exact (Subgroup.zpowers x).inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i)
  have hwYA : w ∈ YA := by
    have e : w = y * w * y⁻¹ := by
      calc w = (w * y) * y⁻¹ := by group
        _ = (y * w) * y⁻¹ := by rw [hwy y hyB]
    have e2 : y * w * y⁻¹ = (y * u * y⁻¹) * (y * u1 * y⁻¹) * (y * u2 * y⁻¹) * (y * u3 * y⁻¹) := by
      rw [hw]
      group
    rw [e, e2]
    have f0 := hfac 0
    have f1 := hfac 1
    have f2 := hfac 2
    have f3 := hfac 3
    rw [← hu1] at f1
    rw [← hu2] at f2
    rw [← hu3] at f3
    simp only [pow_zero, one_mul, inv_one, mul_one] at f0
    exact YA.mul_mem (YA.mul_mem (YA.mul_mem f0 f1) f2) f3
  have huYA : u ∈ YA := by
    have e : u = w * (u1 * u2 * u3)⁻¹ := by rw [hw]; group
    rw [e]
    exact YA.mul_mem hwYA (YA.inv_mem (YA.mul_mem (YA.mul_mem hu1Y hu2Y) hu3Y))
  have huZ : u ∈ Z := by
    have : u ∈ (A ⊔ Z) ⊓ (Z ⊔ YA) := ⟨Subgroup.mem_sup_left huA, Subgroup.mem_sup_right huYA⟩
    rwa [key] at this
  have hYAcomm : Commutes A YA := by
    have hle : YA ≤ Subgroup.centralizer (A : Set G) := by
      refine iSup₂_le fun R' hR' => iSup_le fun hne r hr => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hDcomm A hAD R' hR' (Ne.symm hne) a ha r hr
    intro a ha r hr
    exact Subgroup.mem_centralizer_iff.mp (hle hr) a ha
  have hcenterA : ∀ c ∈ centerIn A, c ∈ A ∧ ∀ t ∈ A, c * t = t * c := by
    rintro _ ⟨c', hc', rfl⟩
    refine ⟨c'.2, fun t ht => ?_⟩
    have := Subgroup.mem_center_iff.mp hc' ⟨t, ht⟩
    exact congrArg Subtype.val this.symm
  set Z' : Subgroup G := ⨆ R' ∈ D, ⨆ (_ : R' ≠ A), centerIn R' with hZ'
  have hZ'YA : Z' ≤ YA := by
    refine iSup₂_le fun R' hR' => iSup_le fun hne => ?_
    refine le_iSup₂_of_le R' hR' (le_iSup_of_le hne ?_)
    rintro _ ⟨c', -, rfl⟩
    exact c'.2
  have hZsplit : Z = centerIn A ⊔ Z' := iSup_mem_eq_sup_iSup_ne D centerIn hAD
  have hcommZ' : Commutes (centerIn A) Z' := fun a ha z hz =>
    hYAcomm a (hcenterA a ha).1 z (hZ'YA hz)
  obtain ⟨c, hc, z', hz', hcz⟩ := exists_mul_of_mem_sup_of_commutes hcommZ' (hZsplit ▸ huZ)
  have hucen : ∀ t ∈ A, u * t = t * u := by
    intro t ht
    rw [hcz]
    calc c * z' * t = c * (z' * t) := by rw [mul_assoc]
      _ = c * (t * z') := by rw [(hYAcomm t ht z' (hZ'YA hz')).symm]
      _ = (c * t) * z' := by rw [mul_assoc]
      _ = (t * c) * z' := by rw [(hcenterA c hc).2 t ht]
      _ = t * (c * z') := by rw [mul_assoc]
  have hsq := hAquat.sq_eq_one_of_central huA hucen
  have hdvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  rw [huord] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

end CFSG.ClassicalInvolution.Asc77
