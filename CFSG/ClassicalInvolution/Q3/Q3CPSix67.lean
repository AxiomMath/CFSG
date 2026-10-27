module

public import CFSG.ClassicalInvolution.Q3.Q3CPLoc26

public section

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem normContradictionGen (hΩ : HypOmegaGen Ω)
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
    exact eq_of_le_of_le hΩ hJ (hΩc w J hJ) hz2 h4 (Subgroup.zpowers_le.mpr hxJ)
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
  set Z : Subgroup G := ⨆ R' ∈ D, Asc77.centerIn R' with hZ
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
  have hcenterA : ∀ c ∈ Asc77.centerIn A, c ∈ A ∧ ∀ t ∈ A, c * t = t * c := by
    rintro _ ⟨c', hc', rfl⟩
    refine ⟨c'.2, fun t ht => ?_⟩
    have := Subgroup.mem_center_iff.mp hc' ⟨t, ht⟩
    exact congrArg Subtype.val this.symm
  set Z' : Subgroup G := ⨆ R' ∈ D, ⨆ (_ : R' ≠ A), Asc77.centerIn R' with hZ'
  have hZ'YA : Z' ≤ YA := by
    refine iSup₂_le fun R' hR' => iSup_le fun hne => ?_
    refine le_iSup₂_of_le R' hR' (le_iSup_of_le hne ?_)
    rintro _ ⟨c', -, rfl⟩
    exact c'.2
  have hZsplit : Z = Asc77.centerIn A ⊔ Z' := iSup_mem_eq_sup_iSup_ne D Asc77.centerIn hAD
  have hcommZ' : Commutes (Asc77.centerIn A) Z' := fun a ha z hz =>
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

theorem claimNotNormalizesGen (h62 : L6_2Gen)
    (hΩ : HypOmegaGen Ω) {K J A B : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hAK : IsSylow2In A K) (hBJ : IsSylow2In B J) (hA : A ∈ RSet Ω) (hB : B ∈ RSet Ω)
    (hKJ : K ≠ J) (hAB : IsPGroup 2 ↥(A ⊔ B)) (hnc : ¬ Commutes A B) {a b : G}
    (ha : IsUniqueInvolution K a) (hb : IsUniqueInvolution J b)
    (hbY : ∀ α ∈ A, ∀ y ∈ B, (b⁻¹ * α⁻¹ * b * α) * y = y * (b⁻¹ * α⁻¹ * b * α)) :
    conjSub b A ≠ A := by
  intro hbA
  have hAq := isQuatSub_of_mem_RSet hΩ hA
  have hBq := isQuatSub_of_mem_RSet hΩ hB
  have hA2 : IsPGroup 2 ↥A := hAK.2.1
  have hB2 : IsPGroup 2 ↥B := hBJ.2.1
  have ha2 : orderOf a = 2 := ConnectedA2.orderOf_eq_two_of_isUniqueInvolution ha
  have hb2 : orderOf b = 2 := ConnectedA2.orderOf_eq_two_of_isUniqueInvolution hb
  have haA : a ∈ A :=
    mem_of_isUniqueInvolution_of_isPGroup ha hAK.1 hA2 (by have := hAq.eight_le; omega)
  have hbB : b ∈ B :=
    mem_of_isUniqueInvolution_of_isPGroup hb hBJ.1 hB2 (by have := hBq.eight_le; omega)
  have hab : a ≠ b := by
    intro hab
    apply hnc
    exact commutes_of_twin_of_isPGroup hΩ hK hJ hKJ ha (hab ▸ hb) hAK.1 hBJ.1 hAB
  have hKJt : K ∉ twinSet Ω J := by
    rintro ⟨-, z, hzJ, hzK⟩
    exact hab ((ha.eq hzK).trans (hb.eq hzJ).symm)
  have hJKt : J ∉ twinSet Ω K := by
    rintro ⟨-, z, hzK, hzJ⟩
    exact hab ((ha.eq hzK).trans (hb.eq hzJ).symm)
  have hnormA : ∀ α ∈ A, b⁻¹ * α⁻¹ * b ∈ A := by
    intro α hα
    have h1 : conjSub b⁻¹ A = A := by
      calc conjSub b⁻¹ A = conjSub b⁻¹ (conjSub b A) := by rw [hbA]
        _ = A := conjSub_inv_conjSub b A
    have h2 : b⁻¹ * α⁻¹ * b⁻¹⁻¹ ∈ conjSub b⁻¹ A := conj_mem_conjSub (A.inv_mem hα)
    rw [h1, inv_inv] at h2
    exact h2
  have hcA : ∀ α ∈ A, b⁻¹ * α⁻¹ * b * α ∈ A := fun α hα => A.mul_mem (hnormA α hα) hα
  by_cases hall : ∀ α ∈ A, b⁻¹ * α⁻¹ * b * α = 1
  ·
    have hAc : A ≤ Subgroup.centralizer ({b} : Set G) := by
      intro α hα
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : α⁻¹ * b * α = b := by
        calc α⁻¹ * b * α = b * (b⁻¹ * α⁻¹ * b * α) := by group
          _ = b := by rw [hall α hα, mul_one]
      have h2 : b * α = α * b := by
        calc b * α = α * (α⁻¹ * b * α) := by group
          _ = α * b := by rw [h1]
      exact h2.symm
    have hSyl : IsSylow2In A (K ⊓ Subgroup.centralizer ({b} : Set G)) :=
      ⟨le_inf hAK.1 hAc, hA2, fun V hV hV2 hAV => hAK.2.2 V (hV.trans inf_le_left) hV2 hAV⟩
    rcases h62 G Ω hΩ J hJ b hb K hK hKJt a ha A hSyl haA with h | h | h | h
    · have h8 := hAq.eight_le
      rw [h.1, Nat.card_zpowers, ha2] at h8
      omega
    · have h8 := hAq.eight_le
      rw [h.1, Nat.card_zpowers, ha2] at h8
      omega
    · obtain ⟨R, -, J', -, -, -, hcyc, -, -⟩ := exists_data_of_mem_USet hΩ h.1
      obtain ⟨x, hx, y, hy, hxy⟩ := hAq.exists_not_commute
      exact hxy (commute_of_isCyclic hcyc hx hy)
    · exact hnc (commutes_of_commutator_le_oddCoreOf hBJ.1 h.2 hAB)
  ·
    push Not at hall
    obtain ⟨α, hα, hne⟩ := hall
    set c : G := b⁻¹ * α⁻¹ * b * α with hc
    have hcA : c ∈ A := hcA α hα
    have hzcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
    have hzc2 : IsPGroup 2 ↥(Subgroup.zpowers c) := hA2.to_le hzcA
    have hcard : 2 ≤ Nat.card (Subgroup.zpowers c) := by
      rw [Nat.card_zpowers]
      have h1 : orderOf c ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
      have h0 : 0 < orderOf c := orderOf_pos c
      omega
    have haz : a ∈ Subgroup.zpowers c :=
      mem_of_isUniqueInvolution_of_isPGroup ha (hzcA.trans hAK.1) hzc2 hcard
    have hBc : B ≤ Subgroup.centralizer ({a} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haz
      have hcy : Commute c y := hbY α hα y hy
      have : Commute a y := hk ▸ Commute.zpow_left hcy k
      exact this.symm.eq
    have hSyl : IsSylow2In B (J ⊓ Subgroup.centralizer ({a} : Set G)) :=
      ⟨le_inf hBJ.1 hBc, hB2, fun V hV hV2 hBV => hBJ.2.2 V (hV.trans inf_le_left) hV2 hBV⟩
    rcases h62 G Ω hΩ K hK a ha J hJ hJKt b hb B hSyl hbB with h | h | h | h
    · have h8 := hBq.eight_le
      rw [h.1, Nat.card_zpowers, hb2] at h8
      omega
    · have h8 := hBq.eight_le
      rw [h.1, Nat.card_zpowers, hb2] at h8
      omega
    · obtain ⟨R, -, J', -, -, -, hcyc, -, -⟩ := exists_data_of_mem_USet hΩ h.1
      obtain ⟨x, hx, y, hy, hxy⟩ := hBq.exists_not_commute
      exact hxy (commute_of_isCyclic hcyc hx hy)
    · exact hnc (commutes_of_commutator_le_oddCoreOf hAK.1 h.2 (sup_comm B A ▸ hAB)).symm

theorem orbitCommutesGen (hΩ : HypOmegaGen Ω) {n : ℕ}
    (ih : ∀ m < n, ∀ S' : Subgroup G, Nat.card S' = m → IsPGroup 2 S' →
      ∀ Δ : Set (Subgroup G), (∀ A ∈ Δ, A ≤ S') → (∀ A ∈ Δ, ∀ s ∈ S', conjSub s A ∈ Δ) →
        Δ ⊆ RSet Ω → ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commutes A B)
    {S C : Subgroup G} (hSn : Nat.card S = n) (hS : IsPGroup 2 S) (hC : C < S)
    (hCR : C ∈ RSet Ω) :
    ∀ C₁ ∈ {C' : Subgroup G | ∃ s ∈ S, C' = conjSub s C},
      ∀ C₂ ∈ {C' : Subgroup G | ∃ s ∈ S, C' = conjSub s C}, C₁ ≠ C₂ → Commutes C₁ C₂ := by
  obtain ⟨hXS, hXlt⟩ := card_biSup_conj_lt hS hC
  refine ih _ (hSn ▸ hXlt) (⨆ s ∈ S, conjSub s C) rfl (hS.to_le hXS)
    {C' : Subgroup G | ∃ s ∈ S, C' = conjSub s C} ?_ ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact le_iSup₂_of_le s hs le_rfl
  · rintro _ ⟨s, hs, rfl⟩ x hx
    exact ⟨x * s, S.mul_mem (hXS hx) hs, conjSub_mul x s C ▸ rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact RSet.conj hΩ.conjInvariant hCR s

theorem l66iMainGen (h62 : L6_2Gen) (hΩ : HypOmegaGen Ω) :
    ∀ n : ℕ, ∀ S : Subgroup G, Nat.card S = n → IsPGroup 2 S → ∀ Δ : Set (Subgroup G),
      (∀ A ∈ Δ, A ≤ S) → (∀ A ∈ Δ, ∀ s ∈ S, conjSub s A ∈ Δ) → Δ ⊆ RSet Ω →
        ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commutes A B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hSn hS Δ hΔS hΔinv hΔR A hA B hB hne
  by_contra hnc
  have hAR := hΔR hA
  have hBR := hΔR hB
  obtain ⟨K, hK, hAK⟩ := exists_isSylow2In_of_mem_RSet hAR
  obtain ⟨J, hJ, hBJ⟩ := exists_isSylow2In_of_mem_RSet hBR
  have hAq := isQuatSub_of_mem_RSet hΩ hAR
  have hBq := isQuatSub_of_mem_RSet hΩ hBR
  have hAS : A ≤ S := hΔS A hA
  have hBS : B ≤ S := hΔS B hB
  have hS' : ∀ P : Subgroup G, IsPGroup 2 ↥(P ⊓ S) := fun P => hS.to_inf_right
  have hKJ : K ≠ J := by
    rintro rfl
    have h1 : K ⊓ S = A := hAK.eq_of_le (hS' K) inf_le_left (le_inf hAK.1 hAS)
    have h2 : K ⊓ S = B := hBJ.eq_of_le (hS' K) inf_le_left (le_inf hBJ.1 hBS)
    exact hne (h1.symm.trans h2)
  obtain ⟨a, ha⟩ := exists_uniqueInvolution hΩ hK
  obtain ⟨b, hb⟩ := exists_uniqueInvolution hΩ hJ
  have hbB : b ∈ B :=
    mem_of_isUniqueInvolution_of_isPGroup hb hBJ.1 hBJ.2.1 (by have := hBq.eight_le; omega)
  have hAltS : A < S := by
    refine lt_of_le_of_ne hAS ?_
    intro hAeq
    have hBA : B ≤ A := hAeq ▸ hBS
    exact hKJ (eq_of_le_of_le hΩ hK hJ hBJ.2.1 (by have := hBq.eight_le; omega)
      (hBA.trans hAK.1) hBJ.1)
  have hBltS : B < S := by
    refine lt_of_le_of_ne hBS ?_
    intro hBeq
    have hAB : A ≤ B := hBeq ▸ hAS
    exact hKJ (eq_of_le_of_le hΩ hK hJ hAK.2.1 (by have := hAq.eight_le; omega)
      hAK.1 (hAB.trans hBJ.1))
  have hXcomm := orbitCommutesGen hΩ ih hSn hS hAltS hAR
  have hYcomm := orbitCommutesGen hΩ ih hSn hS hBltS hBR
  set Y : Subgroup G := ⨆ s ∈ S, conjSub s B with hY
  have hBY : B ≤ Y := le_iSup₂_of_le (1 : G) S.one_mem (conjSub_one B).ge
  have hYinv : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := fun s hs y hy =>
    conjSub_biSup_conj_le hs (conj_mem_conjSub hy)
  have hbcY : ∀ y ∈ Y, b * y = y * b := by
    have hle : Y ≤ Subgroup.centralizer ({b} : Set G) := by
      refine iSup₂_le fun s hs y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hsB : conjSub s B = B
      · have hyB : y ∈ B := hsB ▸ hy
        exact (hb.commute_of_mem (hBJ.1 hyB)).symm
      · exact (hYcomm B ⟨1, S.one_mem, (conjSub_one B).symm⟩ (conjSub s B) ⟨s, hs, rfl⟩
          (Ne.symm hsB) b hbB y hy).symm
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hbY : ∀ α ∈ A, ∀ y ∈ B, (b⁻¹ * α⁻¹ * b * α) * y = y * (b⁻¹ * α⁻¹ * b * α) := by
    intro α hα y hy
    have hyY : y ∈ Y := hBY hy
    have ht : α * y * α⁻¹ ∈ Y := hYinv α (hAS hα) y hyY
    have hbt : b * (α * y * α⁻¹) = (α * y * α⁻¹) * b := hbcY _ ht
    have hby : b⁻¹ * y = y * b⁻¹ := by
      have := hbcY y hyY
      calc b⁻¹ * y = b⁻¹ * (y * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * y) * b⁻¹ := by rw [this]
        _ = y * b⁻¹ := by group
    calc (b⁻¹ * α⁻¹ * b * α) * y = b⁻¹ * α⁻¹ * (b * (α * y * α⁻¹)) * α := by group
      _ = b⁻¹ * α⁻¹ * ((α * y * α⁻¹) * b) * α := by rw [hbt]
      _ = (b⁻¹ * y) * (α⁻¹ * b * α) := by group
      _ = (y * b⁻¹) * (α⁻¹ * b * α) := by rw [hby]
      _ = y * (b⁻¹ * α⁻¹ * b * α) := by group
  have hbn : conjSub b A ≠ A :=
    claimNotNormalizesGen h62 hΩ hK hJ hAK hBJ hAR hBR hKJ
      (hS.to_le (sup_le hAS hBS)) hnc ha hb hbY
  have hreg : ∀ g ∈ B, conjSub g A = A → g = 1 := by
    intro g hg hgA
    by_contra hg1
    have hzgB : Subgroup.zpowers g ≤ B := Subgroup.zpowers_le.mpr hg
    have hz2 : IsPGroup 2 ↥(Subgroup.zpowers g) := hBJ.2.1.to_le hzgB
    have hcard : 2 ≤ Nat.card (Subgroup.zpowers g) := by
      rw [Nat.card_zpowers]
      have h1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
      have h0 : 0 < orderOf g := orderOf_pos g
      omega
    have hbg : b ∈ Subgroup.zpowers g :=
      mem_of_isUniqueInvolution_of_isPGroup hb (hzgB.trans hBJ.1) hz2 hcard
    have hgN : g ∈ Subgroup.normalizer (A : Set G) := mem_normalizer_iff_conjSub_eq.mpr hgA
    have hbN : b ∈ Subgroup.normalizer (A : Set G) := (Subgroup.zpowers_le.mpr hgN) hbg
    exact hbn (mem_normalizer_iff_conjSub_eq.mp hbN)
  have hinj : ∀ g ∈ B, ∀ h ∈ B, conjSub g A = conjSub h A → g = h := by
    intro g hg h hh hgh
    have h1 : conjSub (h⁻¹ * g) A = A := by
      rw [conjSub_mul, hgh, conjSub_inv_conjSub]
    have := hreg (h⁻¹ * g) (B.mul_mem (B.inv_mem hh) hg) h1
    exact (inv_mul_eq_one.mp this).symm
  set X : Subgroup G := ⨆ s ∈ S, conjSub s A with hX
  have hXS : X ≤ S := (card_biSup_conj_lt hS hAltS).1
  have hXinv : ∀ s ∈ S, ∀ g ∈ X, s⁻¹ * g * s ∈ X := by
    intro s hs g hg
    have h2 := conjSub_biSup_conj_le (S := S) (A := A) (S.inv_mem hs) (conj_mem_conjSub hg)
    simpa using h2
  have hXN : ∀ g ∈ X, conjSub g A = A := by
    have hle : X ≤ Subgroup.normalizer (A : Set G) := by
      refine iSup₂_le fun s hs g hg => ?_
      by_cases hsA : conjSub s A = A
      · exact Subgroup.le_normalizer (hsA ▸ hg)
      · have hc : Commutes (conjSub s A) A :=
          hXcomm _ ⟨s, hs, rfl⟩ A ⟨1, S.one_mem, (conjSub_one A).symm⟩ hsA
        exact mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hg hc)
    intro g hg
    exact mem_normalizer_iff_conjSub_eq.mp (hle hg)
  have hAX : ∀ g ∈ B, conjSub g A ≤ X := fun g hg => le_iSup₂_of_le g (hBS hg) le_rfl
  have hcommorbit : ∀ g ∈ B, ∀ h ∈ B, g ≠ h → Commutes (conjSub g A) (conjSub h A) := by
    intro g hg h hh hgh
    exact hXcomm _ ⟨g, hBS hg, rfl⟩ _ ⟨h, hBS hh, rfl⟩ (fun e => hgh (hinj g hg h hh e))
  obtain ⟨x, hxB, hxord⟩ := hBq.exists_orderOf_four
  obtain ⟨u, huA, huord⟩ := hAq.exists_orderOf_four
  exact normContradictionGen hΩ hJ hBJ hS hBS hXS hAq hBq hXinv hXN hAX hinj hcommorbit hxB hxord
    huA huord

theorem l67Gen : L67Gen := by
  intro G _ _ Ω hΩ S R hR R' hR' hRS hR'S hne
  refine l66iMainGen l6_2Gen hΩ _ (S : Subgroup G) rfl S.isPGroup'
    {A | A ∈ RSet Ω ∧ A ≤ (S : Subgroup G)} (fun A hA => hA.2) ?_ (fun A hA => hA.1)
    R ⟨hR, hRS⟩ R' ⟨hR', hR'S⟩ hne
  intro A hA s hs
  refine ⟨RSet.conj hΩ.conjInvariant hA.1 s, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  have h1 : s⁻¹ * x * s ∈ (S : Subgroup G) := hA.2 hx
  have h2 : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
  rw [h2]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs h1) (Subgroup.inv_mem _ hs)

end CFSG.ClassicalInvolution.Q3.Q3CP
