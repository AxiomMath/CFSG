module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_15Abs
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Center

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem center_of_pair (h : Stage1Pair G z S q L₁ L₂) {w : CentralizerBar z} (hw : w ∈ L₁ ⊔ L₂)
    (h1 : ∀ x ∈ L₁, w * x = x * w) (h2 : ∀ x ∈ L₂, w * x = x * w) : w ∈ L₁ ⊓ L₂ := by
  have hP := PairShape.of_stage1Pair h
  obtain ⟨a, ha, b, hb, hab⟩ := CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute hP.comm hw
  have ha1 : ∀ l ∈ L₁, a * l = l * a := by
    intro l hl
    have e : l * a * b = a * l * b := by
      calc l * a * b = l * (a * b) := by group
        _ = l * w := by rw [hab]
        _ = w * l := (h1 l hl).symm
        _ = a * b * l := by rw [hab]
        _ = a * (b * l) := by group
        _ = a * (l * b) := by rw [(hP.comm l hl b hb).symm]
        _ = a * l * b := by group
    exact (mul_right_cancel e).symm
  have hb2 : ∀ l ∈ L₂, b * l = l * b := by
    intro l hl
    have e : a * (b * l) = a * (l * b) := by
      calc a * (b * l) = a * b * l := by group
        _ = w * l := by rw [hab]
        _ = l * w := (h2 l hl)
        _ = l * (a * b) := by rw [hab]
        _ = (l * a) * b := by group
        _ = (a * l) * b := by rw [← hP.comm a ha l hl]
        _ = a * (l * b) := by group
    exact mul_left_cancel e
  have hinf : Nat.card ↥(L₁ ⊓ L₂) = 2 := h.prod.2.2
  have hZ : ∀ {A B : Subgroup (CentralizerBar z)}, HasSL2Model ↥A (fun r => r = q) →
      Nat.card ↥(A ⊓ B) = 2 → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      ∀ x ∈ A, (∀ l ∈ A, x * l = l * x) → x ∈ B := by
    intro A B hA hcard hcomm x hx hxc
    have hle : (A ⊓ B).subgroupOf A ≤ center ↥A := by
      intro t ht
      rw [Subgroup.mem_center_iff]
      intro g
      have htB : (t : CentralizerBar z) ∈ B := (Subgroup.mem_subgroupOf.mp ht).2
      exact Subtype.ext (hcomm g g.2 t htB)
    have hc1 : Nat.card ((A ⊓ B).subgroupOf A) = 2 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv).trans hcard
    have hc2 := CFSG.GH74.GLS.Stage2.Final.L26.card_center_le_two_of_hasSL2Model hA
    have heq : (A ⊓ B).subgroupOf A = center ↥A := Subgroup.eq_of_le_of_card_ge hle (by omega)
    have hxc' : (⟨x, hx⟩ : ↥A) ∈ center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hxc g g.2).symm
    rw [← heq] at hxc'
    exact (Subgroup.mem_subgroupOf.mp hxc').2
  have haL₂ : a ∈ L₂ := hZ h.sl₁ hinf hP.comm a ha ha1
  have hbL₁ : b ∈ L₁ := by
    have hinf' : Nat.card ↥(L₂ ⊓ L₁) = 2 := by rw [inf_comm]; exact hinf
    exact hZ h.sl₂ hinf' (fun x hx y hy => (hP.comm y hy x hx).symm) b hb hb2
  rw [hab]
  exact Subgroup.mul_mem _ ⟨ha, haL₂⟩ ⟨hbL₁, hb⟩


theorem mem_sup_of_centralizes {Q : Type} [Group Q] [Finite Q] {L₁ L₂ : Subgroup Q} (h : PairShape L₁ L₂) {q : Q}
    (h1 : ∀ x ∈ L₁, q * x = x * q) (h2 : ∀ x ∈ L₂, q * x = x * q) : q ∈ L₁ ⊔ L₂ := by
  have hcent : q ∈ centralizer (generalizedFitting Q : Set Q) := by
    rw [h.fitting, Subgroup.mem_centralizer_iff]
    intro x hx
    have hle : L₁ ⊔ L₂ ≤ centralizer ({q} : Set Q) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact (h1 a ha).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact (h2 a ha).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  exact h.fitting ▸ centralizer_generalizedFitting_le Q hcent

theorem bar_eq_of_fix {z : G} {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}
    (h : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hz2 : z * z = 1) (hz1' : z ≠ 1) {y : G} (hyC : y ∈ Cen z)
    (hy2 : y * y = 1) (hsw : cj (toBar z ⟨y, hyC⟩) L₁ = L₂) {x : G} (hxC : x ∈ Cen z)
    (hxfix : cj (toBar z ⟨x, hxC⟩) L₁ = L₁)
    (hxI : x ∈ centralizer (Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) : Set G)) :
    toBar z ⟨x, hxC⟩ = 1 ∨ toBar z ⟨x, hxC⟩ = toBar z ⟨z, mem_Cen_self z⟩ := by
  have hP := PairShape.of_stage1Pair h
  set π := toBar z with hπ
  set xb : CentralizerBar z := π ⟨x, hxC⟩ with hxb
  set yb : CentralizerBar z := π ⟨y, hyC⟩ with hyb
  have hs2 : yb * yb = 1 := by
    rw [hyb, ← map_mul]
    have : (⟨y, hyC⟩ : ↥(Cen z)) * ⟨y, hyC⟩ = 1 := Subtype.ext hy2
    rw [this, map_one]
  have hmemcj : ∀ {K : Subgroup (CentralizerBar z)} {r : CentralizerBar z}, ∀ a ∈ K, r * a * r⁻¹ ∈ cj r K := by
    intro K r a ha
    rw [mem_cj]
    have e : r⁻¹ * (r * a * r⁻¹) * r = a := by group
    rw [e]; exact ha
  have hs₁ : ∀ a ∈ L₁, yb * a * yb⁻¹ ∈ L₂ := fun a ha => hsw ▸ hmemcj a ha
  have hsw' : cj yb L₂ = L₁ := hP.cj_swap hsw
  have hs₂ : ∀ b ∈ L₂, yb * b * yb⁻¹ ∈ L₁ := fun b hb => hsw' ▸ hmemcj b hb
  have hx₁ : ∀ a ∈ L₁, xb * a * xb⁻¹ ∈ L₁ := fun a ha => hxfix ▸ hmemcj a ha
  have hx₂ : ∀ b ∈ L₂, xb * b * xb⁻¹ ∈ L₂ := fun b hb => (hP.cj_fix hxfix) ▸ hmemcj b hb
  obtain ⟨hk₁, hk₂⟩ := hK.swap y hyC hsw
  set I := Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) with hI
  have hI0 : ∀ a ∈ K₁, a * (y * a * y⁻¹) ∈ I := fun a ha =>
    diag_le_layer hK.quasi₁ hK.comm hy2 hk₁ hk₂ ⟨⟨a, ha⟩, rfl⟩
  have hIbar : ∀ a ∈ L₁, a * (yb * a * yb⁻¹) ∈ barOf z I := by
    intro a ha
    rw [← hK.bar₁] at ha
    obtain ⟨k', hk', rfl⟩ := ha
    have hk : (k' : G) ∈ K₁ := hk'
    have hmem : k' * (⟨y, hyC⟩ * k' * ⟨y, hyC⟩⁻¹) ∈ I.subgroupOf (Cen z) := by
      show (k' : G) * (y * (k' : G) * y⁻¹) ∈ I
      exact hI0 _ hk
    refine ⟨_, hmem, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  have hxIbar : ∀ i ∈ barOf z I, xb * i = i * xb := by
    rintro _ ⟨i', hi', rfl⟩
    have hi : (i' : G) ∈ I := hi'
    have := Subgroup.mem_centralizer_iff.mp hxI _ hi
    rw [hxb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext this.symm
  have hperf₁ : ⁅L₁, L₁⁆ = L₁ := Subgroup.isPerfect_iff.mp hP.c₁.1.1
  obtain ⟨hc₁, hc₂⟩ := diag_centralizes hperf₁ hP.comm hs2 hs₁ hs₂ hIbar hx₁ hx₂ hxIbar
  have hxmem := center_of_pair h (mem_sup_of_centralizes hP hc₁ hc₂) hc₁ hc₂
  have hzc := Subgroup.mem_center_iff.mp (toBar_z_mem_center z)
  have hzmem := center_of_pair h (w := π ⟨z, mem_Cen_self z⟩)
    (mem_sup_of_centralizes hP (fun a _ => (hzc a).symm) (fun a _ => (hzc a).symm))
    (fun a _ => (hzc a).symm) (fun a _ => (hzc a).symm)
  have hz1 : π ⟨z, mem_Cen_self z⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := by
      have := (QuotientGroup.eq_one_iff (N := pPrimeCore 2 ↥(Cen z)) (⟨z, mem_Cen_self z⟩ : ↥(Cen z))).mp h1
      exact this
    have hodd : Odd (orderOf (⟨z, mem_Cen_self z⟩ : ↥(Cen z))) := by
      have hd : orderOf (⟨⟨z, mem_Cen_self z⟩, h2⟩ : ↥(pPrimeCore 2 ↥(Cen z))) ∣
          Nat.card ↥(pPrimeCore 2 ↥(Cen z)) := orderOf_dvd_natCard _
      have hodd' : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
        Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
      have h1' := Odd.of_dvd_nat hodd' hd
      rwa [Subgroup.orderOf_mk] at h1'
    have hord : orderOf (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact orderOf_eq_prime (by rw [sq]; exact hz2) hz1'
    rw [hord] at hodd
    exact absurd hodd (by decide)
  by_cases hx1 : xb = 1
  · exact Or.inl hx1
  · right
    have hcard : Nat.card ↥(L₁ ⊓ L₂) = 2 := h.prod.2.2
    obtain ⟨t, ht, huniq⟩ := (Nat.card_eq_two_iff' (⟨1, (L₁ ⊓ L₂).one_mem⟩ : ↥(L₁ ⊓ L₂))).mp hcard
    have h1 := huniq ⟨xb, hxmem⟩ (fun e => hx1 (congrArg Subtype.val e))
    have h2 := huniq ⟨π ⟨z, mem_Cen_self z⟩, hzmem⟩ (fun e => hz1 (congrArg Subtype.val e))
    exact congrArg Subtype.val (h1.trans h2.symm)


theorem eq_one_of_odd_of_two_power {X : Type} [Group X] {a : X} {k : ℕ} (ha : a ^ (2 ^ k) = 1)
    (hodd : Odd (orderOf a)) : a = 1 := by
  have hdvd : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one ha
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra hne
    have : Even (orderOf a) := by
      rw [hj]; exact (Nat.even_pow.mpr ⟨even_two, hne⟩)
    exact (Nat.not_even_iff_odd.mpr hodd) this
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

theorem odd_orderOf_of_mem_pPrimeCore' {X : Type} [Group X] [Finite X] {a : X} (ha : a ∈ pPrimeCore 2 X) :
    Odd (orderOf a) := by
  have hd : orderOf (⟨a, ha⟩ : ↥(pPrimeCore 2 X)) ∣ Nat.card ↥(pPrimeCore 2 X) := orderOf_dvd_natCard _
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 X)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X))
  have h1 := Odd.of_dvd_nat hodd hd
  rwa [Subgroup.orderOf_mk] at h1

theorem fix_eq_of_two_power {z : G} {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    {K₁ K₂ : Subgroup G} (h : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hz2 : z * z = 1)
    (hz1' : z ≠ 1) {y : G} (hyC : y ∈ Cen z) (hy2 : y * y = 1) (hsw : cj (toBar z ⟨y, hyC⟩) L₁ = L₂) {x : G}
    (hxC : x ∈ Cen z) (hxfix : cj (toBar z ⟨x, hxC⟩) L₁ = L₁)
    (hxI : x ∈ centralizer (Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) : Set G)) {k : ℕ}
    (hxk : x ^ (2 ^ k) = 1) : x = 1 ∨ x = z := by
  rcases bar_eq_of_fix h hK hz2 hz1' hyC hy2 hsw hxC hxfix hxI with h1 | h1
  · left
    have hmem : (⟨x, hxC⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).mp h1
    have hodd := odd_orderOf_of_mem_pPrimeCore' hmem
    rw [Subgroup.orderOf_mk] at hodd
    exact eq_one_of_odd_of_two_power hxk hodd
  · right
    have hmem : (⟨x, hxC⟩ : ↥(Cen z))⁻¹ * ⟨z, mem_Cen_self z⟩ ∈ pPrimeCore 2 ↥(Cen z) :=
      QuotientGroup.eq.mp h1
    have hodd := odd_orderOf_of_mem_pPrimeCore' hmem
    have hcomm : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hodd' : Odd (orderOf (x⁻¹ * z)) := by
      have : orderOf ((⟨x, hxC⟩ : ↥(Cen z))⁻¹ * ⟨z, mem_Cen_self z⟩) = orderOf (x⁻¹ * z) := by
        rw [← Subgroup.orderOf_coe]; rfl
      rwa [this] at hodd
    have hpow : (x⁻¹ * z) ^ (2 ^ (k + 1)) = 1 := by
      have hc : Commute x⁻¹ z := (Commute.inv_left (show Commute x z from hcomm))
      rw [hc.mul_pow]
      have h1' : (x⁻¹) ^ (2 ^ (k + 1)) = 1 := by
        rw [inv_pow, pow_succ, pow_mul, hxk]; simp
      have h2' : z ^ (2 ^ (k + 1)) = 1 := by
        rw [pow_succ, mul_comm, pow_mul, show z ^ 2 = 1 by rw [sq]; exact hz2, one_pow]
      rw [h1', h2', one_mul]
    have := eq_one_of_odd_of_two_power hpow hodd'
    exact (inv_mul_eq_one.mp this)


theorem hA_of {z : G} {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}
    (h : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) (hz2 : z * z = 1) (hz1' : z ≠ 1) {y : G}
    (hyC : y ∈ Cen z) (hy2 : y * y = 1) (hsw : cj (toBar z ⟨y, hyC⟩) L₁ = L₂)
    (X : Subgroup G) (hXH : X ≤ centralizer (Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) : Set G))
    (hXz : ∀ x ∈ X, z * x = x * z) (hXp : IsPGroup 2 X) (hyX : y ∈ X) :
    ∀ x ∈ X, x = 1 ∨ x = z ∨ x = y ∨ x = y * z := by
  have hP := PairShape.of_stage1Pair h
  have hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hXp ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hzy : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
  intro x hx
  have hxC : x ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr (hXz x hx).symm
  obtain ⟨k, hk⟩ := hpow x hx
  by_cases hfix : cj (toBar z ⟨x, hxC⟩) L₁ = L₁
  · rcases fix_eq_of_two_power h hK hz2 hz1' hyC hy2 hsw hxC hfix (hXH hx) hk with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have hxy : x * y ∈ X := X.mul_mem hx hyX
    have hxyC : x * y ∈ Cen z := (Cen z).mul_mem hxC hyC
    have hcjx : cj (toBar z ⟨x, hxC⟩) L₁ = L₂ := (hP.cj_cases _).resolve_left hfix
    have hfix' : cj (toBar z ⟨x * y, hxyC⟩) L₁ = L₁ := by
      have e : toBar z ⟨x * y, hxyC⟩ = toBar z ⟨x, hxC⟩ * toBar z ⟨y, hyC⟩ := by
        rw [← map_mul]; rfl
      rw [e]
      refine hP.cj_mul_swap hfix (fun e' => hP.ne ?_)
      exact (e'.symm.trans hsw)
    obtain ⟨k', hk'⟩ := hpow (x * y) hxy
    rcases fix_eq_of_two_power h hK hz2 hz1' hyC hy2 hsw hxyC hfix' (hXH hxy) hk' with h1 | h1
    · right; right; left
      have : x = (x * y) * y⁻¹ := by group
      rw [this, h1, one_mul]
      exact inv_eq_of_mul_eq_one_right hy2
    · right; right; right
      have : x = (x * y) * y⁻¹ := by group
      rw [this, h1, inv_eq_of_mul_eq_one_right hy2, ← hzy]


omit [Finite G] in
theorem OddCore_norm (z : G) {c : G} (hc : c ∈ Cen z) {b : G} (hb : b ∈ OddCore z) : c * b * c⁻¹ ∈ OddCore z :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_map_subtype (Cen z) (pPrimeCore 2 ↥(Cen z)) hc) b).mp hb

omit [Finite G] in
theorem OddCore_le_Cen (z : G) : OddCore z ≤ Cen z := Subgroup.map_subtype_le _

theorem hO_of {z : G} {K₁ K₂ : Subgroup G} {L₁ L₂ : Subgroup (CentralizerBar z)} (hK : CompData z K₁ K₂ L₁ L₂)
    {y : G} (hyC : y ∈ Cen z) (h12c : ∀ f ∈ F20 z, y * f * y⁻¹ = f⁻¹) (hne : OddCore z ≠ ⊥)
    (N : Subgroup G)
    (hNn : ∀ h ∈ centralizer (Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) : Set G), ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hNp : IsPGroup 2 N) (huN : y * z ∈ N) : False := by
  set I := Em ((K₁ ⊔ K₂) ⊓ centralizer ({y} : Set G)) with hI
  have hIL : I ≤ Em (Cen z) := by
    refine (Em_le _).trans (inf_le_left.trans ?_)
    rw [hK.layer]
  have hAH : OddCore z ≤ centralizer (I : Set G) := by
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
    exact (hK.oddcomm a ha i (hIL hi)).symm
  have huC : y * z ∈ Cen z := (Cen z).mul_mem hyC (mem_Cen_self z)
  have hucen : ∀ a ∈ OddCore z, (y * z) * a = a * (y * z) := by
    intro a ha
    have h1 : (y * z) * a * (y * z)⁻¹ ∈ OddCore z := OddCore_norm z huC ha
    have h2 : (y * z) * a * (y * z)⁻¹ * a⁻¹ ∈ OddCore z := (OddCore z).mul_mem h1 ((OddCore z).inv_mem ha)
    have h3 : (y * z) * a * (y * z)⁻¹ * a⁻¹ ∈ N := by
      have hau : a * (y * z) * a⁻¹ ∈ N := hNn a (hAH ha) _ huN
      have e : (y * z) * a * (y * z)⁻¹ * a⁻¹ = (y * z) * (a * (y * z) * a⁻¹)⁻¹ := by group
      rw [e]
      exact N.mul_mem huN (N.inv_mem hau)
    obtain ⟨k, hk⟩ := hNp ⟨_, h3⟩
    have hk' : ((y * z) * a * (y * z)⁻¹ * a⁻¹) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hodd := odd_orderOf_of_mem_pPrimeCoreOf h2
    have h4 := eq_one_of_odd_of_two_power hk' hodd
    calc (y * z) * a = ((y * z) * a * (y * z)⁻¹ * a⁻¹) * (a * (y * z)) := by group
      _ = a * (y * z) := by rw [h4, one_mul]
  have hF1 : ∀ f ∈ F20 z, f = 1 := by
    intro f hf
    have hfA : f ∈ OddCore z := Subgroup.map_subtype_le _ hf
    have hfC : f ∈ Cen z := OddCore_le_Cen z hfA
    have hzf : z * f = f * z := (Subgroup.mem_centralizer_singleton_iff.mp hfC).symm
    have h1 := hucen f hfA
    have h2 := h12c f hf
    have h3 : f = f⁻¹ := by
      calc f = (y * z) * f * (y * z)⁻¹ := by
            rw [h1]; group
        _ = y * (z * f * z⁻¹) * y⁻¹ := by group
        _ = y * f * y⁻¹ := by rw [hzf]; group
        _ = f⁻¹ := h2
    have hff : f ^ (2 ^ 1) = 1 := by
      rw [pow_one, sq]
      exact mul_eq_one_iff_eq_inv.mpr h3
    exact eq_one_of_odd_of_two_power hff (odd_orderOf_of_mem_pPrimeCoreOf hfA)
  apply hne
  have hodd : Odd (Nat.card ↥(OddCore z)) := by
    have h1 : Nat.card ↥(OddCore z) = Nat.card ↥(pPrimeCore 2 ↥(Cen z)) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ (Cen z).subtype (Cen z).subtype_injective).symm.toEquiv
    rw [h1]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
  have hsolv : Group.IsSolvable ↥(OddCore z) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hbot : fittingSubgroup ↥(OddCore z) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : G) ∈ F20 z := ⟨x, hx, rfl⟩
    have h1 := hF1 _ this
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hcard := (fitting_eq_bot_iff_card_eq_one_of_solvable ↥(OddCore z)).mp hbot
  exact Subgroup.card_eq_one.mp hcard

end Center

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Final.Thm6.L20

theorem lemma20_15_thm
    (h12 : Lemma20_12) : Lemma20_15 := by
  intro G _ _ z k S M h hMC hpsp g hS h14
  subst hMC
  have hctx : Stage2Ctx G z k S := h.ctx.ctx17.ctx
  have hSC : S ≤ Cen z := hctx.S_le_Cen
  have hz2 : z * z = 1 := by
    have := hctx.orderOf_z
    calc z * z = z ^ 2 := (sq z).symm
      _ = 1 := by rw [← this]; exact pow_orderOf_eq_one z
  have hz1' : z ≠ 1 := by
    intro h1
    have := hctx.orderOf_z
    rw [h1, orderOf_one] at this
    omega
  have h4a : pLayerOf 2 (Cen z) = Em (Cen z) := h.ctx.thm4.1
  obtain ⟨q, L₁, L₂, hpair, hswap⟩ := hS.swap
  obtain ⟨q', hk, L₁', L₂', hpsp4⟩ := hpsp
  have hT : TypeCl z k S := Or.inr ⟨q', hk, L₁', L₂', hpsp4⟩
  obtain ⟨-, h12b, h12c⟩ := h12 G z k S (Cen z) h rfl hT
  obtain ⟨K₁, K₂, hK⟩ := exists_compData hpair h4a
  have hyS : zc z g ∈ S := hS.y_mem
  have hyC : zc z g ∈ Cen z := hSC hyS
  have hy2 : zc z g * zc z g = 1 := by
    calc zc z g * zc z g = g⁻¹ * (z * z) * g := by simp only [zc]; group
      _ = 1 := by rw [hz2]; group
  have hyconj : IsConj z (zc z g) := isConj_iff.mpr ⟨g⁻¹, by simp [zc]⟩
  have hy1 : zc z g ≠ 1 := by
    intro h1
    apply hz1'
    have : z = g * zc z g * g⁻¹ := by simp only [zc]; group
    rw [this, h1]; group
  obtain ⟨hyC', hsw⟩ := swaps_cj hswap
  have hyne : zc z g ≠ z := by
    intro hyz
    have hcen : toBar z ⟨zc z g, hyC'⟩ ∈ center (CentralizerBar z) := by
      have := toBar_z_mem_center z
      have e : (⟨zc z g, hyC'⟩ : ↥(Cen z)) = ⟨z, mem_Cen_self z⟩ := Subtype.ext hyz
      rwa [e]
    have hfix : cj (toBar z ⟨zc z g, hyC'⟩) L₁ = L₁ :=
      cj_eq_iff.mpr (Subgroup.center_le_normalizer (L₁ : Set (CentralizerBar z)) hcen)
    exact hpair.ne (hfix.symm.trans hsw)
  have hzy : z * zc z g = zc z g * z := (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm
  have hIy : Iy z g = Em ((K₁ ⊔ K₂) ⊓ centralizer ({zc z g} : Set G)) := by
    unfold Iy L20; rw [hK.layer]
  have hHy : Hy z g = centralizer (Em ((K₁ ⊔ K₂) ⊓ centralizer ({zc z g} : Set G)) : Set G) := by
    unfold Hy; rw [hIy]
  have hIL : Iy z g ≤ Em (Cen z) := by
    refine (Subgroup.map_subtype_le _).trans ?_
    exact inf_le_left
  have hzH : z ∈ Hy z g := by
    rw [Hy]
    refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.map_subtype_le _ (hIL hi) : i ∈ Cen z))
  have hyH : zc z g ∈ Hy z g := by
    rw [Hy]
    refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
    have hiy : i ∈ L20 z ⊓ centralizer ({zc z g} : Set G) := Subgroup.map_subtype_le _ hi
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hiy).2
  have hab : Abs15 (Hy z g) z (zc z g) :=
    { hzH := hzH
      hyH := hyH
      hz2 := hz2
      hy2 := hy2
      hzy := hzy
      hne := hyne.symm
      hz1 := hz1'
      hy1 := hy1
      hu := hS.u_not
      hA := fun X hXH hXz hXp hyX => hA_of hpair hK hz2 hz1' hyC' hy2 hsw X (hHy ▸ hXH) hXz hXp hyX
      hF := fun e he => (h14 e he).2.2
      hO := fun N hNH hNn hNp huN =>
        hO_of hK hyC' (fun f hf => h12c _ hyS hyconj ⟨q, L₁, L₂, hpair, hswap⟩ f hf) h.odd_ne N
          (fun hh hhH n hn => hNn hh (hHy ▸ hhH) n hn) hNp huN }
  have hmain := hab.main
  exact ⟨hmain.2, hmain.1⟩

end CFSG.GH74.GLS.Stage2.Final.Thm6
