module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78UnitaryLocal

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {G : Type} [Group G] [Finite G]

section Lift

variable {L P : Subgroup G}

theorem mem_of_mk_mem (hZ : Odd (Nat.card (center L))) (hP : IsSylowOf 2 P L)
    {R : Sylow 2 (rankTwoQuot L)} (hR : (sylowProj hP.le).range = R) {x : G} (hxL : x ∈ L)
    (hxR : QuotientGroup.mk' (center L) ⟨x, hxL⟩ ∈ (R : Subgroup (rankTwoQuot L))) {n : ℕ}
    (hxn : x ^ 2 ^ n = 1) : x ∈ P := by
  rw [← hR] at hxR
  obtain ⟨p, hp⟩ := hxR
  rw [sylowProj_apply] at hp
  have hz : (⟨p, hP.le p.2⟩ : L)⁻¹ * ⟨x, hxL⟩ ∈ center L := QuotientGroup.eq.mp hp
  set z : L := (⟨p, hP.le p.2⟩ : L)⁻¹ * ⟨x, hxL⟩ with hzdef
  have hxz : x = p * (z : G) := by
    rw [hzdef]
    simp
  have hpz : (p : G) * z = z * p := by
    have := mem_center_iff.mp hz ⟨p, hP.le p.2⟩
    exact congrArg Subtype.val this
  have hzn : (z : G) ^ 2 ^ n = ((p : G) ^ 2 ^ n)⁻¹ := by
    rw [hxz, Commute.mul_pow hpz] at hxn
    exact eq_inv_of_mul_eq_one_right hxn
  have hbot : P.subgroupOf L ⊓ center L = ⊥ :=
    AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ (center L)
      (hP.isPGroup.comap_subtype.to_inf_left) hZ inf_le_right
  have hzP : z ^ 2 ^ n ∈ P.subgroupOf L ⊓ center L := by
    refine mem_inf.mpr ⟨?_, pow_mem hz _⟩
    show ((z ^ 2 ^ n : L) : G) ∈ P
    rw [coe_pow, hzn]
    exact inv_mem (pow_mem p.2 _)
  rw [hbot, mem_bot] at hzP
  have hz1 : (⟨z, hz⟩ : center L) = 1 :=
    eq_one_of_pow_two_pow_eq_one_of_odd hZ (Subtype.ext (by simpa using hzP))
  have hz1' : (z : G) = 1 := congrArg (fun w : center L => ((w : L) : G)) hz1
  rw [hxz, hz1', mul_one]
  exact p.2

omit [Finite G] in
theorem mem_normalizer_of_conj_mem {P : Subgroup G} {l : G}
    (h : ∀ p ∈ P, l * p * l⁻¹ ∈ P) (h' : ∀ p ∈ P, l⁻¹ * p * l ∈ P) :
    l ∈ normalizer (P : Set G) := mem_normalizer_iff.mpr fun p =>
  ⟨h p, fun hp => by simpa [mul_assoc] using h' _ hp⟩

theorem mem_normalizer_of_commute (hZ : Odd (Nat.card (center L))) (hP : IsSylowOf 2 P L)
    {q k : ℕ} (hB : fusionBenderBorel (rankTwoQuot L) q k) {a : G}
    (ha : a ∈ P ⊓ centralizer (P : Set G)) (ha1 : a ≠ 1) {l : G} (hlL : l ∈ L)
    (hla : l * a = a * l) : l ∈ normalizer (P : Set G) := by
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hinj := sylowProj_injective hZ hP.isPGroup hP.le
  set π := QuotientGroup.mk' (center L) with hπ
  have haL : a ∈ L := hP.le (mem_inf.mp ha).1
  have haR : π ⟨a, haL⟩ ∈ (R : Subgroup (rankTwoQuot L)) := by
    rw [← hR]
    exact ⟨⟨a, (mem_inf.mp ha).1⟩, rfl⟩
  have ha1' : π ⟨a, haL⟩ ≠ 1 := by
    intro h
    apply ha1
    have h1 : sylowProj hP.le ⟨a, (mem_inf.mp ha).1⟩ = sylowProj hP.le 1 := by
      rw [map_one]
      exact h
    exact congrArg Subtype.val (hinj h1)
  have hlR : π ⟨l, hlL⟩ ∈ normalizer ((R : Subgroup (rankTwoQuot L)) : Set (rankTwoQuot L)) := by
    by_contra hn
    have hne : π ⟨l, hlL⟩ • R ≠ R := fun h => hn (Sylow.smul_eq_iff_mem_normalizer.mp h)
    apply ha1'
    refine Omega.eq_one_of_mem_of_mem (hB R).1 hne haR ?_
    rw [Omega.mem_conj_smul_iff]
    have h1 : (⟨l, hlL⟩ : L)⁻¹ * ⟨a, haL⟩ * ⟨l, hlL⟩ = ⟨a, haL⟩ := by
      apply Subtype.ext
      show l⁻¹ * a * l = a
      rw [mul_assoc, ← hla, inv_mul_cancel_left]
    rw [← map_inv, ← map_mul, ← map_mul, h1]
    exact haR
  have hconj : ∀ m : L, π m ∈ normalizer ((R : Subgroup (rankTwoQuot L)) : Set (rankTwoQuot L)) →
      ∀ p ∈ P, (m : G) * p * (m : G)⁻¹ ∈ P := by
    intro m hm p hp
    have hpL : p ∈ L := hP.le hp
    have hmem : (m : G) * p * (m : G)⁻¹ ∈ L := mul_mem (mul_mem m.2 hpL) (inv_mem m.2)
    obtain ⟨n, hn⟩ := hP.isPGroup ⟨p, hp⟩
    have hpn : p ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine mem_of_mk_mem hZ hP hR hmem ?_ (n := n) ?_
    · have h1 : (⟨(m : G) * p * (m : G)⁻¹, hmem⟩ : L) = m * ⟨p, hpL⟩ * m⁻¹ := rfl
      rw [h1, map_mul, map_mul, map_inv]
      have hpR : π ⟨p, hpL⟩ ∈ (R : Subgroup (rankTwoQuot L)) := by
        rw [← hR]
        exact ⟨⟨p, hp⟩, rfl⟩
      exact (mem_normalizer_iff.mp hm _).mp hpR
    · rw [show ((m : G) * p * (m : G)⁻¹) ^ 2 ^ n = (m : G) * p ^ 2 ^ n * (m : G)⁻¹ by
        rw [conj_pow], hpn, mul_one, mul_inv_cancel]
  refine mem_normalizer_of_conj_mem (hconj ⟨l, hlL⟩ hlR) ?_
  have h1 := hconj ⟨l, hlL⟩⁻¹ (by rw [map_inv]; exact inv_mem hlR)
  simpa using h1

omit [Finite G] in
theorem mk_mem_of_normalizer (hP : IsSylowOf 2 P L) {R : Sylow 2 (rankTwoQuot L)}
    (hR : (sylowProj hP.le).range = R) {l : G} (hlL : l ∈ L) (hlN : l ∈ normalizer (P : Set G))
    {n : ℕ} (hln : QuotientGroup.mk' (center L) ⟨l, hlL⟩ ^ 2 ^ n = 1) :
    QuotientGroup.mk' (center L) ⟨l, hlL⟩ ∈ (R : Subgroup (rankTwoQuot L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center L) with hπ
  have hRmem : ∀ r ∈ (R : Subgroup (rankTwoQuot L)), ∃ p : P, sylowProj hP.le p = r :=
    fun r hr => by rw [← hR] at hr; exact hr
  have hconjR : ∀ m : L, (m : G) ∈ normalizer (P : Set G) → ∀ r ∈ (R : Subgroup (rankTwoQuot L)),
      π m * r * (π m)⁻¹ ∈ (R : Subgroup (rankTwoQuot L)) := by
    intro m hm r hr
    obtain ⟨p, rfl⟩ := hRmem r hr
    have hp' : (m : G) * p * (m : G)⁻¹ ∈ P := (mem_normalizer_iff.mp hm p).mp p.2
    rw [← hR]
    refine ⟨⟨_, hp'⟩, ?_⟩
    rw [sylowProj_apply, sylowProj_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hlR : π ⟨l, hlL⟩ ∈ normalizer ((R : Subgroup (rankTwoQuot L)) : Set (rankTwoQuot L)) := by
    refine mem_normalizer_of_conj_mem (hconjR ⟨l, hlL⟩ hlN) ?_
    intro r hr
    have h1 := hconjR ⟨l, hlL⟩⁻¹ (by simpa using inv_mem hlN) r hr
    simpa using h1
  have hzp : IsPGroup 2 (zpowers (π ⟨l, hlL⟩)) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨n, Subtype.ext ?_⟩
    show (π ⟨l, hlL⟩ ^ k) ^ 2 ^ n = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hln, one_zpow]
  have hsup := hzp.to_sup_of_normal_right' R.isPGroup' (zpowers_le.mpr hlR)
  have heq := R.is_maximal' hsup le_sup_right
  rw [← heq]
  exact mem_sup_left (mem_zpowers _)

theorem commute_of_normalizer (hP : IsSylowOf 2 P L) {l : G} (hlL : l ∈ L)
    (hlN : l ∈ normalizer (P : Set G)) {n : ℕ}
    (hln : QuotientGroup.mk' (center L) ⟨l, hlL⟩ ^ 2 ^ n = 1) :
    ∀ a ∈ P ⊓ centralizer (P : Set G), l * a = a * l := by
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hlR := mk_mem_of_normalizer hP hR hlL hlN hln
  rw [← hR] at hlR
  obtain ⟨p, hp⟩ := hlR
  rw [sylowProj_apply] at hp
  have hz : (⟨p, hP.le p.2⟩ : L)⁻¹ * ⟨l, hlL⟩ ∈ center L := QuotientGroup.eq.mp hp
  intro a ha
  have haL : a ∈ L := hP.le (mem_inf.mp ha).1
  have h1 : ((⟨p, hP.le p.2⟩ : L)⁻¹ * ⟨l, hlL⟩) * ⟨a, haL⟩ =
      ⟨a, haL⟩ * ((⟨p, hP.le p.2⟩ : L)⁻¹ * ⟨l, hlL⟩) := (mem_center_iff.mp hz ⟨a, haL⟩).symm
  have h2 : ((p : G)⁻¹ * l) * a = a * ((p : G)⁻¹ * l) := congrArg Subtype.val h1
  have h3 : (p : G) * a = a * p := mem_centralizer_iff.mp (mem_inf.mp ha).2 p p.2
  calc l * a = p * (((p : G)⁻¹ * l) * a) := by group
    _ = p * (a * ((p : G)⁻¹ * l)) := by rw [h2]
    _ = (p * a) * ((p : G)⁻¹ * l) := by group
    _ = (a * p) * ((p : G)⁻¹ * l) := by rw [h3]
    _ = a * l := by group

theorem exists_torus (hZ : Odd (Nat.card (center L))) (hP : IsSylowOf 2 P L) {q k : ℕ}
    (hB : fusionBenderBorel (rankTwoQuot L) q k) :
    ∃ y ∈ L ⊓ normalizer (P : Set G), Odd (orderOf y) ∧
      (∀ a ∈ P ⊓ centralizer (P : Set G), ∀ b ∈ P ⊓ centralizer (P : Set G), a ≠ 1 → b ≠ 1 →
        ∃ m : ℕ, (y ^ m)⁻¹ * a * y ^ m = b) ∧
      ∀ n ∈ L ⊓ normalizer (P : Set G), ∃ m : ℕ,
        ∀ a ∈ P ⊓ centralizer (P : Set G), n * a * n⁻¹ = y ^ m * a * (y ^ m)⁻¹ := by
  classical
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  have hinj := sylowProj_injective hZ hP.isPGroup hP.le
  have hcen := mem_center_iff_sylowProj hZ hP hR
  set π := QuotientGroup.mk' (center L) with hπ
  obtain ⟨hSE, ⟨D, hDcyc, hDodd, -, hND⟩, -, -, -⟩ := hB R
  obtain ⟨-, hZ2, -, -⟩ := benderBorel_sylowCenter hB R
  have hDN : D ≤ normalizer ((R : Subgroup (rankTwoQuot L)) : Set (rankTwoQuot L)) :=
    hND ▸ le_sup_right
  have : IsCyclic D := hDcyc
  obtain ⟨⟨d₀, hd₀D⟩, hgen⟩ := IsCyclic.exists_generator (α := D)
  have hpowD : ∀ d ∈ D, ∃ m : ℕ, d₀ ^ m = d := by
    intro d hd
    have h1 := hgen ⟨d, hd⟩
    rw [← mem_powers_iff_mem_zpowers] at h1
    obtain ⟨m, hm⟩ := h1
    exact ⟨m, congrArg Subtype.val hm⟩
  obtain ⟨ℓ, hℓ⟩ := QuotientGroup.mk'_surjective (center L) d₀
  set y : G := (ℓ : G) with hydef
  have hπR : ∀ x (hx : x ∈ P), π ⟨x, hP.le hx⟩ ∈ (R : Subgroup (rankTwoQuot L)) := by
    intro x hx
    rw [← hR]
    exact ⟨⟨x, hx⟩, rfl⟩
  have hact : ∀ m ∈ normalizer ((R : Subgroup (rankTwoQuot L)) : Set (rankTwoQuot L)), ∃ d ∈ D,
      ∀ z ∈ sylowCenter (R : Subgroup (rankTwoQuot L)), m * z * m⁻¹ = d * z * d⁻¹ := by
    intro m hm
    rw [← hND, sup_comm] at hm
    obtain ⟨d, hd, r, hr, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hDN hm
    refine ⟨d, hd, fun z hz => ?_⟩
    have hrz : r * z * r⁻¹ = z := by
      rw [(mem_sylowCenter.mp hz).2 r hr, mul_inv_cancel_right]
    calc d * r * z * (d * r)⁻¹ = d * (r * z * r⁻¹) * d⁻¹ := by group
      _ = d * z * d⁻¹ := by rw [hrz]
  have hyL : y ∈ L := ℓ.2
  have hyπ : π ⟨y, hyL⟩ = d₀ := hℓ
  have hyN : y ∈ normalizer (P : Set G) := by
    have hconj : ∀ m : L, π m ∈ D → ∀ p ∈ P, (m : G) * p * (m : G)⁻¹ ∈ P := by
      intro m hm p hp
      have hpL : p ∈ L := hP.le hp
      have hmem : (m : G) * p * (m : G)⁻¹ ∈ L := mul_mem (mul_mem m.2 hpL) (inv_mem m.2)
      obtain ⟨n, hn⟩ := hP.isPGroup ⟨p, hp⟩
      have hpn : p ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      refine mem_of_mk_mem hZ hP hR hmem ?_ (n := n) ?_
      · have h1 : (⟨(m : G) * p * (m : G)⁻¹, hmem⟩ : L) = m * ⟨p, hpL⟩ * m⁻¹ := rfl
        rw [h1, map_mul, map_mul, map_inv]
        exact (mem_normalizer_iff.mp (hDN hm) _).mp (hπR p hp)
      · rw [show ((m : G) * p * (m : G)⁻¹) ^ 2 ^ n = (m : G) * p ^ 2 ^ n * (m : G)⁻¹ by
          rw [conj_pow], hpn, mul_one, mul_inv_cancel]
    refine mem_normalizer_of_conj_mem (hconj ℓ (by rw [hℓ]; exact hd₀D)) ?_
    have h1 := hconj ℓ⁻¹ (by rw [map_inv, hℓ]; exact inv_mem hd₀D)
    simpa using h1
  have hyodd : Odd (orderOf y) := by
    have hd₀odd : Odd (orderOf d₀) := by
      have := orderOf_dvd_natCard (⟨d₀, hd₀D⟩ : D)
      rw [Subgroup.orderOf_mk] at this
      exact hDodd.of_dvd_nat this
    have h1 : ℓ ^ orderOf d₀ ∈ center L := by
      rw [← QuotientGroup.eq_one_iff (N := center L), ← QuotientGroup.mk'_apply, map_pow, hℓ,
        pow_orderOf_eq_one]
    have h2 : ℓ ^ (orderOf d₀ * Nat.card (center L)) = 1 := by
      rw [pow_mul]
      have := pow_card_eq_one' (G := center L) (x := ⟨_, h1⟩)
      exact congrArg Subtype.val this
    have h3 : orderOf ℓ ∣ orderOf d₀ * Nat.card (center L) := orderOf_dvd_of_pow_eq_one h2
    rw [hydef, Subgroup.orderOf_coe]
    exact (hd₀odd.mul hZ).of_dvd_nat h3
  refine ⟨y, mem_inf.mpr ⟨hyL, hyN⟩, hyodd, ?_, ?_⟩
  ·
    intro a ha b hb ha1 hb1
    have haP := (mem_inf.mp ha).1
    have hbP := (mem_inf.mp hb).1
    have haZ := (hcen ⟨a, haP⟩).mp ha
    have hbZ := (hcen ⟨b, hbP⟩).mp hb
    have hne : ∀ x (hx : x ∈ P), x ≠ 1 → sylowProj hP.le ⟨x, hx⟩ ≠ 1 := by
      intro x hx hx1 h
      apply hx1
      have h1 : sylowProj hP.le ⟨x, hx⟩ = sylowProj hP.le 1 := by rw [map_one]; exact h
      exact congrArg Subtype.val (hinj h1)
    obtain ⟨m, hm, hmab⟩ := normalizer_transitive_center hSE hZ2 haZ hbZ
      (hne a haP ha1) (hne b hbP hb1)
    obtain ⟨d, hd, hdz⟩ := hact m hm
    have hmz : ∀ z ∈ sylowCenter (R : Subgroup (rankTwoQuot L)), m⁻¹ * z * m = d⁻¹ * z * d := by
      intro z hz
      have hw := conj_mem_sylowCenter hm hz
      have h1 := hdz _ hw
      calc m⁻¹ * z * m = d⁻¹ * (d * (m⁻¹ * z * m) * d⁻¹) * d := by group
        _ = d⁻¹ * (m * (m⁻¹ * z * m) * m⁻¹) * d := by rw [h1]
        _ = d⁻¹ * z * d := by group
    obtain ⟨j, rfl⟩ := hpowD d hd
    refine ⟨j, ?_⟩
    have hmem : (y ^ j)⁻¹ * a * y ^ j ∈ P := by
      have h1 := (mem_normalizer_iff.mp (pow_mem (inv_mem hyN) j) a).mp haP
      simpa [mul_assoc] using h1
    have key : sylowProj hP.le ⟨_, hmem⟩ = (d₀ ^ j)⁻¹ * sylowProj hP.le ⟨a, haP⟩ * d₀ ^ j := by
      rw [sylowProj_apply, sylowProj_apply]
      have h2 : (⟨(y ^ j)⁻¹ * a * y ^ j, hP.le hmem⟩ : L) =
          (⟨y, hyL⟩ ^ j)⁻¹ * ⟨a, hP.le haP⟩ * ⟨y, hyL⟩ ^ j := by
        apply Subtype.ext
        simp
      rw [h2, map_mul, map_mul, map_inv, map_pow]
      congr 2
      rw [← hyπ]
    have h3 : sylowProj hP.le ⟨_, hmem⟩ = sylowProj hP.le ⟨b, hbP⟩ := by
      rw [key, ← hmz _ haZ, hmab]
    exact congrArg Subtype.val (hinj h3)
  ·
    intro n hn
    obtain ⟨hnL, hnN⟩ := mem_inf.mp hn
    have hnR : π ⟨n, hnL⟩ ∈ normalizer ((R : Subgroup (rankTwoQuot L)) : Set (rankTwoQuot L)) := by
      refine mem_normalizer_of_conj_mem ?_ ?_
      · intro r hr
        rw [← hR] at hr ⊢
        obtain ⟨p, rfl⟩ := hr
        exact ⟨⟨n * p * n⁻¹, (mem_normalizer_iff.mp hnN p).mp p.2⟩, by
          rw [sylowProj_apply, sylowProj_apply, ← map_inv, ← map_mul, ← map_mul]; rfl⟩
      · intro r hr
        rw [← hR] at hr ⊢
        obtain ⟨p, rfl⟩ := hr
        have hp' : n⁻¹ * p * n ∈ P := by
          simpa using (mem_normalizer_iff.mp (inv_mem hnN) p).mp p.2
        exact ⟨⟨n⁻¹ * p * n, hp'⟩, by
          rw [sylowProj_apply, sylowProj_apply, ← map_inv, ← map_mul, ← map_mul]; rfl⟩
    obtain ⟨d, hd, hdz⟩ := hact _ hnR
    obtain ⟨j, rfl⟩ := hpowD d hd
    refine ⟨j, fun a ha => ?_⟩
    have haP := (mem_inf.mp ha).1
    have hm1 : n * a * n⁻¹ ∈ P := (mem_normalizer_iff.mp hnN a).mp haP
    have hm2 : y ^ j * a * (y ^ j)⁻¹ ∈ P := (mem_normalizer_iff.mp (pow_mem hyN j) a).mp haP
    have h1 : sylowProj hP.le ⟨n * a * n⁻¹, hm1⟩ =
        sylowProj hP.le ⟨y ^ j * a * (y ^ j)⁻¹, hm2⟩ := by
      rw [sylowProj_apply, sylowProj_apply]
      have e1 : (⟨n * a * n⁻¹, hP.le hm1⟩ : L) = ⟨n, hnL⟩ * ⟨a, hP.le haP⟩ * ⟨n, hnL⟩⁻¹ := rfl
      have e2 : (⟨y ^ j * a * (y ^ j)⁻¹, hP.le hm2⟩ : L) =
          ⟨y, hyL⟩ ^ j * ⟨a, hP.le haP⟩ * (⟨y, hyL⟩ ^ j)⁻¹ := by
        apply Subtype.ext
        simp
      rw [e1, e2, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, map_pow, hyπ]
      exact hdz _ ((hcen ⟨a, haP⟩).mp ha)
    exact congrArg Subtype.val (hinj h1)

theorem eq_of_mem_of_mem (hZ : Odd (Nat.card (center L))) {P₁ P₂ : Subgroup G}
    (h₁ : IsSylowOf 2 P₁ L) (h₂ : IsSylowOf 2 P₂ L) {q k : ℕ}
    (hB : fusionBenderBorel (rankTwoQuot L) q k) {a : G} (ha₁ : a ∈ P₁) (ha₂ : a ∈ P₂)
    (ha : a ≠ 1) : P₁ = P₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R₁, hR₁⟩ := exists_sylow_range h₁
  obtain ⟨R₂, hR₂⟩ := exists_sylow_range h₂
  have hinj := sylowProj_injective hZ h₁.isPGroup h₁.le
  have haL : a ∈ L := h₁.le ha₁
  have hπ₁ : QuotientGroup.mk' (center L) ⟨a, haL⟩ ∈ (R₁ : Subgroup (rankTwoQuot L)) := by
    rw [← hR₁]
    exact ⟨⟨a, ha₁⟩, rfl⟩
  have hπ₂ : QuotientGroup.mk' (center L) ⟨a, haL⟩ ∈ (R₂ : Subgroup (rankTwoQuot L)) := by
    rw [← hR₂]
    exact ⟨⟨a, ha₂⟩, rfl⟩
  have hR : R₂ = R₁ := by
    by_contra hne
    apply ha
    have h1 := Omega.eq_one_of_mem_of_mem (hB R₁).1 hne hπ₁ hπ₂
    have h2 : sylowProj h₁.le ⟨a, ha₁⟩ = sylowProj h₁.le 1 := by rw [map_one]; exact h1
    exact congrArg Subtype.val (hinj h2)
  have hle : P₂ ≤ P₁ := by
    intro x hx
    obtain ⟨n, hn⟩ := h₂.isPGroup ⟨x, hx⟩
    have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine mem_of_mk_mem hZ h₁ hR₁ (h₂.le hx) ?_ hxn
    rw [← hR]
    rw [← hR₂]
    exact ⟨⟨x, hx⟩, rfl⟩
  exact h₂.eq_of_le hle h₁.le h₁.isPGroup

end Lift

end CFSG.ComponentClassification.GMS78
