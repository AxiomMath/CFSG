module

public import CFSG.Goldschmidt.Steps.G3b35Setup
public import CFSG.Goldschmidt.Steps.G3b35Basic
public import CFSG.Walter.Bender1970.S2.AutJR
public import CFSG.Walter.Bender1970.S2.AutOdd
public import CFSG.Walter.Bender1970.S2.Cyclic

public section

namespace CFSG.Goldschmidt.G3b

open CFSG.Open CFSG.Walter CFSG.GorensteinWalter
open scoped MatrixGroups

section TypeII

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def sylowOfMax {L A : Subgroup G} (hAL : A ≤ L) (hA2 : IsPGroup 2 A)
    (hAmax : ∀ P : Subgroup G, P ≤ L → IsPGroup 2 P → A ≤ P → P = A) : Sylow 2 L where
  toSubgroup := A.subgroupOf L
  isPGroup' := hA2.comap_subtype
  is_maximal' := fun {Q} hQ hAQ => by
    have hQL : Q.map L.subtype ≤ L := Subgroup.map_subtype_le Q
    have hAQ' : A ≤ Q.map L.subtype := fun x hx =>
      ⟨⟨x, hAL hx⟩, hAQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have h := hAmax _ hQL (hQ.map L.subtype) hAQ'
    rw [← h, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]

omit [Finite G] in
theorem coe_sylowOfMax {L A : Subgroup G} (hAL : A ≤ L) (hA2 : IsPGroup 2 A)
    (hAmax : ∀ P : Subgroup G, P ≤ L → IsPGroup 2 P → A ≤ P → P = A) :
    ((sylowOfMax hAL hA2 hAmax : Sylow 2 L) : Subgroup L) = A.subgroupOf L := rfl

omit [Finite G] in
theorem isPGroup_two_of_sq {A : Subgroup G} (hA : ∀ x ∈ A, x ^ 2 = 1) : IsPGroup 2 A :=
  fun x => ⟨1, Subtype.ext (by simpa using hA x x.2)⟩

theorem orderOf_le_natCard (x : G) : orderOf x ≤ Nat.card G :=
  Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard x)

theorem G35_one_L2
    {L A Y : Subgroup G} [L.Normal] (hLq : CFSG.Open.IsQuasisimple L)
    {p f : ℕ} [Fact p.Prime] (e : L ⧸ Subgroup.center L ≃* PSL(2, GaloisField p f))
    (hp : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    (hAL : A ≤ L) (hAab : IsMulCommutative A) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hAmax : ∀ P : Subgroup G, P ≤ L → IsPGroup 2 P → A ≤ P → P = A)
    (hYA : Y ≤ Subgroup.centralizer (A : Set G)) :
    Odd (((L ⊔ Subgroup.centralizer (L : Set G)).subgroupOf Y).index) ∧
      ∃ y ∈ Y, Y ≤ Subgroup.zpowers y ⊔ (L ⊔ Subgroup.centralizer (L : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2' : IsPGroup 2 A := isPGroup_two_of_sq hA2
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set AB : Sylow 2 (L ⧸ Subgroup.center L) :=
    (sylowOfMax hAL hA2' hAmax).mapSurjective hπs with hAB
  have hABmem : ∀ x ∈ (AB : Subgroup (L ⧸ Subgroup.center L)),
      ∃ a : G, ∃ ha : a ∈ A, x = π ⟨a, hAL ha⟩ := by
    intro x hx
    rw [hAB, Sylow.coe_mapSurjective, coe_sylowOfMax] at hx
    obtain ⟨⟨a, haL⟩, ha, rfl⟩ := hx
    exact ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
  obtain ⟨hcomm, ⟨Γ, hΓ, hΓmem⟩, -⟩ := mulAut_fix_props_of_mulEquiv e hp hf h5 h8 AB
  set Φ := conjQuot L with hΦ
  have hfix : ∀ y ∈ Y, ∀ x ∈ (AB : Subgroup (L ⧸ Subgroup.center L)), Φ y x = x := by
    intro y hy x hx
    obtain ⟨a, ha, rfl⟩ := hABmem x hx
    rw [hΦ, hπ, QuotientGroup.mk'_apply, conjQuot_mk]
    congr 2
    rw [← Subgroup.mem_centralizer_iff.mp (hYA hy) a ha, mul_inv_cancel_right]
  have hfixpow : ∀ y ∈ Y, ∀ k : ℕ, ∀ x ∈ (AB : Subgroup (L ⧸ Subgroup.center L)),
      (Φ y ^ k) x = x := by
    intro y hy k x hx
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hfix y hy x hx, ih]
  set N := Nat.card G with hNdef
  let ψ : Y →* MulAut (L ⧸ Subgroup.center L) :=
    { toFun := fun y => Φ y ^ 2 ^ N
      map_one' := by simp
      map_mul' := fun y z => by
        simp only [Subgroup.coe_mul, map_mul]
        exact Commute.mul_pow (hcomm _ _ (hfix y y.2) (hfix z z.2)) _ }
  have hψ : ∀ y : Y, ψ y = Φ y ^ 2 ^ N := fun _ => rfl
  have hodd : ∀ y : Y, Odd (orderOf (ψ y)) := by
    intro y
    rw [hψ]
    exact odd_orderOf_pow_two_pow (orderOf_pos _)
      ((Nat.le_of_dvd (orderOf_pos _) (orderOf_map_dvd Φ y)).trans (orderOf_le_natCard _))
  have hψΓ : ψ.range ≤ Γ := by
    rintro _ ⟨y, rfl⟩
    exact hΓmem _ (hodd y) (hfixpow y y.2 _)
  have hcyc : IsCyclic ψ.range := by
    have : IsCyclic Γ := hΓ
    exact Subgroup.isCyclic_of_le hψΓ
  refine cyclic_quotient_of_hom Y _ ψ hcyc hodd fun y hy => ?_
  apply mem_of_pow_two_pow_mem _ N
  · apply le_sup_right (a := L)
    rw [← conjQuot_eq_one_iff L hLq.1, map_pow]
    exact hy
  · intro k hk
    exact mem_sup_centralizer_of_isPGroup_two hLq hAL hAab hA2' hAmax hk
      ((Subgroup.centralizer (A : Set G)).pow_mem (hYA y.2) k)

theorem le_centralizer_sup_inf_of_coprime {L A Y : Subgroup G} [L.Normal] (hAL : A ≤ L)
    (hA2 : IsPGroup 2 A) (hAN : A ≤ Subgroup.normalizer (Y : Set G)) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hYr : IsPGroup r Y) :
    Y ≤ (Subgroup.centralizer (A : Set G) ⊓ Y) ⊔ (L ⊓ Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φA : A →* MulAut Y := Y.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  let : MulDistribMulAction A Y := MulDistribMulAction.compHom Y φA
  have hsmul : ∀ (b : A) (y : Y), ((b • y : Y) : G) = (b : G) * y * (b : G)⁻¹ := fun _ _ => rfl
  have hsolv : Group.IsSolvable Y := by
    have := hYr.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Y) :=
    IsPGroup.coprime_card_of_ne 2 r (Ne.symm hr2) A Y hA2 hYr
  have htop := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := A) (G := Y) hsolv hcop
  have hfixle : CFSG.fixedPointSubgroup A Y ≤ (Subgroup.centralizer (A : Set G)).subgroupOf Y := by
    intro y hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro b hb
    have h := congrArg Subtype.val (hy ⟨b, hb⟩)
    rw [hsmul] at h
    calc b * (y : G) = ((b : G) * y * (b : G)⁻¹) * b := by group
      _ = y * b := by rw [h]
  have hcomle : CFSG.commutatorAction A Y ≤ L.subgroupOf Y := by
    rw [CFSG.commutatorAction, CFSG.commutatorSubgroup, Subgroup.closure_le]
    rintro _ ⟨b, h, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv, hsmul]
    have h1 : (h : G)⁻¹ * ((b : G) * h * (b : G)⁻¹) =
        ((h : G)⁻¹ * b * (h : G)⁻¹⁻¹) * (b : G)⁻¹ := by group
    rw [h1]
    exact L.mul_mem ((inferInstance : L.Normal).conj_mem _ (hAL b.2) _) (L.inv_mem (hAL b.2))
  intro y hy
  have hmem : (⟨y, hy⟩ : Y) ∈ (Subgroup.centralizer (A : Set G)).subgroupOf Y ⊔ L.subgroupOf Y :=
    (sup_le_sup hfixle hcomle) (htop ▸ Subgroup.mem_top _)
  have h := Subgroup.mem_map_of_mem Y.subtype hmem
  rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype] at h

theorem G35_two_L2
    {L A Y : Subgroup G} [L.Normal] (hLq : CFSG.Open.IsQuasisimple L)
    (hZ : Odd (Nat.card (Subgroup.center L)))
    {p f : ℕ} [Fact p.Prime] (e : L ⧸ Subgroup.center L ≃* PSL(2, GaloisField p f))
    (hp : Odd p) (hf : 0 < f) (h5 : 5 ≤ p ^ f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5)
    (hAL : A ≤ L) (hAab : IsMulCommutative A) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hAmax : ∀ P : Subgroup G, P ≤ L → IsPGroup 2 P → A ≤ P → P = A)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hNY : L ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Y : Set G))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hYr : IsPGroup r Y) :
    Y ≤ L ⊔ Subgroup.centralizer (L : Set G) ∧
      ∃ y ∈ Y, Y ≤ Subgroup.zpowers y ⊔ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hLq.2
  have hA2' : IsPGroup 2 A := isPGroup_two_of_sq hA2
  set C := Subgroup.centralizer (L : Set G) with hC
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set AB : Sylow 2 (L ⧸ Subgroup.center L) :=
    (sylowOfMax hAL hA2' hAmax).mapSurjective hπs with hAB
  have hABmem : ∀ x ∈ (AB : Subgroup (L ⧸ Subgroup.center L)),
      ∃ b : G, ∃ hb : b ∈ A, x = π ⟨b, hAL hb⟩ := by
    intro x hx
    rw [hAB, Sylow.coe_mapSurjective, coe_sylowOfMax] at hx
    obtain ⟨⟨b, hbL⟩, hb, rfl⟩ := hx
    exact ⟨b, Subgroup.mem_subgroupOf.mp hb, rfl⟩
  set Φ := conjQuot L with hΦ
  have haL : a ∈ L := hAL haA
  have haa : a * a = 1 := by rw [← pow_two]; exact hA2 a haA
  set ℓ := π ⟨a, haL⟩ with hℓ
  have hℓAB : ℓ ∈ (AB : Subgroup (L ⧸ Subgroup.center L)) := by
    rw [hAB, Sylow.coe_mapSurjective, coe_sylowOfMax]
    exact ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
  have hℓ2 : orderOf ℓ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hℓ, ← map_pow]
      have : (⟨a, haL⟩ : L) ^ 2 = 1 := Subtype.ext (by simpa using hA2 a haA)
      rw [this, map_one]
    · intro h
      rw [hℓ, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      apply ha1
      have := eq_one_of_mem_center_of_pow hZ h (k := 1) (Subtype.ext (by simpa using hA2 a haA))
      exact congrArg Subtype.val this
  have hcardL : 2 ∣ Nat.card (L ⧸ Subgroup.center L) := hℓ2 ▸ orderOf_dvd_natCard ℓ
  have hL2 : IsTypeL2Odd (L ⧸ Subgroup.center L) := by
    unfold IsTypeL2Odd
    exact ⟨p, f, inferInstance, hp, hf, h5, h8, ⟨e⟩⟩
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := by
    refine le_trans (fun x hx => Subgroup.mem_inf.mpr ⟨hAL hx, ?_⟩) hNY
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨a, haA⟩)
  have hdecomp := le_centralizer_sup_inf_of_coprime hAL hA2' hAN hr2 hYr
  have hYord : ∀ y ∈ Y, ∃ n : ℕ, orderOf y ∣ r ^ n := by
    intro y hy
    obtain ⟨n, hn⟩ := hYr ⟨y, hy⟩
    exact ⟨n, orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)⟩
  have hYA : Subgroup.centralizer (A : Set G) ⊓ Y ≤ C := by
    rintro y ⟨hyA, hyY⟩
    rw [hC, ← conjQuot_eq_one_iff L hLq.1]
    by_contra hy1
    obtain ⟨n, hn⟩ := hYord y hyY
    have hodd : Odd (orderOf (Φ y)) :=
      Odd.of_dvd_nat (hr.odd_of_ne_two hr2).pow ((orderOf_map_dvd Φ y).trans hn)
    obtain ⟨k, r', hr', hr'2, hk⟩ := exists_pow_orderOf_eq_prime hy1 hodd
    have hr'r : r = r' := by
      have h1 : r' ∣ r ^ n := by
        rw [← hk]
        exact ((orderOf_pow_dvd (x := Φ y) k).trans (orderOf_map_dvd Φ y)).trans hn
      exact ((Nat.prime_dvd_prime_iff_eq hr' hr).mp (hr'.dvd_of_dvd_pow h1)).symm
    subst hr'r
    have hΦk : Φ y ^ k = Φ (y ^ k) := (map_pow _ _ _).symm
    refine IsTypeL2Odd.false_of_mulAut hL2 hr' hr'2 (Φ y ^ k) hk AB ?_ hℓAB hℓ2 ?_
    · intro x hx
      obtain ⟨b, hb, rfl⟩ := hABmem x hx
      rw [hΦk, hΦ, hπ, QuotientGroup.mk'_apply, conjQuot_mk]
      congr 2
      rw [← Subgroup.mem_centralizer_iff.mp
        ((Subgroup.centralizer (A : Set G)).pow_mem hyA k) b hb, mul_inv_cancel_right]
    · intro x hx hcop
      obtain ⟨x', rfl⟩ := hπs x
      have hx'a : (x' : G) ∈ Subgroup.centralizer ({a} : Set G) :=
        mem_centralizer_of_mk_mem_centralizer L hZ haL haa x' hx
      have hx'N : (x' : G) ∈ Subgroup.normalizer (Y : Set G) := hNY ⟨x'.2, hx'a⟩
      rw [hΦk, hΦ, hπ, QuotientGroup.mk'_apply, conjQuot_mk] at hcop ⊢
      set w : L := x'⁻¹ * ⟨y ^ k * x' * (y ^ k)⁻¹,
        (inferInstance : L.Normal).conj_mem x' x'.2 (y ^ k)⟩ with hw
      have hwY : (w : G) ∈ Y := by
        have h1 : (w : G) = ((x' : G)⁻¹ * y ^ k * (x' : G)⁻¹⁻¹) * (y ^ k)⁻¹ := by
          rw [hw]
          simp [mul_assoc]
        rw [h1]
        exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx'N) _).mp
          (Y.pow_mem hyY k)) (Y.inv_mem (Y.pow_mem hyY k))
      obtain ⟨m, hm⟩ := hYord _ hwY
      have hπw : orderOf (π w) ∣ r ^ m := by
        refine (orderOf_map_dvd π w).trans ?_
        rw [← Subgroup.orderOf_coe]
        exact hm
      have hcop' : Nat.Coprime (orderOf (π w)) (r ^ m) := by
        have : π w = (x' : L ⧸ Subgroup.center L)⁻¹ *
            ((⟨y ^ k * x' * (y ^ k)⁻¹, (inferInstance : L.Normal).conj_mem x' x'.2 (y ^ k)⟩ :
              L) : L ⧸ Subgroup.center L) := by
          rw [hw, map_mul, map_inv]
          rfl
        rw [this]
        exact Nat.Coprime.pow_right m hcop
      have h1 : π w = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop' hπw)
      rw [hw, map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1.symm
  obtain ⟨u, huY, huL, hu⟩ : ∃ u ∈ Y, u ∈ L ∧ L ⊓ Y ≤ Subgroup.zpowers u ⊔ C := by
    set U := ((L ⊓ Y).subgroupOf L).map π with hU
    have hUr : IsPGroup r U := by
      have h1 : IsPGroup r (L ⊓ Y : Subgroup G) := hYr.to_inf_right
      have h2 : IsPGroup r ((L ⊓ Y).subgroupOf L) := h1.comap_subtype
      exact h2.map π
    have hUodd : Odd (Nat.card U) := by
      obtain ⟨m, hm⟩ := hUr.exists_card_eq
      rw [hm]
      exact (hr.odd_of_ne_two hr2).pow
    have hUnorm : Subgroup.centralizer ({ℓ} : Set (L ⧸ Subgroup.center L)) ≤
        Subgroup.normalizer (U : Set (L ⧸ Subgroup.center L)) := by
      intro c hc
      obtain ⟨c', rfl⟩ := hπs c
      have hc'a : (c' : G) ∈ Subgroup.centralizer ({a} : Set G) :=
        mem_centralizer_of_mk_mem_centralizer L hZ haL haa c' hc
      have hc'N : (c' : G) ∈ Subgroup.normalizer (Y : Set G) := hNY ⟨c'.2, hc'a⟩
      have key : ∀ d : L, (d : G) ∈ Subgroup.normalizer (Y : Set G) →
          ∀ x ∈ U, π d * x * (π d)⁻¹ ∈ U := by
        intro d hd x hx
        obtain ⟨x', hx', rfl⟩ := hx
        refine ⟨d * x' * d⁻¹, ?_, by simp⟩
        have hx'' : (x' : G) ∈ L ⊓ Y := Subgroup.mem_subgroupOf.mp hx'
        show (d * x' * d⁻¹ : L) ∈ (L ⊓ Y).subgroupOf L
        rw [Subgroup.mem_subgroupOf]
        refine Subgroup.mem_inf.mpr ⟨(d * x' * d⁻¹).2, ?_⟩
        simpa using (Subgroup.mem_normalizer_iff.mp hd x').mp hx''.2
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨key c' hc'N x, fun hx => ?_⟩
      have h := key c'⁻¹ (by simpa using Subgroup.inv_mem _ hc'N) _ hx
      simpa [mul_assoc] using h
    have hUcyc : IsCyclic U := by
      by_cases h11 : 11 ≤ p ^ f
      · have hCoat : IsCoatom (Subgroup.centralizer ({ℓ} : Set (L ⧸ Subgroup.center L))) :=
          centralizer_isCoatom_of_mulEquiv e hp hf h11 h8 hℓ2
        by_cases hU1 : U = ⊥
        · rw [hU1]
          infer_instance
        · have hNU : Subgroup.normalizer (U : Set (L ⧸ Subgroup.center L)) ≠ ⊤ := by
            intro h
            have hUn : U.Normal := Subgroup.normalizer_eq_top_iff.mp h
            rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U with h' | h'
            · exact hU1 h'
            · have h2 : 2 ∣ Nat.card U := by rw [h', Subgroup.card_top]; exact hcardL
              exact (Nat.not_even_iff_odd.mpr hUodd) (even_iff_two_dvd.mpr h2)
          have hNeq := (hCoat.le_iff.mp hUnorm).resolve_left hNU
          have hUC : U ≤ Subgroup.centralizer ({ℓ} : Set (L ⧸ Subgroup.center L)) :=
            hNeq ▸ Subgroup.le_normalizer
          have hℓsq : ℓ ^ 2 = 1 := by rw [← hℓ2, pow_orderOf_eq_one]
          exact (odd_normal_subgroup_centralizer hcardL (Or.inl (Or.inr hL2)) hℓsq hUodd hUC
            hUnorm).1
      ·
        have hq5 : p ^ f = 5 := by omega
        have h60 : Nat.card (L ⧸ Subgroup.center L) = 60 := by
          rw [Nat.card_congr e.toEquiv, psl2_card_formula _
            (isOddPrimePower_of_card (GaloisField.card p f hf.ne') hp hf),
            GaloisField.card p f hf.ne', hq5]
          norm_num
        obtain ⟨m, hm⟩ := hUr.exists_card_eq
        have hdvd : r ^ m ∣ 60 := hm ▸ h60 ▸ Subgroup.card_subgroup_dvd_card U
        have hm1 : m ≤ 1 := by
          by_contra hm1
          have h2 : r ^ 2 ∣ 60 := (pow_dvd_pow r (by omega)).trans hdvd
          have hr3 : 3 ≤ r := by
            have := hr.two_le
            omega
          have hr7 : r ≤ 7 := by
            have := Nat.le_of_dvd (by norm_num) h2
            nlinarith
          interval_cases r <;> norm_num at h2
        interval_cases m
        · have : Subsingleton U := by
            rw [pow_zero] at hm
            exact (Nat.card_eq_one_iff_unique.mp hm).1
          exact isCyclic_of_subsingleton
        · rw [pow_one] at hm
          exact isCyclic_of_prime_card hm
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := U)
    obtain ⟨u', hu'mem, hu'eq⟩ := g.2
    have hu'mem' : (u' : G) ∈ L ⊓ Y := Subgroup.mem_subgroupOf.mp hu'mem
    refine ⟨u', hu'mem'.2, u'.2, fun v hv => ?_⟩
    obtain ⟨n, hn⟩ := hg ⟨π ⟨v, hv.1⟩, ⟨v, hv.1⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
    have hn' : π (u' ^ n) = π ⟨v, hv.1⟩ := by
      rw [map_zpow, hu'eq]
      exact congrArg Subtype.val hn
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hn'
    have hcen : ((u' ^ n)⁻¹ * ⟨v, hv.1⟩ : L) ∈ Subgroup.center L := hn'
    have hcC : (((u' ^ n)⁻¹ * ⟨v, hv.1⟩ : L) : G) ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hcen ⟨x, hx⟩))
    have : v = (u' : G) ^ n * (((u' ^ n)⁻¹ * ⟨v, hv.1⟩ : L) : G) := by simp
    rw [this]
    exact Subgroup.mul_mem _ (le_sup_left (a := Subgroup.zpowers (u' : G))
      (Subgroup.zpow_mem_zpowers _ n)) (le_sup_right (a := Subgroup.zpowers (u' : G)) hcC)
  have hYle : Y ≤ Subgroup.zpowers u ⊔ C := hdecomp.trans (sup_le (hYA.trans le_sup_right) hu)
  exact ⟨hYle.trans (sup_le_sup_right (Subgroup.zpowers_le.mpr huL) _), u, huY, hYle⟩

end TypeII

end CFSG.Goldschmidt.G3b
