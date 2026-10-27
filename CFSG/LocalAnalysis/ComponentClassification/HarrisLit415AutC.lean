module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415AutInputs
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSplitCent
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOddClosure
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOuterCent

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup GorensteinWalter AutL2Facts

namespace AutC

theorem commute_of_odd_of_conj_mem {G : Type*} [Group G] [Finite G] {u x : G} {b : ℕ}
    (hu : orderOf u = 2 ^ b) (hx : Odd (orderOf x)) (hxu : x * u * x⁻¹ ∈ zpowers u) :
    x * u = u * x := by
  have hmap : (zpowers u).map (MulAut.conj x).toMonoidHom = zpowers u := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [MonoidHom.map_zpowers, zpowers_le]
      exact hxu
    · exact (Nat.card_congr
        ((zpowers u).equivMapOfInjective _ (MulAut.conj x).injective).toEquiv).le
  let φ : MulAut ↥(zpowers u) :=
    ((MulAut.conj x).subgroupMap (zpowers u)).trans (MulEquiv.subgroupCongr hmap)
  have hφ : ∀ q : ↥(zpowers u), ((φ q : ↥(zpowers u)) : G) = x * q * x⁻¹ := fun q => rfl
  have hφj : ∀ j : ℕ, ∀ q : ↥(zpowers u),
      (((φ ^ j) q : ↥(zpowers u)) : G) = x ^ j * q * (x ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro q; simp
    | succ j ih =>
      intro q
      rw [pow_succ, MulAut.mul_apply, ih, hφ, pow_succ]
      group
  have hφo : φ ^ orderOf x = 1 := by
    refine MulEquiv.ext fun q => Subtype.ext ?_
    rw [hφj, pow_orderOf_eq_one]
    simp
  have hcard : Nat.card (MulAut ↥(zpowers u)) = 2 ^ (b - 1) := by
    rw [IsCyclic.card_mulAut, Nat.card_zpowers, hu]
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      simp
    · rw [Nat.totient_prime_pow Nat.prime_two hb]
      simp
  have h1 : φ = 1 := by
    have h2 : orderOf φ ∣ orderOf x := orderOf_dvd_of_pow_eq_one hφo
    have h3 : orderOf φ ∣ 2 ^ (b - 1) := by
      rw [← hcard]
      exact _root_.orderOf_dvd_natCard φ
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    rcases i with _ | i
    · rw [pow_zero] at hi
      exact orderOf_eq_one_iff.mp hi
    · exfalso
      rw [hi, pow_succ] at h2
      exact (Nat.not_even_iff_odd.mpr hx) (even_iff_two_dvd.mpr ((dvd_mul_left 2 _).trans h2))
  have h4 : ((φ ⟨u, mem_zpowers u⟩ : ↥(zpowers u)) : G) = x * u * x⁻¹ := rfl
  rw [h1] at h4
  have h5 : x * u * x⁻¹ = u := h4.symm
  calc x * u = x * u * x⁻¹ * x := by group
    _ = u * x := by rw [h5]

theorem mem_zpowers_of_two_pow {G : Type*} [Group G] {g v : G} {b m k : ℕ} (hm : Odd m)
    (hg : orderOf g = 2 ^ b * m) (hv : v ∈ zpowers g) (hvk : v ^ 2 ^ k = 1) :
    v ∈ zpowers (g ^ m) := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hv
  have h1 : g ^ (i * ((2 ^ k : ℕ) : ℤ)) = 1 := by
    rw [zpow_mul, zpow_natCast]
    exact hvk
  have h2 : ((orderOf g : ℕ) : ℤ) ∣ i * ((2 ^ k : ℕ) : ℤ) := orderOf_dvd_iff_zpow_eq_one.mpr h1
  have h3 : (m : ℤ) ∣ i * ((2 ^ k : ℕ) : ℤ) :=
    (Int.natCast_dvd_natCast.mpr (Dvd.intro_left _ hg.symm)).trans h2
  have hcop : IsCoprime (m : ℤ) ((2 ^ k : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right k hm.coprime_two_right)
  obtain ⟨j, hj⟩ := hcop.dvd_of_dvd_mul_right h3
  exact mem_zpowers_iff.mpr ⟨j, by rw [hj, zpow_mul, zpow_natCast]⟩

theorem mem_of_mem_sup_of_ne {G : Type*} [Group G] {U : Subgroup G} {w v : G} (hwU : w ∉ U)
    (hww : w * w = 1) (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) (hv : v ∈ U ⊔ zpowers w)
    (hv2 : v * v ≠ 1) : v ∈ U := by
  obtain ⟨u, hu, rfl | rfl⟩ :=
    (GorensteinWalter.mem_sup_zpowers_of_involution_inverts hwU hww hwinv).mp hv
  · exact hu
  · exfalso
    apply hv2
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have h1 := hwinv u hu
    rw [hwi] at h1
    calc u * w * (u * w) = u * (w * u * w) := by group
      _ = 1 := by rw [h1]; group

theorem mem_of_mem_sup_of_commute {G : Type*} [Group G] {U : Subgroup G} {w v u : G}
    (hwU : w ∉ U) (hww : w * w = 1) (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹)
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hv : v ∈ U ⊔ zpowers w) (hu : u ∈ U)
    (hu2 : u * u ≠ 1) (hvu : v * u = u * v) : v ∈ U := by
  obtain ⟨u', hu', rfl | rfl⟩ :=
    (GorensteinWalter.mem_sup_zpowers_of_involution_inverts hwU hww hwinv).mp hv
  · exact hu'
  · exfalso
    apply hu2
    have h1 := hwinv u hu
    have h2 : u' * w * u = u' * u⁻¹ * w := by
      calc u' * w * u = u' * (w * u * w⁻¹) * w := by group
        _ = u' * u⁻¹ * w := by rw [h1]
    rw [h2] at hvu
    have h3 : u' * u⁻¹ = u * u' := by
      calc u' * u⁻¹ = u' * u⁻¹ * w * w⁻¹ := by group
        _ = u * (u' * w) * w⁻¹ := by rw [hvu]
        _ = u * u' := by group
    rw [hUc u hu u' hu'] at h3
    have h4 : u⁻¹ = u := mul_left_cancel h3
    calc u * u = u * u⁻¹ := by rw [h4]
      _ = 1 := mul_inv_cancel u

variable {F : Type} [Field F] [Finite F]

theorem odd_mul_of_commute_nonsplit {U : Subgroup (PGL2 F)} {s w u : PGL2 F} {b : ℕ}
    (hAut : Odd (Nat.card (F ≃+* F)))
    (hCs : centralizer ({s} : Set (PGL2 F)) = U ⊔ zpowers w) (hwU : w ∉ U) (hww : w * w = 1)
    (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hsU : s ∈ U) (huU : u ∈ U) (hu : orderOf u = 2 ^ b) (hb : 2 ≤ b)
    (h2U : ∀ v ∈ U, ∀ k : ℕ, v ^ 2 ^ k = 1 → v ∈ zpowers u) {x y : PGammaL2 F}
    (hx : x * SemidirectProduct.inl s = SemidirectProduct.inl s * x)
    (hy : y * SemidirectProduct.inl s = SemidirectProduct.inl s * y)
    (hxo : Odd (orderOf x)) (hyo : Odd (orderOf y)) : Odd (orderOf (x * y)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ∀ v : PGL2 F, orderOf v = 2 ^ b → v * v ≠ 1 := by
    intro v hv h
    have h1 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [hv] at h1
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have h3 : 2 ^ 2 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    omega
  have hinl : ∀ v : PGL2 F, orderOf (SemidirectProduct.inl v : PGammaL2 F) = orderOf v :=
    fun v => orderOf_injective _ SemidirectProduct.inl_injective v
  have hlin : ∀ g : PGammaL2 F, g.right = 1 →
      g * SemidirectProduct.inl s = SemidirectProduct.inl s * g →
        g = SemidirectProduct.inl g.left ∧ g.left ∈ U ⊔ zpowers w := by
    intro g hg hgs
    have hg' : g = SemidirectProduct.inl g.left := SemidirectProduct.ext rfl hg
    refine ⟨hg', ?_⟩
    rw [← hCs, mem_centralizer_singleton_iff]
    have h1 : (SemidirectProduct.inl (g.left * s) : PGammaL2 F) =
        SemidirectProduct.inl (s * g.left) := by
      rw [map_mul, map_mul, ← hg']
      exact hgs
    exact SemidirectProduct.inl_injective h1
  have hzp : ∀ v ∈ zpowers u, (SemidirectProduct.inl v : PGammaL2 F) ∈
      zpowers (SemidirectProduct.inl u : PGammaL2 F) := by
    intro v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    exact mem_zpowers_iff.mpr ⟨k, (map_zpow _ u k).symm⟩
  have hιs : (SemidirectProduct.inl u : PGammaL2 F) * SemidirectProduct.inl s =
      SemidirectProduct.inl s * SemidirectProduct.inl u := by
    rw [← map_mul, ← map_mul, hUc u huU s hsU]
  have hιo : orderOf (SemidirectProduct.inl u : PGammaL2 F) = 2 ^ b := by rw [hinl, hu]
  have hodd : ∀ g : PGammaL2 F, g * SemidirectProduct.inl s = SemidirectProduct.inl s * g →
      Odd (orderOf g) → g * SemidirectProduct.inl u = SemidirectProduct.inl u * g := by
    intro g hgs hgo
    refine commute_of_odd_of_conj_mem hιo hgo ?_
    have hcr : (g * SemidirectProduct.inl u * g⁻¹).right = 1 := by simp
    have hcs : g * SemidirectProduct.inl u * g⁻¹ * SemidirectProduct.inl s =
        SemidirectProduct.inl s * (g * SemidirectProduct.inl u * g⁻¹) :=
      (((show Commute g (SemidirectProduct.inl s) from hgs).mul_left
        (show Commute (SemidirectProduct.inl u) (SemidirectProduct.inl s) from hιs)).mul_left
        (show Commute g (SemidirectProduct.inl s) from hgs).inv_left).eq
    obtain ⟨hc', hcU'⟩ := hlin _ hcr hcs
    have hco : orderOf (g * SemidirectProduct.inl u * g⁻¹).left = 2 ^ b := by
      have h1 : orderOf (g * SemidirectProduct.inl u * g⁻¹) =
          orderOf (SemidirectProduct.inl u : PGammaL2 F) := by
        have := MulEquiv.orderOf_eq (MulAut.conj g) (SemidirectProduct.inl u)
        rwa [MulAut.conj_apply] at this
      rw [← hinl, ← hc', h1, hιo]
    have hcU := mem_of_mem_sup_of_ne hwU hww hwinv hcU' (hne _ hco)
    have hcQ := h2U _ hcU b (by rw [← hco]; exact pow_orderOf_eq_one _)
    rw [hc']
    exact hzp _ hcQ
  set L : Subgroup (PGammaL2 F) :=
    centralizer ({SemidirectProduct.inl s} : Set (PGammaL2 F)) ⊓
      centralizer ({SemidirectProduct.inl u} : Set (PGammaL2 F)) with hL
  have h2L : ∀ ℓ ∈ L, ∀ k : ℕ, ℓ ^ 2 ^ k = 1 →
      ℓ ∈ zpowers (SemidirectProduct.inl u : PGammaL2 F) := by
    intro ℓ hℓ k hk
    have hℓs := mem_centralizer_singleton_iff.mp (mem_inf.mp hℓ).1
    have hℓι := mem_centralizer_singleton_iff.mp (mem_inf.mp hℓ).2
    have hr : ℓ.right = 1 := by
      have h1 : ℓ.right ^ 2 ^ k = 1 := by
        have := congrArg (fieldProj F) hk
        rwa [map_pow, map_one] at this
      have h2 : orderOf ℓ.right ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
      have h3 : orderOf ℓ.right ∣ Nat.card (F ≃+* F) := _root_.orderOf_dvd_natCard _
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
      rcases i with _ | i
      · rw [pow_zero] at hi
        exact orderOf_eq_one_iff.mp hi
      · exfalso
        rw [hi, pow_succ] at h3
        exact (Nat.not_even_iff_odd.mpr hAut)
          (even_iff_two_dvd.mpr ((dvd_mul_left 2 _).trans h3))
    obtain ⟨hℓ', hℓU'⟩ := hlin ℓ hr hℓs
    have hℓu : ℓ.left * u = u * ℓ.left := by
      have h1 : (SemidirectProduct.inl (ℓ.left * u) : PGammaL2 F) =
          SemidirectProduct.inl (u * ℓ.left) := by
        rw [map_mul, map_mul, ← hℓ']
        exact hℓι
      exact SemidirectProduct.inl_injective h1
    have hℓU := mem_of_mem_sup_of_commute hwU hww hwinv hUc hℓU' huU (hne u hu) hℓu
    have hℓk : ℓ.left ^ 2 ^ k = 1 := by
      have h1 : (SemidirectProduct.inl (ℓ.left ^ 2 ^ k) : PGammaL2 F) =
          SemidirectProduct.inl 1 := by
        rw [map_pow, ← hℓ', hk, map_one]
      exact SemidirectProduct.inl_injective h1
    rw [hℓ']
    exact hzp _ (h2U _ hℓU k hℓk)
  have hxL : x ∈ L := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hx,
    mem_centralizer_singleton_iff.mpr (hodd x hx hxo)⟩
  have hyL : y ∈ L := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hy,
    mem_centralizer_singleton_iff.mpr (hodd y hy hyo)⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  have hPc : ∀ a ∈ (P : Subgroup ↥L), ∀ c : ↥L, a * c = c * a := by
    intro a ha c
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨a, ha⟩
    have hak : (a : PGammaL2 F) ^ 2 ^ k = 1 := by
      rw [← hk, Subgroup.orderOf_mk, ← Subgroup.orderOf_coe]
      exact pow_orderOf_eq_one _
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (h2L a a.2 k hak)
    have hcι : (c : PGammaL2 F) * SemidirectProduct.inl u =
        SemidirectProduct.inl u * (c : PGammaL2 F) :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hj]
    exact (Commute.zpow_left
      (show Commute (SemidirectProduct.inl u : PGammaL2 F) c from hcι.symm) j).eq
  have hP : normalizer (P : Set ↥L) ≤ centralizer (P : Set ↥L) := by
    intro g _
    rw [mem_centralizer_iff]
    intro h hh
    exact hPc h hh g
  have hK := MonoidHom.not_dvd_card_ker_transferSylow P hP
  have hmemK : ∀ a : ↥L, Odd (orderOf a) → a ∈ (MonoidHom.transferSylow P hP).ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' (MonoidHom.transferSylow P hP a)
    have h1 : orderOf (MonoidHom.transferSylow P hP a) ∣ orderOf a := orderOf_map_dvd _ _
    rw [hk] at h1
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact orderOf_eq_one_iff.mp hk
    · exfalso
      rw [pow_succ] at h1
      exact (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr ((dvd_mul_left 2 _).trans h1))
  have hxyK := mul_mem (hmemK ⟨x, hxL⟩ (by rw [Subgroup.orderOf_mk]; exact hxo))
    (hmemK ⟨y, hyL⟩ (by rw [Subgroup.orderOf_mk]; exact hyo))
  have h1 := Subgroup.orderOf_dvd_natCard _ hxyK
  have h2 : orderOf ((⟨x, hxL⟩ : ↥L) * ⟨y, hyL⟩) = orderOf (x * y) := by
    rw [← Subgroup.orderOf_coe]
    rfl
  rw [h2] at h1
  exact Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hK)) h1

theorem exists_nonsplit_data {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n)
    (hsq : ¬ IsSquare (-1 : F)) :
    Odd (Nat.card (F ≃+* F)) ∧ ∃ (U : Subgroup (PGL2 F)) (s w u : PGL2 F) (b : ℕ) (s₀ : PSL2 F),
      centralizer ({s} : Set (PGL2 F)) = U ⊔ zpowers w ∧ w ∉ U ∧ w * w = 1 ∧
      (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧ s ∈ U ∧ u ∈ U ∧
      orderOf u = 2 ^ b ∧ 2 ≤ b ∧ (∀ v ∈ U, ∀ k : ℕ, v ^ 2 ^ k = 1 → v ∈ zpowers u) ∧
      Matrix.ProjectiveSpecialLinearGroup.toPGL s₀ = s ∧
      BenderSuzuki.PFAppendixIII.IsInvolution s₀ := by
  have hFodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have hq3 : Nat.card F % 4 = 3 := by
    classical
    have : Fintype F := Fintype.ofFinite F
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card] at hsq
    omega
  have hn : Odd n := by
    rcases Nat.even_or_odd n with hne | hno
    · exfalso
      have := pow_mod_four_of_even hp hp2 hne
      rw [← hF] at this
      omega
    · exact hno
  refine ⟨by rw [card_ringAut F hp hF]; exact hn, ?_⟩
  obtain ⟨U, s, w, hUcyc, hUcard, hsU, hss, hs1, hwU, hww, hwinv, hCs, -⟩ :=
    pgl2_nonsplit_torus_centralizer_data F hFodd
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := ↥U)).ne'
  have hb : 2 ≤ b := by
    obtain ⟨m', rfl⟩ := hm
    have hU4 : (2 ^ b * (2 * m' + 1)) % 4 = 0 := by rw [← hbm, hUcard]; omega
    rcases (show b = 0 ∨ b = 1 ∨ 2 ≤ b by omega) with rfl | rfl | h
    · simp only [pow_zero, one_mul] at hU4
      omega
    · simp only [pow_one] at hU4
      omega
    · exact h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥U)
  have hgo : orderOf (g : PGL2 F) = 2 ^ b * m := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hbm]
  have hUg : ∀ v ∈ U, v ∈ zpowers (g : PGL2 F) := by
    intro v hv
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨v, hv⟩)
    exact mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  have huU : (g : PGL2 F) ^ m ∈ U := pow_mem g.2 m
  have huo : orderOf ((g : PGL2 F) ^ m) = 2 ^ b := by
    rw [orderOf_pow_of_dvd hm.pos.ne' (Dvd.intro_left _ hgo.symm), hgo,
      Nat.mul_div_cancel _ hm.pos]
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsCyclic.commGroup.mul_comm (⟨x, hx⟩ : ↥U) ⟨y, hy⟩)
  have hexp : 2 ^ b = 2 ^ (b - 2) * 2 * 2 := by
    rw [← pow_succ, ← pow_succ]
    congr 1
    omega
  have hpow : (((g : PGL2 F) ^ m) ^ 2 ^ (b - 2)) ^ 2 * (((g : PGL2 F) ^ m) ^ 2 ^ (b - 2)) ^ 2 =
      1 := by
    have h := pow_orderOf_eq_one ((g : PGL2 F) ^ m)
    rw [huo, hexp, pow_mul, pow_mul, sq] at h
    exact h
  have hs'1 : (((g : PGL2 F) ^ m) ^ 2 ^ (b - 2)) ^ 2 ≠ 1 := by
    intro h
    rw [← pow_mul] at h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [huo] at h1
    have h3 := Nat.le_of_dvd (by positivity) h1
    have h4 : 1 ≤ 2 ^ (b - 2) := Nat.one_le_two_pow
    omega
  have hss' : s = (((g : PGL2 F) ^ m) ^ 2 ^ (b - 2)) ^ 2 := by
    rcases eq_one_or_eq_of_sq_eq_one_cyclic (G := ↥U)
        (s := ⟨_, pow_mem (pow_mem huU _) 2⟩) (y := ⟨s, hsU⟩)
        (Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact hpow))
        (fun h => hs'1 (congrArg Subtype.val h))
        (Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact hss)) with h | h
    · exact absurd (congrArg Subtype.val h) hs1
    · exact congrArg Subtype.val h
  obtain ⟨s₀, hs₀⟩ := sq_mem_psl2Range (((g : PGL2 F) ^ m) ^ 2 ^ (b - 2))
  rw [← hss'] at hs₀
  refine ⟨U, s, w, (g : PGL2 F) ^ m, b, s₀, hCs, hwU, hww, hwinv, hUc, hsU, huU, huo, hb,
    fun v hv k hk => mem_zpowers_of_two_pow hm hgo (hUg v hv) hk, hs₀, fun h => hs1 ?_, ?_⟩
  · rw [← hs₀, h, map_one]
  · apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [map_pow, hs₀, map_one, sq]
    exact hss

end AutC

theorem autPSL2InvolutionCentralizer : AutPSL2InvolutionCentralizerInput := by
  intro Y _ _ p n hp hp2 hY y hy
  obtain ⟨-, hn1, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hodd := isOddPrimePower_of hp hp2 hn1 hF
  have h2 := two_ne_zero_of_isOddPrimePower hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2 : BenderSuzuki.PFAppendixIII.IsInvolution (e y) := by
    have hord : orderOf (e y) = 2 := by rw [MulEquiv.orderOf_eq, hy]
    refine ⟨fun h1 => ?_, by have := pow_orderOf_eq_one (e y); rwa [hord] at this⟩
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  suffices h : ∃ z : PSL2 F, BenderSuzuki.PFAppendixIII.IsInvolution z ∧
      ∀ a ∈ centralizer ({incl F z} : Set (PGammaL2 F)),
        ∀ c ∈ centralizer ({incl F z} : Set (PGammaL2 F)),
          Odd (orderOf a) → Odd (orderOf c) → Odd (orderOf (a * c)) by
    obtain ⟨z, hz, hmul⟩ := h
    obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd (e y) z hy2 hz
    have hconj : incl F g * incl F (e y) * (incl F g)⁻¹ = incl F z := by
      rw [← map_inv, ← map_mul, ← map_mul, hg]
    let φ : MulAction.stabilizer (MulAut Y) y ≃* centralizer ({incl F z} : Set (PGammaL2 F)) :=
      (stabilizerEquiv e y).trans ((centralizerConjEquiv (incl F g) (incl F (e y))).trans
        (MulEquiv.subgroupCongr (by rw [hconj])))
    exact (isPGroup_quotient_pPrimeCore_of_odd_mul _ hmul).of_equiv
      (QuotientGroup.congr (pPrimeCore 2 _) (pPrimeCore 2 _) φ.symm
        (CFSG.pPrimeCore_map_iso 2 φ.symm))
  by_cases hsq : IsSquare (-1 : F)
  ·
    obtain ⟨z, hz⟩ := exists_psl2_tor_neg_one hsq
    have hneg : (-1 : Fˣ) ≠ 1 := by
      intro h1
      apply h2
      have := congrArg (fun u : Fˣ => (u : F)) h1
      simp only [Units.val_neg, Units.val_one] at this
      linear_combination -this
    refine ⟨z, ⟨fun h1 => tor_neg_one_ne_one h2 ?_, ?_⟩, fun a ha c hc hao hco => ?_⟩
    · have : incl F z = 1 := by rw [h1, map_one]
      rw [hz] at this
      exact SemidirectProduct.inl_injective (this.trans (map_one _).symm)
    · apply incl_injective F
      rw [map_pow, hz, ← map_pow, ← map_pow, neg_one_sq, map_one, map_one, map_one]
    · rw [hz] at ha hc
      exact odd_mul_of_commute_z hneg (mem_centralizer_singleton_iff.mp ha)
        (mem_centralizer_singleton_iff.mp hc) hao hco
  ·
    obtain ⟨hAut, U, s, w, u, b, s₀, hCs, hwU, hww, hwinv, hUc, hsU, huU, huo, hb, h2U, hs₀,
      hs₀i⟩ := AutC.exists_nonsplit_data hp hp2 hF hsq
    refine ⟨s₀, hs₀i, fun a ha c hc hao hco => ?_⟩
    rw [incl_apply, hs₀] at ha hc
    exact AutC.odd_mul_of_commute_nonsplit hAut hCs hwU hww hwinv hUc hsU huU huo hb h2U
      (mem_centralizer_singleton_iff.mp ha) (mem_centralizer_singleton_iff.mp hc) hao hco

end CFSG.ComponentClassification.HarrisLit
