module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveEmb
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveGen

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open Subgroup CFSG.HardMathSupport.Dickson.I271.TabMFive

section Prod

variable {G : Type*} [Group G] {p : ℕ} {k : G}

theorem eq_one_of_mem_zpowers_of_center {H : Subgroup G} (hHk : H ≤ centralizer ({k} : Set G))
    (hZ : center ↥H = ⊥) {g : G} (hg : g ∈ zpowers k) (hgH : g ∈ H) : g = 1 := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  have hmem : (⟨k ^ n, hgH⟩ : ↥H) ∈ center ↥H := by
    rw [mem_center_iff]
    intro b
    exact Subtype.ext
      (Commute.zpow_right (mem_centralizer_singleton_iff.1 (hHk b.2) : Commute (b : G) k) n).eq
  rw [hZ, mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem prod_injective' (hk : orderOf k = p) {H' : Subgroup G}
    (hKH : ∀ g ∈ zpowers k, g ∈ H' → g = 1) :
    Function.Injective (fun x : Fin p × ↥H' => k ^ (x.1 : ℕ) * (x.2 : G)) := by
  rintro ⟨i, h⟩ ⟨j, h'⟩ hij
  have hij' : k ^ (i : ℕ) * (h : G) = k ^ (j : ℕ) * (h' : G) := hij
  have h1 : (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ) = (h' : G) * (h : G)⁻¹ := by
    calc (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ)
        = (k ^ (j : ℕ))⁻¹ * (k ^ (i : ℕ) * (h : G)) * (h : G)⁻¹ := by group
      _ = (k ^ (j : ℕ))⁻¹ * (k ^ (j : ℕ) * (h' : G)) * (h : G)⁻¹ := by rw [hij']
      _ = (h' : G) * (h : G)⁻¹ := by group
  have h2 : (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ) ∈ zpowers k :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (mem_zpowers k) _))
      (Subgroup.pow_mem _ (mem_zpowers k) _)
  have h3 : (k ^ (j : ℕ))⁻¹ * k ^ (i : ℕ) ∈ H' := by
    rw [h1]
    exact H'.mul_mem h'.2 (H'.inv_mem h.2)
  have h5 : k ^ (j : ℕ) = k ^ (i : ℕ) := inv_mul_eq_one.1 (hKH _ h2 h3)
  have h6 : (i : ℕ) = (j : ℕ) := by
    have hi : (i : ℕ) ∈ Set.Iio (orderOf k) := by rw [hk]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf k) := by rw [hk]; exact j.2
    exact pow_injOn_Iio_orderOf hi hj h5.symm
  have h7 : (h' : G) * (h : G)⁻¹ = 1 := by rw [← h1, h6]; simp
  have hij2 : i = j := Fin.ext h6
  subst hij2
  exact Prod.ext rfl (Subtype.ext (mul_inv_eq_one.1 h7).symm)

theorem mul_card_le_of_prod' [Finite G] (hk : orderOf k = p) {H' X : Subgroup G}
    (hKH : ∀ g ∈ zpowers k, g ∈ H' → g = 1) (hkX : k ∈ X) (hH'X : H' ≤ X) :
    p * Nat.card ↥H' ≤ Nat.card ↥X := by
  let f : Fin p × ↥H' → ↥X := fun x =>
    ⟨k ^ (x.1 : ℕ) * (x.2 : G), X.mul_mem (X.pow_mem hkX _) (hH'X x.2.2)⟩
  have hf : Function.Injective f := fun x y hxy =>
    prod_injective' hk hKH (congrArg Subtype.val hxy)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at this

theorem eq_prod_of_card_le' [Finite G] (hk : orderOf k = p) {H' X : Subgroup G}
    (hKH : ∀ g ∈ zpowers k, g ∈ H' → g = 1) (hkX : k ∈ X) (hH'X : H' ≤ X)
    (hX : Nat.card ↥X ≤ p * Nat.card ↥H') :
    ∀ x ∈ X, ∃ (i : ℕ) (h : G), h ∈ H' ∧ x = k ^ i * h := by
  let f : Fin p × ↥H' → ↥X := fun x =>
    ⟨k ^ (x.1 : ℕ) * (x.2 : G), X.mul_mem (X.pow_mem hkX _) (hH'X x.2.2)⟩
  have hf : Function.Injective f := fun x y hxy =>
    prod_injective' hk hKH (congrArg Subtype.val hxy)
  have hbij : Function.Bijective f := by
    refine hf.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin]
    exact hX
  intro x hx
  obtain ⟨⟨i, h⟩, hih⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨i, h, h.2, (congrArg Subtype.val hih).symm⟩

theorem mem_of_orderOf_two' (hp : p.Prime) (hp2 : p ≠ 2) (hk : orderOf k = p) {H : Subgroup G}
    {hHk : H ≤ centralizer ({k} : Set G)} (hKH : ∀ g ∈ zpowers k, g ∈ H → g = 1) {t : G}
    (ht : t ∈ prodSub k H hHk) (ho : orderOf t = 2) : t ∈ H := by
  obtain ⟨i, h, hh, rfl⟩ := ht
  have hc : h * k ^ i = k ^ i * h :=
    (Commute.zpow_right (mem_centralizer_singleton_iff.1 (hHk hh) : Commute h k) i).eq
  have hsq : (k ^ i * h) ^ 2 = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  have hsq' : k ^ (2 * i) = (h ^ 2)⁻¹ := by
    have h1 : (k ^ i * h) ^ 2 = k ^ i * k ^ i * (h * h) := by
      calc (k ^ i * h) ^ 2 = k ^ i * h * (k ^ i * h) := sq _
        _ = k ^ i * (h * k ^ i) * h := by simp only [mul_assoc]
        _ = k ^ i * (k ^ i * h) * h := by rw [hc]
        _ = k ^ i * k ^ i * (h * h) := by simp only [mul_assoc]
    rw [h1] at hsq
    rw [two_mul, zpow_add, sq h]
    exact eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using hsq)
  have hz : k ^ (2 * i) ∈ zpowers k := Subgroup.zpow_mem _ (mem_zpowers k) _
  have hH : k ^ (2 * i) ∈ H := by
    rw [hsq']
    exact H.inv_mem (H.pow_mem hh 2)
  have h1 := hKH _ hz hH
  have h2 : k ^ i = 1 := by
    have hodd : orderOf (k ^ i) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
      simpa using h1
    have hdv : orderOf (k ^ i) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hk,
        pow_orderOf_eq_one, one_zpow]
    have h6 : orderOf (k ^ i) ∣ Nat.gcd 2 p := Nat.dvd_gcd hodd hdv
    have h7 : Nat.gcd 2 p = 1 := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    rw [h7] at h6
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h6)
  rw [h2, one_mul]
  exact hh

theorem mul_card_le_cent_inf' [Finite G] (hk : orderOf k = p) {H : Subgroup G}
    (hHk : H ≤ centralizer ({k} : Set G)) (hKH : ∀ g ∈ zpowers k, g ∈ H → g = 1) {t : G}
    (ht : t ∈ H) :
    p * Nat.card ↥(H ⊓ centralizer ({t} : Set G)) ≤
      Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G)) :=
  mul_card_le_of_prod' hk (H' := H ⊓ centralizer ({t} : Set G))
    (fun g hg hgH => hKH g hg hgH.1)
    ⟨mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (hHk ht)).symm,
      mem_centralizer_singleton_iff.2 rfl⟩
    (fun x hx => ⟨hx.2, hHk hx.1⟩)

theorem card_centralizer_le_of_involutions' [Finite G] (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : orderOf k = p) {H : Subgroup G} (hKH : ∀ g ∈ zpowers k, g ∈ H → g = 1)
    (hHk : H ≤ centralizer ({k} : Set G))
    (hup : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G)) ≤
        p * Nat.card ↥(H ⊓ centralizer ({t} : Set G)))
    (hconj : ∀ t ∈ H, ∀ u ∈ H, orderOf t = 2 → orderOf u = 2 →
      Nat.card ↥(H ⊓ centralizer ({t} : Set G)) = Nat.card ↥(H ⊓ centralizer ({u} : Set G)) →
        ∃ g ∈ H, g * u * g⁻¹ = t)
    {t₀ t₁ : G} (ht₀ : t₀ ∈ H) (ht₁ : t₁ ∈ H) (ho₀ : orderOf t₀ = 2) (ho₁ : orderOf t₁ = 2)
    (hne : Nat.card ↥(H ⊓ centralizer ({t₀} : Set G)) ≠
      Nat.card ↥(H ⊓ centralizer ({t₁} : Set G))) :
    centralizer ({k} : Set G) = prodSub k H hHk ∧
      Nat.card ↥(centralizer ({k} : Set G)) ≤ p * Nat.card ↥H := by
  set D := prodSub k H hHk with hD
  have hkC : k ∈ centralizer ({k} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hDC : D ≤ centralizer ({k} : Set G) := prodSub_le hkC hHk
  have hHD : H ≤ D := le_prodSub
  have hkt : ∀ t ∈ H, k ∈ centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G) := fun t ht =>
    ⟨mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (hHk ht)).symm, hkC⟩
  have hHt : ∀ t ∈ H, H ⊓ centralizer ({t} : Set G) ≤
      centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G) := fun t _ x hx =>
    ⟨hx.2, hHk hx.1⟩
  have hKHt : ∀ t : G, ∀ g ∈ zpowers k, g ∈ H ⊓ centralizer ({t} : Set G) → g = 1 :=
    fun _ g hg hgH => hKH g hg hgH.1
  have heq : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G)) =
        p * Nat.card ↥(H ⊓ centralizer ({t} : Set G)) := fun t ht ho =>
    le_antisymm (hup t ht ho) (mul_card_le_of_prod' hk (hKHt t) (hkt t ht) (hHt t ht))
  have heq' : ∀ t ∈ H, orderOf t = 2 →
      Nat.card ↥(centralizer ({k} : Set G) ⊓ centralizer ({t} : Set G)) =
        p * Nat.card ↥(H ⊓ centralizer ({t} : Set G)) := fun t ht ho => by
    rw [inf_comm]
    exact heq t ht ho
  have hsub : ∀ t ∈ H, orderOf t = 2 →
      centralizer ({k} : Set G) ⊓ centralizer ({t} : Set G) ≤ D := by
    intro t ht ho x hx
    have hx' : x ∈ centralizer ({t} : Set G) ⊓ centralizer ({k} : Set G) := ⟨hx.2, hx.1⟩
    obtain ⟨i, h, hh, rfl⟩ :=
      eq_prod_of_card_le' hk (hKHt t) (hkt t ht) (hHt t ht) (hup t ht ho) x hx'
    exact ⟨(i : ℤ), h, hh.1, by rw [zpow_natCast]⟩
  have hDeq : D = centralizer ({k} : Set G) := by
    refine eq_of_involutions hDC ?_ ?_ (hHD ht₀) (hHD ht₁) ho₀ ho₁ ?_
    · intro t ht ho
      exact hsub t (mem_of_orderOf_two' hp hp2 hk hKH ht ho) ho
    · intro t ht u hu hto huo hcard
      have ht' := mem_of_orderOf_two' hp hp2 hk hKH ht hto
      have hu' := mem_of_orderOf_two' hp hp2 hk hKH hu huo
      rw [heq' t ht' hto, heq' u hu' huo] at hcard
      obtain ⟨g, hg, hgu⟩ := hconj t ht' u hu' hto huo (Nat.eq_of_mul_eq_mul_left hp.pos hcard)
      exact ⟨g, hHD hg, hgu⟩
    · rw [heq' t₀ ht₀ ho₀, heq' t₁ ht₁ ho₁]
      exact fun h => hne (Nat.eq_of_mul_eq_mul_left hp.pos h)
  refine ⟨hDeq.symm, ?_⟩
  rw [← hDeq]
  let f : Fin p × ↥H → ↥D := fun x =>
    ⟨k ^ (x.1 : ℕ) * (x.2 : G), ⟨((x.1 : ℕ) : ℤ), x.2, x.2.2, by rw [zpow_natCast]⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨d, i, h, hh, rfl⟩
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hk' : (orderOf k : ℤ) = p := by rw [hk]
    have hnn : 0 ≤ i % (p : ℤ) := Int.emod_nonneg _ hp0.ne'
    have hlt : (i % (p : ℤ)).toNat < p := by
      have := Int.emod_lt_of_pos i hp0
      omega
    have h1 : k ^ i = k ^ ((i % (p : ℤ)).toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← hk', zpow_mod_orderOf]
    refine ⟨(⟨(i % (p : ℤ)).toNat, hlt⟩, ⟨h, hh⟩), Subtype.ext ?_⟩
    show k ^ ((i % (p : ℤ)).toNat) * h = k ^ i * h
    rw [h1]
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at this

end Prod

section Shape

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4

variable {G : Type} [Group G] [Finite G]

theorem tabMSeven_shapeRkAt'_of_simple {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    {k : G} (hk : orderOf k = p) {H : Subgroup G}
    (hHk : H ≤ Subgroup.centralizer ({k} : Set G)) (hs : IsSimpleGroup ↥H)
    (hnab : ∃ a b : ↥H, a * b ≠ b * a) (hpH : p ∣ Nat.card ↥H)
    (hbound : Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ p * Nat.card ↥H)
    (hG : Good ↥H) (hR : Rk ↥H) : ShapeRkAt' p Good Rk k := by
  haveI : Fact p.Prime := ⟨hp⟩
  set X : Subgroup G := Subgroup.centralizer ({k} : Set G) with hX
  have hkX : k ∈ X := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hZ : Subgroup.center ↥H = ⊥ := center_eq_bot_of_simple_nonab hnab
  have hKH : ∀ g ∈ Subgroup.zpowers k, g ∈ H → g = 1 := fun _ hg hgH =>
    eq_one_of_mem_zpowers_of_center hHk hZ hg hgH
  have hdec : ∀ x ∈ X, ∃ (i : ℕ) (h : G), h ∈ H ∧ x = k ^ i * h :=
    eq_prod_of_card_le' hk hKH hkX hHk hbound
  have hcomm : ∀ (i : ℕ) (y : G), y ∈ H → k ^ i * y * (k ^ i)⁻¹ = y := by
    intro i y hy
    have hyk : Commute y k := Subgroup.mem_centralizer_singleton_iff.1 (hHk hy)
    have h1 : y * k ^ i = k ^ i * y := (hyk.pow_right i).eq
    rw [← h1]
    simp
  have hLn : ∀ g ∈ X, ∀ l ∈ H, g * l * g⁻¹ ∈ H := by
    intro g hg l hl
    obtain ⟨i, h, hh, rfl⟩ := hdec g hg
    have hmem : h * l * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hl) (H.inv_mem hh)
    have e1 : k ^ i * h * l * (k ^ i * h)⁻¹ = k ^ i * (h * l * h⁻¹) * (k ^ i)⁻¹ := by group
    rw [e1, hcomm i _ hmem]
    exact hmem
  have hcentle : X ⊓ Subgroup.centralizer (H : Set G) ≤ Subgroup.zpowers k := by
    rintro c ⟨hcX, hcH⟩
    obtain ⟨i, h, hh, rfl⟩ := hdec c hcX
    have hh1 : h = 1 := by
      have hcomm' : ∀ y ∈ H, y * h = h * y := by
        intro y hy
        have h1 := Subgroup.mem_centralizer_iff.1 hcH y hy
        have hyk : Commute y k := Subgroup.mem_centralizer_singleton_iff.1 (hHk hy)
        have h2 : y * k ^ i = k ^ i * y := (hyk.pow_right i).eq
        have h3 : k ^ i * (y * h) = k ^ i * (h * y) := by
          calc k ^ i * (y * h) = (k ^ i * y) * h := by rw [mul_assoc]
            _ = (y * k ^ i) * h := by rw [h2]
            _ = y * (k ^ i * h) := by rw [mul_assoc]
            _ = (k ^ i * h) * y := h1
            _ = k ^ i * (h * y) := by rw [mul_assoc]
        exact mul_left_cancel h3
      have hmem : (⟨h, hh⟩ : ↥H) ∈ Subgroup.center ↥H :=
        Subgroup.mem_center_iff.2 fun b => Subtype.ext (hcomm' b b.2)
      rw [hZ, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    rw [hh1, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers k) _
  have hKp : IsPGroup p ↥(Subgroup.zpowers k) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk, pow_one])
  have hcent : IsPGroup p ↥(X ⊓ Subgroup.centralizer (H : Set G)) := hKp.to_le hcentle
  have hLq : CFSG.Open.IsQuasisimple ↥H := tabMFive_quasisimple_of_simple_nonab hnab
  have hcoreH : GLAPPrimeCore p ↥H = ⊥ := glaPPrimeCore_eq_bot_of_simple hp hpH
  have hG' : Good (PSimple p H) :=
    hGood ↥H (PSimple p H) (pSimpleEquivSelf H hcoreH hZ).symm hG
  have hR' : Rk (PQuot p H) := hRk ↥H (PQuot p H) (pQuotEquivSelf H hcoreH).symm hR
  exact (shapeRkAt_of_normal_quasisimple hp hHk hLn hLq hpH hcent hG' hR').toWeak hp

end Shape

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
