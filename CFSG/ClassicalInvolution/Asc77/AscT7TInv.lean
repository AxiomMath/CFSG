module

public import CFSG.ClassicalInvolution.Asc77.AscT7TC5
public import CFSG.ClassicalInvolution.Asc77.AscT7TStar2
public import CFSG.ClassicalInvolution.Asc77.AscP1Strong
public import CFSG.ClassicalInvolution.Asc77.AscT7TOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7T

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ : G}

theorem perm_R_of_hyp (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) {X : Subgroup G} (hX : X = R ∨ X = R') :
    conjSub s X = R ∨ conjSub s X = R' := by
  have hΩ : HypOmegaMod p f Ω := hyp.std.setting.stand.hyp
  have hXmem : X ∈ RSet Ω := by rcases hX with rfl | rfl; exacts [hyp.hR.1, hyp.hR'.1]
  have hXS : X ≤ (S : Subgroup G) := by rcases hX with rfl | rfl; exacts [hyp.hR.2.2, hyp.hR'.2.2]
  have hmem : conjSub s X ∈ RSet Ω := RSet.conj hΩ.conjInvariant hXmem s
  have hle : conjSub s X ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : s * (s⁻¹ * x * s) * s⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hXS hx)) (Subgroup.inv_mem _ hs)
    simpa [mul_assoc] using h1
  exact hyp.hRS _ hmem hle


theorem conjSub_sup_of_hyp (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) : conjSub s (R ⊔ R') = R ⊔ R' := by
  have hne : R ≠ R' := T7ER.ne_of_hyp25 hyp
  rw [T7F2.conjSub_sup']
  rcases perm_R_of_hyp hyp hs (Or.inl rfl : R = R ∨ R = R') with h | h
  · have h' : conjSub s R' = R' := by
      rcases perm_R_of_hyp hyp hs (Or.inr rfl : R' = R ∨ R' = R') with h' | h'
      · exact absurd (conjSub_injective s (h.trans h'.symm)) hne
      · exact h'
    rw [h, h']
  · have h' : conjSub s R' = R := by
      rcases perm_R_of_hyp hyp hs (Or.inr rfl : R' = R ∨ R' = R') with h' | h'
      · exact h'
      · exact absurd (conjSub_injective s (h.trans h'.symm)) hne
    rw [h, h', sup_comm]

theorem conjSub_centralizer_of_hyp (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {s : G}
    (hs : s ∈ (S : Subgroup G)) :
    conjSub s ((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) =
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
  rw [T7F2.conjSub_inf_centralizer, conjSub_eq_self_of_mem hs, conjSub_sup_of_hyp hyp hs]

theorem z_mem_centralizer_of_hyp (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) :
    z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have h8 := (hΩ.isQuatSub_of_mem_RSet hp hyp.hR.1).eight_le
  have h8' := (hΩ.isQuatSub_of_mem_RSet hp hyp.hR'.1).eight_le
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hyp.hR.2.1 hRsyl.2.1 (by omega)
  have hzR' : z ∈ R' := mem_of_isUniqueInvolution_of_isPGroup hz' hyp.hR'.2.1 hR'syl.2.1 (by omega)
  have hle : R ⊔ R' ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (hyp.hR.2.1.trans (AscP1Nine3.le_centralizer_of_uniqueInvolution hz))
      (hyp.hR'.2.1.trans (AscP1Nine3.le_centralizer_of_uniqueInvolution hz'))
  refine ⟨hyp.hR.2.2 hzR, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  exact this


theorem exists_involution_not_zStar (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    (hne : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ≠
      Subgroup.zpowers z) :
    ∃ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      a * a = 1 ∧ a ≠ 1 ∧ a ≠ z ∧ z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
  set A := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA
  have hzA : z ∈ A := z_mem_centralizer_of_hyp hyp
  have hAS : A ≤ (S : Subgroup G) := inf_le_left
  by_contra hcon
  push Not at hcon
  apply hne
  refine c25_5_proved (p := p) (f := f) G Ω K K' W S R R' z t u₁ u₂ hyp A hzA hAS
    (fun s hs => conjSub_centralizer_of_hyp hyp hs) ?_
  intro a haA ha1
  by_contra hza
  have hA2 : IsPGroup 2 ↥(Subgroup.zpowers a) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (hAS haA))
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hA2) ⟨a, Subgroup.mem_zpowers a⟩
  have hao : orderOf a = 2 ^ m := by
    rw [← hm]; exact (Subgroup.orderOf_mk a (Subgroup.mem_zpowers a)).symm
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hao
    exact ha1 hao
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  set a' := a ^ (2 ^ m') with ha'
  have ha'sq : a' * a' = 1 := by
    rw [ha', ← pow_add, ← two_mul, ← pow_succ']
    have := pow_orderOf_eq_one a
    rwa [hao] at this
  have ha'1 : a' ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hao] at h1
    have h2 := Nat.le_of_dvd (by positivity) h1
    have h3 : 2 ^ m' < 2 ^ (m' + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have ha'A : a' ∈ A := A.pow_mem haA _
  have hle : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer ({a'} : Set G) := by
    intro x hx
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    exact ((show Commute x a from hx').pow_right (2 ^ m')).eq
  have hza' : z ∉ zStarOf (Subgroup.centralizer ({a'} : Set G)) := by
    intro h
    exact hza (mem_zStarOf_of_le hle h
      (Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS a (hAS haA)).symm))
  have ha'z : a' ≠ z := by
    intro h
    rw [h] at hza'
    exact hza' (mem_zStarOf_centralizer_self z)
  exact hza' (hcon a' ha'A ha'sq ha'1 ha'z)


theorem exists_nonfused_of_stronglyClosed (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {E : Subgroup G} (hES : E ≤ (S : Subgroup G)) (hE1 : E ≠ ⊥)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEcl : ∀ e ∈ E, ∀ c ∈ Subgroup.centralizer ({z} : Set G),
      c * e * c⁻¹ ∈ (S : Subgroup G) → c * e * c⁻¹ ∈ E) :
    ∃ e ∈ E, e ≠ 1 ∧ ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({e} : Set G) ∧
      ¬ ∃ c ∈ Subgroup.centralizer ({e} : Set G), c * z * c⁻¹ = g * z * g⁻¹ := by
  by_contra hcon
  push Not at hcon
  refine l17_8 (p := p) (f := f) G Ω K hyp.std.setting.stand S E hES hE1 hEab ⟨hES, ?_⟩
  intro e he g hg
  by_cases he1 : e = 1
  · rw [he1]; simp only [mul_one, mul_inv_cancel]; exact E.one_mem
  have hzc : (g * e * g⁻¹) * z = z * (g * e * g⁻¹) := hyp.hzS _ hg
  have hy : g⁻¹ * z * g ∈ Subgroup.centralizer ({e} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc g⁻¹ * z * g * e = g⁻¹ * (z * (g * e * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * e * g⁻¹) * z) * g := by rw [hzc]
      _ = e * (g⁻¹ * z * g) := by group
  have hy' : g⁻¹ * z * g⁻¹⁻¹ ∈ Subgroup.centralizer ({e} : Set G) := by simpa using hy
  obtain ⟨c, hc, hcz⟩ := hcon e he he1 g⁻¹ hy'
  have hc' : c * e = e * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcz' : c * z * c⁻¹ = g⁻¹ * z * g := by simpa using hcz
  have hh : g * c ∈ Subgroup.centralizer ({z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have : (g * c) * z * (g * c)⁻¹ = z := by
      calc (g * c) * z * (g * c)⁻¹ = g * (c * z * c⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hcz']
        _ = z := by group
    calc (g * c) * z = ((g * c) * z * (g * c)⁻¹) * (g * c) := by group
      _ = z * (g * c) := by rw [this]
  have hhe : (g * c) * e * (g * c)⁻¹ = g * e * g⁻¹ := by
    calc (g * c) * e * (g * c)⁻¹ = g * (c * e) * c⁻¹ * g⁻¹ := by group
      _ = g * (e * c) * c⁻¹ * g⁻¹ := by rw [hc']
      _ = g * e * g⁻¹ := by group
  have := hEcl e he (g * c) hh (by rw [hhe]; exact hg)
  rwa [hhe] at this

theorem c25_16_of_even_case {p f : ℕ} [Fact p.Prime] (h : Even f → C25_16 p f) : C25_16 p f :=
  (Nat.even_or_odd f).elim h c25_16_of_odd


variable (p f)

@[expose] def C25_11Z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z → z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))

variable {p f}

theorem c25_11_of_C25_11Z (h : C25_11Z p f) : C25_11 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  by_contra hne
  obtain ⟨a, haA, ha2, ha1, haz, hza⟩ := exists_involution_not_zStar hyp hne
  exact hza (h G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz)

theorem C25_11Z_of_c25_11 (h : C25_11 p f) : C25_11Z p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz
  exfalso
  rw [h G Ω K K' W S R R' z t u₁ u₂ hyp] at haA
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp haA
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have h1 : z ^ k = 1 ∨ z ^ k = z := by
    have hk0 := zpow_mod_orderOf z k
    have hord : orderOf z = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hz2) hyp.std.setting.hz.ne_one
    rw [hord] at hk0
    have hk' : z ^ (k % 2) = z ^ k := by simpa using hk0
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · left; rw [← hk', h0]; simp
    · right; rw [← hk', h0]; simp
  rcases h1 with h1 | h1
  · exact ha1 h1
  · exact haz h1

end T7T

end CFSG.ClassicalInvolution.Asc77
