module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.GH74.GLS.Stage2.Local.P27.FullStmt
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

section AbstractLift

variable {M : Type} [Group M] [Finite M]

theorem exists_lift_central (N : Subgroup M) [N.Normal] (hN : Odd (Nat.card N)) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (V X : Subgroup (M ⧸ N)) (hV : IsPGroup 2 ↥V) (hX : IsPGroup p ↥X)
    (hXV : X ≤ normalizer (V : Set (M ⧸ N))) (hcomm : ⁅V, X⁆ = V) (s : M ⧸ N)
    (hsV : s ∈ V) (hsc : ∀ w ∈ V, w * s = s * w) (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hXs : ∀ x ∈ X, x * s = s * x) :
    ∃ (V' X' : Subgroup M) (s' : M), IsPGroup 2 ↥V' ∧ IsPGroup p ↥X' ∧
      V'.map (QuotientGroup.mk' N) = V ∧ X'.map (QuotientGroup.mk' N) = X ∧ V' ⊓ N = ⊥ ∧
      X' ≤ normalizer (V' : Set M) ∧ ⁅V', X'⁆ = V' ∧ s' ∈ V' ∧ QuotientGroup.mk' N s' = s ∧
      s' * s' = 1 ∧ s' ≠ 1 ∧ (∀ w ∈ V', w * s' = s' * w) ∧ ∀ x ∈ X', x * s' = s' * x := by
  obtain ⟨V', X', hV'2, hX'p, hV'map, hX'map, hX'V', hV'N⟩ :=
    exists_two_p_lift N hN hp V X hV hX hXV
  set π := QuotientGroup.mk' N with hπ
  have hinj : ∀ a ∈ V', ∀ b ∈ V', π a = π b → a = b := by
    intro a ha b hb hab
    have hN1 : a⁻¹ * b ∈ N := by
      have : π (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp this
    have h1 : a⁻¹ * b ∈ V' ⊓ N := Subgroup.mem_inf.mpr ⟨V'.mul_mem (V'.inv_mem ha) hb, hN1⟩
    rw [hV'N, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.mp h1)
  have hker : ∀ a ∈ V', π a = 1 → a = 1 := fun a ha h1 => by
    simpa using hinj a ha 1 V'.one_mem (by rw [h1, map_one])
  obtain ⟨s', hs'V', hs'π⟩ : s ∈ V'.map π := by rw [hV'map]; exact hsV
  have hs'2 : s' * s' = 1 :=
    hker _ (V'.mul_mem hs'V' hs'V') (by rw [map_mul, hs'π]; exact hs2)
  have hs'1 : s' ≠ 1 := fun he => hs1 (by rw [← hs'π, he, map_one])
  refine ⟨V', X', s', hV'2, hX'p, hV'map, hX'map, hV'N, hX'V', ?_, hs'V', hs'π, hs'2, hs'1, ?_, ?_⟩
  ·
    have hle : ⁅V', X'⁆ ≤ V' := (Subgroup.le_normalizer_iff_commutator_le_left).mp hX'V'
    refine le_antisymm hle fun v hv => ?_
    have hmap : (⁅V', X'⁆).map π = V := by
      rw [Subgroup.map_commutator, hV'map, hX'map, hcomm]
    have : π v ∈ (⁅V', X'⁆).map π := by rw [hmap, ← hV'map]; exact ⟨v, hv, rfl⟩
    obtain ⟨c, hc, hcv⟩ := this
    have := hinj c (hle hc) v hv hcv
    rwa [← this]
  · intro w hw
    have hc : w * s' * w⁻¹ * s'⁻¹ ∈ V' := V'.mul_mem (V'.mul_mem (V'.mul_mem hw hs'V') (V'.inv_mem hw))
      (V'.inv_mem hs'V')
    have hπw : π w ∈ V := by rw [← hV'map]; exact ⟨w, hw, rfl⟩
    have h1 : w * s' * w⁻¹ * s'⁻¹ = 1 := by
      apply hker _ hc
      simp only [map_mul, map_inv, hs'π]
      have := hsc _ hπw
      calc π w * s * (π w)⁻¹ * s⁻¹ = (s * π w) * (π w)⁻¹ * s⁻¹ := by rw [← this]
        _ = 1 := by group
    calc w * s' = (w * s' * w⁻¹ * s'⁻¹) * (s' * w) := by group
      _ = s' * w := by rw [h1, one_mul]
  · intro x hx
    have hxn : x * s' * x⁻¹ ∈ V' := (mem_normalizer_iff.mp (hX'V' hx) s').mp hs'V'
    have hc : x * s' * x⁻¹ * s'⁻¹ ∈ V' := V'.mul_mem hxn (V'.inv_mem hs'V')
    have hπx : π x ∈ X := by rw [← hX'map]; exact ⟨x, hx, rfl⟩
    have h1 : x * s' * x⁻¹ * s'⁻¹ = 1 := by
      apply hker _ hc
      simp only [map_mul, map_inv, hs'π]
      have := hXs _ hπx
      calc π x * s * (π x)⁻¹ * s⁻¹ = (s * π x) * (π x)⁻¹ * s⁻¹ := by rw [← this]
        _ = 1 := by group
    calc x * s' = (x * s' * x⁻¹ * s'⁻¹) * (s' * x) := by group
      _ = s' * x := by rw [h1, one_mul]

end AbstractLift


section DihedralOrderFour

theorem dihedral_order_four_commute {P : Type*} [Group P] {k : ℕ} (e : P ≃* DihedralGroup k) {a b : P}
    (ha : orderOf a = 4) (hb : orderOf b = 4) : a * b = b * a := by
  have key : ∀ c : P, orderOf c = 4 → ∃ i : ZMod k, e c = DihedralGroup.r i := by
    intro c hc
    have h1 : orderOf (e c) = 4 := by rw [MulEquiv.orderOf_eq]; exact hc
    rcases hec : e c with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      rw [hec, DihedralGroup.orderOf_sr] at h1
      omega
  obtain ⟨i, hi⟩ := key a ha
  obtain ⟨j, hj⟩ := key b hb
  apply e.injective
  rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]

end DihedralOrderFour

section CentralLift

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_O2Of_conj {C : Subgroup G} {c y : G} (hc : c ∈ C) (hy : y ∈ O2Of C) :
    c * y * c⁻¹ ∈ O2Of C := by
  obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp hy
  have hn := (Stage1.Thm6.Prod.oResidual_normal 2 ↥C).conj_mem o ho ⟨c, hc⟩
  exact Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * o * ⟨c, hc⟩⁻¹, hn, by simp⟩

omit [Finite G] in
theorem mem_O2Of_of_odd {C : Subgroup G} {x : G} (hxC : x ∈ C) (hx : Nat.Coprime (orderOf x) 2) :
    x ∈ O2Of C := by
  refine Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, Subgroup.subset_closure ?_, rfl⟩
  show Nat.Coprime (orderOf (⟨x, hxC⟩ : ↥C)) 2
  rw [Subgroup.orderOf_mk]
  exact hx


theorem isCentralInvolution_of_lift (hFull : ∀ x : G, IsNonCentralInvolution x → P27.FullG x)
    (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) [H₁.Normal] (hodd : Odd (Nat.card H₁)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (V X : Subgroup (Sec H₀ H₁)) (hV : IsPGroup 2 ↥V) (hX : IsPGroup p ↥X)
    (hXV : X ≤ normalizer (V : Set (Sec H₀ H₁))) (hcomm : ⁅V, X⁆ = V) (s u v : Sec H₀ H₁) (hsV : s ∈ V)
    (hsc : ∀ w ∈ V, w * s = s * w) (hs2 : s * s = 1) (hs1 : s ≠ 1) (hXs : ∀ x ∈ X, x * s = s * x)
    (huV : u ∈ V) (hvV : v ∈ V) (hu4 : orderOf u = 4) (hv4 : orderOf v = 4) (huv : u * v ≠ v * u) :
    ∃ (s' : G) (hs' : s' ∈ H₀), IsCentralInvolution s' ∧ (QuotientGroup.mk ⟨s', hs'⟩ : Sec H₀ H₁) = s := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨V', X', s', hV'2, hX'p, hV'map, hX'map, hV'N, hX'V', hcomm', hs'V', hs'π, hs'2, hs'1, hs'c,
    hs'X⟩ := exists_lift_central H₁ hodd hp2 V X hV hX hXV hcomm s hsV hsc hs2 hs1 hXs
  refine ⟨(s' : G), s'.2, ?_, hs'π⟩
  by_contra hnc
  have hs2G : orderOf (s' : G) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      simpa using congrArg Subtype.val hs'2
    · exact fun he => hs'1 (Subtype.ext he)
  have hF := hFull (s' : G) ⟨hs2G, hnc⟩
  set C : Subgroup G := centralizer ({(s' : G)} : Set G) with hC
  set VG : Subgroup G := V'.map H₀.subtype with hVG
  set XG : Subgroup G := X'.map H₀.subtype with hXG
  have hmemC : ∀ a : ↥H₀, a * s' = s' * a → (a : G) ∈ C := fun a ha => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg Subtype.val ha
  have hXO : ∀ x ∈ X', (x : G) ∈ O2Of C := by
    intro x hx
    refine mem_O2Of_of_odd (hmemC x (hs'X x hx)) ?_
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hX'p) ⟨x, hx⟩
    have h1 : orderOf (x : G) = p ^ k := by
      rw [Subgroup.orderOf_coe, ← Subgroup.orderOf_mk x hx]
      exact hk
    rw [h1]
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hVO : ∀ w ∈ V', (w : G) ∈ O2Of C := by
    have hle : V' ≤ (O2Of C).comap H₀.subtype := by
      rw [← hcomm']
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have haC : (a : G) ∈ C := hmemC a (hs'c a ha)
      have hbO : (b : G) ∈ O2Of C := hXO b hb
      show ((⁅a, b⁆ : ↥H₀) : G) ∈ O2Of C
      have e : (((⁅a, b⁆ : ↥H₀)) : G) = ((a : G) * (b : G) * (a : G)⁻¹) * ((b : G))⁻¹ := by
        simp [commutatorElement_def]
      rw [e]
      exact (O2Of C).mul_mem (mem_O2Of_conj haC hbO) ((O2Of C).inv_mem hbO)
    exact fun w hw => hle hw
  have hVsub : IsPGroup 2 ↥(VG.subgroupOf (O2Of C)) := by
    have hVGO : VG ≤ O2Of C := by
      rintro _ ⟨w, hw, rfl⟩
      exact hVO w hw
    exact (hV'2.map H₀.subtype).of_equiv (Subgroup.subgroupOfEquivOfLe hVGO).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hVsub.exists_le_sylow
  obtain ⟨m, k, -, -, ⟨e⟩⟩ := hF P
  have hlift : ∀ a : Sec H₀ H₁, a ∈ V → orderOf a = 4 →
      ∃ a' : ↥H₀, a' ∈ V' ∧ QuotientGroup.mk' H₁ a' = a ∧ orderOf a' = 4 := by
    intro a ha hao
    have haV : a ∈ V'.map (QuotientGroup.mk' H₁) := by rw [hV'map]; exact ha
    obtain ⟨a', ha'V', ha'π⟩ := haV
    refine ⟨a', ha'V', ha'π, ?_⟩
    have h1 : 4 ∣ orderOf a' := by
      rw [← hao, ← ha'π]
      exact orderOf_map_dvd (QuotientGroup.mk' H₁) a'
    have h2 : orderOf a' ∣ 4 := by
      apply orderOf_dvd_of_pow_eq_one
      have hmem : a' ^ 4 ∈ V' ⊓ H₁ := by
        refine Subgroup.mem_inf.mpr ⟨V'.pow_mem ha'V' 4, ?_⟩
        have : QuotientGroup.mk' H₁ (a' ^ 4) = 1 := by
          rw [map_pow, ha'π, ← hao]
          exact pow_orderOf_eq_one a
        exact (QuotientGroup.eq_one_iff _).mp this
      rw [hV'N, Subgroup.mem_bot] at hmem
      exact hmem
    exact Nat.dvd_antisymm h2 h1
  obtain ⟨u', hu'V', hu'π, hu'4⟩ := hlift u huV hu4
  obtain ⟨v', hv'V', hv'π, hv'4⟩ := hlift v hvV hv4
  have hP' : ∀ a : ↥H₀, ∀ ha : a ∈ V', (⟨(a : G), hVO a ha⟩ : ↥(O2Of C)) ∈ (P : Subgroup ↥(O2Of C)) := by
    intro a ha
    exact hP (Subgroup.mem_subgroupOf.mpr ⟨a, ha, rfl⟩)
  have hord : ∀ (a : ↥H₀) (ha : a ∈ V'), orderOf a = 4 →
      orderOf (⟨⟨(a : G), hVO a ha⟩, hP' a ha⟩ : ↥P) = 4 := by
    intro a ha hao
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    exact hao
  have hcommP := dihedral_order_four_commute e (hord u' hu'V' hu'4) (hord v' hv'V' hv'4)
  have hcomm1 : (u' : G) * v' = v' * u' := by
    have := congrArg (fun t : ↥P => (((t : ↥(O2Of C)) : G))) hcommP
    simpa using this
  have hcomm2 : u' * v' = v' * u' := Subtype.ext hcomm1
  apply huv
  rw [← hu'π, ← hv'π, ← map_mul, ← map_mul, hcomm2]

end CentralLift

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
