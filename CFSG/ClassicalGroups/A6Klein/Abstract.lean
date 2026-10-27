module

public import CFSG.GroupTheory.InvariantSubgroup
public import CFSG.ClassicalGroups.A6Klein.Code
public import CFSG.CGT.Timmesfeld75.WCBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalGroups.A6Klein

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.A6Facts.Core
open CFSG.CGT.Timmesfeld75 CFSG.GroupTheory

theorem pair_mem (g : K0) : (kap g, kap g⁻¹) ∈ pslPairs :=
  List.mem_map.mpr ⟨kap g, kap_mem g, by rw [kap_inv]⟩

theorem mem_pslPairs {p : List ℕ × List ℕ} (hp : p ∈ pslPairs) :
    ∃ g : K0, p = (kap g, kap g⁻¹) := by
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hp
  obtain ⟨g, rfl⟩ := exists_kap hC
  exact ⟨g, by rw [kap_inv]⟩

theorem inV_kap_iff (a b u : K0) :
    inV (kap a) (kap b) (kap u) = true ↔ u = 1 ∨ u = a ∨ u = b ∨ u = a * b := by
  simp only [inV, Bool.or_eq_true, beq_iff_eq, ← kap_one, ← kap_mul, kap_injective.eq_iff]
  tauto

theorem cjp_kap (g v : K0) : cjp (kap g, kap g⁻¹) (kap v) = kap (g * v * g⁻¹) := by
  simp only [cjp, kap_mul]

def kleinSub (a s : K0) (ha : a * a = 1) (hs : s * s = 1) (has : a * s = s * a) :
    Subgroup K0 where
  carrier := {1, a, s, a * s}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have e1 : a * (a * s) = s := by rw [← mul_assoc, ha, one_mul]
    have e2 : s * (a * s) = a := by rw [← mul_assoc, ← has, mul_assoc, hs, mul_one]
    have e3 : a * s * a = s := by rw [has, mul_assoc, ha, mul_one]
    have e4 : a * s * s = a := by rw [mul_assoc, hs, mul_one]
    have e5 : a * s * (a * s) = 1 := by rw [mul_assoc, e2, ha]
    have key : ∀ x y : K0, (x = 1 ∨ x = a ∨ x = s ∨ x = a * s) →
        (y = 1 ∨ y = a ∨ y = s ∨ y = a * s) →
        (x * y = 1 ∨ x * y = a ∨ x * y = s ∨ x * y = a * s) := by
      rintro x y (hx | hx | hx | hx) (hy | hy | hy | hy) <;> rw [hx, hy] <;>
        simp [ha, hs, has.symm, e1, e2, e3, e4, e5]
    exact fun {x y} hx hy => key x y hx hy
  inv_mem' := by
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    rintro x (hx | hx | hx | hx)
    · rw [hx]; simp
    · rw [hx, hai]; simp
    · rw [hx, hsi]; simp
    · rw [hx, mul_inv_rev, hai, hsi, ← has]; simp

theorem mem_kleinSub {a s : K0} {ha : a * a = 1} {hs : s * s = 1} {has : a * s = s * a} {x : K0} :
    x ∈ kleinSub a s ha hs has ↔ x = 1 ∨ x = a ∨ x = s ∨ x = a * s := Iff.rfl

theorem mem_normalizer_of_gens {U : Subgroup K0} {a s σ : K0}
    (hU : ∀ y, y ∈ U ↔ y = 1 ∨ y = a ∨ y = s ∨ y = a * s) (hσ : σ * σ = 1)
    (h1 : σ * a * σ ∈ U) (h2 : σ * s * σ ∈ U) :
    σ ∈ Subgroup.normalizer (U : Set K0) := by
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have fwd : ∀ y ∈ U, σ * y * σ ∈ U := by
    intro y hy
    rcases (hU y).mp hy with hy | hy | hy | hy
    · rw [hy, mul_one, hσ]; exact U.one_mem
    · rw [hy]; exact h1
    · rw [hy]; exact h2
    · rw [hy]
      have : σ * (a * s) * σ = (σ * a * σ) * (σ * s * σ) := by
        calc σ * (a * s) * σ = σ * a * (σ * σ) * s * σ := by simp only [hσ, mul_one, mul_assoc]
          _ = (σ * a * σ) * (σ * s * σ) := by simp only [mul_assoc]
      rw [this]
      exact U.mul_mem h1 h2
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [hσi]
  constructor
  · exact fun hh => fwd h hh
  · intro hh
    have := fwd _ hh
    have e : σ * (σ * h * σ) * σ = h := by
      calc σ * (σ * h * σ) * σ = (σ * σ) * h * (σ * σ) := by simp only [mul_assoc]
        _ = h := by rw [hσ]; simp
    rwa [e] at this

theorem mem_normalizer_conj_iff {V : Subgroup K0} {g v : K0} :
    v ∈ Subgroup.normalizer ((conjSubgroup g V : Subgroup K0) : Set K0) ↔
      g⁻¹ * v * g ∈ Subgroup.normalizer (V : Set K0) := by
  rw [mem_normalizer_iff_conjSubgroup_eq, mem_normalizer_iff_conjSubgroup_eq,
    conjSubgroup_conjSubgroup]
  constructor
  · intro h
    have := congrArg (conjSubgroup g⁻¹) h
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one, ← mul_assoc] at this
    exact this
  · intro h
    have := congrArg (conjSubgroup g) h
    rw [conjSubgroup_conjSubgroup] at this
    have e : g * (g⁻¹ * v * g) = v * g := by group
    rwa [e] at this

theorem kleinC_spec {a b : K0} (h : kleinC (kap a) (kap b) = true) :
    a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧ a * b = b * a := by
  simp only [kleinC, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun e => h1 (by rw [e, kap_one]), fun e => h2 (by rw [e, kap_one]),
    fun e => h3 (by rw [e]), ?_, ?_, ?_⟩
  · apply kap_injective
    rw [kap_mul, h4, kap_one]
  · apply kap_injective
    rw [kap_mul, h5, kap_one]
  · apply kap_injective
    rw [kap_mul, kap_mul]
    exact h6

theorem goodSc_spec {a b s : K0} (h : goodSc (kap a) (kap b) (kap s) = true) :
    s ≠ 1 ∧ s * s = 1 ∧ a * s = s * a := by
  simp only [goodSc, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := h
  refine ⟨fun e => h1 (by rw [e, kap_one]), ?_, ?_⟩
  · apply kap_injective
    rw [kap_mul, h2, kap_one]
  · apply kap_injective
    rw [kap_mul, kap_mul]
    exact h3

theorem checkKlein_unpack {A B : List ℕ} (h : checkKlein A B = true) :
    (∃ Sc ∈ pslLit, goodSc A B Sc = true ∧ condIV A B Sc = true ∧ condS A Sc = true) ∧
      condX A B = true := by
  unfold checkKlein at h
  rw [Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨⟨Sc, hSc, hS⟩, hX⟩ := h
  rw [Bool.and_eq_true, Bool.and_eq_true] at hS
  exact ⟨⟨Sc, hSc, hS.1.1, hS.1.2, hS.2⟩, hX⟩

theorem contains_kleinList_iff (a s y : K0) :
    [cid, kap a, kap s, cmul (kap a) (kap s)].contains (kap y) = true ↔
      y = 1 ∨ y = a ∨ y = s ∨ y = a * s := by
  simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false, ← kap_one,
    ← kap_mul, kap_injective.eq_iff]

theorem invU_kap_iff (a s σ : K0) :
    invU (kap a) (kap s) (kap σ) = true ↔
      (σ * a * σ = 1 ∨ σ * a * σ = a ∨ σ * a * σ = s ∨ σ * a * σ = a * s) ∧
      (σ * s * σ = 1 ∨ σ * s * σ = a ∨ σ * s * σ = s ∨ σ * s * σ = a * s) := by
  have e1 : cmul (cmul (kap σ) (kap a)) (kap σ) = kap (σ * a * σ) := by simp only [kap_mul]
  have e2 : cmul (cmul (kap σ) (kap s)) (kap σ) = kap (σ * s * σ) := by simp only [kap_mul]
  simp only [invU, Bool.and_eq_true, e1, e2, contains_kleinList_iff]

theorem nrmInv_kap_iff (a b n : K0) :
    nrmInv (kap a) (kap b) (kap n) = true ↔
      (n * a * n = 1 ∨ n * a * n = a ∨ n * a * n = b ∨ n * a * n = a * b) ∧
      (n * b * n = 1 ∨ n * b * n = a ∨ n * b * n = b ∨ n * b * n = a * b) := by
  have e1 : cmul (cmul (kap n) (kap a)) (kap n) = kap (n * a * n) := by simp only [kap_mul]
  have e2 : cmul (cmul (kap n) (kap b)) (kap n) = kap (n * b * n) := by simp only [kap_mul]
  simp only [nrmInv, Bool.and_eq_true, e1, e2, inV_kap_iff]

theorem condX_abs {a b : K0} (V : Subgroup K0)
    (hV : ∀ v, v ∈ V ↔ v = 1 ∨ v = a ∨ v = b ∨ v = a * b)
    (haa : a * a = 1) (hX : condX (kap a) (kap b) = true) :
    ∃ x : K0, a ∈ Subgroup.normalizer ((conjSubgroup x V : Subgroup K0) : Set K0) ∧
      ∃ z ∈ V ⊔ conjSubgroup x V, z * z * z = 1 ∧ z ≠ 1 := by
  have haV : a ∈ V := (hV a).mpr (Or.inr (Or.inl rfl))
  have hbV : b ∈ V := (hV b).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have habV : a * b ∈ V := (hV _).mpr (Or.inr (Or.inr (Or.inr rfl)))
  unfold condX at hX
  obtain ⟨X, hXmem, hXc⟩ := List.any_eq_true.mp hX
  obtain ⟨x, rfl⟩ := mem_pslPairs hXmem
  rw [Bool.and_eq_true] at hXc
  obtain ⟨hnrm, hz⟩ := hXc
  obtain ⟨v, hv, hz⟩ := List.any_eq_true.mp hz
  obtain ⟨w, hw, hz⟩ := List.any_eq_true.mp hz
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hz
  set n := x⁻¹ * a * x with hn_def
  have hnn : n * n = 1 := by
    rw [hn_def]
    calc x⁻¹ * a * x * (x⁻¹ * a * x) = x⁻¹ * (a * a) * x := by group
      _ = 1 := by rw [haa]; group
  have hni : n⁻¹ = n := inv_eq_of_mul_eq_one_right hnn
  have e : cmul (cmul (kap x, kap x⁻¹).2 (kap a)) (kap x, kap x⁻¹).1 = kap n := by
    simp only [hn_def, kap_mul]
  have hnrm' : nrmInv (kap a) (kap b) (kap n) = true := by rw [← e]; exact hnrm
  rw [nrmInv_kap_iff] at hnrm'
  have h1 : n * a * n ∈ V := (hV _).mpr hnrm'.1
  have h2 : n * b * n ∈ V := (hV _).mpr hnrm'.2
  have hnN : n ∈ Subgroup.normalizer (V : Set K0) :=
    mem_normalizer_of_gens hV hnn h1 h2
  refine ⟨x, ?_, ?_⟩
  · rw [mem_normalizer_conj_iff]
    exact hnN
  ·
    have hv' : ∃ v' ∈ V, kap v' = v := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨a, haV, rfl⟩
      · exact ⟨b, hbV, rfl⟩
      · exact ⟨a * b, habV, by rw [kap_mul]⟩
    have hw' : ∃ w' ∈ V, kap w' = w := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨a, haV, rfl⟩
      · exact ⟨b, hbV, rfl⟩
      · exact ⟨a * b, habV, by rw [kap_mul]⟩
    obtain ⟨v', hv'V, rfl⟩ := hv'
    obtain ⟨w', hw'V, rfl⟩ := hw'
    set z := v' * (x * w' * x⁻¹) with hz_def
    have hkz : cmul (kap v') (cjp (kap x, kap x⁻¹) (kap w')) = kap z := by
      simp only [cjp_kap, hz_def, kap_mul]
    rw [hkz] at hz
    obtain ⟨hz3, hz1⟩ := hz
    refine ⟨z, ?_, ?_, ?_⟩
    · refine Subgroup.mul_mem_sup hv'V ?_
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hw'V
    · apply kap_injective
      rw [kap_mul, kap_mul, kap_one]
      exact hz3
    · intro hz1'
      apply hz1
      rw [hz1', kap_one]

theorem exists_inv_data_of_check {a b : K0} (V : Subgroup K0)
    (hV : ∀ v, v ∈ V ↔ v = 1 ∨ v = a ∨ v = b ∨ v = a * b)
    (hk : kleinC (kap a) (kap b) = true) (hc : checkKlein (kap a) (kap b) = true) :
    ∃ (x : K0) (Λ : Subgroup K0), ¬ IsPGroup 2 ↥(V ⊔ conjSubgroup x V) ∧
      conjSubgroup x V ≤ Λ ∧ Λ ≠ ⊤ ∧
      ∀ α : MulAut K0, (∀ v ∈ V, α v = v) → Λ.map α.toMonoidHom ≤ Λ := by
  obtain ⟨ha1, hb1, hab, haa, hbb, hcomm⟩ := kleinC_spec hk
  obtain ⟨⟨Sc, hSc, hgood, hIV, hS⟩, hX⟩ := checkKlein_unpack hc
  obtain ⟨s, rfl⟩ := exists_kap hSc
  obtain ⟨hs1, hss, has⟩ := goodSc_spec hgood
  set U := kleinSub a s haa hss has with hUdef
  have hUmem : ∀ y, y ∈ U ↔ y = 1 ∨ y = a ∨ y = s ∨ y = a * s := fun y => mem_kleinSub
  have haV : a ∈ V := (hV a).mpr (Or.inr (Or.inl rfl))
  have hbV : b ∈ V := (hV b).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have haU : a ∈ U := (hUmem a).mpr (Or.inr (Or.inl rfl))
  have hsU : s ∈ U := (hUmem s).mpr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨x, hxnrm, z, hzV, hz3, hz1⟩ := condX_abs V hV haa hX
  have hLam : ∀ g : K0, g⁻¹ * a * g ∈ Subgroup.normalizer (V : Set K0) →
      g * a * g⁻¹ ∈ Subgroup.normalizer (U : Set K0) ∧
        g * b * g⁻¹ ∈ Subgroup.normalizer (U : Set K0) := by
    intro g hn
    set n := g⁻¹ * a * g with hn_def
    have hnn : n * n = 1 := by
      rw [hn_def]
      calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
        _ = 1 := by rw [haa]; group
    have hni : n⁻¹ = n := inv_eq_of_mul_eq_one_right hnn
    have h1 : n * a * n ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp hn a).mp haV
      rwa [hni] at this
    have h2 : n * b * n ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp hn b).mp hbV
      rwa [hni] at this
    have hnrm : nrmInv (kap a) (kap b) (kap n) = true := by
      rw [nrmInv_kap_iff]
      exact ⟨(hV _).mp h1, (hV _).mp h2⟩
    have hp := List.all_eq_true.mp hIV (kap g, kap g⁻¹) (pair_mem g)
    have e : cmul (cmul (kap g, kap g⁻¹).2 (kap a)) (kap g, kap g⁻¹).1 = kap n := by
      simp only [hn_def, kap_mul]
    simp only [e, hnrm, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hp
    obtain ⟨hpa, hpb⟩ := hp
    rw [cjp_kap, invU_kap_iff] at hpa
    rw [cjp_kap, invU_kap_iff] at hpb
    have hgaa : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by
      calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
        _ = 1 := by rw [haa]; group
    have hgbb : (g * b * g⁻¹) * (g * b * g⁻¹) = 1 := by
      calc (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
        _ = 1 := by rw [hbb]; group
    exact ⟨mem_normalizer_of_gens hUmem hgaa ((hUmem _).mpr hpa.1) ((hUmem _).mpr hpa.2),
      mem_normalizer_of_gens hUmem hgbb ((hUmem _).mpr hpb.1) ((hUmem _).mpr hpb.2)⟩
  have hSne : Subgroup.normalizer (U : Set K0) ≠ ⊤ := by
    unfold condS at hS
    obtain ⟨N, hN, hNc⟩ := List.any_eq_true.mp hS
    obtain ⟨n, rfl⟩ := mem_pslPairs hN
    intro htop
    have hn : n ∈ Subgroup.normalizer (U : Set K0) := by rw [htop]; exact Subgroup.mem_top n
    have h1 : n * a * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hn a).mp haU
    have h2 : n * s * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hn s).mp hsU
    have h1' := (contains_kleinList_iff a s _).mpr ((hUmem _).mp h1)
    have h2' := (contains_kleinList_iff a s _).mpr ((hUmem _).mp h2)
    rw [← cjp_kap] at h1' h2'
    rw [Bool.not_eq_true'] at hNc
    rw [h1', h2'] at hNc
    exact absurd hNc (by decide)
  refine ⟨x, invGroup V (Subgroup.zpowers a), ?_, ?_, ?_, ?_⟩
  · intro h2
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (⟨z, hzV⟩ : ↥(V ⊔ conjSubgroup x V)) = 3 := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        simpa [pow_three'] using hz3
      · intro h
        exact hz1 (by simpa using congrArg Subtype.val h)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h2 ⟨z, hzV⟩
    rw [hord] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ dvd_refl 3
    have h4 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  · exact le_invGroup ⟨x, rfl⟩ ((Subgroup.zpowers_le).mpr hxnrm)
  · intro htop
    apply hSne
    rw [eq_top_iff]
    have hΛS : invGroup V (Subgroup.zpowers a) ≤ Subgroup.normalizer (U : Set K0) := by
      refine iSup₂_le fun W hW => ?_
      obtain ⟨⟨g, rfl⟩, hEW⟩ := hW
      have haN : a ∈ Subgroup.normalizer ((conjSubgroup g V : Subgroup K0) : Set K0) :=
        hEW (Subgroup.mem_zpowers a)
      obtain ⟨hga, hgb⟩ := hLam g (mem_normalizer_conj_iff.mp haN)
      intro w hw
      rw [mem_conjSubgroup] at hw
      have hw' : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
      rw [hw']
      rcases (hV _).mp hw with h | h | h | h
      · rw [h, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [h]; exact hga
      · rw [h]; exact hgb
      · rw [h]
        have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ hga hgb
    rw [htop] at hΛS
    exact hΛS
  · exact fun α hα => invGroup_map_le V _ ((Subgroup.zpowers_le).mpr haV) α hα

end CFSG.ClassicalGroups.A6Klein
