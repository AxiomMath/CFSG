module

public import CFSG.GroupTheory.LocalCores.Components
public import TauCeti.GroupTheory.FixedSubgroup

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {V : Type*} [Group V] {X : Type*} [Group X]

private lemma mapsTo_zpow {ρ : X →* MulAut V} [Finite V] {g : X} {S : Subgroup V}
    (hS : ∀ v ∈ S, ρ g v ∈ S) (z : ℤ) : ∀ v ∈ S, (ρ g ^ z) v ∈ S := by
  have hmap : Set.MapsTo (fun v => ρ g v) (S : Set V) S := hS
  have hle : S.map (ρ g).toMonoidHom ≤ S := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨v, hv, rfl⟩
    exact hS v hv
  have heq : S.map (ρ g).toMonoidHom = S := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (ρ g).injective]
  have hinv : Set.MapsTo (fun v => (ρ g)⁻¹ v) (S : Set V) S := by
    intro v hv
    have hv' : v ∈ S.map (ρ g).toMonoidHom := by rw [heq]; exact hv
    rcases Subgroup.mem_map.mp hv' with ⟨w, hw, hwv⟩
    have hvw : (ρ g)⁻¹ v = w := by
      rw [← hwv]
      exact MulEquiv.symm_apply_apply (ρ g) w
    show (ρ g)⁻¹ v ∈ S
    rw [hvw]
    exact hw
  have hP : ∀ z : ℤ, Set.MapsTo (fun v => (ρ g ^ z) v) (S : Set V) S := by
    intro z
    refine zpow_induction_left (g := ρ g)
      (P := fun a => Set.MapsTo (fun v => a v) (S : Set V) S) ?_ ?_ ?_ z
    · intro v hv
      simpa using hv
    · intro a ha v hv
      exact hmap (ha hv)
    · intro a ha v hv
      exact hinv (ha hv)
  exact hP z

private lemma card_modEq_card_inf_fixedSubgroup {ρ : X →* MulAut V} [Finite V]
    {p m : ℕ} [Fact p.Prime] {g : X} (hg : g ^ p ^ m = 1) {S : Subgroup V}
    (hS : ∀ v ∈ S, ρ g v ∈ S) :
    Nat.card S ≡ Nat.card ↥(S ⊓ TauCeti.fixedSubgroup (ρ g).toMonoidHom) [MOD p] := by
  classical
  let H := Subgroup.zpowers g
  have hcardH : Nat.card H ∣ p ^ m := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr hg
  have hH : IsPGroup p H := IsPGroup.of_card_dvd_pow hcardH
  have hinv : ∀ h : H, ∀ v ∈ S, ρ (h : X) v ∈ S := by
    intro h v hv
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp h.2
    rw [← hz, map_zpow]
    exact mapsTo_zpow hS z v hv
  letI : MulAction H S :=
    { smul := fun h v => ⟨ρ (h : X) v.1, hinv h v.1 v.2⟩
      one_smul := by
        intro v
        ext
        show ρ ((1 : H) : X) v.1 = v.1
        simp
      mul_smul := by
        intro h1 h2 v
        ext
        show ρ ((h1 * h2 : H) : X) v.1 = ρ (h1 : X) (ρ (h2 : X) v.1)
        rw [Subgroup.coe_mul, map_mul]
        rfl }
  have hmod : Nat.card S ≡ Nat.card (MulAction.fixedPoints H S) [MOD p] :=
    hH.card_modEq_card_fixedPoints S
  have hfix : Nat.card (MulAction.fixedPoints H S) =
      Nat.card ↥(S ⊓ TauCeti.fixedSubgroup (ρ g).toMonoidHom) := by
    apply Nat.card_congr
    refine
      { toFun := fun v => ⟨v.1.1, ⟨v.1.2, ?_⟩⟩
        invFun := fun w => ⟨⟨w.1, w.2.1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · exact congrArg Subtype.val
        ((MulAction.mem_fixedPoints.mp v.2) ⟨g, Subgroup.mem_zpowers g⟩)
    · rw [MulAction.mem_fixedPoints]
      intro h
      apply Subtype.ext
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp h.2
      show ρ (h : X) w.1 = w.1
      rw [← hz, map_zpow]
      have hw : w.1 ∈ MulAction.fixedBy V (ρ g) := by
        show (ρ g) • w.1 = w.1
        rw [MulAut.smul_def]
        exact (TauCeti.mem_fixedSubgroup (F := (ρ g).toMonoidHom)).mp w.2.2
      exact MulAction.mem_fixedBy_zpow hw z
    · intro v
      rfl
    · intro w
      rfl
  rw [hfix] at hmod
  exact hmod

private def diffHom [IsMulCommutative V] (ρ : X →* MulAut V) (a : X) : V →* V where
  toFun v := ρ a v * v⁻¹
  map_one' := by simp
  map_mul' v w := by
    show ρ a (v * w) * (v * w)⁻¹ = ρ a v * v⁻¹ * (ρ a w * w⁻¹)
    rw [map_mul, mul_inv_rev]
    ac_rfl

private lemma diffHom_apply [IsMulCommutative V] (ρ : X →* MulAut V) (a : X) (v : V) :
    diffHom ρ a v = ρ a v * v⁻¹ := rfl

private lemma diffHom_ker [IsMulCommutative V] (ρ : X →* MulAut V) (a : X) :
    (diffHom ρ a).ker = TauCeti.fixedSubgroup (ρ a).toMonoidHom := by
  ext v
  rw [MonoidHom.mem_ker, TauCeti.mem_fixedSubgroup, diffHom_apply]
  constructor
  · intro h
    have := congrArg (· * v) h
    simpa [mul_assoc] using this
  · intro h
    change ρ a v = v at h
    rw [h, mul_inv_cancel]

private lemma diffHom_comm [IsMulCommutative V] {ρ : X →* MulAut V} {a g : X}
    (h : a * g = g * a) (v : V) :
    ρ g (diffHom ρ a v) = diffHom ρ a (ρ g v) := by
  have hcomm : ρ a * ρ g = ρ g * ρ a := by rw [← map_mul, ← map_mul, h]
  rw [diffHom_apply, diffHom_apply, map_mul, map_inv]
  have h1 : ρ g (ρ a v) = ρ a (ρ g v) := by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, hcomm]
  rw [h1]

private lemma diffHom_range_inf_fixedSubgroup [IsMulCommutative V] {ρ : X →* MulAut V} {a : X}
    (hexp : ∀ v : V, v ^ 2 = 1) (ha : a ^ 11 = 1) :
    (diffHom ρ a).range ⊓ TauCeti.fixedSubgroup (ρ a).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  obtain ⟨hwU, hwC⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hwU
  have hwdef : w = ρ a v * v⁻¹ := by rw [← hv]; rfl
  have hwfix : ρ a w = w := (TauCeti.mem_fixedSubgroup (F := (ρ a).toMonoidHom)).mp hwC
  have hav : ρ a v = w * v := by
    rw [hwdef, mul_assoc, inv_mul_cancel, mul_one]
  have hpow : ∀ n : ℕ, ρ (a ^ n) v = w ^ n * v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul, map_pow, hwfix, hav, pow_succ,
        mul_assoc]
  have h11 : w ^ 11 = 1 := by
    have h := hpow 11
    rw [ha, map_one] at h
    rw [MulAut.one_apply] at h
    exact mul_right_cancel_iff.mp (by rw [one_mul]; exact h.symm)
  have h2 : w ^ 2 = 1 := hexp w
  have hdvd : orderOf w ∣ 1 := by
    have h1 : orderOf w ∣ 11 := orderOf_dvd_iff_pow_eq_one.mpr h11
    have h2' : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have h := Nat.dvd_gcd h1 h2'
    have hg : Nat.gcd 11 2 = 1 := by decide
    rwa [hg] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem exists_ne_one_forall_fixed {V : Type*} [Group V] (hV : IsElementaryAbelian 2 V)
    (hcard : Nat.card V = 2 ^ 20) {X : Type*} [Group X] [Finite X] {ρ : X →* MulAut V}
    (hρ : Function.Injective ρ) {K : Subgroup X} (hK : IsQuasisimple K) {a : X}
    (ha : ∀ k ∈ K, a * k = k * a) (ha11 : orderOf a = 11) {b : X} (hb : b ∈ K)
    (hb7 : ∃ n : ℕ, b ^ 7 ^ n = 1) (hbK : ∃ k ∈ K, b * k ≠ k * b) :
    ∃ v : V, v ≠ 1 ∧ ∀ k ∈ K, ρ k v = v := by
  classical
  haveI := hV
  haveI hVfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI h11p : Fact (Nat.Prime 11) := ⟨by decide⟩
  haveI h7p : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hexp : ∀ v : V, v ^ 2 = 1 := fun v =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 V) v
  have hpow : ∀ S : Subgroup V, ∃ k, Nat.card S = 2 ^ k := by
    intro S
    exact (IsPGroup.iff_card.mp ((IsElementaryAbelian.isPGroup 2 V).to_subgroup S)).imp
      fun k hk => hk
  have hpow_le : ∀ S : Subgroup V, ∀ k, Nat.card S = 2 ^ k → k ≤ 20 := by
    intro S k hk
    have hdvd : 2 ^ k ∣ 2 ^ 20 := by
      rw [← hk, ← hcard]
      exact Subgroup.card_subgroup_dvd_card S
    have hle : 2 ^ k ≤ 2 ^ 20 := Nat.le_of_dvd (by positivity) hdvd
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  have ha_pow : a ^ 11 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [ha11])
  obtain ⟨k, hk⟩ : ∃ k, Nat.card (TauCeti.fixedSubgroup (ρ a).toMonoidHom) = 2 ^ k := hpow _
  have hk20 : k ≤ 20 := hpow_le _ k hk
  have hmodCa : Nat.card V ≡ Nat.card (TauCeti.fixedSubgroup (ρ a).toMonoidHom) [MOD 11] := by
    have h := card_modEq_card_inf_fixedSubgroup (ρ := ρ) (p := 11) (m := 1) (g := a)
      (S := ⊤) (by rw [pow_one]; exact ha_pow) (fun v _ => Subgroup.mem_top (ρ a v))
    simpa using h
  have hk_cases : k = 0 ∨ k = 10 ∨ k = 20 := by
    have hmod : 2 ^ k % 11 = 1 := by
      have h := hmodCa
      rw [hcard, hk] at h
      change 2 ^ 20 % 11 = 2 ^ k % 11 at h
      have h20 : 2 ^ 20 % 11 = 1 := by norm_num
      rw [h20] at h
      exact h.symm
    have htab : ∀ r : Fin 21, 2 ^ (r : ℕ) % 11 = 1 →
        (r : ℕ) = 0 ∨ (r : ℕ) = 10 ∨ (r : ℕ) = 20 := by
      decide
    exact htab ⟨k, by omega⟩ hmod
  have hk20_ne : k ≠ 20 := by
    intro hk20
    have htop : TauCeti.fixedSubgroup (ρ a).toMonoidHom = ⊤ := by
      refine Subgroup.eq_top_of_card_eq (H := TauCeti.fixedSubgroup (ρ a).toMonoidHom) ?_
      rw [hk, hk20, hcard]
    have hρa : ρ a = 1 := by
      ext v
      exact (TauCeti.mem_fixedSubgroup (F := (ρ a).toMonoidHom)).mp (htop ▸ Subgroup.mem_top v)
    have ha1 : a = 1 := hρ (by rw [hρa, map_one])
    rw [ha1, orderOf_one] at ha11
    exact absurd ha11 (by norm_num)
  have hk0_ne : k ≠ 0 := by
    intro hk0
    have hCa_bot : TauCeti.fixedSubgroup (ρ a).toMonoidHom = ⊥ :=
      Subgroup.eq_bot_of_card_eq (H := TauCeti.fixedSubgroup (ρ a).toMonoidHom)
        (by rw [hk, hk0]; norm_num)
    obtain ⟨j, hj⟩ : ∃ j, Nat.card (TauCeti.fixedSubgroup (ρ b).toMonoidHom) = 2 ^ j := hpow _
    have hj20 : j ≤ 20 := hpow_le _ j hj
    have hCb_inv : ∀ v ∈ TauCeti.fixedSubgroup (ρ b).toMonoidHom,
        ρ a v ∈ TauCeti.fixedSubgroup (ρ b).toMonoidHom := by
      intro v hv
      rw [TauCeti.mem_fixedSubgroup] at hv ⊢
      change ρ b v = v at hv
      change ρ b (ρ a v) = ρ a v
      rw [← MulAut.mul_apply, ← map_mul, ← ha b hb, map_mul, MulAut.mul_apply, hv]
    have hmod11 : Nat.card (TauCeti.fixedSubgroup (ρ b).toMonoidHom) ≡
        Nat.card ↥(TauCeti.fixedSubgroup (ρ b).toMonoidHom ⊓
          TauCeti.fixedSubgroup (ρ a).toMonoidHom) [MOD 11] :=
      card_modEq_card_inf_fixedSubgroup (p := 11) (m := 1) (g := a)
        (S := TauCeti.fixedSubgroup (ρ b).toMonoidHom)
        (by rw [pow_one]; exact ha_pow) hCb_inv
    rw [hCa_bot, inf_bot_eq, Subgroup.card_bot, hj] at hmod11
    have hj_cases : j = 0 ∨ j = 10 ∨ j = 20 := by
      have hmod : 2 ^ j % 11 = 1 := by
        have h := hmod11
        change 2 ^ j % 11 = 1 % 11 at h
        simpa using h
      have htab : ∀ r : Fin 21, 2 ^ (r : ℕ) % 11 = 1 →
          (r : ℕ) = 0 ∨ (r : ℕ) = 10 ∨ (r : ℕ) = 20 := by
        decide
      exact htab ⟨j, by omega⟩ hmod
    have hj20_ne : j ≠ 20 := by
      intro hj20
      have htop : TauCeti.fixedSubgroup (ρ b).toMonoidHom = ⊤ := by
        refine Subgroup.eq_top_of_card_eq (H := TauCeti.fixedSubgroup (ρ b).toMonoidHom) ?_
        rw [hj, hj20, hcard]
      have hρb : ρ b = 1 := by
        ext v
        exact (TauCeti.mem_fixedSubgroup (F := (ρ b).toMonoidHom)).mp (htop ▸ Subgroup.mem_top v)
      have hb1 : b = 1 := hρ (by rw [hρb, map_one])
      obtain ⟨k', hk'K, hk'b⟩ := hbK
      exact hk'b (by rw [hb1]; simp)
    obtain ⟨n7, hn7⟩ := hb7
    have hmod7 : Nat.card V ≡ Nat.card (TauCeti.fixedSubgroup (ρ b).toMonoidHom) [MOD 7] := by
      have h := card_modEq_card_inf_fixedSubgroup (ρ := ρ) (p := 7) (m := n7) (g := b)
        (S := ⊤) hn7 (fun v _ => Subgroup.mem_top (ρ b v))
      simpa using h
    rw [hcard, hj] at hmod7
    have hj7 : 2 ^ j % 7 = 4 := by
      have h : 2 ^ j % 7 = 2 ^ 20 % 7 := hmod7.symm
      rw [h]
      norm_num
    rcases hj_cases with h | h | h
    · rw [h] at hj7
      norm_num at hj7
    · rw [h] at hj7
      norm_num at hj7
    · exact hj20_ne h
  have hk10 : k = 10 := by
    rcases hk_cases with h | h | h
    · exact absurd h hk0_ne
    · exact h
    · exact absurd h hk20_ne
  let δ : V →* V := diffHom ρ a
  let U : Subgroup V := δ.range
  have hkerδ : δ.ker = TauCeti.fixedSubgroup (ρ a).toMonoidHom := diffHom_ker ρ a
  have hcardU' : Nat.card δ.range = 2 ^ 10 := by
    have h1 : Nat.card δ.ker * Nat.card δ.range = Nat.card V :=
      Subgroup.card_ker_mul_card_range δ
    rw [hkerδ, hk, hk10, hcard] at h1
    norm_num at h1 ⊢
    omega
  have hcardU : Nat.card U = 2 ^ 10 := hcardU'
  have hUbot : U ⊓ TauCeti.fixedSubgroup (ρ a).toMonoidHom = ⊥ :=
    diffHom_range_inf_fixedSubgroup hexp ha_pow
  have hUa : ∀ v ∈ U, ρ a v ∈ U := by
    intro v hv
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hv
    refine ⟨ρ a w, ?_⟩
    rw [← hw]
    exact (diffHom_comm rfl w).symm
  have hUK : ∀ k ∈ K, ∀ v ∈ U, ρ k v ∈ U := by
    intro k hk v hv
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hv
    refine ⟨ρ k w, ?_⟩
    rw [← hw]
    exact (diffHom_comm (ha k hk) w).symm
  have hUb : ∀ v ∈ U, ρ b v ∈ U := hUK b hb
  have hCU_a_inv : ∀ v ∈ U ⊓ TauCeti.fixedSubgroup (ρ b).toMonoidHom,
      ρ a v ∈ U ⊓ TauCeti.fixedSubgroup (ρ b).toMonoidHom := by
    intro v hv
    obtain ⟨hvU, hvb⟩ := Subgroup.mem_inf.mp hv
    refine Subgroup.mem_inf.mpr ⟨hUa v hvU, ?_⟩
    rw [TauCeti.mem_fixedSubgroup] at hvb ⊢
    change ρ b v = v at hvb
    change ρ b (ρ a v) = ρ a v
    rw [← MulAut.mul_apply, ← map_mul, ← ha b hb, map_mul, MulAut.mul_apply, hvb]
  obtain ⟨m, hm⟩ : ∃ m, Nat.card ↥(U ⊓ TauCeti.fixedSubgroup (ρ b).toMonoidHom) = 2 ^ m := hpow _
  have hm10 : m ≤ 10 := by
    have hdvd : 2 ^ m ∣ 2 ^ 10 := by
      rw [← hm, ← hcardU]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hle : 2 ^ m ≤ 2 ^ 10 := Nat.le_of_dvd (by positivity) hdvd
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  have hmodU11 : Nat.card ↥(U ⊓ TauCeti.fixedSubgroup (ρ b).toMonoidHom) ≡
      Nat.card ↥((U ⊓ TauCeti.fixedSubgroup (ρ b).toMonoidHom) ⊓
        TauCeti.fixedSubgroup (ρ a).toMonoidHom) [MOD 11] :=
    card_modEq_card_inf_fixedSubgroup (p := 11) (m := 1) (g := a)
      (by rw [pow_one]; exact ha_pow) hCU_a_inv
  have hCUbot : (U ⊓ TauCeti.fixedSubgroup (ρ b).toMonoidHom) ⊓
      TauCeti.fixedSubgroup (ρ a).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    calc (U ⊓ TauCeti.fixedSubgroup (ρ b).toMonoidHom) ⊓ TauCeti.fixedSubgroup (ρ a).toMonoidHom
        ≤ U ⊓ TauCeti.fixedSubgroup (ρ a).toMonoidHom := inf_le_inf_right _ inf_le_left
      _ ≤ ⊥ := le_of_eq hUbot
  rw [hCUbot, Subgroup.card_bot, hm] at hmodU11
  have hm_cases : m = 0 ∨ m = 10 := by
    have hmod : 2 ^ m % 11 = 1 := by
      have h := hmodU11
      change 2 ^ m % 11 = 1 % 11 at h
      simpa using h
    have htab : ∀ r : Fin 11, 2 ^ (r : ℕ) % 11 = 1 → (r : ℕ) = 0 ∨ (r : ℕ) = 10 := by
      decide
    exact htab ⟨m, by omega⟩ hmod
  obtain ⟨n7, hn7⟩ := hb7
  have hmodU7 : Nat.card U ≡ Nat.card ↥(U ⊓ TauCeti.fixedSubgroup (ρ b).toMonoidHom) [MOD 7] :=
    card_modEq_card_inf_fixedSubgroup (p := 7) (m := n7) (g := b) hn7 hUb
  rw [hcardU, hm] at hmodU7
  have hm7 : 2 ^ m % 7 = 2 := by
    have h : 2 ^ m % 7 = 2 ^ 10 % 7 := hmodU7.symm
    rw [h]
    norm_num
  have hm10' : m = 10 := by
    rcases hm_cases with h | h
    · rw [h] at hm7
      norm_num at hm7
    · exact h
  have hCU : U ⊓ TauCeti.fixedSubgroup (ρ b).toMonoidHom = U := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [hm, hm10', hcardU]
  have hbU : ∀ v ∈ U, ρ b v = v := by
    intro v hv
    have hv' : v ∈ U ⊓ TauCeti.fixedSubgroup (ρ b).toMonoidHom := by rw [hCU]; exact hv
    exact (TauCeti.mem_fixedSubgroup (F := (ρ b).toMonoidHom)).mp (Subgroup.mem_inf.mp hv').2
  letI : MulAction K U :=
    { smul := fun k u => ⟨ρ (k : X) u.1, hUK (k : X) k.2 u.1 u.2⟩
      one_smul := by
        intro u
        ext
        show ρ ((1 : K) : X) u.1 = u.1
        simp
      mul_smul := by
        intro k1 k2 u
        ext
        show ρ ((k1 * k2 : K) : X) u.1 = ρ (k1 : X) (ρ (k2 : X) u.1)
        rw [Subgroup.coe_mul, map_mul]
        rfl }
  let N : Subgroup K := (MulAction.toPermHom K U).ker
  have hNnorm : N.Normal := MonoidHom.normal_ker _
  have hbN : (⟨b, hb⟩ : K) ∈ N := by
    rw [MonoidHom.mem_ker, MulAction.toPermHom_apply, Equiv.Perm.ext_iff]
    intro u
    rw [MulAction.toPerm_apply]
    exact Subtype.ext (hbU u.1 u.2)
  have hNtop : N = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hK hNnorm with h | h
    · exact h
    · exfalso
      obtain ⟨k, hkK, hbk⟩ := hbK
      have hbc : (⟨b, hb⟩ : K) ∈ Subgroup.center K := h hbN
      have hcomm := (Subgroup.mem_center_iff.mp hbc) ⟨k, hkK⟩
      exact hbk (congrArg Subtype.val hcomm).symm
  have hUbig : 1 < Nat.card U := by rw [hcardU]; norm_num
  haveI : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp hUbig
  obtain ⟨u, hu1⟩ := exists_ne (1 : U)
  refine ⟨u.1, ?_, ?_⟩
  · intro h
    exact hu1 (Subtype.ext h)
  · intro k hk
    have hkN : (⟨k, hk⟩ : K) ∈ N := by rw [hNtop]; exact Subgroup.mem_top _
    have hkfix : (⟨k, hk⟩ : K) • u = u := by
      have h1 : (MulAction.toPermHom K U) ⟨k, hk⟩ = 1 := MonoidHom.mem_ker.mp hkN
      have h2 := congrArg (fun f : Equiv.Perm U => f u) h1
      simpa using h2
    exact congrArg Subtype.val hkfix

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
