module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Local
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Quot

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem odd_geom_sum_iff {a : ℤ} (ha : Odd a) (m : ℕ) :
    Odd (∑ i ∈ Finset.range m, a ^ i) ↔ Odd m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hodd : ¬ Even (a ^ m) := Int.not_even_iff_odd.mpr ha.pow
    rw [Finset.sum_range_succ, Int.odd_add, Nat.odd_add_one, ← ih]
    simp [hodd]

theorem modEq_one_of_pow_modEq_one {a m k : ℕ} (hm : Odd m) (h : a ^ m ≡ 1 [MOD 2 ^ k]) :
    a ≡ 1 [MOD 2 ^ k] := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero]; exact Nat.modEq_one
  have h2 : a ^ m ≡ 1 [MOD 2] := h.of_dvd (dvd_pow_self 2 hk.ne')
  have ha : Odd a := by
    have h3 : Odd (a ^ m) := by
      rw [Nat.odd_iff]
      exact h2
    exact (Nat.odd_pow_iff (by rintro rfl; exact absurd hm (by decide))).mp h3
  have haZ : Odd (a : ℤ) := by exact_mod_cast ha
  obtain ⟨c, hc⟩ := (odd_geom_sum_iff haZ m).mpr hm
  have hcop : IsCoprime ((2 : ℤ) ^ k) (∑ i ∈ Finset.range m, (a : ℤ) ^ i) := by
    have : IsCoprime (2 : ℤ) (∑ i ∈ Finset.range m, (a : ℤ) ^ i) := ⟨-c, 1, by rw [hc]; ring⟩
    exact this.pow_left
  have hdvd : ((2 ^ k : ℕ) : ℤ) ∣ (1 : ℤ) - (a : ℤ) ^ m := by
    have := (Nat.modEq_iff_dvd.mp h)
    push_cast at this ⊢
    exact this
  have hgeom := geom_sum_mul (a : ℤ) m
  rw [Nat.modEq_iff_dvd]
  push_cast at hdvd ⊢
  have h4 : (2 : ℤ) ^ k ∣ ((a : ℤ) - 1) * ∑ i ∈ Finset.range m, (a : ℤ) ^ i := by
    rw [mul_comm, hgeom]
    have := hdvd.neg_right
    rwa [neg_sub] at this
  have h5 := hcop.dvd_of_dvd_mul_right h4
  have := h5.neg_right
  rwa [neg_sub] at this

theorem conj_eq_of_odd_of_cyclic {X : Type*} [Group X] [Finite X] {g y : X}
    (hg : IsPGroup 2 (zpowers g)) (hy : Odd (orderOf y))
    (hyN : y ∈ normalizer (zpowers g : Set X)) : y * g * y⁻¹ = g := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hg) ⟨g, mem_zpowers g⟩
  rw [Subgroup.orderOf_mk] at hk
  have hmem : y * g * y⁻¹ ∈ zpowers g := (mem_normalizer_iff.mp hyN g).mp (mem_zpowers g)
  rw [← mem_powers_iff_mem_zpowers] at hmem
  obtain ⟨a, ha⟩ := Submonoid.mem_powers_iff _ _ |>.mp hmem
  have hj : ∀ j : ℕ, y ^ j * g * (y ^ j)⁻¹ = g ^ (a ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc y ^ (j + 1) * g * (y ^ (j + 1))⁻¹ = y * (y ^ j * g * (y ^ j)⁻¹) * y⁻¹ := by group
        _ = (y * g * y⁻¹) ^ (a ^ j) := by rw [ih, conj_pow]
        _ = g ^ (a ^ (j + 1)) := by rw [← ha, ← pow_mul, pow_succ']
  have h1 := hj (orderOf y)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have h2 : g ^ (a ^ orderOf y) = g ^ 1 := by rw [← h1, pow_one]
  rw [pow_eq_pow_iff_modEq, hk] at h2
  have h3 := modEq_one_of_pow_modEq_one hy h2
  rw [← ha]
  calc g ^ a = g ^ 1 := (pow_eq_pow_iff_modEq.mpr (hk ▸ h3))
    _ = g := pow_one g

theorem eq_one_of_pow_odd {X : Type*} [Group X] [Finite X] {P : Subgroup X} (hP : IsPGroup 2 P)
    {c : X} (hc : c ∈ P) {m : ℕ} (hm : Odd m) (hcm : c ^ m = 1) : c = 1 := by
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨c, hc⟩
  rw [Subgroup.orderOf_mk] at he
  have h1 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one hcm
  rw [he] at h1
  have h2 : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hm)
  have h3 : 2 ^ e = 1 := Nat.Coprime.eq_one_of_dvd h2 h1
  rw [← orderOf_eq_one_iff, he, h3]

theorem IsDihedralRot.conj_eq_of_odd {X : Type} [Group X] [Finite X] {U R : Subgroup X}
    (h : IsDihedralRot U R) {y : X} (hy : Odd (orderOf y))
    (hyN : y ∈ normalizer (R : Set X)) {x : X} (hx : x ∈ R) : y * x * y⁻¹ = x := by
  obtain ⟨ρ, hρ, -⟩ := h.exists_gen
  have hyU : y ∈ normalizer (U : Set X) := h.normalizer_le hyN
  have hU2 : IsPGroup 2 U := h.isPGroup.to_le h.le
  have hyρ : y * ρ * y⁻¹ = ρ := by
    rw [← hρ] at hyU hU2
    exact conj_eq_of_odd_of_cyclic hU2 hy hyU
  have hcU : ∀ u ∈ U, y * u * y⁻¹ = u := by
    intro u hu
    rw [← hρ] at hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← conj_zpow, hyρ]
  by_cases hxU : x ∈ U
  · exact hcU x hxU
  have hyxR : y * x * y⁻¹ ∈ R := (mem_normalizer_iff.mp hyN x).mp hx
  have hyxU : y * x * y⁻¹ ∉ U := fun h' => hxU (by
    have := (mem_normalizer_iff.mp (inv_mem hyU) _).mp h'
    simpa [mul_assoc] using this)
  set c := x⁻¹ * (y * x * y⁻¹) with hc
  have hcU' : c ∈ U := h.mul_mem_of_not_mem (inv_mem hx) hyxR
    (fun h' => hxU (by simpa using inv_mem h')) hyxU
  have hj : ∀ j : ℕ, y ^ j * x * (y ^ j)⁻¹ = x * c ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc y ^ (j + 1) * x * (y ^ (j + 1))⁻¹ = y * (y ^ j * x * (y ^ j)⁻¹) * y⁻¹ := by group
        _ = (y * x * y⁻¹) * (y * c ^ j * y⁻¹) := by rw [ih]; group
        _ = x * c ^ (j + 1) := by
          rw [hcU _ (U.pow_mem hcU' j), pow_succ', ← mul_assoc]
          congr 1
          rw [hc]
          group
  have h1 := hj (orderOf y)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hcm : c ^ orderOf y = 1 := by
    have := congrArg (x⁻¹ * ·) h1
    simpa using this.symm
  have hc1 := eq_one_of_pow_odd hU2 hcU' hy hcm
  calc y * x * y⁻¹ = x * c := by rw [hc]; group
    _ = x := by rw [hc1, mul_one]

theorem IsDihedralRot.inf {X : Type} [Group X] [Finite X] {U R A : Subgroup X}
    (h : IsDihedralRot U R) (hAR : A ≤ R) {s a : X} (hsA : s ∈ A) (hsU : s ∉ U) (haA : a ∈ A)
    (haU : a ∈ U) (haa : a * a ≠ 1) : IsDihedralRot (A ⊓ U) A := by
  have hA2 : IsPGroup 2 A := h.isPGroup.to_le hAR
  refine ⟨inf_le_left, ?_, ?_, ?_, hA2, fun x hx hxU => h.mul_self x (hAR hx) fun h' =>
    hxU (mem_inf.mpr ⟨hx, h'⟩), fun x hx hxU u hu => h.conj_eq x (hAR hx)
      (fun h' => hxU (mem_inf.mpr ⟨hx, h'⟩)) u (mem_inf.mp hu).2⟩
  · have : IsCyclic U := h.isCyclic
    have : IsCyclic ((A ⊓ U).subgroupOf U) := inferInstance
    exact isCyclic_of_surjective (subgroupOfEquivOfLe inf_le_right).toMonoidHom
      (subgroupOfEquivOfLe inf_le_right).surjective
  · rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨s, hsA⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, mem_inf]
    by_cases hbU : (b : X) ∈ U
    · refine Or.inr ⟨⟨b.2, hbU⟩, fun h' => hsU ?_⟩
      have : s = (b : X)⁻¹ * ((b : X) * s) := by group
      rw [this]
      exact U.mul_mem (U.inv_mem hbU) h'.2
    · exact Or.inl ⟨⟨A.mul_mem b.2 hsA, h.mul_mem_of_not_mem (hAR b.2) (hAR hsA) hbU hsU⟩,
        fun h' => hbU h'.2⟩
  · have hao : 4 ≤ orderOf a := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hA2) ⟨a, haA⟩
      rw [Subgroup.orderOf_mk] at hk
      have hk2 : 2 ≤ k := by
        by_contra hlt
        apply haa
        rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hk]
        interval_cases k <;> norm_num
      rw [hk]
      calc 4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    calc 4 ≤ orderOf a := hao
      _ = orderOf (⟨a, mem_inf.mpr ⟨haA, haU⟩⟩ : ↥(A ⊓ U)) := (Subgroup.orderOf_mk _ _).symm
      _ ≤ Nat.card ↥(A ⊓ U) := orderOf_le_card

theorem card_map_of_injOn {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {H : Subgroup X}
    (hf : ∀ x ∈ H, f x = 1 → x = 1) : Nat.card (H.map f) = Nat.card H := by
  symm
  refine Nat.card_eq_of_bijective (fun h => ⟨f h, mem_map_of_mem f h.2⟩) ⟨fun a b hab => ?_, ?_⟩
  · have h1 : f ((a : X)⁻¹ * b) = 1 := by
      have := congrArg Subtype.val hab
      simp only at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    have h2 := hf _ (H.mul_mem (H.inv_mem a.2) b.2) h1
    exact Subtype.ext (by simpa [inv_mul_eq_one] using h2)
  · rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem IsDihedralRot.map {X Y : Type} [Group X] [Group Y] {U R : Subgroup X}
    (h : IsDihedralRot U R) (f : X →* Y) (hf : ∀ x ∈ R, f x = 1 → x = 1) :
    IsDihedralRot (U.map f) (R.map f) := by
  have hcU : Nat.card (U.map f) = Nat.card U := card_map_of_injOn f fun x hx => hf x (h.le hx)
  have hcR : Nat.card (R.map f) = Nat.card R := card_map_of_injOn f hf
  have hle : U.map f ≤ R.map f := map_mono h.le
  have hinv : ∀ x ∈ R, ∀ y ∈ R, f x = f y → x = y := fun x hx y hy hxy => by
    have := hf _ (R.mul_mem (R.inv_mem hx) hy) (by rw [map_mul, map_inv, hxy, inv_mul_cancel])
    simpa [inv_mul_eq_one] using this
  refine ⟨hle, ?_, ?_, hcU ▸ h.four_le, h.isPGroup.map f, ?_, ?_⟩
  · obtain ⟨ρ, hρ, -⟩ := h.exists_gen
    rw [← hρ, MonoidHom.map_zpowers]
    infer_instance
  · have h1 := Subgroup.relIndex_mul_card (U.map f) (R.map f)
    rw [inf_eq_left.mpr hle, hcU, hcR, h.card_eq] at h1
    have := h.four_le
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < Nat.card U) h1
  · rintro _ ⟨x, hx, rfl⟩ hxU
    have hxU' : x ∉ U := fun h' => hxU (mem_map_of_mem f h')
    rw [← map_mul, h.mul_self x hx hxU', map_one]
  · rintro _ ⟨x, hx, rfl⟩ hxU _ ⟨u, hu, rfl⟩
    have hxU' : x ∉ U := fun h' => hxU (mem_map_of_mem f h')
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, h.conj_eq x hx hxU' u hu, map_inv]

theorem IsDihedralRot.subgroupOf {X : Type} [Group X] {U R K : Subgroup X}
    (h : IsDihedralRot U R) (hRK : R ≤ K) : IsDihedralRot (U.subgroupOf K) (R.subgroupOf K) := by
  have hU : (U.subgroupOf K).map K.subtype = U := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr (h.le.trans hRK)]
  have hR : (R.subgroupOf K).map K.subtype = R := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hRK]
  have hcU : Nat.card (U.subgroupOf K) = Nat.card U :=
    (card_map_of_injective K.subtype_injective).symm.trans (by rw [hU])
  have hcR : Nat.card (R.subgroupOf K) = Nat.card R :=
    (card_map_of_injective K.subtype_injective).symm.trans (by rw [hR])
  have hle : U.subgroupOf K ≤ R.subgroupOf K := fun x hx => h.le hx
  refine ⟨hle, ?_, ?_, hcU ▸ h.four_le, h.isPGroup.comap_subtype, fun x hx hxU => ?_,
    fun x hx hxU u hu => ?_⟩
  · have : IsCyclic U := h.isCyclic
    exact isCyclic_of_surjective (subgroupOfEquivOfLe (h.le.trans hRK)).symm.toMonoidHom
      (subgroupOfEquivOfLe (h.le.trans hRK)).symm.surjective
  · have h1 := Subgroup.relIndex_mul_card (U.subgroupOf K) (R.subgroupOf K)
    rw [inf_eq_left.mpr hle, hcU, hcR, h.card_eq] at h1
    have := h.four_le
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < Nat.card U) h1
  · exact Subtype.ext (h.mul_self x hx hxU)
  · exact Subtype.ext (by simpa using h.conj_eq x hx hxU u hu)

theorem isPGroup_two_of_odd {X : Type*} [Group X] [Finite X]
    (h : ∀ y : X, Odd (orderOf y) → y = 1) : IsPGroup 2 X := by
  refine IsPGroup.iff_orderOf.mpr fun x => ?_
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, ?_⟩
  have hy : orderOf (x ^ (2 ^ k)) = m := by
    rw [orderOf_pow' x (by positivity), hkm, Nat.gcd_mul_right_left]
    exact Nat.mul_div_cancel_left m (by positivity)
  have h1 := h _ (hy ▸ hm)
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  rw [hkm] at h2 ⊢
  have hm1 : m = 1 := by
    have := Nat.le_of_dvd (by positivity) h2
    have hm0 : 0 < m := hm.pos
    nlinarith [Nat.one_le_two_pow (n := k)]
  rw [hm1, mul_one]

theorem isPGroup_or_of_charTwo {X : Type} [Group X] [Finite X]
    (hC : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) {U R : Subgroup X}
    (hU : IsDihedralRot U R) (hPR : CFSG.pCore 2 X ≤ R) :
    IsPGroup 2 X ∨ (¬ CFSG.pCore 2 X ≤ U ∧ ∀ p ∈ CFSG.pCore 2 X, p * p = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 X with hPdef
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hPn : P.Normal := CFSG.pCore_normal
  have key : (∀ y : X, Odd (orderOf y) → y ∈ centralizer (P : Set X)) → IsPGroup 2 X := by
    intro hy
    refine isPGroup_two_of_odd fun y hyo => ?_
    exact eq_one_of_pow_odd hP2 (hC (hy y hyo)) hyo (pow_orderOf_eq_one y)
  have hyN : ∀ y : X, y ∈ normalizer (P : Set X) := fun y => by
    rw [normalizer_eq_top_iff.mpr hPn]; exact mem_top y
  by_cases hPU : P ≤ U
  · left
    apply key
    intro y hyo
    have : IsCyclic U := hU.isCyclic
    have hPc : IsCyclic P := isCyclic_of_surjective (subgroupOfEquivOfLe hPU).toMonoidHom
      (subgroupOfEquivOfLe hPU).surjective
    obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top P).mp hPc
    rw [mem_centralizer_iff]
    intro p hp
    rw [← hg] at hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hyg : y * g * y⁻¹ = g := by
      have h2 : IsPGroup 2 (zpowers g) := hg ▸ hP2
      have h3 : y ∈ normalizer (zpowers g : Set X) := hg ▸ hyN y
      exact conj_eq_of_odd_of_cyclic h2 hyo h3
    have hyg' : y⁻¹ * g * y = g := by
      calc y⁻¹ * g * y = y⁻¹ * (y * g * y⁻¹) * y := by rw [hyg]
        _ = g := by group
    have hgk : y⁻¹ * g ^ k * y = g ^ k := by
      have := conj_zpow (a := y⁻¹) (b := g) (i := k)
      rw [inv_inv] at this
      rw [← this, hyg']
    calc g ^ k * y = y * (y⁻¹ * g ^ k * y) := by group
      _ = y * g ^ k := by rw [hgk]
  · by_cases hexp : ∀ p ∈ P, p * p = 1
    · exact Or.inr ⟨hPU, hexp⟩
    left
    push Not at hexp
    obtain ⟨a, haP, haa⟩ := hexp
    obtain ⟨s, hsP, hsU⟩ := Set.not_subset.mp hPU
    have hD := hU.inf hPR hsP hsU haP (hU.mem_of_mul_self_ne_one (hPR haP) haa) haa
    apply key
    intro y hyo
    rw [mem_centralizer_iff]
    intro p hp
    have := hD.conj_eq_of_odd hyo (hyN y) hp
    calc p * y = y * (y⁻¹ * p * y) := by group
      _ = y * p := by
        rw [show y⁻¹ * p * y = p by
          calc y⁻¹ * p * y = y⁻¹ * (y * p * y⁻¹) * y := by rw [this]
            _ = p := by group]

theorem mk_injOn {K R : Subgroup G} (hR : IsPGroup 2 R) :
    ∀ x ∈ R.subgroupOf K, QuotientGroup.mk' (CFSG.Assembly.oddCore K) x = 1 → x = 1 := by
  intro x hx h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h2 : (x : G) ∈ oddCoreIn K ⊓ R := mem_inf.mpr ⟨⟨x, h1, rfl⟩, hx⟩
  rw [oddCoreIn_inf_eq_bot hR, mem_bot] at h2
  exact Subtype.ext h2

theorem mk_conj_mem_pCore {K : Subgroup G} {g : G} (hg : g ∈ normalizer (K : Set G)) {x : G}
    (hx : x ∈ K) (hxg : g * x * g⁻¹ ∈ K)
    (hP : QuotientGroup.mk' (CFSG.Assembly.oddCore K) ⟨x, hx⟩ ∈
      CFSG.pCore 2 (K ⧸ CFSG.Assembly.oddCore K)) :
    QuotientGroup.mk' (CFSG.Assembly.oddCore K) ⟨g * x * g⁻¹, hxg⟩ ∈
      CFSG.pCore 2 (K ⧸ CFSG.Assembly.oddCore K) := by
  let φ : K ≃* K :=
    { toFun := fun k => ⟨g * k * g⁻¹, (mem_normalizer_iff.mp hg k).mp k.2⟩
      invFun := fun k => ⟨g⁻¹ * k * g, by
        simpa using (mem_normalizer_iff.mp (inv_mem hg) k).mp k.2⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp only [coe_mul]; group) }
  have hO : (CFSG.Assembly.oddCore K).map φ.toMonoidHom = CFSG.Assembly.oddCore K := by
    have := assemblyOddCore_characteristic K
    exact characteristic_iff_map_eq.mp this φ
  set ψ := QuotientGroup.congr (CFSG.Assembly.oddCore K) (CFSG.Assembly.oddCore K) φ hO
  have hψ : ψ (QuotientGroup.mk' (CFSG.Assembly.oddCore K) ⟨x, hx⟩) =
      QuotientGroup.mk' (CFSG.Assembly.oddCore K) ⟨g * x * g⁻¹, hxg⟩ := rfl
  have hPψ : (CFSG.pCore 2 (K ⧸ CFSG.Assembly.oddCore K)).map ψ.toMonoidHom =
      CFSG.pCore 2 (K ⧸ CFSG.Assembly.oddCore K) :=
    characteristic_iff_map_eq.mp CFSG.pCore_characteristic ψ
  rw [← hψ, ← hPψ]
  exact mem_map_of_mem _ hP

theorem lemma43 {K R U : Subgroup G} (hlayer : twoPrimeLayerIn K = oddCoreIn K)
    (hR : IsSylowOf 2 R K) (hU : IsDihedralRot U R) :
    IsTwoNil K R ∨ (Nat.card U = 4 ∧ ∃ Q : Subgroup G, Q ≤ R ∧ ¬ Q ≤ U ∧
      (∀ q ∈ Q, q * q = 1) ∧
      normalizer (K : Set G) ⊓ normalizer (R : Set G) ≤ normalizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Assembly.oddCore K
  set π := QuotientGroup.mk' O
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hinj := mk_injOn (K := K) hR.isPGroup
  have hUX := (hU.subgroupOf hR.le).map π hinj
  have hOX : CFSG.pPrimeCore 2 (K ⧸ O) = ⊥ := le_bot_iff.mp
    (CFSG.ComponentClassification.Asc76.L26.pPrimeCore_two_le_oddCore.trans
      (CFSG.ComponentClassification.Asc76.L26.oddCore_quotient_oddCore_eq_bot (G := K)).le)
  have hCX : centralizer (CFSG.pCore 2 (K ⧸ O) : Set (K ⧸ O)) ≤ CFSG.pCore 2 (K ⧸ O) :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ 2 hOX
      ((twoPrimeLayerIn_eq_oddCoreIn_iff K).mp hlayer)
  obtain ⟨Q₀, hQ₀⟩ := hR.exists_sylow_eq_subgroupOf
  have hPn : (CFSG.pCore 2 (K ⧸ O)).Normal := CFSG.pCore_normal
  have hPR : CFSG.pCore 2 (K ⧸ O) ≤ (R.subgroupOf K).map π := by
    have h1 := IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := K ⧸ O))
      (Q₀.mapSurjective hπ)
    rwa [Sylow.coe_mapSurjective, hQ₀] at h1
  rcases isPGroup_or_of_charTwo hCX hUX hPR with h2 | ⟨hPU, hP2⟩
  · left
    have htop : (R.subgroupOf K).map π = ⊤ := by
      have h3 := (Q₀.mapSurjective hπ).is_maximal' (h2.to_subgroup ⊤) le_top
      rw [Sylow.coe_mapSurjective, hQ₀] at h3
      exact h3.symm
    intro k hk
    have hmem : π ⟨k, hk⟩ ∈ (R.subgroupOf K).map π := htop ▸ mem_top _
    obtain ⟨r', hr', hr'eq⟩ := hmem
    have ho' : r'⁻¹ * ⟨k, hk⟩ ∈ O := QuotientGroup.eq.mp hr'eq
    have ho : r' * (r'⁻¹ * ⟨k, hk⟩) * r'⁻¹ ∈ O :=
      (inferInstance : O.Normal).conj_mem _ ho' r'
    refine ⟨((r' * (r'⁻¹ * ⟨k, hk⟩) * r'⁻¹ : K) : G), ⟨_, ho, rfl⟩, (r' : G), hr', ?_⟩
    simp only [coe_mul, coe_inv]
    group
  · right
    set Q := ((CFSG.pCore 2 (K ⧸ O)).comap π).map K.subtype ⊓ R with hQdef
    have hQR : Q ≤ R := inf_le_right
    have hQ2 : ∀ q ∈ Q, q * q = 1 := by
      rintro q ⟨⟨k, hkP, rfl⟩, hkR⟩
      have h1 : π (k * k) = 1 := by rw [map_mul, hP2 _ hkP]
      have h2 := hinj (k * k) (mul_mem (show k ∈ R.subgroupOf K from hkR)
        (show k ∈ R.subgroupOf K from hkR)) h1
      exact congrArg Subtype.val h2
    have hQU : ¬ Q ≤ U := by
      intro hle
      obtain ⟨x, hxP, hxU⟩ := Set.not_subset.mp hPU
      obtain ⟨r₀, hr₀, rfl⟩ := hPR hxP
      exact hxU (mem_map_of_mem π (show r₀ ∈ U.subgroupOf K from
        hle (mem_inf.mpr ⟨⟨r₀, hxP, rfl⟩, hr₀⟩)))
    have hQN : normalizer (K : Set G) ⊓ normalizer (R : Set G) ≤ normalizer (Q : Set G) := by
      intro g hg
      obtain ⟨hgK, hgR⟩ := mem_inf.mp hg
      apply mem_normalizer_of_map_conj_le
      rintro _ ⟨x, ⟨⟨k, hkP, rfl⟩, hkR⟩, rfl⟩
      have hxg : g * (k : G) * g⁻¹ ∈ K := (mem_normalizer_iff.mp hgK _).mp k.2
      refine mem_inf.mpr ⟨⟨⟨_, hxg⟩, mk_conj_mem_pCore hgK k.2 hxg hkP, rfl⟩, ?_⟩
      exact (mem_normalizer_iff.mp hgR _).mp hkR
    have hRQ : R ≤ normalizer (Q : Set G) := fun r hr =>
      hQN (mem_inf.mpr ⟨le_normalizer (hR.le hr), le_normalizer hr⟩)
    exact ⟨hU.card_eq_four hQR hRQ hQ2 hQU, Q, hQR, hQU, hQ2, hQN⟩

end CFSG.ComponentClassification.Asc76.Sec4
