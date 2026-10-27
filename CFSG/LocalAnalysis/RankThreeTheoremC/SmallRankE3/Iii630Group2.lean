module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.LocalVocabulary
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wConjTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
section R10B1

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem r10a11_mul_zpow {x z : G} (hc : Commute x z) (j i j' i' : ℤ) :
    x ^ j * z ^ i * (x ^ j' * z ^ i') = x ^ (j + j') * z ^ (i + i') := by
  have h1 : z ^ i * x ^ j' = x ^ j' * z ^ i := ((hc.zpow_zpow j' i).eq).symm
  calc x ^ j * z ^ i * (x ^ j' * z ^ i')
      = x ^ j * (z ^ i * x ^ j') * z ^ i' := by simp only [mul_assoc]
    _ = x ^ j * (x ^ j' * z ^ i) * z ^ i' := by rw [h1]
    _ = x ^ (j + j') * z ^ (i + i') := by
      rw [zpow_add, zpow_add]
      simp only [mul_assoc]

omit [Finite G] in
private theorem r10a11_inv_zpow {x z : G} (hc : Commute x z) (j i : ℤ) :
    (x ^ j * z ^ i)⁻¹ = x ^ (-j) * z ^ (-i) := by
  rw [mul_inv_rev, zpow_neg, zpow_neg]
  exact ((hc.zpow_zpow j i).inv_inv).eq.symm

omit [Finite G] in
private theorem r10a11_mem_sup {x z b : G} (hxz : x * z = z * x)
    (hb : b ∈ zpowers x ⊔ zpowers z) : ∃ j i : ℤ, b = x ^ j * z ^ i := by
  have hc : Commute x z := hxz
  let T : Subgroup G :=
    { carrier := {g | ∃ j i : ℤ, g = x ^ j * z ^ i}
      mul_mem' := by
        rintro _ _ ⟨j, i, rfl⟩ ⟨j', i', rfl⟩
        exact ⟨j + j', i + i', r10a11_mul_zpow hc j i j' i'⟩
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨j, i, rfl⟩
        exact ⟨-j, -i, r10a11_inv_zpow hc j i⟩ }
  have hle : zpowers x ⊔ zpowers z ≤ T := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  obtain ⟨j, i, hji⟩ : ∃ j i : ℤ, b = x ^ j * z ^ i := hle hb
  exact ⟨j, i, hji⟩

omit [Finite G] in
private theorem r10a11_conj_sq {z g a : G} (hgg : g * g = z) (h : g * a * g⁻¹ = a) :
    z * a * z⁻¹ = a := by
  subst hgg
  calc g * g * a * (g * g)⁻¹ = g * (g * a * g⁻¹) * g⁻¹ := by group
    _ = a := by rw [h, h]

omit [Finite G] in
private theorem r10a11_conj_of_zpow {z a : G} (hz3 : z ^ 3 = 1) {i : ℤ}
    (hi : ¬ (3 : ℤ) ∣ i) (h : z ^ i * a * (z ^ i)⁻¹ = a) : z * a * z⁻¹ = a := by
  have hz3' : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz3
  obtain ⟨q, r, rfl, hr⟩ : ∃ q r : ℤ, i = r + 3 * q ∧ (r = 1 ∨ r = 2) :=
    ⟨i / 3, i % 3, by omega, by omega⟩
  have hzr : z ^ (r + 3 * q) = z ^ r := by
    rw [zpow_add, zpow_mul, hz3', one_zpow, mul_one]
  rw [hzr] at h
  rcases hr with rfl | rfl
  · rw [zpow_one] at h
    exact h
  · refine r10a11_conj_sq (g := z ^ (2 : ℤ)) ?_ h
    rw [← zpow_add, show (2 : ℤ) + 2 = 1 + 3 by norm_num, zpow_add, hz3', mul_one, zpow_one]

omit [Finite G] in
private theorem r10a11_zpow_eq_one {z : G} (hz3 : z ^ (3 : ℤ) = 1) {i : ℤ}
    (h : (3 : ℤ) ∣ i) : z ^ i = 1 := by
  obtain ⟨t, rfl⟩ := h
  rw [zpow_mul, hz3, one_zpow]

omit [Finite G] in
private theorem r10a11_conj_mem_centralizer {F : Subgroup G} {k g : G}
    (hk : k ∈ normalizer (F : Set G)) (hg : g ∈ centralizer (F : Set G)) :
    k * g * k⁻¹ ∈ centralizer (F : Set G) := by
  rw [mem_centralizer_iff]
  intro h hh
  have hh' : k⁻¹ * h * k ∈ F := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hk) h).mp hh
    simpa using h1
  have hc := mem_centralizer_iff.mp hg (k⁻¹ * h * k) hh'
  calc h * (k * g * k⁻¹) = k * (k⁻¹ * h * k * g) * k⁻¹ := by group
    _ = k * (g * (k⁻¹ * h * k)) * k⁻¹ := by rw [hc]
    _ = k * g * k⁻¹ * h := by group

theorem eq_one_of_fixes_of_isPGroup_three {F : Subgroup G} {x z : G}
    (hB : IsSylowOf 3 (zpowers x ⊔ zpowers z) (normalizer (F : Set G)))
    (hxC : x ∈ centralizer (F : Set G)) (hzC : z ∉ centralizer (F : Set G)) (hz3 : z ^ 3 = 1)
    (hxz : x * z = z * x) (hzF : ∀ a ∈ F, z * a * z⁻¹ = a → a = 1) :
    ∀ m ∈ normalizer (F : Set G), IsPGroup 3 (zpowers m) → m ∉ centralizer (F : Set G) →
      ∀ a ∈ F, m * a * m⁻¹ = a → a = 1 := by
  intro m hmN hm3 hmC a haF hma
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3' : z ^ (3 : ℤ) = 1 := by exact_mod_cast hz3
  have hzB : z ∈ zpowers x ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  have hzN : z ∈ normalizer (F : Set G) := hB.le hzB
  obtain ⟨W, hW, hmW⟩ := sr630e_exists_isSylowOf_le (zpowers_le.mpr hmN) hm3
  obtain ⟨k, hkN, hk⟩ := hB.exists_mem_conj hW
  obtain ⟨b, hb⟩ : ∃ b, b = k⁻¹ * m * k := ⟨_, rfl⟩
  have hbB : b ∈ zpowers x ⊔ zpowers z := by
    rw [hb]
    exact (hk m).mp (hmW (mem_zpowers m))
  obtain ⟨j, i, hbji⟩ := r10a11_mem_sup hxz hbB
  have hbC : b ∉ centralizer (F : Set G) := by
    intro hbC
    apply hmC
    have hm : m = k * b * k⁻¹ := by
      rw [hb]
      group
    rw [hm]
    exact r10a11_conj_mem_centralizer hkN hbC
  have hxjC : x ^ j ∈ centralizer (F : Set G) := zpow_mem hxC j
  have hi3 : ¬ (3 : ℤ) ∣ i := by
    intro h3
    apply hbC
    rw [hbji, r10a11_zpow_eq_one hz3' h3, mul_one]
    exact hxjC
  obtain ⟨a', ha'⟩ : ∃ a', a' = k⁻¹ * a * k := ⟨_, rfl⟩
  have ha'F : a' ∈ F := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hkN) a).mp haF
    rw [ha']
    simpa using h1
  have hfix : b * a' * b⁻¹ = a' := by
    rw [hb, ha']
    calc k⁻¹ * m * k * (k⁻¹ * a * k) * (k⁻¹ * m * k)⁻¹
        = k⁻¹ * (m * a * m⁻¹) * k := by group
      _ = k⁻¹ * a * k := by rw [hma]
  obtain ⟨f, hf⟩ : ∃ f, f = z ^ i * a' * (z ^ i)⁻¹ := ⟨_, rfl⟩
  have hfF : f ∈ F := by
    rw [hf]
    exact (mem_normalizer_iff.mp (zpow_mem hzN i) a').mp ha'F
  have hcomm : x ^ j * f = f * x ^ j := (mem_centralizer_iff.mp hxjC f hfF).symm
  have h1 : x ^ j * f * (x ^ j)⁻¹ = a' := by
    calc x ^ j * f * (x ^ j)⁻¹ = b * a' * b⁻¹ := by
          rw [hbji, hf]
          group
      _ = a' := hfix
  have h2 : x ^ j * f * (x ^ j)⁻¹ = f := by
    rw [hcomm]
    group
  have hf_eq : z ^ i * a' * (z ^ i)⁻¹ = a' := by
    rw [← hf]
    exact h2.symm.trans h1
  have hconj : z * a' * z⁻¹ = a' := r10a11_conj_of_zpow hz3 hi3 hf_eq
  have ha'1 : a' = 1 := hzF a' ha'F hconj
  calc a = k * a' * k⁻¹ := by
        rw [ha']
        group
    _ = 1 := by
        rw [ha'1]
        group

end R10B1

section R10B2

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_invariant_sylow_conj {W B : Subgroup G} {r : ℕ} [Fact r.Prime]
    (hB : IsPGroup 3 B) (hBW : B ≤ normalizer (W : Set G)) (hW3 : ¬ 3 ∣ Nat.card W) {h : G}
    (hh : h ∈ W) (hhr : IsPGroup r (zpowers h)) :
    ∃ V : Subgroup G, V ≤ W ∧ IsPGroup r V ∧ B ≤ normalizer (V : Set G) ∧
      ∃ w ∈ W, w⁻¹ * h * w ∈ V := by
  have hr : r.Prime := Fact.out
  have hnorm : normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    normalizer_eq_top_iff.mpr inferInstance
  obtain ⟨S, hS, -, hBS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    (Q := (⊥ : Subgroup G)) (M := W) (A := B) Nat.prime_three hr hB hW3 hBW bot_le
    IsPGroup.of_bot (by rw [hnorm]; exact le_top)
  obtain ⟨T, hT⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS
  have hSyl : IsSylowOf r S W := ⟨T, hT⟩
  obtain ⟨hSW, hSr, -⟩ := hS
  have hP0 : IsPGroup r ((zpowers h).subgroupOf W) := hhr.comap_subtype
  obtain ⟨T', hT'⟩ := IsPGroup.exists_le_sylow hP0
  have hzp : zpowers h ≤ (T' : Subgroup W).map W.subtype := by
    intro x hx
    have hxW : x ∈ W := zpowers_le.mpr hh hx
    have hmem : (⟨x, hxW⟩ : W) ∈ (zpowers h).subgroupOf W := Subgroup.mem_subgroupOf.mpr hx
    exact ⟨⟨x, hxW⟩, hT' hmem, rfl⟩
  have hSyl' : IsSylowOf r ((T' : Subgroup W).map W.subtype) W := ⟨T', rfl⟩
  obtain ⟨k, hk, hkx⟩ := hSyl.exists_mem_conj hSyl'
  exact ⟨S, hSW, hSr, hBS, k, hk, (hkx h).mp (hzp (mem_zpowers h))⟩

end R10B2

section R10B3

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a13_conj_mem {V C : Subgroup G} {z v : G} (hzV : z ∈ normalizer (V : Set G))
    (hcomm : ∀ w ∈ V, z * w * z⁻¹ * w⁻¹ ∈ C) {u : G} (hu : u ∈ V ∧ u * v⁻¹ ∈ C) :
    z * u * z⁻¹ ∈ V ∧ z * u * z⁻¹ * v⁻¹ ∈ C := by
  refine ⟨(Subgroup.mem_set_normalizer_iff.mp hzV u).mp hu.1, ?_⟩
  have h1 : z * u * z⁻¹ * v⁻¹ = (z * u * z⁻¹ * u⁻¹) * (u * v⁻¹) := by group
  rw [h1]
  exact C.mul_mem (hcomm u hu.1) hu.2

private theorem r10a13_not_dvd_card {V C : Subgroup G} {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (hV : IsPGroup r V) {v : G} (hv : v ∈ V) :
    ¬ 3 ∣ Nat.card {u : G // u ∈ V ∧ u * v⁻¹ ∈ C} := by
  intro h3
  haveI : Fact r.Prime := ⟨hr⟩
  let e : {u : G // u ∈ V ∧ u * v⁻¹ ∈ C} ≃ ↥(V ⊓ C) :=
    { toFun := fun u => ⟨u.1 * v⁻¹, Subgroup.mem_inf.mpr ⟨V.mul_mem u.2.1 (V.inv_mem hv), u.2.2⟩⟩
      invFun := fun c => ⟨c.1 * v, V.mul_mem (Subgroup.mem_inf.mp c.2).1 hv, by
        simpa using (Subgroup.mem_inf.mp c.2).2⟩
      left_inv := fun u => Subtype.ext (inv_mul_cancel_right u.1 v)
      right_inv := fun c => Subtype.ext (mul_inv_cancel_right c.1 v) }
  rw [Nat.card_congr e] at h3
  have hdvd : Nat.card ↥(V ⊓ C) ∣ Nat.card ↥V := Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV
  have h3V : 3 ∣ r ^ k := by
    rw [← hk]
    exact dvd_trans h3 hdvd
  have h3r : 3 ∣ r := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3V
  exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h3r).symm

theorem exists_fixed_mem_coset {V C : Subgroup G} {r : ℕ} {z : G} (hr : r.Prime) (hr3 : r ≠ 3)
    (hV : IsPGroup r V) (hz3 : z ^ 3 = 1) (hzV : z ∈ normalizer (V : Set G))
    (hcomm : ∀ v ∈ V, z * v * z⁻¹ * v⁻¹ ∈ C) :
    ∀ v ∈ V, ∃ u ∈ V, u * v⁻¹ ∈ C ∧ z * u = u * z := by
  intro v hv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX3 := r10a13_not_dvd_card (C := C) hr hr3 hV hv
  have hinj : Function.Injective (fun u : {u : G // u ∈ V ∧ u * v⁻¹ ∈ C} =>
      (⟨z * u.1 * z⁻¹, r10a13_conj_mem hzV hcomm u.2⟩ : {u : G // u ∈ V ∧ u * v⁻¹ ∈ C})) := by
    intro a b hab
    have h1 : z * a.1 * z⁻¹ = z * b.1 * z⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Equiv.Perm {u : G // u ∈ V ∧ u * v⁻¹ ∈ C},
      ∀ u, (ρ u).1 = z * u.1 * z⁻¹ :=
    ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), fun u => rfl⟩
  have hρ3 : ρ ^ 3 = 1 := by
    have hz3' : z * z * z = 1 := by simpa only [pow_three, mul_assoc] using hz3
    refine Equiv.ext fun u => Subtype.ext ?_
    simp only [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hρ]
    have e1 : z * (z * (z * u.1 * z⁻¹) * z⁻¹) * z⁻¹ = z * z * z * u.1 * (z * z * z)⁻¹ := by
      group
    rw [e1, hz3']
    simp
  have hP : IsPGroup 3 ↥(Subgroup.zpowers ρ) := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    show g.1 ^ 3 = 1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρ3, one_zpow]
  have hmod := hP.card_modEq_card_fixedPoints {u : G // u ∈ V ∧ u * v⁻¹ ∈ C}
  have hne : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers ρ)
      {u : G // u ∈ V ∧ u * v⁻¹ ∈ C}) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hX3 (Nat.modEq_zero_iff_dvd.mp hmod)
  obtain ⟨⟨u, hu⟩, _⟩ := Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)
  have hρu : ρ u = u := MulAction.mem_fixedPoints.mp hu ⟨ρ, Subgroup.mem_zpowers ρ⟩
  have key : z * u.1 * z⁻¹ = u.1 := by
    have h1 := congrArg Subtype.val hρu
    rwa [hρ u] at h1
  exact ⟨u.1, u.2.1, u.2.2, mul_inv_eq_iff_eq_mul.mp key⟩

end R10B3

section R10B4

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a14_conj_mem {V F : Subgroup G} (hVF : V ≤ normalizer (F : Set G))
    (v : V) (a : F) : (v : G) * (a : G) * (v : G)⁻¹ ∈ F :=
  (Subgroup.mem_set_normalizer_iff.mp (hVF v.2) (a : G)).mp a.2

@[instance_reducible]
private def r10a14_act {V F : Subgroup G} (hVF : V ≤ normalizer (F : Set G)) :
    MulAction V F where
  smul v a := ⟨(v : G) * (a : G) * (v : G)⁻¹, r10a14_conj_mem hVF v a⟩
  one_smul a := by
    apply Subtype.ext
    show (1 : G) * (a : G) * (1 : G)⁻¹ = (a : G)
    simp
  mul_smul v w a := by
    apply Subtype.ext
    show ((v : G) * (w : G)) * (a : G) * ((v : G) * (w : G))⁻¹
      = (v : G) * ((w : G) * (a : G) * (w : G)⁻¹) * (v : G)⁻¹
    simp only [mul_inv_rev, mul_assoc]

theorem false_of_fixed_vector {M F V : Subgroup G} {x z a : G}
    (hP65 : ∀ W : Subgroup G, W ≤ M → W ≠ ⊥ → Nat.Coprime (Nat.card W) 6 →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set G) → normalizer (W : Set G) ≤ M)
    (hFM : F ⊓ M = ⊥) (hVM : V ≤ M) (hV1 : V ≠ ⊥) (hcop : Nat.Coprime (Nat.card V) 6)
    (hBV : zpowers x ⊔ zpowers z ≤ normalizer (V : Set G)) (haF : a ∈ F) (ha1 : a ≠ 1)
    (hfix : ∀ v ∈ V, v * a * v⁻¹ = a) : False := by
  have hN : normalizer (V : Set G) ≤ M := hP65 V hVM hV1 hcop hBV
  have hcomm : ∀ v ∈ V, a * v = v * a := fun v hv => by
    have h := hfix v hv
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have haN : a ∈ normalizer (V : Set G) := by
    refine Subgroup.mem_set_normalizer_iff.mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
    · have e : a * h * a⁻¹ = h := by
        rw [hcomm h hh, mul_inv_cancel_right]
      rw [e]
      exact hh
    · have e : a * h = a * (a * h * a⁻¹) := by
        rw [hcomm (a * h * a⁻¹) hh, inv_mul_cancel_right]
      have h' : h = a * h * a⁻¹ := mul_left_cancel e
      rw [h']
      exact hh
  have haM : a ∈ M := hN haN
  have haFM : a ∈ F ⊓ M := Subgroup.mem_inf.mpr ⟨haF, haM⟩
  rw [hFM, Subgroup.mem_bot] at haFM
  exact ha1 haFM

theorem exists_fixed_ne_one_of_isPGroup {V F : Subgroup G} {f : ℕ} (hf : f.Prime)
    (hV : IsPGroup f V) (hF : IsPGroup f F) (hF1 : F ≠ ⊥) (hVF : V ≤ normalizer (F : Set G)) :
    ∃ a ∈ F, a ≠ 1 ∧ ∀ v ∈ V, v * a * v⁻¹ = a := by
  haveI hfact : Fact f.Prime := ⟨hf⟩
  letI hact : MulAction V F := r10a14_act hVF
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := f)).mp hF
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hF1 (Subgroup.card_eq_one.mp (hn.trans (pow_zero f)))
  have hdvd : f ∣ Nat.card F := by
    rw [hn]
    exact dvd_pow_self f hn0
  have h1 : (1 : F) ∈ MulAction.fixedPoints ↥V ↥F := by
    rw [MulAction.mem_fixedPoints]
    intro y
    apply Subtype.ext
    show (y : G) * (1 : G) * (y : G)⁻¹ = 1
    simp
  obtain ⟨b, hb, hb1⟩ := hV.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥F hdvd h1
  have hbfix := MulAction.mem_fixedPoints.mp hb
  refine ⟨(b : G), b.2, fun h => hb1 (Subtype.ext h.symm), fun v hv => ?_⟩
  exact congrArg Subtype.val (hbfix ⟨v, hv⟩)

end R10B4

section R10B5

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_threeComplement {Y0 : Subgroup G} {x : G} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hxY : x ∈ Y0) (hxc : ∀ g ∈ Y0, g * x = x * g)
    (hsyl : ∀ Q : Subgroup G, Q ≤ Y0 → IsPGroup 3 Q → Nat.card Q ∣ 3) :
    ∃ W : Subgroup G, (∀ g : G, g ∈ W ↔ g ∈ Y0 ∧ ¬ 3 ∣ orderOf g) ∧ ¬ 3 ∣ Nat.card W := by
  obtain ⟨xY, rfl⟩ : ∃ xY : Y0, (xY : G) = x := ⟨⟨x, hxY⟩, rfl⟩
  have hx1Y : xY ≠ 1 := fun h => hx1 (by simp [h])
  have hx3Y : xY ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hx3
  have hx3z : xY ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hx3Y
  have hordx : orderOf xY = 3 := orderOf_eq_prime hx3Y hx1Y
  have hcomm : ∀ g : Y0, g * xY = xY * g := fun g => Subtype.ext (hxc g.1 g.2)
  haveI hKn : (zpowers xY).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g (xY ^ k) := (show Commute g xY from hcomm g).zpow_right k
    have hc' : g * xY ^ k * g⁻¹ = xY ^ k := by
      rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hc']
    exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩⟩
  have hK3 : Nat.card (zpowers xY) = 3 := by rw [Nat.card_zpowers, hordx]
  have hidx : (zpowers xY).index * 3 = Nat.card Y0 := by
    have h1 := Subgroup.index_mul_card (H := zpowers xY)
    rwa [hK3] at h1
  have h9 : ¬ 3 ^ 2 ∣ Nat.card Y0 := by
    intro hdvd
    obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Y0) 3 hdvd
    have hQ' : Nat.card (Q.map Y0.subtype) = 3 ^ 2 := by rw [Subgroup.card_subtype, hQ]
    have hpg : IsPGroup 3 (Q.map Y0.subtype) := IsPGroup.of_card hQ'
    have hd := hsyl (Q.map Y0.subtype) (Subgroup.map_subtype_le Q) hpg
    rw [hQ'] at hd
    norm_num at hd
  have hcop : Nat.Coprime (Nat.card (zpowers xY)) (zpowers xY).index := by
    rw [hK3]
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
    rintro ⟨c, hc⟩
    apply h9
    exact ⟨c, by rw [← hidx, hc]; ring⟩
  obtain ⟨H₀, hH₀⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hcardH : Nat.card (zpowers xY) * Nat.card H₀ = Nat.card Y0 := hH₀.card_mul_card
  have hnd3H : ¬ 3 ∣ Nat.card H₀ := by
    rintro ⟨c, hc⟩
    apply h9
    exact ⟨c, by rw [← hcardH, hK3, hc]; ring⟩
  refine ⟨H₀.map Y0.subtype, ?_, ?_⟩
  · intro g
    constructor
    · intro hg
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hg
      refine ⟨t.2, ?_⟩
      have hord1 : orderOf (Y0.subtype t) = orderOf t := Subgroup.orderOf_coe t
      have hord2 : orderOf t = orderOf (⟨t, ht⟩ : ↥H₀) := Subgroup.orderOf_coe (⟨t, ht⟩ : ↥H₀)
      rw [hord1, hord2]
      rintro h3
      exact hnd3H (dvd_trans h3 (orderOf_dvd_natCard (⟨t, ht⟩ : ↥H₀)))
    · rintro ⟨hgY, hg3⟩
      obtain ⟨gY, rfl⟩ : ∃ gY : Y0, (gY : G) = g := ⟨⟨g, hgY⟩, rfl⟩
      have hm3 : ¬ 3 ∣ orderOf gY := by
        rwa [Subgroup.orderOf_coe] at hg3
      have hbij := (Subgroup.isComplement_iff_bijective (zpowers xY) H₀).1 hH₀
      obtain ⟨⟨s, t⟩, hst⟩ := hbij.2 gY
      have hst' : s.1 * t.1 = gY := hst
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 s.2
      have hpow : (s.1 * t.1) ^ orderOf gY = 1 := by
        rw [hst']
        exact pow_orderOf_eq_one gY
      rw [← hj] at hpow
      have hc1 : Commute (xY ^ j) t.1 :=
        ((show Commute t.1 xY from hcomm t.1).symm).zpow_left j
      rw [hc1.mul_pow] at hpow
      have hpowj : (xY ^ j) ^ orderOf gY = xY ^ (j * (orderOf gY : ℤ)) := by
        rw [zpow_mul, zpow_natCast]
      rw [hpowj] at hpow
      have hu : t.1 ^ orderOf gY = (xY ^ (j * (orderOf gY : ℤ)))⁻¹ :=
        eq_inv_of_mul_eq_one_right hpow
      have htn : t.1 ^ orderOf gY ∈ H₀ := pow_mem t.2 _
      have htK : t.1 ^ orderOf gY ∈ zpowers xY := by
        rw [hu]
        exact inv_mem (Subgroup.mem_zpowers_iff.2 ⟨j * (orderOf gY : ℤ), rfl⟩)
      have hu1 : t.1 ^ orderOf gY = 1 := Subgroup.disjoint_def.1 hH₀.disjoint htK htn
      have hz1 : xY ^ (j * (orderOf gY : ℤ)) = 1 := inv_eq_one.1 (hu.symm.trans hu1)
      have hdvd : ((orderOf xY : ℕ) : ℤ) ∣ j * (orderOf gY : ℤ) :=
        orderOf_dvd_iff_zpow_eq_one.2 hz1
      rw [hordx] at hdvd
      have h3d : (3 : ℤ) ∣ j * (orderOf gY : ℤ) := by exact_mod_cast hdvd
      rcases Int.prime_three.dvd_or_dvd h3d with hj3 | hn3
      · obtain ⟨k, hk⟩ := hj3
        have hjx : xY ^ j = 1 := by
          rw [hk, zpow_mul, hx3z, one_zpow]
        have hs1 : s.1 = 1 := by
          rw [← hj, hjx]
        have ht1 : t.1 = gY := by
          rw [hs1, one_mul] at hst'
          exact hst'
        exact Subgroup.mem_map.2 ⟨t.1, t.2, congrArg Subtype.val ht1⟩
      · exact absurd (by exact_mod_cast hn3 : 3 ∣ orderOf gY) hm3
  · rw [Subgroup.card_subtype]
    exact hnd3H

end R10B5

section R10B6

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a16_conj_mul (z x y : G) :
    z * (x * y) * z⁻¹ = z * x * z⁻¹ * (z * y * z⁻¹) := by
  group

private theorem r10a16_pow_three_eq_one {z r s : G} (hz3 : z ^ 3 = 1) (hzr : z * r = r * z)
    (hzs : z * s * z⁻¹ = r * s) : r ^ 3 = 1 := by
  have hcr : z * r * z⁻¹ = r := by
    rw [hzr, mul_inv_cancel_right]
  have h2 : z * (r * s) * z⁻¹ = r * (r * s) := by
    rw [r10a16_conj_mul, hcr, hzs]
  have h3 : z * (r * (r * s)) * z⁻¹ = r * (r * (r * s)) := by
    rw [r10a16_conj_mul, hcr, h2]
  have h4 : z * (z * (z * s * z⁻¹) * z⁻¹) * z⁻¹ = s := by
    have e : z * (z * (z * s * z⁻¹) * z⁻¹) * z⁻¹ = z ^ 3 * s * (z ^ 3)⁻¹ := by
      rw [pow_three]
      simp only [mul_assoc, mul_inv_rev]
    rw [e, hz3]
    simp
  have h5 : z * (z * (z * s * z⁻¹) * z⁻¹) * z⁻¹ = r * (r * (r * s)) := by
    rw [hzs, h2, h3]
  have h6 : r * (r * r) * s = 1 * s := by
    rw [one_mul, mul_assoc, mul_assoc, ← h5, h4]
  rw [pow_three]
  exact mul_right_cancel h6

private theorem r10a16_eq_one_of_pow_three {S : Subgroup G} (hS : IsPGroup 2 S) {r : G}
    (hrS : r ∈ S) (h3 : r ^ 3 = 1) : r = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨r, hrS⟩
  have h2k : r ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hg : Nat.gcd 3 (2 ^ k) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by decide))
  have h1 : r ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨h3, h2k⟩
  rw [hg, pow_one] at h1
  exact h1

private theorem r10a16_conj_eq_self {S : Subgroup G} {z : G} (hS : IsPGroup 2 S)
    (hz3 : z ^ 3 = 1) (hzS : z ∈ normalizer (S : Set G))
    (hzC : z ∈ centralizer ((⁅zpowers z, S⁆ : Subgroup G) : Set G)) {s : G} (hs : s ∈ S) :
    z * s * z⁻¹ = s := by
  obtain ⟨r, hr⟩ : ∃ r : G, r = z * s * z⁻¹ * s⁻¹ := ⟨_, rfl⟩
  have hcomm := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers z) hs
  have hrR : r ∈ ⁅zpowers z, S⁆ := by
    rw [hr]
    exact hcomm
  have hzr : z * r = r * z := (Subgroup.mem_centralizer_iff.mp hzC r hrR).symm
  have hzs : z * s * z⁻¹ = r * s := by
    rw [hr, inv_mul_cancel_right]
  have hcs : z * s * z⁻¹ ∈ S := (Subgroup.mem_set_normalizer_iff.mp hzS s).mp hs
  have hrS : r ∈ S := by
    rw [hr]
    exact S.mul_mem hcs (S.inv_mem hs)
  have hr3 : r ^ 3 = 1 := r10a16_pow_three_eq_one hz3 hzr hzs
  have hr1 : r = 1 := r10a16_eq_one_of_pow_three hS hrS hr3
  exact mul_inv_eq_one.mp (hr.symm.trans hr1)

theorem not_mem_centralizer_commutator {S : Subgroup G} {z : G} (hS : IsPGroup 2 S)
    (hz3 : z ^ 3 = 1) (hzS : z ∈ normalizer (S : Set G)) (hR1 : ⁅zpowers z, S⁆ ≠ ⊥) :
    z ∉ centralizer ((⁅zpowers z, S⁆ : Subgroup G) : Set G) := by
  intro hzC
  apply hR1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le,
    Subgroup.mem_centralizer_iff]
  intro s hs
  exact (mul_inv_eq_iff_eq_mul.mp (r10a16_conj_eq_self hS hz3 hzS hzC hs)).symm

end R10B6

section R10B7

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a17_three_dvd_orderOf {Q : Subgroup G} (hQ : IsPGroup 3 Q) {g : G}
    (hgQ : g ∈ Q) (hg1 : g ≠ 1) : 3 ∣ orderOf g := by
  obtain ⟨k, hk⟩ := hQ ⟨g, hgQ⟩
  have hk' : g ^ 3 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (orderOf_dvd_of_pow_eq_one hk')
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hg1
    exact orderOf_eq_one_iff.mp (by rw [hi, pow_zero])
  rw [hi]
  exact dvd_pow_self 3 hi0

private theorem r10a17_orderOf_pow_three_lt {g : G} (h3 : 3 ∣ orderOf g) :
    orderOf (g ^ 3) < orderOf g := by
  rw [orderOf_pow_of_dvd (by norm_num) h3]
  exact Nat.div_lt_self (orderOf_pos g) (by norm_num)

theorem exists_mem_not_mem_pow_three_mem {Q B : Subgroup G} (hQ : IsPGroup 3 Q)
    (hB : B < Q) : ∃ g ∈ Q, g ∉ B ∧ g ^ 3 ∈ B := by
  classical
  have hex0 : ∃ q, q ∈ Q ∧ q ∉ B := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact ne_of_lt hB (le_antisymm (le_of_lt hB) (fun q hq => hcon q hq))
  obtain ⟨q, hqQ, hqB⟩ := hex0
  have hex : ∃ n : ℕ, ∃ g ∈ Q, g ∉ B ∧ orderOf g = n := ⟨_, q, hqQ, hqB, rfl⟩
  obtain ⟨g, hgQ, hgB, hgn⟩ := Nat.find_spec hex
  refine ⟨g, hgQ, hgB, ?_⟩
  by_contra hcon
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hgB B.one_mem
  have h3 : 3 ∣ orderOf g := r10a17_three_dvd_orderOf hQ hgQ hg1
  have hlt : orderOf (g ^ 3) < Nat.find hex := by
    rw [← hgn]
    exact r10a17_orderOf_pow_three_lt h3
  exact Nat.find_min hex hlt ⟨g ^ 3, Q.pow_mem hgQ 3, hcon, rfl⟩

private theorem r10a17_plane_decomp {x z b : G} (hxz : x * z = z * x)
    (hb : b ∈ zpowers x ⊔ zpowers z) : ∃ j i : ℤ, b = x ^ j * z ^ i := by
  have hxz' : Commute x z := hxz
  have hc : ∀ j i : ℤ, Commute (x ^ j) (z ^ i) := fun j i => hxz'.zpow_zpow j i
  have hmul : ∀ j i j' i' : ℤ,
      x ^ j * z ^ i * (x ^ j' * z ^ i') = x ^ (j + j') * z ^ (i + i') := by
    intro j i j' i'
    have hc' : z ^ i * x ^ j' = x ^ j' * z ^ i := (hc j' i).symm.eq
    calc x ^ j * z ^ i * (x ^ j' * z ^ i')
        = x ^ j * (z ^ i * x ^ j') * z ^ i' := by simp only [mul_assoc]
      _ = x ^ j * (x ^ j' * z ^ i) * z ^ i' := by rw [hc']
      _ = x ^ (j + j') * z ^ (i + i') := by simp only [zpow_add, mul_assoc]
  have hinv : ∀ j i : ℤ, (x ^ j * z ^ i)⁻¹ = x ^ (-j) * z ^ (-i) := by
    intro j i
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact (hc (-j) (-i)).eq.symm
  let M : Subgroup G :=
    { carrier := {b | ∃ j i : ℤ, b = x ^ j * z ^ i}
      mul_mem' := by
        rintro _ _ ⟨j, i, rfl⟩ ⟨j', i', rfl⟩
        exact ⟨j + j', i + i', hmul j i j' i'⟩
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨j, i, rfl⟩
        exact ⟨-j, -i, hinv j i⟩ }
  have hxM : zpowers x ≤ M := by
    rw [Subgroup.zpowers_le]
    show ∃ j i : ℤ, x = x ^ j * z ^ i
    exact ⟨1, 0, by simp⟩
  have hzM : zpowers z ≤ M := by
    rw [Subgroup.zpowers_le]
    show ∃ j i : ℤ, z = x ^ j * z ^ i
    exact ⟨0, 1, by simp⟩
  exact (sup_le hxM hzM) hb

theorem mem_zpowers_of_mem_plane_of_mem_centralizer {x z : G} {R : Subgroup G}
    (hxz : x * z = z * x) (hx : x ∈ centralizer (R : Set G)) (hz3 : z ^ 3 = 1)
    (hz : z ∉ centralizer (R : Set G)) {b : G} (hb : b ∈ zpowers x ⊔ zpowers z)
    (hbR : b ∈ centralizer (R : Set G)) : b ∈ zpowers x := by
  obtain ⟨j, i, rfl⟩ := r10a17_plane_decomp hxz hb
  have hz3' : z ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hz3]
  have hC : z ^ i ∈ centralizer (R : Set G) := by
    have h1 : x ^ j ∈ centralizer (R : Set G) := zpow_mem hx j
    have h2 := mul_mem (inv_mem h1) hbR
    rwa [inv_mul_cancel_left] at h2
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1 ∨ r = 2) ∧ i = 3 * q + r :=
    ⟨i / 3, i % 3, by omega, by omega⟩
  have e : z ^ (3 * q + r) = z ^ r := by
    rw [zpow_add, zpow_mul, hz3', one_zpow, one_mul]
  rw [e] at hC
  rcases hr with rfl | rfl | rfl
  · rw [e, zpow_zero, mul_one]
    exact zpow_mem_zpowers x j
  · exfalso
    apply hz
    rwa [zpow_one] at hC
  · exfalso
    apply hz
    have h4 := zpow_mem hC 2
    rw [← zpow_mul, show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add, hz3', one_mul,
      zpow_one] at h4
    exact h4

private theorem r10a17_conj_mem_commutator {S : Subgroup G} {g z : G}
    (hg : g ∈ normalizer (S : Set G)) (hgz : g * z = z * g) {c : G}
    (hc : c ∈ (⁅zpowers z, S⁆ : Subgroup G)) :
    g * c * g⁻¹ ∈ (⁅zpowers z, S⁆ : Subgroup G) := by
  have hgz' : Commute g z := hgz
  have hle : (⁅zpowers z, S⁆ : Subgroup G) ≤
      (⁅zpowers z, S⁆ : Subgroup G).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro h hh s hs
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hh
    have hcomm : Commute g (z ^ n) := hgz'.zpow_right n
    have h1 : g * z ^ n * g⁻¹ ∈ zpowers z := by
      rw [hcomm.eq, mul_inv_cancel_right]
      exact zpow_mem_zpowers z n
    have h2 : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hg s).mp hs
    have h3 : (g * z ^ n * g⁻¹) * (g * s * g⁻¹) * (g * z ^ n * g⁻¹)⁻¹ * (g * s * g⁻¹)⁻¹
        ∈ (⁅zpowers z, S⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator h1 h2
    have e : g * (z ^ n * s * (z ^ n)⁻¹ * s⁻¹) * g⁻¹ =
        (g * z ^ n * g⁻¹) * (g * s * g⁻¹) * (g * z ^ n * g⁻¹)⁻¹ * (g * s * g⁻¹)⁻¹ := by
      group
    show g * (z ^ n * s * (z ^ n)⁻¹ * s⁻¹) * g⁻¹ ∈ (⁅zpowers z, S⁆ : Subgroup G)
    rw [e]
    exact h3
  exact hle hc

theorem mem_normalizer_commutator_of_commute {S : Subgroup G} {g z : G}
    (hg : g ∈ normalizer (S : Set G)) (hgz : g * z = z * g) :
    g ∈ normalizer ((⁅zpowers z, S⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact r10a17_conj_mem_commutator hg hgz hc
  · intro hc
    have hg' : g⁻¹ ∈ normalizer (S : Set G) := inv_mem hg
    have hgz' : g⁻¹ * z = z * g⁻¹ := (show Commute g z from hgz).inv_left
    have h3 := r10a17_conj_mem_commutator (c := g * c * g⁻¹) hg' hgz' hc
    have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
    rw [e] at h3
    exact h3

theorem le_centralizer_of_isPGroup_of_normalizes {W X : Subgroup G} (hW : IsPGroup 3 W)
    (hX3 : Nat.card X = 3) (hWX : W ≤ normalizer (X : Set G)) :
    W ≤ centralizer (X : Set G) := by
  haveI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨y, hyX⟩, hy1⟩ := exists_ne (1 : X)
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hy3 : y ^ 3 = 1 := by
    have h : (⟨y, hyX⟩ : X) ^ 3 = 1 := by
      rw [← hX3]
      exact pow_card_eq_one'
    simpa using congrArg Subtype.val h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1'
  have hy3z : y ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hy3]
  have hzp : zpowers y = X := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact Subgroup.zpowers_le.mpr hyX
    · simp only [Nat.card_zpowers, hord, hX3, le_refl]
  have key : ∀ w ∈ W, Commute w y := by
    intro w hwW
    have hwN : w ∈ normalizer (X : Set G) := hWX hwW
    have hcX : w * y * w⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hwN y).mp hyX
    have hcZ : w * y * w⁻¹ ∈ zpowers y := by
      rw [hzp]
      exact hcX
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hcZ
    have hwy : w * y = y ^ k * w := by
      rw [hk, inv_mul_cancel_right]
    have hk3 : ¬ (3 : ℤ) ∣ k := by
      rintro ⟨t, rfl⟩
      have h1 : y ^ (3 * t) = 1 := by
        rw [zpow_mul, hy3z, one_zpow]
      have h2 : w * y * w⁻¹ = 1 := by
        rw [← hk, h1]
      exact hy1' (by simpa using h2)
    have hmod : (3 : ℤ) ∣ k * k - 1 := by
      have h : (3 : ℤ) ∣ (k - 1) ∨ (3 : ℤ) ∣ (k + 1) := by omega
      have h' : (3 : ℤ) ∣ (k - 1) * (k + 1) := by
        rcases h with h | h
        · exact dvd_mul_of_dvd_left h _
        · exact dvd_mul_of_dvd_right h _
      have e : k * k - 1 = (k - 1) * (k + 1) := by ring
      rw [e]
      exact h'
    have hyk : y ^ (k * k) = y := by
      obtain ⟨t, ht⟩ := hmod
      have e : k * k = 3 * t + 1 := by linarith
      rw [e, zpow_add, zpow_mul, hy3z, one_zpow, one_mul, zpow_one]
    have hconj : ∀ m : ℤ, w * y ^ m * w⁻¹ = y ^ (k * m) := by
      intro m
      rw [← conj_zpow, ← hk, ← zpow_mul]
    have hconk : w * y ^ k = y ^ (k * k) * w := by
      have h := hconj k
      rw [← h, inv_mul_cancel_right]
    have hsq : w ^ 2 * y = y * w ^ 2 := by
      calc w ^ 2 * y = w * (w * y) := by rw [pow_two, mul_assoc]
        _ = w * (y ^ k * w) := by rw [hwy]
        _ = w * y ^ k * w := by rw [mul_assoc]
        _ = y ^ (k * k) * w * w := by rw [hconk]
        _ = y ^ (k * k) * (w * w) := by rw [mul_assoc]
        _ = y * (w * w) := by rw [hyk]
        _ = y * w ^ 2 := by rw [pow_two]
    obtain ⟨s, hs⟩ := hW ⟨w, hwW⟩
    have hws : w ^ 3 ^ s = 1 := by
      simpa using congrArg Subtype.val hs
    obtain ⟨m, hm⟩ : Odd (3 ^ s) := Odd.pow ⟨1, by norm_num⟩
    rw [hm, pow_succ, pow_mul] at hws
    have hu : (w ^ 2) ^ m * w = 1 := hws
    have hcu : Commute ((w ^ 2) ^ m) y := (show Commute (w ^ 2) y from hsq).pow_left m
    have hwinv : w = ((w ^ 2) ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hu
    rw [hwinv]
    exact hcu.inv_left
  intro w hwW
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [← hzp] at hh
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (SetLike.mem_coe.mp hh)
  exact ((key w hwW).zpow_right j).eq.symm

end R10B7

section R10B8

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_inv_mul_eq {C N : Subgroup G} (hCN : C ≤ N)
    (hnorm : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) {c g : G} (hc : c ∈ C) (hgN : g ∈ N) (k : ℕ) :
    ∃ c' ∈ C, (c⁻¹ * g) ^ k = c' * g ^ k := by
  induction k with
  | zero => exact ⟨1, one_mem C, by simp⟩
  | succ k ih =>
    obtain ⟨c', hc', hpow⟩ := ih
    refine ⟨c' * (g ^ k * c⁻¹ * (g ^ k)⁻¹), mul_mem hc' (hnorm _ (pow_mem hgN k) _ (inv_mem hc)),
      ?_⟩
    rw [pow_succ (c⁻¹ * g) k, hpow, pow_succ g k]
    simp only [mul_assoc, inv_mul_cancel_left]

private theorem r10a18_eq_of_isSylowOf {p : ℕ} {B K T : Subgroup G} (hB : IsSylowOf p B K)
    (hT : IsPGroup p T) (hTK : T ≤ K) (hBT : B ≤ T) : T = B := by
  obtain ⟨Q0, hQ0⟩ := hB
  have hU : IsPGroup p (T.subgroupOf K) := hT.comap_subtype
  have hQU : (Q0 : Subgroup K) ≤ T.subgroupOf K := by
    intro x hx
    have hxB : (x : G) ∈ B := by
      rw [← hQ0]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (hBT hxB)
  have h := Q0.is_maximal' hU hQU
  have h2 : (T.subgroupOf K).map K.subtype = B := by
    rw [h]
    exact hQ0
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTK] at h2
  exact h2

theorem isSylowOf_of_le_of_le {p : ℕ} {B Y K : Subgroup G} (hB : IsSylowOf p B K)
    (hBY : B ≤ Y) (hYK : Y ≤ K) : IsSylowOf p B Y := by
  have hBp : IsPGroup p (B.subgroupOf Y) := hB.isPGroup.comap_subtype
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hBp
  have hBT : B ≤ (S : Subgroup Y).map Y.subtype := by
    intro x hx
    have hxY : x ∈ Y := hBY hx
    have hmem : (⟨x, hxY⟩ : Y) ∈ B.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hxY⟩, hS hmem, rfl⟩
  have hTK : (S : Subgroup Y).map Y.subtype ≤ K :=
    (Subgroup.map_subtype_le (S : Subgroup Y)).trans hYK
  have hT := r10a18_eq_of_isSylowOf hB (S.isPGroup'.map Y.subtype) hTK hBT
  exact ⟨S, hT⟩

theorem card_dvd_three_of_le_normal {Y Y0 B : Subgroup G} {x : G} (hx1 : x ≠ 1)
    (hx3 : x ^ 3 = 1) (hY0 : Y0 ≤ Y) (hY0norm : ∀ g ∈ Y, ∀ w ∈ Y0, g * w * g⁻¹ ∈ Y0)
    (hB : IsSylowOf 3 B Y) (hBY0 : B ⊓ Y0 ≤ zpowers x) :
    ∀ Q : Subgroup G, Q ≤ Y0 → IsPGroup 3 Q → Nat.card Q ∣ 3 := by
  intro Q hQY0 hQ3
  have hQY : Q ≤ Y := hQY0.trans hY0
  have hQ' : IsPGroup 3 (Q.subgroupOf Y) := hQ3.comap_subtype
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hQ'
  have hQP : Q ≤ (S : Subgroup Y).map Y.subtype := by
    intro q hq
    have hmem : (⟨q, hQY hq⟩ : Y) ∈ Q.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hq
    exact Subgroup.mem_map.mpr ⟨⟨q, hQY hq⟩, hS hmem, rfl⟩
  have hP : IsSylowOf 3 ((S : Subgroup Y).map Y.subtype) Y := ⟨S, rfl⟩
  obtain ⟨k, hkY, hk⟩ := IsSylowOf.exists_mem_conj hB hP
  have hsub : Q.map (MulAut.conj k⁻¹).toMonoidHom ≤ zpowers x := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    have hkq : k⁻¹ * q * k ∈ B := (hk q).mp (hQP hq)
    have hY0q : k⁻¹ * q * k⁻¹⁻¹ ∈ Y0 := hY0norm k⁻¹ (inv_mem hkY) q (hQY0 hq)
    rw [inv_inv] at hY0q
    have hmem : k⁻¹ * q * k ∈ B ⊓ Y0 := Subgroup.mem_inf.mpr ⟨hkq, hY0q⟩
    have hz := hBY0 hmem
    show k⁻¹ * q * k⁻¹⁻¹ ∈ zpowers x
    rw [inv_inv]
    exact hz
  have hcard : Nat.card (Q.map (MulAut.conj k⁻¹).toMonoidHom) = Nat.card Q :=
    Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
  have hdvd := Subgroup.card_dvd_of_le hsub
  rw [hcard, Nat.card_zpowers, orderOf_eq_prime hx3 hx1] at hdvd
  exact hdvd

end R10B8

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
