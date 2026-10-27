module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma411

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

theorem mem_closure_pair {G : Type*} [Group G] {a b x : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : a * b = b * a) (hx : x ∈ closure {a, b}) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hab' : Commute a b := hab
  have hcl : closure ({a, b} : Set G) = zpowers a ⊔ zpowers b := by
    rw [show ({a, b} : Set G) = {a} ∪ {b} by rw [Set.insert_eq], Subgroup.closure_union,
      ← zpowers_eq_closure, ← zpowers_eq_closure]
  have haN : zpowers a ≤ normalizer (zpowers b : Set G) := fun y hy => by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => ?_)
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
    exact (Commute.zpow_zpow hab' i j).symm.eq
  rw [hcl] at hx
  have hx' : x ∈ (zpowers a : Set G) * (zpowers b : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ haN]
    exact hx
  obtain ⟨a', ha', b', hb', rfl⟩ := hx'
  beta_reduce
  have h2 : ∀ {c c' : G}, c ^ 2 = 1 → c' ∈ zpowers c → c' = 1 ∨ c' = c := by
    intro c c' hc hc'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc'
    rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
    · left
      rw [zpow_mul, show c ^ (2 : ℤ) = 1 by exact_mod_cast hc, one_zpow]
    · right
      rw [zpow_add, zpow_mul, show c ^ (2 : ℤ) = 1 by exact_mod_cast hc, one_zpow, one_mul,
        zpow_one]
  rcases h2 ha ha' with h1 | h1 <;> rcases h2 hb hb' with h3 | h3 <;> rw [h1, h3]
  · left
    rw [one_mul]
  · right
    right
    left
    rw [one_mul]
  · right
    left
    rw [mul_one]
  · right
    right
    right
    rfl

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

theorem IsBeta411.ne_one {S V : Subgroup X} {w z β : X} (hβ : IsBeta411 t L S w z V β) :
    β ≠ 1 := fun h1 => hβ.not_mem (h1 ▸ one_mem _)

namespace Standing

theorem t_ne_one (h : Standing t L p f) : t ≠ 1 := by
  intro ht
  have := h.config.orderOf_eq
  rw [ht, orderOf_one] at this
  exact absurd this (by norm_num)

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem z_ne_one (hσ : Setup42 h hS w z) : z ≠ 1 := by
  intro hz
  have := hσ.z_order
  rw [hz, orderOf_one] at this
  exact absurd this (by norm_num)

theorem eq_of_mem_X_not_tD [Finite X] (hσ : Setup42 h hS w z) {β : X}
    (hβX : β ∈ closure {t, w ^ (orderOf w / 2), z}) (hβD : β ∉ zpowers t ⊔ (S ⊓ L)) :
    ∃ a₀ c₀ : X, (a₀ = 1 ∨ a₀ = t) ∧ (c₀ = 1 ∨ c₀ = z) ∧ β = a₀ * w ^ (orderOf w / 2) * c₀ := by
  obtain ⟨a, b, c, ha, hb, hc, hβ⟩ := hσ.mem_X hβX
  rcases hb with hb | hb
  · exfalso
    apply hβD
    rw [hβ, hb, mul_one]
    refine mul_mem ?_ ?_
    · rcases ha with ha | ha <;> rw [ha]
      · exact one_mem _
      · exact mem_sup_left (mem_zpowers t)
    · rcases hc with hc | hc <;> rw [hc]
      · exact one_mem _
      · exact mem_sup_right hσ.z_mem
  · exact ⟨a, c, ha, hc, by rw [hβ, hb]⟩

theorem mem_closure_beta_z_or [Finite X] (hσ : Setup42 h hS w z) {β : X}
    (hβX : β ∈ closure {t, w ^ (orderOf w / 2), z}) (hβD : β ∉ zpowers t ⊔ (S ⊓ L)) {x : X}
    (hx : x ∈ closure {t, w ^ (orderOf w / 2), z}) :
    x ∈ closure {β, z} ∨ t⁻¹ * x ∈ closure {β, z} := by
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hβB : β ∈ closure ({β, z} : Set X) := subset_closure (by simp)
  have hzB : z ∈ closure ({β, z} : Set X) := subset_closure (by simp)
  have ht2 : t ^ 2 = 1 := hσ.sq_eq_one_of_mem_X htX
  have hz2 : z ^ 2 = 1 := hσ.sq_eq_one_of_mem_X hzX
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq, ht2])
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq, hz2])
  obtain ⟨a₀, c₀, ha₀, hc₀, hβ⟩ := hσ.eq_of_mem_X_not_tD hβX hβD
  obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := hσ.mem_X hx
  have hcB : c ∈ closure ({β, z} : Set X) := by
    rcases hc with hc | hc <;> rw [hc]
    · exact one_mem _
    · exact hzB
  have hc₀B : c₀ ∈ closure ({β, z} : Set X) := by
    rcases hc₀ with hc | hc <;> rw [hc]
    · exact one_mem _
    · exact hzB
  have hXc : ∀ {x y : X}, x ∈ closure {t, w ^ (orderOf w / 2), z} →
      y ∈ closure {t, w ^ (orderOf w / 2), z} → x * y = y * x := fun hx hy => hσ.X_comm hx hy
  have huX : w ^ (orderOf w / 2) ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have haX : a ∈ closure {t, w ^ (orderOf w / 2), z} := by
    rcases ha with ha | ha <;> rw [ha]
    · exact one_mem _
    · exact htX
  have ha₀X : a₀ ∈ closure {t, w ^ (orderOf w / 2), z} := by
    rcases ha₀ with ha | ha <;> rw [ha]
    · exact one_mem _
    · exact htX
  have hcX : c ∈ closure {t, w ^ (orderOf w / 2), z} := by
    rcases hc with hc | hc <;> rw [hc]
    · exact one_mem _
    · exact hzX
  have hc₀X : c₀ ∈ closure {t, w ^ (orderOf w / 2), z} := by
    rcases hc₀ with hc | hc <;> rw [hc]
    · exact one_mem _
    · exact hzX
  have ha₀2 : a₀ * a₀ = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X ha₀X
  have hc₀2 : c₀ * c₀ = 1 := by rw [← sq]; exact hσ.sq_eq_one_of_mem_X hc₀X
  have hu : w ^ (orderOf w / 2) = a₀ * β * c₀ := by
    rw [hβ]
    calc w ^ (orderOf w / 2) = (a₀ * a₀) * w ^ (orderOf w / 2) * (c₀ * c₀) := by
          rw [ha₀2, hc₀2, one_mul, mul_one]
      _ = a₀ * (a₀ * w ^ (orderOf w / 2) * c₀) * c₀ := by group
  have hkey : ∀ a' y : X, y ∈ closure ({β, z} : Set X) → (a' = 1 ∨ a' = t) →
      a' * y ∈ closure ({β, z} : Set X) ∨ t⁻¹ * (a' * y) ∈ closure ({β, z} : Set X) := by
    intro a' y hy ha'
    rcases ha' with ha' | ha' <;> rw [ha']
    · left
      rw [one_mul]
      exact hy
    · right
      rw [← mul_assoc, inv_mul_cancel, one_mul]
      exact hy
  rcases hb with hb | hb
  · rw [hb, mul_one]
    exact hkey a c hcB ha
  ·
    rw [hb, hu]
    have haa₀ : a * a₀ = 1 ∨ a * a₀ = t := by
      rcases ha with ha | ha <;> rcases ha₀ with ha' | ha' <;> rw [ha, ha']
      · left
        rw [one_mul]
      · right
        rw [one_mul]
      · right
        rw [mul_one]
      · left
        rw [← sq, ht2]
    have heq : a * (a₀ * β * c₀) * c = (a * a₀) * (β * (c₀ * c)) := by group
    rw [heq]
    exact hkey (a * a₀) _ (mul_mem hβB (mul_mem hc₀B hcB)) haa₀

theorem not_mem_closure_beta_z [Finite X] (hσ : Setup42 h hS w z) {β : X}
    (hβX : β ∈ closure {t, w ^ (orderOf w / 2), z}) (hβD : β ∉ zpowers t ⊔ (S ⊓ L)) :
    t ∉ closure ({β, z} : Set X) := by
  intro htB
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hβ2 := hσ.sq_eq_one_of_mem_X hβX
  have hz2 := hσ.sq_eq_one_of_mem_X hzX
  have hz2' : z * z = 1 := by rw [← sq, hz2]
  have htD : t ∈ zpowers t ⊔ (S ⊓ L) := mem_sup_left (mem_zpowers t)
  have hzD : z ∈ zpowers t ⊔ (S ⊓ L) := mem_sup_right hσ.z_mem
  rcases mem_closure_pair hβ2 hz2 (hσ.X_comm hβX hzX) htB with h1 | h1 | h1 | h1
  · exact h.t_ne_one h1
  · exact hβD (h1 ▸ htD)
  ·
    have htL : t ∈ L := by rw [h1]; exact hσ.z_mem.2
    exact h.t_ne_one (h.eq_one_of_mem_zpowers_of_mem (mem_zpowers t) htL)
  · apply hβD
    have : β = t * z := by
      calc β = β * z * z := by rw [mul_assoc, hz2', mul_one]
        _ = t * z := by rw [← h1]
    rw [this]
    exact mul_mem htD hzD

variable {V : Subgroup X} {β : X}

theorem beta_ne_z (hσ : Setup42 h hS w z) (hβ : IsBeta411 t L S w z V β) : β ≠ z :=
  fun h1 => hβ.not_mem (h1 ▸ mem_sup_right hσ.z_mem)

theorem sq_mem_T_of_mem_U [Finite X] (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z)
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hβ : IsBeta411 t L S w z V β) {v : X}
    (hv : v ∈ V ⊓ centralizer ({β} : Set X)) : v ^ 2 ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  have hvβ : v * β * v⁻¹ = β := by
    have := mem_centralizer_singleton_iff.mp hv.2
    rw [this]
    group
  exact hσ.sq_mem_T_of_fix hKC hV hSV hβ.mem_X hβ.ne_one (hσ.beta_ne_z hβ) hv.1 hvβ

theorem inf_U_S [Finite X] (hσ : Setup42 h hS w z) (hβ : IsBeta411 t L S w z V β) :
    V ⊓ centralizer ({β} : Set X) ⊓ S = zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  refine le_antisymm (fun x hx => ?_) (le_inf hβ.lt.le hσ.T_le)
  rw [← hβ.inf_eq]
  exact Subgroup.mem_inf.mpr ⟨hx.1, hS.le hx.2⟩

theorem relIndex_T_U [Finite X] (hKF : AutPSL2FusionInput) (hσ : Setup42 h hS w z)
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hβ : IsBeta411 t L S w z V β) :
    (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex (V ⊓ centralizer ({β} : Set X)) = 2 ∨
      (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex (V ⊓ centralizer ({β} : Set X)) = 4 := by
  have hUS := hσ.inf_U_S hβ
  have h1 : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex (V ⊓ centralizer ({β} : Set X)) =
      S.relIndex (V ⊓ centralizer ({β} : Set X)) := by
    rw [← hUS, Subgroup.inf_relIndex_left]
  have hle : S.relIndex (V ⊓ centralizer ({β} : Set X)) ≤ S.relIndex V :=
    Subgroup.relIndex_le_of_le_right inf_le_left (relIndex_ne_zero_of_finite S V)
  have h4 := hσ.relIndex_le_four hKF hV hSV
  have hne1 : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex (V ⊓ centralizer ({β} : Set X)) ≠ 1 :=
    fun h' => hβ.lt.ne (le_antisymm hβ.lt.le (Subgroup.relIndex_eq_one.mp h'))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hV.isPGroup.to_le
    (inf_le_left : V ⊓ centralizer ({β} : Set X) ≤ V))
  have hdvd : (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex (V ⊓ centralizer ({β} : Set X)) ∣
      2 ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [he] at hne1 ⊢
  have hle4 : 2 ^ e ≤ 4 := by
    rw [← he, h1]
    rcases h4 with h4 | h4 <;> omega
  rcases e with _ | _ | _ | e
  · exact absurd (pow_zero 2) hne1
  · left
    rfl
  · right
    rfl
  · exfalso
    have : 8 ≤ 2 ^ (e + 1 + 1 + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (e + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem closure_beta_z_le_centralizer [Finite X] (hσ : Setup42 h hS w z)
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    {v : X} (hv : v ∈ V ⊓ centralizer ({β} : Set X)) :
    closure ({β, z} : Set X) ≤ centralizer ({v} : Set X) := by
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  rcases hx with hx | hx <;> rw [hx]
  · exact (mem_centralizer_singleton_iff.mp hv.2).symm
  · have hvz := hσ.conj_z_of_mem_normalizer_T (hV.le hv.1)
    calc z * v = (v * z * v⁻¹) * v := by rw [hvz]
      _ = v * z := by group

theorem center_U [Finite X] (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z)
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hβ : IsBeta411 t L S w z V β) :
    V ⊓ centralizer ({β} : Set X) ⊓ centralizer ((V ⊓ centralizer ({β} : Set X) :
      Subgroup X) : Set X) = closure ({β, z} : Set X) := by
  have hTU := hβ.lt.le
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  refine le_antisymm (fun x hx => ?_) ?_
  ·
    have hxT : x ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
      rw [← hσ.inf_centralizer_X_eq hKC hV hSV]
      refine Subgroup.mem_inf.mpr ⟨hx.1.1, mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact mem_centralizer_iff.mp hx.2 y (hTU (hσ.X_le_T hy))
    have hxX : x ∈ closure {t, w ^ (orderOf w / 2), z} := by
      rw [← hσ.center_T]
      exact Subgroup.mem_inf.mpr ⟨hxT, mem_centralizer_iff.mpr fun y hy =>
        mem_centralizer_iff.mp hx.2 y (hTU hy)⟩
    rcases hσ.mem_closure_beta_z_or hβ.mem_X hβ.not_mem hxX with h1 | h1
    · exact h1
    · exfalso
      have htB := (closure ({β, z} : Set X)).inv_mem h1
      have htZ : t ∈ centralizer ((V ⊓ centralizer ({β} : Set X) : Subgroup X) : Set X) := by
        have h2 : (t⁻¹ * x)⁻¹ ∈ centralizer ((V ⊓ centralizer ({β} : Set X) :
            Subgroup X) : Set X) := by
          refine mem_centralizer_iff.mpr fun y hy => ?_
          have := hσ.closure_beta_z_le_centralizer hV hy htB
          exact (mem_centralizer_singleton_iff.mp this).symm
        have h3 := mul_mem hx.2 h2
        rwa [show x * (t⁻¹ * x)⁻¹ = t by group] at h3
      apply hβ.lt.ne
      rw [← hβ.inf_eq]
      exact inf_eq_left.mpr fun y hy => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp htZ y hy)
  · rw [closure_le]
    rintro x (rfl | rfl)
    · refine Subgroup.mem_inf.mpr ⟨hTU (hσ.X_le_T hβ.mem_X), mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact (mem_centralizer_singleton_iff.mp hy.2)
    · refine Subgroup.mem_inf.mpr ⟨hTU (hσ.X_le_T hzX), mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hvz := hσ.conj_z_of_mem_normalizer_T (hV.le hy.1)
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = x * y := by rw [hvz]

theorem conj_t_mem_of_mem_U [Finite X] (hσ : Setup42 h hS w z)
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hβ : IsBeta411 t L S w z V β) {v : X} (hv : v ∈ V ⊓ centralizer ({β} : Set X)) :
    t⁻¹ * (v * t * v⁻¹) ∈ closure ({β, z} : Set X) := by
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hvX : v * t * v⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
    (mem_normalizer_iff.mp (hσ.normalizer_T_le_normalizer_X (hV.le hv.1)) t).mp htX
  rcases hσ.mem_closure_beta_z_or hβ.mem_X hβ.not_mem hvX with h1 | h1
  · exfalso
    apply hσ.not_mem_closure_beta_z hβ.mem_X hβ.not_mem
    have hc := mem_centralizer_singleton_iff.mp (hσ.closure_beta_z_le_centralizer hV hv h1)
    have : t = v * t * v⁻¹ := by
      calc t = v⁻¹ * ((v * t * v⁻¹) * v) := by group
        _ = v⁻¹ * (v * (v * t * v⁻¹)) := by rw [hc]
        _ = v * t * v⁻¹ := by group
    rw [this]
    exact h1
  · exact h1

theorem inf_W_t [Finite X] (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z)
    (hβ : IsBeta411 t L S w z V β) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({β} : Set X)))
    (hUW : V ⊓ centralizer ({β} : Set X) ≤ W) :
    W ⊓ centralizer ({t} : Set X) = zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  obtain ⟨i, j, hβeq⟩ := hσ.mem_X_not_tD hβ.mem_X hβ.not_mem
  have hSyl := hσ.isSylowOf_centralizer hKC i j
  rw [← hβeq] at hSyl
  exact hSyl.eq_of_le (le_inf (hβ.lt.le.trans hUW) (hσ.T_le.trans hS.le))
    (fun y hy => Subgroup.mem_inf.mpr ⟨hy.2, hW.le hy.1⟩)
    (hW.isPGroup.to_le inf_le_left)

theorem center_W [Finite X] (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z)
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hβ : IsBeta411 t L S w z V β) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({β} : Set X)))
    (hUW : V ⊓ centralizer ({β} : Set X) ≤ W) :
    β ∈ W ⊓ centralizer (W : Set X) ∧
      W ⊓ centralizer (W : Set X) ≤ closure ({β, z} : Set X) := by
  have hTU := hβ.lt.le
  have htW : t ∈ W := hUW (hTU (mem_sup_left (mem_sup_left (mem_zpowers t))))
  constructor
  · refine Subgroup.mem_inf.mpr ⟨hUW (hTU (hσ.X_le_T hβ.mem_X)),
      mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact mem_centralizer_singleton_iff.mp (hW.le hy)
  · intro x hx
    have hxT : x ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
      rw [← hσ.inf_W_t hKC hβ hW hUW]
      exact Subgroup.mem_inf.mpr ⟨hx.1, mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hx.2 t htW).symm⟩
    rw [← hσ.center_U hKC hV hSV hβ]
    exact Subgroup.mem_inf.mpr ⟨hTU hxT, mem_centralizer_iff.mpr fun y hy =>
      mem_centralizer_iff.mp hx.2 y (hUW hy)⟩

theorem ncard_conj_t_U (hβ : IsBeta411 t L S w z V β) :
    {y : X | ∃ v ∈ V ⊓ centralizer ({β} : Set X), v * t * v⁻¹ = y}.ncard =
      (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex (V ⊓ centralizer ({β} : Set X)) := by
  rw [ncard_conj_orbit _ (hβ.lt.le (mem_sup_left (mem_sup_left (mem_zpowers t)))),
    ← inf_relIndex_right, inf_comm (centralizer ({t} : Set X)), hβ.inf_eq]

theorem relIndex_T_U_eq_four_tfae [Finite X] (hKF : AutPSL2FusionInput)
    (hσ : Setup42 h hS w z)
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) (hβ : IsBeta411 t L S w z V β) :
    List.TFAE [(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w).relIndex (V ⊓ centralizer ({β} : Set X)) = 4,
      ∃ g ∈ centralizer ({β} : Set X), g * t * g⁻¹ = t * β,
      ∀ c ∈ closure ({β, z} : Set X), ∃ v ∈ V ⊓ centralizer ({β} : Set X),
        v * t * v⁻¹ = t * c] := by
  classical
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hβ2 := hσ.sq_eq_one_of_mem_X hβ.mem_X
  have hz2 := hσ.sq_eq_one_of_mem_X hzX
  have hβz := hσ.X_comm hβ.mem_X hzX
  have hβ1 := hβ.ne_one
  have hz1 := hσ.z_ne_one
  have hβz' := hσ.beta_ne_z hβ
  have hz2' : z * z = 1 := by rw [← sq, hz2]
  set O := {y : X | ∃ v ∈ V ⊓ centralizer ({β} : Set X), v * t * v⁻¹ = y} with hO
  have hOsub : O ⊆ (fun c => t * c) '' (closure ({β, z} : Set X) : Set X) := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨_, hσ.conj_t_mem_of_mem_U hV hβ hv, by group⟩
  have hB4 : ((fun c => t * c) '' (closure ({β, z} : Set X) : Set X)).ncard ≤ 4 := by
    have hsub : (closure ({β, z} : Set X) : Set X) ⊆ {1, β, z, β * z} := by
      intro x hx
      rcases mem_closure_pair hβ2 hz2 hβz hx with h1 | h1 | h1 | h1 <;> rw [h1] <;> simp
    calc ((fun c => t * c) '' (closure ({β, z} : Set X) : Set X)).ncard ≤
        (closure ({β, z} : Set X) : Set X).ncard := Set.ncard_image_le (Set.toFinite _)
      _ ≤ ({1, β, z, β * z} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 4 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
        exact Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  have hOcard := ncard_conj_t_U hβ
  rw [← hO] at hOcard
  obtain ⟨v₁, hv₁, -, -, hv₁t⟩ := hβ.exists_mem
  tfae_have 1 → 3 := by
    intro h4 c hc
    have heq : O = (fun c => t * c) '' (closure ({β, z} : Set X) : Set X) :=
      Set.eq_of_subset_of_ncard_le hOsub (by rw [hOcard, h4]; exact hB4) (Set.toFinite _)
    have : t * c ∈ O := by
      rw [heq]
      exact ⟨c, hc, rfl⟩
    obtain ⟨v, hv, hvt⟩ := this
    exact ⟨v, hv, hvt⟩
  tfae_have 3 → 2 := by
    intro h3
    obtain ⟨v, hv, hvt⟩ := h3 β (subset_closure (by simp))
    exact ⟨v, hv.2, hvt⟩
  tfae_have 2 → 1 := by
    rintro ⟨g, hg, hgt⟩
    have htβX : g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} := by
      rw [hgt]
      exact mul_mem (subset_closure (by simp)) hβ.mem_X
    obtain ⟨v₂, hv₂, hv₂t⟩ := hβ.fusion g hg htβX
    have htO : t ∈ O := ⟨1, one_mem _, by group⟩
    have htβO : t * β ∈ O := ⟨v₂, hv₂, hv₂t.trans hgt⟩
    have hv₁O : v₁ * t * v₁⁻¹ ∈ O := ⟨v₁, hv₁, rfl⟩
    have hne1 : t ≠ t * β := fun h' => hβ1 (by
      calc β = t⁻¹ * (t * β) := by group
        _ = 1 := by rw [← h']; group)
    have hne2 : t ≠ v₁ * t * v₁⁻¹ := by
      rcases hv₁t with h' | h' <;> rw [h'] <;> intro h''
      · exact hz1 (by
          calc z = t⁻¹ * (t * z) := by group
            _ = 1 := by rw [← h'']; group)
      · apply hβz'
        have : β * z = 1 := by
          calc β * z = t⁻¹ * (t * β * z) := by group
            _ = 1 := by rw [← h'']; group
        calc β = β * z * z := by rw [mul_assoc, hz2', mul_one]
          _ = z := by rw [this, one_mul]
    have hne3 : t * β ≠ v₁ * t * v₁⁻¹ := by
      rcases hv₁t with h' | h' <;> rw [h'] <;> intro h''
      · exact hβz' (mul_left_cancel h'')
      · apply hz1
        calc z = (t * β)⁻¹ * (t * β * z) := by group
          _ = 1 := by rw [← h'']; group
    have h3 : 3 ≤ O.ncard := by
      have hsub : ({t, t * β, v₁ * t * v₁⁻¹} : Set X) ⊆ O := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact htO
        · exact htβO
        · exact hv₁O
      have hc3 : ({t, t * β, v₁ * t * v₁⁻¹} : Set X).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem, Set.ncard_pair hne3]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hne1, hne2⟩
      calc 3 = ({t, t * β, v₁ * t * v₁⁻¹} : Set X).ncard := hc3.symm
        _ ≤ O.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rcases hσ.relIndex_T_U hKF hV hSV hβ with h' | h'
    · omega
    · exact h'
  tfae_finish

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
