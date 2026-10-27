module

public import CFSG.ClassicalInvolution.Asc77.AscC25W14
public import CFSG.ClassicalInvolution.Asc77.AscC25W4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX7Eng

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {R R' : Subgroup G} {z : G}

theorem not_mem_of_badSub_gen
    (hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s)
    {D : Subgroup G}
    (hDA : D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hDbad : z ∉ zStarOf (Subgroup.centralizer (D : Set G)))
    : z ∉ D := by
  intro hzD
  apply hDbad
  refine T7T.mem_zStarOf_of_le ?_ (T7T.mem_zStarOf_centralizer_self z) ?_
  · intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hg) z hzD).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact hzS g (hDA hg).1

theorem exists_bad_complement_of_ext_gen
    (hz2 : z * z = 1)
    (hz1 : z ≠ 1)
    (hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s)
    (hexbad : ∀ {D₀ : Subgroup G} (hD₀A : D₀ ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' :
        Subgroup G) : Set G)) (hD₀bad : z ∉ zStarOf (Subgroup.centralizer (D₀ : Set G))) (hD₀1 : D₀
        ≠ ⊥) (hsmall : Nat.card D₀ < 4 → ∃ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' :
        Subgroup G) : Set G), x ∉ D₀ ∧ x * z ∉ D₀ ∧ (∀ d ∈ D₀, x * d = d * x) ∧ (x * x ∈ D₀ ∨ x * x
        * z ∈ D₀)), ∃ D : Subgroup G, D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' :
        Subgroup G) : Set G) ∧ D₀ ≤ D ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G)) ∧ ∀ g ∈ (S :
        Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), g ∈ D ∨ g * z ∈ D)
    (hsq : ∀ {z x : G} (hz2 : z * z = 1) (hx : x ∈ Subgroup.zpowers z), x = 1 ∨ x = z)
    (hfour : ∀ {D : Subgroup G} (hD2 : IsPGroup 2 D) {a b : G} (ha : a ∈ D) (hb : b ∈ D) (ha1 : a ≠
        1) (hb1 : b ≠ 1) (hab : a ≠ b), 4 ≤ Nat.card D)
    {a : G}
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (ha2 : a * a = 1)
    (ha1 : a ≠ 1)
    (haz : a ≠ z)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    {y : G}
    (hyA : y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hya : y * a = a * y)
    (hy2 : C25W.InFour a z (y * y))
    (hyV : ¬ C25W.InFour a z y)
    : ∃ D : Subgroup G, D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
        ∧ a ∈ D ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G)) ∧ (∀ g ∈ (S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), g ∈ D ∨ g * z ∈ D) ∧ 4 ≤ Nat.card D := by
  classical
  have hza : a * z = z * a := hzS a haA.1
  have hzy : y * z = z * y := hzS y hyA.1
  have hD₀A : Subgroup.zpowers a ≤
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr haA
  have hD₀bad : z ∉ zStarOf (Subgroup.centralizer (Subgroup.zpowers a : Set G)) := by
    rwa [centralizer_zpowers_eq_singleton']
  have hD₀1 : Subgroup.zpowers a ≠ ⊥ := by
    intro h
    apply ha1
    have : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
    rwa [h, Subgroup.mem_bot] at this
  have hmemA : ∀ g, g ∈ Subgroup.zpowers a → g = 1 ∨ g = a := fun g hg =>
    hsq ha2 hg
  have hyD₀ : y ∉ Subgroup.zpowers a := by
    intro h
    rcases hmemA y h with h1 | h1
    · exact hyV (Or.inl h1)
    · exact hyV (Or.inr (Or.inl h1))
  have hyzD₀ : y * z ∉ Subgroup.zpowers a := by
    intro h
    rcases hmemA _ h with h1 | h1
    · apply hyV
      right; right; left
      calc y = y * z * z := by rw [mul_assoc, hz2, mul_one]
        _ = z := by rw [h1, one_mul]
    · apply hyV
      right; right; right
      calc y = y * z * z := by rw [mul_assoc, hz2, mul_one]
        _ = a * z := by rw [h1]
  have hsmall : Nat.card (Subgroup.zpowers a) < 4 → ∃ x ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), x ∉ Subgroup.zpowers a ∧
        x * z ∉ Subgroup.zpowers a ∧ (∀ d ∈ Subgroup.zpowers a, x * d = d * x) ∧
        (x * x ∈ Subgroup.zpowers a ∨ x * x * z ∈ Subgroup.zpowers a) := by
    intro _
    refine ⟨y, hyA, hyD₀, hyzD₀, fun d hd => ?_, ?_⟩
    · rcases hmemA d hd with rfl | rfl
      · simp
      · exact hya
    · rcases hy2 with h | h | h | h
      · left; rw [h]; exact one_mem _
      · left; rw [h]; exact Subgroup.mem_zpowers a
      · right; rw [h, hz2]; exact one_mem _
      · right; rw [h, mul_assoc, hz2, mul_one]; exact Subgroup.mem_zpowers a
  obtain ⟨D, hDA, hD₀D, hDbad, hcov⟩ :=
    hexbad hD₀A hD₀bad hD₀1 hsmall
  have haD : a ∈ D := hD₀D (Subgroup.mem_zpowers a)
  refine ⟨D, hDA, haD, hDbad, hcov, ?_⟩
  have hzD : z ∉ D := by
    intro hzD
    apply hDbad
    refine T7T.mem_zStarOf_of_le ?_ (T7T.mem_zStarOf_centralizer_self z) ?_
    · intro g hg
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hg) z hzD).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hzS g (hDA hg).1
  have hD2 : IsPGroup 2 D := S.isPGroup'.to_le (hDA.trans inf_le_left)
  rcases hcov y hyA with hyD | hyzD
  · refine hfour hD2 haD hyD ha1 (fun h => hyV (Or.inl h)) ?_
    intro h
    exact hyV (Or.inr (Or.inl h.symm))
  · refine hfour hD2 haD hyzD ha1 ?_ ?_
    · intro h
      apply hyV
      right; right; left
      calc y = y * z * z := by rw [mul_assoc, hz2, mul_one]
        _ = z := by rw [h, one_mul]
    · intro h
      apply hyV
      right; right; right
      calc y = y * z * z := by rw [mul_assoc, hz2, mul_one]
        _ = a * z := by rw [← h]

theorem elemAbelian_of_noMix_gen
    (hz2 : z * z = 1)
    (hz1 : z ≠ 1)
    (hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s)
    (hzA : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hexbad : ∀ {D₀ : Subgroup G} (hD₀A : D₀ ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' :
        Subgroup G) : Set G)) (hD₀bad : z ∉ zStarOf (Subgroup.centralizer (D₀ : Set G))) (hD₀1 : D₀
        ≠ ⊥) (hsmall : Nat.card D₀ < 4 → ∃ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' :
        Subgroup G) : Set G), x ∉ D₀ ∧ x * z ∉ D₀ ∧ (∀ d ∈ D₀, x * d = d * x) ∧ (x * x ∈ D₀ ∨ x * x
        * z ∈ D₀)), ∃ D : Subgroup G, D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' :
        Subgroup G) : Set G) ∧ D₀ ≤ D ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G)) ∧ ∀ g ∈ (S :
        Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), g ∈ D ∨ g * z ∈ D)
    (hsq : ∀ {z x : G} (hz2 : z * z = 1) (hx : x ∈ Subgroup.zpowers z), x = 1 ∨ x = z)
    (hfour : ∀ {D : Subgroup G} (hD2 : IsPGroup 2 D) {a b : G} (ha : a ∈ D) (hb : b ∈ D) (ha1 : a ≠
        1) (hb1 : b ≠ 1) (hab : a ≠ b), 4 ≤ Nat.card D)
    (hscm : ∀ {A D' : Subgroup G} {z : G} (hz2 : z * z = 1) (hzA : z ∈ A) (hzc : ∀ g ∈ A, g * z = z
        * g) (hcov : ∀ g ∈ A, g ∈ D' ∨ g * z ∈ D') {d e : G} (hd : d ∈ A) (he : e ∈ A), d * d ∈ D' ∧
        d * e * d⁻¹ * e⁻¹ ∈ D')
    (hnsq : ∀ {A H : Subgroup G} (hA : IsPGroup 2 A) (hHA : H ≤ A) (hne : H ≠ A), ∃ x ∈ A, x ∉ H ∧ x
        ∈ Subgroup.normalizer (H : Set G) ∧ x * x ∈ H)
    {D : Subgroup G}
    (hDA : D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hDbad : z ∉ zStarOf (Subgroup.centralizer (D : Set G)))
    (h4 : 4 ≤ Nat.card D)
    (hnomix : ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), x ∉
        Subgroup.zpowers z → z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) → z ∉ zStarOf
        (Subgroup.centralizer ({x * z} : Set G)))
    : (∀ d ∈ D, d * d = 1) ∧ ∀ d ∈ D, ∀ e ∈ D, d * e = e * d := by
  classical
  set A := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA
  have hzcA : ∀ g ∈ A, g * z = z * g := fun g hg => hzS g hg.1
  have hzD : z ∉ D := not_mem_of_badSub_gen hzS hDA hDbad
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le inf_le_left
  have hD2 : IsPGroup 2 D := hA2.to_le hDA
  have hex : ∀ w ∈ D, w ≠ 1 → ∃ D' : Subgroup G, D' ≤ A ∧ w * z ∈ D' ∧
      z ∉ zStarOf (Subgroup.centralizer (D' : Set G)) ∧ ∀ g ∈ A, g ∈ D' ∨ g * z ∈ D' := by
    intro w hw hw1
    have hwA : w ∈ A := hDA hw
    have hwzA : w * z ∈ A := A.mul_mem hwA hzA
    have hwz : w ≠ z := fun h => hzD (h ▸ hw)
    have hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G)) :=
      C25W.not_mem_zStarOf_of_mem_badSub hw (fun y hy => hzS y (hDA hy).1) hDbad
    have hwnz : w ∉ Subgroup.zpowers z := by
      intro h
      rcases hsq hz2 h with h1 | h1
      · exact hw1 h1
      · exact hwz h1
    have hwzbad := hnomix w hwA hwnz hwbad
    have hwzD : w * z ∉ D := by
      intro h
      apply hzD
      have : z = w⁻¹ * (w * z) := by group
      rw [this]
      exact D.mul_mem (D.inv_mem hw) h
    have hwz1 : w * z ≠ 1 := by
      intro h
      apply hwz
      calc w = w * z * z := by rw [mul_assoc, hz2, mul_one]
        _ = z := by rw [h, one_mul]
    have hD₀A : Subgroup.zpowers (w * z) ≤ A := Subgroup.zpowers_le.mpr hwzA
    have hD₀bad : z ∉ zStarOf (Subgroup.centralizer (Subgroup.zpowers (w * z) : Set G)) := by
      rwa [centralizer_zpowers_eq_singleton']
    have hD₀1 : Subgroup.zpowers (w * z) ≠ ⊥ := by
      intro h
      apply hwz1
      have : w * z ∈ Subgroup.zpowers (w * z) := Subgroup.mem_zpowers _
      rwa [h, Subgroup.mem_bot] at this
    have hsmall : Nat.card (Subgroup.zpowers (w * z)) < 4 → ∃ x ∈ A,
        x ∉ Subgroup.zpowers (w * z) ∧ x * z ∉ Subgroup.zpowers (w * z) ∧
          (∀ d ∈ Subgroup.zpowers (w * z), x * d = d * x) ∧
          (x * x ∈ Subgroup.zpowers (w * z) ∨ x * x * z ∈ Subgroup.zpowers (w * z)) := by
      intro hlt
      have hwz2 : (w * z) * (w * z) = 1 := by
        have h2 : IsPGroup 2 (Subgroup.zpowers (w * z)) := hA2.to_le hD₀A
        obtain ⟨k, hk⟩ := h2.exists_card_eq
        rw [Nat.card_zpowers] at hk hlt
        have hk1 : k ≤ 1 := by
          by_contra h
          have : 4 ≤ 2 ^ k := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hdvd : orderOf (w * z) ∣ 2 := by
          rw [hk]
          interval_cases k <;> norm_num
        have := orderOf_dvd_iff_pow_eq_one.mp hdvd
        rwa [pow_two] at this
      have hw2 : w * w = 1 := by
        have e : (w * z) * (w * z) = w * w := by
          calc (w * z) * (w * z) = w * (z * w) * z := by group
            _ = w * (w * z) * z := by rw [← hzcA w hwA]
            _ = w * w * (z * z) := by group
            _ = w * w := by rw [hz2, mul_one]
        rw [← e, hwz2]
      set C := D ⊓ Subgroup.centralizer ({w} : Set G) with hC
      have hHC : Subgroup.zpowers w ≤ C := Subgroup.zpowers_le.mpr
        ⟨hw, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      have hHne : Subgroup.zpowers w ≠ C := by
        intro hHC'
        have hmem2 : ∀ g ∈ C, g = 1 ∨ g = w := fun g hg =>
          hsq hw2 (hHC' ▸ hg)
        have hnt : Nontrivial ↥D := by
          rw [Subgroup.nontrivial_iff_ne_bot]
          intro h
          rw [h, Subgroup.card_bot] at h4
          omega
        obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
          (hD2.bot_lt_center).ne'
        have hcC : ((c : ↥D) : G) ∈ C := ⟨(c : ↥D).2,
          Subgroup.mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨w, hw⟩)).symm⟩
        rcases hmem2 _ hcC with h | h
        · exact hc1 (Subtype.ext (Subtype.ext h))
        ·
          have hwcen : ∀ d ∈ D, d * w = w * d := by
            intro d hd
            have := Subgroup.mem_center_iff.mp c.2 ⟨d, hd⟩
            have h' := congrArg Subtype.val this
            simp only [Subgroup.coe_mul] at h'
            rw [h] at h'
            exact h'
          have hall : ∀ d ∈ D, d = 1 ∨ d = w := fun d hd =>
            hmem2 d ⟨hd, Subgroup.mem_centralizer_singleton_iff.mpr (hwcen d hd)⟩
          have hle : Nat.card D ≤ Nat.card (Fin 2) := by
            refine Nat.card_le_card_of_injective
              (fun d : D => if (d : G) = 1 then (0 : Fin 2) else 1) fun d₁ d₂ hd => ?_
            apply Subtype.ext
            by_cases h₁ : (d₁ : G) = 1 <;> by_cases h₂ : (d₂ : G) = 1 <;>
              simp only [h₁, h₂, ↓reduceIte] at hd
            · rw [h₁, h₂]
            · exact absurd hd (by decide)
            · exact absurd hd (by decide)
            · rw [(hall d₁ d₁.2).resolve_left h₁, (hall d₂ d₂.2).resolve_left h₂]
          rw [Nat.card_fin] at hle
          omega
      have hC2 : IsPGroup 2 C := hD2.to_le inf_le_left
      obtain ⟨x, hxC, hxH, -, hx2⟩ := hnsq hC2 hHC hHne
      have hxD : x ∈ D := hxC.1
      have hxw : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp hxC.2
      have hmemWZ : ∀ g ∈ Subgroup.zpowers (w * z), g = 1 ∨ g = w * z := fun g hg =>
        hsq hwz2 hg
      refine ⟨x, hDA hxD, ?_, ?_, ?_, ?_⟩
      · intro h
        rcases hmemWZ x h with h1 | h1
        · exact hxH (h1 ▸ Subgroup.one_mem _)
        · exact hwzD (h1 ▸ hxD)
      · intro h
        rcases hmemWZ _ h with h1 | h1
        · apply hzD
          have : z = x⁻¹ * (x * z) := by group
          rw [this, h1, mul_one]
          exact D.inv_mem hxD
        · apply hxH
          have : x = w := by
            calc x = x * z * z⁻¹ := by group
              _ = w := by rw [h1]; group
          rw [this]
          exact Subgroup.mem_zpowers w
      · intro d hd
        rcases hmemWZ d hd with rfl | rfl
        · simp
        · calc x * (w * z) = (x * w) * z := by group
            _ = (w * x) * z := by rw [hxw]
            _ = w * (z * x) := by rw [mul_assoc, hzS x (hDA hxD).1]
            _ = w * z * x := by group
      · rcases hsq hw2 hx2 with h | h
        · left
          rw [h]
          exact one_mem _
        · right
          rw [h]
          exact Subgroup.mem_zpowers _
    obtain ⟨D', hD'A, hD₀D', hD'bad, hD'cov⟩ :=
      hexbad hD₀A hD₀bad hD₀1 hsmall
    exact ⟨D', hD'A, hD₀D' (Subgroup.mem_zpowers _), hD'bad, hD'cov⟩
  have htriv : ∀ g ∈ D, (∀ w ∈ D, w ≠ 1 → ∀ D' : Subgroup G, D' ≤ A → w * z ∈ D' →
      z ∉ zStarOf (Subgroup.centralizer (D' : Set G)) → (∀ h ∈ A, h ∈ D' ∨ h * z ∈ D') →
        g ∈ D') → g = 1 := by
    intro g hg hall
    by_contra hg1
    obtain ⟨D', hD'A, hgzD', hD'bad, hD'cov⟩ := hex g hg hg1
    have hgD' := hall g hg hg1 D' hD'A hgzD' hD'bad hD'cov
    apply not_mem_of_badSub_gen hzS hD'A hD'bad
    have : z = g⁻¹ * (g * z) := by group
    rw [this]
    exact D'.mul_mem (D'.inv_mem hgD') hgzD'
  refine ⟨fun d hd => htriv _ (D.mul_mem hd hd) fun w _ _ D' hD'A _ _ hD'cov =>
    (hscm hz2 hzA hzcA hD'cov (hDA hd) (hDA hd)).1,
    fun d hd e he => ?_⟩
  have h1 := htriv _ (D.mul_mem (D.mul_mem (D.mul_mem hd he) (D.inv_mem hd)) (D.inv_mem he))
    fun w _ _ D' hD'A _ _ hD'cov =>
      (hscm hz2 hzA hzcA hD'cov (hDA hd) (hDA he)).2
  calc d * e = (d * e * d⁻¹ * e⁻¹) * (e * d) := by group
    _ = e * d := by rw [h1, one_mul]

end CX7Eng

end CFSG.ClassicalInvolution.Asc77
