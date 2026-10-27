module

public import CFSG.ClassicalInvolution.Asc77.AscCX8D
public import CFSG.ClassicalInvolution.Asc77.AscCX7
public import CFSG.ClassicalInvolution.Asc77.AscC25W18
public import CFSG.ClassicalInvolution.ModelFacts.L6CFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Witness

variable {G : Type} [Group G]

theorem exists_witness_of_ext {S : Subgroup G} {z a y b : G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzS : ∀ s ∈ S, s * z = z * s)
    (haS : a ∈ S) (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hconj : ∀ s ∈ S, s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hyS : y ∈ S) (hya : y * a = a * y) (hy2 : C25W.InFour a z (y * y))
    (hyc : ∀ s ∈ S, C25W.InFour a z (s * y * s⁻¹ * y⁻¹)) (hyV : ¬ C25W.InFour a z y)
    (hbS : b ∈ S) (hb2 : b * b = 1) :
    ∃ x ∈ ({a, y, y * a} : Set G), x ≠ 1 ∧ x ≠ b ∧ x * z ≠ 1 ∧ x * z ≠ b ∧ x * b = b * x ∧
      C25W.InFour b z (x * x) := by
  have hza : a * z = z * a := hzS a haS
  have hzy : y * z = z * y := hzS y hyS
  have hzb : b * z = z * b := hzS b hbS
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hy1 : y ≠ 1 := fun h => hyV (Or.inl h)
  have hya' : y ≠ a := fun h => hyV (Or.inr (Or.inl h))
  have hyz : y ≠ z := fun h => hyV (Or.inr (Or.inr (Or.inl h)))
  have hyaz : y ≠ a * z := fun h => hyV (Or.inr (Or.inr (Or.inr h)))
  have hmz : ∀ u v : G, u * z = v → u = v * z := by
    intro u v h
    calc u = u * z * z := by rw [mul_assoc, hz2, mul_one]
      _ = v * z := by rw [h]
  rcases hconj b hbS with hba | hba
  ·
    have hbac : b * a = a * b := by
      calc b * a = b * a * b⁻¹ * b := by group
        _ = a * b := by rw [hba]
    by_cases hab : a = b ∨ a = b * z
    ·
      have hb' : b = a ∨ b = a * z := by
        rcases hab with h | h
        · exact Or.inl h.symm
        · right
          calc b = b * z * z := by rw [mul_assoc, hz2, mul_one]
            _ = a * z := by rw [← h]
      refine ⟨y, by simp, hy1, ?_, ?_, ?_, ?_, ?_⟩
      · rintro rfl
        rcases hb' with h | h
        · exact hya' h
        · exact hyaz h
      · intro h
        exact hyz (by simpa using hmz y 1 h)
      · intro h
        rcases hb' with rfl | rfl
        · exact hyaz (hmz y b h)
        · apply hya'
          calc y = a * z * z := hmz y (a * z) h
            _ = a := by rw [mul_assoc, hz2, mul_one]
      · rcases hb' with rfl | rfl
        · exact hya
        · calc y * (a * z) = (y * a) * z := by group
            _ = (a * y) * z := by rw [hya]
            _ = a * (y * z) := by group
            _ = a * (z * y) := by rw [hzy]
            _ = (a * z) * y := by group
      · rcases hb' with rfl | rfl
        · exact hy2
        · rcases hy2 with h | h | h | h
          · exact Or.inl h
          · right; right; right
            rw [h, mul_assoc, hz2, mul_one]
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inl h)
    ·
      push Not at hab
      refine ⟨a, by simp, ha1, hab.1, ?_, ?_, hbac.symm, Or.inl ha2⟩
      · intro h
        exact haz (by simpa using hmz a 1 h)
      · intro h
        exact hab.2 (hmz a b h)
  ·
    have hnc : ∀ u : G, u * a = a * u → u ≠ b := by
      rintro u hu rfl
      apply hz1
      have h1 : u * a * u⁻¹ = a := by rw [hu]; group
      rw [hba] at h1
      calc z = a⁻¹ * (a * z) := by group
        _ = 1 := by rw [h1, inv_mul_cancel]
    have hyza : (y * z) * a = a * (y * z) := by
      calc (y * z) * a = y * (z * a) := by group
        _ = y * (a * z) := by rw [hza]
        _ = (y * a) * z := by group
        _ = (a * y) * z := by rw [hya]
        _ = a * (y * z) := by group
    set w := b * y * b⁻¹ * y⁻¹ with hw
    have hwy : b * y * b⁻¹ = w * y := by rw [hw]; group
    have hbw : (b * w * b⁻¹) * w = 1 := by
      have h1 : y = (b * w * b⁻¹) * w * y := by
        calc y = b * (b * y * b⁻¹) * b⁻¹ := by
              rw [show b * (b * y * b⁻¹) * b⁻¹ = (b * b) * y * (b * b)⁻¹ by group, hb2]
              group
          _ = b * (w * y) * b⁻¹ := by rw [hwy]
          _ = (b * w * b⁻¹) * (b * y * b⁻¹) := by group
          _ = (b * w * b⁻¹) * w * y := by rw [hwy]; group
      calc (b * w * b⁻¹) * w = (b * w * b⁻¹) * w * y * y⁻¹ := by group
        _ = 1 := by rw [← h1, mul_inv_cancel]
    have hbaz : b * (a * z) * b⁻¹ = a := by
      calc b * (a * z) * b⁻¹ = (b * a * b⁻¹) * (b * z * b⁻¹) := by group
        _ = a * z * z := by rw [hba, hzb]; group
        _ = a := by rw [mul_assoc, hz2, mul_one]
    have hw1z : w = 1 ∨ w = z := by
      rcases hyc b hbS with h | h | h | h
      · exact Or.inl h
      · exfalso
        have h' : w = a := by rw [hw]; exact h
        rw [h', hba] at hbw
        apply hz1
        calc z = a * z * a := by rw [mul_assoc, ← hza, ← mul_assoc, ha2, one_mul]
          _ = 1 := hbw
      · exact Or.inr h
      · exfalso
        have h' : w = a * z := by rw [hw]; exact h
        rw [h', hbaz] at hbw
        apply hz1
        calc z = a * (a * z) := by rw [← mul_assoc, ha2, one_mul]
          _ = 1 := hbw
    have hy2' : b * (y * y) * b⁻¹ = y * y → y * y = 1 ∨ y * y = z := by
      intro hinv
      rcases hy2 with h | h | h | h
      · exact Or.inl h
      · exfalso
        rw [h, hba] at hinv
        apply hz1
        calc z = a⁻¹ * (a * z) := by group
          _ = 1 := by rw [hinv, inv_mul_cancel]
      · exact Or.inr h
      · exfalso
        rw [h, hbaz] at hinv
        apply hz1
        calc z = a⁻¹ * (a * z) := by group
          _ = 1 := by rw [← hinv, inv_mul_cancel]
    rcases hw1z with hw1 | hwz
    ·
      have hby : b * y * b⁻¹ = y := by rw [hwy, hw1, one_mul]
      have hyy : y * y = 1 ∨ y * y = z := hy2' (by
        calc b * (y * y) * b⁻¹ = (b * y * b⁻¹) * (b * y * b⁻¹) := by group
          _ = y * y := by rw [hby])
      refine ⟨y, by simp, hy1, hnc y hya, ?_, hnc _ hyza, ?_, ?_⟩
      · intro h
        exact hyz (by simpa using hmz y 1 h)
      · calc y * b = b * y * b⁻¹ * b := by rw [hby]
          _ = b * y := by group
      · rcases hyy with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
    ·
      have hby : b * y * b⁻¹ = z * y := by rw [hwy, hwz]
      have hyy : y * y = 1 ∨ y * y = z := hy2' (by
        calc b * (y * y) * b⁻¹ = (b * y * b⁻¹) * (b * y * b⁻¹) := by group
          _ = z * y * (z * y) := by rw [hby]
          _ = z * (y * z) * y := by group
          _ = z * (z * y) * y := by rw [hzy]
          _ = (z * z) * (y * y) := by group
          _ = y * y := by rw [hz2, one_mul])
      have hyac : (y * a) * a = a * (y * a) := by
        calc (y * a) * a = (a * y) * a := by rw [hya]
          _ = a * (y * a) := by group
      have hyazc : (y * a * z) * a = a * (y * a * z) := by
        calc (y * a * z) * a = y * a * (z * a) := by group
          _ = y * a * (a * z) := by rw [hza]
          _ = (y * a) * a * z := by group
          _ = a * (y * a) * z := by rw [hyac]
          _ = a * (y * a * z) := by group
      have hbya : b * (y * a) * b⁻¹ = y * a := by
        calc b * (y * a) * b⁻¹ = (b * y * b⁻¹) * (b * a * b⁻¹) := by group
          _ = z * y * (a * z) := by rw [hby, hba]
          _ = (z * y) * (z * a) := by rw [hza]
          _ = (y * z) * (z * a) := by rw [hzy]
          _ = y * (z * z) * a := by group
          _ = y * a := by rw [hz2, mul_one]
      refine ⟨y * a, by simp, ?_, hnc _ hyac, ?_, hnc _ hyazc, ?_, ?_⟩
      · intro h
        apply hya'
        calc y = y * a * a⁻¹ := by group
          _ = a := by rw [h, one_mul, inv_eq_of_mul_eq_one_right ha2]
      · intro h
        apply hyaz
        calc y = y * a * z * (a * z)⁻¹ := by group
          _ = (a * z)⁻¹ := by rw [h, one_mul]
          _ = a * z := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hz2, inv_eq_of_mul_eq_one_right ha2, hza]
      · calc y * a * b = b * (y * a) * b⁻¹ * b := by rw [hbya]
          _ = b * (y * a) := by group
      · have hsq : (y * a) * (y * a) = y * y := by
          calc (y * a) * (y * a) = y * (a * y) * a := by group
            _ = y * (y * a) * a := by rw [hya]
            _ = y * y * (a * a) := by group
            _ = y * y := by rw [ha2, mul_one]
        rw [hsq]
        rcases hyy with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))

end Witness

section Main

variable {p f : ℕ} [Fact p.Prime]



theorem exists_badCompl_of_bad {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
    {t u₁ u₂ : G} (h6 : Layer6Twin p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G}
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) {y : G}
    (hyA : y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hya : y * a = a * y) (hy2 : C25W.InFour a z (y * y))
    (hyc : ∀ s ∈ (S : Subgroup G), C25W.InFour a z (s * y * s⁻¹ * y⁻¹))
    (hyV : ¬ C25W.InFour a z y) {b : G}
    (hbA : b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hb1 : b ≠ 1) (hbbad : z ∉ zStarOf (Subgroup.centralizer ({b} : Set G))) :
    ∃ D : Subgroup G, D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ∧
      b ∈ D ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G)) ∧
      ∀ g ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        g ∈ D ∨ g * z ∈ D := by
  classical
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hD₀A : Subgroup.zpowers b ≤
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hbA
  have hD₀bad : z ∉ zStarOf (Subgroup.centralizer (Subgroup.zpowers b : Set G)) := by
    rwa [centralizer_zpowers_eq_singleton']
  have hD₀1 : Subgroup.zpowers b ≠ ⊥ := by
    intro h
    apply hb1
    have : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
    rwa [h, Subgroup.mem_bot] at this
  have hsmall : Nat.card (Subgroup.zpowers b) < 4 → ∃ x ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G), x ∉ Subgroup.zpowers b ∧
        x * z ∉ Subgroup.zpowers b ∧ (∀ d ∈ Subgroup.zpowers b, x * d = d * x) ∧
        (x * x ∈ Subgroup.zpowers b ∨ x * x * z ∈ Subgroup.zpowers b) := by
    intro hlt
    have hb2 : b * b = 1 := by
      have h2 : IsPGroup 2 (Subgroup.zpowers b) :=
        S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hbA.1)
      obtain ⟨n, hn⟩ := h2.exists_card_eq
      rw [Nat.card_zpowers] at hn hlt
      have hn1 : n ≤ 1 := by
        by_contra h
        push Not at h
        have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
        omega
      have hdvd : orderOf b ∣ 2 ^ 1 := by
        rw [hn]
        exact Nat.pow_dvd_pow 2 hn1
      have h := orderOf_dvd_iff_pow_eq_one.mp hdvd
      rwa [pow_one, pow_two] at h
    obtain ⟨x, hxset, hx1, hxb, hxz1, hxzb, hxbc, hxx⟩ := exists_witness_of_ext hz2 hz1
      hyp.hzS haA.1 ha2 ha1 haz hconj hyA.1 hya hy2 hyc hyV hbA.1 hb2
    have hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxset
      rcases hxset with rfl | rfl | rfl
      · exact haA
      · exact hyA
      · exact Subgroup.mul_mem _ hyA haA
    have hmem : ∀ g ∈ Subgroup.zpowers b, g = 1 ∨ g = b := fun g hg =>
      mem_zpowers_of_sq hb2 hg
    refine ⟨x, hxA, ?_, ?_, ?_, ?_⟩
    · intro h
      rcases hmem x h with h | h
      · exact hx1 h
      · exact hxb h
    · intro h
      rcases hmem _ h with h | h
      · exact hxz1 h
      · exact hxzb h
    · intro d hd
      rcases hmem d hd with rfl | rfl
      · simp
      · exact hxbc
    · rcases hxx with h | h | h | h
      · left
        rw [h]
        exact one_mem _
      · left
        rw [h]
        exact Subgroup.mem_zpowers b
      · right
        rw [h, hz2]
        exact one_mem _
      · right
        rw [h, mul_assoc, hz2, mul_one]
        exact Subgroup.mem_zpowers b
  obtain ⟨D, hDA, hD₀D, hDbad, hcov⟩ := exists_bad_complement h6 hyp hD₀A hD₀bad hD₀1 hsmall
  exact ⟨D, hDA, hD₀D (Subgroup.mem_zpowers b), hDbad, hcov⟩

theorem centExtMix_of (h6 : Layer6Twin p f) : C25W.CentExtMix p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hya hy2 hyc
    hmix
  by_contra hyV
  obtain ⟨x, hxA, hxz, -, hxgood⟩ := hmix
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hzA : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    T7T.z_mem_centralizer_of_hyp hyp
  set A : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
    with hA
  set 𝒟 : Set (Subgroup G) := {D | D ≤ A ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G)) ∧
    ∀ g ∈ A, g ∈ D ∨ g * z ∈ D} with h𝒟
  set N : Subgroup G := A ⊓ ⨅ D ∈ 𝒟, D with hN
  have hmemN : ∀ g, g ∈ N ↔ g ∈ A ∧ ∀ D ∈ 𝒟, g ∈ D := by
    intro g
    simp only [hN, Subgroup.mem_inf, Subgroup.mem_iInf]
  obtain ⟨D₁, hD₁A, -, hD₁bad, hD₁cov, -⟩ :=
    exists_bad_complement_of_ext h6 hyp haA ha2 ha1 haz hbad hyA hya hy2 hyV
  have hD₁ : D₁ ∈ 𝒟 := ⟨hD₁A, hD₁bad, hD₁cov⟩
  have hzD : ∀ D ∈ 𝒟, z ∉ D := fun D hD => not_mem_of_badSub hyp hD.1 hD.2.1
  have hbadD : ∀ D ∈ 𝒟, ∀ g ∈ D, g ≠ 1 → z ∉ zStarOf (Subgroup.centralizer ({g} : Set G)) :=
    fun D hD g hg _ => C25W.not_mem_zStarOf_of_mem_badSub hg
      (fun y hy => hzS y (hD.1 hy).1) hD.2.1
  have hNA : N ≤ A := inf_le_left
  have hND : ∀ D ∈ 𝒟, N ≤ D := fun D hD g hg => ((hmemN g).mp hg).2 D hD
  have hxN : x ∈ N := by
    refine (hmemN x).mpr ⟨hxA, fun D hD => ?_⟩
    rcases hD.2.2 x hxA with h | h
    · exact h
    · exfalso
      by_cases hxz1 : x * z = 1
      · apply hxz
        have : x = z := by
          calc x = x * z * z := by rw [mul_assoc, hz2, mul_one]
            _ = z := by rw [hxz1, one_mul]
        rw [this]
        exact Subgroup.mem_zpowers z
      · exact hbadD D hD _ h hxz1 hxgood
  have hN1 : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hxN
    apply hxz
    rw [hxN]
    exact one_mem _
  have hNbad : ∀ n ∈ N, n ≠ 1 → z ∉ zStarOf (Subgroup.centralizer ({n} : Set G)) :=
    fun n hn hn1 => hbadD D₁ hD₁ n (hND D₁ hD₁ hn) hn1
  have hNgood : ∀ n ∈ N, n ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({n * z} : Set G)) := by
    intro n hn hn1
    by_contra hng
    have hnz1 : n * z ≠ 1 := by
      intro h
      apply hzD D₁ hD₁
      have : n = z := by
        calc n = n * z * z := by rw [mul_assoc, hz2, mul_one]
          _ = z := by rw [h, one_mul]
      rw [← this]
      exact hND D₁ hD₁ hn
    obtain ⟨D', hD'A, hnzD', hD'bad, hD'cov⟩ := exists_badCompl_of_bad h6 hyp haA ha2 ha1 haz
      hconj hyA hya hy2 hyc hyV (A.mul_mem (hNA hn) hzA) hnz1 hng
    have hD' : D' ∈ 𝒟 := ⟨hD'A, hD'bad, hD'cov⟩
    apply hzD D' hD'
    have e1 : z = n⁻¹ * (n * z) := by group
    rw [e1]
    exact D'.mul_mem (D'.inv_mem (hND D' hD' hn)) hnzD'
  have hAsc : ∀ g ∈ A, ∀ c : G, c * z * c⁻¹ = z → c * g * c⁻¹ ∈ (S : Subgroup G) →
      c * g * c⁻¹ ∈ A := by
    intro g hg c hc hcS
    have h1 := mem_trivialOnQuot_of_mem_A hyp hg
    exact C25Y.conj_mem_Csub hyp h1.1 h1.2 hc hcS
  have hsc := C25W.stronglyClosed_inter_of_good hz2 hAsc 𝒟 (fun D hD => hD.2.2) hzD hbadD hNA
    hND (fun g hg hall => (hmemN g).mpr ⟨hg, hall⟩) hNgood
  exact false_of_mixedClosed h6 (ModelFacts.L6C.layer6Cen4_proved p f) hyp hNA hN1 hsc hNbad
    hNgood

theorem centExt_of_noMixParity (h6 : Layer6Twin p f) (h : NoMixParity p f) :
    C25W.CentExt p f :=
  centExt_of h6 (centExtMix_of h6) h

end Main

end CFSG.ClassicalInvolution.Asc77.CX
