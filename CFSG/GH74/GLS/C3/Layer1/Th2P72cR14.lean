module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR12

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS
open CFSG.Walter.Huppert
open scoped commutatorElement

section Assemble

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem dd_mem {X₀ X₁ : Subgroup G} {a y : G} (ha : a ∈ X₀) (hy : y ∈ X₁) :
    ⁅(⁅a⁻¹, y⁆)⁻¹, y⁆ ∈ ⁅⁅X₀, X₁⁆, X₁⁆ :=
  Subgroup.commutator_mem_commutator (Subgroup.inv_mem _
    (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ ha) hy)) hy

theorem ne_one_of_nq {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p ↥P) {x : G}
    (hx : x ∈ normalizer (P : Set G)) {z : ↥P} (h : NQ hP ⟨x, hx⟩ z) :
    ⁅(⁅(z : G)⁻¹, x⁆)⁻¹, x⁆ ≠ 1 := by
  obtain ⟨hw, hnu⟩ := nuP_mk_eq hP hx z
  intro h1
  apply h
  change nuP hP ⟨x, hx⟩ (QuotientGroup.mk z) = 1
  rw [hnu]
  have : (⟨⁅(⁅(z : G)⁻¹, x⁆)⁻¹, x⁆, hw⟩ : ↥P) = 1 := Subtype.ext h1
  rw [this]
  exact QuotientGroup.mk_one _

omit [Finite G] in
theorem conj_mem_inf_centralizer {P A : Subgroup G} {g : G} (hg : g ∈ normalizer (P : Set G))
    (hgA : ∀ a ∈ A, g * a = a * g) {z : G} (hz : z ∈ P ⊓ centralizer (A : Set G)) :
    g * z * g⁻¹ ∈ P ⊓ centralizer (A : Set G) := by
  obtain ⟨hzP, hzA⟩ := Subgroup.mem_inf.1 hz
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hg z).1 hzP, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 := hgA a ha
  have h2 := Subgroup.mem_centralizer_iff.1 hzA a ha
  have h3 : g⁻¹ * a = a * g⁻¹ := by
    calc g⁻¹ * a = g⁻¹ * (a * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * a) * g⁻¹ := by rw [h1]
      _ = a * g⁻¹ := by group
  calc a * (g * z * g⁻¹) = (a * g) * z * g⁻¹ := by group
    _ = (g * a) * z * g⁻¹ := by rw [h1]
    _ = g * (a * z) * g⁻¹ := by group
    _ = g * (z * a) * g⁻¹ := by rw [h2]
    _ = g * z * (a * g⁻¹) := by group
    _ = g * z * (g⁻¹ * a) := by rw [h3]
    _ = g * z * g⁻¹ * a := by group

theorem exists_index_two {V : Subgroup G} (hV : CFSG.IsElementaryAbelian 2 ↥V)
    (hrk : 1 ≤ pRank 2 ↥V) : ∃ W : Subgroup G, W ≤ V ∧ Nat.card V = 2 * Nat.card W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C3.Layer1.Back.card_eq_two_pow_pRank hV
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥V) 2 (n := pRank 2 ↥V - 1)
    (by rw [hc]; exact pow_dvd_pow 2 (Nat.sub_le _ _))
  refine ⟨K.map V.subtype, Subgroup.map_subtype_le K, ?_⟩
  rw [Subgroup.card_map_of_injective V.subtype_injective, hK, hc]
  obtain ⟨r, hr⟩ : ∃ r, pRank 2 ↥V = r + 1 := ⟨pRank 2 ↥V - 1, by omega⟩
  rw [hr]
  simp [pow_succ, mul_comm]

theorem eq_sup_zpowers_of_index_two {V F : Subgroup G} (hFV : F ≤ V)
    (hcard : Nat.card V = 2 * Nat.card F) {v : G} (hv : v ∈ V) (hvF : v ∉ F) :
    V = F ⊔ zpowers v := by
  have hSV : F ⊔ zpowers v ≤ V := sup_le hFV (zpowers_le.2 hv)
  have h1 : Nat.card F ∣ Nat.card ↥(F ⊔ zpowers v) := Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card ↥(F ⊔ zpowers v) ∣ Nat.card V := Subgroup.card_dvd_of_le hSV
  obtain ⟨d, hd⟩ := h1
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have h3 : d ∣ 2 := by
    rw [hd, hcard] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hFpos (by rwa [mul_comm 2 (Nat.card F)] at h2)
  rcases (Nat.dvd_prime Nat.prime_two).1 h3 with h | h
  · exfalso
    rw [h, mul_one] at hd
    have hFS : F = F ⊔ zpowers v := Subgroup.eq_of_le_of_card_ge le_sup_left hd.le
    exact hvF (hFS ▸ Subgroup.mem_sup_right (mem_zpowers v))
  · symm
    refine Subgroup.eq_of_le_of_card_ge hSV ?_
    rw [hd, h, hcard, mul_comm]

theorem assemble_core {p : ℕ} [Fact p.Prime] {P A B Hc : Subgroup G} (hP : IsPGroup p ↥P)
    (hPO : P ≤ pPrimeCoreOf 2 Hc) {x₁ b : G} (hx₁Hc : x₁ ∈ Hc)
    (hx₁N : x₁ ∈ normalizer (P : Set G)) (hBN : B ≤ normalizer (P : Set G))
    (hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a) (hAB : A ≤ B)
    (hAx : ∀ a ∈ A, a * x₁ = x₁ * a) (hbx : b * x₁ * b⁻¹ = x₁⁻¹) (hx₁odd : Odd (orderOf x₁))
    {z : ↥P} (hzA : (z : G) ∈ centralizer (A : Set G)) (hnq : NQ hP ⟨x₁, hx₁N⟩ z) :
    Odd (Nat.card ↥(P ⊓ centralizer (A : Set G))) ∧ Odd (Nat.card ↥(zpowers x₁)) ∧
      P ⊓ centralizer (A : Set G) ≤ pPrimeCoreOf 2 Hc ∧ zpowers x₁ ≤ Hc ∧
      (∀ a ∈ A, ∀ z ∈ P ⊓ centralizer (A : Set G), a * z = z * a) ∧
      (∀ g ∈ B, ∀ z ∈ P ⊓ centralizer (A : Set G), g * z * g⁻¹ ∈ P ⊓ centralizer (A : Set G)) ∧
      (∀ y ∈ zpowers x₁, ∀ z' ∈ P ⊓ centralizer (A : Set G),
        y * z' * y⁻¹ ∈ P ⊓ centralizer (A : Set G)) ∧
      (∀ y ∈ zpowers x₁, b * y * b⁻¹ = y⁻¹) ∧
      ⁅⁅P ⊓ centralizer (A : Set G), zpowers x₁⁆, zpowers x₁⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle0 : P ⊓ centralizer (A : Set G) ≤ pPrimeCoreOf 2 Hc := inf_le_left.trans hPO
  refine ⟨?_, ?_, hle0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd Hc) (Subgroup.card_dvd_of_le hle0)
  · rw [Nat.card_zpowers]; exact hx₁odd
  · exact (Subgroup.zpowers_le.2 hx₁Hc)
  · intro a ha z hz
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 a ha
  · intro g hg z hz
    exact conj_mem_inf_centralizer (hBN hg) (fun a ha => hBc g hg a (hAB ha)) hz
  · intro y hy z' hz'
    have hyN : y ∈ normalizer (P : Set G) := (Subgroup.zpowers_le.2 hx₁N) hy
    have hyA : ∀ a ∈ A, y * a = a * y := by
      intro a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hc : Commute x₁ a := (hAx a ha).symm
      exact (Commute.zpow_left hc n).eq
    exact conj_mem_inf_centralizer hyN hyA hz'
  · intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← conj_zpow, hbx, inv_zpow]
  · intro hbot
    have hzX : (z : G) ∈ P ⊓ centralizer (A : Set G) := Subgroup.mem_inf.2 ⟨z.2, hzA⟩
    have h1 := dd_mem (X₀ := P ⊓ centralizer (A : Set G)) (X₁ := zpowers x₁) hzX
      (Subgroup.mem_zpowers x₁)
    rw [hbot, Subgroup.mem_bot] at h1
    exact ne_one_of_nq hP hx₁N hnq h1

theorem p79_assemble {p : ℕ} [Fact p.Prime] {P V B Hc : Subgroup G} (hP : IsPGroup p ↥P)
    (hp2 : p ≠ 2) (hPO : P ≤ pPrimeCoreOf 2 Hc) {x₁ b : G} (hx₁Hc : x₁ ∈ Hc)
    (hx₁N : x₁ ∈ normalizer (P : Set G)) (hBN : B ≤ normalizer (P : Set G))
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hVB : V ≤ B) (hrk : 3 ≤ pRank 2 ↥V)
    (hVx : ∀ v ∈ V, v * x₁ = x₁ * v) (hbx : b * x₁ * b⁻¹ = x₁⁻¹) (hx₁odd : Odd (orderOf x₁))
    {z₀ : ↥P} (hz₀ : NQ hP ⟨x₁, hx₁N⟩ z₀) :
    ∃ (W X₀ X₁ : Subgroup G), X₁ = Subgroup.zpowers x₁ ∧ W ≤ V ∧
      Nat.card V = 2 * Nat.card W ∧
      Odd (Nat.card X₀) ∧ Odd (Nat.card X₁) ∧ X₀ ≤ pPrimeCoreOf 2 Hc ∧ X₁ ≤ Hc ∧
      (∀ w ∈ W, ∀ z ∈ X₀, w * z = z * w) ∧ (∀ v ∈ V, ∀ z ∈ X₁, v * z = z * v) ∧
      (∀ g ∈ B, ∀ z ∈ X₀, g * z * g⁻¹ ∈ X₀) ∧ (∀ z ∈ X₁, ∀ z' ∈ X₀, z * z' * z⁻¹ ∈ X₀) ∧
      (∀ z ∈ X₁, b * z * b⁻¹ = z⁻¹) ∧ ⁅⁅X₀, X₁⁆, X₁⁆ ≠ ⊥ ∧
      ((∀ v ∈ V, ∀ z ∈ X₀, v * z = z * v) ∨
        (∀ v ∈ V, v ∉ W → ∃ z ∈ ⁅⁅X₀, X₁⁆, X₁⁆, v * z ≠ z * v)) := by
  classical
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hVel : CFSG.IsElementaryAbelian 2 ↥V := isElementaryAbelian_le hBel hVB
  have hVN : V ≤ normalizer (P : Set G) := hVB.trans hBN
  have hcommz : ∀ v ∈ V, ∀ y ∈ zpowers x₁, v * y = y * v := by
    intro v hv y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (hVx v hv) n)
  rcases exists_selection hP hp2 hVel hrk hVN hx₁N hz₀ with
    ⟨z, hzV, hznq⟩ | ⟨F, hFV, hFcard, ⟨z, hzF, hznq⟩, hnoV⟩
  · obtain ⟨W, hWV, hWcard⟩ := exists_index_two hVel (by omega)
    obtain ⟨hodd0, hodd1, hle0, hle1, hcA, hBinv, hX1inv, hbinv, hne⟩ :=
      assemble_core hP hPO hx₁Hc hx₁N hBN hBc hVB hVx hbx hx₁odd hzV hznq
    refine ⟨W, P ⊓ centralizer (V : Set G), zpowers x₁, rfl, hWV, hWcard, hodd0, hodd1, hle0, hle1,
      fun w hw z hz => hcA w (hWV hw) z hz, hcommz, hBinv, hX1inv, hbinv, hne, Or.inl hcA⟩
  · obtain ⟨hodd0, hodd1, hle0, hle1, hcA, hBinv, hX1inv, hbinv, hne⟩ :=
      assemble_core hP hPO hx₁Hc hx₁N hBN hBc (hFV.trans hVB) (fun a ha => hVx a (hFV ha)) hbx
        hx₁odd hzF hznq
    refine ⟨F, P ⊓ centralizer (F : Set G), zpowers x₁, rfl, hFV, hFcard, hodd0, hodd1, hle0, hle1,
      hcA, hcommz, hBinv, hX1inv, hbinv, hne, Or.inr ?_⟩
    intro v hv hvF
    by_contra hno
    push Not at hno
    have hvN : v ∈ normalizer (P : Set G) := hVN hv
    have hv2 : v * v = 1 := hBsq v (hVB hv)
    have hvx : x₁ * v = v * x₁ := (hVx v hv).symm
    have hvF' : ∀ a ∈ F, v * a = a * v := fun a ha => hBc v (hVB hv) a (hVB (hFV ha))
    have hzX : (z : G) ∈ P ⊓ centralizer (F : Set G) := Subgroup.mem_inf.2 ⟨z.2, hzF⟩
    obtain ⟨hw, hnu⟩ := nuP_mk_eq hP hx₁N z
    have hwZ : ⁅(⁅(z : G)⁻¹, x₁⁆)⁻¹, x₁⁆ ∈ ⁅⁅P ⊓ centralizer (F : Set G), zpowers x₁⁆, zpowers x₁⁆ :=
      dd_mem hzX (Subgroup.mem_zpowers x₁)
    have hvw := hno _ hwZ
    have hfix : fAct P ⟨v, hvN⟩ (nuP hP ⟨x₁, hx₁N⟩ (QuotientGroup.mk z)) =
        nuP hP ⟨x₁, hx₁N⟩ (QuotientGroup.mk z) := by
      rw [hnu, fAct_mk]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact mul_inv_eq_iff_eq_mul.2 hvw
    obtain ⟨z', hz'X, hz'v, hz'nq⟩ := exists_fixed_nq hP hp2
      hx₁N hvN hv2 hvx (fun w hw => conj_mem_inf_centralizer hvN hvF' hw) hzX hznq hfix
    have hVeq : V = F ⊔ zpowers v := eq_sup_zpowers_of_index_two hFV hFcard hv hvF
    have hz'V : (z' : G) ∈ centralizer (V : Set G) := by
      have hz'F := (Subgroup.mem_inf.1 hz'X).2
      have hle : V ≤ centralizer ({(z' : G)} : Set G) := by
        rw [hVeq]
        refine sup_le ?_ ?_
        · intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro c hc
          rw [Set.mem_singleton_iff] at hc
          subst hc
          exact (Subgroup.mem_centralizer_iff.1 hz'F a ha).symm
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro c hc
          rw [Set.mem_singleton_iff] at hc
          subst hc
          have : v * (z' : G) = (z' : G) * v := by
            have := hz'v
            rw [mul_inv_eq_iff_eq_mul] at this
            exact this
          exact this.symm
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have := Subgroup.mem_centralizer_iff.1 (hle ha) (z' : G) (Set.mem_singleton _)
      exact this.symm
    exact hnoV z' hz'V hz'nq

end Assemble

end CFSG.GH74.GLS.Th2.Obs
