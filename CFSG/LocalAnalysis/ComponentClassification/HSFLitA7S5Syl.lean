module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5T1

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem eq_one_or_of_mem_zpowers {G : Type*} [Group G] {a b : G} (hb : b ^ 2 = 1)
    (h : a ∈ zpowers b) : a = 1 ∨ a = b := by
  obtain ⟨n, rfl⟩ := h
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    simp only
    rw [hk, zpow_mul, show b ^ (2 : ℤ) = 1 by rw [zpow_ofNat]; exact hb, one_zpow]
  · right
    simp only
    rw [hk, zpow_add, zpow_mul, show b ^ (2 : ℤ) = 1 by rw [zpow_ofNat]; exact hb, one_zpow,
      one_mul, zpow_one]

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Sec5Hyp

variable {T₁ : Subgroup X} (H : S.Sec5Hyp T₁)
include H

theorem card_normalizer (I : S.Inst) :
    Nat.card (normalizer (I.E : Set X)) = 24 * Nat.card (centralizer (I.E : Set X)) := by
  rw [I.card_normalizer_eq H.fus, H.ncard_orbitN_four I]
  ring

theorem factorization_normalizer (I : S.Inst) :
    (Nat.card (normalizer (I.E : Set X))).factorization 2 = 7 := by
  have hpos : Nat.card (centralizer (I.E : Set X)) ≠ 0 := Nat.card_pos.ne'
  rw [H.card_normalizer I, mul_comm, Nat.factorization_mul hpos (by norm_num), Finsupp.add_apply,
    I.factorization_centralizer, show (24 : ℕ) = 2 ^ 3 * 3 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd]

omit H in
theorem le_E (I : S.Inst) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer (I.E : Set X)) : P ≤ I.E := by
  have hE2 : IsPGroup 2 I.E := S.data.isPGroup_T.to_le I.E_le_T
  have hPN : P ≤ normalizer (I.E : Set X) := hPC.trans I.centralizer_le_normalizer
  have hp : IsPGroup 2 (I.E ⊔ P : Subgroup X) := hE2.to_sup_of_normal_left' hP hPN
  have heq := I.eq_E_of_le_centralizer hp le_sup_left (sup_le I.E_le_centralizer hPC)
  rw [← heq]
  exact le_sup_right

theorem exists_R : ∃ R : Subgroup X, IsPGroup 2 R ∧ R ≤ normalizer (S.inst₁.E : Set X) ∧
    (∀ Q : Subgroup X, IsPGroup 2 Q → R ≤ Q → Q ≤ normalizer (S.inst₁.E : Set X) → Q = R) ∧
    S.T₂of T₁ ≤ R ∧ Nat.card R = 128 ∧ R ⊓ centralizer (S.inst₁.E : Set X) = S.inst₁.E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (S.inst₁.E : Set X)
  have hT₂N : S.T₂of T₁ ≤ N := H.T₂of_le_normalizer S.inst₁
  have hT₂p : IsPGroup 2 (S.T₂of T₁) := H.isPGroup.to_le T₂of_le
  have hT' : IsPGroup 2 ((S.T₂of T₁).subgroupOf N) :=
    hT₂p.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  set R : Subgroup X := (Q : Subgroup N).map N.subtype with hR
  have hRN : R ≤ N := map_subtype_le _
  have hcard : Nat.card R = 128 := by
    rw [hR, card_map_of_injective (subtype_injective _), Sylow.card_eq_multiplicity,
      H.factorization_normalizer S.inst₁]
    rfl
  have hp : IsPGroup 2 R := Q.isPGroup'.map _
  have hTR : S.T₂of T₁ ≤ R := fun g hg => ⟨⟨g, hT₂N hg⟩, hQ hg, rfl⟩
  refine ⟨R, hp, hRN, fun Q' hQ' hle hQ'N => ?_, hTR, hcard, ?_⟩
  · refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    obtain ⟨m, hm⟩ := hQ'.exists_card_eq
    have hdvd : Nat.card Q' ∣ Nat.card N := Subgroup.card_dvd_of_le hQ'N
    rw [hm] at hdvd ⊢
    rw [hcard, show (128 : ℕ) = 2 ^ 7 by rfl]
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd |>.trans
        (H.factorization_normalizer S.inst₁).le)
  · have hEle : S.inst₁.E ≤ R ⊓ centralizer (S.inst₁.E : Set X) :=
      le_inf ((S.inst₁.E_le_T.trans H.T_le_T₂of).trans hTR) S.inst₁.E_le_centralizer
    exact S.inst₁.eq_E_of_le_centralizer (hp.to_le inf_le_left) hEle inf_le_right

theorem conj_R_z {R : Subgroup X} (hRp : IsPGroup 2 R) (hRN : R ≤ normalizer (S.inst₁.E : Set X))
    (hxR : S.x ∈ R) {r : X} (hr : r ∈ R) : r * S.z * r⁻¹ = S.z := by
  set I := S.inst₁
  by_contra hne
  have hsub : ∀ {n : X}, n ∈ R → n * S.z * n⁻¹ = S.z ∨ n * S.z * n⁻¹ = I.yi ∨
      n * S.z * n⁻¹ = S.z * I.yi := by
    intro n hn
    obtain ⟨p, q, hpq⟩ := H.conj_E00 I (hRN hn) 1 0
    rw [show I.wV (1, 0, 0, 0) = S.z by simp [Inst.wV]] at hpq
    rw [hpq]
    have hne1 : I.wV (p, q, 0, 0) ≠ 1 := by
      rw [← hpq]
      intro h
      apply S.z_ne_one
      calc S.z = n⁻¹ * (n * S.z * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    rcases Fin.exists_fin_two.mp ⟨p, rfl⟩ with rfl | rfl <;>
      rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with rfl | rfl
    · exact absurd (by simp [Inst.wV]) hne1
    · right; left; simp [Inst.wV]
    · left; simp [Inst.wV]
    · right; right; simp [Inst.wV]
  have hxz : S.x * S.z * S.x⁻¹ = S.z := by rw [← S.z_comm_of_mem_T S.x_mem.1]; group
  have hxy : S.x * I.yi * S.x⁻¹ = S.z * I.yi := I.x_conj_yi
  have hxzy : S.x * (S.z * I.yi) * S.x⁻¹ = I.yi := by
    calc S.x * (S.z * I.yi) * S.x⁻¹ = (S.x * S.z * S.x⁻¹) * (S.x * I.yi * S.x⁻¹) := by group
      _ = I.yi := by
          rw [hxz, hxy, ← mul_assoc, ← pow_two, S.z_sq, one_mul]
  have horb : {y | ∃ g ∈ R, g * S.z * g⁻¹ = y} = ({S.z, I.yi, S.z * I.yi} : Set X) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      rcases hsub hg with h | h | h <;> simp [h]
    · intro hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hsub hr with h | h | h
      · exact absurd h hne
      · rcases hy with rfl | rfl | rfl
        · exact ⟨1, one_mem _, by group⟩
        · exact ⟨r, hr, h⟩
        · refine ⟨S.x * r, mul_mem hxR hr, ?_⟩
          calc S.x * r * S.z * (S.x * r)⁻¹ = S.x * (r * S.z * r⁻¹) * S.x⁻¹ := by group
            _ = S.z * I.yi := by rw [h, hxy]
      · rcases hy with rfl | rfl | rfl
        · exact ⟨1, one_mem _, by group⟩
        · refine ⟨S.x * r, mul_mem hxR hr, ?_⟩
          calc S.x * r * S.z * (S.x * r)⁻¹ = S.x * (r * S.z * r⁻¹) * S.x⁻¹ := by group
            _ = I.yi := by rw [h, hxzy]
        · exact ⟨r, hr, h⟩
  have h3 : ({S.z, I.yi, S.z * I.yi} : Set X).ncard = 3 := by
    have e : ({S.z, I.yi, S.z * I.yi} : Set X) =
        I.wV '' {v | v = (1, 0, 0, 0) ∨ v = (0, 1, 0, 0) ∨ v = (1, 1, 0, 0)} := by
      rw [← I.orbit_z H.fus]
      ext y
      constructor
      · intro hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        obtain ⟨d, hd, hdz, hdy⟩ := I.exists_d
        rcases hy with rfl | rfl | rfl
        · exact ⟨1, one_mem _, by group⟩
        · exact ⟨d, hd, hdz⟩
        · refine ⟨d * d, mul_mem hd hd, ?_⟩
          calc d * d * S.z * (d * d)⁻¹ = d * (d * S.z * d⁻¹) * d⁻¹ := by group
            _ = S.z * I.yi := by rw [hdz, hdy]
      · rintro ⟨g, hg, rfl⟩
        rcases I.conj_mem_three H.fus hg (Or.inl rfl) with h | h | h <;> simp [h]
    rw [e, I.ncard_image_wV, card_three]
  have hidx := relIndex_inf_centralizer_eq_ncard R S.z
  rw [horb, h3] at hidx
  have hdvd : (R ⊓ centralizer ({S.z} : Set X)).relIndex R ∣ Nat.card R :=
    Subgroup.relIndex_dvd_card _ _
  rw [hidx] at hdvd
  obtain ⟨m, hm⟩ := hRp.exists_card_eq
  rw [hm] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem not_sylow : ∃ P : Subgroup X, IsPGroup 2 P ∧ T₁ < P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  obtain ⟨R, hRp, hRN, -, hT₂R, hRc, -⟩ := H.exists_R
  obtain ⟨g, hg, -, -, hgt, hgk⟩ := H.exists_g
  have hZ := H.center_T₁ hg hgt hgk
  obtain ⟨P, hP⟩ := H.isPGroup.exists_le_sylow
  have hT₁P : T₁ = (P : Subgroup X) := by
    by_contra hne
    exact hcon ⟨P, P.isPGroup', lt_of_le_of_ne hP hne⟩
  have hcardT₁ : Nat.card T₁ = 2 ^ (Nat.card (⊤ : Subgroup X)).factorization 2 := by
    rw [hT₁P, Sylow.card_eq_multiplicity, Subgroup.card_top]
  have hcardR : Nat.card R = 2 ^ (Nat.card (⊤ : Subgroup X)).factorization 2 := by
    rw [← hcardT₁, hRc, H.card, S.card_T]
  obtain ⟨c, -, hc⟩ := exists_conj_eq_of_card_eq le_top le_top hcardT₁ hcardR
  have hxR : S.x ∈ R := hT₂R (H.T_le_T₂of S.x_mem.1)
  have hcen : ∀ e : X, e ∈ R → (∀ r ∈ R, r * e * r⁻¹ = e) → c⁻¹ * e * c ∈ zpowers S.z := by
    intro e he hfix
    have he' : c⁻¹ * e * c ∈ T₁ := by
      rw [← hc] at he
      obtain ⟨f, hf, rfl⟩ := he
      simpa [mul_assoc] using hf
    refine (hZ _ he').mp fun b hb => ?_
    have hbR : c * b * c⁻¹ ∈ R := by rw [← hc]; exact ⟨b, hb, rfl⟩
    have h1 := hfix _ hbR
    calc c⁻¹ * e * c * b = c⁻¹ * (e * (c * b * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * b * c⁻¹) * e) * c := by
          congr 2
          calc e * (c * b * c⁻¹) = (c * b * c⁻¹) * e * (c * b * c⁻¹)⁻¹ * (c * b * c⁻¹) := by
                rw [h1]
            _ = (c * b * c⁻¹) * e := by group
      _ = b * (c⁻¹ * e * c) := by group
  have hkR : S.k ∈ R := hT₂R (H.T_le_T₂of S.k_mem)
  have hzR : S.z ∈ R := hT₂R (H.T_le_T₂of S.z_mem.1)
  have hk := hcen S.k hkR fun r hr => H.k_fixed S.inst₁ (hRN hr)
  have hz := hcen S.z hzR fun r hr => H.conj_R_z hRp hRN hxR hr
  have hz2 : S.z ^ 2 = 1 := S.z_sq
  have hne1 : ∀ {e : X}, e ≠ 1 → c⁻¹ * e * c ≠ 1 := by
    intro e he h
    apply he
    calc e = c * (c⁻¹ * e * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  rcases eq_one_or_of_mem_zpowers hz2 hk with hk1 | hk1
  · exact hne1 S.k_ne_one hk1
  rcases eq_one_or_of_mem_zpowers hz2 hz with hz1 | hz1
  · exact hne1 S.z_ne_one hz1
  have hkz : S.k = S.z := by
    calc S.k = c * (c⁻¹ * S.k * c) * c⁻¹ := by group
      _ = c * (c⁻¹ * S.z * c) * c⁻¹ := by rw [hk1, hz1]
      _ = S.z := by group
  have := S.inst₁.wV_injective ((show S.inst₁.wV (0, 0, 0, 1) = S.k by simp [Inst.wV, inst₁]).trans
    (hkz.trans (show S.z = S.inst₁.wV (1, 0, 0, 0) by simp [Inst.wV])))
  simp at this

end Sec5Hyp

end A7Base

end CFSG.ComponentClassification.HSFLit
