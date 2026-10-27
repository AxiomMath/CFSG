module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46T1
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46Count

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

theorem four_dvd_filter : ∀ P : Fin 2 → Fin 2 → Bool,
    4 ∣ ((Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2 × Fin 2)).filter
      fun v => P v.2.2.1 v.2.2.2).card := by decide

theorem word_E_ψ_inj : ∀ e : ZMod 8, dbit8 e = 0 → ∀ a b l a' b' l' : Fin 2,
    z8 ^ (a : ℕ) * aff8 (-1) e ^ (b : ℕ) * k8 ^ (l : ℕ) =
      z8 ^ (a' : ℕ) * aff8 (-1) e ^ (b' : ℕ) * k8 ^ (l' : ℕ) → a = a' ∧ b = b' ∧ l = l' := by
  decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} (S : KDBase A C)

@[expose] noncomputable def wy (v : Fin 2 × Fin 2 × Fin 2 × Fin 2) : X :=
  S.z ^ (v.1 : ℕ) * S.y ^ (v.2.1 : ℕ) * t ^ (v.2.2.1 : ℕ) * S.k ^ (v.2.2.2 : ℕ)

theorem wy_mem (v : Fin 2 × Fin 2 × Fin 2 × Fin 2) : wy S v ∈ S.E S.y :=
  mul_mem (mul_mem (mul_mem (pow_mem (mem_E_z S _) _) (pow_mem (mem_E_yi S _) _))
    (pow_mem (mem_E_t S _) _)) (pow_mem (mem_E_k S _) _)

theorem exists_wy {e : X} (he : e ∈ S.E S.y) : ∃ v, e = wy S v := by
  obtain ⟨a, b, c, l, ha, hb, hc, hl, rfl⟩ := eq_of_mem_E S S.y_mem S.y_sq he
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨l, hl⟩), rfl⟩

theorem wy_injective : Function.Injective (wy S) := by
  rintro ⟨a, b, c, l⟩ ⟨a', b', c', l'⟩ h
  obtain ⟨e, he, hψy⟩ := ψ_y S
  have hψ := congrArg (ψX A) h
  have hw : ∀ v : Fin 2 × Fin 2 × Fin 2 × Fin 2, ψX A (wy S v) =
      z8 ^ (v.1 : ℕ) * aff8 (-1) e ^ (v.2.1 : ℕ) * k8 ^ (v.2.2.2 : ℕ) := by
    intro v
    simp only [wy]
    rw [ψX_mul (mul_mem (mul_mem (pow_mem (z_mem_T S) _) (pow_mem (y_mem_T S) _))
      (pow_mem A.t_mem_T _)) (pow_mem (k_mem_T S) _),
      ψX_mul (mul_mem (pow_mem (z_mem_T S) _) (pow_mem (y_mem_T S) _)) (pow_mem A.t_mem_T _),
      ψX_mul (pow_mem (z_mem_T S) _) (pow_mem (y_mem_T S) _), ψX_pow (z_mem_T S),
      ψX_pow (y_mem_T S), ψX_pow A.t_mem_T, ψX_pow (k_mem_T S), ψ_z, hψy, ψX_t, ψ_k, one_pow,
      mul_one]
  rw [hw, hw] at hψ
  obtain ⟨rfl, rfl, rfl⟩ := word_E_ψ_inj e he a b l a' b' l' hψ
  have h' : t ^ (c : ℕ) = t ^ (c' : ℕ) := by
    simp only [wy] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hc : c = c' := by
    rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl <;>
      rcases Fin.exists_fin_two.mp ⟨c', rfl⟩ with rfl | rfl
    · rfl
    · exact absurd (by simpa using h') (t_ne_one' (A := A)).symm
    · exact absurd (by simpa using h') (t_ne_one' (A := A))
    · rfl
  rw [hc]

theorem conjTo_wy_iff (a c l : Fin 2) :
    ConjTo t (wy S (a, 1, c, l)) ↔ ConjTo t (wy S (1, 0, c, l)) := by
  obtain ⟨g, hgC, -, hgz, hgy, hgk⟩ := S.d_y
  replace hgz : g * S.z * g⁻¹ = S.y := hgz
  replace hgy : g * S.y * g⁻¹ = S.z * S.y := hgy
  replace hgk : g * S.k * g⁻¹ = S.k := hgk
  have hgt : g * t * g⁻¹ = t := by rw [mem_centralizer_singleton_iff.mp hgC, mul_inv_cancel_right]
  set f := t ^ (c : ℕ) * S.k ^ (l : ℕ) with hf
  have hgf : g * f * g⁻¹ = f := by
    calc g * f * g⁻¹ = (g * t * g⁻¹) ^ (c : ℕ) * (g * S.k * g⁻¹) ^ (l : ℕ) := by
          rw [conj_pow, conj_pow, hf]; group
      _ = f := by rw [hgt, hgk]
  have hw1 : wy S (1, 0, c, l) = S.z * f := by simp [wy, hf, mul_assoc]
  have hconj : ∀ {u v : X} (h : X), h * u * h⁻¹ = v → (ConjTo t u ↔ ConjTo t v) := by
    intro u v h huv
    rw [← huv]
    constructor
    · rintro ⟨g', hg'⟩
      exact ⟨h * g', by rw [← hg']; group⟩
    · rintro ⟨g', hg'⟩
      exact ⟨h⁻¹ * g', by
        calc h⁻¹ * g' * t * (h⁻¹ * g')⁻¹ = h⁻¹ * (g' * t * g'⁻¹) * h := by group
          _ = u := by rw [hg']; group⟩
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl
  · have hw : wy S (0, 1, c, l) = S.y * f := by simp [wy, hf, mul_assoc]
    rw [hw, hw1]
    refine hconj g⁻¹ ?_
    have hgy' : g⁻¹ * S.y * g = S.z := by
      calc g⁻¹ * S.y * g = g⁻¹ * (g * S.z * g⁻¹) * g := by rw [hgz]
        _ = S.z := by group
    have hgf' : g⁻¹ * f * g = f := by
      calc g⁻¹ * f * g = g⁻¹ * (g * f * g⁻¹) * g := by rw [hgf]
        _ = f := by group
    calc g⁻¹ * (S.y * f) * g⁻¹⁻¹ = (g⁻¹ * S.y * g) * (g⁻¹ * f * g) := by group
      _ = S.z * f := by rw [hgy', hgf']
  · have hw : wy S (1, 1, c, l) = S.z * S.y * f := by simp [wy, hf, mul_assoc]
    rw [hw, hw1]
    refine hconj g ?_
    have hyzy : S.y * (S.z * S.y) = S.z := by
      calc S.y * (S.z * S.y) = S.z * (S.y * S.y) := by rw [← mul_assoc, ← z_comm_y S, mul_assoc]
        _ = S.z := by rw [← pow_two, S.y_sq, mul_one]
    calc g * (S.z * S.y * f) * g⁻¹ = (g * S.z * g⁻¹) * (g * S.y * g⁻¹) * (g * f * g⁻¹) := by
          group
      _ = S.z * f := by rw [hgz, hgy, hgf, hyzy]

@[expose] def orbE : Set X := {e | ∃ n ∈ normalizer (S.E S.y : Set X), n * t * n⁻¹ = e}

theorem mem_orbE_iff {e : X} : e ∈ orbE S ↔ e ∈ S.E S.y ∧ ConjTo t e := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(mem_normalizer_iff.mp hn t).mp (mem_E_t S _), ⟨n, rfl⟩⟩
  · rintro ⟨he, hc⟩
    exact exists_normalizer_E_conj_eq S (Or.inl rfl) he hc

theorem ncard_orbE (P : Fin 2 → Fin 2 → Bool)
    (hP : ∀ a c l : Fin 2, ConjTo t (wy S (a, 0, c, l)) ↔ (a = 1 ∨ c = 1 ∨ l = 1) ∧ P c l)
    (hP1 : ∀ c l : Fin 2, P c l → c = 1 ∨ l = 1) :
    (orbE S).ncard = ((Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2 × Fin 2)).filter
      fun v => P v.2.2.1 v.2.2.2).card := by
  classical
  have hset : orbE S = wy S '' {v | P v.2.2.1 v.2.2.2} := by
    ext e
    rw [mem_orbE_iff]
    constructor
    · rintro ⟨he, hc⟩
      obtain ⟨v, rfl⟩ := exists_wy S he
      refine ⟨v, ?_, rfl⟩
      obtain ⟨a, b, c, l⟩ := v
      rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
      · exact ((hP a c l).mp hc).2
      · rw [conjTo_wy_iff] at hc
        exact ((hP 1 c l).mp hc).2
    · rintro ⟨v, hv, rfl⟩
      refine ⟨wy_mem S v, ?_⟩
      obtain ⟨a, b, c, l⟩ := v
      have h1 := hP1 c l hv
      rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
      · exact (hP a c l).mpr ⟨by tauto, hv⟩
      · rw [conjTo_wy_iff]
        exact (hP 1 c l).mpr ⟨Or.inl rfl, hv⟩
  rw [hset, Set.ncard_image_of_injective _ (wy_injective S), ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

theorem conjTo_mul_z_iff (htz : ConjTo t (t * S.z)) {b : X} (hb : b ∈ S.B) :
    ConjTo t (S.z * b) ↔ ConjTo t b := by
  obtain ⟨n, hn, hnt⟩ := exists_normalizer_conj_eq S (mul_mem (mem_B_t S) (mem_B_z S)) htz
  have key : ∀ {b : X}, b ∈ S.B → ConjTo t b → ConjTo t (S.z * b) := by
    intro b hb hbc
    obtain ⟨m, hm, hmt⟩ := exists_normalizer_conj_eq S hb hbc
    refine ⟨m * n, ?_⟩
    have hmz := conj_z_of_mem_normalizer S hm
    calc m * n * t * (m * n)⁻¹ = m * (n * t * n⁻¹) * m⁻¹ := by group
      _ = (m * t * m⁻¹) * (m * S.z * m⁻¹) := by rw [hnt]; group
      _ = S.z * b := by rw [hmt, hmz, B_comm S hb (mem_B_z S)]
  constructor
  · intro h
    have := key (mul_mem (mem_B_z S) hb) h
    rwa [← mul_assoc, ← pow_two, z_sq S, one_mul] at this
  · exact key hb

theorem two_mul_card_T_le (htz : ConjTo t (t * S.z)) :
    2 * Nat.card A.T ≤ 2 ^ (Nat.card (normalizer (S.E S.y : Set X))).factorization 2 := by
  classical
  set N := normalizer (S.E S.y : Set X) with hN
  set H := N ⊓ centralizer ({t} : Set X) with hH
  set P : Fin 2 → Fin 2 → Bool := fun c l => decide (ConjTo t (t ^ (c : ℕ) * S.k ^ (l : ℕ)))
    with hPdef
  have hP : ∀ a c l : Fin 2, ConjTo t (wy S (a, 0, c, l)) ↔ (a = 1 ∨ c = 1 ∨ l = 1) ∧ P c l := by
    intro a c l
    have hf : t ^ (c : ℕ) * S.k ^ (l : ℕ) ∈ S.B :=
      mul_mem (pow_mem (mem_B_t S) _) (pow_mem (mem_B_k S) _)
    have h1 : ¬ ConjTo t (t ^ ((0 : Fin 2) : ℕ) * S.k ^ ((0 : Fin 2) : ℕ)) := by
      simpa using not_conjTo_one (A := A)
    rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl
    · have e : wy S (0, 0, c, l) = t ^ (c : ℕ) * S.k ^ (l : ℕ) := by simp [wy]
      rw [e, hPdef, decide_eq_true_iff]
      constructor
      · intro h
        refine ⟨?_, h⟩
        rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl <;>
          rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
        · exact absurd h h1
        all_goals simp
      · exact fun h => h.2
    · have e : wy S (1, 0, c, l) = S.z * (t ^ (c : ℕ) * S.k ^ (l : ℕ)) := by simp [wy, mul_assoc]
      rw [e, conjTo_mul_z_iff S htz hf, hPdef, decide_eq_true_iff]
      exact ⟨fun h => ⟨Or.inl rfl, h⟩, fun h => h.2⟩
  have hP1 : ∀ c l : Fin 2, P c l → c = 1 ∨ l = 1 := by
    intro c l h
    rw [hPdef, decide_eq_true_iff] at h
    rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl <;>
      rcases Fin.exists_fin_two.mp ⟨l, rfl⟩ with rfl | rfl
    · exact absurd (by simpa using h) (not_conjTo_one (A := A))
    all_goals simp
  have h4 : 4 ∣ (orbE S).ncard := by rw [ncard_orbE S P hP hP1]; exact four_dvd_filter P
  have hpos : (orbE S).ncard ≠ 0 := by
    have : t ∈ orbE S := ⟨1, one_mem _, by group⟩
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨t, this⟩ |>.ne'
  have hv : 2 ≤ (orbE S).ncard.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp (by simpa using h4)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 N) := inferInstance
  have hQ : Nat.card ((Q : Subgroup N).map N.subtype) = 2 ^ (Nat.card N).factorization 2 := by
    rw [card_map_of_injective (subtype_injective _), Sylow.card_eq_multiplicity]
  have hidx : H.relIndex N = (orbE S).ncard := relIndex_inf_centralizer_eq_ncard N t
  have hc := card_eq_mul_two_pow (P := (Q : Subgroup N).map N.subtype) (Q := S.TE)
    (inf_le_left : H ≤ N) hQ (card_TE_eq_two_pow S (Or.inl rfl))
  rw [hidx] at hc
  rw [← hQ, hc, card_T_eq S]
  calc 2 * (2 * Nat.card S.TE) = Nat.card S.TE * 2 ^ 2 := by ring
    _ ≤ Nat.card S.TE * 2 ^ (orbE S).ncard.factorization 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hv)

theorem not_sylow_T (hnot : ¬ SectRank4 X) (P : Sylow 2 X) : (P : Subgroup X) ≠ A.T :=
  fun hP => hnot fun Q hQ => A.gen4_of_coe_sylow_eq P hP Q hQ

include A in
theorem two_dvd_index (hnot : ¬ SectRank4 X) : 2 ∣ (centralizer ({t} : Set X)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h2
  set H := centralizer ({t} : Set X) with hH
  have hX : Nat.card X = Nat.card H * H.index := (H.card_mul_index).symm
  have hidx0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hv : (Nat.card X).factorization 2 = (Nat.card H).factorization 2 := by
    rw [hX, Nat.factorization_mul Nat.card_pos.ne' hidx0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h2, add_zero]
  have hT : Nat.card A.T = 2 ^ (Nat.card X).factorization 2 := by
    rw [hv]; exact card_T_eq_two_pow (A := A)
  exact not_sylow_T hnot (Sylow.ofCard A.T hT) (Sylow.coe_ofCard _ _)

include S in
theorem four_dvd_index [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hnot : ¬ SectRank4 X) : 4 ∣ (centralizer ({t} : Set X)).index := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h4
  set H := centralizer ({t} : Set X) with hH
  have h2 : 2 ∣ H.index := two_dvd_index (A := A) hnot
  have hmod := (card_Om_modEq_index hnab (t_sq' (A := A))).symm.trans (card_Om_modEq S)
  have htz : ConjTo t (t * S.z) := by
    by_contra hn
    simp only [hn, ↓reduceIte, add_zero] at hmod
    have h' := Nat.ModEq.of_mul_left 2 (show H.index ≡ _ [MOD 2 * 2] from hmod)
    unfold Nat.ModEq at h'
    generalize (if ConjTo t S.k then 1 else 0) = a at h'
    generalize (if ConjTo t (t * S.k) then 1 else 0) = b at h'
    obtain ⟨m, hm⟩ := h2
    omega
  have hidx0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hvidx : H.index.factorization 2 = 1 := by
    have h1 : 1 ≤ H.index.factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hidx0).mp h2
    have h3 : H.index.factorization 2 < 2 := by
      by_contra h
      apply h4
      have := (Nat.Prime.pow_dvd_iff_le_factorization (k := 2) Nat.prime_two hidx0).mpr
        (by omega)
      simpa using this
    omega
  have hX2 : 2 ^ (Nat.card X).factorization 2 = 2 * Nat.card A.T := by
    rw [show Nat.card X = Nat.card H * H.index from (H.card_mul_index).symm,
      Nat.factorization_mul Nat.card_pos.ne' hidx0, Finsupp.add_apply, hvidx, pow_add, pow_one,
      card_T_eq_two_pow (A := A), mul_comm]
  obtain ⟨T₁, hT₁p, hTT₁, -, -, -, hlt, -⟩ := exists_T₁ S hnot
  have hT₁ : Nat.card T₁ = 2 * Nat.card A.T := by
    obtain ⟨m, hm⟩ := hT₁p.exists_card_eq
    have hdvd : Nat.card A.T ∣ Nat.card T₁ := Subgroup.card_dvd_of_le hTT₁
    have hle : Nat.card T₁ ≤ 2 * Nat.card A.T := by
      rw [← hX2, hm]
      have hdvd' : 2 ^ m ∣ Nat.card X := hm ▸ Subgroup.card_subgroup_dvd_card T₁
      exact Nat.pow_le_pow_right (by norm_num)
        ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd')
    obtain ⟨r, hr⟩ := hdvd
    have hpos : 0 < Nat.card A.T := Nat.card_pos
    have h1 : 1 < r := by
      by_contra h
      push Not at h
      have : Nat.card A.T * r ≤ Nat.card A.T * 1 := Nat.mul_le_mul_left _ h
      omega
    have h2' : r ≤ 2 := by
      by_contra h
      push Not at h
      have : Nat.card A.T * 3 ≤ Nat.card A.T * r := Nat.mul_le_mul_left _ h
      omega
    have hr2 : r = 2 := by omega
    rw [hr, hr2, mul_comm]
  set N := normalizer (S.E S.y : Set X) with hN
  obtain ⟨Q⟩ : Nonempty (Sylow 2 N) := inferInstance
  set R : Subgroup X := (Q : Subgroup N).map N.subtype with hR
  have hRN : R ≤ N := map_subtype_le _
  have hRp : IsPGroup 2 R := Q.isPGroup'.map _
  have hRc : Nat.card R = 2 ^ (Nat.card N).factorization 2 := by
    rw [hR, card_map_of_injective (subtype_injective _), Sylow.card_eq_multiplicity]
  have hR2 : Nat.card R = 2 * Nat.card A.T := by
    refine le_antisymm ?_ (hRc ▸ two_mul_card_T_le S htz)
    rw [← hX2, hRc]
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_subgroup_dvd_card N) 2)
  have hE₁R : S.E S.y ≤ R := by
    have hE₁N : S.E S.y ≤ N := le_normalizer
    have hEp : IsPGroup 2 (S.E S.y) := A.isPGroup_T.to_le (E_le_T S _ S.y_mem)
    have hRE : R ≤ normalizer (S.E S.y : Set X) := hRN
    have hp := IsPGroup.to_sup_of_normal_right' hRp hEp hRE
    have hle : R ⊔ S.E S.y ≤ N := sup_le hRN hE₁N
    have heq : R ⊔ S.E S.y = R := by
      refine (eq_of_le_of_card_ge le_sup_left ?_).symm
      obtain ⟨m, hm⟩ := hp.exists_card_eq
      have hdvd : Nat.card (R ⊔ S.E S.y : Subgroup X) ∣ Nat.card N := Subgroup.card_dvd_of_le hle
      rw [hm] at hdvd ⊢
      rw [hRc]
      exact Nat.pow_le_pow_right (by norm_num)
        ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd)
    rw [← heq]
    exact le_sup_right
  obtain ⟨g, -, hg⟩ := exists_conj_eq_of_card_eq (le_top : R ≤ ⊤) (le_top : T₁ ≤ ⊤)
    (by rw [hR2, card_top, hX2]) (by rw [hT₁, card_top, hX2])
  set E : Subgroup X := (S.E S.y).map (MulAut.conj g).toMonoidHom with hE
  have hET₁ : E ≤ T₁ := by rw [← hg]; exact map_mono hE₁R
  have hT₁E : ∀ h ∈ T₁, ∀ e ∈ E, h * e * h⁻¹ ∈ E := by
    intro h hh e he
    rw [← hg] at hh
    obtain ⟨r, hr, rfl⟩ := hh
    obtain ⟨e', he', rfl⟩ := he
    have hr' : r * e' * r⁻¹ ∈ S.E S.y := (mem_normalizer_iff.mp (hRN hr) e').mp he'
    refine ⟨r * e' * r⁻¹, hr', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hEel : ElemAbelianTwo E := elem_map (elem_E S S.y_mem S.y_sq) g
  have hE16 : Nat.card E = 16 := by
    rw [hE, card_map_of_injective (MulAut.conj g).injective, card_E₁]
  have hdT₁ : S.d ∈ T₁ := hTT₁ (d_mem_T S)
  have hET : ¬ E ≤ A.T := by
    intro hle
    rcases eq_E_of_card S hle hEel hE16 with h | h
    · apply d_not_mem_TE S
      refine mem_TE_of_mem_normalizer_E₁ S (d_mem_T S) (mem_normalizer_of_conj_mem fun e he => ?_)
      rw [← h] at he ⊢
      exact hT₁E _ hdT₁ e he
    · apply d_not_mem_TE S
      refine mem_TE_of_mem_normalizer_E₂ S (d_mem_T S) (mem_normalizer_of_conj_mem fun e he => ?_)
      rw [← h] at he ⊢
      exact hT₁E _ hdT₁ e he
  have htE : t ∉ E := by
    intro ht
    apply hET
    have hle : E ≤ T₁ ⊓ H := le_inf hET₁ fun e he =>
      mem_centralizer_singleton_iff.mpr (hEel.comm e he t ht)
    have heq : T₁ ⊓ H = A.T := eq_T_of_le (hT₁p.to_le inf_le_left) (le_inf hTT₁ A.T_le_centralizer)
      inf_le_right
    rw [← heq]
    exact hle
  set F : Subgroup X := E ⊓ A.T with hF
  have hFc : Nat.card F = 8 := by
    have hrel : A.T.relIndex T₁ = 2 := by
      have := relIndex_mul_card A.T T₁
      rw [inf_of_le_left hTT₁, hT₁] at this
      have hpos : 0 < Nat.card A.T := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos (by rw [this, mul_comm])
    have h1 : A.T.relIndex E ≤ 2 := by
      rw [← hrel]
      exact relIndex_le_of_le_right hET₁ (by rw [hrel]; norm_num)
    have h2' : A.T.relIndex E ≠ 1 := fun h => hET (relIndex_eq_one.mp h)
    have h3 : A.T.relIndex E ≠ 0 := by
      intro h0
      have := relIndex_mul_card A.T E
      rw [h0, zero_mul] at this
      exact Nat.card_pos.ne' this.symm
    have h22 : A.T.relIndex E = 2 := by omega
    have := relIndex_mul_card A.T E
    rw [h22, hE16, inf_comm] at this
    have h8 : 2 * Nat.card F = 16 := by rw [hF]; exact this
    omega
  have hFel : ElemAbelianTwo F :=
    ⟨fun a ha b hb => hEel.comm a ha.1 b hb.1, fun a ha => hEel.sq_eq_one a ha.1⟩
  have htF : t ∉ F := fun h => htE h.1
  have hFTE : F ≤ S.TE := by
    by_contra h
    exact htF ((card_le_of_not_le_TE S inf_le_right hFel h).2 hFc)
  have hdF : ∀ f ∈ F, S.d⁻¹ * f * S.d⁻¹⁻¹ ∈ F := fun f hf =>
    Subgroup.mem_inf.mpr ⟨hT₁E _ (inv_mem hdT₁) f (Subgroup.mem_inf.mp hf).1,
      mul_mem (mul_mem (inv_mem (d_mem_T S)) (Subgroup.mem_inf.mp hf).2)
        (inv_mem (inv_mem (d_mem_T S)))⟩
  have hd := fun {a : X} => conj_E_of_not_mem_TE S (e := a) (d_mem_T S) (d_not_mem_TE S)
  have hFB : F ≤ S.B := by
    rw [← E₁_inf_E₂ S]
    rcases le_E_of_elem S hFTE hFel with h | h
    · refine le_inf h fun f hf => ?_
      have := hd.1 (h (hdF f hf))
      simpa [mul_assoc] using this
    · refine le_inf (fun f hf => ?_) h
      have := hd.2 (h (hdF f hf))
      simpa [mul_assoc] using this
  have hFeq : F = S.B := eq_of_le_of_card_ge hFB (by rw [card_B, hFc])
  exact htF (hFeq ▸ mem_B_t S)

end CFSG.ComponentClassification.HSFLit.KD46
