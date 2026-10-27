module

public import CFSG.GH74.GLS.C3.Layer1.St1P89DB
public import CFSG.GH74.GLS.C3.Layer1.St1Prop81

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU.SU1

section DC

variable {G : Type} [Group G] [Finite G] {T P Q S : Subgroup G} {u z x f r s a : G}

theorem Cfg89T.S_cases (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a) {g : G} (hg : g ∈ S) :
    ∃ m ∈ M0 c, g = m ∨ g = m * x ∨ g = a * m ∨ g = a * (m * x) := by
  rcases sc.S_split g hg with h | h
  · rcases T_cases c h with h1 | ⟨m, hm, hm'⟩
    · exact ⟨g, h1, Or.inl rfl⟩
    · exact ⟨m, hm, Or.inr (Or.inl hm')⟩
  · rcases T_cases c h with h1 | ⟨m, hm, hm'⟩
    · exact ⟨a⁻¹ * g, h1, Or.inr (Or.inr (Or.inl (by group)))⟩
    · exact ⟨m, hm, Or.inr (Or.inr (Or.inr (by rw [← hm']; group)))⟩

theorem Cfg89T.false_of_conj_mem (c : Cfg89T G T P Q u z x f r s) {g : G} (hg : g⁻¹ * x * g ∈ M0 c) :
    False := by
  have hx2 : x ^ 2 = 1 := c.x2
  have hx'2 : (g⁻¹ * x * g) ^ 2 = 1 := by
    have : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
      have := conj_pow (a := g⁻¹) (b := x) (i := 2)
      simpa using this
    rw [this, hx2]; group
  have hx'1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    have hx1 : x = 1 := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    have := c.x_ord
    rw [hx1, orderOf_one] at this
    omega
  have hstar := isStar2_of_mem_M0 c hg hx'2 hx'1
  apply c.x_not_star
  have := isStar2_conj hstar g
  simpa [mul_assoc] using this

theorem Cfg89T.false_of_sq_not_mem (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) (h : a * a ∉ M0 c) : False := by
  have hxS : x ∈ S := sc.T_le c.x_mem
  have hM0S : M0 c ≤ S := (M0_le_T c).trans sc.T_le
  obtain ⟨m0, hm0, hm0e⟩ : ∃ m ∈ M0 c, a * a = m * x := by
    rcases T_cases c sc.aa_mem with h1 | h1
    · exact absurd h1 h
    · exact h1
  have haaS : (a * a)⁻¹ ∈ S := S.inv_mem (S.mul_mem sc.a_mem sc.a_mem)
  have hnorm : ∀ g ∈ S, ∀ m ∈ M0 c, g * m * g⁻¹ ∈ M0 c := fun g hg m hm => c.M0_norm_S sc hQ hg hm
  have hx2 : (a * a)⁻¹ * x ∈ M0 c := by
    have hx : x = m0⁻¹ * (a * a) := by rw [hm0e]; group
    have e : (a * a)⁻¹ * x = (a * a)⁻¹ * m0⁻¹ * ((a * a)⁻¹)⁻¹ := by rw [hx]; simp [mul_assoc]
    rw [e]
    exact hnorm _ haaS _ ((M0 c).inv_mem hm0)
  have hmx : ∀ m ∈ M0 c, (a * a)⁻¹ * (m * x) ∈ M0 c := by
    intro m hm
    have e : (a * a)⁻¹ * (m * x) = ((a * a)⁻¹ * m * ((a * a)⁻¹)⁻¹) * ((a * a)⁻¹ * x) := by group
    rw [e]
    exact (M0 c).mul_mem (hnorm _ haaS _ hm) hx2
  have hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ M0 c := by
    refine ⟨a, sc.a_mem, fun t ht => ?_⟩
    rcases sc.S_split t ht with h1 | h1
    · rcases T_cases c h1 with h2 | ⟨m, hm, rfl⟩
      · exact ⟨0, by simpa using h2⟩
      · refine ⟨2, ?_⟩
        rw [zpow_two]
        exact hmx m hm
    · rcases T_cases c h1 with h2 | ⟨m, hm, hm'⟩
      · refine ⟨1, ?_⟩
        rw [zpow_one]
        have : a⁻¹ * t = a⁻¹ * t := rfl
        exact h2
      · refine ⟨3, ?_⟩
        have e : (a ^ (3 : ℤ))⁻¹ * t = (a * a)⁻¹ * (m * x) := by
          have : t = a * (m * x) := by rw [← hm']; group
          rw [this]; simp [zpow_ofNat, pow_succ]; group
        rw [e]
        exact hmx m hm
  obtain ⟨g, hg⟩ := exists_conj_mem_of_cyclic_quot c.simple c.nonab sc.sylowS hM0S hnorm hcyc hxS c.x_ord
  exact c.false_of_conj_mem hg

theorem Cfg89T.cent_x_decomp (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {m : G} (hm : m ∈ M0 c) (hxm : x * m = m * x) :
    ∃ i j : ℕ, m = z ^ i * u ^ j := by
  obtain ⟨p, hp, p', hp', rfl⟩ := (mem_M0_iff c sc hQ).mp hm
  have h1 : (x * p * x⁻¹) * (x * p' * x⁻¹) = p * p' := by
    calc (x * p * x⁻¹) * (x * p' * x⁻¹) = x * (p * p') * x⁻¹ := by group
      _ = p * p' := by rw [hxm]; group
  obtain ⟨hA, hB⟩ := c.PPa_unique sc hQ (c.P_norm x c.x_mem p hp) hp
    (sc.conjSub_norm c.P_norm x c.x_mem p' hp') hp' h1
  have hpz := c.isD8.cent_of_outer c.x_r c.x_s hp hA
  have hp'u := (c.isD8_Pa sc hQ).cent_of_outer (c.x_shape_Pa sc hQ).1 (c.x_shape_Pa sc hQ).2 hp' hB
  rcases hpz with h | h <;> rcases hp'u with h' | h' <;> rw [h, h']
  · exact ⟨0, 0, by simp⟩
  · exact ⟨0, 1, by simp⟩
  · exact ⟨1, 0, by simp⟩
  · exact ⟨1, 1, by simp⟩

theorem Cfg89T.card_cent_x_le (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) (hax : a * x = x * a) :
    Nat.card ↥(S ⊓ centralizer ({x} : Set G)) ≤ 16 := by
  classical
  let F : Fin 2 × Fin 2 × Fin 2 × Fin 2 → G := fun w =>
    a ^ (w.1 : ℕ) * (z ^ (w.2.1 : ℕ) * u ^ (w.2.2.1 : ℕ)) * x ^ (w.2.2.2 : ℕ)
  have hsub : ((S ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) ⊆ Set.range F := by
    intro g hg
    have hgS : g ∈ S := (Subgroup.mem_inf.mp hg).1
    have hgx : g * x = x * g := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2
    obtain ⟨m, hm, hcase⟩ := c.S_cases sc hgS
    have hmx : x * m = m * x := by
      rcases hcase with h | h | h | h <;> rw [h] at hgx
      · exact hgx.symm
      · have : m * x * x = x * m * x := by rw [mul_assoc x m x]; exact hgx
        exact (mul_right_cancel this).symm
      · have : a * (m * x) = a * (x * m) := by
          calc a * (m * x) = a * m * x := by group
            _ = x * (a * m) := hgx
            _ = (x * a) * m := by group
            _ = (a * x) * m := by rw [hax]
            _ = a * (x * m) := by group
        exact (mul_left_cancel this).symm
      · have : m * x * x = x * m * x := by
          have h1 : a * (m * x * x) = a * (x * m * x) := by
            calc a * (m * x * x) = a * (m * x) * x := by group
              _ = x * (a * (m * x)) := hgx
              _ = (x * a) * (m * x) := by group
              _ = (a * x) * (m * x) := by rw [hax]
              _ = a * (x * m * x) := by group
          exact mul_left_cancel h1
        exact (mul_right_cancel this).symm
    obtain ⟨i, j, hij⟩ := c.cent_x_decomp sc hQ hm hmx
    have hz2 : ∀ n : ℕ, z ^ n = z ^ (n % 2) := fun n => pow_eq_pow_mod n c.z_sq
    have hu2 : ∀ n : ℕ, u ^ n = u ^ (n % 2) := fun n => pow_eq_pow_mod n c.u2
    have hi : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hmm : m = z ^ (i % 2) * u ^ (j % 2) := by rw [hij, ← hz2, ← hu2]
    rcases hcase with h | h | h | h
    · exact ⟨(0, ⟨i % 2, hi⟩, ⟨j % 2, hj⟩, 0), by simp [F, h, hmm]⟩
    · exact ⟨(0, ⟨i % 2, hi⟩, ⟨j % 2, hj⟩, 1), by simp [F, h, hmm]⟩
    · exact ⟨(1, ⟨i % 2, hi⟩, ⟨j % 2, hj⟩, 0), by simp [F, h, hmm]⟩
    · exact ⟨(1, ⟨i % 2, hi⟩, ⟨j % 2, hj⟩, 1), by simp [F, h, hmm, mul_assoc]⟩
  have h1 : (Set.range F).ncard ≤ Nat.card (Fin 2 × Fin 2 × Fin 2 × Fin 2) := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le (Set.toFinite _)).trans_eq (Set.ncard_univ _)
  have h2 : Nat.card ↥(S ⊓ centralizer ({x} : Set G)) =
      ((S ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
  rw [h2]
  calc _ ≤ (Set.range F).ncard := Set.ncard_le_ncard hsub (Set.finite_range F)
    _ ≤ _ := h1
    _ = 16 := by simp

theorem Cfg89T.W_sep (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hax : a * x = x * a) (haa : a * a = 1) (w w' : Fin 2 × Fin 2)
    (h : (a ^ (w.1 : ℕ) * x ^ (w.2 : ℕ)) * (a ^ (w'.1 : ℕ) * x ^ (w'.2 : ℕ))⁻¹ ∈ M0 c) : w = w' := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hxM : x ∉ M0 c := x_not_mem_M0 c
  have haT : a ∉ T := sc.a_nmem
  have e12 : a * (x⁻¹ * a) = x⁻¹ := by
    calc a * (x⁻¹ * a) = a * (a * x⁻¹) := by
          rw [show x⁻¹ * a = a * x⁻¹ from by
            calc x⁻¹ * a = x⁻¹ * (a * x) * x⁻¹ := by group
              _ = x⁻¹ * (x * a) * x⁻¹ := by rw [hax]
              _ = a * x⁻¹ := by group]
      _ = (a * a) * x⁻¹ := by group
      _ = x⁻¹ := by rw [haa, one_mul]
  have e15 : a * x * a = x := by
    calc a * x * a = x * a * a := by rw [hax]
      _ = x * (a * a) := by group
      _ = x := by rw [haa, mul_one]
  obtain ⟨l, k⟩ := w
  obtain ⟨l', k'⟩ := w'
  have hl : (l : ℕ) = 0 ∨ (l : ℕ) = 1 := by have := l.isLt; omega
  have hk : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by have := k.isLt; omega
  have hl' : (l' : ℕ) = 0 ∨ (l' : ℕ) = 1 := by have := l'.isLt; omega
  have hk' : (k' : ℕ) = 0 ∨ (k' : ℕ) = 1 := by have := k'.isLt; omega
  simp only at h
  rcases hl with hl | hl <;> rcases hk with hk | hk <;> rcases hl' with hl' | hl' <;> rcases hk' with hk' | hk' <;>
    rw [hl, hk, hl', hk'] at h <;> simp only [pow_zero, pow_one, mul_one, one_mul, inv_one, mul_inv_rev, hainv] at h
  all_goals first
    | exact Prod.ext (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))
    | (exfalso
       first
        | exact sc.a_nmem (M0_le_T c h)
        | exact hxM h
        | exact hxM (by simpa using h)
        | exact sc.a_nmem (by have := T.mul_mem c.x_mem (M0_le_T c h); simpa using this)
        | exact sc.a_nmem (by have := T.mul_mem (T.inv_mem c.x_mem) (M0_le_T c h); simpa using this)
        | exact sc.a_nmem (by have := T.mul_mem (M0_le_T c h) c.x_mem; simpa using this)
        | exact sc.a_nmem (by have := T.mul_mem (M0_le_T c h) (T.inv_mem c.x_mem); simpa using this)
        | exact sc.a_nmem (M0_le_T c (by simpa using h))
        | (rw [e12] at h; exact hxM (by simpa using h))
        | (rw [e15] at h; exact hxM h))

theorem Cfg89T.card_cent_a_ge (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) (hax : a * x = x * a) (haa : a * a = 1) :
    32 ≤ Nat.card ↥(S ⊓ centralizer ({a} : Set G)) := by
  classical
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  let D : ↥P → G := fun p => (p : G) * (a * (p : G) * a⁻¹)
  let Φ : ↥P × (Fin 2 × Fin 2) → G := fun w => D w.1 * (a ^ (w.2.1 : ℕ) * x ^ (w.2.2 : ℕ))
  have hDa : ∀ p : ↥P, a * D p * a⁻¹ = D p := by
    intro p
    have hp' : a * (p : G) * a⁻¹ ∈ conjSub a P := conj_mem_conjSub p.2
    have hcomm := c.P_Pa_comm sc hQ p p.2 _ hp'
    have e1 : a * (a * (p : G) * a⁻¹) * a⁻¹ = p := by
      have : a * (a * (p : G) * a⁻¹) * a⁻¹ = (a * a) * p * (a * a)⁻¹ := by group
      rw [this, haa]; group
    have e2 : a * ((p : G) * (a * p * a⁻¹)) * a⁻¹ = (a * p * a⁻¹) * (a * (a * p * a⁻¹) * a⁻¹) := by group
    show a * ((p : G) * (a * p * a⁻¹)) * a⁻¹ = (p : G) * (a * p * a⁻¹)
    rw [e2, e1, hcomm]
  have hDcomm : ∀ p : ↥P, Commute (D p) a := fun p => by
    have := hDa p
    show D p * a = a * D p
    calc D p * a = (a * D p * a⁻¹) * a := by rw [this]
      _ = a * D p := by group
  have hDM : ∀ p : ↥P, D p ∈ M0 c := fun p =>
    (mem_M0_iff c sc hQ).mpr ⟨p, p.2, _, conj_mem_conjSub p.2, rfl⟩
  have hmem : ∀ w : ↥P × (Fin 2 × Fin 2), Φ w ∈ S ⊓ centralizer ({a} : Set G) := by
    intro w
    have hpS : (w.1 : G) ∈ S := sc.T_le (c.P_le w.1.2)
    have hDS : D w.1 ∈ S :=
      S.mul_mem hpS (S.mul_mem (S.mul_mem sc.a_mem hpS) (S.inv_mem sc.a_mem))
    have hWS : a ^ (w.2.1 : ℕ) * x ^ (w.2.2 : ℕ) ∈ S :=
      S.mul_mem (S.pow_mem sc.a_mem _) (S.pow_mem (sc.T_le c.x_mem) _)
    refine Subgroup.mem_inf.mpr ⟨S.mul_mem hDS hWS, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hW : Commute (a ^ (w.2.1 : ℕ) * x ^ (w.2.2 : ℕ)) a :=
      (Commute.pow_left (Commute.refl a) _).mul_left (Commute.pow_left (show Commute x a from hax.symm) _)
    exact ((hDcomm w.1).mul_left hW).eq
  have hinj : Function.Injective (fun w : ↥P × (Fin 2 × Fin 2) =>
      (⟨Φ w, hmem w⟩ : ↥(S ⊓ centralizer ({a} : Set G)))) := by
    rintro ⟨p, l, k⟩ ⟨p', l', k'⟩ h
    have h1 : Φ (p, l, k) = Φ (p', l', k') := congrArg Subtype.val h
    simp only [Φ] at h1
    have hM : (a ^ (l : ℕ) * x ^ (k : ℕ)) * (a ^ (l' : ℕ) * x ^ (k' : ℕ))⁻¹ ∈ M0 c := by
      have : (a ^ (l : ℕ) * x ^ (k : ℕ)) * (a ^ (l' : ℕ) * x ^ (k' : ℕ))⁻¹ = (D p)⁻¹ * D p' := by
        calc (a ^ (l : ℕ) * x ^ (k : ℕ)) * (a ^ (l' : ℕ) * x ^ (k' : ℕ))⁻¹
            = (D p)⁻¹ * (D p * (a ^ (l : ℕ) * x ^ (k : ℕ))) * (a ^ (l' : ℕ) * x ^ (k' : ℕ))⁻¹ := by group
          _ = (D p)⁻¹ * (D p' * (a ^ (l' : ℕ) * x ^ (k' : ℕ))) * (a ^ (l' : ℕ) * x ^ (k' : ℕ))⁻¹ := by rw [h1]
          _ = (D p)⁻¹ * D p' := by group
      rw [this]
      exact (M0 c).mul_mem ((M0 c).inv_mem (hDM p)) (hDM p')
    have hw := c.W_sep sc hax haa (l, k) (l', k') hM
    have hlk : l = l' ∧ k = k' := ⟨congrArg Prod.fst hw, congrArg Prod.snd hw⟩
    obtain ⟨rfl, rfl⟩ := hlk
    have hD : D p = D p' := mul_right_cancel h1
    obtain ⟨hpp, -⟩ := c.PPa_unique sc hQ p.2 p'.2 (conj_mem_conjSub p.2) (conj_mem_conjSub p'.2) hD
    have : p = p' := Subtype.ext hpp
    rw [this]
  have hcard := Nat.card_le_card_of_injective _ hinj
  have hP := c.card_P_ge
  rw [Nat.card_prod, Nat.card_prod] at hcard
  have h2 : Nat.card (Fin 2) = 2 := by simp
  rw [h2] at hcard
  omega

theorem card_le_of_isSylowOf {R K H : Subgroup G} (hR : IsSylowOf 2 R K) (hHK : H ≤ K)
    {n : ℕ} (hn : Nat.card ↥H = 2 ^ n) : Nat.card ↥H ≤ Nat.card ↥R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ n ∣ Nat.card ↥K := by rw [← hn]; exact Subgroup.card_dvd_of_le hHK
  have hK0 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
  have hle : n ≤ (Nat.card ↥K).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hK0).mp hdvd
  rw [hn, hR.card_eq]
  exact Nat.pow_le_pow_right (by norm_num) hle

theorem Cfg89S.relIndex_le (sc : Cfg89S G T u S a) : T.relIndex S ≤ 2 := by
  classical
  let N : Subgroup ↥S := T.subgroupOf S
  let f : Fin 2 → ↥S ⧸ N := fun i => QuotientGroup.mk (⟨a ^ (i : ℕ), S.pow_mem sc.a_mem _⟩ : ↥S)
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rcases sc.S_split (g : G) g.2 with h | h
      · refine ⟨0, ?_⟩
        show (QuotientGroup.mk (⟨a ^ (0 : ℕ), _⟩ : ↥S) : ↥S ⧸ N) = QuotientGroup.mk g
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using h
      · refine ⟨1, ?_⟩
        show (QuotientGroup.mk (⟨a ^ (1 : ℕ), _⟩ : ↥S) : ↥S ⧸ N) = QuotientGroup.mk g
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using h
  have := Nat.card_le_card_of_surjective f hsurj
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  simpa using this

theorem Cfg89T.isStar2_a (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) (hax : a * x = x * a) (haa : a * a = 1) : IsStar2 a := by
  have ha2 : a ^ 2 = 1 := by rw [sq]; exact haa
  have ha1 : a ≠ 1 := fun h => sc.a_nmem (by rw [h]; exact T.one_mem)
  have haord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hperf : a ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ⊔ (⊥ : Subgroup G) := by
    rw [commutator_top_of_simple c.simple c.nonab, top_sup_eq]
    exact Subgroup.mem_top a
  obtain ⟨y, -, hyT, hySyl⟩ := Stage1.Thm3.Sec5.ig_15_16_ext_thm G (⊤ : Subgroup G) S T ⊥ a sc.sylowS
    sc.T_le sc.relIndex_le bot_le (fun _ _ n hn => by simp at hn; simp [hn]) (by simp) sc.a_mem haord hperf
  have ha1'2 : (y⁻¹ * a * y) ^ 2 = 1 := by
    have : (y⁻¹ * a * y) ^ 2 = y⁻¹ * a ^ 2 * y := by
      have := conj_pow (a := y⁻¹) (b := a) (i := 2)
      simpa using this
    rw [this, ha2]; group
  have ha1'1 : y⁻¹ * a * y ≠ 1 := by
    intro h
    apply ha1
    calc a = y * (y⁻¹ * a * y) * y⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hlow : 32 ≤ Nat.card ↥(S ⊓ centralizer ({y⁻¹ * a * y} : Set G)) := by
    have h32 := c.card_cent_a_ge sc hQ hax haa
    set H : Subgroup G := S ⊓ centralizer ({a} : Set G) with hH
    have hcardH : Nat.card ↥(conjSub y⁻¹ H) = Nat.card ↥H := card_conjSub _ _
    have hSH : Nat.card ↥H ∣ Nat.card ↥S := Subgroup.card_dvd_of_le inf_le_left
    have hS2 : Nat.card ↥S = 2 ^ (Nat.card ↥(⊤ : Subgroup G)).factorization 2 := sc.sylowS.card_eq
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hS2 ▸ hSH)
    have hle : conjSub y⁻¹ H ≤ (⊤ : Subgroup G) ⊓ centralizer ({y⁻¹ * a * y} : Set G) := by
      intro g hg
      obtain ⟨h, hh, rfl⟩ := mem_conjSub.mp hg
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hh).2
      calc y⁻¹ * h * y⁻¹⁻¹ * (y⁻¹ * a * y) = y⁻¹ * (h * a) * y := by group
        _ = y⁻¹ * (a * h) * y := by rw [this]
        _ = y⁻¹ * a * y * (y⁻¹ * h * y⁻¹⁻¹) := by group
    have := card_le_of_isSylowOf hySyl hle (n := n) (by rw [hcardH]; exact hn)
    rw [hcardH] at this
    have hinf : (⊤ : Subgroup G) ⊓ centralizer ({y⁻¹ * a * y} : Set G) = centralizer ({y⁻¹ * a * y} : Set G) := top_inf_eq _
    omega
  by_cases hM : y⁻¹ * a * y ∈ M0 c
  · have hstar := isStar2_of_mem_M0 c hM ha1'2 ha1'1
    have := isStar2_conj hstar y
    simpa [mul_assoc] using this
  · exfalso
    obtain ⟨g, hg, hga⟩ := c.inv_conj_x sc hQ hyT hM ha1'2
    have hgS : g ∈ S := sc.T_le (M0_le_T c hg)
    have hinj : Function.Injective (fun w : ↥(S ⊓ centralizer ({y⁻¹ * a * y} : Set G)) =>
        (⟨g⁻¹ * (w : G) * g, by
          refine Subgroup.mem_inf.mpr ⟨S.mul_mem (S.mul_mem (S.inv_mem hgS) (Subgroup.mem_inf.mp w.2).1) hgS, ?_⟩
          rw [mem_centralizer_singleton_iff]
          have hw0 := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp w.2).2
          have hw : (w : G) * (g * x * g⁻¹) = (g * x * g⁻¹) * (w : G) := by rw [← hga]; exact hw0
          calc g⁻¹ * (w : G) * g * x = g⁻¹ * ((w : G) * (g * x * g⁻¹)) * g := by group
            _ = g⁻¹ * ((g * x * g⁻¹) * (w : G)) * g := by rw [hw]
            _ = x * (g⁻¹ * (w : G) * g) := by group⟩ : ↥(S ⊓ centralizer ({x} : Set G)))) := by
      intro w w' h
      have := congrArg Subtype.val h
      apply Subtype.ext
      simpa using this
    have h1 := Nat.card_le_card_of_injective _ hinj
    have h2 := c.card_cent_x_le sc hQ hax
    omega

@[expose] def M1 (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) (haa : a * a = 1) : Subgroup G where
  carrier := {g | g ∈ M0 c ∨ ∃ m ∈ M0 c, g = a * m}
  one_mem' := Or.inl (M0 c).one_mem
  mul_mem' := by
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    rintro g1 g2 (h1 | ⟨m1, hm1, rfl⟩) (h2 | ⟨m2, hm2, rfl⟩)
    · exact Or.inl ((M0 c).mul_mem h1 h2)
    · right
      have := c.a_conj_M0 sc hQ h1
      rw [hainv] at this
      refine ⟨(a⁻¹ * g1 * a) * m2, (M0 c).mul_mem (by rw [hainv]; exact this) hm2, by group⟩
    · exact Or.inr ⟨m1 * g2, (M0 c).mul_mem hm1 h2, by group⟩
    · left
      have e : a * m1 * (a * m2) = (a * m1 * a⁻¹) * (a * a) * m2 := by group
      rw [e, haa, mul_one]
      exact (M0 c).mul_mem (c.a_conj_M0 sc hQ hm1) hm2
  inv_mem' := by
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    rintro g (h | ⟨m, hm, rfl⟩)
    · exact Or.inl ((M0 c).inv_mem h)
    · right
      refine ⟨a * m⁻¹ * a⁻¹, c.a_conj_M0 sc hQ ((M0 c).inv_mem hm), ?_⟩
      calc (a * m)⁻¹ = m⁻¹ * a⁻¹ := mul_inv_rev a m
        _ = (a * a) * m⁻¹ * a⁻¹ := by rw [haa, one_mul]
        _ = a * (a * m⁻¹ * a⁻¹) := by group

theorem Cfg89T.inv_aM0 (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) (haa : a * a = 1) {m : G} (hm : m ∈ M0 c)
    (h2 : (a * m) ^ 2 = 1) : ∃ p ∈ P, a * m = p⁻¹ * a * p := by
  obtain ⟨p, hp, p', hp', rfl⟩ := (mem_M0_iff c sc hQ).mp hm
  have h3 : a * (p * p') * a⁻¹ = (p * p')⁻¹ := by
    have h0 : (a * (p * p')) * (a * (p * p')) = 1 := by rw [← sq]; exact h2
    have e : a * (p * p') * (a * (p * p')) = (a * (p * p') * a⁻¹) * (a * a) * (p * p') := by group
    rw [e, haa, mul_one] at h0
    exact eq_inv_of_mul_eq_one_left h0
  have hX : a * p * a⁻¹ ∈ conjSub a P := conj_mem_conjSub hp
  have hY : a * p' * a⁻¹ ∈ P := c.conj_Pa_mem_P sc hp'
  have hXY : (a * p' * a⁻¹) * (a * p * a⁻¹) = p⁻¹ * p'⁻¹ := by
    have hc1 : (a * p' * a⁻¹) * (a * p * a⁻¹) = (a * p * a⁻¹) * (a * p' * a⁻¹) :=
      c.P_Pa_comm sc hQ _ hY _ hX
    have hc2 : p⁻¹ * p'⁻¹ = p'⁻¹ * p⁻¹ :=
      c.P_Pa_comm sc hQ p⁻¹ (P.inv_mem hp) p'⁻¹ ((conjSub a P).inv_mem hp')
    calc (a * p' * a⁻¹) * (a * p * a⁻¹) = (a * p * a⁻¹) * (a * p' * a⁻¹) := hc1
      _ = a * (p * p') * a⁻¹ := by group
      _ = (p * p')⁻¹ := h3
      _ = p'⁻¹ * p⁻¹ := mul_inv_rev p p'
      _ = p⁻¹ * p'⁻¹ := hc2.symm
  obtain ⟨hB, -⟩ := c.PPa_unique sc hQ hY (P.inv_mem hp) hX ((conjSub a P).inv_mem hp') hXY
  refine ⟨p, hp, ?_⟩
  have hcomm : p * p' = p' * p := c.P_Pa_comm sc hQ p hp p' hp'
  have e : a * (p * p') = (a * p' * a⁻¹) * a * p := by rw [hcomm]; group
  rw [e, hB]

theorem Cfg89T.false_of_comm_sq (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) (hax : a * x = x * a) (haa : a * a = 1) : False := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hxS : x ∈ S := sc.T_le c.x_mem
  have hM1S : M1 c sc hQ haa ≤ S := by
    intro g hg
    rcases hg with h | ⟨m, hm, rfl⟩
    · exact sc.T_le (M0_le_T c h)
    · exact S.mul_mem sc.a_mem (sc.T_le (M0_le_T c hm))
  have hc3 : ∀ m ∈ M0 c, a⁻¹ * m * a ∈ M0 c := by
    intro m hm
    have := c.a_conj_M0 sc hQ hm
    rw [hainv] at this ⊢
    exact this
  have hxa : x * a * x⁻¹ = a := by
    calc x * a * x⁻¹ = a * x * x⁻¹ := by rw [hax]
      _ = a := by group
  have hxa' : x⁻¹ * a = a * x⁻¹ := by
    calc x⁻¹ * a = x⁻¹ * (a * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * a) * x⁻¹ := by rw [hax]
      _ = a * x⁻¹ := by group
  have hconj_a : ∀ m ∈ M0 c, ∃ m' ∈ M0 c, m * a * m⁻¹ = a * m' := by
    intro m hm
    exact ⟨(a⁻¹ * m * a) * m⁻¹, (M0 c).mul_mem (hc3 m hm) ((M0 c).inv_mem hm), by group⟩
  have hconj_a2 : ∀ m ∈ M0 c, ∃ m' ∈ M0 c, (a * m) * a * (a * m)⁻¹ = a * m' := by
    intro m hm
    obtain ⟨m', hm', hme⟩ := hconj_a m hm
    refine ⟨a⁻¹ * m' * a⁻¹, ?_, ?_⟩
    · have := hc3 m' hm'
      rw [hainv] at this ⊢
      exact this
    · calc (a * m) * a * (a * m)⁻¹ = a * (m * a * m⁻¹) * a⁻¹ := by group
        _ = a * (a * m') * a⁻¹ := by rw [hme]
        _ = (a * a) * m' * a⁻¹ := by group
        _ = a * (a⁻¹ * m' * a⁻¹) := by rw [haa, one_mul]; group
  have hcomm_a : ∀ g ∈ S, ∃ m' ∈ M0 c, g * a * g⁻¹ = a * m' := by
    intro g hg
    obtain ⟨m, hm, hcase⟩ := c.S_cases sc hg
    rcases hcase with h | h | h | h
    · rw [h]; exact hconj_a m hm
    · rw [h]
      obtain ⟨m', hm', hme⟩ := hconj_a m hm
      refine ⟨m', hm', ?_⟩
      calc m * x * a * (m * x)⁻¹ = m * (x * a * x⁻¹) * m⁻¹ := by group
        _ = m * a * m⁻¹ := by rw [hxa]
        _ = a * m' := hme
    · rw [h]; exact hconj_a2 m hm
    · rw [h]
      obtain ⟨m', hm', hme⟩ := hconj_a2 m hm
      refine ⟨m', hm', ?_⟩
      calc a * (m * x) * a * (a * (m * x))⁻¹ = (a * m) * (x * a * x⁻¹) * (a * m)⁻¹ := by group
        _ = (a * m) * a * (a * m)⁻¹ := by rw [hxa]
        _ = a * m' := hme
  have hnorm : ∀ g ∈ S, ∀ q ∈ M1 c sc hQ haa, g * q * g⁻¹ ∈ M1 c sc hQ haa := by
    intro g hg q hq
    rcases hq with hq | ⟨m0, hm0, rfl⟩
    · exact Or.inl (c.M0_norm_S sc hQ hg hq)
    · obtain ⟨m', hm', hge⟩ := hcomm_a g hg
      right
      refine ⟨m' * (g * m0 * g⁻¹), (M0 c).mul_mem hm' (c.M0_norm_S sc hQ hg hm0), ?_⟩
      calc g * (a * m0) * g⁻¹ = (g * a * g⁻¹) * (g * m0 * g⁻¹) := by group
        _ = (a * m') * (g * m0 * g⁻¹) := by rw [hge]
        _ = a * (m' * (g * m0 * g⁻¹)) := by group
  have hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ M1 c sc hQ haa := by
    refine ⟨x, hxS, fun t ht => ?_⟩
    obtain ⟨m, hm, hcase⟩ := c.S_cases sc ht
    have hxm : x⁻¹ * m * x ∈ M0 c := by
      have := M0_norm c (T.inv_mem c.x_mem) hm
      simpa using this
    rcases hcase with h | h | h | h
    · exact ⟨0, by rw [h, zpow_zero, inv_one, one_mul]; exact Or.inl hm⟩
    · exact ⟨1, by rw [h, zpow_one]; exact Or.inl (by simpa [mul_assoc] using hxm)⟩
    · exact ⟨0, by rw [h, zpow_zero, inv_one, one_mul]; exact Or.inr ⟨m, hm, rfl⟩⟩
    · refine ⟨1, ?_⟩
      rw [h, zpow_one]
      right
      refine ⟨x⁻¹ * m * x, hxm, ?_⟩
      calc x⁻¹ * (a * (m * x)) = (x⁻¹ * a) * (m * x) := by group
        _ = (a * x⁻¹) * (m * x) := by rw [hxa']
        _ = a * (x⁻¹ * m * x) := by group
  obtain ⟨g, hg⟩ := exists_conj_mem_of_cyclic_quot c.simple c.nonab sc.sylowS hM1S hnorm hcyc hxS c.x_ord
  rcases hg with hg | ⟨m, hm, hgm⟩
  · exact c.false_of_conj_mem hg
  · have hw2 : (a * m) ^ 2 = 1 := by
      rw [← hgm]
      have : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
        have := conj_pow (a := g⁻¹) (b := x) (i := 2)
        simpa using this
      rw [this, c.x2]; group
    obtain ⟨p, hp, hpe⟩ := c.inv_aM0 sc hQ haa hm hw2
    have hstar := c.isStar2_a sc hQ hax haa
    apply c.x_not_star
    have h1 := isStar2_conj hstar (g * p⁻¹)
    have e : (g * p⁻¹) * a * (g * p⁻¹)⁻¹ = x := by
      calc (g * p⁻¹) * a * (g * p⁻¹)⁻¹ = g * (p⁻¹ * a * p) * g⁻¹ := by group
        _ = g * (a * m) * g⁻¹ := by rw [← hpe]
        _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hgm]
        _ = x := by group
    rw [e] at h1
    exact h1

theorem Cfg89T.false_of_comm_a (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) (hax : a * x = x * a) : False := by
  by_cases h : a * a ∈ M0 c
  · have hxaa : x * (a * a) = (a * a) * x := by
      calc x * (a * a) = (x * a) * a := by group
        _ = (a * x) * a := by rw [hax]
        _ = a * (x * a) := by group
        _ = a * (a * x) := by rw [hax]
        _ = (a * a) * x := by group
    obtain ⟨i, j, hij⟩ := c.cent_x_decomp sc hQ h hxaa
    have hz2 : ∀ n : ℕ, z ^ n = z ^ (n % 2) := fun n => pow_eq_pow_mod n c.z_sq
    have hu2 : ∀ n : ℕ, u ^ n = u ^ (n % 2) := fun n => pow_eq_pow_mod n c.u2
    have hi : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rw [hz2 i, hu2 j] at hij
    have haaa : a * (a * a) * a⁻¹ = a * a := by group
    have hzT : z ∈ T := c.P_le c.z_mem
    generalize i % 2 = I at hi hij
    generalize j % 2 = J at hj hij
    interval_cases I <;> interval_cases J
    · have hij' : a * a = 1 := by simpa using hij
      exact c.false_of_comm_sq sc hQ hax hij'
    · have hij' : a * a = u := by simpa using hij
      rw [hij'] at haaa
      exact c.u_ne_z (haaa.symm.trans (c.aua sc hQ))
    · have hij' : a * a = z := by simpa using hij
      rw [hij'] at haaa
      exact c.u_ne_z ((c.aza sc hQ).symm.trans haaa)
    · have hij' : a * a = z * u := by simpa using hij
      have huz : z * u = u * z := c.u_central z hzT
      have hzx : x * z = z * x := c.z_central x c.x_mem
      have haa' : (z * a) * (z * a) = 1 := by
        calc (z * a) * (z * a) = z * (a * z * a⁻¹) * (a * a) := by group
          _ = z * u * (z * u) := by rw [c.aza sc hQ, hij']
          _ = z * (u * z) * u := by group
          _ = z * (z * u) * u := by rw [← huz]
          _ = (z * z) * (u * u) := by group
          _ = 1 := by rw [← sq, ← sq, c.z_sq, c.u2, mul_one]
      have hax' : (z * a) * x = x * (z * a) := by
        calc (z * a) * x = z * (a * x) := by group
          _ = z * (x * a) := by rw [hax]
          _ = (z * x) * a := by group
          _ = (x * z) * a := by rw [hzx]
          _ = x * (z * a) := by group
      exact c.false_of_comm_sq (sc.of_mul hzT) hQ hax' haa'
  · exact c.false_of_sq_not_mem sc hQ h

theorem Cfg89T.false_of_hQ (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) : False := by
  obtain ⟨g, hg, hax⟩ := c.exists_comm_a sc hQ
  exact c.false_of_comm_a (sc.of_mul (T.inv_mem (M0_le_T c hg))) hQ hax

end DC

end CFSG.GH74.GLS.C3.Layer1.P89
