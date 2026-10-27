module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2A8Card

public section

namespace CFSG.OddStandard.ThmC.O2.A8

open CFSG Subgroup

section Counting

variable {K : Type} [Group K] [Finite K] {A : Type} [Group A] [Finite A]
  {ρ : K →* MulAut A} {V : Sylow 2 K} {Z : Subgroup A}

theorem qa_no_commute : ∀ y : Equiv.Perm (Fin 5), y ^ 5 = 1 → y ≠ 1 →
    ∀ t : Equiv.Perm (Fin 5), t * t = 1 → t ≠ 1 → t * y ≠ y * t := by decide +kernel

theorem qa_invert {G : Type} [Group G] {v y : G} (hv : v * v = 1) (hy : orderOf y = 5)
    (hj : ∃ j : Fin 5, v * y * v⁻¹ = y ^ (j : ℕ)) : v * y = y * v ∨ v * y * v⁻¹ = y⁻¹ := by
  obtain ⟨⟨j, hjlt⟩, hj⟩ := hj
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hy5 : y ^ 5 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy] at this
  have h1 : y ^ (j * j) = y ^ 1 := by
    calc y ^ (j * j) = (y ^ j) ^ j := pow_mul y j j
      _ = (v * y * v⁻¹) ^ j := by rw [hj]
      _ = v * y ^ j * v⁻¹ := conj_pow
      _ = v * (v * y * v⁻¹) * v⁻¹ := by rw [hj]
      _ = y ^ 1 := by
        rw [hvi, pow_one]
        calc v * (v * y * v) * v = (v * v) * y * (v * v) := by group
          _ = y := by rw [hv]; simp
  have h2 : j * j ≡ 1 [MOD 5] := hy ▸ pow_eq_pow_iff_modEq.1 h1
  simp only at hj
  interval_cases j
  · exact absurd h2 (by decide)
  · left
    rw [pow_one] at hj
    exact mul_inv_eq_iff_eq_mul.1 hj
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · right
    rw [hj]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hy5)

theorem qa_card_dvd {α : Type} [Finite α] [Nonempty α] (H : Subgroup (Equiv.Perm α))
    (htrans : ∀ x y : α, ∃ σ ∈ H, σ x = y) : Nat.card α ∣ Nat.card H := by
  have : MulAction.IsPretransitive H α := ⟨fun x y => by
    obtain ⟨σ, hσ, h⟩ := htrans x y
    exact ⟨⟨σ, hσ⟩, h⟩⟩
  obtain ⟨x⟩ := ‹Nonempty α›
  rw [← MulAction.index_stabilizer_of_transitive H x]
  exact Subgroup.index_dvd_card _

theorem qa_sixty (H : Subgroup (Equiv.Perm (Fin 5))) (h : Nat.card H = 60) :
    H = alternatingGroup (Fin 5) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have h1 := H.card_mul_index
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp [Nat.factorial]
  rw [h, h120] at h1
  omega

theorem qa_sylow_norm {G : Type} [Group G] [Finite G] (hG : Nat.card G = 20) (y : G)
    (hy : orderOf y = 5) (v : G) : v * y * v⁻¹ ∈ Subgroup.zpowers y := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 G))
  have hf : (Nat.card G).factorization 5 = 1 := by
    rw [hG, Nat.factorization_def _ (by norm_num : Nat.Prime 5)]
    decide +kernel
  have hP : Nat.card P = 5 := by rw [Sylow.card_eq_multiplicity, hf]; norm_num
  have hidx : (P : Subgroup G).index = 4 := by
    have := (P : Subgroup G).card_mul_index
    rw [hP, hG] at this
    omega
  have hn : Nat.card (Sylow 5 G) = 1 := by
    have h1 := card_sylow_modEq_one 5 G
    have h2 : Nat.card (Sylow 5 G) ∣ 4 := hidx ▸ P.card_dvd_index
    have h3 : Nat.card (Sylow 5 G) ≤ 4 := Nat.le_of_dvd (by norm_num) h2
    have h4 : Nat.card (Sylow 5 G) ≠ 0 := Nat.card_pos.ne'
    unfold Nat.ModEq at h1
    interval_cases (Nat.card (Sylow 5 G)) <;> simp_all
  have : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.1 hn).1
  have hPn : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  have hz : IsPGroup 5 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; norm_num)
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  have hQP : Q = P := Subsingleton.elim _ _
  subst hQP
  have heq : Subgroup.zpowers y = (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hQ (by rw [hP, Nat.card_zpowers, hy])
  rw [heq]
  exact hPn.conj_mem y (heq ▸ Subgroup.mem_zpowers y) v

theorem qa_mem_zpowers_fin {G : Type} [Group G] {y x : G} (hy : orderOf y = 5)
    (hx : x ∈ Subgroup.zpowers y) : ∃ j : Fin 5, x = y ^ (j : ℕ) := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  refine ⟨⟨(n % 5).toNat, by omega⟩, ?_⟩
  have h1 : ((n % 5).toNat : ℤ) = n % 5 := Int.toNat_of_nonneg (by omega)
  rw [← zpow_mod_orderOf, hy, Nat.cast_ofNat]
  show y ^ (n % 5) = y ^ (n % 5).toNat
  rw [← zpow_natCast, h1]

theorem qa_twenty (H : Subgroup (Equiv.Perm (Fin 5))) (h : Nat.card H = 20)
    (h5 : 5 ∣ Nat.card H) (a b : Equiv.Perm (Fin 5)) (ha : a ∈ H) (hb : b ∈ H)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 h5
  have hy : orderOf (y' : Equiv.Perm (Fin 5)) = 5 := by rw [Subgroup.orderOf_coe, hy']
  have hy5 : (y' : Equiv.Perm (Fin 5)) ^ 5 = 1 := by
    have := pow_orderOf_eq_one (y' : Equiv.Perm (Fin 5))
    rwa [hy] at this
  have hy1 : (y' : Equiv.Perm (Fin 5)) ≠ 1 := fun h1 => by simp [h1] at hy
  have hnorm : ∀ v ∈ H, ∃ j : Fin 5, v * y' * v⁻¹ = (y' : Equiv.Perm (Fin 5)) ^ (j : ℕ) := by
    intro v hv
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (qa_sylow_norm (G := H) h y' hy' ⟨v, hv⟩)
    have h2 : v * y' * v⁻¹ ∈ Subgroup.zpowers (y' : Equiv.Perm (Fin 5)) :=
      Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
    exact qa_mem_zpowers_fin hy h2
  have hay : a * y' * a⁻¹ = (y' : Equiv.Perm (Fin 5))⁻¹ :=
    (qa_invert ha2 hy (hnorm a ha)).resolve_left (qa_no_commute y' hy5 hy1 a ha2 ha1)
  have hby : b * y' * b⁻¹ = (y' : Equiv.Perm (Fin 5))⁻¹ :=
    (qa_invert hb2 hy (hnorm b hb)).resolve_left (qa_no_commute y' hy5 hy1 b hb2 hb1)
  have hty : (a * b) * y' = y' * (a * b) := by
    have h1 : a * (b * y' * b⁻¹) * a⁻¹ = y' := by
      rw [hby]
      have : a * (y' : Equiv.Perm (Fin 5))⁻¹ * a⁻¹ = (a * y' * a⁻¹)⁻¹ := by group
      rw [this, hay, inv_inv]
    calc a * b * y' = a * (b * y' * b⁻¹) * a⁻¹ * (a * b) := by group
      _ = y' * (a * b) := by rw [h1]
  have ht2 : (a * b) * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have ht1 : a * b ≠ 1 := by
    intro h1
    apply hne
    have h3 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h4 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [h3, h4]
  exact qa_no_commute y' hy5 hy1 (a * b) ht2 ht1 hty

theorem qa_S5 (H : Subgroup (Equiv.Perm (Fin 5))) (h5 : 5 ∣ Nat.card H) (h4 : 4 ∣ Nat.card H)
    (h8 : ¬ 8 ∣ Nat.card H) (a b : Equiv.Perm (Fin 5)) (ha : a ∈ H) (hb : b ∈ H)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b) : H = alternatingGroup (Fin 5) := by
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp [Nat.factorial]
  have hdvd : Nat.card H ∣ 120 := h120 ▸ H.card_subgroup_dvd_card
  have hcases : Nat.card H = 20 ∨ Nat.card H = 60 := by
    have hle : Nat.card H ≤ 120 := Nat.le_of_dvd (by norm_num) hdvd
    revert hle hdvd h5 h4 h8
    generalize Nat.card H = n
    intro hle hdvd h5 h4 h8
    interval_cases n <;> omega
  rcases hcases with h20 | h60
  · exact (qa_twenty H h20 h5 a b ha hb ha2 hb2 hab ha1 hb1 hne).elim
  · exact qa_sixty H h60

omit [Finite K] in
theorem qa_mem_of_normalizer {x : K} (hx : orderOf x = 2) (W : Sylow 2 K)
    (hxW : x ∈ normalizer ((W : Subgroup K) : Set K)) : x ∈ (W : Subgroup K) := by
  have hz : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  have h1 : Subgroup.zpowers x ⊓ normalizer ((W : Subgroup K) : Set K) =
      Subgroup.zpowers x ⊓ (W : Subgroup K) := hz.inf_normalizer_sylow W
  have hx1 : x ∈ Subgroup.zpowers x ⊓ normalizer ((W : Subgroup K) : Set K) :=
    ⟨Subgroup.mem_zpowers x, hxW⟩
  rw [h1] at hx1
  exact hx1.2

theorem Hyp.qa_ker_odd (h : Hyp ρ V Z) :
    Odd (Nat.card (MulAction.toPermHom K (Sylow 2 K)).ker) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (MulAction.toPermHom K (Sylow 2 K)).ker :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := (MulAction.toPermHom K (Sylow 2 K)).ker)
    2 h2
  have hx : orderOf (x' : K) = 2 := by rw [Subgroup.orderOf_coe, hx']
  have hker : ∀ W : Sylow 2 K, (x' : K) ∈ normalizer ((W : Subgroup K) : Set K) := by
    intro W
    refine Sylow.smul_eq_iff_mem_normalizer.1 ?_
    have h1 := x'.2
    rw [MonoidHom.mem_ker] at h1
    simpa using congrArg (fun σ : Equiv.Perm (Sylow 2 K) => σ W) h1
  obtain ⟨k, hk⟩ : ∃ k : K, k ∉ normalizer ((V : Subgroup K) : Set K) := by
    by_contra hall
    push Not at hall
    exact h.not_normal (Subgroup.normalizer_eq_top_iff.1 ((Subgroup.eq_top_iff' _).2 hall))
  have h1 : (x' : K) = 1 :=
    h.ti hk _ (qa_mem_of_normalizer hx V (hker V)) (qa_mem_of_normalizer hx (k • V) (hker _))
  rw [h1, orderOf_one] at hx
  exact absurd hx (by norm_num)

omit [Finite A] in
theorem Hyp.qa_two_elts (h : Hyp ρ V Z) :
    ∃ v₁ ∈ (V : Subgroup K), ∃ v₂ ∈ (V : Subgroup K), v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ ≠ v₂ := by
  have : Fintype (V : Subgroup K) := Fintype.ofFinite _
  have hc : 2 < Fintype.card (V : Subgroup K) := by
    rw [← Nat.card_eq_fintype_card, h.cardV]; norm_num
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 hc
  by_cases ha : a = 1
  · refine ⟨b, b.2, c, c.2, ?_, ?_, fun h' => hbc (Subtype.ext h')⟩
    · intro h'; exact hab (ha.trans (Subtype.ext h').symm)
    · intro h'; exact hac (ha.trans (Subtype.ext h').symm)
  by_cases hb : b = 1
  · refine ⟨a, a.2, c, c.2, fun h' => ha (Subtype.ext h'), ?_, fun h' => hac (Subtype.ext h')⟩
    intro h'; exact hbc (hb.trans (Subtype.ext h').symm)
  · exact ⟨a, a.2, b, b.2, fun h' => ha (Subtype.ext h'), fun h' => hb (Subtype.ext h'),
      fun h' => hab (Subtype.ext h')⟩

theorem Hyp.qa_perm_ne (h : Hyp ρ V Z) {v : K} (hv : v ∈ (V : Subgroup K)) (hv1 : v ≠ 1) :
    MulAction.toPermHom K (Sylow 2 K) v ≠ 1 := by
  intro hker
  have hmem : v ∈ (MulAction.toPermHom K (Sylow 2 K)).ker := hker
  have hord : orderOf v = 2 := orderOf_eq_prime ((pow_two v).trans (h.sqV v hv)) hv1
  have h2 : 2 ∣ Nat.card (MulAction.toPermHom K (Sylow 2 K)).ker := by
    have h3 : orderOf (⟨v, hmem⟩ : (MulAction.toPermHom K (Sylow 2 K)).ker) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hord
    have h4 := orderOf_dvd_natCard (⟨v, hmem⟩ : (MulAction.toPermHom K (Sylow 2 K)).ker)
    rwa [h3] at h4
  exact (Nat.not_even_iff_odd.2 h.qa_ker_odd) (even_iff_two_dvd.2 h2)

noncomputable def qa_f1 (e : Sylow 2 K ≃ Fin 5) : K →* Equiv.Perm (Fin 5) :=
  e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom K (Sylow 2 K))

omit [Finite K] in
theorem qa_f1_apply (e : Sylow 2 K ≃ Fin 5) (k : K) (W : Sylow 2 K) :
    qa_f1 e k (e W) = e (k • W) := by
  simp [qa_f1, Equiv.permCongrHom, Equiv.permCongr_apply]

omit [Finite K] in
theorem qa_f1_eq_one (e : Sylow 2 K ≃ Fin 5) (k : K) :
    qa_f1 e k = 1 ↔ MulAction.toPermHom K (Sylow 2 K) k = 1 :=
  MulEquiv.map_eq_one_iff e.permCongrHom

theorem Hyp.qa_range (h : Hyp ρ V Z) (e : Sylow 2 K ≃ Fin 5) :
    (qa_f1 e).range = alternatingGroup (Fin 5) := by
  have hodd : Odd (Nat.card (qa_f1 e).ker) := by
    have : (qa_f1 e).ker = (MulAction.toPermHom K (Sylow 2 K)).ker := by
      ext k; exact qa_f1_eq_one e k
    rw [this]; exact h.qa_ker_odd
  have hK : Nat.card K = 4 * (V : Subgroup K).index := by
    have := (V : Subgroup K).card_mul_index
    rw [h.cardV] at this; exact this.symm
  have hVi : ¬ 2 ∣ (V : Subgroup K).index := V.not_dvd_index
  have hprod : Nat.card (qa_f1 e).ker * Nat.card (qa_f1 e).range = Nat.card K :=
    Subgroup.card_ker_mul_card_range _
  have hcop : Nat.Coprime 4 (Nat.card (qa_f1 e).ker) := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
    simpa using this
  have h4 : 4 ∣ Nat.card (qa_f1 e).range := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [hprod, hK]; exact dvd_mul_right _ _
  have h8 : ¬ 8 ∣ Nat.card (qa_f1 e).range := by
    intro h8
    have h1 : 8 ∣ Nat.card K := by
      rw [← hprod]; exact Dvd.dvd.mul_left h8 _
    rw [hK] at h1
    omega
  have h5 : 5 ∣ Nat.card (qa_f1 e).range := by
    have := qa_card_dvd (qa_f1 e).range (fun i j => by
      obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K (e.symm i) (e.symm j)
      refine ⟨qa_f1 e k, ⟨k, rfl⟩, ?_⟩
      have h1 := qa_f1_apply e k (e.symm i)
      rw [Equiv.apply_symm_apply] at h1
      rw [h1, hk, Equiv.apply_symm_apply])
    simpa using this
  obtain ⟨v₁, hv₁, v₂, hv₂, hv₁1, hv₂1, hv₁₂⟩ := h.qa_two_elts
  have hcomm : v₁ * v₂ = v₂ * v₁ := by
    have e1 : (v₁ * v₂)⁻¹ = v₁ * v₂ :=
      inv_eq_of_mul_eq_one_right (h.sqV (v₁ * v₂) ((V : Subgroup K).mul_mem hv₁ hv₂))
    have e2 : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right (h.sqV v₁ hv₁)
    have e3 : v₂⁻¹ = v₂ := inv_eq_of_mul_eq_one_right (h.sqV v₂ hv₂)
    calc v₁ * v₂ = (v₁ * v₂)⁻¹ := e1.symm
      _ = v₂⁻¹ * v₁⁻¹ := mul_inv_rev _ _
      _ = v₂ * v₁ := by rw [e2, e3]
  refine qa_S5 _ h5 h4 h8 (qa_f1 e v₁) (qa_f1 e v₂) ⟨v₁, rfl⟩ ⟨v₂, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_mul, h.sqV v₁ hv₁, map_one]
  · rw [← map_mul, h.sqV v₂ hv₂, map_one]
  · rw [← map_mul, ← map_mul, hcomm]
  · exact fun h1 => h.qa_perm_ne hv₁ hv₁1 ((qa_f1_eq_one e v₁).1 h1)
  · exact fun h1 => h.qa_perm_ne hv₂ hv₂1 ((qa_f1_eq_one e v₂).1 h1)
  · intro h1
    have h2 : qa_f1 e (v₁⁻¹ * v₂) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have hmem : v₁⁻¹ * v₂ ∈ (V : Subgroup K) :=
      (V : Subgroup K).mul_mem ((V : Subgroup K).inv_mem hv₁) hv₂
    by_cases hne : v₁⁻¹ * v₂ = 1
    · exact hv₁₂ (inv_mul_eq_one.1 hne)
    · exact h.qa_perm_ne hmem hne ((qa_f1_eq_one e _).1 h2)

theorem Hyp.quot_A5 (h : Hyp ρ V Z) :
    ∃ (e : Sylow 2 K ≃ Fin 5) (f : K →* alternatingGroup (Fin 5)), Function.Surjective f ∧
      Odd (Nat.card f.ker) ∧
      (∀ (k : K) (W : Sylow 2 K), e (k • W) = (f k : Equiv.Perm (Fin 5)) (e W)) ∧
      ∀ k : K, k ∈ f.ker ↔ ∀ W : Sylow 2 K, k ∈ normalizer ((W : Subgroup K) : Set K) := by
  obtain e := Finite.equivFinOfCardEq h.card_sylow
  have hr := h.qa_range e
  let f : K →* alternatingGroup (Fin 5) :=
    (qa_f1 e).codRestrict (alternatingGroup (Fin 5)) (fun k => by rw [← hr]; exact ⟨k, rfl⟩)
  have hker : f.ker = (MulAction.toPermHom K (Sylow 2 K)).ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← qa_f1_eq_one e k]
    exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
  refine ⟨e, f, ?_, ?_, ?_, ?_⟩
  · intro σ
    have h1 : (σ : Equiv.Perm (Fin 5)) ∈ (qa_f1 e).range := by rw [hr]; exact σ.2
    obtain ⟨k, hk⟩ := h1
    exact ⟨k, Subtype.ext hk⟩
  · rw [hker]; exact h.qa_ker_odd
  · intro k W
    exact (qa_f1_apply e k W).symm
  · intro k
    rw [hker]
    constructor
    · intro hk W
      refine Sylow.smul_eq_iff_mem_normalizer.1 ?_
      simpa using congrArg (fun σ : Equiv.Perm (Sylow 2 K) => σ W) hk
    · intro hk
      refine Equiv.Perm.ext fun W => ?_
      simpa using Sylow.smul_eq_iff_mem_normalizer.2 (hk W)

end Counting

end CFSG.OddStandard.ThmC.O2.A8
