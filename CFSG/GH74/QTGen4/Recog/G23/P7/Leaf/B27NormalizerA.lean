module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7.B27N

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

theorem mem_sup_of_normalizes {A B : Subgroup G} (hB : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A)
    {x : G} : x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  refine ⟨fun hx => ?_, fun ⟨a, ha, b, hb, h⟩ => h ▸ mul_mem (Subgroup.mem_sup_left ha)
    (Subgroup.mem_sup_right hb)⟩
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, mul_one x⟩
    · exact ⟨1, A.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
    exact ⟨a₁ * (b₁ * a₂ * b₁⁻¹), A.mul_mem ha₁ (hB b₁ hb₁ a₂ ha₂), b₁ * b₂, B.mul_mem hb₁ hb₂,
      by group⟩
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have h1 := hB b⁻¹ (B.inv_mem hb) a⁻¹ (A.inv_mem ha)
    refine ⟨b⁻¹ * a⁻¹ * b, by simpa using h1, b⁻¹, B.inv_mem hb, by group⟩

theorem card_sup_of_normalizes [Finite G] {A B : Subgroup G}
    (hB : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (hAB : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hmem : ∀ p : ↥A × ↥B, (p.1 : G) * (p.2 : G) ∈ A ⊔ B := fun p =>
    mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
  let f : ↥A × ↥B → ↥(A ⊔ B) := fun p => ⟨(p.1 : G) * (p.2 : G), hmem p⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val h
    have key : (a' : G)⁻¹ * a = (b' : G) * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [h']
        _ = (b' : G) * (b : G)⁻¹ := by group
    have hmem2 : (a' : G)⁻¹ * a ∈ A ⊓ B := by
      refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
      rw [key]
      exact B.mul_mem b'.2 (B.inv_mem b.2)
    rw [hAB, Subgroup.mem_bot] at hmem2
    have haa : a = a' := Subtype.ext (inv_mul_eq_one.mp hmem2).symm
    subst haa
    have hbb : b = b' := Subtype.ext (mul_left_cancel h')
    subst hbb
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_normalizes hB).mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

theorem conj_eq_of_pow_three_eq_one {g a : G} {n : ℕ} (hg : g ^ 3 ^ n = 1) (ha : orderOf a = 3)
    {k : ℕ} (hk : g * a * g⁻¹ = a ^ k) : g * a * g⁻¹ = a := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero, pow_one] at hg
    subst hg
    simp
  have key : ∀ m : ℕ, g ^ m * a * (g ^ m)⁻¹ = a ^ (k ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc g ^ (m + 1) * a * (g ^ (m + 1))⁻¹ = g * (g ^ m * a * (g ^ m)⁻¹) * g⁻¹ := by group
        _ = g * a ^ (k ^ m) * g⁻¹ := by rw [ih]
        _ = (g * a * g⁻¹) ^ (k ^ m) := by rw [conj_pow]
        _ = a ^ (k * k ^ m) := by rw [hk, ← pow_mul]
        _ = a ^ (k ^ (m + 1)) := by rw [pow_succ']
  have h1 := key (3 ^ n)
  rw [hg] at h1
  simp only [one_mul, inv_one, mul_one] at h1
  have hmod : k ^ 3 ^ n ≡ 1 [MOD 3] := by
    have h2 : a ^ (k ^ 3 ^ n) = a ^ 1 := by rw [pow_one]; exact h1.symm
    rw [pow_eq_pow_iff_modEq, ha] at h2
    exact h2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz : ((k : ZMod 3)) ^ 3 ^ n = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmod
    push_cast at this
    rw [← Nat.cast_pow] at this
    simpa using this
  have hk1 : (k : ZMod 3) = 1 := by
    have hpow : ((k : ZMod 3)) ^ 3 ^ n = (k : ZMod 3) := ZMod.pow_card_pow _
    rw [hpow] at hz
    exact hz
  have hk2 : k % 3 = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' k 1 3).mp (by simpa using hk1)
    simpa using this
  calc g * a * g⁻¹ = a ^ k := hk
    _ = a ^ (k % orderOf a) := (pow_mod_orderOf a k).symm
    _ = a := by rw [ha, hk2, pow_one]

theorem normal_of_index_three [Finite G] {K H : Subgroup G} (hHK : H ≤ K)
    (hK : Nat.card ↥K = 81) (hH : Nat.card ↥H = 27) :
    ∀ g ∈ K, ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
  have hidx : (H.subgroupOf K).index = (Nat.card ↥K).minFac := by
    have h1 := Subgroup.index_mul_card (H.subgroupOf K)
    have h2 : Nat.card ↥(H.subgroupOf K) = 27 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, hH]
    rw [h2, hK] at h1
    have h3 : (81 : ℕ) = 27 * 3 := by norm_num
    rw [h3] at h1
    have h4 : (H.subgroupOf K).index = 3 := by
      have := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 27) (by linarith [h1] : 27 * (H.subgroupOf K).index = 27 * 3)
      exact this
    rw [h4, hK]
    norm_num
  have hN : (H.subgroupOf K).Normal := Subgroup.normal_of_index_eq_minFac_card hidx
  intro g hg h hh
  have hmem := Subgroup.Normal.conj_mem hN (⟨h, hHK hh⟩ : ↥K) (Subgroup.mem_subgroupOf.mpr hh)
    (⟨g, hg⟩ : ↥K)
  have h' := Subgroup.mem_subgroupOf.mp hmem
  simpa using h'

theorem pow_three_pow_eq_one_of_isPGroup {M : Subgroup G} (hM : IsPGroup 3 M) {g : G}
    (hg : g ∈ M) : ∃ n : ℕ, g ^ 3 ^ n = 1 := by
  obtain ⟨k, hk⟩ := hM ⟨g, hg⟩
  exact ⟨k, by have h := congrArg Subtype.val hk; simpa using h⟩


theorem comm_of_sup_comm {A B : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hBA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A := by
    intro b hb a ha
    have := hAB a ha b hb
    rw [← this, mul_inv_cancel_right]
    exact ha
  have hdec : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, a * b = x := fun x hx =>
    (mem_sup_of_normalizes hBA).mp hx
  intro x hx y hy
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hdec x hx
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hdec y hy
  calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
    _ = a₁ * (a₂ * b₁) * b₂ := by rw [hAB a₂ ha₂ b₁ hb₁]
    _ = (a₁ * a₂) * (b₁ * b₂) := by group
    _ = (a₂ * a₁) * (b₂ * b₁) := by rw [hA a₁ ha₁ a₂ ha₂, hB b₁ hb₁ b₂ hb₂]
    _ = a₂ * (a₁ * b₂) * b₁ := by group
    _ = a₂ * (b₂ * a₁) * b₁ := by rw [hAB a₁ ha₁ b₂ hb₂]
    _ = a₂ * b₂ * (a₁ * b₁) := by group


structure Core {G : Type} [Group G] (a b t z : G) (H H₁ H₂ M₁ M₂ Pb : Subgroup G) : Prop where
  z_mul : z * z = 1
  z_ne : z ≠ 1
  cent_z : ∀ g : G, g * z = z * g ↔ g ∈ H
  inv_conj : ∀ u : G, u * u = 1 → u ≠ 1 → IsConj z u
  a_H : a ∈ H
  b_H : b ∈ H
  t_H : t ∈ H
  t_mul : t * t = 1
  t_ne : t ≠ 1
  a_ne : a ≠ 1
  b_ne : b ≠ 1
  a_cube : a ^ 3 = 1
  b_cube : b ^ 3 = 1
  ab_comm : a * b = b * a
  t_a : t * a * t⁻¹ = a⁻¹
  t_b : t * b * t⁻¹ = b⁻¹
  H₂_le : H₂ ≤ H
  H₂_cent_a : ∀ h ∈ H₂, a * h = h * a
  inf_eq : H₁ ⊓ H₂ = Subgroup.zpowers z
  card_H : Nat.card H = 576
  M₁_card : Nat.card M₁ = 27
  M₁_comm : ∀ x ∈ M₁, ∀ y ∈ M₁, x * y = y * x
  M₁_cube : ∀ x ∈ M₁, x ^ 3 = 1
  a_M₁ : a ∈ M₁
  M₁_inf_H : M₁ ⊓ H = Subgroup.zpowers a
  M₁_sup : M₁ ⊔ H₂ = Subgroup.centralizer {a}
  M₁_disj : M₁ ⊓ H₂ = ⊥
  M₁_conjC : ∀ c ∈ Subgroup.centralizer {a}, ∀ m ∈ M₁, c * m * c⁻¹ ∈ M₁
  M₁_t : ∀ m ∈ M₁, t * m * t⁻¹ ∈ M₁
  norm_a : Subgroup.normalizer (Subgroup.zpowers a : Set G) =
    Subgroup.centralizer {a} ⊔ Subgroup.zpowers t
  M₂_card : Nat.card M₂ = 27
  M₂_inf_H : M₂ ⊓ H = Subgroup.zpowers b
  M₂_conjC : ∀ c ∈ Subgroup.centralizer {b}, ∀ m ∈ M₂, c * m * c⁻¹ ∈ M₂
  M₂_sup : M₂ ⊔ H₁ = Subgroup.centralizer {b}
  Pb_card : Nat.card Pb = 27
  Pb_three : IsPGroup 3 Pb
  Pb_comm : ∀ x ∈ Pb, ∀ y ∈ Pb, x * y = y * x
  a_Pb : a ∈ Pb
  b_Pb : b ∈ Pb
  cent_P : Subgroup.centralizer ((Subgroup.closure {a, b} : Subgroup G) : Set G) = Pb ⊔
    Subgroup.zpowers z
  Pb_disj : Pb ⊓ Subgroup.zpowers z = ⊥
  Pb_conjP : ∀ c ∈ Subgroup.centralizer ((Subgroup.closure {a, b} : Subgroup G) : Set G),
    ∀ p ∈ Pb, c * p * c⁻¹ ∈ Pb
  Pb_inf_z : Pb ⊓ Subgroup.centralizer {z} = Subgroup.closure {a, b}
  Pb_t : ∀ p ∈ Pb, t * p * t⁻¹ ∈ Pb
  Pb_eq_b : Pb = (M₁ ⊓ Subgroup.centralizer {b}) ⊔ Subgroup.zpowers b
  Pb_eq_a : Pb = (M₂ ⊓ Subgroup.centralizer {a}) ⊔ Subgroup.zpowers a
  card_M₁_cent_b : Nat.card ↥(M₁ ⊓ Subgroup.centralizer {b}) = 9
  norm_P : Subgroup.normalizer ((Subgroup.closure {a, b} : Subgroup G) : Set G) =
    Pb ⊔ Subgroup.closure {t, z}
  norm_P_H : Subgroup.normalizer ((Subgroup.closure {a, b} : Subgroup G) : Set G) ⊓ H =
    Subgroup.closure {a, b} ⊔ Subgroup.closure {t, z}
  card_P : Nat.card (Subgroup.closure ({a, b} : Set G)) = 9
  not_243_cent_a : ¬ 3 ^ 5 ∣ Nat.card ↥(Subgroup.centralizer {a})
  not_conj_ab : ¬ IsConj a b
  not_conj_mixed : ¬ IsConj a (a * b) ∧ ¬ IsConj a (a * b⁻¹)


theorem zOf_mem_inf {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G} (h : Setup G T H H₁ H₂ M e) :
    zOf e ∈ H₁ ⊓ H₂ := by
  have hr : FreeGroup.lift e (FreeGroup.mk ([(0, true), (1, true), (0, true), (1, true),
      (3, false), (2, false), (3, false), (2, false)] : List (Fin 6 × Bool))) = 1 :=
    h.lets.rels _ (by simp [g23WordsH])
  have hr' : e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹ = 1 := by
    simpa [FreeGroup.lift_mk, mul_assoc] using hr
  have hA : e 0 * e 1 * e 0 * e 1 = e 2 * e 3 * e 2 * e 3 := by
    calc e 0 * e 1 * e 0 * e 1
        = (e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹) *
            (e 2 * e 3 * e 2 * e 3) := by group
      _ = e 2 * e 3 * e 2 * e 3 := by rw [hr', one_mul]
  have hz2 : zOf e = (e 2 * e 3) ^ 2 := by
    unfold zOf
    simp only [sq, mul_assoc] at hA ⊢
    exact hA
  have he0 : e 0 ∈ H₁ := by
    rw [← h.lets.gen₁]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have he1 : e 1 ∈ H₁ := by
    rw [← h.lets.gen₁]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have he2 : e 2 ∈ H₂ := by
    rw [← h.lets.gen₂]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have he3 : e 3 ∈ H₂ := by
    rw [← h.lets.gen₂]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact pow_mem (mul_mem he0 he1) 2
  · rw [hz2]; exact pow_mem (mul_mem he2 he3) 2

theorem core_of_leaf [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    {M₁ M₂ Pb Np Nm : Subgroup G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card Pb = 27)
    (ha₁ : IsElemAbelian 3 M₁) (ha₂ : IsElemAbelian 3 M₂) :
    Core (e 0) (e 2) (e 4) (zOf e) H H₁ H₂ M₁ M₂ Pb := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hone := h.ctx.one
  have hH1 : H₁ ≤ H := hone.le_one
  have hH2 : H₂ ≤ H := hone.le_two
  have he0 : e 0 ∈ H₁ := by
    rw [← h.lets.gen₁]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have he2 : e 2 ∈ H₂ := by
    rw [← h.lets.gen₂]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have he4 : e 4 ∈ H := by
    rw [← h.lets.gen]
    exact Subgroup.subset_closure ⟨4, rfl⟩
  have ha_H : e 0 ∈ H := hH1 he0
  have hb_H : e 2 ∈ H := hH2 he2
  have rel : ∀ r : List (Fin 6 × Bool), r ∈ g23WordsH → FreeGroup.lift e (FreeGroup.mk r) = 1 :=
    fun r hr => h.lets.rels r hr
  have r_tt : e 4 * e 4 = 1 := by
    have := rel [(4, true), (4, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk] using this
  have r_ta : e 4 * e 0 * e 4 * e 0 = 1 := by
    have := rel [(4, true), (0, true), (4, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have r_tb : e 4 * e 2 * e 4 * e 2 = 1 := by
    have := rel [(4, true), (2, true), (4, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have r_a3 : e 0 * e 0 * e 0 = 1 := by
    have := rel [(0, true), (0, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have r_b3 : e 2 * e 2 * e 2 = 1 := by
    have := rel [(2, true), (2, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have r_ab : (e 0)⁻¹ * (e 2)⁻¹ * e 0 * e 2 = 1 := by
    have := rel [(0, false), (2, false), (0, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have hab : e 0 * e 2 = e 2 * e 0 := by
    calc e 0 * e 2 = e 2 * e 0 * ((e 0)⁻¹ * (e 2)⁻¹ * e 0 * e 2) := by group
      _ = e 2 * e 0 := by rw [r_ab, mul_one]
  have ht_inv : (e 4)⁻¹ = e 4 := inv_eq_of_mul_eq_one_right r_tt
  have ha3 : e 0 ^ 3 = 1 := by rw [pow_three, ← mul_assoc]; exact r_a3
  have hb3 : e 2 ^ 3 = 1 := by rw [pow_three, ← mul_assoc]; exact r_b3
  have ht_a : e 4 * e 0 * (e 4)⁻¹ = (e 0)⁻¹ := by
    rw [ht_inv]
    exact eq_inv_of_mul_eq_one_left r_ta
  have ht_b : e 4 * e 2 * (e 4)⁻¹ = (e 2)⁻¹ := by
    rw [ht_inv]
    exact eq_inv_of_mul_eq_one_left r_tb
  have hcard9 : Nat.card (Subgroup.closure ({e 0, e 2} : Set G)) = 9 := hF.card_P
  have ha_ne : e 0 ≠ 1 := by
    intro h0
    have hsub : Subgroup.closure ({e 0, e 2} : Set G) ≤ Subgroup.zpowers (e 2) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx, h0]; exact Subgroup.one_mem _
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]; exact Subgroup.mem_zpowers _
    have hc := Subgroup.card_le_of_le hsub
    rw [Nat.card_zpowers, hcard9] at hc
    have hd : orderOf (e 2) ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hb_ne : e 2 ≠ 1 := by
    intro h0
    have hsub : Subgroup.closure ({e 0, e 2} : Set G) ≤ Subgroup.zpowers (e 0) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · rw [hx]; exact Subgroup.mem_zpowers _
      · rw [Set.mem_singleton_iff] at hx
        rw [hx, h0]; exact Subgroup.one_mem _
    have hc := Subgroup.card_le_of_le hsub
    rw [Nat.card_zpowers, hcard9] at hc
    have hd : orderOf (e 0) ∣ 3 := orderOf_dvd_of_pow_eq_one ha3
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have ht_ne : e 4 ≠ 1 := by
    intro ht
    rw [ht] at r_ta
    have h2 : e 0 * e 0 = 1 := by simpa using r_ta
    apply ha_ne
    calc e 0 = (e 0 * e 0 * e 0) * (e 0 * e 0)⁻¹ := by group
      _ = 1 := by rw [r_a3, h2, inv_one, mul_one]
  have ht2 : e 4 ^ 2 = 1 := by rw [sq]; exact r_tt
  obtain ⟨c, hc⟩ := isConj_iff.mp (hO (e 4) (orderOf_eq_prime ht2 ht_ne))
  have hz_mul : zOf e * zOf e = 1 := by
    have key : (c * zOf e * c⁻¹) * (c * zOf e * c⁻¹) = 1 := by rw [hc, r_tt]
    calc zOf e * zOf e = c⁻¹ * ((c * zOf e * c⁻¹) * (c * zOf e * c⁻¹)) * c := by group
      _ = 1 := by rw [key]; group
  have hz_ne : zOf e ≠ 1 := by
    intro hz
    apply ht_ne
    rw [← hc, hz]
    simp
  have hz_ord : orderOf (zOf e) = 2 := orderOf_eq_prime (by rw [sq]; exact hz_mul) hz_ne
  have hzmem : zOf e ∈ H₁ ⊓ H₂ := zOf_mem_inf h
  have inf_eq : H₁ ⊓ H₂ = Subgroup.zpowers (zOf e) := by
    have hle : Subgroup.zpowers (zOf e) ≤ H₁ ⊓ H₂ := Subgroup.zpowers_le.mpr hzmem
    have hcardz : Nat.card (Subgroup.zpowers (zOf e)) = 2 := by rw [Nat.card_zpowers, hz_ord]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardz, hone.card_inf])).symm
  have hH_eq : H = Subgroup.centralizer ((Subgroup.zpowers (zOf e) : Subgroup G) : Set G) := by
    have := hone.eq_centralizer
    rw [inf_eq] at this
    exact this
  have cent_z : ∀ g : G, g * zOf e = zOf e * g ↔ g ∈ H := by
    intro g
    constructor
    · intro hg
      rw [hH_eq, Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (show Commute (zOf e) g from hg.symm) k).eq
    · intro hg
      rw [hH_eq, Subgroup.mem_centralizer_iff] at hg
      exact (hg (zOf e) (Subgroup.mem_zpowers _)).symm
  have hv1 := hL.v₁
  have hv2 := hL.v₂
  have hM₁_comm : ∀ x ∈ M₁, ∀ y ∈ M₁, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (ha₁.1.is_comm.comm (⟨x, hx⟩ : ↥M₁) ⟨y, hy⟩)
  have hM₁_cube : ∀ x ∈ M₁, x ^ 3 = 1 := fun x hx => ha₁.2 x hx
  have hM₁_card : Nat.card M₁ = 27 := by
    rcases hL.cor.cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hPb] at h2; omega
    · exact h1
    · rw [hPb] at h2; omega
  have hM₂_card : Nat.card M₂ = 27 := by rw [← hL.cor.card_eq]; exact hM₁_card
  have hcardMb : Nat.card ↥(M₁ ⊓ Subgroup.centralizer {e 2}) = 9 := by
    have := hL.cor.card_Pb₂
    rw [hPb] at this
    omega
  have hsup₁ : M₁ ⊔ H₂ = Subgroup.centralizer {e 0} := hv1.compl.sup_eq
  have hH₂_cent : ∀ h ∈ H₂, e 0 * h = h * e 0 := by
    intro hh hmem
    have hc' : hh ∈ Subgroup.centralizer {e 0} := hsup₁ ▸ Subgroup.mem_sup_right hmem
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc').symm
  have hPb_comm : ∀ x ∈ Pb, ∀ y ∈ Pb, x * y = y * x := by
    rw [hL.cor.Pb_eq₂]
    have hA : ∀ x ∈ M₁ ⊓ Subgroup.centralizer {e 2}, ∀ y ∈ M₁ ⊓ Subgroup.centralizer {e 2},
        x * y = y * x := fun x hx y hy => hM₁_comm x hx.1 y hy.1
    have hB : ∀ x ∈ Subgroup.zpowers (e 2), ∀ y ∈ Subgroup.zpowers (e 2), x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow_self _ _ _).eq
    have hAB : ∀ x ∈ M₁ ⊓ Subgroup.centralizer {e 2}, ∀ y ∈ Subgroup.zpowers (e 2),
        x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hxb : x * e 2 = e 2 * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      exact (Commute.zpow_right (show Commute x (e 2) from hxb) k).eq
    exact comm_of_sup_comm hA hB hAB
  have a_Pb : e 0 ∈ Pb := hL.pb.P_le (Subgroup.subset_closure (by simp))
  have b_Pb : e 2 ∈ Pb := hL.pb.P_le (Subgroup.subset_closure (by simp))
  have ha_M₁ : e 0 ∈ M₁ := by
    have : e 0 ∈ M₁ ⊓ H := hv1.inf_H ▸ Subgroup.mem_zpowers _
    exact this.1
  exact
  { z_mul := hz_mul
    z_ne := hz_ne
    cent_z := cent_z
    inv_conj := fun u hu hu1 => hO u (orderOf_eq_prime (by rw [sq]; exact hu) hu1)
    a_H := ha_H
    b_H := hb_H
    t_H := he4
    t_mul := r_tt
    t_ne := ht_ne
    a_ne := ha_ne
    b_ne := hb_ne
    a_cube := ha3
    b_cube := hb3
    ab_comm := hab
    t_a := ht_a
    t_b := ht_b
    H₂_le := hH2
    H₂_cent_a := hH₂_cent
    inf_eq := inf_eq
    card_H := hF.card_H
    M₁_card := hM₁_card
    M₁_comm := hM₁_comm
    M₁_cube := hM₁_cube
    a_M₁ := ha_M₁
    M₁_inf_H := hv1.inf_H
    M₁_sup := hv1.compl.sup_eq
    M₁_disj := hv1.compl.disjoint
    M₁_conjC := hv1.compl.conj_mem
    M₁_t := hv1.conj_t
    norm_a := hv1.normalizer_eq
    M₂_card := hM₂_card
    M₂_inf_H := hv2.inf_H
    M₂_conjC := hv2.compl.conj_mem
    M₂_sup := hv2.compl.sup_eq
    Pb_card := hPb
    Pb_three := hL.pb.three
    Pb_comm := hPb_comm
    a_Pb := a_Pb
    b_Pb := b_Pb
    cent_P := hL.pb.compl.sup_eq.symm
    Pb_disj := hL.pb.compl.disjoint
    Pb_conjP := hL.pb.compl.conj_mem
    Pb_inf_z := hL.pb.inf_cent_z
    Pb_t := hL.pb.conj_t
    Pb_eq_b := hL.cor.Pb_eq₂
    Pb_eq_a := hL.cor.Pb_eq₁
    card_M₁_cent_b := hcardMb
    norm_P := hL.pb.normalizer_eq
    norm_P_H := hF.normP
    card_P := hcard9
    not_243_cent_a := by
      have hsupM : Nat.card ↥(M₁ ⊔ H₂) = Nat.card ↥M₁ * Nat.card ↥H₂ := by
        apply card_sup_of_normalizes
        · intro b hb m hm
          exact hv1.compl.conj_mem b (Subgroup.mem_centralizer_singleton_iff.mpr
            (hH₂_cent b hb).symm) m hm
        · exact hv1.compl.disjoint
      have hsupZ : Nat.card ↥(H₂ ⊔ Subgroup.zpowers (e 0)) = 3 * Nat.card ↥H₂ := by
        rw [card_sup_of_normalizes (A := H₂) (B := Subgroup.zpowers (e 0)), Nat.card_zpowers,
          orderOf_eq_prime ha3 ha_ne]
        · ring
        · intro g hg x hx
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
          have hc : Commute (e 0 ^ k) x :=
            Commute.zpow_left (show Commute (e 0) x from hH₂_cent x hx) k
          rw [hc.eq, mul_inv_cancel_right]
          exact hx
        · rw [inf_comm]; exact hF.disj₁
      have hCinf : Nat.card ↥(Subgroup.centralizer {e 0} ⊓ H) = 3 * Nat.card ↥H₂ := by
        rw [hF.cent₁, sup_comm, hsupZ]
      have hdvd : Nat.card ↥(Subgroup.centralizer {e 0} ⊓ H) ∣ 576 := by
        rw [← hF.card_H]; exact Subgroup.card_dvd_of_le inf_le_right
      have hCC : Nat.card ↥(Subgroup.centralizer {e 0}) = 27 * Nat.card ↥H₂ := by
        rw [← hsup₁, hsupM, hM₁_card]
      intro hdiv
      rw [hCC] at hdiv
      have h9 : 9 ∣ Nat.card ↥H₂ := by
        have h27 : 27 * 9 ∣ 27 * Nat.card ↥H₂ := by norm_num; exact hdiv
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h27
      obtain ⟨k, hk⟩ := h9
      have h27 : 27 ∣ Nat.card ↥(Subgroup.centralizer {e 0} ⊓ H) := by
        rw [hCinf, hk]; exact ⟨k, by ring⟩
      have := dvd_trans h27 hdvd
      norm_num at this
    not_conj_ab := hL.four.s12
    not_conj_mixed :=
      ⟨(hL.four.pure_mixed (e 0 * e 2) (by simp)).1,
        (hL.four.pure_mixed (e 0 * (e 2)⁻¹) (by simp)).1⟩ }


section Part2

variable {a b t z : G} {H H₁ H₂ M₁ M₂ Pb : Subgroup G}

theorem Core.comm_za (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) : z * a = a * z :=
  ((C.cent_z a).mpr C.a_H).symm

theorem Core.comm_zb (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) : z * b = b * z :=
  ((C.cent_z b).mpr C.b_H).symm

theorem Core.comm_zt (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) : z * t = t * z :=
  ((C.cent_z t).mpr C.t_H).symm

theorem Core.z_inv (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right C.z_mul

theorem conj_eq_self_of_commute {x y : G} (h : Commute x y) : y⁻¹ * x * y = x := by
  calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
    _ = y⁻¹ * (y * x) := by rw [h.eq]
    _ = x := by group

theorem zpow_involution {x : G} (hx : x * x = 1) (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h]
  · left; exact zpow_zero x
  · right; exact zpow_one x

def vMinus (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) : Subgroup G where
  carrier := {x | x ∈ M₁ ∧ z * x * z⁻¹ = x⁻¹}
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨M₁.mul_mem hx hy, ?_⟩
    calc z * (x * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [hx', hy']
      _ = (y * x)⁻¹ := by rw [mul_inv_rev]
      _ = (x * y)⁻¹ := by rw [C.M₁_comm y hy x hx]
  one_mem' := ⟨M₁.one_mem, by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨M₁.inv_mem hx, ?_⟩
    calc z * x⁻¹ * z⁻¹ = (z * x * z⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [hx']

theorem mem_vMinus (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {x : G} :
    x ∈ vMinus C ↔ x ∈ M₁ ∧ z * x * z⁻¹ = x⁻¹ := Iff.rfl

theorem Core.z_conj_M₁ (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {m : G} (hm : m ∈ M₁) :
    z * m * z⁻¹ ∈ M₁ :=
  C.M₁_conjC z (Subgroup.mem_centralizer_singleton_iff.mpr C.comm_za) m hm

theorem Core.decomp (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {m : G} (hm : m ∈ M₁) :
    m = (m * (z * m * z⁻¹))⁻¹ * (m⁻¹ * (z * m * z⁻¹)) ∧
      (m * (z * m * z⁻¹))⁻¹ ∈ Subgroup.zpowers a ∧
      m⁻¹ * (z * m * z⁻¹) ∈ vMinus C := by
  obtain ⟨y, hy⟩ : ∃ y, y = z * m * z⁻¹ := ⟨_, rfl⟩
  rw [← hy]
  have hyM : y ∈ M₁ := hy ▸ C.z_conj_M₁ hm
  have hmy : m * y = y * m := C.M₁_comm m hm y hyM
  have hzy : z * y * z⁻¹ = m := by
    rw [hy, C.z_inv]
    calc z * (z * m * z) * z = (z * z) * m * (z * z) := by group
      _ = m := by rw [C.z_mul]; group
  have hm3 : m * m * m = 1 := by
    have h := C.M₁_cube m hm
    rw [pow_three, ← mul_assoc] at h
    exact h
  have hmm : m⁻¹ * m⁻¹ = m := by
    calc m⁻¹ * m⁻¹ = m⁻¹ * m⁻¹ * (m * m * m) := by rw [hm3, mul_one]
      _ = m := by group
  have hcm : Commute (m⁻¹ * m⁻¹) y := by
    have h1 : Commute m y := hmy
    exact (h1.inv_left.mul_left h1.inv_left)
  have hdec : m = (m * y)⁻¹ * (m⁻¹ * y) := by
    calc m = m⁻¹ * m⁻¹ := hmm.symm
      _ = y⁻¹ * (m⁻¹ * m⁻¹) * y := (conj_eq_self_of_commute hcm).symm
      _ = (m * y)⁻¹ * (m⁻¹ * y) := by rw [mul_inv_rev]; group
  have hmyM : (m * y)⁻¹ ∈ M₁ := M₁.inv_mem (M₁.mul_mem hm hyM)
  have hc2 : Commute m⁻¹ y⁻¹ := (show Commute m y from hmy).inv_left.inv_right
  have hmyz : z * (m * y)⁻¹ * z⁻¹ = (m * y)⁻¹ := by
    calc z * (m * y)⁻¹ * z⁻¹ = (z * y * z⁻¹)⁻¹ * (z * m * z⁻¹)⁻¹ := by
          rw [mul_inv_rev]; group
      _ = m⁻¹ * y⁻¹ := by rw [hzy, ← hy]
      _ = y⁻¹ * m⁻¹ := hc2.eq
      _ = (m * y)⁻¹ := by rw [mul_inv_rev]
  refine ⟨hdec, ?_, ?_⟩
  · have hzc : z * (m * y)⁻¹ = (m * y)⁻¹ * z := by
      calc z * (m * y)⁻¹ = z * (m * y)⁻¹ * z⁻¹ * z := by group
        _ = (m * y)⁻¹ * z := by rw [hmyz]
    have hH : (m * y)⁻¹ ∈ H := (C.cent_z _).mp hzc.symm
    have hmem : (m * y)⁻¹ ∈ M₁ ⊓ H := ⟨hmyM, hH⟩
    rw [C.M₁_inf_H] at hmem
    exact hmem
  · rw [mem_vMinus]
    refine ⟨M₁.mul_mem (M₁.inv_mem hm) hyM, ?_⟩
    calc z * (m⁻¹ * y) * z⁻¹ = (z * m⁻¹ * z⁻¹) * (z * y * z⁻¹) := by group
      _ = (z * m * z⁻¹)⁻¹ * m := by rw [hzy]; group
      _ = y⁻¹ * m := by rw [← hy]
      _ = (m⁻¹ * y)⁻¹ := by rw [mul_inv_rev, inv_inv]

def wOne (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) : Subgroup G :=
  vMinus C ⊓ Subgroup.centralizer {b}

theorem mem_wOne (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {x : G} :
    x ∈ wOne C ↔ (x ∈ M₁ ∧ z * x * z⁻¹ = x⁻¹) ∧ x * b = b * x := by
  unfold wOne
  rw [Subgroup.mem_inf, mem_vMinus, Subgroup.mem_centralizer_singleton_iff]

theorem wOne_le_M₁ (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) : wOne C ≤ M₁ :=
  fun x hx => ((mem_wOne C).mp hx).1.1

theorem Core.cube_of_zpowers (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {x : G}
    (hx : x ∈ Subgroup.zpowers a) : x ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, C.a_cube, one_zpow]

theorem Core.commute_z_zpow_a (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {x : G}
    (hx : x ∈ Subgroup.zpowers a) : Commute z x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact Commute.zpow_right (show Commute z a from C.comm_za) k

theorem Core.vMinus_inf_zpowers (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    vMinus C ⊓ Subgroup.zpowers a = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hx, hxa⟩ := hx
  rw [Subgroup.mem_bot]
  rw [mem_vMinus] at hx
  have hcz : z * x = x * z := (C.commute_z_zpow_a hxa).eq
  have hxx : x * x = 1 := by
    have h1 : z * x * z⁻¹ = x := by rw [hcz]; group
    rw [h1] at hx
    calc x * x = x * x⁻¹ := by rw [← hx.2]
      _ = 1 := mul_inv_cancel x
  have hx3 := C.cube_of_zpowers hxa
  have hx3' : x * x * x = 1 := by
    have h := hx3
    rwa [pow_three, ← mul_assoc] at h
  calc x = (x * x * x) * (x * x)⁻¹ := by group
    _ = 1 := by rw [hx3', hxx, inv_one, mul_one]

theorem Core.M₁_cent_b_eq (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    M₁ ⊓ Subgroup.centralizer {b} = Subgroup.zpowers a ⊔ wOne C := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxb⟩ := Subgroup.mem_inf.mp hx
    have hxb' : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp hxb
    obtain ⟨hdec, hpl, hmin⟩ := C.decomp hxM
    have hyb : Commute b (z * x * z⁻¹) := by
      have hzb : z * b = b * z := C.comm_zb
      have hzb' : z⁻¹ * b = b * z⁻¹ := by
        calc z⁻¹ * b = z⁻¹ * (b * z) * z⁻¹ := by group
          _ = z⁻¹ * (z * b) * z⁻¹ := by rw [hzb]
          _ = b * z⁻¹ := by group
      show b * (z * x * z⁻¹) = (z * x * z⁻¹) * b
      calc b * (z * x * z⁻¹) = (b * z) * x * z⁻¹ := by group
        _ = (z * b) * x * z⁻¹ := by rw [hzb]
        _ = z * (b * x) * z⁻¹ := by group
        _ = z * (x * b) * z⁻¹ := by rw [hxb']
        _ = z * x * (b * z⁻¹) := by group
        _ = z * x * (z⁻¹ * b) := by rw [hzb']
        _ = (z * x * z⁻¹) * b := by group
    have hmin_b : x⁻¹ * (z * x * z⁻¹) ∈ wOne C := by
      rw [mem_wOne]
      refine ⟨⟨M₁.mul_mem (M₁.inv_mem hxM) (C.z_conj_M₁ hxM), ?_⟩, ?_⟩
      · exact (mem_vMinus C).mp hmin |>.2
      · exact (show Commute b (x⁻¹ * (z * x * z⁻¹)) from
          (show Commute b x⁻¹ from (show Commute b x from hxb'.symm).inv_right).mul_right hyb).eq.symm
    rw [hdec]
    exact mul_mem (Subgroup.mem_sup_left hpl) (Subgroup.mem_sup_right hmin_b)
  · rw [sup_le_iff]
    constructor
    · intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine Subgroup.mem_inf.mpr ⟨M₁.zpow_mem C.a_M₁ k, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (show (a ^ k) * b = b * (a ^ k) from (Commute.zpow_left (show Commute a b from C.ab_comm) k).eq)
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨wOne_le_M₁ C hx, Subgroup.mem_centralizer_singleton_iff.mpr ((mem_wOne C).mp hx).2⟩

theorem Core.card_wOne [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Nat.card ↥(wOne C) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥(M₁ ⊓ Subgroup.centralizer {b}) = 9 := C.card_M₁_cent_b
  rw [C.M₁_cent_b_eq, sup_comm] at hcard
  have hdisj : wOne C ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have h1 : x ∈ vMinus C ⊓ Subgroup.zpowers a :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx.1).1, hx.2⟩
    rw [C.vMinus_inf_zpowers, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr h1
  have hnorm : ∀ g ∈ Subgroup.zpowers a, ∀ x ∈ wOne C, g * x * g⁻¹ ∈ wOne C := by
    intro g hg x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc : Commute (a ^ k) x :=
      Commute.zpow_left (C.M₁_comm a C.a_M₁ x (wOne_le_M₁ C hx)) k
    rw [hc.eq, mul_inv_cancel_right]
    exact hx
  have hcard2 := card_sup_of_normalizes hnorm hdisj
  rw [hcard2, Nat.card_zpowers, orderOf_eq_prime C.a_cube C.a_ne] at hcard
  omega

theorem Core.t_wOne (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {x : G} (hx : x ∈ wOne C) :
    t * x * t⁻¹ ∈ wOne C := by
  have hx' := (mem_wOne C).mp hx
  rw [mem_wOne]
  have hc : Commute z t := C.comm_zt
  have hc' : Commute z⁻¹ t⁻¹ := hc.inv_left.inv_right
  refine ⟨⟨C.M₁_t x hx'.1.1, ?_⟩, ?_⟩
  · calc z * (t * x * t⁻¹) * z⁻¹ = (z * t) * x * (t⁻¹ * z⁻¹) := by group
      _ = (t * z) * x * (z⁻¹ * t⁻¹) := by rw [hc.eq, ← hc'.eq]
      _ = t * (z * x * z⁻¹) * t⁻¹ := by group
      _ = t * x⁻¹ * t⁻¹ := by rw [hx'.1.2]
      _ = (t * x * t⁻¹)⁻¹ := by group
  · have hbt : t * b⁻¹ * t⁻¹ = b := by
      calc t * b⁻¹ * t⁻¹ = (t * b * t⁻¹)⁻¹ := by group
        _ = b := by rw [C.t_b, inv_inv]
    have hbinv : b⁻¹ * x = x * b⁻¹ :=
      (show Commute b x from hx'.2.symm).inv_left.eq
    symm
    calc b * (t * x * t⁻¹) = (t * b⁻¹ * t⁻¹) * (t * x * t⁻¹) := by rw [hbt]
      _ = t * (b⁻¹ * x) * t⁻¹ := by group
      _ = t * (x * b⁻¹) * t⁻¹ := by rw [hbinv]
      _ = (t * x * t⁻¹) * (t * b⁻¹ * t⁻¹) := by group
      _ = (t * x * t⁻¹) * b := by rw [hbt]

theorem Core.exists_t' [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    ∃ t' : G, (t' = t ∨ t' = t * z) ∧ ∀ w ∈ wOne C, t' * w * t'⁻¹ = w := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w₀, hw₀, hw₀1⟩ : ∃ w ∈ wOne C, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : wOne C = ⊥ := eq_bot_iff.mpr (fun x hx => (Subgroup.mem_bot).mpr (hcon x hx))
    have h3 := C.card_wOne
    rw [hbot, Subgroup.card_bot] at h3
    norm_num at h3
  have hw₀3 : w₀ ^ 3 = 1 := C.M₁_cube w₀ (wOne_le_M₁ C hw₀)
  have hw₀3z : w₀ ^ (3 : ℤ) = 1 := by simpa using hw₀3
  have hw3' : w₀ * (w₀ * w₀) = 1 := by rw [← pow_three]; exact hw₀3
  have hord : orderOf w₀ = 3 := orderOf_eq_prime hw₀3 hw₀1
  have hzp : Subgroup.zpowers w₀ = wOne C :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw₀)
      (by rw [Nat.card_zpowers, hord, C.card_wOne])
  have h2 : w₀ ^ (2 : ℤ) = w₀⁻¹ := by
    rw [zpow_two]; exact (inv_eq_of_mul_eq_one_right hw3').symm
  have helem : ∀ w ∈ wOne C, w = 1 ∨ w = w₀ ∨ w = w₀⁻¹ := by
    intro w hw
    rw [← hzp] at hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [zpow_eq_zpow_emod k hw₀3z]
    have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk with h | h | h <;> rw [h]
    · left; simp
    · right; left; simp
    · right; right; exact h2
  have hu : t * w₀ * t⁻¹ ∈ wOne C := C.t_wOne hw₀
  have hu1 : t * w₀ * t⁻¹ ≠ 1 := by
    intro h
    apply hw₀1
    calc w₀ = t⁻¹ * (t * w₀ * t⁻¹) * t := by group
      _ = 1 := by rw [h]; group
  rcases helem _ hu with hu' | hu' | hu'
  · exact absurd hu' hu1
  · refine ⟨t, Or.inl rfl, fun w hw => ?_⟩
    rcases helem w hw with rfl | rfl | rfl
    · simp
    · exact hu'
    · calc t * w₀⁻¹ * t⁻¹ = (t * w₀ * t⁻¹)⁻¹ := by group
        _ = w₀⁻¹ := by rw [hu']
  · refine ⟨t * z, Or.inr rfl, fun w hw => ?_⟩
    have hzw := (mem_wOne C).mp hw
    have key : t * z * w * (t * z)⁻¹ = (t * w * t⁻¹)⁻¹ := by
      calc t * z * w * (t * z)⁻¹ = t * (z * w * z⁻¹) * t⁻¹ := by group
        _ = t * w⁻¹ * t⁻¹ := by rw [hzw.1.2]
        _ = (t * w * t⁻¹)⁻¹ := by group
    rw [key]
    rcases helem w hw with rfl | rfl | rfl
    · simp
    · rw [hu', inv_inv]
    · calc (t * w₀⁻¹ * t⁻¹)⁻¹ = t * w₀ * t⁻¹ := by group
        _ = w₀⁻¹ := hu'

theorem zpowers_eq_of_mem_of_ne_one [Finite G] {x y : G} (hy : y ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers y) (hx1 : x ≠ 1) : Subgroup.zpowers x = Subgroup.zpowers y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hx1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    simp
  have hyo : orderOf y = 3 := orderOf_eq_prime hy hy1
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hyo])

theorem Core.Pb_eq_sup (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Pb = Subgroup.closure ({a, b} : Set G) ⊔ wOne C := by
  have hP : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hP' : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Subgroup.closure ({a, b} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
  have hPeq : Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    le_antisymm hP hP'
  have h1 : Pb = (M₁ ⊓ Subgroup.centralizer {b}) ⊔ Subgroup.zpowers b := C.Pb_eq_b
  rw [C.M₁_cent_b_eq] at h1
  refine h1.trans ?_
  rw [hPeq]
  simp only [sup_assoc, sup_comm, sup_left_comm]

theorem Core.z_mem_cent_P (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    z ∈ Subgroup.centralizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) := by
  have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer {z} := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.mem_centralizer_singleton_iff.mpr C.comm_za.symm
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Subgroup.mem_centralizer_singleton_iff.mpr C.comm_zb.symm
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hs)

theorem Core.z_norm_Pb (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {p : G} (hp : p ∈ Pb) :
    z * p * z⁻¹ ∈ Pb :=
  C.Pb_conjP z C.z_mem_cent_P p hp

theorem Core.b_mem_norm_M₁ (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    b ∈ Subgroup.normalizer (M₁ : Set G) := by
  have hbC : b ∈ Subgroup.centralizer {a} := Subgroup.mem_centralizer_singleton_iff.mpr C.ab_comm.symm
  have hbinv : b⁻¹ ∈ Subgroup.centralizer {a} := Subgroup.inv_mem _ hbC
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact C.M₁_conjC b hbC h hh
  · intro hh
    have key : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
    rw [← key]
    exact C.M₁_conjC b⁻¹ hbinv _ hh

theorem Core.zpow_b_norm_M₁ (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    ∀ g ∈ Subgroup.zpowers b, ∀ x ∈ M₁, g * x * g⁻¹ ∈ M₁ := fun g hg x hx =>
  (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr C.b_mem_norm_M₁ hg) x).mp hx

theorem Core.M₁_inf_zpowers_b [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    M₁ ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxM, hxb⟩ := hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxH : x ∈ M₁ ⊓ H := Subgroup.mem_inf.mpr ⟨hxM, Subgroup.zpowers_le.mpr C.b_H hxb⟩
  rw [C.M₁_inf_H] at hxH
  have h1 := zpowers_eq_of_mem_of_ne_one C.a_cube hxH hx1
  have h2 := zpowers_eq_of_mem_of_ne_one C.b_cube hxb hx1
  have hab : a ∈ Subgroup.zpowers b := by
    have : Subgroup.zpowers a = Subgroup.zpowers b := h1.symm.trans h2
    rw [← this]
    exact Subgroup.mem_zpowers a
  have hPle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.zpowers b := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact hab
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]; exact Subgroup.mem_zpowers _
  have hc := Subgroup.card_le_of_le hPle
  rw [C.card_P, Nat.card_zpowers, orderOf_eq_prime C.b_cube C.b_ne] at hc
  omega

theorem Core.card_MM [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Nat.card ↥(M₁ ⊔ Subgroup.zpowers b) = 81 := by
  rw [card_sup_of_normalizes C.zpow_b_norm_M₁ C.M₁_inf_zpowers_b, C.M₁_card,
    Nat.card_zpowers, orderOf_eq_prime C.b_cube C.b_ne]

theorem Core.Pb_le_MM (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Pb ≤ M₁ ⊔ Subgroup.zpowers b := by
  rw [C.Pb_eq_sup, sup_le_iff]
  constructor
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.mem_sup_left C.a_M₁
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · exact le_trans (wOne_le_M₁ C) le_sup_left

theorem Core.MM_le_norm_Pb [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    M₁ ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (Pb : Set G) := by
  intro g hg
  have hcard27 : Nat.card ↥Pb = 27 := C.Pb_card
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact normal_of_index_three C.Pb_le_MM C.card_MM hcard27 g hg h hh
  · intro hh
    have hg' : g⁻¹ ∈ M₁ ⊔ Subgroup.zpowers b := Subgroup.inv_mem _ hg
    have key := normal_of_index_three C.Pb_le_MM C.card_MM hcard27 g⁻¹ hg' _ hh
    have e1 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [← e1]
    exact key

theorem Core.zpowers_inf_bot [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxa, hxb⟩ := hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have h1 := zpowers_eq_of_mem_of_ne_one C.a_cube hxa hx1
  have h2 := zpowers_eq_of_mem_of_ne_one C.b_cube hxb hx1
  have hab : a ∈ Subgroup.zpowers b := by
    have : Subgroup.zpowers a = Subgroup.zpowers b := h1.symm.trans h2
    rw [← this]
    exact Subgroup.mem_zpowers a
  have hPle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.zpowers b := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact hab
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]; exact Subgroup.mem_zpowers _
  have hc := Subgroup.card_le_of_le hPle
  rw [C.card_P, Nat.card_zpowers, orderOf_eq_prime C.b_cube C.b_ne] at hc
  omega

theorem Core.M₂_inf_zpowers_a [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    M₂ ⊓ Subgroup.zpowers a = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxM, hxa⟩ := hx
  have hxH : x ∈ M₂ ⊓ H := Subgroup.mem_inf.mpr ⟨hxM, Subgroup.zpowers_le.mpr C.a_H hxa⟩
  rw [C.M₂_inf_H] at hxH
  have hxb := hxH
  have : x ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := Subgroup.mem_inf.mpr ⟨hxa, hxb⟩
  rw [C.zpowers_inf_bot, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr this

theorem Core.a_mem_norm_M₂ (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    a ∈ Subgroup.normalizer (M₂ : Set G) := by
  have haC : a ∈ Subgroup.centralizer {b} := Subgroup.mem_centralizer_singleton_iff.mpr C.ab_comm
  have hainv : a⁻¹ ∈ Subgroup.centralizer {b} := Subgroup.inv_mem _ haC
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact C.M₂_conjC a haC h hh
  · intro hh
    have key : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rw [← key]
    exact C.M₂_conjC a⁻¹ hainv _ hh

theorem Core.card_M₂a [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Nat.card ↥(M₂ ⊔ Subgroup.zpowers a) = 81 := by
  have hnorm : ∀ g ∈ Subgroup.zpowers a, ∀ x ∈ M₂, g * x * g⁻¹ ∈ M₂ := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr C.a_mem_norm_M₂ hg) x).mp hx
  rw [card_sup_of_normalizes hnorm C.M₂_inf_zpowers_a, C.M₂_card,
    Nat.card_zpowers, orderOf_eq_prime C.a_cube C.a_ne]

theorem Core.Pb_le_M₂a (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Pb ≤ M₂ ⊔ Subgroup.zpowers a := by
  rw [C.Pb_eq_a]
  exact sup_le_sup_right inf_le_left _

theorem Core.exists_w0 [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    ∃ w₀ ∈ wOne C, w₀ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : wOne C = ⊥ := eq_bot_iff.mpr (fun x hx => (Subgroup.mem_bot).mpr (hcon x hx))
  have h3 := C.card_wOne
  rw [hbot, Subgroup.card_bot] at h3
  norm_num at h3

theorem Core.mem_Pb_of_cent_P [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {m : G}
    (hm : m ∈ Subgroup.centralizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G))
    {n : ℕ} (hn : m ^ 3 ^ n = 1) : m ∈ Pb := by
  have hcent : m ∈ Pb ⊔ Subgroup.zpowers z := by
    rw [← C.cent_P]; exact hm
  have hB : ∀ q ∈ Subgroup.zpowers z, ∀ p ∈ Pb, q * p * q⁻¹ ∈ Pb := by
    intro q hq p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    rcases zpow_involution C.z_mul k with h | h <;> rw [h]
    · simpa using hp
    · exact C.z_norm_Pb hp
  obtain ⟨p, hp, q, hq, hpq⟩ := (mem_sup_of_normalizes hB).mp hcent
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  subst hpq
  rcases zpow_involution C.z_mul k with h | h
  · rw [h, mul_one]; exact hp
  · rw [h] at hn ⊢
    have hxx : (p * z) * (p * z) ∈ Pb := by
      have : (p * z) * (p * z) = p * (z * p * z⁻¹) := by
        calc (p * z) * (p * z) = p * (z * p * z⁻¹) * (z * z) := by group
          _ = p * (z * p * z⁻¹) := by rw [C.z_mul, mul_one]
      rw [this]
      exact Pb.mul_mem hp (C.z_norm_Pb hp)
    have hodd : Odd (3 ^ n) := Odd.pow (by decide)
    obtain ⟨j, hj⟩ := hodd
    have key : p * z = (p * z) ^ (2 * j + 1) * (((p * z) ^ 2) ^ j)⁻¹ := by
      rw [← pow_mul, pow_succ, ((Commute.refl (p * z)).pow_left (2 * j)).eq, mul_inv_cancel_right]
    have hpow1 : (p * z) ^ (2 * j + 1) = 1 := by rw [← hj]; exact hn
    rw [hpow1, one_mul] at key
    rw [key]
    apply Pb.inv_mem
    apply Pb.pow_mem
    rw [sq]; exact hxx

theorem Core.t_inv (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right C.t_mul

theorem Core.P_le_Pb (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Subgroup.closure ({a, b} : Set G) ≤ Pb := by
  rw [C.Pb_eq_sup]; exact le_sup_left

theorem Core.E_le_norm_Pb (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Subgroup.closure ({t, z} : Set G) ≤ Subgroup.normalizer (Pb : Set G) := by
  have ht : t ∈ Subgroup.normalizer (Pb : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact C.Pb_t h hh
    · intro hh
      have := C.Pb_t _ hh
      rw [C.t_inv] at this
      have key : t * (t * h * t) * t = h := by
        calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
          _ = h := by rw [C.t_mul]; group
      rw [← key]; exact this
  have hz : z ∈ Subgroup.normalizer (Pb : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact C.z_norm_Pb hh
    · intro hh
      have := C.z_norm_Pb hh
      rw [C.z_inv] at this
      have key : z * (z * h * z) * z = h := by
        calc z * (z * h * z) * z = (z * z) * h * (z * z) := by group
          _ = h := by rw [C.z_mul]; group
      rw [← key]; exact this
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact ht
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact hz

theorem Core.norm_inter_H [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Pb : Set G)) (hgH : g ∈ H) :
    g ∈ Subgroup.closure ({a, b} : Set G) ⊔ Subgroup.closure ({t, z} : Set G) := by
  have hfwd : ∀ g' : G, g' ∈ Subgroup.normalizer (Pb : Set G) → g' ∈ H →
      ∀ h ∈ Subgroup.closure ({a, b} : Set G), g' * h * g'⁻¹ ∈ Subgroup.closure ({a, b} : Set G) := by
    intro g' hg'N hg'H h hh
    have hpb : h ∈ Pb := C.P_le_Pb hh
    have hconj : g' * h * g'⁻¹ ∈ Pb := (Subgroup.mem_normalizer_iff.mp hg'N h).mp hpb
    have hzh : h * z = z * h := Subgroup.mem_centralizer_iff.mp C.z_mem_cent_P h hh
    have hg'z : g' * z = z * g' := (C.cent_z g').mpr hg'H
    have hcomm : (g' * h * g'⁻¹) * z = z * (g' * h * g'⁻¹) := by
      have hgz : g'⁻¹ * z = z * g'⁻¹ := (show Commute g' z from hg'z).inv_left.eq
      calc (g' * h * g'⁻¹) * z = g' * h * (g'⁻¹ * z) := by group
        _ = g' * h * (z * g'⁻¹) := by rw [hgz]
        _ = g' * (h * z) * g'⁻¹ := by group
        _ = g' * (z * h) * g'⁻¹ := by rw [hzh]
        _ = (g' * z) * h * g'⁻¹ := by group
        _ = (z * g') * h * g'⁻¹ := by rw [hg'z]
        _ = z * (g' * h * g'⁻¹) := by group
    have hmem : g' * h * g'⁻¹ ∈ Pb ⊓ Subgroup.centralizer {z} :=
      Subgroup.mem_inf.mpr ⟨hconj, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    rw [C.Pb_inf_z] at hmem
    exact hmem
  have hgP : g ∈ Subgroup.normalizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact hfwd g hgN hgH h hh
    · intro hh
      have hginv : g⁻¹ ∈ Subgroup.normalizer (Pb : Set G) := Subgroup.inv_mem _ hgN
      have hinvH : g⁻¹ ∈ H := H.inv_mem hgH
      have := hfwd g⁻¹ hginv hinvH _ hh
      have key : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rw [← key]; exact this
  have hmem : g ∈ Subgroup.normalizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) ⊓ H :=
    Subgroup.mem_inf.mpr ⟨hgP, hgH⟩
  rw [C.norm_P_H] at hmem
  exact hmem

theorem Core.t_conj_cent_a (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {c : G}
    (hc : c ∈ Subgroup.centralizer {a}) : t * c * t⁻¹ ∈ Subgroup.centralizer {a} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  have hta : t⁻¹ * a * t = a⁻¹ := by
    rw [C.t_inv]
    have := C.t_a
    rw [C.t_inv] at this
    exact this
  calc t * c * t⁻¹ * a = t * c * (t⁻¹ * a * t) * t⁻¹ := by group
    _ = t * c * a⁻¹ * t⁻¹ := by rw [hta]
    _ = t * (a⁻¹ * c) * t⁻¹ := by
        have hca : c * a⁻¹ = a⁻¹ * c := by
          have h1 : Commute c a⁻¹ := (show Commute c a from hc).inv_right
          exact h1.eq
        rw [← hca]
        group
    _ = a * (t * c * t⁻¹) := by
        have hta' : t * a⁻¹ * t⁻¹ = a := by
          calc t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
            _ = a := by rw [C.t_a, inv_inv]
        calc t * (a⁻¹ * c) * t⁻¹ = (t * a⁻¹ * t⁻¹) * (t * c * t⁻¹) := by group
          _ = a * (t * c * t⁻¹) := by rw [hta']

theorem Core.norm_inter_norm_a [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Pb : Set G))
    (hga : g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    g ∈ (M₁ ⊔ Subgroup.zpowers b) ⊔ Subgroup.closure ({t, z} : Set G) := by
  have hga' : g ∈ Subgroup.centralizer {a} ⊔ Subgroup.zpowers t := by
    rw [← C.norm_a]; exact hga
  have hBt : ∀ s ∈ Subgroup.zpowers t, ∀ c ∈ Subgroup.centralizer {a},
      s * c * s⁻¹ ∈ Subgroup.centralizer {a} := by
    intro s hs c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    rcases zpow_involution C.t_mul k with h | h <;> rw [h]
    · simpa using hc
    · exact C.t_conj_cent_a hc
  obtain ⟨c, hc, s, hs, hcs⟩ := (mem_sup_of_normalizes hBt).mp hga'
  have hH₂C : ∀ h ∈ H₂, h ∈ Subgroup.centralizer {a} := fun h hh =>
    C.M₁_sup ▸ Subgroup.mem_sup_right hh
  have hBH : ∀ h ∈ H₂, ∀ m ∈ M₁, h * m * h⁻¹ ∈ M₁ := fun h hh m hm =>
    C.M₁_conjC h (hH₂C h hh) m hm
  have hc' : c ∈ M₁ ⊔ H₂ := C.M₁_sup ▸ hc
  obtain ⟨m, hm, h, hh, hmh⟩ := (mem_sup_of_normalizes hBH).mp hc'
  have hsH : s ∈ H := Subgroup.zpowers_le.mpr C.t_H hs
  have hhH : h ∈ H := C.H₂_le hh
  have hMN : M₁ ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (Pb : Set G) := C.MM_le_norm_Pb
  have heq : m⁻¹ * g = h * s := by
    rw [← hcs, ← hmh]; group
  have hhsN : h * s ∈ Subgroup.normalizer (Pb : Set G) := by
    rw [← heq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMN (Subgroup.mem_sup_left hm))) hgN
  have hhsPE := C.norm_inter_H hhsN (H.mul_mem hhH hsH)
  have hE : ∀ e' ∈ Subgroup.closure ({t, z} : Set G), ∀ p ∈ Subgroup.closure ({a, b} : Set G),
      e' * p * e'⁻¹ ∈ Subgroup.closure ({a, b} : Set G) := fun e' he' p hp =>
    ((Subgroup.mem_normalizer_iff.mp (by rw [C.norm_P]; exact Subgroup.mem_sup_right he')) p).mp hp
  obtain ⟨p, hp, e', he', hpe⟩ := (mem_sup_of_normalizes hE).mp hhsPE
  have hg2 : g = m * (h * s) := by
    rw [← heq]; group
  rw [← hpe] at hg2
  have hpMM : p ∈ M₁ ⊔ Subgroup.zpowers b := C.Pb_le_MM (C.P_le_Pb hp)
  have hmpMM : m * p ∈ M₁ ⊔ Subgroup.zpowers b := mul_mem (Subgroup.mem_sup_left hm) hpMM
  rw [hg2, ← mul_assoc]
  exact mul_mem (Subgroup.mem_sup_left hmpMM) (Subgroup.mem_sup_right he')

theorem zpow_eq_pow_nat {a : G} (ha : a ^ 3 = 1) (k : ℤ) : ∃ j : ℕ, a ^ k = a ^ j := by
  have h3 : a ^ (3 : ℤ) = 1 := by simpa using ha
  refine ⟨(k % 3).toNat, ?_⟩
  rw [zpow_eq_zpow_emod k h3, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]

theorem Core.wOne_le_Pb (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) : wOne C ≤ Pb := by
  intro x hx
  rw [C.Pb_eq_sup]
  exact Subgroup.mem_sup_right hx

theorem Core.zpowers_z_norm (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    ∀ q ∈ Subgroup.zpowers z, ∀ p ∈ Pb, q * p * q⁻¹ ∈ Pb := by
  intro q hq p hp
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  rcases zpow_involution C.z_mul k with h | h <;> rw [h]
  · simpa using hp
  · exact C.z_norm_Pb hp

theorem Core.M₂a_le_norm_Pb [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    M₂ ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (Pb : Set G) := by
  intro g hg
  have hcard27 : Nat.card ↥Pb = 27 := C.Pb_card
  have hnorm : ∀ g' ∈ Subgroup.zpowers a, ∀ x ∈ M₂, g' * x * g'⁻¹ ∈ M₂ := fun g' hg' x hx =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr C.a_mem_norm_M₂ hg') x).mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact normal_of_index_three C.Pb_le_M₂a C.card_M₂a hcard27 g hg h hh
  · intro hh
    have hg' : g⁻¹ ∈ M₂ ⊔ Subgroup.zpowers a := Subgroup.inv_mem _ hg
    have key := normal_of_index_three C.Pb_le_M₂a C.card_M₂a hcard27 g⁻¹ hg' _ hh
    have e1 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [← e1]
    exact key

theorem Core.a_notin_zpowers_b [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    a ∉ Subgroup.zpowers b := by
  intro ha
  have hPle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.zpowers b := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact ha
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]; exact Subgroup.mem_zpowers _
  have hc := Subgroup.card_le_of_le hPle
  rw [C.card_P, Nat.card_zpowers, orderOf_eq_prime C.b_cube C.b_ne] at hc
  omega

theorem Core.not_le_norm_a [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    ¬ Subgroup.normalizer (Pb : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  intro hle
  have hM₂N : M₂ ≤ Subgroup.normalizer (Pb : Set G) := le_trans le_sup_left C.M₂a_le_norm_Pb
  have hM₂3 : IsPGroup 3 M₂ := IsPGroup.of_card (n := 3) (by rw [C.M₂_card]; norm_num)
  have hMa : M₂ ≤ Subgroup.centralizer {a} := by
    intro m hm
    have hna : m ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := hle (hM₂N hm)
    have hconj : m * a * m⁻¹ ∈ Subgroup.zpowers a :=
      (Subgroup.mem_normalizer_iff.mp hna a).mp (Subgroup.mem_zpowers a)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj
    obtain ⟨j, hj⟩ := zpow_eq_pow_nat C.a_cube k
    obtain ⟨n, hn⟩ := pow_three_pow_eq_one_of_isPGroup hM₂3 hm
    have hfix := conj_eq_of_pow_three_eq_one hn (orderOf_eq_prime C.a_cube C.a_ne)
      (show m * a * m⁻¹ = a ^ j by rw [← hj, hk])
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m * a = (m * a * m⁻¹) * m := by group
      _ = a * m := by rw [hfix]
  have hMb : M₂ ≤ Subgroup.centralizer {b} := by
    intro m hm
    have : m ∈ M₂ ⊔ H₁ := Subgroup.mem_sup_left hm
    rw [C.M₂_sup] at this
    exact this
  have hMPb : M₂ ≤ Pb := by
    intro m hm
    have hcP : m ∈ Subgroup.centralizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hle2 : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer {m} := by
        rw [Subgroup.closure_le]
        intro x hx
        rcases hx with rfl | hx
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp (hMa hm)).symm
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp (hMb hm)).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle2 (SetLike.mem_coe.mp hs))
    obtain ⟨n, hn⟩ := pow_three_pow_eq_one_of_isPGroup hM₂3 hm
    exact C.mem_Pb_of_cent_P hcP hn
  have hEq : M₂ = Pb := Subgroup.eq_of_le_of_card_ge hMPb (by rw [C.M₂_card, C.Pb_card])
  have haM₂ : a ∈ M₂ := hEq ▸ C.a_Pb
  have hab : a ∈ Subgroup.zpowers b := by
    have h1 : a ∈ M₂ ⊓ H := Subgroup.mem_inf.mpr ⟨haM₂, C.a_H⟩
    rw [C.M₂_inf_H] at h1
    exact h1
  exact C.a_notin_zpowers_b hab

theorem Core.cent_Pb_eq [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) :
    Subgroup.centralizer (Pb : Set G) = Pb := by
  ext g
  constructor
  · intro hg
    have hgP : g ∈ Subgroup.centralizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact Subgroup.mem_centralizer_iff.mp hg s (C.P_le_Pb (SetLike.mem_coe.mp hs))
    have hgPbZ : g ∈ Pb ⊔ Subgroup.zpowers z := by rw [← C.cent_P]; exact hgP
    obtain ⟨p, hp, q, hq, hpq⟩ := (mem_sup_of_normalizes C.zpowers_z_norm).mp hgPbZ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    rcases zpow_involution C.z_mul k with h | h
    · rw [← hpq, h, mul_one]; exact hp
    · exfalso
      rw [h] at hpq
      have hgC : ∀ x ∈ Pb, x * g = g * x := fun x hx => Subgroup.mem_centralizer_iff.mp hg x hx
      have hzC : ∀ x ∈ Pb, x * z = z * x := by
        intro x hx
        have h1 : x * (p * z) = (p * z) * x := by
          have := hgC x hx
          rw [← hpq] at this
          exact this
        have hpx : p * x = x * p := C.Pb_comm p hp x hx
        calc x * z = p⁻¹ * (p * x * z) := by group
          _ = p⁻¹ * (x * p * z) := by rw [hpx]
          _ = p⁻¹ * (x * (p * z)) := by group
          _ = p⁻¹ * ((p * z) * x) := by rw [h1]
          _ = z * x := by group
      obtain ⟨w₀, hw₀, hw₀1⟩ := C.exists_w0
      have hw₀P : w₀ ∈ Pb := C.wOne_le_Pb hw₀
      have hzw : z * w₀ = w₀ * z := (hzC w₀ hw₀P).symm
      have hinv := (mem_wOne C).mp hw₀
      have hz_w0 : z * w₀ * z⁻¹ = w₀ := by rw [hzw]; group
      have hw_inv : w₀ = w₀⁻¹ := hz_w0.symm.trans hinv.1.2
      have h2 : w₀ * w₀ = 1 := by
        calc w₀ * w₀ = w₀ * w₀⁻¹ := by rw [← hw_inv]
          _ = 1 := mul_inv_cancel w₀
      have hw3 : w₀ ^ 3 = 1 := C.M₁_cube w₀ (wOne_le_M₁ C hw₀)
      have hw3' : w₀ * w₀ * w₀ = 1 := by rw [← pow_three']; exact hw3
      apply hw₀1
      calc w₀ = (w₀ * w₀ * w₀) * (w₀ * w₀)⁻¹ := by group
        _ = 1 := by rw [hw3', h2, inv_one, mul_one]
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact C.Pb_comm x hx g hg

theorem Core.t'_mul (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G} (ht' : t' = t ∨ t' = t * z) :
    t' * t' = 1 := by
  rcases ht' with rfl | rfl
  · exact C.t_mul
  · calc t * z * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [C.comm_zt]
      _ = (t * t) * (z * z) := by group
      _ = 1 := by rw [C.t_mul, C.z_mul, mul_one]

theorem Core.t'_ne (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G} (ht' : t' = t ∨ t' = t * z) :
    t' ≠ 1 := by
  rcases ht' with rfl | rfl
  · exact C.t_ne
  · intro h
    apply C.a_ne
    have htz : t = z := by
      calc t = t * z * z := by rw [mul_assoc, C.z_mul, mul_one]
        _ = z := by rw [h, one_mul]
    have hza : z * a * z⁻¹ = a := by
      calc z * a * z⁻¹ = a * z * z⁻¹ := by rw [C.comm_za]
        _ = a := by group
    have h1 : t * a * t⁻¹ = a := by rw [htz]; exact hza
    rw [C.t_a] at h1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel a
    have h3 : a * a * a = 1 := by
      have := C.a_cube
      rwa [pow_three, ← mul_assoc] at this
    calc a = (a * a * a) * (a * a)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, mul_one]

theorem Core.t'_a (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G} (ht' : t' = t ∨ t' = t * z) :
    t' * a * t'⁻¹ = a⁻¹ := by
  rcases ht' with rfl | rfl
  · exact C.t_a
  · calc t * z * a * (t * z)⁻¹ = t * (z * a * z⁻¹) * t⁻¹ := by group
      _ = t * (a * z * z⁻¹) * t⁻¹ := by rw [C.comm_za]
      _ = t * a * t⁻¹ := by group
      _ = a⁻¹ := C.t_a

theorem Core.t'_b (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G} (ht' : t' = t ∨ t' = t * z) :
    t' * b * t'⁻¹ = b⁻¹ := by
  rcases ht' with rfl | rfl
  · exact C.t_b
  · calc t * z * b * (t * z)⁻¹ = t * (z * b * z⁻¹) * t⁻¹ := by group
      _ = t * (b * z * z⁻¹) * t⁻¹ := by rw [C.comm_zb]
      _ = t * b * t⁻¹ := by group
      _ = b⁻¹ := C.t_b

theorem Core.t'_z (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G} (ht' : t' = t ∨ t' = t * z) :
    t' * z = z * t' := by
  rcases ht' with rfl | rfl
  · exact C.comm_zt.symm
  · calc t * z * z = t := by rw [mul_assoc, C.z_mul, mul_one]
      _ = z * (t * z) := by rw [← mul_assoc, C.comm_zt, mul_assoc, C.z_mul, mul_one]

theorem Core.P_le_cent_w (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {w : G} (hw : w ∈ wOne C) :
    Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer {w} := by
  rw [Subgroup.closure_le]
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · rw [hx]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (C.M₁_comm a C.a_M₁ w (wOne_le_M₁ C hw))
  · rw [hx]
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((mem_wOne C).mp hw).2.symm

theorem Core.P_comm (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) (x y : G)
    (hx : x ∈ Subgroup.closure ({a, b} : Set G)) (hy : y ∈ Subgroup.closure ({a, b} : Set G)) :
    x * y = y * x :=
  C.Pb_comm x (C.P_le_Pb hx) y (C.P_le_Pb hy)

theorem Core.inv_on_P (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) {x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    t' * x * t'⁻¹ = x⁻¹ := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact C.t'_a ht'
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact C.t'_b ht'
  | one => simp
  | mul x y hx hy ihx ihy =>
    calc t' * (x * y) * t'⁻¹ = (t' * x * t'⁻¹) * (t' * y * t'⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
      _ = (y * x)⁻¹ := by rw [mul_inv_rev]
      _ = (x * y)⁻¹ := by rw [C.P_comm y x hy hx]
  | inv x hx ih =>
    calc t' * x⁻¹ * t'⁻¹ = (t' * x * t'⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [ih]

theorem Core.P_cube (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {x : G}
    (hx : x ∈ Subgroup.closure ({a, b} : Set G)) : x ^ 3 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact C.a_cube
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact C.b_cube
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (show Commute x y from C.P_comm x y hx hy) 3), ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem Core.Pb_cube [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {x : G} (hx : x ∈ Pb) :
    x ^ 3 = 1 := by
  have hx' : x ∈ Subgroup.closure ({a, b} : Set G) ⊔ wOne C := by
    rw [← C.Pb_eq_sup]; exact hx
  have hx2 : x ∈ wOne C ⊔ Subgroup.closure ({a, b} : Set G) := by
    rw [sup_comm]; exact hx'
  have hB : ∀ p ∈ Subgroup.closure ({a, b} : Set G), ∀ w ∈ wOne C, p * w * p⁻¹ ∈ wOne C := by
    intro p hp w hw
    have hc : p * w = w * p := Subgroup.mem_centralizer_singleton_iff.mp (C.P_le_cent_w hw hp)
    rw [hc, mul_inv_cancel_right]
    exact hw
  obtain ⟨w, hw, p, hp, hwp⟩ := (mem_sup_of_normalizes hB).mp hx2
  have hc : Commute w p := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (C.P_le_cent_w hw hp)
    exact (show Commute p w from this).symm
  rw [← hwp, Commute.mul_pow hc 3, C.M₁_cube w (wOne_le_M₁ C hw), C.P_cube hp, one_mul]

theorem Core.Pb_decomp (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {x : G} (hx : x ∈ Pb) :
    ∃ w ∈ wOne C, ∃ p ∈ Subgroup.closure ({a, b} : Set G), w * p = x := by
  have hx' : x ∈ Subgroup.closure ({a, b} : Set G) ⊔ wOne C := by
    rw [← C.Pb_eq_sup]; exact hx
  have hx2 : x ∈ wOne C ⊔ Subgroup.closure ({a, b} : Set G) := by
    rw [sup_comm]; exact hx'
  have hB : ∀ p ∈ Subgroup.closure ({a, b} : Set G), ∀ w ∈ wOne C, p * w * p⁻¹ ∈ wOne C := by
    intro p hp w hw
    have hc : p * w = w * p := Subgroup.mem_centralizer_singleton_iff.mp (C.P_le_cent_w hw hp)
    rw [hc, mul_inv_cancel_right]
    exact hw
  exact (mem_sup_of_normalizes hB).mp hx2

theorem Core.z_fix_P (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {p : G}
    (hp : p ∈ Subgroup.closure ({a, b} : Set G)) : z * p * z⁻¹ = p := by
  have h1 : p * z = z * p := Subgroup.mem_centralizer_iff.mp C.z_mem_cent_P p hp
  calc z * p * z⁻¹ = (p * z) * z⁻¹ := by rw [h1]
    _ = p := by group

theorem Core.Pb_inf_cent_t' [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) :
    Pb ⊓ Subgroup.centralizer {t'} = wOne C := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxPb, hxc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨w, hw, p, hp, rfl⟩ := C.Pb_decomp hxPb
    have hxc' : (w * p) * t' = t' * (w * p) := Subgroup.mem_centralizer_singleton_iff.mp hxc
    have hconj : t' * (w * p) * t'⁻¹ = w * p := by
      rw [← hxc']; group
    have hconj' : t' * (w * p) * t'⁻¹ = w * p⁻¹ := by
      calc t' * (w * p) * t'⁻¹ = (t' * w * t'⁻¹) * (t' * p * t'⁻¹) := by group
        _ = w * p⁻¹ := by rw [hW w hw, C.inv_on_P ht' hp]
    have hpp : p⁻¹ = p := by
      have h1 : w * p⁻¹ = w * p := hconj'.symm.trans hconj
      exact mul_left_cancel h1
    have hp2 : p * p = 1 := by
      calc p * p = p * p⁻¹ := by rw [hpp]
        _ = 1 := mul_inv_cancel p
    have hp3 : p * p * p = 1 := by
      have := C.P_cube hp
      rwa [pow_three, ← mul_assoc] at this
    have hp1 : p = 1 := by
      calc p = (p * p * p) * (p * p)⁻¹ := by group
        _ = 1 := by rw [hp3, hp2, inv_one, mul_one]
    rw [hp1, mul_one]
    exact hw
  · intro hx
    have hxPb : x ∈ Pb := C.wOne_le_Pb hx
    refine Subgroup.mem_inf.mpr ⟨hxPb, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx1 := hW x hx
    have h2 : t' * x = x * t' := by
      calc t' * x = (t' * x * t'⁻¹) * t' := by group
        _ = x * t' := by rw [hx1]
    exact h2.symm

theorem Core.Pb_inf_cent_t'z [Finite G] (C : Core a b t z H H₁ H₂ M₁ M₂ Pb) {t' : G}
    (ht' : t' = t ∨ t' = t * z) (hW : ∀ w ∈ wOne C, t' * w * t'⁻¹ = w) :
    Pb ⊓ Subgroup.centralizer {t' * z} = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxPb, hxc⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  have hxc' : x * (t' * z) = (t' * z) * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
  obtain ⟨w, hw, p, hp, rfl⟩ := C.Pb_decomp hxPb
  have hzw : z * w * z⁻¹ = w⁻¹ := ((mem_wOne C).mp hw).1.2
  have hWinv : t' * w⁻¹ * t'⁻¹ = w⁻¹ := by
    calc t' * w⁻¹ * t'⁻¹ = (t' * w * t'⁻¹)⁻¹ := by group
      _ = w⁻¹ := by rw [hW w hw]
  have hsig : (t' * z) * (w * p) * (t' * z)⁻¹ = w⁻¹ * p⁻¹ := by
    calc (t' * z) * (w * p) * (t' * z)⁻¹ = (t' * (z * w * z⁻¹) * t'⁻¹) * (t' * (z * p * z⁻¹) * t'⁻¹) := by
          group
      _ = t' * w⁻¹ * t'⁻¹ * (t' * p * t'⁻¹) := by rw [hzw, C.z_fix_P hp]
      _ = w⁻¹ * p⁻¹ := by rw [hWinv, C.inv_on_P ht' hp]
  have hk : w⁻¹ * p⁻¹ = w * p := by
    rw [← hsig, ← hxc']
    group
  have hcomm' : Commute p w := Subgroup.mem_centralizer_singleton_iff.mp (C.P_le_cent_w hw hp)
  have hinv : (w * p)⁻¹ = w⁻¹ * p⁻¹ := by
    rw [mul_inv_rev]
    exact (hcomm'.inv_left.inv_right).eq
  have hsq : (w * p) * (w * p) = 1 := by
    have h1 : (w * p)⁻¹ = w * p := by rw [hinv, hk]
    calc (w * p) * (w * p) = (w * p) * (w * p)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel _
  have hcube : (w * p) ^ 3 = 1 := C.Pb_cube hxPb
  have hx3 : (w * p) * (w * p) * (w * p) = 1 := by rw [← pow_three']; exact hcube
  calc w * p = ((w * p) * (w * p) * (w * p)) * ((w * p) * (w * p))⁻¹ := by group
    _ = 1 := by rw [hx3, hsq, inv_one, mul_one]

end Part2

end CFSG.GH74.QTGen4.Recog.G23.P7.B27N

end
