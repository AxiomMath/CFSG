module

public import CFSG.ClassicalInvolution.AschTight.S1916WrAut
public import CFSG.ClassicalInvolution.Asc77.AscL62Quat

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G]

theorem isWreathed_wrData {P : Subgroup G} (hP : IsWreathed P) :
    ∃ (a c b : G) (B : Subgroup G), WrData P a c b B := by
  obtain ⟨a, c, b, ha4, hca, hac, hcard, hb2, hbac, hbca, hcl⟩ := hP
  set n := orderOf a with hn
  obtain ⟨B, hB⟩ : ∃ B : Subgroup G, Subgroup.zpowers a ⊔ Subgroup.zpowers c = B := ⟨_, rfl⟩
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_sup_zpowers hac (hB ▸ hx) (hB ▸ hy)
  have hconj : ∀ i j : ℤ, b * (a ^ i * c ^ j) * b⁻¹ = c ^ i * a ^ j := by
    intro i j
    rw [show b * (a ^ i * c ^ j) * b⁻¹ = (b * a * b⁻¹) ^ i * (b * c * b⁻¹) ^ j by
      rw [conj_zpow, conj_zpow]; group, hbac, hbca]
  have hbB : b ∈ Subgroup.normalizer (B : Set G) := by
    refine mem_normalizer_of_mul_self_eq_one hb2 fun x hx => ?_
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hac (hB ▸ hx)
    rw [hconj, ← hB]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _))
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _))
  have hP : P = B ⊔ Subgroup.zpowers b := by
    rw [← hcl, ← hB, Set.insert_eq, Set.insert_eq, Subgroup.closure_union, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure,
      sup_assoc]
  have hPcard : Nat.card P ≤ Nat.card B * 2 := by
    have e : Nat.card P = Nat.card ↥(((B ⊔ Subgroup.zpowers b : Subgroup G) : Set G)) := by
      rw [← hP]; rfl
    rw [e, Subgroup.coe_mul_of_right_le_normalizer_left B _ (Subgroup.zpowers_le.mpr hbB)]
    refine Set.natCard_mul_le.trans (Nat.mul_le_mul_left _ ?_)
    change Nat.card ↥(Subgroup.zpowers b) ≤ 2
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hb2))
  have hcomm : ∀ (m : ↥(Subgroup.zpowers a)) (k : ↥(Subgroup.zpowers c)),
      Commute ((Subgroup.zpowers a).subtype m) ((Subgroup.zpowers c).subtype k) := fun m k =>
    mul_comm_of_mem_sup_zpowers hac (Subgroup.mem_sup_left (by simp))
      (Subgroup.mem_sup_right (by simp))
  let φ := (Subgroup.zpowers a).subtype.noncommCoprod (Subgroup.zpowers c).subtype hcomm
  have hrange : φ.range = B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, hB]
  have hker := Subgroup.card_ker_mul_card_range φ
  rw [hrange, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hca] at hker
  have hn0 : 0 < n := by omega
  have hBn : Nat.card B = n * n := by
    have hk1 : 1 ≤ Nat.card φ.ker := Nat.card_pos
    have hB0 : 0 < Nat.card B := Nat.card_pos
    have h2 : Nat.card B ≤ n * n := by nlinarith
    have h3 : n * n ≤ Nat.card B := by rw [hcard] at hPcard; nlinarith
    omega
  have hker1 : Nat.card φ.ker = 1 := by
    have hpos : 0 < n * n := Nat.mul_pos hn0 hn0
    rw [hBn] at hker
    nlinarith
  have hac1 : ∀ x ∈ Subgroup.zpowers a, x ∈ Subgroup.zpowers c → x = 1 := by
    intro x hxa hxc
    have hmem : ((⟨x, hxa⟩, ⟨x⁻¹, Subgroup.inv_mem _ hxc⟩) :
        ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers c)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact mul_inv_cancel x
    have hbot : φ.ker = ⊥ := (Subgroup.card_eq_one).mp hker1
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg (fun q => (q.1 : G)) hmem
  have hbnB : b ∉ B := by
    intro hbB'
    have hle : P ≤ B := hP ▸ sup_le le_rfl (Subgroup.zpowers_le.mpr hbB')
    have := Subgroup.card_le_of_le hle
    rw [hcard, hBn] at this
    nlinarith
  have hacc : Commute a c := hac
  have hDord : orderOf (a * c) = n := by
    refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) ?_
    · rw [hacc.mul_pow, pow_orderOf_eq_one, ← hca, pow_orderOf_eq_one, one_mul]
    · have h1 : (a * c) ^ orderOf (a * c) = 1 := pow_orderOf_eq_one _
      rw [hacc.mul_pow] at h1
      have h2 : a ^ orderOf (a * c) = (c ^ orderOf (a * c))⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : a ^ orderOf (a * c) = 1 := by
        refine hac1 _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _) ?_
        rw [h2]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
      exact orderOf_dvd_of_pow_eq_one h3
  exact ⟨a, c, b, B, ⟨hB, hBc, ha4, hac, hb2, hbac, hbca, hP, hbnB, hbB, hBn,
    by rw [hcard, sq], hac1, hDord⟩⟩

omit [Finite G] in
theorem eq_one_of_pow_odd {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hx : x ∈ Q) {o : ℕ}
    (ho : Odd o) (hxo : x ^ o = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : orderOf x ∣ o := orderOf_dvd_of_pow_eq_one hxo
  rw [hk] at h1
  rcases k with _ | k
  · simpa using hk
  · exfalso
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr
      ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h1))

theorem centralizes_of_isWreathed_of_odd {P : Subgroup G} (hP : IsWreathed P)
    (hP2 : IsPGroup 2 P) {n : G} (hnP : conjSub n P = P) (hno : Odd (orderOf n)) :
    ∀ x ∈ P, n * x * n⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, c, b, B, h⟩ := isWreathed_wrData hP
  have hBP := h.BP
  have hbP := h.bP
  have hB2 : IsPGroup 2 B := hP2.to_le hBP
  have haB : a ∈ B := h.B_eq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hcB : c ∈ B := h.B_eq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_right h.b2
  have hBN : P ≤ Subgroup.normalizer (B : Set G) := by
    rw [h.P_eq]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr h.bN)
  have hnB : conjSub n B = B := by
    by_contra hne
    have hB'P : conjSub n B ≤ P := by rw [← hnP]; exact conjSub_mono hBP
    have hB'ab : ∀ x ∈ conjSub n B, ∀ y ∈ conjSub n B, x * y = y * x := by
      intro x hx y hy
      rw [mem_conjSub_iff] at hx hy
      have h1 := h.comm _ hx _ hy
      calc x * y = n * ((n⁻¹ * x * n) * (n⁻¹ * y * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * y * n) * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
        _ = y * x := by group
    have hcardB' : Nat.card ↥(conjSub n B) = Nat.card B := AscL62.natCard_conjSub n B
    obtain ⟨x, hxB', hxB⟩ : ∃ x ∈ conjSub n B, x ∉ B := by
      by_contra hcon
      push Not at hcon
      exact hne (Subgroup.eq_of_le_of_card_ge hcon (by rw [hcardB']))
    have hinf : B ⊓ conjSub n B ≤ Subgroup.zpowers (a * c) := by
      rintro y ⟨hyB, hyB'⟩
      have hxb : x * b ∈ B := (h.PB x (hB'P hxB')).resolve_left hxB
      have h1 : y * x = x * y := hB'ab y hyB' x hxB'
      have h2 : y * (x * b) = (x * b) * y := h.comm y hyB _ hxb
      have h3 : y * b = b * y := by
        have h4 : x * (y * b) = x * (b * y) := by
          calc x * (y * b) = (y * x) * b := by rw [← mul_assoc, ← h1]
            _ = (x * b) * y := by rw [mul_assoc, h2]
            _ = x * (b * y) := by group
        exact mul_left_cancel h4
      refine h.fix hyB ?_
      rw [← h3, mul_assoc, mul_inv_cancel, mul_one]
    have hcardinf : Nat.card ↥(B ⊓ conjSub n B) ≤ orderOf a :=
      (Subgroup.card_le_of_le hinf).trans (by rw [Nat.card_zpowers, h.ord_ac])
    have h1 := card_sup_mul_card_inf (A := B) (C := conjSub n B) (hB'P.trans hBN)
    have h2 : Nat.card ↥(B ⊔ conjSub n B) ≤ Nat.card P :=
      Subgroup.card_le_of_le (sup_le hBP hB'P)
    rw [hcardB', h.card_B] at h1
    rw [h.card_P] at h2
    have h5 := Nat.mul_le_mul h2 hcardinf
    rw [h1] at h5
    have h4 := h.four
    nlinarith
  have hβB : ∀ y ∈ B, n * y * n⁻¹ ∈ B := fun y hy => hnB ▸ conj_mem_conjSub hy
  have hβB' : ∀ y ∈ B, n⁻¹ * y * n ∈ B := by
    intro y hy
    have h1 : y ∈ conjSub n B := hnB.symm ▸ hy
    rw [mem_conjSub_iff] at h1
    exact h1
  have hnbP : n * b * n⁻¹ ∈ P := hnP ▸ conj_mem_conjSub hbP
  have hnbB : n * b * n⁻¹ ∉ B := by
    intro hmem
    apply h.bB
    have := hβB' _ hmem
    simpa [mul_assoc] using this
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, x₀ = n * b * n⁻¹ * b := ⟨_, rfl⟩
  have hx₀B : x₀ ∈ B := hx₀ ▸ (h.PB _ hnbP).resolve_left hnbB
  have hnb : n * b * n⁻¹ = x₀ * b := by rw [hx₀, mul_assoc (n * b * n⁻¹) b b, h.b2, mul_one]
  have hσβ : ∀ y ∈ B, n * (b * y * b⁻¹) * n⁻¹ = b * (n * y * n⁻¹) * b⁻¹ := by
    intro y hy
    have hbyB : b * (n * y * n⁻¹) * b⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp h.bN _).mp (hβB y hy)
    have hc := h.comm x₀ hx₀B _ hbyB
    calc n * (b * y * b⁻¹) * n⁻¹ = (n * b * n⁻¹) * (n * y * n⁻¹) * (n * b * n⁻¹)⁻¹ := by group
      _ = (x₀ * b) * (n * y * n⁻¹) * (x₀ * b)⁻¹ := by rw [hnb]
      _ = x₀ * (b * (n * y * n⁻¹) * b⁻¹) * x₀⁻¹ := by group
      _ = (b * (n * y * n⁻¹) * b⁻¹) * x₀ * x₀⁻¹ := by rw [hc]
      _ = b * (n * y * n⁻¹) * b⁻¹ := by group
  have hacc : Commute a c := h.hac
  have hacB : a * c ∈ B := B.mul_mem haB hcB
  have hac'B : a * c⁻¹ ∈ B := B.mul_mem haB (B.inv_mem hcB)
  have hbacb : b * (a * c) * b⁻¹ = a * c := by
    rw [show b * (a * c) * b⁻¹ = (b * a * b⁻¹) * (b * c * b⁻¹) by group, h.bac, h.bca, h.hac]
  have hbac'b : b * (a * c⁻¹) * b⁻¹ = (a * c⁻¹)⁻¹ := by
    rw [show b * (a * c⁻¹) * b⁻¹ = (b * a * b⁻¹) * (b * c * b⁻¹)⁻¹ by group, h.bac, h.bca,
      mul_inv_rev, inv_inv]
  have hD : conjSub n (Subgroup.zpowers (a * c)) = Subgroup.zpowers (a * c) := by
    have hmem : n * (a * c) * n⁻¹ ∈ Subgroup.zpowers (a * c) := by
      refine h.fix (hβB _ hacB) ?_
      rw [← hσβ _ hacB, hbacb]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [AscL62.natCard_conjSub])
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    change n * (a * c) ^ k * n⁻¹ ∈ _
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hmem _
  have hE : conjSub n (Subgroup.zpowers (a * c⁻¹)) = Subgroup.zpowers (a * c⁻¹) := by
    have hmem : n * (a * c⁻¹) * n⁻¹ ∈ Subgroup.zpowers (a * c⁻¹) := by
      refine h.anti (hβB _ hac'B) ?_
      rw [← hσβ _ hac'B, hbac'b]
      group
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [AscL62.natCard_conjSub])
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    change n * (a * c⁻¹) ^ k * n⁻¹ ∈ _
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hmem _
  have hcD := centralizes_of_isCyclic_of_odd (Subgroup.isCyclic_zpowers _)
    (hB2.to_le (Subgroup.zpowers_le.mpr hacB)) hD hno
  have hcE := centralizes_of_isCyclic_of_odd (Subgroup.isCyclic_zpowers _)
    (hB2.to_le (Subgroup.zpowers_le.mpr hac'B)) hE hno
  obtain ⟨e, he⟩ : ∃ e : G, e = a⁻¹ * (n * a * n⁻¹) := ⟨_, rfl⟩
  have heB : e ∈ B := he ▸ B.mul_mem (B.inv_mem haB) (hβB a haB)
  have hβa : n * a * n⁻¹ = a * e := by rw [he, mul_inv_cancel_left]
  have hβc : n * c * n⁻¹ = c * (b * e * b⁻¹) := by
    calc n * c * n⁻¹ = n * (b * a * b⁻¹) * n⁻¹ := by rw [h.bac]
      _ = b * (n * a * n⁻¹) * b⁻¹ := hσβ a haB
      _ = (b * a * b⁻¹) * (b * e * b⁻¹) := by rw [hβa]; group
      _ = c * (b * e * b⁻¹) := by rw [h.bac]
  have hσeB : b * e * b⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp h.bN _).mp heB
  have h1 : e * (b * e * b⁻¹) = 1 := by
    have h2 := hcD (a * c) (Subgroup.mem_zpowers _)
    rw [show n * (a * c) * n⁻¹ = (n * a * n⁻¹) * (n * c * n⁻¹) by group, hβa, hβc] at h2
    have h3 : a * c * (e * (b * e * b⁻¹)) = a * c * 1 := by
      rw [mul_one]
      calc a * c * (e * (b * e * b⁻¹)) = a * (c * e) * (b * e * b⁻¹) := by group
        _ = a * (e * c) * (b * e * b⁻¹) := by rw [h.comm c hcB e heB]
        _ = a * e * (c * (b * e * b⁻¹)) := by group
        _ = a * c := h2
    exact mul_left_cancel h3
  have h2 : e * (b * e * b⁻¹)⁻¹ = 1 := by
    have h4 := hcE (a * c⁻¹) (Subgroup.mem_zpowers _)
    rw [show n * (a * c⁻¹) * n⁻¹ = (n * a * n⁻¹) * (n * c * n⁻¹)⁻¹ by group, hβa, hβc] at h4
    have h3 : a * (e * (b * e * b⁻¹)⁻¹) * c⁻¹ = a * 1 * c⁻¹ := by
      rw [mul_one]
      calc a * (e * (b * e * b⁻¹)⁻¹) * c⁻¹ = a * e * ((b * e * b⁻¹)⁻¹ * c⁻¹) := by group
        _ = a * e * (c * (b * e * b⁻¹))⁻¹ := by rw [mul_inv_rev c (b * e * b⁻¹)]
        _ = a * c⁻¹ := h4
    exact mul_left_cancel (mul_right_cancel h3)
  have hσe : b * e * b⁻¹ = e := by
    have := mul_eq_one_iff_eq_inv.mp h2
    rw [inv_inv] at this
    exact this.symm
  have heD : e ∈ Subgroup.zpowers (a * c) := h.fix heB hσe
  have hne : n * e * n⁻¹ = e := hcD e heD
  have hiter : ∀ k : ℕ, n ^ k * a * (n ^ k)⁻¹ = a * e ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc n ^ (k + 1) * a * (n ^ (k + 1))⁻¹ = n * (n ^ k * a * (n ^ k)⁻¹) * n⁻¹ := by
            rw [pow_succ']; group
        _ = (n * a * n⁻¹) * (n * e * n⁻¹) ^ k := by rw [ih, conj_pow]; group
        _ = a * e ^ (k + 1) := by rw [hβa, hne, mul_assoc, ← pow_succ']
  have hee : e * e = 1 := by
    rw [hσe] at h1
    exact h1
  have he1 : e = 1 := by
    have hk := hiter (orderOf n)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hk
    have h5 : e ^ orderOf n = 1 := by
      have := congrArg (a⁻¹ * ·) hk
      simpa using this.symm
    exact eq_one_of_pow_odd hB2 heB hno h5
  have hna : n * a * n⁻¹ = a := by rw [hβa, he1, mul_one]
  have hnc : n * c * n⁻¹ = c := by rw [hβc, he1, mul_one, mul_inv_cancel, mul_one]
  have hBC : B ≤ Subgroup.centralizer ({n} : Set G) := by
    rw [← h.B_eq]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc a * n = n * (n⁻¹ * a * n) := by group
        _ = n * a := by
          congr 1
          calc n⁻¹ * a * n = n⁻¹ * (n * a * n⁻¹) * n := by rw [hna]
            _ = a := by group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc c * n = n * (n⁻¹ * c * n) := by group
        _ = n * c := by
          congr 1
          calc n⁻¹ * c * n = n⁻¹ * (n * c * n⁻¹) * n := by rw [hnc]
            _ = c := by group
  have hnx₀ : n * x₀ * n⁻¹ = x₀ := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hBC hx₀B)
    rw [← this]
    group
  have hiterb : ∀ k : ℕ, n ^ k * b * (n ^ k)⁻¹ = x₀ ^ k * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc n ^ (k + 1) * b * (n ^ (k + 1))⁻¹ = n * (n ^ k * b * (n ^ k)⁻¹) * n⁻¹ := by
            rw [pow_succ']; group
        _ = (n * x₀ * n⁻¹) ^ k * (n * b * n⁻¹) := by rw [ih, conj_pow]; group
        _ = x₀ ^ (k + 1) * b := by rw [hnx₀, hnb, ← mul_assoc, ← pow_succ]
  have hx₀1 : x₀ = 1 := by
    have hk := hiterb (orderOf n)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hk
    have h5 : x₀ ^ orderOf n = 1 := by
      have := congrArg (· * b⁻¹) hk
      simpa using this.symm
    exact eq_one_of_pow_odd hB2 hx₀B hno h5
  have hnb' : n * b * n⁻¹ = b := by rw [hnb, hx₀1, one_mul]
  have hPC : P ≤ Subgroup.centralizer ({n} : Set G) := by
    rw [h.P_eq]
    refine sup_le hBC (Subgroup.zpowers_le.mpr ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc b * n = n * (n⁻¹ * b * n) := by group
      _ = n * b := by
        congr 1
        calc n⁻¹ * b * n = n⁻¹ * (n * b * n⁻¹) * n := by rw [hnb']
          _ = b := by group
  intro x hx
  have := Subgroup.mem_centralizer_singleton_iff.mp (hPC hx)
  rw [← this]
  group

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
