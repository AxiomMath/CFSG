module

public import CFSG.ClassicalInvolution.AschTight.TzConj
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G]

theorem card_sup_mul_card_inf [Finite G] {A C : Subgroup G}
    (hC : C ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ C) * Nat.card ↥(A ⊓ C) = Nat.card A * Nat.card C := by
  have hA : A ≤ A ⊔ C := le_sup_left
  have hCL : C ≤ A ⊔ C := le_sup_right
  have : (A.subgroupOf (A ⊔ C)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mpr (sup_le Subgroup.le_normalizer hC)
  have h1 := Subgroup.relIndex_sup_left (C.subgroupOf (A ⊔ C)) (A.subgroupOf (A ⊔ C))
  rw [← Subgroup.subgroupOf_sup hA hCL, Subgroup.subgroupOf_self, Subgroup.relIndex_top_right,
    Subgroup.relIndex_subgroupOf hCL] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ C)
  have h3 := Subgroup.relIndex_mul_card (H := A) (K := C)
  rw [inf_eq_left.mpr hA] at h2
  have h4 : A.relIndex (A ⊔ C) = A.relIndex C := by
    rw [Subgroup.relIndex, ← h1]
  rw [← h2, ← h3, h4]
  ring

theorem mem_or_mul_mem_of_closure {B : Subgroup G} {b : G} (hb2 : b * b = 1)
    (hbB : b ∈ Subgroup.normalizer (B : Set G)) {x : G} (hx : x ∈ B ⊔ Subgroup.zpowers b) :
    x ∈ B ∨ x * b ∈ B :=
  mem_or_mul_mem_of_mem_sup_zpowers hb2 hbB hx

theorem exists_wreathBase [Finite G] {P : Subgroup G} (hP : IsWreathed P) :
    ∃ (B D : Subgroup G) (b : G) (n : ℕ), B ≤ P ∧ b ∈ P ∧ b ∉ B ∧ b * b = 1 ∧ 4 ≤ n ∧
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ Nat.card B = n * n ∧ Nat.card P = 2 * (n * n) ∧
      (∀ x ∈ B, x ^ n = 1) ∧ (∀ x ∈ P, x ∈ B ∨ x * b ∈ B) ∧
      D ≤ B ∧ Nat.card D = n ∧ (∀ d ∈ D, ∀ x ∈ P, d * x = x * d) ∧
      ∀ x ∈ P, x ∉ B → ∀ y ∈ B, y * x = x * y → y ∈ D := by
  obtain ⟨a, c, b, ha4, hca, hac, hcard, hb2, hbac, hbca, hcl⟩ := hP
  set n := orderOf a with hn
  obtain ⟨B, hB⟩ : ∃ B : Subgroup G, Subgroup.zpowers a ⊔ Subgroup.zpowers c = B := ⟨_, rfl⟩
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_sup_zpowers hac (hB ▸ hx) (hB ▸ hy)
  have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
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
  have hPB : ∀ x ∈ P, x ∈ B ∨ x * b ∈ B := fun x hx =>
    mem_or_mul_mem_of_closure hb2 hbB (hP ▸ hx)
  have hBP : B ≤ P := hP ▸ le_sup_left
  have hbP : b ∈ P := hP ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
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
  have hpow : ∀ x ∈ B, x ^ n = 1 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hac (hB ▸ hx)
    have h : Commute (a ^ i) (c ^ j) := (Commute.zpow_zpow (show Commute a c from hac) i j)
    rw [h.mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm i,
      mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, pow_orderOf_eq_one, ← hca,
      pow_orderOf_eq_one, one_zpow, one_zpow, one_mul]
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
  have hacB : a * c ∈ B := hB ▸ Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hbac' : b * (a * c) = (a * c) * b := by
    have e : b * (a * c) * b⁻¹ = c * a := by
      rw [show b * (a * c) * b⁻¹ = (b * a * b⁻¹) * (b * c * b⁻¹) by group, hbac, hbca]
    calc b * (a * c) = b * (a * c) * b⁻¹ * b := by group
      _ = c * a * b := by rw [e]
      _ = a * c * b := by rw [hacc.eq]
  have hcentral : ∀ d ∈ Subgroup.zpowers (a * c), ∀ x ∈ P, d * x = x * d := by
    intro d hd x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    have hdB : (a * c) ^ k ∈ B := Subgroup.zpow_mem _ hacB k
    have hdb : (a * c) ^ k * b = b * (a * c) ^ k :=
      ((Commute.zpow_right (show Commute b (a * c) from hbac') k).eq).symm
    rcases hPB x hx with h | h
    · exact hBc _ hdB _ h
    · have hx' : x = x * b * b := by rw [mul_assoc, hb2, mul_one]
      rw [hx']
      calc (a * c) ^ k * (x * b * b) = ((a * c) ^ k * (x * b)) * b := by group
        _ = (x * b * (a * c) ^ k) * b := by rw [hBc _ hdB _ h]
        _ = x * b * ((a * c) ^ k * b) := by group
        _ = x * b * (b * (a * c) ^ k) := by rw [hdb]
        _ = x * b * b * (a * c) ^ k := by group
  have hfix : ∀ x ∈ B, b * x * b⁻¹ = x → x ∈ Subgroup.zpowers (a * c) := by
    intro x hx hbx
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hac (hB ▸ hx)
    have hx' : a ^ i * c ^ j = (a * c) ^ i * c ^ (j - i) := by
      rw [hacc.mul_zpow, mul_assoc, ← zpow_add, add_sub_cancel]
    have hx'' : c ^ i * a ^ j = (a * c) ^ i * a ^ (j - i) := by
      rw [hacc.mul_zpow, show a ^ i * c ^ i = c ^ i * a ^ i from (hacc.zpow_zpow i i).eq,
        mul_assoc, ← zpow_add, add_sub_cancel]
    rw [hconj, hx'', hx'] at hbx
    have h1 : a ^ (j - i) = c ^ (j - i) := mul_left_cancel hbx
    have h2 : c ^ (j - i) = 1 := by
      rw [← h1]
      refine hac1 _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _) ?_
      rw [h1]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _
    rw [hx', h2, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  refine ⟨B, Subgroup.zpowers (a * c), b, n, hBP, hbP, hbnB, hb2, ha4, hBc, hBn,
    by rw [hcard, sq], hpow, hPB,
    Subgroup.zpowers_le.mpr hacB, by rw [Nat.card_zpowers, hDord], hcentral, ?_⟩
  intro x hx hxB y hy hyx
  have hxb : x * b ∈ B := (hPB x hx).resolve_left hxB
  apply hfix y hy
  have h1 : y * (x * b) = (x * b) * y := hBc _ hy _ hxb
  have hx' : x = x * b * b := by rw [mul_assoc, hb2, mul_one]
  have h2 : y * b = b * y := by
    have h3 : y * (x * b * b) = (x * b * b) * y := by rw [← hx']; exact hyx
    have h4 : (x * b) * (y * b) = (x * b) * (b * y) := by
      calc (x * b) * (y * b) = y * (x * b) * b := by rw [← mul_assoc, ← h1]
        _ = y * (x * b * b) := by group
        _ = (x * b * b) * y := h3
        _ = (x * b) * (b * y) := by group
    exact mul_left_cancel h4
  rw [hbb, ← h2, mul_assoc, hb2, mul_one]

theorem mul_comm_of_isUniqueInvolution {Q : Subgroup G} {z : G} (hz : IsUniqueInvolution Q z)
    {q : G} (hq : q ∈ Q) : q * z = z * q := by
  have hmem : q * z * q⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hq hz.mem) (Q.inv_mem hq)
  have hsq : q * z * q⁻¹ * (q * z * q⁻¹) = 1 := by
    calc q * z * q⁻¹ * (q * z * q⁻¹) = q * (z * z) * q⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have hne : q * z * q⁻¹ ≠ 1 := by
    intro h
    apply hz.ne_one
    calc z = q⁻¹ * (q * z * q⁻¹) * q := by group
      _ = 1 := by rw [h]; group
  have h1 : q * z * q⁻¹ = z := (hz.unique _ hmem hsq).resolve_left hne
  calc q * z = q * z * q⁻¹ * q := by group
    _ = z * q := by rw [h1]

theorem card_inf_le_of_pow [Finite G] {Q B : Subgroup G} {z : G} {n : ℕ} (hn : 0 < n)
    (hQ : IsPGroup 2 Q) (hz : IsUniqueInvolution Q z)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hpow : ∀ x ∈ B, x ^ n = 1) :
    Nat.card ↥(Q ⊓ B) ≤ n := by
  have hH : IsPGroup 2 ↥(Q ⊓ B) := hQ.to_le inf_le_left
  have hcomm : ∀ x y : ↥(Q ⊓ B), x * y = y * x := fun x y =>
    Subtype.ext (hBc _ x.2.2 _ y.2.2)
  have huniq : ∀ u v : ↥(Q ⊓ B), orderOf u = 2 → orderOf v = 2 → u = v := by
    have key : ∀ u : ↥(Q ⊓ B), orderOf u = 2 → (u : G) = z := by
      intro u hu
      have hu2 : (u : G) * u = 1 := by
        have h := pow_orderOf_eq_one u
        rw [hu, sq] at h
        exact congrArg Subtype.val h
      have hu1 : (u : G) ≠ 1 := by
        intro h
        have h1 : u = 1 := Subtype.ext h
        rw [h1, orderOf_one] at hu
        exact absurd hu (by norm_num)
      exact (hz.unique _ u.2.1 hu2).resolve_left hu1
    intro u v hu hv
    exact Subtype.ext ((key u hu).trans (key v hv).symm)
  have : IsCyclic ↥(Q ⊓ B) := CFSG.ABGLocalTools.isCyclic_of_isPGroup_two_of_comm hH hcomm huniq
  have hexp : Monoid.exponent ↥(Q ⊓ B) ∣ n :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simp [hpow g g.2.2])
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd hn hexp

theorem card_eq_two_mul_card_inf [Finite G] {P Q B : Subgroup G} (hBP : B ≤ P)
    (hcard : Nat.card P = 2 * Nat.card B) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hQP : Q ≤ P) (hnc : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x) :
    Nat.card Q = 2 * Nat.card ↥(Q ⊓ B) := by
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := P)
  rw [inf_eq_left.mpr hBP, hcard] at h1
  have hB0 : 0 < Nat.card B := Nat.card_pos
  have hrel : B.relIndex P = 2 := by nlinarith
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := Q)
  have hle : B.relIndex Q ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hQP (by rw [hrel]; norm_num)).trans hrel.le
  have hne1 : B.relIndex Q ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact hxy (hBc x (h hx) y (h hy))
  have hne0 : B.relIndex Q ≠ 0 := by
    intro h
    rw [h, zero_mul] at h2
    exact (Nat.card_pos (α := Q)).ne' h2.symm
  have hrelQ : B.relIndex Q = 2 := by omega
  rw [hrelQ, inf_comm] at h2
  exact h2.symm

theorem card_mul_self_eq_of_isWreathed [Finite G] {P Q : Subgroup G} {z : G}
    (hP : IsWreathed P) (hQP : Q ≤ P) (hQ : IsPGroup 2 Q) (hz : IsUniqueInvolution Q z)
    (hnc : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x) (hN : P ≤ Subgroup.normalizer (Q : Set G))
    (hcyc : ∃ g ∈ P, ∀ x ∈ P, ∃ k : ℤ, (g ^ k)⁻¹ * x ∈ Q) :
    Nat.card Q * Nat.card Q = 2 * Nat.card P := by
  obtain ⟨B, D, b, n, hBP, -, -, -, hn4, hBc, hBn, hPn, hpow, -, -, -, -, -⟩ :=
    exists_wreathBase hP
  have hn0 : 0 < n := by omega
  have hle := card_inf_le_of_pow hn0 hQ hz hBc hpow
  have hQB := card_eq_two_mul_card_inf hBP (by rw [hPn, hBn]) hBc hQP hnc
  have : (Q.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hN
  obtain ⟨g, hgP, hg⟩ := hcyc
  have hcycM : IsCyclic (↥P ⧸ Q.subgroupOf P) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgP⟩, fun y => ?_⟩⟩
    induction y using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hg x x.2
      refine ⟨k, ?_⟩
      show (QuotientGroup.mk (⟨g, hgP⟩ : ↥P) : ↥P ⧸ Q.subgroupOf P) ^ k = QuotientGroup.mk x
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hk
  let ψ : ↥B →* ↥P ⧸ Q.subgroupOf P :=
    (QuotientGroup.mk' (Q.subgroupOf P)).comp (Subgroup.inclusion hBP)
  have hker := Subgroup.card_ker_mul_card_range ψ
  have hrange : Nat.card ψ.range ≤ n := by
    have hexp : Monoid.exponent ψ.range ∣ n := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
      obtain ⟨y, x, rfl⟩ := y
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow]
      have : x ^ n = 1 := Subtype.ext (by simp [hpow x x.2])
      rw [this, map_one]
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hn0 hexp
  have hkerle : Nat.card ψ.ker ≤ Nat.card ↥(Q ⊓ B) := by
    let ι : ψ.ker → ↥(Q ⊓ B) := fun x => ⟨((x : ↥B) : G), by
      have hx : ψ x = 1 := x.2
      have h1 : (Subgroup.inclusion hBP (x : ↥B) : ↥P) ∈ Q.subgroupOf P :=
        (QuotientGroup.eq_one_iff _).mp hx
      exact ⟨Subgroup.mem_subgroupOf.mp h1, (x : ↥B).2⟩⟩
    refine Nat.card_le_card_of_injective ι fun x y hxy => ?_
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  rw [hBn] at hker
  have hge : n ≤ Nat.card ↥(Q ⊓ B) := by
    by_contra h
    push Not at h
    have h1 : Nat.card ψ.ker * Nat.card ψ.range < n * n :=
      lt_of_le_of_lt (Nat.mul_le_mul hkerle hrange) (Nat.mul_lt_mul_of_pos_right h hn0)
    omega
  have heq : Nat.card ↥(Q ⊓ B) = n := le_antisymm hle hge
  rw [hQB, heq, hPn]
  ring

theorem not_forall_inner_of_isWreathed [Finite G] {P Q : Subgroup G} {z : G}
    (hP : IsWreathed P) (hQP : Q ≤ P) (hQ : IsPGroup 2 Q) (hz : IsUniqueInvolution Q z)
    (hnc : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x) :
    ¬ ∀ w ∈ P, ∃ q ∈ Q, ∀ y ∈ Q, w * y * w⁻¹ = q * y * q⁻¹ := by
  intro hinner
  obtain ⟨B, D, b, n, hBP, -, -, hb2, hn4, hBc, hBn, hPn, hpow, hPB, hDB, hDn, hDc, hcent⟩ :=
    exists_wreathBase hP
  have hn0 : 0 < n := by omega
  have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  set C : Subgroup G := P ⊓ Subgroup.centralizer (Q : Set G) with hC
  obtain ⟨x₀, hx₀Q, hx₀B⟩ : ∃ x₀ ∈ Q, x₀ ∉ B := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact hxy (hBc x (h x hx) y (h y hy))
  have hCD : C ≤ D := by
    intro y hy
    have hyP : y ∈ P := hy.1
    have hyc : ∀ q ∈ Q, q * y = y * q := fun q hq =>
      Subgroup.mem_centralizer_iff.mp hy.2 q hq
    by_cases hyB : y ∈ B
    · exact hcent x₀ (hQP hx₀Q) hx₀B y hyB (hyc x₀ hx₀Q).symm
    · exfalso
      have hform : ∀ q ∈ Q, ∃ d ∈ D, d = q ∨ d * y = q := by
        intro q hq
        by_cases hqB : q ∈ B
        · exact ⟨q, hcent y hyP hyB q hqB (hyc q hq), Or.inl rfl⟩
        · have hqb : q * b ∈ B := (hPB q (hQP hq)).resolve_left hqB
          have hyb : y * b ∈ B := (hPB y hyP).resolve_left hyB
          have hmem : q * y⁻¹ ∈ B := by
            have e : q * y⁻¹ = (q * b) * (y * b)⁻¹ := by group
            rw [e]
            exact B.mul_mem hqb (B.inv_mem hyb)
          refine ⟨q * y⁻¹, hcent y hyP hyB _ hmem ?_, Or.inr (by group)⟩
          rw [show y * (q * y⁻¹) = (y * q) * y⁻¹ by group, ← hyc q hq]
          group
      obtain ⟨x, hx, w, hw, hxw⟩ := hnc
      apply hxw
      obtain ⟨d₁, hd₁, h1⟩ := hform x hx
      obtain ⟨d₂, hd₂, h2⟩ := hform w hw
      have hd₂P : d₂ ∈ P := hBP (hDB hd₂)
      have e1 : y * d₂ = d₂ * y := (hDc d₂ hd₂ y hyP).symm
      have e2 : y * d₁ = d₁ * y := (hDc d₁ hd₁ y hyP).symm
      have e3 : d₁ * d₂ = d₂ * d₁ := hDc d₁ hd₁ d₂ hd₂P
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact e3
      · calc d₁ * (d₂ * y) = d₁ * d₂ * y := by group
          _ = d₂ * d₁ * y := by rw [e3]
          _ = d₂ * (y * d₁) := by rw [e2]; group
          _ = d₂ * y * d₁ := by group
      · calc d₁ * y * d₂ = d₁ * (y * d₂) := by group
          _ = d₁ * d₂ * y := by rw [e1]; group
          _ = d₂ * d₁ * y := by rw [e3]
          _ = d₂ * (d₁ * y) := by group
      · calc d₁ * y * (d₂ * y) = d₁ * (y * d₂) * y := by group
          _ = d₁ * d₂ * y * y := by rw [e1]; group
          _ = d₂ * d₁ * y * y := by rw [e3]
          _ = d₂ * (y * d₁) * y := by rw [e2]; group
          _ = d₂ * y * (d₁ * y) := by group
  have hCn : Nat.card C ≤ n := hDn ▸ Subgroup.card_le_of_le hCD
  have hQ2n : Nat.card Q ≤ 2 * n := by
    rw [card_eq_two_mul_card_inf hBP (by rw [hPn, hBn]) hBc hQP hnc]
    have := card_inf_le_of_pow hn0 hQ hz hBc hpow
    omega
  have hzC : z ∈ Q ⊓ C := by
    refine ⟨hz.mem, hQP hz.mem, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    exact mul_comm_of_isUniqueInvolution hz hq
  have hinf : 2 ≤ Nat.card ↥(Q ⊓ C) := by
    have hne : Q ⊓ C ≠ ⊥ := by
      intro h
      rw [h, Subgroup.mem_bot] at hzC
      exact hz.ne_one hzC
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hCN : C ≤ Subgroup.normalizer (Q : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hprod := card_sup_mul_card_inf hCN
  have hPle : P ≤ Q ⊔ C := by
    intro w hw
    obtain ⟨q, hq, hqw⟩ := hinner w hw
    have hc : q⁻¹ * w ∈ C := by
      refine ⟨P.mul_mem (P.inv_mem (hQP hq)) hw, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h1 := hqw y hy
      calc y * (q⁻¹ * w) = q⁻¹ * (q * y * q⁻¹) * w := by group
        _ = q⁻¹ * (w * y * w⁻¹) * w := by rw [h1]
        _ = q⁻¹ * w * y := by group
    have e : w = q * (q⁻¹ * w) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hq hc
  have hPsup := Subgroup.card_le_of_le hPle
  rw [hPn] at hPsup
  have h1 : Nat.card ↥(Q ⊔ C) * 2 ≤ 2 * n * n := by
    calc Nat.card ↥(Q ⊔ C) * 2 ≤ Nat.card ↥(Q ⊔ C) * Nat.card ↥(Q ⊓ C) :=
          Nat.mul_le_mul_left _ hinf
      _ = Nat.card Q * Nat.card C := hprod
      _ ≤ 2 * n * n := Nat.mul_le_mul hQ2n hCn
  nlinarith

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
