module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem shape3_a2_sq : (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 := by decide

theorem shape3_a2_ne_one : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide

theorem shape3_a1_sq : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 := by
  decide

theorem shape3_xa0_sq : (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 := by
  decide

theorem shape3_conj :
    (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
      QuaternionGroup.a 2 * QuaternionGroup.a 1 := by
  decide

theorem shape3_comm_a2 : ∀ q : QuaternionGroup 2, q * QuaternionGroup.a 2 = QuaternionGroup.a 2 * q := by
  decide

theorem shape3_center : ∀ q : QuaternionGroup 2,
    (∀ q' : QuaternionGroup 2, q * q' = q' * q) → q = 1 ∨ q = QuaternionGroup.a 2 := by
  decide

theorem shape3_sq : ∀ q : QuaternionGroup 2, q ^ 2 = 1 ∨ q ^ 2 = QuaternionGroup.a 2 := by
  decide

theorem shape3_comm : ∀ q q' : QuaternionGroup 2,
    q * q' * q⁻¹ * q'⁻¹ = 1 ∨ q * q' * q⁻¹ * q'⁻¹ = QuaternionGroup.a 2 := by
  decide

theorem shape3_card : Nat.card (QuaternionGroup 2) = 2 ^ (2 + 1) := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

theorem shape3 {R : Subgroup K} (e : ↥R ≃* QuaternionGroup 2) :
    ∃ i j t : K, RShape 3 2 R t ∧ i ∈ R ∧ j ∈ R ∧ i ^ 2 = t ∧ j ^ 2 = t ∧
      j * i * j⁻¹ = t * i := by
  obtain ⟨g, hg⟩ : ∃ g : QuaternionGroup 2 → K, ∀ q, g q = ((e.symm q : ↥R) : K) :=
    ⟨fun q => ((e.symm q : ↥R) : K), fun q => rfl⟩
  have hg_mul : ∀ q q', g (q * q') = g q * g q' := by
    intro q q'
    simp [hg, map_mul]
  have hg_one : g 1 = 1 := by
    simp [hg]
  have hg_inv : ∀ q, g q⁻¹ = (g q)⁻¹ := by
    intro q
    simp [hg, map_inv]
  have hg_pow : ∀ (q : QuaternionGroup 2) (k : ℕ), g (q ^ k) = g q ^ k := by
    intro q k
    simp [hg, map_pow]
  have hg_mem : ∀ q, g q ∈ R := by
    intro q
    rw [hg]
    exact (e.symm q).2
  have hg_surj : ∀ r ∈ R, ∃ q, g q = r := by
    intro r hr
    refine ⟨e ⟨r, hr⟩, ?_⟩
    rw [hg]
    simp
  have hg_inj : ∀ q q', g q = g q' → q = q' := by
    intro q q' h
    rw [hg, hg] at h
    have h' : e.symm q = e.symm q' := Subtype.ext h
    simpa using congrArg e h'
  have hg_ne : g (QuaternionGroup.a 2) ≠ 1 := by
    intro h
    exact shape3_a2_ne_one (hg_inj _ _ (h.trans hg_one.symm))
  have hR : RShape 3 2 R (g (QuaternionGroup.a 2)) :=
    { pd := Or.inl ⟨rfl, rfl⟩
      card := by
        rw [Nat.card_congr e.toEquiv, shape3_card]
      t_mem := hg_mem _
      t_sq := by
        rw [← hg_pow, shape3_a2_sq, hg_one]
      t_ne := hg_ne
      t_comm := by
        intro r hr
        obtain ⟨q, rfl⟩ := hg_surj r hr
        rw [← hg_mul, ← hg_mul, shape3_comm_a2 q]
      center_le := by
        intro y hy hcomm
        obtain ⟨q, rfl⟩ := hg_surj y hy
        have hq : ∀ q' : QuaternionGroup 2, q * q' = q' * q := by
          intro q'
          apply hg_inj
          rw [hg_mul, hg_mul]
          exact hcomm _ (hg_mem q')
        rcases shape3_center q hq with h | h
        · rw [h, hg_one]
          exact Subgroup.one_mem _
        · rw [h]
          exact Subgroup.mem_zpowers _
      sq_mem := by
        intro r hr
        obtain ⟨q, rfl⟩ := hg_surj r hr
        rw [← hg_pow]
        rcases shape3_sq q with h | h
        · rw [h, hg_one]
          exact Subgroup.one_mem _
        · rw [h]
          exact Subgroup.mem_zpowers _
      comm_mem := by
        intro r hr s hs
        obtain ⟨q, rfl⟩ := hg_surj r hr
        obtain ⟨q', rfl⟩ := hg_surj s hs
        have hc : ⁅g q, g q'⁆ = g (q * q' * q⁻¹ * q'⁻¹) := by
          simp only [commutatorElement_def, hg_mul, hg_inv]
        rw [hc]
        rcases shape3_comm q q' with h | h
        · rw [h, hg_one]
          exact Subgroup.one_mem _
        · rw [h]
          exact Subgroup.mem_zpowers _
      sqrt := ⟨g (QuaternionGroup.a 1), hg_mem _, by rw [← hg_pow, shape3_a1_sq]⟩ }
  refine ⟨g (QuaternionGroup.a 1), g (QuaternionGroup.xa 0), g (QuaternionGroup.a 2), hR,
    hg_mem _, hg_mem _, by rw [← hg_pow, shape3_a1_sq], by rw [← hg_pow, shape3_xa0_sq], ?_⟩
  have h := congrArg g shape3_conj
  simp only [hg_mul, hg_inv] at h
  exact h
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem shape5_q8_central : ∀ x : QuaternionGroup 2,
    (∀ y : QuaternionGroup 2, x * y = y * x) → x = 1 ∨ x = QuaternionGroup.a 2 := by
  decide

theorem shape5_q8_comm : ∀ x y : QuaternionGroup 2,
    ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = QuaternionGroup.a 2 := by
  decide

theorem shape5_q8_sq : ∀ x : QuaternionGroup 2, x ^ 2 = 1 ∨ x ^ 2 = QuaternionGroup.a 2 := by
  decide

theorem shape5_d8_central : ∀ x : DihedralGroup 4,
    (∀ y : DihedralGroup 4, x * y = y * x) → x = 1 ∨ x = DihedralGroup.r 2 := by
  decide

theorem shape5_d8_comm : ∀ x y : DihedralGroup 4,
    ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = DihedralGroup.r 2 := by
  decide

theorem shape5_d8_sq : ∀ x : DihedralGroup 4, x ^ 2 = 1 ∨ x ^ 2 = DihedralGroup.r 2 := by
  decide

theorem shape5_q8_a2_ne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by
  decide

theorem shape5_q8_mul_rel : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 *
    (QuaternionGroup.xa 0)⁻¹ = QuaternionGroup.a 2 * QuaternionGroup.a 1 := by
  decide

theorem shape5_q8_sq_i : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 := by
  decide

theorem shape5_q8_sq_j : (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 := by
  decide

theorem shape5_d8_sq_r : (DihedralGroup.r 1 : DihedralGroup 4) ^ 2 = DihedralGroup.r 2 := by
  decide

theorem shape5_d8_sq_s : (DihedralGroup.sr 0 : DihedralGroup 4) ^ 2 = 1 := by
  decide

theorem shape5_d8_sr0_ne : (DihedralGroup.sr 0 : DihedralGroup 4) ≠ 1 := by
  decide

theorem shape5_d8_rel : (DihedralGroup.r 1 : DihedralGroup 4) * DihedralGroup.sr 0 *
    (DihedralGroup.r 1)⁻¹ = DihedralGroup.r 2 * DihedralGroup.sr 0 := by
  decide

theorem shape5_card_sup_mul_inf {A B : Subgroup K} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B : Subgroup K) * Nat.card ↥(A ⊓ B : Subgroup K) =
      Nat.card ↥A * Nat.card ↥B := by
  let φ : (↥A × ↥B) →* K :=
    { toFun := fun p => (p.1 : K) * (p.2 : K)
      map_one' := by simp
      map_mul' := by
        intro p q
        have h : (q.1 : K) * (p.2 : K) = (p.2 : K) * (q.1 : K) := hAB _ q.1.2 _ p.2.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (p.1 : K) * q.1 * (p.2 * q.2) = p.1 * (q.1 * p.2) * q.2 := by simp only [mul_assoc]
          _ = p.1 * (p.2 * q.1) * q.2 := by rw [h]
          _ = p.1 * p.2 * (q.1 * q.2) := by simp only [mul_assoc] }
  have hrange : φ.range = A ⊔ B := by
    apply le_antisymm
    · intro y hy
      obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hy
      exact Subgroup.mul_mem _ ((le_sup_left : A ≤ A ⊔ B) p.1.2)
        ((le_sup_right : B ≤ A ⊔ B) p.2.2)
    · apply sup_le
      · intro a ha
        exact MonoidHom.mem_range.mpr ⟨(⟨a, ha⟩, 1), by simp [φ]⟩
      · intro b hb
        exact MonoidHom.mem_range.mpr ⟨(1, ⟨b, hb⟩), by simp [φ]⟩
  have hcardker : Nat.card φ.ker = Nat.card ↥(A ⊓ B : Subgroup K) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : K), ?_⟩
        invFun := fun c => ⟨(⟨(c : K), c.2.1⟩, ⟨(c : K)⁻¹, inv_mem c.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun c => Subtype.ext rfl }
    · have hx : (x.1.1 : K) * (x.1.2 : K) = 1 := MonoidHom.mem_ker.mp x.2
      have hB : (x.1.1 : K) = (x.1.2 : K)⁻¹ := eq_inv_of_mul_eq_one_left hx
      exact Subgroup.mem_inf.mpr ⟨x.1.1.2, by rw [hB]; exact inv_mem x.1.2.2⟩
    · exact MonoidHom.mem_ker.mpr (mul_inv_cancel (c : K))
    · have hx : (x.1.1 : K) * (x.1.2 : K) = 1 := MonoidHom.mem_ker.mp x.2
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        exact (eq_inv_of_mul_eq_one_right hx).symm
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hrange, Nat.card_prod, hcardker] at h1
  rw [mul_comm]
  exact h1

theorem shape5_q8_a2_central : ∀ y : QuaternionGroup 2,
    QuaternionGroup.a 2 * y = y * QuaternionGroup.a 2 := by
  decide

theorem shape5_q8_a2_sq : (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 := by
  decide

theorem shape5_sup_decomp {A B : Subgroup K} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : K}
    (hy : y ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  let φ : (↥A × ↥B) →* K :=
    { toFun := fun p => (p.1 : K) * (p.2 : K)
      map_one' := by simp
      map_mul' := by
        intro p q
        have h : (q.1 : K) * (p.2 : K) = (p.2 : K) * (q.1 : K) := hAB _ q.1.2 _ p.2.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (p.1 : K) * q.1 * (p.2 * q.2) = p.1 * (q.1 * p.2) * q.2 := by simp only [mul_assoc]
          _ = p.1 * (p.2 * q.1) * q.2 := by rw [h]
          _ = p.1 * p.2 * (q.1 * q.2) := by simp only [mul_assoc] }
  have hle : A ⊔ B ≤ φ.range := by
    apply sup_le
    · intro a ha
      exact MonoidHom.mem_range.mpr ⟨(⟨a, ha⟩, 1), by simp [φ]⟩
    · intro b hb
      exact MonoidHom.mem_range.mpr ⟨(1, ⟨b, hb⟩), by simp [φ]⟩
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp (hle hy)
  exact ⟨(p.1 : K), p.1.2, (p.2 : K), p.2.2, hp.symm⟩

theorem shape5_comm_decomp {A B : Subgroup K} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {a1 a2 b1 b2 : K} (ha1 : a1 ∈ A) (ha2 : a2 ∈ A) (hb1 : b1 ∈ B) (hb2 : b2 ∈ B) :
    ⁅a1 * b1, a2 * b2⁆ = ⁅a1, a2⁆ * ⁅b1, b2⁆ := by
  have sw : ∀ {a b : K}, a ∈ A → b ∈ B → ∀ y : K, b * (a * y) = a * (b * y) := by
    intro a b ha hb y
    rw [← mul_assoc, ← mul_assoc, hAB a ha b hb]
  have ha1i : a1⁻¹ ∈ A := inv_mem ha1
  have ha2i : a2⁻¹ ∈ A := inv_mem ha2
  have hb1i : b1⁻¹ ∈ B := inv_mem hb1
  have hb2i : b2⁻¹ ∈ B := inv_mem hb2
  simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
  rw [sw ha2 hb1, sw ha1i hb1i, sw ha1i hb2, sw ha1i hb1, ← hAB _ ha2i _ hb2i,
    sw ha2i hb1i, sw ha2i hb2, sw ha2i hb1]

theorem shape5 {R A B : Subgroup K} (eA : ↥A ≃* QuaternionGroup 2) (eB : ↥B ≃* DihedralGroup 4)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hR : A ⊔ B = R)
    (hcard : Nat.card ↥(A ⊓ B : Subgroup K) = 2) :
    ∃ i j r s t : K, RShape 5 4 R t ∧ i ∈ A ∧ j ∈ A ∧ r ∈ B ∧ s ∈ B ∧ i ^ 2 = t ∧ j ^ 2 = t ∧
      j * i * j⁻¹ = t * i ∧ r ^ 2 = t ∧ s ^ 2 = 1 ∧ s ≠ 1 ∧ r * s * r⁻¹ = t * s := by
  subst hR
  obtain ⟨c, hcAB, hc1⟩ : ∃ c : K, c ∈ A ⊓ B ∧ c ≠ 1 := by
    obtain ⟨x, hx⟩ : ∃ x : ↥(A ⊓ B : Subgroup K), x ≠ 1 := by
      by_contra hcon
      have hall : ∀ x : ↥(A ⊓ B : Subgroup K), x = 1 :=
        fun x => not_not.mp (fun hx => hcon ⟨x, hx⟩)
      have h1 : Nat.card ↥(A ⊓ B : Subgroup K) = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun x y => by rw [hall x, hall y]⟩, ⟨1⟩⟩
      omega
    exact ⟨x.1, x.2, fun h => hx (Subtype.ext h)⟩
  obtain ⟨hcA, hcB⟩ := Subgroup.mem_inf.mp hcAB
  obtain ⟨tA', htA'⟩ : ∃ x : ↥A, x = eA.symm (QuaternionGroup.a 2) := ⟨_, rfl⟩
  have hetA : eA tA' = QuaternionGroup.a 2 := by
    rw [htA', MulEquiv.apply_symm_apply]
  have hcAel : (⟨c, hcA⟩ : ↥A) = tA' := by
    have hcen : ∀ y : QuaternionGroup 2, eA ⟨c, hcA⟩ * y = y * eA ⟨c, hcA⟩ := by
      intro y
      have h2 : eA.symm y * ⟨c, hcA⟩ = ⟨c, hcA⟩ * eA.symm y :=
        Subtype.ext (hAB _ (eA.symm y).2 c hcB)
      have h3 := congrArg eA h2
      simp only [map_mul, MulEquiv.apply_symm_apply] at h3
      exact h3.symm
    rcases shape5_q8_central _ hcen with h | h
    · exact absurd (congrArg Subtype.val (eA.injective (h.trans (map_one eA).symm))) hc1
    · apply eA.injective
      rw [h, hetA]
  have hct : c = (tA' : K) := congrArg Subtype.val hcAel
  have htA_mem : (tA' : K) ∈ B := by
    rw [← hct]
    exact hcB
  have htA_A : (tA' : K) ∈ A := tA'.2
  have htA_ne : (tA' : K) ≠ 1 := by
    intro h
    have h1 : tA' = 1 := Subtype.ext h
    apply shape5_q8_a2_ne
    rw [← hetA, h1, map_one]
  have htA_sq : (tA' : K) ^ 2 = 1 := by
    have h1 : tA' ^ 2 = 1 := by
      apply eA.injective
      rw [map_pow, hetA, map_one]
      exact shape5_q8_a2_sq
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have htA_cent_A : ∀ a ∈ A, (tA' : K) * a = a * (tA' : K) := by
    intro a ha
    have h1 : tA' * (⟨a, ha⟩ : ↥A) = (⟨a, ha⟩ : ↥A) * tA' := by
      apply eA.injective
      rw [map_mul, map_mul, hetA]
      exact shape5_q8_a2_central _
    exact congrArg Subtype.val h1
  have htA_cent_B : ∀ b ∈ B, (tA' : K) * b = b * (tA' : K) := fun b hb => hAB _ htA_A b hb
  have hBcomm : ∀ b : ↥B,
      (⟨(tA' : K), htA_mem⟩ : ↥B) * b = b * (⟨(tA' : K), htA_mem⟩ : ↥B) := by
    intro b
    exact Subtype.ext (htA_cent_B _ b.2)
  have hcentB : ∀ y : DihedralGroup 4,
      eB ⟨(tA' : K), htA_mem⟩ * y = y * eB ⟨(tA' : K), htA_mem⟩ := by
    intro y
    have h3 := congrArg eB (hBcomm (eB.symm y))
    simp only [map_mul, MulEquiv.apply_symm_apply] at h3
    exact h3
  have hetB2 : eB ⟨(tA' : K), htA_mem⟩ = DihedralGroup.r 2 := by
    rcases shape5_d8_central _ hcentB with h | h
    · exfalso
      have h4 : (⟨(tA' : K), htA_mem⟩ : ↥B) = 1 := eB.injective (h.trans (map_one eB).symm)
      exact htA_ne (congrArg Subtype.val h4)
    · exact h
  have hsq_r : (eB.symm (DihedralGroup.r 1)) ^ 2 = (⟨(tA' : K), htA_mem⟩ : ↥B) := by
    apply eB.injective
    rw [map_pow, MulEquiv.apply_symm_apply, shape5_d8_sq_r, hetB2]
  have hsq_s : (eB.symm (DihedralGroup.sr 0)) ^ 2 = 1 := by
    apply eB.injective
    rw [map_pow, MulEquiv.apply_symm_apply, shape5_d8_sq_s, map_one]
  have hne_s : eB.symm (DihedralGroup.sr 0) ≠ 1 := by
    intro h
    apply shape5_d8_sr0_ne
    have h' := congrArg eB h
    rwa [map_one, MulEquiv.apply_symm_apply] at h'
  have hrel_B : eB.symm (DihedralGroup.r 1) * eB.symm (DihedralGroup.sr 0) *
      (eB.symm (DihedralGroup.r 1))⁻¹ =
        (⟨(tA' : K), htA_mem⟩ : ↥B) * eB.symm (DihedralGroup.sr 0) := by
    apply eB.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hetB2]
    exact shape5_d8_rel
  have hsq_i : (eA.symm (QuaternionGroup.a 1)) ^ 2 = tA' := by
    apply eA.injective
    rw [map_pow, MulEquiv.apply_symm_apply, shape5_q8_sq_i, hetA]
  have hsq_j : (eA.symm (QuaternionGroup.xa 0)) ^ 2 = tA' := by
    apply eA.injective
    rw [map_pow, MulEquiv.apply_symm_apply, shape5_q8_sq_j, hetA]
  have hrel_A : eA.symm (QuaternionGroup.xa 0) * eA.symm (QuaternionGroup.a 1) *
      (eA.symm (QuaternionGroup.xa 0))⁻¹ = tA' * eA.symm (QuaternionGroup.a 1) := by
    apply eA.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hetA]
    exact shape5_q8_mul_rel
  have hi_sq : (eA.symm (QuaternionGroup.a 1) : K) ^ 2 = (tA' : K) := congrArg Subtype.val hsq_i
  have hj_sq : (eA.symm (QuaternionGroup.xa 0) : K) ^ 2 = (tA' : K) :=
    congrArg Subtype.val hsq_j
  have hji : (eA.symm (QuaternionGroup.xa 0) : K) * (eA.symm (QuaternionGroup.a 1) : K) *
      (eA.symm (QuaternionGroup.xa 0) : K)⁻¹ =
        (tA' : K) * (eA.symm (QuaternionGroup.a 1) : K) :=
    congrArg Subtype.val hrel_A
  have hr_sq : (eB.symm (DihedralGroup.r 1) : K) ^ 2 = (tA' : K) :=
    congrArg Subtype.val hsq_r
  have hs_sq : (eB.symm (DihedralGroup.sr 0) : K) ^ 2 = 1 := congrArg Subtype.val hsq_s
  have hs_ne : (eB.symm (DihedralGroup.sr 0) : K) ≠ 1 := fun h => hne_s (Subtype.ext h)
  have hrs : (eB.symm (DihedralGroup.r 1) : K) * (eB.symm (DihedralGroup.sr 0) : K) *
      (eB.symm (DihedralGroup.r 1) : K)⁻¹ =
        (tA' : K) * (eB.symm (DihedralGroup.sr 0) : K) :=
    congrArg Subtype.val hrel_B
  have hA8 : Nat.card ↥A = 8 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hB8 : Nat.card ↥B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hcardR : Nat.card ↥(A ⊔ B : Subgroup K) = 32 := by
    have h := shape5_card_sup_mul_inf hAB
    rw [hcard, hA8, hB8] at h
    omega
  have hmemZ : ∀ x : K, (x = 1 ∨ x = (tA' : K)) → x ∈ zpowers (tA' : K) := by
    rintro x (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  have hZA : ∀ x : K, x ∈ A → (∀ a' ∈ A, x * a' = a' * x) → x = 1 ∨ x = (tA' : K) := by
    intro x hx hxc
    have hcen : ∀ y : QuaternionGroup 2, eA ⟨x, hx⟩ * y = y * eA ⟨x, hx⟩ := by
      intro y
      have h2 : (⟨x, hx⟩ : ↥A) * eA.symm y = eA.symm y * ⟨x, hx⟩ :=
        Subtype.ext (hxc _ (eA.symm y).2)
      have h3 := congrArg eA h2
      simp only [map_mul, MulEquiv.apply_symm_apply] at h3
      exact h3
    rcases shape5_q8_central _ hcen with h | h
    · left
      have h4 : (⟨x, hx⟩ : ↥A) = 1 := eA.injective (h.trans (map_one eA).symm)
      exact congrArg Subtype.val h4
    · right
      have h4 : (⟨x, hx⟩ : ↥A) = tA' := eA.injective (h.trans hetA.symm)
      exact congrArg Subtype.val h4
  have hZB : ∀ x : K, x ∈ B → (∀ b' ∈ B, x * b' = b' * x) → x = 1 ∨ x = (tA' : K) := by
    intro x hx hxc
    have hcen : ∀ y : DihedralGroup 4, eB ⟨x, hx⟩ * y = y * eB ⟨x, hx⟩ := by
      intro y
      have h2 : (⟨x, hx⟩ : ↥B) * eB.symm y = eB.symm y * ⟨x, hx⟩ :=
        Subtype.ext (hxc _ (eB.symm y).2)
      have h3 := congrArg eB h2
      simp only [map_mul, MulEquiv.apply_symm_apply] at h3
      exact h3
    rcases shape5_d8_central _ hcen with h | h
    · left
      have h4 : (⟨x, hx⟩ : ↥B) = 1 := eB.injective (h.trans (map_one eB).symm)
      exact congrArg Subtype.val h4
    · right
      have h4 : (⟨x, hx⟩ : ↥B) = ⟨(tA' : K), htA_mem⟩ := eB.injective (h.trans hetB2.symm)
      exact congrArg Subtype.val h4
  have hsqA : ∀ x : K, x ∈ A → x ^ 2 = 1 ∨ x ^ 2 = (tA' : K) := by
    intro x hx
    rcases shape5_q8_sq (eA ⟨x, hx⟩) with h | h
    · left
      have h4 : (⟨x, hx⟩ : ↥A) ^ 2 = 1 := eA.injective (by rw [map_pow, map_one]; exact h)
      exact congrArg Subtype.val h4
    · right
      have h4 : (⟨x, hx⟩ : ↥A) ^ 2 = tA' := eA.injective (by rw [map_pow, hetA]; exact h)
      exact congrArg Subtype.val h4
  have hsqB : ∀ x : K, x ∈ B → x ^ 2 = 1 ∨ x ^ 2 = (tA' : K) := by
    intro x hx
    rcases shape5_d8_sq (eB ⟨x, hx⟩) with h | h
    · left
      have h4 : (⟨x, hx⟩ : ↥B) ^ 2 = 1 := eB.injective (by rw [map_pow, map_one]; exact h)
      exact congrArg Subtype.val h4
    · right
      have h4 : (⟨x, hx⟩ : ↥B) ^ 2 = ⟨(tA' : K), htA_mem⟩ :=
        eB.injective (by rw [map_pow, hetB2]; exact h)
      exact congrArg Subtype.val h4
  have hcomA : ∀ u ∈ A, ∀ v ∈ A, ⁅u, v⁆ = 1 ∨ ⁅u, v⁆ = (tA' : K) := by
    intro u hu v hv
    rcases shape5_q8_comm (eA ⟨u, hu⟩) (eA ⟨v, hv⟩) with h | h
    · left
      have h4 : ⁅(⟨u, hu⟩ : ↥A), (⟨v, hv⟩ : ↥A)⁆ = 1 :=
        eA.injective (by rw [map_commutatorElement, map_one]; exact h)
      exact congrArg Subtype.val h4
    · right
      have h4 : ⁅(⟨u, hu⟩ : ↥A), (⟨v, hv⟩ : ↥A)⁆ = tA' :=
        eA.injective (by rw [map_commutatorElement, hetA]; exact h)
      exact congrArg Subtype.val h4
  have hcomB : ∀ u ∈ B, ∀ v ∈ B, ⁅u, v⁆ = 1 ∨ ⁅u, v⁆ = (tA' : K) := by
    intro u hu v hv
    rcases shape5_d8_comm (eB ⟨u, hu⟩) (eB ⟨v, hv⟩) with h | h
    · left
      have h4 : ⁅(⟨u, hu⟩ : ↥B), (⟨v, hv⟩ : ↥B)⁆ = 1 :=
        eB.injective (by rw [map_commutatorElement, map_one]; exact h)
      exact congrArg Subtype.val h4
    · right
      have h4 : ⁅(⟨u, hu⟩ : ↥B), (⟨v, hv⟩ : ↥B)⁆ = (⟨(tA' : K), htA_mem⟩ : ↥B) :=
        eB.injective (by rw [map_commutatorElement, hetB2]; exact h)
      exact congrArg Subtype.val h4
  have hcenter : ∀ y ∈ A ⊔ B, (∀ r ∈ A ⊔ B, y * r = r * y) → y ∈ zpowers (tA' : K) := by
    intro y hy hcen
    obtain ⟨a, ha, b, hb, rfl⟩ := shape5_sup_decomp hAB hy
    have hca : ∀ a' ∈ A, a * a' = a' * a := by
      intro a' ha'
      have h1 : a * b * a' = a' * (a * b) := hcen a' ((le_sup_left : A ≤ A ⊔ B) ha')
      have h2 : a' * b = b * a' := hAB a' ha' b hb
      have h3 : a * a' * b = a' * a * b := by
        calc a * a' * b = a * (a' * b) := by rw [mul_assoc]
          _ = a * (b * a') := by rw [h2]
          _ = a * b * a' := by rw [mul_assoc]
          _ = a' * (a * b) := h1
          _ = a' * a * b := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hcb : ∀ b' ∈ B, b * b' = b' * b := by
      intro b' hb'
      have h1 : a * b * b' = b' * (a * b) := hcen b' ((le_sup_right : B ≤ A ⊔ B) hb')
      have h2 : a * b' = b' * a := hAB a ha b' hb'
      have h3 : a * (b * b') = a * (b' * b) := by
        calc a * (b * b') = a * b * b' := by rw [mul_assoc]
          _ = b' * (a * b) := h1
          _ = b' * a * b := by rw [mul_assoc]
          _ = a * b' * b := by rw [h2]
          _ = a * (b' * b) := by rw [mul_assoc]
      exact mul_left_cancel h3
    exact Subgroup.mul_mem _ (hmemZ _ (hZA a ha hca)) (hmemZ _ (hZB b hb hcb))
  have hsq : ∀ r ∈ A ⊔ B, r ^ 2 ∈ zpowers (tA' : K) := by
    intro r hr
    obtain ⟨a, ha, b, hb, rfl⟩ := shape5_sup_decomp hAB hr
    rw [(show Commute a b from hAB a ha b hb).mul_pow]
    exact Subgroup.mul_mem _ (hmemZ _ (hsqA a ha)) (hmemZ _ (hsqB b hb))
  have hcomm : ∀ r ∈ A ⊔ B, ∀ s ∈ A ⊔ B, ⁅r, s⁆ ∈ zpowers (tA' : K) := by
    intro r hr s hs
    obtain ⟨a1, ha1, b1, hb1, rfl⟩ := shape5_sup_decomp hAB hr
    obtain ⟨a2, ha2, b2, hb2, rfl⟩ := shape5_sup_decomp hAB hs
    rw [shape5_comm_decomp hAB ha1 ha2 hb1 hb2]
    exact Subgroup.mul_mem _ (hmemZ _ (hcomA a1 ha1 a2 ha2)) (hmemZ _ (hcomB b1 hb1 b2 hb2))
  have hcent : A ⊔ B ≤ Subgroup.centralizer ({(tA' : K)} : Set K) := by
    apply sup_le
    · intro a ha
      exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact htA_cent_A a ha)
    · intro b hb
      exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact htA_cent_B b hb)
  have ht_comm : ∀ r ∈ A ⊔ B, r * (tA' : K) = (tA' : K) * r := by
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (hcent hr) _ (Set.mem_singleton _)).symm
  have hshape : RShape 5 4 (A ⊔ B : Subgroup K) (tA' : K) :=
    { pd := Or.inr ⟨rfl, rfl⟩
      card := hcardR.trans (by norm_num)
      t_mem := (le_sup_left : A ≤ A ⊔ B) htA_A
      t_sq := htA_sq
      t_ne := htA_ne
      t_comm := ht_comm
      center_le := hcenter
      sq_mem := hsq
      comm_mem := hcomm
      sqrt := ⟨(eA.symm (QuaternionGroup.a 1) : K),
        (le_sup_left : A ≤ A ⊔ B) (eA.symm (QuaternionGroup.a 1)).2, hi_sq⟩ }
  exact ⟨(eA.symm (QuaternionGroup.a 1) : K), (eA.symm (QuaternionGroup.xa 0) : K),
    (eB.symm (DihedralGroup.r 1) : K), (eB.symm (DihedralGroup.sr 0) : K), (tA' : K), hshape,
    (eA.symm (QuaternionGroup.a 1)).2, (eA.symm (QuaternionGroup.xa 0)).2,
    (eB.symm (DihedralGroup.r 1)).2, (eB.symm (DihedralGroup.sr 0)).2,
    hi_sq, hj_sq, hji, hr_sq, hs_sq, hs_ne, hrs⟩
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
