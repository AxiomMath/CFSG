module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630AutQ8D8Center

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.AutQ8D8

variable {Γ : Type} [Group Γ]

structure Q8D8Facts (S : Subgroup Γ) (z : Γ) : Prop where
  z_mem : z ∈ S
  z_ne_one : z ≠ 1
  z_mul_self : z * z = 1
  card_eq : Nat.card S = 32
  center_iff : ∀ s ∈ S, (∀ s' ∈ S, s * s' = s' * s) ↔ (s = 1 ∨ s = z)
  comm_mem : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ = 1 ∨ s * s' * s⁻¹ * s'⁻¹ = z
  sq_mem : ∀ s ∈ S, s * s = 1 ∨ s * s = z

structure Q8D8Gens (S : Subgroup Γ) (z i j r t : Γ) : Prop where
  i_mem : i ∈ S
  j_mem : j ∈ S
  r_mem : r ∈ S
  t_mem : t ∈ S
  ii : i * i = z
  jj : j * j = z
  rr : r * r = z
  tt : t * t = 1
  ij : i * j = z * (j * i)
  tr : t * r = z * (r * t)
  ir : i * r = r * i
  it : i * t = t * i
  jr : j * r = r * j
  jt : j * t = t * j

theorem exists_mul_of_comm' {A B S : Subgroup Γ} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hsup : A ⊔ B = S) {s : Γ} (hs : s ∈ S) : ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
  let M : Subgroup Γ :=
    { carrier := {r | ∃ a ∈ A, ∃ b ∈ B, r = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by simp only [mul_assoc]
          _ = a₁ * (a₂ * b₁) * b₂ := by rw [hcomm a₂ ha₂ b₁ hb₁]
          _ = a₁ * a₂ * (b₁ * b₂) := by simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)).symm }
  have hM : A ⊔ B ≤ M := by
    refine sup_le ?_ ?_
    · intro a ha
      exact ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩
    · intro b hb
      exact ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩
  obtain ⟨a, ha, b, hb, h⟩ := hM (hsup ▸ hs)
  exact ⟨a, ha, b, hb, h⟩

theorem quaternion_comm_aux :
    ∀ x y : QuaternionGroup 2, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = QuaternionGroup.a 2 := by
  decide

theorem quaternion_sq_aux :
    ∀ x : QuaternionGroup 2, x * x = 1 ∨ x * x = QuaternionGroup.a 2 := by
  decide

theorem dihedral_comm_aux :
    ∀ x y : DihedralGroup 4, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = DihedralGroup.r 2 := by
  decide

theorem dihedral_sq_aux :
    ∀ x : DihedralGroup 4, x * x = 1 ∨ x * x = DihedralGroup.r 2 := by
  decide

theorem q8d8_exists {S : Subgroup Γ} (h : CFSG.LocalAnalysis.RankThreeTheoremC.smallRankIsQ8D8 S) :
    ∃ z i j r t : Γ, Q8D8Facts S z ∧ Q8D8Gens S z i j r t := by
  obtain ⟨A, B, ⟨eA⟩, ⟨eB⟩, hcomm, hsup, hAB⟩ := h
  have hAS : A ≤ S := hsup ▸ le_sup_left
  have hBS : B ≤ S := hsup ▸ le_sup_right
  obtain ⟨c, hc1⟩ := exists_ne_one_of_natCard_eq_two hAB
  have hzA : (c : Γ) ∈ A := (Subgroup.mem_inf.mp c.2).1
  have hzB : (c : Γ) ∈ B := (Subgroup.mem_inf.mp c.2).2
  have hz1 : (c : Γ) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hzz : (c : Γ) * c = 1 := by
    have h1 : c ^ 2 = 1 := by
      have := pow_card_eq_one' (x := c)
      rwa [hAB] at this
    have h2 : c * c = 1 := by rwa [sq] at h1
    exact congrArg Subtype.val h2
  set z : Γ := (c : Γ) with hzdef
  let zA : ↥A := ⟨z, hzA⟩
  let zB : ↥B := ⟨z, hzB⟩
  have hzA_cen : ∀ y : ↥A, y * zA = zA * y := fun y => Subtype.ext (hcomm y y.2 z hzB)
  have hzB_cen : ∀ y : ↥B, y * zB = zB * y := fun y => Subtype.ext (hcomm z hzA y y.2).symm
  have hzA1 : zA ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzB1 : zB ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have heA : eA zA = QuaternionGroup.a 2 := by
    rcases quaternion_central_eq (eA zA) (central_transfer eA zA hzA_cen) with h | h
    · exact absurd (eA.injective (h.trans (map_one eA).symm)) hzA1
    · exact h
  have heB : eB zB = DihedralGroup.r 2 := by
    rcases dihedral_central_eq (eB zB) (central_transfer eB zB hzB_cen) with h | h
    · exact absurd (eB.injective (h.trans (map_one eB).symm)) hzB1
    · exact h
  have heA' : eA.symm (QuaternionGroup.a 2) = zA := by rw [← heA]; exact eA.symm_apply_apply zA
  have heB' : eB.symm (DihedralGroup.r 2) = zB := by rw [← heB]; exact eB.symm_apply_apply zB
  have mulA : ∀ x y : QuaternionGroup 2, eA.symm x * eA.symm y = eA.symm (x * y) :=
    fun x y => (map_mul eA.symm x y).symm
  have mulB : ∀ x y : DihedralGroup 4, eB.symm x * eB.symm y = eB.symm (x * y) :=
    fun x y => (map_mul eB.symm x y).symm
  let i : ↥A := eA.symm (QuaternionGroup.a 1)
  let j : ↥A := eA.symm (QuaternionGroup.xa 0)
  let r : ↥B := eB.symm (DihedralGroup.r 1)
  let t : ↥B := eB.symm (DihedralGroup.sr 0)
  have hii : i * i = zA := by
    show eA.symm (QuaternionGroup.a 1) * eA.symm (QuaternionGroup.a 1) = zA
    rw [mulA, ← heA']
    congr 1
  have hjj : j * j = zA := by
    show eA.symm (QuaternionGroup.xa 0) * eA.symm (QuaternionGroup.xa 0) = zA
    rw [mulA, ← heA']
    congr 1
  have hrr : r * r = zB := by
    show eB.symm (DihedralGroup.r 1) * eB.symm (DihedralGroup.r 1) = zB
    rw [mulB, ← heB']
    congr 1
  have htt : t * t = 1 := by
    show eB.symm (DihedralGroup.sr 0) * eB.symm (DihedralGroup.sr 0) = 1
    rw [mulB]
    have : (DihedralGroup.sr 0 * DihedralGroup.sr 0 : DihedralGroup 4) = 1 := by decide
    rw [this, map_one]
  have hij : i * j = zA * (j * i) := by
    show eA.symm (QuaternionGroup.a 1) * eA.symm (QuaternionGroup.xa 0) =
      zA * (eA.symm (QuaternionGroup.xa 0) * eA.symm (QuaternionGroup.a 1))
    rw [← heA']
    simp only [mulA]
    congr 1
  have htr : t * r = zB * (r * t) := by
    show eB.symm (DihedralGroup.sr 0) * eB.symm (DihedralGroup.r 1) =
      zB * (eB.symm (DihedralGroup.r 1) * eB.symm (DihedralGroup.sr 0))
    rw [← heB']
    simp only [mulB]
    congr 1
  let Φ : ↥A × ↥B →* Γ := MonoidHom.noncommCoprod A.subtype B.subtype
    (fun a b => hcomm a a.2 b b.2)
  have hΦ : ∀ p : ↥A × ↥B, Φ p = (p.1 : Γ) * (p.2 : Γ) := fun p => rfl
  have hdec : ∀ s ∈ S, ∃ p : ↥A × ↥B, Φ p = s := by
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_comm' hcomm hsup hs
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hzs : ∀ g g' : Γ, (g = 1 ∨ g = z) → (g' = 1 ∨ g' = z) → (g * g' = 1 ∨ g * g' = z) := by
    intro g g' hg hg'
    rcases hg with rfl | rfl <;> rcases hg' with rfl | rfl
    · left; simp
    · right; simp
    · right; simp
    · left; exact hzz
  have hAcomm : ∀ a a' : ↥A, ((a * a' * a⁻¹ * a'⁻¹ : ↥A) : Γ) = 1 ∨
      ((a * a' * a⁻¹ * a'⁻¹ : ↥A) : Γ) = z := by
    intro a a'
    rcases quaternion_comm_aux (eA a) (eA a') with h | h
    · left
      have : a * a' * a⁻¹ * a'⁻¹ = 1 := by
        apply eA.injective
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_one]
        exact h
      rw [this]; rfl
    · right
      have : a * a' * a⁻¹ * a'⁻¹ = zA := by
        apply eA.injective
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, heA]
        exact h
      rw [this]
  have hBcomm : ∀ b b' : ↥B, ((b * b' * b⁻¹ * b'⁻¹ : ↥B) : Γ) = 1 ∨
      ((b * b' * b⁻¹ * b'⁻¹ : ↥B) : Γ) = z := by
    intro b b'
    rcases dihedral_comm_aux (eB b) (eB b') with h | h
    · left
      have : b * b' * b⁻¹ * b'⁻¹ = 1 := by
        apply eB.injective
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_one]
        exact h
      rw [this]; rfl
    · right
      have : b * b' * b⁻¹ * b'⁻¹ = zB := by
        apply eB.injective
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, heB]
        exact h
      rw [this]
  have hAsq : ∀ a : ↥A, ((a * a : ↥A) : Γ) = 1 ∨ ((a * a : ↥A) : Γ) = z := by
    intro a
    rcases quaternion_sq_aux (eA a) with h | h
    · left
      have : a * a = 1 := by
        apply eA.injective
        rw [map_mul, map_one]
        exact h
      rw [this]; rfl
    · right
      have : a * a = zA := by
        apply eA.injective
        rw [map_mul, heA]
        exact h
      rw [this]
  have hBsq : ∀ b : ↥B, ((b * b : ↥B) : Γ) = 1 ∨ ((b * b : ↥B) : Γ) = z := by
    intro b
    rcases dihedral_sq_aux (eB b) with h | h
    · left
      have : b * b = 1 := by
        apply eB.injective
        rw [map_mul, map_one]
        exact h
      rw [this]; rfl
    · right
      have : b * b = zB := by
        apply eB.injective
        rw [map_mul, heB]
        exact h
      rw [this]
  have hcard : Nat.card S = 32 := by
    let φ : (↥A × ↥B) →* ↥S := Φ.codRestrict S (fun p => by
      rw [hΦ]; exact S.mul_mem (hAS p.1.2) (hBS p.2.2))
    have hsurj : Function.Surjective φ := by
      intro s
      obtain ⟨p, hp⟩ := hdec s s.2
      exact ⟨p, Subtype.ext hp⟩
    have hker : Nat.card φ.ker = 2 := by
      let e : φ.ker ≃ (A ⊓ B : Subgroup Γ) :=
        { toFun := fun p => ⟨(p.1.1 : Γ), Subgroup.mem_inf.mpr
            ⟨p.1.1.2, mem_of_mul_eq_one p.1.2.2 (congrArg Subtype.val (MonoidHom.mem_ker.mp p.2))⟩⟩
          invFun := fun a => ⟨(⟨a.1, (Subgroup.mem_inf.mp a.2).1⟩,
            ⟨a.1⁻¹, B.inv_mem (Subgroup.mem_inf.mp a.2).2⟩),
            MonoidHom.mem_ker.mpr (Subtype.ext (mul_inv_cancel a.1))⟩
          left_inv := by
            rintro ⟨⟨a, b⟩, hh⟩
            have h' : (a : Γ) * (b : Γ) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hh)
            apply Subtype.ext
            apply Prod.ext
            · rfl
            · apply Subtype.ext
              exact (eq_inv_of_mul_eq_one_right h').symm
          right_inv := fun a => rfl }
      exact (Nat.card_congr e).trans hAB
    have hA8 : Nat.card ↥A = 8 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      all_goals norm_num
    have hB8 : Nat.card ↥B = 8 := by
      rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
      all_goals norm_num
    have hprod : Nat.card (↥A × ↥B) = 64 := by
      rw [Nat.card_prod, hA8, hB8]
    have hquot : Nat.card ((↥A × ↥B) ⧸ φ.ker) = Nat.card ↥S :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [hprod, hquot, hker] at hsplit
    omega
  have hcen : ∀ s ∈ S, (∀ s' ∈ S, s * s' = s' * s) ↔ (s = 1 ∨ s = z) := by
    intro s hs
    constructor
    · intro hcs
      obtain ⟨⟨a, b⟩, hp⟩ := hdec s hs
      have hs' : s = (a : Γ) * (b : Γ) := hp.symm
      subst hs'
      have haC : ∀ a' : ↥A, a' * a = a * a' := by
        intro a'
        apply Subtype.ext
        have h1 := hcs a' (hAS a'.2)
        show (a' : Γ) * a = a * a'
        have h2 : (a : Γ) * a' * b = a' * a * b := by
          calc (a : Γ) * a' * b = a * (a' * b) := by rw [mul_assoc]
            _ = a * (b * a') := by rw [hcomm a' a'.2 b b.2]
            _ = a * b * a' := by rw [mul_assoc]
            _ = a' * (a * b) := h1
            _ = a' * a * b := by rw [mul_assoc]
        exact (mul_right_cancel h2).symm
      have hbC : ∀ b' : ↥B, b' * b = b * b' := by
        intro b'
        apply Subtype.ext
        have h1 := hcs b' (hBS b'.2)
        show (b' : Γ) * b = b * b'
        have h2 : (a : Γ) * (b * b') = a * (b' * b) := by
          calc (a : Γ) * (b * b') = a * b * b' := by rw [mul_assoc]
            _ = b' * (a * b) := h1
            _ = b' * a * b := by rw [mul_assoc]
            _ = a * b' * b := by rw [← hcomm a a.2 b' b'.2]
            _ = a * (b' * b) := by rw [mul_assoc]
        exact (mul_left_cancel h2).symm
      have hAc : ∀ q : QuaternionGroup 2, q * eA a = eA a * q := by
        intro q
        obtain ⟨y, rfl⟩ := eA.surjective q
        rw [← map_mul, ← map_mul, haC y]
      have hBc : ∀ q : DihedralGroup 4, q * eB b = eB b * q := by
        intro q
        obtain ⟨y, rfl⟩ := eB.surjective q
        rw [← map_mul, ← map_mul, hbC y]
      have ha' : (a : Γ) = 1 ∨ (a : Γ) = z := by
        rcases quaternion_central_eq (eA a) hAc with h | h
        · left
          have := eA.injective (h.trans (map_one eA).symm)
          rw [this]; rfl
        · right
          have := eA.injective (h.trans heA.symm)
          rw [this]
      have hb' : (b : Γ) = 1 ∨ (b : Γ) = z := by
        rcases dihedral_central_eq (eB b) hBc with h | h
        · left
          have := eB.injective (h.trans (map_one eB).symm)
          rw [this]; rfl
        · right
          have := eB.injective (h.trans heB.symm)
          rw [this]
      exact hzs _ _ ha' hb'
    · rintro (rfl | rfl) s' hs'
      · simp
      · obtain ⟨⟨a', b'⟩, hp⟩ := hdec s' hs'
        have hs'' : s' = (a' : Γ) * (b' : Γ) := hp.symm
        subst hs''
        calc (c : Γ) * (a' * b') = (c * a') * b' := by rw [mul_assoc]
          _ = (a' * c) * b' := by rw [← hcomm a' a'.2 c hzB]
          _ = a' * (c * b') := by rw [mul_assoc]
          _ = a' * (b' * c) := by rw [hcomm c hzA b' b'.2]
          _ = (a' * b') * c := by rw [mul_assoc]
  have hcomm_mem : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ = 1 ∨ s * s' * s⁻¹ * s'⁻¹ = z := by
    intro s hs s' hs'
    obtain ⟨p, hp⟩ := hdec s hs
    obtain ⟨p', hp'⟩ := hdec s' hs'
    have h1 : s * s' * s⁻¹ * s'⁻¹ = Φ (p * p' * p⁻¹ * p'⁻¹) := by
      rw [← hp, ← hp']
      simp only [map_mul, map_inv]
    rw [h1]
    have e : p * p' * p⁻¹ * p'⁻¹ =
        (p.1 * p'.1 * p.1⁻¹ * p'.1⁻¹, p.2 * p'.2 * p.2⁻¹ * p'.2⁻¹) := rfl
    rw [e, hΦ]
    exact hzs _ _ (hAcomm p.1 p'.1) (hBcomm p.2 p'.2)
  have hsq_mem : ∀ s ∈ S, s * s = 1 ∨ s * s = z := by
    intro s hs
    obtain ⟨p, hp⟩ := hdec s hs
    have h1 : s * s = Φ (p * p) := by
      rw [← hp]
      simp only [map_mul]
    rw [h1]
    have e : p * p = (p.1 * p.1, p.2 * p.2) := rfl
    rw [e, hΦ]
    exact hzs _ _ (hAsq p.1) (hBsq p.2)
  refine ⟨z, (i : Γ), (j : Γ), (r : Γ), (t : Γ),
    ⟨hAS hzA, hz1, hzz, hcard, hcen, hcomm_mem, hsq_mem⟩, ?_⟩
  exact ⟨hAS i.2, hAS j.2, hBS r.2, hBS t.2, congrArg Subtype.val hii,
    congrArg Subtype.val hjj, congrArg Subtype.val hrr, congrArg Subtype.val htt,
    congrArg Subtype.val hij, congrArg Subtype.val htr,
    hcomm i i.2 r r.2, hcomm i i.2 t t.2, hcomm j j.2 r r.2, hcomm j j.2 t t.2⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
