module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.MStructB
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7.MS

variable {G : Type} [Group G]

section Letters

theorem letters_rel {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} (hlets : HLetters H H₁ H₂ e)
    {w : List (Fin 6 × Bool)} (hw : w ∈ g23WordsH) : FreeGroup.lift e (FreeGroup.mk w) = 1 :=
  hlets.rels w hw

theorem letters_pow3 {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} (hlets : HLetters H H₁ H₂ e)
    {i : Fin 6} (hi : (i = 0 ∨ i = 2)) : e i * e i * e i = 1 := by
  rcases hi with rfl | rfl
  · have := letters_rel hlets (w := [(0, true), (0, true), (0, true)]) (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := letters_rel hlets (w := [(2, true), (2, true), (2, true)]) (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this

theorem letters_sq4 {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} (hlets : HLetters H H₁ H₂ e) :
    e 4 * e 4 = 1 := by
  have := letters_rel hlets (w := [(4, true), (4, true)]) (by simp [g23WordsH])
  simpa [FreeGroup.lift_mk, mul_assoc] using this

end Letters


theorem closure_pair_gen {a b : G} (hab : Commute a b) :
    ∀ p ∈ Subgroup.closure ({a, b} : Set G), ∃ i j : ℤ, a ^ i * b ^ j = p := by
  intro p hp
  induction hp using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    refine ⟨i + k, j + l, ?_⟩
    have hc : Commute (b ^ j) (a ^ k) := ((hab.symm).zpow_left j).zpow_right k
    symm
    calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by group
      _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [hc.eq]
      _ = a ^ (i + k) * b ^ (j + l) := by rw [zpow_add, zpow_add]; group
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨-i, -j, ?_⟩
    symm
    calc (a ^ i * b ^ j)⁻¹ = (b ^ j)⁻¹ * (a ^ i)⁻¹ := by group
      _ = b ^ (-j) * a ^ (-i) := by rw [zpow_neg, zpow_neg]
      _ = a ^ (-i) * b ^ (-j) := ((hab.zpow_left (-i)).zpow_right (-j)).symm.eq

section Letters2

open CFSG.Quasithin.G23Type

variable {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}

theorem letters_mem_H₁ (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e) :
    e 0 ∈ H₁ ∧ e 1 ∈ H₁ := by
  have h0 : e 0 ∈ Subgroup.closure ({e 0, e 1} : Set G) := Subgroup.subset_closure (by simp)
  have h1 : e 1 ∈ Subgroup.closure ({e 0, e 1} : Set G) := Subgroup.subset_closure (by simp)
  rw [hlets.gen₁] at h0 h1
  exact ⟨h0, h1⟩

theorem letters_mem_H₂ (hlets : HLetters H H₁ H₂ e) : e 2 ∈ H₂ ∧ e 3 ∈ H₂ := by
  have h0 : e 2 ∈ Subgroup.closure ({e 2, e 3} : Set G) := Subgroup.subset_closure (by simp)
  have h1 : e 3 ∈ Subgroup.closure ({e 2, e 3} : Set G) := Subgroup.subset_closure (by simp)
  rw [hlets.gen₂] at h0 h1
  exact ⟨h0, h1⟩

theorem letters_mem_H (hlets : HLetters H H₁ H₂ e) : e 4 ∈ H := by
  have : e 4 ∈ Subgroup.closure (Set.range fun i : Fin 5 => e i.castSucc) := by
    apply Subgroup.subset_closure
    exact ⟨4, rfl⟩
  rwa [hlets.gen] at this

theorem letters_t_not_mem (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e) :
    e 4 ∉ H₁ ⊔ H₂ := by
  intro ht
  obtain ⟨h0, h1⟩ := letters_mem_H₁ hone hlets
  obtain ⟨h2, h3⟩ := letters_mem_H₂ hlets
  have hle : H ≤ H₁ ⊔ H₂ := by
    rw [← hlets.gen]
    apply Subgroup.closure_le _ |>.mpr
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact Subgroup.mem_sup_left h0
    · exact Subgroup.mem_sup_left h1
    · exact Subgroup.mem_sup_right h2
    · exact Subgroup.mem_sup_right h3
    · exact ht
  have h1' : (H₁ ⊔ H₂).relIndex H = 1 := Subgroup.relIndex_eq_one.mpr hle
  rw [hone.index] at h1'
  norm_num at h1'

end Letters2


section Letters3

open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23

variable {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}

theorem pow3_of_mul3 {x : G} (h : x * x * x = 1) : x ^ 3 = 1 := by
  rw [pow_three, ← mul_assoc]; exact h

theorem letters_comm02 (hF : HFacts H H₁ H₂ e) : e 0 * e 2 = e 2 * e 0 := by
  have h0 : e 0 ∈ Psub e := Subgroup.subset_closure (by simp [Psub])
  have h2 : e 2 ∈ Psub e := Subgroup.subset_closure (by simp [Psub])
  have := hF.elem_P.1.is_comm.comm ⟨e 0, h0⟩ ⟨e 2, h2⟩
  exact congrArg Subtype.val this

theorem letters_P_gen (hF : HFacts H H₁ H₂ e) :
    ∀ p ∈ Psub e, ∃ i j : ℤ, e 0 ^ i * e 2 ^ j = p :=
  closure_pair_gen (show Commute (e 0) (e 2) from letters_comm02 hF)

theorem letters_ne1_0 [Finite G] (hlets : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e) :
    e 0 ≠ 1 := by
  intro h
  have hle : Psub e ≤ Subgroup.zpowers (e 2) := by
    apply Subgroup.closure_le _ |>.mpr
    intro x hx
    rcases hx with rfl | rfl
    · rw [h]; exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  have hcard := Subgroup.card_le_of_le hle
  rw [hF.card_P, Nat.card_zpowers] at hcard
  have h3 : orderOf (e 2) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (pow3_of_mul3 (letters_pow3 hlets (Or.inr rfl)))
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem letters_ne1_2 [Finite G] (hlets : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e) :
    e 2 ≠ 1 := by
  intro h
  have hle : Psub e ≤ Subgroup.zpowers (e 0) := by
    apply Subgroup.closure_le _ |>.mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_zpowers _
    · rw [h]; exact Subgroup.one_mem _
  have hcard := Subgroup.card_le_of_le hle
  rw [hF.card_P, Nat.card_zpowers] at hcard
  have h3 : orderOf (e 0) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (pow3_of_mul3 (letters_pow3 hlets (Or.inl rfl)))
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem t_inv_of_norm {σ : G} (σ3 : σ ^ 3 = 1) (σ1 : σ ≠ 1)
    (hnorm : e 4 ∈ Subgroup.normalizer (Subgroup.zpowers σ : Set G))
    (hnc : e 4 * σ ≠ σ * e 4) : e 4 * σ * (e 4)⁻¹ = σ⁻¹ := by
  have hx : e 4 * σ * (e 4)⁻¹ ∈ Subgroup.zpowers σ :=
    (Subgroup.mem_normalizer_iff.mp hnorm σ).mp (Subgroup.mem_zpowers σ)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases zpow3_cases σ3 σ1 k with h0 | h1 | h2
  · exfalso
    apply σ1
    have h1' : e 4 * σ * (e 4)⁻¹ = 1 := by rw [← hk, h0]
    calc σ = (e 4)⁻¹ * (e 4 * σ * (e 4)⁻¹) * e 4 := by group
      _ = 1 := by rw [h1']; group
  · exfalso
    apply hnc
    have h1' : e 4 * σ * (e 4)⁻¹ = σ := by rw [← hk, h1]
    calc e 4 * σ = (e 4 * σ * (e 4)⁻¹) * e 4 := by group
      _ = σ * e 4 := by rw [h1']
  · have h1' : e 4 * σ * (e 4)⁻¹ = σ⁻¹ := by rw [← hk, h2]
    exact h1'

theorem letters_t_inv_0 [Finite G] (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) : e 4 * e 0 * (e 4)⁻¹ = (e 0)⁻¹ := by
  have hσ3 : e 0 ^ 3 = 1 := pow3_of_mul3 (letters_pow3 hlets (Or.inl rfl))
  have hσ1 := letters_ne1_0 hlets hF
  have hnorm : e 4 ∈ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G) := by
    have hmem : e 4 ∈ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G) ⊓ H := by
      rw [hF.norm₁]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (e 4))
    exact (Subgroup.mem_inf.mp hmem).1
  have hK : Subgroup.zpowers (e 0) ⊔ H₂ ≤ H₁ ⊔ H₂ :=
    sup_le (le_sup_of_le_left ((Subgroup.zpowers_le).mpr (letters_mem_H₁ hone hlets).1))
      le_sup_right
  have hnc : e 4 * e 0 ≠ e 0 * e 4 := by
    intro heq
    have hcent : e 4 ∈ Subgroup.centralizer {e 0} ⊓ H := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, letters_mem_H hlets⟩
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact heq.symm
    rw [hF.cent₁] at hcent
    exact letters_t_not_mem hone hlets (hK hcent)
  exact t_inv_of_norm hσ3 hσ1 hnorm hnc

theorem letters_t_inv_2 [Finite G] (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) : e 4 * e 2 * (e 4)⁻¹ = (e 2)⁻¹ := by
  have hσ3 : e 2 ^ 3 = 1 := pow3_of_mul3 (letters_pow3 hlets (Or.inr rfl))
  have hσ1 := letters_ne1_2 hlets hF
  have hnorm : e 4 ∈ Subgroup.normalizer (Subgroup.zpowers (e 2) : Set G) := by
    have hmem : e 4 ∈ Subgroup.normalizer (Subgroup.zpowers (e 2) : Set G) ⊓ H := by
      rw [hF.norm₂]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (e 4))
    exact (Subgroup.mem_inf.mp hmem).1
  have hK : Subgroup.zpowers (e 2) ⊔ H₁ ≤ H₁ ⊔ H₂ :=
    sup_le (le_sup_of_le_right ((Subgroup.zpowers_le).mpr (letters_mem_H₂ hlets).1)) le_sup_left
  have hnc : e 4 * e 2 ≠ e 2 * e 4 := by
    intro heq
    have hcent : e 4 ∈ Subgroup.centralizer {e 2} ⊓ H := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, letters_mem_H hlets⟩
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact heq.symm
    rw [hF.cent₂] at hcent
    exact letters_t_not_mem hone hlets (hK hcent)
  exact t_inv_of_norm hσ3 hσ1 hnorm hnc

end Letters3


section ZFacts

open scoped MatrixGroups
open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23

variable {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}

theorem zOf_mem_inf (hF : HFacts H H₁ H₂ e) : zOf e ∈ H₁ ⊓ H₂ := by
  have h1 : zOf e ∈ Subgroup.centralizer {e 0} ⊓ H₁ := by
    rw [hF.centL₁]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have h2 : zOf e ∈ Subgroup.centralizer {e 2} ⊓ H₂ := by
    rw [hF.centL₂]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h1).2, (Subgroup.mem_inf.mp h2).2⟩

theorem card_sl2_three : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Matrix.card_SL_field 2]
  simp [ZMod.card, Fin.prod_univ_two]

theorem card_H₂_24 (hone : G23One H H₁ H₂) : Nat.card ↥H₂ = 24 := by
  obtain ⟨ψ⟩ := hone.iso_two
  rw [Nat.card_congr ψ.toEquiv, card_sl2_three]

theorem card_H₁_24 (hone : G23One H H₁ H₂) : Nat.card ↥H₁ = 24 := by
  obtain ⟨ψ⟩ := hone.iso_one
  rw [Nat.card_congr ψ.toEquiv, card_sl2_three]

theorem zOf_ne_one [Finite G] (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) : zOf e ≠ 1 := by
  intro hz
  obtain ⟨ψ⟩ := hone.iso_one
  let m1 : SL(2, ZMod 3) := ⟨-1, by decide +kernel⟩
  let u' : ↥H₁ := ψ.symm m1
  have hm1sq : m1 * m1 = 1 := by
    apply Subtype.ext
    show (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (-1) = 1
    decide +kernel
  have hm1ne : m1 ≠ 1 := fun h => by
    have : (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := congrArg Subtype.val h
    exact absurd this (by decide)
  have hm1c : ∀ A : SL(2, ZMod 3), A * m1 = m1 * A := by
    decide +kernel
  have hu'c : ∀ x : ↥H₁, x * u' = u' * x := by
    intro x
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hm1c _
  have hu'sq : u' * u' = 1 := by
    apply ψ.injective
    rw [map_mul, MulEquiv.apply_symm_apply, map_one]
    exact hm1sq
  have hu'ne : u' ≠ 1 := by
    intro h
    apply hm1ne
    have := congrArg ψ h
    rw [MulEquiv.apply_symm_apply, map_one] at this
    exact this
  have h0 : e 0 ∈ H₁ := (letters_mem_H₁ hone hlets).1
  have hcomm0 : (e 0) * (u' : G) = (u' : G) * e 0 :=
    congrArg Subtype.val (hu'c ⟨e 0, h0⟩)
  have hu_mem : (u' : G) ∈ Subgroup.centralizer {e 0} ⊓ H₁ := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, u'.2⟩
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact hcomm0
  rw [hF.centL₁, hz, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hu_mem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu_mem
  have hcube : (u' : G) ^ 3 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      pow3_of_mul3 (letters_pow3 hlets (Or.inl rfl)), one_zpow]
  have hsq : (u' : G) * (u' : G) = 1 := congrArg Subtype.val hu'sq
  apply hu'ne
  apply Subtype.ext
  exact eq_one_of_sq_cube hsq hcube

end ZFacts


section Common

open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23

variable {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}

theorem zOf_sq [Finite G] (hone : G23One H H₁ H₂) (hF : HFacts H H₁ H₂ e) :
    zOf e * zOf e = 1 := by
  have hpow := pow_card_eq_one' (G := ↥(H₁ ⊓ H₂)) (x := ⟨zOf e, zOf_mem_inf hF⟩)
  rw [hone.card_inf] at hpow
  have h2 : zOf e ^ 2 = 1 := congrArg Subtype.val hpow
  rwa [pow_two] at h2

theorem e4_ne_one (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e) : e 4 ≠ 1 := by
  intro h
  apply letters_t_not_mem hone hlets
  rw [h]
  exact (H₁ ⊔ H₂).one_mem

theorem e4_orderOf (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e) : orderOf (e 4) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]; exact letters_sq4 hlets
  · exact e4_ne_one hone hlets

theorem ct_fact [Finite G] (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e)
    (hO : OneClass e) : ∃ c : G, c * zOf e * c⁻¹ = e 4 :=
  isConj_iff.mp (hO (e 4) (e4_orderOf hone hlets))

theorem ctz_fact [Finite G] (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) (hO : OneClass e) : ∃ c : G, c * zOf e * c⁻¹ = e 4 * zOf e := by
  obtain ⟨g, -, hgeq⟩ := hF.conj_t₁
  have hsq : (e 4 * zOf e) * (e 4 * zOf e) = 1 := by
    rw [← hgeq]
    calc (g * e 4 * g⁻¹) * (g * e 4 * g⁻¹) = g * (e 4 * e 4) * g⁻¹ := by group
      _ = 1 := by rw [letters_sq4 hlets]; group
  have hne : e 4 * zOf e ≠ 1 := by
    intro h
    have hz : zOf e ∈ H₁ ⊓ H₂ := zOf_mem_inf hF
    have he4 : e 4 = (zOf e)⁻¹ := eq_inv_of_mul_eq_one_left h
    apply letters_t_not_mem hone hlets
    rw [he4]
    exact (H₁ ⊔ H₂).inv_mem ((le_sup_left : H₁ ≤ H₁ ⊔ H₂) (Subgroup.mem_inf.mp hz).1)
  have hord : orderOf (e 4 * zOf e) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  exact isConj_iff.mp (hO _ hord)

theorem P_comm_gen [Finite G] (hF : HFacts H H₁ H₂ e) :
    ∀ p ∈ Psub e, ∀ q ∈ Psub e, p * q = q * p :=
  fun p hp q hq => congrArg Subtype.val (hF.elem_P.1.is_comm.comm ⟨p, hp⟩ ⟨q, hq⟩)

theorem P_pow3_gen (hF : HFacts H H₁ H₂ e) : ∀ p ∈ Psub e, p ^ 3 = 1 := hF.elem_P.2

theorem e0_mem_P : e 0 ∈ Psub e := Subgroup.subset_closure (by simp [Psub])

theorem e2_mem_P : e 2 ∈ Psub e := Subgroup.subset_closure (by simp [Psub])

theorem Pgen_02 (hF : HFacts H H₁ H₂ e) : ∀ p ∈ Psub e, ∃ i j : ℤ, e 0 ^ i * e 2 ^ j = p :=
  letters_P_gen hF

theorem Pgen_20 (hF : HFacts H H₁ H₂ e) : ∀ p ∈ Psub e, ∃ i j : ℤ, e 2 ^ i * e 0 ^ j = p := by
  have hP : Psub e = Subgroup.closure ({e 2, e 0} : Set G) := by
    rw [Psub, Set.pair_comm]
  rw [hP]
  exact closure_pair_gen (show Commute (e 2) (e 0) from (letters_comm02 hF).symm)

theorem CP_fact [Finite G] {M₁ M₂ Pb Np Nm : Subgroup G}
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card ↥Pb = 81)
    (hlets : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e) (hone : G23One H H₁ H₂) :
    Nat.card ↥(Subgroup.centralizer (Psub e : Set G)) = 162 := by
  rw [card_of_centComplement hL.pb.compl, Nat.card_zpowers, hPb,
    orderOf_eq_prime (by rw [pow_two]; exact zOf_sq hone hF) (zOf_ne_one hone hlets hF)]

end Common


section Assembly

open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23

variable {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}

theorem zC_fact [Finite G] (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) : ∀ g : G, g * zOf e = zOf e * g → g ∈ H := by
  intro g hg
  have hz := zOf_mem_inf hF
  have hzle : Subgroup.zpowers (zOf e) ≤ H₁ ⊓ H₂ := (Subgroup.zpowers_le).mpr hz
  have heq : Subgroup.zpowers (zOf e) = H₁ ⊓ H₂ := by
    apply Subgroup.eq_of_le_of_card_ge hzle
    rw [hone.card_inf, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact zOf_sq hone hF)
      (zOf_ne_one hone hlets hF)]
  rw [hone.eq_centralizer, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [← heq] at hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact ((show Commute g (zOf e) from hg).zpow_right k).eq.symm

theorem zH_fact [Finite G] (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) : ∀ h ∈ H, h * zOf e = zOf e * h := by
  intro h hh
  have hC : h ∈ Subgroup.centralizer ((H₁ ⊓ H₂ : Subgroup G) : Set G) := by
    rw [← hone.eq_centralizer]; exact hh
  exact ((Subgroup.mem_centralizer_iff.mp hC) (zOf e) (zOf_mem_inf hF)).symm

theorem card_of_Cor {M₁ M₂ Pb Np Nm : Subgroup G} (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm)
    (hPb : Nat.card ↥Pb = 81) : Nat.card ↥M₁ = 243 ∧ Nat.card ↥M₂ = 243 := by
  rcases hL.cor.cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hPb] at h2; omega
  · rw [hPb] at h2; omega
  · have hM2 : Nat.card ↥M₂ = 243 := by rw [← hL.cor.card_eq]; exact h1
    exact ⟨h1, hM2⟩

theorem card_sq_81 {c : ℕ} (h : 243 = 3 * c ^ 2) : c = 9 := by
  have h2 : c ^ 2 = 81 := by omega
  have hc : c ≤ 9 := by nlinarith
  interval_cases c <;> omega

theorem vx_one [Finite G] (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) (hO : OneClass e) {M₁ M₂ Pb Np Nm : Subgroup G}
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card ↥Pb = 81) :
    VxData H (zOf e) (e 4) (e 0) (e 2) M₁ M₂ (Psub e) := by
  obtain ⟨hM1, hM2⟩ := card_of_Cor hL hPb
  refine
    { zz := zOf_sq hone hF
      zC := zC_fact hone hlets hF
      zH := zH_fact hone hlets hF
      tH := letters_mem_H hlets
      σH := hone.le_one (letters_mem_H₁ hone hlets).1
      τH := hone.le_two (letters_mem_H₂ hlets).1
      σ3 := pow3_of_mul3 (letters_pow3 hlets (Or.inl rfl))
      σ1 := letters_ne1_0 hlets hF
      τ3 := pow3_of_mul3 (letters_pow3 hlets (Or.inr rfl))
      τ1 := letters_ne1_2 hlets hF
      στ := letters_comm02 hF
      t2 := letters_sq4 hlets
      tσ := letters_t_inv_0 hone hlets hF
      tτ := letters_t_inv_2 hone hlets hF
      ct := ct_fact hone hlets hO
      ctz := ctz_fact hone hlets hF hO
      nc := hL.four.s12
      P9 := hF.card_P
      Pexp := P_pow3_gen hF
      Pcomm := P_comm_gen hF
      σP := e0_mem_P
      τP := e2_mem_P
      Pgen := Pgen_02 hF
      odd := hF.odd_sub
      CP := CP_fact hL hPb hlets hF hone
      Cσ := by rw [card_of_centComplement hL.v₁.compl, hM1, card_H₂_24 hone]
      Nσ := hL.v₁.normalizer_eq
      MC := hL.v₁.compl.left_le
      Mnorm := hL.v₁.compl.conj_mem
      Mt := hL.v₁.conj_t
      MH := hL.v₁.inf_H
      M243 := hM1
      MB := card_sq_81 (by rw [← hL.v₁.card_eq, hM1])
      MBz := by rw [hL.v₁.card_cent']; exact card_sq_81 (by rw [← hL.v₁.card_eq, hM1])
      Mτ := by have := hL.cor.card_Pb₂; rw [hPb] at this; omega
      M'C := hL.v₂.compl.left_le
      M'norm := hL.v₂.compl.conj_mem
      M'243 := hM2
      M'H := hL.v₂.inf_H }

end Assembly


section Assembly2

open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23

variable {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}

theorem vx_two [Finite G] (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) (hO : OneClass e) {M₁ M₂ Pb Np Nm : Subgroup G}
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card ↥Pb = 81) :
    VxData H (zOf e) (e 4) (e 2) (e 0) M₂ M₁ (Psub e) := by
  obtain ⟨hM1, hM2⟩ := card_of_Cor hL hPb
  refine
    { zz := zOf_sq hone hF
      zC := zC_fact hone hlets hF
      zH := zH_fact hone hlets hF
      tH := letters_mem_H hlets
      σH := hone.le_two (letters_mem_H₂ hlets).1
      τH := hone.le_one (letters_mem_H₁ hone hlets).1
      σ3 := pow3_of_mul3 (letters_pow3 hlets (Or.inr rfl))
      σ1 := letters_ne1_2 hlets hF
      τ3 := pow3_of_mul3 (letters_pow3 hlets (Or.inl rfl))
      τ1 := letters_ne1_0 hlets hF
      στ := (letters_comm02 hF).symm
      t2 := letters_sq4 hlets
      tσ := letters_t_inv_2 hone hlets hF
      tτ := letters_t_inv_0 hone hlets hF
      ct := ct_fact hone hlets hO
      ctz := ctz_fact hone hlets hF hO
      nc := fun h => hL.four.s12 h.symm
      P9 := hF.card_P
      Pexp := P_pow3_gen hF
      Pcomm := P_comm_gen hF
      σP := e2_mem_P
      τP := e0_mem_P
      Pgen := Pgen_20 hF
      odd := hF.odd_sub
      CP := CP_fact hL hPb hlets hF hone
      Cσ := by rw [card_of_centComplement hL.v₂.compl, hM2, card_H₁_24 hone]
      Nσ := hL.v₂.normalizer_eq
      MC := hL.v₂.compl.left_le
      Mnorm := hL.v₂.compl.conj_mem
      Mt := hL.v₂.conj_t
      MH := hL.v₂.inf_H
      M243 := hM2
      MB := card_sq_81 (by rw [← hL.v₂.card_eq, hM2])
      MBz := by rw [hL.v₂.card_cent']; exact card_sq_81 (by rw [← hL.v₂.card_eq, hM2])
      Mτ := by have := hL.cor.card_Pb₁; rw [hPb] at this; omega
      M'C := hL.v₁.compl.left_le
      M'norm := hL.v₁.compl.conj_mem
      M'243 := hM1
      M'H := hL.v₁.inf_H }

theorem mstruct_main [Finite G] (hone : G23One H H₁ H₂) (hlets : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) (hO : OneClass e) {M₁ M₂ Pb Np Nm : Subgroup G}
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card ↥Pb = 81) :
    MStruct e M₁ M₂ := by
  obtain ⟨hM1, hM2⟩ := card_of_Cor hL hPb
  obtain ⟨ex1, cm1, na1, cz1, zi1⟩ := (vx_one hone hlets hF hO hL hPb).vertex
  obtain ⟨ex2, cm2, na2, cz2, zi2⟩ := (vx_two hone hlets hF hO hL hPb).vertex
  exact ⟨hM1, hM2, ex1, ex2, cm1, cm2, na1, na2, cz1, cz2, zi1, zi2⟩

end Assembly2

end CFSG.GH74.QTGen4.Recog.G23.P7.MS

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

theorem leafMStruct
    : LeafMStruct := by
  intro G _ _ T H H₁ H₂ M e M₁ M₂ Pb Np Nm h hF hO hL hPb
  exact MS.mstruct_main h.ctx.one h.lets hF hO hL hPb

end CFSG.GH74.QTGen4.Recog.G23.P7
