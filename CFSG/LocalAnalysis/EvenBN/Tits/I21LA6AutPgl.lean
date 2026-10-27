module

public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped MatrixGroups

section SupZpowers

variable {Y : Type*} [Group Y] (J : Subgroup Y) [J.Normal] {t : Y}

theorem pglP_mem_zpowers {z : Y} (ht2 : t * t = 1) (hz : z ∈ zpowers t) : z = 1 ∨ z = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem pglP_mem_sup {x : Y} (ht2 : t * t = 1) :
    x ∈ J ⊔ zpowers t ↔ x ∈ J ∨ ∃ j ∈ J, x = j * t := by
  rw [mem_sup_of_normal_left]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rcases pglP_mem_zpowers ht2 hz with rfl | rfl
    · left
      simpa using hy
    · right
      exact ⟨y, hy, rfl⟩
  · rintro (hx | ⟨j, hj, rfl⟩)
    · exact ⟨x, hx, 1, one_mem _, mul_one x⟩
    · exact ⟨j, hj, t, mem_zpowers t, rfl⟩

theorem pglP_sq_mem (ht2 : t * t = 1) {x : Y} (hx : x ∈ J ⊔ zpowers t) : x * x ∈ J := by
  rcases (pglP_mem_sup J ht2).1 hx with h | ⟨j, hj, rfl⟩
  · exact J.mul_mem h h
  · have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have h1 : j * t * (j * t) = j * (t * j * t⁻¹) := by
      rw [hti]
      group
    rw [h1]
    exact J.mul_mem hj (Normal.conj_mem inferInstance j hj t)

theorem pglP_mul_inv_mem (ht2 : t * t = 1) {x y : Y} (hx : x ∈ J ⊔ zpowers t)
    (hy : y ∈ J ⊔ zpowers t) (hxJ : x ∉ J) (hyJ : y ∉ J) : x * y⁻¹ ∈ J := by
  rcases (pglP_mem_sup J ht2).1 hx with h | ⟨j, hj, rfl⟩
  · exact absurd h hxJ
  rcases (pglP_mem_sup J ht2).1 hy with h | ⟨k, hk, rfl⟩
  · exact absurd h hyJ
  have : j * t * (k * t)⁻¹ = j * k⁻¹ := by group
  rw [this]
  exact J.mul_mem hj (J.inv_mem hk)

theorem pglP_card_sup [Finite Y] (ht2 : t * t = 1) (htJ : t ∉ J) :
    Nat.card ↥(J ⊔ zpowers t) = 2 * Nat.card J := by
  have ht1 : t ≠ 1 := fun h => htJ (h ▸ J.one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hinf : J ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff_forall]
    rintro x ⟨hxJ, hxz⟩
    rcases pglP_mem_zpowers ht2 hxz with rfl | rfl
    · rfl
    · exact absurd hxJ htJ
  have hrel : J.relIndex (J ⊔ zpowers t) = 2 := by
    rw [relIndex_sup_left, ← inf_relIndex_right, hinf, relIndex_bot_left, Nat.card_zpowers, hord]
  have h1 := card_mul_index (J.subgroupOf (J ⊔ zpowers t))
  have h2 : Nat.card ↥(J.subgroupOf (J ⊔ zpowers t)) = Nat.card J :=
    Nat.card_congr (subgroupOfEquivOfLe le_sup_left).toEquiv
  rw [h2] at h1
  have h3 : (J.subgroupOf (J ⊔ zpowers t)).index = 2 := hrel
  rw [h3] at h1
  rw [← h1, mul_comm]

end SupZpowers

section PglIso

theorem pglP_card_field {F : Type} [Field F] [Finite F] {q : ℕ} (hq : Odd q)
    (hqF : Nat.card F = q ^ 2) (h360 : Nat.card (PSL2 F) = 360) :
    L2Field F ∧ Nat.card F = 9 := by
  have hodd : Odd (Nat.card F) := by rw [hqF]; exact hq.pow
  have hgt : 3 < Nat.card F := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨k, rfl⟩ := hq
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hqF
      omega
    · rw [hqF]
      nlinarith
  have hL : L2Field F := ⟨hodd, hgt⟩
  have hform := psl2_card_formula F (isOddPrimePower_of_L2Field hL)
  rw [h360] at hform
  refine ⟨hL, ?_⟩
  set n := Nat.card F with hn
  have hn10 : n < 10 := by
    by_contra h
    replace h := not_lt.1 h
    have h1 : 100 ≤ n ^ 2 := by nlinarith
    have h2 : 10 * 99 ≤ n * (n ^ 2 - 1) := Nat.mul_le_mul h (by omega)
    omega
  interval_cases n <;> omega

@[expose] noncomputable def pglRho {Y : Type*} [Group Y] (J : Subgroup Y) [J.Normal] {F : Type}
    [Field F] (e2 : J ≃* L2 F) : Y →* MulAut (L2 F) :=
  (MulAut.congr e2).toMonoidHom.comp (MulAut.conjNormal (H := J))

theorem pglRho_apply {Y : Type*} [Group Y] (J : Subgroup Y) [J.Normal] {F : Type} [Field F]
    (e2 : J ≃* L2 F) (y : Y) (k : L2 F) :
    pglRho J e2 y k = e2 (MulAut.conjNormal (H := J) y (e2.symm k)) := rfl

theorem pglRho_injective {Y : Type*} [Group Y] (J : Subgroup Y) [J.Normal]
    (hC : centralizer (J : Set Y) = ⊥) {F : Type} [Field F] (e2 : J ≃* L2 F) :
    Function.Injective (pglRho J e2) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have hmem : y ∈ centralizer (J : Set Y) := by
    rw [mem_centralizer_iff]
    intro j hj
    have h1 := congrArg (fun α : MulAut (L2 F) => e2.symm (α (e2 ⟨j, hj⟩))) hy
    simp only [pglRho_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [hC] at hmem
  exact hmem

theorem pglRho_coe {Y : Type*} [Group Y] (J : Subgroup Y) [J.Normal] {F : Type} [Field F]
    (e2 : J ≃* L2 F) (j : J) : pglRho J e2 (j : Y) = MulAut.conj (e2 j) := by
  ext k
  simp only [pglRho_apply, MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem pglRho_eq_innDiagHom {Y : Type*} [Group Y] (J : Subgroup Y) [J.Normal] {F : Type}
    [Field F] [Finite F] (e : J ≃* PSL(2, F)) (g : PGL(2, F)) {t : Y}
    (hconj : ∀ x y : J, (y : Y) = t * x * t⁻¹ →
      Matrix.ProjectiveSpecialLinearGroup.toPGL (e y) =
        g * Matrix.ProjectiveSpecialLinearGroup.toPGL (e x) * g⁻¹) :
    pglRho J (e.trans (L2.equivPSL F).symm) t = innDiagHom (MulEquiv.refl (L2 F)) g := by
  ext k
  obtain ⟨x, rfl⟩ := (e.trans (L2.equivPSL F).symm).surjective k
  apply (toPSL (MulEquiv.refl (L2 F))).injective
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_toPSL_innDiagHom, pglRho_apply, MulEquiv.symm_apply_apply]
  have h1 := hconj x (MulAut.conjNormal (H := J) t x) (by rw [MulAut.conjNormal_apply])
  simpa [toPSL] using h1

theorem pglP_iso {Y : Type*} [Group Y] [Finite Y] (J : Subgroup Y) [J.Normal] {t : Y}
    (hcard : Nat.card J = 360) (ht2 : t * t = 1) (htJ : t ∉ J) (hpgl : PGLTwoSquareOuter J t) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 9 ∧
      Nonempty (↥(J ⊔ zpowers t) ≃* PGL(2, F)) := by
  obtain ⟨-, hC, F, hFld, hFin, q, hq, hqF, e, g, -, hconj⟩ := hpgl
  haveI : Finite F := Finite.of_fintype F
  have hqF' : Nat.card F = q ^ 2 := by rw [Nat.card_eq_fintype_card, hqF]
  have h360 : Nat.card (PSL2 F) = 360 := by
    rw [← hcard]
    exact (Nat.card_congr e.toEquiv).symm
  obtain ⟨hL, hF9⟩ := pglP_card_field hq hqF' h360
  refine ⟨F, hFld, inferInstance, hF9, ?_⟩
  let e2 : J ≃* L2 F := e.trans (L2.equivPSL F).symm
  let eK : L2 F ≃* L2 F := MulEquiv.refl _
  have hρt : pglRho J e2 t = innDiagHom eK g := pglRho_eq_innDiagHom J e g hconj
  have hle : J ⊔ zpowers t ≤ (innDiagSub eK).comap (pglRho J e2) := by
    refine sup_le ?_ ?_
    · intro j hj
      show pglRho J e2 ((⟨j, hj⟩ : J) : Y) ∈ innDiagSub eK
      rw [pglRho_coe J e2 ⟨j, hj⟩]
      exact innAut_le_innDiagSub eK ⟨e2 ⟨j, hj⟩, rfl⟩
    · rw [zpowers_le]
      show pglRho J e2 t ∈ innDiagSub eK
      rw [hρt]
      exact ⟨g, rfl⟩
  let ρP : ↥(J ⊔ zpowers t) →* ↥(innDiagSub eK) :=
    ((pglRho J e2).comp (J ⊔ zpowers t).subtype).codRestrict (innDiagSub eK) fun x => hle x.2
  have hinj : Function.Injective ρP := by
    intro x y hxy
    have h1 : pglRho J e2 (x : Y) = pglRho J e2 (y : Y) := congrArg Subtype.val hxy
    exact Subtype.ext (pglRho_injective J hC e2 h1)
  have hcardP : Nat.card ↥(J ⊔ zpowers t) = 720 := by
    rw [pglP_card_sup J ht2 htJ, hcard]
  have hcardD : Nat.card ↥(innDiagSub eK) = 720 := by
    rw [card_innDiagSub eK hL, Nat.card_congr e2.symm.toEquiv, hcard]
  have hbij : Function.Bijective ρP :=
    hinj.bijective_of_nat_card_le (by rw [hcardP, hcardD])
  exact ⟨(MulEquiv.ofBijective ρP hbij).trans
    (MonoidHom.ofInjective (innDiagHom_injective eK)).symm⟩

theorem pglP_finite (F : Type) [Field F] [Finite F] : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

theorem pglP_card_pgl {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9) :
    Nat.card (PGL2 F) = 720 := by
  rw [pgl2_card_formula, hF]
  norm_num

theorem pglP_factorization_720 : (720 : ℕ).factorization 2 = 4 := by
  rw [show (720 : ℕ) = 2 ^ 4 * 45 by norm_num,
    Nat.factorization_mul_apply_of_coprime ((by decide : Nat.Coprime 2 45).pow_left 4),
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45), Nat.add_zero]

theorem pglP_card_sylow {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 720)
    (S : Sylow 2 G) : Nat.card S = 16 := by
  rw [S.card_eq_multiplicity, hG, pglP_factorization_720]
  norm_num

theorem pglP_sylow_dihedral {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9)
    (S : Sylow 2 (PGL2 F)) : Nonempty (↥S ≃* DihedralGroup 8) := by
  haveI := pglP_finite F
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨3, 2, Nat.prime_three, ⟨1, rfl⟩, by norm_num, by rw [hF]; norm_num⟩
  obtain ⟨m, -, ⟨ψ⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hodd S
  have h16 := pglP_card_sylow (pglP_card_pgl hF) S
  rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card] at h16
  have hm : m = 3 := by
    have h8 : 2 ^ m = 2 ^ 3 := by omega
    exact Nat.pow_right_injective (le_refl 2) h8
  subst hm
  exact ⟨ψ⟩

theorem pglP_exists_orderOf_eight {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9) :
    ∃ x : PGL2 F, orderOf x = 8 := by
  haveI := pglP_finite F
  obtain ⟨ψ⟩ := pglP_sylow_dihedral hF (Classical.choice inferInstance)
  refine ⟨(ψ.symm (DihedralGroup.r 1) : PGL2 F), ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]

theorem pglP_dihedral_of_le {Y : Type*} [Group Y] {P : Subgroup Y} {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 9) (Φ : ↥P ≃* PGL(2, F)) {D : Subgroup Y} (hDP : D ≤ P)
    (hD : Nat.card D = 16) : Nonempty (↥D ≃* DihedralGroup 8) := by
  haveI := pglP_finite F
  let D' : Subgroup (PGL2 F) := (D.subgroupOf P).map Φ.toMonoidHom
  have hD' : Nat.card D' = 16 := by
    rw [card_map_of_injective Φ.injective, ← hD]
    exact Nat.card_congr (subgroupOfEquivOfLe hDP).toEquiv
  let S : Sylow 2 (PGL2 F) :=
    Sylow.ofCard D' (by rw [hD', pglP_card_pgl hF, pglP_factorization_720]; norm_num)
  obtain ⟨ψ⟩ := pglP_sylow_dihedral hF S
  exact ⟨((subgroupOfEquivOfLe hDP).symm.trans (Φ.subgroupMap (D.subgroupOf P))).trans ψ⟩

def pglD16Chk (a b c : DihedralGroup 8) : Bool :=
  !decide (a * a = 1) || !decide (b * b = 1) || !decide (c * c = 1) || decide (a = 1) ||
    decide (b = 1) || decide (c = 1) || decide (a = b) || decide (a = c) ||
    decide (b = c) || !decide (a * b = b * a) || !decide (a * c = c * a) ||
    !decide (b * c = c * b) || decide (a * b = c)

theorem pglD16Chk_true : ∀ a b c : DihedralGroup 8, pglD16Chk a b c = true := by decide

theorem pglD16_key {a b c : DihedralGroup 8} (h1 : a * a = 1) (h2 : b * b = 1) (h3 : c * c = 1)
    (h4 : a ≠ 1) (h5 : b ≠ 1) (h6 : c ≠ 1) (h7 : a ≠ b) (h8 : a ≠ c) (h9 : b ≠ c)
    (h10 : a * b = b * a) (h11 : a * c = c * a) (h12 : b * c = c * b) : a * b = c := by
  have h := pglD16Chk_true a b c
  simp only [pglD16Chk, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  tauto

theorem pglD16_conj {a b : DihedralGroup 8} (ha : a * a = 1) (hb : b * b = 1)
    (ha' : ∀ x, x * x ≠ a) (hb' : ∀ x, x * x ≠ b) (hab : (a * b) ^ 4 = 1) :
    ∃ d, d * a * d⁻¹ = b := by
  have key : ∀ a b : DihedralGroup 8, a * a = 1 → b * b = 1 → (∀ x, x * x ≠ a) →
      (∀ x, x * x ≠ b) → (a * b) ^ 4 = 1 → ∃ d, d * a * d⁻¹ = b := by decide
  exact key a b ha hb ha' hb' hab

theorem pglD16_pow (x : DihedralGroup 8) : x ^ 8 = 1 := by
  have key : ∀ x : DihedralGroup 8, x ^ 8 = 1 := by decide
  exact key x

theorem pglP_card_le_four_of_key {G : Type*} [Group G] [Finite G] (F : Subgroup G)
    (key : ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, a ≠ 1 → b ≠ 1 → c ≠ 1 → a ≠ b → a ≠ c → b ≠ c →
      a * b = c) : Nat.card F ≤ 4 := by
  classical
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hmiss : ∀ s : Finset G, s.card ≤ 4 → ∃ c ∈ F, c ∉ s := by
    intro s hs
    by_contra hall
    have hsub : (F : Set G) ⊆ (s : Set G) := fun x hx => by
      by_contra hxs
      exact hall ⟨x, hx, hxs⟩
    have h1 := Set.ncard_le_ncard hsub s.finite_toSet
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
    exact absurd (h1.trans hs) (by simpa using hlt)
  obtain ⟨a, haF, ha⟩ := hmiss {1} (by simp)
  obtain ⟨b, hbF, hb⟩ := hmiss {1, a} (Finset.card_le_two.trans (by norm_num))
  obtain ⟨c, hcF, hc⟩ := hmiss {1, a, b, a * b} Finset.card_le_four
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc
  exact hc.2.2.2 (key a haF b hbF c hcF ha hb.1 hc.1 (Ne.symm hb.2) (Ne.symm hc.2.1)
    (Ne.symm hc.2.2.1)).symm

end PglIso

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
