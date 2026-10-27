module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Main
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

@[expose] def vv (a b b' t : G) : G := a * (b * b' * t)

@[expose] def Tcompl (a b b' t : G) : Subgroup G := zpowers (vv a b b' t) ⊔ zpowers t

theorem not_mem_zpowers_of_inv_conj {v t : G} (hv : t * v * t⁻¹ = v⁻¹) (hv2 : v * v ≠ 1) :
    t ∉ zpowers v := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hc : v ^ k * v = v * v ^ k := ((Commute.refl v).zpow_left k).eq
  rw [hk] at hc
  have h2 : t * v * t⁻¹ = v := by
    rw [hc]; group
  rw [h2] at hv
  apply hv2
  calc v * v = v * v⁻¹ := by rw [← hv]
    _ = 1 := mul_inv_cancel v

namespace Rel

variable {a b a' b' t : G} {M : ℕ}

theorem s2_a_inv (h : Rel a b a' b' t M) : (b * b' * t) * a⁻¹ = a' * (b * b' * t) := by
  have e := h.a_s2_a_inv
  calc (b * b' * t) * a⁻¹ = a⁻¹ * (a * (b * b' * t) * a⁻¹) := by group
    _ = a⁻¹ * ((a * a') * (b * b' * t)) := by rw [e]
    _ = a' * (b * b' * t) := by group

theorem s2_a (h : Rel a b a' b' t M) : (b * b' * t) * a * (b * b' * t)⁻¹ = a'⁻¹ := by
  have e1 := h.s2_a_inv
  calc (b * b' * t) * a * (b * b' * t)⁻¹ = ((b * b' * t) * a⁻¹ * (b * b' * t)⁻¹)⁻¹ := by group
    _ = (a' * (b * b' * t) * (b * b' * t)⁻¹)⁻¹ := by rw [e1]
    _ = a'⁻¹ := by group

theorem vv_sq (h : Rel a b a' b' t M) : vv a b b' t * vv a b b' t = a * a'⁻¹ := by
  unfold vv
  have e := h.s2_a
  have hs := h.s2_sq
  calc a * (b * b' * t) * (a * (b * b' * t))
      = a * ((b * b' * t) * a * (b * b' * t)⁻¹) * ((b * b' * t) * (b * b' * t)) := by group
    _ = a * a'⁻¹ := by rw [e, hs, mul_one]

theorem t_vv (h : Rel a b a' b' t M) : t * vv a b b' t * t⁻¹ = (vv a b b' t)⁻¹ := by
  unfold vv
  have e1 := h.s2_a_inv
  have e2 := h.t_s2
  have e3 : t * a * t⁻¹ = a' := by rw [h.t_inv]; exact h.tat
  calc t * (a * (b * b' * t)) * t⁻¹ = (t * a * t⁻¹) * (t * (b * b' * t) * t⁻¹) := by group
    _ = a' * (b * b' * t) := by rw [e3, e2]
    _ = (b * b' * t) * a⁻¹ := e1.symm
    _ = (a * (b * b' * t))⁻¹ := by rw [mul_inv_rev, h.s2_inv]

theorem orderOf_vv (h : Rel a b a' b' t M) : orderOf (vv a b b' t) = 2 * (2 * M) := by
  have hv2 : vv a b b' t ^ 2 = a * a'⁻¹ := by rw [pow_two]; exact h.vv_sq
  have h1 : orderOf (vv a b b' t ^ 2) = 2 * M := by rw [hv2]; exact h.orderOf_dl1
  rw [orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0)] at h1
  have hM := h.one_le
  generalize orderOf (vv a b b' t) = m at h1 ⊢
  rcases Nat.even_or_odd m with he | ho
  · have hg : Nat.gcd m 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.1 he)
    rw [hg] at h1
    obtain ⟨k, hk⟩ := he
    omega
  · obtain ⟨k, hk⟩ := ho
    have hg : Nat.gcd m 2 = 1 := by
      have : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (by intro hd; obtain ⟨c, hc⟩ := hd; omega)
      exact this.symm
    rw [hg, Nat.div_one] at h1
    omega

theorem t_not_mem_vv (h : Rel a b a' b' t M) : t ∉ zpowers (vv a b b' t) := by
  refine not_mem_zpowers_of_inv_conj h.t_vv ?_
  rw [h.vv_sq]
  intro e
  have h1 := h.orderOf_dl1
  rw [e, orderOf_one] at h1
  have := h.one_le
  omega

theorem v_pow_order (h : Rel a b a' b' t M) : vv a b b' t ^ (2 * (2 * M)) = 1 :=
  h.orderOf_vv ▸ pow_orderOf_eq_one _

theorem D1_le_Tcompl (h : Rel a b a' b' t M) : D1 a a' t ≤ Tcompl a b b' t := by
  refine sup_le ?_ ?_
  · rw [zpowers_le, ← h.vv_sq]
    exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_left (mem_zpowers _))
  · exact le_sup_right

theorem mem_Tcompl_iff (h : Rel a b a' b' t M) {g : G} :
    g ∈ Tcompl a b b' t ↔ ∃ i : ℕ, g = vv a b b' t ^ i ∨ g = t * vv a b b' t ^ i := by
  have : NeZero (2 * (2 * M)) := ⟨by have := h.one_le; omega⟩
  exact mem_dihedral_iff (2 * (2 * M)) h.v_pow_order h.t_sq h.t_vv

theorem v_pow_even (h : Rel a b a' b' t M) (j : ℕ) : vv a b b' t ^ (2 * j) = (a * a'⁻¹) ^ j := by
  rw [pow_mul, pow_two, h.vv_sq]

theorem Tcompl_inf_D2 (h : Rel a b a' b' t M) :
    Tcompl a b b' t ⊓ D2 a a' b b' t = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgT, hgD⟩
  have hD12 : D1 a a' t ⊓ D2 a a' b b' t = ⊥ := h.D1_inf_D2
  have hs2 : b * b' * t ∈ D2 a a' b b' t := s2_mem_D2 a a' b b' t
  have hna := h.a_not_mem_sup
  have hd1 : ∀ j : ℕ, (a * a'⁻¹) ^ j ∈ D1 a a' t := fun j => pow_mem (dl1_mem_D1 a a' t) j
  obtain ⟨i, hi | hi⟩ := h.mem_Tcompl_iff.1 hgT
  · obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · have hgD1 : g ∈ D1 a a' t := by
        rw [hi, h.v_pow_even]
        exact hd1 j
      have : g ∈ D1 a a' t ⊓ D2 a a' b b' t := ⟨hgD1, hgD⟩
      rw [hD12] at this
      exact this
    · exfalso
      apply hna
      have hg : g = (a * a'⁻¹) ^ j * (a * (b * b' * t)) := by
        rw [hi, pow_succ, h.v_pow_even]; rfl
      have h1 : (a * a'⁻¹) ^ j * a ∈ D2 a a' b b' t := by
        have := mul_mem hgD (Subgroup.inv_mem _ hs2)
        rw [hg] at this
        simpa [mul_assoc] using this
      have hm : ((a * a'⁻¹) ^ j)⁻¹ * ((a * a'⁻¹) ^ j * a) ∈ D1 a a' t ⊔ D2 a a' b b' t :=
        mul_mem (mem_sup_left (Subgroup.inv_mem _ (hd1 j))) (mem_sup_right h1)
      have e : ((a * a'⁻¹) ^ j)⁻¹ * ((a * a'⁻¹) ^ j * a) = a := by group
      rw [e] at hm
      exact hm
  · obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · have hgD1 : g ∈ D1 a a' t := by
        rw [hi, h.v_pow_even]
        exact mul_mem (t_mem_D1 a a' t) (hd1 j)
      have : g ∈ D1 a a' t ⊓ D2 a a' b b' t := ⟨hgD1, hgD⟩
      rw [hD12] at this
      exact this
    · exfalso
      apply hna
      have hg : g = (t * (a * a'⁻¹) ^ j) * (a * (b * b' * t)) := by
        rw [hi, pow_succ, h.v_pow_even]; unfold vv; simp only [mul_assoc]
      have h1 : (t * (a * a'⁻¹) ^ j) * a ∈ D2 a a' b b' t := by
        have := mul_mem hgD (Subgroup.inv_mem _ hs2)
        rw [hg] at this
        simpa [mul_assoc] using this
      have hm : (t * (a * a'⁻¹) ^ j)⁻¹ * ((t * (a * a'⁻¹) ^ j) * a) ∈
          D1 a a' t ⊔ D2 a a' b b' t :=
        mul_mem (mem_sup_left (Subgroup.inv_mem _ (mul_mem (t_mem_D1 a a' t) (hd1 j))))
          (mem_sup_right h1)
      have e : (t * (a * a'⁻¹) ^ j)⁻¹ * ((t * (a * a'⁻¹) ^ j) * a) = a := by group
      rw [e] at hm
      exact hm

theorem D2_sup_Tcompl (h : Rel a b a' b' t M) :
    D2 a a' b b' t ⊔ Tcompl a b b' t = D1 a a' t ⊔ D2 a a' b b' t ⊔ zpowers a := by
  have hs2 : b * b' * t ∈ D2 a a' b b' t := s2_mem_D2 a a' b b' t
  have hD1 : D1 a a' t ≤ D1 a a' t ⊔ D2 a a' b b' t ⊔ zpowers a := le_sup_of_le_left le_sup_left
  have hD2 : D2 a a' b b' t ≤ D1 a a' t ⊔ D2 a a' b b' t ⊔ zpowers a := le_sup_of_le_left le_sup_right
  have hA : zpowers a ≤ D1 a a' t ⊔ D2 a a' b b' t ⊔ zpowers a := le_sup_right
  apply le_antisymm
  · refine sup_le hD2 (sup_le ?_ ?_)
    · rw [zpowers_le]
      exact mul_mem (hA (mem_zpowers a)) (hD2 hs2)
    · rw [zpowers_le]
      exact hD1 (t_mem_D1 a a' t)
  · refine sup_le (sup_le ?_ le_sup_left) ?_
    · exact h.D1_le_Tcompl.trans le_sup_right
    · rw [zpowers_le]
      have : a = vv a b b' t * (b * b' * t)⁻¹ := by unfold vv; group
      have hv : vv a b b' t ∈ D2 a a' b b' t ⊔ Tcompl a b b' t :=
        mem_sup_right (mem_sup_left (mem_zpowers _))
      have hs : (b * b' * t)⁻¹ ∈ D2 a a' b b' t ⊔ Tcompl a b b' t :=
        mem_sup_left (Subgroup.inv_mem _ hs2)
      have hm := mul_mem hv hs
      rw [← this] at hm
      exact hm

end Rel

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4

namespace CFSG.GH74.GLS.Stage2.Local.P27

variable {G : Type} [Group G]

structure Ps4Compl (T D₁ D₂ T₁s : Subgroup G) : Prop where
  le : T₁s ≤ T
  dih : IsDihedral ↥T₁s
  D₁_le : D₁ ≤ T₁s
  inf : T₁s ⊓ D₂ = ⊥
  sup : D₂ ⊔ T₁s = T

end CFSG.GH74.GLS.Stage2.Local.P27

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

section Fin

variable [Finite G]

namespace Canon

variable {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ} {a₀ b₀ : G} {M : ℕ}

omit [Finite G] in
theorem exists_compl (h : Canon S P₁ P₂ z t a a₀ b₀ M) :
    ∃ T₁s : Subgroup G, T₁s ≤ HH t a₀ b₀ ∧ IVK.IsDihedralTwoGroup ↥T₁s a ∧
      D1 a₀ (t * a₀ * t⁻¹) t ≤ T₁s ∧
      T₁s ⊓ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t = ⊥ ∧
      D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ⊔ T₁s = HH t a₀ b₀ := by
  have hr := h.rel
  have hsup := hr.D2_sup_Tcompl
  refine ⟨Tcompl a₀ b₀ (t * b₀ * t⁻¹) t, ?_, ?_, hr.D1_le_Tcompl, hr.Tcompl_inf_D2, hsup⟩
  · exact le_sup_right.trans hsup.le
  · have ha3 : 3 ≤ a := by
      by_contra hlt
      have h0 : a - 2 = 0 := by omega
      have h1 := h.hN
      rw [h0, pow_zero] at h1
      omega
    have hord : orderOf (vv a₀ b₀ (t * b₀ * t⁻¹) t) = 2 ^ (a - 1) := by
      rw [hr.orderOf_vv, show 2 * (2 * M) = 2 * 2 ^ (a - 2) by rw [h.hN], ← pow_succ']
      congr 1
      omega
    have := isDihedralTwoGroup_sup (a - 1) (by omega) (vv a₀ b₀ (t * b₀ * t⁻¹) t) t hord hr.t_sq
      hr.t_vv hr.t_not_mem_vv
    rwa [show a - 1 + 1 = a by omega] at this

theorem ps4_decomp_compl (h : Canon S P₁ P₂ z t a a₀ b₀ M) {w0 : G}
    (hw0 : w0 ∈ Vset S (P₁ ⊔ P₂) z t (xx t a₀ M)) {U : Subgroup G}
    (hU : U ≤ Tc S t a₀ M ⊓ centralizer ({w0} : Set G)) (hcard : Nat.card ↥U = 2 ^ (a - 1))
    (hinf : ∀ y ∈ U, y ∈ zpowers (xx t a₀ M) ⊔ zpowers w0 → y = 1)
    (hcls : ∀ d ∈ U, d * d = 1 → d ≠ 1 → d ∈ Xc (P₁ ⊔ P₂) z t ∧ w0 * d ∈ Xc (P₁ ⊔ P₂) z t ∧
      xx t a₀ M * w0 * d ∈ Xc (P₁ ⊔ P₂) z t ∧ xx t a₀ M * d ∈ Zc (P₁ ⊔ P₂) z t) :
    ∃ D₁ T₁ M' T₁s : Subgroup G, Ps4Decomp (Tc S t a₀ M) D₁ U T₁ M' z (xx t a₀ M) w0 a
      (Zc (P₁ ⊔ P₂) z t) (Xc (P₁ ⊔ P₂) z t) ∧ Ps4Compl (Tc S t a₀ M) D₁ U T₁s := by
  obtain ⟨k, hk⟩ := h.V_form hw0
  have hw : w0 = (a₀ * (t * a₀ * t⁻¹)⁻¹) ^ (k : ℤ) * t := by rw [zpow_natCast]; exact hk
  have hUD : U = D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t := h.rigid hw hU hcard hinf hcls
  subst hUD
  obtain ⟨T₁s, hle, hdih, hD1le, hinf2, hsup⟩ := h.exists_compl
  have hTH : Tc S t a₀ M = HH t a₀ b₀ := h.Tc_eq_HH
  refine ⟨D1 a₀ (t * a₀ * t⁻¹) t, zpowers (a₀ * (t * a₀ * t⁻¹)⁻¹), Mm t a₀ b₀, T₁s, ?_,
    ⟨by rw [hTH]; exact hle, ⟨2 ^ a, hdih.2⟩, hD1le, hinf2, by rw [hTH]; exact hsup⟩⟩
  exact
    { D₁_dih := h.D1_dihedral
      D₂_dih := h.D2_dihedral
      D₁_le := (D1_le_HH t a₀ b₀).trans h.HH_le_Tc
      D₂_le := (D2_le_HH t a₀ b₀).trans h.HH_le_Tc
      comm := h.rel.D1_D2_comm
      inter := h.rel.D1_inf_D2
      index := by rw [hTH]; exact h.relIndex_K
      D₁_normal := fun s hs d hd => h.D1_normal s (hTH ▸ hs) d hd
      u_mem := h.xx_mem_D1
      center_D₁ := h.center_D1
      w0_mem := by rw [hw]; exact h.refl_mem_D1 _
      uz_mem := h.xz_mem_D2
      CTw0 := by
        intro g hg hgc
        have hmem : g ∈ Tc S t a₀ M ⊓ centralizer ({w0} : Set G) :=
          ⟨hg, mem_centralizer_singleton_iff.2 hgc⟩
        have hC := (h.Cw_eq (k : ℤ))
        rw [← hw] at hC
        rw [hC] at hmem
        have hV := h.V4_le_D1 (k : ℤ)
        rw [← hw] at hV
        have hle : (zpowers (xx t a₀ M) ⊔ zpowers w0) ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t ≤
            D1 a₀ (t * a₀ * t⁻¹) t ⊔ D2 a₀ (t * a₀ * t⁻¹) b₀ (t * b₀ * t⁻¹) t :=
          sup_le (hV.trans le_sup_left) le_sup_right
        exact hle hmem
      T₁_le := h.zpowers_r_le_D1
      T₁_cyc := inferInstance
      u_T₁ := by rw [h.xx_eq_pow]; exact pow_mem (mem_zpowers _) M
      T₁_idx := h.relIndex_T1
      T₁_refl := h.T1_refl
      M_le := h.Mm_le_HH.trans h.HH_le_Tc
      M_idx := by rw [hTH]; exact h.relIndex_Mm
      R_le := h.L_le_Mm
      M_inter := fun g hg => h.Mm_inter_K g hg.1 hg.2
      M_der := h.Mm_der
      M_cos := fun w hw' hwM => h.Mm_cos (hTH ▸ hw') hwM
      M_sep := fun s hs hsM hss m hm hmm hm1 hmu => h.Mm_sep s (hTH ▸ hs) hsM hss m hm hmm hm1 hmu }

end Canon

end Fin

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup

variable {G : Type} [Group G]

structure Ps4StdC (S : Subgroup G) (z u : G) (a : ℕ) (Z X : Set G) : Prop where
  std : Ps4Std S z u a Z X
  compl : ∀ w0 : G, w0 ∈ S ⊓ centralizer ({u} : Set G) → w0 * w0 = 1 → w0 ∈ Z → w0 ≠ z → u * w0 ∈ Z →
    Nat.card ↥(S ⊓ centralizer ({u} : Set G) ⊓ centralizer ({w0} : Set G)) = 2 ^ (a + 1) →
    ∀ U : Subgroup G, U ≤ S ⊓ centralizer ({u} : Set G) ⊓ centralizer ({w0} : Set G) →
      (∀ c ∈ S ⊓ centralizer ({u} : Set G) ⊓ centralizer ({w0} : Set G), ∀ d ∈ U, c * d * c⁻¹ ∈ U) →
      Nat.card ↥U = 2 ^ (a - 1) → IVK.IsDihedralTwoGroup ↥U (a - 1) →
      (∀ y ∈ U, y ∈ zpowers u ⊔ zpowers w0 → y = 1) →
      (∀ d ∈ U, d * d = 1 → d ≠ 1 → d ∈ X ∧ w0 * d ∈ X ∧ u * w0 * d ∈ X ∧ u * d ∈ Z) →
      ∃ D₁ T₁ M T₁s : Subgroup G, Ps4Decomp (S ⊓ centralizer ({u} : Set G)) D₁ U T₁ M z u w0 a Z X ∧
        Ps4Compl (S ⊓ centralizer ({u} : Set G)) D₁ U T₁s

end CFSG.GH74.GLS.Stage2.Local.P27

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q

variable {G : Type} [Group G]

section Fin3

variable [Finite G] {S P₁ P₂ : Subgroup G} {z t u : G} {a : ℕ}

theorem ps4_std_compl (h : Data S P₁ P₂ z t a) (hu : UHyp S P₁ P₂ z u) :
    Ps4StdC S z u a (Zc (P₁ ⊔ P₂) z t) (Xc (P₁ ⊔ P₂) z t) := by
  refine ⟨ps4_std h hu, ?_⟩
  obtain ⟨t', a₀, b₀, M, hC, hux, hZ, hX⟩ := exists_canon_of_uhyp h hu
  intro w0 hw0T hw0sq hw0Z hw0z huw0Z hcard U hU hnorm hUcard hUdih hinf hcls
  rw [hux] at hw0T huw0Z hinf hcls hU
  rw [← hZ] at hw0Z huw0Z
  rw [← hX, ← hZ] at hcls
  have hV : w0 ∈ Vset S (P₁ ⊔ P₂) z t' (xx t' a₀ M) := ⟨hw0T, hw0Z, hw0z, huw0Z⟩
  rw [hux, ← hZ, ← hX]
  exact hC.ps4_decomp_compl hV hU hUcard hinf hcls

end Fin3

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4
