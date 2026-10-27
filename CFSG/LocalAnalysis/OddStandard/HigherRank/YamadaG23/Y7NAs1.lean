module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RWr

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

structure NtAbs (t g : G) (Lam P S U P1 : Subgroup G) : Prop where
  t_sq : t ^ 2 = 1
  g_sq : g ^ 2 = 1
  tg : t * g = g * t
  pgroup : IsPGroup 2 P1
  t_mem : t ∈ P1
  g_mem : g ∈ P1
  P_le : P ≤ P1
  wr : Wr7 t P U
  cent : centEl P t = S
  card_S : Nat.card S = 2 ^ 6
  card_P : Nat.card P = 2 ^ 12
  U_le : U ≤ Lam
  comm : ∀ x ∈ Lam, ∀ y ∈ conjSub t Lam, x * y = y * x
  direct : Lam ⊓ conjSub t Lam = ⊥
  center : ∀ x ∈ Lam, (∀ y ∈ Lam, y * x = x * y) → x = 1
  ne_bot : Lam ≠ ⊥
  perm : ∀ x ∈ P1,
    (conjSub x Lam = Lam ∧ conjSub x (conjSub t Lam) = conjSub t Lam) ∨
    (conjSub x Lam = conjSub t Lam ∧ conjSub x (conjSub t Lam) = Lam)
  cent_K : ∀ z ∈ P1, (∀ x ∈ Lam, z * x = x * z) → (∀ y ∈ conjSub t Lam, z * y = y * z) → z = 1
  aut : ∀ Z : Subgroup G, IsPGroup 2 Z → Z ≤ normalizer (Lam : Set G) →
    Nat.card Z ≤ 2 ^ 7 * Nat.card ↥(Z ⊓ centralizer (Lam : Set G))
  g_norm_Lam : conjSub g Lam = Lam
  g_norm_P : ∀ x ∈ P, g * x * g⁻¹ ∈ P
  g_not_S : g ∉ S
  g_norm_S : ∀ x ∈ S, g * x * g⁻¹ ∈ S

private lemma conjSub_mul (a b : G) (Y : Subgroup G) :
    conjSub (a * b) Y = conjSub a (conjSub b Y) := by
  unfold conjSub
  rw [Subgroup.map_map (g := (MulAut.conj a).toMonoidHom) (f := (MulAut.conj b).toMonoidHom)]
  congr 1
  ext x
  change MulAut.conj (a * b) x = MulAut.conj a (MulAut.conj b x)
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  group

private lemma conjSub_inv_conjSub (c : G) (Y : Subgroup G) :
    conjSub c⁻¹ (conjSub c Y) = Y := by
  rw [conjSub, conjSub, Subgroup.map_map]
  have h : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom
      = MonoidHom.id G := by
    ext x
    change MulAut.conj c⁻¹ (MulAut.conj c x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [h, Subgroup.map_id]

namespace NtAbs

variable {t g : G} {Lam P S U P1 : Subgroup G}

private lemma Lam_ne_conjSub (h : NtAbs t g Lam P S U P1) : Lam ≠ conjSub t Lam := by
  intro heq
  have hbot : Lam ⊓ conjSub t Lam = ⊥ := h.direct
  rw [← heq, inf_idem] at hbot
  exact h.ne_bot hbot

private lemma conjSub_fix_right (h : NtAbs t g Lam P S U P1) {x : G} (hx : x ∈ P1)
    (hxL : conjSub x Lam = Lam) : conjSub x (conjSub t Lam) = conjSub t Lam := by
  rcases h.perm x hx with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact h2
  · exact absurd (hxL.symm.trans h1) (Lam_ne_conjSub h)

theorem P_le_normalizer (h : NtAbs t g Lam P S U P1) : P ≤ normalizer (Lam : Set G) := by
  rw [← h.wr.direct.1]
  refine sup_le (h.U_le.trans (Subgroup.le_normalizer (H := Lam))) ?_
  refine ((Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) h.U_le).trans ?_).trans
    (Subgroup.centralizer_le_normalizer (Lam : Set G))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact h.comm y hy x hx

theorem normal (h : NtAbs t g Lam P S U P1) :
    P1 ≤ normalizer ((normIn P1 Lam : Subgroup G) : Set G) := by
  refine (Subgroup.le_normalizer_iff (H := P1) (K := normIn P1 Lam)).mpr ?_
  intro x hx y hy
  have hyP1 : y ∈ P1 := hy.1
  have hyL : conjSub y Lam = Lam :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := Lam)).mp hy.2
  have hyL' : conjSub y (conjSub t Lam) = conjSub t Lam := conjSub_fix_right h hyP1 hyL
  refine Subgroup.mem_inf.mpr
    ⟨P1.mul_mem (P1.mul_mem hx hyP1) (P1.inv_mem hx), ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub (x * y * x⁻¹) Lam = Lam
  by_cases hxL : conjSub x Lam = Lam
  · have hxL' : conjSub x (conjSub t Lam) = conjSub t Lam := conjSub_fix_right h hx hxL
    have hxinv : conjSub x⁻¹ Lam = Lam := by
      have hc := conjSub_inv_conjSub x Lam
      rwa [hxL] at hc
    rw [conjSub_mul, conjSub_mul, hxinv, hyL, hxL]
  · have hswap : conjSub x (conjSub t Lam) = Lam := by
      rcases h.perm x hx with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 hxL
      · exact h2
    have hxinv : conjSub x⁻¹ Lam = conjSub t Lam := by
      have hc : conjSub x⁻¹ (conjSub x (conjSub t Lam)) = conjSub x⁻¹ Lam := by rw [hswap]
      rw [conjSub_inv_conjSub] at hc
      exact hc.symm
    rw [conjSub_mul, conjSub_mul, hxinv, hyL', hswap]

theorem split (h : NtAbs t g Lam P S U P1) : P1 = normIn P1 Lam ⊔ zpowers t := by
  refine le_antisymm ?_ (sup_le inf_le_left (Subgroup.zpowers_le.mpr h.t_mem))
  intro x hx
  by_cases hxL : conjSub x Lam = Lam
  · exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr
      ⟨hx, (Subgroup.mem_normalizer_iff_map_conj_eq (H := Lam)).mpr hxL⟩)
  · have hswap : conjSub x (conjSub t Lam) = Lam := by
      rcases h.perm x hx with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 hxL
      · exact h2
    have hxt : x * t ∈ normIn P1 Lam :=
      Subgroup.mem_inf.mpr ⟨P1.mul_mem hx h.t_mem,
        (Subgroup.mem_normalizer_iff_map_conj_eq (H := Lam)).mpr
          (by change conjSub (x * t) Lam = Lam; rw [conjSub_mul, hswap])⟩
    have hxeq : x = (x * t) * t⁻¹ := by group
    rw [hxeq]
    exact Subgroup.mul_mem_sup hxt (Subgroup.inv_mem _ (Subgroup.mem_zpowers t))

end NtAbs

end CFSG.OddStandard.HigherRank.YamadaG23
