module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Basic
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SD1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68b
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

@[expose] def Hsub8 (t : G) (B K : Subgroup G) : Subgroup G :=
  Nsub8 t B ⊓ normalizer (K : Set G) ⊓ centralizer ({t} : Set G)

theorem sec8t84a1_mem_H {t : G} {B K : Subgroup G} {h : G} :
    h ∈ Hsub8 t B K ↔
      h ∈ Nsub8 t B ∧ (∀ x : G, x ∈ K ↔ h * x * h⁻¹ ∈ K) ∧ h * t = t * h := by
  unfold Hsub8
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

theorem sec8t84a1_B_comm {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hctx : Sec8Ctx G t L S z g B) {a b : G} (ha : a ∈ B) (hb : b ∈ B) : a * b = b * a :=
  sec9d_B_comm hctx.toSec8Base ha hb

theorem sec8t84a1_B_sq {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hctx : Sec8Ctx G t L S z g B) {b : G} (hb : b ∈ B) : b * b = 1 :=
  sec9d_B_sq hctx.toSec8Base hb

theorem sec8t84a1_B_card {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hctx : Sec8Ctx G t L S z g B) : Nat.card B = 16 := by
  rw [hctx.B_e16.2]
  norm_num

theorem sec8t84a1_t_sq {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hctx : Sec8Ctx G t L S z g B) : t * t = 1 :=
  sec9d_t_sq hctx.toSec8Base

theorem sec8t84a1_A_comm {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hctx : Sec8Ctx G t L S z g B) {a b : G} (ha : a ∈ Asub8 t B) (hb : b ∈ Asub8 t B) :
    a * b = b * a :=
  CFSG.Open.IsElemAbelian.comm (sec8t84a1_A_elem hctx).1 ha hb

theorem sec8t84a1_A_sq {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hctx : Sec8Ctx G t L S z g B) {a : G} (ha : a ∈ Asub8 t B) : a * a = 1 :=
  CFSG.Open.IsElemAbelian.mul_self_eq_one (sec8t84a1_A_elem hctx).1 ha

theorem sec8t84a1_mem_A {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hctx : Sec8Ctx G t L S z g B) {y : G} (hy : y ∈ Asub8 t B) :
    y ∈ B ∨ ∃ b ∈ B, y = t * b :=
  sec68_mem_sup (sec8t84a1_t_sq hctx) (fun b hb => (sec8t84a1_t_comm hctx hb).symm) hy

theorem sec8t84a1_t_mul_not_mem_B {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hctx : Sec8Ctx G t L S z g B) {b : G} (hb : b ∈ B) : t * b ∉ B := by
  intro h
  apply sec8t84a1_t_not_mem_B hctx
  have h' : t * b * b⁻¹ ∈ B := B.mul_mem h (B.inv_mem hb)
  rwa [mul_inv_cancel_right] at h'

structure Sec8T84A1Pre (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B K : Subgroup G) : Prop where
  ctx : Sec8Ctx G t L S z g B
  le_C : K ≤ Nsub8 t B ⊓ centralizer (B : Set G)
  syl : IsSylow2Of K (Nsub8 t B ⊓ centralizer (B : Set G))
  A_le : Asub8 t B ≤ K
  card : Nat.card K = 2 ^ 9
  cent_t : K ⊓ centralizer ({t} : Set G) = Asub8 t B
  tau : ∀ b ∈ B, ∃ k ∈ K, k * t * k⁻¹ * t⁻¹ = b

end CFSG.OddStandard.SmallF3.Omega
