module

public import CFSG.LargeExtraspecial.S111BEF
public import CFSG.LargeExtraspecial.S4Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

section O2

variable {H : Type*} [Group H]

noncomputable abbrev O2Sub (X : Subgroup H) : Subgroup H := (CFSG.pCore 2 X).map X.subtype

theorem O2Sub_le (X : Subgroup H) : O2Sub X ≤ X := map_subtype_le _

theorem O2Sub_normal {X : Subgroup H} {x o : H} (hx : x ∈ X) (ho : o ∈ O2Sub X) :
    x * o * x⁻¹ ∈ O2Sub X := by
  obtain ⟨o', ho', rfl⟩ := ho
  exact ⟨⟨x, hx⟩ * o' * ⟨x, hx⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' ⟨x, hx⟩, rfl⟩

theorem isPGroup_O2Sub (X : Subgroup H) : IsPGroup 2 (O2Sub X) :=
  CFSG.pCore_isPGroup.map _

theorem le_O2Sub {X P : Subgroup H} (hPX : P ≤ X) (hPn : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    (hP : IsPGroup 2 P) : P ≤ O2Sub X := by
  have hN : (P.subgroupOf X).Normal := ⟨fun n hn x => by
    rw [mem_subgroupOf] at hn ⊢
    exact hPn x x.2 n hn⟩
  have hP' : IsPGroup 2 (P.subgroupOf X) := hP.of_equiv (subgroupOfEquivOfLe hPX).symm
  have hle : P.subgroupOf X ≤ CFSG.pCore 2 X := le_sSup ⟨hN, hP'⟩
  intro p hp
  exact ⟨⟨p, hPX hp⟩, hle (mem_subgroupOf.mpr hp), rfl⟩

theorem subgroupOf_O2Sub (X : Subgroup H) : (O2Sub X).subgroupOf X = CFSG.pCore 2 X :=
  comap_map_eq_self_of_injective X.subtype_injective _

theorem le_normalizer_O2Sub (X : Subgroup H) : X ≤ normalizer (O2Sub X : Set H) := fun x hx =>
  mem_normalizer_iff.mpr fun o => ⟨fun ho => O2Sub_normal hx ho, fun ho => by
    have := O2Sub_normal (inv_mem hx) ho
    rwa [show x⁻¹ * (x * o * x⁻¹) * x⁻¹⁻¹ = o by group] at this⟩

end O2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}
  {h k k' : G}

theorem O2Sub_le_normalizer_Lbar {j : G} (H : Hyp4 S j) (C : Cons311 S j) {X : Subgroup S.O}
    (hLX : S.Lbar j ≤ X) (hXM : X ≤ S.Mbar) :
    O2Sub X ≤ normalizer (S.Lbar j : Set S.O) := by
  have h2 : IsPGroup 2 (S.Lbar j ⊔ O2Sub X : Subgroup S.O) :=
    (isPGroup_Lbar S H.conj_mem).to_sup_of_normal_right' (isPGroup_O2Sub X)
      (hLX.trans (le_normalizer_O2Sub X))
  have hle := S4.le_normalizer_of_weaklyClosed C.weaklyClosed h2
    (sup_le (S.Lbar_le_Mbar j) ((O2Sub_le X).trans hXM)) le_sup_left
  exact le_sup_right.trans hle

theorem Lbar_sup_le_Mbar (S : Setting G) (k k' : G) : S.Lbar k ⊔ S.Lbar k' ≤ S.Mbar :=
  sup_le (S.Lbar_le_Mbar k) (S.Lbar_le_Mbar k')

namespace Pair111

variable (P : Pair111 S g A h k k')
include P


theorem EF_le_O2Sub : Ebar S k k' ⊔ Ebar S k' k ≤ O2Sub (S.Lbar k ⊔ S.Lbar k') :=
  le_O2Sub (Ebar_sup_le S k k') (fun _ hx _ hn => P.conj_mem_EF hx hn) P.isPGroup_EF

theorem inf_O2Sub_eq : S.Lbar k ⊓ O2Sub (S.Lbar k ⊔ S.Lbar k') = Ebar S k k' := by
  refine le_antisymm (fun x hx => ⟨hx.1, O2Sub_le_normalizer_Lbar P.hy'.hyp4 P.hy'.cons
    le_sup_right (Lbar_sup_le_Mbar S k k') hx.2⟩)
    (le_inf inf_le_left (le_sup_left.trans P.EF_le_O2Sub))

theorem inf_O2Sub_eq' : S.Lbar k' ⊓ O2Sub (S.Lbar k ⊔ S.Lbar k') = Ebar S k' k := by
  rw [sup_comm]
  exact P.swap.inf_O2Sub_eq

theorem not_Lbar_le_O2Sub : ¬ S.Lbar k ≤ O2Sub (S.Lbar k ⊔ S.Lbar k') := fun hle => by
  obtain ⟨x, hx, hxE⟩ := P.exists_not_mem_Ebar
  rw [← P.inf_O2Sub_eq] at hxE
  exact hxE ⟨hx, hle hx⟩

end Pair111

variable {m : S.M}

theorem Pair111.hyp97 (P : Pair111 S g A h k ((m : G) * k)) (hE : Ebar S k ((m : G) * k) ≠ ⊥) :
    S9.Hyp97 S k m (O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k))) where
  hyp4 := P.hy.hyp4
  cons := P.hy.cons
  le := O2Sub_le _
  normal := fun _ hx _ ho => O2Sub_normal hx ho
  isPGroup := isPGroup_O2Sub _
  max := fun _ hPX hPn hP => le_O2Sub hPX hPn hP
  inf_ne_bot := by rw [P.inf_O2Sub_eq]; exact hE

theorem Pair111.false_of_index_two (P : Pair111 S g A h k ((m : G) * k))
    (hE : Ebar S k ((m : G) * k) ≠ ⊥)
    (hidx : Nat.card (S.Lbar k) = 2 * Nat.card (Ebar S k ((m : G) * k))) : False := by
  have X97 := P.hyp97 hE
  have hidx' : Nat.card (S.Lbar k) =
      2 * Nat.card (S.Lbar k ⊓ O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k)) : Subgroup S.O) := by
    rw [P.inf_O2Sub_eq]; exact hidx
  obtain ⟨φ, hφs, hφk⟩ := X97.exists_hom_perm_three hidx' P.not_Lbar_le_O2Sub
  have hker : φ.ker = CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar ((m : G) * k)) :=
    hφk.trans (subgroupOf_O2Sub _)
  have hX : Nonempty ((↥(S.Lbar k ⊔ S.Lbar ((m : G) * k)) ⧸
      CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar ((m : G) * k))) ≃* Equiv.Perm (Fin 3)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩
  rcases lemma_4_3 P.hy.hyp4 (fun _ => P.hy.cons) m hX with hβ | ⟨α, h1, h2, h3⟩
  · have hβA := P.cfg.star P.mem P.ne P.memQ' hβ
    have hmem : ((m : G) * k) * S.z * ((m : G) * k)⁻¹ ∈ A ⊓ A.map (MulAut.conj h).toMonoidHom :=
      ⟨hβA, P.mem'⟩
    rw [P.disj, Setting.mem_zpowers_iff_of_mul_self S.z_mul_z] at hmem
    rcases hmem with h1 | h1
    · exact conj_z_ne_one S _ h1
    · exact P.ne' h1
  · exact P.hy.noA2' α h1 h2 h3

end CFSG.LargeExtraspecial.S11
