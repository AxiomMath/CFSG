module

public import CFSG.LargeExtraspecial.S9SevenI
public import CFSG.LargeExtraspecial.S111ADisj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

section Defs

variable {G : Type*} [Group G] [Finite G]

variable (S : Setting G) in
noncomputable abbrev Ebar (k k' : G) : Subgroup S.O :=
  S.Lbar k ⊓ normalizer (S.Lbar k' : Set S.O)

variable (S : Setting G) in
@[expose] def IsTIModEF (k k' : G) : Prop :=
  ∀ x ∈ S.Lbar k ⊔ S.Lbar k',
    (S.Lbar k ⊔ (Ebar S k k' ⊔ Ebar S k' k)).map (MulAut.conj x).toMonoidHom =
        S.Lbar k ⊔ (Ebar S k k' ⊔ Ebar S k' k) ∨
      (S.Lbar k ⊔ (Ebar S k k' ⊔ Ebar S k' k)).map (MulAut.conj x).toMonoidHom ⊓
          (S.Lbar k ⊔ (Ebar S k k' ⊔ Ebar S k' k)) ≤ Ebar S k k' ⊔ Ebar S k' k

end Defs

@[expose] def TIClaim111 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G)
    (A : Subgroup G), Cfg111 S g A → 6 ≤ S.width → ∀ h ∈ S.M,
    A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z → ∀ k k' : G,
    k * S.z * k⁻¹ ∈ A → k * S.z * k⁻¹ ≠ S.z →
    k' * S.z * k'⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom → k' * S.z * k'⁻¹ ≠ S.z →
    Ebar S k k' ≠ ⊥ → 4 * Nat.card (Ebar S k k') ≤ Nat.card (S.Lbar k) → IsTIModEF S k k'

@[expose] def Residual97For111 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G)
    (A : Subgroup G), Cfg111 S g A → 6 ≤ S.width → ∀ h ∈ S.M,
    A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z → ∀ (k : G) (m : S.M),
    k * S.z * k⁻¹ ∈ A → k * S.z * k⁻¹ ≠ S.z →
    ((m : G) * k) * S.z * ((m : G) * k)⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom →
    ∀ O : Subgroup S.O, S9.Timmesfeld97Residual S k m O

@[expose] def A5Input111 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G)
    (A : Subgroup G), Cfg111 S g A → 6 ≤ S.width → ∀ h ∈ S.M,
    A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z → ∀ (k : G) (m : S.M),
    k * S.z * k⁻¹ ∈ A → k * S.z * k⁻¹ ≠ S.z →
    ((m : G) * k) * S.z * ((m : G) * k)⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom →
    Ebar S k ((m : G) * k) ≠ ⊥ →
    4 * Nat.card (Ebar S k ((m : G) * k)) ≤ Nat.card (S.Lbar k) →
    ∃ φ : ↥(S.Lbar k ⊔ S.Lbar ((m : G) * k)) →* alternatingGroup (Fin 5),
      Function.Surjective φ ∧ φ.ker = CFSG.pCore 2 ↥(S.Lbar k ⊔ S.Lbar ((m : G) * k))

variable {G : Type*} [Group G] [Finite G]

variable (S : Setting G) in
structure Pair111 (g : G) (A : Subgroup G) (h k k' : G) : Prop where
  cfg : Cfg111 S g A
  hM : h ∈ S.M
  disj : A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z
  mem : k * S.z * k⁻¹ ∈ A
  ne : k * S.z * k⁻¹ ≠ S.z
  mem' : k' * S.z * k'⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom
  ne' : k' * S.z * k'⁻¹ ≠ S.z

variable {S : Setting G} {g : G} {A : Subgroup G} {h k k' : G}

namespace Pair111

variable (P : Pair111 S g A h k k')
include P

theorem swap : Pair111 S (h * g) (A.map (MulAut.conj h).toMonoidHom) h⁻¹ k' k where
  cfg := P.cfg.conj P.hM
  hM := S.M.inv_mem P.hM
  disj := inf_map_conj_symm P.disj
  mem := P.mem'
  ne := P.ne'
  mem' := by rw [map_conj_inv_map_conj]; exact P.mem
  ne' := P.ne

theorem memQ : k * S.z * k⁻¹ ∈ S.QG := P.cfg.inc.le_QG P.mem

theorem memQ' : k' * S.z * k'⁻¹ ∈ S.QG := (P.cfg.inc.map_conj P.hM).le_QG P.mem'

theorem hy : Hyp S k := P.cfg.hy.of_conj P.memQ P.ne

theorem hy' : Hyp S k' := P.cfg.hy.of_conj P.memQ' P.ne'

theorem inf_eq_bot : S.Lbar k ⊓ S.Lbar k' = ⊥ :=
  P.cfg.Lbar_inf_eq_bot P.hM P.disj P.mem P.ne P.mem' P.ne'

theorem inf_Qa_le {e : G} (he : e * S.z * e⁻¹ ∈ A) (hez : e * S.z * e⁻¹ ≠ S.z) :
    A.map (MulAut.conj h).toMonoidHom ⊓ S.Qa e ≤ zpowers S.z :=
  P.cfg.inf_Qa_le P.hM P.disj he hez

theorem inf_Qa_le' : A ⊓ S.Qa k' ≤ zpowers S.z :=
  P.cfg.inf_Qa_le_of_mem_map P.hM P.disj P.mem' P.ne'

theorem exists_conj : ∃ m : S.M, ((m : G) * k) * S.z * ((m : G) * k)⁻¹ = k' * S.z * k'⁻¹ := by
  obtain ⟨m, hm, hmk⟩ := P.hy.fusion k' P.memQ' P.ne'
  exact ⟨⟨m, hm⟩, by rw [mul_conj_z]; exact hmk⟩

end Pair111

end CFSG.LargeExtraspecial.S11
