module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPairDefs
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermModel

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

section Emb

variable {X : Type} [Group X] {n : ℕ} {A : Subgroup X}

@[expose] noncomputable def AhatModel.emb (M : AhatModel X n A) (hA : pPrimeCore 2 ↥A = ⊥) :
    M.K →* X :=
  A.subtype.comp (M.toKEquiv hA).symm.toMonoidHom

variable (M : AhatModel X n A) (hA : pPrimeCore 2 ↥A = ⊥)

theorem AhatModel.emb_toK (a : ↥A) : M.emb hA (M.toK a) = a := by
  show ((M.toKEquiv hA).symm (M.toK a) : X) = a
  have : M.toK a = M.toKEquiv hA a := rfl
  rw [this, MulEquiv.symm_apply_apply]

theorem AhatModel.emb_mem (k : M.K) : M.emb hA k ∈ A := ((M.toKEquiv hA).symm k).2

theorem AhatModel.toK_emb (k : M.K) : M.toK ⟨M.emb hA k, M.emb_mem hA k⟩ = k := by
  have : (⟨M.emb hA k, M.emb_mem hA k⟩ : ↥A) = (M.toKEquiv hA).symm k := rfl
  rw [this]
  exact (M.toKEquiv hA).apply_symm_apply k

theorem AhatModel.emb_injective : Function.Injective (M.emb hA) :=
  A.subtype_injective.comp (M.toKEquiv hA).symm.injective

theorem AhatModel.emb_commute_iff (x y : M.K) :
    M.emb hA x * M.emb hA y = M.emb hA y * M.emb hA x ↔ x * y = y * x := by
  rw [← map_mul, ← map_mul, (M.emb_injective hA).eq_iff]

theorem AhatModel.emb_autOf {c : X} (hc : c ∈ normalizer (A : Set X)) (k : M.K) :
    M.emb hA (M.autOf c hc k) = c * M.emb hA k * c⁻¹ := by
  obtain ⟨a, rfl⟩ := M.toK_surjective k
  rw [M.autOf_toK hc a, M.emb_toK hA, M.emb_toK hA]
  rfl

theorem AhatModel.autOf_eq_iff {c : X} (hc : c ∈ normalizer (A : Set X)) (k : M.K) :
    M.autOf c hc k = k ↔ M.emb hA k * c = c * M.emb hA k := by
  rw [← (M.emb_injective hA).eq_iff, M.emb_autOf hA hc]
  constructor
  · intro h
    calc M.emb hA k * c = (c * M.emb hA k * c⁻¹) * c := by rw [h]
      _ = c * M.emb hA k := by group
  · intro h
    rw [← h]
    group

theorem AhatModel.mem_fixSub_iff {c : X} (hc : c ∈ normalizer (A : Set X)) (k : M.K) :
    k ∈ AhatData.fixSub (M.autOf c hc) ↔ M.emb hA k ∈ centralizer ({c} : Set X) := by
  rw [AhatData.mem_fixSub, M.autOf_eq_iff hA hc, Subgroup.mem_centralizer_singleton_iff]

theorem AhatModel.perm_emb (hn : 8 ≤ n) (k : M.K) :
    M.perm (M.emb hA k) (Subgroup.le_normalizer (M.emb_mem hA k)) = M.C.ρ k := by
  rw [M.perm_of_mem hn (M.emb_mem hA k)]
  exact congrArg M.C.ρ (M.toK_emb hA k)

theorem AhatModel.perm_congr (M : AhatModel X n A) {c c' : X} (h : c = c')
    (hc : c ∈ normalizer (A : Set X)) (hc' : c' ∈ normalizer (A : Set X)) :
    M.perm c hc = M.perm c' hc' := by
  subst h
  rfl

end Emb

section Std

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {n : ℕ} {z : G}

@[expose] noncomputable def StdSetup.zK (S : StdSetup G L n z) (M : AhatModel G n L) : M.K :=
  M.toK ⟨z, S.z_mem⟩

@[expose] noncomputable def StdSetup.emb (S : StdSetup G L n z) (M : AhatModel G n L) :
    M.K →* G :=
  M.emb S.pPrimeCore_eq_bot

variable (S : StdSetup G L n z) (M : AhatModel G n L)

theorem StdSetup.emb_zK : S.emb M (S.zK M) = z := M.emb_toK S.pPrimeCore_eq_bot ⟨z, S.z_mem⟩

theorem StdSetup.emb_mem (k : M.K) : S.emb M k ∈ L := M.emb_mem S.pPrimeCore_eq_bot k

theorem StdSetup.emb_injective : Function.Injective (S.emb M) :=
  M.emb_injective S.pPrimeCore_eq_bot

theorem StdSetup.perm_emb (k : M.K) :
    M.perm (S.emb M k) (Subgroup.le_normalizer (S.emb_mem M k)) = M.C.ρ k :=
  M.perm_emb S.pPrimeCore_eq_bot S.hn k

theorem StdSetup.zK_mem_center : S.zK M ∈ center M.K := by
  rw [Subgroup.mem_center_iff]
  intro k
  obtain ⟨l, rfl⟩ := M.toK_surjective k
  show M.toK l * M.toK ⟨z, S.z_mem⟩ = M.toK ⟨z, S.z_mem⟩ * M.toK l
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 S.z_cent (l : G) l.2)

theorem StdSetup.zK_ne_one : S.zK M ≠ 1 := fun h => by
  have h1 : S.emb M (S.zK M) = 1 := by rw [h, map_one]
  rw [S.emb_zK M] at h1
  have := S.hz
  rw [h1, orderOf_one] at this
  omega

theorem StdSetup.eq_zK_of_mem_center {k : M.K} (hk : k ∈ center M.K) (hk1 : k ≠ 1) :
    k = S.zK M :=
  M.C.center_eq_of_ne_one hk (S.zK_mem_center M) hk1 (S.zK_ne_one M)

end Std

section Pair

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L L' : Subgroup G} {n : ℕ} {z a : G}

theorem StdPair.emb_pairLift (P : StdPair G L L' n z a) (M : AhatModel G n L) {r : M.K}
    (hr : IsPairLift M.C (M.perm a P.a_mem_norm) r) :
    P.setup.emb M r * P.setup.emb M r = z ∧ P.setup.emb M r * a = a * P.setup.emb M r := by
  have hn := P.setup.hn
  constructor
  · have h1 : r * r ∈ center M.K := hr.sq_mem_center
    have h2 : r * r ≠ 1 := hr.sq_ne_one hn
    rw [← map_mul, P.setup.eq_zK_of_mem_center M h1 h2, P.setup.emb_zK M]
  · have h := M.induces_perm hn a P.a_mem_norm
    have h2 : M.autOf a P.a_mem_norm r = r := hr.apply_eq h
    exact (M.autOf_eq_iff P.setup.pPrimeCore_eq_bot P.a_mem_norm r).1 h2

end Pair

end CFSG.OddStandard.Solomon75
