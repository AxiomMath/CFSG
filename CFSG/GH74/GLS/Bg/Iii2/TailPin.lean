module

public import CFSG.GH74.GLS.Bg.Iii2.TailConj
public import CFSG.GH74.GLS.Bg.Iii2.TailZStar
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Thm3.Sec6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem exists_isSylowOf_ge {A C : Subgroup G} (hA : IsPGroup 2 A) (hAC : A ≤ C) :
    ∃ T' : Subgroup G, IsSylowOf 2 T' C ∧ A ≤ T' := by
  have hA' : IsPGroup 2 (A.subgroupOf C) := hA.comap_subtype
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨(Q : Subgroup C).map C.subtype, ⟨Q, rfl⟩, ?_⟩
  intro a ha
  exact ⟨⟨a, hAC ha⟩, hQ ha, rfl⟩

theorem rr_unique_inv (hquat : II4_4_quat) (hG : IsKProperSimple G) {u : G} {J A : Subgroup G}
    (hJ : IsRigidRankOneComp u J) (hA2 : IsPGroup 2 A) (hAJ : A ≤ J)
    (hAu : A ≤ centralizer ({u} : Set G)) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (haa : a * a = 1) (hbb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨T', hT', hAT'⟩ := exists_isSylowOf_ge hA2 hAu
  have hq : ∃ n, IVK.IsQuaternionTwoGroup ↥(T' ⊓ J) n :=
    hquat G hG u (rr_ord hJ) T' J hT' (rr_pcomp hJ) hJ.2
  obtain ⟨z, -, -, -, -, -, hzu, -⟩ := quat_data hq
  have ha' : a ∈ T' ⊓ J := ⟨hAT' ha, hAJ ha⟩
  have hb' : b ∈ T' ⊓ J := ⟨hAT' hb, hAJ hb⟩
  rcases hzu a ha' haa with h | h
  · exact absurd h ha1
  rcases hzu b hb' hbb with h' | h'
  · exact absurd h' hb1
  rw [h, h']

theorem not_mem_of_third (hquat : II4_4_quat) (hG : IsKProperSimple G) {u z : G}
    {K T J : Subgroup G} (hT2 : IsPGroup 2 T) (hJ : IsRigidRankOneComp u J) (hPJ : T ⊓ K ≤ J)
    (huT : u ∈ T) (huJ : u ∈ J) (huu : u * u = 1) (hu1 : u ≠ 1)
    (hcomm : ∀ p ∈ T ⊓ K, u * p = p * u) (hz : QData T K z) (huz : u ≠ z) : False := by
  have hA2 : IsPGroup 2 ↥((T ⊓ K) ⊔ zpowers u) :=
    hT2.to_le (sup_le inf_le_left ((zpowers_le).2 huT))
  have hAJ : (T ⊓ K) ⊔ zpowers u ≤ J := sup_le hPJ ((zpowers_le).2 huJ)
  have hAu : (T ⊓ K) ⊔ zpowers u ≤ centralizer ({u} : Set G) :=
    sup_le (fun p hp => Subgroup.mem_centralizer_singleton_iff.2 (hcomm p hp).symm)
      ((zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))
  exact huz (rr_unique_inv hquat hG hJ hA2 hAJ hAu (Subgroup.mem_sup_right (mem_zpowers u))
    (Subgroup.mem_sup_left hz.mem) huu hz.sq hu1 hz.ne)

structure KleinCfg (x : G) (T K₁ K₂ : Subgroup G) (z₁ z₂ : G) : Prop where
  ord : orderOf x = 2
  hT : IsSylowOf 2 T (centralizer ({x} : Set G))
  h₁ : IsRigidRankOneComp x K₁
  h₂ : IsRigidRankOneComp x K₂
  ne : K₁ ≠ K₂
  all : ∀ K, IsRigidRankOneComp x K → K = K₁ ∨ K = K₂
  q₁ : QData T K₁ z₁
  q₂ : QData T K₂ z₂
  z_ne : z₁ ≠ z₂

namespace KleinCfg

variable {x : G} {T K₁ K₂ : Subgroup G} {z₁ z₂ : G}

theorem comm₁₂ (C : KleinCfg x T K₁ K₂ z₁ z₂) : ∀ p ∈ T ⊓ K₁, ∀ q ∈ T ⊓ K₂, p * q = q * p :=
  rr_sylow_comm C.h₁ C.h₂ C.ne C.hT

theorem z_comm (C : KleinCfg x T K₁ K₂ z₁ z₂) : z₁ * z₂ = z₂ * z₁ :=
  C.comm₁₂ z₁ C.q₁.mem z₂ C.q₂.mem

omit [Finite G] in
theorem orderOf_z₁ (C : KleinCfg x T K₁ K₂ z₁ z₂) : orderOf z₁ = 2 :=
  orderOf_eq_prime (by rw [sq]; exact C.q₁.sq) C.q₁.ne

omit [Finite G] in
theorem orderOf_z₂ (C : KleinCfg x T K₁ K₂ z₁ z₂) : orderOf z₂ = 2 :=
  orderOf_eq_prime (by rw [sq]; exact C.q₂.sq) C.q₂.ne

theorem z₃_sq (C : KleinCfg x T K₁ K₂ z₁ z₂) : (z₁ * z₂) * (z₁ * z₂) = 1 := by
  calc (z₁ * z₂) * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by simp only [mul_assoc]
    _ = z₁ * (z₁ * z₂) * z₂ := by rw [C.z_comm]
    _ = (z₁ * z₁) * (z₂ * z₂) := by simp only [mul_assoc]
    _ = 1 := by rw [C.q₁.sq, C.q₂.sq, mul_one]

omit [Finite G] in
theorem z₃_ne (C : KleinCfg x T K₁ K₂ z₁ z₂) : z₁ * z₂ ≠ 1 := by
  intro h
  apply C.z_ne
  have h2 : z₁ = z₂⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [h2]
  exact inv_eq_of_mul_eq_one_right C.q₂.sq

theorem orderOf_z₃ (C : KleinCfg x T K₁ K₂ z₁ z₂) : orderOf (z₁ * z₂) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact C.z₃_sq) C.z₃_ne

omit [Finite G] in
theorem z₃_mem (C : KleinCfg x T K₁ K₂ z₁ z₂) : z₁ * z₂ ∈ T :=
  T.mul_mem C.q₁.mem.1 C.q₂.mem.1

theorem z₃_comm₁ (C : KleinCfg x T K₁ K₂ z₁ z₂) :
    ∀ p ∈ T ⊓ K₁, (z₁ * z₂) * p = p * (z₁ * z₂) := by
  intro p hp
  calc z₁ * z₂ * p = z₁ * (z₂ * p) := mul_assoc _ _ _
    _ = z₁ * (p * z₂) := by rw [C.comm₁₂ p hp z₂ C.q₂.mem]
    _ = z₁ * p * z₂ := (mul_assoc _ _ _).symm
    _ = p * z₁ * z₂ := by rw [C.q₁.central p hp]
    _ = p * (z₁ * z₂) := mul_assoc _ _ _

theorem z₃_comm₂ (C : KleinCfg x T K₁ K₂ z₁ z₂) :
    ∀ p ∈ T ⊓ K₂, (z₁ * z₂) * p = p * (z₁ * z₂) := by
  intro p hp
  calc z₁ * z₂ * p = z₁ * (z₂ * p) := mul_assoc _ _ _
    _ = z₁ * (p * z₂) := by rw [C.q₂.central p hp]
    _ = z₁ * p * z₂ := (mul_assoc _ _ _).symm
    _ = p * z₁ * z₂ := by rw [C.comm₁₂ z₁ C.q₁.mem p hp]
    _ = p * (z₁ * z₂) := mul_assoc _ _ _

theorem sec (C : KleinCfg x T K₁ K₂ z₁ z₂) (h44 : II4_44) (hG : IsKProperSimple G) :
    ∀ K, IsRigidRankOneComp x K → z₁ ∈ cSec K ∧ z₂ ∈ cSec K := by
  intro K hK
  have e₁ : z₁ ∈ cSec K₁ := rr_inv_mem_cSec h44 hG C.h₁ C.q₁.mem.2 C.orderOf_z₁
  have e₂ : z₂ ∈ cSec K₂ := rr_inv_mem_cSec h44 hG C.h₂ C.q₂.mem.2 C.orderOf_z₂
  have f₁₂ : K₁ ≤ cSec K₂ := le_cSec_of_ne (rr_pcomp C.h₁) (rr_pcomp C.h₂) C.ne
  have f₂₁ : K₂ ≤ cSec K₁ := le_cSec_of_ne (rr_pcomp C.h₂) (rr_pcomp C.h₁) C.ne.symm
  rcases C.all K hK with rfl | rfl
  · exact ⟨e₁, f₂₁ C.q₂.mem.2⟩
  · exact ⟨f₁₂ C.q₁.mem.2, e₂⟩

theorem sec₃ (C : KleinCfg x T K₁ K₂ z₁ z₂) (h44 : II4_44) (hG : IsKProperSimple G) :
    ∀ K, IsRigidRankOneComp x K → z₁ * z₂ ∈ cSec K := fun K hK =>
  (cSec K).mul_mem (C.sec h44 hG K hK).1 (C.sec h44 hG K hK).2

theorem false_of_conj (C : KleinCfg x T K₁ K₂ z₁ z₂) (hCM : CM) (hquat : II4_4_quat) (h44 : II4_44)
    (hG : IsKProperSimple G) (h3 : 3 ≤ pRank 2 G) (hxT : T ≤ centralizer ({x} : Set G))
    (hc₁ : IsConj x z₁) (hc₃ : IsConj x (z₁ * z₂)) : False := by
  have hpin₁ : Pin z₁ := by
    obtain ⟨J, -, hrr, -, hP⟩ := cm_apply hCM hG h3 C.ord C.orderOf_z₁ (hxT C.q₁.mem.1) hc₁
      (fun K hK => (C.sec h44 hG K hK).1)
    refine ⟨J K₁, hrr K₁ C.h₁, ?_⟩
    exact hP K₁ C.h₁ (T ⊓ K₁) (rr_sylow C.h₁ C.hT) (fun p hp => (C.q₁.central p hp).symm)
      C.q₁.mem
  have hpin₃ : Pin (z₁ * z₂) := pin_conj hpin₁ (hc₁.symm.trans hc₃)
  obtain ⟨J, -, hrr, hset, hP⟩ := cm_apply hCM hG h3 C.ord C.orderOf_z₃ (hxT C.z₃_mem) hc₃
    (C.sec₃ h44 hG)
  obtain ⟨J', hJ', hz₃J'⟩ := hpin₃
  have hmem : J' ∈ {J'' : Subgroup G | IsRigidRankOneComp (z₁ * z₂) J''} := hJ'
  rw [hset] at hmem
  obtain ⟨K, hK, rfl⟩ := hmem
  have hT2 : IsPGroup 2 ↥T := C.hT.isPGroup
  rcases C.all K hK with rfl | rfl
  · refine not_mem_of_third hquat hG hT2 hJ' ?_ C.z₃_mem hz₃J' C.z₃_sq C.z₃_ne C.z₃_comm₁ C.q₁ ?_
    · exact hP K C.h₁ (T ⊓ K) (rr_sylow C.h₁ C.hT) C.z₃_comm₁
    · intro h
      apply C.q₂.ne
      have : z₁ * z₂ = z₁ * 1 := by rw [mul_one]; exact h
      exact mul_left_cancel this
  · refine not_mem_of_third hquat hG hT2 hJ' ?_ C.z₃_mem hz₃J' C.z₃_sq C.z₃_ne C.z₃_comm₂ C.q₂ ?_
    · exact hP K C.h₂ (T ⊓ K) (rr_sylow C.h₂ C.hT) C.z₃_comm₂
    · intro h
      apply C.q₁.ne
      have : z₁ * z₂ = 1 * z₂ := by rw [one_mul]; exact h
      exact mul_right_cancel this

end KleinCfg

end CFSG.GH74.GLS.Bg.Iii2
