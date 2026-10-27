module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Naturality
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der7
public import CFSG.GH74.GLS.Stage2.Final.L26.Core
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen5
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Covering

variable {G : Type} [Group G]

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := (MulAut.conj g).injective hyx
    rw [← this]
    exact hy

theorem exists_mul_of_mem_sup_of_le_normalizer {A B : Subgroup G} (h : A ≤ normalizer (B : Set G))
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let T : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', (a'⁻¹ * b * a') * b', B.mul_mem ?_ hb', by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (h (A.inv_mem ha')) b).mp hb
        simpa using this
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, ?_, by group⟩
        exact (Subgroup.mem_normalizer_iff.mp (h ha) b⁻¹).mp (B.inv_mem hb) }
  have hA : A ≤ T := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
  have hB : B ≤ T := fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩
  exact (sup_le hA hB) hx

theorem le_pPrimeCoreOf_of_normal_odd {N X : Subgroup G} (hNX : N ≤ X)
    (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hodd : Odd (Nat.card ↥N)) :
    N ≤ pPrimeCoreOf 2 X := by
  have hnormal : (N.subgroupOf X).Normal := ⟨fun a ha h => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hnorm (h : G) h.2 (a : G) ha⟩
  have hcop : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : N.subgroupOf X ≤ pPrimeCore 2 ↥X := le_sSup ⟨hnormal, hcop⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

variable [Finite G]

theorem covers_iff_covers_sup {A T I : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hTI : T ≤ normalizer (I : Set G)) (hTA : T ≤ A) :
    Covers A I (pPrimeCoreOf 2 I) ↔ Covers A (I ⊔ T) (pPrimeCoreOf 2 (I ⊔ T)) := by
  have hIT : I ≤ I ⊔ T := le_sup_left
  have hTT : T ≤ I ⊔ T := le_sup_right
  have hTsI : I ⊔ T ≤ normalizer (I : Set G) := sup_le Subgroup.le_normalizer hTI
  have hTOi : T ≤ normalizer ((pPrimeCoreOf 2 I : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_of_map_conj_eq
    have h1 := pPrimeCoreOf_map 2 (MulAut.conj t) I
    rw [map_conj_eq_of_mem_normalizer (hTI ht)] at h1
    exact h1.symm
  have hTsOi : I ⊔ T ≤ normalizer ((pPrimeCoreOf 2 I : Subgroup G) : Set G) :=
    sup_le (le_normalizer_pPrimeCoreOf I) hTOi
  have hOiOt : pPrimeCoreOf 2 I ≤ pPrimeCoreOf 2 (I ⊔ T) :=
    le_pPrimeCoreOf_of_normal_odd ((Subgroup.map_subtype_le _).trans hIT)
      (fun x hx n hn => (Subgroup.mem_normalizer_iff.mp (hTsOi hx) n).mp hn) (odd_card_pPrimeCoreOf I)
  have hTsOt : I ⊔ T ≤ normalizer ((pPrimeCoreOf 2 (I ⊔ T) : Subgroup G) : Set G) :=
    le_normalizer_pPrimeCoreOf (I ⊔ T)
  have hOtTs : pPrimeCoreOf 2 (I ⊔ T) ≤ I ⊔ T := Subgroup.map_subtype_le _
  constructor
  · intro h
    refine sup_le ?_ ?_
    · calc I ≤ (A ⊓ I) ⊔ pPrimeCoreOf 2 I := h
        _ ≤ (A ⊓ (I ⊔ T)) ⊔ pPrimeCoreOf 2 (I ⊔ T) :=
          sup_le_sup (inf_le_inf_left A hIT) hOiOt
    · exact le_trans (le_inf hTA hTT) le_sup_left
  · intro h g hg
    have hg' : g ∈ (A ⊓ (I ⊔ T)) ⊔ pPrimeCoreOf 2 (I ⊔ T) := h (hIT hg)
    obtain ⟨n, hn, o, ho, hno⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (A := A ⊓ (I ⊔ T)) (B := pPrimeCoreOf 2 (I ⊔ T)) (fun x hx => hTsOt hx.2) hg'
    obtain ⟨τ, hτ, i₀, hi₀, hni⟩ := exists_mul_of_mem_sup_of_le_normalizer (A := T) (B := I) hTI
      (by rw [sup_comm]; exact hn.2)
    have hτIO : τ ∈ I ⊔ pPrimeCoreOf 2 (I ⊔ T) := by
      have : τ = g * (o⁻¹ * i₀⁻¹) := by
        rw [hno, hni]
        group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg)
        (Subgroup.mul_mem _ (Subgroup.mem_sup_right ((pPrimeCoreOf 2 (I ⊔ T)).inv_mem ho))
          (Subgroup.mem_sup_left (I.inv_mem hi₀)))
    have hτI : τ ∈ I := by
      have hτTs : τ ∈ I ⊔ T := hTT hτ
      have : (I.subgroupOf (I ⊔ T)).Normal := ⟨fun a ha b => by
        rw [Subgroup.mem_subgroupOf] at ha ⊢
        simpa using (Subgroup.mem_normalizer_iff.mp (hTsI b.2) a).mp ha⟩
      have hN : ∀ x ∈ (pPrimeCoreOf 2 (I ⊔ T)).subgroupOf (I ⊔ T), Nat.Coprime (orderOf x) 2 := by
        intro x hx
        have h1 : (x : G) ∈ pPrimeCoreOf 2 (I ⊔ T) := Subgroup.mem_subgroupOf.mp hx
        have := coprime_orderOf_of_mem_pPrimeCoreOf Nat.prime_two h1
        rw [Subgroup.orderOf_coe] at this
        exact this.symm
      have hx : (⟨τ, hτTs⟩ : ↥(I ⊔ T)) ∈
          I.subgroupOf (I ⊔ T) ⊔ (pPrimeCoreOf 2 (I ⊔ T)).subgroupOf (I ⊔ T) := by
        rw [← Subgroup.subgroupOf_sup hIT hOtTs]
        exact Subgroup.mem_subgroupOf.mpr hτIO
      obtain ⟨a, ha⟩ := hT2 ⟨τ, hτ⟩
      have hxa : (⟨τ, hτTs⟩ : ↥(I ⊔ T)) ^ (2 ^ a) = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val ha)
      exact Subgroup.mem_subgroupOf.mp
        (CFSG.GH74.GLS.Stage2.Final.L26.mem_of_two_pow_of_mem_sup_odd hN hx hxa)
    have hnI : n ∈ I := by
      rw [hni]
      exact I.mul_mem hτI hi₀
    have hoI : o ∈ I := by
      have : o = n⁻¹ * g := by rw [hno]; group
      rw [this]
      exact I.mul_mem (I.inv_mem hnI) hg
    have hoO : o ∈ pPrimeCoreOf 2 I := by
      refine le_pPrimeCoreOf_of_normal_odd (N := pPrimeCoreOf 2 (I ⊔ T) ⊓ I) inf_le_right
        (fun x hx m hm => ⟨(Subgroup.mem_normalizer_iff.mp (hTsOt (hIT hx)) m).mp hm.1,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) m).mp hm.2⟩)
        (Odd.of_dvd_nat (odd_card_pPrimeCoreOf (I ⊔ T)) (Subgroup.card_dvd_of_le inf_le_left)) ⟨ho, hoI⟩
    rw [hno]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hn.1, hnI⟩) (Subgroup.mem_sup_right hoO)

end Covering

section Choice

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {Q T U : Subgroup G} {t g : G}

theorem Ctx10.T5A (h : Ctx10 G z k S M p Q T U t g) (h1 : ¬ TypeOneCase G k) :
    T5A z k S T (Iof U ⊔ T) := by
  refine Or.inr ⟨h1, U, h.choice.U_le, h.choice.U_four, h.z_mem_U, ⟨t, ?_, (h.choice.T_two h1).2.1⟩,
    (h.choice.T_two h1).2.2.1, h.T_le_S, rfl⟩
  rw [h.choice.U_gen]
  exact Subgroup.mem_sup_right (mem_zpowers t)

theorem Ctx10.T_le_normalizer_Iof (h : Ctx10 G z k S M p Q T U t g) (h1 : ¬ TypeOneCase G k) :
    T ≤ normalizer ((Iof U : Subgroup G) : Set G) := by
  intro x hx
  have hxC : x ∈ centralizer (U : Set G) := by
    have := (h.choice.T_two h1).1
    rw [this] at hx
    exact hx.2
  exact CFSG.GH74.GLS.Stage1.Thm2.Recip.mem_normalizer_pLayerOf hxC

theorem Ctx10.T_isPGroup (h : Ctx10 G z k S M p Q T U t g) : IsPGroup 2 ↥T :=
  h.ctx9.ctx.sylow.isPGroup.to_le h.T_le_S

end Choice

end CFSG.GH74.GLS.Stage2.Bender.Thm2
