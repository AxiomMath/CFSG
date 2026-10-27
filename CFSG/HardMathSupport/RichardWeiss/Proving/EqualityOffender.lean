module

public import CFSG.Quasithin.Background.Basic
public import CFSG.CGT.PushingUpLit.SYMB.ProdCard
public import CFSG.HardMathSupport.RichardWeiss.Proving.CommutingClosure

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.Quasithin CFSG.Open

variable {G : Type} [Group G]

theorem mul_comm_of_mem_isMulCommutative {E : Subgroup G} (hE : IsMulCommutative E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)

theorem isElemAbelian_sup_of_centralizer {A V : Subgroup G} (hAab : IsElemAbelian 2 A)
    (hV : IsElemAbelian 2 V) :
    IsElemAbelian 2 ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) := by
  obtain ⟨hAc, hAsq⟩ := hAab
  obtain ⟨hVc, hVsq⟩ := hV
  have hKA : ∀ k ∈ A ⊓ Subgroup.centralizer (V : Set G), k ∈ A := fun k hk => hk.1
  have hKV : ∀ k ∈ A ⊓ Subgroup.centralizer (V : Set G), ∀ v ∈ V, k * v = v * k :=
    fun k hk v hv => ((Subgroup.mem_centralizer_iff.1 hk.2) v hv).symm
  have hsup : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V =
      Subgroup.closure (((A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∪
        (V : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hpair : ∀ x ∈ ((A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∪ (V : Set G),
      ∀ y ∈ ((A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∪ (V : Set G),
      x * y = y * x := by
    rintro x (hx | hx) y (hy | hy)
    · exact mul_comm_of_mem_isMulCommutative hAc (hKA x hx) (hKA y hy)
    · exact hKV x hx y hy
    · exact (hKV y hy x hx).symm
    · exact mul_comm_of_mem_isMulCommutative hVc hx hy
  have h2 : ∀ x ∈ ((A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∪ (V : Set G),
      x ^ 2 = 1 := by
    rintro x (hx | hx)
    · exact hAsq x (hKA x hx)
    · exact hVsq x hx
  obtain ⟨hsq, hcomm⟩ := CFSG.HardMathSupport.RichardWeiss.Proving.pairwise_closure_sq_and_commute
    (((A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∪ (V : Set G)) h2 hpair
  rw [hsup]
  refine ⟨⟨⟨?_⟩⟩, fun x hx => hsq x hx⟩
  intro a b
  exact Subtype.ext (hcomm a.1 a.2 b.1 b.2)

theorem inf_centralizer_inf_eq {A V : Subgroup G} (hV : IsElemAbelian 2 V) :
    (A ⊓ Subgroup.centralizer (V : Set G)) ⊓ V = A ⊓ V := by
  obtain ⟨hVc, -⟩ := hV
  ext x
  constructor
  · rintro ⟨⟨hxA, -⟩, hxV⟩
    exact ⟨hxA, hxV⟩
  · rintro ⟨hxA, hxV⟩
    refine ⟨⟨hxA, ?_⟩, hxV⟩
    exact Subgroup.mem_centralizer_iff.2 fun h hh => mul_comm_of_mem_isMulCommutative hVc hh hxV

theorem inf_le_centralizer_inf {A V : Subgroup G} (hAab : IsElemAbelian 2 A) :
    A ⊓ V ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
  obtain ⟨hAc, -⟩ := hAab
  rintro x ⟨hxA, hxV⟩
  refine ⟨hxV, ?_⟩
  exact Subgroup.mem_centralizer_iff.2 fun h hh => mul_comm_of_mem_isMulCommutative hAc hh hxA

theorem card_le_card_sup_core [Finite G] {A K V : Subgroup G} (hAab : IsElemAbelian 2 A)
    (hJ : Nat.card ↥(K ⊔ V) * Nat.card ↥(A ⊓ V) = Nat.card ↥K * Nat.card ↥V)
    (hA1 : K.relIndex A * Nat.card ↥K = Nat.card ↥A)
    (hV1 : (A ⊓ V).relIndex V * Nat.card ↥(A ⊓ V) = Nat.card ↥V)
    (hle : K.relIndex A ≤ (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V) :
    Nat.card ↥A ≤ Nat.card ↥(K ⊔ V) := by
  have hne : (A ⊓ V).relIndex V ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have hmono : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ (A ⊓ V).relIndex V :=
    Subgroup.relIndex_le_of_le_left (inf_le_centralizer_inf hAab) hne
  have hi : 0 < Nat.card ↥(A ⊓ V) := Nat.card_pos
  have key : Nat.card ↥(K ⊔ V) * Nat.card ↥(A ⊓ V) =
      (Nat.card ↥K * (A ⊓ V).relIndex V) * Nat.card ↥(A ⊓ V) := by
    rw [hJ, ← hV1]
    ring
  have hc : Nat.card ↥(K ⊔ V) = Nat.card ↥K * (A ⊓ V).relIndex V :=
    Nat.eq_of_mul_eq_mul_right hi key
  rw [← hA1, hc]
  calc K.relIndex A * Nat.card ↥K ≤ (A ⊓ V).relIndex V * Nat.card ↥K :=
        Nat.mul_le_mul_right _ (hle.trans hmono)
    _ = Nat.card ↥K * (A ⊓ V).relIndex V := Nat.mul_comm _ _

theorem isMaxElemAbelian_sup_of_relIndex_le [Finite G] {S A V : Subgroup G}
    (hA : IsMaxElemAbelian S A) (hV : IsElemAbelian 2 V) (hVS : V ≤ S)
    (hle : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤
      (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V) :
    IsMaxElemAbelian S ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) := by
  obtain ⟨hAS, hAab, hmax⟩ := hA
  have hJ : IsElemAbelian 2 ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) :=
    isElemAbelian_sup_of_centralizer hAab hV
  have hJS : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ S :=
    sup_le (inf_le_left.trans hAS) hVS
  have hcomm : ∀ c ∈ A ⊓ Subgroup.centralizer (V : Set G), ∀ d ∈ V, c * d = d * c :=
    fun c hc d hd => ((Subgroup.mem_centralizer_iff.1 hc.2) d hd).symm
  have hJc := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute
    (C := A ⊓ Subgroup.centralizer (V : Set G)) (D := V) hcomm
  rw [inf_centralizer_inf_eq hV] at hJc
  have hKA : A ⊓ Subgroup.centralizer (V : Set G) ≤ A := inf_le_left
  have hA1 : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) = Nat.card ↥A := by
    have h := Subgroup.relIndex_mul_card (H := A ⊓ Subgroup.centralizer (V : Set G)) (K := A)
    rwa [inf_eq_left.2 hKA] at h
  have hAV : A ⊓ V ≤ V := inf_le_right
  have hV1 : (A ⊓ V).relIndex V * Nat.card ↥(A ⊓ V) = Nat.card ↥V := by
    have h := Subgroup.relIndex_mul_card (H := A ⊓ V) (K := V)
    rwa [inf_eq_left.2 hAV] at h
  have hAll := card_le_card_sup_core hAab hJc hA1 hV1 hle
  unfold IsMaxElemAbelian
  refine ⟨hJS, hJ, fun B hBS hB => ?_⟩
  exact (hmax B hBS hB).trans hAll

theorem le_thompsonJ_of_relIndex_le [Finite G] {S A V : Subgroup G}
    (hA : IsMaxElemAbelian S A) (hV : IsElemAbelian 2 V) (hVS : V ≤ S)
    (hle : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤
      (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V) :
    V ≤ thompsonJ S := by
  have hmax := isMaxElemAbelian_sup_of_relIndex_le hA hV hVS hle
  unfold thompsonJ
  exact le_trans le_sup_right
    (le_iSup₂ (f := fun (B : Subgroup G) (_ : IsMaxElemAbelian S B) => B) _ hmax)

end CFSG.HardMathSupport.RichardWeiss.Proving
