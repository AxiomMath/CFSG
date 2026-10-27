module

public import CFSG.ClassicalInvolution.Q3.TL4S289Kind2
public import CFSG.ClassicalInvolution.Q3.TL4VtxMain
public import CFSG.ClassicalInvolution.Q3.TL4OddMu9F

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance

namespace S289

theorem mem_of_map_mem {Q Z : Type} [Group Q] [Group Z] {N L : Subgroup Q} (e : ↥N ≃* Z)
    {x : Q} (hx : x ∈ N) (h : e ⟨x, hx⟩ ∈ (L.subgroupOf N).map e.toMonoidHom) : x ∈ L := by
  obtain ⟨y, hy, hyx⟩ := h
  have e1 : y = ⟨x, hx⟩ := e.injective hyx
  have h1 := Subgroup.mem_subgroupOf.mp hy
  rwa [e1] at h1

theorem normal_of_simple_quot {X : Type} [Group X] [Finite X]
    (hS : IsSimpleGroup (X ⧸ Subgroup.center X)) {C : Subgroup X} (hC : IsComponent C) :
    C.Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨c, hc, hz⟩ := exists_mul_center_of_simple_quot hS hC g
  have hzx : (c⁻¹ * g) * x = x * (c⁻¹ * g) := (Subgroup.mem_center_iff.mp hz x).symm
  have e : g * x * g⁻¹ = c * x * c⁻¹ := by
    calc g * x * g⁻¹ = c * ((c⁻¹ * g) * x) * (c⁻¹ * g)⁻¹ * c⁻¹ := by group
      _ = c * x * c⁻¹ := by rw [hzx]; group
  rw [e]
  exact C.mul_mem (C.mul_mem hc hx) (C.inv_mem hc)

variable {G : Type} [Group G] [Finite G] {t u w : G}

omit [Finite G] in
theorem mul_self_of_mem_modOdd {B : Subgroup G} (hB : IsElemAbelian 2 B) :
    ∀ x ∈ modOdd t B, x * x = 1 := by
  rintro _ ⟨k, hk, rfl⟩
  have hkk : k * k = 1 :=
    Subtype.ext ((sq (k : G)).symm.trans (hB.2 _ (Subgroup.mem_subgroupOf.mp hk)))
  rw [← map_mul, hkk, map_one]

section Cit3


theorem inner_of_frame (hB : IsElemAbelian 2 (Subgroup.closure ({t, u, w} : Set G)))
    (hutC : u ∈ Subgroup.centralizer ({t} : Set G))
    (hwtC : w ∈ Subgroup.centralizer ({t} : Set G)) {L : Subgroup (OddQuot t)}
    (huL : oddQuotMk t ⟨u, hutC⟩ ∈ L) (hwL : oddQuotMk t ⟨w, hwtC⟩ ∈ L) :
    ∀ x ∈ inducedImage L (modOdd t (Subgroup.closure ({t, u, w} : Set G))),
      ((x : ↥(inducedAutOn L)) : MulAut ↥L) ∈ Q3NM.innSubgroup ↥L := by
  have hset : Subgroup.closure ({t, u, w} : Set G) = Subgroup.closure ({u, w, t} : Set G) := by
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rintro _ ⟨v, hv, rfl⟩
  have hv' : (v : OddQuot t) ∈ modOdd t (Subgroup.closure ({t, u, w} : Set G)) := hv
  obtain ⟨d, hd, hdC, e, he, hve⟩ :=
    Q3CH.exists_mul_central_of_mem_modOdd (hset ▸ hB) hset hv'
  have hdL : oddQuotMk t ⟨d, hdC⟩ ∈ L := by
    rcases hd with rfl | rfl | rfl | rfl
    · rw [show (⟨1, hdC⟩ : ↥(Subgroup.centralizer ({t} : Set G))) = 1 from rfl, map_one]
      exact L.one_mem
    · exact huL
    · exact hwL
    · rw [show (⟨u * w, hdC⟩ : ↥(Subgroup.centralizer ({t} : Set G))) = ⟨u, hutC⟩ * ⟨w, hwtC⟩
        from rfl, map_mul]
      exact L.mul_mem huL hwL
  exact ⟨⟨_, hdL⟩, (Q3CH.conjOnNormalizer_eq_conj v hdL he hve).symm⟩

end Cit3

theorem natCard_inducedImage_eq_four (hB : IsElemAbelian 2 (Subgroup.closure ({t, u, w} : Set G)))
    (hutC : u ∈ Subgroup.centralizer ({t} : Set G))
    (hwtC : w ∈ Subgroup.centralizer ({t} : Set G)) {L : Subgroup (OddQuot t)}
    (huL : oddQuotMk t ⟨u, hutC⟩ ∈ L) (hwL : oddQuotMk t ⟨w, hwtC⟩ ∈ L)
    (hmu : ∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * y ≠ y * oddQuotMk t ⟨u, hutC⟩)
    (hmw : ∃ y ∈ L, oddQuotMk t ⟨w, hwtC⟩ * y ≠ y * oddQuotMk t ⟨w, hwtC⟩)
    (hmuw : ∃ y ∈ L, oddQuotMk t ⟨u, hutC⟩ * oddQuotMk t ⟨w, hwtC⟩ * y ≠
      y * (oddQuotMk t ⟨u, hutC⟩ * oddQuotMk t ⟨w, hwtC⟩)) :
    Nat.card ↥(inducedImage L (modOdd t (Subgroup.closure ({t, u, w} : Set G)))) = 4 := by
  have hfin : Finite (MulAut ↥L) :=
    Finite.of_injective (fun α : MulAut ↥L => (α : ↥L → ↥L)) fun _ _ e => MulEquiv.ext (congrFun e)
  have hset : Subgroup.closure ({t, u, w} : Set G) = Subgroup.closure ({u, w, t} : Set G) := by
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have huN := Subgroup.le_normalizer huL
  have hwN := Subgroup.le_normalizer hwL
  rw [hset, Vtx.inducedImage_modOdd_eq hutC hwtC huN hwN]
  have hsq : ∀ (x : G) (hx : x ∈ Subgroup.closure ({t, u, w} : Set G))
      (hxC : x ∈ Subgroup.centralizer ({t} : Set G))
      (hxN : oddQuotMk t ⟨x, hxC⟩ ∈ Subgroup.normalizer (L : Set (OddQuot t))),
      toInducedAutOn L ⟨_, hxN⟩ * toInducedAutOn L ⟨_, hxN⟩ = 1 := by
    intro x hx hxC hxN
    rw [← map_mul]
    have h1 : (⟨_, hxN⟩ * ⟨_, hxN⟩ : ↥(Subgroup.normalizer (L : Set (OddQuot t)))) = 1 :=
      Subtype.ext (mul_self_of_mem_modOdd hB _ (oddQuotMk_mem_modOdd hx hxC))
    rw [h1, map_one]
  have hm3 := mem_closure_three_left t u w
  obtain ⟨yu, hyu, hneu⟩ := hmu
  obtain ⟨yw, hyw, hnew⟩ := hmw
  obtain ⟨yuw, hyuw, hneuw⟩ := hmuw
  have h1u := Lemma52Proof.toInducedAutOn_ne_one_of_moved L huN hyu hneu
  have h1w := Lemma52Proof.toInducedAutOn_ne_one_of_moved L hwN hyw hnew
  have hne : toInducedAutOn L ⟨_, huN⟩ ≠ toInducedAutOn L ⟨_, hwN⟩ := by
    intro heq
    have huwN := Subgroup.le_normalizer (L.mul_mem huL hwL)
    apply Lemma52Proof.toInducedAutOn_ne_one_of_moved L huwN hyuw hneuw
    have e1 : (⟨_, huwN⟩ : ↥(Subgroup.normalizer (L : Set (OddQuot t)))) = ⟨_, huN⟩ * ⟨_, hwN⟩ :=
      rfl
    rw [e1, map_mul, heq]
    exact hsq w hm3.2.2 hwtC hwN
  have hcomm : toInducedAutOn L ⟨_, huN⟩ * toInducedAutOn L ⟨_, hwN⟩ =
      toInducedAutOn L ⟨_, hwN⟩ * toInducedAutOn L ⟨_, huN⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show oddQuotMk t ⟨u, hutC⟩ * oddQuotMk t ⟨w, hwtC⟩ =
      oddQuotMk t ⟨w, hwtC⟩ * oddQuotMk t ⟨u, hutC⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (DeltaClosure.comm_of_mem_elemAbelian hB hm3.2.1 hm3.2.2)
  exact Bootstrap.card_closure_pair_eq_four (hsq u hm3.2.1 hutC huN) (hsq w hm3.2.2 hwtC hwN)
    h1u h1w hne hcomm

end S289

end CFSG.ClassicalInvolution.Q3.TL4
