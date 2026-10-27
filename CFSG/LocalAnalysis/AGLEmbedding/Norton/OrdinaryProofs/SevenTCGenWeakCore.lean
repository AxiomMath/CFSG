module

public import CFSG.Monster.Generated.Data
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.AGLEmbedding CFSG.Open CFSG.Monster.Generated

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem isElemAbelian_map_mulEquiv {p : ℕ} (e : X ≃* Y) {E : Subgroup X}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map e.toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem isElemAbelian_map_symm {p : ℕ} (e : X ≃* Y) {E : Subgroup Y}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map e.symm.toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem pRank_map_mulEquiv_open [Finite X] [Finite Y] (e : X ≃* Y) (p : ℕ) (H : Subgroup X) :
    CFSG.Open.pRank p (H.map e.toMonoidHom) = CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, hEH, hE, hc⟩
    refine ⟨E.map e.symm.toMonoidHom, ?_, isElemAbelian_map_symm e hE, ?_⟩
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp (hEH hy)
      simpa using hh
    · rw [Subgroup.card_map_of_injective e.symm.injective, hc]
  · rintro ⟨E, hEH, hE, hc⟩
    refine ⟨E.map e.toMonoidHom, Subgroup.map_mono hEH, isElemAbelian_map_mulEquiv e hE, ?_⟩
    rw [Subgroup.card_map_of_injective e.injective, hc]

theorem map_sup_inf_centralizer (e : X ≃* Y) (U P : Subgroup X) :
    (U ⊔ (P ⊓ Subgroup.centralizer (U : Set X))).map e.toMonoidHom =
      U.map e.toMonoidHom ⊔
        (P.map e.toMonoidHom ⊓ Subgroup.centralizer ((U.map e.toMonoidHom : Subgroup Y) : Set Y)) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sup_le ?_ ?_
    · intro u hu
      exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hu))
    · rintro x ⟨hxP, hxC⟩
      refine Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem _ hxP, ?_⟩))
      refine Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hh
      have := Subgroup.mem_centralizer_iff.mp hxC u hu
      simpa [map_mul] using congrArg e.toMonoidHom this
  · refine sup_le ?_ ?_
    · exact Subgroup.map_mono le_sup_left
    · rintro y ⟨hyP, hyC⟩
      obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.mp hyP
      refine Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_right (⟨hxP, ?_⟩ : x ∈ P ⊓ Subgroup.centralizer (U : Set X)))
      refine Subgroup.mem_centralizer_iff.mpr (fun u hu => ?_)
      have := Subgroup.mem_centralizer_iff.mp hyC (e.toMonoidHom u) (Subgroup.mem_map_of_mem _ hu)
      apply e.injective
      simpa [map_mul] using this

end Transport

theorem tcGenDatum_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (p : ℕ) [Fact p.Prime] (h : TCGenDatum X p) : TCGenDatum Y p := by
  obtain ⟨r, U, P, S, hP, hUP, hU, hS, hSU⟩ := h
  refine ⟨r, fun i => (U i).map e.toMonoidHom, P.map e.toMonoidHom,
    e.toMonoidHom '' S, ?_, fun i => Subgroup.map_mono (hUP i), ?_, ?_, ?_⟩
  · intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one, ← hxg, ← map_pow, h1, map_one]
  · intro i
    obtain ⟨h2, h3⟩ := hU i
    refine ⟨?_, ?_⟩
    · show 2 ≤ CFSG.Open.pRank p ((U i).map e.toMonoidHom)
      rw [pRank_map_mulEquiv_open e p]
      exact h2
    · show 3 ≤ CFSG.Open.pRank p ((U i).map e.toMonoidHom ⊔
        (P.map e.toMonoidHom ⊓ Subgroup.centralizer (((U i).map e.toMonoidHom : Subgroup Y) : Set Y)))
      rw [← map_sup_inf_centralizer e (U i) P, pRank_map_mulEquiv_open e p]
      exact h3
  · rw [← MonoidHom.map_closure, hS, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact e.surjective
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := hSU x hx
    refine ⟨i, ?_⟩
    show e x ∈ Subgroup.normalizer (((U i).map e.toMonoidHom : Subgroup Y) : Set Y)
    rw [Subgroup.mem_normalizer_iff] at hi ⊢
    intro h
    obtain ⟨h', rfl⟩ := e.surjective h
    have key := hi h'
    simp only [Subgroup.mem_map_equiv, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact key

theorem weakCore_seven_of_tcGen {T : Type} [Group T] [Finite T] [Finite ↥Gmat] [Fact (Nat.Prime 7)]
    (f : T ≃* ↥Gmat) (hTC : TCGenDatum ↥Gmat 7) (S : Sylow 7 T) :
    GLBWeakCore 7 (S : Subgroup T) = ⊤ :=
  weakCoreOfTC T 7 (tcGenDatum_of_mulEquiv f.symm 7 hTC) S

end CFSG.AGLEmbedding.Norton.OrdinaryProofs
