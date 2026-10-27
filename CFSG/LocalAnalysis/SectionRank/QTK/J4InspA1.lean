module

public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.SectionRank.QTK

open CFSG.OrderReductions.FrattiniAutomorphisms

section Frattini

variable {L : Type} [Group L] [Finite L] (Q : Subgroup L) [Q.Normal]

noncomputable def frattiniConjAct : L →* MulAut (↥Q ⧸ frattini ↥Q) :=
  (quotientAutomorphism (frattini ↥Q)).comp (MulAut.conjNormal (H := Q))

theorem frattiniConjAct_mk (x : L) (q : ↥Q) :
    frattiniConjAct Q x (QuotientGroup.mk' (frattini ↥Q) q) =
      QuotientGroup.mk' (frattini ↥Q) (MulAut.conjNormal (H := Q) x q) := by
  unfold frattiniConjAct
  rw [MonoidHom.comp_apply, quotientAutomorphism_apply]

theorem frattiniConjAct_of_mem (hQ : IsPGroup 2 ↥Q) (q : Q) :
    frattiniConjAct Q (q : L) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : IsMulCommutative (↥Q ⧸ frattini ↥Q) :=
    (CFSG.GroupTheory.frattini_elementary_quotient (p := 2) (P := ↥Q) hQ).2.1
  refine MulEquiv.ext fun v => ?_
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥Q) v
  have hc : QuotientGroup.mk' (frattini ↥Q) q * QuotientGroup.mk' (frattini ↥Q) r =
      QuotientGroup.mk' (frattini ↥Q) r * QuotientGroup.mk' (frattini ↥Q) q :=
    hcomm.is_comm.comm _ _
  have hconj : MulAut.conjNormal (H := Q) (q : L) r = q * r * q⁻¹ := by
    apply Subtype.ext
    simp [MulAut.conjNormal_apply]
  have key : QuotientGroup.mk' (frattini ↥Q) (MulAut.conjNormal (H := Q) (q : L) r) =
      QuotientGroup.mk' (frattini ↥Q) r := by
    rw [hconj, map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
  show frattiniConjAct Q (q : L) (QuotientGroup.mk' (frattini ↥Q) r) =
    QuotientGroup.mk' (frattini ↥Q) r
  rw [frattiniConjAct_mk]
  exact key

theorem eq_one_of_perfect_isPGroup {G : Type} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) : ∀ g : G, g = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent G := hG.isNilpotent
  intro g
  rcases subsingleton_or_nontrivial G with h | hnt'
  · exact Subsingleton.elim g 1
  · exfalso
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := G)
    have hc : _root_.commutator G = ⊤ := hperf
    rw [hc] at hlt
    exact lt_irrefl _ hlt

theorem commutator_eq_top_of_surjective {L G : Type} [Group L] [Group G] (f : L →* G)
    (hsurj : Function.Surjective f) (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
  have hgtop : (⊤ : Subgroup G) = (⊤ : Subgroup L).map f := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hsurj]
  calc ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
      = ⁅(⊤ : Subgroup L).map f, (⊤ : Subgroup L).map f⁆ := by
        rw [← hgtop]
    _ = (⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆).map f :=
        (Subgroup.map_commutator (⊤ : Subgroup L) (⊤ : Subgroup L) f).symm
    _ = (⊤ : Subgroup L).map f := by rw [hperf]
    _ = ⊤ := hgtop.symm

theorem frattini_kernel_le (hQ : IsPGroup 2 ↥Q)
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤)
    (hsimp : IsSimpleGroup (L ⧸ Q)) (hnt : ⁅Q, (⊤ : Subgroup L)⁆ ≠ ⊥) :
    ∀ x : L, frattiniConjAct Q x = 1 → x ∈ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hsimp
  haveI : Finite (MulAut ↥Q) :=
    Finite.of_injective (fun g : MulAut ↥Q => (g : ↥Q → ↥Q))
      fun g h hgh => MulEquiv.ext (congrFun hgh)
  have hQC : Q ≤ (frattiniConjAct Q).ker := by
    intro q hq
    exact MonoidHom.mem_ker.mpr (frattiniConjAct_of_mem Q hQ ⟨q, hq⟩)
  have hCmap : ((frattiniConjAct Q).ker.map (QuotientGroup.mk' Q)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Q)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((frattiniConjAct Q).ker.map (QuotientGroup.mk' Q)) with hbot | htop
  ·
    intro x hx
    have hxC : x ∈ (frattiniConjAct Q).ker := MonoidHom.mem_ker.mpr hx
    have hmem : QuotientGroup.mk' Q x ∈ (frattiniConjAct Q).ker.map (QuotientGroup.mk' Q) :=
      Subgroup.mem_map_of_mem _ hxC
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  · exfalso
    have hCtop : (frattiniConjAct Q).ker = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : QuotientGroup.mk' Q y ∈ (frattiniConjAct Q).ker.map (QuotientGroup.mk' Q) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
      have h1 : c⁻¹ * y ∈ Q := QuotientGroup.eq.mp hcy
      have h2 : c * (c⁻¹ * y) ∈ (frattiniConjAct Q).ker := (frattiniConjAct Q).ker.mul_mem hc (hQC h1)
      simpa using h2
    have hall : ∀ y : L, frattiniConjAct Q y = 1 := by
      intro y
      have hy : y ∈ (frattiniConjAct Q).ker := by
        rw [hCtop]
        exact Subgroup.mem_top y
      exact MonoidHom.mem_ker.mp hy
    have hK := (CFSG.GroupTheory.frattini_automorphism_kernel (p := 2) (P := ↥Q) hQ).2
    have hmemK : ∀ y : L, MulAut.conjNormal (H := Q) y ∈
        (quotientAutomorphism (frattini ↥Q)).ker := fun y => hall y
    have hHp : IsPGroup 2 ↥(MulAut.conjNormal (H := Q)).range := by
      intro h
      obtain ⟨g, ⟨y, rfl⟩⟩ := h
      obtain ⟨k, hk⟩ := hK ⟨MulAut.conjNormal (H := Q) y, hmemK y⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    have hone := eq_one_of_perfect_isPGroup hHp
      (commutator_eq_top_of_surjective (MulAut.conjNormal (H := Q)).rangeRestrict
        (MonoidHom.rangeRestrict_surjective _) hperf)
    have hf1 : ∀ y : L, MulAut.conjNormal (H := Q) y = 1 := fun y =>
      congrArg Subtype.val (hone ⟨MulAut.conjNormal (H := Q) y, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩)
    apply hnt
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ _
    rw [Subgroup.mem_bot]
    have hact := congrArg (fun z : MulAut ↥Q => (z ⟨g₁, hg₁⟩ : ↥Q)) (hf1 g₂)
    have hcg : g₂ * g₁ * g₂⁻¹ = g₁ := by
      have := congrArg Subtype.val hact
      simpa [MulAut.conjNormal_apply] using this
    have hcomm' : Commute g₁ g₂ := (mul_inv_eq_iff_eq_mul.mp hcg).symm
    exact commutatorElement_eq_one_iff_commute.mpr hcomm'

end Frattini

end CFSG.SectionRank.QTK
