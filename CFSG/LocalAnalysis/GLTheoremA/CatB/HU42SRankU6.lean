module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42STorus
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.RankThree.PerfectCover.HopfCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S

open CFSG.Open CFSG.RankThree.PerfectCover

theorem elemAbelian_of_map_injective {Q S : Type} [Group Q] [Finite Q] [Group S] (π : Q →* S) (W : Subgroup Q)
    (hinj : Function.Injective (π.comp W.subtype)) (hE : IsElemAbelian 3 (W.map π)) :
    IsElemAbelian 3 W ∧ Nat.card W = Nat.card (W.map π) := by
  have hr : (π.comp W.subtype).range = W.map π := by
    ext x
    simp [MonoidHom.mem_range, Subgroup.mem_map]
  have hcard : Nat.card W = Nat.card (W.map π) := by
    rw [← hr]
    exact (card_range_of_injective' _ hinj).symm
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, hcard⟩
  · apply hinj
    have hcomm : (⟨π x.1, Subgroup.mem_map.2 ⟨x.1, x.2, rfl⟩⟩ : ↥(W.map π)) *
        ⟨π y.1, Subgroup.mem_map.2 ⟨y.1, y.2, rfl⟩⟩ =
        ⟨π y.1, Subgroup.mem_map.2 ⟨y.1, y.2, rfl⟩⟩ *
          ⟨π x.1, Subgroup.mem_map.2 ⟨x.1, x.2, rfl⟩⟩ :=
      hE.1.is_comm.comm _ _
    have key := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul] at key ⊢
    exact key
  · intro x hx
    have hw : (⟨x, hx⟩ : W) ^ 3 = 1 := by
      apply hinj
      have hpx : (π x) ^ 3 = 1 := hE.2 _ (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
      simpa [map_pow, map_one] using hpx
    have := congrArg Subtype.val hw
    simpa using this

theorem exists_elemAbelian_lift {Q S : Type} [Group Q] [Finite Q] [Group S] (p : Q →* S)
    (hp : Function.Surjective p) (hker : ¬ 3 ∣ Nat.card p.ker) {E : Subgroup S}
    (hE : IsElemAbelian 3 E) : ∃ W : Subgroup Q, IsElemAbelian 3 W ∧ Nat.card W = Nat.card E := by
  have hPE : IsPGroup 3 E := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 g.1 g.2⟩
  have hle : E ≤ p.range := by
    rw [MonoidHom.range_eq_top.2 hp]
    exact le_top
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨W, -, hWE, hinj⟩ := exists_pSubgroup_lift Nat.prime_three p hker hPE hle
  have hinj' : Function.Injective (p.comp W.subtype) := hinj
  have hE' : IsElemAbelian 3 (W.map p) := by rw [hWE]; exact hE
  obtain ⟨h1, h2⟩ := elemAbelian_of_map_injective p W hinj' hE'
  refine ⟨W, h1, ?_⟩
  rw [h2, hWE]

end CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S
