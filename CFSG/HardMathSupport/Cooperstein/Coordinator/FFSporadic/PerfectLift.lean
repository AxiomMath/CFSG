module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PerfectCoreCover
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.AGLEmbedding CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family

theorem exists_hom_lift_of_kernelTrivialAt {G S F : Type} [Group G] [Finite G] [Group S] [Group F]
    [Finite F] [Group.IsPerfect F] {p : ℕ} (hF : KernelTrivialAt F p) (π : G →* S)
    (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center G) (hp : IsPGroup p π.ker)
    (ι : F →* S) : ∃ σ : F →* G, ∀ f, π (σ f) = ι f := by
  classical
  let P : Subgroup (G × F) :=
    (π.comp (MonoidHom.fst G F)).eqLocus (ι.comp (MonoidHom.snd G F))
  have hmem : ∀ g f, (g, f) ∈ P ↔ π g = ι f := fun g f => Iff.rfl
  let q : P →* F := (MonoidHom.snd G F).comp P.subtype
  have hq : Function.Surjective q := by
    intro f
    obtain ⟨g, hg⟩ := hπ (ι f)
    exact ⟨⟨(g, f), (hmem g f).2 hg⟩, rfl⟩
  obtain ⟨E, -, hEperf, hEmap⟩ := PerfectCoreCover.exists_perfect_normal_map_eq_top q hq
  let qE : E →* F := q.comp E.subtype
  have hqE : Function.Surjective qE := fun f => by
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 (hEmap ▸ Subgroup.mem_top f : f ∈ E.map q)
    exact ⟨⟨e, he⟩, rfl⟩
  have hkerπ : ∀ x : E, qE x = 1 → π ((x : P) : G × F).1 = 1 := by
    intro x hx
    have h1 : ((x : P) : G × F).2 = 1 := hx
    have h2 := ((x : P) : G × F).2
    have h3 : π ((x : P) : G × F).1 = ι ((x : P) : G × F).2 := (x : P).2
    rw [h3, h1, map_one]
  have hker : qE.ker = ⊥ := by
    refine @hF E _ _ hEperf qE hqE ?_ ?_
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hx1 : ((x : P) : G × F).2 = 1 := hx
      have hcent := Subgroup.mem_center_iff.1 (hc (MonoidHom.mem_ker.2 (hkerπ x hx)))
        ((y : P) : G × F).1
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact hcent
      · show ((y : P) : G × F).2 * ((x : P) : G × F).2 =
          ((x : P) : G × F).2 * ((y : P) : G × F).2
        rw [hx1, mul_one, one_mul]
    · intro x
      obtain ⟨k, hk⟩ := hp ⟨((x.1 : P) : G × F).1, MonoidHom.mem_ker.2 (hkerπ x.1 x.2)⟩
      refine ⟨k, ?_⟩
      have hx1 : ((x.1 : P) : G × F).2 = 1 := x.2
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val hk
      · show ((x.1 : P) : G × F).2 ^ p ^ k = 1
        rw [hx1, one_pow]
  have hinj : Function.Injective qE := (MonoidHom.ker_eq_bot_iff qE).1 hker
  let eqv : E ≃* F := MulEquiv.ofBijective qE ⟨hinj, hqE⟩
  refine ⟨(MonoidHom.fst G F).comp (P.subtype.comp (E.subtype.comp eqv.symm.toMonoidHom)),
    fun f => ?_⟩
  have h3 : π (((eqv.symm f : E) : P) : G × F).1 = ι (((eqv.symm f : E) : P) : G × F).2 :=
    ((eqv.symm f : E) : P).2
  have h4 : (((eqv.symm f : E) : P) : G × F).2 = f := by
    have := eqv.apply_symm_apply f
    exact this
  show π (((eqv.symm f : E) : P) : G × F).1 = ι f
  rw [h3, h4]

theorem two_pow_le_card_of_heisCfg_of_embedding {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} {S : Type} [Group S] (e : CQ L ≃* S)
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hZ : IsPGroup p (Subgroup.center ↥L))
    {F : Type} [Group F] [Finite F] [Group.IsPerfect F] (hF : KernelTrivialAt F p)
    (ι : F →* S) (hι : Function.Injective ι) {x y : Fin n → F} {z : F}
    (h : HeisCfg p n x y z) : 2 ^ (p ^ n * orderOf (2 : ZMod p)) ≤ Nat.card W := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hK := ker_centerQuotientHom e
  obtain ⟨σ, hσ⟩ := exists_hom_lift_of_kernelTrivialAt hF (centerQuotientHom e)
    (centerQuotientHom_surjective e) hK.le (hK ▸ hZ) ι
  have hz : σ z ≠ 1 := fun h1 => h.z1 (hι (by rw [← hσ, h1, map_one, map_one]))
  have hz' : L.subtype (σ z) ≠ 1 := fun h1 => hz (L.subtype_injective (by rw [h1, map_one]))
  have h2 := two_pow_le_card_imgT_of_heisCfg hW hp2 ((h.map σ hz).map L.subtype hz')
  exact h2.trans (Subgroup.card_le_card_group _)

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
