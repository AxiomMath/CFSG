module

public import CFSG.GroupTheory.SteinbergCBFTPSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
public import CFSG.GroupTheory.SteinbergCBFTSCN

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure

open CFSG.HallHigman CFSG.GroupTheory.FT63ChII

theorem isPSolvable_of_le {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    {N Y : Subgroup X} (hN : CFSG.HallHigman.IsPSolvable p ↥N) (hYN : Y ≤ N) :
    CFSG.HallHigman.IsPSolvable p ↥Y := by
  have hsep : IsPiSeparable {q : Nat.Primes | q.val = p} ↥N :=
    isPiSeparable_of_isPSolvable (Fact.out) hN
  have hsub : IsPSolvable p ↥(Y.subgroupOf N) :=
    isPSolvable_of_isPiSeparable (hsep.subgroup (Y.subgroupOf N))
  exact QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hYN) hsub

theorem isPSolvable_map {p : ℕ} [Fact p.Prime] {X W : Type} [Group X] [Group W] [Finite X]
    (f : X →* W) {N : Subgroup X} (hN : CFSG.HallHigman.IsPSolvable p ↥N) :
    CFSG.HallHigman.IsPSolvable p ↥(N.map f) := by
  set φ : ↥N →* W := f.comp N.subtype with hφ
  have hr : φ.range = N.map f := by
    ext x
    simp [hφ, MonoidHom.mem_range, Subgroup.mem_map]
  have hsep : IsPiSeparable {q : Nat.Primes | q.val = p} ↥N :=
    isPiSeparable_of_isPSolvable (Fact.out) hN
  have hQ : CFSG.HallHigman.IsPSolvable p (↥N ⧸ φ.ker) :=
    isPSolvable_of_isPiSeparable (hsep.quotient φ.ker)
  have hE : CFSG.HallHigman.IsPSolvable p ↥φ.range :=
    QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv (QuotientGroup.quotientKerEquivRange φ) hQ
  rw [← hr]
  exact hE

theorem transfer_ker_index {A Q : Type} [Group A] [Group Q] [IsSimpleGroup Q] (ψ : A →* Q)
    (hψ : Function.Surjective ψ) :
    IsSimpleGroup (A ⧸ ψ.ker) ∧ ψ.ker.index = Nat.card Q :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).isSimpleGroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv⟩

theorem isPSolvable_of_normal {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    (N : Subgroup X) [N.Normal] (hN : IsPSolvable p ↥N)
    (hQ : IsPSolvable p (X ⧸ N)) : IsPSolvable p X := by
  intro H hH T hT hs
  have := hs
  have hMn : ((N.subgroupOf H).map (QuotientGroup.mk' T)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective T)
  by_cases hM : (N.subgroupOf H).map (QuotientGroup.mk' T) = ⊥
  ·
    have hKT : N.subgroupOf H ≤ T := by
      intro k hk
      have hmem : QuotientGroup.mk' T k ∈ (⊥ : Subgroup (H ⧸ T)) := by
        rw [← hM]; exact Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hmem
    let S : Subgroup (X ⧸ N) := H.map (QuotientGroup.mk' N)
    have hS : S.IsSubnormal := hH.map (QuotientGroup.mk'_surjective N)
    let φ : H →* S := MonoidHom.codRestrict ((QuotientGroup.mk' N).comp H.subtype) S
      (fun h => Subgroup.mem_map.mpr ⟨h, h.2, rfl⟩)
    have hφ : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨h, hh⟩, Subtype.ext rfl⟩
    have hker : φ.ker ≤ T := by
      intro k hk
      have hk1 : (QuotientGroup.mk' N) (k : X) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
      exact hKT (Subgroup.mem_subgroupOf.mpr ((QuotientGroup.eq_one_iff _).mp hk1))
    let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
    let ψ : S →* H ⧸ T :=
      (QuotientGroup.map φ.ker T (MonoidHom.id H) hker).comp e.symm.toMonoidHom
    have hψ : Function.Surjective ψ := by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨e (QuotientGroup.mk h), ?_⟩
      show (QuotientGroup.map φ.ker T (MonoidHom.id H) hker) (e.symm (e (QuotientGroup.mk h)))
        = QuotientGroup.mk h
      rw [MulEquiv.symm_apply_apply]
      rfl
    obtain ⟨hsimp, hidx⟩ := transfer_ker_index ψ hψ
    have key := hQ S hS ψ.ker hsimp
    have hT' : ψ.ker.index = T.index := hidx
    rw [hT'] at key
    exact key
  ·
    have hM' : (N.subgroupOf H).map (QuotientGroup.mk' T) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf H).map (QuotientGroup.mk' T)) with h | h
      · exact absurd h hM
      · exact h
    let f : ↥(H.subgroupOf N) →* H :=
      { toFun := fun x => ⟨(x.1 : X), Subgroup.mem_subgroupOf.mp x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    let ψ : ↥(H.subgroupOf N) →* H ⧸ T := (QuotientGroup.mk' T).comp f
    have hψ : Function.Surjective ψ := by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      have hmem : QuotientGroup.mk' T h ∈ (N.subgroupOf H).map (QuotientGroup.mk' T) := by
        rw [hM']; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkh⟩ := Subgroup.mem_map.mp hmem
      refine ⟨⟨⟨(k : X), Subgroup.mem_subgroupOf.mp hk⟩, Subgroup.mem_subgroupOf.mpr k.2⟩, ?_⟩
      exact hkh
    obtain ⟨hsimp, hidx⟩ := transfer_ker_index ψ hψ
    have hA : (H.subgroupOf N).IsSubnormal := hH.subgroupOf
    have key := hN (H.subgroupOf N) hA ψ.ker hsimp
    have hT' : ψ.ker.index = T.index := hidx
    rw [hT'] at key
    exact key

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
