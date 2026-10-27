module

public import CFSG.Quasithin.Background.SmithCurtisBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin CFSG.Quasithin.SmithCurtis CFSG.QuasithinUnique.Setup

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [CommGroup V]

@[expose] noncomputable def zmodTwoEquiv (hK : Nat.card K = 2) : ZMod 2 ≃+* K :=
  RingEquiv.ofBijective (ZMod.castHom (dvd_refl 2) K)
    ((ZMod.castHom (dvd_refl 2) K).injective.bijective_of_nat_card_le (by rw [hK, Nat.card_zmod]))

noncomputable abbrev binModule (hK : Nat.card K = 2) (hV : ∀ v : V, v * v = 1) :
    Module K (Additive V) :=
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun v => by
    rw [two_nsmul]; exact hV (Additive.toMul v)
  Module.compHom (Additive V) (zmodTwoEquiv hK).symm.toRingHom

@[expose] noncomputable def binRep (hK : Nat.card K = 2) (hV : ∀ v : V, v * v = 1) {G : Type*}
    [Group G] (ι : G →* MulAut V) :
    letI := binModule hK hV; Representation K G (Additive V) :=
  letI := binModule hK hV
  { toFun := fun g =>
      { toFun := fun v => Additive.ofMul (ι g (Additive.toMul v))
        map_add' := fun v w => by simp
        map_smul' := fun c v => by
          obtain ⟨a, rfl⟩ := (zmodTwoEquiv hK).surjective c
          rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a with rfl | rfl
          · rw [map_zero, zero_smul, RingHom.id_apply, zero_smul, toMul_zero, map_one, ofMul_one]
          · rw [map_one, one_smul, RingHom.id_apply, one_smul] }
    map_one' := by ext v; simp
    map_mul' := fun g h => by ext v; simp }

theorem binRep_apply (hK : Nat.card K = 2) (hV : ∀ v : V, v * v = 1) {G : Type*} [Group G]
    (ι : G →* MulAut V) (g : G) (v : V) :
    binRep hK hV ι g (Additive.ofMul v) = Additive.ofMul (ι g v) :=
  rfl

theorem isSimpleRep_binRep [Finite V] (hK : Nat.card K = 2) (hV : ∀ v : V, v * v = 1)
    {G : Type*} [Group G] (ι : G →* MulAut V) {L : Subgroup (MulAut V)} (hirr : X1.IsIrrOn L)
    (hι : ∀ l ∈ L, ∃ g, ι g = l) :
    letI := binModule hK hV; IsSimpleRep (binRep hK hV ι) := by
  let := binModule hK hV
  have := hirr.1
  refine ⟨Additive.instNontrivial, ?_⟩
  intro W hW
  let U : Subgroup V :=
    { carrier := {v | Additive.ofMul v ∈ W}
      one_mem' := by
        show Additive.ofMul (1 : V) ∈ W
        exact W.zero_mem
      mul_mem' := by
        intro a b ha hb
        exact W.add_mem ha hb
      inv_mem' := by
        intro a ha
        exact W.neg_mem ha }
  have hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U := by
    intro l hl u hu
    obtain ⟨g, hg⟩ := hι l hl
    show Additive.ofMul (l u) ∈ W
    rw [← hg]
    rw [← binRep_apply hK hV ι g u]
    exact hW g _ hu
  rcases hirr.2 U hU with hUbot | hUtop
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxU : Additive.toMul x ∈ U := by
      show Additive.ofMul (Additive.ofMul.symm x) ∈ W
      rw [Equiv.apply_symm_apply]
      exact hx
    rw [hUbot] at hxU
    have hx1 : Additive.ofMul.symm x = 1 := Subgroup.mem_bot.mp hxU
    calc x = Additive.ofMul (Additive.ofMul.symm x) :=
          (Equiv.apply_symm_apply (Additive.ofMul) x).symm
      _ = Additive.ofMul 1 := by rw [hx1]
      _ = 0 := rfl
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have hxU : Additive.ofMul.symm x ∈ U := by
      rw [hUtop]
      exact Subgroup.mem_top _
    rw [← Equiv.apply_symm_apply (Additive.ofMul) x]
    exact hxU

theorem card_eq_card_fix_mul_two_pow [Finite V] (hK : Nat.card K = 2) (hV : ∀ v : V, v * v = 1)
    {G : Type*} [Group G] (ι : G →* MulAut V) (g : G) :
    letI := binModule hK hV
    Nat.card V = Nat.card {v : V // ι g v = v} *
      2 ^ Module.finrank K (LinearMap.range (binRep hK hV ι g - 1)) := by
  let := binModule hK hV
  let f : Module.End K (Additive V) := binRep hK hV ι g - 1
  have hf : ∀ v : V, f (Additive.ofMul v) = Additive.ofMul (ι g v) - Additive.ofMul v := by
    intro v
    simp only [f, LinearMap.sub_apply, Module.End.one_apply, binRep_apply]
  have hker : Nat.card (LinearMap.ker f) = Nat.card {v : V // ι g v = v} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨Additive.ofMul.symm x.1, ?_⟩
        invFun := fun y => ⟨Additive.ofMul y.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx : f (Additive.ofMul (Additive.ofMul.symm x.1)) = 0 := by
        rw [Equiv.apply_symm_apply]
        exact LinearMap.mem_ker.mp x.2
      rw [hf, sub_eq_zero] at hx
      exact (Additive.ofMul).injective hx
    · rw [LinearMap.mem_ker, hf, y.2, sub_self]
    · intro x
      ext
      exact Equiv.apply_symm_apply (Additive.ofMul) x.1
    · intro y
      ext
      exact Equiv.symm_apply_apply (Additive.ofMul) y.1
  have hrange : Nat.card (LinearMap.range f) = 2 ^ Module.finrank K (LinearMap.range f) := by
    have : Module.Finite K (LinearMap.range f) := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range f), hK]
  have hquot : Nat.card (Additive V ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr (LinearMap.quotKerEquivRange f).toEquiv
  calc Nat.card V = Nat.card (Additive V) := rfl
    _ = Nat.card (LinearMap.ker f) * Nat.card (Additive V ⧸ LinearMap.ker f) :=
        Submodule.card_eq_card_quotient_mul_card _
    _ = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by rw [hquot]
    _ = Nat.card {v : V // ι g v = v} * 2 ^ Module.finrank K (LinearMap.range f) := by
        rw [hker, hrange]

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
