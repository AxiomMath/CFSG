module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128SplA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128CentPsi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsS8

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

namespace Sec128Coord

variable {M : Type} [Group M] {V1 : Subgroup M} {φ : (Fin 5 → ZMod 2) → M}

theorem map_zero (hc : Sec128Coord V1 φ) : φ 0 = 1 := by
  have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
  have h := hc.mul 0 0 h0 h0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem mul_self (hc : Sec128Coord V1 φ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    φ v * φ v = 1 := by
  have hsq : v + v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  rw [← hc.mul v v hv hv, hsq, hc.map_zero]

theorem eq_iff (hc : Sec128Coord V1 φ) {a b : Fin 5 → ZMod 2} (ha : IsEvenVec a)
    (hb : IsEvenVec b) : φ a = φ b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have hab : IsEvenVec (a + b) := by
    unfold IsEvenVec at *
    simp [Finset.sum_add_distrib, ha, hb]
  have h1 : φ (a + b) = 1 := by
    rw [hc.mul a b ha hb, h]
    exact hc.mul_self hb
  have h2 := hc.inj _ hab h1
  funext i
  have h3 := congrFun h2 i
  have key : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact key _ _ h3

end Sec128Coord

theorem sec128_moved : ∀ v : Fin 5 → ZMod 2, IsEvenVec v → v ≠ 0 →
    ∃ σ : Equiv.Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) ∧ permVec σ v ≠ v := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  unfold IsEvenVec permVec
  decide +kernel

theorem sec128_exists_even_ne : ∃ v : Fin 5 → ZMod 2, IsEvenVec v ∧ v ≠ 0 :=
  ⟨![1, 1, 0, 0, 0], by unfold IsEvenVec; decide, by decide⟩

theorem sec128_fixed_zero {v : Fin 5 → ZMod 2} (hv : IsEvenVec v)
    (h : ∀ a : Sec128A5, permVec (a : Equiv.Perm (Fin 5)) v = v) : v = 0 := by
  by_contra hne
  obtain ⟨σ, hσ, hmove⟩ := sec128_moved v hv hne
  exact hmove (h ⟨σ, hσ⟩)

theorem sec128_schur_side {M : Type} [Group M] {V1 : Subgroup M}
    {φ : (Fin 5 → ZMod 2) → M} (hφ : Sec128Coord V1 φ) (c : MulAut M)
    (hcV : ∀ u ∈ V1, c u ∈ V1)
    (hperm : ∀ σ ∈ alternatingGroup (Fin 5), ∃ s : MulAut M,
      (∀ v, IsEvenVec v → s (φ v) = φ (permVec σ v)) ∧ c * s = s * c) :
    ∀ u ∈ V1, c u = u := by
  classical
  have hex : ∀ w : EvW, ∃ v : EvW, φ v.1 = c (φ w.1) := fun w => by
    obtain ⟨v, hv, h⟩ := hφ.surj (c (φ w.1)) (hcV _ (hφ.mem _ w.2))
    exact ⟨⟨v, hv⟩, h⟩
  choose g hg using hex
  have hadd : ∀ w1 w2 : EvW, g (w1 + w2) = g w1 + g w2 := by
    intro w1 w2
    apply Subtype.ext
    refine (hφ.eq_iff (g (w1 + w2)).2 (g w1 + g w2).2).mp ?_
    have h1 : φ (g (w1 + w2)).1 = c (φ w1.1 * φ w2.1) := by
      rw [hg, show ((w1 + w2 : EvW) : Fin 5 → ZMod 2) = w1.1 + w2.1 from rfl,
        hφ.mul _ _ w1.2 w2.2]
    rw [h1, map_mul, ← hg w1, ← hg w2,
      show ((g w1 + g w2 : EvW) : Fin 5 → ZMod 2) = (g w1).1 + (g w2).1 from rfl,
      hφ.mul _ _ (g w1).2 (g w2).2]
  let gh : EvW →+ EvW := AddMonoidHom.mk' g hadd
  have hcomm : ∀ σ ∈ alternatingGroup (Fin 5), ∀ a, gh (permW σ a) = permW σ (gh a) := by
    intro σ hσ a
    obtain ⟨s, hs, hcs⟩ := hperm σ hσ
    have hcs' : ∀ x, c (s x) = s (c x) := fun x => congrArg (fun f : MulAut M => f x) hcs
    apply Subtype.ext
    refine (hφ.eq_iff (g (permW σ a)).2 (permW σ (g a)).2).mp ?_
    have h1 : φ (g (permW σ a)).1 = c (φ (permVec σ a.1)) := by
      rw [hg]
      rfl
    show φ (g (permW σ a)).1 = φ (permVec σ (g a).1)
    rw [h1, ← hs a.1 a.2, hcs', ← hg a, hs _ (g a).2]
  rcases sec128_schurW gh hcomm with h0 | h1
  · exfalso
    obtain ⟨v, hv, hv0⟩ := sec128_exists_even_ne
    have hz : g ⟨v, hv⟩ = 0 := DFunLike.congr_fun h0 ⟨v, hv⟩
    have h2 : c (φ v) = 1 := by
      rw [← hg ⟨v, hv⟩, hz]
      exact hφ.map_zero
    have h3 : φ v = 1 := c.injective (h2.trans (map_one c).symm)
    exact hv0 (hφ.inj v hv h3)
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := hφ.surj u hu
    have h2 : g ⟨v, hv⟩ = ⟨v, hv⟩ := DFunLike.congr_fun h1 ⟨v, hv⟩
    rw [← hg ⟨v, hv⟩, h2]

structure Sec128Spl {M : Type} [Group M] (ρ : Sec128A5 × Sec128A5 →* MulAut M)
    (V1 V2 : Subgroup M) (φ1 φ2 : (Fin 5 → ZMod 2) → M) : Prop where
  comm : ∀ x y : M, x * y = y * x
  inj : Function.Injective ρ
  sup : V1 ⊔ V2 = ⊤
  inf : V1 ⊓ V2 = ⊥
  c1 : Sec128Coord V1 φ1
  c2 : Sec128Coord V2 φ2
  act1 : ∀ (a b : Sec128A5) (v : Fin 5 → ZMod 2), IsEvenVec v →
    ρ (a, b) (φ1 v) = φ1 (permVec (a : Equiv.Perm (Fin 5)) v)
  act2 : ∀ (a b : Sec128A5) (v : Fin 5 → ZMod 2), IsEvenVec v →
    ρ (a, b) (φ2 v) = φ2 (permVec (b : Equiv.Perm (Fin 5)) v)

namespace Sec128Spl

variable {M : Type} [Group M] {ρ : Sec128A5 × Sec128A5 →* MulAut M} {V1 V2 : Subgroup M}
  {φ1 φ2 : (Fin 5 → ZMod 2) → M}

theorem decomp (h : Sec128Spl ρ V1 V2 φ1 φ2) (u : M) : ∃ x ∈ V1, ∃ y ∈ V2, u = x * y :=
  sec128_mem_sup (fun a _ b _ => h.comm a b) (h.sup ▸ Subgroup.mem_top u)

theorem fix1 (h : Sec128Spl ρ V1 V2 φ1 φ2) {u : M} (hu : ∀ a : Sec128A5, ρ (a, 1) u = u) :
    u ∈ V2 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h.decomp u
  obtain ⟨v, hv, rfl⟩ := h.c1.surj x hx
  obtain ⟨w, hw, rfl⟩ := h.c2.surj y hy
  have hv0 : v = 0 := by
    refine sec128_fixed_zero hv fun a => ?_
    have h1 := hu a
    rw [map_mul, h.act1 a 1 v hv, h.act2 a 1 w hw] at h1
    have h2 : φ1 (permVec (a : Equiv.Perm (Fin 5)) v) = φ1 v := by
      have h3 : permVec ((1 : Sec128A5) : Equiv.Perm (Fin 5)) w = w := rfl
      rw [h3] at h1
      exact mul_right_cancel h1
    exact (h.c1.eq_iff (sec128_isEven_permVec _ hv) hv).mp h2
  rw [hv0, h.c1.map_zero, one_mul]
  exact h.c2.mem w hw

theorem fix2 (h : Sec128Spl ρ V1 V2 φ1 φ2) {u : M} (hu : ∀ b : Sec128A5, ρ (1, b) u = u) :
    u ∈ V1 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h.decomp u
  obtain ⟨v, hv, rfl⟩ := h.c1.surj x hx
  obtain ⟨w, hw, rfl⟩ := h.c2.surj y hy
  have hw0 : w = 0 := by
    refine sec128_fixed_zero hw fun b => ?_
    have h1 := hu b
    rw [map_mul, h.act1 1 b v hv, h.act2 1 b w hw] at h1
    have h2 : φ2 (permVec (b : Equiv.Perm (Fin 5)) w) = φ2 w := by
      have h3 : permVec ((1 : Sec128A5) : Equiv.Perm (Fin 5)) v = v := rfl
      rw [h3] at h1
      exact mul_left_cancel h1
    exact (h.c2.eq_iff (sec128_isEven_permVec _ hw) hw).mp h2
  rw [hw0, h.c2.map_zero, mul_one]
  exact h.c1.mem v hv

theorem fixed1 (h : Sec128Spl ρ V1 V2 φ1 φ2) {u : M} (hu : u ∈ V2) (a : Sec128A5) :
    ρ (a, 1) u = u := by
  obtain ⟨w, hw, rfl⟩ := h.c2.surj u hu
  rw [h.act2 a 1 w hw]
  rfl

theorem fixed2 (h : Sec128Spl ρ V1 V2 φ1 φ2) {u : M} (hu : u ∈ V1) (b : Sec128A5) :
    ρ (1, b) u = u := by
  obtain ⟨v, hv, rfl⟩ := h.c1.surj u hu
  rw [h.act1 1 b v hv]
  rfl

theorem exists_ne_one2 (h : Sec128Spl ρ V1 V2 φ1 φ2) : ∃ u ∈ V2, u ≠ 1 := by
  obtain ⟨v, hv, hv0⟩ := sec128_exists_even_ne
  refine ⟨φ2 v, h.c2.mem v hv, fun h1 => hv0 (h.c2.inj v hv h1)⟩

theorem exists_ne_one1 (h : Sec128Spl ρ V1 V2 φ1 φ2) : ∃ u ∈ V1, u ≠ 1 := by
  obtain ⟨v, hv, hv0⟩ := sec128_exists_even_ne
  refine ⟨φ1 v, h.c1.mem v hv, fun h1 => hv0 (h.c1.inj v hv h1)⟩

theorem cent_one (h : Sec128Spl ρ V1 V2 φ1 φ2) {c : MulAut M} (hc : ∀ p, c * ρ p = ρ p * c) :
    c = 1 := by
  have hcomm : ∀ p u, c (ρ p u) = ρ p (c u) := fun p u =>
    congrArg (fun f : MulAut M => f u) (hc p)
  have hcV1 : ∀ u ∈ V1, c u ∈ V1 := fun u hu =>
    h.fix2 fun b => by rw [← hcomm, h.fixed2 hu]
  have hcV2 : ∀ u ∈ V2, c u ∈ V2 := fun u hu =>
    h.fix1 fun a => by rw [← hcomm, h.fixed1 hu]
  have h1 := sec128_schur_side h.c1 c hcV1
    (fun σ hσ => ⟨ρ (⟨σ, hσ⟩, 1), fun v hv => h.act1 _ _ v hv, hc _⟩)
  have h2 := sec128_schur_side h.c2 c hcV2
    (fun σ hσ => ⟨ρ (1, ⟨σ, hσ⟩), fun v hv => h.act2 _ _ v hv, hc _⟩)
  ext u
  obtain ⟨x, hx, y, hy, rfl⟩ := h.decomp u
  rw [map_mul, h1 x hx, h2 y hy]
  rfl

end Sec128Spl

theorem sec128_splitNatOn_spl {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAb2 V 8)
    {Z : Subgroup (MulAut ↥V)} {V1 V2 : Subgroup ↥V} (h : Sec128SplitNatOn V Z V1 V2) :
    ∃ (φ1 φ2 : (Fin 5 → ZMod 2) → ↥V) (ρ : Sec128A5 × Sec128A5 →* MulAut ↥V),
      Sec128Spl ρ V1 V2 φ1 φ2 ∧ ρ.range = Z := by
  obtain ⟨φ1, φ2, ψ, hsup, hinf, hc1, hc2, hact⟩ := h
  refine ⟨φ1, φ2, Z.subtype.comp ψ.toMonoidHom, ⟨?_, ?_, hsup, hinf, hc1, hc2,
    fun a b v hv => (hact a b v hv).1, fun a b v hv => (hact a b v hv).2⟩, ?_⟩
  · exact fun x y => Subtype.ext (hV.1.comm x.2 y.2)
  · exact Z.subtype_injective.comp ψ.injective
  · ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact (ψ p).2
    · intro hz
      exact ⟨ψ.symm ⟨z, hz⟩, by simp⟩

end CFSG.OddStandard.SmallF3.Omega
