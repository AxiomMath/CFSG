module

public import CFSG.GH74.GLS.Stage1.Main.BrPair

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final
open scoped commutatorElement

theorem exists_term7_model {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {q : ℕ}
    {w : G} (hodd : Odd q) (h5 : 5 ≤ q) (hK₁ : HatSL2 K₁ q) (hT7 : Term7 z S K₁ K₂ q w) :
    ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs) (z' t' w' : Gs) (S' : Sylow 2 Gs)
      (E₁ E₂ : Subgroup Gs),
      orderOf z' = 2 ∧ (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' ∧
      z' ∈ (S' : Subgroup Gs) ∧ (∀ x ∈ (S' : Subgroup Gs), x * z' = z' * x) ∧
      Compat7 z (K₁ ⊔ K₂ ⊔ S) S (IVK.Ez z') (S' : Subgroup Gs) ∧
      Dat410 q z' (S' : Subgroup Gs) t' w' E₁ E₂ ∧ (w' = 1 ↔ w = 1) := by
  obtain ⟨F, iF, fF, hFq, -⟩ := id hK₁
  obtain ⟨Gs, iGs, fGs, p, f, hGs, hmod⟩ := exists_model7 hodd h5 (w = 1) hFq
  obtain ⟨S'⟩ : Nonempty (Sylow 2 Gs) := inferInstance
  obtain ⟨z', hz'o, hcenS'⟩ := modelCenter Gs p f hGs S'
  have hC := hT7 Gs z' S' hmod hz'o hcenS'
  have hSp : IVK.IsSp4L4U4 Gs q := by
    rcases hmod with ⟨-, hP⟩ | ⟨-, hLU⟩
    · exact Or.inl hP
    · exact Or.inr hLU
  have hz'mem : z' ∈ ((center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype) := by
    rw [hcenS']
    exact mem_zpowers z'
  obtain ⟨c, hc', hcz⟩ := hz'mem
  have hcz' : (c : Gs) = z' := hcz
  have hz'S' : z' ∈ (S' : Subgroup Gs) := hcz' ▸ c.2
  have hz'c : ∀ x ∈ (S' : Subgroup Gs), x * z' = z' * x := by
    intro x hx
    have := Subgroup.mem_center_iff.1 hc' ⟨x, hx⟩
    rw [← hcz']
    exact congrArg Subtype.val this
  obtain ⟨t', w', E₁, E₂, ht'S, hw'S, ht'o, hw'o, hcomm', hprod', hinter', ht'c, hEz, hE₂, hsl2,
      hinterE, hcommE, hnormE, hw1iff, hcls, htzne, hEfus, hpgl, hwfus, -⟩ :=
    ivk_4_10 Gs q hodd h5 hSp S' z' hz'S' hz'o hz'c
  have hdat : Dat410 q z' (S' : Subgroup Gs) t' w' E₁ E₂ :=
    ⟨ht'S, hw'S, ht'o, hw'o, hcomm'.eq, hprod', hinter', ht'c, hEz, hE₂, hsl2, hinterE, hcommE,
      hnormE, hcls, htzne, hEfus, hpgl, hwfus⟩
  have hww : w' = 1 ↔ w = 1 := by
    rcases hmod with ⟨hw1, hP⟩ | ⟨hw1, hLU⟩
    · exact ⟨fun _ => hw1, fun _ => hw1iff.2 hP⟩
    · have hnP : ¬IVK.IsPSp4 Gs q := fun hP => by
        rcases hLU with ⟨-, hl⟩ | ⟨-, hl⟩
        · exact (ivk_PSp4_ne_LU Gs q hP).1 hl
        · exact (ivk_PSp4_ne_LU Gs q hP).2 hl
      exact ⟨fun h1 => absurd (hw1iff.1 h1) hnP, fun h1 => absurd h1 hw1⟩
  exact ⟨Gs, iGs, fGs, z', t', w', S', E₁, E₂, hz'o, hcenS', hz'S', hz'c, hC, hdat, hww⟩

theorem eq_one_of_mem_pgroup_oddCore {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hS : IsPGroup 2 ↥S) {s : G} (hs : s ∈ S) (hz : s ∈ Oz z) : s = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have h1 : s ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hd : orderOf s ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have ho : orderOf s ∣ Nat.card ↥(Oz z) := Subgroup.orderOf_dvd_natCard (Oz z) hz
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(Oz z)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 card_Oz_odd)
  have h2 : Nat.Coprime (orderOf s) (orderOf s) :=
    Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.coprime_dvd_right ho hcop)
  exact orderOf_eq_one_iff.1 (Nat.coprime_self _ |>.1 h2)

theorem exists_equiv_of_compat {G : Type} [Group G] {z : G} {X S : Subgroup G} (hSX : S ≤ X)
    (hS : ∀ s ∈ S, s ∈ Oz z → s = 1) {Gs : Type} [Group Gs] {E S' : Subgroup Gs}
    (hcompat : Compat7 z X S E S') : Nonempty (↥S ≃* ↥S') := by
  obtain ⟨hN, ψ, hψS, hψS', -⟩ := hcompat
  let g : ↥S →* ↥(E ⊔ S') :=
    ψ.toMonoidHom.comp ((QuotientGroup.mk' ((Oz z).subgroupOf X)).comp (Subgroup.inclusion hSX))
  have hgS : ∀ s : ↥S, (g s : Gs) ∈ S' := fun s => hψS ⟨(s : G), hSX s.2⟩ s.2
  let f : ↥S →* ↥S' :=
    { toFun := fun s => ⟨(g s : Gs), hgS s⟩
      map_one' := Subtype.ext (by
        show ((g 1 : ↥(E ⊔ S')) : Gs) = 1
        rw [map_one]
        rfl)
      map_mul' := fun x y => Subtype.ext (by
        show ((g (x * y) : ↥(E ⊔ S')) : Gs) = (g x : Gs) * (g y : Gs)
        rw [map_mul]
        rfl) }
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : g x = g y := Subtype.ext
      (show ((g x : ↥(E ⊔ S')) : Gs) = (g y : Gs) from congrArg (fun u : ↥S' => (u : Gs)) hxy)
    have h2 : (QuotientGroup.mk (Subgroup.inclusion hSX x) : ↥X ⧸ (Oz z).subgroupOf X) =
        QuotientGroup.mk (Subgroup.inclusion hSX y) := ψ.injective h1
    rw [QuotientGroup.eq] at h2
    have h3 : (x : G)⁻¹ * y ∈ Oz z := h2
    have h4 : (x : G)⁻¹ * y = 1 := hS _ (S.mul_mem (S.inv_mem x.2) y.2) h3
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : Gs) ∈ E ⊔ S' := Subgroup.mem_sup_right y.2
    obtain ⟨s, hsS, hs⟩ := hψS' (ψ.symm ⟨y, hy⟩) (by simp)
    refine ⟨⟨(s : G), hsS⟩, ?_⟩
    apply Subtype.ext
    show ((g ⟨(s : G), hsS⟩ : ↥(E ⊔ S')) : Gs) = y
    have : g ⟨(s : G), hsS⟩ = ⟨y, hy⟩ := by
      show ψ (QuotientGroup.mk (Subgroup.inclusion hSX ⟨(s : G), hsS⟩)) = _
      have e : Subgroup.inclusion hSX ⟨(s : G), hsS⟩ = s := Subtype.ext rfl
      rw [e, hs]
      exact ψ.apply_symm_apply _
    rw [this]
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

end CFSG.GH74.GLS.Stage1.Main
