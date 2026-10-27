module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Alt1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Alt2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Clo
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Cl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Br
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Odd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem isKGroupCat_autIn {G : Type} [Group G] {H V : Subgroup G}
    (hK : CFSG.SectionRank.IsKGroupCat ↥H) : CFSG.SectionRank.IsKGroupCat ↥(autIn H V) := by
  let ι : ↥(H.subgroupOf (normalizer (V : Set G))) →* ↥H :=
    { toFun := fun x => ⟨((x : ↥(normalizer (V : Set G))) : G), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b hab => by
    have h1 : ((a : ↥(normalizer (V : Set G))) : G) = ((b : ↥(normalizer (V : Set G))) : G) :=
      congrArg (fun x : ↥H => (x : G)) hab
    exact Subtype.ext (Subtype.ext h1)
  exact (hK.of_injective ι hι).of_surjective
    (V.normalizerMonoidHom.subgroupMap (H.subgroupOf (normalizer (V : Set G))))
    (MonoidHom.subgroupMap_surjective _ _)

theorem sec128_closure_data_of_z2a5K {G : Type} [Group G] [Finite G] (hZ : Asc82Z2A5K)
    {V : Subgroup G} (hV : IsElemAb2 V 8) {Y Xt : Subgroup (MulAut ↥V)} {τ : MulAut ↥V}
    (h : Sec128Inv V Y Xt τ) (hKY : CFSG.SectionRank.IsKGroupCat ↥Y)
    (hD : Nat.card ↥(Subgroup.centralizer (Xt : Set (MulAut ↥V))) ∣ 6 ∧
      ∀ c ∈ Subgroup.centralizer (Xt : Set (MulAut ↥V)), c ^ 3 = 1 → c ≠ 1 →
        ∀ v : ↥V, c v = v → v = 1) :
    ∃ Z : Subgroup (MulAut ↥V), Z ≤ Y ∧ Xt ≤ Z ∧ (Z.subgroupOf Y).Normal ∧
      (∀ z ∈ Z, ∀ o ∈ oddCore ↥Y, z * (o : MulAut ↥V) = (o : MulAut ↥V) * z) ∧
      Z ⊓ (oddCore ↥Y).map Y.subtype = ⊥ ∧
      (((Z.subgroupOf Y ⊔ oddCore ↥Y).index = 2 ∧
          Nonempty (↥Z ≃* (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))))) ∨
        LieModel ↥Z .PSL 2 2 4 ∨ LieModel ↥Z .PSL 3 2 2) := by
  obtain ⟨h2, hK, hfus⟩ :=
    sec128_z2a5_hyps h.ty h.xy h.sq h.ne h.a5 h.tx h.comm h.cases h.cent h.fus
  have hQ := hZ ↥Y ⟨τ, h.ty⟩ hKY ⟨h2, hK, hfus⟩
  have hO : oTwoRes (Subgroup.centralizer ({(⟨τ, h.ty⟩ : ↥Y)} : Set ↥Y)) = Xt.subgroupOf Y :=
    sec128_oTwoRes_sub h.ty h.xy h.sq h.a5 h.tx h.comm h.cases
  have hcent : ∀ o ∈ oddCore ↥Y, ∀ x ∈ Xt.subgroupOf Y, x * o = o * x := by
    intro o ho x hx
    exact (sec128_oddCore_cent ⟨τ, h.ty⟩ h2 hK hfus).2 o ho x (hO ▸ hx)
  exact sec128_closure_typeK V hV Y Xt h.xy h.a5 hcent hD hQ

theorem sec128_dichotomy_of_z2a5K {G : Type} [Group G] [Finite G] (hZ : Asc82Z2A5K)
    {V : Subgroup G} (hV : IsElemAb2 V 8) {Y Xt : Subgroup (MulAut ↥V)} {τ : MulAut ↥V}
    (h : Sec128Inv V Y Xt τ) (hKY : CFSG.SectionRank.IsKGroupCat ↥Y)
    (hD : Nat.card ↥(Subgroup.centralizer (Xt : Set (MulAut ↥V))) ∣ 6 ∧
      ∀ c ∈ Subgroup.centralizer (Xt : Set (MulAut ↥V)), c ^ 3 = 1 → c ≠ 1 →
        ∀ v : ↥V, c v = v → v = 1)
    (hfix : ∀ u : ↥V, (∀ x ∈ Xt, x u = u) → u = 1)
    (hn34 : ∀ Z : Subgroup (MulAut ↥V), Xt ≤ Z → ¬ LieModel ↥Z .PSL 3 2 2)
    (hn216 : ∀ Z : Subgroup (MulAut ↥V), Xt ≤ Z → ¬ LieModel ↥Z .PSL 2 2 4)
    (hdich : ∀ Z : Subgroup (MulAut ↥V), Xt ≤ Z →
      Nonempty (↥Z ≃* (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)))) →
        Sec128SplitNat V Z ∨ IsNatOmega4Plus V Z) :
    (Sec128WrNat V Y ∧ Sec128WrAct V Y) ∨
      (IsNatOmega4Plus V ((CFSG.layer ↥Y).map Y.subtype) ∧
        (Nat.card ↥Y = 2 * Nat.card ↥((CFSG.layer ↥Y).map Y.subtype) ∨
          Nat.card ↥Y = 6 * Nat.card ↥((CFSG.layer ↥Y).map Y.subtype))) := by
  obtain ⟨Z, hZY, hXZ, hZn, hZc, hZO, hty⟩ := sec128_closure_data_of_z2a5K hZ hV h hKY hD
  rcases hty with ⟨hidx, hZe⟩ | h216 | h34
  · rcases hdich Z hXZ hZe with hS | hΩ
    · exact Or.inl (sec128_alt1 hV hZY hXZ h.ty h.ne h.sq h.a5 h.comm hfix hZn hZc hidx hS)
    · exact Or.inr (sec128_alt2 hZY hXZ hD.1 hZn hZc hZO hidx hZe hΩ)
  · exact absurd h216 (hn216 Z hXZ)
  · exact absurd h34 (hn34 Z hXZ)

end CFSG.OddStandard.SmallF3.Omega
