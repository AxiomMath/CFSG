module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.LocalAnalysis.AGLEmbedding.BlockTransvectionCyclicSylow
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.LemmaBGlue

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def CitedBlockTransvectionInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L → p.Prime → p ≠ 2 →
    PerfectCyclicSylow p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →
    ∀ u : ↥M, (u : G) ∈ Subgroup.normalizer (S : Set G) →
      (u : G) ∈ Subgroup.normalizer (L : Set G) → (∃ k : ℕ, u ^ p ^ k = 1) →
      ∃ l ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), ∀ x ∈ barM M L,
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) u * x * (QuotientGroup.mk' (CFSG.pCore 2 ↥M) u)⁻¹ =
          l * x * l⁻¹

theorem citedBlockTransvectionCyclic_of (hTPLT : CitedBlockTransvectionPLType)
    (hInner : CitedBlockTransvectionInner) : CitedBlockTransvectionCyclic := by
  intro G _ _ M S L p hK hA hL hX hS h3 hp hp2 hperf U hUK hUL hUp
  have : Fact p.Prime := ⟨hp⟩
  have hUM : U ≤ M := hUK.trans inf_le_left
  set Lb := barM M L
  set Pb := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set NL := Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  set c : ↥NL →* MulAut ↥Lb := Lb.normalizerMonoidHom
  have hPbL : Pb ≤ Lb := barM_mono inf_le_right
  have hLbN : Lb ≤ NL := Subgroup.le_normalizer
  have hUbN : barM M U ≤ NL := barM_le_normalizer_barM hUL
  set Ub' := (barM M U).subgroupOf NL
  set Pb' := Pb.subgroupOf NL
  set X := Ub'.map c
  have hc : ∀ (n : ↥NL) (y : ↥Lb), ((c n y : ↥Lb) : ↥M ⧸ CFSG.pCore 2 ↥M) = n * y * n⁻¹ :=
    fun _ _ => rfl
  have hXP : X ≤ Pb'.map c := by
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_subgroupOf.mp hn
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    obtain ⟨k, hk⟩ := hUp ⟨u, huU⟩
    have hk' : u ^ p ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    obtain ⟨l, hl, hlx⟩ := hInner G M S L p hK hA hL hX hS h3 hp hp2 hperf u (hUK huU).2
      (hUL huU) ⟨k, hk'⟩
    refine ⟨⟨l, hLbN (hPbL hl)⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
    ext y
    rw [hc, hc]
    change l * y * l⁻¹ = (n : ↥M ⧸ CFSG.pCore 2 ↥M) * y * (n : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹
    rw [← hue]
    exact (hlx y y.2).symm
  have hXp : IsPGroup p X := ((isPGroup_barM hUp).comap_subtype (K := NL)).map c
  have hXc : IsCyclic X := by
    set B := Pb' ⊓ X.comap c
    have hBX : ∀ b : ↥B, c b ∈ X := fun b => b.2.2
    set g : ↥B →* ↥X := (c.domRestrict B).codRestrict X hBX
    have hg : Function.Surjective g := by
      rintro ⟨x, hx⟩
      obtain ⟨b, hb, rfl⟩ := hXP hx
      exact ⟨⟨b, hb, hx⟩, rfl⟩
    obtain ⟨P⟩ : Nonempty (Sylow p ↥B) := inferInstance
    set Q := P.mapSurjective hg
    have hQ : (Q : Subgroup ↥X) = ⊤ :=
      (Q.is_maximal' (hXp.of_equiv Subgroup.topEquiv.symm) le_top).symm
    have hPc : IsCyclic ↥(P : Subgroup ↥B) := by
      set A := ((P : Subgroup ↥B).map B.subtype).map NL.subtype
      have hAP : A ≤ Pb := by
        rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
        exact Subgroup.mem_subgroupOf.mp b.2.1
      have hAc := isCyclic_of_le_blockPL hTPLT hK hA hL hX hS h3 hp hp2 hperf hAP
        ((P.isPGroup'.map _).map _)
      have e1 : ↥(P : Subgroup ↥B) ≃* ↥A :=
        ((P : Subgroup ↥B).equivMapOfInjective _ B.subtype_injective).trans
          (((P : Subgroup ↥B).map B.subtype).equivMapOfInjective _ NL.subtype_injective)
      exact isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective
    have hQc : IsCyclic ↥(Q : Subgroup ↥X) := by
      rw [Sylow.coe_mapSurjective]
      exact isCyclic_of_surjective (g.subgroupMap (P : Subgroup ↥B))
        (g.subgroupMap_surjective (P : Subgroup ↥B))
    rw [hQ] at hQc
    exact isCyclic_of_surjective (Subgroup.topEquiv.toMonoidHom) Subgroup.topEquiv.surjective
  obtain ⟨⟨x₀, hx₀⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥X)
  obtain ⟨n₀, hn₀, rfl⟩ := hx₀
  obtain ⟨u₀, hu₀, hu₀e⟩ := Subgroup.mem_subgroupOf.mp hn₀
  have hu₀U : (u₀ : G) ∈ U := Subgroup.mem_subgroupOf.mp hu₀
  refine ⟨u₀, hu₀U, fun x hx => ?_⟩
  set x' : ↥M := ⟨x, hUM hx⟩
  have hxN : q x' ∈ NL := hUbN ⟨x', Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hxX : c ⟨q x', hxN⟩ ∈ X := ⟨⟨q x', hxN⟩, Subgroup.mem_subgroupOf.mpr
    ⟨x', Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (hgen ⟨_, hxX⟩) : _ ∈ Submonoid.powers _)
  refine ⟨k, ?_⟩
  have hk' : c n₀ ^ k = c ⟨q x', hxN⟩ := by
    simpa using congrArg Subtype.val hk
  have hker : ⟨q x', hxN⟩ * (n₀ ^ k)⁻¹ ∈ c.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hk', mul_inv_cancel]
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  have hcent : q (x' * (u₀ ^ k)⁻¹) ∈
      Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have h1 := Subgroup.mem_subgroupOf.mp hker
    rw [map_mul, map_inv, map_pow, hu₀e]
    simpa using h1
  have := (mem_blockCentralizer_iff (x' * (u₀ ^ k)⁻¹)).mpr hcent
  simpa [x'] using this

end CFSG.AGLEmbedding
