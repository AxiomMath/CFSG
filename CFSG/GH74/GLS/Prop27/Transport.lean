module

public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.Timmesfeld.Final.Simple
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint Assembly.LowTwoRank

theorem card_quotient_center_eq_of_surjective {K Kb : Type} [Group K] [Group Kb] [Finite K]
    (hK : IsQuasisimple K) (f : K →* Kb) (hf : Function.Surjective f) (hker : f.ker ≤ center K) :
    Nat.card (Kb ⧸ center Kb) = Nat.card (K ⧸ center K) :=
  Nat.card_congr
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hK hf hker).symm.toEquiv

theorem center_eq_bot_of_lieModel
    {K : Type} [Group K] {t : StatedLieTag} {n p f : ℕ}
    (hq : IsQuasisimple K) (hL : LieModel K t n p f) : center K = ⊥ := by
  have := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    refine hab ?_
    have hy : y ∈ center K := h ▸ Subgroup.mem_top y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hy x]

private theorem even_card_of_quasisimple_aux {K : Type*} [Group K] [Finite K]
    (hK : IsQuasisimple K) : Even (Nat.card K) := by
  obtain ⟨-, hs, hnab⟩ := hK
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab).1
  obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (center K)
  rw [hk]
  exact heven.mul_right k

theorem exists_component_bar {G : Type} [Group G] [Finite G] {x : G} (_hx : orderOf x = 2)
    {K : Subgroup G} (hK : IsCompIn (centralizer ({x} : Set G)) K) :
    ∃ Kb : Subgroup (CentralizerBar x), IsComponent Kb ∧
      ∃ f : ↥K →* ↥Kb, Function.Surjective f ∧ f.ker ≤ center ↥K := by
  obtain ⟨hKC, hcomp⟩ := hK
  set C : Subgroup G := centralizer ({x} : Set G)
  set K' : Subgroup ↥C := K.subgroupOf C
  let π : ↥C →* CentralizerBar x := QuotientGroup.mk' (pPrimeCore 2 ↥C)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let φ : ↥K' →* ↥(K'.map π) := π.subgroupMap K'
  have hφ : Function.Surjective φ := π.subgroupMap_surjective K'
  have hker_eq : φ.ker = pPrimeCore 2 ↥K' := by
    rw [← CFSG.GH74.GLS.ker_restrict_eq_pPrimeCore hcomp.2]
    ext y
    constructor
    · intro h
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp h))
    · intro h
      exact MonoidHom.mem_ker.mpr (Subtype.ext (MonoidHom.mem_ker.mp h))
  have hker_ne_top : φ.ker ≠ ⊤ := by
    intro htop
    have h1 : pPrimeCore 2 ↥K' = ⊤ := hker_eq ▸ htop
    have h2 : Nat.card ↥K' = Nat.card ↥(pPrimeCore 2 ↥K') := by rw [h1, Subgroup.card_top]
    have h3 : Nat.Coprime 2 (Nat.card ↥K') := h2 ▸ pPrimeCore_coprime_card
    exact Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp h3)
      (even_card_of_quasisimple_aux hcomp.1)
  have hker : φ.ker ≤ center ↥K' := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hcomp.1 (MonoidHom.normal_ker φ) with
      h | h
    · exact absurd h hker_ne_top
    · exact h
  have hφnt : ∃ k, φ k ≠ 1 := by
    by_contra hcon
    refine hker_ne_top ((Subgroup.eq_top_iff' _).mpr fun k => MonoidHom.mem_ker.mpr ?_)
    by_contra hk
    exact hcon ⟨k, hk⟩
  refine ⟨K'.map π,
    ⟨CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hcomp.1 hφ hφnt, hcomp.2.map hπ⟩, ?_⟩
  let e : ↥K ≃* ↥K' := (Subgroup.subgroupOfEquivOfLe hKC).symm
  refine ⟨φ.comp e.toMonoidHom, hφ.comp e.surjective, fun k hk => ?_⟩
  have hk' : e k ∈ center ↥K' := hker (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hk))
  rw [Subgroup.mem_center_iff] at hk' ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul]
  exact hk' (e g)

end CFSG.GH74.GLS.Prop27
