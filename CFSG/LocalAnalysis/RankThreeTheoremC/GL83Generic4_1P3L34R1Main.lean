module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1L33
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1K0
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34g
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

structure KFactsL34Full : Prop extends KFactsL34 where
  sylowTransitive : KFactL34SylowTransitive
  outerCentralizer : KFactL34OuterCentralizer

theorem l34_prop34 (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hK7 : KFactL34SylowTransitive)
    (hK10 : KFactL34OuterCentralizer) (hSig : SignalizerTwoGroupKFact)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    L34Prop34 3 P J x := by
  obtain ⟨hEel, hEcard, hΩ⟩ := l34_omega hS hU0 hK1 hK2 hK10 hp hM hgen hJ
  have hK₀tr := l34_transitive hK7 hgen hJ
  have hK₀card := l34Sign_card_inf hS hU0 hK1 hK2 hp hM hgen hJ
  have hxJ := l34_x_not_mem_J hS hU0 hK1 hK2 hp hM hgen hJ
  have hL33 : ∀ D : Subgroup G, D ≤ ((P : Subgroup G) ⊓ J) ⊔ zpowers x → IsElemAbelian 3 D →
      Nat.card D = 3 ^ 2 → ¬ ∃ S : Finset (Subgroup G), S.card = 3 ∧ ∀ L ∈ S, L ≤ D ∧
        Nat.card L = 3 ∧ ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom :=
    fun D hDE hD hDc => l34_not_exists_conj_lines hS hU0 hD1 hK1 hK2 hK10 hSig hp hM hgen hJ
      hDE hD hDc
  have hJC := hJ.le_centralizer
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Q : Subgroup G := (P : Subgroup G) ⊓ C with hQ
  set A : Subgroup G := (P : Subgroup G) ⊓ J with hA
  set E : Subgroup G := A ⊔ zpowers x with hE
  have hAC : A ≤ C := inf_le_right.trans hJC
  have hAQ : A ≤ Q := le_inf inf_le_left hAC
  obtain ⟨hxP, hlo, -, -⟩ := hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := hlo
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hxQ : x ∈ Q := ⟨hxP, hxC⟩
  have hEQ : E ≤ Q := sup_le hAQ (zpowers_le.mpr hxQ)
  have hxA : x ∉ A := fun h => hxJ h.2
  have hAE : A ≤ E := le_sup_left
  have hxE : x ∈ E := mem_sup_right (mem_zpowers x)
  have hK₀el : IsElemAbelian 3 A :=
    ⟨⟨⟨fun a b => Subtype.ext (by
      have h := congrArg Subtype.val (hEel.1.is_comm.comm (⟨a, hAE a.2⟩ : E) ⟨b, hAE b.2⟩)
      exact h)⟩⟩, fun a ha => hEel.2 a (hAE ha)⟩
  have hfus := p34_fusion hL33 hx1 hx3 hxE hAE hAC hK₀el hK₀card hxA hK₀tr
  have hPC : (P : Subgroup G) ≤ C := by
    by_contra hnot
    have hlt : Q < (P : Subgroup G) := inf_lt_left.mpr hnot
    have hgrow := pGroup_proper_subgroup_lt_internal_normalizer 3 Nat.prime_three
      (P : Subgroup G) Q P.isPGroup' hlt
    obtain ⟨y, hy, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
    have hyP : y ∈ (P : Subgroup G) := hy.1
    have hyN : y ∈ normalizer (Q : Set G) := hy.2
    have hx'Q : y * x * y⁻¹ ∈ Q := (mem_normalizer_iff.mp hyN x).mp hxQ
    have hx'3 : (y * x * y⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; simp
    have hx'x : y * x * y⁻¹ ∈ zpowers x := hfus _ (hΩ _ hx'Q hx'3) ⟨y, rfl⟩
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨y, hyP⟩
    have hym : y ^ (3 ^ m) = 1 := congrArg Subtype.val hm
    have hxy := p34_conj_eq_of_pow hx1 hx3 hym hx'x
    have hyC : y ∈ C := mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hxy)
    exact hyQ ⟨hyP, hyC⟩
  have hPQ : (P : Subgroup G) = Q := (inf_eq_left.mpr hPC).symm
  refine ⟨hPC, hEel, hEcard, ?_, ?_⟩
  · intro y hy hy3
    exact hΩ y (hPQ ▸ hy) hy3
  · intro g hg
    have hy : g * x * g⁻¹ ∈ (P : Subgroup G) := hg ⟨x, mem_zpowers x, rfl⟩
    have hyQ : g * x * g⁻¹ ∈ Q := hPQ ▸ hy
    have hy3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; simp
    have hyx : g * x * g⁻¹ ∈ zpowers x := hfus _ (hΩ _ hyQ hy3) ⟨g, rfl⟩
    have hle : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ zpowers x := by
      rw [MonoidHom.map_zpowers]
      exact zpowers_le.mpr hyx
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

theorem GL83GenericPrimeThreeL34Prop34.of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hSig : SignalizerTwoGroupKFact) (hL : KFactsL34Full) :
    GL83GenericPrimeThreeL34Prop34 G := by
  intro p hp P M hM _ _ x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  exact l34_prop34 hS hU0 hD1 hL.twoSignalizer hL.three hL.sylowTransitive hL.outerCentralizer
    hSig hp hM hgen ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
