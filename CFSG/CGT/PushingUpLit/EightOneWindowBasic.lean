module

public import CFSG.CGT.PushingUpLit.BlocksCommuteDefs
public import CFSG.CGT.PushingUpLit.EightOneRel

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.QuasithinUnique.Setup.Campbell CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement

namespace EightOneWindow

section Core

variable {G : Type} [Group G]

theorem oTwoIn_le_centralizerModCore (X : Subgroup G) : oTwoIn X ≤ centralizerModCore X := by
  intro g hg
  refine ⟨Subgroup.le_normalizer (oTwoIn_le X hg), fun x hx => ?_⟩
  have h1 : x * g⁻¹ * x⁻¹ ∈ oTwoIn X :=
    conj_mem_oTwoIn (Subgroup.le_normalizer hx) (inv_mem hg)
  have e : g * x * g⁻¹ * x⁻¹ = g * (x * g⁻¹ * x⁻¹) := by group
  rw [e]
  exact mul_mem hg h1

theorem centralizerModCore_le_normalizer (X : Subgroup G) :
    centralizerModCore X ≤ Subgroup.normalizer (X : Set G) :=
  fun _ hg => hg.1

theorem le_normalizer_of_le_centralizerModCore {X D : Subgroup G} (hOD : oTwoIn X ≤ D)
    (hDC : D ≤ centralizerModCore X) : X ≤ Subgroup.normalizer (D : Set G) := by
  have key : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    intro x hx d hd
    have h1 : d * x⁻¹ * d⁻¹ * x⁻¹⁻¹ ∈ oTwoIn X := (hDC hd).2 x⁻¹ (inv_mem hx)
    have h2 : x * (d * x⁻¹ * d⁻¹ * x⁻¹⁻¹) * x⁻¹ ∈ oTwoIn X :=
      conj_mem_oTwoIn (Subgroup.le_normalizer hx) h1
    have e : x * d * x⁻¹ = (x * (d * x⁻¹ * d⁻¹ * x⁻¹⁻¹) * x⁻¹) * d := by group
    rw [e]
    exact mul_mem (hOD h2) hd
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨key x hx d, fun h => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ h
  simpa [mul_assoc] using this

theorem normalizer_le_normalizer_centralizerModCore (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (centralizerModCore X : Set G) := by
  have key : ∀ s ∈ Subgroup.normalizer (X : Set G), ∀ c ∈ centralizerModCore X,
      s * c * s⁻¹ ∈ centralizerModCore X := by
    intro s hs c hc
    obtain ⟨hcN, hc'⟩ := hc
    refine ⟨mul_mem (mul_mem hs hcN) (inv_mem hs), fun x hx => ?_⟩
    have hx' : s⁻¹ * x * s⁻¹⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (inv_mem hs) x).mp hx
    have h1 := conj_mem_oTwoIn hs (hc' _ hx')
    have e : s * (c * (s⁻¹ * x * s⁻¹⁻¹) * c⁻¹ * (s⁻¹ * x * s⁻¹⁻¹)⁻¹) * s⁻¹ =
        s * c * s⁻¹ * x * (s * c * s⁻¹)⁻¹ * x⁻¹ := by group
    rwa [e] at h1
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key s hs c, fun hc => ?_⟩
  have := key s⁻¹ (inv_mem hs) _ hc
  simpa [mul_assoc] using this

theorem isSylowOf_of_le_of_le {S K K' : Subgroup G} (hS : IsSylowOf 2 S K) (hSK' : S ≤ K')
    (hK'K : K' ≤ K) : IsSylowOf 2 S K' :=
  ⟨hSK', hS.2.1, fun h2 => hS.2.2 (by
    rw [← Subgroup.relIndex_mul_relIndex S K' K hSK' hK'K]
    exact dvd_mul_of_dvd_left h2 _)⟩

theorem pRank_conjugate (S : Subgroup G) (k : G) :
    pRank 2 ↥(conjugate S k) = pRank 2 ↥S :=
  Nine.pRank_map_injective (MulAut.conj k⁻¹).toMonoidHom (MulAut.conj k⁻¹).injective S 2

theorem pRank_eq_of_isSylowOf [Finite G] {S K : Subgroup G} (hS : IsSylowOf 2 S K) :
    pRank 2 ↥S = pRank 2 ↥K := by
  refine le_antisymm (pRank_mono hS.1) ?_
  obtain ⟨A, hA⟩ := exists_mem_elemFamilyIn K
  obtain ⟨hAK, hAe, hAc⟩ := mem_elemFamilyIn.mp hA
  have hA2 : IsPGroup 2 A := by
    have := hAe
    exact IsElementaryAbelian.isPGroup 2 ↥A
  obtain ⟨S', hS', hAS'⟩ := Nine.exists_isSylowOf_ge hA2 hAK
  obtain ⟨a, -, rfl⟩ := EightOneRel.exists_conjugate_eq_of_isSylowOf hS' hS
  calc pRank 2 ↥K ≤ pRank 2 ↥(conjugate S a) := pRank_le_of_card_le hAS' hAe hAc
    _ = pRank 2 ↥S := pRank_conjugate S a

theorem exists_isSylowOf_normalizer_between [Finite G] {X D : Subgroup G}
    (hDsyl : IsSylowOf 2 D (centralizerModCore X)) :
    ∃ S : Subgroup G, IsSylowOf 2 S (Subgroup.normalizer (X : Set G)) ∧ D ≤ S ∧
      S ≤ Subgroup.normalizer (D : Set G) := by
  have hDN : D ≤ Subgroup.normalizer (X : Set G) :=
    hDsyl.1.trans (centralizerModCore_le_normalizer X)
  obtain ⟨S, hS, hDS⟩ := Nine.exists_isSylowOf_ge hDsyl.2.1 hDN
  have hSC : S ⊓ centralizerModCore X ≤ D :=
    Nine.le_of_isSylowOf_of_le hDsyl (hS.2.1.to_le inf_le_left) (le_inf hDS hDsyl.1) inf_le_right
  have key : ∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D := by
    intro s hs d hd
    have h1 : s * d * s⁻¹ ∈ S := mul_mem (mul_mem hs (hDS hd)) (inv_mem hs)
    have h2 : s * d * s⁻¹ ∈ centralizerModCore X :=
      (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_centralizerModCore X (hS.1 hs)) d).mp (hDsyl.1 hd)
    exact hSC ⟨h1, h2⟩
  refine ⟨S, hS, hDS, fun s hs => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨key s hs d, fun hd => ?_⟩
  have := key s⁻¹ (inv_mem hs) _ hd
  simpa [mul_assoc] using this

end Core

end EightOneWindow

end CFSG.CGT.PushingUpLit
