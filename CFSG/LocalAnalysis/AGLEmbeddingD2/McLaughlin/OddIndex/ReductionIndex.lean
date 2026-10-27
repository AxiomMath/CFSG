module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.ReductionQuot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectSolv
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {N : Type} [Group N] [Finite N]

@[expose] def redImg (X A : Subgroup N) [X.Normal] : Subgroup (Red X (CFSG.pPrimeCore 3 N)) :=
  (A.subgroupOf X).map (redMk X (CFSG.pPrimeCore 3 N))

@[expose] def redW (X H : Subgroup N) [X.Normal] : Subgroup (Red X (CFSG.pPrimeCore 3 N)) :=
  (H.subgroupOf X).map (redMk X (CFSG.pPrimeCore 3 N))

theorem card_redImg {X A : Subgroup N} [X.Normal] (hA : Nat.card A = 3) (hAX : A ≤ X) :
    Nat.card (redImg X A) = 3 := by
  have hc : Nat.card (A.subgroupOf X) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv).trans hA
  have hpg : IsPGroup 3 (A.subgroupOf X) := IsPGroup.iff_card.mpr ⟨1, by rw [hc, pow_one]⟩
  obtain ⟨e⟩ := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_pGroup_equiv_image 3
    Nat.prime_three (redMk X (CFSG.pPrimeCore 3 N)) (card_ker_redMk_coprime X) (A.subgroupOf X) hpg
  rw [redImg, ← Nat.card_congr e.toEquiv, hc]

theorem normalizer_redImg_le {X A H : Subgroup N} [X.Normal]
    (hcyc : ∀ R : Subgroup N, IsPGroup 3 R → IsCyclic R) (hA : Nat.card A = 3) (hAX : A ≤ X)
    (hAH : A ≤ H) (hNH : Subgroup.normalizer (A : Set N) ≤ H)
    (hIH : CFSG.pPrimeCore 3 N ≤ H) :
    Subgroup.normalizer ((redImg X A : Subgroup (Red X (CFSG.pPrimeCore 3 N))) : Set _) ≤
      redW X H := by
  classical
  set I : Subgroup N := CFSG.pPrimeCore 3 N with hI
  intro k hk
  obtain ⟨x, rfl⟩ := redMk_surjective X I k
  set At : Subgroup N := ((redImg X A).comap (redMk X I)).map X.subtype with hAt
  have hAAt : A ≤ At := by
    intro a ha
    exact Subgroup.mem_map.mpr ⟨⟨a, hAX ha⟩,
      Subgroup.mem_map.mpr ⟨⟨a, hAX ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩, rfl⟩
  have hxX : (x : N) ∈ X := x.2
  have hCAt : A.map (MulAut.conj (x : N)).toMonoidHom ≤ At := by
    rintro _ hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    have haX : a ∈ X := hAX ha
    refine Subgroup.mem_map.mpr ⟨x * ⟨a, haX⟩ * x⁻¹, ?_, ?_⟩
    · show redMk X I (x * ⟨a, haX⟩ * x⁻¹) ∈ redImg X A
      rw [map_mul, map_mul, map_inv]
      have hmem : redMk X I ⟨a, haX⟩ ∈ redImg X A :=
        Subgroup.mem_map.mpr ⟨⟨a, haX⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hk _).mp hmem
    · simp [MulAut.conj_apply]
  have hCc : Nat.card (A.map (MulAut.conj (x : N)).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (x : N)).injective, hA]
  obtain ⟨a', ha'At, hconj⟩ := exists_conj_mem_of_card_eq (p := 3) hcyc hAAt hCAt hA hCc
  have hle : A.map (MulAut.conj (a'⁻¹ * (x : N))).toMonoidHom ≤ A := by
    rintro _ hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    have hxt : (x : N) * t * (x : N)⁻¹ ∈ A.map (MulAut.conj a').toMonoidHom := by
      rw [← hconj]
      exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp hxt
    have : (a'⁻¹ * (x : N)) * t * (a'⁻¹ * (x : N))⁻¹ = s := by
      have h1 : a' * s * a'⁻¹ = (x : N) * t * (x : N)⁻¹ := hst
      calc (a'⁻¹ * (x : N)) * t * (a'⁻¹ * (x : N))⁻¹
          = a'⁻¹ * ((x : N) * t * (x : N)⁻¹) * a' := by group
        _ = s := by rw [← h1]; group
    rw [show (MulAut.conj (a'⁻¹ * (x : N))).toMonoidHom t =
      (a'⁻¹ * (x : N)) * t * (a'⁻¹ * (x : N))⁻¹ from rfl, this]
    exact hs
  have hcardle : Nat.card (A.map (MulAut.conj (a'⁻¹ * (x : N))).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hA]
  have heq : A.map (MulAut.conj (a'⁻¹ * (x : N))).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardle, hA])
  have hgN : a'⁻¹ * (x : N) ∈ Subgroup.normalizer (A : Set N) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have : (a'⁻¹ * (x : N)) * t * (a'⁻¹ * (x : N))⁻¹ ∈
          A.map (MulAut.conj (a'⁻¹ * (x : N))).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      rwa [heq] at this
    · intro ht
      rw [← heq] at ht
      obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp ht
      have : s = t := by
        have h1 : (a'⁻¹ * (x : N)) * s * (a'⁻¹ * (x : N))⁻¹ =
            (a'⁻¹ * (x : N)) * t * (a'⁻¹ * (x : N))⁻¹ := hst
        simpa using h1
      rwa [← this]
  have hga : a'⁻¹ * (x : N) ∈ H := hNH hgN
  have ha'H : a' ∈ H := by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha'At
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hy
    have hbH : (b : N) ∈ H := hAH (Subgroup.mem_subgroupOf.mp hb)
    have hker : b⁻¹ * y ∈ (redMk X I).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hby, inv_mul_cancel]
    have hker' : ((b⁻¹ * y : ↥X) : N) ∈ I := (redMk_eq_one_iff X I _).mp hker
    have : ((y : ↥X) : N) = (b : N) * ((b⁻¹ * y : ↥X) : N) := by simp
    show ((y : ↥X) : N) ∈ H
    rw [this]
    exact H.mul_mem hbH (hIH hker')
  have hxH : (x : N) ∈ H := by
    have : (x : N) = a' * (a'⁻¹ * (x : N)) := by group
    rw [this]
    exact H.mul_mem ha'H hga
  exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr hxH, rfl⟩

omit [Finite N] in
theorem index_redW {X H : Subgroup N} [X.Normal] (hIH : CFSG.pPrimeCore 3 N ≤ H) :
    (redW X H).index = H.relIndex X := by
  have hker : (redMk X (CFSG.pPrimeCore 3 N)).ker ≤ H.subgroupOf X := by
    intro x hx
    have : ((x : ↥X) : N) ∈ CFSG.pPrimeCore 3 N := (redMk_eq_one_iff _ _ _).mp hx
    exact Subgroup.mem_subgroupOf.mpr (hIH this)
  rw [redW, Subgroup.index_map_eq _ (redMk_surjective X _) hker]
  rfl

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
