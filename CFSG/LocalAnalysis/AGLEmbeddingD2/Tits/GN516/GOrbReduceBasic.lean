module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCentral
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.QuasisimpleTwoNonabBridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def GOrbConcl {Y : Type*} [Group Y] (R P : Subgroup Y) : Prop :=
  Group.IsSolvable ↥(pElementSubgroup 2 (conjClosure P R)) ∨
      (∃ C : Subgroup Y, C ≤ pElementSubgroup 2 (conjClosure P R) ∧
        pElementSubgroup 2 (conjClosure P R) ≤ Subgroup.normalizer (C : Set Y) ∧
        pElementSubgroup 2 (conjClosure P R) ≤ conjClosure C R ∧
        ∀ r ∈ R, r ∉ Subgroup.normalizer (P : Set Y) →
          ⁅C, B6.conjSub r C⁆ ≤ pCoreOf 2 (pElementSubgroup 2 (conjClosure P R))) ∨
      QuasisimpleModTwoNonab ↥(twoResidual (pElementSubgroup 2 (conjClosure P R)))

namespace GOrbReduce

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem isChevTwo_congr {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : IsChevTwo Y) :
    IsChevTwo Y' := by
  rcases h with ⟨d, hd, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨d, hd, ⟨φ⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans φ⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans φ⟩⟩)

theorem quasisimpleModTwoNonab_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : QuasisimpleModTwoNonab A) : QuasisimpleModTwoNonab B :=
  (quasisimpleModTwoNonab_iff B).2
    (IsQuasisimpleTwoNonab.of_mulEquiv (QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e))
      ((quasisimpleModTwoNonab_iff A).1 h))

theorem map_conjSub (φ : G →* G') (g : G) (X : Subgroup G) :
    (B6.conjSub g X).map φ = B6.conjSub (φ g) (X.map φ) := by
  ext y
  simp only [Subgroup.mem_map, B6.mem_conjSub]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g⁻¹ * x * g, hx, by simp [map_mul, map_inv]⟩
  · rintro ⟨x', hx', hxy⟩
    refine ⟨g * x' * g⁻¹, ?_, ?_⟩
    · rw [show g⁻¹ * (g * x' * g⁻¹) * g = x' by group]
      exact hx'
    · rw [map_mul, map_mul, map_inv, hxy]
      group

theorem pCoreOf_map_injective {ι : G →* G'} (hι : Function.Injective ι) (W : Subgroup G) :
    pCoreOf 2 (W.map ι) = (pCoreOf 2 W).map ι := by
  have h := CFSG.pCore_map_iso 2 (W.equivMapOfInjective ι hι)
  unfold pCoreOf
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem comap_normalizer_map {ψ : G →* G'} (hψ : Function.Injective ψ) (S : Subgroup G) :
    (Subgroup.normalizer ((S.map ψ : Subgroup G') : Set G')).comap ψ =
      Subgroup.normalizer (S : Set G) := by
  apply le_antisymm
  · intro x hx
    have h := Subgroup.le_normalizer_comap ψ hx
    rwa [Subgroup.comap_map_eq_self_of_injective hψ] at h
  · intro x hx
    exact Subgroup.le_normalizer_map ψ ⟨x, hx, rfl⟩

theorem map_inf_normalizer {ψ : G →* G'} (hψ : Function.Injective ψ) (L S : Subgroup G) :
    (L ⊓ Subgroup.normalizer (S : Set G)).map ψ =
      L.map ψ ⊓ Subgroup.normalizer ((S.map ψ : Subgroup G') : Set G') := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, Subgroup.le_normalizer_map ψ ⟨x, hx.2, rfl⟩⟩
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    have h : x ∈ (Subgroup.normalizer ((S.map ψ : Subgroup G') : Set G')).comap ψ := hy
    rwa [comap_normalizer_map hψ] at h

theorem isMinOverBorel_map_iff {ψ : G →* G'} (hψ : Function.Injective ψ) {L S P : Subgroup G} :
    IsMinOverBorel (L.map ψ) (S.map ψ) (P.map ψ) ↔ IsMinOverBorel L S P := by
  unfold IsMinOverBorel
  rw [← map_inf_normalizer hψ]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hψ).1 h1,
      (Subgroup.map_lt_map_iff_of_injective hψ).1 h2, fun Q hQ1 hQ2 => ?_⟩
    rcases h3 (Q.map ψ) (Subgroup.map_mono hQ1) (Subgroup.map_mono hQ2) with h | h
    · exact Or.inl (Subgroup.map_injective hψ h)
    · exact Or.inr (Subgroup.map_injective hψ h)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨Subgroup.map_mono h1, (Subgroup.map_lt_map_iff_of_injective hψ).2 h2,
      fun Q hQ1 hQ2 => ?_⟩
    have hQr : Q ≤ ψ.range := hQ2.trans (Subgroup.map_le_range ψ P)
    have e : (Q.comap ψ).map ψ = Q := Subgroup.map_comap_eq_self hQr
    have h4 : L ⊓ Subgroup.normalizer (S : Set G) ≤ Q.comap ψ :=
      Subgroup.map_le_iff_le_comap.1 hQ1
    have h5 : Q.comap ψ ≤ P := by
      have := Subgroup.comap_mono (f := ψ) hQ2
      rwa [Subgroup.comap_map_eq_self_of_injective hψ] at this
    rcases h3 (Q.comap ψ) h4 h5 with h | h
    · left
      rw [← e, h]
    · right
      rw [← e, h]

end Transport

section Sylow

variable {G G' : Type*} [Group G] [Group G']

theorem isSylowTwoOf_map (φ : G →* G') {S L : Subgroup G} (h : IsSylowTwoOf S L) :
    IsSylowTwoOf (S.map φ) (L.map φ) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map φ, ?_⟩
  have hsur := φ.subgroupMap_surjective L
  have hmap : (S.subgroupOf L).map (φ.subgroupMap L) = (S.map φ).subgroupOf (L.map φ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · intro hy
      obtain ⟨s, hs, hsy⟩ := hy
      exact ⟨⟨s, h.1 hs⟩, hs, Subtype.ext hsy⟩
  have hdvd := Subgroup.index_map_dvd (H := S.subgroupOf L) hsur
  rw [hmap] at hdvd
  intro h2
  exact h.2.2 (h2.trans hdvd)

theorem isSylowTwoOf_map_iff {φ : G →* G'} (hφ : Function.Injective φ) {S L : Subgroup G} :
    IsSylowTwoOf (S.map φ) (L.map φ) ↔ IsSylowTwoOf S L := by
  refine ⟨fun h => ⟨(Subgroup.map_le_map_iff_of_injective hφ).1 h.1,
    h.2.1.of_equiv (Subgroup.equivMapOfInjective S φ hφ).symm, ?_⟩, isSylowTwoOf_map φ⟩
  have := h.2.2
  rwa [show ((S.map φ).subgroupOf (L.map φ)).index = (S.subgroupOf L).index from
    Subgroup.relIndex_map_map_of_injective S L hφ] at this

theorem eq_of_isSylowTwoOf_of_le [Finite G] {S T L : Subgroup G} (hS : IsSylowTwoOf S L)
    (hST : S ≤ T) (hTL : T ≤ L) (hT : IsPGroup 2 T) : T = S := by
  have h1 : S.relIndex T * T.relIndex L = S.relIndex L :=
    Subgroup.relIndex_mul_relIndex S T L hST hTL
  obtain ⟨n, hn⟩ := B6.exists_relIndex_eq_two_pow_of_isPGroup hT S
  have hodd : ¬ 2 ∣ S.relIndex L := hS.2.2
  have hn0 : n = 0 := by
    by_contra hne
    apply hodd
    rw [← h1, hn]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hne) _
  rw [hn0, pow_zero] at hn
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hn) hST

theorem inf_map_eq_map_inf [Finite G'] (f : G →* G') {L R : Subgroup G} (hR : IsPGroup 2 R)
    (hS : IsSylowTwoOf (R ⊓ L) L) :
    R.map f ⊓ L.map f = (R ⊓ L).map f ∧ IsSylowTwoOf (R.map f ⊓ L.map f) (L.map f) := by
  have hS' := isSylowTwoOf_map f hS
  have heq : R.map f ⊓ L.map f = (R ⊓ L).map f :=
    eq_of_isSylowTwoOf_of_le hS' (Subgroup.map_inf_le R L f) inf_le_right
      ((hR.map f).to_le inf_le_left)
  exact ⟨heq, heq ▸ hS'⟩

end Sylow

section Concl

variable {G G' : Type*} [Group G] [Group G']

theorem gOrbConcl_map [Finite G] {ι : G →* G'} (hι : Function.Injective ι) {R P : Subgroup G}
    (h : GOrbConcl R P) : GOrbConcl (R.map ι) (P.map ι) := by
  have hX : conjClosure (P.map ι) (R.map ι) = (conjClosure P R).map ι :=
    (map_conjClosure ι P R).symm
  have hW : pElementSubgroup 2 (conjClosure (P.map ι) (R.map ι)) =
      (pElementSubgroup 2 (conjClosure P R)).map ι := by
    rw [hX]
    exact (map_pElementSubgroup_two ι _).symm
  unfold GOrbConcl at h ⊢
  rw [hW]
  set W₁ := pElementSubgroup 2 (conjClosure P R) with hW₁
  rcases h with h | ⟨C, hCW, hWN, hWC, hcomm⟩ | h
  · left
    haveI := h
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective W₁ ι hι).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective W₁ ι hι).symm.injective
  · right
    left
    refine ⟨C.map ι, Subgroup.map_mono hCW,
      (Subgroup.map_mono hWN).trans (Subgroup.le_normalizer_map ι),
      (Subgroup.map_mono hWC).trans (map_conjClosure ι C R).le, ?_⟩
    rintro _ ⟨r, hr, rfl⟩ hrP
    have hrP' : r ∉ Subgroup.normalizer (P : Set G) := fun hn =>
      hrP (Subgroup.le_normalizer_map ι ⟨r, hn, rfl⟩)
    have h1 := Subgroup.map_mono (f := ι) (hcomm r hr hrP')
    rw [Subgroup.map_commutator, map_conjSub, ← pCoreOf_map_injective hι] at h1
    exact h1
  · right
    right
    rw [← map_twoResidual ι W₁]
    exact quasisimpleModTwoNonab_congr (Subgroup.equivMapOfInjective _ ι hι) h

end Concl

end GOrbReduce

end CFSG.AGLEmbeddingD2.Tits.GN516
