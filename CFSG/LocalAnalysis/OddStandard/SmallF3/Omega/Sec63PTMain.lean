module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem sec63PT_oddCentralCover_of_equiv {A P : Type} [Group A] [Finite A] [Group P]
    (e : A ⧸ oddCore A ≃* P) (hcen : oddCore A ≤ center A) :
    OddCentralCover (e.toMonoidHom.comp (QuotientGroup.mk' (oddCore A))) := by
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (oddCore A))).ker = oddCore A := by
    ext n
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      have h' : e (QuotientGroup.mk' (oddCore A) n) = 1 := h
      rw [MulEquiv.map_eq_one_iff] at h'
      exact (QuotientGroup.eq_one_iff n).mp h'
    · intro h
      have h1 : QuotientGroup.mk' (oddCore A) n = 1 := (QuotientGroup.eq_one_iff n).mpr h
      rw [h1, map_one]
  refine ⟨e.surjective.comp (QuotientGroup.mk'_surjective (oddCore A)), ?_, ?_⟩
  · rw [hker]; exact hcen
  · rw [hker]; exact odd_card_oddCore

theorem sec63PT_isL29_map {A P : Type} [Group A] [Finite A] [Group P] [Finite P] {ρ : A →* P}
    (h : OddCentralCover ρ) {V : Subgroup A} (hV : IsL29 V) : IsL29 (V.map ρ) := by
  have hφ : OddCentralCover (ρ.subgroupMap V) := sec63PT_oddCentralCover_subgroupMap h V
  unfold IsL29 at hV ⊢
  exact (sec63PT_lieModel_psl_iff (ρ.subgroupMap V) hφ.surjective hφ.odd_card_ker 2 3 2).mp hV

theorem sec63PT_isL29_coverDerived {A P : Type} [Group A] [Finite A] [Group P] [Finite P]
    {ρ : A →* P} (h : OddCentralCover ρ) {X : Subgroup P} (hX : IsQuasisimple X)
    (hL : IsL29 X) : IsL29 (coverDerived ρ X) := by
  have hφ : OddCentralCover (coverDerivedHom ρ X) := h.oddCentralCover_coverDerivedHom hX
  unfold IsL29 at hL ⊢
  exact (sec63PT_lieModel_psl_iff (coverDerivedHom ρ X) hφ.surjective hφ.odd_card_ker 2 3 2).mpr hL

theorem sec63PT_lift_unique {A P : Type} [Group A] [Finite A] [Group P] {ρ : A →* P}
    (h : OddCentralCover ρ) {b : A} (hb : b * b = 1) {X : Subgroup P}
    (hX : IsComponentIn X (centralizer ({ρ b} : Set P)))
    (hu : ∀ K : Subgroup P, IsComponentIn K (centralizer ({ρ b} : Set P)) → K = X) :
    IsComponentIn (coverDerived ρ X) (centralizer ({b} : Set A)) ∧
      (coverDerived ρ X).map ρ = X ∧
      ∀ K : Subgroup A, IsComponentIn K (centralizer ({b} : Set A)) → K = coverDerived ρ X := by
  refine ⟨h.isComponentIn_coverDerived hb hX, sec63PT_map_coverDerived h hX.isQuasisimple, ?_⟩
  intro K hK
  have hKi : IsComponentIn (K.map ρ) (centralizer ({ρ b} : Set P)) := by
    have hmap := sec63PT_isComponentIn_map ρ h.ker_le_center hK
    rwa [h.map_centralizer_singleton hb] at hmap
  have hKmap : K.map ρ = X := hu (K.map ρ) hKi
  have hCoverMap : (coverDerived ρ X).map ρ = X := sec63PT_map_coverDerived h hX.isQuasisimple
  exact sec63PT_eq_of_map_eq_in ρ h.ker_le_center hK
    (h.isComponentIn_coverDerived hb hX) (by rw [hKmap, hCoverMap])

theorem sec63PT_two_bound {A P : Type} [Group A] [Finite A] [Group P] {ρ : A →* P}
    (h : OddCentralCover ρ) {V Vb : Subgroup A} {b : A}
    (h2 : ∀ Q : Subgroup P, IsPGroup 2 Q →
      Q ≤ V.map ρ ⊓ centralizer ({ρ b} : Set P) ⊓ centralizer ((Vb.map ρ : Subgroup P) : Set P) →
        Nat.card Q ≤ 2) :
    ∀ Q : Subgroup A, IsPGroup 2 Q →
      Q ≤ V ⊓ centralizer ({b} : Set A) ⊓ centralizer (Vb : Set A) → Nat.card Q ≤ 2 := by
  intro Q hQ hQle
  have hQmap : IsPGroup 2 (Q.map ρ) := hQ.map ρ
  have hle' : Q.map ρ ≤ V.map ρ ⊓ centralizer ({ρ b} : Set P) ⊓
      centralizer ((Vb.map ρ : Subgroup P) : Set P) := by
    rintro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    have hqm := hQle hq
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hqm
    obtain ⟨⟨hqV, hqb⟩, hqVb⟩ := hqm
    have hqb' : q * b = b * q :=
      (Subgroup.mem_centralizer_singleton_iff (g := b) (k := q)).mp hqb
    have hqVb' : ∀ v ∈ Vb, v * q = q * v :=
      (Subgroup.mem_centralizer_iff (g := q) (s := (Vb : Set A))).mp hqVb
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨q, hqV, rfl⟩
    · exact (Subgroup.mem_centralizer_singleton_iff (g := ρ b) (k := ρ q)).mpr (by
        rw [← map_mul, ← map_mul, hqb'])
    · refine (Subgroup.mem_centralizer_iff (g := ρ q)
        (s := ((Vb.map ρ : Subgroup P) : Set P))).mpr ?_
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_mul, ← map_mul, hqVb' v hv]
  exact sec63PT_card_le_two_of_map h.odd_card_ker hQ (h2 (Q.map ρ) hQmap hle')

theorem sec63PT_R_lift {A P : Type} [Group A] [Finite A] [Group P] {ρ : A →* P}
    (h : OddCentralCover ρ) {V : Subgroup A} {b : A} (hb : b * b = 1)
    {R : Subgroup P} (h2 : IsPGroup 2 R) (hle : R ≤ V.map ρ ⊓ centralizer ({ρ b} : Set P))
    (h8 : Nat.card R = 8) (hgen : R = closure {r : P | r ∈ R ∧ orderOf r = 2}) :
    ∃ S : Subgroup A, IsPGroup 2 S ∧ S ≤ V ⊓ centralizer ({b} : Set A) ∧ Nat.card S = 8 ∧
      S = closure {s : A | s ∈ S ∧ orderOf s = 2} := by
  have hle' : R ≤ (V ⊓ centralizer ({b} : Set A)).map ρ := by
    rw [sec63PT_map_inf_centralizer h hb]
    exact hle
  obtain ⟨S, hSH, hS2, hS8, hSgen⟩ :=
    sec63PT_exists_lift_gen ρ h.odd_card_ker (V ⊓ centralizer ({b} : Set A)) R h2 hle' h8 hgen
  exact ⟨S, hS2, hSH, hS8, hSgen⟩

end CFSG.OddStandard.SmallF3.Omega
