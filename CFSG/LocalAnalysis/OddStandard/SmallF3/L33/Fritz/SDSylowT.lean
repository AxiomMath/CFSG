module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDAutP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDModel
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSylow

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDSylowT

open Subgroup CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

theorem exists_sylow_P (M : SDModel ↥L) :
    ∃ S : Sylow 2 (MulAut ↥L), (S : Subgroup (MulAut ↥L)) = SDAutP.P M.F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut ↥L) :=
    Nat.finite_of_card_ne_zero (by rw [M.card_aut]; norm_num)
  have hfac : (Nat.card (MulAut ↥L)).factorization 2 = 5 := by
    rw [M.card_aut]
    have h' : (11232 : ℕ) = 2 ^ 5 * 351 := by norm_num
    rw [h', Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcard : Nat.card (SDAutP.P M.F) = 2 ^ (Nat.card (MulAut ↥L)).factorization 2 := by
    rw [SDAutP.card_P, hfac]
    norm_num
  exact ⟨Sylow.ofCard (SDAutP.P M.F) hcard, Sylow.coe_ofCard _ _⟩

theorem exists_sylow_compat (hN : centralizer ({t} : Set X) ≤ normalizer (L : Set X))
    (hL : L ≤ centralizer ({t} : Set X)) (M : SDModel ↥L) :
    ∃ T : Sylow 2 ↥(centralizer ({t} : Set X)),
      ∀ g ∈ (T : Subgroup ↥(centralizer ({t} : Set X))), SDAct.actC hN g ∈ SDAutP.P M.F := by
  obtain ⟨S, hS⟩ := exists_sylow_P M
  obtain ⟨T, hT⟩ := SDAct.exists_sylow_actC_le hN hL M.index_inner S
  exact ⟨T, fun g hg => by rw [← hS]; exact hT g hg⟩

theorem card_inf_L (hN : centralizer ({t} : Set X) ≤ normalizer (L : Set X))
    (hL : L ≤ centralizer ({t} : Set X)) (M : SDModel ↥L)
    (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    Nat.card (Config.sylowIn T ⊓ L : Subgroup X) = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card ↥L).factorization 2 = 4 := by
    rw [M.card_L]
    have h' : (5616 : ℕ) = 2 ^ 4 * 351 := by norm_num
    rw [h', Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hup : Nat.card (Config.sylowIn T ⊓ L : Subgroup X) ≤ 16 := by
    have h2 : IsPGroup 2 ((Config.sylowIn T ⊓ L : Subgroup X).subgroupOf L) :=
      (Config.isPGroup_sylowIn T).to_inf_left.comap_of_injective L.subtype (subtype_injective L)
    obtain ⟨Q, hQ⟩ := h2.exists_le_sylow
    have hcQ : Nat.card Q = 16 := by
      rw [Sylow.card_eq_multiplicity, hfac]
      norm_num
    have hle := Subgroup.card_le_of_le hQ
    rw [hcQ, Nat.card_congr
      (subgroupOfEquivOfLe (inf_le_right : Config.sylowIn T ⊓ L ≤ L)).toEquiv] at hle
    exact hle
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  have hcQ : Nat.card Q = 16 := by
    rw [Sylow.card_eq_multiplicity, hfac]
    norm_num
  set Q' : Subgroup (centralizer ({t} : Set X)) :=
    ((Q : Subgroup ↥L).map L.subtype).comap (centralizer ({t} : Set X)).subtype with hQ'
  have hQ'p : IsPGroup 2 Q' := (Q.isPGroup'.map L.subtype).comap_of_injective _
    (subtype_injective _)
  obtain ⟨T', hT'⟩ := hQ'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (centralizer ({t} : Set X)) T' T
  have hsub : ((Q : Subgroup ↥L).map L.subtype).map (MulAut.conj (g : X)).toMonoidHom ≤
      Config.sylowIn T ⊓ L := by
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have hqC : (q : X) ∈ centralizer ({t} : Set X) := hL q.2
      have hqT' : (⟨q, hqC⟩ : centralizer ({t} : Set X)) ∈
          (T' : Subgroup (centralizer ({t} : Set X))) := hT' (by
        rw [mem_comap]
        exact ⟨q, hq, rfl⟩)
      have : g * (⟨q, hqC⟩ : centralizer ({t} : Set X)) * g⁻¹ ∈
          (T : Subgroup (centralizer ({t} : Set X))) := by
        rw [← hg, Sylow.coe_subgroup_smul]
        exact ⟨_, hqT', rfl⟩
      exact ⟨_, this, rfl⟩
    · have := (mem_normalizer_iff.mp (hN g.2) q).mp q.2
      simpa [MulAut.conj_apply] using this
  have hlow : 16 ≤ Nat.card (Config.sylowIn T ⊓ L : Subgroup X) := by
    have hle := Subgroup.card_le_of_le hsub
    rw [card_map_of_injective (MulAut.conj (g : X)).injective,
      card_map_of_injective L.subtype_injective, hcQ] at hle
    exact hle
  omega

theorem ker_le_sylowIn
    (hK : IsPGroup 2 ↥(centralizer ({t} : Set X) ⊓ centralizer (L : Set X)))
    (hN : centralizer ({t} : Set X) ≤ normalizer (L : Set X))
    (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    (centralizer ({t} : Set X) ⊓ centralizer (L : Set X) : Subgroup X) ≤ Config.sylowIn T := by
  have hK'eq :
      (centralizer ({t} : Set X) ⊓ centralizer (L : Set X) : Subgroup X).subgroupOf
          (centralizer ({t} : Set X)) = (SDAct.actC hN).ker := by
    ext c
    rw [Subgroup.mem_subgroupOf, SDAct.mem_ker_actC hN]
    exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩
  have hK'p : IsPGroup 2
      ((centralizer ({t} : Set X) ⊓ centralizer (L : Set X) : Subgroup X).subgroupOf
        (centralizer ({t} : Set X))) :=
    hK.comap_of_injective (centralizer ({t} : Set X)).subtype (subtype_injective _)
  have hle :
      ((centralizer ({t} : Set X) ⊓ centralizer (L : Set X) : Subgroup X).subgroupOf
        (centralizer ({t} : Set X))) ≤ (T : Subgroup ↥(centralizer ({t} : Set X))) := by
    have hnormal :
        ((centralizer ({t} : Set X) ⊓ centralizer (L : Set X) : Subgroup X).subgroupOf
          (centralizer ({t} : Set X))).Normal := by
      rw [hK'eq]
      infer_instance
    haveI := hnormal
    exact hK'p.le_sylow_of_normal T
  intro k hk
  have hk' : k ∈ (centralizer ({t} : Set X) ⊓ centralizer (L : Set X) : Subgroup X) := hk
  have hkC : k ∈ centralizer ({t} : Set X) := (Subgroup.mem_inf.mp hk').1
  have hkK : (⟨k, hkC⟩ : ↥(centralizer ({t} : Set X))) ∈
      ((centralizer ({t} : Set X) ⊓ centralizer (L : Set X) : Subgroup X).subgroupOf
        (centralizer ({t} : Set X))) := by
    rw [Subgroup.mem_subgroupOf]
    exact hk'
  exact Subgroup.mem_map_of_mem (centralizer ({t} : Set X)).subtype (hle hkK)

end CFSG.OddStandard.SmallF3.L33.KD.SDSylowT
