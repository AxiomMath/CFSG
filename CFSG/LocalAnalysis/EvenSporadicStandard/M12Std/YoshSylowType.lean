module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

private theorem card_eq_two_of_forall_eq {X : Type*} [Group X] (H : Subgroup X) (a : X)
    (ha : a ≠ 1) (haH : a ∈ H) (h : ∀ x ∈ H, x = 1 ∨ x = a) : Nat.card H = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨a, haH⟩, fun h1 => ha (congrArg Subtype.val h1).symm, ?_⟩
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases h x x.2 with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

private theorem factorization_two_card_alternatingGroup_fin_twelve :
    (Nat.card (alternatingGroup (Fin 12))).factorization 2 = 9 := by
  have hcard : Nat.card (alternatingGroup (Fin 12)) = 2 ^ 9 * 467775 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [hcard, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

private theorem sylowType_of_hom_subgroup {G : Type*} [Group G] [Finite G] (c : G)
    (C S : Subgroup G) (P : Subgroup (alternatingGroup (Fin 12))) (f : ↥S →* ↥P)
    (hc1 : c ≠ 1) (hcC : c ∈ C) (hcS : c ∈ S) (hSC : S ≤ C) (hcc : ∀ g ∈ C, g * c = c * g)
    (hZ : ∀ z ∈ Subgroup.center ↥C, (z : G) = 1 ∨ (z : G) = c)
    (hSsyl : Nat.card S = 2 ^ (Nat.card C).factorization 2)
    (hP : Nat.card P = 2 ^ 9) (hf : Function.Surjective f)
    (hker : ∀ s : ↥S, f s = 1 ↔ (s : G) = 1 ∨ (s : G) = c) :
    ∃ (S₁ : Sylow 2 (↥C ⧸ Subgroup.center ↥C)) (S₂ : Sylow 2 (alternatingGroup (Fin 12))),
      Nonempty (↥(S₁ : Subgroup (↥C ⧸ Subgroup.center ↥C)) ≃*
        ↥(S₂ : Subgroup (alternatingGroup (Fin 12)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcZ : (⟨c, hcC⟩ : ↥C) ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    exact fun g => Subtype.ext (hcc g g.2)
  have hZcard : Nat.card (Subgroup.center ↥C) = 2 :=
    card_eq_two_of_forall_eq _ ⟨c, hcC⟩ (fun h => hc1 (congrArg Subtype.val h)) hcZ
      fun x hx => by
        rcases hZ x hx with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
  have hkerCard : Nat.card f.ker = 2 :=
    card_eq_two_of_forall_eq _ ⟨c, hcS⟩ (fun h => hc1 (congrArg Subtype.val h))
      ((hker _).2 (Or.inr rfl)) fun x hx => by
        rcases (hker x).1 hx with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
  have hSP : Nat.card S = 2 ^ 10 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hP,
      hkerCard] at h
    rw [h]
    norm_num
  have hC10 : (Nat.card C).factorization 2 = 10 :=
    Nat.pow_right_injective le_rfl (hSsyl.symm.trans hSP)
  have hK9 : (Nat.card (↥C ⧸ Subgroup.center ↥C)).factorization 2 = 9 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥C)
    rw [hZcard] at h
    have hK0 : Nat.card (↥C ⧸ Subgroup.center ↥C) ≠ 0 := Nat.card_pos.ne'
    rw [h, Nat.factorization_mul hK0 (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two] at hC10
    omega
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥S →* (↥C ⧸ Subgroup.center ↥C),
      ∀ s : ↥S, φ s = (QuotientGroup.mk (⟨s, hSC s.2⟩ : ↥C) : ↥C ⧸ Subgroup.center ↥C) :=
    ⟨(QuotientGroup.mk' (Subgroup.center ↥C)).comp (Subgroup.inclusion hSC), fun s => rfl⟩
  have hφker : φ.ker = f.ker := by
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker, hφ, QuotientGroup.eq_one_iff]
    refine ⟨fun h => hZ _ h, ?_⟩
    rintro (h | h)
    · have h1 : (⟨s, hSC s.2⟩ : ↥C) = 1 := Subtype.ext h
      rw [h1]
      exact one_mem _
    · have h1 : (⟨s, hSC s.2⟩ : ↥C) = ⟨c, hcC⟩ := Subtype.ext h
      rw [h1]
      exact hcZ
  obtain ⟨e⟩ : Nonempty (↥φ.range ≃* ↥P) :=
    ⟨(QuotientGroup.quotientKerEquivRange φ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hφker).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf))⟩
  have hS1 : Nat.card φ.range = 2 ^ (Nat.card (↥C ⧸ Subgroup.center ↥C)).factorization 2 := by
    rw [Nat.card_congr e.toEquiv, hP, hK9]
  have hS2 : Nat.card P = 2 ^ (Nat.card (alternatingGroup (Fin 12))).factorization 2 := by
    rw [hP, factorization_two_card_alternatingGroup_fin_twelve]
  exact ⟨Sylow.ofCard φ.range hS1, Sylow.ofCard P hS2, ⟨e⟩⟩

theorem sylowType_of_hom {G : Type} [Group G] [Finite G] (c : G) (S : Subgroup G)
    (P : Subgroup (alternatingGroup (Fin 12))) (f : ↥S →* ↥P)
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hcS : c ∈ S) (hSC : ∀ s ∈ S, s * c = c * s)
    (hZ : ∀ z ∈ Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)), (z : G) = 1 ∨ (z : G) = c)
    (hSsyl : Nat.card S = 2 ^ (Nat.card (Subgroup.centralizer ({c} : Set G))).factorization 2)
    (hP : Nat.card P = 2 ^ 9) (hf : Function.Surjective f)
    (hker : ∀ s : ↥S, f s = 1 ↔ (s : G) = 1 ∨ (s : G) = c) :
    ∃ (S₁ : Sylow 2 (↥(Subgroup.centralizer ({c} : Set G)) ⧸
        Subgroup.center ↥(Subgroup.centralizer ({c} : Set G))))
      (S₂ : Sylow 2 (alternatingGroup (Fin 12))),
      Nonempty (↥(S₁ : Subgroup (↥(Subgroup.centralizer ({c} : Set G)) ⧸
          Subgroup.center ↥(Subgroup.centralizer ({c} : Set G)))) ≃*
        ↥(S₂ : Subgroup (alternatingGroup (Fin 12)))) :=
  sylowType_of_hom_subgroup c (Subgroup.centralizer ({c} : Set G)) S P f hc1
    (Subgroup.mem_centralizer_singleton_iff.2 rfl) hcS
    (fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hSC s hs))
    (fun g hg => Subgroup.mem_centralizer_singleton_iff.1 hg) hZ hSsyl hP hf hker

end CFSG.EvenSporadicStandard.M12Std.Yosh
