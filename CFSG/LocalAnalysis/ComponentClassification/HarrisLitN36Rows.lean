module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Unique
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndInputs

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts

@[expose] def Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsQuasisimple G → pPrimeCore 2 G = ⊥ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → IsOfType (InClosure (IsSimpleChevalleyOver p)) G →
    ∀ τ : MulAut G, orderOf τ = 2 →
    ∀ m : ℕ, 1 ≤ m → 16 ∣ p ^ (2 * m) - 1 →
    ∀ K : Subgroup G, IsTwoComponentIn K (fixedPoints τ) →
      (∀ K' : Subgroup G, IsTwoComponentIn K' (fixedPoints τ) → K' = K) →
      Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 p m →
      ¬ IsSimpleGroup G → ¬ IsMType p G →
      (Nonempty (G ⧸ center G ≃* Blueprint.NativeSporadic.J2) ∧ Nat.card ↥(center G) = 2 ∧
          τ ∉ innAut G) ∨
        (Nonempty (G ⧸ center G ≃* Blueprint.NativeSporadic.HS) ∧ Nat.card ↥(center G) = 2 ∧
          Nonempty (↥(generalizedFitting ↥(fixedPoints τ)) ≃*
            Multiplicative (ZMod 4) × ↥(alternatingGroup (Fin 6))) ∧
          τ ∈ innAut G) ∨
        (Blueprint.LieModel (G ⧸ center G) .PSL 3 2 2 ∧ Nat.card ↥(center G) < 16 ∧
          τ ∉ innAut G) ∨
        (∃ k : ℕ, m = 2 * k ∧
          (Blueprint.LieModel (G ⧸ center G) .PSL 4 p k ∨
            Blueprint.LieModel (G ⧸ center G) .PSU 4 p k))

@[expose] def Concl (G : Type) [Group G] (p m : ℕ) (τ : MulAut G) : Prop :=
  (Nonempty (G ⧸ center G ≃* Blueprint.NativeSporadic.J2) ∧ Nat.card ↥(center G) = 2 ∧
      τ ∉ innAut G) ∨
    (Nonempty (G ⧸ center G ≃* Blueprint.NativeSporadic.HS) ∧ Nat.card ↥(center G) = 2 ∧
      Nonempty (↥(generalizedFitting ↥(fixedPoints τ)) ≃*
        Multiplicative (ZMod 4) × ↥(alternatingGroup (Fin 6))) ∧
      τ ∈ innAut G) ∨
    (Blueprint.LieModel (G ⧸ center G) .PSL 3 2 2 ∧ Nat.card ↥(center G) < 16 ∧
      τ ∉ innAut G) ∨
    (∃ k : ℕ, m = 2 * k ∧
      (Blueprint.LieModel (G ⧸ center G) .PSL 4 p k ∨
        Blueprint.LieModel (G ⧸ center G) .PSU 4 p k))

structure Config (G : Type) [Group G] [Finite G] (p m : ℕ) (τ : MulAut G) (K : Subgroup G) :
    Prop where
  quasisimple : IsQuasisimple G
  oddCore : pPrimeCore 2 G = ⊥
  prime : p.Prime
  ne_two : p ≠ 2
  orderOf_eq : orderOf τ = 2
  one_le : 1 ≤ m
  sixteen_dvd : 16 ∣ p ^ (2 * m) - 1
  comp : IsTwoComponentIn K (fixedPoints τ)
  unique : ∀ K' : Subgroup G, IsTwoComponentIn K' (fixedPoints τ) → K' = K
  lieModel : Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 p m
  not_simple : ¬ IsSimpleGroup G
  not_mType : ¬ IsMType p G

@[expose] def RowFor (C : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p m : ℕ) (τ : MulAut G) (K : Subgroup G),
    Config G p m τ K → C (G ⧸ center G) → Concl G p m τ

@[expose] def IsAlt (Y : Type) [Group Y] : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n))

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

theorem perfect (h : Config G p m τ K) : Group.IsPerfect G := h.quasisimple.1

theorem simple_bar (h : Config G p m τ K) : IsSimpleGroup (G ⧸ center G) := h.quasisimple.2.1

theorem nonabelian_bar (h : Config G p m τ K) : ∃ a b : G ⧸ center G, a * b ≠ b * a :=
  h.quasisimple.2.2

theorem center_isPGroup (h : Config G p m τ K) : IsPGroup 2 (center G) :=
  N36.center_isPGroup h.oddCore

theorem center_ne_bot (h : Config G p m τ K) : center G ≠ ⊥ :=
  N36.center_ne_bot h.quasisimple h.not_simple

theorem orderOf_bar (h : Config G p m τ K) : orderOf (quotAut τ) = 2 :=
  orderOf_quotAut_eq_two h.quasisimple h.orderOf_eq

theorem bar_mem_innAut_iff (h : Config G p m τ K) :
    quotAut τ ∈ innAut (G ⧸ center G) ↔ τ ∈ innAut G := by
  have := h.perfect
  exact quotAut_mem_innAut_iff τ

theorem inf_center (h : Config G p m τ K) : K ⊓ center G = ⊥ :=
  inf_center_eq_bot h.oddCore h.lieModel

theorem isTwoComponentIn_bar (h : Config G p m τ K) :
    IsTwoComponentIn (K.map (QuotientGroup.mk' (center G))) (fixedPoints (quotAut τ)) :=
  N36.isTwoComponentIn_bar h.comp h.inf_center

theorem eq_bar (h : Config G p m τ K) {J : Subgroup (G ⧸ center G)}
    (hJ : IsTwoComponentIn J (fixedPoints (quotAut τ))) :
    J = K.map (QuotientGroup.mk' (center G)) :=
  eq_bar_of_isTwoComponentIn h.oddCore h.unique hJ

theorem nonempty_equiv (h : Config G p m τ K) :
    Nonempty (↥K ≃* ↥(K.map (QuotientGroup.mk' (center G)))) :=
  nonempty_equiv_bar h.inf_center

theorem lieModel_bar (h : Config G p m τ K) :
    Blueprint.LieModel (↥(K.map (QuotientGroup.mk' (center G))) ⧸
      pPrimeCore 2 ↥(K.map (QuotientGroup.mk' (center G)))) .PSL 2 p m := by
  obtain ⟨e⟩ := h.nonempty_equiv
  exact GSThmB.OddQuot.lieModel_of_equiv
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e) h.lieModel

theorem seven_le (h : Config G p m τ K) : 7 ≤ p ^ m :=
  Hin.seven_le_of_sixteen_dvd h.prime h.ne_two h.one_le h.sixteen_dvd

theorem isComponent_bar (h : Config G p m τ K)
    (hO : pPrimeCore 2 ↥(fixedPoints (quotAut τ)) = ⊥) :
    IsComponent ((K.map (QuotientGroup.mk' (center G))).subgroupOf (fixedPoints (quotAut τ))) ∧
      Blueprint.LieModel ↥((K.map (QuotientGroup.mk' (center G))).subgroupOf
        (fixedPoints (quotAut τ))) .PSL 2 p m := by
  have hc := h.isTwoComponentIn_bar
  have hp := (isTwoComponentIn_iff hc.1).mp hc
  have hcomp := (isTwoComponent_iff_isComponent hO _).mp
    ((isTwoComponent_iff_isPComponent _).mpr hp)
  refine ⟨hcomp, ?_⟩
  have hO' : pPrimeCore 2 ↥((K.map (QuotientGroup.mk' (center G))).subgroupOf
      (fixedPoints (quotAut τ))) = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hcomp.2
  have e1 : ↥((K.map (QuotientGroup.mk' (center G))).subgroupOf (fixedPoints (quotAut τ))) ≃*
      ↥((K.map (QuotientGroup.mk' (center G))).subgroupOf (fixedPoints (quotAut τ))) ⧸
        pPrimeCore 2 ↥((K.map (QuotientGroup.mk' (center G))).subgroupOf
          (fixedPoints (quotAut τ))) :=
    ((QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot).symm
  have e2 := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
    (subgroupOfEquivOfLe hc.1)
  exact GSThmB.OddQuot.lieModel_of_equiv (e1.trans e2).symm h.lieModel_bar

end Config

theorem classicalRep_or_exceptionalRep {Y : Type} [Group Y] {t : Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : Blueprint.LieModel Y t n p f) :
    Milestones.ClassicalRep Y ∨ Blueprint.ExceptionalRep Y := by
  rcases h with ⟨-, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, -, hm⟩
  · exact Or.inl ⟨t, n, p, f, hm⟩
  · exact Or.inr (Or.inl ⟨t, p, f, ht, hm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨t, p, f, ht, hm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p, f, hm⟩))

theorem statement_of_rows (hAlt : RowFor IsAlt) (hCl : RowFor Milestones.ClassicalRep)
    (hEx : RowFor Blueprint.ExceptionalRep) (hSp : RowFor Blueprint.NativeSporadic.SporadicRep) :
    Statement := by
  intro G _ _ hq hO p hp hp2 hF τ hτ m hm h16 K hK hu hL hns hM
  have hc : Config G p m τ K := ⟨hq, hO, hp, hp2, hτ, hm, h16, hK, hu, hL, hns, hM⟩
  rcases catalog_or_chevalley hq hO hF with hcat | ⟨t, n, f, hlie⟩
  · rcases hcat with ⟨q, hq', ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hcl | hex | hsp
    · exfalso
      obtain ⟨a, b, hab⟩ := hc.nonabelian_bar
      apply hab
      apply e.injective
      rw [map_mul, map_mul, mul_comm]
    · exact hAlt G p m τ K hc ⟨n, hn, ⟨e⟩⟩
    · exact hCl G p m τ K hc hcl
    · exact hEx G p m τ K hc hex
    · exact hSp G p m τ K hc hsp
  · rcases classicalRep_or_exceptionalRep hlie with hcl | hex
    · exact hCl G p m τ K hc hcl
    · exact hEx G p m τ K hc hex

end CFSG.ComponentClassification.HarrisLit.N36
