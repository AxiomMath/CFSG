module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeRk

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

section Normal

variable {Q : Type} [Group Q] [Finite Q]

theorem normal_subgroupOf_of_conj {C L : Subgroup Q}
    (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) : (L.subgroupOf C).Normal :=
  ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hLn g.1 g.2 x hx⟩

theorem glaPComponent_of_normal_quasisimple {p : ℕ} {C L : Subgroup Q} (hLC : L ≤ C)
    (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hcore : GLAPPrimeCore p ↥C = ⊥) : GLAPComponent p C L := by
  have hnorm : (L.subgroupOf C).Normal := normal_subgroupOf_of_conj hLn
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) :=
    mk'_injective_of_eq_bot _ hcore
  have hnormπ : ((L.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore p ↥C))).Normal :=
    hnorm.map _ (QuotientGroup.mk'_surjective _)
  refine ⟨hLC, IsSubnormal.step hLC hnorm (IsSubnormal.refl C),
    ⟨le_top, IsSubnormal.step le_top (hnormπ.subgroupOf ⊤) (IsSubnormal.refl ⊤), ?_⟩, ?_⟩
  · have e1 : ↥(L.subgroupOf C) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
    have e2 : ↥(L.subgroupOf C) ≃*
        ↥((L.subgroupOf C).map (QuotientGroup.mk' (GLAPPrimeCore p ↥C))) :=
      Subgroup.equivMapOfInjective _ _ hinj
    exact isQuasisimple_of_mulEquiv' (e1.symm.trans e2) hLq
  · intro J hJ _ heq
    have h1 : J.subgroupOf C = L.subgroupOf C := Subgroup.map_injective hinj heq
    have h2 : J ⊓ C = L ⊓ C := Subgroup.subgroupOf_inj.1 h1
    rw [inf_of_le_left (hJ.le.trans hLC), inf_of_le_left hLC] at h2
    exact hJ.ne h2

theorem glaPPrimeCore_eq_bot_of_normal_quasisimple {p : ℕ} (hp : p.Prime) {C L : Subgroup Q}
    (hLC : L ≤ C) (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hpL : p ∣ Nat.card ↥L) (hcent : IsPGroup p ↥(C ⊓ Subgroup.centralizer (L : Set Q))) :
    GLAPPrimeCore p ↥C = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup ↥C := GLAPPrimeCore p ↥C with hN
  have hcop : Nat.Coprime p (Nat.card N) := CFSG.pPrimeCore_coprime_card (p := p) (G := ↥C)
  have hnorm : (L.subgroupOf C).Normal := normal_subgroupOf_of_conj hLn
  have e1 : ↥(L.subgroupOf C) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  have hq1 : CFSG.Open.IsQuasisimple ↥(L.subgroupOf C) :=
    isQuasisimple_of_mulEquiv' e1.symm hLq
  have hq' : CFSG.IsQuasisimple ↥(L.subgroupOf C) :=
    ⟨⟨hq1.1⟩, hq1.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq1⟩
  have hK : CFSG.IsComponent (L.subgroupOf C) := ⟨hq', Subgroup.Normal.isSubnormal hnorm⟩
  rcases CFSG.LocalCores.component_normal_subgroup hK (inferInstance : N.Normal) with h | h
  · exfalso
    have h1 : Nat.card (L.subgroupOf C) ∣ Nat.card N := Subgroup.card_dvd_of_le h
    have h2 : p ∣ Nat.card (L.subgroupOf C) := by
      rw [Nat.card_congr e1.toEquiv]
      exact hpL
    exact hp.ne_one (hcop.eq_one_of_dvd (h2.trans h1))
  · have hle : N.map C.subtype ≤ C ⊓ Subgroup.centralizer (L : Set Q) := by
      rintro _ ⟨n, hn, rfl⟩
      refine ⟨n.2, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro l hl
      have hl' : (⟨l, hLC hl⟩ : ↥C) ∈ L.subgroupOf C := hl
      have hc : ⁅(⟨l, hLC hl⟩ : ↥C), n⁆ ∈ ⁅L.subgroupOf C, N⁆ :=
        Subgroup.commutator_mem_commutator hl' hn
      rw [h, Subgroup.mem_bot] at hc
      have := congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.1 hc)
      exact this
    have hNp : IsPGroup p N :=
      (hcent.to_le hle).of_equiv (N.equivMapOfInjective C.subtype C.subtype_injective).symm
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hNp
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at hcop
      exact hp.ne_one (hcop.eq_one_of_dvd (dvd_pow_self p hk0))
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq N hk

theorem eq_of_glaPComponent_of_normal_quasisimple {p : ℕ} (hp : p.Prime) {C L J : Subgroup Q}
    (hLC : L ≤ C) (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hcore : GLAPPrimeCore p ↥C = ⊥) (hcent : IsPGroup p ↥(C ⊓ Subgroup.centralizer (L : Set Q)))
    (hJ : GLAPComponent p C J) : J = L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hL : GLAPComponent p C L := glaPComponent_of_normal_quasisimple hLC hLn hLq hcore
  by_contra hne
  have hb : barX p C J ≠ barX p C L := fun h => hne (glaPComponent_unique hJ hL h)
  have hcomm : ⁅barX p C J, barX p C L⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hJ.2.2.1 hL.2.2.1 hb
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥C)) :=
    mk'_injective_of_eq_bot _ hcore
  have hJC : J ≤ C := hJ.1
  have hJcent : J ≤ C ⊓ Subgroup.centralizer (L : Set Q) := by
    intro x hx
    refine ⟨hJC hx, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro l hl
    have hx' : (⟨x, hJC hx⟩ : ↥C) ∈ J.subgroupOf C := hx
    have hl' : (⟨l, hLC hl⟩ : ↥C) ∈ L.subgroupOf C := hl
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hJC hx⟩ ∈ barX p C J :=
      Subgroup.mem_map_of_mem _ hx'
    have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨l, hLC hl⟩ ∈ barX p C L :=
      Subgroup.mem_map_of_mem _ hl'
    have hc : ⁅QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨x, hJC hx⟩,
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨l, hLC hl⟩⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator h1 h2
      rw [hcomm, Subgroup.mem_bot] at this
      exact this
    rw [← map_commutatorElement] at hc
    have hc2 := hinj (hc.trans (map_one _).symm)
    have := commutatorElement_eq_one_iff_mul_comm.1 hc2
    exact (congrArg Subtype.val this).symm
  have hJp : IsPGroup p ↥J := hcent.to_le hJcent
  have hbp : IsPGroup p ↥(barX p C J) := by
    have h1 : IsPGroup p ↥(J.subgroupOf C) :=
      hJp.of_equiv (Subgroup.subgroupOfEquivOfLe hJC).symm
    exact h1.of_equiv ((J.subgroupOf C).equivMapOfInjective _ hinj)
  have hq := hJ.2.2.1.2.2
  haveI : Nontrivial ↥(barX p C J) := by
    have := hq.2.exists_pair_ne
    obtain ⟨a, b, hab⟩ := this
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [h])⟩
  haveI : Group.IsNilpotent ↥(barX p C J) := hbp.isNilpotent
  have hsolv : Group.IsSolvable ↥(barX p C J) := inferInstance
  have hperf : Group.IsPerfect ↥(barX p C J) := ⟨hq.1⟩
  exact Group.IsPerfect.not_isSolvable _ hsolv

theorem shapeRkAt_of_normal_quasisimple {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop} {t : Q} {L : Subgroup Q}
    (hLC : L ≤ Subgroup.centralizer ({t} : Set Q))
    (hLn : ∀ g ∈ Subgroup.centralizer ({t} : Set Q), ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hpL : p ∣ Nat.card ↥L)
    (hcent : IsPGroup p ↥(Subgroup.centralizer ({t} : Set Q) ⊓ Subgroup.centralizer (L : Set Q)))
    (hG : Good (PSimple p L)) (hR : Rk (PQuot p L)) : ShapeRkAt p Good Rk t := by
  have hcore := glaPPrimeCore_eq_bot_of_normal_quasisimple hp hLC hLn hLq hpL hcent
  exact Or.inr ⟨L, glaPComponent_of_normal_quasisimple hLC hLn hLq hcore,
    fun I hI => eq_of_glaPComponent_of_normal_quasisimple hp hLC hLn hLq hcore hcent hI, hG, hR⟩

end Normal

end CFSG.HardMathSupport.Dickson.I271
