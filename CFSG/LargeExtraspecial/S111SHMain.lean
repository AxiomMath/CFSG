module

public import CFSG.LargeExtraspecial.S111SHCor3
public import CFSG.LargeExtraspecial.S111CShult
public import CFSG.LargeExtraspecial.S4CEMain
public import CFSG.LargeExtraspecial.S14Early
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4

@[expose] def GoldschmidtConcl (X : Type) [Group X] (P : Sylow 2 X) (A : Subgroup X) : Prop :=
  let M : Subgroup X := Subgroup.normalClosure (A : Set X)
  have π := QuotientGroup.mk' (goldschmidtOddCore M)
  have T := ((P : Subgroup X).subgroupOf M).map π ⊓ goldschmidtLayer (M ⧸ goldschmidtOddCore M)
  CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊤ ∧
  (A.subgroupOf M).map π =
    CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
  ∀ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ →
    goldschmidtSimpleType (K ⧸ Subgroup.center K)

theorem goldschmidtConcl_of
    (X : Type) [Group X] [Finite X] (P : Sylow 2 X) (A : Subgroup X) (hAP : A ≤ P)
    (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (P : Subgroup X) → g⁻¹ * a * g ∈ A) :
    GoldschmidtConcl X P A :=
  CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian X P A hAP hAab hcl

variable {G : Type} [Group G] [Finite G]

theorem map_subtype_wcl (S : Setting G) {t : S.O} (htM : t ∈ S.Mbar) :
    (wcl (⟨t, htM⟩ : S.Mbar)).map S.Mbar.subtype =
      closure {y : S.O | ∃ m ∈ S.Mbar, y = m * t * m⁻¹ ∧ y * t = t * y} := by
  rw [wcl, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨m, rfl, hm⟩, rfl⟩
    refine ⟨m, m.2, by simp, ?_⟩
    simpa using congrArg Subtype.val hm
  · rintro ⟨m, hm, rfl, hc⟩
    refine ⟨⟨m, hm⟩ * ⟨t, htM⟩ * (⟨m, hm⟩ : S.Mbar)⁻¹,
      ⟨⟨m, hm⟩, rfl, Subtype.ext (by simpa using hc)⟩, rfl⟩

theorem isMulCommutative_wcl_of (S : Setting G) {t : S.O} (htM : t ∈ S.Mbar)
    (hab : IsMulCommutative
      (closure {y : S.O | ∃ m ∈ S.Mbar, y = m * t * m⁻¹ ∧ y * t = t * y})) :
    IsMulCommutative (wcl (⟨t, htM⟩ : S.Mbar)) := by
  rw [← map_subtype_wcl S htM] at hab
  refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
  have := congrArg Subtype.val (hab.is_comm.comm
    ⟨((a : S.Mbar) : S.O), ⟨(a : S.Mbar), a.2, rfl⟩⟩
    ⟨((b : S.Mbar) : S.O), ⟨(b : S.Mbar), b.2, rfl⟩⟩)
  simpa using this

omit [Finite G] in
theorem mem_sylow_of_commute {X : Type*} [Group X] (P : Sylow 2 X) {t : X} (ht2 : t * t = 1)
    (htc : ∀ x ∈ (P : Subgroup X), x * t = t * x) : t ∈ (P : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht2)
  have hz : IsPGroup 2 (zpowers t) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hPN : (P : Subgroup X) ≤ normalizer (zpowers t : Set X) := by
    intro x hx
    refine centralizer_le_normalizer' _ (mem_centralizer_iff.mpr fun h hh => ?_)
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hh
    have hc : Commute t x := (htc x hx).symm
    exact (hc.zpow_left i).eq
  have hmax := P.is_maximal' (P.isPGroup'.to_sup_of_normal_right' hz hPN) le_sup_left
  have h1 : t ∈ (P : Subgroup X) ⊔ zpowers t := (le_sup_right : zpowers t ≤ _) (mem_zpowers t)
  rwa [hmax] at h1

@[expose] def ShultF6Residual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G),
    Hyp S g → ¬ S.IsReducible → 6 ≤ S.width →
    (∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) →
    ∀ (P : Sylow 2 S.Mbar) (t : S.Mbar), (t : S.O) ∈ S.Lbar g → t ≠ 1 →
      t ∈ (P : Subgroup S.Mbar) → (∀ x ∈ (P : Subgroup S.Mbar), x * t = t * x) →
      IsMulCommutative (wcl t) → wcl t ≤ P →
      (∀ a ∈ wcl t, ∀ x : S.Mbar, x⁻¹ * a * x ∈ (P : Subgroup S.Mbar) → x⁻¹ * a * x ∈ wcl t) →
      GoldschmidtConcl S.Mbar P (wcl t) →
      (Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 ∧ CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∧
        timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar) →
      False

theorem shultInput111_of
    (h : ShultF6Residual) : ShultInput111 := by
  intro G _ _ _ S g hy hirr h6 hT P t ht ht1 htP hab
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  have hab' := isMulCommutative_wcl_of S htM hab
  have ht2 : (⟨t, htM⟩ : S.Mbar) * ⟨t, htM⟩ = 1 :=
    Subtype.ext (S4.mul_self_of_mem_Lbar S hy.hyp4.conj_mem ht)
  have htc : ∀ x ∈ (P : Subgroup S.Mbar), x * ⟨t, htM⟩ = ⟨t, htM⟩ * x := fun x hx =>
    Subtype.ext (htP x hx)
  have htP' : (⟨t, htM⟩ : S.Mbar) ∈ (P : Subgroup S.Mbar) := mem_sylow_of_commute P ht2 htc
  obtain ⟨hWP, hcl⟩ := wcl_stronglyClosed P htP' htc hab'
  have hGo := goldschmidtConcl_of S.Mbar P _ hWP hab' hcl
  have h55 := S5.timmesfeld_5_5 S4.centralExtInput (S14.irr_of_not_isReducible hirr) hy.hyp4
    hy.noA2' hy.cons (S45Q.hyp45Q hy.hyp4 hy.cons) (by omega)
  exact h G S g hy hirr h6 hT P ⟨t, htM⟩ ht (fun e => ht1 (congrArg Subtype.val e)) htP' htc
    hab' hWP hcl hGo h55

end CFSG.LargeExtraspecial.S11
