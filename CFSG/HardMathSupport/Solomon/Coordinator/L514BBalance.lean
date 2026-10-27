module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VBalance
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification
  CFSG.ComponentClassification.LBalance Subgroup

section Generic

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem l514b_lBalancePLayer_centralizer_le
    (helem : ∀ (M : Subgroup X) (x : X), x ∈ M → (∃ n : ℕ, x ^ p ^ n = 1) →
      lBalancePLayer p (M ⊓ centralizer ({x} : Set X)) ≤ lBalancePLayer p M)
    (P : Subgroup X) (hP : IsPGroup p P) :
    lBalancePLayer p (centralizer (P : Set X)) ≤ lBalancePLayer p ⊤ := by
  induction hn : Nat.card P using Nat.strong_induction_on generalizing P with
  | h n ih =>
  by_cases hbot : P = ⊥
  · subst hbot
    have htop : centralizer ((⊥ : Subgroup X) : Set X) = ⊤ :=
      centralizer_eq_top_iff_subset.mpr (SetLike.coe_subset_coe.mpr bot_le)
    exact (congrArg (lBalancePLayer p) htop).le
  obtain ⟨Q, hQP, hcard, x, hxP, hxQ, hPQ⟩ := Asm.exists_sup_zpowers hP hbot
  have hxY := Asm.mem_normalizer_centralizer hxQ
  have hYM : centralizer (Q : Set X) ≤ centralizer (Q : Set X) ⊔ zpowers x := le_sup_left
  have hxM : x ∈ centralizer (Q : Set X) ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  have hMN : centralizer (Q : Set X) ⊔ zpowers x ≤ normalizer (centralizer (Q : Set X) : Set X) :=
    sup_le le_normalizer (zpowers_le.mpr hxY)
  have hCP : centralizer (P : Set X) = centralizer (Q : Set X) ⊓ centralizer ({x} : Set X) := by
    refine le_antisymm (le_inf (centralizer_le hQP)
      (centralizer_le (Set.singleton_subset_iff.mpr hxP))) ?_
    rintro z ⟨hzQ, hzx⟩
    have hle : Q ⊔ zpowers x ≤ centralizer ({z} : Set X) := by
      refine sup_le (fun q hq => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hzQ q hq)) (zpowers_le.mpr ?_)
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hzx).symm
    exact mem_centralizer_iff.mpr fun g hg => mem_centralizer_singleton_iff.mp (hle (hPQ hg))
  rw [hCP]
  have : ((centralizer (Q : Set X) ⊓ centralizer ({x} : Set X)).subgroupOf
      ((centralizer (Q : Set X) ⊔ zpowers x) ⊓ centralizer ({x} : Set X))).Normal := by
    refine (normal_subgroupOf_iff (inf_le_inf_right _ hYM)).mpr fun z c hz hc =>
      mem_inf.mpr ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp (hMN (mem_inf.mp hc).1) z).mp (mem_inf.mp hz).1
    · exact mul_mem (mul_mem (mem_inf.mp hc).2 (mem_inf.mp hz).2) (inv_mem (mem_inf.mp hc).2)
  have h1 := pLayer_relative_normal_mono p _ _ (inf_le_inf_right (centralizer ({x} : Set X)) hYM)
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h2 := helem _ x hxM ⟨k, by simpa using congrArg Subtype.val hk⟩
  have : ((centralizer (Q : Set X)).subgroupOf (centralizer (Q : Set X) ⊔ zpowers x)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYM).mpr hMN
  have h3 : lBalancePLayer p (centralizer (Q : Set X) ⊔ zpowers x) ≤
      lBalancePLayer p (centralizer (Q : Set X)) := by
    refine Asm.pLayer_le_of_pComponents_le p _ _ hYM fun L hL => ?_
    have : Group.IsPerfect L := pComponent_perfect p _ L hL
    exact Asm.le_of_perfect_le_sup_zpowers hxY (subnormal_le hL.1)
  have h4 := ih (Nat.card Q) (hcard.trans_eq hn) Q (hP.to_le hQP) rfl
  exact h1.trans (h2.trans (h3.trans h4))

end Generic

section KProper

variable {G : Type} [Group G] [Finite G]

theorem l514b_glaPLayer_centralizer_le_top (hS : CatalogueRelativeB.CatalogueSchreier)
    (hKP : CFSG.Open.IsKProper G) {P : Subgroup G} (hP : IsPGroup 3 ↥P) :
    GLAPLayer 3 (Subgroup.centralizer (P : Set G)) ≤ GLAPLayer 3 (⊤ : Subgroup G) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hKP' : CFSG.IsKProper G :=
    CatalogueKProper.isKProper_of_kProper (CatalogueKProper.open_isKProper_iff.1 hKP)
  rw [i183_glaPLayer_eq, i183_glaPLayer_eq]
  refine l514b_lBalancePLayer_centralizer_le (fun M x hxM hx => ?_) P hP
  by_cases hM : M = ⊤
  · subst hM
    rw [top_inf_eq]
    exact i183v_lBalancePLayer_centralizer_element_le hS hKP' hx
  · have hK : CFSG.Open.IsKGroup ↥M := isKGroup_of_isKProper hKP hM
    have hEp : IsPGroup 3 ↥(zpowers x) := by
      obtain ⟨n, hn⟩ := hx
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hn)
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hcz : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    have := i183_glaPLayer_inf_centralizer_le hS hK hp (zpowers_le.2 hxM) hEp
    rw [hcz] at this
    rwa [i183_glaPLayer_eq, i183_glaPLayer_eq] at this

end KProper

theorem l514b_open_of_isKGroup {X : Type} [Group X] (h : CFSG.IsKGroup X) :
    CFSG.Open.IsKGroup X := fun K L _ _ hs _ => h K (L.subgroupOf K) hs

theorem lemma514Cover_input18_1_of_schreier (hS : CatalogueRelativeB.CatalogueSchreier) :
    LocalBalance.Lemma514CoverNs.Input18_1 := by
  intro G _ _ X hK Q hQX hQ
  exact i183_glaPLayer_inf_centralizer_le hS (l514b_open_of_isKGroup hK) Nat.prime_three hQX hQ

end CFSG.HardMathSupport.Solomon.Coordinator
