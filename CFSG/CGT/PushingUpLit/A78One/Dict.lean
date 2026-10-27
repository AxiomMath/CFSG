module

public import CFSG.CGT.PushingUpLit.A78One.DictStar
public import CFSG.RankThree.PartOne.S12.Sec15Final

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2K
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {L M T T' : Subgroup G} {n : ℕ}

theorem normalizer_blockU_eq_of (hyp : T2Hyp G L M n)
    (nM : M ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup.normalizer (blockU L : Set G) = M := by
  have hMV : M ≤ Subgroup.normalizer (blockU L : Set G) :=
    NatBlock.le_normalizer_blockU_of_le nM
  by_contra hne
  exact hyp.maxLocal.2 _ (lt_of_le_of_ne hMV (Ne.symm hne))
    ⟨blockU L, hyp.blockU_ne_bot, isPGroup_blockU' L, rfl⟩

theorem normalizer_eq_of (hyp : T2Hyp G L M n) (nM : M ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup.normalizer (L : Set G) = M := by
  refine le_antisymm (fun g hg => ?_) nM
  rw [← normalizer_blockU_eq_of hyp nM, Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => conj_mem_blockU hg hu, fun hu => ?_⟩
  have := conj_mem_blockU ((Subgroup.normalizer (L : Set G)).inv_mem hg) hu
  simpa [mul_assoc] using this

theorem normalizer_M_of (hyp : T2Hyp G L M n) : Subgroup.normalizer (M : Set G) = M :=
  RankThree.PartTwo.Late.normalizer_self_of_isMaximalTwoLocal hyp.maxLocal

theorem normalizer_le_of (hyp : T2Hyp G L M n) {B : Subgroup G} (hB : B ≠ ⊥)
    (hB2 : IsPGroup 2 B) (hL : L ≤ Subgroup.normalizer (B : Set G)) :
    Subgroup.normalizer (B : Set G) ≤ M := by
  have hloc : IsPLocal 2 (Subgroup.normalizer (B : Set G)) := ⟨B, hB, hB2, rfl⟩
  obtain ⟨N, hle, hNmax⟩ := Sec15Final.exists_isMaximalTwoLocal_ge hloc
  have hNM : N = M := by
    have : N ∈ maximalTwoLocalsContaining (L : Set G) := ⟨hNmax, fun x hx => hle (hL hx)⟩
    rw [hyp.unique] at this
    exact this
  rw [← hNM]
  exact hle

theorem le_of_isMax_T_of (hyp : T2Hyp G L M n) (nM : M ≤ Subgroup.normalizer (L : Set G))
    (sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hge : (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (blockU L : Set G)) ≤ T') {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) : A ≤ T' := by
  by_cases hAU : A ≤ Subgroup.centralizer (blockU L : Set G)
  · exact (le_inf hA.1 hAU).trans (le_sup_right.trans hge)
  · have H : Hyp45 L M T A n := ⟨hyp.natBlock, hyp.le, nM, sylow, hA, hAU⟩
    intro a ha
    have h1 := H.lOf_mem_T ⟨a, ha⟩
    have h2 := H.tOf_mem ⟨a, ha⟩
    apply hge
    have e : a = H.lOf ⟨a, ha⟩ * ((H.lOf ⟨a, ha⟩)⁻¹ * a) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left ⟨h1, H.lOf_mem _⟩) (Subgroup.mem_sup_right h2)

theorem isMax_iff_of (hyp : T2Hyp G L M n) (nM : M ≤ Subgroup.normalizer (L : Set G))
    (sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hle : T' ≤ T)
    (hge : (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (blockU L : Set G)) ≤ T') {A : Subgroup G} :
    IsMaxElemAbelian T A ↔ IsMaxElemAbelian T' A := by
  constructor
  · intro hA
    exact ⟨le_of_isMax_T_of hyp nM sylow hge hA, hA.2.1,
      fun B hB hBe => hA.2.2 B (hB.trans hle) hBe⟩
  · intro hA
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
    have h0 := hA.2.2 A₀ (le_of_isMax_T_of hyp nM sylow hge hA₀) hA₀.2.1
    exact ⟨hA.1.trans hle, hA.2.1, fun B hB hBe => (hA₀.2.2 B hB hBe).trans h0⟩

theorem le_normalizer_P_of (hyp : T2Hyp G L M n) (nM : M ≤ Subgroup.normalizer (L : Set G))
    (sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    L ≤ Subgroup.normalizer ((cexP L T : Subgroup G) : Set G) := by
  have key : ∀ l ∈ L, ∀ p ∈ cexP L T, l * p * l⁻¹ ∈ cexP L T := by
    intro l hl p hp
    have hpM : p ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨sylow.le hp.1, hp.2⟩
    have h1 := hyp.natBlock.comm_centralizer_mem_blockU nM hpM l hl
    have hVP : blockU L ≤ cexP L T :=
      le_inf (NatBlock.blockU_le_sylow hyp.le nM sylow) (fun v hv =>
        Subgroup.mem_centralizer_iff.2 fun w hw => hyp.natBlock.blockU_comm w hw v hv)
    have e : l * p * l⁻¹ = (⁅p, l⁆)⁻¹ * p := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (inv_mem (hVP h1)) hp
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro p
  exact ⟨fun hp => key l hl p hp, fun hp => by
    have := key l⁻¹ (L.inv_mem hl) _ hp
    simpa [mul_assoc] using this⟩

omit [Finite G] in
theorem le_normalizer_P'_of (nM : M ≤ Subgroup.normalizer (L : Set G))
    (sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    T ≤ Subgroup.normalizer ((cexP L T : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro p
  have hV : t ∈ Subgroup.normalizer (blockU L : Set G) :=
    NatBlock.le_normalizer_blockU_of_le nM (sylow.le ht)
  have hC : t ∈ Subgroup.normalizer (Subgroup.centralizer (blockU L : Set G) : Set G) :=
    mem_normalizer_centralizer hV
  have h1 := Subgroup.mem_normalizer_iff.1 hC p
  have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer ht : t ∈ Subgroup.normalizer
    (T : Set G)) p
  simp only [Subgroup.mem_inf, h1, h2]

omit [Finite G] in
theorem isPGroup_cexP (sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M) : IsPGroup 2 (cexP L T) :=
  sylow.isPGroup.to_le inf_le_left

omit [Finite G] in
private theorem exists_pow_mem_centralizer_of_isPGroup {R : Subgroup G} (hR : IsPGroup 2 R)
    (L : Subgroup G) : ∀ x ∈ R, ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (L : Set G) := by
  intro x hx
  obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
  refine ⟨k, ?_⟩
  rw [show x ^ 2 ^ k = 1 from congrArg Subtype.val hk]
  exact one_mem _

theorem oTwoIn_sup_eq (hyp : T2Hyp G L M n) (nM : M ≤ Subgroup.normalizer (L : Set G))
    (sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hle : T' ≤ T)
    (hge : (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (blockU L : Set G)) ≤ T') :
    oTwoIn (L ⊔ T') = cexP L T := by
  have hHN : L ⊔ T' ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer ((hle.trans sylow.le).trans nM)
  apply le_antisymm
  · have hRU : oTwoIn (L ⊔ T') ≤ Subgroup.centralizer (blockU L : Set G) :=
      hyp.natBlock.le_centralizer_of_two_quot le_sup_left hHN (oTwoIn_le _)
        (SixThree.le_normalizer_oTwoIn _)
        (exists_pow_mem_centralizer_of_isPGroup (isPGroup_oTwoIn _) L)
    exact (le_inf (oTwoIn_le _) hRU).trans (centralizer_U_of hyp nM sylow hle hge).le
  · have hPT' : cexP L T ≤ T' := le_sup_right.trans hge
    refine SixThree.le_oTwoIn_of_isPGroup (hPT'.trans le_sup_right) (isPGroup_cexP sylow) ?_
    exact sup_le (le_normalizer_P_of hyp nM sylow) (hle.trans (le_normalizer_P'_of nM sylow))

namespace CexCtx

variable {x : G}

theorem normalizer_eq (c : CexCtx L M n T T' x) : Subgroup.normalizer (L : Set G) = M :=
  normalizer_eq_of c.hyp c.nM

theorem normalizer_M (c : CexCtx L M n T T' x) : Subgroup.normalizer (M : Set G) = M :=
  normalizer_M_of c.hyp

theorem normalizer_le (c : CexCtx L M n T T' x) {B : Subgroup G} (hB : B ≠ ⊥)
    (hB2 : IsPGroup 2 B) (hL : L ≤ Subgroup.normalizer (B : Set G)) :
    Subgroup.normalizer (B : Set G) ≤ M :=
  normalizer_le_of c.hyp hB hB2 hL

theorem isMax_iff (c : CexCtx L M n T T' x) {A : Subgroup G} :
    IsMaxElemAbelian T A ↔ IsMaxElemAbelian T' A :=
  isMax_iff_of c.hyp c.nM c.sylow c.le c.ge

theorem oTwoIn_H (c : CexCtx L M n T T' x) : oTwoIn (L ⊔ T') = cexP L T :=
  oTwoIn_sup_eq c.hyp c.nM c.sylow c.le c.ge

theorem oTwoIn_LT (c : CexCtx L M n T T' x) : oTwoIn (L ⊔ T) = cexP L T :=
  oTwoIn_sup_eq c.hyp c.nM c.sylow le_rfl (sup_le inf_le_left inf_le_left)

end CexCtx

end CFSG.CGT.PushingUpLit.A78One
