module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017CentFix
public import CFSG.Sporadic.Co1Block.TwoACent
public import CFSG.Sporadic.Co1Block.TwoCCent
public import Certificates.Certificate431007
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Bound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Dag
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Tree
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017J3McL
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Co1Block.TwoBCentBase2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

section Generic

variable {Y : Type} [Group Y]

theorem card_centralizer_image_conj (g : Y) (S : Set Y) :
    Nat.card (Subgroup.centralizer ((fun x => g * x * g⁻¹) '' S)) =
      Nat.card (Subgroup.centralizer S) := by
  refine (Nat.card_congr (α := Subgroup.centralizer S)
      (β := Subgroup.centralizer ((fun x => g * x * g⁻¹) '' S))
    { toFun := fun x => ⟨g * (x : Y) * g⁻¹, ?_⟩
      invFun := fun x => ⟨g⁻¹ * (x : Y) * g, ?_⟩
      left_inv := fun x => Subtype.ext (by
        show g⁻¹ * (g * (x : Y) * g⁻¹) * g = x
        group)
      right_inv := fun x => Subtype.ext (by
        show g * (g⁻¹ * (x : Y) * g) * g⁻¹ = x
        group) }).symm
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have h := Subgroup.mem_centralizer_iff.1 x.2 s hs
    calc g * s * g⁻¹ * (g * x * g⁻¹) = g * (s * x) * g⁻¹ := by group
      _ = g * (x * s) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * (g * s * g⁻¹) := by group
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := Subgroup.mem_centralizer_iff.1 x.2 (g * s * g⁻¹) ⟨s, hs, rfl⟩
    calc s * (g⁻¹ * x * g) = g⁻¹ * ((g * s * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * s * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * x * g * s := by group

theorem comm_two_pow {g a b : Y} (ha : a * g = g * a) (hb : b * g = g * b) (m n : ℕ) :
    g * (a ^ m * b ^ n) = a ^ m * b ^ n * g :=
  (((Commute.symm ha).pow_right m).mul_right ((Commute.symm hb).pow_right n)).eq

theorem card_centralizer_of_isConj {t r : Y} (h : IsConj t r) :
    Nat.card (Subgroup.centralizer ({t} : Set Y)) = Nat.card (Subgroup.centralizer ({r} : Set Y)) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  rw [← hg, ← card_centralizer_image_conj g {t}, Set.image_singleton]

theorem coe_map_conj (g : Y) (F : Subgroup Y) :
    ((F.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y) = (fun x => g * x * g⁻¹) '' F := by
  ext x
  simp [MulAut.conj_apply]

theorem not_dvd_card_centralizer_of_sylow [Finite Y] {p n m : ℕ} (hp : p.Prime) {t r : Y}
    (hc : IsConj t r) {F Fr : Subgroup Y} (hF : F ≤ Subgroup.centralizer ({t} : Set Y))
    (hFr : Fr ≤ Subgroup.centralizer ({r} : Set Y)) (hcF : Nat.card F = p ^ n)
    (hcFr : Nat.card Fr = p ^ n)
    (hmax : ¬ p ^ (n + 1) ∣ Nat.card (Subgroup.centralizer ({r} : Set Y)))
    (hb : ¬ m ∣ Nat.card (Subgroup.centralizer (Fr : Set Y))) :
    ¬ m ∣ Nat.card (Subgroup.centralizer (F : Set Y)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 hc
  set F' : Subgroup Y := F.map (MulAut.conj g).toMonoidHom with hF'def
  have hF'C : F' ≤ Subgroup.centralizer ({r} : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.1 (hF hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hg]
    calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hx']
      _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group
  have hcF' : Nat.card F' = p ^ n := by
    rw [hF'def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcF]
  set C := Subgroup.centralizer ({r} : Set Y) with hCdef
  have hCne : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card C).factorization p = n := by
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      exact hmax ((Nat.Prime.pow_dvd_iff_le_factorization hp hCne).2 hlt)
    · rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hCne, ← hcFr]
      exact Subgroup.card_dvd_of_le hFr
  have hcard1 : Nat.card (F'.subgroupOf C) = p ^ (Nat.card C).factorization p := by
    rw [hfac, ← hcF']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF'C).toEquiv
  have hcard2 : Nat.card (Fr.subgroupOf C) = p ^ (Nat.card C).factorization p := by
    rw [hfac, ← hcFr]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFr).toEquiv
  let P1 : Sylow p C := Sylow.ofCard (F'.subgroupOf C) hcard1
  let P2 : Sylow p C := Sylow.ofCard (Fr.subgroupOf C) hcard2
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq C P1 P2
  set F'' : Subgroup Y := F'.map (MulAut.conj (h : Y)).toMonoidHom with hF''def
  have hle : F'' ≤ Fr := by
    rintro _ ⟨y, hy, rfl⟩
    have hyC : y ∈ C := hF'C hy
    have hmem : (⟨y, hyC⟩ : C) ∈ (P1 : Subgroup C) := Subgroup.mem_subgroupOf.2 hy
    have h2 : (MulAut.conj h) • (⟨y, hyC⟩ : C) ∈ (P2 : Subgroup C) := by
      rw [← hh, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul (⟨y, hyC⟩ : C) (MulAut.conj h) (P1 : Subgroup C) hmem
    have h3 := Subgroup.mem_subgroupOf.1 h2
    simpa [MulAut.smul_def, MulAut.conj_apply] using h3
  have hcF'' : Nat.card F'' = Nat.card Fr := by
    rw [hF''def, Subgroup.card_map_of_injective (MulAut.conj (h : Y)).injective, hcF', hcFr]
  have heq : F'' = Fr := Subgroup.eq_of_le_of_card_ge hle hcF''.ge
  have hcent : Nat.card (Subgroup.centralizer (Fr : Set Y)) =
      Nat.card (Subgroup.centralizer (F : Set Y)) := by
    rw [← heq, hF''def, coe_map_conj, card_centralizer_image_conj, hF'def, coe_map_conj,
      card_centralizer_image_conj]
  rwa [← hcent]

end Generic

section Helpers

open CFSG.Sporadic.Co1Schreier

theorem ga_comm_iff (a b : GA) : a * b = b * a ↔ (a : GL24) * b = b * a := by
  rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]

theorem setOf_mem_three {G : Type*} (a b c : G) :
    {g | g ∈ [a, b, c]} = ({a, b, c} : Set G) := by
  ext x
  simp

end Helpers

section Data

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Dickson.I271.TabCo1
  CFSG.LocalAnalysis.GLTheoremA.H1017.Co1FiveNative CFSG.Sporadic.Co1.TwoBNative


theorem side_facts {tR f₁R f₂R f₃R : Native.Rows} {t f₁ f₂ f₃ : GL24} (rt : MRep tR t)
    (r₁ : MRep f₁R f₁) (r₂ : MRep f₂R f₂) (r₃ : MRep f₃R f₃) (ht : t ∈ GA) (h₁ : f₁ ∈ GA)
    (h₂ : f₂ ∈ GA) (h₃ : f₃ ∈ GA) {nfix : ℕ} {base : List ℕ} {conds : List (List Cond)}
    {cnts : List ℕ} {span : List (ℕ × ℕ)} {comb : List ℕ}
    (h : sideOK tR f₁R f₂R f₃R nfix base conds cnts span comb = true) :
    ∃ (T : GA) (F : Subgroup GA), orderOf T = 2 ∧ (xFix (T : GL24)).ncard = nfix ∧
      F ≤ Subgroup.centralizer ({T} : Set GA) ∧ Nat.card F = 5 ^ 2 ∧
      125 ∣ Nat.card (Subgroup.centralizer (F : Set GA)) ∧
      Nat.card (Subgroup.centralizer (F : Set GA)) ≤ 1999 := by
  simp only [sideOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨htt, hv, hne, hfix, hc₁, hc₂, h₁₂, h₁₃, h₂₃, hFok, hFsz, hEok, hEsz, hb, hprod⟩ := h
  have ct₁ : t * f₁ = f₁ * t := (rt.mul r₁).eq (by rw [hc₁]; exact r₁.mul rt)
  have ct₂ : t * f₂ = f₂ * t := (rt.mul r₂).eq (by rw [hc₂]; exact r₂.mul rt)
  have c₁₂ : f₁ * f₂ = f₂ * f₁ := (r₁.mul r₂).eq (by rw [h₁₂]; exact r₂.mul r₁)
  have c₁₃ : f₁ * f₃ = f₃ * f₁ := (r₁.mul r₃).eq (by rw [h₁₃]; exact r₃.mul r₁)
  have c₂₃ : f₂ * f₃ = f₃ * f₂ := (r₂.mul r₃).eq (by rw [h₂₃]; exact r₃.mul r₂)
  obtain ⟨T, rfl⟩ : ∃ T : GA, (T : GL24) = t := ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨F₁, rfl⟩ : ∃ F₁ : GA, (F₁ : GL24) = f₁ := ⟨⟨f₁, h₁⟩, rfl⟩
  obtain ⟨F₂, rfl⟩ : ∃ F₂ : GA, (F₂ : GL24) = f₂ := ⟨⟨f₂, h₂⟩, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup GA, F = Subgroup.closure {F₁, F₂} := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup GL24,
      H = Subgroup.centralizer ({(F₁ : GL24), (F₂ : GL24)} : Set GL24) ⊓ GA := ⟨_, rfl⟩
  have hmemF : ∀ x : GA, x ∈ Subgroup.centralizer (F : Set GA) ↔
      (F₁ : GL24) * x = x * F₁ ∧ (F₂ : GL24) * x = x * F₂ := by
    intro x
    constructor
    · intro hx
      have hx' := Subgroup.mem_centralizer_iff.1 hx
      rw [hFdef] at hx'
      exact ⟨(ga_comm_iff _ _).1 (hx' _ (Subgroup.subset_closure (Set.mem_insert _ _))),
        (ga_comm_iff _ _).1 (hx' _ (Subgroup.subset_closure
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))))⟩
    · rintro ⟨hx₁, hx₂⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hle : F ≤ Subgroup.centralizer ({x} : Set GA) := by
        rw [hFdef, Subgroup.closure_le]
        intro z hz
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        rcases hz with rfl | hz
        · exact (ga_comm_iff _ _).2 hx₁
        · rw [Set.mem_singleton_iff] at hz
          subst hz
          exact (ga_comm_iff _ _).2 hx₂
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  have hHA : H ≤ GA := by rw [hHdef]; exact inf_le_right
  have hcardH : Nat.card (Subgroup.centralizer (F : Set GA)) = Nat.card H := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : GA) : GL24), ?_⟩
        invFun := fun y => ⟨⟨y, ?_⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · obtain ⟨hx₁, hx₂⟩ := (hmemF x).1 x.2
      rw [hHdef]
      refine ⟨Subgroup.mem_centralizer_iff.2 fun z hz => ?_, (x : GA).2⟩
      rcases hz with rfl | hz
      · exact hx₁
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hx₂
    · exact hHA y.2
    · have hy : (y : GL24) ∈ Subgroup.centralizer ({(F₁ : GL24), (F₂ : GL24)} : Set GL24) ⊓ GA :=
        hHdef ▸ y.2
      have hy' := Subgroup.mem_centralizer_iff.1 hy.1
      exact (hmemF _).2 ⟨hy' _ (Set.mem_insert _ _),
        hy' _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  have hr : List.Forall₂ MRep (betas f₁R f₂R)
      ((List.range 25).map fun i => (F₁ : GL24) ^ (i / 5) * (F₂ : GL24) ^ (i % 5)) := by
    unfold betas
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro i _
    exact (r₁.pow _).mul (r₂.pow _)
  have hcomm : ∀ g ∈ H, ∀ β ∈ ((List.range 25).map fun i =>
      (F₁ : GL24) ^ (i / 5) * (F₂ : GL24) ^ (i % 5)), g * β = β * g := by
    intro g hg β hβ
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hβ
    rw [hHdef] at hg
    have hg' := Subgroup.mem_centralizer_iff.1 hg.1
    exact comm_two_pow (hg' _ (Set.mem_insert _ _))
      (hg' _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) (i / 5) (i % 5)
  have hHle := card_le_of_listBound hr hHA hcomm (by simp [betas]) hb
  have hE : Nat.card (Subgroup.closure ({(F₁ : GL24), (F₂ : GL24), f₃} : Set GL24)) = 125 := by
    have := card_closure_list (List.Forall₂.cons r₁ (List.Forall₂.cons r₂
      (List.Forall₂.cons r₃ List.Forall₂.nil))) hEok
    rwa [hEsz, setOf_mem_three] at this
  have hEH : Subgroup.closure ({(F₁ : GL24), (F₂ : GL24), f₃} : Set GL24) ≤ H := by
    rw [hHdef, Subgroup.closure_le]
    intro z hz
    have hzc : ∀ w ∈ ({(F₁ : GL24), (F₂ : GL24)} : Set GL24), w * z = z * w := by
      intro w hw
      rcases hz with rfl | rfl | hz
      · rcases hw with rfl | hw
        · rfl
        · rw [Set.mem_singleton_iff] at hw
          subst hw
          exact c₁₂.symm
      · rcases hw with rfl | hw
        · exact c₁₂
        · rw [Set.mem_singleton_iff] at hw
          subst hw
          rfl
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        rcases hw with rfl | hw
        · exact c₁₃
        · rw [Set.mem_singleton_iff] at hw
          subst hw
          exact c₂₃
    refine ⟨Subgroup.mem_centralizer_iff.2 hzc, ?_⟩
    rcases hz with rfl | rfl | hz
    · exact F₁.2
    · exact F₂.2
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact h₃
  have hFcard : Nat.card F = 5 ^ 2 := by
    have hmap : F.map GA.subtype = Subgroup.closure ({(F₁ : GL24), (F₂ : GL24)} : Set GL24) := by
      rw [hFdef, MonoidHom.map_closure, Set.image_pair]
      rfl
    have := card_closure_list (List.Forall₂.cons r₁ (List.Forall₂.cons r₂ List.Forall₂.nil))
      hFok
    rw [hFsz, setOf_mem_pair, ← hmap, Subgroup.card_map_of_injective GA.subtype_injective] at this
    exact this.trans (by norm_num)
  refine ⟨T, F, orderOf_two_of_rows rt T.2 htt hv hne, by rw [ncard_fix_certX rt, hfix], ?_,
    hFcard, ?_, ?_⟩
  · rw [hFdef, Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hz with rfl | hz
    · exact ((ga_comm_iff _ _).2 ct₁).symm
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ((ga_comm_iff _ _).2 ct₂).symm
  · rw [hcardH, ← hE]
    exact Subgroup.card_dvd_of_le hEH
  · rw [hcardH]
    exact hHle.trans hprod

theorem co1Five_sides :
    (∃ (T : GA) (F : Subgroup GA), orderOf T = 2 ∧ (xFix (T : GL24)).ncard = 2280 ∧
      F ≤ Subgroup.centralizer ({T} : Set GA) ∧ Nat.card F = 5 ^ 2 ∧
      125 ∣ Nat.card (Subgroup.centralizer (F : Set GA)) ∧
      Nat.card (Subgroup.centralizer (F : Set GA)) ≤ 1999) ∧
    (∃ (T : GA) (F : Subgroup GA), orderOf T = 2 ∧ (xFix (T : GL24)).ncard = 0 ∧
      F ≤ Subgroup.centralizer ({T} : Set GA) ∧ Nat.card F = 5 ^ 2 ∧
      125 ∣ Nat.card (Subgroup.centralizer (F : Set GA)) ∧
      Nat.card (Subgroup.centralizer (F : Set GA)) ≤ 1999) := by
  have h := (Certificates.certificate431007 : co1FiveCheck () = true)
  simp only [co1FiveCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hD, hA⟩, hB⟩ := h
  exact ⟨side_facts (rep_nd hD 91) (rep_nd hD 88) (rep_nd hD 94) (rep_nd hD 92) (kG_mem _ 91)
      (kG_mem _ 88) (kG_mem _ 94) (kG_mem _ 92) hA,
    side_facts (rep_nd hD 95) (rep_nd hD 88) (rep_nd hD 92) (rep_nd hD 93) (kG_mem _ 95)
      (kG_mem _ 88) (kG_mem _ 92) (kG_mem _ 93) hB⟩

theorem card_cent_classes :
    Nat.card (Subgroup.centralizer ({aC} : Set GA)) = 89181388800 ∧
      Nat.card (Subgroup.centralizer ({cC} : Set GA)) = 389283840 ∧
      Nat.card (Subgroup.centralizer ({a₁} : Set GA)) = 2012774400 := by
  refine ⟨?_, ?_, card_cent_a₁⟩
  · rw [card_centralizer_GA, coe_aC]
    exact card_cent_aG
  · rw [card_centralizer_GA, coe_cC]
    exact card_cent_cG

theorem co1_five_ha (t : GA) (ht : orderOf t = 2) :
    ¬ 5 ^ (2 + 1) ∣ Nat.card (Subgroup.centralizer ({t} : Set GA)) := by
  obtain ⟨hA, hC, hB⟩ := card_cent_classes
  rcases involution_classes.1 t ht with h | h | h
  · rw [card_centralizer_of_isConj h, hA]; norm_num
  · rw [card_centralizer_of_isConj h, hC]; norm_num
  · rw [card_centralizer_of_isConj h, hB]; norm_num

theorem co1_five_hb (t : GA) (ht : orderOf t = 2) (F : Subgroup GA)
    (hF : F ≤ Subgroup.centralizer ({t} : Set GA)) (_ : IsElemAbelian 5 F)
    (hcF : Nat.card F = 5 ^ 2) : ¬ 2 ^ 4 ∣ Nat.card (Subgroup.centralizer (F : Set GA)) := by
  obtain ⟨hA, hC, hB⟩ := card_cent_classes
  obtain ⟨⟨TA, FA, hTA, hfA, hFA, hcFA, h125A, hleA⟩, ⟨TB, FB, hTB, hfB, hFB, hcFB, h125B, hleB⟩⟩ :=
    co1Five_sides
  have hnot : ∀ n : ℕ, 0 < n → 125 ∣ n → n ≤ 1999 → ¬ 2 ^ 4 ∣ n := fun n h0 h1 h2 h3 => by
    omega
  have hposA := (Nat.card_pos (α := Subgroup.centralizer (FA : Set GA)))
  have hposB := (Nat.card_pos (α := Subgroup.centralizer (FB : Set GA)))
  have hTAa : IsConj TA aC := by
    rcases involution_classes.1 TA hTA with h | h | h
    · exact h
    · have := ncard_fix_isConj h
      rw [ncard_fix_cC, hfA] at this
      norm_num at this
    · have := ncard_fix_isConj h
      rw [ncard_fix_a₁, hfA] at this
      norm_num at this
  have hTBb : IsConj TB a₁ := isConj_a₁_of_ncard_fix hTB hfB
  rcases involution_classes.1 t ht with h | h | h
  · have hc : IsConj t TA := h.trans hTAa.symm
    refine not_dvd_card_centralizer_of_sylow Nat.prime_five hc hF hFA hcF hcFA ?_
      (hnot _ hposA h125A hleA)
    rw [card_centralizer_of_isConj hTAa, hA]
    norm_num
  · have hdvd := Subgroup.card_dvd_of_le hF
    rw [hcF, card_centralizer_of_isConj h, hC] at hdvd
    norm_num at hdvd
  · have hc : IsConj t TB := h.trans hTBb.symm
    refine not_dvd_card_centralizer_of_sylow Nat.prime_five hc hF hFB hcF hcFB ?_
      (hnot _ hposB h125B hleB)
    rw [card_centralizer_of_isConj hTBb, hB]
    norm_num

set_option maxRecDepth 10000 in
theorem twoRankLe_five_co1 : TwoRankLe 5 .Co1 2 := by
  have hb0 : Nonempty (CFSG.Blueprint.NativeSporadic.Co1 ≃*
      (TauCeti.CFSGIndex.sporadic .Co1).Group) := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  obtain ⟨b⟩ := hb0
  have hbr : Nonempty (↥GA ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group) :=
    ⟨co1MatEquiv.symm.trans b⟩
  have hGA : GLATwoLocalRank 5 ↥GA ≤ 2 :=
    glaTwoLocalRank_le_of_cent (p := 5) (k := 2) (m := 4) Nat.prime_five (by norm_num)
      (fun j hj0 hj4 => by interval_cases j <;> decide) co1_five_ha co1_five_hb
  have key := @twoRankLe_of_model .Co1 5 2 Nat.prime_five ↥GA _
  refine key hbr fun K _ _ hK => ?_
  obtain ⟨φ⟩ := hK
  have hcongr := @CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr K ↥GA _ _
  have he := hcongr (p := 5) (by norm_num) φ
  omega

end Data

end CFSG.LocalAnalysis.GLTheoremA.H1017
