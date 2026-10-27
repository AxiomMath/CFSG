module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsS1

public section

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

variable {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁)
include hx

omit hPC in
theorem outer_mem_P_of_mem_centralizer_V₀ {s : G} (hs : s ∈ P ⊔ zpowers x)
    (hsC : s ∈ centralizer (V₀ : Set G)) : s ∈ P := by
  rcases (outer_mem_sup_iff hx).mp hs with h1 | h1
  · exact h1
  · exfalso
    apply h.outer_not_mem_centralizer_V₀ hx
    rw [mem_centralizer_iff]
    intro w hw
    have h2 := outer_conj_V₀ hP hx h1 hw
    have h3 : s * w * s⁻¹ = w := by
      rw [← mem_centralizer_iff.mp hsC w hw]
      group
    rw [h3] at h2
    calc w * x = x * w * x⁻¹ * x := by rw [← h2]
      _ = x * w := by group

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
  {V' : Subgroup G} (hV' : IsVprime (R ⊔ T) V₀ P V')
include hIIa hV'

theorem outer_sylow (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (S : Sylow 2 G) (hS₁S : P ⊔ zpowers x ≤ S) :
    (S : Subgroup G) ≤ normalizer ((P ⊔ zpowers x : Subgroup G) : Set G) ∧
      Nat.card (S : Subgroup G) = 256 ∧
      (S : Subgroup G) ⊓ normalizer ((R ⊔ T : Subgroup G) : Set G) = P ⊔ zpowers x ∧
      (∀ s ∈ (S : Subgroup G), s ∉ P ⊔ zpowers x →
        rightConjugate (R ⊔ T) s = V' ∧ rightConjugate V' s = R ⊔ T) ∧
      ∀ E : Subgroup G, E ≤ S → IsElemAbelian 2 E → Nat.card E = 16 → E = R ⊔ T ∨ E = V' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hSp : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hS₁ := h.outer_isSylowOf_sup hP hPC hx hP64
  have hS₁S' : P ⊔ zpowers x < S :=
    lt_of_le_of_ne hS₁S (h.outer_sup_ne_sylow hP hPC hx hV' hGold hGs hP64 S).symm
  obtain ⟨S₂, hS₂⟩ : ∃ S₂ : Subgroup G,
      (S : Subgroup G) ⊓ normalizer ((P ⊔ zpowers x : Subgroup G) : Set G) = S₂ := ⟨_, rfl⟩
  have hS₁S₂ : P ⊔ zpowers x < S₂ := hS₂ ▸ lt_inf_normalizer hSp hS₁S'
  have hS₂S : S₂ ≤ S := hS₂ ▸ inf_le_left
  have hS₂N : S₂ ≤ normalizer ((P ⊔ zpowers x : Subgroup G) : Set G) := hS₂ ▸ inf_le_right
  have hS₂p : IsPGroup 2 S₂ := hSp.to_le hS₂S
  have hS₂V : S₂ ⊓ normalizer ((R ⊔ T : Subgroup G) : Set G) = P ⊔ zpowers x :=
    hS₁.eq_of_le (le_inf hS₁S₂.le hS₁.le) inf_le_right (hS₂p.to_le inf_le_left)
  have hconj : ∀ s ∈ S₂, ∀ X : Subgroup G, X ≤ P ⊔ zpowers x →
      rightConjugate X s ≤ P ⊔ zpowers x := by
    intro s hs X hX
    have h1 : rightConjugate X s ≤ rightConjugate (P ⊔ zpowers x) s := map_mono hX
    rwa [(rightConjugate_eq_self_iff _ s).mpr (hS₂N hs)] at h1
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  have hES₁ : ∀ E : Subgroup G, E ≤ P ⊔ zpowers x → IsElemAbelian 2 E → Nat.card E = 16 →
      E = R ⊔ T ∨ E = V' := fun E hE hEe hE16 =>
    h.outer_eq_or_eq_of_elemAbelian hP hPC hx hIIa hV' hE hEe hE16
  have hVV' : R ⊔ T ≠ V' := h.ne_of_inf_eq hV'.inf
  have hswap : ∀ s ∈ S₂, s ∉ P ⊔ zpowers x →
      rightConjugate (R ⊔ T) s = V' ∧ rightConjugate V' s = R ⊔ T := by
    intro s hs hsS₁
    have hVs : rightConjugate (R ⊔ T) s = V' := by
      rcases hES₁ _ (hconj s hs _ (hVP.trans le_sup_left))
        (isElemAbelian_rightConjugate h.loc.elem s)
        (by rw [rightConjugate_card, h.loc.card]) with h1 | h1
      · exfalso
        apply hsS₁
        rw [← hS₂V]
        exact mem_inf.mpr ⟨hs, (rightConjugate_eq_self_iff _ s).mp h1⟩
      · exact h1
    refine ⟨hVs, ?_⟩
    rcases hES₁ _ (hconj s hs _ (hV'.le.trans le_sup_left))
      (isElemAbelian_rightConjugate hV'.elem s) (by rw [rightConjugate_card, hV'.card]) with
      h1 | h1
    · exact h1
    · exact absurd (rightConjugate_injective (hVs.trans h1.symm)) hVV'
  obtain ⟨s₀, hs₀, hs₀S₁⟩ := IsConcreteLE.exists_of_lt hS₁S₂
  have hidx : (P ⊔ zpowers x).relIndex S₂ = 2 := by
    change ((P ⊔ zpowers x).subgroupOf S₂).index = 2
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨s₀, hs₀⟩, hs₀S₁, fun b => ?_⟩
    by_cases hb : (b : G) ∈ P ⊔ zpowers x
    · exact Or.inr hb
    · left
      change (b : G) * s₀ ∈ P ⊔ zpowers x
      rw [← hS₂V]
      refine mem_inf.mpr ⟨mul_mem b.2 hs₀, ?_⟩
      rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, (hswap b b.2 hb).1,
        (hswap s₀ hs₀ hs₀S₁).2]
  have hS₂256 : Nat.card S₂ = 256 := by
    have h1 := Subgroup.relIndex_mul_card (P ⊔ zpowers x) S₂
    rw [hidx, inf_eq_left.mpr hS₁S₂.le, outer_card_sup hx hP64] at h1
    omega
  have hP4 : P.relIndex S₂ = 4 := by
    have h1 := Subgroup.relIndex_mul_card P S₂
    rw [inf_eq_left.mpr (le_sup_left.trans hS₁S₂.le), hP64, hS₂256] at h1
    omega
  have hES₂ : ∀ E : Subgroup G, E ≤ S₂ → IsElemAbelian 2 E → Nat.card E = 16 →
      E = R ⊔ T ∨ E = V' := by
    intro E hES hE hE16
    by_cases hES₁' : E ≤ P ⊔ zpowers x
    · exact hES₁ E hES₁' hE hE16
    exfalso
    obtain ⟨e, heE, heS₁⟩ := IsConcreteLE.not_le_iff_exists.mp hES₁'
    obtain ⟨hVe, hV'e⟩ := hswap e (hES heE) heS₁
    have hcomm : ∀ y ∈ E, ∀ y' ∈ E, y * y' * y⁻¹ = y' := by
      intro y hy y' hy'
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
      simp only [coe_mul] at this
      rw [this]
      group
    have hsub : P ⊓ E ≤ V₀ := by
      rcases h.le_or_le_of_elemAbelian hP hPC hV'.inv hV₀V' inf_le_left
        (isElemAbelian_of_le hE inf_le_right) with h1 | h1
      · intro y hy
        rw [← hV'.inf]
        refine mem_inf.mpr ⟨h1 hy, ?_⟩
        rw [← hVe, mem_rightConjugate_iff, hcomm e heE y (mem_inf.mp hy).2]
        exact h1 hy
      · intro y hy
        rw [← hV'.inf]
        refine mem_inf.mpr ⟨?_, h1 hy⟩
        rw [← hV'e, mem_rightConjugate_iff, hcomm e heE y (mem_inf.mp hy).2]
        exact h1 hy
    have hle : (P ⊔ zpowers x).relIndex E ≤ 2 := by
      have h1 := Subgroup.relIndex_le_of_le_right (H := P ⊔ zpowers x) hES (by
        rw [hidx]
        norm_num)
      exact h1.trans (le_of_eq hidx)
    have h8 : 8 ≤ Nat.card ((P ⊔ zpowers x) ⊓ E : Subgroup G) := by
      have h1 := Subgroup.relIndex_mul_card (P ⊔ zpowers x) E
      rw [hE16] at h1
      have h2 : 16 ≤ 2 * Nat.card ((P ⊔ zpowers x) ⊓ E : Subgroup G) :=
        h1 ▸ Nat.mul_le_mul_right _ hle
      omega
    by_cases hS₁E : (P ⊔ zpowers x) ⊓ E ≤ P
    · have hle' : (P ⊔ zpowers x) ⊓ E ≤ V₀ := fun y hy =>
        hsub (mem_inf.mpr ⟨hS₁E hy, (mem_inf.mp hy).2⟩)
      have := card_le_of_le hle'
      rw [h.card_V₀] at this
      omega
    · obtain ⟨u, huS₁E, huP⟩ := IsConcreteLE.not_le_iff_exists.mp hS₁E
      obtain ⟨huS₁, huE⟩ := mem_inf.mp huS₁E
      have hxu : x * u ∈ P := ((outer_mem_sup_iff hx).mp huS₁).resolve_left huP
      have hle4 : P.relIndex E ≤ 4 := by
        have h1 := Subgroup.relIndex_le_of_le_right (H := P) hES (by
          rw [hP4]
          norm_num)
        exact h1.trans (le_of_eq hP4)
      have h4 : 4 ≤ Nat.card (P ⊓ E : Subgroup G) := by
        have h1 := Subgroup.relIndex_mul_card P E
        rw [hE16] at h1
        have h2 : 16 ≤ 4 * Nat.card (P ⊓ E : Subgroup G) := h1 ▸ Nat.mul_le_mul_right _ hle4
        omega
      have hPE : P ⊓ E = V₀ := eq_of_le_of_card_ge hsub (by rw [h.card_V₀]; exact h4)
      apply h.outer_not_mem_centralizer_V₀ hx
      rw [mem_centralizer_iff]
      intro w hw
      have hwE : w ∈ E := (mem_inf.mp (show w ∈ P ⊓ E by rw [hPE]; exact hw)).2
      have h2 := outer_conj_V₀ hP hx hxu hw
      rw [hcomm u huE w hwE] at h2
      calc w * x = x * w * x⁻¹ * x := by rw [← h2]
        _ = x * w := by group
  have hNV : ∀ n ∈ normalizer (S₂ : Set G), n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) →
      n ∈ normalizer ((P ⊔ zpowers x : Subgroup G) : Set G) := by
    intro n hn hnV
    rw [← hS₂V]
    exact mem_normalizer_inf hn (le_normalizer hnV)
  have hNS₂ : normalizer (S₂ : Set G) ≤ normalizer ((P ⊔ zpowers x : Subgroup G) : Set G) := by
    intro n hn
    have hS₂n : rightConjugate S₂ n = S₂ := (rightConjugate_eq_self_iff S₂ n).mpr hn
    have hVn : rightConjugate (R ⊔ T) n ≤ S₂ := by
      have h1 : rightConjugate (R ⊔ T) n ≤ rightConjugate S₂ n :=
        map_mono (hVP.trans (le_sup_left.trans hS₁S₂.le))
      rwa [hS₂n] at h1
    rcases hES₂ _ hVn (isElemAbelian_rightConjugate h.loc.elem n)
      (by rw [rightConjugate_card, h.loc.card]) with h1 | h1
    · exact hNV n hn ((rightConjugate_eq_self_iff _ n).mp h1)
    · have hns : n * s₀ ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := by
        rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, h1, (hswap s₀ hs₀ hs₀S₁).2]
      have h2 := hNV (n * s₀) (mul_mem hn (le_normalizer hs₀)) hns
      have h3 : n = n * s₀ * s₀⁻¹ := by group
      rw [h3]
      exact mul_mem h2 (inv_mem (hS₂N hs₀))
  have hS₂eq : S₂ = S := by
    by_contra hne
    obtain ⟨n, hn, hnS₂⟩ :=
      IsConcreteLE.exists_of_lt (lt_inf_normalizer hSp (lt_of_le_of_ne hS₂S hne))
    apply hnS₂
    rw [← hS₂]
    exact mem_inf.mpr ⟨(mem_inf.mp hn).1, hNS₂ (mem_inf.mp hn).2⟩
  subst hS₂eq
  exact ⟨inf_eq_left.mp hS₂, hS₂256, hS₂V, hswap, hES₂⟩

variable (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G) (hP64 : Nat.card P = 64)
  (S : Sylow 2 G) (hS₁S : P ⊔ zpowers x ≤ S)
include hGold hGs hP64 hS₁S

omit hIIa in
theorem outer_lt_sylow : P ⊔ zpowers x < S :=
  lt_of_le_of_ne hS₁S (h.outer_sup_ne_sylow hP hPC hx hV' hGold hGs hP64 S).symm

theorem outer_relIndex_sylow : (P ⊔ zpowers x).relIndex S = 2 := by
  obtain ⟨-, h256, -, -, -⟩ := h.outer_sylow hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  have h1 := Subgroup.relIndex_mul_card (P ⊔ zpowers x) S
  rw [inf_eq_left.mpr hS₁S, outer_card_sup hx hP64, h256] at h1
  omega

theorem outer_relIndex_P : P.relIndex S = 4 := by
  obtain ⟨-, h256, -, -, -⟩ := h.outer_sylow hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  have h1 := Subgroup.relIndex_mul_card P S
  rw [inf_eq_left.mpr (le_sup_left.trans hS₁S), hP64, h256] at h1
  omega

theorem outer_le_normalizer_P : (S : Subgroup G) ≤ normalizer (P : Set G) := by
  obtain ⟨-, -, -, hswap, -⟩ := h.outer_sylow hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  intro s hs
  by_cases hsS₁ : s ∈ P ⊔ zpowers x
  · exact (sup_le le_normalizer (zpowers_le.mpr hx.normP)) hsS₁
  · obtain ⟨h1, h2⟩ := hswap s hs hsS₁
    rw [← rightConjugate_eq_self_iff, ← hV'.sup]
    change ((R ⊔ T) ⊔ V').map (MulAut.conj s⁻¹).toMonoidHom = _
    rw [Subgroup.map_sup]
    change rightConjugate (R ⊔ T) s ⊔ rightConjugate V' s = _
    rw [h1, h2]
    exact sup_comm _ _

theorem outer_le_normalizer_V₀ : (S : Subgroup G) ≤ normalizer (V₀ : Set G) := by
  obtain ⟨-, -, -, hswap, -⟩ := h.outer_sylow hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  intro s hs
  by_cases hsS₁ : s ∈ P ⊔ zpowers x
  · exact h.normalizer_le_normalizer_V₀
      ((sup_le (fun n hn => (hP.le hn).1) (zpowers_le.mpr hx.normV)) hsS₁)
  · obtain ⟨h1, h2⟩ := hswap s hs hsS₁
    rw [← rightConjugate_eq_self_iff, ← hV'.inf]
    change ((R ⊔ T) ⊓ V').map (MulAut.conj s⁻¹).toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj s⁻¹).injective]
    change rightConjugate (R ⊔ T) s ⊓ rightConjugate V' s = _
    rw [h1, h2]
    exact inf_comm _ _

theorem outer_mul_mem_centralizer_V₀ {s : G} (hs : s ∈ (S : Subgroup G))
    (hsC : s ∉ centralizer (V₀ : Set G)) : s * x ∈ centralizer (V₀ : Set G) :=
  mul_mem_centralizer_of_card_four h.card_V₀ (fun _ hw => h.mul_self (h.V₀_le hw))
    S.isPGroup' (h.outer_le_normalizer_V₀ hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S) hs
    (hS₁S (mem_sup_right (mem_zpowers x))) hsC (h.outer_not_mem_centralizer_V₀ hx)

theorem outer_comm_z {s : G} (hs : s ∈ (S : Subgroup G)) : s * z = z * s := by
  by_cases hsC : s ∈ centralizer (V₀ : Set G)
  · exact (mem_centralizer_iff.mp hsC z hx.z_mem).symm
  · have h1 := mem_centralizer_iff.mp
      (h.outer_mul_mem_centralizer_V₀ hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S hs hsC) z hx.z_mem
    calc s * z = s * (x * z * x⁻¹) := by rw [hx.z_comm]; group
      _ = s * x * z * x⁻¹ := by group
      _ = z * (s * x) * x⁻¹ := by rw [← h1]
      _ = z * s := by group

theorem outer_sq_mem {s : G} (hs : s ∈ (S : Subgroup G)) : s * s ∈ P := by
  have hidx := h.outer_relIndex_sylow hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  have hs1 : s * s ∈ P ⊔ zpowers x := by
    by_cases hsS₁ : s ∈ P ⊔ zpowers x
    · exact mul_mem hsS₁ hsS₁
    · have := CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hidx (inv_mem hs) hs
        (by rwa [inv_mem_iff]) hsS₁
      rwa [inv_inv] at this
  have hs2 : s * s ∈ centralizer (V₀ : Set G) := by
    by_cases hsC : s ∈ centralizer (V₀ : Set G)
    · exact mul_mem hsC hsC
    · exact mul_mem_centralizer_of_card_four h.card_V₀ (fun _ hw => h.mul_self (h.V₀_le hw))
        S.isPGroup' (h.outer_le_normalizer_V₀ hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S) hs hs
        hsC hsC
  exact h.outer_mem_P_of_mem_centralizer_V₀ hP hx hs1 hs2

theorem outer_relIndex_centralizer_V₀ :
    ((S : Subgroup G) ⊓ centralizer (V₀ : Set G)).relIndex S = 2 := by
  have hxS : x ∈ (S : Subgroup G) := hS₁S (mem_sup_right (mem_zpowers x))
  have hxC := h.outer_not_mem_centralizer_V₀ hx
  change (((S : Subgroup G) ⊓ centralizer (V₀ : Set G)).subgroupOf S).index = 2
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨⟨x, hxS⟩, fun h' => hxC (mem_inf.mp (mem_subgroupOf.mp h')).2, fun b => ?_⟩
  by_cases hb : (b : G) ∈ centralizer (V₀ : Set G)
  · exact Or.inr (mem_subgroupOf.mpr (mem_inf.mpr ⟨b.2, hb⟩))
  · left
    change (b : G) * x ∈ (S : Subgroup G) ⊓ centralizer (V₀ : Set G)
    exact mem_inf.mpr ⟨mul_mem b.2 hxS,
      h.outer_mul_mem_centralizer_V₀ hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S b.2 hb⟩

theorem outer_mem_centralizer_V₀ {w : G} (hw : w ∈ V₀) (hw1 : w ≠ 1) (hwz : w ≠ z) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hsw : s * w = w * s) : s ∈ centralizer (V₀ : Set G) := by
  by_contra hsC
  have h1 := mem_centralizer_iff.mp
    (h.outer_mul_mem_centralizer_V₀ hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S hs hsC) w hw
  have hxw : x * w = w * x := by
    have h2 : s * (x * w) = s * (w * x) := by
      calc s * (x * w) = s * x * w := (mul_assoc _ _ _).symm
        _ = w * (s * x) := h1.symm
        _ = w * s * x := (mul_assoc _ _ _).symm
        _ = s * w * x := by rw [hsw]
        _ = s * (w * x) := mul_assoc _ _ _
    exact mul_left_cancel h2
  rcases hx.fix_V₀ w hw hxw with h2 | h2
  · exact hw1 h2
  · exact hwz h2

theorem outer_isRootInv_of_mem_V' {v : G} (hv : v ∈ V') (hv0 : v ∉ V₀) : IsRootInv A v := by
  obtain ⟨-, -, -, hswap, -⟩ := h.outer_sylow hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S
  obtain ⟨s₀, hs₀, hs₀S₁⟩ :=
    IsConcreteLE.exists_of_lt (h.outer_lt_sylow hP hPC hx hV' hGold hGs hP64 S hS₁S)
  obtain ⟨h1, -⟩ := hswap s₀ hs₀ hs₀S₁
  have hvV : s₀ * v * s₀⁻¹ ∈ R ⊔ T := by
    rw [← h1] at hv
    exact (mem_rightConjugate_iff _ _ _).mp hv
  have hvV₀ : s₀ * v * s₀⁻¹ ∉ V₀ := fun h0 => hv0 (by
    have h2 := (mem_normalizer_iff.mp
      (inv_mem (h.outer_le_normalizer_V₀ hP hPC hx hIIa hV' hGold hGs hP64 S hS₁S hs₀)) _).mp h0
    have e : s₀⁻¹ * (s₀ * v * s₀⁻¹) * s₀⁻¹⁻¹ = v := by group
    rwa [e] at h2)
  have h3 := (h.isRootInv_of_mem_V hvV hvV₀).conj s₀
  have e : s₀⁻¹ * (s₀ * v * s₀⁻¹) * s₀ = v := by group
  rwa [e] at h3

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
