module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeaklyClosed
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise

variable {X : Type} [Group X]

theorem relativeWeakClosure_le_of_normalizer [Finite X] {G T S M : Subgroup X}
    (hF : Frame G T) (hS2 : IsPGroup 2 S) (hSGT : S ≤ G ⊔ T) (hMS : M ≤ S)
    (hM : relativeWeakClosure G T M = M)
    (hN : ∀ g ∈ G, rightConjugate T g ≤ S ⊓ Subgroup.normalizer (M : Set X) →
      rightConjugate T g ≤ M) :
    relativeWeakClosure G T S ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ y ∈ S, rightConjugate M y ≤ S ⊓ Subgroup.normalizer (M : Set X) →
      rightConjugate M y ≤ M := by
    intro y hy hle
    have hle' : rightConjugate (relativeWeakClosure G T M) y ≤ M := by
      unfold relativeWeakClosure rightConjugate
      rw [Subgroup.map_iSup]
      refine iSup_le fun c => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hc => ?_
      have hcy : (c : X)⁻¹ * y ∈ G ⊔ T :=
        (G ⊔ T).mul_mem (Subgroup.mem_sup_left (G.inv_mem c.2)) (hSGT hy)
      obtain ⟨-, -, g', hg', -, hrc⟩ := hF.exists_rightConjugate_eq hcy
      have heq : (conjugateSubgroup (c : X) T).map (MulAut.conj y⁻¹).toMonoidHom =
          rightConjugate T g' := by
        rw [← hrc, ← rightConjugate_mul]
        unfold rightConjugate
        rw [inv_inv]
      rw [heq]
      apply hN g' hg'
      rw [← heq]
      refine le_trans ?_ hle
      exact rightConjugate_le_rightConjugate (hc.trans le_rfl) y |>.trans le_rfl
    rwa [hM] at hle'
  have hSN : S ≤ Subgroup.normalizer (M : Set X) := by
    by_contra hcon
    let R : Subgroup S := (Subgroup.normalizer (M : Set X)).subgroupOf S
    have hRtop : R < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun hR => hcon fun x hx => ?_
      have hmem : (⟨x, hx⟩ : S) ∈ R := hR ▸ Subgroup.mem_top _
      exact hmem
    have : Group.IsNilpotent S := hS2.isNilpotent
    obtain ⟨y, hyN, hyR⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent R hRtop)
    have hyR' : (y : X) ∉ Subgroup.normalizer (M : Set X) := hyR
    apply hyR'
    rw [← rightConjugate_eq_self_iff]
    apply Subgroup.eq_of_le_of_card_ge _ (rightConjugate_card M y).ge
    apply hconj y y.2
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have hxS : x ∈ S := by
      have hyxy : (y : X) * x * (y : X)⁻¹ ∈ S := hMS hx
      have heq : x = (y : X)⁻¹ * ((y : X) * x * (y : X)⁻¹) * y := by group
      rw [heq]
      exact S.mul_mem (S.mul_mem (S.inv_mem y.2) hyxy) y.2
    refine ⟨hxS, ?_⟩
    have hmem : (⟨(y : X) * x * (y : X)⁻¹, hMS hx⟩ : S) ∈ R :=
      Subgroup.le_normalizer hx
    have hconj' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) _).mp hmem
    have hconj'' := Subgroup.mem_subgroupOf.mp hconj'
    simpa [mul_assoc] using hconj''
  refine iSup_le fun c => iSup_le fun hc => ?_
  have heq : conjugateSubgroup (c : X) T = rightConjugate T (c : X)⁻¹ := by
    unfold rightConjugate
    rw [inv_inv]
  rw [heq] at hc ⊢
  exact hN _ (G.inv_mem c.2) (le_inf hc (hc.trans hSN))

theorem exists_conj_le_normalizer [Finite X] {G T S : Subgroup X} (hF : Frame G T)
    (hS2 : IsPGroup 2 S) (hSGT : S ≤ G ⊔ T) (hTS : T ≤ S) (hW : relativeWeakClosure G T S ≠ T) :
    ∃ g ∈ G, rightConjugate T g ≤ S ⊓ Subgroup.normalizer (T : Set X) ∧
      rightConjugate T g ≠ T := by
  by_contra hcon
  push Not at hcon
  apply hW
  refine le_antisymm (relativeWeakClosure_le_of_normalizer hF hS2 hSGT hTS ?_ ?_)
    (subgroup_le_relative_weak_closure G T S hTS)
  · exact le_antisymm (relative_weak_closure_le G T T)
      (subgroup_le_relative_weak_closure G T T le_rfl)
  · intro g hg hle
    exact (hcon g hg hle).le

namespace Hyp45

variable {G T S Q H : Subgroup X} {g : X}

theorem inf_eq_bot_of_not_le [Finite X] (h : Hyp45 G T S Q H g) {y : X} (hy : y ∈ G)
    {V : Subgroup X} (hVT : V ≤ rightConjugate T y)
    (hVS : V ≤ S ⊓ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X))
    (hVW : ¬ V ≤ T ⊔ rightConjugate T g) : V ⊓ H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := T ⊔ rightConjugate T g with hWdef
  by_contra hne
  obtain ⟨⟨v, hvV, hvH⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
  have hvS : v ∈ S := (hVS hvV).1
  have hvCW : v ∈ Subgroup.centralizer (W : Set X) :=
    (h.inf_eq_centralizer_W.le ⟨hvH, hvS⟩).2
  have hF₁ := h.frame.rightConjugate_frame hy
  have h43₁ := h.hyp43.rightConjugate_hyp hy
  have hGT₁ : G ⊔ rightConjugate T y = G ⊔ T := sup_rightConjugate hy
  have hWS : W ≤ S := h.W_le.trans inf_le_right
  have hWH₁ : W ≤ rightConjugate H y := fun w hw =>
    h43₁.centralizer_le hF₁ (hVT hvV) hv1' ⟨hGT₁ ▸ h.le_sup (hWS hw),
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hvCW w hw)⟩
  have hVH₁ : V ≤ rightConjugate H y := hVT.trans h43₁.le_H
  have hW2 : IsPGroup 2 W := h.isPGroup_S.to_le hWS
  have hV2 : IsPGroup 2 V := h.isPGroup_S.to_le (hVS.trans inf_le_left)
  have hR₀2 : IsPGroup 2 (W ⊔ V : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' hW2 hV2 (hVS.trans inf_le_right)
  obtain ⟨R, hR, hR₀R⟩ := exists_isSylowOf_le hR₀2 (sup_le hWH₁ hVH₁)
  have hRQ := hR.inf_of_le_normalizer h43₁.le h43₁.le_normalizer
  obtain ⟨c, hcQ, hcT⟩ := exists_rightConjugate_eq_of_isSylowOf hRQ h43₁.sylow
  have hycGT : y * c ∈ G ⊔ T :=
    (G ⊔ T).mul_mem (Subgroup.mem_sup_left hy) (hGT₁ ▸ h43₁.le_sup (h43₁.le hcQ))
  obtain ⟨-, -, g₂, hg₂, -, hrc₂⟩ := h.frame.exists_rightConjugate_eq hycGT
  have hT₂eq : R ⊓ rightConjugate Q y = rightConjugate T g₂ := by
    rw [← hcT, rightConjugate_mul, hrc₂]
  have hF₂ := h.frame.rightConjugate_frame hg₂
  have hT₂comm : IsMulCommutative (rightConjugate T g₂) :=
    isMulCommutative_rightConjugate h.isMulCommutative g₂
  have hVT₂ : V ≤ rightConjugate T g₂ := by
    rw [← hT₂eq]
    exact le_inf (le_sup_right.trans hR₀R) (hVT.trans h43₁.le_Q)
  have hRN : R ≤ Subgroup.normalizer (rightConjugate T g₂ : Set X) := by
    rw [← hT₂eq]
    intro r hr
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hr, h43₁.le_normalizer (hR.le hr)⟩
  have hRGT : R ≤ G ⊔ T := hR.le.trans (h43₁.le_sup.trans hGT₁.le)
  have hT₂R : rightConjugate T g₂ ≤ R := hT₂eq ▸ inf_le_left
  have hRC : R ≤ Subgroup.centralizer (rightConjugate T g₂ : Set X) := by
    have hle := inf_normalizer_le_centralizer hF₂
      (by rw [sup_rightConjugate hg₂]; exact hRGT) hT₂R hT₂comm
    rwa [inf_eq_left.mpr hRN] at hle
  have hT₂C : rightConjugate T g₂ ≤ Subgroup.centralizer (W : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    exact (le_sup_left.trans hR₀R).trans hRC
  have hT₂GT : rightConjugate T g₂ ≤ G ⊔ T := hT₂R.trans hRGT
  have hCN : (G ⊔ T) ⊓ Subgroup.centralizer (W : Set X) ≤
      (G ⊔ T) ⊓ Subgroup.normalizer (T : Set X) :=
    inf_le_inf_left _ ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hSC : S ⊓ Subgroup.normalizer (T : Set X) ≤
      (G ⊔ T) ⊓ Subgroup.centralizer (W : Set X) := by
    rw [← h.inf_eq_normalizer, h.inf_eq_centralizer_W]
    exact inf_le_inf_right _ h.le_sup
  have hsylC := h.sylowFrame.sylow_normalizer.of_le hSC hCN
  obtain ⟨c', hc'C, hc'le⟩ := exists_rightConjugate_le_of_isSylowOf hsylC
    (isPGroup_rightConjugate h.frame.isPGroup g₂) (le_inf hT₂GT hT₂C)
  have hg₂c' : g₂ * c' ∈ G ⊔ T := (G ⊔ T).mul_mem (Subgroup.mem_sup_left hg₂) hc'C.1
  obtain ⟨-, -, g₃, hg₃, -, hrc₃⟩ := h.frame.exists_rightConjugate_eq hg₂c'
  have hT₃ : rightConjugate (rightConjugate T g₂) c' = rightConjugate T g₃ := by
    rw [rightConjugate_mul, hrc₃]
  have hT₃W : rightConjugate (rightConjugate T g₂) c' ≤ W := by
    rw [hT₃, hWdef, ← h.weakClosure]
    apply rightConjugate_le_relativeWeakClosure hg₃
    rw [← hT₃, h.inf_eq_normalizer]
    exact hc'le
  apply hVW
  have hc'W : rightConjugate W c'⁻¹ = W :=
    (rightConjugate_eq_self_iff W c'⁻¹).mpr
      (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hc'C.2))
  have hle : rightConjugate V c' ≤ W := (rightConjugate_le_rightConjugate hVT₂ c').trans hT₃W
  calc V = rightConjugate (rightConjugate V c') c'⁻¹ := by
        rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    _ ≤ rightConjugate W c'⁻¹ := rightConjugate_le_rightConjugate hle _
    _ = W := hc'W

end Hyp45

theorem SylowFrame.card_normalizer_le [Finite X] {G T S : Subgroup X} (h : SylowFrame G T S)
    {c : X} (hc : c ∈ G ⊔ T) :
    Nat.card (S ⊓ Subgroup.normalizer (rightConjugate T c : Set X) : Subgroup X) ≤
      Nat.card (S ⊓ Subgroup.normalizer (T : Set X) : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : rightConjugate ((G ⊔ T) ⊓ Subgroup.normalizer (T : Set X)) c =
      (G ⊔ T) ⊓ Subgroup.normalizer (rightConjugate T c : Set X) := by
    rw [rightConjugate_inf, rightConjugate_normalizer, rightConjugate_eq_of_mem hc]
  have hsyl := isSylowOf_rightConjugate h.sylow_normalizer c
  rw [hL] at hsyl
  have h1 := card_le_of_isSylowOf hsyl h.sylow.isPGroup.to_inf_left
    (inf_le_inf_right _ h.sylow.le)
  rwa [rightConjugate_card] at h1

theorem le_of_inf_ne_bot [Finite X] {G T S Q H : Subgroup X} (h : SylowFrame G T S)
    (h43 : Hyp43 G T Q H) {c : X} (hc : c ∈ G) (hcS : rightConjugate T c ≤ S)
    {B : Subgroup X} (hBS : B ≤ S) (hB : IsMulCommutative B)
    (hcard : Nat.card (S ⊓ Subgroup.normalizer (T : Set X) : Subgroup X) ≤ Nat.card B)
    (hne : rightConjugate T c ⊓ B ≠ ⊥) : rightConjugate T c ≤ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨t, htT, htB⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
  have hFc := h.toFrame.rightConjugate_frame hc
  have h43c := h43.rightConjugate_hyp hc
  have hGTc : G ⊔ rightConjugate T c = G ⊔ T := sup_rightConjugate hc
  have hBC : B ≤ Subgroup.centralizer {t} := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative] at hB
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hB hb) t htB).symm
  have hBH : B ≤ rightConjugate H c := fun b hb =>
    h43c.centralizer_le hFc htT ht1' ⟨hGTc ▸ h.sylow.le (hBS hb), hBC hb⟩
  have hNc : rightConjugate H c ⊓ S ≤ Subgroup.normalizer (rightConjugate T c : Set X) :=
    h43c.le_normalizer_of_le h.sylow.isPGroup.to_inf_right (le_inf h43c.le_H hcS) inf_le_left
  have hBN : B ≤ S ⊓ Subgroup.normalizer (rightConjugate T c : Set X) :=
    le_inf hBS ((le_inf hBH hBS).trans hNc)
  have hcGT : c ∈ G ⊔ T := Subgroup.mem_sup_left hc
  have heq : B = S ⊓ Subgroup.normalizer (rightConjugate T c : Set X) :=
    Subgroup.eq_of_le_of_card_ge hBN ((h.card_normalizer_le hcGT).trans hcard)
  rw [heq]
  refine le_inf hcS Subgroup.le_normalizer

theorem isMulCommutative_sup {A B : Subgroup X} (hA : IsMulCommutative A)
    (hB : IsMulCommutative B) (hAB : A ≤ Subgroup.centralizer (B : Set X)) :
    IsMulCommutative (A ⊔ B : Subgroup X) := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative] at hA hB ⊢
  have hBA : B ≤ Subgroup.centralizer (A : Set X) := Subgroup.le_centralizer_iff.mp hAB
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le hA hBA
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le hAB hB

theorem two_le_pRank_of_involutions [Finite X] {P : Subgroup X} {a b : X} (ha : a ∈ P)
    (hb : b ∈ P) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hcomm : a * b = b * a) : 2 ≤ pRank 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := Subgroup.zpowers a
  set B := Subgroup.zpowers b
  have horda : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hordb : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  have hmem2 : ∀ c : X, orderOf c = 2 → ∀ x ∈ Subgroup.zpowers c, x = 1 ∨ x = c := by
    intro c hc x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hc]
    rcases Int.emod_two_eq_zero_or_one i with h0 | h1
    · left
      simp [h0]
    · right
      simp [h1]
  have hcommAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    rcases hmem2 a horda x hx with rfl | rfl <;> rcases hmem2 b hordb y hy with rfl | rfl <;>
      simp [hcomm]
  have hAC : A ≤ Subgroup.centralizer (B : Set X) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hcommAB x hx y hy).symm
  have hBN : B ≤ Subgroup.normalizer (A : Set X) :=
    (Subgroup.le_centralizer_iff.mp hAC).trans (Subgroup.centralizer_le_normalizer _)
  have hAB : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxb⟩
    rw [Subgroup.mem_bot]
    rcases hmem2 a horda x hxa with h1 | rfl
    · exact h1
    · rcases hmem2 b hordb x hxb with h2 | h2
      · exact absurd h2 ha1
      · exact absurd h2 hab
  set E := A ⊔ B
  have hcard : Nat.card E = 2 ^ 2 := by
    rw [card_sup_of_le_normalizer hBN hAB, Nat.card_zpowers, Nat.card_zpowers, horda, hordb]
    norm_num
  have hEcomm : IsMulCommutative E :=
    isMulCommutative_sup (Subgroup.zpowers_isMulCommutative a)
      (Subgroup.zpowers_isMulCommutative b) hAC
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := by
    intro x hx
    have hxmem : x ∈ (A : Set X) * (B : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B
        (hAC.trans (Subgroup.centralizer_le_normalizer _))]
      exact hx
    obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hxmem
    have hu2 : u ^ 2 = 1 := by rcases hmem2 a horda u hu with rfl | rfl <;> simp [ha2]
    have hw2 : w ^ 2 = 1 := by rcases hmem2 b hordb w hw with rfl | rfl <;> simp [hb2]
    calc (u * w) ^ 2 = u * (w * u) * w := by simp only [pow_two, mul_assoc]
      _ = u * (u * w) * w := by rw [hcommAB u hu w hw]
      _ = u ^ 2 * w ^ 2 := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [hu2, hw2, one_mul]
  have hEP : E ≤ P := sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
  exact CFSG.SectionRank.le_pRank (by norm_num) hEP ⟨hEcomm, hE2⟩ hcard

theorem card_eq_two_of_pRank_le_one [Finite X] {G T S Q H : Subgroup X} {g : X}
    (h : Hyp45 G T S Q H g) (hm : ¬ 1 < pRank 2 T) {y : X} (hy : y ∈ G)
    (hVS : rightConjugate T y ≤
      S ⊓ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X))
    (hVW : ¬ rightConjugate T y ≤ T ⊔ rightConjugate T g) : Nat.card T = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := T ⊔ rightConjugate T g with hWdef
  set V := rightConjugate T y with hVdef
  have hVH : V ⊓ H = ⊥ := h.inf_eq_bot_of_not_le hy le_rfl hVS hVW
  obtain ⟨t₀, ht₀, ht₀2, -⟩ := exists_center_involution h.frame.isPGroup h.ne_bot
  have ht₀sq : t₀ ^ 2 = 1 := by rw [← ht₀2]; exact pow_orderOf_eq_one t₀
  have ht₀1 : t₀ ≠ 1 := by rintro rfl; rw [orderOf_one] at ht₀2; omega
  have hcommT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    have hc := h.isMulCommutative
    rw [← Subgroup.le_centralizer_iff_isMulCommutative] at hc
    exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hc hb) a ha)
  have huniq : ∀ a ∈ T, a ^ 2 = 1 → a = 1 ∨ a = t₀ := by
    intro a ha ha2
    by_contra hcon
    push Not at hcon
    exact hm (two_le_pRank_of_involutions ha ht₀ ha2 ht₀sq hcon.1 ht₀1 hcon.2
      (hcommT a ha t₀ ht₀))
  set b₀ := g⁻¹ * t₀ * g with hb₀def
  have hb₀ : b₀ ∈ rightConjugate T g := conj_mem_rightConjugate ht₀ g
  have huniq' : ∀ b ∈ rightConjugate T g, b ^ 2 = 1 → b = 1 ∨ b = b₀ := by
    intro b hb hb2
    rw [mem_rightConjugate_iff] at hb
    have hb2' : (g * b * g⁻¹) ^ 2 = 1 := by
      rw [show (g * b * g⁻¹) ^ 2 = g * b ^ 2 * g⁻¹ by simp only [pow_two]; group, hb2]
      group
    rcases huniq _ hb hb2' with h1 | h1
    · left
      calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · right
      calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = b₀ := by rw [h1]
  have hTK : T ≤ Subgroup.normalizer (rightConjugate T g : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.facts.2.2.1).trans
      (Subgroup.centralizer_le_normalizer _)
  have hinvW : ∀ w ∈ W, w ^ 2 = 1 → w ≠ 1 → w ∈ ({t₀, b₀, t₀ * b₀} : Set X) := by
    intro w hw hw2 hw1
    have hwmem : w ∈ (T : Set X) * (rightConjugate T g : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T _ hTK]
      exact hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hwmem
    have hab : a * b = b * a :=
      (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h.facts.2.2.1 ha) b hb).symm
    have h1 : a ^ 2 * b ^ 2 = 1 := by
      rw [← hw2]
      calc a ^ 2 * b ^ 2 = a * (a * b) * b := by simp only [pow_two, mul_assoc]
        _ = a * (b * a) * b := by rw [hab]
        _ = (a * b) ^ 2 := by simp only [pow_two, mul_assoc]
    have ha2 : a ^ 2 = 1 := by
      have hmem : a ^ 2 ∈ T ⊓ rightConjugate T g := by
        refine ⟨T.pow_mem ha 2, ?_⟩
        rw [eq_inv_of_mul_eq_one_left h1]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hb 2)
      rw [h.facts.2.1, Subgroup.mem_bot] at hmem
      exact hmem
    have hb2 : b ^ 2 = 1 := by rwa [ha2, one_mul] at h1
    rcases huniq a ha ha2 with rfl | rfl
    · rcases huniq' b hb hb2 with rfl | rfl
      · exact absurd (mul_one 1) hw1
      · simp
    · rcases huniq' b hb hb2 with rfl | rfl
      · simp
      · simp
  have hmapV : ∀ v ∈ (V : Set X), v⁻¹ * t₀ * v ∈ ({t₀, b₀, t₀ * b₀} : Set X) := by
    intro v hv
    have hvN := (hVS hv).2
    have hmem : v⁻¹ * t₀ * v ∈ W := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hvN) t₀).mp
        (Subgroup.mem_sup_left ht₀)
      simpa using h1
    refine hinvW _ hmem ?_ ?_
    · rw [show (v⁻¹ * t₀ * v) ^ 2 = v⁻¹ * t₀ ^ 2 * v by simp only [pow_two]; group, ht₀sq]
      group
    · intro h1
      apply ht₀1
      calc t₀ = v * (v⁻¹ * t₀ * v) * v⁻¹ := by group
        _ = 1 := by rw [h1]; group
  have hinj : Set.InjOn (fun v => v⁻¹ * t₀ * v) (V : Set X) := by
    intro v hv v' hv' heq
    simp only at heq
    have hvv' : v' * v⁻¹ ∈ Subgroup.centralizer {t₀} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc v' * v⁻¹ * t₀ = v' * (v⁻¹ * t₀ * v) * v⁻¹ := by group
        _ = v' * (v'⁻¹ * t₀ * v') * v⁻¹ := by rw [heq]
        _ = t₀ * (v' * v⁻¹) := by group
    have hvGT : v' * v⁻¹ ∈ G ⊔ T :=
      (G ⊔ T).mul_mem (h.le_sup (hVS hv').1) ((G ⊔ T).inv_mem (h.le_sup (hVS hv).1))
    have hvH : v' * v⁻¹ ∈ H :=
      h.hyp43.centralizer_le h.frame ht₀ ht₀1 ⟨hvGT, hvv'⟩
    have hmem : v' * v⁻¹ ∈ V ⊓ H := ⟨V.mul_mem hv' (V.inv_mem hv), hvH⟩
    rw [hVH, Subgroup.mem_bot] at hmem
    exact (mul_inv_eq_one.mp hmem).symm
  have hle := Set.ncard_le_ncard_of_injOn _ hmapV hinj (Set.toFinite _)
  have h3 : ({t₀, b₀, t₀ * b₀} : Set X).ncard ≤ 3 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
    rw [Set.ncard_singleton]
  have hVcard : Nat.card V = Nat.card T := rightConjugate_card T y
  have hcardV : Nat.card V = (V : Set X).ncard := Nat.card_coe_set_eq _
  have hT3 : Nat.card T ≤ 3 := by omega
  obtain ⟨k, hk⟩ := h.frame.isPGroup.exists_card_eq
  have hT1 : Nat.card T ≠ 1 := fun h1 => h.ne_bot (Subgroup.card_eq_one.mp h1)
  rw [hk] at hT3 hT1 ⊢
  have hk1 : k ≠ 0 := by
    rintro rfl
    simp at hT1
  have hk2 : k < 2 := by
    by_contra hk2
    push Not at hk2
    have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  have hk' : k = 1 := by omega
  rw [hk', pow_one]

end CFSG.ComponentClassification.AschbacherTheorem3
