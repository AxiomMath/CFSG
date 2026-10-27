module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gLside
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gAbel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dAbs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S (ae6ConjIn)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d (FourTwins bool_four false_of_four_twins)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.A6h1
  (ae6Img mem_ae6Img ae6Img_mono ae6Img_le_range)

section Excl

variable {Y : Type} [Group Y] [Finite Y] {Ω P : Set (Subgroup Y)}

theorem false_of_four_twins_on {n : ℕ} {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AEQ n)}
    (hn : 5 ≤ n) (hn8 : n ≠ 8) (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (h8 : ∀ J ∈ Ω, Nat.card J = 8) (hPΩ : P ⊆ Ω) (I : AEIdentOn P n 𝒜 H)
    (hk : IsPGroup 2 I.φ.ker) {z : Y} {A₁ A₂ A₃ A₄ : Subgroup Y} (F : FourTwins P z A₁ A₂ A₃ A₄) :
    False := by
  obtain ⟨α₁, -, h₁, b₁, hl₁⟩ := I.label A₁ F.m₁
  obtain ⟨α₂, -, h₂', b₂, hl₂⟩ := I.label A₂ F.m₂
  obtain ⟨α₃, -, h₃, b₃, hl₃⟩ := I.label A₃ F.m₃
  obtain ⟨α₄, -, h₄, b₄, hl₄⟩ := I.label A₄ F.m₄
  have e₁ := phi_map_eq_zBar I.φ hn F.m₁ (h8 _ (hPΩ F.m₁)) hl₁ F.z₁
  have e₂ := phi_map_eq_zBar I.φ hn F.m₂ (h8 _ (hPΩ F.m₂)) hl₂ F.z₂
  have e₃ := phi_map_eq_zBar I.φ hn F.m₃ (h8 _ (hPΩ F.m₃)) hl₃ F.z₃
  have e₄ := phi_map_eq_zBar I.φ hn F.m₄ (h8 _ (hPΩ F.m₄)) hl₄ F.z₄
  have a₂ : α₂ = α₁ := eq_of_zBar_eq hn8 (e₂.symm.trans e₁)
  have a₃ : α₃ = α₁ := eq_of_zBar_eq hn8 (e₃.symm.trans e₁)
  have a₄ : α₄ = α₁ := eq_of_zBar_eq hn8 (e₄.symm.trans e₁)
  have key : ∀ {α : Finset (Fin n)} {h : α.card = 4} {B C : Subgroup Y} (hB : B ∈ P) (hC : C ∈ P)
      {b c : Bool}, (B.subgroupOf (pSpan P)).map I.φ = memBar α h b →
      (C.subgroupOf (pSpan P)).map I.φ = memBar α h c → b = c → B = C := by
    intro α h B C hB hC b c hb hc hbc
    subst hbc
    exact TL4.eq_of_map_le_memBar hΩ h2 hn I.φ hk (hPΩ hB) (hPΩ hC) (le_pSpan hB) (le_pSpan hC)
      hb (hb.trans hc.symm).le
  subst a₂ a₃ a₄
  rcases bool_four b₁ b₂ b₃ b₄ with h' | h' | h' | h' | h' | h'
  · exact F.ne₁₂ (key F.m₁ F.m₂ hl₁ hl₂ h')
  · exact F.ne₁₃ (key F.m₁ F.m₃ hl₁ hl₃ h')
  · exact F.ne₁₄ (key F.m₁ F.m₄ hl₁ hl₄ h')
  · exact F.ne₂₃ (key F.m₂ F.m₃ hl₂ hl₃ h')
  · exact F.ne₂₄ (key F.m₂ F.m₄ hl₂ hl₄ h')
  · exact F.ne₃₄ (key F.m₃ F.m₄ hl₃ hl₄ h')

theorem aeIdent8_of_thmD' (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (h8 : ∀ J ∈ Ω, Nat.card J = 8) (hA : ∀ J ∈ Ω, AEmpty Ω J) (hPΩ : P ⊆ Ω)
    (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L')
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hodd : classicalInvolutionOddCore ↥(pSpan P) = ⊥)
    (he2 : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → ∃ Q : Subgroup Y, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q)
    (hD : ThmDAbsAt 3 ↥(pSpan P)) {z : Y} {A₁ A₂ A₃ A₄ : Subgroup Y}
    (F : FourTwins P z A₁ A₂ A₃ A₄)
    (hthin : ∀ L ∈ P, ∀ u : Y, IsUniqueInvolution L u → ∀ Q : Subgroup Y, Q ≤ pSpan P →
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) → IsPGroup 2 Q → ∀ x ∈ L, x ∈ Q → x = 1 ∨ x = u)
    (hno64 : IsEmpty (AEIdentOn P 7 e64Sets e64Sub))
    (hno29 : IsEmpty (AEIdentOn P 8 e29Sets e29Sub)) : Nonempty (AEIdent P 8) := by
  have hcard : ∀ J ∈ Ω, Nat.card J = 2 ^ 3 := fun J hJ => (h8 J hJ).trans (by norm_num)
  have hPne : P.Nonempty := ⟨A₁, F.m₁⟩
  rcases thmDGen_at hΩ h2 hcard hA hPΩ hD htrans hinv hodd he2 with
    hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | hI64 | ⟨m, hm5, hIm⟩ | hI29
  · exact absurd (hsing A₁ F.m₁ A₂ F.m₂) F.ne₁₂
  · exact (false_of_WIn_eq hΩ h2 h8 hPΩ hPne hinv hthin hW).elim
  · have hS : SecHyp 3 Ω P := ⟨hΩ, h2, hcard, hA, hPΩ, hinv, htrans, hodd, he2⟩
    have hΦ := hS.thmDHyp
    have hE' := hE.toTop
    have hmem : ∀ {A : Subgroup Y}, A ∈ P → A.subgroupOf (pSpan P) ∈ restrictFamily P (pSpan P) :=
      fun hA => ⟨_, hA, le_pSpan hA, rfl⟩
    have heq := eq_of_inv_e8 hΦ hE' (hmem F.m₁) (hmem F.m₂)
      (isUniqueInvolution_subgroupOf F.z₁ (le_pSpan F.m₁))
      (isUniqueInvolution_subgroupOf F.z₂ (le_pSpan F.m₂))
    have h12 := Subgroup.subgroupOf_inj.mp heq
    rw [inf_eq_left.mpr (le_pSpan F.m₁), inf_eq_left.mpr (le_pSpan F.m₂)] at h12
    exact absurd h12 F.ne₁₂
  · obtain ⟨I⟩ := hI64
    exact (hno64.false I).elim
  · obtain ⟨I⟩ := hIm
    by_cases hm8 : m = 8
    · subst hm8
      exact ⟨I⟩
    · exact (false_of_four_twins hm5 hm8 hΩ h2 h8 hPΩ I (I.isPGroup_ker hodd) F).elim
  · obtain ⟨I⟩ := hI29
    exact (hno29.false I).elim

end Excl

section Lside

variable {Y : Type} [Group Y] [Finite Y] {L K : Subgroup Y}

theorem thin_of_lside {V : Subgroup Y} {t : Y} (hLV : L ≤ V)
    {B : AEIdentOn (ae6ConjIn L K) 8 e29Sets e29Sub} {hspan : pSpan (ae6ConjIn L K) = L}
    (hker : B.φ.ker = ⊥) (hKt : IsUniqueInvolution K t)
    (h8 : ∀ J ∈ ae6ConjIn L K, Nat.card J = 8) {Q : Subgroup Y}
    (hQV : ∀ x ∈ V, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) (hQ2 : IsPGroup 2 Q) {x₀ : Y} (hx₀K : x₀ ∈ K)
    (hx₀Q : x₀ ∈ Q) : x₀ = 1 ∨ x₀ = t := by
  have hinj := lhom_injective B hspan hker
  have hrange := lhom_range B hspan
  have hK1 : K ∈ ae6ConjIn L K := ⟨1, L.one_mem, conjSub_one K⟩
  have hKL : K ≤ L := (le_pSpan hK1).trans hspan.le
  have hx₀L : x₀ ∈ L := hKL hx₀K
  have htL : t ∈ L := hKL hKt.mem
  obtain ⟨α, -, h, b, hlab⟩ := B.label K hK1
  have hTle : ae6Img (lhom B hspan) (Q ⊓ L) ≤ e29Sub := hrange ▸ ae6Img_le_range _
  have hTn : ∀ e ∈ e29Sub, ∀ a ∈ ae6Img (lhom B hspan) (Q ⊓ L),
      e * a * e⁻¹ ∈ ae6Img (lhom B hspan) (Q ⊓ L) := by
    intro e he a ha
    have he' : e ∈ (lhom B hspan).range := hrange ▸ he
    obtain ⟨⟨l, hl⟩, rfl⟩ := he'
    obtain ⟨q, hq, hqQL, rfl⟩ := mem_ae6Img.mp ha
    have hmem : l * q * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hq) (L.inv_mem hl)
    refine mem_ae6Img.mpr ⟨l * q * l⁻¹, hmem, ⟨hQV l (hLV hl) q hqQL.1, hmem⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hT2 : IsPGroup 2 ↥(ae6Img (lhom B hspan) (Q ⊓ L)) :=
    ((hQ2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm).map _
  have hTN : ae6Img (lhom B hspan) (Q ⊓ L) ≤ nBar := le_nBar_of_normal hTle hTn hT2
  have hφx : lhom B hspan ⟨x₀, hx₀L⟩ ∈ ae6Img (lhom B hspan) (Q ⊓ L) :=
    mem_ae6Img.mpr ⟨x₀, hx₀L, ⟨hx₀Q, hx₀L⟩, rfl⟩
  have hφK : lhom B hspan ⟨x₀, hx₀L⟩ ∈ memBar α h b := by
    rw [← hlab]
    exact ⟨⟨x₀, hspan.symm.le hx₀L⟩, Subgroup.mem_subgroupOf.mpr hx₀K, rfl⟩
  rcases memBar_inf_nBar hφK (hTN hφx).2 with h1 | h1
  · left
    have : (⟨x₀, hx₀L⟩ : ↥L) = 1 := hinj (by rw [h1, map_one])
    exact congrArg Subtype.val this
  · right
    have h2 := phi_map_eq_zBar B.φ (by norm_num : 5 ≤ 8) hK1 (h8 K hK1) hlab hKt
    have : (⟨x₀, hx₀L⟩ : ↥L) = ⟨t, htL⟩ := hinj (by rw [h1]; exact h2.symm)
    exact congrArg Subtype.val this

@[expose] def labs : Set (Finset (Fin 8) × Bool) := {ℓ | ℓ.1 ∈ e29Sets}

theorem memBar_congr_lab {ℓ ℓ' : Finset (Fin 8) × Bool} (a : ℓ.1.card = 4) (b : ℓ'.1.card = 4)
    (h : ℓ = ℓ') : memBar ℓ.1 a ℓ.2 = memBar ℓ'.1 b ℓ'.2 := by
  subst h
  rfl

theorem no_e29_of_far {L Lj K E₃ : Subgroup Y} {t : Y} {Ω : Set (Subgroup Y)}
    (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (hPΩ : ae6ConjIn (L ⊔ Lj) K ⊆ Ω)
    (I₀ : AEIdentOn (ae6ConjIn (L ⊔ Lj) K) 8 e29Sets e29Sub) (hk : IsPGroup 2 I₀.φ.ker)
    (B : AEIdentOn (ae6ConjIn L K) 8 e29Sets e29Sub) (hKt : IsUniqueInvolution K t)
    (hnorm : ∀ l ∈ L, ∀ e ∈ E₃, l * e * l⁻¹ ∈ E₃) (htE : t ∈ E₃)
    (hfar : ∃ g ∈ Lj, g * t * g⁻¹ ∉ E₃) : False := by
  classical
  have hQP : ae6ConjIn L K ⊆ ae6ConjIn (L ⊔ Lj) K := by
    rintro J ⟨g, hg, rfl⟩
    exact ⟨g, (le_sup_left : L ≤ L ⊔ Lj) hg, rfl⟩
  have hP_le : (ae6ConjIn (L ⊔ Lj) K).ncard ≤ labs.ncard := by
    let f : Subgroup Y → Finset (Fin 8) × Bool := fun J =>
      Classical.epsilon (fun ℓ : Finset (Fin 8) × Bool => ℓ.1 ∈ e29Sets ∧ ∃ h : ℓ.1.card = 4,
        (J.subgroupOf (pSpan (ae6ConjIn (L ⊔ Lj) K))).map I₀.φ = memBar ℓ.1 h ℓ.2)
    have hspec : ∀ J ∈ ae6ConjIn (L ⊔ Lj) K, (f J).1 ∈ e29Sets ∧ ∃ h : (f J).1.card = 4,
        (J.subgroupOf (pSpan (ae6ConjIn (L ⊔ Lj) K))).map I₀.φ = memBar (f J).1 h (f J).2 := by
      intro J hJ
      obtain ⟨α, hα, h, b, hlab⟩ := I₀.label J hJ
      exact Classical.epsilon_spec (p := fun ℓ : Finset (Fin 8) × Bool => ℓ.1 ∈ e29Sets ∧
        ∃ h : ℓ.1.card = 4, (J.subgroupOf (pSpan (ae6ConjIn (L ⊔ Lj) K))).map I₀.φ =
          memBar ℓ.1 h ℓ.2) ⟨(α, b), hα, h, hlab⟩
    refine Set.ncard_le_ncard_of_injOn f (fun J hJ => (hspec J hJ).1) ?_ (Set.toFinite _)
    intro J hJ J' hJ' hf
    obtain ⟨-, h1, hl1⟩ := hspec J hJ
    obtain ⟨-, h2', hl2⟩ := hspec J' hJ'
    have himg : (J.subgroupOf (pSpan (ae6ConjIn (L ⊔ Lj) K))).map I₀.φ =
        (J'.subgroupOf (pSpan (ae6ConjIn (L ⊔ Lj) K))).map I₀.φ := by
      rw [hl1, hl2]
      exact memBar_congr_lab h1 h2' hf
    exact TL4.eq_of_map_le_memBar hΩ h2 (by norm_num : 5 ≤ 8) I₀.φ hk (hPΩ hJ) (hPΩ hJ')
      (le_pSpan hJ) (le_pSpan hJ') hl1 himg.le
  have hL_le : labs.ncard ≤ (ae6ConjIn L K).ncard := by
    let g : Finset (Fin 8) × Bool → Subgroup Y := fun ℓ =>
      Classical.epsilon (fun J : Subgroup Y => J ∈ ae6ConjIn L K ∧ ∃ h : ℓ.1.card = 4,
        (J.subgroupOf (pSpan (ae6ConjIn L K))).map B.φ = memBar ℓ.1 h ℓ.2)
    have hspec : ∀ ℓ ∈ labs, g ℓ ∈ ae6ConjIn L K ∧ ∃ h : ℓ.1.card = 4,
        ((g ℓ).subgroupOf (pSpan (ae6ConjIn L K))).map B.φ = memBar ℓ.1 h ℓ.2 := by
      intro ℓ hℓ
      have h4 := affinePlanes_card ℓ.1 hℓ
      obtain ⟨J, hJ, hlab⟩ := B.label_surj ℓ.1 hℓ h4 ℓ.2
      exact Classical.epsilon_spec (p := fun J : Subgroup Y => J ∈ ae6ConjIn L K ∧
        ∃ h : ℓ.1.card = 4, (J.subgroupOf (pSpan (ae6ConjIn L K))).map B.φ = memBar ℓ.1 h ℓ.2)
        ⟨J, hJ, h4, hlab⟩
    refine Set.ncard_le_ncard_of_injOn g (fun ℓ hℓ => (hspec ℓ hℓ).1) ?_ (Set.toFinite _)
    intro ℓ hℓ ℓ' hℓ' hg
    obtain ⟨-, h1, hl1⟩ := hspec ℓ hℓ
    obtain ⟨-, h2', hl2⟩ := hspec ℓ' hℓ'
    have hmb : memBar ℓ.1 h1 ℓ.2 = memBar ℓ'.1 h2' ℓ'.2 := by rw [← hl1, ← hl2, hg]
    obtain ⟨δ, b⟩ := ℓ
    obtain ⟨δ', b'⟩ := ℓ'
    have hδ : δ = δ' := eq_of_memBar_eq' (by norm_num) hmb
    subst hδ
    cases b <;> cases b'
    · rfl
    · exact absurd hmb.symm (memBar_true_ne_false (by norm_num) δ h2')
    · exact absurd hmb (memBar_true_ne_false (by norm_num) δ h1)
    · rfl
  have hEq : ae6ConjIn L K = ae6ConjIn (L ⊔ Lj) K :=
    Set.eq_of_subset_of_ncard_le hQP (hP_le.trans hL_le) (Set.toFinite _)
  obtain ⟨g, hgLj, hfar'⟩ := hfar
  have hgV : g ∈ L ⊔ Lj := (le_sup_right : Lj ≤ L ⊔ Lj) hgLj
  have hJP : conjSub g K ∈ ae6ConjIn (L ⊔ Lj) K := ⟨g, hgV, rfl⟩
  rw [← hEq] at hJP
  obtain ⟨l, hl, hlg⟩ := hJP
  have h1 := hKt.conj l
  have h2' := hKt.conj g
  rw [hlg] at h1
  have heq := h1.eq h2'
  exact hfar' (heq ▸ hnorm l hl t htE)

end Lside

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6g
