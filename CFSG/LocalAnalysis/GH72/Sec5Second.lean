module

public import CFSG.LocalAnalysis.GH72.Sec5CKbar
public import CFSG.LocalAnalysis.GH72.Sec5Eighteen
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement Pointwise

section Commutator

variable {G : Type} [Group G]

variable [Finite G]

theorem commutator_commutator_eq_bot_of_le_centralizer {t : ℕ} (ht : t.Prime) (ht2 : t ≠ 2)
    {T X Y : Subgroup G} (hT : IsPGroup t T) (hYT : Y ≤ normalizer (T : Set G))
    (hXY : X ≤ centralizer (Y : Set G)) (hY : IsKleinFour Y)
    (h : ∀ y ∈ Y, y ≠ 1 → X ≤ centralizer ((⁅T ⊓ C y, Y⁆ : Subgroup G) : Set G)) :
    ⁅⁅T, X⁆, Y⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsKleinFour Y := hY
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card (n := 2) (by rw [hY.card_four]; norm_num)
  have hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb => mul_comm_of_mem_kleinFour hY ha hb
  set C₀ : Subgroup G := T ⊓ centralizer (Y : Set G) with hC₀def
  set N : Subgroup G := ⨆ y : {y : G // y ∈ Y ∧ y ≠ 1}, ⁅T ⊓ C (y : G), Y⁆ with hNdef
  have hYTy : ∀ y ∈ Y, Y ≤ normalizer ((T ⊓ C y : Subgroup G) : Set G) := fun y hy b hb =>
    inf_normalizer_le_normalizer_inf
      ⟨hYT hb, le_normalizer (mem_centralizer_singleton_iff.mpr (hYc b hb y hy))⟩
  have hTy : ∀ y : {y : G // y ∈ Y ∧ y ≠ 1}, T ⊓ C (y : G) ≤ N ⊔ C₀ := by
    intro y
    have h1 := le_commutator_sup_inf_centralizer_of_coprime_pGroup ht ht2 (hT.to_le inf_le_left) hY2
      (hYTy y y.2.1)
    refine h1.trans (sup_le_sup (le_iSup (fun y : {y : G // y ∈ Y ∧ y ≠ 1} =>
      (⁅T ⊓ C (y : G), Y⁆ : Subgroup G)) y) ?_)
    exact inf_le_inf_right _ inf_le_left
  have hTodd : Odd (Nat.card T) := odd_card_of_isPGroup ht ht2 hT
  obtain ⟨y₁, hy₁, hy₁1⟩ := exists_ne_one_of_isKleinFour hY
  obtain ⟨y₂, hy₂, hy₂1, hy₂₁⟩ := exists_mem_kleinFour_ne hY hy₁
  have hy₃ : y₁ * y₂ ∈ Y := mul_mem hy₁ hy₂
  have hy₃1 : y₁ * y₂ ≠ 1 := fun e => hy₂₁ (by
    have h1 : y₁ * y₁ = 1 := by rw [← pow_two]; exact sq_eq_one_of_mem_kleinFour hY hy₁
    calc y₂ = y₁ * y₁ * y₂ := by rw [h1, one_mul]
      _ = y₁ * (y₁ * y₂) := by rw [mul_assoc]
      _ = y₁ := by rw [e, mul_one])
  have hy₁₃ : y₁ ≠ y₁ * y₂ := fun e =>
    hy₂1 (mul_left_cancel (a := y₁) (by rw [mul_one]; exact e.symm))
  have hy₂₃ : y₂ ≠ y₁ * y₂ := fun e =>
    hy₁1 (mul_right_cancel (b := y₂) (by rw [one_mul]; exact e.symm))
  have hTN : T ≤ N ⊔ C₀ := by
    intro g hg
    have hg' : g ∈ (T : Set G) := hg
    rw [four_group_odd_eq_mul_centralizers hTodd hYT hy₁ hy₂ hy₃ hy₁1 hy₂1 hy₃1 hy₂₁.symm hy₁₃
      hy₂₃] at hg'
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hg'
    exact mul_mem (mul_mem (hTy ⟨y₁, hy₁, hy₁1⟩ ha) (hTy ⟨y₂, hy₂, hy₂1⟩ hb))
      (hTy ⟨y₁ * y₂, hy₃, hy₃1⟩ hc)
  have hNn : ∀ g : G, (∀ y : {y : G // y ∈ Y ∧ y ≠ 1},
      g ∈ normalizer ((⁅T ⊓ C (y : G), Y⁆ : Subgroup G) : Set G)) →
      g ∈ normalizer (N : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change N.map (MulAut.conj g).toMonoidHom = N
    rw [hNdef, Subgroup.map_iSup]
    exact iSup_congr fun y => map_conj_eq_of_mem_normalizer (hg y)
  have hC₀N : C₀ ≤ normalizer (N : Set G) := fun c hc => hNn c fun y =>
    le_normalizer_commutator (H := T ⊓ C (y : G)) (K := Y) (L := C₀)
      (fun c' hc' => le_normalizer ⟨hc'.1, mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hc'.2 y y.2.1)).symm⟩)
      (fun c' hc' => centralizer_le_normalizer _ hc'.2) hc
  have hYN : Y ≤ normalizer (N : Set G) := fun b hb => hNn b fun y =>
    le_normalizer_commutator (hYTy y y.2.1) le_normalizer hb
  have hTYN : ⁅T, Y⁆ ≤ N := by
    rw [commutator_le]
    intro g hg y hy
    have hg' : g ∈ ((N ⊔ C₀ : Subgroup G) : Set G) := hTN hg
    rw [coe_mul_of_right_le_normalizer_left N C₀ hC₀N] at hg'
    obtain ⟨n, hn, c, hc, rfl⟩ := Set.mem_mul.mp hg'
    rw [commutatorElement_mul_of_commute (mem_centralizer_iff.mp hc.2 y hy).symm]
    rw [commutatorElement_def]
    have h1 : y * n⁻¹ * y⁻¹ ∈ N := (mem_normalizer_iff.mp (hYN hy) n⁻¹).mp (inv_mem hn)
    have := mul_mem hn h1
    simpa [mul_assoc] using this
  have hNX : N ≤ centralizer (X : Set G) :=
    iSup_le fun y => (le_centralizer_iff.mp (h y y.2.1 y.2.2))
  apply commutator_commutator_eq_bot_of_rotate
  · rw [(commutator_eq_bot_iff_le_centralizer).mpr hXY, commutator_bot_left]
  · rw [commutator_comm Y T]
    exact (commutator_eq_bot_iff_le_centralizer).mpr (hTYN.trans hNX)

end Commutator

namespace Sec5ConfigTR

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  {𝔠 : Sec5ConfigR ρ p} (𝔱 : Sec5ConfigTR 𝔠)

theorem isPGroup_T : IsPGroup 𝔱.t 𝔱.T := 𝔱.hT.2.1.isPGroup

theorem A_le_normalizer_T : A ≤ normalizer (𝔱.T : Set G) := 𝔱.hT.2.2.1

theorem X_le_normalizer_T : ρ.X ≤ normalizer (𝔱.T : Set G) :=
  ρ.X_le_A.trans 𝔱.A_le_normalizer_T

theorem commutator_T_X_le : ⁅𝔱.T, ρ.X⁆ ≤ 𝔱.T := by
  rw [commutator_comm]
  exact le_normalizer_iff_commutator_le_right.mp 𝔱.X_le_normalizer_T

theorem A_le_normalizer_E : A ≤ normalizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) :=
  le_normalizer_commutator 𝔱.A_le_normalizer_T (ρ.A_le_normalizer_of_le ρ.X_le_A)

theorem A_le_C_x₁ : A ≤ C 𝔱.x₁ := fun _ ha =>
  mem_centralizer_singleton_iff.mpr (ρ.comm (ρ.X_le_A 𝔱.hx₁.1) ha).symm

theorem M_le_C_x₁ : ρ.M ≤ C 𝔱.x₁ := fun _ hm =>
  mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hm) 𝔱.x₁ 𝔱.hx₁.1).symm

theorem O_C_x₁_inf_centralizer_X_le :
    O (C 𝔱.x₁) ⊓ centralizer (ρ.X : Set G) ≤ O ρ.M := by
  refine G5d.le_O_of_le_normalizer inf_le_right (fun m hm => ?_)
    ((card_O_odd _).of_dvd_nat (card_dvd_of_le inf_le_left))
  exact inf_normalizer_le_normalizer_inf
    ⟨le_normalizer_O _ (𝔱.M_le_C_x₁ hm), le_normalizer hm⟩

theorem not_le_centralizer_E
    (h : 𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) = ⊥) :
    ¬ ρ.Y ≤ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) := fun hY =>
  𝔠.Y_not_le_centralizer_Q (G5d.le_centralizer_of_le_centralizer_commutator
    (𝔠.Q_le_P.trans 𝔱.hXP) 𝔱.hT.2.2.2.1 (ρ.Y_le_A.trans 𝔠.A_le_normalizer_Q) h hY)

theorem lemma_5_15 (h : 𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) = ⊥) :
    Sec4Setting.PConstrainedWrt 𝔱.t A (C 𝔱.x₁) ρ.Y :=
  ⟨𝔱.T, 𝔱.hT.2.1, 𝔱.hT.2.2.1, fun hYT => 𝔱.not_le_centralizer_E h
    (hYT.trans (centralizer_le fun _ hx => 𝔱.commutator_T_X_le hx))⟩

theorem lemma_5_16_of
    (h411 : (∀ x ∈ ρ.X, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, ρ.X⁆ ⊔ ⁅⁅D, ρ.Y⁆, ⁅D, ρ.Y⁆⁆ ≤ O (C x)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
        A ≤ normalizer (D : Set G) → ⁅D, ρ.Y⁆ ⊔ ⁅⁅D, ρ.X⁆, ⁅D, ρ.X⁆⁆ ≤ O (C y)))
    (h : 𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) = ⊥) :
    ∃ y₁ ∈ ρ.Y, y₁ ≠ 1 ∧ Sec4Setting.PConstrainedWrt 𝔱.t A (C y₁) ρ.X := by
  have ht := 𝔱.ht.1
  have ht2 := 𝔱.ht.2.1
  by_contra hcon
  apply 𝔱.not_le_centralizer_E h
  rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
  have hall : ∀ y ∈ ρ.Y, y ≠ 1 →
      ρ.X ≤ centralizer ((⁅𝔱.T ⊓ C y, ρ.Y⁆ : Subgroup G) : Set G) := by
    intro y hy hy1
    by_contra hX
    apply hcon
    have hAy : A ≤ C y := fun a ha =>
      mem_centralizer_singleton_iff.mpr (ρ.comm (ρ.Y_le_A hy) ha).symm
    have hTy : A ≤ normalizer ((𝔱.T ⊓ C y : Subgroup G) : Set G) := fun a ha =>
      inf_normalizer_le_normalizer_inf ⟨𝔱.A_le_normalizer_T ha, le_normalizer (hAy ha)⟩
    set D : Subgroup G := ⁅𝔱.T ⊓ C y, ρ.Y⁆ with hDdef
    have hDO : D ≤ O (C y) :=
      le_sup_left.trans (h411.2 y hy hy1 (𝔱.T ⊓ C y) inf_le_right
        ((odd_card_of_isPGroup ht ht2 𝔱.isPGroup_T).of_dvd_nat (card_dvd_of_le inf_le_left))
        hTy)
    have hDT : D ≤ 𝔱.T := by
      rw [hDdef, commutator_comm]
      exact (le_normalizer_iff_commutator_le_right.mp
        (fun b hb => inf_normalizer_le_normalizer_inf
          ⟨𝔱.A_le_normalizer_T (ρ.Y_le_A hb),
            le_normalizer (hAy (ρ.Y_le_A hb))⟩)).trans
        inf_le_left
    have hAD : A ≤ normalizer (D : Set G) :=
      le_normalizer_commutator hTy (ρ.A_le_normalizer_of_le ρ.Y_le_A)
    obtain ⟨T', hT', hDT', hAT'⟩ := CFSG.ABGTheoremB.exists_isSylowOf_normalized_ge_of_odd ht
      ρ.isPGroup_A (hAy.trans (le_normalizer_O _)) (card_O_odd _) hDO
      (𝔱.isPGroup_T.to_le hDT) hAD
    exact ⟨y, hy, hy1, T', hT', hAT', fun hXT' => hX
      (hXT'.trans (centralizer_le fun _ hx => hDT' hx))⟩
  exact commutator_commutator_eq_bot_of_le_centralizer ht ht2 𝔱.isPGroup_T
    (ρ.Y_le_A.trans 𝔱.A_le_normalizer_T)
    (ρ.X_le_A.trans (ρ.A_le_centralizer_of_le ρ.Y_le_A)) ρ.isKleinFour_Y hall

theorem lemma_5_14
    (h : 𝔠.Q ⊓ centralizer ((⁅𝔱.T, ρ.X⁆ : Subgroup G) : Set G) ≠ ⊥) :
    ∃ H, ρ.IsCovering p H := by
  have h48i := 𝔠.quotIs_N₀
  have hXN₀ := 𝔠.X_le_N₀
  have ht := 𝔱.ht.1
  have hp := 𝔠.hp
  have hXP := 𝔱.hXP
  have hQ := 𝔱.hQ
  set E : Subgroup G := ⁅𝔱.T, ρ.X⁆ with hEdef
  set Qs : Subgroup G := 𝔠.Q ⊓ centralizer (E : Set G) with hQsdef
  have hXQ : 𝔠.Q ≤ centralizer (ρ.X : Set G) := 𝔠.Q_le_P.trans hXP
  have hQE : 𝔠.Q ≤ normalizer (E : Set G) :=
    G5d.le_normalizer_commutator_of_mul_comm hXQ 𝔱.hT.2.2.2.1
  have hPE : 𝔠.P ≤ normalizer (E : Set G) :=
    G5d.le_normalizer_commutator_of_mul_comm hXP 𝔱.hT.2.2.2.2
  have hXE : ρ.X ≤ normalizer (E : Set G) := ρ.X_le_A.trans 𝔱.A_le_normalizer_E
  have hXCx : ρ.X ≤ normalizer (O (C 𝔱.x₁) : Set G) :=
    (ρ.X_le_A.trans 𝔱.A_le_C_x₁).trans (le_normalizer_O _)
  have hTsE : 𝔱.Tstar ≤ E := by
    rw [← 𝔱.hTstar.2.2.2.1, hEdef]
    exact commutator_mono 𝔱.hT.1 le_rfl
  have hQsV : Qs ≤ 𝔠.V := by
    rw [← 𝔱.hTstar.2.2.2.2]
    exact le_inf (inf_le_left.trans 𝔠.Q_le_P)
      (inf_le_right.trans (centralizer_le fun _ hx => hTsE hx))
  have hOMn := ρ.M₀_le_normalizer_O_M
  have hMcov : Covers ρ.M ρ.M₀ (O ρ.M) := fun m hm =>
    mem_sup_left ⟨ρ.M₀_le hm, hm⟩
  have hNT : Covers (normalizer (𝔱.T : Set G)) ρ.M₀ (O ρ.M) :=
    covers_normalizer_of_isSylowOf ht ρ.isPGroup_two_X hXCx (card_O_odd _) 𝔱.hT.2.1
      𝔱.X_le_normalizer_T hMcov
      (fun m hm => le_normalizer_O _ (𝔱.M_le_C_x₁ hm.1)) (fun m hm => hm.1)
      𝔱.O_C_x₁_inf_centralizer_X_le le_sup_right hOMn
  set Γ : Subgroup G := O (C 𝔱.x₁) ⊓ centralizer (E : Set G) with hΓdef
  have hQO : 𝔠.Q ≤ O (C 𝔱.x₁) := hQ.le
  have hQΓ : 𝔠.Q ≤ normalizer (Γ : Set G) := fun q hq =>
    inf_normalizer_le_normalizer_inf
      ⟨le_normalizer (hQO hq), normalizer_le_normalizer_centralizer _ (hQE hq)⟩
  have hQsΓ : IsSylowOf p Qs Γ := by
    have : Fact p.Prime := ⟨hp⟩
    have h1 : IsSylowOf p 𝔠.Q (𝔠.Q ⊔ Γ) :=
      hQ.of_le le_sup_left (sup_le hQO inf_le_left)
    have h2 := h1.inf_of_le_normalizer (le_sup_right : Γ ≤ 𝔠.Q ⊔ Γ)
      (sup_le hQΓ le_normalizer)
    have e : 𝔠.Q ⊓ Γ = Qs := by
      rw [hΓdef, hQsdef, ← inf_assoc, inf_eq_left.mpr hQO]
    rwa [e] at h2
  have hNQs : Covers (normalizer (Qs : Set G)) ρ.M₀ (O ρ.M) := by
    refine covers_normalizer_of_isSylowOf hp ρ.isPGroup_two_X ?_
      ((card_O_odd _).of_dvd_nat (card_dvd_of_le inf_le_left)) hQsΓ ?_ hNT ?_
      (fun m hm => ρ.M₀_le hm.2) ?_ le_sup_right hOMn
    · exact fun x hx => inf_normalizer_le_normalizer_inf
        ⟨hXCx hx, normalizer_le_normalizer_centralizer _ (hXE hx)⟩
    · intro x hx
      apply centralizer_le_normalizer
      rw [mem_centralizer_iff]
      intro q hq
      exact (mem_centralizer_iff.mp (hXQ hq.1) x hx).symm
    · intro m hm
      have hmM : m ∈ ρ.M := ρ.M₀_le hm.2
      have hmE : m ∈ normalizer (E : Set G) :=
        le_normalizer_commutator (H := 𝔱.T) (K := ρ.X) (L := normalizer (𝔱.T : Set G) ⊓ ρ.M₀)
          (fun g hg => hg.1)
          (fun g hg => centralizer_le_normalizer _ (ρ.M₀_le hg.2)) hm
      exact inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_O _ (𝔱.M_le_C_x₁ hmM), normalizer_le_normalizer_centralizer _ hmE⟩
    · exact (inf_le_inf_right _ inf_le_left).trans 𝔱.O_C_x₁_inf_centralizer_X_le
  have hAQs : A ≤ normalizer (Qs : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf
      ⟨𝔠.A_le_normalizer_Q ha, normalizer_le_normalizer_centralizer _ (𝔱.A_le_normalizer_E ha)⟩
  have hPQs : 𝔠.P ≤ normalizer (Qs : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf
      ⟨𝔠.P_le_normalizer_Q hg, normalizer_le_normalizer_centralizer _ (hPE hg)⟩
  refine ⟨normalizer (Qs : Set G), ⟨⟨Qs, h, 𝔠.isPGroup_P.to_le (inf_le_left.trans 𝔠.Q_le_P),
    rfl⟩, hAQs, 𝔠.P, 𝔠.hP, hPQs⟩, hNQs, ?_⟩
  refine (𝔠.covers_centralizer_V h48i hXN₀).mono fun g hg => ?_
  apply centralizer_le_normalizer
  exact centralizer_le (fun x hx => hQsV hx) hg.1

end Sec5ConfigTR

end CFSG.GH72
