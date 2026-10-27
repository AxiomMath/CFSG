module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Fus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_24

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type*} [Group G]

theorem mul_comm_of_isCyclic {F : Subgroup G} (hF : IsCyclic ↥F) {a b : G} (ha : a ∈ F)
    (hb : b ∈ F) : a * b = b * a := by
  obtain ⟨g₀, hg₀⟩ := hF.exists_generator
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ ⟨a, ha⟩)
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ ⟨b, hb⟩)
  have hk' : (g₀ : G) ^ k = a := by simpa using congrArg Subtype.val hk
  have hl' : (g₀ : G) ^ l = b := by simpa using congrArg Subtype.val hl
  rw [← hk', ← hl']
  exact (Commute.zpow_zpow_self (g₀ : G) k l).eq

theorem forall_mul_comm_sup {A B : Subgroup G} (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ u ∈ A ⊔ B, ∀ v ∈ A ⊔ B, u * v = v * u := by
  intro u hu v hv
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ :=
    (mem_sup_iff_of_le_normalizer (le_normalizer_of_commute hAB)).1 hu
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ :=
    (mem_sup_iff_of_le_normalizer (le_normalizer_of_commute hAB)).1 hv
  calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
    _ = a₁ * (a₂ * b₁) * b₂ := by rw [← hAB a₂ ha₂ b₁ hb₁]
    _ = (a₁ * a₂) * (b₁ * b₂) := by group
    _ = (a₂ * a₁) * (b₂ * b₁) := by rw [hA a₁ ha₁ a₂ ha₂, hB b₁ hb₁ b₂ hb₂]
    _ = a₂ * (a₁ * b₂) * b₁ := by group
    _ = a₂ * (b₂ * a₁) * b₁ := by rw [hAB a₁ ha₁ b₂ hb₂]
    _ = a₂ * b₂ * (a₁ * b₁) := by group

end Generic

theorem lemma2_4_s1_fusion_of (E : Lin2Hyp) (core : Lemma2_4_24_core) : Lemma2_4_s1_fusion := by
  intro G _ _ T M H S L D n hcfg s hs hsR hs2 g hg
  by_contra hgS
  have hc : centerOf L = ⊥ := core G T M H S L D n hcfg
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hST : S ≤ T := hcfg.S_le_T
  have hRT : thompsonJ S ≤ T := hRS.trans hST
  have hTR : T ≤ Subgroup.normalizer (thompsonJ S : Set G) := E.TnR hcfg
  have hi2 : (g⁻¹ * s * g) ^ 2 = 1 := by
    have : (g⁻¹ * s * g) ^ 2 = g⁻¹ * s ^ 2 * g := by simp only [pow_two]; group
    rw [this, hs2]; simp
  obtain ⟨B, hB⟩ := E.exists_B hcfg
  obtain ⟨⟨-, hRTB⟩, -, y, -, hyS, hy2, -, -, hFcyc, hTBeq, -, hFC⟩ :=
    lemma2_4_24 E.h8 E.h12 E.h14 E.h17 E.h22 core G T M H S L D n hcfg B hB _ rfl
  have hTBcomm : ∀ a ∈ T ⊓ Subgroup.normalizer (B : Set G),
      ∀ b ∈ T ⊓ Subgroup.normalizer (B : Set G), a * b = b * a := by
    rw [hTBeq]
    refine forall_mul_comm_sup (A := Subgroup.zpowers y)
      (B := S ⊓ Subgroup.normalizer (B : Set G)) ?_ ?_ ?_
    · intro a ha a' ha'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
      exact (Commute.zpow_zpow_self y k l).eq
    · intro b hb b' hb'
      exact mul_comm_of_isCyclic hFcyc hb hb'
    · intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      have h1 : Commute y b := (Subgroup.mem_centralizer_singleton_iff.mp (hFC hb)).symm
      exact (h1.zpow_left k).eq
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a⁻¹ * b⁻¹ * a * b ∈ thompsonJ S :=
    commutator_mem_of_sup_commutative hTR inf_le_left hRTB hTBcomm
  have hiT : g⁻¹ * s * g ∈ T := hg
  have hiS : g⁻¹ * s * g ∉ S := hgS
  obtain ⟨x, hxT, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  have hsq : (g⁻¹ * s * g) ^ 2 ∈ thompsonJ S := by rw [hi2]; exact one_mem _
  obtain ⟨-, htrans, hcases⟩ := E.h14 G T M H S L D n hcfg (g⁻¹ * s * g) hiT hiS hsq
  have hxcomm : ∀ g' ∈ T, (g⁻¹ * s * g)⁻¹ * g'⁻¹ * (g⁻¹ * s * g) * g' ∈ thompsonJ S :=
    fun g' hg' => hcomm _ hiT g' hg'
  rcases hcases hi2 with hA | hB' | hC'
  ·
    obtain ⟨-, hZRi, -⟩ := hA
    have hZc : lin2Z L (thompsonJ S) = centerOf (thompsonJ S) :=
      ((lin2Z_cases (rfl : lin2Z L (thompsonJ S) = lin2Z L (thompsonJ S))).resolve_right
        fun h => h.1 hc).2
    obtain ⟨hZe, hZcard, -⟩ := E.Zbasic hcfg (Z := lin2Z L (thompsonJ S)) rfl
    have hZTI : fusionIsTI (lin2Z L (thompsonJ S)) := E.ZTI hcfg (Z := lin2Z L (thompsonJ S)) rfl
    have hRweak : thompsonJ S = weakClosure (lin2Z L (thompsonJ S)) T :=
      E.h19 G T M H S L D n hcfg (lin2Z L (thompsonJ S)) rfl
    have hZle_i : lin2Z L (thompsonJ S) ≤ Subgroup.centralizer ({g⁻¹ * s * g} : Set G) := by
      intro z hz
      rw [hZc, hZRi] at hz
      exact hz.2
    have hZR : lin2Z L (thompsonJ S) ≤ thompsonJ S := by rw [hZc]; exact inf_le_left
    have hZT : lin2Z L (thompsonJ S) ≤ T := hZR.trans hRT
    obtain ⟨-, -, -, -, -, hsyl⟩ := lemma2_4_23_main E G T M H S L D n hcfg s hs hsR hs2
    set Z := lin2Z L (thompsonJ S) with hZdef
    set C := Subgroup.centralizer ({s} : Set G) with hC
    have hZ'C : conjR Z g⁻¹ ≤ C := by
      intro y' hy'
      rw [mem_conjR, inv_inv] at hy'
      have h1 : g⁻¹ * y' * g * (g⁻¹ * s * g) = (g⁻¹ * s * g) * (g⁻¹ * y' * g) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hZle_i hy')
      have h2 : g⁻¹ * (y' * s) * g = g⁻¹ * (s * y') * g := by
        calc g⁻¹ * (y' * s) * g = g⁻¹ * y' * g * (g⁻¹ * s * g) := by group
          _ = g⁻¹ * s * g * (g⁻¹ * y' * g) := h1
          _ = g⁻¹ * (s * y') * g := by group
      exact Subgroup.mem_centralizer_singleton_iff.2 (mul_left_cancel (mul_right_cancel h2))
    have hZ2 : IsPGroup 2 (conjR Z g⁻¹) :=
      (isPGroup_conjR_iff 2).mpr (hcfg.sylowT.isPGroup.to_le hZT)
    obtain ⟨P₁, hZ'P₁, hP₁⟩ := exists_isSylowTwoOf_of_le hZ'C hZ2
    obtain ⟨c, hcC, hc'⟩ := hsyl.exists_conj hP₁
    have hZ''Ts : conjR (conjR Z g⁻¹) c ≤ T ⊓ C := by
      intro y' hy'
      rw [mem_conjR] at hy'
      have h1 : c * y' * c⁻¹ ∈ P₁ := hZ'P₁ hy'
      rw [hc'] at h1
      obtain ⟨z, hz, hzy⟩ := h1
      have h2 : c * z * c⁻¹ = c * y' * c⁻¹ := by simpa [MulAut.conj_apply] using hzy
      have : z = y' := by
        calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
          _ = c⁻¹ * (c * y' * c⁻¹) * c := by rw [h2]
          _ = y' := by group
      rw [← this]
      exact hz
    have hZ''e : conjR Z (g⁻¹ * c) ≤ T ⊓ C := by rw [← conjR_conjR]; exact hZ''Ts
    have hZ''R : conjR Z (g⁻¹ * c) ≤ thompsonJ S := by
      rw [hRweak]
      exact le_weakClosure (hZ''e.trans inf_le_left)
    have hZ''RC : conjR Z (g⁻¹ * c) ≤ thompsonJ S ⊓ C := le_inf hZ''R (hZ''e.trans inf_le_right)
    have hZ''ea : IsElemAbelian 2 (conjR Z (g⁻¹ * c)) := (isElemAbelian_conjR_iff _ _).mpr hZe
    have hZ''card : Nat.card (conjR Z (g⁻¹ * c)) = 2 ^ n := by rw [card_conjR]; exact hZcard
    obtain ⟨hUs, -⟩ := (E.U_s_values hcfg hs hsR hs2 hxT hxS).1 hc
    have hVs := E.card_conjR_U_inf_centralizer hcfg hs hsR hs2 hxT
    have hZCle : Z ⊓ C ≤ conjR Z (g⁻¹ * c) := by
      have hZU : Z ≤ blockU L := by rw [hZc]; exact E.centerOf_R_le_U hcfg
      rcases E.elem_le_U_s_or_V_s hcfg hxT hxS hZ''RC hZ''ea with hU | hV
      · have heq : conjR Z (g⁻¹ * c) = blockU L ⊓ C :=
          Subgroup.eq_of_le_of_card_ge hU (by rw [hUs, hZ''card])
        rw [heq]
        exact inf_le_inf_right _ hZU
      · have heq : conjR Z (g⁻¹ * c) = conjR (blockU L) x ⊓ C :=
          Subgroup.eq_of_le_of_card_ge hV (by rw [hVs, hUs, hZ''card])
        rw [heq]
        have hZx : conjR Z x = Z := by
          rcases E.Zcases hcfg (Z := Z) rfl hxT hxS with ⟨-, h, -⟩ | ⟨h, -⟩
          · exact h
          · exact absurd hc h
        refine inf_le_inf_right _ ?_
        calc Z = conjR Z x := hZx.symm
          _ ≤ conjR (blockU L) x := conjR_mono hZU x
    have hCZ : Nat.card (Z ⊓ C : Subgroup G) = 2 ^ (n / 2) :=
      E.card_Z_inf_centralizer hcfg (Z := Z) rfl hs hsR hs2
    have hn := hcfg.one_lt
    have hne : Z ⊓ conjR Z (g⁻¹ * c) ≠ ⊥ := by
      intro h
      have h0 : Z ⊓ C ≤ Z ⊓ conjR Z (g⁻¹ * c) := le_inf inf_le_left hZCle
      rw [h] at h0
      have h1 : Nat.card (Z ⊓ C : Subgroup G) ≤ 1 := by
        have := Subgroup.card_le_of_le h0
        simpa using this
      rw [hCZ] at h1
      have : 1 < 2 ^ (n / 2) := Nat.one_lt_two_pow (by omega)
      omega
    have hEq : conjR Z (g⁻¹ * c) = Z := conjR_eq_of_inf_ne_bot hZTI hne
    have hZC : Z ≤ C := by
      have : Z ≤ conjR Z (g⁻¹ * c) := by rw [hEq]
      exact this.trans (hZ''e.trans inf_le_right)
    have hZinf : Z ⊓ C = Z := inf_eq_left.mpr hZC
    rw [hZinf, hZcard] at hCZ
    have := Nat.pow_right_injective (le_refl 2) hCZ
    omega
  ·
    obtain ⟨-, -, hcardR, hcardΩ⟩ := hB'
    refine E.not_conj_of_card hcfg hs hsR hs2 hi2 hxcomm htrans ?_ ?_ g rfl
    · rw [hcardR, (E.card_R_inf_centralizer hcfg hs hsR hs2).1 hc]
    · rw [hcardΩ, ((E.U_s_values hcfg hs hsR hs2 hxT hxS).1 hc).1]
      exact Nat.pow_lt_pow_right (by norm_num) (by have := hcfg.one_lt; omega)
  · exact (hC'.1 hc).elim

end CFSG.QuasithinUnique.Lin2
