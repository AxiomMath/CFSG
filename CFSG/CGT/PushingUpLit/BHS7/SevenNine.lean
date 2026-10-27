module

public import CFSG.CGT.PushingUpLit.BHS7.BlockV
public import CFSG.CGT.PushingUpLit.BHS7.Dedekind

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

omit [Group Γ] in
theorem commutator_mul_left_of_mem_centralizer [Group Γ] {V : Subgroup Γ} {c f v : Γ}
    (hc : c ∈ Subgroup.centralizer (V : Set Γ)) (hf : f ∈ Subgroup.normalizer (V : Set Γ))
    (hv : v ∈ V) : ⁅c * f, v⁆ = ⁅f, v⁆ := by
  have hu : f * v * f⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hf v).mp hv
  have hcu : c * (f * v * f⁻¹) = (f * v * f⁻¹) * c :=
    (Subgroup.mem_centralizer_iff.mp hc _ hu).symm
  simp only [commutatorElement_def]
  calc c * f * v * (c * f)⁻¹ * v⁻¹ = c * (f * v * f⁻¹) * c⁻¹ * v⁻¹ := by group
    _ = (f * v * f⁻¹) * c * c⁻¹ * v⁻¹ := by rw [hcu]
    _ = f * v * f⁻¹ * v⁻¹ := by group

omit [Group Γ] in
theorem commutator_mul_right_of_mem_centralizer [Group Γ] {V : Subgroup Γ} {c x w : Γ}
    (hc : c ∈ Subgroup.centralizer (V : Set Γ)) (hx : x ∈ Subgroup.normalizer (V : Set Γ))
    (hw : w ∈ V) : ⁅w, c * x⁆ = ⁅w, x⁆ := by
  have hu : x * w⁻¹ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hx w⁻¹).mp (V.inv_mem hw)
  have hv : w * (x * w⁻¹ * x⁻¹) ∈ V := V.mul_mem hw hu
  have hcw : c * w = w * c := (Subgroup.mem_centralizer_iff.mp hc w hw).symm
  have hcv : c * (w * (x * w⁻¹ * x⁻¹)) = (w * (x * w⁻¹ * x⁻¹)) * c :=
    (Subgroup.mem_centralizer_iff.mp hc _ hv).symm
  simp only [commutatorElement_def]
  have e1 : w * (c * x) * w⁻¹ * (c * x)⁻¹ = c * (w * (x * w⁻¹ * x⁻¹)) * c⁻¹ := by
    calc w * (c * x) * w⁻¹ * (c * x)⁻¹ = (w * c) * x * w⁻¹ * x⁻¹ * c⁻¹ := by group
      _ = (c * w) * x * w⁻¹ * x⁻¹ * c⁻¹ := by rw [hcw]
      _ = c * (w * (x * w⁻¹ * x⁻¹)) * c⁻¹ := by group
  rw [e1, hcv]
  group

section Finite

variable [Finite Γ] {G T F V X : Subgroup Γ}

theorem conj_mem_blockW_of_comm_mod (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hF : IsBTBlock G T F) (hVQ : V ≤ pCoreOf 2 G) (hGV : G ≤ Subgroup.normalizer (V : Set Γ))
    (hne : ⁅F, V⁆ ≠ ⊥) {x : Γ} (hxG : x ∈ G)
    (hx : ∀ f ∈ F, ⁅x, f⁆ ∈ Subgroup.centralizer (V : Set Γ)) :
    ∀ w ∈ blockW F, x * w * x⁻¹ ∈ blockW F := by
  have hFV : F ≤ Subgroup.normalizer (V : Set Γ) := hF.le.trans hGV
  have hW : ⁅F, V⁆ = blockW F := commutator_eq_blockW hG hT hF hVQ hFV hne
  have hle : ⁅F, V⁆ ≤ (blockW F).comap (MulAut.conj x).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro f hf v hv
    have hxv : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hGV hxG) v).mp hv
    have h1 : x * ⁅f, v⁆ * x⁻¹ = ⁅⁅x, f⁆ * f, x * v * x⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    show x * ⁅f, v⁆ * x⁻¹ ∈ blockW F
    rw [h1, commutator_mul_left_of_mem_centralizer (hx f hf) (hFV hf) hxv, ← hW]
    exact Subgroup.commutator_mem_commutator hf hxv
  intro w hw
  exact hle (hW ▸ hw : w ∈ ⁅F, V⁆)

theorem commutator_blockW_eq_bot_of_comm_mod (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hF : IsBTBlock G T F) (hVQ : V ≤ pCoreOf 2 G) (hGV : G ≤ Subgroup.normalizer (V : Set Γ))
    (hne : ⁅F, V⁆ ≠ ⊥) (hX2 : IsPGroup 2 X) (hXG : X ≤ G)
    (hX : ∀ x ∈ X, ∀ f ∈ F, ⁅x, f⁆ ∈ Subgroup.centralizer (V : Set Γ)) :
    ⁅blockW F, X⁆ = ⊥ := by
  have hFV : F ≤ Subgroup.normalizer (V : Set Γ) := hF.le.trans hGV
  have hW : ⁅F, V⁆ = blockW F := commutator_eq_blockW hG hT hF hVQ hFV hne
  have hWV : blockW F ≤ V := hW ▸ commutator_le_of_le_normalizer hFV
  have hWE : blockW F = pCoreOf 2 F := blockW_eq_pCoreOf hF
  have hchar : CharTwo F := charTwo_of_isBTBlock hG hT hF
  have hWab : ∀ x ∈ blockW F, ∀ y ∈ blockW F, x * y = y * x := by
    rw [hWE]; exact hF.elemAbelian.1
  have hW2 : IsPGroup 2 ↥(blockW F) := by
    rw [hWE]; exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 F
  have hWne : blockW F ≠ ⊥ := by
    rw [hWE]; exact pCoreOf_ne_bot hF hchar
  have hFW : ∀ g ∈ F, ∀ w ∈ blockW F, g * w * g⁻¹ ∈ blockW F := fun g hg w hw =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_blockW F hg) w).mp hw
  have hXW : ∀ x ∈ X, ∀ w ∈ blockW F, x * w * x⁻¹ ∈ blockW F := fun x hx =>
    conj_mem_blockW_of_comm_mod hG hT hF hVQ hGV hne (hXG hx) (hX x hx)
  have hXN : X ≤ Subgroup.normalizer (blockW F : Set Γ) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hXW x hx w hw, fun hw => ?_⟩
    have := hXW x⁻¹ (X.inv_mem hx) _ hw
    simpa [mul_assoc] using this
  set N : Subgroup Γ := ⁅blockW F, X⁆ with hN
  have hNW : N ≤ pCoreOf 2 F := by
    rw [← hWE, hN, Subgroup.commutator_le]
    intro w hw x hx
    have h1 : ⁅w, x⁆ = w * (x * w⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [h1]
    exact (blockW F).mul_mem hw (hXW x hx _ ((blockW F).inv_mem hw))
  have hNinv : ∀ g ∈ F, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg
    have hle : N ≤ N.comap (MulAut.conj g).toMonoidHom := by
      rw [hN, Subgroup.commutator_le]
      intro w hw x hx
      have hc : ⁅g, x⁆ ∈ Subgroup.centralizer (V : Set Γ) := by
        have := (Subgroup.centralizer (V : Set Γ)).inv_mem (hX x hx g hg)
        rwa [commutatorElement_inv] at this
      have hgw : g * w * g⁻¹ ∈ blockW F := hFW g hg w hw
      have h1 : g * ⁅w, x⁆ * g⁻¹ = ⁅g * w * g⁻¹, ⁅g, x⁆ * x⁆ := by
        simp only [commutatorElement_def]; group
      show g * ⁅w, x⁆ * g⁻¹ ∈ ⁅blockW F, X⁆
      rw [h1, commutator_mul_right_of_mem_centralizer hc (hGV (hXG hx)) (hWV hgw)]
      exact Subgroup.commutator_mem_commutator hgw hx
    exact fun n hn => hle hn
  set C : Subgroup Γ := pCoreOf 2 F ⊓ Subgroup.centralizer (F : Set Γ) with hC
  have hCW : C ≤ pCoreOf 2 F := inf_le_left
  have hCN : ∀ c ∈ C, ∀ g ∈ F, g * c * g⁻¹ = c := fun c hc g hg => by
    have := Subgroup.mem_centralizer_iff.mp hc.2 g hg
    calc g * c * g⁻¹ = c * g * g⁻¹ := by rw [this]
      _ = c := by group
  have hinv : ∀ g ∈ F, ∀ m ∈ N ⊔ C, g * m * g⁻¹ ∈ N ⊔ C := by
    intro g hg
    have hle : N ⊔ C ≤ (N ⊔ C).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun n hn => ?_) (fun c hc => ?_)
      · exact (le_sup_left : N ≤ N ⊔ C) (hNinv g hg n hn)
      · show g * c * g⁻¹ ∈ N ⊔ C
        rw [hCN c hc g hg]
        exact (le_sup_right : C ≤ N ⊔ C) hc
    exact fun m hm => hle hm
  have hNnc : N ≤ C := by
    rcases pCoreOf_irred hF hchar (N ⊔ C) le_sup_right (sup_le hNW hCW) hinv with h1 | h2
    · exact le_sup_left.trans h1.le
    · exfalso
      have hWN : blockW F ≤ N := by
        have hperf : ⁅blockW F, F⁆ = blockW F := by rw [hWE]; exact hF.perfect
        rw [← hperf, Subgroup.commutator_le]
        intro w hw g hg
        have hwNC : w ∈ N ⊔ C := by rw [h2, ← hWE]; exact hw
        obtain ⟨n, hn, c, hc, rfl⟩ := exists_mul_of_mem_sup'
          (fun n hn c hc => hWab n (by rw [hWE]; exact hNW hn) c (by rw [hWE]; exact hCW hc)) hwNC
        have hcg : c * g = g * c := (Subgroup.mem_centralizer_iff.mp hc.2 g hg).symm
        have h1 : ⁅n * c, g⁆ = n * (g * n⁻¹ * g⁻¹) := by
          simp only [commutatorElement_def]
          calc n * c * g * (n * c)⁻¹ * g⁻¹ = n * (c * g) * c⁻¹ * n⁻¹ * g⁻¹ := by group
            _ = n * (g * c) * c⁻¹ * n⁻¹ * g⁻¹ := by rw [hcg]
            _ = n * (g * n⁻¹ * g⁻¹) := by group
        rw [h1]
        exact N.mul_mem hn (by simpa [mul_assoc] using hNinv g hg n⁻¹ (N.inv_mem hn))
      have hlt := commutator_lt_of_isPGroup hW2 hX2 hXN hWne
      exact absurd (le_antisymm (hN ▸ hlt.le) hWN) hlt.ne
  have h1 : ⁅⁅F, X⁆, blockW F⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro y hy w hw
    have hyC : y ∈ Subgroup.centralizer (V : Set Γ) := by
      refine (Subgroup.commutator_le.mpr (fun f hf x hx => ?_) : ⁅F, X⁆ ≤ _) hy
      have := (Subgroup.centralizer (V : Set Γ)).inv_mem (hX x hx f hf)
      rwa [commutatorElement_inv] at this
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hyC w (hWV hw)).symm
  have h2 : ⁅⁅X, blockW F⁆, F⁆ = ⊥ := by
    rw [Subgroup.commutator_comm X (blockW F), ← hN, eq_bot_iff, Subgroup.commutator_le]
    intro n hn g hg
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hNnc hn).2 g hg).symm
  have h3 : ⁅⁅blockW F, F⁆, X⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := blockW F) (H₂ := F) (H₃ := X) h1 h2
  have hperf : ⁅blockW F, F⁆ = blockW F := by rw [hWE]; exact hF.perfect
  rwa [hperf] at h3

theorem commutator_commutator_eq_bot_of_comm_mod (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hF : IsBTBlock G T F) (hVQ : V ≤ pCoreOf 2 G) (hGV : G ≤ Subgroup.normalizer (V : Set Γ))
    (hne : ⁅F, V⁆ ≠ ⊥) (hX2 : IsPGroup 2 X) (hXG : X ≤ G)
    (hX : ∀ x ∈ X, ∀ f ∈ F, ⁅x, f⁆ ∈ Subgroup.centralizer (V : Set Γ)) :
    ⁅⁅V, X⁆, F⁆ = ⊥ := by
  have hFV : F ≤ Subgroup.normalizer (V : Set Γ) := hF.le.trans hGV
  have hW : ⁅F, V⁆ = blockW F := commutator_eq_blockW hG hT hF hVQ hFV hne
  have hWX := commutator_blockW_eq_bot_of_comm_mod hG hT hF hVQ hGV hne hX2 hXG hX
  have h1 : ⁅⁅V, F⁆, X⁆ = ⊥ := by
    rw [Subgroup.commutator_comm V F, hW]; exact hWX
  have h2 : ⁅⁅F, X⁆, V⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro y hy v hv
    have hyC : y ∈ Subgroup.centralizer (V : Set Γ) := by
      refine (Subgroup.commutator_le.mpr (fun f hf x hx => ?_) : ⁅F, X⁆ ≤ _) hy
      have := (Subgroup.centralizer (V : Set Γ)).inv_mem (hX x hx f hf)
      rwa [commutatorElement_inv] at this
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hyC v hv).symm
  rw [Subgroup.commutator_comm V X]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := X) (H₂ := V) (H₃ := F) h1 h2

end Finite

end CFSG.CGT.PushingUpLit.BHS7
