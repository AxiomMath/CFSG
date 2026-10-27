module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf16AeM

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin

section E64

theorem e64_core : ∀ ℓ ∈ AE.fanoLines, ∀ ℓ' ∈ AE.fanoLines, ∃ k : Fin 7, ∃ ℓ₃ ∈ AE.fanoLines,
    ∃ c : ZMod 2, (∀ i ∈ ℓ₃ᶜ, ind ℓᶜ i + ind ℓ'ᶜ i = c) ∧
      ℓ₃ᶜ = (ℓᶜ).map ((finRotate 7) ^ k.val).toEmbedding := by
  decide +kernel

theorem finRotate_mem_l32 : finRotate 7 ∈ AE.l32 := by
  intro s hs
  revert s
  decide +kernel

theorem sign_finRotate_pow (k : ℕ) : Equiv.Perm.sign ((finRotate 7) ^ k) = 1 := by
  rw [map_pow, sign_finRotate]
  norm_num

theorem e64_comb : ∀ α ∈ AE.e64Sets, ∀ β ∈ AE.e64Sets, ∃ γ ∈ AE.e64Sets, ∃ (_ : γ.card = 4) (c : ZMod 2),
    (∀ i ∈ γ, ind α i + ind β i = c) ∧ ∃ σ : Equiv.Perm (Fin 7),
      (σ ∈ AE.l32 ∧ Equiv.Perm.sign σ = 1) ∧ ∀ y, y ∈ γ ↔ σ.symm y ∈ α := by
  rintro α ⟨ℓ, hℓ, rfl⟩ β ⟨ℓ', hℓ', rfl⟩
  obtain ⟨k, ℓ₃, h₃, c, hc, hmap⟩ := e64_core ℓ hℓ ℓ' hℓ'
  refine ⟨ℓ₃ᶜ, ⟨ℓ₃, h₃, rfl⟩, ?_, c, hc, (finRotate 7) ^ k.val,
    ⟨pow_mem finRotate_mem_l32 _, sign_finRotate_pow _⟩, ?_⟩
  · have : ∀ ℓ ∈ AE.fanoLines, ℓᶜ.card = 4 := by decide +kernel
    exact this ℓ₃ h₃
  · intro y
    rw [hmap]
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨_, hy, by simp⟩

end E64

section OnGeneric


open AeM CFSG.ClassicalInvolution.Q3.AE in
theorem e189_aeOn_alt2 {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (F : TwinDisc.ExitO2.Q8Fam Y Δ) {n : ℕ} (hn5 : 5 ≤ n)
    {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AE.AEQ n)} (I : AEIdentOn Δ n 𝒜 H)
    (P : Equiv.Perm (Fin n) → Prop) (hP : ∀ σ, P σ → AE.mkQ n (AE.Wr.ofPerm σ) ∈ H)
    (hcomb : ∀ α ∈ 𝒜, ∀ β ∈ 𝒜, ∃ γ ∈ 𝒜, ∃ (hγ : γ.card = 4),
      (∀ δ ∈ 𝒜, ∀ hδ : δ.card = 4, AE.zBar δ hδ = AE.zBar γ hγ →
        ∃ c : ZMod 2, ∀ i ∈ δ, ind α i + ind β i = c) ∧
      ∃ σ : Equiv.Perm (Fin n), P σ ∧ ∀ y, y ∈ γ ↔ σ.symm y ∈ α)
    {K J : Subgroup Y} (hK : K ∈ Δ) (hJ : J ∈ Δ) {z t : Y} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    ∃ x : Y, ∃ M' ∈ twinSet Δ (conjSub x K), M' ≠ conjSub x K ∧ ∃ R₁ R₂ : Subgroup Y,
      IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  have hΩ := F.hyp
  have hX : ∀ y : Y, y ∈ pSpan Δ := fun y => F.gen ▸ Subgroup.mem_top y
  let ψ : Y →* AE.AEQ n :=
    { toFun := fun y => I.φ ⟨y, hX y⟩
      map_one' := by
        rw [show (⟨1, hX 1⟩ : ↥(pSpan Δ)) = 1 from rfl, map_one]
      map_mul' := fun a b => by
        rw [show (⟨a * b, hX (a * b)⟩ : ↥(pSpan Δ)) = ⟨a, hX a⟩ * ⟨b, hX b⟩ from rfl, map_mul] }
  have map_psi : ∀ L : Subgroup Y, L.map ψ = (L.subgroupOf (pSpan Δ)).map I.φ := by
    intro L
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hX y⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    · rintro ⟨⟨y, hy'⟩, hy, rfl⟩
      exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  have hlab' : ∀ L ∈ Δ, ∃ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Δ)).map I.φ = AE.memBar α h b := fun L hL => by
    obtain ⟨α, -, h, b, hl⟩ := I.label L hL
    exact ⟨α, h, b, hl⟩
  refine e189_ae_core' hΩ F.two ψ 𝒜 P ?_ ?_ ?_ ?_ ?_ hcomb hK hJ hz ht hzt hne
  · intro L hL
    obtain ⟨α, hα, h, b, hl⟩ := I.label L hL
    exact ⟨α, hα, h, b, by rw [map_psi]; exact hl⟩
  · intro L hL M hM hLM
    obtain ⟨a, haL, ha2⟩ := F.exists_mul_self_ne_one L hL
    refine TwinDisc.ExitO2.fam_eq_of_phi_mem I.φ F hn5 I.ker_le hlab' hL hM haL ha2 ?_
    have : I.φ ⟨a, le_pSpan hL haL⟩ ∈ (L.subgroupOf (pSpan Δ)).map I.φ :=
      ⟨⟨a, le_pSpan hL haL⟩, Subgroup.mem_subgroupOf.mpr haL, rfl⟩
    rw [← map_psi, hLM, map_psi] at this
    exact this
  · intro M hM l₁ hl₁ l₂ hl₂ he
    obtain ⟨α, h, b, hl⟩ := hlab' M hM
    exact phi_injOn I.φ hn5 hM ((F.card M hM).trans (by norm_num)) hl hl₁ hl₂ he
  · intro L hL α h b hl u hu
    have h8 : Nat.card ↥L = 8 := (F.card L hL).trans (by norm_num)
    exact phi_map_eq_zBar I.φ hn5 hL h8 (by rw [← map_psi]; exact hl) hu
  · intro σ hσ
    have hxr : AE.mkQ n (AE.Wr.ofPerm σ) ∈ I.φ.range := by
      rw [I.range_eq]
      exact hP σ hσ
    obtain ⟨x', hx'⟩ := hxr
    exact ⟨(x' : Y), hx'⟩

end OnGeneric

section E64Main


open AeM CFSG.ClassicalInvolution.Q3.AE in
theorem e189_e64_alt2 {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (F : TwinDisc.ExitO2.Q8Fam Y Δ) (I : AEIdentOn Δ 7 AE.e64Sets AE.e64Sub)
    {K J : Subgroup Y} (hK : K ∈ Δ) (hJ : J ∈ Δ) {z t : Y} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    ∃ x : Y, ∃ M' ∈ twinSet Δ (conjSub x K), M' ≠ conjSub x K ∧ ∃ R₁ R₂ : Subgroup Y,
      IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  refine e189_aeOn_alt2 F (by norm_num) I
    (fun σ => σ ∈ AE.l32 ∧ Equiv.Perm.sign σ = 1) ?_ ?_ hK hJ hz ht hzt hne
  · rintro σ ⟨hl, hs⟩
    exact Subgroup.mem_map_of_mem _ ⟨ofPerm_mem_aeSub hs, hl⟩
  · intro α hα β hβ
    obtain ⟨γ, hγ𝒜, hγ, c, hc, hσ⟩ := e64_comb α hα β hβ
    refine ⟨γ, hγ𝒜, hγ, fun δ _ hδ he => ?_, hσ⟩
    have := AE.eq_of_zBar_eq (by norm_num) he
    subst this
    exact ⟨c, hc⟩

end E64Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
