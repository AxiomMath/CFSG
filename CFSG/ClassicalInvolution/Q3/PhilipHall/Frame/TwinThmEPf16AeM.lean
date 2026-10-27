module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf15Rigid
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf14Ae5Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Phi

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open scoped commutatorElement

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin

namespace AeM

open CFSG.ClassicalInvolution.Q3.AE

theorem conj_zOf_set {m : ℕ} (x : AE.Wr m) (α γ : Finset (Fin m)) (hα : α.card = 4)
    (hγ : γ.card = 4) (hx : ∀ y, y ∈ γ ↔ x.perm.symm y ∈ α) :
    x * zOf (emb α hα) * x⁻¹ = zOf (emb γ hγ) := by
  refine AE.Wr.ext (funext fun y => ?_) ?_
  · rw [Ae5Model.conj_vec_of_perm_one x _ (zOf_perm _), zOf_vec_apply, zOf_vec_apply]
    have hr : ∀ (s : Finset (Fin m)) (h : s.card = 4), Set.range (emb s h) = ↑s := fun s h => range_emb s h
    have h1 : x.perm.symm y ∈ Set.range (emb α hα) ↔ y ∈ Set.range (emb γ hγ) := by
      rw [hr, hr]
      simp only [Finset.mem_coe]
      exact (hx y).symm
    simp only [h1]
  · rw [AE.Wr.mul_perm, AE.Wr.mul_perm, zOf_perm, zOf_perm, AE.Wr.inv_perm, mul_one,
      mul_inv_cancel]

theorem zBar_conj_set {m : ℕ} (x : AE.Wr m) (α γ : Finset (Fin m)) (hα : α.card = 4)
    (hγ : γ.card = 4) (hx : ∀ y, y ∈ γ ↔ x.perm.symm y ∈ α) :
    mkQ m x * zBar α hα * (mkQ m x)⁻¹ = zBar γ hγ := by
  unfold zBar
  rw [← map_inv, ← map_mul, ← map_mul, conj_zOf_set x α γ hα hγ hx]

theorem comm_vec_embed {m : ℕ} (U : AE.Wr m) (hU1 : U.perm = 1) (ι : Fin 4 ↪ Fin m)
    (hU : ∀ i ∈ Set.range ι, ∀ j ∈ Set.range ι, U.vec i = U.vec j) (k : AE.Wr 4) :
    U * embed ι k = embed ι k * U := by
  refine AE.Wr.ext (funext fun i => ?_) ?_
  · rw [AE.Wr.mul_vec, AE.Wr.mul_vec, hU1]
    have h1 : (embed ι k).vec (( (1 : Equiv.Perm (Fin m))).symm i) = (embed ι k).vec i := rfl
    rw [h1]
    have h2 : U.vec ((embed ι k).perm.symm i) = U.vec i := by
      by_cases hi : i ∈ Set.range ι
      · obtain ⟨j, rfl⟩ := hi
        rw [embed_perm, embedPerm_symm_apply]
        exact hU _ (Set.mem_range_self _) _ (Set.mem_range_self _)
      · rw [embed_perm, embedPerm_symm_of_not_mem ι _ hi]
    rw [h2, add_comm]
  · rw [AE.Wr.mul_perm, AE.Wr.mul_perm, hU1, one_mul, mul_one]

theorem exists_even_perm_map {m : ℕ} (α γ : Finset (Fin m)) (h : α.card = γ.card) (h2 : 2 ≤ α.card) :
    ∃ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ = 1 ∧ ∀ y, y ∈ γ ↔ σ.symm y ∈ α := by
  classical
  let e : {x // x ∈ α} ≃ {x // x ∈ γ} := Finset.equivOfCardEq h
  set σ₀ : Equiv.Perm (Fin m) := e.extendSubtype with hσ₀
  have hmap : α.map σ₀.toEmbedding = γ := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      exact Equiv.extendSubtype_mem e x hx
    · rw [Finset.card_map, h]
  have hiff : ∀ σ : Equiv.Perm (Fin m), α.map σ.toEmbedding = γ → ∀ y, y ∈ γ ↔ σ.symm y ∈ α := by
    intro σ hσ y
    rw [← hσ]
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨σ.symm y, hy, by simp⟩
  by_cases hs : Equiv.Perm.sign σ₀ = 1
  · exact ⟨σ₀, hs, hiff σ₀ hmap⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < α.card)
    refine ⟨σ₀ * Equiv.swap a b, ?_, hiff _ ?_⟩
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
      have : Equiv.Perm.sign σ₀ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ₀) with h | h
        · exact absurd h hs
        · exact h
      rw [this]; decide
    · rw [← hmap]
      ext y
      simp only [Finset.mem_map, Equiv.coe_toEmbedding, Equiv.Perm.mul_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨Equiv.swap a b x, ?_, rfl⟩
        rw [Equiv.swap_apply_def]
        split_ifs <;> assumption
      · rintro ⟨x, hx, rfl⟩
        refine ⟨Equiv.swap a b x, ?_, ?_⟩
        · rw [Equiv.swap_apply_def]
          split_ifs <;> assumption
        · simp

theorem ofPerm_mem_aeSub {m : ℕ} {σ : Equiv.Perm (Fin m)} (h : Equiv.Perm.sign σ = 1) :
    AE.Wr.ofPerm σ ∈ AE.aeSub m := by
  refine ⟨?_, h⟩
  unfold AE.Wr.wsum
  simp [AE.Wr.ofPerm]

end AeM

section Main


open AeM CFSG.ClassicalInvolution.Q3.AE in
@[expose] def ind {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : ZMod 2 := if i ∈ s then 1 else 0

open AeM CFSG.ClassicalInvolution.Q3.AE in
theorem e189_ae_core' {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (hΩ : HypOmegaGen Δ) (htwo : ∀ L ∈ Δ, IsPGroup 2 L) {n : ℕ}
    (ψ : Y →* AE.AEQ n) (𝒜 : Set (Finset (Fin n))) (P : Equiv.Perm (Fin n) → Prop)
    (hlab : ∀ L ∈ Δ, ∃ α ∈ 𝒜, ∃ h : α.card = 4, ∃ b : Bool, L.map ψ = AE.memBar α h b)
    (hinj : ∀ L ∈ Δ, ∀ M ∈ Δ, L.map ψ = M.map ψ → L = M)
    (hinjOn : ∀ M ∈ Δ, Set.InjOn ψ (M : Set Y))
    (zimg : ∀ L ∈ Δ, ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      L.map ψ = AE.memBar α h b → ∀ u : Y, IsUniqueInvolution L u → ψ u = AE.zBar α h)
    (hlift : ∀ σ : Equiv.Perm (Fin n), P σ → ∃ x : Y, ψ x = AE.mkQ n (AE.Wr.ofPerm σ))
    (hcomb : ∀ α ∈ 𝒜, ∀ β ∈ 𝒜, ∃ γ ∈ 𝒜, ∃ (hγ : γ.card = 4),
      (∀ δ ∈ 𝒜, ∀ hδ : δ.card = 4, AE.zBar δ hδ = AE.zBar γ hγ →
        ∃ c : ZMod 2, ∀ i ∈ δ, ind α i + ind β i = c) ∧
      ∃ σ : Equiv.Perm (Fin n), P σ ∧ ∀ y, y ∈ γ ↔ σ.symm y ∈ α)
    {K J : Subgroup Y} (hK : K ∈ Δ) (hJ : J ∈ Δ) {z t : Y} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    ∃ x : Y, ∃ M' ∈ twinSet Δ (conjSub x K), M' ≠ conjSub x K ∧ ∃ R₁ R₂ : Subgroup Y,
      IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  have hconj : ∀ g : Y, ∀ L ∈ Δ, conjSub g L ∈ Δ := fun g L hL => hΩ.conjInvariant g L hL
  have hsyl : ∀ L ∈ Δ, IsSylow2In L L := fun L hL =>
    ⟨le_rfl, htwo L hL, fun V hV _ hLV => le_antisymm hV hLV⟩
  set K'' := conjSub t K with hK''def
  have hK'' : K'' ∈ Δ := hconj t K hK
  have hzK'' : IsUniqueInvolution K'' z := by
    have := hz.conj t
    rwa [show t * z * t⁻¹ = z by rw [← hzt]; group] at this
  obtain ⟨α, hα𝒜, hα, bK, hKl⟩ := hlab K hK
  obtain ⟨β, hβ𝒜, hβ, bJ, hJl⟩ := hlab J hJ
  have hψz : ψ z = AE.zBar α hα := zimg K hK α hα bK hKl z hz
  have hψt : ψ t = AE.zBar β hβ := zimg J hJ β hβ bJ hJl t ht
  set Z1 := zOf (emb α hα) with hZ1
  set Z2 := zOf (emb β hβ) with hZ2
  set U := Z1 * Z2 with hU
  have hψzt : ψ (z * t) = AE.mkQ n U := by
    rw [map_mul, hψz, hψt]
    rfl
  have hU1 : U.perm = 1 := by rw [hU, AE.Wr.mul_perm, hZ1, hZ2, zOf_perm, zOf_perm, mul_one]
  have hUvec : ∀ i, U.vec i = ind α i + ind β i := fun i => by
    rw [hU, AE.Wr.mul_vec]
    have : (Z1.perm).symm i = i := by rw [hZ1, zOf_perm]; rfl
    rw [this, hZ1, hZ2, zOf_vec_apply, zOf_vec_apply]
    have r1 : ∀ i, i ∈ Set.range (emb α hα) ↔ i ∈ α := fun i => by
      rw [range_emb]; exact Finset.mem_coe
    have r2 : ∀ i, i ∈ Set.range (emb β hβ) ↔ i ∈ β := fun i => by
      rw [range_emb]; exact Finset.mem_coe
    simp only [r1, r2, ind]
  obtain ⟨γ, hγ𝒜, hγ, hconst, σ, hPσ, hσ⟩ := hcomb α hα𝒜 β hβ𝒜
  obtain ⟨x, hψx⟩ := hlift σ hPσ
  have hxperm : ∀ y, y ∈ γ ↔ (AE.Wr.ofPerm σ).perm.symm y ∈ α := hσ
  have hzx : ψ (x * z * x⁻¹) = AE.zBar γ hγ := by
    rw [map_mul, map_mul, map_inv, hψx, hψz]
    exact zBar_conj_set (AE.Wr.ofPerm σ) α γ hα hγ hxperm
  have hKx : conjSub x K ∈ Δ := hconj x K hK
  have hK''x : conjSub x K'' ∈ Δ := hconj x K'' hK''
  obtain ⟨δ₁, hδ₁𝒜, hδ₁, b₁, hl₁⟩ := hlab _ hKx
  obtain ⟨δ₂, hδ₂𝒜, hδ₂, b₂, hl₂⟩ := hlab _ hK''x
  have e₁ : AE.zBar δ₁ hδ₁ = AE.zBar γ hγ :=
    (zimg _ hKx δ₁ hδ₁ b₁ hl₁ _ (hz.conj x)).symm.trans hzx
  have e₂ : AE.zBar δ₂ hδ₂ = AE.zBar γ hγ :=
    (zimg _ hK''x δ₂ hδ₂ b₂ hl₂ _ (hzK''.conj x)).symm.trans hzx
  have hcomm_img : ∀ (L : Subgroup Y) (δ : Finset (Fin n)) (hδ : δ.card = 4) (b : Bool),
      (∃ c : ZMod 2, ∀ i ∈ δ, ind α i + ind β i = c) → L.map ψ = AE.memBar δ hδ b →
      ∀ w ∈ L, ψ (z * t) * ψ w = ψ w * ψ (z * t) := by
    intro L δ hδ b hcδ hl w hw
    obtain ⟨c, hc⟩ := hcδ
    have hw' : ψ w ∈ AE.memBar δ hδ b := by
      rw [← hl]; exact Subgroup.mem_map_of_mem _ hw
    obtain ⟨e, he, hew⟩ := hw'
    have hek : ∃ k : AE.Wr 4, e = embed (emb δ hδ) k := by
      cases b
      · obtain ⟨k, -, rfl⟩ := he
        exact ⟨k, rfl⟩
      · obtain ⟨k, -, rfl⟩ := he
        exact ⟨k, rfl⟩
    obtain ⟨k, rfl⟩ := hek
    have hUc : ∀ i ∈ Set.range (emb δ hδ), ∀ j ∈ Set.range (emb δ hδ), U.vec i = U.vec j := by
      intro i hi j hj
      rw [range_emb] at hi hj
      rw [hUvec, hUvec, hc i (by exact_mod_cast hi), hc j (by exact_mod_cast hj)]
    rw [hψzt, ← hew, ← map_mul, ← map_mul, comm_vec_embed U hU1 _ hUc k]
  have hc1 : ∀ w ∈ conjSub x K, (z * t) * w = w * (z * t) :=
    centralizes_of_image ψ hconj hinj hinjOn hKx
      (hcomm_img _ δ₁ hδ₁ b₁ (hconst δ₁ hδ₁𝒜 hδ₁ e₁) hl₁)
  have hc2 : ∀ w ∈ conjSub x K'', (z * t) * w = w * (z * t) :=
    centralizes_of_image ψ hconj hinj hinjOn hK''x
      (hcomm_img _ δ₂ hδ₂ b₂ (hconst δ₂ hδ₂𝒜 hδ₂ e₂) hl₂)
  have hne' : conjSub x K'' ≠ conjSub x K := by
    intro h
    apply hne
    have := congrArg (conjSub x⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have htw : conjSub x K'' ∈ twinSet Δ (conjSub x K) :=
    ⟨hK''x, x * z * x⁻¹, hz.conj x, hzK''.conj x⟩
  refine ⟨x, conjSub x K'', htw, hne', conjSub x K, conjSub x K'', hsyl _ hKx, hsyl _ hK''x, ?_, ?_⟩
  · intro a ha b hb
    have hco := Sec6Gen.comm_le_oddCore_of_twin hΩ hKx hK''x (Ne.symm hne') (hz.conj x)
      (hzK''.conj x)
    have h0 : ⁅a, b⁆ ∈ oddCoreOf (conjSub x K) ⊓ oddCoreOf (conjSub x K'') :=
      hco (Subgroup.commutator_mem_commutator ha hb)
    have hb0 : ⁅a, b⁆ = 1 :=
      TwinExitPf12.eq_one_of_odd_orderOf_of_pGroup (htwo _ hKx) (oddCoreOf_le_self _ h0.1)
        (TwinExitPf12.odd_orderOf_of_mem_odd (odd_natCard_oddCoreOf _) h0.1)
    rw [commutatorElement_def] at hb0
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hb0, one_mul]
  · intro w hw
    have hle : conjSub x K ⊔ conjSub x K'' ≤ Subgroup.centralizer ({z * t} : Set Y) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hc1 w hw).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hc2 w hw).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)

open AeM CFSG.ClassicalInvolution.Q3.AE in
theorem e189_ae_core {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (hΩ : HypOmegaGen Δ) (htwo : ∀ L ∈ Δ, IsPGroup 2 L) {n : ℕ} (hn8 : n ≠ 8)
    (ψ : Y →* AE.AEQ n) (𝒜 : Set (Finset (Fin n))) (P : Equiv.Perm (Fin n) → Prop)
    (hlab : ∀ L ∈ Δ, ∃ α ∈ 𝒜, ∃ h : α.card = 4, ∃ b : Bool, L.map ψ = AE.memBar α h b)
    (hinj : ∀ L ∈ Δ, ∀ M ∈ Δ, L.map ψ = M.map ψ → L = M)
    (hinjOn : ∀ M ∈ Δ, Set.InjOn ψ (M : Set Y))
    (zimg : ∀ L ∈ Δ, ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      L.map ψ = AE.memBar α h b → ∀ u : Y, IsUniqueInvolution L u → ψ u = AE.zBar α h)
    (hlift : ∀ σ : Equiv.Perm (Fin n), P σ → ∃ x : Y, ψ x = AE.mkQ n (AE.Wr.ofPerm σ))
    (hcomb : ∀ α ∈ 𝒜, ∀ β ∈ 𝒜, ∃ γ ∈ 𝒜, ∃ (_ : γ.card = 4) (c : ZMod 2),
      (∀ i ∈ γ, ind α i + ind β i = c) ∧ ∃ σ : Equiv.Perm (Fin n), P σ ∧ ∀ y, y ∈ γ ↔ σ.symm y ∈ α)
    {K J : Subgroup Y} (hK : K ∈ Δ) (hJ : J ∈ Δ) {z t : Y} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    ∃ x : Y, ∃ M' ∈ twinSet Δ (conjSub x K), M' ≠ conjSub x K ∧ ∃ R₁ R₂ : Subgroup Y,
      IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  refine e189_ae_core' hΩ htwo ψ 𝒜 P hlab hinj hinjOn zimg hlift ?_ hK hJ hz ht hzt hne
  intro α hα β hβ
  obtain ⟨γ, hγ𝒜, hγ, c, hc, σ, hP, hσ⟩ := hcomb α hα β hβ
  refine ⟨γ, hγ𝒜, hγ, fun δ _ hδ he => ?_, σ, hP, hσ⟩
  have := AE.eq_of_zBar_eq hn8 he
  subst this
  exact ⟨c, hc⟩

end Main

section Inst


open AeM CFSG.ClassicalInvolution.Q3.AE in
theorem sum_ind {n : ℕ} (s : Finset (Fin n)) : ∑ i, ind s i = (s.card : ZMod 2) := by
  classical
  unfold ind
  rw [Finset.sum_ite_mem Finset.univ s (fun _ => (1 : ZMod 2))]
  simp

open AeM CFSG.ClassicalInvolution.Q3.AE in
theorem e189_aeM_alt2 {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (F : TwinDisc.ExitO2.Q8Fam Y Δ) {m : ℕ} (hm : 6 ≤ m) (hm8 : m ≠ 8) (I : AEIdent Δ m)
    {K J : Subgroup Y} (hK : K ∈ Δ) (hJ : J ∈ Δ) {z t : Y} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z * t = t * z) (hne : conjSub t K ≠ K) :
    ∃ x : Y, ∃ M' ∈ twinSet Δ (conjSub x K), M' ≠ conjSub x K ∧ ∃ R₁ R₂ : Subgroup Y,
      IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  have hΩ := F.hyp
  have hm5 : 5 ≤ m := by omega
  have hX : ∀ y : Y, y ∈ pSpan Δ := fun y => F.gen ▸ Subgroup.mem_top y
  let ψ : Y →* AE.AEQ m :=
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
  refine e189_ae_core hΩ F.two hm8 ψ {α | α.card = 4} (fun σ => Equiv.Perm.sign σ = 1) ?_ ?_ ?_ ?_ ?_ ?_
    hK hJ hz ht hzt hne
  · intro L hL
    obtain ⟨α, h, b, hl⟩ := I.label L hL
    exact ⟨α, h, h, b, by rw [map_psi]; exact hl⟩
  · intro L hL M hM hLM
    obtain ⟨a, haL, ha2⟩ := F.exists_mul_self_ne_one L hL
    refine TwinDisc.ExitO2.fam_eq_of_phi_mem I.φ F hm5 I.ker_le I.label hL hM haL ha2 ?_
    have := I.mem_map hL haL
    rw [← map_psi, hLM, map_psi] at this
    exact this
  · intro M hM l₁ hl₁ l₂ hl₂ he
    obtain ⟨α, h, b, hl⟩ := I.label M hM
    exact I.injOn hm5 hM ((F.card M hM).trans (by norm_num)) hl hl₁ hl₂ he
  · intro L hL α h b hl u hu
    have h8 : Nat.card ↥L = 8 := (F.card L hL).trans (by norm_num)
    exact I.map_eq_zBar hm5 hL h8 (by rw [← map_psi]; exact hl) hu
  · intro σ hσ
    have hxr : AE.mkQ m (AE.Wr.ofPerm σ) ∈ I.φ.range := by
      rw [I.range_eq]
      exact Subgroup.mem_map_of_mem _ (ofPerm_mem_aeSub hσ)
    obtain ⟨x', hx'⟩ := hxr
    exact ⟨(x' : Y), hx'⟩
  · intro α hα β hβ
    have hsum : ∑ i, (ind α i + ind β i) = 0 := by
      rw [Finset.sum_add_distrib, sum_ind, sum_ind]
      have h1 : α.card = 4 := hα
      have h2 : β.card = 4 := hβ
      rw [h1, h2]
      decide
    obtain ⟨γ, hγ, c, hc⟩ := exists_const_four_set hm (fun i => ind α i + ind β i) hsum
    obtain ⟨σ, hs, hσ⟩ := exists_even_perm_map α γ (by rw [(hα : α.card = 4), hγ]) (by
      rw [(hα : α.card = 4)]; omega)
    exact ⟨γ, hγ, hγ, c, hc, σ, hs, hσ⟩

end Inst

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
