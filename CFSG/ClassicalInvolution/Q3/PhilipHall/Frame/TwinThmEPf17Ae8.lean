module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf16AeM

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open scoped commutatorElement

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin

namespace Ae8

open CFSG.ClassicalInvolution.Q3.AE

theorem exists_even_perm_comp {n : ℕ} (hn : 6 ≤ n) (ι κ : Fin 4 ↪ Fin n) :
    ∃ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = 1 ∧ ∀ i, σ (ι i) = κ i := by
  classical
  let e : {x // x ∈ Set.range ι} ≃ {x // x ∈ Set.range κ} :=
    ι.toEquivRange.symm.trans κ.toEquivRange
  set σ₀ : Equiv.Perm (Fin n) := e.extendSubtype with hσ₀
  have hσ₀ι : ∀ i, σ₀ (ι i) = κ i := by
    intro i
    rw [hσ₀, Equiv.extendSubtype_apply_of_mem e _ (Set.mem_range_self i)]
    simp [e, toEquivRange_symm_apply, toEquivRange_apply]
  by_cases hs : Equiv.Perm.sign σ₀ = 1
  · exact ⟨σ₀, hs, hσ₀ι⟩
  ·
    have hcard : (Finset.univ.map ι).card = 4 := by simp
    have hout : 2 ≤ ((Finset.univ.map ι)ᶜ : Finset (Fin n)).card := by
      rw [Finset.card_compl, Fintype.card_fin, hcard]; omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((Finset.univ.map ι)ᶜ).card)
    refine ⟨σ₀ * Equiv.swap a b, ?_, fun i => ?_⟩
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
      have : Equiv.Perm.sign σ₀ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ₀) with h | h
        · exact absurd h hs
        · exact h
      rw [this]; decide
    · have hai : ι i ≠ a := fun h => by
        have : a ∈ Finset.univ.map ι := h ▸ Finset.mem_map_of_mem ι (Finset.mem_univ i)
        exact (Finset.mem_compl.mp ha) this
      have hbi : ι i ≠ b := fun h => by
        have : b ∈ Finset.univ.map ι := h ▸ Finset.mem_map_of_mem ι (Finset.mem_univ i)
        exact (Finset.mem_compl.mp hb) this
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hai hbi, hσ₀ι]

theorem conj_embed_comp {n : ℕ} {ι κ : Fin 4 ↪ Fin n} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i, σ (ι i) = κ i) (a : AE.Wr 4) :
    AE.Wr.ofPerm σ * embed ι a * (AE.Wr.ofPerm σ)⁻¹ = embed κ a := by
  classical
  have hsymm : ∀ i, σ.symm (κ i) = ι i := fun i => by
    rw [Equiv.symm_apply_eq, hσ]
  have hout : ∀ x, x ∉ Set.range κ → σ.symm x ∉ Set.range ι := by
    rintro x hx ⟨i, hi⟩
    apply hx
    exact ⟨i, by rw [← hσ, hi, Equiv.apply_symm_apply]⟩
  refine AE.Wr.ext (funext fun x => ?_) ?_
  · rw [ofPerm_conj_vec, embed_vec, embed_vec]
    by_cases hx : x ∈ Set.range κ
    · obtain ⟨i, rfl⟩ := hx
      rw [hsymm, embedVec_apply, embedVec_apply]
    · rw [embedVec_of_not_mem κ _ hx, embedVec_of_not_mem ι _ (hout x hx)]
  · show σ * embedPerm ι a.perm * σ⁻¹ = embedPerm κ a.perm
    refine Equiv.ext fun y => ?_
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    by_cases hy : y ∈ Set.range κ
    · obtain ⟨i, rfl⟩ := hy
      rw [hsymm, embedPerm_apply, hσ, embedPerm_apply]
    · rw [embedPerm_of_not_mem κ _ hy, embedPerm_of_not_mem ι _ (hout y hy)]
      exact Equiv.apply_symm_apply σ y

theorem conj_memAt_comp {n : ℕ} {α γ : Finset (Fin n)} {hα : α.card = 4} {hγ : γ.card = 4}
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ i, σ (emb α hα i) = emb γ hγ i) (b : Bool) :
    (∀ e ∈ memAt α hα b, AE.Wr.ofPerm σ * e * (AE.Wr.ofPerm σ)⁻¹ ∈ memAt γ hγ b) ∧
    (∀ f ∈ memAt γ hγ b, ∃ e ∈ memAt α hα b, AE.Wr.ofPerm σ * e * (AE.Wr.ofPerm σ)⁻¹ = f) := by
  have key : ∀ k : AE.Wr 4,
      AE.Wr.ofPerm σ * embed (emb α hα) k * (AE.Wr.ofPerm σ)⁻¹ = embed (emb γ hγ) k :=
    fun k => conj_embed_comp hσ k
  cases b
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨k, hk, (key k).symm⟩
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨embed (emb α hα) k, ⟨k, hk, rfl⟩, key k⟩
  · refine ⟨?_, ?_⟩
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨k, hk, (key k).symm⟩
    · rintro _ ⟨k, hk, rfl⟩
      exact ⟨embed (emb α hα) k, ⟨k, hk, rfl⟩, key k⟩

theorem conj_label_perm {Y : Type} [Group Y] {n : ℕ} (ψ : Y →* AE.AEQ n) {L : Subgroup Y}
    {α γ : Finset (Fin n)} {hα : α.card = 4} {hγ : γ.card = 4} {b : Bool}
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ i, σ (emb α hα i) = emb γ hγ i) {x : Y}
    (hx : ψ x = AE.mkQ n (AE.Wr.ofPerm σ)) (hL : L.map ψ = AE.memBar α hα b) :
    (conjSub x L).map ψ = AE.memBar γ hγ b := by
  obtain ⟨h1, h2⟩ := conj_memAt_comp hσ b
  have hconj : ∀ e : AE.Wr n, ψ x * AE.mkQ n e * (ψ x)⁻¹ =
      AE.mkQ n (AE.Wr.ofPerm σ * e * (AE.Wr.ofPerm σ)⁻¹) := fun e => by
    rw [hx, map_mul, map_mul, map_inv]
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' := mem_conjSub_iff.mp hw
    have hψw : ψ (x⁻¹ * w * x) ∈ AE.memBar α hα b := by
      rw [← hL]; exact Subgroup.mem_map_of_mem _ (by simpa using hw')
    obtain ⟨e, he, hew⟩ := hψw
    refine ⟨AE.Wr.ofPerm σ * e * (AE.Wr.ofPerm σ)⁻¹, h1 e he, ?_⟩
    have hw2 : ψ w = ψ x * ψ (x⁻¹ * w * x) * (ψ x)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    rw [← hconj, hew, ← hw2]
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨e, he, hef⟩ := h2 f hf
    have : AE.mkQ n e ∈ L.map ψ := by rw [hL]; exact Subgroup.mem_map_of_mem _ he
    obtain ⟨l, hl, hle⟩ := this
    refine ⟨x * l * x⁻¹, mem_conjSub_iff.mpr (by simpa [mul_assoc] using hl), ?_⟩
    rw [map_mul, map_mul, map_inv, hle, hconj, hef]

theorem exists_moves_all_kList : ∃ k ∈ kList, ∀ i : Fin 4, k.perm i ≠ i := by decide +kernel

theorem exists_moves_all_kStarList : ∃ k ∈ kStarList, ∀ i : Fin 4, k.perm i ≠ i := by decide +kernel

theorem exists_moves_all {n : ℕ} (α : Finset (Fin n)) (hα : α.card = 4) (b : Bool) :
    ∃ e ∈ memAt α hα b, ∀ x ∈ α, e.perm x ≠ x := by
  have hr : ∀ x ∈ α, ∃ i, emb α hα i = x := fun x hx => by
    have : x ∈ Set.range (emb α hα) := by rw [range_emb]; exact_mod_cast hx
    exact this
  cases b
  · obtain ⟨k, hk, hmv⟩ := exists_moves_all_kStarList
    refine ⟨embed (emb α hα) k, ⟨k, hk, rfl⟩, fun x hx => ?_⟩
    obtain ⟨i, rfl⟩ := hr x hx
    rw [embed_perm, embedPerm_apply]
    exact fun h => hmv i ((emb α hα).injective h)
  · obtain ⟨k, hk, hmv⟩ := exists_moves_all_kList
    refine ⟨embed (emb α hα) k, ⟨k, hk, rfl⟩, fun x hx => ?_⟩
    obtain ⟨i, rfl⟩ := hr x hx
    rw [embed_perm, embedPerm_apply]
    exact fun h => hmv i ((emb α hα).injective h)

theorem label_eq_of_vec_conj {Y : Type} [Group Y] {n : ℕ} (ψ : Y →* AE.AEQ n) {L : Subgroup Y}
    {α δ : Finset (Fin n)} {hα : α.card = 4} {hδ : δ.card = 4} {b b' : Bool} {y : Y}
    (hL : L.map ψ = AE.memBar α hα b) (hL' : (conjSub y L).map ψ = AE.memBar δ hδ b')
    {U : AE.Wr n} (hU1 : U.perm = 1) (hy : ψ y = AE.mkQ n U) : δ = α := by
  obtain ⟨e, he, hmv⟩ := exists_moves_all α hα b
  have h1 : AE.mkQ n e ∈ L.map ψ := by rw [hL]; exact Subgroup.mem_map_of_mem _ he
  obtain ⟨l, hl, hle⟩ := h1
  have h2 : AE.mkQ n (U * e * U⁻¹) ∈ AE.memBar δ hδ b' := by
    rw [← hL']
    refine ⟨y * l * y⁻¹, mem_conjSub_iff.mpr (by simpa [mul_assoc] using hl), ?_⟩
    rw [map_mul, map_mul, map_inv, hy, hle, map_mul, map_mul, map_inv]
  obtain ⟨f, hf, hfe⟩ := h2
  have hperm : f.perm = e.perm := by
    rcases AE.mkQ_eq_iff.mp hfe with h | h
    · have := congrArg AE.Wr.perm h
      rw [AE.Wr.mul_perm, AE.Wr.inv_perm, AE.Wr.mul_perm, AE.Wr.mul_perm, AE.Wr.inv_perm, hU1] at this
      simp only [inv_one, one_mul, mul_one] at this
      have h3 : f.perm⁻¹ * e.perm = 1 := this
      exact inv_mul_eq_one.mp h3
    · have := congrArg AE.Wr.perm h
      rw [AE.Wr.mul_perm, AE.Wr.inv_perm, AE.Wr.mul_perm, AE.Wr.mul_perm, AE.Wr.inv_perm, hU1] at this
      simp only [inv_one, one_mul, mul_one] at this
      have h3 : f.perm⁻¹ * e.perm = 1 := this
      exact inv_mul_eq_one.mp h3
  have hsupp := supportedOn_of_mem_memAt hf
  have hsub : α ⊆ δ := by
    intro x hx
    by_contra hxδ
    have hxr : x ∉ Set.range (emb δ hδ) := by
      rw [range_emb]; exact_mod_cast hxδ
    exact hmv x hx (by rw [← hperm]; exact (hsupp x hxr).2)
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hα, hδ])).symm

end Ae8

section Exact


open AeM CFSG.ClassicalInvolution.Q3.AE in
theorem e189_ae_exact {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (hΩ : HypOmegaGen Δ) (htwo : ∀ L ∈ Δ, IsPGroup 2 L) {n : ℕ} (hn6 : 6 ≤ n)
    (ψ : Y →* AE.AEQ n)
    (hlab : ∀ L ∈ Δ, ∃ α : Finset (Fin n), ∃ h : α.card = 4, ∃ b : Bool, L.map ψ = AE.memBar α h b)
    (hinj : ∀ L ∈ Δ, ∀ M ∈ Δ, L.map ψ = M.map ψ → L = M)
    (hinjOn : ∀ M ∈ Δ, Set.InjOn ψ (M : Set Y))
    (zimg : ∀ L ∈ Δ, ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      L.map ψ = AE.memBar α h b → ∀ u : Y, IsUniqueInvolution L u → ψ u = AE.zBar α h)
    (hlift : ∀ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = 1 →
      ∃ x : Y, ψ x = AE.mkQ n (AE.Wr.ofPerm σ))
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
  obtain ⟨α, hα, bK, hKl⟩ := hlab K hK
  obtain ⟨β, hβ, bJ, hJl⟩ := hlab J hJ
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
  have hsum : ∑ i, (ind α i + ind β i) = 0 := by
    rw [Finset.sum_add_distrib, sum_ind, sum_ind, hα, hβ]
    decide
  obtain ⟨γ, hγ, c, hc⟩ := exists_const_four_set hn6 (fun i => ind α i + ind β i) hsum
  obtain ⟨σ, hsign, hσ⟩ := Ae8.exists_even_perm_comp hn6 (emb α hα) (emb γ hγ)
  obtain ⟨x, hψx⟩ := hlift σ hsign
  obtain ⟨δ, hδ, b'', hl''⟩ := hlab K'' hK''
  have hδα : δ = α :=
    Ae8.label_eq_of_vec_conj ψ hKl hl'' (U := Z2) (by rw [hZ2, zOf_perm]) (by rw [hψt]; rfl)
  subst hδα
  have hKx : conjSub x K ∈ Δ := hconj x K hK
  have hK''x : conjSub x K'' ∈ Δ := hconj x K'' hK''
  have hl₁' : (conjSub x K).map ψ = AE.memBar γ hγ bK := Ae8.conj_label_perm ψ hσ hψx hKl
  have hl₂' : (conjSub x K'').map ψ = AE.memBar γ hγ b'' := Ae8.conj_label_perm ψ hσ hψx hl''
  have hcomm_img : ∀ (L : Subgroup Y) (b : Bool), L.map ψ = AE.memBar γ hγ b →
      ∀ w ∈ L, ψ (z * t) * ψ w = ψ w * ψ (z * t) := by
    intro L b hl w hw
    have hw' : ψ w ∈ AE.memBar γ hγ b := by
      rw [← hl]; exact Subgroup.mem_map_of_mem _ hw
    obtain ⟨e, he, hew⟩ := hw'
    have hek : ∃ k : AE.Wr 4, e = embed (emb γ hγ) k := by
      cases b
      · obtain ⟨k, -, rfl⟩ := he
        exact ⟨k, rfl⟩
      · obtain ⟨k, -, rfl⟩ := he
        exact ⟨k, rfl⟩
    obtain ⟨k, rfl⟩ := hek
    have hUc : ∀ i ∈ Set.range (emb γ hγ), ∀ j ∈ Set.range (emb γ hγ), U.vec i = U.vec j := by
      intro i hi j hj
      rw [range_emb] at hi hj
      rw [hUvec, hUvec, hc i (by exact_mod_cast hi), hc j (by exact_mod_cast hj)]
    rw [hψzt, ← hew, ← map_mul, ← map_mul, comm_vec_embed U hU1 _ hUc k]
  have hc1 : ∀ w ∈ conjSub x K, (z * t) * w = w * (z * t) :=
    centralizes_of_image ψ hconj hinj hinjOn hKx (hcomm_img _ bK hl₁')
  have hc2 : ∀ w ∈ conjSub x K'', (z * t) * w = w * (z * t) :=
    centralizes_of_image ψ hconj hinj hinjOn hK''x (hcomm_img _ b'' hl₂')
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


end Exact

section Inst8


theorem e189_aeM_alt2_all {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}
    (F : TwinDisc.ExitO2.Q8Fam Y Δ) {m : ℕ} (hm : 6 ≤ m) (I : AEIdent Δ m)
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
  refine e189_ae_exact hΩ F.two hm ψ ?_ ?_ ?_ ?_ ?_ hK hJ hz ht hzt hne
  · intro L hL
    obtain ⟨α, h, b, hl⟩ := I.label L hL
    exact ⟨α, h, b, by rw [map_psi]; exact hl⟩
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
      exact Subgroup.mem_map_of_mem _ (AeM.ofPerm_mem_aeSub hσ)
    obtain ⟨x', hx'⟩ := hxr
    exact ⟨(x' : Y), hx'⟩

end Inst8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
