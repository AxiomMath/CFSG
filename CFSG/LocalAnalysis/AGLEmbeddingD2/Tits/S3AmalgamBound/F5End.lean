module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Frattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Count
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowProduct
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GuestConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Lift

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {V M : Subgroup G} {hU : IsElemAbelian 2 V}

omit [Finite G] in
theorem card_le_of_le_sup_centralizer (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M)) {K Q : Subgroup G}
    (hKM : K ≤ M) (hQ : Q ≤ Subgroup.centralizer (V : Set G) ⊓ M ⊔ K) (hQp : IsPGroup 3 Q)
    {b : ℕ} (hb : ∀ Q' : Subgroup (MulAut (IntMod V hU)), Q' ≤ autI hU K → IsPGroup 3 Q' →
      Nat.card Q' ≤ b) : Nat.card Q ≤ b := by
  set CM : Subgroup G := Subgroup.centralizer (V : Set G) ⊓ M with hCM
  have hCMn : M ≤ Subgroup.normalizer (CM : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).1
      (centralizer_inf_subgroupOf_normal hU hMN)
  have hQM : Q ≤ M := hQ.trans (sup_le inf_le_right hKM)
  set φ : ↥Q →* MulAut (IntMod V hU) := (actM hU hMN).comp (Subgroup.inclusion hQM) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hcent : (q : G) ∈ Subgroup.centralizer (V : Set G) :=
      (actM_eq_one_iff hU hMN ⟨q, hQM q.2⟩).1 hq
    have hmem : (q : G) ∈ CM := ⟨hcent, hQM q.2⟩
    obtain ⟨k, hk⟩ := hQp q
    have hsk : (q : G) ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hord : orderOf (q : G) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hsk
    have hord2 : orderOf (q : G) ∣ Nat.card CM := Subgroup.orderOf_dvd_natCard _ hmem
    have hcop : Nat.Coprime (3 ^ k) (Nat.card CM) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC3)
    have h1 : orderOf (q : G) = 1 := (hcop.of_dvd_left hord).eq_one_of_dvd hord2
    exact Subtype.ext (orderOf_eq_one_iff.1 h1)
  have hrange : ∀ q : ↥Q, φ q ∈ autI hU K := by
    intro q
    have hq := hQ q.2
    rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K CM
      (hKM.trans hCMn), Set.mem_mul] at hq
    obtain ⟨k, hk, c, hc, hkc⟩ := hq
    have hc1 : actM hU hMN ⟨c, hc.2⟩ = 1 := (actM_eq_one_iff hU hMN _).2 hc.1
    have : φ q = actM hU hMN ⟨k, hKM hk⟩ := by
      have e : (⟨(q : G), hQM q.2⟩ : ↥M) = ⟨k, hKM hk⟩ * ⟨c, hc.2⟩ := Subtype.ext hkc.symm
      show actM hU hMN ⟨(q : G), hQM q.2⟩ = _
      rw [e, map_mul, hc1, mul_one]
    rw [this, actM_eq_convI]
    exact convI_mem_autI hU hk _
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hRp : IsPGroup 3 φ.range := hQp.of_surjective φ.rangeRestrict hsurj
  have hRK : φ.range ≤ autI hU K := by
    rintro _ ⟨q, rfl⟩; exact hrange q
  have hcard : Nat.card Q = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hcard]
  exact hb _ hRK hRp

@[expose] def FFPairData (M T : Subgroup G) (hU : IsElemAbelian 2 V)
    (I : Finset (Subgroup (MulAut (IntMod V hU)))) (C₁ C₂ : Subgroup G) : Prop :=
  C₁ ≠ ⊥ ∧ IsPGroup 2 C₁ ∧ C₂ ≠ ⊥ ∧ IsPGroup 2 C₂ ∧
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₁ : Set G) ∧
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₂ : Set G) ∧
    Subgroup.centralizer (V : Set G) ⊓ M ≤ Subgroup.normalizer (C₁ : Set G) ∧
    M ⊓ Subgroup.normalizer (baum T : Set G) ≤ Subgroup.normalizer (C₂ : Set G) ∧
    ∀ L ∈ I, ∃ H : Subgroup G, H ≤ M ∧ L ≤ autI hU H ∧
      (∀ Q : Subgroup (MulAut (IntMod V hU)), Q ≤ autI hU H → IsPGroup 3 Q → Nat.card Q ≤ 3) ∧
      (H ≤ Subgroup.normalizer (C₁ : Set G) ∨ H ≤ Subgroup.normalizer (C₂ : Set G))


theorem false_of_pair_data {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K₀) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hSylJ : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)))
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M)) {C₁ C₂ : Subgroup G}
    (hdat : FFPairData M T hU I C₁ C₂) : False := by
  obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, hCM₁, hJ₂, hH⟩ := hdat
  have hN₁ : ¬ Subgroup.normalizer (C₁ : Set G) ≤ M := fun h => hNT (hT₁.trans h)
  have hN₂ : ¬ Subgroup.normalizer (C₂ : Set G) ≤ M := fun h => hNT (hT₂.trans h)
  choose! Hf hHM hHL hH3 hHcase using hH
  set KA : Subgroup G := ⨆ L ∈ I, ⨆ (_ : Hf L ≤ Subgroup.normalizer (C₁ : Set G)), Hf L with hKA
  set KB : Subgroup G := ⨆ L ∈ I, ⨆ (_ : ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G)), Hf L
    with hKB
  have hKAM : KA ≤ M := iSup₂_le fun L hL => iSup_le fun _ => hHM L hL
  have hKBM : KB ≤ M := iSup₂_le fun L hL => iSup_le fun _ => hHM L hL
  have hKAN : KA ≤ Subgroup.normalizer (C₁ : Set G) := iSup₂_le fun L hL => iSup_le fun h => h
  have hKBN : KB ≤ Subgroup.normalizer (C₂ : Set G) :=
    iSup₂_le fun L hL => iSup_le fun h => (hHcase L hL).resolve_left h
  have hcov : ∀ L ∈ I, L ≤ autI hU KA ∨ L ≤ autI hU KB := by
    intro L hL
    by_cases h : Hf L ≤ Subgroup.normalizer (C₁ : Set G)
    · exact Or.inl ((hHL L hL).trans (autI_mono hU
        (le_iSup₂_of_le L hL (le_iSup (fun _ : Hf L ≤ Subgroup.normalizer (C₁ : Set G) => Hf L) h))))
    · exact Or.inr ((hHL L hL).trans (autI_mono hU
        (le_iSup₂_of_le L hL (le_iSup (fun _ : ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G) => Hf L) h))))
  have hAuniq : ∀ L₁ ∈ I, ∀ L₂ ∈ I, Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) →
      Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) → L₁ = L₂ := by
    intro L₁ h₁ L₂ h₂ hH₁ hH₂
    by_contra hne
    exact false_of_two_factors_in_normalizer hc hstr hOnly hMN hC₁1 hC₁2 hN₁ hKAM hKAN hC3 hI hcard
      h₁ h₂ hne ((hHL L₁ h₁).trans (autI_mono hU (le_iSup₂_of_le L₁ h₁
        (le_iSup (fun _ : Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) => Hf L₁) hH₁))))
      ((hHL L₂ h₂).trans (autI_mono hU (le_iSup₂_of_le L₂ h₂
        (le_iSup (fun _ : Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) => Hf L₂) hH₂))))
  have hBuniq : ∀ L₁ ∈ I, ∀ L₂ ∈ I, ¬ Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) →
      ¬ Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) → L₁ = L₂ := by
    intro L₁ h₁ L₂ h₂ hH₁ hH₂
    by_contra hne
    exact false_of_two_factors_in_normalizer hc hstr hOnly hMN hC₂1 hC₂2 hN₂ hKBM hKBN hC3 hI hcard
      h₁ h₂ hne ((hHL L₁ h₁).trans (autI_mono hU (le_iSup₂_of_le L₁ h₁
        (le_iSup (fun _ : ¬ Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) => Hf L₁) hH₁))))
      ((hHL L₂ h₂).trans (autI_mono hU (le_iSup₂_of_le L₂ h₂
        (le_iSup (fun _ : ¬ Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) => Hf L₂) hH₂))))
  have hbA : ∀ Q' : Subgroup (MulAut (IntMod V hU)), Q' ≤ autI hU KA → IsPGroup 3 Q' →
      Nat.card Q' ≤ 3 := by
    intro Q' hQ' hQ'p
    by_cases hex : ∃ L₀ ∈ I, Hf L₀ ≤ Subgroup.normalizer (C₁ : Set G)
    · obtain ⟨L₀, hL₀, hH₀⟩ := hex
      have hKAeq : KA ≤ Hf L₀ := iSup₂_le fun L hL => iSup_le fun h => by
        rw [hAuniq L hL L₀ hL₀ h hH₀]
      exact hH3 L₀ hL₀ Q' (hQ'.trans (autI_mono hU hKAeq)) hQ'p
    · push Not at hex
      have hKAbot : KA = ⊥ := by
        refine le_bot_iff.1 (iSup₂_le fun L hL => iSup_le fun h => absurd h (hex L hL))
      have hQ'bot : Q' = ⊥ := by
        refine le_bot_iff.1 (fun φ hφ => ?_)
        obtain ⟨g, hg, rfl⟩ := (mem_autI hU).1 (hQ' hφ)
        rw [hKAbot, Subgroup.mem_bot] at hg
        have : g = 1 := Subtype.ext hg
        rw [this, map_one]
        exact Subgroup.one_mem _
      rw [hQ'bot, Subgroup.card_bot]; norm_num
  set CM : Subgroup G := Subgroup.centralizer (V : Set G) ⊓ M with hCM
  set 𝒜 : Subgroup G := CM ⊔ KA with h𝒜
  set ℬ : Subgroup G := KB ⊔ (M ⊓ Subgroup.normalizer (baum T : Set G)) with hℬ
  have h𝒜M : 𝒜 ≤ M := sup_le inf_le_right hKAM
  have hℬM : ℬ ≤ M := sup_le hKBM inf_le_left
  have hℬN : ℬ ≤ Subgroup.normalizer (C₂ : Set G) := sup_le hKBN hJ₂
  have hfac : ∀ m ∈ M, ∃ a ∈ 𝒜, ∃ b ∈ ℬ, m = a * b := by
    intro m hm
    obtain ⟨c, hc', a, ha, b, hb, n, hn, rfl⟩ := exists_factor_of_covering hMN hT (C1GN.baum_le T)
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T))
      (normalizer_inf_sup_le_normalizer_baum T _) hI hSylJ hJM
      hKAM hKBM hcov m hm
    exact ⟨c * a, Subgroup.mul_mem _ (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right ha),
      b * n, Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hn),
      by group⟩
  obtain ⟨W, hWM, hWp, hWidx, hWfac⟩ :=
    OrdinaryProofs.exists_sylow_eq_mul_of_mul (p := 3) h𝒜M hℬM hfac
  obtain ⟨E, hEW, hEel, hEc⟩ := exists_elemAbelian_le_sylow hWM hWp hWidx
    (hc.esc.four_le_pRank_M hc.beta)
  refine false_of_E81_small_factor (W := W) (E := E) (A' := W ⊓ 𝒜) (U := W ⊓ ℬ) hEW hEel hEc
    inf_le_left inf_le_left ?_ ?_ (fun w hw => ?_)
  · exact card_le_of_le_sup_centralizer hMN hC3 hKAM inf_le_right (hWp.to_le inf_le_left) hbA
  · intro hnc
    exact D2L34BetaConf.card_le_nine_of_not_isCyclic hc hstr
      (⟨C₂, hC₂1, hC₂2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₂ : Set G))) hN₂
      (inf_le_right.trans hℬN) (inf_le_right.trans hℬM) (hWp.to_le inf_le_left) hnc
  · obtain ⟨a, ha, b, hb, rfl⟩ := hWfac w hw
    exact ⟨a, ha, b, hb, rfl⟩

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
