module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27TwoEsc
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WRankTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WCycC

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

private theorem exists_sq_pow_eq_of_pow_three {Ω : Type*} [Monoid Ω] {q : Ω} {k : ℕ}
    (hq : q ^ 3 ^ k = 1) : ∃ m : ℕ, (q ^ 2) ^ m = q := by
  obtain ⟨m, hm⟩ := (Odd.pow (by decide : Odd 3) : Odd (3 ^ k))
  refine ⟨m + 1, ?_⟩
  rw [← pow_mul, show 2 * (m + 1) = 3 ^ k + 1 by omega, pow_succ, hq, one_mul]

private theorem sl2_cube_cases : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    a ^ 3 = 1 → a ≠ 1 → b ^ 3 = 1 → b = 1 ∨ b = a ∨ b = a * a := by
  decide

section Conj

variable {Ω : Type*} [CommGroup Ω]

private theorem conjAut_one' (K : Subgroup (MulAut Ω)) : B1.conjAut 1 K = K := by
  ext x
  simp [B1.mem_conjAut]

private theorem conjAut_mul' (a b : MulAut Ω) (K : Subgroup (MulAut Ω)) :
    B1.conjAut (a * b) K = B1.conjAut a (B1.conjAut b K) := by
  ext x
  simp only [B1.mem_conjAut, mul_inv_rev, mul_assoc]

private theorem commute_of_conjAut_eq {L : Subgroup (MulAut Ω)}
    (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) {q : MulAut Ω} {k : ℕ}
    (hq : q ^ 3 ^ k = 1) (hqL : B1.conjAut q L = L) {g : MulAut Ω} (hg : g ∈ L)
    (hg3 : g ^ 3 = 1) : q * g = g * q := by
  by_cases hg1 : g = 1
  · rw [hg1, mul_one, one_mul]
  have hx : q * g * q⁻¹ ∈ L := by
    rw [← hqL, B1.mem_conjAut]
    simpa [mul_assoc] using hg
  have hx3 : (q * g * q⁻¹) ^ 3 = 1 := conj_pow_three_eq_one q hg3
  have hga : e ⟨g, hg⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨g, hg⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using hg3), map_one]
  have hga1 : e ⟨g, hg⟩ ≠ 1 := fun h => hg1 (by
    have := e.injective (h.trans (map_one e).symm)
    simpa using congrArg Subtype.val this)
  have hxa : e ⟨q * g * q⁻¹, hx⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨q * g * q⁻¹, hx⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using hx3),
      map_one]
  rcases sl2_cube_cases _ _ hga hga1 hxa with h | h | h
  ·
    exfalso
    have h1 : q * g * q⁻¹ = 1 := by
      have := e.injective (h.trans (map_one e).symm)
      simpa using congrArg Subtype.val this
    apply hg1
    calc g = q⁻¹ * (q * g * q⁻¹) * q := by group
      _ = 1 := by rw [h1]; group
  · have h1 : q * g * q⁻¹ = g := by
      have := e.injective h
      simpa using congrArg Subtype.val this
    calc q * g = q * g * q⁻¹ * q := by group
      _ = g * q := by rw [h1]
  · have h1 : q * g * q⁻¹ = g * g := by
      have := e.injective (h.trans (map_mul e _ _).symm)
      simpa using congrArg Subtype.val this
    have e1 : q ^ 2 * g * (q ^ 2)⁻¹ = g := by
      calc q ^ 2 * g * (q ^ 2)⁻¹ = q * (q * g * q⁻¹) * q⁻¹ := by
            rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
        _ = q * (g * g) * q⁻¹ := by rw [h1]
        _ = (q * g * q⁻¹) * (q * g * q⁻¹) := by group
        _ = (g * g) * (g * g) := by rw [h1]
        _ = g ^ 3 * g := by rw [pow_three]; simp only [mul_assoc]
        _ = g := by rw [hg3, one_mul]
    have h2 : Commute (q ^ 2) g := by
      show q ^ 2 * g = g * q ^ 2
      calc q ^ 2 * g = q ^ 2 * g * (q ^ 2)⁻¹ * q ^ 2 := by group
        _ = g * q ^ 2 := by rw [e1]
    obtain ⟨m, hm⟩ := exists_sq_pow_eq_of_pow_three hq
    have h3 := h2.pow_left m
    rw [hm] at h3
    exact h3

end Conj

variable {G : Type} [Group G] [Finite G]

theorem center3_of_pairData27
    {V M : Subgroup G} {hU : IsElemAbelian 2 V}
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {T : Subgroup G}
    (c : D2L34R27 G d P M A H R Rbar K₀ T) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I) (hI0 : I.Nonempty)
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hSylJ : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)))
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L)
    (hperm : ∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M)) {C₁ C₂ : Subgroup G}
    (hdat : FFPairData M T hU I C₁ C₂) : Center3Conclusion M := by
  classical
  have ctx := c.ctx
  have := ctx.amb
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT := c.sylow
  have hNT := c.not_normalizer_le
  obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, -, hJ₂, hH⟩ := hdat
  have hN₂ : ¬ Subgroup.normalizer (C₂ : Set G) ≤ M := fun h => hNT (hT₂.trans h)
  have hYn : ∀ g ∈ autI hU M, ∀ φ ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))),
      g * φ * g⁻¹ ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))) := by
    intro g hg φ hφ
    rw [← hJM] at hφ ⊢
    exact autI_thompsonJ_normalized g hg φ hφ
  choose! Hf hHM hHL hH3 hHcase using hH
  have hside : ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup 2 X →
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X : Set G) →
      ∀ L₁ ∈ I, ∀ L₂ ∈ I, Hf L₁ ≤ Subgroup.normalizer (X : Set G) →
        Hf L₂ ≤ Subgroup.normalizer (X : Set G) → L₁ = L₂ := by
    intro X hX1 hX2 hXT L₁ h₁ L₂ h₂ hH₁ hH₂
    by_contra hne
    exact c.false_of_two_factors_in_normalizer hMN hX1 hX2 hXT
      (sup_le (hHM L₁ h₁) (hHM L₂ h₂)) (sup_le hH₁ hH₂) hC3 hI hcard h₁ h₂ hne
      ((hHL L₁ h₁).trans (autI_mono hU le_sup_left))
      ((hHL L₂ h₂).trans (autI_mono hU le_sup_right))
      (fun x₁ x₂ _ _ hcomm ho₁ ho₂ hx₁M hx₂M hL₁ hL₂ hn₁ hn₂ =>
        ctx.hasGoodE9_closure_pair hMN hI hcard hC3 hYn h₁ h₂ hne hx₁M hx₂M hcomm ho₁ ho₂ hL₁
          hL₂ hn₁ hn₂)
  have hAuniq := hside C₁ hC₁1 hC₁2 hT₁
  have hBuniq : ∀ L₁ ∈ I, ∀ L₂ ∈ I, ¬ Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) →
      ¬ Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) → L₁ = L₂ := fun L₁ h₁ L₂ h₂ hH₁ hH₂ =>
    hside C₂ hC₂1 hC₂2 hT₂ L₁ h₁ L₂ h₂ ((hHcase L₁ h₁).resolve_left hH₁)
      ((hHcase L₂ h₂).resolve_left hH₂)
  have huniq : ∀ L₁ ∈ I, ∀ L₂ ∈ I, ∀ L₃ ∈ I, L₁ = L₂ ∨ L₁ = L₃ ∨ L₂ = L₃ := by
    intro L₁ h₁ L₂ h₂ L₃ h₃
    rcases em (Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G)) with hA₁ | hA₁ <;>
    rcases em (Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G)) with hA₂ | hA₂ <;>
    rcases em (Hf L₃ ≤ Subgroup.normalizer (C₁ : Set G)) with hA₃ | hA₃
    · exact Or.inl (hAuniq L₁ h₁ L₂ h₂ hA₁ hA₂)
    · exact Or.inl (hAuniq L₁ h₁ L₂ h₂ hA₁ hA₂)
    · exact Or.inr (Or.inl (hAuniq L₁ h₁ L₃ h₃ hA₁ hA₃))
    · exact Or.inr (Or.inr (hBuniq L₂ h₂ L₃ h₃ hA₂ hA₃))
    · exact Or.inr (Or.inr (hAuniq L₂ h₂ L₃ h₃ hA₂ hA₃))
    · exact Or.inr (Or.inl (hBuniq L₁ h₁ L₃ h₃ hA₁ hA₃))
    · exact Or.inl (hBuniq L₁ h₁ L₂ h₂ hA₁ hA₂)
    · exact Or.inl (hBuniq L₁ h₁ L₂ h₂ hA₁ hA₂)
  have hstab : ∀ q ∈ autI hU M, ∀ k : ℕ, q ^ 3 ^ k = 1 → ∀ L ∈ I, B1.conjAut q L = L := by
    intro q hq k hqk L hL
    have h₁ := hperm q hq L hL
    have h₂ := hperm q hq _ h₁
    rcases huniq L hL _ h₁ _ h₂ with h | h | h
    · exact h.symm
    · have hq2 : B1.conjAut (q ^ 2) L = L := by
        rw [pow_two, conjAut_mul']
        exact h.symm
      have hpow : ∀ n : ℕ, B1.conjAut ((q ^ 2) ^ n) L = L := by
        intro n
        induction n with
        | zero => rw [pow_zero]; exact conjAut_one' L
        | succ n ih => rw [pow_succ (q ^ 2) n, conjAut_mul', hq2, ih]
      obtain ⟨m, hm⟩ := exists_sq_pow_eq_of_pow_three hqk
      rw [← hm]
      exact hpow m
    · have h' := congrArg (B1.conjAut q⁻¹) h
      rw [B1.conjAut_inv_conjAut, B1.conjAut_inv_conjAut] at h'
      exact h'.symm
  set KA : Subgroup G := ⨆ L ∈ I, ⨆ (_ : Hf L ≤ Subgroup.normalizer (C₁ : Set G)), Hf L
  set KB : Subgroup G := ⨆ L ∈ I, ⨆ (_ : ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G)), Hf L
  have hKAM : KA ≤ M := iSup₂_le fun L hL => iSup_le fun _ => hHM L hL
  have hKBM : KB ≤ M := iSup₂_le fun L hL => iSup_le fun _ => hHM L hL
  have hKBN : KB ≤ Subgroup.normalizer (C₂ : Set G) :=
    iSup₂_le fun L hL => iSup_le fun h => (hHcase L hL).resolve_left h
  have hcov : ∀ L ∈ I, L ≤ autI hU KA ∨ L ≤ autI hU KB := by
    intro L hL
    by_cases h : Hf L ≤ Subgroup.normalizer (C₁ : Set G)
    · exact Or.inl ((hHL L hL).trans (autI_mono hU (le_iSup₂_of_le L hL
        (le_iSup (fun _ : Hf L ≤ Subgroup.normalizer (C₁ : Set G) => Hf L) h))))
    · exact Or.inr ((hHL L hL).trans (autI_mono hU
        (le_iSup₂_of_le L hL (le_iSup (fun _ : ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G) => Hf L)
          h))))
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
  set CM : Subgroup G := Subgroup.centralizer (V : Set G) ⊓ M
  set 𝒜 : Subgroup G := CM ⊔ KA with h𝒜
  set ℬ : Subgroup G := KB ⊔ (M ⊓ Subgroup.normalizer (baum T : Set G))
  have h𝒜M : 𝒜 ≤ M := sup_le inf_le_right hKAM
  have hℬM : ℬ ≤ M := sup_le hKBM inf_le_left
  have hℬN : ℬ ≤ Subgroup.normalizer (C₂ : Set G) := sup_le hKBN hJ₂
  have hfac : ∀ m ∈ M, ∃ a ∈ 𝒜, ∃ b ∈ ℬ, m = a * b := by
    intro m hm
    obtain ⟨y, hy, a, ha, b, hb, n, hn, rfl⟩ := exists_factor_of_covering hMN hT (C1GN.baum_le T)
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T))
      (normalizer_inf_sup_le_normalizer_baum T _) hI hSylJ hJM hKAM hKBM hcov m hm
    exact ⟨y * a, Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right ha),
      b * n, Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hn),
      by group⟩
  obtain ⟨W, hWM, hWp, hWidx, hWfac⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_sylow_eq_mul_of_mul (p := 3) h𝒜M hℬM hfac
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal ctx.setting ctx.sigma ctx.core
  have h3 : 3 ≤ CFSG.Open.pRank 3 M := hP3.ge.trans (pRank_mono 3 Nat.prime_three hPM)
  obtain ⟨F, hFW, hFel, hFc⟩ := exists_elemAbelian_le_sylow_pow hWM hWp hWidx h3
  have hF27 : Nat.card F = 27 := by rw [hFc]; norm_num
  set U : Subgroup G := W ⊓ ℬ
  have hUW : U ≤ W := inf_le_left
  have hUp : IsPGroup 3 U := hWp.to_le hUW
  have hA'3 : Nat.card (W ⊓ 𝒜 : Subgroup G) ≤ 3 :=
    card_le_of_le_sup_centralizer hMN hC3 hKAM inf_le_right (hWp.to_le inf_le_left) hbA
  obtain ⟨-, hWle⟩ := not_isCyclic_of_E27_small_factor hFW hFel hF27 inf_le_left hUW hA'3 hWfac
  have hrk := ctx.pRank_inf_le_two
    (⟨C₂, hC₂1, hC₂2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₂ : Set G))) hN₂
  have hWU : ¬ W ≤ U := fun h => by
    have hFN : F ≤ Subgroup.normalizer (C₂ : Set G) ⊓ M :=
      le_inf (hFW.trans (h.trans (inf_le_right.trans hℬN))) (hFW.trans hWM)
    have := CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hFN hFel hFc
    omega
  obtain ⟨LA, hLA, hHA⟩ : ∃ L ∈ I, Hf L ≤ Subgroup.normalizer (C₁ : Set G) := by
    by_contra hno
    push Not at hno
    have hKAbot : KA = ⊥ :=
      le_bot_iff.1 (iSup₂_le fun L hL => iSup_le fun h => absurd h (hno L hL))
    refine hWU fun w hw => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hWfac w hw
    have haCM : a ∈ CM := by
      have h2 := ha.2
      rw [h𝒜, hKAbot, sup_bot_eq] at h2
      exact h2
    obtain ⟨k, hk⟩ := (hWp.to_le inf_le_left : IsPGroup 3 (W ⊓ 𝒜 : Subgroup G)) ⟨a, ha⟩
    have ha1 : a = 1 := eq_one_of_three_pow_eq_one_of_mem_coprime
      (by simpa using congrArg Subtype.val hk) haCM hC3
    rw [ha1, one_mul]
    exact hb
  obtain ⟨eA, -, -⟩ := hI.nat LA hLA
  obtain ⟨gA', hgA'⟩ := exists_prime_orderOf_dvd_card' (G := ↥LA) 3
    (by rw [hcard LA hLA]; norm_num)
  have hgAL : (gA' : MulAut (IntMod V hU)) ∈ LA := gA'.2
  have hgA3 : (gA' : MulAut (IntMod V hU)) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one gA'
    rw [hgA'] at h
    simpa using congrArg Subtype.val h
  have hgA1 : (gA' : MulAut (IntMod V hU)) ≠ 1 := fun h => by
    have h' : gA' = 1 := Subtype.ext h
    rw [h', orderOf_one] at hgA'
    omega
  set gA : MulAut (IntMod V hU) := (gA' : MulAut (IntMod V hU))
  have hWp' : IsPGroup 3 (W.subgroupOf M) := hWp.of_equiv (Subgroup.subgroupOfEquivOfLe hWM).symm
  have hWbarp : IsPGroup 3 ↥(autI hU W) := by
    rw [autI_eq_map_convHom hU hMN hWM]
    exact hWp'.map _
  have hcentA : ∀ q ∈ autI hU W, q * gA = gA * q := by
    intro q hq
    obtain ⟨k, hk⟩ := hWbarp ⟨q, hq⟩
    have hqk : q ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact commute_of_conjAut_eq eA hqk (hstab q (autI_mono hU hWM hq) k hqk LA hLA) hgAL hgA3
  have hgAW : gA ∈ autI hU W := by
    have hordg : orderOf gA = 3 := orderOf_eq_prime hgA3 hgA1
    have hZp : IsPGroup 3 (Subgroup.zpowers gA) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordg, pow_one])
    have hnorm : autI hU W ≤ Subgroup.normalizer
        ((Subgroup.zpowers gA : Subgroup (MulAut (IntMod V hU))) : Set (MulAut (IntMod V hU))) :=
      fun q hq => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2
        fun x hx => by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          exact ((show Commute gA q from (hcentA q hq).symm).zpow_left n).eq)
    have hQp : IsPGroup 3 ↥(autI hU W ⊔ Subgroup.zpowers gA) :=
      IsPGroup.to_sup_of_normal_right' hWbarp hZp hnorm
    have hidxW : ¬ 3 ∣ ((autI hU W).subgroupOf (autI hU M)).index := fun h =>
      hWidx (h.trans (relIndex_autI_dvd hMN hWM))
    have hgAM : Subgroup.zpowers gA ≤ autI hU M := by
      rw [Subgroup.zpowers_le]
      have : gA ∈ autI hU (thompsonJ M) := by
        rw [hJM]
        exact Subgroup.mem_iSup_of_mem LA (Subgroup.mem_iSup_of_mem hLA hgAL)
      exact autI_mono hU (B6.thompsonJ_le M) this
    exact (le_sup_right.trans (le_of_isPGroup_of_not_dvd_relIndex le_sup_left
      (sup_le (autI_mono hU hWM) hgAM) hQp hidxW)) (Subgroup.mem_zpowers gA)
  obtain ⟨⟨wA, hwAN⟩, hwAW, hwA⟩ := (mem_autI hU).1 hgAW
  have hwAM : wA ∈ M := hWM hwAW
  have hπwA : actM hU hMN ⟨wA, hwAM⟩ = gA := hwA
  set ψ : ↥W →* MulAut (IntMod V hU) := (actM hU hMN).comp (Subgroup.inclusion hWM)
  have hinj : Function.Injective ψ := injective_actM_comp_inclusion hMN hC3 hWM hWp
  have hψA : ψ ⟨wA, hwAW⟩ = gA := hπwA
  have hwA3 : wA ^ 3 = 1 := by
    have h : ψ (⟨wA, hwAW⟩ ^ 3) = ψ 1 := by rw [map_pow, hψA, hgA3, map_one]
    simpa using congrArg Subtype.val (hinj h)
  have hwA1 : wA ≠ 1 := fun h => hgA1 (by
    have h' : (⟨wA, hwAW⟩ : ↥W) = 1 := Subtype.ext h
    rw [← hψA, h', map_one])
  have hordA : orderOf wA = 3 := orderOf_eq_prime hwA3 hwA1
  have hwAc : ∀ w ∈ W, w * wA = wA * w := by
    intro w hw
    have hπw : ψ ⟨w, hw⟩ ∈ autI hU W := (mem_autI hU).2 ⟨⟨w, hMN (hWM hw)⟩, hw, rfl⟩
    have h : ψ (⟨w, hw⟩ * ⟨wA, hwAW⟩) = ψ (⟨wA, hwAW⟩ * ⟨w, hw⟩) := by
      rw [map_mul, map_mul, hψA]
      exact hcentA _ hπw
    simpa using congrArg Subtype.val (hinj h)
  have hwA𝒜 : wA ∈ 𝒜 := by
    obtain ⟨h', hh'H, hh'⟩ := (mem_autI hU).1 (hHL LA hLA hgAL)
    have hh'M : (h' : G) ∈ M := hHM LA hLA hh'H
    have hle : Hf LA ≤ KA := le_iSup₂_of_le LA hLA
      (le_iSup (fun _ : Hf LA ≤ Subgroup.normalizer (C₁ : Set G) => Hf LA) hHA)
    have hh'KA : (h' : G) ∈ KA := hle hh'H
    have hπh' : actM hU hMN ⟨(h' : G), hh'M⟩ = gA := hh'
    have hcM : wA * (h' : G)⁻¹ ∈ M := M.mul_mem hwAM (M.inv_mem hh'M)
    have hone : actM hU hMN ⟨wA * (h' : G)⁻¹, hcM⟩ = 1 := by
      have e : actM hU hMN ⟨wA * (h' : G)⁻¹, hcM⟩ =
          actM hU hMN ⟨wA, hwAM⟩ * (actM hU hMN ⟨(h' : G), hh'M⟩)⁻¹ := by
        rw [← map_inv, ← map_mul]
        rfl
      rw [e, hπwA, hπh', mul_inv_cancel]
    have hcCM : wA * (h' : G)⁻¹ ∈ CM := ⟨(actM_eq_one_iff hU hMN _).1 hone, hcM⟩
    have := 𝒜.mul_mem (Subgroup.mem_sup_left hcCM) (Subgroup.mem_sup_right hh'KA)
    simpa using this
  have hzA : Subgroup.zpowers wA = W ⊓ 𝒜 :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ⟨hwAW, hwA𝒜⟩)
      (by rw [Nat.card_zpowers, hordA]; exact hA'3)
  have hwAU : wA ∉ U := fun h => hWU fun w hw => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hWfac w hw
    rw [← hzA] at ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact U.mul_mem (U.zpow_mem h n) hb
  have hU9 : 9 ≤ Nat.card U := by
    have := Subgroup.card_le_of_le hFW
    rw [hF27] at this
    omega
  have hUnt : Nontrivial ↥U := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  have hZnt : Nontrivial ↥(Subgroup.center ↥U) := hUp.center_nontrivial
  have hZ3 : 3 ∣ Nat.card ↥(Subgroup.center ↥U) := by
    rcases (hUp.to_subgroup (Subgroup.center ↥U)).card_eq_or_dvd with h | h
    · have := Finite.one_lt_card_iff_nontrivial.2 hZnt
      omega
    · exact h
  obtain ⟨u₀, hu₀⟩ := exists_prime_orderOf_dvd_card' 3 hZ3
  set u : G := ((u₀ : ↥U) : G) with hudef
  have huU : u ∈ U := (u₀ : ↥U).2
  have hordu : orderOf u = 3 := by
    rw [hudef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu₀]
  have hu3 : u ^ 3 = 1 := by
    rw [← hordu]
    exact pow_orderOf_eq_one u
  have huUc : ∀ b ∈ U, b * u = u * b := fun b hb =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 u₀.2 ⟨b, hb⟩)
  have huc : ∀ w ∈ W, w * u = u * w := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hWfac w hw
    rw [← hzA] at ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have h1 : Commute (wA ^ n) u := (show Commute wA u from (hwAc u (hUW huU)).symm).zpow_left n
    have h2 : Commute b u := huUc b hb
    exact (h1.mul_left h2).eq
  have hcommAu : wA * u = u * wA := (hwAc u (hUW huU)).symm
  set E : Subgroup G := Subgroup.closure ({wA, u} : Set G)
  have hEp : IsPGroup 3 E := isPGroup_three_closure_pair hcommAu hwA3 hu3
  have hnc : ¬ IsCyclic E := by
    intro hcyc
    obtain ⟨z, hz⟩ := hcyc.exists_generator
    have hz3 : z ^ 3 = 1 := Subtype.ext (by
      simpa using pow_three_of_mem_closure_pair hcommAu hwA3 hu3 z.2)
    have hcardE : Nat.card E ≤ 3 := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hz]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz3)
    have hAE : Subgroup.zpowers wA = E := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))
      (by rw [Nat.card_zpowers, hordA]; exact hcardE)
    have huA : u ∈ Subgroup.zpowers wA := hAE ▸ Subgroup.subset_closure (by simp)
    have hzz : Subgroup.zpowers u = Subgroup.zpowers wA := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.2 huA) (by rw [Nat.card_zpowers, Nat.card_zpowers, hordu, hordA])
    have hwAu : wA ∈ Subgroup.zpowers u := hzz ▸ Subgroup.mem_zpowers wA
    exact hwAU (Subgroup.zpowers_le.2 huU hwAu)
  obtain ⟨E₉, hE₉E, hE₉el, hE₉c⟩ := exists_E9_le_of_not_isCyclic hEp hnc
  have hEc : E ≤ Subgroup.centralizer (W : Set G) := (Subgroup.closure_le _).2 (by
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.mem_centralizer_iff.2 fun w hw => hwAc w hw
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_centralizer_iff.2 fun w hw => huc w hw)
  have hEW : E ≤ W := (Subgroup.closure_le W).2 (by
    intro x hx
    rcases hx with rfl | hx
    · exact hwAW
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hUW huU)
  refine ⟨W, hWM, hWp, hWidx, E₉, hE₉E.trans hEW, hE₉el, hE₉c, fun w hw _ e he => ?_⟩
  exact Subgroup.mem_centralizer_iff.1 (hEc (hE₉E he)) w hw

theorem center3_of_coprime27
    (hX : D1NoXBlock3 G) {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {T : Subgroup G}
    (c : D2L34R27 G d P M A H R Rbar K T) (hC3 : ¬ 3 ∣ Nat.card ↥(ffC M T)) :
    Center3Conclusion M := by
  have ctx := c.ctx
  have hN : NoXBlockFor G := noXBlockFor_of_setting hX ctx.setting
  have := ctx.amb
  have hc := ctx.conf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT := c.sylow
  have hNT := c.not_normalizer_le
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal ctx.setting ctx.sigma ctx.core
  have h3 : 3 ≤ CFSG.Open.pRank 3 M := hP3.ge.trans (pRank_mono 3 Nat.prime_three hPM)
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G)
  · exact (ctx.false_of_thompsonJ_le_of_coprime' h3 hT hNT hJ hC3).elim
  · set V := conjClosure (quasithinOmegaOneCenter T) M with hV
    obtain ⟨hU, -⟩ := B2_15 hF hT
    have hMN : M ≤ Subgroup.normalizer (V : Set G) :=
      (conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)).2.2.2.1
    have hsAut : Group.IsSolvable ↥(autOn M V) := by
      have := c.solvable
      exact Group.isSolvable_of_surjective (actOnAutOn_surjective hMN)
    have hFFc : FFConclusion M T V := ffConclusion_of_solvable hF hsAut hT hV hJ
    obtain ⟨hU', hMN', I, hI0, hcard, hJM, hSyl, hperm, hI⟩ :=
      exists_family_of_ffConclusion hT hJ hFFc
    obtain ⟨C₁, C₂, hdat⟩ := exists_ffPairData3_free hN ffGroupStep3Free ctx hT hNT hU' I hMN'
      hcard hJM hSyl hperm hI
    obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
    have hVT : V ≤ T := hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
    have hBS : autI hU' (baum T) ≤ autI hU' (thompsonJ M) :=
      autI_baum_le_autI_thompsonJ hMN' hT hVT hI hJM (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
        hperm
    have hSylB : IsSylowTwoOf (autI hU' (baum T)) (autI hU' (thompsonJ M)) :=
      isSylowTwoOf_of_le_of_le hSyl (autI_mono hU' (thompsonJ_le_baum T)) hBS
        (isPGroup_autI hU' (hT.2.1.to_le (C1GN.baum_le T)))
    exact center3_of_pairData27 c hMN' hI hI0 hcard hSylB hJM hperm hC3 hdat

end CFSG.LocalAnalysis.RankThreeTheoremC
