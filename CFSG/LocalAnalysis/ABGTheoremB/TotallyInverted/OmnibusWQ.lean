module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusWN
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.QCover
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusWBasic

public section

namespace CFSG.ABGTheoremB.TotallyInverted.OmnibusW

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion Omnibus
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem a_mem_normalizer_T (hσ : σ.IsValid) (Δ : Data σ r) :
    Δ.a ∈ Subgroup.normalizer (σ.T : Set G) := by
  apply mem_normalizer_of_conj_le
  intro t ht
  rcases (mem_T_iff hσ).mp ht with rfl | ⟨j, rfl⟩
  · rw [mul_one, mul_inv_cancel]
    exact σ.T.one_mem
  · rw [Δ.a_cycle j]
    exact xs_mem_T _

section Maximal

theorem exists_eq_sup_of_mem_maximals (hσ : σ.IsValid) (Δ : Data σ r) {U : Subgroup G}
    (hU : U ∈ maximals (signalizersPerm σ.N σ.T σ.C r)) :
    IsSylowOf r (U ⊓ σ.C) σ.C ∧ ∃ Y ∈ ({Δ.Q 0, Δ.Qs 0} : Set (Subgroup G)),
      U = U ⊓ σ.C ⊔ Y ⊔ σ.Ps r 0 := by
  have hR := isSylowOf_inf_C hσ Δ σ.C_le_N hU
  refine ⟨hR, ?_⟩
  have hmem : U ∈ {V | V ∈ maximals (signalizersPerm (σ.Ns 0) σ.T σ.C r) ∧ U ⊓ σ.C ≤ V} :=
    ⟨hU, inf_le_left⟩
  rw [Δ.lemma72 0 _ hR] at hmem
  split_ifs at hmem with hq
  · rcases hmem with h | h
    · exact ⟨Δ.Q 0, Or.inl rfl, h⟩
    · exact ⟨Δ.Qs 0, Or.inr rfl, h⟩
  · refine ⟨Δ.Q 0, Or.inl rfl, ?_⟩
    rw [(Δ.Q_trivial hq 0).1, sup_bot_eq]
    exact hmem

variable {K : Subgroup G}

theorem exists_swap (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (Δ : Data σ r) (hKN : K ≤ σ.N)
    (hCK : σ.C ≤ K) (hcover : (σ.L₀ : Set G) ⊆ (K : Set G) * σ.ON) :
    ∃ m ∈ K ⊓ Subgroup.normalizer (σ.T : Set G), conjSub m (Δ.Q 0) = Δ.Qs 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hq : σ.DeltaEpsMinus ∧ r ∣ σ.q
  swap
  · refine ⟨1, ⟨K.one_mem, Subgroup.one_mem _⟩, ?_⟩
    rw [conjSub_one, (Δ.Q_trivial hq 0).1, (Δ.Q_trivial hq 0).2]
  obtain ⟨-, -, -, -, ⟨z, hzD, hz⟩, -⟩ := Δ.Q_cases hq 0
  have hzD' : z ∈ σ.D := by simpa using hzD
  have hzN : z ∈ σ.N := σ.D_le_N hσ hzD'
  have hzT : z ∈ Subgroup.normalizer (σ.T : Set G) :=
    (show σ.D ≤ Subgroup.normalizer (σ.T : Set G) from inf_le_right) hzD'
  have hKON : K ≤ Subgroup.normalizer (σ.ON : Set G) := hKN.trans σ.N_le_normalizer_ON
  have hLK : σ.L ≤ K ⊔ σ.ON := by
    rw [hII.L_eq]
    refine sup_le (fun l hl => ?_) ((inf_le_right.trans hCK).trans le_sup_left)
    obtain ⟨k, hk, o, ho, rfl⟩ := hcover hl
    exact Subgroup.mul_mem_sup hk ho
  have hzL : z ∈ σ.L := Subgroup.mem_sup_right (σ.D_le_S hzD')
  have hz' : z ∈ ((K ⊔ σ.ON : Subgroup G) : Set G) := hLK hzL
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K σ.ON hKON] at hz'
  obtain ⟨k, hk, o, ho, hko⟩ := hz'
  have hko' : k = z * o⁻¹ := by
    have : k * o = z := hko
    rw [← this]
    group
  have hONQ : ∀ Y : Subgroup G, Y ≤ Δ.J → σ.ON ≤ Subgroup.normalizer (Y : Set G) := fun Y hY =>
    ((Subgroup.le_centralizer_iff.mp Δ.J_centralizes).trans (Subgroup.centralizer_le hY)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQJ : Δ.Q 0 ≤ Δ.J ∧ Δ.Qs 0 ≤ Δ.J := by simpa using Δ.Q_le 0
  have hkQ : conjSub k (Δ.Q 0) = Δ.Qs 0 := by
    rw [hko', conjSub_mul, conjSub_eq_self (hONQ _ hQJ.1 (σ.ON.inv_mem ho)), hz]
  have hTK : σ.T ≤ K := (σ.T_le_C hσ).trans hCK
  have hTON : σ.T ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (σ.T_le_N hσ).trans σ.N_le_normalizer_ON
  set B : Subgroup G := K ⊓ (σ.T ⊔ σ.ON) with hBdef
  have hTB : σ.T ≤ B := le_inf hTK le_sup_left
  have hkT : conjSub k σ.T ≤ B := by
    refine le_inf ((conjSub_mono hTK).trans (conjSub_eq_self_of_mem hk).le) ?_
    have hzTON : conjSub z (σ.T ⊔ σ.ON) = σ.T ⊔ σ.ON := by
      rw [conjSub_sup, conjSub_eq_self hzT, conjSub_eq_self (σ.N_le_normalizer_ON hzN)]
    rw [hko', conjSub_mul, ← hzTON]
    exact conjSub_mono ((conjSub_mono le_sup_left).trans
      (conjSub_eq_self_of_mem (Subgroup.mem_sup_right (σ.ON.inv_mem ho))).le)
  have hTsyl : IsSylowOf 2 σ.T B := by
    refine isSylowOf_iff.mpr ⟨hTB, T_isPGroup hσ, fun h2 => ?_⟩
    have h1 : σ.T.relIndex B ∣ σ.T.relIndex (σ.T ⊔ σ.ON) :=
      Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ hTB inf_le_right)
    rw [sup_comm, relIndex_sup_of_mul_comm (mul_comm_of_le_normalizer hTON).symm] at h1
    have hodd : Odd (σ.T.relIndex σ.ON) :=
      σ.odd_card_ON.of_dvd_nat (Subgroup.relIndex_dvd_card _ _)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans h1))
  obtain ⟨b, hbB, hle⟩ :=
    exists_le_conjSub_of_isSylowOf hTsyl hkT (isPGroup_conjSub (T_isPGroup hσ))
  have heq : conjSub k σ.T = conjSub b σ.T :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [card_conjSub, card_conjSub]))
  refine ⟨b⁻¹ * k, ⟨K.mul_mem (K.inv_mem hbB.1) hk, ?_⟩, ?_⟩
  · apply mem_normalizer_of_conjSub_eq
    rw [conjSub_mul, heq, conjSub_inv_conjSub]
  · have hbQ : b⁻¹ ∈ Subgroup.normalizer (Δ.Qs 0 : Set G) :=
      sup_le ((σ.T_le_C hσ).trans (Δ.Q_C 0).2) (hONQ _ hQJ.2) (Subgroup.inv_mem _ hbB.2)
    rw [conjSub_mul, hkQ, conjSub_eq_self hbQ]

theorem exists_conj_of_mem_maximals (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (Δ : Data σ r)
    (hKN : K ≤ σ.N) (hCK : σ.C ≤ K) (hcover : (σ.L₀ : Set G) ⊆ (K : Set G) * σ.ON)
    {U U' : Subgroup G} (hU : U ∈ maximals (signalizersPerm σ.N σ.T σ.C r))
    (hU' : U' ∈ maximals (signalizersPerm σ.N σ.T σ.C r)) :
    ∃ m ∈ K ⊓ Subgroup.normalizer (σ.T : Set G), conjSub m U' = U := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  obtain ⟨hR, Y, hY, hUeq⟩ := exists_eq_sup_of_mem_maximals hσ Δ hU
  obtain ⟨hR', Y', hY', hU'eq⟩ := exists_eq_sup_of_mem_maximals hσ Δ hU'
  obtain ⟨m₀, ⟨hm₀K, hm₀T⟩, hm₀⟩ := exists_swap hσ hII Δ hKN hCK hcover
  have hY2 : Y = Δ.Q 0 ∨ Y = Δ.Qs 0 := hY
  have hY'2 : Y' = Δ.Q 0 ∨ Y' = Δ.Qs 0 := hY'
  have hCY : σ.C ≤ Subgroup.normalizer (Y : Set G) := by
    rcases hY2 with h | h <;> rw [h]
    · exact (Δ.Q_C 0).1
    · exact (Δ.Q_C 0).2
  obtain ⟨m, ⟨hmK, hmT⟩, hm⟩ :
      ∃ m ∈ K ⊓ Subgroup.normalizer (σ.T : Set G), conjSub m Y' = Y := by
    rcases hY2 with h | h <;> rcases hY'2 with h' | h' <;> rw [h, h']
    · exact ⟨1, ⟨K.one_mem, Subgroup.one_mem _⟩, conjSub_one _⟩
    · exact ⟨m₀⁻¹, ⟨K.inv_mem hm₀K, Subgroup.inv_mem _ hm₀T⟩,
        by rw [← hm₀, conjSub_inv_conjSub]⟩
    · exact ⟨m₀, ⟨hm₀K, hm₀T⟩, hm₀⟩
    · exact ⟨1, ⟨K.one_mem, Subgroup.one_mem _⟩, conjSub_one _⟩
  have hmP : conjSub m (σ.Ps r 0) = σ.Ps r 0 :=
    conjSub_eq_self (le_normalizer_pCoreIn r σ.N (hKN hmK))
  have hR'' : IsSylowOf r (conjSub m (U' ⊓ σ.C)) σ.C := by
    have := isSylowOf_conjSub m hR'
    rwa [conjSub_eq_self (normalizer_T_le_M hmT)] at this
  obtain ⟨c, hc, hcR⟩ := exists_conjSub_eq_of_isSylowOf hR'' hR
  have hcY : conjSub c Y = Y := conjSub_eq_self (hCY hc)
  have hcP : conjSub c (σ.Ps r 0) = σ.Ps r 0 :=
    conjSub_eq_self (le_normalizer_pCoreIn r σ.N (σ.C_le_N hc))
  refine ⟨c * m, ⟨K.mul_mem (hCK hc) hmK, Subgroup.mul_mem _ (C_le_normalizer_T hc) hmT⟩, ?_⟩
  rw [hU'eq, hUeq]
  simp only [conjSub_mul, conjSub_sup]
  rw [hcR, hm, hmP, hcY, hcP]

theorem sup_ON_inf_mem (hσ : σ.IsValid) (hKN : K ≤ σ.N) (hCK : σ.C ≤ K)
    (hOK : oddCoreIn K ≤ σ.ON) {U : Subgroup G} (hU : U ∈ signalizersPerm σ.N σ.T σ.C r) :
    (U ⊔ σ.ON) ⊓ K ∈ liftedSignalizers σ K r := by
  obtain ⟨⟨hUN, hUp, hTU, -⟩, hperm⟩ := hU
  have hKO : K ⊓ σ.ON ≤ oddCoreIn K :=
    inf_le_oddCoreIn (hKN.trans σ.N_le_normalizer_ON) σ.odd_card_ON
  have hUON : U ≤ Subgroup.normalizer (σ.ON : Set G) := hUN.trans σ.N_le_normalizer_ON
  have hCON : σ.C ≤ Subgroup.normalizer (σ.ON : Set G) := σ.C_le_N.trans σ.N_le_normalizer_ON
  have hUr : ∀ u ∈ U, ∃ k : ℕ, u ^ r ^ k ∈ σ.ON := by
    intro u hu
    obtain ⟨k, hk⟩ := hUp ⟨u, hu⟩
    refine ⟨k, ?_⟩
    have : u ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact σ.ON.one_mem
  have hcoe : ((U ⊔ σ.ON : Subgroup G) : Set G) = U * σ.ON :=
    Subgroup.coe_mul_of_left_le_normalizer_right U σ.ON hUON
  have hpermON : ((U ⊔ σ.ON : Subgroup G) : Set G) * σ.C = σ.C * (U ⊔ σ.ON : Subgroup G) := by
    calc ((U ⊔ σ.ON : Subgroup G) : Set G) * σ.C = (U * σ.ON) * σ.C := by rw [hcoe]
      _ = U * (σ.C * σ.ON) := by rw [mul_assoc, ← mul_comm_of_le_normalizer hCON]
      _ = (σ.C * U) * σ.ON := by rw [← mul_assoc, hperm]
      _ = σ.C * (U ⊔ σ.ON : Subgroup G) := by rw [mul_assoc, hcoe]
  refine ⟨le_inf (hOK.trans le_sup_right) (oddCoreIn_le K), inf_le_right, fun g hg => ?_,
    fun t ht => mem_normalizer_inf (mem_normalizer_sup (hTU ht)
      (σ.N_le_normalizer_ON (σ.T_le_N hσ ht)))
      (Subgroup.le_normalizer (((σ.T_le_C hσ).trans hCK) ht)),
    inf_mul_comm_of_le hCK hpermON⟩
  have hg' : g ∈ σ.ON ⊔ U := by
    rw [sup_comm]
    exact hg.1
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hUON hUr hg'
  exact ⟨k, hKO ⟨K.pow_mem hg.2 _, hk⟩⟩

theorem exists_le_sup_ON_inf (hσ : σ.IsValid) (Δ : Data σ r) (hN : ABG_II_4_11_Input Δ)
    (hKN : K ≤ σ.N) (hCK : σ.C ≤ K) (hOK : oddCoreIn K ≤ σ.ON) {Y : Subgroup G}
    (hY : Y ∈ liftedSignalizers σ K r) :
    ∃ U ∈ maximals (signalizersPerm σ.N σ.T σ.C r), Y ≤ (U ⊔ σ.ON) ⊓ K := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  have hYodd := odd_card_of_mem_liftedSignalizers Δ hY
  obtain ⟨hOY, hYK, hYr, hTY, hperm⟩ := hY
  obtain ⟨V', hV', hTV'⟩ := exists_isSylowOf_le_normalizer (T_isPGroup hσ) hYodd hTY r
  set X : Subgroup G := Y ⊔ σ.C with hXdef
  have hX := hasNormalPComplement_sup hσ Δ hYodd hTY hperm
  have hXK : X ≤ K := sup_le hYK hCK
  have hTO : σ.T ≤ Subgroup.normalizer ((oddCoreIn X : Subgroup G) : Set G) :=
    ((σ.T_le_C hσ).trans le_sup_right).trans (le_normalizer_oddCoreIn X)
  have hV'O : V' ≤ oddCoreIn X := le_oddCoreIn_of_hasNormalPComplement hX
    (hV'.le.trans le_sup_left) (odd_card_of_isPGroup Δ.prime Δ.ne_two hV'.isPGroup)
  obtain ⟨V, hV, hV'V, hTV⟩ := exists_isSylowOf_le_normalizer_of_le (T_isPGroup hσ)
    (odd_card_oddCoreIn X) hTO hV'O hV'.isPGroup hTV'
  have hVX := isSylowOf_of_isSylowOf_oddCoreIn Δ.prime Δ.ne_two hX hV
  have hVmem : V ∈ signalizersPerm σ.N σ.T σ.C r :=
    mem_signalizersPerm hσ Δ (hVX.le.trans (hXK.trans hKN)) hVX.isPGroup hTV
      (mul_comm_of_isSylowOf hσ Δ hN hYodd hTY hperm hVX hTV)
  obtain ⟨U, hU, hVU⟩ := exists_le_mem_maximals hVmem
  refine ⟨U, hU, le_inf ((le_sup_of_isSylowOf Δ.prime hOY
    (hYK.trans (le_normalizer_oddCoreIn K)) hYr hV').trans
    (sup_le (hOK.trans le_sup_right) ((hV'V.trans hVU).trans le_sup_left))) hYK⟩

theorem exists_eq_sup_ON_inf (hσ : σ.IsValid) (Δ : Data σ r) (hN : ABG_II_4_11_Input Δ)
    (hKN : K ≤ σ.N) (hCK : σ.C ≤ K) (hOK : oddCoreIn K ≤ σ.ON) {Y : Subgroup G}
    (hY : Y ∈ maximals (liftedSignalizers σ K r)) :
    ∃ U ∈ maximals (signalizersPerm σ.N σ.T σ.C r), Y = (U ⊔ σ.ON) ⊓ K := by
  obtain ⟨U, hU, hle⟩ := exists_le_sup_ON_inf hσ Δ hN hKN hCK hOK hY.1
  exact ⟨U, hU, (hY.2 _ (sup_ON_inf_mem hσ hKN hCK hOK hU.1) hle).symm⟩

theorem conjugate_of_le_N (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (Δ : Data σ r)
    (hN : ABG_II_4_11_Input Δ) (hKN : K ≤ σ.N) (hCK : σ.C ≤ K)
    (hcover : (σ.L₀ : Set G) ⊆ (K : Set G) * σ.ON) (hOK : oddCoreIn K ≤ σ.ON) :
    Conjugate σ K r := by
  intro Y hY Y' hY'
  obtain ⟨U, hU, rfl⟩ := exists_eq_sup_ON_inf hσ Δ hN hKN hCK hOK hY
  obtain ⟨U', hU', rfl⟩ := exists_eq_sup_ON_inf hσ Δ hN hKN hCK hOK hY'
  obtain ⟨m, ⟨hmK, hmT⟩, hm⟩ := exists_conj_of_mem_maximals hσ hII Δ hKN hCK hcover hU hU'
  refine ⟨m, ⟨hmK, hmT⟩, ?_⟩
  rw [conjSub_inf, conjSub_sup, hm, conjSub_eq_self (σ.N_le_normalizer_ON (hKN hmK)),
    conjSub_eq_self_of_mem hmK]

end Maximal

section QGroup

theorem exists_le_oddCoreIn_sup_inf_Ns (hσ : σ.IsValid) (Δ : Data σ r)
    (h31 : ABG_II_3_1_Input G) {H : Subgroup G} (hCH : σ.C ≤ H) (hHQ : IsQGroup H) :
    ∃ i : Fin 3, H ≤ oddCoreIn H ⊔ H ⊓ σ.Ns i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : σ.T ≤ H := (σ.T_le_C hσ).trans hCH
  obtain ⟨Q, hTQ⟩ := ((T_isPGroup hσ).comap_subtype (K := H)).exists_le_sylow
  set S₁ : Subgroup G := (Q : Subgroup H).map H.subtype with hS₁def
  have hS₁ : IsSylowOf 2 S₁ H := ⟨Q, rfl⟩
  have hTS₁ : σ.T ≤ S₁ := fun t ht => ⟨⟨t, hTH ht⟩, hTQ ht, rfl⟩
  obtain ⟨z, hzS, hzZ, hz2⟩ : ∃ z ∈ S₁, z ∈ Subgroup.centralizer (S₁ : Set G) ∧
      orderOf z = 2 := by
    have hS₁p : IsPGroup 2 S₁ := hS₁.isPGroup
    have : Nontrivial S₁ := ⟨⟨1, ⟨σ.x, hTS₁ σ.x_mem_T⟩, fun h => x_ne_one hσ
      (congrArg Subtype.val h).symm⟩⟩
    have hZ := hS₁p.center_nontrivial
    have hZp : IsPGroup 2 (Subgroup.center S₁) := hS₁p.to_subgroup _
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZp
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hn
    have h2 : 2 ∣ Nat.card (Subgroup.center S₁) := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 2 h2
    refine ⟨((z₀ : S₁) : G), (z₀ : S₁).2, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z₀.2 ⟨s, hs⟩)
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz₀]
  have hzC : z ∈ σ.C := by
    rw [Setting.C, Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp hzZ) t (hTS₁ ht)
  have hzT : z ∈ σ.T :=
    mem_T_of_mem_C_of_sq Δ hzC (by rw [← hz2]; exact pow_orderOf_eq_one z)
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  obtain ⟨i, rfl⟩ := ((mem_T_iff hσ).mp hzT).resolve_left hz1
  refine ⟨i, (h31 H hHQ S₁ hS₁).trans (sup_le_sup_left (inf_le_inf_left H ?_) _)⟩
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ⟨hzS, hzZ⟩)

theorem conjugate_of_le_sup_inf_N (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (hQC : σ.QCoverFact) (Δ : Data σ r) (hN : ABG_II_4_11_Input Δ) {H : Subgroup G}
    (hCH : σ.C ≤ H) (hHQ : IsQGroup H) (hdec : H ≤ oddCoreIn H ⊔ H ⊓ σ.N) :
    Conjugate σ H r := by
  have hCK : σ.C ≤ H ⊓ σ.N := le_inf hCH σ.C_le_N
  have hKQ := isQGroup_of_le_sup inf_le_left hdec hHQ
  have hcover := hQC (H ⊓ σ.N) inf_le_right hCK hKQ
  have hOK := hII.N_oddCore_of_cover (H ⊓ σ.N) inf_le_right hcover
  exact conjugate_of_conjugate_inf hσ inf_le_left hCK hdec
    (conjugate_of_le_N hσ hII Δ hN inf_le_right hCK hcover hOK)

theorem qConjugacy (hσ : σ.IsValid) (hh : σ.height ≠ 1) (hII : σ.ChapterIIFacts)
    (hT : σ.TIFacts) (hQC : σ.QCoverFact) (h31 : ABG_II_3_1_Input G) (Δ : Data σ r) :
    ABG_V_8_7_Q_Input σ r := by
  intro H hCH _ hHQ
  have hN := nStructure hσ hh hT Δ
  obtain ⟨i, hdec⟩ := exists_le_oddCoreIn_sup_inf_Ns hσ Δ h31 hCH hHQ
  set m : G := (Δ.a ^ (i : ℕ))⁻¹ with hmdef
  have hm : m ∈ Subgroup.normalizer (σ.T : Set G) :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ (a_mem_normalizer_T hσ Δ) _)
  have hmN : conjSub m (σ.Ns i) = σ.N := by
    rw [hmdef, ← conjSub_a_pow_N Δ i, conjSub_inv_conjSub]
  refine conjugate_of_conjSub hm (conjugate_of_le_sup_inf_N hσ hII hQC Δ hN ?_
    (IsQGroup.of_mulEquiv (conjSubEquiv m H) hHQ) ?_)
  · rw [← conjSub_C hm]
    exact conjSub_mono hCH
  · calc conjSub m H ≤ conjSub m (oddCoreIn H ⊔ H ⊓ σ.Ns i) := conjSub_mono hdec
      _ = oddCoreIn (conjSub m H) ⊔ conjSub m H ⊓ σ.N := by
        rw [conjSub_sup, conjSub_inf, hmN, oddCoreIn_conjSub]

end QGroup

end CFSG.ABGTheoremB.TotallyInverted.OmnibusW
