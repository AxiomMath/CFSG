module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Derived
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.Quasithin.Background.A4
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Aux

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem isShort2_eq_oTwoUpper {L : Subgroup G} (hL : IsShort2 L) : L = oTwoUpper L := by
  refine le_antisymm ?_ (oTwoUpper_le L)
  have hN : ((oTwoUpper L).subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoUpper L)
  have h2 : IsPGroup 2 (L ⧸ (oTwoUpper L).subgroupOf L) := by
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper L g.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have htop := hL.1 ((oTwoUpper L).subgroupOf L) h2
  intro x hx
  have : (⟨x, hx⟩ : L) ∈ (oTwoUpper L).subgroupOf L := by rw [htop]; trivial
  exact this

theorem isPGroup_sup_of_le_normalizer_two {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) :
    IsPGroup 2 (A ⊔ B : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hA.exists_card_eq
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  have hc := card_sup_mul_card_inf hAB
  rw [ha, hb, ← pow_add] at hc
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hc)
  exact IsPGroup.of_card hk

omit [Finite G] in
theorem le_blockZ_or_eq_blockU {L V : Subgroup G} (hL : IsShort2 L) (hUQ : pCoreOf 2 L = blockU L)
    (hVU : V ≤ blockU L) (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    V ≤ blockZ L ∨ V = blockU L := by
  have hZN : L ≤ Subgroup.normalizer (blockZ L : Set G) :=
    le_normalizer_of_commute fun z hz ℓ hℓ => (Subgroup.mem_centralizer_iff.1 hz.2 ℓ hℓ).symm
  have hWN : L ≤ Subgroup.normalizer ((V ⊔ blockZ L : Subgroup G) : Set G) := by
    intro g hg
    rw [← conjR_eq_self_iff, conjR_sup, conjR_eq_of_mem_normalizer (hLV hg),
      conjR_eq_of_mem_normalizer (hZN hg)]
  have hWU : V ⊔ blockZ L ≤ blockU L := sup_le hVU (blockZ_le_blockU L)
  rcases hL.2.2.2.2.2 (V ⊔ blockZ L) le_sup_right hWU hWN with hW | hW
  · exact Or.inl (le_sup_left.trans hW.le)
  · right
    refine le_antisymm hVU ?_
    have hUU : blockU L = ⁅blockU L, L⁆ := by
      conv_lhs => rw [blockU, blockQ, hUQ]
    have hZV : blockZ L ≤ Subgroup.normalizer (V : Set G) := by
      refine le_normalizer_of_commute fun v hv z hz => ?_
      have hvU := hVU hv
      have hzU := blockZ_le_blockU L hz
      exact (Subgroup.mem_centralizer_iff.1 (hL.2.2.1.1 hvU).2 z (hL.2.2.1.1 hzU).1).symm
    rw [hUU]
    refine Subgroup.commutator_le.2 fun u hu ℓ hℓ => ?_
    rw [← hW] at hu
    obtain ⟨v, hv, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer hZV).1 hu
    have hzℓ : ℓ * z = z * ℓ := Subgroup.mem_centralizer_iff.1 hz.2 ℓ hℓ
    have e : ⁅v * z, ℓ⁆ = v * (ℓ * v⁻¹ * ℓ⁻¹) := by
      rw [commutatorElement_def]
      calc v * z * ℓ * (v * z)⁻¹ * ℓ⁻¹ = v * (z * ℓ) * z⁻¹ * v⁻¹ * ℓ⁻¹ := by group
        _ = v * (ℓ * z) * z⁻¹ * v⁻¹ * ℓ⁻¹ := by rw [← hzℓ]
        _ = v * (ℓ * v⁻¹ * ℓ⁻¹) := by group
    rw [e]
    exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.1 (hLV hℓ) v⁻¹).1 (V.inv_mem hv))

theorem Lin2Cfg.le_pCoreOf_of_isSignalizer (h : Lin2Cfg G T M H S L n D)
    (hN : Subgroup.normalizer (pCoreOf 2 H : Set G) = Subgroup.normalizer (L : Set G))
    {V : Subgroup G} (hV : IsSignalizer (Subgroup.normalizer (pCoreOf 2 H : Set G)) L V) :
    V ≤ pCoreOf 2 H := by
  set Q := pCoreOf 2 H with hQ
  set N := Subgroup.normalizer (Q : Set G) with hNdef
  have hX : L = oTwoUpper L := isShort2_eq_oTwoUpper h.short
  have hLN : L ≤ N := by rw [hN]; exact Subgroup.le_normalizer
  have hXM : IsSubnormal L N :=
    A4.subnormal_of_normal hLN ((Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2 hN.le)
  obtain ⟨-, -, -, hSN, -⟩ := h.cs.gamma0.core_normalizer h.cs.setting h.cs.sylow_inf
  have hT : IsSylowTwoOf S (N ⊓ Subgroup.normalizer (L : Set G)) := by
    rw [← hN, inf_idem]
    exact hSN
  have hmax := a4_2_5 hX hXM hT
  rw [← h.H_eq] at hmax
  obtain ⟨R, hR, hVR⟩ := exists_isMaxSignalizer_ge hV
  have hRC := (a4_2_4 hX hXM R).1 hR
  have hQC := (a4_2_4 hX hXM Q).1 hmax
  have hCN : centralizerSection N L (pCoreOf 2 L) ≤ N := centralizerSection_le_left _ _ _
  have hQR : Q ≤ R :=
    A4.le_of_normal_of_isSylowTwoOf hRC hQC.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQC.1).2 hCN)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  have hRQ : R = Q := hQC.eq_of_le hQR hRC.1 hRC.isPGroup
  exact hRQ ▸ hVR

end Aux

@[expose] def Lemma2_4_11_core : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
    centerOf L ≠ ⊥ → ∀ v ∈ centerOf L, v ≠ 1 →
      Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (pCoreOf 2 H : Set G)

theorem lemma2_4_11 (h8 : Lemma2_4_8) (h246 : Lemma246Chi) (hcore : Lemma2_4_11_core) :
    Lemma2_4_11 := by
  intro G _ _ T M H S L D n hcfg
  obtain ⟨-, ⟨hQL, hUH⟩, -, h4, -⟩ := h8 G T M H S L D n hcfg
  have hQL' : pCoreOf 2 L = pCoreOf 2 H := hQL.trans hUH
  have hN : Subgroup.normalizer (pCoreOf 2 H : Set G) = Subgroup.normalizer (L : Set G) := by
    apply le_antisymm
    · exact h246 G T M H S L hcfg.cs hcfg.single (Or.inl ⟨n, hcfg.one_lt, hcfg.lin2⟩)
    · intro g hg
      rw [← conjR_eq_self_iff] at hg ⊢
      rw [← hQL', ← conjR_pCoreOf, hg]
  have h3 : centerOf L ≠ ⊥ → fusionIsTI (centerOf L) ∧
      Subgroup.normalizer (pCoreOf 2 H : Set G) = Subgroup.normalizer (centerOf L : Set G) := by
    intro hZ
    have hI := hcore G T M H S L D n hcfg hZ
    obtain ⟨x, hxT, hxS⟩ := hcfg.exists_mem_T_not_mem_S
    obtain ⟨hDx, hreg⟩ := h4 x hxT hxS
    rcases hreg with hbot | ⟨-, -, hAR⟩
    · exact absurd hbot hZ
    obtain ⟨v, hv⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
    have hv1 : (v : G) ≠ 1 := fun e => hv (Subtype.ext e)
    have hII : Subgroup.normalizer (centerOf L : Set G) ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
      intro g hg
      have hvg : g⁻¹ * (v : G) * g ∈ centerOf L := by
        have := (Subgroup.mem_normalizer_iff''.1 hg (v : G)).1 v.2
        exact this
      have hvg1 : g⁻¹ * (v : G) * g ≠ 1 := by
        intro e
        apply hv1
        have := congrArg (fun w => g * w * g⁻¹) e
        simpa [mul_assoc] using this
      obtain ⟨b, hb, hbv⟩ := hAR.2.1 (v : G) ⟨v.2, hv1⟩ _ ⟨hvg, hvg1⟩
      have hgb : g * b⁻¹ ∈ Subgroup.centralizer ({(v : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (g * b⁻¹) * (v : G) = g * (b⁻¹ * (v : G) * b) * b⁻¹ := by group
          _ = g * (g⁻¹ * (v : G) * g) * b⁻¹ := by rw [hbv]
          _ = (v : G) * (g * b⁻¹) := by group
      have h1 : g * b⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
        hI v v.2 hv1 hgb
      have h2 : b ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := hN ▸ hDx hb
      have : g = (g * b⁻¹) * b := by group
      rw [this]
      exact Subgroup.mul_mem _ h1 h2
    have hNZ : Subgroup.normalizer (pCoreOf 2 H : Set G) =
        Subgroup.normalizer (centerOf L : Set G) := by
      refine le_antisymm ?_ hII
      intro g hg
      rw [← conjR_eq_self_iff]
      exact centerOf_normalized (hN ▸ hg)
    refine ⟨?_, hNZ⟩
    refine fusionIsTI_of_centralizer_le hNZ.symm (fun u hu hu1 => hI u hu hu1) ?_
    intro u hu g hug
    by_cases hu1 : u = 1
    · exact ⟨1, one_mem _, by simp [hu1]⟩
    have hu'1 : g⁻¹ * u * g ≠ 1 := by
      intro e
      apply hu1
      have := congrArg (fun w => g * w * g⁻¹) e
      simpa [mul_assoc] using this
    obtain ⟨b, hb, hbu⟩ := hAR.2.1 u ⟨hu, hu1⟩ _ ⟨hug, hu'1⟩
    exact ⟨b, hN ▸ hDx hb, hbu.symm⟩
  refine ⟨hN, ?_, fun hZ => h3 hZ⟩
  intro X hLX hP
  by_contra hXN
  set P := pCoreOf 2 X with hPdef
  set Q := pCoreOf 2 H with hQdef
  have hXP : X ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  have hP2 : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X
  have hLN : L ≤ Subgroup.normalizer (Q : Set G) := by rw [hN]; exact Subgroup.le_normalizer
  have hQLle : Q ≤ L := by
    rw [← hQL']
    exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L
  have hsig : IsSignalizer (Subgroup.normalizer (Q : Set G)) L
      (P ⊓ Subgroup.normalizer (Q : Set G)) :=
    ⟨inf_le_right, hP2.to_inf_left, fun g hg =>
      A4.mem_normalizer_inf (hXP (hLX hg)) (Subgroup.le_normalizer (hLN hg))⟩
  have hP₀Q : P ⊓ Subgroup.normalizer (Q : Set G) ≤ Q := hcfg.le_pCoreOf_of_isSignalizer hN hsig
  have hQNP : Q ≤ Subgroup.normalizer (P : Set G) := hQLle.trans (hLX.trans hXP)
  have hPQ : P ≤ Q := by
    by_contra hnle
    have hW2 : IsPGroup 2 (Q ⊔ P : Subgroup G) :=
      isPGroup_sup_of_le_normalizer_two hQNP (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
        hP2
    rw [sup_comm] at hW2
    have hlt : Q < P ⊔ Q :=
      lt_of_le_of_ne le_sup_right fun heq => hnle (le_sup_left.trans heq.ge)
    obtain ⟨w, hw, hwN, hwQ⟩ := A4.exists_mem_normalizer_not_mem hW2 hlt
    obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff_of_le_normalizer hQNP).1 hw
    have hpN : p ∈ Subgroup.normalizer (Q : Set G) := by
      have : p = (p * q) * q⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hwN (Subgroup.inv_mem _ (Subgroup.le_normalizer hq))
    exact hwQ (Q.mul_mem (hP₀Q ⟨hp, hpN⟩) hq)
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := hLX.trans hXP
  have hPU : P ≤ blockU L := by rw [hUH]; exact hPQ
  rcases le_blockZ_or_eq_blockU hcfg.short hQL hPU hLP with hPZ | hPU'
  · have hZc : blockZ L = centerOf L := blockZ_eq_centerOf hcfg.charTwo_L hQL
    rw [hZc] at hPZ
    have hZne : centerOf L ≠ ⊥ := fun hb => hP (le_bot_iff.1 (hb ▸ hPZ))
    obtain ⟨hTI, hNZ⟩ := h3 hZne
    apply hXN
    intro x hx
    have hPx : conjR P x = P := conjR_eq_self_iff.2 (hXP hx)
    have hne : centerOf L ⊓ conjR (centerOf L) x ≠ ⊥ := by
      intro hbot
      apply hP
      have hle : P ≤ centerOf L ⊓ conjR (centerOf L) x :=
        le_inf hPZ (hPx ▸ conjR_mono hPZ x)
      exact le_bot_iff.1 (hbot ▸ hle)
    have := conjR_eq_of_inf_ne_bot hTI hne
    rw [hNZ]
    exact conjR_eq_self_iff.1 this
  · apply hXN
    have : P = Q := hPU'.trans hUH
    rw [← this]
    exact hXP

end CFSG.QuasithinUnique.Lin2
