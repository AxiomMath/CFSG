module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenLatCert
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParC4Group

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open Equiv CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

section Main

variable {n : ℕ}

theorem twoParLat_of_latCert {A : Subgroup (Perm (Fin n))} (c : LatCert (Perm (Fin n)))
    (hM : Subgroup.closure {g | g ∈ c.mGens} = A)
    (hTA : Subgroup.closure {g | g ∈ c.tGens} ≤ A) (hc : c.check RN.enc = true)
    (L₁ L₂ L₃ : List (Perm (Fin n))) (hlat : c.lat = [L₁, L₂, L₃])
    (sT sP sM : ℕ) (hsz : c.sizes = [sT, sP, sP, sM]) (hmsize : c.msize = sM)
    (m : ℕ) (hm : sP = sT * m) (hmodd : ¬ 2 ∣ m) (hsTP : sT < sP) (hsPM : sP < sM)
    (hT1 : ∀ g ∈ c.tGens, g ∈ L₁) (hT2 : ∀ g ∈ c.tGens, g ∈ L₂)
    (hL1A : Subgroup.closure {g | g ∈ L₁} ≤ A) (hL2A : Subgroup.closure {g | g ∈ L₂} ≤ A)
    (k : ℕ) (hexp1 : ∀ g ∈ L₁, g ^ 2 ^ k = 1) (hexp2 : ∀ g ∈ L₂, g ^ 2 ^ k = 1)
    (hdist : ∃ color2 : Fin n → ℕ, (∀ t ∈ L₂, ∀ p, color2 (t p) = color2 p) ∧
      ∃ g ∈ L₁, ∃ p, color2 (g p) ≠ color2 p)
    (hSyl : IsSylowTwoOf ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A) ⊤)
    (hov : ∀ Y : Subgroup ↥A, (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ Y →
      Y = ⊤ ∨ CharTwo Y) :
    TwoParLat ↥A ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A)
      ((Subgroup.closure {g | g ∈ L₁}).subgroupOf A)
      ((Subgroup.closure {g | g ∈ L₂}).subgroupOf A) := by
  classical
  subst hM
  set A := Subgroup.closure {g | g ∈ c.mGens} with hA
  set T0 : Subgroup (Perm (Fin n)) := Subgroup.closure {g | g ∈ c.tGens} with hT0
  set T : Subgroup ↥A := T0.subgroupOf A with hT
  set M1 : Subgroup (Perm (Fin n)) := Subgroup.closure {g | g ∈ L₁} with hM1
  set M2 : Subgroup (Perm (Fin n)) := Subgroup.closure {g | g ∈ L₂} with hM2
  set M3 : Subgroup (Perm (Fin n)) := Subgroup.closure {g | g ∈ L₃} with hM3
  set P₁ : Subgroup ↥A := M1.subgroupOf A with hP1
  set P₂ : Subgroup ↥A := M2.subgroupOf A with hP2
  have hcl := c.closedOK_of_check hc
  have hszOK := c.sizesOK_of_check hc
  have hlen : (c.tGens :: c.lat).length = 4 := by simp [hlat]
  have hmem0 : (c.tGens :: c.lat)[0]'(by omega) = c.tGens := rfl
  have hmem1 : (c.tGens :: c.lat)[1]'(by omega) = L₁ := by simp [hlat]
  have hmem2 : (c.tGens :: c.lat)[2]'(by omega) = L₂ := by simp [hlat]
  have hmem3 : (c.tGens :: c.lat)[3]'(by omega) = L₃ := by simp [hlat]
  have hcardT0 : Nat.card T0 = sT := by
    have := c.card_t (rawIsEnc n) hcl hszOK
    rw [hsz] at this
    exact this
  have hcardM1 : Nat.card M1 = sP := by
    have := c.card_member_idx (rawIsEnc n) hcl hszOK 1 (by omega)
    rw [hmem1, hsz] at this
    exact this
  have hcardM2 : Nat.card M2 = sP := by
    have := c.card_member_idx (rawIsEnc n) hcl hszOK 2 (by omega)
    rw [hmem2, hsz] at this
    exact this
  have hcardM3 : Nat.card M3 = sM := by
    have := c.card_member_idx (rawIsEnc n) hcl hszOK 3 (by omega)
    rw [hmem3, hsz] at this
    exact this
  have hcardA : Nat.card A = sM := by
    rw [c.card_m (rawIsEnc n) hcl hszOK, hmsize]
  have hcardSub : ∀ Mj : Subgroup (Perm (Fin n)), Mj ≤ A →
      Nat.card (Mj.subgroupOf A) = Nat.card Mj :=
    fun Mj h => Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have hcardT : Nat.card T = sT := by rw [hT, hcardSub T0 hTA, hcardT0]
  have hcardP1 : Nat.card P₁ = sP := by rw [hP1, hcardSub M1 hL1A, hcardM1]
  have hcardP2 : Nat.card P₂ = sP := by rw [hP2, hcardSub M2 hL2A, hcardM2]
  have hsTpos : 0 < sT := hcardT ▸ Nat.card_pos
  have hT0M1 : T0 ≤ M1 := by
    rw [hT0, Subgroup.closure_le]
    exact fun g hg => Subgroup.subset_closure (hT1 g hg)
  have hT0M2 : T0 ≤ M2 := by
    rw [hT0, Subgroup.closure_le]
    exact fun g hg => Subgroup.subset_closure (hT2 g hg)
  have hTP1 : T ≤ P₁ := fun x hx => Subgroup.mem_subgroupOf.2 (hT0M1 (Subgroup.mem_subgroupOf.1 hx))
  have hTP2 : T ≤ P₂ := fun x hx => Subgroup.mem_subgroupOf.2 (hT0M2 (Subgroup.mem_subgroupOf.1 hx))
  have hover : ∀ Y : Subgroup ↥A, T ≤ Y → ∃ Mj : Subgroup (Perm (Fin n)),
      ((Mj = T0 ∧ Nat.card Mj = sT) ∨ (Mj = M1 ∧ Nat.card Mj = sP) ∨
        (Mj = M2 ∧ Nat.card Mj = sP) ∨ (Mj = M3 ∧ Nat.card Mj = sM)) ∧ Mj ≤ A ∧
      Y = Mj.subgroupOf A := by
    intro Y hY
    obtain ⟨j, hj, hLA, hYL, hcardL⟩ := c.overgroup_cases_idx (rawIsEnc n) hc Y hY
    have hj4 : j < 4 := by omega
    interval_cases j
    · rw [hmem0] at hLA hYL hcardL
      rw [hsz] at hcardL
      exact ⟨_, Or.inl ⟨rfl, by simpa using hcardL⟩, hLA, hYL⟩
    · rw [hmem1] at hLA hYL hcardL
      rw [hsz] at hcardL
      exact ⟨_, Or.inr (Or.inl ⟨rfl, by simpa using hcardL⟩), hLA, hYL⟩
    · rw [hmem2] at hLA hYL hcardL
      rw [hsz] at hcardL
      exact ⟨_, Or.inr (Or.inr (Or.inl ⟨rfl, by simpa using hcardL⟩)), hLA, hYL⟩
    · rw [hmem3] at hLA hYL hcardL
      rw [hsz] at hcardL
      exact ⟨_, Or.inr (Or.inr (Or.inr ⟨rfl, by simpa using hcardL⟩)), hLA, hYL⟩
  have hnoN : ∀ (L : List (Perm (Fin n))) (hLA : Subgroup.closure {g | g ∈ L} ≤ A)
      (hTL : T0 ≤ Subgroup.closure {g | g ∈ L}) (hexp : ∀ g ∈ L, g ^ 2 ^ k = 1)
      (hcardL : Nat.card (Subgroup.closure {g | g ∈ L}) = sP),
      ¬ (Subgroup.closure {g | g ∈ L}).subgroupOf A ≤ Subgroup.normalizer (T : Set ↥A) := by
    intro L hLA hTL hexp hcardL hle
    set ML := Subgroup.closure {g | g ∈ L} with hML
    set PL := ML.subgroupOf A with hPL
    have hTPL : T ≤ PL := fun x hx =>
      Subgroup.mem_subgroupOf.2 (hTL (Subgroup.mem_subgroupOf.1 hx))
    have hnormal : (T.subgroupOf PL).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTPL).2 hle
    have hcardPL : Nat.card PL = sP := by rw [hPL, hcardSub ML hLA, hcardL]
    have hcardTP : Nat.card (T.subgroupOf PL) = sT := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTPL).toEquiv, hcardT]
    have hQ : Nat.card (↥PL ⧸ T.subgroupOf PL) = m := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf PL)
      rw [hcardPL, hcardTP, hm, mul_comm] at h1
      exact (Nat.eq_of_mul_eq_mul_right hsTpos h1).symm
    have hgen : ∀ g ∈ L, g ∈ T0 := by
      intro g hg
      have hgA : g ∈ A := hLA (Subgroup.subset_closure hg)
      have hgP : (⟨g, hgA⟩ : ↥A) ∈ PL := Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure hg)
      set x : ↥PL := ⟨⟨g, hgA⟩, hgP⟩ with hx
      have hpow : (QuotientGroup.mk x : ↥PL ⧸ T.subgroupOf PL) ^ 2 ^ k = 1 := by
        rw [← QuotientGroup.mk_pow]
        have : x ^ 2 ^ k = 1 := by
          apply Subtype.ext; apply Subtype.ext
          simpa using hexp g hg
        rw [this]; rfl
      have hd1 : orderOf (QuotientGroup.mk x : ↥PL ⧸ T.subgroupOf PL) ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one hpow
      have hd2 : orderOf (QuotientGroup.mk x : ↥PL ⧸ T.subgroupOf PL) ∣ m := by
        rw [← hQ]; exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime (2 ^ k) m :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hmodd)
      have h1 : orderOf (QuotientGroup.mk x : ↥PL ⧸ T.subgroupOf PL) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
      have hx1 : (QuotientGroup.mk x : ↥PL ⧸ T.subgroupOf PL) = 1 := orderOf_eq_one_iff.1 h1
      have hxT : x ∈ T.subgroupOf PL := (QuotientGroup.eq_one_iff x).1 hx1
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hxT)
    have hML_le : ML ≤ T0 := by
      rw [hML, Subgroup.closure_le]
      exact hgen
    have := Subgroup.card_le_of_le hML_le
    rw [hcardL, hcardT0] at this
    omega
  have hN : Subgroup.normalizer (T : Set ↥A) = T := by
    refine le_antisymm ?_ Subgroup.le_normalizer
    obtain ⟨Mj, hMj, hMA, hYM⟩ := hover _ (Subgroup.le_normalizer (H := T))
    rcases hMj with ⟨rfl, -⟩ | ⟨rfl, hc1⟩ | ⟨rfl, hc2⟩ | ⟨rfl, hc3⟩
    · exact hYM ▸ le_rfl
    · exact absurd (hYM ▸ le_rfl) (hnoN L₁ hL1A hT0M1 hexp1 hcardM1)
    · exact absurd (hYM ▸ le_rfl) (hnoN L₂ hL2A hT0M2 hexp2 hcardM2)
    · exfalso
      have hM3A : M3 = A := by
        have : Nat.card M3 = Nat.card A := by rw [hc3, hcardA]
        exact Subgroup.eq_of_le_of_card_ge hMA (le_of_eq this.symm)
      have hNtop : Subgroup.normalizer (T : Set ↥A) = ⊤ := by
        rw [hYM, hM3A, Subgroup.subgroupOf_self]
      exact hnoN L₁ hL1A hT0M1 hexp1 hcardM1 (by rw [hNtop]; exact le_top)
  have hatom : ∀ P : Subgroup ↥A, T ≤ P → Nat.card P = sP → ∀ Q, T ≤ Q → Q ≤ P → Q = T ∨ Q = P := by
    intro P hTP hcardP Q hTQ hQP
    obtain ⟨Mj, hMj, hMA, hQM⟩ := hover Q hTQ
    have hcQ : Nat.card Q = Nat.card Mj := by rw [hQM]; exact hcardSub Mj hMA
    have hdvd : Nat.card Q ∣ sP := hcardP ▸ Subgroup.card_dvd_of_le hQP
    rcases hMj with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · left
      exact (Subgroup.eq_of_le_of_card_ge hTQ (by rw [hcQ, h, hcardT])).symm
    · right
      exact Subgroup.eq_of_le_of_card_ge hQP (by rw [hcardP, hcQ, h])
    · right
      exact Subgroup.eq_of_le_of_card_ge hQP (by rw [hcardP, hcQ, h])
    · exfalso
      rw [hcQ, h] at hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  have hJ : P₁ ⊔ P₂ = ⊤ := by
    obtain ⟨Mj, hMj, hMA, hJM⟩ := hover (P₁ ⊔ P₂) (hTP1.trans le_sup_left)
    have hcJ : Nat.card (P₁ ⊔ P₂ : Subgroup ↥A) = Nat.card Mj := by
      rw [hJM]; exact hcardSub Mj hMA
    have hdvd : sP ∣ Nat.card Mj := hcJ ▸ hcardP1 ▸ Subgroup.card_dvd_of_le le_sup_left
    have hdist' : P₁ ≠ P₂ := by
      intro hP12
      obtain ⟨color2, hc2, g, hgL, p, hp⟩ := hdist
      have hgA : g ∈ A := hL1A (Subgroup.subset_closure hgL)
      have hgP1 : (⟨g, hgA⟩ : ↥A) ∈ P₁ := Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure hgL)
      have hgP2 : (⟨g, hgA⟩ : ↥A) ∈ P₂ := hP12 ▸ hgP1
      exact hp (color_of_mem_closure color2 hc2 (Subgroup.mem_subgroupOf.1 hgP2) p)
    rcases hMj with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨hM3', h⟩
    · exfalso
      rw [h] at hdvd
      have := Nat.le_of_dvd hsTpos hdvd
      omega
    · exfalso
      have hP1J : P₁ = P₁ ⊔ P₂ :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcJ, h, hcardP1])
      have hP2P1 : P₂ ≤ P₁ := hP1J ▸ le_sup_right
      exact hdist' (Subgroup.eq_of_le_of_card_ge hP2P1 (by rw [hcardP1, hcardP2])).symm
    · exfalso
      have hP1J : P₁ = P₁ ⊔ P₂ :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcJ, h, hcardP1])
      have hP2P1 : P₂ ≤ P₁ := hP1J ▸ le_sup_right
      exact hdist' (Subgroup.eq_of_le_of_card_ge hP2P1 (by rw [hcardP1, hcardP2])).symm
    · rw [hJM]
      have hM3A : Mj = A := by
        have : Nat.card Mj = Nat.card A := by rw [h, hcardA]
        exact Subgroup.eq_of_le_of_card_ge hMA (le_of_eq this.symm)
      rw [hM3A, Subgroup.subgroupOf_self]
  have hpElt : ∀ (L : List (Perm (Fin n))) (hLA : Subgroup.closure {g | g ∈ L} ≤ A),
      (∀ g ∈ L, g ^ 2 ^ k = 1) →
      (Subgroup.closure {g | g ∈ L}).subgroupOf A ≤
        pElementSubgroup 2 ((Subgroup.closure {g | g ∈ L}).subgroupOf A) := by
    intro L hLA hexp
    set P := (Subgroup.closure {g | g ∈ L}).subgroupOf A with hP
    refine (Subgroup.map_le_map_iff_of_injective A.subtype_injective).1 ?_
    rw [hP, Subgroup.map_subgroupOf_eq_of_le hLA, Subgroup.closure_le]
    intro g hg
    have hgA : g ∈ A := hLA (Subgroup.subset_closure hg)
    have hgP : (⟨g, hgA⟩ : ↥A) ∈ P := Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure hg)
    obtain ⟨j, hj⟩ := exists_orderOf_two_pow (hexp g hg)
    refine ⟨⟨g, hgA⟩, Subgroup.subset_closure ⟨hgP, j, ?_⟩, rfl⟩
    rw [← hj, ← Subgroup.orderOf_coe]
  have hP1p := hpElt L₁ hL1A hexp1
  have hP2p := hpElt L₂ hL2A hexp2
  have hne : ∀ Q : Subgroup ↥A, T ≤ Q → Nat.card Q = sP → T < Q := by
    intro Q hTQ hcQ
    refine lt_of_le_of_ne hTQ fun h => ?_
    rw [h, hcQ] at hcardT
    omega
  have hdist' : P₁ ≠ P₂ := by
    intro hP12
    obtain ⟨color2, hc2, g, hgL, p, hp⟩ := hdist
    have hgA : g ∈ A := hL1A (Subgroup.subset_closure hgL)
    have hgP1 : (⟨g, hgA⟩ : ↥A) ∈ P₁ := Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure hgL)
    have hgP2 : (⟨g, hgA⟩ : ↥A) ∈ P₂ := hP12 ▸ hgP1
    exact hp (color_of_mem_closure color2 hc2 (Subgroup.mem_subgroupOf.1 hgP2) p)
  have hcardTop : Nat.card (⊤ : Subgroup ↥A) = sM := by rw [Subgroup.card_top, hcardA]
  have htop1 : P₁ ≠ ⊤ := fun h => by
    rw [h, hcardTop] at hcardP1
    omega
  have htop2 : P₂ ≠ ⊤ := fun h => by
    rw [h, hcardTop] at hcardP2
    omega
  refine ⟨hSyl, hN, hne _ hTP1 hcardP1, hne _ hTP2 hcardP2, hatom _ hTP1 hcardP1,
    hatom _ hTP2 hcardP2, hdist', htop1, htop2, ?_, hP1p, hP2p,
    (hov P₁ hTP1).resolve_left htop1, (hov P₂ hTP2).resolve_left htop2⟩
  intro Y hY
  obtain ⟨Mj, hMj, hMA, hYM⟩ := hover Y hY
  rcases hMj with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hc3⟩
  · exact Or.inl hYM
  · exact Or.inr (Or.inl hYM)
  · exact Or.inr (Or.inr (Or.inl hYM))
  · refine Or.inr (Or.inr (Or.inr ?_))
    have hM3A : M3 = A := by
      have : Nat.card M3 = Nat.card A := by rw [hc3, hcardA]
      exact Subgroup.eq_of_le_of_card_ge hMA (le_of_eq this.symm)
    rw [hYM, hM3A, Subgroup.subgroupOf_self]

end Main

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
