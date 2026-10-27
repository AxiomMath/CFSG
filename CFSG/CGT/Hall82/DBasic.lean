module

public import CFSG.CGT.Hall82.DModelFacts
public import CFSG.CGT.Hall82.Psi
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G}

theorem pCoreOf_centralizer_eq_bot {L : Subgroup G}
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) = ⊥ := by
  rw [hC1]
  exact eq_bot_iff.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 ⊥)

theorem hW2_of_eq_bot (S : Setting G M L)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) := by
  intro Q _ hQ
  rw [hC1] at hQ
  rw [pCoreOf_centralizer_eq_bot hC1]
  exact hQ

theorem hWab_of_eq_bot (S : Setting G M L)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a := by
  intro a ha b hb
  rw [pCoreOf_centralizer_eq_bot hC1, Subgroup.mem_bot] at ha hb
  rw [ha, hb]

theorem blockU_le (S : Setting G M L) : blockU L ≤ M :=
  (S.blockU_le_blockQ.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).trans S.le

theorem pCoreOf_eq_blockU (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    CFSG.Open.pCoreOf 2 M = blockU L := by
  simp [S.pCoreOf_eq hF hc, pCoreOf_centralizer_eq_bot hC1]

theorem centralizer_blockU_eq_blockU (S : Setting G M L)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    Subgroup.centralizer (blockU L : Set G) = blockU L := by
  simp [S.centralizer_blockU_eq, hC1]

theorem psiM_eq_one_iff_mem_blockU (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) (m : ↥M) :
    S.psiM hc m = 1 ↔ (m : G) ∈ blockU L := by
  rw [S.psiM_eq_one_iff hc, S.centralizer_blockU_eq_blockU hC1]

theorem card_eq_card_inf_blockU_mul (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) {A : Subgroup G} (hA : A ≤ M) :
    Nat.card A = Nat.card ↥(A ⊓ blockU L) * Nat.card (S.psiSub hc A) := by
  have h := S.card_psiSub hc hA
  rw [S.centralizer_blockU_eq_blockU hC1] at h
  exact h

theorem psiSub_M_eq (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) :
    S.psiSub hc M = hexaL ∨ S.psiSub hc M = hexaM := by
  set K := S.psiSub hc M with hK
  have hLK : hexaL ≤ K := by
    rw [← S.psiSub_L hF hc]
    exact S.psiSub_mono hc S.le
  have hKM : K ≤ hexaM := S.psiSub_le_hexaM hc M
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hLK
  have hmpos : 0 < m := by
    have hpos : 0 < Nat.card K := Nat.card_pos
    rw [hm, hF.card] at hpos
    omega
  have hdvdm : m ∣ 2 := by
    have h := Subgroup.card_dvd_of_le hKM
    rw [hm, hF.card, hF.card_hexaM] at h
    rw [show (2160 : ℕ) = 1080 * 2 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 1080) h
  rcases Nat.prime_two.eq_one_or_self_of_dvd m hdvdm with hm1 | hm2
  · left
    apply hF.eq_of_card K hKM
    rw [hm, hm1, mul_one, hF.card]
  · right
    apply Subgroup.eq_of_le_of_card_ge hKM
    rw [hm, hF.card, hm2, hF.card_hexaM]

theorem exists_mem_L_psiM_eq (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    {x : Equiv.Perm (Fin 64)} (hx : x ∈ hexaL) :
    ∃ m : ↥M, (m : G) ∈ L ∧ S.psiM hc m = x := by
  have hx' : x ∈ S.psiSub hc L := by rwa [S.psiSub_L hF hc]
  rw [mem_psiSub S hc S.le] at hx'
  obtain ⟨l, hl, hlM, hψ⟩ := hx'
  exact ⟨⟨l, hlM⟩, hl, hψ⟩

theorem card_centralizer_rep (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥) (v : Fin 64) :
    Nat.card ↥(M ⊓ Subgroup.centralizer ({rep v} : Set G)) =
      64 * Nat.card (stabSub (S.psiSub hc M) v) := by
  set A : Subgroup G := M ⊓ Subgroup.centralizer ({rep v} : Set G) with hAdef
  have hA : A ≤ M := inf_le_left
  have hVA : blockU L ≤ A := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨S.blockU_le ha, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact S.blockU_comm (hc.mem v) ha
  have hAV : A ⊓ blockU L = blockU L :=
    le_antisymm inf_le_right (le_inf hVA le_rfl)
  have hψ : S.psiSub hc A = stabSub (S.psiSub hc M) v := by
    ext x
    rw [mem_psiSub S hc hA, stabSub, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      Equiv.Perm.smul_def]
    constructor
    · rintro ⟨a, haA, haM, rfl⟩
      have hcomm : a * rep v = rep v * a :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haA).2 (rep v)
          (by simp)).symm
      have hfix : S.psiM hc ⟨a, haM⟩ v = v := by
        refine (conj_rep_eq_iff S hc ⟨a, haM⟩ v).mp ?_
        calc a * rep v * a⁻¹ = rep v * a * a⁻¹ := by rw [hcomm]
          _ = rep v := by group
      refine ⟨?_, hfix⟩
      rw [mem_psiSub S hc (le_refl M)]
      exact ⟨a, (Subgroup.mem_inf.mp haA).1, haM, rfl⟩
    · rintro ⟨hxM, hxv⟩
      rw [mem_psiSub S hc (le_refl M)] at hxM
      obtain ⟨a, haM, haM', hψa⟩ := hxM
      have hfix : S.psiM hc ⟨a, haM'⟩ v = v := by
        rw [hψa]
        exact hxv
      have hconj : a * rep v * a⁻¹ = rep v :=
        (conj_rep_eq_iff S hc ⟨a, haM'⟩ v).mpr hfix
      have hcomm : a * rep v = rep v * a := by
        calc a * rep v = (a * rep v * a⁻¹) * a := by group
          _ = rep v * a := by rw [hconj]
      refine ⟨a, ?_, haM', hψa⟩
      refine Subgroup.mem_inf.mpr ⟨haM, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hcomm.symm
  have hcard := S.card_eq_card_inf_blockU_mul hc hC1 hA
  rw [hAV, hψ] at hcard
  simpa [hAdef, S.card_blockU] using hcard

theorem rep_mul_self (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (v : Fin 64) :
    rep v * rep v = 1 := by
  have h := hc.add v v
  rw [xorF_self, hc.rep_zero] at h
  exact h.symm

theorem rep_eq_one_iff (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {v : Fin 64} :
    rep v = 1 ↔ v = 0 := by
  constructor
  · intro h
    rw [← hc.rep_zero] at h
    exact hc.inj h
  · rintro rfl
    exact hc.rep_zero

theorem mem_blockU_iff (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) {x : G} :
    x ∈ blockU L ↔ ∃ v, rep v = x := by
  constructor
  · intro hx
    exact hc.surj x hx
  · rintro ⟨v, rfl⟩
    exact hc.mem v

theorem psiM_xorF (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (m : ↥M) (v w : Fin 64) :
    S.psiM hc m (xorF v w) = xorF (S.psiM hc m v) (S.psiM hc m w) := by
  apply hc.inj
  rw [S.rep_psiM hc m (xorF v w), hc.add v w,
    hc.add (S.psiM hc m v) (S.psiM hc m w), S.rep_psiM hc m v, S.rep_psiM hc m w]
  group

theorem psiM_zero (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) (m : ↥M) :
    S.psiM hc m 0 = 0 := by
  have h := S.psiM_xorF hc m 0 0
  simpa [xorF_self] using h

end CFSG.CGT.Hall82.Setting
