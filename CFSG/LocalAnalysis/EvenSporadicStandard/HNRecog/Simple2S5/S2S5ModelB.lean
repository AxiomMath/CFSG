module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5DDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step10
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step6
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Transport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.HNRecog

theorem yK_eq_closure {k : ℕ} (hk : k < 2) :
    yK k = Subgroup.closure ({yOne k, yTwo k} : Set (Equiv.Perm (Fin 1408))) := by
  have hl : ykWords.getD k [] = [yWord k 0, yWord k 1] := by
    interval_cases k <;> decide +kernel
  have hset : (elemW '' {w | w ∈ ([yWord k 0, yWord k 1] : List (List Nat))}) =
      ({yOne k, yTwo k} : Set (Equiv.Perm (Fin 1408))) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [Set.mem_setOf_eq, List.mem_cons, List.mem_nil_iff, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl
      · exact by simp [yOne]
      · exact by simp [yTwo]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨yWord k 0, by simp, rfl⟩
      · exact ⟨yWord k 1, by simp, rfl⟩
  show wSub (ykWords.getD k []) =
    Subgroup.closure ({yOne k, yTwo k} : Set (Equiv.Perm (Fin 1408)))
  rw [wSub, hl, hset]

theorem eq_stab_of_dFacts (hP : Nat.card ↥P1408 = 177408000)
    (hT : TFacts 0) (hD : DFacts) {S : Subgroup (Equiv.Perm (Fin 1408))}
    (hS : Good S (elemA * elemZ)) (hSP : S ≤ pPrime) (hA1 : elemA ≠ 1)
    (haS : S ⊓ Subgroup.zpowers elemA = ⊥) (hdvd : Nat.card ↥S ∣ 44352000)
    (hY : S ⊓ Subgroup.centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408))) = yK 0)
    (hSyl : IsSylow2In S (tSub 0)) {h : Equiv.Perm (Fin 1408)} (hhS : h ∈ S)
    (hh1 : h * (elemA * elemZ) * h⁻¹ = uElt 0)
    (hh2 : h * uElt 0 * h⁻¹ = elemA * elemZ ∨ h * uElt 0 * h⁻¹ = elemA * elemZ * uElt 0) :
    ∃ p : Fin 1408, S = P1408 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1408)) p := by
  have hYS : yK 0 ≤ S := by rw [← hY]; exact inf_le_left
  have hy1 : yOne 0 ∈ S := hYS (yOne_mem (by norm_num : (0 : ℕ) < 2))
  have hy2 : yTwo 0 ∈ S := hYS (yTwo_mem (by norm_num : (0 : ℕ) < 2))
  obtain ⟨j, hj, hjmem⟩ := hD.cover h (hSP hhS) hh1 hh2
  have hgjS : gElt j ∈ S := by
    have hinv : (gElt j)⁻¹ * h ∈ S := hYS hjmem
    have hmem : h * ((gElt j)⁻¹ * h)⁻¹ ∈ S := S.mul_mem hhS (S.inv_mem hinv)
    convert hmem using 1
    group
  have hjj : j = jStar := by
    by_contra hne
    have hkill := hD.killed j hj hne
    have hcl : Subgroup.closure ({yOne 0, yTwo 0, gElt j} : Set (Equiv.Perm (Fin 1408))) ≤ S := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hy1
      · exact hy2
      · exact hgjS
    have hmemA : elemA ∈ S ⊓ Subgroup.zpowers elemA :=
      ⟨hcl hkill, Subgroup.mem_zpowers elemA⟩
    rw [haS, Subgroup.mem_bot] at hmemA
    exact hA1 hmemA
  have hgjstarS : gElt jStar ∈ S := by simpa [hjj] using hgjS
  have hWS : wGroup ≤ S := by
    rw [wGroup, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hy1
    · exact hy2
    · exact hgjstarS
  obtain ⟨p, hp1, hp2, hp3⟩ := hD.fix
  have hWStab : wGroup ≤ P1408 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1408)) p := by
    rw [wGroup, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_inf.mpr
        ⟨hS.le hy1, by rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]; exact hp1⟩
    · exact Subgroup.mem_inf.mpr
        ⟨hS.le hy2, by rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]; exact hp2⟩
    · exact Subgroup.mem_inf.mpr
        ⟨hS.le hgjstarS, by rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]; exact hp3⟩
  have hcardStab :
      Nat.card ↥(P1408 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1408)) p) = 126000 := by
    obtain ⟨e⟩ := nonempty_mulEquiv_u0_of_eq_stab
      (S₁ := P1408 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1408)) p) (p := p) rfl
    rw [Nat.card_congr e.toEquiv, card_u0 hP]
  have h16 : 16 ∣ Nat.card ↥wGroup := by
    have hyKleW : yK 0 ≤ wGroup := by
      rw [yK_eq_closure (by norm_num : (0 : ℕ) < 2), wGroup]
      apply Subgroup.closure_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    have hle : tSub 0 ≤ wGroup := (tSub_le_yK 0).trans hyKleW
    have h := Subgroup.card_dvd_of_le hle
    rwa [hT.card_T] at h
  obtain ⟨Q7, hQ7le, hQ7card⟩ := hD.sylow7
  obtain ⟨Q9, hQ9le, hQ9card⟩ := hD.sylow9
  obtain ⟨Q125, hQ125le, hQ125card⟩ := hD.sylow125
  have h7 : 7 ∣ Nat.card ↥wGroup := by
    rw [← hQ7card]; exact Subgroup.card_dvd_of_le hQ7le
  have h9 : 9 ∣ Nat.card ↥wGroup := by
    rw [← hQ9card]; exact Subgroup.card_dvd_of_le hQ9le
  have h125 : 125 ∣ Nat.card ↥wGroup := by
    rw [← hQ125card]; exact Subgroup.card_dvd_of_le hQ125le
  have hdvd126000 : 126000 ∣ Nat.card ↥wGroup := by
    have h169 : (16 * 9 : ℕ) ∣ Nat.card ↥wGroup :=
      (by decide : Nat.Coprime 16 9).mul_dvd_of_dvd_of_dvd h16 h9
    have h169125 : (16 * 9 * 125 : ℕ) ∣ Nat.card ↥wGroup :=
      (by decide : Nat.Coprime (16 * 9) 125).mul_dvd_of_dvd_of_dvd h169 h125
    have h : (16 * 9 * 125 * 7 : ℕ) ∣ Nat.card ↥wGroup :=
      (by decide : Nat.Coprime (16 * 9 * 125) 7).mul_dvd_of_dvd_of_dvd h169125 h7
    norm_num at h
    exact h
  have hWcard : Nat.card ↥wGroup = 126000 := by
    have hge : 126000 ≤ Nat.card ↥wGroup := Nat.le_of_dvd Nat.card_pos hdvd126000
    have hle : Nat.card ↥wGroup ≤
        Nat.card ↥(P1408 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1408)) p) :=
      Subgroup.card_le_of_le hWStab
    have hle' : Nat.card ↥wGroup ≤ 126000 := by rw [← hcardStab]; exact hle
    exact le_antisymm hle' hge
  have hWStab_eq : wGroup = P1408 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1408)) p :=
    Subgroup.eq_of_le_of_card_ge hWStab (by rw [hcardStab, hWcard])
  haveI : IsSimpleGroup ↥S := hS.simple
  have h2 : ∀ R : Subgroup (Equiv.Perm (Fin 1408)), R ≤ S → IsPGroup 2 ↥R →
      Nat.card ↥R ≤ 16 :=
    fun R hRS hR => hSyl.card_le_of_pGroup hT.card_T hRS hR
  have hWS_eq : wGroup = S := eq_of_card_eq hWS hWcard h2 hdvd
  exact ⟨p, hWS_eq.symm.trans hWStab_eq⟩

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
