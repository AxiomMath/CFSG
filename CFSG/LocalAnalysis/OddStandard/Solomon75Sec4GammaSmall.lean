module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaBasic
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaElem
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaSub
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GenMain

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG CFSG.GH74.GLS

section Eight

theorem gamma_two_eq_top_eight
    {K : Type} [Group K] [Finite K] (hK : IsDoubleCoverOfAlt K 8) (S : Sylow 2 K) :
    properTwoGenCoreGamma (S : Subgroup K) 2 = ⊤ := by
  have h := normalizers_generate_eight_of_certificate hK S
  rw [eq_top_iff, ← h]
  refine iSup_le fun E => iSup_le fun hEJ => iSup_le fun _ => iSup_le fun hr => ?_
  refine normalizer_le_gamma (hEJ.trans ?_) hr
  exact sSup_le fun E hE => hE.1

theorem le_gamma_of_sylow_subcover
    {K : Type} [Group K] [Finite K] {L : Subgroup K} (hL : IsDoubleCoverOfAlt ↥L 8)
    (B : Sylow 2 ↥L) {S : Subgroup K} (hBS : (B : Subgroup ↥L).map L.subtype ≤ S) :
    L ≤ properTwoGenCoreGamma S 2 := by
  have h := gamma_map_subtype_le hBS
  rwa [gamma_two_eq_top_eight hL B, Subgroup.map_top, Subgroup.range_subtype] at h

end Eight

section Nine

variable {K : Type} [Group K]

theorem eq_comap_altEmb {n m : ℕ} {C : CoverSetup n K} {e : Fin m ↪ Fin n} {L : Subgroup K}
    (hmap : L.map C.ρ = altEmb e) (hcen : center K ≤ L) : L = (altEmb e).comap C.ρ := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_comap, ← hmap]
    exact ⟨x, hx, rfl⟩
  · intro x hx
    rw [Subgroup.mem_comap, ← hmap] at hx
    obtain ⟨l, hl, hlx⟩ := hx
    have hxl : x * l⁻¹ ∈ center K := by
      rw [← C.ρ_eq_one_iff, map_mul, map_inv, ← hlx, mul_inv_cancel]
    have hx' : x = (x * l⁻¹) * l := by group
    rw [hx']
    exact L.mul_mem (hcen hxl) hl

theorem range_succAboveEmb {n : ℕ} (i : Fin (n + 1)) :
    Set.range (Fin.succAboveEmb i) = {i}ᶜ := Fin.range_succAbove i

theorem comap_altEmb_succAbove (C : CoverSetup 9 K) (i : Fin 9) :
    (altEmb (Fin.succAboveEmb i)).comap C.ρ =
      (MulAction.stabilizer (Perm (Fin 9)) i).comap C.ρ := by
  ext x
  simp only [Subgroup.mem_comap, mem_altEmb_iff, MulAction.mem_stabilizer_iff, Perm.smul_def,
    range_succAboveEmb, Set.mem_compl_iff, Set.mem_singleton_iff, not_not]
  constructor
  · rintro ⟨h, -⟩
    exact h i rfl
  · intro h
    exact ⟨fun y hy => hy ▸ h, C.sign_ρ x⟩

theorem factorization_two_factorial_eight : (Nat.factorial 8).factorization 2 = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.factorization_def _ Nat.prime_two, padicValNat_factorial (b := 5) (by norm_num)]
  decide

theorem factorization_two_factorial_nine : (Nat.factorial 9).factorization 2 = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.factorization_def _ Nat.prime_two, padicValNat_factorial (b := 5) (by norm_num)]
  decide

theorem fixes_point_of_mem_normalizer_nine [Finite K] (C : CoverSetup 9 K) {T : Subgroup K}
    {i : Fin 9} (hTfix : ∀ x ∈ T, C.ρ x i = i) (hT : 2 ≤ Open.pRank 2 T) :
    ∀ g ∈ normalizer (T : Set K), C.ρ g i = i := by
  obtain ⟨x, hxT, hx1, hx2, h8⟩ := C.exists_involution_of_two_le_pRank (by norm_num) hT
  intro g hg
  have hcard : (C.ρ x).support.card = 8 := by
    have h1 : (C.ρ x).support.card ≤ 9 := by
      simpa using Finset.card_le_univ (C.ρ x).support
    have h2 : (C.ρ x).support.card ≠ 0 := fun h => hx1 (Equiv.Perm.card_support_eq_zero.1 h)
    obtain ⟨c, hc⟩ := h8
    omega
  have huniq : ∀ y, C.ρ x y = y → C.ρ x i = i → y = i := by
    intro y hy hyi
    by_contra hne
    have hsub : (C.ρ x).support ⊆ ({i, y} : Finset (Fin 9))ᶜ := by
      intro z hz
      rw [Perm.mem_support] at hz
      simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hz (h ▸ hyi), fun h => hz (h ▸ hy)⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_compl, Finset.card_pair (Ne.symm hne), hcard] at this
    simp at this
  have hconj : g * x * g⁻¹ ∈ T := (mem_normalizer_iff.1 hg x).1 hxT
  have h1 := hTfix _ hconj
  rw [map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply] at h1
  have h2 : C.ρ x ((C.ρ g)⁻¹ i) = (C.ρ g)⁻¹ i := by
    apply (C.ρ g).injective
    simpa using h1
  have h3 := huniq _ h2 (hTfix x hxT)
  exact ((Perm.inv_eq_iff_eq).1 h3).symm

theorem exists_point_gamma_eq_stabilizer
    [Finite K] (C : CoverSetup 9 K) (S : Sylow 2 K) :
    ∃ i : Fin 9, properTwoGenCoreGamma (S : Subgroup K) 2 =
        (MulAction.stabilizer (Perm (Fin 9)) i).comap C.ρ ∧
      IsDoubleCoverOfAlt ↥((MulAction.stabilizer (Perm (Fin 9)) i).comap C.ρ) 8 := by
  set i₀ : Fin 9 := Fin.last 8 with hi₀
  obtain ⟨L₀, hL₀, hmap₀, hcen₀⟩ := exists_doubleCover_altEmb (n := 9) (m := 8) (by norm_num)
    (by norm_num) C (Fin.succAboveEmb i₀)
  have hL₀eq : L₀ = (altEmb (Fin.succAboveEmb i₀)).comap C.ρ := eq_comap_altEmb hmap₀ hcen₀
  obtain ⟨S₁⟩ : Nonempty (Sylow 2 ↥L₀) := inferInstance
  have hLcard : Nat.card ↥L₀ = Nat.factorial 8 := card_K_eq (by norm_num) hL₀
  have hKcard : Nat.card K = Nat.factorial 9 := card_K_eq (by norm_num) C.hX
  have hPcard : Nat.card ((S₁ : Subgroup ↥L₀).map L₀.subtype) =
      2 ^ (Nat.card K).factorization 2 := by
    rw [Subgroup.card_map_of_injective L₀.subtype_injective, S₁.card_eq_multiplicity, hLcard,
      hKcard, factorization_two_factorial_eight, factorization_two_factorial_nine]
  let P : Sylow 2 K := Sylow.ofCard _ hPcard
  have hPcoe : (P : Subgroup K) = (S₁ : Subgroup ↥L₀).map L₀.subtype := rfl
  have hΓP : properTwoGenCoreGamma (P : Subgroup K) 2 = L₀ := by
    apply le_antisymm
    · unfold properTwoGenCoreGamma
      refine iSup_le fun T => iSup_le fun hTP => iSup_le fun hT => ?_
      have hTL : T ≤ L₀ := by
        intro x hx
        rw [hPcoe] at hTP
        obtain ⟨s, -, rfl⟩ := hTP hx
        exact s.2
      have hTfix : ∀ x ∈ T, C.ρ x i₀ = i₀ := by
        intro x hx
        have : C.ρ x ∈ altEmb (Fin.succAboveEmb i₀) := by
          rw [← hmap₀]
          exact ⟨x, hTL hx, rfl⟩
        exact this.1 i₀ (by simp)
      intro g hg
      rw [hL₀eq, Subgroup.mem_comap, mem_altEmb_iff]
      refine ⟨fun y hy => ?_, C.sign_ρ g⟩
      have hy' : y = i₀ := by simpa [range_succAboveEmb] using hy
      rw [hy']
      exact fixes_point_of_mem_normalizer_nine C hTfix hT g hg
    · exact le_gamma_of_sylow_subcover hL₀ S₁ (S := (P : Subgroup K)) (by rw [hPcoe])
  obtain ⟨g, hg⟩ := exists_sylow_map_conj_eq P S
  refine ⟨C.ρ g i₀, ?_, ?_⟩
  · rw [hg, gamma_conj, hΓP, hL₀eq, comap_altEmb_succAbove]
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Perm.smul_def, map_mul, map_inv,
      Perm.mul_apply]
    rw [Perm.inv_eq_iff_eq]
  · obtain ⟨L, hL, hmap, hcen⟩ := exists_doubleCover_altEmb (n := 9) (m := 8) (by norm_num)
      (by norm_num) C (Fin.succAboveEmb (C.ρ g i₀))
    rw [← comap_altEmb_succAbove, ← eq_comap_altEmb hmap hcen]
    exact hL

end Nine

end CFSG.OddStandard.Solomon75.AhatData
