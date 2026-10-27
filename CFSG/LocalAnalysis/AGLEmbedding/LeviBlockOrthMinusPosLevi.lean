module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusVoid
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusPosCover
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusPosIndex
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusPosSylow
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockTargets

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail LeviBlock

theorem LeviBlock.idxTwistedD_of_at {c : ℕ} {d : TauCeti.LieTypeIndex} (hd : IdxTwistedDAt c d) :
    IdxTwistedD d := by
  cases d with
  | twistedD r₀ q => exact hd.1
  | _ => exact hd.elim

theorem LeviBlock.exists_eq_twistedD_of_at {c : ℕ} {d : TauCeti.LieTypeIndex}
    (hd : IdxTwistedDAt c d) : ∃ r₀ q, d = .twistedD r₀ q ∧ q.p = 2 ∧ q.card = c := by
  cases d with
  | twistedD r₀ q => exact ⟨r₀, q, rfl, hd⟩
  | _ => exact hd.elim

theorem kFactCompParabLeviU42On_twistedD_two (hZ : OddCenterRest) :
    KFactCompParabLeviU42On (IsLieOf (IdxTwistedDAt 2)) := by
  intro Y _ _ L P hCP hC _ O W hOP hPO hO3 hWP hPWO _ _ d' ψ hd' hψ _ hsyl
  obtain ⟨dI, hdI, ⟨e⟩⟩ := hC
  obtain ⟨n, q, hdq, hqp, hqc⟩ := LeviBlock.exists_eq_twistedD_of_at hdI
  obtain ⟨K, _, _, _, b, c, r, s, d, ρ, hr, hirr, hd, hρ, hq, hZ1⟩ :=
    LeviBlock.exists_orthCover_rank_of_twistedD hZ hCP dI (LeviBlock.idxTwistedD_of_at hdI) e
  obtain ⟨hK, rfl⟩ := hq n q hdq
  rw [hqc] at hK
  have : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := LeviBlock.finite_orthLinearEquiv
  obtain ⟨hcard, hsimp⟩ := LeviBlock.catGroup_u42_facts hd'
  have : Finite (CatGroup d') := Finite.of_surjective ψ hψ
  have hnc : ∃ a b : CatGroup d', a * b ≠ b * a :=
    ThreeFives.exists_noncomm_of_simple hsimp (by rw [hcard]; norm_num)
  have hQ := LeviBlock.hasLeviBlocks_orthParab_blocks hd hr hirr
  rw [← hρ] at hQ
  have hmem := card_mem_of_section hCP.parab.1 ρ.toMonoidHom ρ.surjective hQ hOP hPO hO3 hWP
    hPWO hnc (by rw [hcard]; norm_num) ψ hψ
  rw [hcard] at hmem
  obtain ⟨j, hjq, hj⟩ := hmem
  obtain ⟨-, ht, -⟩ := LeviBlock.eq_inr_of_orthLeviBlock_u42 (f := 1) (by rw [hK, pow_one])
    hirr hjq hj.symm
  have hP : Nat.card ↥(orthParab r (minusTailForm K b c) d) = Nat.card ↥P := by
    rw [← hρ]
    exact LeviBlock.card_comap_subgroupOf_of_mulEquiv hCP.parab.1 ρ
  have h5 : ¬ 3 ^ 5 ∣ Nat.card ↥P := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    intro h5
    obtain ⟨T⟩ : Nonempty (Sylow 3 ↥P) := inferInstance
    have hT := hsyl T
    rw [Sylow.card_eq_multiplicity] at hT
    have hfac : (Nat.card ↥P).factorization 3 = 4 := Nat.pow_right_injective (by norm_num) hT
    have := (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h5
    omega
  have h1 : ∀ l : Fin s, d l.succ - d l.castSucc = 1 := by
    intro l
    by_contra hne
    have hlt := hd.mono (Fin.castSucc_lt_succ (i := l))
    exact h5 (hP ▸ three_pow_five_dvd_card_orthParab hK hd hr hirr ht (l := l) (by omega))
  have hdv := LeviBlock.orthCuts_eq_val hd h1
  rw [hdv (Fin.last s), Fin.val_last] at ht
  obtain rfl : d = fun i : Fin (s + 1) => (i : ℕ) := funext hdv
  obtain rfl : r = s + 2 := by omega
  have hqe : q.exponent = 1 := by
    rw [TauCeti.PrimePower.card_def, hqp] at hqc
    exact Nat.pow_right_injective le_rfl (hqc.trans (pow_one 2).symm)
  right
  refine ⟨s + 3, dI, by omega, ⟨q, hqp, hqe, hdq⟩,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm.trans e⟩, ?_⟩
  rw [Subgroup.relIndex,
    ← Subgroup.index_comap_of_surjective _ (f := ρ.toMonoidHom) ρ.surjective, hρ]
  exact LeviBlock.index_orthParab_minus_two hK hirr s

theorem kFactCompParabLeviU42On_twistedD_all (hZ : OddCenterRest) :
    KFactCompParabLeviU42On (IsLieOf IdxTwistedD) :=
  kFactCompParabLeviU42On_twistedD_of_two hZ (kFactCompParabLeviU42On_twistedD_two hZ)

end CFSG.AGLEmbedding
