module

public import CFSG.LocalAnalysis.RankThreeUC.K37HBGlue
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Dickson.I271

variable {X : Type} [Group X] [Finite X]

theorem k37b_inf_primeCore_eq_bot {K E S : Subgroup X} (h : K37Setting X K E S) :
    K ⊓ GLAPPrimeCore 3 X = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := GLAPPrimeCore 3 X
  haveI hRn : R.Normal := GLAPPrimeCore.normal 3 X
  have hN : (R.subgroupOf K).Normal := hRn.subgroupOf K
  have hcopR : Nat.Coprime 3 (Nat.card R) := CFSG.pPrimeCore_coprime_card
  have hcop : Nat.Coprime 3 (Nat.card (R.subgroupOf K)) := by
    refine Nat.Coprime.coprime_dvd_right ?_ hcopR
    rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : R.subgroupOf K ≤ CFSG.pPrimeCore 3 ↥K := le_sSup ⟨hN, hcop⟩
  rw [h.core] at hle
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxR⟩
  have h1 := hle (show (⟨x, hxK⟩ : ↥K) ∈ R.subgroupOf K from hxR)
  exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 h1))

theorem k37b_mem_centralizer_of_map {K E S : Subgroup X} (h : K37Setting X K E S) {x : X}
    (hx : QuotientGroup.mk' (GLAPPrimeCore 3 X) x ∈
      Subgroup.centralizer ((K.map (QuotientGroup.mk' (GLAPPrimeCore 3 X)) : Subgroup _) :
        Set (X ⧸ GLAPPrimeCore 3 X))) :
    x ∈ Subgroup.centralizer (K : Set X) := by
  haveI hRn : (GLAPPrimeCore 3 X).Normal := GLAPPrimeCore.normal 3 X
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 X)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hcomm : π k * π x = π x * π k :=
    Subgroup.mem_centralizer_iff.1 hx (π k) (Subgroup.mem_map_of_mem _ hk)
  have hc1 : x * k * x⁻¹ * k⁻¹ ∈ K :=
    Subgroup.mul_mem _ (h.normal.conj_mem k hk x) (Subgroup.inv_mem _ hk)
  have hc2 : x * k * x⁻¹ * k⁻¹ ∈ GLAPPrimeCore 3 X := by
    have h1 : π (x * k * x⁻¹ * k⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    exact (QuotientGroup.eq_one_iff _).1 h1
  have h2 : x * k * x⁻¹ * k⁻¹ ∈ K ⊓ GLAPPrimeCore 3 X := ⟨hc1, hc2⟩
  rw [k37b_inf_primeCore_eq_bot h, Subgroup.mem_bot] at h2
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)).symm

theorem k37b_quot {K E S : Subgroup X} (h : K37Setting X K E S) (h3 : 3 ∣ Nat.card K) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (K' B' : Subgroup Y), Nonempty (↥K ≃* ↥K') ∧
      CFSG.Open.IsKGroup Y ∧ GLAPPrimeCore 3 Y = ⊥ ∧ GLAPComponent 3 ⊤ K' ∧ IsSCp 3 ⊤ B' ∧
      B' ≤ Subgroup.normalizer (K' : Set Y) ∧ 9 ≤ autOrderIn B' K' ∧
      (IsStronglyBalancedIn 3 B' K' → S ≤ Subgroup.centralizer (K : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B, hB, hEB, hBS⟩ := k37b_exists_scp h
  haveI hRn : (GLAPPrimeCore 3 X).Normal := GLAPPrimeCore.normal 3 X
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 X)
  have hKR := k37b_inf_primeCore_eq_bot h
  have hψ : Function.Injective (π.comp K.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have h1 : (k : X) ∈ K ⊓ GLAPPrimeCore 3 X :=
      ⟨k.2, (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hk)⟩
    rw [hKR, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hrange : (π.comp K.subtype).range = K.map π := by
    ext y
    simp only [MonoidHom.mem_range, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.mem_map,
      Subtype.exists, exists_prop]
  let φ : ↥K ≃* ↥(K.map π) :=
    (MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange)
  have hKn : (K.map π).Normal := h.normal.map π (QuotientGroup.mk'_surjective _)
  have hq : CFSG.Open.IsQuasisimple ↥(K.map π) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv φ.symm (k37b_isQuasisimple h)
  have hcardK : Nat.card (K.map π) = Nat.card K := (Nat.card_congr φ.toEquiv).symm
  have hRc : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hall : ∀ T : Subgroup (X ⧸ GLAPPrimeCore 3 X),
      T ≤ Subgroup.normalizer ((K.map π : Subgroup _) : Set (X ⧸ GLAPPrimeCore 3 X)) := fun T => by
    rw [Subgroup.normalizer_eq_top_iff.2 hKn]
    exact le_top
  refine ⟨X ⧸ GLAPPrimeCore 3 X, inferInstance, inferInstance, K.map π, B.map π, ⟨φ⟩, ?_,
    glaPPrimeCore_quotient_eq_bot Nat.prime_three, ?_, isSCp_map_quotient _ hRc hB, hall _, ?_, ?_⟩
  · exact CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.1 (h.catalog.quotient _)
  · exact glaPComponent_of_normal Nat.prime_three hq (hcardK ▸ h3) le_top (hKn.subgroupOf ⊤)
  · have h1 := k37b_inf_centralizer_eq_bot h
    have h4 := k37b_card_le_autOrderIn (hall _) (A := E) (fun e => π e.1)
      (fun e => Subgroup.mem_map_of_mem π (hEB e.2)) (fun a b hab => by
        have hab' : π ((a : X)⁻¹ * b) ∈
            Subgroup.centralizer ((K.map π : Subgroup _) : Set (X ⧸ GLAPPrimeCore 3 X)) := by
          rw [map_mul, map_inv]
          exact hab
        have h3 : (a : X)⁻¹ * b ∈ E ⊓ Subgroup.centralizer (K : Set X) :=
          ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ a.2) b.2, k37b_mem_centralizer_of_map h hab'⟩
        rw [h1, Subgroup.mem_bot] at h3
        exact Subtype.ext (inv_mul_eq_one.1 h3))
    rwa [h.card] at h4
  · intro hbal s hs
    have hcop : Nat.Coprime 3 (Nat.card (S.map π)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd S π) (k37b_coprime_card h)
    have hnorm : B.map π ⊓ Subgroup.normalizer
        ((K.map π : Subgroup _) : Set (X ⧸ GLAPPrimeCore 3 X)) ≤
        Subgroup.normalizer ((S.map π : Subgroup _) : Set (X ⧸ GLAPPrimeCore 3 X)) :=
      inf_le_left.trans ((Subgroup.map_mono hBS).trans (Subgroup.le_normalizer_map π))
    exact k37b_mem_centralizer_of_map h (hbal (S.map π) (hall _) hcop hnorm
      (Subgroup.mem_map_of_mem π hs))

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
