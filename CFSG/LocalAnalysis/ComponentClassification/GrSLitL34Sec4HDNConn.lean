module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDChain

public section

namespace CFSG.ComponentClassification.GrSLit.HeNormal

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit.HeDiag
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem held_equiv_of_sup_eq {K L : Subgroup X} (hLK : L ≤ K)
    (hsup : L ⊔ (pPrimeCore 2 ↥K).map K.subtype = K)
    (hidx : (pPrimeCore 2 ↥L).index = (pPrimeCore 2 ↥K).index)
    (e : L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He) :
    Nonempty (K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He) := by
  set g : ↥L →* ↥K ⧸ pPrimeCore 2 ↥K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (inclusion hLK) with hg
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) q
    have hk : (k : X) ∈ ((L ⊔ (pPrimeCore 2 ↥K).map K.subtype : Subgroup X) : Set X) := by
      rw [hsup]
      exact k.2
    rw [coe_mul_of_left_le_normalizer_right L _ (hLK.trans (le_normalizer_oddIn (L := K)))]
      at hk
    obtain ⟨l, hl, o, ⟨o', ho', hoo'⟩, hlo⟩ := hk
    refine ⟨⟨l, hl⟩, ?_⟩
    change ((⟨l, hLK hl⟩ : ↥K) : ↥K ⧸ pPrimeCore 2 ↥K) = (k : ↥K ⧸ pPrimeCore 2 ↥K)
    rw [QuotientGroup.eq]
    have h1 : (⟨l, hLK hl⟩ : ↥K)⁻¹ * k = o' := by
      apply Subtype.ext
      change l⁻¹ * (k : X) = (o' : X)
      rw [← hlo, ← hoo']
      simp
    rw [h1]
    exact ho'
  have hmap : g.ker.map (inclusion hLK) ≤ pPrimeCore 2 ↥K := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
  have hcop : Nat.Coprime 2 (Nat.card g.ker) := by
    have h1 := card_dvd_of_le hmap
    rw [card_map_of_injective (inclusion_injective hLK)] at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have hker : g.ker ≤ pPrimeCore 2 ↥L := by
    unfold pPrimeCore
    exact le_sSup ⟨MonoidHom.normal_ker g, hcop⟩
  set φ : ↥L ⧸ g.ker →* ↥L ⧸ pPrimeCore 2 ↥L :=
    QuotientGroup.map g.ker (pPrimeCore 2 ↥L) (MonoidHom.id _) (by simpa using hker) with hφ
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) q
    exact ⟨(l : ↥L ⧸ g.ker), rfl⟩
  let eK : ↥L ⧸ g.ker ≃* ↥K ⧸ pPrimeCore 2 ↥K := QuotientGroup.quotientKerEquivOfSurjective g hgs
  have hcard : Nat.card (↥L ⧸ g.ker) ≤ Nat.card (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [Nat.card_congr eK.toEquiv]
    exact le_of_eq hidx.symm
  exact ⟨(eK.symm.trans (MulEquiv.ofBijective φ (hφs.bijective_of_nat_card_le hcard))).trans e⟩

omit [Finite X] in
theorem mem_coreActionKernel_of_sup_eq {K L : Subgroup X} (hLK : L ≤ K)
    (hsup : L ⊔ (pPrimeCore 2 ↥K).map K.subtype = K) {a : X}
    (haN : a ∈ normalizer (K : Set X)) (haL : L ≤ centralizer ({a} : Set X)) :
    a ∈ coreActionKernel K := by
  refine mem_coreActionKernel.mpr ⟨haN, fun k hk => ?_⟩
  set O : Subgroup X := (pPrimeCore 2 ↥K).map K.subtype with hO
  have hk' : k ∈ ((L ⊔ O : Subgroup X) : Set X) := by
    rw [hO, hsup]
    exact hk
  rw [coe_mul_of_left_le_normalizer_right L O (hLK.trans (le_normalizer_oddIn (L := K)))] at hk'
  obtain ⟨l, hl, o, ho, rfl⟩ := hk'
  have haO : a ∈ normalizer (O : Set X) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic K (pPrimeCore 2 ↥K) haN
  have hal : Commute a⁻¹ l :=
    (Commute.inv_left (show Commute a l from (mem_centralizer_singleton_iff.mp (haL hl)).symm))
  have h1 : (l * o)⁻¹ * a⁻¹ * (l * o) * a = o⁻¹ * (a⁻¹ * o * a⁻¹⁻¹) := by
    calc (l * o)⁻¹ * a⁻¹ * (l * o) * a = o⁻¹ * (l⁻¹ * (a⁻¹ * l)) * o * a := by group
      _ = o⁻¹ * (l⁻¹ * (l * a⁻¹)) * o * a := by rw [hal.eq]
      _ = o⁻¹ * (a⁻¹ * o * a⁻¹⁻¹) := by group
  rw [h1]
  exact mul_mem (inv_mem ho) ((mem_normalizer_iff.mp (inv_mem haO) o).mp ho)

theorem card_inf_eq_of_normal
    {M K T : Subgroup X}
    (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He) (hKM : K ≤ M)
    (hKn : M ≤ normalizer (K : Set X)) (hTsyl : IsSylowTwoIn T M) :
    Nat.card ↥(T ⊓ K) = 1024 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 := hTsyl.isPGroup
  have hle : Nat.card ↥(T ⊓ K) ≤ 1024 := by
    rw [← card_imL (e := e₁) inf_le_right (hT2.to_le inf_le_left)]
    exact card_le_of_le_heP (imL_le_heP _) (isPGroup_imL e₁ inf_le_right (hT2.to_le inf_le_left))
  have hK : Nat.card K = Nat.card heP * Nat.card (pPrimeCore 2 ↥K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K),
      Nat.card_congr (e₁.trans heEquivP).toEquiv]
  have hdvd : 2 ^ 10 ∣ Nat.card K := by
    rw [hK, card_heP]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  set Q' : Subgroup X := Q.map K.subtype with hQ'
  have hQ'K : Q' ≤ K := map_subtype_le _
  have hQ'c : Nat.card Q' = 1024 := by
    rw [hQ', card_map_of_injective K.subtype_injective, hQ]
    norm_num
  have hQ'2 : IsPGroup 2 Q' := IsPGroup.of_card (n := 10) (by rw [hQ'c]; norm_num)
  obtain ⟨c, hcM, hcT⟩ := hTsyl.exists_conj_le (hQ'K.trans hKM) hQ'2
  have h1 : Q'.map (MulAut.conj c).toMonoidHom ≤ T ⊓ K := by
    rintro _ ⟨q, hq, rfl⟩
    exact mem_inf.mpr ⟨hcT q hq, (mem_normalizer_iff.mp (hKn hcM) q).mp (hQ'K hq)⟩
  have hge : 1024 ≤ Nat.card ↥(T ⊓ K) := by
    calc 1024 = Nat.card ↥(Q'.map (MulAut.conj c).toMonoidHom) := by
          rw [card_map_of_injective (MulAut.conj c).injective, hQ'c]
      _ ≤ Nat.card ↥(T ⊓ K) := card_le_of_le h1
  exact le_antisymm hle hge

section Sylow

variable {K T : Subgroup X} (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
  (h64 : HeldSylowElementarySixtyFour) (hOut : HeldOuterInvolutionRank) (hT2 : IsPGroup 2 T)
  (hTN : T ≤ normalizer (K : Set X)) (h1024 : Nat.card ↥(T ⊓ K) = 1024)
include e₁ h64 hOut hT2 hTN h1024

theorem isThreeConnected_of_normal : IsThreeConnected T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1024' : Nat.card ↥(T ⊓ normalizer (K : Set X) ⊓ K) = 1024 := by
    rw [inf_of_le_left hTN]
    exact h1024
  obtain ⟨E, hER, hRN, hEe, hE64⟩ := exists_elem_sixtyFour e₁ h64 inf_le_right
    (hT2.to_le inf_le_left) h1024
  set R : Subgroup X := T ⊓ K ⊔ T ⊓ coreActionKernel K with hR
  have hRT : R ≤ T := sup_le inf_le_left inf_le_left
  have hR2 : IsPGroup 2 ↥R := hT2.to_le hRT
  have hERR : E ≤ R := hER.trans le_sup_left
  have hRNE : R ≤ normalizer (E : Set X) :=
    sup_le hRN fun p hp => mem_normalizer_of_commute fun v hv =>
      (commute_of_mem_coreActionKernel hT2 (mem_inf.mp hp).1 (mem_inf.mp hp).2
        (mem_inf.mp (hER hv)).1 (mem_inf.mp (hER hv)).2).symm
  obtain ⟨ζ, hζ, hζ2, hζc⟩ := exists_central_involution hT2 (inf_le_left : T ⊓ K ≤ T)
    (le_normalizer_inf_left hTN) fun hbot => by
      rw [hbot, card_bot] at h1024
      omega
  have hconn : ∀ A : Subgroup X, A ≤ T → IsAbelianTwoOfRank 3 A →
      AbelianConnectedIn T 3 A E := by
    intro A hAT hA
    obtain ⟨F, hFA, hF, hF8⟩ := exists_isElemTwo_eight hA
    have hFT : F ≤ T := hFA.trans hAT
    have hFr : IsAbelianTwoOfRank 3 F := hF.isAbelianTwoOfRank (by omega)
    have hAF : AbelianConnectedIn T 3 A F :=
      ⟨hAT, hA, Relation.ReflTransGen.single ⟨hFT, hFr, fun x hx y hy => hA.2.1 x hx y (hFA hy)⟩⟩
    obtain ⟨A', hA'R, hA', hFA'⟩ : ∃ A' : Subgroup X, A' ≤ R ∧ IsAbelianTwoOfRank 3 A' ∧
        AbelianConnectedIn T 3 F A' := by
      by_cases hFK : ∀ x ∈ F, x ∈ K ⊔ coreActionKernel K
      · exact ⟨F, fun x hx => inf_sup_coreActionKernel_le' e₁ hTN hT2 h1024
          (mem_inf.mpr ⟨hFT hx, hFK x hx⟩), hFr, hFT, hFr, Relation.ReflTransGen.refl⟩
      · push Not at hFK
        obtain ⟨x, hxF, hxK⟩ := hFK
        obtain ⟨A', hA'K, hA', hc⟩ := exists_chain_outer e₁ hOut hT2 h1024'
          (mem_inf.mp hζ).1 hζ2 hζc (mem_sup_left (mem_inf.mp hζ).2)
          (fun f hf => mem_inf.mpr ⟨hFT hf, hTN (hFT hf)⟩) hF hF8 hxF hxK
        exact ⟨A', hA'K.trans le_sup_left, hA', hc⟩
    exact hAF.trans (hFA'.trans ((abelianConnectedIn_of_normal_elementary hR2 hERR hRNE hEe
      (by omega) hA'R hA').mono hRT))
  intro A B hAT hBT hA hB
  exact (hconn A hAT hA).trans (hconn B hBT hB).symm

theorem three_le_pRank_centralizer_of_sq {s : X} (hs : s ∈ T)
    (hss : s * s ∈ T ⊓ coreActionKernel K) :
    3 ≤ pRank 2 ↥(T ⊓ centralizer ({s} : Set X)) := by
  have hTK2 : IsPGroup 2 ↥(T ⊓ K) := hT2.to_le inf_le_left
  obtain ⟨E, hER, hRN, hEe, hE64⟩ := exists_elem_sixtyFour e₁ h64 inf_le_right hTK2 h1024
  by_cases hsLK : s ∈ K ⊔ coreActionKernel K
  · have hsTP := inf_sup_coreActionKernel_le' e₁ hTN hT2 h1024 (mem_inf.mpr ⟨hs, hsLK⟩)
    have hPT : T ⊓ coreActionKernel K ≤ normalizer ((T ⊓ K : Subgroup X) : Set X) :=
      (inf_le_left : T ⊓ coreActionKernel K ≤ T).trans (le_normalizer_inf_left hTN)
    have hsset : s ∈ ((T ⊓ K : Subgroup X) : Set X) *
        ((T ⊓ coreActionKernel K : Subgroup X) : Set X) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hPT]
      exact hsTP
    obtain ⟨t', ht', p', hp', rfl⟩ := hsset
    have hcomm : ∀ t ∈ T ⊓ K, ∀ p ∈ T ⊓ coreActionKernel K, t * p = p * t :=
      fun t ht p hp => commute_of_mem_coreActionKernel hT2 (mem_inf.mp hp).1 (mem_inf.mp hp).2
        (mem_inf.mp ht).1 (mem_inf.mp ht).2
    have ht'2 : t' * t' = 1 := by
      have h1 : t' * t' = (t' * p') * (t' * p') * (p' * p')⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc t' * t' * (p' * p') = t' * (t' * p') * p' := by group
          _ = t' * (p' * t') * p' := by rw [hcomm t' ht' p' hp']
          _ = t' * p' * (t' * p') := by group
      have h2 : t' * t' ∈ T ⊓ coreActionKernel K := by
        rw [h1]
        exact mul_mem hss (inv_mem (mul_mem hp' hp'))
      exact eq_one_of_mem_coreActionKernel e₁ hT2 (mul_mem (mem_inf.mp ht').1 (mem_inf.mp ht').1)
        (mul_mem (mem_inf.mp ht').2 (mem_inf.mp ht').2) (mem_inf.mp h2).2
    have hc := card_le_card_inf_centralizer_sq hEe (hRN ht') ht'2
    rw [hE64] at hc
    have h8 : 8 ≤ Nat.card ↥(E ⊓ centralizer ({t'} : Set X)) :=
      (le_card_of_le_card_sq (hEe.isPGroup.to_le inf_le_left)).2 (by omega)
    refine three_le_pRank_of_le (hEe.mono inf_le_left) h8 fun f hf => ?_
    obtain ⟨hfE, hft⟩ := mem_inf.mp hf
    refine mem_inf.mpr ⟨(mem_inf.mp (hER hfE)).1, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := mem_centralizer_singleton_iff.mp hft
    have h2 := hcomm f (hER hfE) p' hp'
    calc f * (t' * p') = f * t' * p' := by group
      _ = t' * f * p' := by rw [h1]
      _ = t' * (f * p') := by group
      _ = t' * (p' * f) := by rw [h2]
      _ = t' * p' * f := by group
  · obtain ⟨F, hFT, hFs, -, hFe, hF8⟩ := exists_outer_eight e₁ hOut inf_le_right hTK2 h1024
      (hTN hs) (le_normalizer_inf_left hTN hs) hsLK (mem_inf.mp hss).2 (one_mem _) (mul_one 1)
      (by group)
    exact three_le_pRank_of_le hFe (by omega) (le_inf (hFT.trans inf_le_left) hFs)

end Sylow

end CFSG.ComponentClassification.GrSLit.HeNormal
