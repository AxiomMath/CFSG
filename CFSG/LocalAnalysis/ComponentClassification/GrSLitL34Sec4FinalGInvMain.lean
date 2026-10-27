module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGInv
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndG3

public section

namespace CFSG.ComponentClassification.GrSLit.FinalG

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem l34GraphInvertGlobalStep_of_actual
    {G : Type} [Group G] [Finite G] {a : G} {J S B : Subgroup G} {c : G}
    (hTr : L34EightTransvectionFact)
    (hJper : ⁅J, J⁆ = J)
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hS : IsSylowTwoIn S (normalizer (J : Set G)))
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S)
    (ha2 : orderOf a = 2) (haZ : a ∈ S ⊓ zStarIn J)
    (hZc : IsCyclic ↥(S ⊓ zStarIn J))
    (hZ4 : Nat.card ↥(S ⊓ zStarIn J) = 4)
    (hBP : B ≤ S ⊓ J) (hB8 : IsEightGroup B) (hBZ : B ⊓ zStarIn J = zpowers a)
    (hSN : S ≤ normalizer (B : Set G))
    (hAut : ∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B,
      n⁻¹ * (b : G) * n = (σ b : G))
    (hcS : c ∈ S) (hcc : c * c = 1) (hcW : c ∉ withKernel J)
    (hTc : S ⊓ centralizer (B : Set G) =
      S ⊓ J ⊓ centralizer (B : Set G) ⊔ zpowers c)
    (hmod : ∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), c * s * c * s ∈ zStarIn J) :
    (∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G),
        ∀ t ∈ S ⊓ J ⊓ centralizer (B : Set G), s * t = t * s) ∧
      ∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), c * s * c = s⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hS
  have hZJ : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  have hZJle : zStarIn J ≤ J := map_subtype_le _
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [inf_assoc, inf_eq_right.mpr hZJle]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have haB : a ∈ B := (le_of_eq hBZ.symm).trans inf_le_left (mem_zpowers a)
  have hSO : ∀ y ∈ S, y ∈ oddIn J → y = 1 := by
    intro y hyS hyO
    have hbot := eq_bot_of_le_two_group_of_le_odd hS2 (GrSLit.odd_card_map_pPrimeCore J)
      (inf_le_left : S ⊓ oddIn J ≤ S) inf_le_right
    have hy : y ∈ S ⊓ oddIn J := mem_inf.mpr ⟨hyS, hyO⟩
    rw [hbot] at hy
    exact hy
  have hZcent : ∀ z ∈ S ⊓ zStarIn J, ∀ y ∈ S ⊓ J, y * z = z * y := by
    intro z hz y hy
    have hzK : z ∈ coreActionKernel J := by
      have h := (mem_inf.mp hz).2
      rw [hZJ] at h
      exact (mem_inf.mp h).2
    have h1 := (mem_coreActionKernel.mp hzK).2 y (mem_inf.mp hy).2
    have h2 : y⁻¹ * z⁻¹ * y * z = 1 := hSO _ (mul_mem (mul_mem (mul_mem (inv_mem (mem_inf.mp hy).1)
      (inv_mem (mem_inf.mp hz).1)) (mem_inf.mp hy).1) (mem_inf.mp hz).1) h1
    calc y * z = z * (y * (y⁻¹ * z⁻¹ * y * z)) := by group
      _ = z * y := by rw [h2, mul_one]
  have hZT₁ : S ⊓ zStarIn J ≤ S ⊓ J ⊓ centralizer (B : Set G) := fun z hz =>
    mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hz).1, hZJle (mem_inf.mp hz).2⟩,
      mem_centralizer_iff.mpr fun b hb => hZcent z hz b (hBP hb)⟩
  have hBT₁ : B ≤ S ⊓ J ⊓ centralizer (B : Set G) := fun b hb =>
    mem_inf.mpr ⟨hBP hb, mem_centralizer_iff.mpr fun y hy => hB8.1.1 y hy b hb⟩
  have hT₁T : S ⊓ J ⊓ centralizer (B : Set G) ≤ S ⊓ centralizer (B : Set G) := fun t ht =>
    mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp ht).1).1, (mem_inf.mp ht).2⟩
  have hT₁S : ∀ {t : G}, t ∈ S ⊓ J ⊓ centralizer (B : Set G) → t ∈ S := fun ht =>
    (mem_inf.mp (mem_inf.mp ht).1).1
  have hT₁J : S ⊓ J ⊓ centralizer (B : Set G) ≤ J := fun _ ht => (mem_inf.mp (mem_inf.mp ht).1).2
  have hcT : c ∈ S ⊓ centralizer (B : Set G) := by
    rw [hTc]
    exact (le_sup_right : zpowers c ≤ _) (mem_zpowers c)
  have hcT₁ : c ∉ S ⊓ J ⊓ centralizer (B : Set G) := fun h =>
    hcW ((le_sup_left : J ≤ withKernel J) (hT₁J h))
  have hδ : ∀ t ∈ S ⊓ J ⊓ centralizer (B : Set G), c * t * c * t ∈ S ⊓ zStarIn J := fun t ht =>
    mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem hcS (hT₁S ht)) hcS) (hT₁S ht), hmod t ht⟩
  have hcN : ∀ t ∈ S ⊓ J ⊓ centralizer (B : Set G), c * t * c ∈ S ⊓ J ⊓ centralizer (B : Set G) :=
    fun t ht => by
      have := mul_mem (hZT₁ (hδ t ht)) (inv_mem ht)
      rwa [show c * t * c * t * t⁻¹ = c * t * c by group] at this
  have hmemT : ∀ t ∈ S ⊓ centralizer (B : Set G),
      t ∈ S ⊓ J ⊓ centralizer (B : Set G) ∨ t * c ∈ S ⊓ J ⊓ centralizer (B : Set G) := by
    have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
    have hle : zpowers c ≤ normalizer ((S ⊓ J ⊓ centralizer (B : Set G) : Subgroup G) : Set G) :=
      zpowers_le.mpr (GrS4.mem_normalizer_of_map_le_self (by
        rintro _ ⟨s, hs, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hci]
        exact hcN s hs))
    intro t ht
    open scoped Pointwise in
    have ht' : t ∈ ((S ⊓ J ⊓ centralizer (B : Set G) : Subgroup G) : Set G) *
        (zpowers c : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ (zpowers c) hle, ← hTc]
      exact ht
    obtain ⟨s, hs, u, hu, rfl⟩ := ht'
    rcases GrS4.eq_one_or_eq_of_mem_zpowers hcc hu with rfl | rfl
    · left
      simpa using hs
    · right
      rw [mul_assoc, hcc, mul_one]
      exact hs
  have hsqT : ∀ t ∈ S ⊓ centralizer (B : Set G), t ∉ S ⊓ J ⊓ centralizer (B : Set G) →
      t * t ∈ S ⊓ zStarIn J := by
    intro t ht htT
    have hs := (hmemT t ht).resolve_left htT
    have hz := hδ _ hs
    have hcomm := hZcent _ hz _ (mem_inf.mp hs).1
    have e : t * t = (t * c) * (c * (t * c) * c * (t * c)) * (t * c)⁻¹ := by
      calc t * t = t * (c * c) * t * (c * c) := by rw [hcc]; group
        _ = (t * c) * (c * (t * c) * c * (t * c)) * (t * c)⁻¹ := by group
    rw [e, hcomm, mul_inv_cancel_right]
    exact hz
  have hT₁64 : Nat.card ↥(S ⊓ J ⊓ centralizer (B : Set G)) ≤ 64 :=
    GrS4.card_inf_centralizer_le hTr hJper hL34 hP (by rwa [hZP]) (by rwa [hZP]) hBP hB8 hBZ ha1
  obtain ⟨h, e, hhT, hhB, hpow, hhC⟩ :=
    exists_seven_of_aut hB8 (GrS4.isSylowTwoIn_inf_centralizer hSyl hSN) hAut
  have hfix : ∀ j : ℤ, ¬ (7 : ℤ) ∣ j → h ^ j * a * (h ^ j)⁻¹ ≠ a := fun j hj =>
    zpow_conj_ne hB8.2 hpow hhB hhC haB ha1 hj
  have hha : h * a * h⁻¹ ≠ a := by
    have := hfix 1 (by norm_num)
    rwa [zpow_one] at this
  obtain ⟨z, hzZ, hza⟩ : ∃ z ∈ S ⊓ zStarIn J, z * z = a := by
    have : IsCyclic ↥(S ⊓ zStarIn J) := hZc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(S ⊓ zStarIn J))
    have hog : orderOf g = 4 := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hZ4
    refine ⟨g, g.2, GrS4.eq_of_mul_self_eq_one_of_isCyclic hZc (mul_mem g.2 g.2) haZ ?_ haa ?_
      ha1⟩
    · have h4 : g ^ 4 = 1 := by rw [← hog]; exact pow_orderOf_eq_one g
      have := congrArg Subtype.val h4
      rw [SubmonoidClass.coe_pow] at this
      rw [show (g : G) * g * (g * g) = (g : G) ^ 4 by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
      exact this
    · intro h1
      have h2 : g ^ 2 = 1 := Subtype.ext (by rw [SubmonoidClass.coe_pow, pow_two]; exact h1)
      exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hog]; norm_num) h2
  have hhT₁ := mem_normalizer_of_seven hT₁T hT₁64 hsqT hBT₁ hB8.2 hB8.1.2
    (fun b hb t ht => mem_centralizer_iff.mp (mem_inf.mp ht).2 b hb)
    (fun b hb hbZ => GrS4.eq_one_or_eq_of_mem_zpowers haa
      (by rw [← hBZ]; exact mem_inf.mpr ⟨hb, (mem_inf.mp hbZ).2⟩))
    haB (hZT₁ hzZ) hza ha1 hhT hhB hfix
  have hcomm : ∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), ∀ t ∈ S ⊓ J ⊓ centralizer (B : Set G),
      s⁻¹ * t⁻¹ * s * t ∈ S ⊓ zStarIn J := fun s hs t ht =>
    mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem (inv_mem (hT₁S hs)) (inv_mem (hT₁S ht))) (hT₁S hs))
      (hT₁S ht), GrS4.commutator_mem_zStarIn_of_invert hT₁J hcc hmod hs ht⟩
  have hab := comm_of_seven hZc hZ4 haZ haa ha1 hcomm hhT₁ hha
  have hhc : h * c * h⁻¹ * c ∈ S ⊓ J ⊓ centralizer (B : Set G) := by
    rcases hmemT _ ((mem_normalizer_iff.mp hhT c).mp hcT) with h1 | h1
    · exfalso
      apply hcT₁
      have := (mem_normalizer_iff.mp (inv_mem hhT₁) _).mp h1
      rwa [show h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c by group] at this
    · exact h1
  exact ⟨hab, inv_of_seven hZc hZ4 haZ haa ha1 hab hcc hcN hδ hhT₁ hhc hha⟩
theorem l34GraphInvertGlobalStep_of_inputs
    (hTr : L34EightTransvectionFact) : L34GraphInvertGlobalStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBP hB8 hBZ hSN hBiff
    hAut c hcS hcc hcW hTc hmod
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := hset
  obtain ⟨ha2, -, -, hJa, hJc, -, -⟩ := hU3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hJc
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hZ4
    norm_num at hZ4
  have haZ : a ∈ S ⊓ zStarIn J := hZ hZne
  exact l34GraphInvertGlobalStep_of_actual hTr hJper hL34 hS hSyl ha2 haZ hZc hZ4 hBP hB8 hBZ
    hSN hAut hcS hcc hcW hTc hmod
theorem l34EndGraphStep_of_covers
    (hCov : L34GraphInvertCoverFact) (hSol : SolomonFixedLayerStep) (hSq : L34OutSquareFact)
    (hNo : L34NoFrobeniusFact) (hTr : L34EightTransvectionFact) : L34EndGraphStep :=
  l34EndGraphStep_of_parts hCov (l34GraphInvertGlobalStep_of_inputs hTr)
      (l34GraphFinalStep_of_inputs hSol hSq hNo) hTr

end CFSG.ComponentClassification.GrSLit.FinalG
