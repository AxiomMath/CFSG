module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEnd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.Sporadic.HeldB.OuterFixedCore

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeKR

section Aut

open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct

theorem exists_conj_of_card_ne {S : Type*} [Group S] (e : S ≃* Blueprint.NativeSporadic.He)
    (α : MulAut S) (hα : α * α = 1) (hcard : Nat.card (fixedSubgroup α) ≠ 15120) :
    ∃ t : S, t * t = 1 ∧ α = MulAut.conj t := by
  set θ : S ≃* heP := e.trans heEquivP with hθ
  by_cases h1 : α = 1
  · exact ⟨1, mul_one 1, by rw [h1, map_one]⟩
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα) h1
  have hβ : orderOf (MulAut.congr θ α) = 2 := by
    rw [CFSG.Sporadic.HeldB.orderOf_congr, hα2]
  by_cases hinn : MulAut.congr θ α ∈ (MulAut.conj : heP →* MulAut heP).range
  · obtain ⟨s, hs⟩ := (congr_mem_range_conj_iff θ α).mp hinn
    refine ⟨s, ?_, hs.symm⟩
    apply CFSG.Sporadic.HeldB.conj_injective_of_center
      (center_eq_bot_of_mulEquiv θ heP_center_eq_bot)
    rw [map_mul, hs, hα, map_one]
  · exfalso
    apply hcard
    obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq ctbh_full_automorphism_permutation_model.1
      (MulAut.congr θ α) hβ hinn
    obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
    have e' : fixedSubgroup α ≃*
        (heP ⊓ centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))) :=
      ((fixedSubgroupCongr θ α).trans (MulEquiv.subgroupCongr (by rw [hx]))).trans
        (fixedSubgroupEquivOfConj x hg heAutU hxg)
    rw [Nat.card_congr e'.toEquiv, card_heP_centralizer_heAutU]

end Aut

variable {X : Type} [Group X] [Finite X]

theorem heldEndSetting_of_steps (hW : HeldWGroupStep) (hStd : HeldStandardStep)
    (hAS : AschbacherSeitzHeldInput) {L N : Subgroup X} {w : X} (hset : HeldEndSetting X L)
    (hw2 : orderOf w = 2) (hNw : N ≤ centralizer ({w} : Set X))
    (hNp : IsPComponent 2 (N.subgroupOf (centralizer ({w} : Set X))))
    (e : ↥N ⧸ pPrimeCore 2 ↥N ≃* Blueprint.NativeSporadic.He) : HeldEndSetting X N := by
  obtain ⟨⟨hsimp, hnab, hK, hU, hLB, -, -⟩, -⟩ := hset
  have hsetN : HeldSetting X N := ⟨hsimp, hnab, hK, hU, hLB, ⟨w, hw2, hNw, hNp⟩, ⟨e⟩⟩
  have hWN := hW X N hsetN
  obtain ⟨hstd, hO⟩ := hStd X N hsetN hWN
  have hHe := nonempty_mulEquiv_held_of_pPrimeCore_eq_bot hO e
  have : IsSimpleGroup X := hsimp
  have htop : GeneralizedFitting.subgroup X = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup X ≃* X :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup X) := eF.isSimpleGroup
  have hnF : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  exact ⟨hsetN, hWN, hstd, hHe, hAS X hK hsF hnF N hstd hHe⟩

theorem exists_twoA_of_strict
    {N M : Subgroup X} {c w : X} (hsetN : HeldEndSetting X N)
    (hc2 : orderOf c = 2) (hw2 : orderOf w = 2) (hcw : c * w = w * c)
    (hNw : N ≤ centralizer ({w} : Set X))
    (hNp : IsPComponent 2 (N.subgroupOf (centralizer ({w} : Set X))))
    (hMc : M ≤ centralizer ({c} : Set X))
    (hMcp : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))))
    (hNc : conjugate N c = N) (hMNc : M ≤ N ⊓ centralizer ({c} : Set X))
    (hMNcp : IsPComponent 2 (M.subgroupOf (N ⊓ centralizer ({c} : Set X))))
    (hlt : (pPrimeCore 2 ↥M).index < (pPrimeCore 2 ↥N).index)
    (htype : IsL34Type (↥M ⧸ Open.fusionZStar ↥M)) :
    ∃ n₀ : X, HeldTwoA N n₀ ∧ gsFixedLayer N n₀ = M ∧ (c = n₀ ∨ c = n₀ * w) := by
  obtain ⟨-, -, -, ⟨eN⟩, hrank⟩ := hsetN
  have hcc : c * c = 1 := by rw [← pow_two, ← hc2, pow_orderOf_eq_one]
  have hww : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    norm_num at hc2
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw2
    norm_num at hw2
  have hMN : M ≤ N := hMNc.trans inf_le_left
  have hwN : ∀ x ∈ N, x * w = w * x := fun x hx => mem_centralizer_singleton_iff.mp (hNw hx)
  have hMcard : 20160 ≤ Nat.card M := by
    have h1 : 20160 ∣ Nat.card M := by
      rw [← CatLeaf.card_of_isL34Type htype]
      exact Subgroup.card_quotient_dvd_card _
    exact Nat.le_of_dvd Nat.card_pos h1
  have hcN : c ∈ normalizer (N : Set X) := by
    rw [mem_normalizer_iff]
    intro y
    rw [← UnbalancedLayer.mem_conjugate_iff, hNc]
  set α : MulAut N := N.normalizerMonoidHom ⟨c, hcN⟩ with hαdef
  have hαapp : ∀ x : N, ((α x : N) : X) = c * x * c⁻¹ := fun x => rfl
  have hαα : α * α = 1 := MulEquiv.ext fun x => Subtype.ext (by
    rw [MulAut.mul_apply, MulAut.one_apply, hαapp, hαapp]
    calc c * (c * (x : X) * c⁻¹) * c⁻¹ = (c * c) * x * (c * c)⁻¹ := by group
      _ = x := by rw [hcc]; group)
  have hfixN : FixedCommutingProduct.fixedSubgroup α =
      (N ⊓ centralizer ({c} : Set X)).subgroupOf N := by
    ext x
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hαapp] at h1
      refine ⟨x.2, ?_⟩
      calc (x : X) * c = c * x * c⁻¹ * c := by rw [h1]
        _ = c * x := by group
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      rw [hαapp]
      calc c * (x : X) * c⁻¹ = x * c * c⁻¹ := by rw [hx]
        _ = x := by group
  have hcard : Nat.card (FixedCommutingProduct.fixedSubgroup α) ≠ 15120 := by
    rw [hfixN, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
    have := Subgroup.card_le_of_le hMNc
    omega
  obtain ⟨t, htt, hαt⟩ := exists_conj_of_card_ne eN α hαα hcard
  set n₀ : X := (t : X) with hn₀
  have hn₀N : n₀ ∈ N := t.2
  have hn₀n₀ : n₀ * n₀ = 1 := congrArg Subtype.val htt
  have hn₀inv : n₀⁻¹ = n₀ := inv_eq_of_mul_eq_one_right hn₀n₀
  have hact : ∀ x ∈ N, c * x * c⁻¹ = n₀ * x * n₀ := by
    intro x hx
    have h := congrArg (fun φ : MulAut N => ((φ ⟨x, hx⟩ : N) : X)) hαt
    simp only [hαapp, MulAut.conj_apply, coe_mul, coe_inv] at h
    rw [h, hn₀inv]
  have hcn₀ : c * n₀ = n₀ * c := by
    have h := hact n₀ hn₀N
    calc c * n₀ = c * n₀ * c⁻¹ * c := by group
      _ = n₀ * n₀ * n₀ * c := by rw [h]
      _ = n₀ * c := by rw [hn₀n₀, one_mul]
  have hn₀w : n₀ * w = w * n₀ := hwN n₀ hn₀N
  have hyC : n₀ * c ∈ centralizer (N : Set X) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h := hact x hx
    calc x * (n₀ * c) = n₀ * n₀ * x * n₀ * c := by rw [hn₀n₀]; group
      _ = n₀ * (n₀ * x * n₀) * c := by group
      _ = n₀ * (c * x * c⁻¹) * c := by rw [h]
      _ = n₀ * c * x := by group
  have hwC : w ∈ centralizer (N : Set X) := mem_centralizer_iff.mpr hwN
  have hyy : n₀ * c * (n₀ * c) = 1 := by
    calc n₀ * c * (n₀ * c) = n₀ * (c * n₀) * c := by group
      _ = n₀ * (n₀ * c) * c := by rw [hcn₀]
      _ = (n₀ * n₀) * (c * c) := by group
      _ = 1 := by rw [hn₀n₀, hcc, one_mul]
  have hyw : n₀ * c * w = w * (n₀ * c) := by
    calc n₀ * c * w = n₀ * (c * w) := by group
      _ = n₀ * (w * c) := by rw [hcw]
      _ = n₀ * w * c := by group
      _ = w * n₀ * c := by rw [hn₀w]
      _ = w * (n₀ * c) := by group
  have hy : n₀ * c = 1 ∨ n₀ * c = w := by
    by_contra hcon
    rw [not_or] at hcon
    have h2 := HeEnd.two_le_pRank_of_pair hyC hwC hyy hww hcon.1 hw1 hcon.2 hyw
    omega
  have hn₀1 : n₀ ≠ 1 := by
    intro h1
    rcases hy with h | h
    · rw [h1, one_mul] at h
      exact hc1 h
    · rw [h1, one_mul] at h
      rw [h] at hMc hMcp
      have hMN' := HeDB.eq_of_le hMc hMcp hNw hNp hMN
      rw [hMN'] at hlt
      exact lt_irrefl _ hlt
  have hn₀2 : orderOf n₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hn₀n₀) hn₀1
  have hNC : N ⊓ centralizer ({c} : Set X) = N ⊓ centralizer ({n₀} : Set X) := by
    ext x
    simp only [mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hx, hxc⟩
      refine ⟨hx, ?_⟩
      have h2 : n₀ * x * n₀ = x := by
        rw [← hact x hx, ← hxc]
        group
      calc x * n₀ = n₀ * x * n₀ * n₀ := by rw [h2]
        _ = n₀ * x := by rw [mul_assoc, hn₀n₀, mul_one]
    · rintro ⟨hx, hxn⟩
      refine ⟨hx, ?_⟩
      have h2 : c * x * c⁻¹ = x := by rw [hact x hx, ← hxn, mul_assoc, hn₀n₀, mul_one]
      calc x * c = c * x * c⁻¹ * c := by rw [h2]
        _ = c * x := by group
  have hMH : M ≤ N ⊓ centralizer ({n₀} : Set X) := hNC ▸ hMNc
  have hMHp : IsPComponent 2 (M.subgroupOf (N ⊓ centralizer ({n₀} : Set X))) := hNC ▸ hMNcp
  have hMK : M ≤ gsFixedLayer N n₀ := by
    have h1 : M.subgroupOf (N ⊓ centralizer ({n₀} : Set X)) ≤
        pLayer ↥(N ⊓ centralizer ({n₀} : Set X)) 2 :=
      le_sSup (s := {J : Subgroup ↥(N ⊓ centralizer ({n₀} : Set X)) | IsPComponent 2 J}) hMHp
    have h2 := map_mono (f := (N ⊓ centralizer ({n₀} : Set X)).subtype) h1
    rwa [subgroupOf_map_subtype, inf_eq_left.mpr hMH] at h2
  have hMne : M ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hMcard
    omega
  have hKne : gsFixedLayer N n₀ ≠ ⊥ := fun h => hMne (le_bot_iff.mp (h ▸ hMK))
  have hTA : HeldTwoA N n₀ := ⟨hn₀N, hn₀2, hKne⟩
  have hMeq := HeDB.eq_of_le hMH hMHp (gsFixedLayer_le_inf N n₀)
    (isPComponent_gsFixedLayer_of_held eN hTA) hMK
  refine ⟨n₀, hTA, hMeq.symm, ?_⟩
  rcases hy with h | h
  · left
    rw [eq_inv_of_mul_eq_one_right h, hn₀inv]
  · right
    calc c = n₀ * (n₀ * c) := by rw [← mul_assoc, hn₀n₀, one_mul]
      _ = n₀ * w := by rw [h]

end HeKR

end CFSG.ComponentClassification.GrSLit
