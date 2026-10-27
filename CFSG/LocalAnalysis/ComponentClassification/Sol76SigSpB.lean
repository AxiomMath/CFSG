module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigSpA
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigConn
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigSplit

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

@[expose] def Sp4CoreFacts (K : Subgroup G) (b : G) : Prop :=
  (∀ y ∈ K, y ∈ coreActionKernel K → y ∈ oddCoreIn K ∨ y⁻¹ * b ∈ oddCoreIn K) ∧
    ∀ s ∈ K, orderOf s = 2 →
      ∃ k ∈ K, s⁻¹ * k⁻¹ * s * k ∈ oddCoreIn K ∧ (k * k)⁻¹ * b ∈ oddCoreIn K

omit [Finite G] in
theorem mk_eq_one_iff {x : ↥N} :
    QuotientGroup.mk' (pPrimeCore 2 ↥N) x = 1 ↔ (x : G) ∈ oddCoreIn N := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨o, ho, he⟩
    rwa [← Subtype.ext he]

theorem mem_sup_oddCoreIn_of_forced {R : SigOrientation} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') (hR : R G N K K') (hR' : R G N K' K)
    {e f : G} (heK : e ∈ K) (he2 : orderOf e = 2) (hfK' : f ∈ K') (hf2 : orderOf f = 2)
    (hfe : f * e = e * f) (hF : SigForced R N K K' e f) {w : G} (hwN : w ∈ N)
    (hwQ : w ∈ coreActionKernel K) (hwQ' : w ∈ coreActionKernel K')
    (hw2 : w ^ 2 ∈ oddCoreIn N) (hwO : w ∉ oddCoreIn N) : w ∈ K ⊔ oddCoreIn N := by
  obtain ⟨-, -, hX⟩ := forced_facts hK hK' hne heK he2 hfK' hf2 hfe hR hR' hF
  have hOodd : Odd (Nat.card (oddCoreIn N)) :=
    Nat.coprime_two_left.mp (coprime_card_oddCoreIn N)
  have hOQ : oddCoreIn N ≤ coreActionKernel K := oddCoreIn_le_coreActionKernel hK.1
  have hOQ' : oddCoreIn N ≤ coreActionKernel K' := oddCoreIn_le_coreActionKernel hK'.1
  have he2' := Sig.sq_eq_one_of_orderOf_eq_two he2
  have hf2' := Sig.sq_eq_one_of_orderOf_eq_two hf2
  have hP2 : ∀ x ∈ zpowers e ⊔ zpowers f, x ^ 2 = 1 :=
    FooteLit.sq_eq_one_of_mem_sup (fun y hy => FooteLit.sq_eq_one_of_mem_zpowers he2' hy)
      (fun y hy => FooteLit.sq_eq_one_of_mem_zpowers hf2' hy) fun x hx y hy => by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow hfe.symm i j).eq
  have hPx : zpowers e ⊔ zpowers f ≤ commModSubgroup (oddCoreIn N) w := sup_le
    (zpowers_le.mpr ⟨le_normalizer_oddCoreIn N (hK.1.1 heK),
      FooteLit.oddCoreIn_le_of_isTwoComponentIn hK.1 ((mem_coreActionKernel.mp hwQ).2 e heK)⟩)
    (zpowers_le.mpr ⟨le_normalizer_oddCoreIn N (hK'.1.1 hfK'),
      FooteLit.oddCoreIn_le_of_isTwoComponentIn hK'.1
        ((mem_coreActionKernel.mp hwQ').2 f hfK')⟩)
  obtain ⟨c, hc2, hwc, hcP⟩ := exists_involution_mem_coset hOodd
    (le_normalizer_oddCoreIn N hwN) hw2 hwO (isPGroup_of_sq_eq_one hP2) hPx
  have hc : c = w * (w⁻¹ * c) := by group
  have hcN : c ∈ N := by
    rw [hc]
    exact mul_mem hwN (map_subtype_le _ hwc)
  have hcQ : c ∈ coreActionKernel K := by
    rw [hc]
    exact mul_mem hwQ (hOQ hwc)
  have hcQ' : c ∈ coreActionKernel K' := by
    rw [hc]
    exact mul_mem hwQ' (hOQ' hwc)
  have hcK := hX c ⟨⟨hcN, hcQ⟩, hcQ'⟩ hc2 (hcP e (mem_sup_left (mem_zpowers e))).symm
    (hcP f (mem_sup_right (mem_zpowers f))).symm
  have hw : w = c * (w⁻¹ * c)⁻¹ := by group
  rw [hw]
  exact mul_mem (mem_sup_left hcK.1) (mem_sup_right (inv_mem hwc))

theorem exists_sq_mem_coset_of_three_le {R : SigOrientation} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') (hR : R G N K K') (hR' : R G N K' K)
    (h2K : CFSG.Open.pRank 2 K ≤ 2) {e f : G} (heK : e ∈ K) (he2 : orderOf e = 2)
    (hfK' : f ∈ K') (hf2 : orderOf f = 2) (hfe : f * e = e * f) (hF : SigForced R N K K' e f)
    {b : G} (hS : Sp4CoreFacts K b)
    (h3 : 3 ≤ CFSG.Open.pRank 2 ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K')) :
    ∃ w ∈ N, w ∈ coreActionKernel K ∧ w ∈ coreActionKernel K' ∧
      (w * w)⁻¹ * b ∈ oddCoreIn N ∧ w ∉ K ⊔ oddCoreIn N := by
  obtain ⟨A, hAX, hA2, hA8⟩ := exists_sq_eq_one_card_eight_le h3
  have hMN : oddTwoCoreIn N ⊔ twoLayerIn N ≤ N := sup_le (map_subtype_le _) (map_subtype_le _)
  obtain ⟨a, haA, haKO⟩ := exists_not_mem_sup_of_card_eight hK h2K hA2 hA8
  have haM := (hAX haA).1
  have haQ' := (hAX haA).2
  have haN : a ∈ N := hMN haM
  obtain ⟨k, hkK, hwQ⟩ := exists_inv_mul_mem_coreActionKernel hK.1 haM
  have hkN : k ∈ N := hK.1.1 hkK
  have hKQ' : K ≤ coreActionKernel K' := le_coreActionKernel_of_ne hK' hK hne.symm
  have hOK : oddCoreIn K ≤ oddCoreIn N := FooteLit.oddCoreIn_le_of_isTwoComponentIn hK.1
  have hOQ : oddCoreIn N ≤ coreActionKernel K := oddCoreIn_le_coreActionKernel hK.1
  set w := k⁻¹ * a with hw
  have hwN : w ∈ N := mul_mem (inv_mem hkN) haN
  have hwQ' : w ∈ coreActionKernel K' := mul_mem (inv_mem (hKQ' hkK)) haQ'
  have hak : a = k * w := by rw [hw, mul_inv_cancel_left]
  have hwKO : w ∉ K ⊔ oddCoreIn N := fun h => haKO (by
    rw [hak]
    exact mul_mem (mem_sup_left hkK) h)
  have hkw : Commute (QuotientGroup.mk' (pPrimeCore 2 ↥N) ⟨k, hkN⟩)
      (QuotientGroup.mk' (pPrimeCore 2 ↥N) ⟨w, hwN⟩) :=
    commute_mk_of_mem_coreActionKernel hK.1 hkK hwQ
  have hkkN : k⁻¹ * k⁻¹ ∈ N := mul_mem (inv_mem hkN) (inv_mem hkN)
  have hwwN : w * w ∈ N := mul_mem hwN hwN
  have hyw : (w * w)⁻¹ * (k⁻¹ * k⁻¹) ∈ oddCoreIn N := by
    set κ := QuotientGroup.mk' (pPrimeCore 2 ↥N) ⟨k, hkN⟩
    set ω := QuotientGroup.mk' (pPrimeCore 2 ↥N) ⟨w, hwN⟩
    have ha1 : κ * ω * (κ * ω) = 1 := by
      have h1 : (⟨k, hkN⟩ * ⟨w, hwN⟩ * (⟨k, hkN⟩ * ⟨w, hwN⟩) : ↥N) = 1 := Subtype.ext (by
        change k * w * (k * w) = 1
        rw [← hak, ← sq, hA2 a haA])
      rw [← map_mul, ← map_mul, h1, map_one]
    have h2 : κ * κ * (ω * ω) = 1 := by rwa [← hkw.symm.mul_mul_mul_comm]
    have h3 : ω * ω = κ⁻¹ * κ⁻¹ := by
      rw [eq_inv_of_mul_eq_one_right h2, mul_inv_rev]
    have h4 : QuotientGroup.mk' (pPrimeCore 2 ↥N) ⟨w * w, hwwN⟩ =
        QuotientGroup.mk' (pPrimeCore 2 ↥N) ⟨k⁻¹ * k⁻¹, hkkN⟩ := by
      have e1 : (⟨w * w, hwwN⟩ : ↥N) = ⟨w, hwN⟩ * ⟨w, hwN⟩ := rfl
      have e2 : (⟨k⁻¹ * k⁻¹, hkkN⟩ : ↥N) = (⟨k, hkN⟩)⁻¹ * (⟨k, hkN⟩)⁻¹ := rfl
      rw [e1, e2, map_mul, map_mul, map_inv, h3]
    exact mk_eq_mk_iff.mp h4
  have hyK : k⁻¹ * k⁻¹ ∈ K := mul_mem (inv_mem hkK) (inv_mem hkK)
  have hwwQ : w * w ∈ coreActionKernel K := mul_mem hwQ hwQ
  have hyQ : k⁻¹ * k⁻¹ ∈ coreActionKernel K := by
    have e : k⁻¹ * k⁻¹ = (w * w) * ((w * w)⁻¹ * (k⁻¹ * k⁻¹)) := by group
    rw [e]
    exact mul_mem hwwQ (hOQ hyw)
  rcases hS.1 _ hyK hyQ with hyO | hyb
  ·
    exfalso
    have hw2 : w ^ 2 ∈ oddCoreIn N := by
      have e : w ^ 2 = (k⁻¹ * k⁻¹) * ((w * w)⁻¹ * (k⁻¹ * k⁻¹))⁻¹ := by group
      rw [e]
      exact mul_mem (hOK hyO) (inv_mem hyw)
    have hwO : w ∉ oddCoreIn N := fun h => hwKO (mem_sup_right h)
    exact hwKO (mem_sup_oddCoreIn_of_forced hK hK' hne hR hR' heK he2 hfK' hf2 hfe hF hwN hwQ
      hwQ' hw2 hwO)
  · refine ⟨w, hwN, hwQ, hwQ', ?_, hwKO⟩
    have e : (w * w)⁻¹ * b = ((w * w)⁻¹ * (k⁻¹ * k⁻¹)) * ((k⁻¹ * k⁻¹)⁻¹ * b) := by group
    rw [e]
    exact mul_mem hyw (hOK hyb)

theorem false_of_sq_mem_coset {R : SigOrientation} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') (hR : R G N K K') {e f : G} (heK : e ∈ K)
    (he2 : orderOf e = 2) (hfK' : f ∈ K') (hf2 : orderOf f = 2) (hfe : f * e = e * f)
    (hF : SigForced R N K K' e f) {b : G} (hbK : b ∈ K) (hbK' : b ∈ K') (hb2 : orderOf b = 2)
    (hbQ : b ∈ coreActionKernel K) (hbQ' : b ∈ coreActionKernel K') (hbe : b * e = e * b)
    (hbf : b * f = f * b) (hS : Sp4CoreFacts K b) {w : G} (hwN : w ∈ N)
    (hwQ : w ∈ coreActionKernel K) (hwQ' : w ∈ coreActionKernel K')
    (hwb : (w * w)⁻¹ * b ∈ oddCoreIn N) (hwKO : w ∉ K ⊔ oddCoreIn N) : False := by
  have hf2' : IsPGroup 2 (zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf2, pow_one])
  obtain ⟨s, hsK, hs2, hsb, hsbc, hsf, heE⟩ : ∃ s ∈ K, orderOf s = 2 ∧ s ≠ b ∧ s * b = b * s ∧
      s * f = f * s ∧ e ∈ closure ({s, b} : Set G) := by
    by_cases heb : e = b
    · have hfQ : zpowers f ≤ coreActionKernel K :=
        zpowers_le.mpr (le_coreActionKernel_of_ne hK hK' hne hfK')
      have hrank := two_le_pRank_inf_centralizer hK hf2' hfQ
      have hbY : b ∈ K ⊓ centralizer ((zpowers f : Subgroup G) : Set G) := by
        refine mem_inf.mpr ⟨hbK, ?_⟩
        rw [Sig.centralizer_zpowers_eq]
        exact mem_centralizer_singleton_iff.mpr hbf
      obtain ⟨F, hFY, hF4, hbF⟩ := exists_isKleinFour_mem hrank hbY hb2
      obtain ⟨s, hsF, hsz⟩ := exists_not_mem_zpowers_of_isKleinFour hF4 hbF
      have hs1 : s ≠ 1 := fun h => hsz (h ▸ one_mem _)
      have hsC := (hFY hsF).2
      rw [Sig.centralizer_zpowers_eq] at hsC
      refine ⟨s, (hFY hsF).1, orderOf_eq_two_of_isKleinFour hF4 hsF hs1,
        fun h => hsz (h ▸ mem_zpowers b), comm_of_isKleinFour hF4 s hsF b hbF,
        mem_centralizer_singleton_iff.mp hsC, ?_⟩
      rw [heb]
      exact subset_closure (Set.mem_insert_of_mem _ rfl)
    · exact ⟨e, heK, he2, heb, hbe.symm, hfe.symm, subset_closure (Set.mem_insert e _)⟩
  have hE : IsKleinFour (closure ({s, b} : Set G)) :=
    UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair hs2 hb2 hsbc hsb
  set E := closure ({s, b} : Set G) with hEdef
  have hEK : E ≤ K := by
    rw [hEdef, closure_le]
    rintro y (rfl | rfl)
    · exact hsK
    · exact hbK
  have hEf : E ≤ centralizer ({f} : Set G) := by
    rw [hEdef, closure_le]
    rintro y (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr hsf
    · exact mem_centralizer_singleton_iff.mpr hbf
  have hfE : f ∈ K' ⊓ centralizer (E : Set G) :=
    ⟨hfK', mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hEf hy)⟩
  obtain ⟨k, hkK, hks, hkb⟩ := hS.2 s hsK hs2
  have hKQ' : K ≤ coreActionKernel K' := le_coreActionKernel_of_ne hK' hK hne.symm
  have hOK : oddCoreIn K ≤ oddCoreIn N := FooteLit.oddCoreIn_le_of_isTwoComponentIn hK.1
  have hOQ' : oddCoreIn N ≤ coreActionKernel K' := oddCoreIn_le_coreActionKernel hK'.1
  have hOodd : Odd (Nat.card (oddCoreIn N)) :=
    Nat.coprime_two_left.mp (coprime_card_oddCoreIn N)
  have hkN : k ∈ N := hK.1.1 hkK
  have hsN : s ∈ N := hK.1.1 hsK
  have hbN : b ∈ N := hK.1.1 hbK
  have hfN : f ∈ N := hK'.1.1 hfK'
  set x₀ := k * w with hx₀
  have hx₀N : x₀ ∈ N := mul_mem hkN hwN
  have hx₀Q' : x₀ ∈ coreActionKernel K' := mul_mem (hKQ' hkK) hwQ'
  have hwx₀ : w = k⁻¹ * x₀ := by rw [hx₀, inv_mul_cancel_left]
  have hx₀KO : ∀ y ∈ K, y⁻¹ * x₀ ∈ oddCoreIn N → False := fun y hy h => hwKO (by
    rw [hwx₀]
    have e : k⁻¹ * x₀ = (k⁻¹ * y) * (y⁻¹ * x₀) := by group
    rw [e]
    exact mul_mem (mem_sup_left (mul_mem (inv_mem hkK) hy)) (mem_sup_right h))
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥N) with hπ
  have hx₀π : π ⟨x₀, hx₀N⟩ = π ⟨k, hkN⟩ * π ⟨w, hwN⟩ := by
    rw [← map_mul]
    rfl
  have hkw : Commute (π ⟨k, hkN⟩) (π ⟨w, hwN⟩) := commute_mk_of_mem_coreActionKernel hK.1 hkK hwQ
  have hk2 : π ⟨k, hkN⟩ * π ⟨k, hkN⟩ = π ⟨b, hbN⟩ := by
    rw [← map_mul]
    exact mk_eq_mk_iff.mpr (hOK hkb)
  have hw2 : π ⟨w, hwN⟩ * π ⟨w, hwN⟩ = π ⟨b, hbN⟩ := by
    rw [← map_mul]
    exact mk_eq_mk_iff.mpr hwb
  have hbb : π ⟨b, hbN⟩ * π ⟨b, hbN⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨b, hbN⟩ * ⟨b, hbN⟩ : ↥N) = 1 :=
      Subtype.ext (by
        change b * b = 1
        rw [← sq]
        exact Sig.sq_eq_one_of_orderOf_eq_two hb2)
    rw [h1, map_one]
  have hx₀2 : x₀ ^ 2 ∈ oddCoreIn N := by
    have h : π ⟨x₀ * x₀, mul_mem hx₀N hx₀N⟩ = 1 := by
      have e1 : (⟨x₀ * x₀, mul_mem hx₀N hx₀N⟩ : ↥N) = ⟨x₀, hx₀N⟩ * ⟨x₀, hx₀N⟩ := rfl
      rw [e1, map_mul, hx₀π, hkw.symm.mul_mul_mul_comm, hk2, hw2, hbb]
    rw [sq]
    exact mk_eq_one_iff.mp h
  have hx₀O : x₀ ∉ oddCoreIn N := fun h => hx₀KO 1 (one_mem _) (by rwa [inv_one, one_mul])
  have hcomm : ∀ p : G, (hp : p ∈ N) → Commute (π ⟨p, hp⟩) (π ⟨k, hkN⟩) →
      Commute (π ⟨p, hp⟩) (π ⟨w, hwN⟩) → p ∈ commModSubgroup (oddCoreIn N) x₀ := by
    intro p hp h1 h2
    refine ⟨le_normalizer_oddCoreIn N hp, ?_⟩
    have h3 : Commute (π ⟨p, hp⟩) (π ⟨x₀, hx₀N⟩) := by
      rw [hx₀π]
      exact h1.mul_right h2
    exact (mk_mul_comm_iff ⟨p, hp⟩ ⟨x₀, hx₀N⟩).mp h3
  have hsC : s ∈ commModSubgroup (oddCoreIn N) x₀ :=
    hcomm s hsN ((mk_mul_comm_iff ⟨s, hsN⟩ ⟨k, hkN⟩).mpr (hOK hks))
      (commute_mk_of_mem_coreActionKernel hK.1 hsK hwQ)
  have hbC : b ∈ commModSubgroup (oddCoreIn N) x₀ :=
    hcomm b hbN (commute_mk_of_mem_coreActionKernel hK.1 hkK hbQ).symm
      (commute_mk_of_mem_coreActionKernel hK.1 hbK hwQ)
  have hfC : f ∈ commModSubgroup (oddCoreIn N) x₀ :=
    hcomm f hfN (commute_mk_of_mem_coreActionKernel hK'.1 hfK' (hKQ' hkK))
      (commute_mk_of_mem_coreActionKernel hK'.1 hfK' hwQ')
  have hEfz : E ≤ centralizer ((zpowers f : Subgroup G) : Set G) := by
    rw [Sig.centralizer_zpowers_eq]
    exact hEf
  have hP2 : IsPGroup 2 (E ⊔ zpowers f : Subgroup G) :=
    isPGroup_sup_of_le_centralizer (isPGroup_of_isKleinFour hE) hf2' hEfz
  have hPx : E ⊔ zpowers f ≤ commModSubgroup (oddCoreIn N) x₀ := by
    refine sup_le ?_ (zpowers_le.mpr hfC)
    rw [hEdef, closure_le]
    rintro y (rfl | rfl)
    · exact hsC
    · exact hbC
  obtain ⟨x, hx2, hx₀x, hxP⟩ := exists_involution_mem_coset hOodd
    (le_normalizer_oddCoreIn N hx₀N) hx₀2 hx₀O hP2 hPx
  have hx : x = x₀ * (x₀⁻¹ * x) := by group
  have hxN : x ∈ N := by
    rw [hx]
    exact mul_mem hx₀N (map_subtype_le _ hx₀x)
  have hxQ' : x ∈ coreActionKernel K' := by
    rw [hx]
    exact mul_mem hx₀Q' (hOQ' hx₀x)
  have hxE : x ∉ E := fun h => hx₀KO x (hEK h) (by
    have e : x⁻¹ * x₀ = (x₀⁻¹ * x)⁻¹ := by group
    rw [e]
    exact inv_mem hx₀x)
  have hEx : E ≤ centralizer ({x} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (hxP y (mem_sup_left hy))
  have hxf : x * f = f * x := (hxP f (mem_sup_right (mem_zpowers f))).symm
  have hconn := involutionGraph_preconnected_of_central hK' (isPGroup_of_isKleinFour hE)
    (hEK.trans hKQ') hbK' hb2 hbQ'
  exact hF.1 hR (Or.inr (Or.inr ⟨E, hE, hEK, heE, hfE, hconn, f, x, hfE, hf2, hxN, hxQ', hx2,
    hxE, hEx, hxf⟩))

theorem false_of_forced_shared {R : SigOrientation} (hN : IsSolomonChoice N)
    (hr : (kStarComponents N).ncard = 2) (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') (hR : R G N K K') (hR' : R G N K' K)
    (h2K : CFSG.Open.pRank 2 K ≤ 2) (h2K' : CFSG.Open.pRank 2 K' ≤ 2) {e f : G} (heK : e ∈ K)
    (he2 : orderOf e = 2) (hfK' : f ∈ K') (hf2 : orderOf f = 2) (hfe : f * e = e * f) {b : G}
    (hbK : b ∈ K) (hbK' : b ∈ K') (hb2 : orderOf b = 2) (hbQ : b ∈ coreActionKernel K)
    (hbQ' : b ∈ coreActionKernel K') (hbe : b * e = e * b) (hbf : b * f = f * b)
    (hF : SigForced R N K K' e f) (hS : Sp4CoreFacts K b) (hS' : Sp4CoreFacts K' b) : False := by
  rcases three_le_pRank_of_ncard_eq_two hN hr hK hK' hne with h3 | h3
  · have hF' : SigForced R N K' K f e := ⟨hF.2, hF.1⟩
    obtain ⟨w, hwN, hwQ, hwQ', hwb, hwKO⟩ := exists_sq_mem_coset_of_three_le hK' hK hne.symm hR'
      hR h2K' hfK' hf2 heK he2 hfe.symm hF' hS' h3
    exact false_of_sq_mem_coset hK' hK hne.symm hR' hfK' hf2 heK he2 hfe.symm hF' hbK' hbK hb2
      hbQ' hbQ hbf hbe hS' hwN hwQ hwQ' hwb hwKO
  · obtain ⟨w, hwN, hwQ, hwQ', hwb, hwKO⟩ := exists_sq_mem_coset_of_three_le hK hK' hne hR hR'
      h2K heK he2 hfK' hf2 hfe hF hS h3
    exact false_of_sq_mem_coset hK hK' hne hR heK he2 hfK' hf2 hfe hF hbK hbK' hb2 hbQ hbQ' hbe
      hbf hS hwN hwQ hwQ' hwb hwKO

theorem forcedSharedRankTwoFor_of_facts
    (h : ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G,
      IsSolomonChoice N → ∀ K ∈ kStarComponents N, CFSG.Open.pRank 2 K ≤ 2 →
        ∀ b ∈ K, orderOf b = 2 → b ∈ coreActionKernel K → Sp4CoreFacts K b) :
    ForcedSharedRankTwoFor := by
  intro G _ _ hG N hN hr K hK K' hK' hne hR hR' h2K h2K' e heK he2 f hfK' hf2 hfe b hb hb2 hbQ
    hbQ' hbe hbf hF
  exact (false_of_forced_shared hN hr hK hK' hne hR hR' h2K h2K' heK he2 hfK' hf2 hfe hb.1 hb.2
    hb2 hbQ hbQ' hbe hbf hF (h G hG N hN K hK h2K b hb.1 hb2 hbQ)
    (h G hG N hN K' hK' h2K' b hb.2 hb2 hbQ')).elim

end CFSG.ComponentClassification.Sol76.Sig
