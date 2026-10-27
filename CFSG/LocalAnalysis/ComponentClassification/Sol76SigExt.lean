module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigMain
public import CFSG.GroupTheory.InvolutionFixedCentralSylow

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

omit [Finite G] in
theorem le_of_mem_kStarComponents (hK : K ∈ kStarComponents N) : K ≤ N := hK.1.1

omit [Finite G] in
theorem isPGroup_of_sq_eq_one {B : Subgroup G} (hB : ∀ x ∈ B, x ^ 2 = 1) : IsPGroup 2 B := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact hB x x.2

theorem exists_sq_eq_one_card_eight_le {X : Subgroup G} (h3 : 3 ≤ CFSG.Open.pRank 2 X) :
    ∃ A : Subgroup G, A ≤ X ∧ (∀ x ∈ A, x ^ 2 = 1) ∧ Nat.card A = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEX, hE, hEcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) X
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 (n := 3)
    (by rw [hEcard]; exact pow_dvd_pow 2 h3)
  refine ⟨A₀.map E.subtype, (map_subtype_le A₀).trans hEX, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hE.2 x x.2
  · rw [card_map_of_injective E.subtype_injective, hA₀]
    norm_num

theorem exists_sigPair_of_le (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {B E : Subgroup G} (hBQ : B ≤ coreActionKernel K') (hBN : B ≤ N)
    (hB2 : ∀ x ∈ B, x ^ 2 = 1) (hB8 : Nat.card B = 8) (hE : IsKleinFour E) (hEB : E ≤ B)
    (hEK : E ≤ K) {f : G} (hfK' : f ∈ K') (hf2 : orderOf f = 2)
    (hBf : B ≤ centralizer ({f} : Set G)) : ∃ V : Subgroup G, SigPair N K K' V B ∧ f ∈ V := by
  have hrank := two_le_pRank_inf_centralizer hK' (isPGroup_of_sq_eq_one hB2) hBQ
  have hfC : f ∈ K' ⊓ centralizer (B : Set G) :=
    ⟨hfK', mem_centralizer_iff.mpr fun b hb => mem_centralizer_singleton_iff.mp (hBf hb)⟩
  obtain ⟨V, hVX, hV, hfV⟩ := exists_isKleinFour_mem hrank hfC hf2
  refine ⟨V, ⟨hK, hK', hne, hV, hVX.trans inf_le_left, hBQ, ?_,
    ⟨FooteLit.isMulCommutative_of_sq_eq_one hB2, hB2⟩, hB8, hBN, E, hE, hEB, hEK⟩, hfV⟩
  intro b hb
  rw [mem_centralizer_iff]
  intro v hv
  exact ((mem_centralizer_iff.mp (hVX hv).2) b hb).symm

theorem exists_sigPair_of_isKleinFour (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {E : Subgroup G} (hE : IsKleinFour E)
    (hEK : E ≤ K) {t x : G} (htK' : t ∈ K') (ht2 : orderOf t = 2)
    (hEt : E ≤ centralizer ({t} : Set G)) (hxN : x ∈ N) (hxQ : x ∈ coreActionKernel K')
    (hx2 : orderOf x = 2) (hxE : x ∉ E) (hEx : E ≤ centralizer ({x} : Set G))
    (hxt : x * t = t * x) :
    ∃ V : Subgroup G, SigPair N K K' V (E ⊔ zpowers x) ∧ t ∈ V := by
  obtain ⟨hB2, hB8⟩ := FooteLit.sup_zpowers_spec hE hxE (Sig.sq_eq_one_of_orderOf_eq_two hx2)
    fun w hw => mem_centralizer_singleton_iff.mp (hEx hw)
  exact exists_sigPair_of_le hK hK' hne
    (sup_le (hEK.trans (le_coreActionKernel_of_ne hK' hK hne.symm)) (zpowers_le.mpr hxQ))
    (sup_le (hEK.trans (le_of_mem_kStarComponents hK)) (zpowers_le.mpr hxN)) hB2 hB8 hE
    le_sup_left hEK htK' ht2
    (sup_le hEt (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxt)))

theorem exists_sigPair_of_three_le_pRank (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {e f : G} (heK : e ∈ K)
    (he2 : orderOf e = 2) (hfK' : f ∈ K') (hf2 : orderOf f = 2) (hfe : f * e = e * f)
    (h3 : 3 ≤ CFSG.Open.pRank 2 (K ⊓ centralizer ({e} : Set G) ⊓ centralizer ({f} : Set G))) :
    ∃ V B : Subgroup G, SigPair N K K' V B ∧ f ∈ V ∧ e ∈ B := by
  obtain ⟨A, hAX, hA2, hA8⟩ := exists_sq_eq_one_card_eight_le h3
  have hAe : ∀ a ∈ A, a * e = e * a := fun a ha =>
    mem_centralizer_singleton_iff.mp (hAX ha).1.2
  obtain ⟨B, hB2, hB8, heB, hBle⟩ :=
    FooteLit.exists_card_eight_mem hA2 hA8 (Sig.sq_eq_one_of_orderOf_eq_two he2) hAe
  have hBK : B ≤ K ⊓ centralizer ({f} : Set G) := by
    refine hBle.trans (sup_le (hAX.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
      ?_)
    rw [zpowers_le]
    exact ⟨heK, mem_centralizer_singleton_iff.mpr hfe.symm⟩
  obtain ⟨E, hE, hEB⟩ := FooteLit.exists_isKleinFour_le hB2 (by rw [hB8]; norm_num)
  obtain ⟨V, hP, hfV⟩ := exists_sigPair_of_le hK hK' hne
    ((hBK.trans inf_le_left).trans (le_coreActionKernel_of_ne hK' hK hne.symm))
    ((hBK.trans inf_le_left).trans (le_of_mem_kStarComponents hK)) hB2 hB8 hE hEB
    (hEB.trans (hBK.trans inf_le_left)) hfK' hf2 (hBK.trans inf_le_right)
  exact ⟨V, B, hP, hfV, heB⟩

theorem exists_sigPair_of_not_mem (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {e f b : G} (heK : e ∈ K) (he2 : orderOf e = 2) (hfK' : f ∈ K')
    (hf2 : orderOf f = 2) (hfe : f * e = e * f) (hbN : b ∈ N) (hbQ : b ∈ coreActionKernel K)
    (hbQ' : b ∈ coreActionKernel K') (hb2 : orderOf b = 2) (hbK : b ∉ K)
    (hbe : b * e = e * b) (hbf : b * f = f * b) :
    ∃ V B : Subgroup G, SigPair N K K' V B ∧ f ∈ V ∧ e ∈ B := by
  have hb2' := Sig.sq_eq_one_of_orderOf_eq_two hb2
  have hf2' := Sig.sq_eq_one_of_orderOf_eq_two hf2
  have hT2 : ∀ x ∈ zpowers b ⊔ zpowers f, x ^ 2 = 1 :=
    FooteLit.sq_eq_one_of_mem_sup (fun y hy => FooteLit.sq_eq_one_of_mem_zpowers hb2' hy)
      (fun y hy => FooteLit.sq_eq_one_of_mem_zpowers hf2' hy) fun x hx y hy => by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow hbf i j).eq
  have hTQ : zpowers b ⊔ zpowers f ≤ coreActionKernel K :=
    sup_le (zpowers_le.mpr hbQ) (zpowers_le.mpr (le_coreActionKernel_of_ne hK hK' hne hfK'))
  have hrank := two_le_pRank_inf_centralizer hK (isPGroup_of_sq_eq_one hT2) hTQ
  have hTe : zpowers b ⊔ zpowers f ≤ centralizer ({e} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hbe))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hfe))
  have heT : e ∈ centralizer ((zpowers b ⊔ zpowers f : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun t ht => mem_centralizer_singleton_iff.mp (hTe ht)
  obtain ⟨E, hEX, hE, heE⟩ := exists_isKleinFour_mem hrank ⟨heK, heT⟩ he2
  have hbT : b ∈ zpowers b ⊔ zpowers f := Subgroup.mem_sup_left (mem_zpowers b)
  have hfT : f ∈ zpowers b ⊔ zpowers f := Subgroup.mem_sup_right (mem_zpowers f)
  have hEb : E ≤ centralizer ({b} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEX hw).2) b hbT).symm
  have hEf : E ≤ centralizer ({f} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEX hw).2) f hfT).symm
  obtain ⟨V, hP, hfV⟩ := exists_sigPair_of_isKleinFour hK hK' hne hE (hEX.trans inf_le_left)
    hfK' hf2 hEf hbN hbQ' hb2 (fun h => hbK (hEX h).1) hEb hbf
  exact ⟨V, E ⊔ zpowers b, hP, hfV, Subgroup.mem_sup_left heE⟩

theorem exists_involution_commute_of_le_normalizer {C : Subgroup G} {e f : G}
    (he2 : orderOf e = 2) (hf2 : orderOf f = 2) (hfe : f * e = e * f)
    (heC : e ∈ normalizer (C : Set G)) (hfC : f ∈ normalizer (C : Set G))
    (hC : Even (Nat.card C)) :
    ∃ b ∈ C, orderOf b = 2 ∧ b * e = e * b ∧ b * f = f * b := by
  have he2' := Sig.sq_eq_one_of_orderOf_eq_two he2
  have hf2' := Sig.sq_eq_one_of_orderOf_eq_two hf2
  have hP2 : ∀ x ∈ zpowers e ⊔ zpowers f, x ^ 2 = 1 :=
    FooteLit.sq_eq_one_of_mem_sup (fun y hy => FooteLit.sq_eq_one_of_mem_zpowers he2' hy)
      (fun y hy => FooteLit.sq_eq_one_of_mem_zpowers hf2' hy) fun x hx y hy => by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
        exact (Commute.zpow_zpow hfe.symm i j).eq
  obtain ⟨b, hbC, hb2, hbP⟩ :=
    CFSG.GroupTheory.exists_involution_commute_of_isPGroup_le_normalizer
      (isPGroup_of_sq_eq_one hP2) (sup_le (zpowers_le.mpr heC) (zpowers_le.mpr hfC)) hC
  exact ⟨b, hbC, hb2, (hbP e (Subgroup.mem_sup_left (mem_zpowers e))).symm,
    (hbP f (Subgroup.mem_sup_right (mem_zpowers f))).symm⟩

theorem exists_sigPair_or_forced (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {e f : G} (heK : e ∈ K) (he2 : orderOf e = 2) (hfK' : f ∈ K')
    (hf2 : orderOf f = 2) (hfe : f * e = e * f) :
    (∃ V B : Subgroup G, SigPair N K K' V B ∧ f ∈ V ∧ e ∈ B) ∨
      (∃ V B : Subgroup G, SigPair N K' K V B ∧ e ∈ V ∧ f ∈ B) ∨
      (CFSG.Open.pRank 2 (K ⊓ centralizer ({e} : Set G) ⊓ centralizer ({f} : Set G)) ≤ 2 ∧
        CFSG.Open.pRank 2 (K' ⊓ centralizer ({e} : Set G) ⊓ centralizer ({f} : Set G)) ≤ 2 ∧
        ∀ b ∈ N ⊓ coreActionKernel K ⊓ coreActionKernel K', orderOf b = 2 →
          b * e = e * b → b * f = f * b → b ∈ K ⊓ K') := by
  by_cases h1 : 3 ≤ CFSG.Open.pRank 2 (K ⊓ centralizer ({e} : Set G) ⊓ centralizer ({f} : Set G))
  · exact Or.inl (exists_sigPair_of_three_le_pRank hK hK' hne heK he2 hfK' hf2 hfe h1)
  by_cases h2 : 3 ≤ CFSG.Open.pRank 2 (K' ⊓ centralizer ({e} : Set G) ⊓ centralizer ({f} : Set G))
  · rw [inf_right_comm] at h2
    exact Or.inr (Or.inl
      (exists_sigPair_of_three_le_pRank hK' hK hne.symm hfK' hf2 heK he2 hfe.symm h2))
  by_cases h3 : ∃ b ∈ N ⊓ coreActionKernel K ⊓ coreActionKernel K', orderOf b = 2 ∧
      b * e = e * b ∧ b * f = f * b ∧ b ∉ K ⊓ K'
  · obtain ⟨b, hb, hb2, hbe, hbf, hbKK'⟩ := h3
    rw [mem_inf, not_and_or] at hbKK'
    rcases hbKK' with hbK | hbK'
    · exact Or.inl (exists_sigPair_of_not_mem hK hK' hne heK he2 hfK' hf2 hfe hb.1.1 hb.1.2 hb.2
        hb2 hbK hbe hbf)
    · exact Or.inr (Or.inl (exists_sigPair_of_not_mem hK' hK hne.symm hfK' hf2 heK he2 hfe.symm
        hb.1.1 hb.2 hb.1.2 hb2 hbK' hbf hbe))
  refine Or.inr (Or.inr ⟨by omega, by omega, fun b hb hb2 hbe hbf => ?_⟩)
  by_contra hn
  exact h3 ⟨b, hb, hb2, hbe, hbf, hn⟩

theorem oddCoreIn_inf_eq_bot_of_sigPair {V B : Subgroup G} (hP : SigPair N K K' V B)
    (hW : wGroup B V = ⊥) {e f : G} (heB : e ∈ B) (he1 : e ≠ 1) (hfV : f ∈ V) :
    oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥ :=
  eq_bot_iff.mpr ((oddCoreIn_inf_le_wGroup hP.2.2.2.1 hP.2.2.2.2.2.2.1 heB he1 hfV).trans hW.le)

theorem oddCoreIn_inf_eq_bot_of_forced (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    (hW : ∀ V B : Subgroup G, SigPair N K K' V B → wGroup B V = ⊥)
    (hW' : ∀ V B : Subgroup G, SigPair N K' K V B → wGroup B V = ⊥) {e f : G} (heK : e ∈ K)
    (he2 : orderOf e = 2) (hfK' : f ∈ K') (hf2 : orderOf f = 2) (hfe : f * e = e * f)
    (hforced :
      CFSG.Open.pRank 2 (K ⊓ centralizer ({e} : Set G) ⊓ centralizer ({f} : Set G)) ≤ 2 →
      CFSG.Open.pRank 2 (K' ⊓ centralizer ({e} : Set G) ⊓ centralizer ({f} : Set G)) ≤ 2 →
      (∀ b ∈ N ⊓ coreActionKernel K ⊓ coreActionKernel K', orderOf b = 2 →
        b * e = e * b → b * f = f * b → b ∈ K ⊓ K') →
      oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥) :
    oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥ := by
  have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he2; norm_num at he2
  have hf1 : f ≠ 1 := fun h => by rw [h, orderOf_one] at hf2; norm_num at hf2
  rcases exists_sigPair_or_forced hK hK' hne heK he2 hfK' hf2 hfe with
    ⟨V, B, hP, hfV, heB⟩ | ⟨V, B, hP, heV, hfB⟩ | ⟨h1, h2, h3⟩
  · exact oddCoreIn_inf_eq_bot_of_sigPair hP (hW V B hP) heB he1 hfV
  · rw [inf_comm]
    exact oddCoreIn_inf_eq_bot_of_sigPair hP (hW' V B hP) hfB hf1 heV
  · exact hforced h1 h2 h3

end CFSG.ComponentClassification.Sol76.Sig
