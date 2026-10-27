module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma42
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCor34
import CFSG.LocalAnalysis.ComponentClassification.FooteLitComponentRigidity
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm33

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem ker_le_pPrimeCore {T K : Subgroup G} (hTK : T ≤ K) :
    ((QuotientGroup.mk' (pPrimeCore 2 K)).comp (Subgroup.inclusion hTK)).ker ≤ pPrimeCore 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := (QuotientGroup.mk' (pPrimeCore 2 K)).comp (Subgroup.inclusion hTK) with hψ
  have hmap : ψ.ker.map (Subgroup.inclusion hTK) ≤ pPrimeCore 2 K := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 K)) (Subgroup.inclusion hTK x) = 1 := hx
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hcop : Nat.Coprime 2 (Nat.card ψ.ker) := by
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hTK)]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hmap)
      (pPrimeCore_coprime_card (p := 2) (G := ↥K))
  exact le_sSup ⟨ψ.normal_ker, hcop⟩

theorem le_sup_oddCoreIn_of_card_le {T K : Subgroup G} (hTK : T ≤ K)
    (hcard : Nat.card (K ⧸ pPrimeCore 2 K) ≤ Nat.card (T ⧸ pPrimeCore 2 T)) :
    K ≤ T ⊔ oddCoreIn K := by
  set ψ := (QuotientGroup.mk' (pPrimeCore 2 K)).comp (Subgroup.inclusion hTK) with hψ
  have hker := ker_le_pPrimeCore hTK
  have hrange : ψ.range = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top ψ.range).mp
    apply le_antisymm (Subgroup.card_le_card_group _)
    rw [← Subgroup.index_ker]
    exact hcard.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker))
  intro k hk
  obtain ⟨t, ht⟩ : ∃ t, ψ t = QuotientGroup.mk' (pPrimeCore 2 K) ⟨k, hk⟩ :=
    (hrange ▸ mem_top _ : _ ∈ ψ.range)
  rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at ht
  have hk' : k = (t : G) * (((Subgroup.inclusion hTK t)⁻¹ * ⟨k, hk⟩ : K) : G) := by
    simp [Subgroup.coe_inclusion]
  rw [hk']
  exact mul_mem (mem_sup_left t.2) (mem_sup_right ⟨_, ht, rfl⟩)

theorem card_quotient_eq_of_le_sup {T K : Subgroup G} (hTK : T ≤ K)
    (hcov : K ≤ T ⊔ oddCoreIn K) [IsSimpleGroup (K ⧸ pPrimeCore 2 K)]
    (heven : 2 ∣ Nat.card (K ⧸ pPrimeCore 2 K)) :
    Nat.card (T ⧸ pPrimeCore 2 T) = Nat.card (K ⧸ pPrimeCore 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := (QuotientGroup.mk' (pPrimeCore 2 K)).comp (Subgroup.inclusion hTK) with hψ
  have hTO : T ≤ normalizer ((oddCoreIn K : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (le_normalizer (hTK hx))
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 K) q
    have hk' := hcov hk
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right T (oddCoreIn K) hTO] at hk'
    obtain ⟨t, ht, o, ho, he⟩ := hk'
    obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have e1 : (Subgroup.inclusion hTK ⟨t, ht⟩)⁻¹ * ⟨k, hk⟩ = o' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← he]
      simp
    rw [e1]
    exact ho'
  have hN : ((pPrimeCore 2 T).map ψ).Normal := (inferInstance : (pPrimeCore 2 T).Normal).map _ hsurj
  have hbot : (pPrimeCore 2 T).map ψ = ⊥ := by
    rcases hN.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have h1 : Nat.card (K ⧸ pPrimeCore 2 K) ∣ Nat.card (pPrimeCore 2 T) := by
        rw [← Subgroup.card_top (G := K ⧸ pPrimeCore 2 K), ← h]
        exact Subgroup.card_map_dvd _ _
      have h2 := Nat.Coprime.coprime_dvd_right h1 (pPrimeCore_coprime_card (p := 2) (G := ↥T))
      exact absurd (Nat.Coprime.eq_one_of_dvd h2 heven) (by norm_num)
  have hker : ψ.ker = pPrimeCore 2 T := le_antisymm (ker_le_pPrimeCore hTK)
    ((Subgroup.map_eq_bot_iff _).mp hbot)
  have hrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  calc Nat.card (T ⧸ pPrimeCore 2 T) = (pPrimeCore 2 T).index := rfl
    _ = ψ.ker.index := by rw [hker]
    _ = Nat.card ψ.range := Subgroup.index_ker ψ
    _ = Nat.card (K ⧸ pPrimeCore 2 K) := by rw [hrange, Subgroup.card_top]

omit [Finite G] in
theorem exists_orderOf_eq_two_pow {V : Subgroup G} (hV : IsPGroup 2 V) {v : G} (hv : v ∈ V) :
    ∃ k : ℕ, orderOf v = 2 ^ k := by
  obtain ⟨n, hn⟩ := hV ⟨v, hv⟩
  have h1 : v ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨k, hk⟩

theorem le_closure_conjugates {A E V : Subgroup G} [IsSimpleGroup (A ⧸ pPrimeCore 2 A)]
    (hE : IsPGroup 2 E) (hEA : E ≤ coreActionKernel A) (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hVW : V ≤ A ⊓ centralizer (E : Set G)) :
    A ≤ oddResidualIn (A ⊓ centralizer (E : Set G)) ⊔ oddCoreIn A ∧
      oddResidualIn (A ⊓ centralizer (E : Set G)) ≤
        closure (⋃ g ∈ A ⊓ centralizer (E : Set G),
          ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) := by
  set W := A ⊓ centralizer (E : Set G) with hW
  set N := closure (⋃ g ∈ W, ((V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    with hN
  have hconj : ∀ g ∈ W, V.map (MulAut.conj g).toMonoidHom ≤ W := fun g hg => by
    rintro _ ⟨v, hv, rfl⟩
    exact W.mul_mem (W.mul_mem hg (hVW hv)) (W.inv_mem hg)
  have hNW : N ≤ W := by
    rw [hN, closure_le]
    intro x hx
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
    obtain ⟨g, hg, hxg⟩ := hx
    exact hconj g hg hxg
  have hNL : N ≤ oddResidualIn W := by
    rw [hN, closure_le]
    intro x hx
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
    obtain ⟨g, hg, v, hv, rfl⟩ := hx
    obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hV hv
    refine mem_oddResidualIn (hconj g hg ⟨v, hv, rfl⟩) ⟨k, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hk]
  have hWN : W ≤ normalizer (N : Set G) := fun h hh => by
    apply mem_normalizer_of_map_conj_le
    rw [hN, MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
    obtain ⟨g, hg, v, hv, rfl⟩ := hx
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    refine ⟨h * g, W.mul_mem hh hg, v, hv, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hWA : W ≤ A := inf_le_left
  have hNO : N ≤ normalizer ((oddCoreIn A : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (le_normalizer (hWA (hNW hx)))
  have hAN : A ≤ normalizer ((N ⊔ oddCoreIn A : Subgroup G) : Set G) := by
    refine (le_inf_centralizer_sup_oddCoreIn hE hEA).trans (sup_le ?_ ?_)
    · exact fun x hx => mem_normalizer_sup (hWN hx)
        (mem_normalizer_oddCoreIn (le_normalizer (hWA hx)))
    · exact le_normalizer_sup_of_le_normalizer hNO
  have hNOA : N ⊔ oddCoreIn A ≤ A := sup_le (hNW.trans hWA) (map_subtype_le _)
  have hnorm : ((N ⊔ oddCoreIn A).subgroupOf A).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNOA).mpr hAN
  have hcov : A ≤ N ⊔ oddCoreIn A := by
    rcases (hnorm.map (QuotientGroup.mk' (pPrimeCore 2 A))
      (QuotientGroup.mk'_surjective _)).eq_bot_or_eq_top with h | h
    · exfalso
      apply hV1
      rw [eq_bot_iff]
      intro v hv
      have hvA : v ∈ A := hWA (hVW hv)
      have h1 : QuotientGroup.mk' (pPrimeCore 2 A) (⟨v, hvA⟩ : A) ∈
          ((N ⊔ oddCoreIn A).subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 A)) :=
        mem_map_of_mem _ (show (⟨v, hvA⟩ : A) ∈ (N ⊔ oddCoreIn A).subgroupOf A from
          mem_sup_left (Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨1, one_mem W, v, hv,
            by simp⟩)))
      rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact eq_one_of_mem_isPGroup_of_mem_odd hV (odd_card_oddCoreIn A) hv ⟨_, h1, rfl⟩
    · intro x hx
      have h1 : QuotientGroup.mk' (pPrimeCore 2 A) (⟨x, hx⟩ : A) ∈
          ((N ⊔ oddCoreIn A).subgroupOf A).map (QuotientGroup.mk' (pPrimeCore 2 A)) :=
        h ▸ mem_top _
      obtain ⟨y, hy, hyx⟩ := mem_map.mp h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      have e1 : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : A) : G) := by simp
      rw [e1]
      exact mul_mem hy (mem_sup_right ⟨_, hyx, rfl⟩)
  refine ⟨hcov.trans (sup_le_sup_right hNL _), ?_⟩
  set Q := oddCoreIn A ⊓ centralizer (E : Set G) with hQ
  have hQW : Q ≤ W := inf_le_inf_right _ (map_subtype_le _)
  have hWQN : W ≤ Q ⊔ N := by
    intro x hx
    have hx' := hcov (hWA hx)
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right N (oddCoreIn A) hNO] at hx'
    obtain ⟨n, hn, o, ho, rfl⟩ := hx'
    have hoE : o ∈ centralizer (E : Set G) := by
      have h1 := mul_mem (inv_mem (mem_inf.mp (hNW hn)).2) (mem_inf.mp hx).2
      rwa [inv_mul_cancel_left] at h1
    exact mul_mem (mem_sup_right hn) (mem_sup_left (mem_inf.mpr ⟨ho, hoE⟩))
  have hQodd : Odd (Nat.card Q) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn A) (card_dvd_of_le inf_le_left)
  refine (closure_le _).mpr fun g hg => ?_
  obtain ⟨hgW, h2⟩ := hg
  exact mem_of_two_element_of_mem_sup (hQW.trans hWN)
    (by rw [oddResidualIn_eq_bot_of_odd hQodd]; exact bot_le) (hWQN hgW) h2

theorem foote_lemma_4_3_le_coreActionKernel {A E V : Subgroup G}
    [IsSimpleGroup (A ⧸ pPrimeCore 2 A)] (hEc : IsMulCommutative E) (h8 : Nat.card E = 8)
    (hEA : E ≤ coreActionKernel A) (hV : IsKleinFour V) (hVA : V ≤ A ⊓ centralizer (E : Set G))
    (K : G → Subgroup G) (hK : ∀ e ∈ E, e ≠ 1 → IsTwoComponentAt e (K e))
    (hKA : ∀ e ∈ E, e ≠ 1 → oddResidualIn (A ⊓ centralizer ({e} : Set G)) ≤ K e)
    (hKcard : ∀ e ∈ E, e ≠ 1 →
      Nat.card (K e ⧸ pPrimeCore 2 (K e)) = Nat.card (A ⧸ pPrimeCore 2 A)) :
    ∀ e ∈ E, e ≠ 1 → E ≤ coreActionKernel (K e) := by
  intro e he he1 a ha
  set W := A ⊓ centralizer (E : Set G) with hW
  set L₀ := oddResidualIn W with hL₀def
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  have hV1 : V ≠ ⊥ := fun h => by
    have h4 := hV.card_four
    rw [h, card_bot] at h4
    omega
  obtain ⟨hAcov, -⟩ := le_closure_conjugates hEp hEA hVp hV1 hVA
  have heven : 2 ∣ Nat.card (A ⧸ pPrimeCore 2 A) := by
    have h1 : 2 ∣ Nat.card A := (show 2 ∣ Nat.card V by rw [hV.card_four]; norm_num).trans
      (Subgroup.card_dvd_of_le (hVA.trans inf_le_left))
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 A)] at h1
    exact (Nat.Coprime.dvd_mul_right (pPrimeCore_coprime_card (p := 2) (G := ↥A))).mp h1
  have hL₀E : L₀ ≤ centralizer (E : Set G) := (oddResidualIn_le W).trans inf_le_right
  have hcardL₀ : Nat.card (L₀ ⧸ pPrimeCore 2 L₀) = Nat.card (A ⧸ pPrimeCore 2 A) :=
    card_quotient_eq_of_le_sup ((oddResidualIn_le W).trans inf_le_left) hAcov heven
  have hK₀ : L₀ ≤ K e := (oddResidualIn_mono (inf_le_inf_left A (Subgroup.centralizer_le
    (Set.singleton_subset_iff.mpr he)))).trans (hKA e he he1)
  have hsup : L₀ ⊔ oddCoreIn (K e) = K e := le_antisymm (sup_le hK₀ (map_subtype_le _))
    (le_sup_oddCoreIn_of_card_le hK₀ (by rw [hKcard e he he1, hcardL₀]))
  have haL₀ : a ∈ coreActionKernel L₀ := GSLit.mem_coreActionKernel_of_le_centralizer fun x hx =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hL₀E hx)) a ha).symm
  have hae : a ∈ centralizer ({e} : Set G) := mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (isMulCommutative_iff.mp hEc ⟨a, ha⟩ ⟨e, he⟩))
  exact mem_coreActionKernel_of_sup hK₀ hsup
    (mem_normalizer_of_not_le_coreActionKernel (hK e he he1) hK₀
      (not_le_coreActionKernel_of_sup_oddCoreIn_eq (hK e he he1) hsup) hae haL₀.1) haL₀

theorem foote_lemma_4_3_i (hLB : FooteLBalanceInput) {A E V : Subgroup G}
    [IsSimpleGroup (A ⧸ pPrimeCore 2 A)] (hEc : IsMulCommutative E)
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (h8 : Nat.card E = 8) (hEA : E ≤ coreActionKernel A)
    (hV : IsKleinFour V) (hVA : V ≤ A ⊓ centralizer (E : Set G))
    (h41 : ∀ a ∈ E, a ≠ 1 → ⁅oddCoreOfCentralizer a, V⁆ ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer (V : Set G)))
    (K : G → Subgroup G) (hK : ∀ e ∈ E, e ≠ 1 → IsTwoComponentAt e (K e))
    (hKA : ∀ e ∈ E, e ≠ 1 → oddResidualIn (A ⊓ centralizer ({e} : Set G)) ≤ K e)
    (hKcard : ∀ e ∈ E, e ≠ 1 →
      Nat.card (K e ⧸ pPrimeCore 2 (K e)) = Nat.card (A ⧸ pPrimeCore 2 A)) :
    Odd (Nat.card ↥(⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (K e))) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (K e)) ≤ oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ≤
        oddResidualIn (A ⊓ centralizer (E : Set G)) ⊔ oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) := by
  set W := A ⊓ centralizer (E : Set G) with hW
  set L₀ := oddResidualIn W with hL₀def
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  have hV1 : V ≠ ⊥ := fun h => by
    have h4 := hV.card_four
    rw [h, card_bot] at h4
    omega
  obtain ⟨hAcov, hL₀gen⟩ := le_closure_conjugates hEp hEA hVp hV1 hVA
  have heven : 2 ∣ Nat.card (A ⧸ pPrimeCore 2 A) := by
    have h1 : 2 ∣ Nat.card A := (show 2 ∣ Nat.card V by rw [hV.card_four]; norm_num).trans
      (Subgroup.card_dvd_of_le (hVA.trans inf_le_left))
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 A)] at h1
    exact (Nat.Coprime.dvd_mul_right (pPrimeCore_coprime_card (p := 2) (G := ↥A))).mp h1
  have hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G) := fun e he => mem_centralizer_iff.mpr
    fun v hv => ((mem_centralizer_iff.mp (mem_inf.mp (hVA hv)).2) e he).symm
  have hL₀E : L₀ ≤ centralizer (E : Set G) := (oddResidualIn_le W).trans inf_le_right
  have hWE : W ≤ centralizer (E : Set G) := inf_le_right
  have hWL₀ : ∀ g ∈ W, V.map (MulAut.conj g).toMonoidHom ≤ L₀ := fun g hg => by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hVp hv
    refine mem_oddResidualIn (W.mul_mem (W.mul_mem hg (hVA hv)) (W.inv_mem hg)) ⟨k, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hk]
  have hVL₀ : V ≤ L₀ := fun v hv => mem_oddResidualIn (hVA hv) (exists_orderOf_eq_two_pow hVp hv)
  have hL₀A : L₀ ≤ A := (oddResidualIn_le W).trans inf_le_left
  have hcardL₀ : Nat.card (L₀ ⧸ pPrimeCore 2 L₀) = Nat.card (A ⧸ pPrimeCore 2 A) :=
    card_quotient_eq_of_le_sup hL₀A hAcov heven
  have hK₀ : ∀ e ∈ E, e ≠ 1 → L₀ ≤ K e := fun e he he1 =>
    (oddResidualIn_mono (inf_le_inf_left A (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr he)))).trans (hKA e he he1)
  have hKsup : ∀ e ∈ E, e ≠ 1 → K e ≤ L₀ ⊔ oddCoreIn (K e) := fun e he he1 =>
    le_sup_oddCoreIn_of_card_le (hK₀ e he he1) (by rw [hKcard e he he1, hcardL₀])
  have hKres : ∀ e ∈ E, e ≠ 1 → K e ≤ oddResidualIn (K e) := fun e he he1 =>
    (oddResidualIn_eq_self_of_isPComponent (hK e he he1).2.1 (hK e he he1).2.2).ge
  have hKO : ∀ e ∈ E, e ≠ 1 → oddCoreIn (K e) ≤ oddCoreOfCentralizer e := fun e he he1 =>
    oddCoreIn_le_of_isTwoComponentIn ⟨(hK e he he1).2.1, (hK e he he1).2.2⟩
  have hVK : ∀ e ∈ E, e ≠ 1 → V ≤ K e := fun e he he1 => hVL₀.trans (hK₀ e he he1)
  have hEK : ∀ a ∈ E, ∀ b ∈ E, b ≠ 1 → a ∈ coreActionKernel (K b) := fun a ha b hb hb1 =>
    foote_lemma_4_3_le_coreActionKernel hEc h8 hEA hV hVA K hK hKA hKcard b hb hb1 ha
  have hbal := foote_lemma_4_2 hLB hexp hEc hV hVE h41 K hK hVK hEK
  obtain ⟨hXO, hMsup⟩ := le_sup_oddCoreIn_iSup hEc hexp h8 hV hVE hbal hL₀E hWE hWL₀ hL₀gen K
    hK₀ hKsup hKres hKO
  exact ⟨odd_card_iSup_oddCoreIn hEc hexp h8 hV hVE hbal hL₀E hWE hWL₀ hL₀gen K hK₀ hKsup hKres
    hKO, hXO, hMsup⟩

theorem foote_lemma_4_3_i_of_mem_footeFamilyOf (hLB : FooteLBalanceInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) {L : Subgroup G}
    (hLfam : FooteFamilyType L)
    (huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
      K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M)
    (hrank2 : ∀ B ∈ footeFamilyOf L, CFSG.pRank 2 ↥B = 2)
    {z : G} {A : Subgroup G} (hAmax : FootePointedMaximal z A) (hAF : A ∈ footeFamilyOf L)
    {E V : Subgroup G} (hEc : IsMulCommutative E) (hexp : ∀ e ∈ E, e ^ 2 = 1)
    (h8 : Nat.card E = 8) (hEA : E ≤ coreActionKernel A) (hV : IsKleinFour V)
    (hVA : V ≤ A ⊓ centralizer (E : Set G))
    (h41 : ∀ a ∈ E, a ≠ 1 → ⁅oddCoreOfCentralizer a, V⁆ ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer (V : Set G))) :
    ∃ K : G → Subgroup G, (∀ e ∈ E, e ≠ 1 → IsTwoComponentAt e (K e) ∧ K e ∈ footeFamilyOf L) ∧
      Odd (Nat.card ↥(⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (K e))) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (K e)) ≤ oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ≤
        oddResidualIn (A ⊓ centralizer (E : Set G)) ⊔ oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) := by
  classical
  have hex : ∀ e : G, ∃ B : Subgroup G, e ∈ E → e ≠ 1 → IsTwoComponentAt e B ∧
      B ∈ footeFamilyOf L ∧ oddResidualIn (A ⊓ centralizer ({e} : Set G)) ≤ B := by
    intro e
    by_cases he : e ∈ E ∧ e ≠ 1
    · have hord : orderOf e = 2 := orderOf_eq_prime (hexp e he.1) he.2
      obtain ⟨B, hB, -, hBF, hBA⟩ :=
        exists_mem_footeFamilyOf_of_mem_coreActionKernel hLB huniq hAmax hAF hord (hEA he.1)
      exact ⟨B, fun _ _ => ⟨hB, hBF, hBA⟩⟩
    · exact ⟨⊥, fun h1 h2 => absurd ⟨h1, h2⟩ he⟩
  choose K hK using hex
  have hquot : ∀ B ∈ footeFamilyOf L, (∃ b : G, IsTwoComponentAt b B) →
      Nonempty (B ⧸ pPrimeCore 2 B ≃* L ⧸ Open.fusionZStar L) := by
    intro B hBF hB
    obtain ⟨-, ⟨eBL⟩⟩ := id hBF
    obtain ⟨e₁⟩ := nonempty_quotient_equiv_fusionZStar hGA hGC hSA hB
      (footeFamilyType_of_equiv eBL hLfam) (by rw [hrank2 B hBF])
    exact ⟨e₁.trans eBL⟩
  obtain ⟨eA⟩ := hquot A hAF ⟨z, hAmax.1⟩
  have hsimp : IsSimpleGroup (A ⧸ pPrimeCore 2 A) := by
    obtain ⟨hz, hAz, hApc⟩ := hAmax.1
    obtain ⟨hs, -⟩ := zStarQuotient_simple hApc
    obtain ⟨e₂⟩ := nonempty_quotient_fusionZStar_equiv
      (subgroupOfEquivOfLe hAz : ↥(A.subgroupOf (centralizer ({z} : Set G))) ≃* ↥A)
    obtain ⟨-, ⟨eAL⟩⟩ := id hAF
    exact (e₂.trans (eAL.trans eA.symm)).symm.isSimpleGroup
  refine ⟨K, fun e he he1 => ⟨(hK e he he1).1, (hK e he he1).2.1⟩, ?_⟩
  exact foote_lemma_4_3_i hLB hEc hexp h8 hEA hV hVA h41 K (fun e he he1 => (hK e he he1).1)
    (fun e he he1 => (hK e he he1).2.2)
    (fun e he he1 => by
      obtain ⟨eK⟩ := hquot (K e) (hK e he he1).2.1 ⟨e, (hK e he he1).1⟩
      exact Nat.card_congr (eK.trans eA.symm).toEquiv)

end CFSG.ComponentClassification.FooteLit
