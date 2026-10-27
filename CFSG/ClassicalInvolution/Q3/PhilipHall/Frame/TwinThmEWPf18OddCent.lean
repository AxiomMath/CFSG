module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf18OddW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf13BarB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section OddCent


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem isPGroup_sup_of_commutes_or_eq {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (h : Commutes A B ∨ B = A) : IsPGroup 2 ↥(A ⊔ B) := by
  rcases h with h | rfl
  · exact hA.to_sup_of_normal_right' hB fun x hx =>
      mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hx h)
  · rwa [sup_idem]

theorem exists_lift_pair_odd (hΩ : HypOmegaGen Ω) (hΩ' : HypOmegaGen (quotFamily Ω N))
    (hN : Odd (Nat.card N)) {M₀ : Subgroup G} (hM₀ : M₀ ∈ Ω) {Jb : Subgroup (G ⧸ N)}
    (hJb : Jb ∈ KPerp (quotFamily Ω N) (M₀.map (QuotientGroup.mk' N)))
    {Rb₁ Rb₂ : Subgroup (G ⧸ N)} (hRb₁ : Rb₁ ∈ RSet (quotFamily Ω N))
    (hRb₁M : Rb₁ ≤ M₀.map (QuotientGroup.mk' N)) (hRb₂ : Rb₂ ∈ RSet (quotFamily Ω N))
    (hRb₂J : Rb₂ ≤ Jb) (hcb : Commutes Rb₁ Rb₂ ∨ Rb₂ = Rb₁) :
    ∃ M ∈ Ω, ∃ J ∈ KPerp Ω M, ∃ R₁ R₂ : Subgroup G, R₁ ∈ RSet Ω ∧ R₁ ≤ M ∧ R₂ ∈ RSet Ω ∧ R₂ ≤ J ∧
      (Commutes R₁ R₂ ∨ R₂ = R₁) ∧ M.map (QuotientGroup.mk' N) = M₀.map (QuotientGroup.mk' N) ∧
      J.map (QuotientGroup.mk' N) = Jb ∧ R₁.map (QuotientGroup.mk' N) = Rb₁ ∧
      R₂.map (QuotientGroup.mk' N) = Rb₂ := by
  set π := QuotientGroup.mk' N with hπ
  have hMb : M₀.map π ∈ quotFamily Ω N := map_mem_quotFamily hM₀
  have hRb₁syl : IsSylow2In Rb₁ (M₀.map π) :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ' hMb hRb₁ hRb₁M
  obtain ⟨R₁, hR₁, hR₁map⟩ := exists_lift_sylow hN hRb₁syl
  have hR₁Ω : R₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hM₀ hR₁
  rcases hJb with hJbeq | hJbn
  ·
    have hRb₂M : Rb₂ ≤ M₀.map π := hJbeq ▸ hRb₂J
    have hRb₂syl : IsSylow2In Rb₂ (M₀.map π) :=
      Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ' hMb hRb₂ hRb₂M
    have hRbeq : Rb₂ = Rb₁ := by
      rcases hcb with hc | hc
      · have hsup2 : IsPGroup 2 ↥(Rb₁ ⊔ Rb₂) :=
          isPGroup_sup_of_commutes_or_eq hRb₁syl.2.1 hRb₂syl.2.1 (Or.inl hc)
        have h1 : Rb₁ ⊔ Rb₂ = Rb₁ := hRb₁syl.eq_of_le hsup2 (sup_le hRb₁M hRb₂M) le_sup_left
        have h2 : Rb₂ ≤ Rb₁ := h1 ▸ le_sup_right
        exact (hRb₂syl.eq_of_le hRb₁syl.2.1 hRb₁M h2).symm
      · exact hc
    exact ⟨M₀, hM₀, M₀, Set.mem_insert _ _, R₁, R₁, hR₁Ω, hR₁.1, hR₁Ω, hR₁.1, Or.inr rfl, rfl,
      hJbeq.symm, hR₁map, hR₁map.trans hRbeq.symm⟩
  ·
    obtain ⟨J₀, hJ₀, hJ₀eq⟩ := hJbn.1
    subst hJ₀eq
    have hne : J₀.map π ≠ M₀.map π := hJbn.2.1
    have hRb₂syl : IsSylow2In Rb₂ (J₀.map π) :=
      Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ' hJbn.1 hRb₂ hRb₂J
    have hcb' : Commutes Rb₁ Rb₂ := by
      rcases hcb with hc | hc
      · exact hc
      · exfalso
        have h2 := hΩ'.card_le_two_of_le_inf hJbn.1 hMb hne hRb₂syl.2.1 hRb₂J (hc ▸ hRb₁M)
        have h8 := hΩ'.eight_le_of_mem_RSet hRb₂
        omega
    obtain ⟨T, hT, hTmap⟩ := exists_lift_sylow hN hRb₂syl
    have hc : Commutes (T.map π) (R₁.map π) := by
      rw [hR₁map, hTmap]
      exact fun a ha b hb => (hcb' b hb a ha).symm
    obtain ⟨m, hm, hTm⟩ := exists_conj_normalizer_of_commutes_gen hN hT.2.1 hR₁.2.1 hc
    have hmπ : π m = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    set M'' := conjSub m M₀ with hM''
    have hM''Ω : M'' ∈ Ω := hΩ.conjInvariant m M₀ hM₀
    have hM''map : M''.map π = M₀.map π := by
      rw [hM'', AscQuot.map_conjSub, hmπ, conjSub_one]
    have hR₁' : IsSylow2In (conjSub m R₁) M'' := IsSylow2In.conj hR₁ m
    have hR₁'Ω : conjSub m R₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hM''Ω hR₁'
    have hTΩ : T ∈ RSet Ω := mem_RSet_of_isSylow2In hJ₀ hT
    have hMJ : M'' ≠ J₀ := fun h => hne (by rw [← h, hM''map])
    have hP : IsPGroup 2 ↥(T ⊔ conjSub m R₁) := hT.2.1.to_sup_of_normal_right' hR₁'.2.1 hTm
    have hTR : T ≠ conjSub m R₁ := by
      intro h
      exact hMJ (hΩ.eq_of_le_of_le hM''Ω hJ₀ hR₁'.2.1 (by have := hΩ.eight_le_of_mem_RSet hR₁'Ω; omega)
        hR₁'.1 (h ▸ hT.1))
    obtain ⟨S, hS⟩ := hP.exists_le_sylow
    have hcomm : Commutes (conjSub m R₁) T :=
      Q3CP.l67Gen G Ω hΩ S _ hR₁'Ω T hTΩ (le_sup_right.trans hS) (le_sup_left.trans hS) hTR.symm
    obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hM''Ω
    have hzR : z ∈ conjSub m R₁ :=
      AscL62.mem_of_uniqueInvolution_of_pGroup hz hR₁'.1 hR₁'.2.1
        (by have := hΩ.eight_le_of_mem_RSet hR₁'Ω; omega)
    have hAc : T ≤ Subgroup.centralizer ({z} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzR y hy).symm
    have hTN : T ≤ Subgroup.normalizer (M'' : Set G) :=
      hΩ.le_normalizer_of_le_centralizer hM''Ω hJ₀ hMJ hz hT.1 hT.2.1
        (by have := hΩ.eight_le_of_mem_RSet hTΩ; omega) hAc
    have hJm : J₀ ∈ omegaNbr Ω M'' := ⟨hJ₀, hMJ.symm, T, hTΩ, hT.1, hTN⟩
    refine ⟨M'', hM''Ω, J₀, Set.mem_insert_of_mem _ hJm, conjSub m R₁, T, hR₁'Ω, hR₁'.1, hTΩ,
      hT.1, Or.inl hcomm, hM''map, rfl, ?_, hTmap⟩
    rw [AscQuot.map_conjSub, hmπ, conjSub_one]
    exact hR₁map

theorem quotOdd_exists_W {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}
    (hst : EStandQ8 Ω K S R W) (hC : CentPairs Ω (S : Subgroup G) W H) (hN : Odd (Nat.card N))
    (hNH : N ≤ H) :
    ∃ Wb ∈ WSet (quotFamily Ω N), Wb ≤ (S : Subgroup G).map (QuotientGroup.mk' N) ∧
      (∀ s ∈ (S : Subgroup G).map (QuotientGroup.mk' N), conjSub s Wb = Wb) ∧
      CentPairs (quotFamily Ω N) ((S : Subgroup G).map (QuotientGroup.mk' N)) Wb
        (H.map (QuotientGroup.mk' N)) := by
  set π := QuotientGroup.mk' N with hπ
  have hΩ := hst.hyp
  obtain ⟨hΩ', -, -⟩ := oddQuotHypQ8 hΩ hst.cls hst.q8 hN
  obtain ⟨hWΩ, hWS, hWn⟩ := hst.hW
  have hS2 : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  refine ⟨W.map π, map_mem_WSet hΩ hΩ' hN hWΩ, Subgroup.map_mono hWS, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [← AscQuot.map_conjSub, hWn s hs]
  intro Mb hMb _ Jb hJb Rb₁ Rb₂ hRb₁ hRb₁M hRb₁S hRb₂ hRb₂J hRb₂S hcb ab habR habW hab1 hab2
  obtain ⟨M₀, hM₀, rfl⟩ := hMb
  obtain ⟨M, hMΩ, J, hJ, R₁, R₂, hR₁, hR₁M, hR₂, hR₂J, hcomm, -, rfl, rfl, rfl⟩ :=
    exists_lift_pair_odd hΩ hΩ' hN hM₀ hJb hRb₁ hRb₁M hRb₂ hRb₂J hcb
  have hP2 : IsPGroup 2 ↥(R₁ ⊔ R₂) := by
    obtain ⟨M₁, -, hR₁M₁⟩ := exists_isSylow2In_of_mem_RSet hR₁
    obtain ⟨M₂, -, hR₂M₂⟩ := exists_isSylow2In_of_mem_RSet hR₂
    exact isPGroup_sup_of_commutes_or_eq hR₁M₁.2.1 hR₂M₂.2.1 hcomm
  have hPle : R₁ ⊔ R₂ ≤ (S : Subgroup G) ⊔ N :=
    le_sup_of_map_le (by rw [Subgroup.map_sup]; exact sup_le hRb₁S hRb₂S)
  obtain ⟨n, hn, hnle⟩ := exists_conj_le_of_le_sup hN hP2 hPle
  have hnπ : π n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  have hmapn : ∀ X : Subgroup G, (conjSub n X).map π = X.map π := fun X => by
    rw [AscQuot.map_conjSub, hnπ, conjSub_one]
  have hMn : conjSub n M ∈ Ω := hΩ.conjInvariant n M hMΩ
  have hJn : conjSub n J ∈ KPerp Ω (conjSub n M) := KPerp_conj hΩ.conjInvariant hJ n
  have hR₁n : conjSub n R₁ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR₁ n
  have hR₂n : conjSub n R₂ ∈ RSet Ω := RSet.conj hΩ.conjInvariant hR₂ n
  have hR₁nS : conjSub n R₁ ≤ (S : Subgroup G) := (conjSub_mono le_sup_left).trans hnle
  have hR₂nS : conjSub n R₂ ≤ (S : Subgroup G) := (conjSub_mono le_sup_right).trans hnle
  have hcommn : Commutes (conjSub n R₁) (conjSub n R₂) ∨ conjSub n R₂ = conjSub n R₁ := by
    rcases hcomm with h | h
    · exact Or.inl (h.conjSub n)
    · exact Or.inr (by rw [h])
  have habX : ab ∈ (conjSub n R₁ ⊔ conjSub n R₂).map π := by
    rw [Subgroup.map_sup, hmapn, hmapn]
    exact habR
  obtain ⟨b, hbX, rfl⟩ := habX
  have hbS : b ∈ (S : Subgroup G) := (sup_le hR₁nS hR₂nS) hbX
  obtain ⟨w, hwW, hwb⟩ := habW
  have hbW : b ∈ W := by
    have h1 : w⁻¹ * b ∈ (S : Subgroup G) ⊓ N := by
      refine ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hWS hwW)) hbS, ?_⟩
      have h0 : π (w⁻¹ * b) = 1 := by rw [map_mul, map_inv, hwb, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h0
    rw [inf_bot_of_isPGroup hN hS2] at h1
    have : w = b := inv_mul_eq_one.mp h1
    rw [← this]
    exact hwW
  have hb2 : b * b = 1 := by
    have h1 : b * b ∈ (S : Subgroup G) ⊓ N :=
      ⟨(S : Subgroup G).mul_mem hbS hbS, (QuotientGroup.eq_one_iff _).mp
        (show π (b * b) = 1 by rw [map_mul]; exact hab2)⟩
    rw [inf_bot_of_isPGroup hN hS2] at h1
    exact h1
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hab1 (map_one π)
  have hMW : conjSub n M ⊓ W ∈ USet Ω :=
    inf_W_mem_USet' hΩ hWΩ hWS hMn hR₁n (conjSub_mono hR₁M) hR₁nS
  have hCb := hC _ hMn hMW _ hJn _ _ hR₁n (conjSub_mono hR₁M) hR₁nS hR₂n (conjSub_mono hR₂J)
    hR₂nS hcommn b hbX hbW hb1 hb2
  exact (centralizer_map_le hN hb2).trans (Subgroup.map_mono hCb)

theorem printedQuotOdd_proved : PrintedQuotOdd :=
  ⟨fun G _ _ Ω K S R W H N _ hst hC hN hNH => quotOdd_exists_W hst hC hN hNH⟩

end OddCent

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
