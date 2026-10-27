module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeGammaFrattini
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGamma
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeGamma
import CFSG.LocalAnalysis.GL83PartI.I_24_3.InnerPGroup
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_of_mem_sup_comm {A C : Subgroup G} (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    {x : G} (hx : x ∈ A ⊔ C) : ∃ a ∈ A, ∃ c ∈ C, x = a * c := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ c ∈ C, x = a * c}
      mul_mem' := by
        rintro _ _ ⟨a, ha, c, hc, rfl⟩ ⟨a', ha', c', hc', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', c * c', C.mul_mem hc hc', ?_⟩
        have : c * a' = a' * c := (hcomm a' ha' c hc).symm
        calc a * c * (a' * c') = a * (c * a') * c' := by group
          _ = a * (a' * c) * c' := by rw [this]
          _ = a * a' * (c * c') := by group
      one_mem' := ⟨1, A.one_mem, 1, C.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, c, hc, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
        have h1 : a * c = c * a := hcomm a ha c hc
        calc (a * c)⁻¹ = (c * a)⁻¹ := by rw [h1]
          _ = a⁻¹ * c⁻¹ := by group }
  have hle : A ⊔ C ≤ S := sup_le (fun a ha => ⟨a, ha, 1, C.one_mem, by simp⟩)
    (fun c hc => ⟨1, A.one_mem, c, hc, by simp⟩)
  exact hle hx

theorem exists_orderOf_three_of_ne_bot {X : Subgroup G} (hX : IsPGroup 3 X) (hX1 : X ≠ ⊥) :
    ∃ x ∈ X, orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hX
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hX1 (Subgroup.eq_bot_of_card_eq X (by simpa using hk))
  have h3 : 3 ∣ Nat.card X := by
    rw [hk]
    exact dvd_pow_self 3 hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
  exact ⟨x, x.2, by rw [← Subgroup.orderOf_coe] at hx; exact hx⟩

theorem gammaZeroIn_map_of_directProd {P : Sylow 3 G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape 3 P M H₁ R₁) {H Q' A C : Subgroup G} (hQ'H : Q' ≤ H)
    (hQ'c : Nat.card (Q'.subgroupOf H) = 3 ^ (Nat.card H).factorization 3) (hQ'M : Q' ≤ M)
    (hAQ : A ≤ Q') (hCQ : C ≤ Q') (hAel : IsElemAbelian 3 A) (hA9 : Nat.card A = 9)
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hdisj : A ⊓ C = ⊥) (hgen : A ⊔ C = Q')
    (hC1 : C = ⊥ → normalizer (Q' : Set G) ≤ M)
    {B : Type*} [Group B] (π : H →* B) (hπ : Function.Surjective π) :
    GammaZeroIn ((Q'.subgroupOf H).map π) ((M.subgroupOf H).map π) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ'p : IsPGroup 3 Q' := by
    have h := IsPGroup.of_card hQ'c
    have := h.map H.subtype
    rwa [Subgroup.map_subgroupOf_eq_of_le hQ'H] at this
  refine ⟨Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
    (hQ'M (Subgroup.mem_subgroupOf.mp hx)), ?_⟩
  intro R hRS hRnc b hb
  obtain ⟨h, rfl⟩ := hπ b
  obtain ⟨r, hr, n, hn, rfl⟩ := exists_mul_of_map_mem_normalizer π hQ'c hRS hb
  rw [map_mul]
  refine mul_mem (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
    (hQ'M (Subgroup.mem_subgroupOf.mp hx))) (hRS hr)) ?_
  set R₂ : Subgroup H := Q'.subgroupOf H ⊓ R.comap π with hR₂
  set R₂G : Subgroup G := R₂.map H.subtype with hR₂G
  have hR₂GQ : R₂G ≤ Q' := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hx.1
  have hnN : (n : G) ∈ normalizer (R₂G : Set G) :=
    Subgroup.le_normalizer_map H.subtype ⟨n, hn, rfl⟩
  have hR₂map : R₂.map π = R := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, hy, rfl⟩ := hx
      exact hy.2
    · obtain ⟨y, hy, rfl⟩ := hRS hx
      exact ⟨y, ⟨hy, hx⟩, rfl⟩
  have hR₂nc : ¬ IsCyclic R₂ := fun hcyc => hRnc (by
    have h : IsCyclic (R₂.map π) :=
      isCyclic_of_surjective (π.subgroupMap R₂) (π.subgroupMap_surjective R₂)
    rwa [hR₂map] at h)
  have hR₂Gnc : ¬ IsCyclic R₂G := fun hcyc => hR₂nc
    (isCyclic_of_injective (R₂.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
      (R₂.equivMapOfInjective H.subtype H.subtype_injective).injective)
  have hR₂Gp : IsPGroup 3 R₂G := hQ'p.to_le hR₂GQ
  have hnM : (n : G) ∈ M := by
    by_cases hC : C = ⊥
    ·
      have hQA : Q' = A := by rw [← hgen, hC, sup_bot_eq]
      have hR₂GA : R₂G = Q' := by
        refine Subgroup.eq_of_le_of_card_ge hR₂GQ ?_
        rw [hQA, hA9]
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR₂Gp
        have hdvd : Nat.card R₂G ∣ 9 := hA9 ▸ Subgroup.card_dvd_of_le (hQA ▸ hR₂GQ)
        rw [hk] at hdvd ⊢
        have hk2 : k ≤ 2 := by
          have := Nat.le_of_dvd (by norm_num) hdvd
          by_contra h
          have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        by_contra hlt
        have hk1 : k ≤ 1 := by
          rcases Nat.lt_or_ge k 2 with h | h
          · omega
          · exact absurd (by rw [show k = 2 by omega]; norm_num) hlt
        apply hR₂Gnc
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
        · haveI : Subsingleton R₂G :=
            (Nat.card_eq_one_iff_unique.mp (by rw [hk, pow_zero])).1
          exact isCyclic_of_subsingleton
        · exact isCyclic_of_prime_card (p := 3) (by rw [hk, pow_one])
      rw [hR₂GA] at hnN
      exact hC1 hC hnN
    · refine Hyp111.normalizer_le_of_weakCoreRank he hQ'p hQ'M hR₂GQ
        (two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) hR₂Gp hR₂Gnc) ?_ hnN
      have hAcent : ∀ a ∈ A, a ∈ Q' ⊓ centralizer (R₂G : Set G) := by
        intro a ha
        refine ⟨hAQ ha, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        have hxQ := hR₂GQ hx
        rw [← hgen] at hxQ
        obtain ⟨a', ha', c', hc', rfl⟩ := exists_mul_of_mem_sup_comm hcomm hxQ
        have h1 : a * a' = a' * a :=
          congrArg Subtype.val (hAel.1.is_comm.comm (⟨a, ha⟩ : A) ⟨a', ha'⟩)
        have h2 : a * c' = c' * a := hcomm a ha c' hc'
        calc a' * c' * a = a' * (c' * a) := by group
          _ = a' * (a * c') := by rw [h2]
          _ = (a' * a) * c' := by group
          _ = a * a' * c' := by rw [h1]
          _ = a * (a' * c') := by group
      by_cases hAR : A ≤ R₂G
      ·
        obtain ⟨c, hcC, hc3, hcW⟩ : ∃ c ∈ C, orderOf c = 3 ∧
            c ∈ R₂G ⊔ (Q' ⊓ centralizer (R₂G : Set G)) := by
          by_cases hCR : C ⊓ R₂G = ⊥
          · obtain ⟨c, hc, hc3⟩ := exists_orderOf_three_of_ne_bot (hQ'p.to_le hCQ) hC
            refine ⟨c, hc, hc3, mem_sup_right ⟨hCQ hc, Subgroup.mem_centralizer_iff.mpr ?_⟩⟩
            intro x hx
            have hxQ := hR₂GQ hx
            rw [← hgen] at hxQ
            obtain ⟨a', ha', c', hc', rfl⟩ := exists_mul_of_mem_sup_comm hcomm hxQ
            have hc'R : c' ∈ R₂G := by
              have : c' = a'⁻¹ * (a' * c') := by group
              rw [this]
              exact R₂G.mul_mem (R₂G.inv_mem (hAR ha')) hx
            have hc'1 : c' = 1 := by
              have : c' ∈ C ⊓ R₂G := ⟨hc', hc'R⟩
              rw [hCR, Subgroup.mem_bot] at this
              exact this
            rw [hc'1, mul_one]
            exact hcomm a' ha' c hc
          · obtain ⟨c, hc, hc3⟩ := exists_orderOf_three_of_ne_bot
              ((hQ'p.to_le hCQ).to_le inf_le_left) hCR
            exact ⟨c, hc.1, hc3, mem_sup_left hc.2⟩
        have hcA : c ∉ A := by
          intro hcA
          have : c ∈ A ⊓ C := ⟨hcA, hcC⟩
          rw [hdisj, Subgroup.mem_bot] at this
          rw [this, orderOf_one] at hc3
          omega
        obtain ⟨hE27, hE27c⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hAel hc3
          (fun a ha => hcomm a ha c hcC) hcA
        refine CFSG.AGLEmbedding.KFactProofs.G28.three_le_pRank_of_card_27 ?_ hE27
          (by rw [hE27c, hA9])
        exact sup_le (hAR.trans le_sup_left) ((Subgroup.zpowers_le).mpr hcW)
      ·
        obtain ⟨a, haA, haR⟩ := Set.not_subset.mp hAR
        have ha1 : a ≠ 1 := fun h => haR (h ▸ R₂G.one_mem)
        have ha3 : orderOf a = 3 := orderOf_eq_prime (hAel.2 a haA) ha1
        obtain ⟨E, hER, hEel, hE9⟩ :=
          GL83.I243.Inner.exists_isElemAbelian_card_sq_of_not_isCyclic (by norm_num) hR₂Gp hR₂Gnc
        have haE : a ∉ E := fun h => haR (hER h)
        obtain ⟨hE27, hE27c⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hEel ha3
          (fun e he => Subgroup.mem_centralizer_iff.mp (hAcent a haA).2 e (hER he)) haE
        refine CFSG.AGLEmbedding.KFactProofs.G28.three_le_pRank_of_card_27 ?_ hE27
          (by rw [hE27c, hE9]; norm_num)
        exact sup_le (hER.trans le_sup_left) ((Subgroup.zpowers_le).mpr
          (mem_sup_right (hAcent a haA)))
  exact ⟨n, Subgroup.mem_subgroupOf.mpr hnM, rfl⟩

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
