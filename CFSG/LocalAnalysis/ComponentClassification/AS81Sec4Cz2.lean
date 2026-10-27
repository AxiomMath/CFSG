module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cz
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Center
import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step410
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open Matrix
open scoped MatrixGroups Pointwise

theorem le_center_of_normal_of_card_eq_two {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    (hN : N.Normal) (h2 : Nat.card N = 2) : N ≤ center X := by
  intro n hn
  by_cases h1 : n = 1
  · rw [h1]
    exact one_mem _
  have hd : orderOf n ∣ 2 := h2 ▸ Subgroup.orderOf_dvd_natCard N hn
  have ho : orderOf n = 2 := by
    have h0 : orderOf n ≠ 1 := fun h => h1 (orderOf_eq_one_iff.mp h)
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : orderOf n
    · exact absurd hd (by norm_num)
    · exact absurd rfl h0
    · rfl
  have hz : zpowers n = N :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hn) (by rw [h2, Nat.card_zpowers, ho])
  rw [mem_center_iff]
  intro x
  have hx : x * n * x⁻¹ ∈ zpowers n := hz ▸ hN.conj_mem n hn x
  rcases eq_one_or_eq_of_mem_zpowers ho hx with h | h
  · refine absurd ?_ h1
    calc n = x⁻¹ * (x * n * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · calc x * n = x * n * x⁻¹ * x := by group
      _ = n * x := by rw [h]

theorem isSimpleGroup_GL32 : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
  CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh

theorem center_GL32 : center (GL (Fin 3) (ZMod 2)) = ⊥ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
  rintro _ ⟨r, rfl⟩
  rw [Subsingleton.elim r 1, map_one]
  exact Subgroup.one_mem _

theorem center_PGL27 : center (ProjGenLinGroup (Fin 2) (ZMod 7)) = ⊥ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact CFSG.GorensteinWalter.pgl2_center_eq_bot (ZMod 7)

theorem card_eq_card_inf_ker_mul_card_map {H K : Type*} [Group H] [Group K] [Finite H]
    (φ : H →* K) (W : Subgroup H) :
    Nat.card W = Nat.card (W ⊓ φ.ker : Subgroup H) * Nat.card (W.map φ) := by
  let f : W →* K := φ.comp W.subtype
  have hrange : f.range = W.map φ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_map, ← MonoidHom.range_eq_map, range_subtype]
  have hker : Nat.card f.ker = Nat.card (W ⊓ φ.ker : Subgroup H) := by
    have h1 : f.ker = φ.ker.subgroupOf W := (MonoidHom.comap_ker φ W.subtype).symm
    rw [h1, ← inf_subgroupOf_left]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker, mul_comm]

section Quot

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_normalizer_of_quot {C Q Y W : Subgroup G} {X : Type} [Group X]
    (hcX : center X = ⊥) (φ : ↥C →* X) (hφ : Function.Surjective φ)
    (hφker : φ.ker = Q.subgroupOf C) (hYC : Y ≤ C) (hY2 : Y.relIndex C ≤ 2)
    (ψ : ↥Y →* GL (Fin 3) (ZMod 2)) (hψ : Function.Surjective ψ)
    (hψker : ψ.ker = Q.subgroupOf Y) (hQW : Q ≤ W) (hWC : W ≤ C)
    (hCW : C ≤ normalizer (W : Set G)) (hW : ((W ⊓ Y).subgroupOf Y).map ψ ≠ ⊤) : W ≤ Q := by
  have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := isSimpleGroup_GL32
  have : Finite X := Finite.of_surjective φ hφ
  have hWY : W ⊓ Y ≤ Q := by
    have hn : ((W ⊓ Y).subgroupOf Y).Normal := by
      rw [normal_subgroupOf_iff_le_normalizer inf_le_right, inf_comm]
      exact le_normalizer_inf hYC hCW
    have := hn.map ψ hψ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((W ⊓ Y).subgroupOf Y).map ψ) with h | h
    · rw [Subgroup.map_eq_bot_iff, hψker] at h
      intro w hw
      exact h (show (⟨w, hw.2⟩ : Y) ∈ (W ⊓ Y).subgroupOf Y from hw)
    · exact absurd h hW
  by_contra hWQ
  have h1 := Subgroup.relIndex_mul_card Y W
  have hY0 : Y.relIndex C ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_mul_card Y C
    rw [h0, zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  have h2 : Y.relIndex W ≤ Y.relIndex C := Subgroup.relIndex_le_of_le_right hWC hY0
  have h3 : Nat.card (Y ⊓ W : Subgroup G) ≤ Nat.card Q :=
    Subgroup.card_le_of_le (by rw [inf_comm]; exact hWY)
  have hlt : Nat.card Q < Nat.card W := Subgroup.card_lt_of_lt (lt_of_le_of_ne hQW
    (fun h => hWQ (h ▸ le_rfl)))
  obtain ⟨k, hk⟩ : Nat.card Q ∣ Nat.card W := Subgroup.card_dvd_of_le hQW
  have hQ0 := Nat.card_pos (α := Q)
  have hk2 : k = 2 := by
    have hk1 : 1 < k := by
      by_contra hk1
      push Not at hk1
      interval_cases k <;> simp_all
    have : k ≤ 2 := by nlinarith
    omega
  have hWn : (W.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hWC).mpr hCW
  have hc := card_eq_card_inf_ker_mul_card_map φ (W.subgroupOf C)
  have hcW : Nat.card (W.subgroupOf C) = Nat.card W :=
    Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv
  have hcK : Nat.card (W.subgroupOf C ⊓ φ.ker : Subgroup C) = Nat.card Q := by
    rw [hφker, inf_eq_right.mpr (subgroupOf_mono C hQW)]
    exact Nat.card_congr (subgroupOfEquivOfLe (hQW.trans hWC)).toEquiv
  rw [hcW, hcK, hk, hk2] at hc
  have hm : Nat.card ((W.subgroupOf C).map φ) = 2 := by
    have := Nat.eq_of_mul_eq_mul_left hQ0 hc
    omega
  have hle := le_center_of_normal_of_card_eq_two (hWn.map φ hφ) hm
  rw [hcX, le_bot_iff] at hle
  rw [hle, card_bot] at hm
  exact absurd hm (by norm_num)

omit [Finite G] in
theorem mem_normalizer_sup_of_mem {H K : Subgroup G} {n : G} (hH : n ∈ normalizer (H : Set G))
    (hK : n ∈ normalizer (K : Set G)) : n ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem not_isPGroup_GL32 : ¬ IsPGroup 2 (⊤ : Subgroup (GL (Fin 3) (ZMod 2))) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  rw [card_top, card_GL32] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 168)
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem le_of_normal_of_quot {C Q Y S : Subgroup G} {X : Type} [Group X]
    (hcX : center X = ⊥) (φ : ↥C →* X) (hφ : Function.Surjective φ)
    (hφker : φ.ker = Q.subgroupOf C) (hYC : Y ≤ C) (hY2 : Y.relIndex C ≤ 2)
    (ψ : ↥Y →* GL (Fin 3) (ZMod 2)) (hψ : Function.Surjective ψ)
    (hψker : ψ.ker = Q.subgroupOf Y) (hQC : Q ≤ C) (hCQ : C ≤ normalizer (Q : Set G))
    (hS : IsSylowOf 2 S C) (hQS : Q ≤ S) (P : Subgroup ↥C) (hPn : P.Normal)
    (hP : IsPGroup 2 P) : P ≤ Q.subgroupOf C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hS
  have hPS : P.map C.subtype ≤ S := hT ▸ map_mono (hP.le_sylow_of_normal T)
  have hW2 : IsPGroup 2 (P.map C.subtype ⊔ Q : Subgroup G) :=
    (hT ▸ T.isPGroup'.map C.subtype).to_le (sup_le hPS hQS)
  have hle := le_of_le_normalizer_of_quot (W := P.map C.subtype ⊔ Q) hcX φ hφ hφker hYC hY2
    ψ hψ hψker le_sup_right (sup_le (map_subtype_le _) hQC)
    (fun c hc => mem_normalizer_sup_of_mem (AS76b.le_normalizer_map_subtype_of_normal C P hc)
      (hCQ hc))
    (fun h => not_isPGroup_GL32 (h ▸ ((hW2.to_le inf_le_left).comap_subtype.map ψ)))
  intro p hp
  exact hle (mem_sup_left ⟨p, hp, rfl⟩)

theorem centralizer_le_of_quot {C Q Y V₁ : Subgroup G} {z : G} {X : Type} [Group X]
    (hcX : center X = ⊥) (φ : ↥C →* X) (hφ : Function.Surjective φ)
    (hφker : φ.ker = Q.subgroupOf C) (hYC : Y ≤ C) (hY2 : Y.relIndex C ≤ 2)
    (ψ : ↥Y →* GL (Fin 3) (ZMod 2)) (hψ : Function.Surjective ψ)
    (hψker : ψ.ker = Q.subgroupOf Y) (hQC : Q ≤ C) (hCQ : C ≤ normalizer (Q : Set G))
    (hYz : Y ≤ centralizer ({z} : Set G)) (hz2 : orderOf z = 2)
    (hzc : ∀ q ∈ Q, q * z = z * q)
    (hcomm : ∀ q ∈ Q, ∀ v ∈ Q, q * v * q⁻¹ * v⁻¹ ∈ zpowers z)
    (hV₁Q : V₁ ≤ Q) (hV₁ : IsElemAbelian 2 V₁) (hV₁16 : Nat.card V₁ = 16) (hzV : zpowers z ≤ V₁)
    (hirr : ∀ W : Subgroup G, zpowers z ≤ W → W ≤ V₁ → Y ≤ normalizer (W : Set G) →
      W = zpowers z ∨ W = V₁) :
    centralizer ((Q.subgroupOf C : Subgroup ↥C) : Set ↥C) ≤ Q.subgroupOf C := by
  have hQn : (Q.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hQC).mpr hCQ
  obtain ⟨D, hD⟩ : ∃ D, D = centralizer ((Q.subgroupOf C : Subgroup ↥C) : Set ↥C) := ⟨_, rfl⟩
  rw [← hD]
  have hDn : D.Normal := by
    have := hQn
    rw [hD]
    infer_instance
  have hDQ : ∀ d ∈ D.map C.subtype, ∀ q ∈ Q, d * q = q * d := by
    rintro _ ⟨d, hd, rfl⟩ q hq
    rw [hD] at hd
    have := mem_centralizer_iff.mp hd ⟨q, hQC hq⟩ (show (⟨q, hQC hq⟩ : C) ∈ Q.subgroupOf C from hq)
    exact (congrArg Subtype.val this).symm
  have hCD : C ≤ normalizer ((D.map C.subtype : Subgroup G) : Set G) :=
    AS76b.le_normalizer_map_subtype_of_normal C D
  have hW : (((D.map C.subtype ⊔ Q) ⊓ Y).subgroupOf Y).map ψ ≠ ⊤ := by
    intro htop
    have hYW : Y ≤ D.map C.subtype ⊔ Q := by
      intro y hy
      obtain ⟨w, hw, hwy⟩ : ψ ⟨y, hy⟩ ∈ (((D.map C.subtype ⊔ Q) ⊓ Y).subgroupOf Y).map ψ :=
        htop ▸ mem_top _
      have hk : w⁻¹ * ⟨y, hy⟩ ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hwy, inv_mul_cancel]
      rw [hψker, mem_subgroupOf] at hk
      have hy' : y = (w : G) * ((w⁻¹ * ⟨y, hy⟩ : Y) : G) := by simp
      rw [hy']
      exact mul_mem (mem_subgroupOf.mp hw).1 (mem_sup_right hk)
    have hact : ∀ y ∈ Y, ∀ v ∈ Q, ∃ c ∈ zpowers z, y * v * y⁻¹ = c * v := by
      intro y hy v hv
      have hy' : y ∈ ((D.map C.subtype : Subgroup G) : Set G) * (Q : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hQC.trans hCD)]
        exact hYW hy
      obtain ⟨d, hd, q, hq, rfl⟩ := hy'
      refine ⟨q * v * q⁻¹ * v⁻¹, hcomm q hq v hv, ?_⟩
      have hqv : q * v * q⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hq hv) (Q.inv_mem hq)
      calc d * q * v * (d * q)⁻¹ = d * (q * v * q⁻¹) * d⁻¹ := by group
        _ = (q * v * q⁻¹) * d * d⁻¹ := by rw [hDQ d hd _ hqv]
        _ = q * v * q⁻¹ * v⁻¹ * v := by group
    have hz2' : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
    obtain ⟨v, hvV, hvz⟩ : ∃ v ∈ V₁, v ∉ zpowers z := by
      by_contra h
      push Not at h
      have := Subgroup.card_le_of_le (show V₁ ≤ zpowers z from h)
      omega
    have hvQ := hV₁Q hvV
    have hv2 : v ^ 2 = 1 := hV₁.2 v hvV
    have hW₀le : zpowers z ⊔ zpowers v ≤ V₁ := sup_le hzV (zpowers_le.mpr hvV)
    have hYW₀ : Y ≤ normalizer ((zpowers z ⊔ zpowers v : Subgroup G) : Set G) := by
      intro y hy
      refine AS76b.mem_normalizer_of_map_conj_le ?_
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · have hyz := mem_centralizer_singleton_iff.mp (hYz hy)
        have : (MulAut.conj y).toMonoidHom z = z := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [hyz, mul_inv_cancel_right]
        rw [this]
        exact mem_sup_left (mem_zpowers z)
      · obtain ⟨c, hc, hcv⟩ := hact y hy v hvQ
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hcv]
        exact mul_mem (mem_sup_left hc) (mem_sup_right (mem_zpowers v))
    rcases hirr _ le_sup_left hW₀le hYW₀ with h | h
    · exact hvz (h ▸ mem_sup_right (mem_zpowers v))
    ·
      have hvn : zpowers v ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
        rw [zpowers_le]
        refine (centralizer_le_normalizer _) (mem_centralizer_iff.mpr ?_)
        intro w hw
        obtain ⟨k, rfl⟩ := hw
        exact (Commute.zpow_left (hzc v hvQ).symm k).eq
      have hcard : Nat.card (zpowers z ⊔ zpowers v : Subgroup G) ≤ 2 * 2 := by
        have hset := Subgroup.coe_mul_of_right_le_normalizer_left (zpowers z) (zpowers v) hvn
        calc Nat.card (zpowers z ⊔ zpowers v : Subgroup G)
            = Nat.card (((zpowers z : Subgroup G) : Set G) * ((zpowers v : Subgroup G) : Set G)) := by
              rw [← hset]; rfl
          _ ≤ Nat.card (zpowers z) * Nat.card (zpowers v) := Set.natCard_mul_le
          _ ≤ 2 * 2 := by
              rw [hz2', Nat.card_zpowers]
              exact Nat.mul_le_mul_left 2
                (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hv2))
      rw [h, hV₁16] at hcard
      omega
  have hle := le_of_le_normalizer_of_quot (W := D.map C.subtype ⊔ Q) hcX φ hφ hφker hYC hY2
    ψ hψ hψker le_sup_right (sup_le (map_subtype_le _) hQC)
    (fun c hc => mem_normalizer_sup_of_mem (hCD hc) (hCQ hc)) hW
  intro d hd
  exact hle (mem_sup_left ⟨d, hd, rfl⟩)

end Quot

end CFSG.ComponentClassification.AS81
