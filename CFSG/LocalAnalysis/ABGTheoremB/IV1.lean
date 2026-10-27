module

public import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI
public import CFSG.LocalAnalysis.ABGTheoremB.Facts
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements

public section

namespace CFSG.ABGTheoremB

open CFSG.ABGLocalTools
open scoped Pointwise

universe u

section General

variable {G : Type u} [Group G]

theorem normalizer_inf_normalizer_le_normalizer_sup (A B : Subgroup G) :
    Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  obtain ⟨hA, hB⟩ := Subgroup.mem_inf.mp hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem relIndex_sup_right_of_le_normalizer {H N : Subgroup G}
    (h : H ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  have : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
  have : (N.subgroupOf (H ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv).symm

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card A (B ⊔ A)
  have h2 := Subgroup.relIndex_mul_card A B
  rw [inf_eq_left.mpr (le_sup_right : A ≤ B ⊔ A), relIndex_sup_right_of_le_normalizer h] at h1
  rw [sup_comm, ← h1, ← h2]
  ring

theorem relIndex_sup_eq_relIndex_of_le_normalizer [Finite G] {N P : Subgroup G}
    (h : P ≤ Subgroup.normalizer (N : Set G)) : P.relIndex (N ⊔ P) = P.relIndex N := by
  have h1 := Subgroup.relIndex_mul_card P (N ⊔ P)
  have h3 := Subgroup.relIndex_mul_card P N
  have h4 := card_sup_mul_card_inf_of_le_normalizer h
  rw [inf_eq_left.mpr (le_sup_right : P ≤ N ⊔ P)] at h1
  rw [inf_comm] at h3
  have hpos : 0 < Nat.card P * Nat.card (N ⊓ P : Subgroup G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc P.relIndex (N ⊔ P) * (Nat.card P * Nat.card (N ⊓ P : Subgroup G))
      = Nat.card (N ⊔ P : Subgroup G) * Nat.card (N ⊓ P : Subgroup G) := by rw [← h1]; ring
    _ = P.relIndex N * (Nat.card P * Nat.card (N ⊓ P : Subgroup G)) := by rw [h4, ← h3]; ring

theorem odd_card_sup_of_le_normalizer_of_odd {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) (hA : Odd (Nat.card A)) (hB : Odd (Nat.card B)) :
    Odd (Nat.card (A ⊔ B : Subgroup G)) :=
  (hA.mul hB).of_dvd_nat (Dvd.intro _ (card_sup_mul_card_inf_of_le_normalizer h))

theorem subset_inf_mul_of_subset_mul {X H K M : Subgroup G} (hXM : X ≤ M) (hKM : K ≤ M)
    (h : (X : Set G) ⊆ (H : Set G) * (K : Set G)) :
    (X : Set G) ⊆ ((H ⊓ M : Subgroup G) : Set G) * (K : Set G) := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := h hx
  refine ⟨a, ⟨ha, ?_⟩, b, hb, rfl⟩
  simpa using M.mul_mem (hXM hx) (M.inv_mem (hKM hb))

theorem exists_sylow_le_inf_of_subset_mul [Finite G] {p : ℕ} [Fact p.Prime] {H L M : Subgroup G}
    (S : Sylow p G) (hSL : (S : Subgroup G) ≤ L) (hML : M ≤ L)
    (hLM : L ≤ Subgroup.normalizer (M : Set G)) (hM : ¬ p ∣ Nat.card M)
    (hcov : (L : Set G) ⊆ (H : Set G) * (M : Set G)) :
    ∃ P : Sylow p G, (P : Subgroup G) ≤ H ⊓ L := by
  have hKL : H ⊓ L ≤ L := inf_le_right
  have hKM : H ⊓ L ≤ Subgroup.normalizer (M : Set G) := hKL.trans hLM
  have hLeq : M ⊔ H ⊓ L = L := by
    refine le_antisymm (sup_le hML hKL) fun l hl => ?_
    have h1 := subset_inf_mul_of_subset_mul le_rfl hML hcov hl
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKM, sup_comm] at h1
    exact h1
  have hidx : ¬ p ∣ (H ⊓ L).relIndex L := by
    have h1 := relIndex_sup_eq_relIndex_of_le_normalizer hKM
    rw [hLeq] at h1
    rw [h1]
    exact fun hdvd => hM (hdvd.trans (Dvd.intro _ (Subgroup.relIndex_mul_card _ _)))
  obtain ⟨P, hP⟩ := exists_isSylowOf p (H ⊓ L)
  have hPK : P ≤ H ⊓ L := hP.le
  have hL : ¬ p ∣ L.index := fun hdvd =>
    S.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hSL))
  have hPidx : ¬ p ∣ P.index := by
    rw [← Subgroup.relIndex_mul_index (hPK.trans hKL),
      ← Subgroup.relIndex_mul_relIndex P (H ⊓ L) L hPK hKL]
    exact (Fact.out : p.Prime).not_dvd_mul
      ((Fact.out : p.Prime).not_dvd_mul (isSylowOf_iff.mp hP).2.2 hidx) hL
  exact ⟨hP.isPGroup.toSylow hPidx, by rw [IsPGroup.toSylow_coe]; exact hPK⟩

theorem exists_isSylowOf_normalized_of_coprime [Finite G] {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    {A K : Subgroup G} (hA : IsPGroup p A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hK : ¬ p ∣ Nat.card K) :
    ∃ R : Subgroup G, IsSylowOf r R K ∧ A ≤ Subgroup.normalizer (R : Set G) := by
  obtain ⟨Q, hQ⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow p r hp hr
    A K hA hAK ((Nat.Prime.coprime_iff_not_dvd hp).mpr hK)
  exact ⟨_, ⟨Q, rfl⟩, hQ⟩

theorem exists_isSylowOf_normalized_ge_of_coprime [Finite G] {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) {A K P : Subgroup G} (hA : IsPGroup p A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hK : ¬ p ∣ Nat.card K) (hPK : P ≤ K)
    (hP : IsPGroup r P) (hAP : A ≤ Subgroup.normalizer (P : Set G)) :
    ∃ R : Subgroup G, IsSylowOf r R K ∧ P ≤ R ∧ A ≤ Subgroup.normalizer (R : Set G) := by
  let _action := CFSG.SignalizerFunctor.Helpers.conjugationAction A K hAK
  obtain ⟨Q, hPQ, hQ⟩ := CFSG.SignalizerFunctor.Helpers.invariant_sylow_containing p r hp hr hA
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hK) (P.subgroupOf K) hP.comap_subtype
    (CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_subgroup A K P hAK hAP)
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hPK]
    exact Subgroup.map_mono hPQ
  · apply CFSG.SignalizerFunctor.Helpers.invariant_subgroup_map_normalized A K hAK
    change ∀ a : A, ∀ x ∈ (Q : Subgroup K), a • x ∈ (Q : Subgroup K)
    intro a x hx
    have hmem := Subgroup.smul_mem_pointwise_smul x a (Q : Subgroup K) hx
    rwa [← Sylow.pointwise_smul_def, hQ a] at hmem

theorem exists_conj_eq_of_isSylowOf_normalized_of_coprime [Finite G] {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) {A K R₁ R₂ : Subgroup G} (hA : IsPGroup p A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hK : ¬ p ∣ Nat.card K)
    (hR₁ : IsSylowOf r R₁ K) (hR₂ : IsSylowOf r R₂ K)
    (hAR₁ : A ≤ Subgroup.normalizer (R₁ : Set G)) (hAR₂ : A ≤ Subgroup.normalizer (R₂ : Set G)) :
    ∃ c ∈ K ⊓ Subgroup.centralizer (A : Set G), R₁.map (MulAut.conj c).toMonoidHom = R₂ := by
  obtain ⟨Q₁, rfl⟩ := hR₁
  obtain ⟨Q₂, rfl⟩ := hR₂
  let _action := CFSG.SignalizerFunctor.Helpers.conjugationAction A K hAK
  obtain ⟨g, hg, hfix⟩ :=
    CFSG.SignalizerFunctor.Helpers.invariant_sylows_conjugate_by_fixed_element p r hp hr A hA K
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hK) Q₁ Q₂
      (CFSG.SignalizerFunctor.Helpers.invariant_subgroup_sylow_fixed A K hAK r Q₁ hAR₁)
      (CFSG.SignalizerFunctor.Helpers.invariant_subgroup_sylow_fixed A K hAK r Q₂ hAR₂)
  refine ⟨g, Subgroup.mem_inf.mpr ⟨g.2, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := congrArg Subtype.val (hfix ⟨a, ha⟩)
    change a * (g : G) * a⁻¹ = g at h
    calc a * (g : G) = a * g * a⁻¹ * a := by group
      _ = g * a := by rw [h]
  · have hsmul : ((g • Q₁ : Sylow r K) : Subgroup K) =
        (Q₁ : Subgroup K).map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [← hg, hsmul, Subgroup.map_map, Subgroup.map_map]
    congr 1

theorem exists_isSylowOf_normalized_of_odd [Finite G] {r : ℕ} (hr : r.Prime) {A K : Subgroup G}
    (hA : IsPGroup 2 A) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hK : Odd (Nat.card K)) :
    ∃ R : Subgroup G, IsSylowOf r R K ∧ A ≤ Subgroup.normalizer (R : Set G) :=
  exists_isSylowOf_normalized_of_coprime Nat.prime_two hr hA hAK hK.not_two_dvd_nat

theorem exists_isSylowOf_normalized_ge_of_odd [Finite G] {r : ℕ} (hr : r.Prime)
    {A K P : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hK : Odd (Nat.card K)) (hPK : P ≤ K) (hP : IsPGroup r P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) :
    ∃ R : Subgroup G, IsSylowOf r R K ∧ P ≤ R ∧ A ≤ Subgroup.normalizer (R : Set G) :=
  exists_isSylowOf_normalized_ge_of_coprime Nat.prime_two hr hA hAK hK.not_two_dvd_nat hPK hP hAP

theorem exists_conj_eq_of_isSylowOf_normalized_of_odd [Finite G] {r : ℕ} (hr : r.Prime)
    {A K R₁ R₂ : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hK : Odd (Nat.card K)) (hR₁ : IsSylowOf r R₁ K) (hR₂ : IsSylowOf r R₂ K)
    (hAR₁ : A ≤ Subgroup.normalizer (R₁ : Set G)) (hAR₂ : A ≤ Subgroup.normalizer (R₂ : Set G)) :
    ∃ c ∈ K ⊓ Subgroup.centralizer (A : Set G), R₁.map (MulAut.conj c).toMonoidHom = R₂ :=
  exists_conj_eq_of_isSylowOf_normalized_of_coprime Nat.prime_two hr hA hAK hK.not_two_dvd_nat
    hR₁ hR₂ hAR₁ hAR₂

theorem IsPLocal.pCore_ne_bot {r : ℕ} {H : Subgroup G} (h : IsPLocal r H) :
    CFSG.pCore r H ≠ ⊥ := by
  obtain ⟨R, hR, hRp, rfl⟩ := h
  intro hbot
  have hle : R.subgroupOf (Subgroup.normalizer (R : Set G)) ≤
      CFSG.pCore r (Subgroup.normalizer (R : Set G)) :=
    le_sSup ⟨Subgroup.normal_in_normalizer, hRp.comap_subtype⟩
  rw [hbot, le_bot_iff] at hle
  apply hR
  rw [← Subgroup.map_subgroupOf_eq_of_le (Subgroup.le_normalizer : R ≤ _), hle, Subgroup.map_bot]

theorem oddCoreIn_ne_bot_of_isPLocal [Finite G] {r : ℕ} {H : Subgroup G} (hr : r.Prime)
    (hr2 : r ≠ 2) (h : IsPLocal r H) : oddCoreIn H ≠ ⊥ := by
  obtain ⟨R, hR, hRp, rfl⟩ := h
  have : Fact r.Prime := ⟨hr⟩
  have hodd : Odd (Nat.card R) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    rw [hk]
    exact (hr.eq_two_or_odd'.resolve_left hr2).pow
  have hle := le_oddCoreIn Subgroup.le_normalizer le_rfl hodd
  intro hbot
  rw [hbot, le_bot_iff] at hle
  exact hR hle

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

theorem two_not_dvd_card_ON : ¬ 2 ∣ Nat.card σ.ON :=
  σ.odd_card_ON.not_two_dvd_nat

theorem prime_ne_two_of_dvd_ON {r : ℕ} : r.Prime → r ∣ Nat.card σ.ON → r ≠ 2 :=
  fun _ hdvd h2 => σ.two_not_dvd_card_ON (h2 ▸ hdvd)

theorem L₀_subset_inf_N_mul_ON (hσ : σ.IsValid) {H : Subgroup G}
    (hcov : (σ.L₀ : Set G) ⊆ (H : Set G) * (σ.ON : Set G)) :
    (σ.L₀ : Set G) ⊆ ((H ⊓ σ.N : Subgroup G) : Set G) * (σ.ON : Set G) :=
  subset_inf_mul_of_subset_mul hσ.L₀_le_N σ.ON_le_N hcov

theorem L_subset_inf_N_mul_ON_of_cover (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {H : Subgroup G} (hDH : σ.D ≤ H) (hcov : (σ.L₀ : Set G) ⊆ (H : Set G) * (σ.ON : Set G)) :
    (σ.L : Set G) ⊆ ((H ⊓ σ.N : Subgroup G) : Set G) * (σ.ON : Set G) := by
  have hnorm : H ⊓ σ.N ≤ Subgroup.normalizer (σ.ON : Set G) :=
    inf_le_right.trans σ.N_le_normalizer_ON
  rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm, SetLike.coe_subset_coe,
    hII.L_eq]
  refine sup_le (fun l hl => ?_) ?_
  · have h1 := σ.L₀_subset_inf_N_mul_ON hσ hcov hl
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at h1
    exact h1
  · exact inf_le_left.trans ((le_inf hDH (σ.D_le_N hσ)).trans le_sup_left)

theorem exists_sylow_two_le_inf_L (hσ : σ.IsValid) {H : Subgroup G}
    (hcovL : (σ.L : Set G) ⊆ (H : Set G) * (σ.ON : Set G)) :
    ∃ P : Sylow 2 G, (P : Subgroup G) ≤ H ⊓ σ.L :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exists_sylow_le_inf_of_subset_mul σ.S le_sup_right (hσ.ON_le_L₀.trans le_sup_left)
    ((sup_le hσ.L₀_le_N (σ.S_le_N hσ)).trans σ.N_le_normalizer_ON) σ.two_not_dvd_card_ON hcovL

theorem oddCoreIn_inf_N_le_ON_of_cover (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {H : Subgroup G} (hcov : (σ.L₀ : Set G) ⊆ (H : Set G) * (σ.ON : Set G)) :
    oddCoreIn H ⊓ σ.N ≤ σ.ON := by
  refine le_trans ?_
    (hII.N_oddCore_of_cover (H ⊓ σ.N) inf_le_right (σ.L₀_subset_inf_N_mul_ON hσ hcov))
  apply le_oddCoreIn (inf_le_inf_right _ (oddCoreIn_le H))
  · exact (le_inf (inf_le_left.trans (le_normalizer_oddCoreIn H))
      (inf_le_right.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  · exact (odd_card_oddCoreIn H).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem ON_inf_le_oddCoreIn_of_sup_eq {H : Subgroup G} (hfac : oddCoreIn H ⊔ (H ⊓ σ.N) = H) :
    σ.ON ⊓ H ≤ oddCoreIn H := by
  have hXH : oddCoreIn H ⊔ (σ.ON ⊓ H) ≤ H := sup_le (oddCoreIn_le H) inf_le_right
  have hON : H ⊓ σ.N ≤ Subgroup.normalizer ((σ.ON ⊓ H : Subgroup G) : Set G) :=
    (le_inf (inf_le_right.trans σ.N_le_normalizer_ON)
      (inf_le_left.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hnorm : H ≤ Subgroup.normalizer ((oddCoreIn H ⊔ (σ.ON ⊓ H) : Subgroup G) : Set G) :=
    hfac.ge.trans (sup_le (le_sup_left.trans Subgroup.le_normalizer)
      ((le_inf (inf_le_left.trans (le_normalizer_oddCoreIn H)) hON).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)))
  have hodd : Odd (Nat.card (oddCoreIn H ⊔ (σ.ON ⊓ H) : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd (inf_le_right.trans (le_normalizer_oddCoreIn H))
      (odd_card_oddCoreIn H) (σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  exact le_sup_right.trans (le_oddCoreIn hXH hnorm hodd)

theorem exists_sylow_ON_normalized_le_oddCoreIn (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    {H : Subgroup G} (hDH : σ.D ≤ H) (hON : σ.ON ⊓ H ≤ oddCoreIn H) {R₀ : Subgroup G}
    (hR₀ : IsSylowOf r R₀ σ.ON) (hR₀H : R₀ ≤ H) :
    ∃ R : Subgroup G, IsSylowOf r R σ.ON ∧ σ.D ≤ Subgroup.normalizer (R : Set G) ∧
      R ≤ oddCoreIn H := by
  have : Fact r.Prime := ⟨hr⟩
  have hR₀K : IsSylowOf r R₀ (σ.ON ⊓ H) := hR₀.of_le (le_inf hR₀.le hR₀H) inf_le_left
  have hDK : σ.D ≤ Subgroup.normalizer ((σ.ON ⊓ H : Subgroup G) : Set G) :=
    (le_inf ((σ.D_le_N hσ).trans σ.N_le_normalizer_ON)
      (hDH.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  obtain ⟨R, hR, hDR⟩ := exists_isSylowOf_normalized_of_odd hr hD2 hDK
    (σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  refine ⟨R, isSylowOf_of_card (hR.le.trans inf_le_left) ?_, hDR, hR.le.trans hON⟩
  rw [hR.card_eq, ← hR₀K.card_eq]
  exact hR₀.card_eq

theorem familyL_properties (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : r.Prime)
    (hdiv : r ∣ Nat.card σ.ON) {H : Subgroup G} (hH : H ∈ σ.familyL r) :
    CFSG.ABGQGroups.HasQCharPower H σ.q ∧
      oddCoreIn H ⊔ (H ⊓ σ.N) = H ∧
      (σ.L : Set G) ⊆ (H : Set G) * (σ.ON : Set G) ∧
      (∃ P : Sylow 2 G, (P : Subgroup G) ≤ H ⊓ σ.L) ∧
      (oddCoreIn H ⊓ σ.N ≤ σ.ON ∧ σ.ON ⊓ H ≤ oddCoreIn H) ∧
      (∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r R σ.ON ∧
        σ.D ≤ Subgroup.normalizer (R : Set G) ∧ R ≤ oddCoreIn H) := by
  obtain ⟨hloc, hcov, hDH, R₀, hR₀, hR₀H⟩ := hH
  have hO : oddCoreIn H ≠ ⊥ :=
    oddCoreIn_ne_bot_of_isPLocal hr (σ.prime_ne_two_of_dvd_ON hr hdiv) hloc
  obtain ⟨hQ, hfac⟩ := hII.cover_qgroup H ((σ.T_le_D hσ).trans hDH) hO hcov
  have hLH : (σ.L : Set G) ⊆ (H : Set G) * (σ.ON : Set G) :=
    (σ.L_subset_inf_N_mul_ON_of_cover hσ hII hDH hcov).trans
      (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr inf_le_left))
  have hON := σ.ON_inf_le_oddCoreIn_of_sup_eq hfac
  exact ⟨hQ, hfac, hLH, σ.exists_sylow_two_le_inf_L hσ hLH,
    ⟨σ.oddCoreIn_inf_N_le_ON_of_cover hσ hII hcov, hON⟩,
    σ.exists_sylow_ON_normalized_le_oddCoreIn hσ hr hDH hON hR₀ hR₀H⟩

end Setting

end CFSG.ABGTheoremB
