module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D5LiftA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sec8t84d5_lift {N E P : Subgroup G} {t : G} (hEN : E ≤ N) (hE2 : IsPGroup 2 E)
    (hM : ((E ⊔ oddCoreIn N).subgroupOf N).Normal) (htN : t ∈ N) (ht2 : t * t = 1)
    (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) (hPN : P ≤ N) (hP2 : IsPGroup 2 P)
    (hPt : ∀ p ∈ P, t * p = p * t) :
    ∃ P' : Subgroup G, P' ≤ N ⊓ normalizer (E : Set G) ∧ IsPGroup 2 P' ∧
      (∀ p ∈ P', t * p = p * t) ∧ P' ⊓ oddCoreIn N = ⊥ ∧ P' ⊔ oddCoreIn N = P ⊔ oddCoreIn N := by
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set Q : Subgroup G := oddCoreIn N with hQ
  set M : Subgroup G := E ⊔ Q with hMdef
  have hQN : Q ≤ N := (oddCoreIn_normal N).1
  have hQnormN : (Q.subgroupOf N).Normal := (oddCoreIn_normal N).2
  have hQodd : Odd (Nat.card Q) := odd_card_oddCoreIn N
  have hEleM : E ≤ M := le_sup_left
  have hQleM : Q ≤ M := le_sup_right
  have hMleN : M ≤ N := sup_le hEN hQN
  have hMnormN : (M.subgroupOf N).Normal := hM
  have hNleNormM : N ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMleN).mp hMnormN
  have htM : t ∈ Subgroup.normalizer (M : Set G) := hNleNormM htN
  have hNleNormQ : N ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mp hQnormN
  have htQ : t ∈ Subgroup.normalizer (Q : Set G) := hNleNormQ htN
  have hPnorm : P ≤ Subgroup.normalizer (Q : Set G) := hPN.trans hNleNormQ
  have htE' : t ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => htE e he, fun he => ?_⟩
    have h := htE (t * e * t⁻¹) he
    have heq : t * (t * e * t⁻¹) * t⁻¹ = e := by
      rw [ht_inv]
      calc t * (t * e * t) * t = (t * t) * e * (t * t) := by group
        _ = e := by rw [ht2]; group
    rwa [heq] at h
  have htP : t ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.centralizer_le_normalizer (P : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun p hp => (hPt p hp).symm)
  have hEsyl : IsSylow2Of E M :=
    sec8t84d5_isSylow2Of_sup_of_normal_odd hEN hE2 hQN hQnormN hQodd
  set V : Subgroup G := M ⊔ P with hVdef
  set NE : Subgroup G := V ⊓ Subgroup.normalizer (E : Set G) with hNEdef
  have hPleV : P ≤ V := le_sup_right
  have hMleV : M ≤ V := le_sup_left
  have hQleV : Q ≤ V := hQleM.trans hMleV
  have hVleN : V ≤ N := sup_le hMleN hPN
  have hMnormV : (M.subgroupOf V).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMleV]
    exact hVleN.trans hNleNormM
  have hVleNormM : V ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMleV).mp hMnormV
  have hEleNE : E ≤ NE := by
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hMleV (hEleM hx), Subgroup.le_normalizer hx⟩
  have hFrattini : V = M ⊔ NE := by
    apply le_antisymm
    · intro v hv
      obtain ⟨a, ha, hae⟩ :=
        sec8t84d5_exists_mul_mem_sup_normalizer hEsyl (hVleNormM hv)
      have hva : v = a * (a⁻¹ * v) := by group
      rw [hva]
      refine Subgroup.mul_mem_sup ha ?_
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMleV ha)) hv, hae⟩
    · exact sup_le hMleV inf_le_left
  have hVQ : V = Q ⊔ NE := by
    rw [hFrattini, hMdef, sup_assoc, sup_eq_right.mpr (hEleNE.trans le_sup_right)]
  have hVmap : V.map (MulAut.conj t) = V := by
    rw [hVdef, Subgroup.map_sup,
      show M.map (MulAut.conj t) = M from Subgroup.mem_normalizer_iff_map_conj_eq.mp htM,
      show P.map (MulAut.conj t) = P from Subgroup.mem_normalizer_iff_map_conj_eq.mp htP]
  have htV : t ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hVmap
  have hPQmap : (P ⊔ Q).map (MulAut.conj t) = P ⊔ Q := by
    rw [Subgroup.map_sup,
      show P.map (MulAut.conj t) = P from Subgroup.mem_normalizer_iff_map_conj_eq.mp htP,
      show Q.map (MulAut.conj t) = Q from Subgroup.mem_normalizer_iff_map_conj_eq.mp htQ]
  have htPQ : t ∈ Subgroup.normalizer (↑(P ⊔ Q) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPQmap
  set K : Subgroup G := NE ⊓ (P ⊔ Q) with hKdef
  have hKleNE : K ≤ NE := inf_le_left
  have hNEleV : NE ≤ V := inf_le_left
  have hKleV : K ≤ V := hKleNE.trans hNEleV
  have hKleN : K ≤ N := hKleV.trans hVleN
  have hKlePQ : K ≤ P ⊔ Q := inf_le_right
  have hKQle : K ≤ Subgroup.normalizer (Q : Set G) := hKleN.trans hNleNormQ
  have hKQ : K ⊔ Q = P ⊔ Q := by
    apply le_antisymm
    · exact sup_le hKlePQ le_sup_right
    · apply sup_le _ le_sup_right
      intro x hx
      have hxV : x ∈ V := (sup_le hPleV hQleV) (Subgroup.mem_sup_left hx)
      have hxV' : x ∈ (↑(NE ⊔ Q) : Set G) := by
        rw [sup_comm, ← hVQ]
        exact hxV
      rw [Subgroup.coe_mul_of_left_le_normalizer_right NE Q
        (hNEleV.trans (hVleN.trans hNleNormQ))] at hxV'
      obtain ⟨n, hn, q, hq, hnq⟩ := hxV'
      have hnK : n ∈ K := by
        rw [hKdef]
        refine Subgroup.mem_inf.mpr ⟨hn, ?_⟩
        have hn_eq : n = x * q⁻¹ := by rw [← hnq]; group
        rw [hn_eq]
        exact Subgroup.mul_mem_sup hx (Subgroup.inv_mem _ hq)
      rw [← hnq]
      exact Subgroup.mul_mem_sup hnK hq
  have hconjK : ∀ {s : G}, s ∈ Subgroup.normalizer (V : Set G) →
      s ∈ Subgroup.normalizer (E : Set G) →
      s ∈ Subgroup.normalizer (↑(P ⊔ Q) : Set G) → K.map (MulAut.conj s) ≤ K := by
    intro s hsV hsE hsPQ y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hKdef] at hx ⊢
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp hsV x).mp hx.1.1,
         sec8t84d5_conj_mem_normalizer hsE hx.1.2⟩,
       (Subgroup.mem_normalizer_iff.mp hsPQ x).mp hx.2⟩
  have htK : t ∈ Subgroup.normalizer (K : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm (hconjK htV htE' htPQ)
    have h2 := hconjK (Subgroup.inv_mem _ htV) (Subgroup.inv_mem _ htE')
      (Subgroup.inv_mem _ htPQ)
    intro y hy
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj t⁻¹) y, ?_, ?_⟩
    · exact h2 (Subgroup.mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hy)
    · show (MulAut.conj t) ((MulAut.conj t⁻¹) y) = y
      simp only [MulAut.conj_apply]
      group
  let φ : ↥K ≃* ↥K :=
    { toFun := fun x => ⟨t * (x : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htK (x : G)).mp x.2⟩
      invFun := fun x => ⟨t⁻¹ * (x : G) * t,
        (Subgroup.mem_normalizer_iff.mp htK (t⁻¹ * (x : G) * t)).mpr (by
          convert x.2 using 1; group)⟩
      left_inv := fun x => by ext; group
      right_inv := fun x => by ext; group
      map_mul' := fun x y => by
        ext
        simp only [Subgroup.coe_mul]
        group }
  have hφ2 : φ ^ 2 = 1 := by
    ext x
    show t * (t * (x : G) * t⁻¹) * t⁻¹ = (x : G)
    rw [ht_inv]
    calc t * (t * (x : G) * t) * t = (t * t) * (x : G) * (t * t) := by group
      _ = (x : G) := by rw [ht2]; group
  let σ : Equiv.Perm (Sylow 2 ↥K) := MulAction.toPermHom (MulAut ↥K) (Sylow 2 ↥K) φ
  have hσ2 : σ ^ 2 = 1 := by
    change (MulAction.toPermHom (MulAut ↥K) (Sylow 2 ↥K) φ) ^ 2 = 1
    rw [← map_pow, hφ2, map_one]
  haveI : Fintype (Sylow 2 ↥K) := Fintype.ofFinite _
  have hodd : ¬ 2 ∣ Fintype.card (Sylow 2 ↥K) := by
    rw [← Nat.card_eq_fintype_card]
    exact not_dvd_card_sylow 2 ↥K
  obtain ⟨P', hP'⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hodd (by simpa using hσ2)
  have hP'' : φ • P' = P' := hP'
  have hfix : φ • (P' : Subgroup ↥K) = (P' : Subgroup ↥K) := by
    rw [← Sylow.pointwise_smul_def, hP'']
  have hmem : ∀ x : ↥K, x ∈ (P' : Subgroup ↥K) → φ x ∈ (P' : Subgroup ↥K) := by
    intro x hx
    have h1 : φ • x ∈ φ • (P' : Subgroup ↥K) :=
      Subgroup.smul_mem_pointwise_smul x φ (P' : Subgroup ↥K) hx
    rw [hfix] at h1
    simpa using h1
  let PG : Subgroup G := (P' : Subgroup ↥K).map K.subtype
  have hPG2 : IsPGroup 2 PG := P'.isPGroup'.map K.subtype
  have hPGleK : PG ≤ K := Subgroup.map_subtype_le _
  have hPGlePQ : PG ≤ P ⊔ Q := hPGleK.trans hKlePQ
  have hP'Q : PG ⊓ Q = ⊥ := by
    have hdisj : Disjoint PG Q :=
      IsPGroup.disjoint_of_coprime hPG2 (IsPGroup.card (G := Q))
        (Nat.coprime_two_left.mpr hQodd)
    exact disjoint_iff.mp hdisj
  have hPGle : PG ≤ N ⊓ Subgroup.normalizer (E : Set G) := by
    intro x hx
    have hxNE : x ∈ NE := hPGleK.trans hKleNE hx
    exact Subgroup.mem_inf.mpr ⟨hVleN hxNE.1, hxNE.2⟩
  have htPG : ∀ x ∈ PG, t * x * t⁻¹ ∈ PG := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Subgroup.mem_map_of_mem K.subtype (hmem y hy)
  have hcentral : ∀ p ∈ PG, t * p = p * t := by
    intro p hp
    have hpK : p ∈ K := hPGleK hp
    have hpPQ : p ∈ P ⊔ Q := hKlePQ hpK
    have htp : t * p * t⁻¹ ∈ PG := htPG p hp
    have hmemQ : (t * p * t⁻¹) * p⁻¹ ∈ Q := by
      have hpPQ' : p ∈ (↑(P ⊔ Q) : Set G) := hpPQ
      rw [Subgroup.coe_mul_of_left_le_normalizer_right P Q hPnorm] at hpPQ'
      obtain ⟨p1, hp1, q, hq, hpq⟩ := hpPQ'
      have hconjp1 : t * p1 * t⁻¹ = p1 := by
        rw [hPt p1 hp1, mul_assoc, mul_inv_cancel, mul_one]
      have hqconj : t * q * t⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hNleNormQ htN) q).mp hq
      have hqmem : t * q * t⁻¹ * q⁻¹ ∈ Q :=
        Subgroup.mul_mem _ hqconj (Subgroup.inv_mem _ hq)
      have hp1conj : p1 * (t * q * t⁻¹ * q⁻¹) * p1⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hNleNormQ (hPN hp1)) _).mp hqmem
      have heq : (t * p * t⁻¹) * p⁻¹ = p1 * (t * q * t⁻¹ * q⁻¹) * p1⁻¹ := by
        rw [← hpq]
        rw [show t * (p1 * q) * t⁻¹ = (t * p1 * t⁻¹) * (t * q * t⁻¹) by group, hconjp1]
        group
      rwa [heq]
    have hone : (t * p * t⁻¹) * p⁻¹ = 1 := by
      have hmem : (t * p * t⁻¹) * p⁻¹ ∈ PG ⊓ Q :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ htp (Subgroup.inv_mem _ hp), hmemQ⟩
      rw [hP'Q] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hconj : t * p * t⁻¹ = p := by
      calc t * p * t⁻¹ = (t * p * t⁻¹) * p⁻¹ * p := by group
        _ = 1 * p := by rw [hone]
        _ = p := by group
    calc t * p = (t * p * t⁻¹) * t := by group
      _ = p * t := by rw [hconj]
  have hQnormK : (Q.subgroupOf K).Normal := by
    refine ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hNleNormQ (hKleN g.2)) (n : G)).mp
      (Subgroup.mem_subgroupOf.mp hn)
  have hquot : IsPGroup 2 (↥K ⧸ Q.subgroupOf K) := by
    haveI : (Q.subgroupOf K).Normal := hQnormK
    have hPQle : P ≤ Subgroup.normalizer (Q : Set G) := hPnorm
    have hPQ : P ⊓ Q = ⊥ := by
      have hdisj : Disjoint P Q :=
        IsPGroup.disjoint_of_coprime hP2 (IsPGroup.card (G := Q))
          (Nat.coprime_two_left.mpr hQodd)
      exact disjoint_iff.mp hdisj
    have e : ↥K ⧸ Q.subgroupOf K ≃* ↥P := by
      haveI : (Q.subgroupOf P).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hPQle
      haveI : (Q.subgroupOf (K ⊔ Q)).Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer hKQle
      haveI : (Q.subgroupOf (P ⊔ Q)).Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer hPQle
      have e1 := QuotientGroup.quotientInfEquivProdNormalizerQuotient K Q hKQle
      have e2 : ↥(K ⊔ Q) ⧸ Q.subgroupOf (K ⊔ Q) ≃*
          ↥(P ⊔ Q) ⧸ Q.subgroupOf (P ⊔ Q) :=
        QuotientGroup.equivQuotientSubgroupOfOfEq (A' := Q) (A := K ⊔ Q) (B' := Q)
          (B := P ⊔ Q) rfl hKQ
      have e3 := (QuotientGroup.quotientInfEquivProdNormalizerQuotient P Q hPQle).symm
      have hqP : Q.subgroupOf P = ⊥ :=
        Subgroup.subgroupOf_eq_bot.mpr (disjoint_iff.mpr (by rw [inf_comm]; exact hPQ))
      have e4 : ↥P ⧸ Q.subgroupOf P ≃* ↥P :=
        (QuotientGroup.quotientMulEquivOfEq hqP).trans (QuotientGroup.quotientBot (G := ↥P))
      exact (e1.trans e2).trans (e3.trans e4)
    exact hP2.of_equiv e.symm
  have hKle : K ≤ PG ⊔ Q := by
    haveI : (Q.subgroupOf K).Normal := hQnormK
    intro x hxK
    have hq : QuotientGroup.mk' (Q.subgroupOf K) ⟨x, hxK⟩ ∈
        (P' : Subgroup ↥K).map (QuotientGroup.mk' (Q.subgroupOf K)) := by
      have htop : (P'.mapSurjective (QuotientGroup.mk'_surjective (Q.subgroupOf K)) :
          Subgroup (↥K ⧸ Q.subgroupOf K)) = ⊤ :=
        ((P'.mapSurjective (QuotientGroup.mk'_surjective (Q.subgroupOf K))).is_maximal'
          (hquot.to_subgroup ⊤) le_top).symm
      rw [Sylow.coe_mapSurjective] at htop
      rw [htop]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_map] at hq
    obtain ⟨y, hyP, hyq⟩ := hq
    have hyker : y⁻¹ * ⟨x, hxK⟩ ∈ Q.subgroupOf K := by
      rw [← QuotientGroup.ker_mk' (N := Q.subgroupOf K), MonoidHom.mem_ker, map_mul, map_inv, hyq]
      group
    have hx_eq : x = (y : G) * (((y⁻¹ * ⟨x, hxK⟩ : ↥K) : G)) := by
      have := congrArg Subtype.val (show (⟨x, hxK⟩ : ↥K) = y * (y⁻¹ * ⟨x, hxK⟩) by group)
      simpa using this
    rw [hx_eq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem K.subtype hyP)
      (Subgroup.mem_subgroupOf.mp hyker)
  have hPGQ : PG ⊔ Q = P ⊔ Q := by
    apply le_antisymm
    · exact sup_le hPGlePQ le_sup_right
    · calc P ⊔ Q = K ⊔ Q := hKQ.symm
        _ ≤ PG ⊔ Q := sup_le hKle le_sup_right
  exact ⟨PG, hPGle, hPG2, hcentral, hP'Q, hPGQ⟩

theorem sec8t84d5_equiv_of_sup_eq {A B Q : Subgroup G} (hA : A ⊓ Q = ⊥) (hB : B ⊓ Q = ⊥)
    (hsup : A ⊔ Q = B ⊔ Q) (hn : ∀ x ∈ A ⊔ Q, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) :
    Nonempty (↥A ≃* ↥B) := by
  have hAle : A ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha q hq
    exact hn a (Subgroup.mem_sup_left ha) q hq
  have hBle : B ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb q hq
    exact hn b (by rw [hsup]; exact Subgroup.mem_sup_left hb) q hq
  have hdisjA : Disjoint Q A := disjoint_iff.mpr (by rw [inf_comm]; exact hA)
  have hdisjB : Disjoint Q B := disjoint_iff.mpr (by rw [inf_comm]; exact hB)
  have hqA : Q.subgroupOf A = ⊥ := Subgroup.subgroupOf_eq_bot.mpr hdisjA
  have hqB : Q.subgroupOf B = ⊥ := Subgroup.subgroupOf_eq_bot.mpr hdisjB
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hAle
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAle
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hBle
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBle
  have eA : ↥A ≃* ↥(A ⊔ Q) ⧸ Q.subgroupOf (A ⊔ Q) := by
    have h := QuotientGroup.quotientInfEquivProdNormalizerQuotient A Q hAle
    exact ((QuotientGroup.quotientBot (G := ↥A)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hqA).symm).trans h
  have eB : ↥B ≃* ↥(B ⊔ Q) ⧸ Q.subgroupOf (B ⊔ Q) := by
    have h := QuotientGroup.quotientInfEquivProdNormalizerQuotient B Q hBle
    exact ((QuotientGroup.quotientBot (G := ↥B)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hqB).symm).trans h
  refine ⟨eA.trans ?_⟩
  exact (QuotientGroup.equivQuotientSubgroupOfOfEq (A' := Q) (A := A ⊔ Q)
    (B' := Q) (B := B ⊔ Q) rfl hsup).trans eB.symm

end CFSG.OddStandard.SmallF3.Omega
