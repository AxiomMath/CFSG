module

public import CFSG.Open.GLBDefs
import CFSG.LocalAnalysis.GL83PartI.I_24_3.InnerAux
import CFSG.LocalAnalysis.GL83PartI.I_24_3.InnerPGroup
import CFSG.LocalAnalysis.PreuniquenessRankFour.RankTwo
import CFSG.LocalAnalysis.SectionRank.OddCover.CoverTools
import CFSG.LocalAnalysis.ComponentClassification.Components
import CFSG.Walter.AStar.Subnormal

public section

namespace GL83.I243.Inner

open CFSG.Open

variable {X : Type*} [Group X] [Finite X]

theorem exists_noncommuting_of_perfect {p : ℕ} [Fact p.Prime] {K : Subgroup X}
    (hperf : commutator K = ⊤) (P : Sylow p K) {z : X} (hzK : z ∈ K)
    (hzc : z ∈ Subgroup.centralizer (K : Set X)) (hzp : orderOf z = p) :
    ∃ x ∈ (P : Subgroup K).map K.subtype, ∃ y ∈ (P : Subgroup K).map K.subtype, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  haveI : Group.IsPerfect K := ⟨hperf⟩
  have hcomm : ∀ x ∈ (P : Subgroup K), ∀ y ∈ (P : Subgroup K), x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hcon x (Subgroup.mem_map_of_mem _ hx) y (Subgroup.mem_map_of_mem _ hy))
  obtain ⟨Cp⟩ : Nonempty (Sylow p (QuotientGroup.mk' (Subgroup.center K)).ker) := inferInstance
  have hbot := CFSG.SectionRank.OddCover.sylow_kernel_eq_bot_of_commute
    (QuotientGroup.mk' (Subgroup.center K)) (by rw [QuotientGroup.ker_mk']) P hcomm Cp
  have hzcen : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc g g.2)
  have hdvd : p ∣ Nat.card (QuotientGroup.mk' (Subgroup.center K)).ker := by
    rw [QuotientGroup.ker_mk']
    have h := orderOf_dvd_natCard (⟨⟨z, hzK⟩, hzcen⟩ : Subgroup.center K)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hzp] at h
  exact Sylow.ne_bot_of_dvd_card Cp hdvd hbot

theorem three_le_pRank_of_mem_centralizer {p : ℕ} (hp : p.Prime) {D H : Subgroup X}
    (hD : IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2) {x : X} (hxp : orderOf x = p)
    (hxD : x ∉ D) (hxC : x ∈ Subgroup.centralizer (D : Set X)) (hDH : D ≤ H) (hxH : x ∈ H) :
    3 ≤ pRank p H := by
  have hxp1 : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hDx : D ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup X) : Set X) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hxC)
  have hJ := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p hD
    (isElemAbelian_zpowers hxp1) hDx
  have hJH : D ⊔ Subgroup.zpowers x ≤ H := sup_le hDH (Subgroup.zpowers_le.mpr hxH)
  by_contra hlt
  have heq := CFSG.PreuniquenessRankFour.Helpers.elementary_subgroup_eq_of_rank_bound p hp hJ
    le_sup_left 2 hDcard
    (by have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hJH; omega)
  exact hxD (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

theorem isCyclic_inf_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (R : Sylow p X)
    {K : Subgroup X} (hKR : ¬ K ≤ GLBWeakCore p (R : Subgroup X)) {x y : X} (hxK : x ∈ K)
    (hxR : x ∈ (R : Subgroup X)) (hxp : x ^ p = 1) (hyK : y ∈ K) (hxy : x * y ≠ y * x) :
    IsCyclic ↥((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hncyc
  have hC0p : IsPGroup p ↥((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)) :=
    R.isPGroup'.to_le inf_le_left
  obtain ⟨D, hDC0, hD, hDcard⟩ := exists_isElemAbelian_card_sq_of_not_isCyclic hp2 hC0p hncyc
  have hDR : D ≤ (R : Subgroup X) := hDC0.trans inf_le_left
  have hDC : D ≤ Subgroup.centralizer (K : Set X) := hDC0.trans inf_le_right
  have hKD : K ≤ Subgroup.centralizer (D : Set X) := Subgroup.le_centralizer_iff.mp hDC
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxy (by rw [one_mul, mul_one])
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxD : x ∉ D := fun hxD =>
    hxy (Subgroup.mem_centralizer_iff.mp (hDC hxD) y hyK).symm
  have hxC : x ∈ Subgroup.centralizer (D : Set X) := hKD hxK
  have hrank2 : 2 ≤ pRank p D :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp D) ⟨D, le_rfl, hD, hDcard⟩
  have hrank3 : 3 ≤ pRank p (D ⊔ ((R : Subgroup X) ⊓ Subgroup.centralizer (D : Set X))) :=
    three_le_pRank_of_mem_centralizer hp hD hDcard hxord hxD hxC le_sup_left
      (Subgroup.mem_sup_right ⟨hxR, hxC⟩)
  have hN := CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p hDR hrank2 hrank3
  exact hKR (hKD.trans ((Subgroup.centralizer_le_normalizer _).trans hN))

theorem exists_mul_mem_inf_of_inner {p : ℕ} [Fact p.Prime] {R K B : Subgroup X}
    (P : Sylow p K) (hP : (P : Subgroup K).map K.subtype = R ⊓ K)
    (hBR : B ≤ R) (hBp : ∀ b ∈ B, b ^ p = 1) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hinner : ∀ b ∈ B, ∃ k ∈ K, ∀ y ∈ K, b * y * b⁻¹ = k * y * k⁻¹) {b : X} (hb : b ∈ B) :
    ∃ t ∈ R ⊓ K, ∃ c ∈ R ⊓ Subgroup.centralizer (K : Set X), b = t * c := by
  obtain ⟨k, hk, hbk⟩ := hinner b hb
  have hbR : b ∈ R := hBR hb
  have hbN : ∀ y ∈ K, b * y * b⁻¹ ∈ K := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hBN hb) y).mp hy
  have hbN' : ∀ y ∈ K, b⁻¹ * y * b ∈ K := by
    intro y hy
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hBN hb)) y).mp hy
    rwa [inv_inv] at h
  have hc : k⁻¹ * b ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hbk y hy
    calc y * (k⁻¹ * b) = k⁻¹ * (k * y * k⁻¹) * b := by group
      _ = k⁻¹ * (b * y * b⁻¹) * b := by rw [h]
      _ = k⁻¹ * b * y := by group
  have hbkc : b = k * (k⁻¹ * b) := by group
  have hkc : Commute k (k⁻¹ * b) := Subgroup.mem_centralizer_iff.mp hc k hk
  have hkp : k ^ p ∈ Subgroup.centralizer (K : Set X) := by
    have h1 : (k * (k⁻¹ * b)) ^ p = k ^ p * (k⁻¹ * b) ^ p := hkc.mul_pow p
    have h2 : k ^ p * (k⁻¹ * b) ^ p = 1 := by
      rw [← h1, ← hbkc]
      exact hBp b hb
    have h3 : k ^ p = ((k⁻¹ * b) ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [h3]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc p)
  have hbk' : ∀ y ∈ K, b⁻¹ * y * b = k⁻¹ * y * k := by
    intro y hy
    have h := hbk (k⁻¹ * y * k) (K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk)
    calc b⁻¹ * y * b = b⁻¹ * (k * (k⁻¹ * y * k) * k⁻¹) * b := by group
      _ = b⁻¹ * (b * (k⁻¹ * y * k) * b⁻¹) * b := by rw [h]
      _ = k⁻¹ * y * k := by group
  have hnorm : ∀ y ∈ K, y ∈ R ⊓ K ↔ k * y * k⁻¹ ∈ R ⊓ K := by
    intro y hy
    constructor
    · rintro ⟨hyR, hyK⟩
      rw [← hbk y hy]
      exact ⟨R.mul_mem (R.mul_mem hbR hyR) (R.inv_mem hbR), hbN y hyK⟩
    · rintro ⟨hyR', hyK'⟩
      have hy' : y = b⁻¹ * (k * y * k⁻¹) * b := by
        rw [hbk' _ hyK']
        group
      rw [hy']
      exact ⟨R.mul_mem (R.mul_mem (R.inv_mem hbR) hyR') hbR, hbN' _ hyK'⟩
  obtain ⟨n, hn, hkn⟩ := exists_pow_mem_of_sylow_map P hP hk hnorm
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr hn
  obtain ⟨a, a', hka⟩ := exists_zpow_mul_zpow k hcop
  obtain ⟨z₀, hz₀, t, ht, hkzt⟩ : ∃ z₀ ∈ Subgroup.centralizer (K : Set X), ∃ t ∈ R ⊓ K,
      k = z₀ * t :=
    ⟨(k ^ p) ^ a, Subgroup.zpow_mem _ hkp a, (k ^ n) ^ a', Subgroup.zpow_mem _ hkn a', hka⟩
  have htz : z₀ * t = t * z₀ := (Subgroup.mem_centralizer_iff.mp hz₀ t ht.2).symm
  have hb_eq : b = t * (z₀ * (k⁻¹ * b)) := by
    calc b = k * (k⁻¹ * b) := hbkc
      _ = z₀ * t * (k⁻¹ * b) := by rw [← hkzt]
      _ = t * z₀ * (k⁻¹ * b) := by rw [htz]
      _ = t * (z₀ * (k⁻¹ * b)) := by rw [mul_assoc]
  refine ⟨t, ht, z₀ * (k⁻¹ * b), ⟨?_, Subgroup.mul_mem _ hz₀ hc⟩, hb_eq⟩
  have h : z₀ * (k⁻¹ * b) = t⁻¹ * b := by
    rw [eq_inv_mul_iff_mul_eq, ← hb_eq]
  rw [h]
  exact R.mul_mem (R.inv_mem ht.1) hbR

end GL83.I243.Inner

namespace GL83.I243

open CFSG.Open GL83.I243.Inner

theorem false_of_inner
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (R : Sylow p X)
    {B K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hKR : ¬ K ≤ GLBWeakCore p (R : Subgroup X))
    (hBR : B ≤ (R : Subgroup X)) (hBel : IsElemAbelian p B) (hB3 : p ^ 3 ≤ Nat.card B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    {z : X} (hzB : z ∈ B) (hzK : z ∈ K) (hzc : z ∈ Subgroup.centralizer (K : Set X))
    (hzp : orderOf z = p)
    (hCB : ∀ b ∈ B, b ∈ Subgroup.centralizer (K : Set X) → b ∈ Subgroup.zpowers z)
    (hinner : ∀ b ∈ B, ∃ k ∈ K, ∀ y ∈ K, b * y * b⁻¹ = k * y * k⁻¹)
    (hK4 : ¬ p ^ 4 ∣ Nat.card K) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hTcard : Nat.card ↥((R : Subgroup X) ⊓ K) ≤ p ^ 3 := card_le_of_sylow_map P hP hK4
  have hTp : IsPGroup p ↥((R : Subgroup X) ⊓ K) := R.isPGroup'.to_le inf_le_left
  have hTnc := exists_noncommuting_of_perfect hK.2.2.1 P hzK hzc hzp
  rw [hP] at hTnc
  obtain ⟨x, hxT, hxp, y, hyT, hxy⟩ := exists_pow_eq_one_not_central hp2 hTp hTnc hTcard
  have hcyc : IsCyclic ↥((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)) :=
    isCyclic_inf_centralizer hp hp2 R hKR hxT.2 hxT.1 hxp hyT.2 hxy
  have hdec : ∀ b ∈ B, ∃ t ∈ (R : Subgroup X) ⊓ K,
      ∃ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), b = t * c := fun b hb =>
    exists_mul_mem_inf_of_inner P hP hBR hBel.2 hBN hinner hb
  have hC0comm : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X),
      ∀ c' ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), c * c' = c' * c :=
    fun c hc c' hc' => congrArg Subtype.val (mul_comm' (⟨c, hc⟩ : ↥((R : Subgroup X) ⊓
      Subgroup.centralizer (K : Set X))) ⟨c', hc'⟩)
  have hTC0 : ∀ t ∈ (R : Subgroup X) ⊓ K,
      ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), t * c = c * t :=
    fun t ht c hc => Subgroup.mem_centralizer_iff.mp hc.2 t ht.2
  have hBC0 : ∀ b ∈ B, ∀ c' ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X),
      b * c' = c' * b := by
    intro b hb c' hc'
    obtain ⟨t, ht, c, hc, rfl⟩ := hdec b hb
    calc t * c * c' = t * (c * c') := mul_assoc _ _ _
      _ = t * (c' * c) := by rw [hC0comm c hc c' hc']
      _ = (t * c') * c := (mul_assoc _ _ _).symm
      _ = (c' * t) * c := by rw [hTC0 t ht c' hc']
      _ = c' * (t * c) := mul_assoc _ _ _
  have hBle : B ≤ ((R : Subgroup X) ⊓ K) ⊔
      ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)) := by
    intro b hb
    obtain ⟨t, ht, c, hc, rfl⟩ := hdec b hb
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hc)
  have hBinf : Nat.card ↥(B ⊓ ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X))) ≤ p := by
    have hle : B ⊓ ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)) ≤
        Subgroup.zpowers z := fun b hb => hCB b hb.1 hb.2.2
    calc Nat.card ↥(B ⊓ ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)))
        ≤ Nat.card ↥(Subgroup.zpowers z) := Subgroup.card_le_of_le hle
      _ = p := by rw [Nat.card_zpowers, hzp]
  have hTinf : p ≤ Nat.card ↥(((R : Subgroup X) ⊓ K) ⊓
      ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X))) := by
    have hzT : z ∈ ((R : Subgroup X) ⊓ K) ⊓
        ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)) :=
      ⟨⟨hBR hzB, hzK⟩, hBR hzB, hzc⟩
    have hle : Subgroup.zpowers z ≤ ((R : Subgroup X) ⊓ K) ⊓
        ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)) := Subgroup.zpowers_le.mpr hzT
    calc p = Nat.card ↥(Subgroup.zpowers z) := by rw [Nat.card_zpowers, hzp]
      _ ≤ _ := Subgroup.card_le_of_le hle
  have hTle := le_sup_of_card_le hp.pos hTC0 hBC0 hBle hTcard hB3 hTinf hBinf
  haveI : IsMulCommutative B := hBel.1
  have hBcomm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : B) ⟨b', hb'⟩)
  exact hxy (mul_comm_of_mem_sup hBcomm hC0comm hBC0 (hTle hxT) (hTle hyT))

end GL83.I243
