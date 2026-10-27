module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroChar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UPrimeExcL34
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.factor_of_l34Cover (hd : D1OneSmallData 3 P M H R Rbar K)
    {J : Subgroup G} (hcov : ∀ k ∈ K, ∃ a ∈ J, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) :
    ∀ h ∈ H, ∃ a ∈ J, ∃ b ∈ H ⊓ M, h = a * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨T₁, hT₁, -⟩ := hd.exists_sylow
  have htop := Sylow.normalizer_sup_eq_top T₁
  rw [hT₁] at htop
  obtain ⟨zb, hzbR, hzbK, hzbp, hzbc⟩ := hd.z
  have hN := hd.cfg.red.normalizer_inf_le_of_rankOne hd.noncyclic hzbR hzbK hzbp hzbc
  intro h hh
  have hmem : π ⟨h, hh⟩ ∈ K ⊔ Subgroup.normalizer
      (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [sup_comm, htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk, ν, hν, hkν⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  obtain ⟨a, haJ, haH, rfl⟩ := hcov k hk
  obtain ⟨m, hm, rfl⟩ := hN hν
  have hmM : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
  have h1 : π ((⟨a, haH⟩ * m)⁻¹ * ⟨h, hh⟩) = 1 := by
    rw [map_mul, map_inv, map_mul, hkν]; group
  have hoM : (((⟨a, haH⟩ * m)⁻¹ * ⟨h, hh⟩ : H) : G) ∈ M :=
    hd.cfg.ext.toD1Escape.primeCore_le ((mk'_primeComplementCore_eq_one_iff 3 _).mp h1)
  refine ⟨a, haJ, (m : G) * (((⟨a, haH⟩ * m)⁻¹ * ⟨h, hh⟩ : H) : G),
    ⟨H.mul_mem m.2 (((⟨a, haH⟩ * m)⁻¹ * ⟨h, hh⟩ : H)).2, M.mul_mem hmM hoM⟩, ?_⟩
  simp [mul_assoc]

theorem D1OneSmallData.conj_mem_rbar (hd : D1OneSmallData 3 P M H R Rbar K)
    (hOR : ¬ D1SmallOuterR 3 H Rbar K) {κ : H ⧸ primeComplementCore (G := H) 3} (hκK : κ ∈ K)
    (hκN : ∀ x ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K,
      κ * x * κ⁻¹ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K)
    {r : H ⧸ primeComplementCore (G := H) 3}
    (hr : r ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3))) :
    κ * r * κ⁻¹ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdec := exists_mul_eq_of_le_normalizer_sup_centralizer Rbar
    (fun r hr => hd.cfg.red.sylow_le_normalizer_component hd.comp hr) (not_not.mp hOR)
  obtain ⟨t, ht, c, hc, rfl⟩ := hdec r hr
  have hcκ : κ * c = c * κ := Subgroup.mem_centralizer_iff.mp hc.2 κ hκK
  have h2 : c * κ⁻¹ = κ⁻¹ * c := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hcκ, ← mul_assoc, inv_mul_cancel, one_mul]
  have e : κ * (t * c) * κ⁻¹ = (κ * t * κ⁻¹) * c := by
    calc κ * (t * c) * κ⁻¹ = κ * t * (c * κ⁻¹) := by group
      _ = (κ * t * κ⁻¹) * c := by rw [h2]; group
  rw [e]
  exact Subgroup.mul_mem _ (hκN t ht).1 hc.1

theorem D1OneSmallData.trans_of_l34Cover (hd : D1OneSmallData 3 P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt 3 H R K z) (hL : IsLinThreeFour K) (hOR : ¬ D1SmallOuterR 3 H Rbar K)
    {J : Subgroup G} (hJH : J ≤ H) (hRJ : R ≤ J)
    (hcov : ∀ k ∈ K, ∃ a ∈ J, ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) :
    ∀ t ∈ d1LiftX 3 H R K, t ≠ 1 → ∀ s ∈ d1LiftX 3 H R K, s ≠ 1 →
      ∃ n ∈ J ⊓ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z ∧
        (∀ x ∈ d1LiftX 3 H R K, n * x * n⁻¹ ∈ d1LiftX 3 H R K) ∧ n * t * n⁻¹ = s := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hO := primeComplementCore_coprime (G := H) 3
  have hRH : R ≤ H := hd.cfg.ext.le_H
  have hRHp : IsPGroup 3 (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  have hRb : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) = (R.subgroupOf H).map π :=
    hd.cfg.rbar
  obtain ⟨T₁, hT₁, -⟩ := hd.exists_sylow
  have hloc := KFactProofs.UPrimeExcL34.localData_of_isLinThreeFour hL T₁
  have hTT₁ : ∀ x ∈ d1LiftX 3 H R K, x ≠ 1 → ∃ hx : x ∈ H, ∃ hxK : π ⟨x, hx⟩ ∈ K,
      (⟨π ⟨x, hx⟩, hxK⟩ : K) ∈ (T₁ : Subgroup K) ∧ (⟨π ⟨x, hx⟩, hxK⟩ : K) ≠ 1 := by
    intro y hy hx1
    obtain ⟨⟨x, hxH⟩, ⟨hxR, hxK⟩, hxx⟩ := hy
    obtain rfl : x = y := hxx
    refine ⟨hxH, hxK, ?_, ?_⟩
    · have hmem : π ⟨x, hxH⟩ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :=
        ⟨hRb ▸ ⟨⟨x, hxH⟩, hxR, rfl⟩, hxK⟩
      rw [← hT₁] at hmem
      obtain ⟨y, hy, hyx⟩ := hmem
      have : y = ⟨π ⟨x, hxH⟩, hxK⟩ := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro h1
      have h2 : π ⟨x, hxH⟩ = 1 := congrArg Subtype.val h1
      have h3 : (⟨x, hxH⟩ : H) ∈ R.subgroupOf H ⊓ primeComplementCore (G := H) 3 :=
        ⟨hxR, (QuotientGroup.eq_one_iff _).mp h2⟩
      rw [inf_eq_bot_of_isPGroup hp hRHp hO, Subgroup.mem_bot] at h3
      exact hx1 (congrArg Subtype.val h3)
  intro t ht ht1 s hs hs1
  obtain ⟨htH, htK, htT, htne⟩ := hTT₁ t ht ht1
  obtain ⟨hsH, hsK, hsT, hsne⟩ := hTT₁ s hs hs1
  obtain ⟨κ, hκN, hκ⟩ := hloc.trans _ htT htne _ hsT hsne
  have hκconj : ∀ ν : K, ν ∈ Subgroup.normalizer ((T₁ : Subgroup K) : Set K) →
      ∀ r ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
        (ν : H ⧸ primeComplementCore (G := H) 3) * r * (ν : H ⧸ primeComplementCore (G := H) 3)⁻¹
          ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
    intro ν hν r hr
    refine hd.conj_mem_rbar hOR ν.2 (fun x hx => ?_) hr
    rw [← hT₁] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨ν * y * ν⁻¹, (Subgroup.mem_normalizer_iff.mp hν y).mp hy, rfl⟩
  have hκR : (κ : H ⧸ primeComplementCore (G := H) 3) ∈ Subgroup.normalizer
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) :
        Set (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨hκconj κ hκN r, fun hr => ?_⟩
    have := hκconj κ⁻¹ (inv_mem hκN) _ hr
    simpa [mul_assoc] using this
  obtain ⟨a, haJ, haH, hπa⟩ := hcov κ κ.2
  set ψ : J →* H ⧸ primeComplementCore (G := H) 3 := π.comp (Subgroup.inclusion hJH) with hψ
  have hψker : Nat.Coprime 3 (Nat.card ψ.ker) := by
    have hle : ψ.ker.map J.subtype ≤ GLBPrimeCore 3 H := by
      rintro _ ⟨j, hj, rfl⟩
      exact (mk'_primeComplementCore_eq_one_iff 3 (Subgroup.inclusion hJH j)).mp hj
    rw [← Subgroup.card_map_of_injective J.subtype_injective]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle) (glbPrimeCore_coprime 3 H)
  have hψeq : ∀ x y : J, QuotientGroup.mk' ψ.ker x = QuotientGroup.mk' ψ.ker y ↔
      ψ x = ψ y := by
    intro x y
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, MonoidHom.mem_ker,
      map_mul, map_inv, inv_mul_eq_one]
  have hSp : IsPGroup 3 (R.subgroupOf J) := hd.cfg.ext.isPGroup.comap_subtype
  have hSmem : ∀ x : J, QuotientGroup.mk' ψ.ker x ∈ (R.subgroupOf J).map
      (QuotientGroup.mk' ψ.ker) ↔ ψ x ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
    intro x
    constructor
    · rintro ⟨r, hr, hrx⟩
      rw [hψeq] at hrx
      rw [← hrx, hRb]
      exact ⟨Subgroup.inclusion hJH r, hr, rfl⟩
    · intro hx
      rw [hRb] at hx
      obtain ⟨⟨r, hrH⟩, hr, hrx⟩ := hx
      refine ⟨⟨r, hRJ hr⟩, hr, ?_⟩
      rw [hψeq]
      exact hrx
  have hψa : ψ ⟨a, haJ⟩ = κ := hπa
  have hxN : QuotientGroup.mk' ψ.ker ⟨a, haJ⟩ ∈ Subgroup.normalizer
      (((R.subgroupOf J).map (QuotientGroup.mk' ψ.ker) : Subgroup (J ⧸ ψ.ker)) :
        Set (J ⧸ ψ.ker)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ψ.ker w
    rw [← map_mul, ← map_inv, ← map_mul, hSmem, hSmem, map_mul, map_mul, map_inv, hψa]
    exact Subgroup.mem_normalizer_iff.mp hκR (ψ x)
  have hzJ : z ∈ J := hRJ hz.1
  have hzS : (⟨z, hzJ⟩ : J) ∈ R.subgroupOf J := hz.1
  have hzC : ψ ⟨z, hzJ⟩ ∈ Subgroup.centralizer
      (K : Set (H ⧸ primeComplementCore (G := H) 3)) := hz.2.2.2
  have hxz : QuotientGroup.mk' ψ.ker ⟨a, haJ⟩ * QuotientGroup.mk' ψ.ker ⟨z, hzJ⟩ =
      QuotientGroup.mk' ψ.ker ⟨z, hzJ⟩ * QuotientGroup.mk' ψ.ker ⟨a, haJ⟩ := by
    rw [← map_mul, ← map_mul, hψeq, map_mul, map_mul, hψa]
    exact Subgroup.mem_centralizer_iff.mp hzC κ κ.2
  obtain ⟨g, hgN, hgx, hgz⟩ :=
    exists_mem_normalizer_mk_eq_commute hp ψ.ker hψker hSp hxN hzS hxz
  have hψg : ψ g = κ := by
    rw [← hψa]
    exact (hψeq g ⟨a, haJ⟩).mp hgx
  have hgR : (g : G) ∈ Subgroup.normalizer (R : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hRJ] at hgN
    exact hgN
  have hconjπ : ∀ x : G, ∀ hx : x ∈ H, ∀ hgx : (g : G) * x * (g : G)⁻¹ ∈ H,
      π ⟨(g : G) * x * (g : G)⁻¹, hgx⟩ = κ * π ⟨x, hx⟩ * (κ : H ⧸ primeComplementCore 3)⁻¹ := by
    intro x hx hgx
    have e : (⟨(g : G) * x * (g : G)⁻¹, hgx⟩ : H) =
        Subgroup.inclusion hJH g * ⟨x, hx⟩ * (Subgroup.inclusion hJH g)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    change ψ g * π ⟨x, hx⟩ * (ψ g)⁻¹ = _
    rw [hψg]
  refine ⟨g, ⟨g.2, hgR⟩, ?_, ?_, ?_⟩
  · have := congrArg Subtype.val hgz
    simp only [Subgroup.coe_mul] at this
    rw [this, mul_inv_cancel_right]
  · rintro _ ⟨⟨x, hxH⟩, ⟨hxR, hxK⟩, rfl⟩
    have hgxR : (g : G) * x * (g : G)⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hgR x).mp hxR
    refine ⟨⟨(g : G) * x * (g : G)⁻¹, hRH hgxR⟩, ⟨hgxR, ?_⟩, rfl⟩
    change π _ ∈ K
    rw [hconjπ x hxH]
    exact K.mul_mem (K.mul_mem κ.2 hxK) (K.inv_mem κ.2)
  · have hgtR : (g : G) * t * (g : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hgR t).mp (d1LiftX_le 3 H R K ht)
    have hsR : s ∈ R := d1LiftX_le 3 H R K hs
    have h1 : π ⟨(g : G) * t * (g : G)⁻¹, hRH hgtR⟩ = π ⟨s, hsH⟩ := by
      rw [hconjπ t htH]
      have := congrArg Subtype.val hκ
      simpa using this
    have h2 := eq_of_mk_eq_of_isPGroup hp _ hO hRHp
      (show (⟨(g : G) * t * (g : G)⁻¹, hRH hgtR⟩ : H) ∈ R.subgroupOf H from hgtR)
      (show (⟨s, hsH⟩ : H) ∈ R.subgroupOf H from hsR) h1
    exact congrArg Subtype.val h2

end CFSG.AGLEmbedding
