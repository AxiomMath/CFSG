module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporOddCent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open Subgroup CFSG.QuasithinUnique.Lin2.RankCert

theorem uniqueRank_exists_conj {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) {N Hg : Subgroup G} {z : G} (hz : orderOf z = p)
    (hzN : z ∈ N) (hHN : Hg ≤ N) (hpH : p ∣ Nat.card Hg) :
    ∃ c ∈ N, c * z * c⁻¹ ∈ Hg := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpH
  have hsylN : ¬ p ^ 2 ∣ Nat.card N := fun h =>
    hsyl (h.trans (Subgroup.card_subgroup_dvd_card N))
  have hyN : (y : G) ∈ N := hHN y.2
  have hzord : orderOf (⟨z, hzN⟩ : N) = p := (Subgroup.orderOf_mk z hzN).trans hz
  have hyord : orderOf (⟨(y : G), hyN⟩ : N) = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    exact hy
  obtain ⟨c, hc⟩ := exists_conj_zpowers hp hsylN hzord hyord
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h1 := congrArg Subtype.val hk
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] at h1
  refine ⟨c, c.2, ?_⟩
  rw [← h1]
  exact Hg.zpow_mem y.2 k

theorem uniqueRank_kxSection {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) {K N Hg : Subgroup G} {z : G} (hz : orderOf z = p)
    (hNK : N ≤ K) (hzN : z ∈ N) (hHN : Hg ≤ N) (hsimp : IsSimpleGroup Hg)
    (hnc : ¬ IsMulCommutative Hg) (h3 : 3 ∣ Nat.card Hg) (hpH : p ∣ Nat.card Hg) :
    KxSection z K 3 := by
  obtain ⟨c, hcN, hc⟩ := uniqueRank_exists_conj hp hsyl hz hzN hHN hpH
  obtain ⟨hsimp', hnc', hcard⟩ := ZCAbs.map_simple_nonabelian (MulAut.conj c⁻¹) hsimp hnc
  have hzH : z ∈ Hg.map (MulAut.conj c⁻¹).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨c * z * c⁻¹, hc, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hHK : Hg.map (MulAut.conj c⁻¹).toMonoidHom ≤ K := by
    rintro _ ⟨h, hh, rfl⟩
    refine hNK ?_
    simpa [MulAut.conj_apply] using N.mul_mem (N.mul_mem (N.inv_mem hcN) (hHN hh)) hcN
  exact ZCAbs.kxSection_of_nonabelian_simple hp hz hHK hsimp' hnc' hzH
    (by rw [hcard]; exact h3)

theorem row_of_uniqueRank {s : TauCeti.SporadicName} {p : ℕ} (hs : s ≠ .M11) (X : Type)
    [Group X] [Finite X] (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hcent : ∀ t z : X, orderOf t = 2 → orderOf z = p → t * z ≠ z * t) (V₀ H : Subgroup X)
    (hV₀ : ∀ E : Subgroup X, IsElemAbelian 2 E → 2 ^ orderOf (2 : ZMod p) ≤ Nat.card E →
      ∃ g : X, E.map (MulAut.conj g).toMonoidHom = V₀)
    (hHN : H ≤ normalizer (V₀ : Set X)) (hsimp : IsSimpleGroup H) (hnc : ¬ IsMulCommutative H)
    (h3 : 3 ∣ Nat.card H) (hpH : p ∣ Nat.card H) (hp2 : ¬ p ^ 2 ∣ Nat.card X) :
    KFactSporLocalRow s p := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp hp5 K z hz _ hzK _ hcl hy _
  refine ⟨?_, hs⟩
  obtain ⟨f⟩ := hX
  let φ : G ≃* X := e.trans f.symm
  have hpne : p ≠ 2 := by omega
  have hsylG : ¬ p ^ 2 ∣ Nat.card G := by
    rwa [Nat.card_congr φ.toEquiv]
  obtain ⟨y, hyQ, hyz⟩ := hy
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyz (by rw [mul_one, one_mul])
  obtain ⟨u, huQ, hu2, hu1, huc⟩ := ZCAbs.exists_central_involution_pCoreOf hyQ hy1
  have hu : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hzu : z * u ≠ u * z := fun h =>
    hcent (φ u) (φ z) (by rw [MulEquiv.orderOf_eq]; exact hu)
      (by rw [MulEquiv.orderOf_eq]; exact hz) (by rw [← map_mul, ← map_mul, h.symm])
  have hQ : ∀ g ∈ zpowers z, g * u * g⁻¹ ∈ pCoreOf 2 K := fun g hg =>
    ZCAbs.conj_mem_pCoreOf (zpowers_le.mpr hzK hg) huQ
  have hV := zConjClosure_isElemAbelian hzK huQ hu2 huc
  have hVle : zConjClosure z u ≤ pCoreOf 2 K := ZCAbs.zConjClosure_le hQ
  have huV : u ∈ zConjClosure z u := by
    simpa using ZCAbs.conj_mem_zConjClosure (z := z) u (one_mem (zpowers z))
  have hdvd := two_pow_orderOf_dvd_card hp hpne hz
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hVle)
    (ZCAbs.mem_normalizer_zConjClosure z u) ⟨u, huV, hzu⟩
  have hNK := ZCAbs.normalizer_zConjClosure_le hu1 hcl hQ
  have hV' : IsElemAbelian 2 ((zConjClosure z u).map φ.toMonoidHom) :=
    CFSG.QuasithinUnique.Lin2.isElemAbelian_map' hV _
  have hcard' : Nat.card ((zConjClosure z u).map φ.toMonoidHom) =
      Nat.card (zConjClosure z u) :=
    CFSG.QuasithinUnique.Lin2.card_map_of_inf_ker_eq_bot _ _
      (fun x _ hx => φ.map_eq_one_iff.mp hx)
  obtain ⟨g, hg⟩ := hV₀ _ hV' (by rw [hcard']; exact Nat.le_of_dvd Nat.card_pos hdvd)
  let ψ : G ≃* X := φ.trans (MulAut.conj g)
  have hVψ : (zConjClosure z u).map ψ.toMonoidHom = V₀ := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hHg : H.map ψ.symm.toMonoidHom ≤ normalizer (zConjClosure z u : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := mem_normalizer_image_of_mem ψ.symm (hHN hx)
    have h2 : ψ.symm '' (V₀ : Set X) = (zConjClosure z u : Set G) := by
      rw [← hVψ, Subgroup.coe_map, Set.image_image]
      ext a
      simp
    rw [h2] at h1
    exact h1
  obtain ⟨hsimp', hnc', hcard⟩ := ZCAbs.map_simple_nonabelian ψ.symm hsimp hnc
  exact uniqueRank_kxSection hp hsylG hz hNK (ZCAbs.mem_normalizer_zConjClosure z u) hHg
    hsimp' hnc' (by rw [hcard]; exact h3) (by rw [hcard]; exact hpH)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
