module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalOrd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open Subgroup CFSG.QuasithinUnique.Lin2.RankCert

theorem zConjClosure_isElemAbelian {G : Type*} [Group G] {K : Subgroup G} {z u : G}
    (hzK : z ∈ K) (huQ : u ∈ pCoreOf 2 K) (hu2 : u * u = 1)
    (huc : ∀ q ∈ pCoreOf 2 K, u * q = q * u) : IsElemAbelian 2 (zConjClosure z u) := by
  have hS : {x | ∃ g ∈ zpowers z, x = g * u * g⁻¹}.Pairwise Commute := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ -
    exact ZCAbs.conj_comm_of_central hzK huQ huc hg hh
  have hc : IsMulCommutative (closure {x | ∃ g ∈ zpowers z, x = g * u * g⁻¹}) :=
    Subgroup.isMulCommutative_closure hS
  have hsq : ∀ x ∈ closure {x | ∃ g ∈ zpowers z, x = g * u * g⁻¹}, x ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, -, rfl⟩ := hx
      rw [conj_pow, sq, hu2, mul_one, mul_inv_cancel]
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y := congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  exact ⟨hc, hsq⟩

theorem false_of_oddCent_rank {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Subgroup G} {z : G} (hz : orderOf z = p) (hzK : z ∈ K)
    (hy : ∃ y ∈ pCoreOf 2 K, z * y ≠ y * z)
    (hcent : ∀ t : G, orderOf t = 2 → t * z ≠ z * t)
    (hrank : ElemAbelianLt G (2 ^ orderOf (2 : ZMod p))) : False := by
  obtain ⟨y, hyQ, hyz⟩ := hy
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyz (by rw [mul_one, one_mul])
  obtain ⟨u, huQ, hu2, hu1, huc⟩ := ZCAbs.exists_central_involution_pCoreOf hyQ hy1
  have hu : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hzu : z * u ≠ u * z := fun h => hcent u hu h.symm
  have hV := zConjClosure_isElemAbelian hzK huQ hu2 huc
  have hVle : zConjClosure z u ≤ pCoreOf 2 K :=
    ZCAbs.zConjClosure_le fun g hg => ZCAbs.conj_mem_pCoreOf (zpowers_le.mpr hzK hg) huQ
  have huV : u ∈ zConjClosure z u := by
    simpa using ZCAbs.conj_mem_zConjClosure (z := z) u (one_mem (zpowers z))
  have hdvd := two_pow_orderOf_dvd_card hp hp2 hz
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hVle)
    (ZCAbs.mem_normalizer_zConjClosure z u) ⟨u, huV, hzu⟩
  exact absurd (Nat.le_of_dvd Nat.card_pos hdvd) (not_le.mpr (hrank _ hV))

theorem row_of_oddCent_rank {s : TauCeti.SporadicName} {p : ℕ} (X : Type) [Group X]
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hcent : ∀ t z : X, orderOf t = 2 → orderOf z = p → t * z ≠ z * t)
    (hrank : ElemAbelianLt X (2 ^ orderOf (2 : ZMod p))) :
    KFactSporLocalRow s p := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp hp5 K z hz _ hzK _ _ hy _
  obtain ⟨f⟩ := hX
  let φ : G ≃* X := e.trans f.symm
  refine (false_of_oddCent_rank hp (by omega) hz hzK hy (fun t ht htz => ?_)
    (ElemAbelianLt.of_mulEquiv φ hrank)).elim
  refine hcent (φ t) (φ z) (by rw [MulEquiv.orderOf_eq]; exact ht)
    (by rw [MulEquiv.orderOf_eq]; exact hz) ?_
  rw [← map_mul, ← map_mul, htz]

theorem card_inf_centralizer_conj {G : Type*} [Group G] {Γ : Subgroup G} {c : G} (hc : c ∈ Γ)
    (t : G) : Nat.card ↥(Γ ⊓ Subgroup.centralizer {c * t * c⁻¹}) =
      Nat.card ↥(Γ ⊓ Subgroup.centralizer {t}) := by
  have hmap : (Γ ⊓ Subgroup.centralizer {t}).map (MulAut.conj c).toMonoidHom =
      Γ ⊓ Subgroup.centralizer {c * t * c⁻¹} := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨g, ⟨hg, hgt⟩, rfl⟩
      refine ⟨Γ.mul_mem (Γ.mul_mem hc hg) (Γ.inv_mem hc), ?_⟩
      calc c * g * c⁻¹ * (c * t * c⁻¹) = c * (g * t) * c⁻¹ := by group
        _ = c * (t * g) * c⁻¹ := by rw [hgt]
        _ = c * t * c⁻¹ * (c * g * c⁻¹) := by group
    · rintro ⟨hy, hyt⟩
      refine ⟨c⁻¹ * y * c, ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hc) hy) hc, ?_⟩, by group⟩
      calc c⁻¹ * y * c * t = c⁻¹ * (y * (c * t * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * t * c⁻¹ * y) * c := by rw [hyt]
        _ = t * (c⁻¹ * y * c) := by group
  rw [← hmap]
  exact (Nat.card_congr ((Γ ⊓ Subgroup.centralizer {t}).equivMapOfInjective _
    (MulAut.conj c).injective).toEquiv).symm

theorem card_centralizer_mulEquiv {G X : Type*} [Group G] [Group X] (φ : G ≃* X) (t : G) :
    Nat.card (Subgroup.centralizer ({φ t} : Set X)) =
      Nat.card (Subgroup.centralizer ({t} : Set G)) := by
  have hmap : (Subgroup.centralizer ({t} : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ t} : Set X) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [← map_mul, ← map_mul, hg]
    · intro hy
      refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
      apply φ.injective
      rw [map_mul, map_mul, φ.apply_symm_apply]
      exact hy
  rw [← hmap]
  exact (Nat.card_congr ((Subgroup.centralizer ({t} : Set G)).equivMapOfInjective _
    φ.injective).toEquiv).symm

theorem card_centralizer_subtype {G : Type*} [Group G] {H : Subgroup G} (t : H) :
    Nat.card (Subgroup.centralizer ({t} : Set H)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer {(t : G)}) := by
  have hmap : (Subgroup.centralizer ({t} : Set H)).map H.subtype =
      H ⊓ Subgroup.centralizer {(t : G)} := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g.2, congrArg Subtype.val hg⟩
    · rintro ⟨hyH, hy⟩
      exact ⟨⟨y, hyH⟩, Subtype.ext hy, rfl⟩
  rw [← hmap]
  exact Nat.card_congr ((Subgroup.centralizer ({t} : Set H)).equivMapOfInjective _
    H.subtype_injective).toEquiv

theorem false_of_oddCent_rank' {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Subgroup G} {z : G} (hz : orderOf z = p) (hzK : z ∈ K)
    (hy : ∃ y ∈ pCoreOf 2 K, z * y ≠ y * z)
    (hcent : ∀ t : G, orderOf t = 2 → t * z = z * t →
      ¬ 2 ^ orderOf (2 : ZMod p) ∣ Nat.card (Subgroup.centralizer ({t} : Set G)))
    (hrank : ElemAbelianLt G (2 ^ orderOf (2 : ZMod p))) : False := by
  obtain ⟨y, hyQ, hyz⟩ := hy
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyz (by rw [mul_one, one_mul])
  obtain ⟨u, huQ, hu2, hu1, huc⟩ := ZCAbs.exists_central_involution_pCoreOf hyQ hy1
  have hu : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  by_cases hzu : z * u = u * z
  ·
    have hQle : pCoreOf 2 K ≤ Subgroup.centralizer ({u} : Set G) := fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.mpr (huc q hq).symm
    have hdvd := two_pow_orderOf_dvd_card hp hp2 hz
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 K hzK)
      ⟨y, hyQ, hyz⟩
    exact hcent u hu hzu.symm (hdvd.trans (Subgroup.card_dvd_of_le hQle))
  ·
    have hV := zConjClosure_isElemAbelian hzK huQ hu2 huc
    have hVle : zConjClosure z u ≤ pCoreOf 2 K :=
      ZCAbs.zConjClosure_le fun g hg => ZCAbs.conj_mem_pCoreOf (zpowers_le.mpr hzK hg) huQ
    have huV : u ∈ zConjClosure z u := by
      simpa using ZCAbs.conj_mem_zConjClosure (z := z) u (one_mem (zpowers z))
    have hdvd := two_pow_orderOf_dvd_card hp hp2 hz
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hVle)
      (ZCAbs.mem_normalizer_zConjClosure z u) ⟨u, huV, hzu⟩
    exact absurd (Nat.le_of_dvd Nat.card_pos hdvd) (not_le.mpr (hrank _ hV))

theorem row_of_oddCent_rank' {s : TauCeti.SporadicName} {p : ℕ} (X : Type) [Group X]
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hcent : ∀ t z : X, orderOf t = 2 → orderOf z = p → t * z = z * t →
      ¬ 2 ^ orderOf (2 : ZMod p) ∣ Nat.card (Subgroup.centralizer ({t} : Set X)))
    (hrank : ElemAbelianLt X (2 ^ orderOf (2 : ZMod p))) :
    KFactSporLocalRow s p := by
  apply row_of_model
  intro G _ _ ⟨e⟩ hp hp5 K z hz _ hzK _ _ hy _
  obtain ⟨f⟩ := hX
  let φ : G ≃* X := e.trans f.symm
  refine (false_of_oddCent_rank' hp (by omega) hz hzK hy (fun t ht htz hdvd => ?_)
    (ElemAbelianLt.of_mulEquiv φ hrank)).elim
  refine hcent (φ t) (φ z) (by rw [MulEquiv.orderOf_eq]; exact ht)
    (by rw [MulEquiv.orderOf_eq]; exact hz) (by rw [← map_mul, ← map_mul, htz]) ?_
  rwa [card_centralizer_mulEquiv φ t]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
