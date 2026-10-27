module

public import CFSG.GH74.GLS.Bg.Pu5.L293Step0
public import CFSG.GH74.GLS.Bg.Iii2.ExtBasic

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_comm_of_stable {S E : Subgroup G} (hS : IsPGroup 2 ↥S) (hES : E ≤ S)
    {t : G} (htS : t ∈ S) (htE : ∀ w ∈ E, t * w * t⁻¹ ∈ E) (hne : E ≠ ⊥) :
    ∃ v ∈ E, orderOf v = 2 ∧ v * t = t * v := by
  have hmap : E.map (MulAut.conj t).toMonoidHom ≤ E := by
    rintro _ ⟨w, hw, rfl⟩
    exact htE w hw
  have hmap' : E.map (MulAut.conj t).toMonoidHom = E :=
    Subgroup.eq_of_le_of_card_ge hmap
      (by rw [Subgroup.card_map_of_injective (MulAut.conj t).injective])
  have htN : t ∈ normalizer (E : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.2 hmap'
  have hH : IsPGroup 2 ↥(E ⊔ zpowers t) := hS.to_le (sup_le hES (zpowers_le.2 htS))
  have hle : E ⊔ zpowers t ≤ normalizer (E : Set G) :=
    sup_le Subgroup.le_normalizer (zpowers_le.2 htN)
  have hstable : ∀ s ∈ E ⊔ zpowers t, ∀ p ∈ E, s * p * s⁻¹ ∈ E := fun s hs p hp =>
    ((Subgroup.mem_normalizer_iff.1 (hle hs)) p).1 hp
  obtain ⟨v, hvE, hv2, hvc⟩ := exists_involution_normal hH le_sup_left hstable hne
  exact ⟨v, hvE, hv2, (hvc t (Subgroup.mem_sup_right (mem_zpowers t))).symm⟩

theorem l293_main (hLP : L292LP) (hTP : L292TP) (h44 : II4_44) (hquat : II4_4_quat) {z t : G}
    {S : Subgroup G} (hC : Cfg G z t S) {u : G} (hu : orderOf u = 2) (huS : u ∈ S)
    (hut : u ∈ centralizer ({t} : Set G)) {K₀ : Subgroup G} (hK₀ : IsRigidRankOneComp z K₀)
    (huK₀ : u ∈ cSec K₀) {L₀ : Subgroup G} (hL₀ : IsRigidRankOneComp t L₀)
    (huL₀ : u ∈ cSec L₀) : False := by
  have hS2 : IsPGroup 2 ↥S := hC.sylow.isPGroup
  have hSz : S ≤ centralizer ({z} : Set G) := hC.sylow.le
  have huz : u ∈ centralizer ({z} : Set G) := hSz huS
  have htz : t ∈ centralizer ({z} : Set G) := hC.tC
  let W : Set G := {w | ∃ K', IsRigidRankOneComp z K' ∧ u ∈ cSec K' ∧ w ∈ S ⊓ K' ∧ orderOf w = 2}
  let E : Subgroup G := Subgroup.closure W
  have hES : E ≤ S := by
    rw [Subgroup.closure_le]
    rintro w ⟨K', -, -, hw, -⟩
    exact hw.1
  obtain ⟨w₀, hw₀, hw₀2⟩ := exists_involution_inf hquat hC.simple hK₀ hC.sylow
  have hw₀E : w₀ ∈ E := Subgroup.subset_closure ⟨K₀, hK₀, huK₀, hw₀, hw₀2⟩
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hw₀E
    rw [hw₀E, orderOf_one] at hw₀2
    omega
  have htcomm : t * u * t⁻¹ = u := by
    have : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.1 hut
    rw [← this]
    group
  have hWt : ∀ w ∈ W, t * w * t⁻¹ ∈ W := by
    rintro w ⟨K', hK', huK', hw, hw2⟩
    refine ⟨cmap t K', isRigidRankOneComp_cmap hK' htz, ?_,
      ⟨S.mul_mem (S.mul_mem hC.tS hw.1) (S.inv_mem hC.tS), conj_mem_cmap' hw.2 t⟩, ?_⟩
    · have := conj_mem_cSec_cmap huK' t
      rwa [htcomm] at this
    · rw [orderOf_conj_eq']
      exact hw2
  have hEt : ∀ w ∈ E, t * w * t⁻¹ ∈ E := by
    have hmap : E.map (MulAut.conj t).toMonoidHom ≤ E := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      exact Subgroup.subset_closure (hWt w hw)
    intro w hw
    exact hmap ⟨w, hw, rfl⟩
  obtain ⟨v, hvE, hv2, hvt⟩ := exists_involution_comm_of_stable hS2 hES hC.tS hEt hEne
  have hvt' : v ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hvt
  have hWu : ∀ w ∈ W, w * u = u * w := by
    rintro w ⟨K', -, huK', hw, -⟩
    exact comm_of_mem_cSec hS2 hw.1 huS hw.2 huK'
  have hEu : E ≤ centralizer ({u} : Set G) := by
    rw [Subgroup.closure_le]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.2 (hWu w hw)
  have hvu : v ∈ centralizer ({u} : Set G) := hEu hvE
  have hEZ : E ≤ zStar (rigidProduct u) := by
    rw [Subgroup.closure_le]
    intro w hw
    obtain ⟨K', hK', huK', hwS, hw2⟩ := hw
    exact hLP G hC.simple hC.rank z u K' hK' hu huz huK' w
      (mem_zStar_of_involution h44 hC.simple hK' hwS.2 hw2)
      (exists_two_pow_eq_one_of_orderOf hw2)
      (Subgroup.mem_centralizer_singleton_iff.2 (hWu w ⟨K', hK', huK', hwS, hw2⟩))
  have hvZ : v ∈ zStar (rigidProduct u) := hEZ hvE
  have hvL : v ∈ cSec L₀ := hTP G hC.simple hC.rank t u L₀ hL₀ hu hut huL₀ v hv2 hvt' hvu hvZ
  have hvK : ∀ K'', IsRigidRankOneComp z K'' → v ∈ cSec K'' := by
    intro K'' hK''
    have hle : E ≤ cSec K'' := by
      rw [Subgroup.closure_le]
      rintro w ⟨K', hK', -, hw, hw2⟩
      by_cases hKK : K' = K''
      · subst hKK
        exact rr_inv_mem_cSec h44 hC.simple hK' hw.2 hw2
      · exact le_cSec_of_ne (rr_pcomp hK') (rr_pcomp hK'') hKK hw.2
    exact hle hvE
  have hvz : v ∈ centralizer ({z} : Set G) := hSz (hES hvE)
  have hzv : z ∈ centralizer ({v} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hvz).symm
  have hz_v : z ∈ zStar (rigidProduct v) :=
    lpFull hLP h44 hquat hC.simple hC.gen4 hC.rank hv2 hvz hvK hC.z_mem_zStar
      (exists_two_pow_eq_one_of_orderOf hC.hz) hzv
  have hzL₀ : z ∈ cSec L₀ :=
    hTP G hC.simple hC.rank t v L₀ hL₀ hv2 hvt' hvL z hC.hz hC.z_mem_centralizer_t hzv hz_v
  obtain ⟨T', hT', hzT'⟩ := exists_isSylowOf_ge' (zpowers_le.2 hC.z_mem_centralizer_t)
    (isPGroup_zpowers_of_pow_eq_one (exists_two_pow_eq_one_of_orderOf hC.hz))
  obtain ⟨w, hwT'L, hw2⟩ := exists_involution_inf hquat hC.simple hL₀ hT'
  have hwz : w * z = z * w :=
    comm_of_mem_cSec hT'.isPGroup hwT'L.1 (hzT' (mem_zpowers z)) hwT'L.2 hzL₀
  have hwZ : w ∈ zStar (rigidProduct z) :=
    hLP G hC.simple hC.rank t z L₀ hL₀ hC.hz hC.z_mem_centralizer_t hzL₀ w
      (mem_zStar_of_involution h44 hC.simple hL₀ hwT'L.2 hw2)
      (exists_two_pow_eq_one_of_orderOf hw2) (Subgroup.mem_centralizer_singleton_iff.2 hwz)
  refine step0 hLP hTP h44 hquat hC hw2 (Subgroup.mem_centralizer_singleton_iff.2 hwz)
    ((rr_pcomp hL₀).1 hwT'L.2) (fun K hK => ?_) (fun L hL => ?_)
  · exact mem_cSec_of_mem_zStar h44 hquat hC.simple hC.gen4 hwZ
      (exists_two_pow_eq_one_of_orderOf hw2) hK
  · by_cases hLL : L₀ = L
    · subst hLL
      exact rr_inv_mem_cSec h44 hC.simple hL₀ hwT'L.2 hw2
    · exact le_cSec_of_ne (rr_pcomp hL₀) (rr_pcomp hL) hLL hwT'L.2

theorem l293_of (hLP : L292LP) (hTP : L292TP) (h44 : II4_44) (hquat : II4_4_quat) : L293 := by
  intro G _ _ z t S hC u hu hz ht K hK huK L hL huL
  have hD : IsSylowOf 2 (S ⊓ centralizer ({t} : Set G))
      (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) := hC.ext
  have huD : u ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := ⟨hz, ht⟩
  obtain ⟨c, hcD, hcu⟩ := exists_conj_mem_of_isSylowOf' hD huD ⟨1, by rw [hu, pow_one]⟩
  exact l293_main hLP hTP h44 hquat hC (u := c * u * c⁻¹) (by rw [orderOf_conj_eq']; exact hu)
    hcu.1 hcu.2 (isRigidRankOneComp_cmap hK hcD.1) (conj_mem_cSec_cmap huK c)
    (isRigidRankOneComp_cmap hL hcD.2) (conj_mem_cSec_cmap huL c)

end CFSG.GH74.GLS.Bg.Pu5
