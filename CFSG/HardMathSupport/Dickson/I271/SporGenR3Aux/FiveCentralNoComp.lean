module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.PCentralLayerGLA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.FiveCentralLeaf

public section

namespace CFSG.HardMathSupport.Dickson.I271.FiveCentralNoComp

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem no_glaPComponent_of_central_sylow (hGA : GriessAllModelsStatement)
    (hSpM : SporadicMultipliers) {G : Type} [Group G] [Finite G] (hG : CFSG.Open.IsKGroup G)
    (hM : Nat.card G ∣ monsterOrder) (h65 : ∀ g : G, orderOf g ≠ 65) {z : G}
    (hzo : orderOf z = 5) {P : Subgroup G} (hPC : P ≤ Subgroup.centralizer ({z} : Set G))
    (hP : Nat.card P = 5 ^ (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization 5)
    (hZ : ∀ c ∈ P, (∀ g ∈ P, c * g = g * c) → c ∈ Subgroup.zpowers z)
    (hO : GLAPPrimeCoreOf 5 (Subgroup.centralizer ({z} : Set G)) = ⊥) (J : Subgroup G) :
    ¬ GLAPComponent 5 (Subgroup.centralizer ({z} : Set G)) J := by
  intro hJ
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hcent : ∀ g ∈ C, g * z = z * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.1 hg z (Set.mem_singleton _)).symm
  obtain ⟨K, hK, h5K⟩ := PCentralLayer.exists_component_dvd_card_center_of_glaPComponent
    Nat.prime_five hzC hcent hzo hPC hP hZ hO hJ
  have hq : CFSG.Open.IsQuasisimple ↥K := ⟨hK.1.1.1, hK.1.2.1⟩
  have hKg : CFSG.Open.IsKGroup ↥K := (hG.subgroup C).subgroup K
  have hKG : Nat.card ↥K ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card K).trans (Subgroup.card_subgroup_dvd_card C)
  have h1341 := FiveCentralLeaf.five_central_leaf hGA hSpM hq hKg h5K (hKG.trans hM)
  have h13 : 13 ∣ Nat.card ↥K := (Dvd.intro 41 rfl).trans h1341
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥K)) 5 h5K
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 13 h13
  let φ : ↥K →* G := C.subtype.comp K.subtype
  have hφ : Function.Injective φ := C.subtype_injective.comp K.subtype_injective
  have hw' : orderOf (φ (w : ↥K)) = 5 :=
    (orderOf_injective φ hφ _).trans ((Subgroup.orderOf_coe w).trans hw)
  have hy' : orderOf (φ y) = 13 := (orderOf_injective φ hφ _).trans hy
  have hcommK : Commute (w : ↥K) y := (Subgroup.mem_center_iff.1 w.2 y).symm
  have hcomm : Commute (φ (w : ↥K)) (φ y) := hcommK.map φ
  have h65' : orderOf (φ (w : ↥K) * φ y) = 65 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hw', hy']; norm_num), hw', hy']
  exact h65 _ h65'

end CFSG.HardMathSupport.Dickson.I271.FiveCentralNoComp
