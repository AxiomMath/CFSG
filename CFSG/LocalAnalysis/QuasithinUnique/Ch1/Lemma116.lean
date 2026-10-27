module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem inf_eq_of_isSylowTwoOf_of_le {S H T : Subgroup G} (hS : IsSylowTwoOf S H)
    (hT : IsPGroup 2 T) (hST : S ≤ T) : T ⊓ H = S := by
  have hSP : S ≤ T ⊓ H := le_inf hST hS.1
  have hmul := Subgroup.relIndex_mul_relIndex S (T ⊓ H) H hSP inf_le_right
  have hodd : ¬ 2 ∣ S.relIndex H := hS.2.2
  have hodd1 : ¬ 2 ∣ S.relIndex (T ⊓ H) := fun h => hodd (h.trans ⟨_, hmul.symm⟩)
  obtain ⟨n, hn⟩ := (hT.to_le inf_le_left).exists_card_eq
  have hdvd : S.relIndex (T ⊓ H) ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card S (T ⊓ H)
  obtain ⟨m, -, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm : m = 0 := by
    by_contra hm0
    exact hodd1 (hmeq ▸ dvd_pow_self 2 hm0)
  have h1 : S.relIndex (T ⊓ H) = 1 := by rw [hmeq, hm, pow_zero]
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hSP

theorem lemma116 (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G)
    {B H S T M : Subgroup G} {z : G} (hB : IsPGroup 2 B) (hB1 : B ≠ ⊥)
    (hBH : B ⊔ Subgroup.centralizer (B : Set G) ≤ H) (hHB : H ≤ Subgroup.normalizer (B : Set G))
    (hS : IsSylowTwoOf S H) (hT : IsSylowTwoOf T ⊤) (hST : S ≤ T) (hzT : z ∈ T)
    (hzc : z ∈ Subgroup.centralizer (T : Set G)) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hM : CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M)
    (hCM : Subgroup.centralizer ({z} : Set G) ≤ M) : Lemma115Hyp H S M z := by
  have hBH' : B ≤ H := le_sup_left.trans hBH
  have hCBH : Subgroup.centralizer (B : Set G) ≤ H := le_sup_right.trans hBH
  have hBQ : B ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer hBH' hHB hB
  have hQS : pCoreOf 2 H ≤ S := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
  have hBT : B ≤ T := (hBQ.trans hQS).trans hST
  have hTM : T ≤ M := fun t ht =>
    hCM (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc t ht))
  have hcharM : CharTwo M := charTwo_of_isTwoLocal_of_isSylowTwoOf_le hev hT hM.1 hTM
  have hMpc : pCoreOf 2 M ≠ ⊥ := by
    obtain ⟨P, hP1, hP2, rfl⟩ := hM.1
    have hPQ : P ≤ pCoreOf 2 (Subgroup.normalizer (P : Set G)) :=
      le_pCoreOf_of_le_normalizer Subgroup.le_normalizer le_rfl hP2
    intro h
    exact hP1 (le_bot_iff.mp (h ▸ hPQ))
  have hSM : S ≤ M := hST.trans hTM
  have hBHM : B ≤ H ⊓ M := le_inf hBH' ((hBQ.trans hQS).trans hSM)
  have hBQ' : B ≤ pCoreOf 2 (H ⊓ M) :=
    le_pCoreOf_of_le_normalizer hBHM (inf_le_left.trans hHB) hB
  have hC : pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) ≤ H := fun x hx =>
    hCBH (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBQ') hx.2)
  have hzB : z ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun b hb => Subgroup.mem_centralizer_iff.mp hzc b (hBT hb)
  have hzS : z ∈ S := by
    rw [← inf_eq_of_isSylowTwoOf_of_le hS hT.2.1 hST]
    exact ⟨hzT, hCBH hzB⟩
  exact
    { pCore_ne_bot := fun h => hB1 (le_bot_iff.mp (h ▸ hBQ))
      sylow := hS
      charTwo := hcharM
      pCore_M_ne_bot := hMpc
      le := hSM
      centralizer_le := hC
      centralizer_z_le := hCM
      z_ne_one := hz1
      z_mem := hzS
      z_central := Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hST) hzc
      z_sq := hz2 }

theorem actual_normalizer_intersection_and_component_action
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {B S T M : Subgroup G} {z : G}
    (hB : IsPGroup 2 B) (hB1 : B ≠ ⊥) (hS : IsSylowTwoOf S (Subgroup.normalizer (B : Set G)))
    (hT : IsSylowTwoOf T ⊤) (hST : S ≤ T) (hzT : z ∈ T)
    (hzc : z ∈ Subgroup.centralizer (T : Set G)) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hM : CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M)
    (hCM : Subgroup.centralizer ({z} : Set G) ≤ M) :
    B ≤ S ∧ CharTwo (Subgroup.normalizer (B : Set G) ⊓ M) ∧ z ∈ S ∧
      z ∈ Subgroup.centralizer (S : Set G) ∧
      oddCoreIn (Subgroup.normalizer (B : Set G)) ⊓ (Subgroup.normalizer (B : Set G) ⊓ M) = ⊥ ∧
      (∀ x ∈ oddCoreIn (Subgroup.normalizer (B : Set G)),
        ∀ y ∈ oddCoreIn (Subgroup.normalizer (B : Set G)), x * y = y * x) ∧
      (∀ y ∈ oddCoreIn (Subgroup.normalizer (B : Set G)), z⁻¹ * y * z = y⁻¹) ∧
      ∀ L : Subgroup G, IsComponentIn L (Subgroup.normalizer (B : Set G)) →
        z ∈ Subgroup.normalizer (L : Set G) ∧ ¬ L ≤ M ∧ ⁅L, Subgroup.zpowers z⁆ = L ∧
          CharTwo (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have h := lemma116 hev hB hB1
    (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))
    le_rfl hS hT hST hzT hzc hz1 hz2 hM hCM
  obtain ⟨hYA, -, hinv, hab⟩ := h.oddCoreIn_properties
  exact ⟨le_pCoreOf_of_le_normalizer Subgroup.le_normalizer le_rfl hB |>.trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS), h.charTwo_inf, h.z_mem, h.z_central, hYA,
    hab, hinv, fun L hL =>
      let hc := h.component_action hL
      ⟨hc.1, hc.2.2.1, hc.2.1, hc.2.2.2⟩⟩

end CFSG.QuasithinUnique
