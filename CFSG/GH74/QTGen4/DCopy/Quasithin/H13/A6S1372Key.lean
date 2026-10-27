module

public import CFSG.Quasithin.H13.A6S1372Key
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13721b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

@[expose] def Key13721_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L → S.G1 ∈ S.Hz →
    IsElemAbelian 2 (conjClosure S.V3 S.G1) → ¬ IsElemAbelian 2 (conjClosure V S.G1) →
    ∃ K ∈ cComp S.G1, ∃ hL1K : S.L1 ≤ K,
      K ≤ Subgroup.centralizer ((conjClosure S.V3 S.G1 ⊓
        Subgroup.centralizer (pCoreOf 2 S.G1 : Set G) : Subgroup G) : Set G) ∧
      ⁅conjClosure S.V3 S.G1, K⁆ ⊔ fsuV1 T V = conjClosure S.V3 S.G1 ∧
      ∃ (α : ↥K →* alternatingGroup (Fin 6)) (β : ↥(conjClosure S.V3 S.G1) →* ↥W4),
        Function.Surjective α ∧ (∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 S.G1) ∧
        Function.Surjective β ∧
        (∀ u : ↥(conjClosure S.V3 S.G1),
          β u = 1 ↔ ∀ k ∈ K, k * (u : G) * k⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V) ∧
        (∀ (k : ↥K) (u : ↥(conjClosure S.V3 S.G1))
          (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 S.G1),
          β ⟨_, hku⟩ = act4 (α k : Perm (Fin 6)) (β u)) ∧
        ∀ c (hc : c ∈ S.L1), c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 →
          ∀ w : ↥W4, act4 (α ⟨c, hL1K hc⟩ : Perm (Fin 6)) w = w → w = 1

theorem input13721K_of_key_F4
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) (hKey : Key13721_F4) : Input13721K_F4 := by
  intro G _ _ T L V S hNS hNU hhat hG1 hab hna
  obtain ⟨K, hKc, hL1K, hKU0, hUK, α, β, hαs, hαk, hβs, hβk, hβα, hfix⟩ :=
    hKey G T L V S hNS hNU hhat hG1 hab hna
  have hF := S.hypF91_F4 hNS h13315 h1356two hG1
  let D : S.KeyData S.G1 K := ⟨le_of_mem_cComp hKc, α, β, hαs, hαk, hβs, hβk, hβα, hUK⟩
  have hHK := D.le_normalizer_of_key hG1 hF hKc
  refine ⟨K, hHK, hL1K, D.sup_eq_of_key hG1 hF hHK, hKU0, ⟨α, hαs, hαk⟩,
    fun h hh hk => D.mem_pCoreOf_of_comm hG1 hF hh hk, fun c hc hc3 hcO => ⟨?_, ?_⟩⟩
  · exact D.exists_comm_not_mem_of_key hhat hG1 hHK hL1K hc hc3 (hfix c hc hc3 hcO)
  · exact D.sixteen_le_nu_of_key (hL1K hc) (hfix c hc hc3 hcO)

end CFSG.Quasithin.H13.A6
