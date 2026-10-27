module

public import CFSG.GH74.GLS.LU.Local.FiveStdBase2
public import CFSG.GH74.GLS.Stage2.Final.ModelTransport

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local
  CFSG.GH74.GLS.Stage2.Final.ModelBlock

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd

theorem exists_equiv_sylow {Gs G : Type} [Group Gs] [Group G] [Finite Gs] [Finite G] (e : Gs ≃* G)
    (S₀ : Sylow 2 G) (z₀ : G) (hz₀ : orderOf z₀ = 2) (h₀ : CenterIs (S₀ : Subgroup G) z₀)
    (S' : Sylow 2 Gs) (z' : Gs) (hz' : orderOf z' = 2) (hc : CenterIs (S' : Subgroup Gs) z') :
    ∃ Ψ : Gs ≃* G, Ψ z' = z₀ ∧ (S' : Subgroup Gs).map Ψ.toMonoidHom = (S₀ : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ (sylowMap e S')
  have hcoe : ((g • S₀ : Sylow 2 G) : Subgroup G) =
      (S₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := toSubmonoid_inj.mp rfl
  have h1 : CenterIs ((sylowMap e S' : Sylow 2 G) : Subgroup G) ((MulAut.conj g) z₀) := by
    rw [← hg, hcoe]
    exact h₀.map_equiv (MulAut.conj g)
  have h2 : CenterIs ((sylowMap e S' : Sylow 2 G) : Subgroup G) (e z') := by
    rw [coe_sylowMap]
    exact hc.map_equiv e
  have hmem : e z' ∈ Subgroup.zpowers ((MulAut.conj g) z₀) :=
    (h1 (e z')).1 ((h2 (e z')).2 (Subgroup.mem_zpowers _))
  have hord1 : orderOf ((MulAut.conj g) z₀) = 2 := by rw [MulEquiv.orderOf_eq, hz₀]
  have hord2 : orderOf (e z') = 2 := by rw [MulEquiv.orderOf_eq, hz']
  have hez : e z' = (MulAut.conj g) z₀ := eq_of_mem_zpowers_of_orderOf_two hord1 hord2 hmem
  refine ⟨e.trans (MulAut.conj g⁻¹), ?_, ?_⟩
  · show (MulAut.conj g⁻¹) (e z') = z₀
    rw [hez]
    simp only [MulAut.conj_apply]
    group
  · have hS : (S' : Subgroup Gs).map e.toMonoidHom = (S₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [← coe_sylowMap e S', ← hg, hcoe]
    have hcomp : (e.trans (MulAut.conj g⁻¹)).toMonoidHom =
        (MulAut.conj g⁻¹).toMonoidHom.comp e.toMonoidHom := rfl
    rw [hcomp, ← Subgroup.map_map, hS, Subgroup.map_map]
    have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
      ext x
      show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      group
    rw [this, Subgroup.map_id]

theorem isPCompIn_two_of_isCompIn {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hO : pPrimeCoreOf 2 X = ⊥) (hK : IsCompIn X K) : IsPCompIn 2 X K := by
  refine ⟨hK.1, ?_⟩
  apply CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hK.2
  intro hle
  have h1 : pPrimeCore 2 ↥X = ⊥ := by
    have h2 : (pPrimeCore 2 ↥X).map X.subtype = ⊥ := hO
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 h2
  rw [h1, le_bot_iff] at hle
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hK.2.1
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt hle

namespace FiveStdSetting

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

omit [Finite G] in
theorem exists_sylow_std (hb : baseCheck = true) (hodd : Odd (Cz st.z).index) :
    ∃ S₀ : Sylow 2 G, ((S₀ : Subgroup G) : Set G) = S st.ι S0 ∧
      CenterIs (S₀ : Subgroup G) st.z ∧ st.K₁ ⊔ st.K₂ ⊔ (S₀ : Subgroup G) = Cz st.z := by
  obtain ⟨S0G, hset, hcard, hp2, hz, hzc, hZ, hCc, hcov⟩ := st.S0_facts hb
  have hG : Nat.card G = (Cz st.z).index * 28800 := by
    rw [← hCc]
    exact (Subgroup.index_mul_card _).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : S0G.index = (Cz st.z).index * 225 := by
    have h1 := Subgroup.index_mul_card S0G
    rw [hcard, hG] at h1
    omega
  obtain ⟨k, hk⟩ := hodd
  let S₀ : Sylow 2 G := hp2.toSylow (by rw [hidx, hk]; omega)
  have hS₀ : (S₀ : Subgroup G) = S0G := rfl
  obtain ⟨-, hV1, hV2, hV0, -⟩ := baseCheck_spec hb
  have hcen : CenterIs (S₀ : Subgroup G) st.z := by
    intro x
    rw [hS₀]
    constructor
    · rintro ⟨hx, hc⟩
      rcases hZ x hx hc with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · intro hx
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
      exact ⟨zpow_mem hz n, fun s hs => (Commute.zpow_right (show Commute s st.z from hzc s hs) n).eq⟩
  refine ⟨S₀, by rw [hS₀]; exact hset, hcen, ?_⟩
  rw [hS₀]
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      have hx' : x ∈ S st.ι K1l := by rw [← st.hK₁]; exact hx
      obtain ⟨k, hk, rfl⟩ := mem_S.1 hx'
      exact st.ι_mem_C (hV1 k hk)
    · intro x hx
      have hx' : x ∈ S st.ι K2l := by rw [← st.hK₂]; exact hx
      obtain ⟨k, hk, rfl⟩ := mem_S.1 hx'
      exact st.ι_mem_C (hV2 k hk)
    · intro x hx
      have hx' : x ∈ S st.ι S0 := by rw [← hset]; exact hx
      obtain ⟨k, hk, rfl⟩ := mem_S.1 hx'
      exact st.ι_mem_C (hV0 k hk)
  · intro c hc
    obtain ⟨k, hk, s, hs, rfl⟩ := hcov c hc
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hs)

end FiveStdSetting

end CFSG.GH74.GLS.LU.Local.Five
