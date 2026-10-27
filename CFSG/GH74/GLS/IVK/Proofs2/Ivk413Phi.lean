module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Clauses
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.L5U5

namespace CFSG.GH74.Ivk413

variable {F : Type} [Field F]

theorem exists_sylow_center_good [Finite F] {M : ModelData F} (hG : GoodModel M) :
    ∃ S : Sylow 2 (PG M), CenterIs (S : Subgroup (PG M)) (yP M) := by
  obtain ⟨a, b, hab, hH⟩ := hG.quat
  obtain ⟨S, hS⟩ := exists_sylow_center M hG.two_ne_zero hG.odd_index (rhoQ hab) hH
    (rhoQ_irr hab hG.two_ne_zero) (rhoQ_nc hab) isPGroup_q8q8
  exact ⟨S, (centerIs_iff _ _).1 hS⟩

theorem exists_Phi [Finite F] {M : ModelData F} (hG : GoodModel M) {H : Type} [Group H] [Finite H]
    (K : Subgroup H) [K.Normal] (e : ↥K ≃* PG M) {z : H} (hz : z ∈ K) (S : Sylow 2 H)
    (hzS : z ∈ (S : Subgroup H)) (hz2 : orderOf z = 2)
    (hSc : ∀ x ∈ (S : Subgroup H) ⊓ K, x * z = z * x) :
    ∃ Φ : ↥K ≃* PG M, Φ ⟨z, hz⟩ = yP M := by
  obtain ⟨S₁, hS₁⟩ := exists_sylow_center_good hG
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal S K
  have hz'ord : orderOf (⟨z, hz⟩ : ↥K) = 2 := by
    rw [← hz2]
    exact Subgroup.orderOf_mk z hz
  have hzP : (⟨z, hz⟩ : ↥K) ∈ (P : Subgroup ↥K) := by
    have h : z ∈ (P : Subgroup ↥K).map K.subtype := by
      rw [hP]
      exact ⟨hzS, hz⟩
    obtain ⟨x, hx, hxz⟩ := h
    have : x = ⟨z, hz⟩ := Subtype.ext hxz
    exact this ▸ hx
  have hc : ∀ s ∈ (P : Subgroup ↥K), s * ⟨z, hz⟩ = ⟨z, hz⟩ * s := by
    intro s hs
    apply Subtype.ext
    have h : (s : H) ∈ (S : Subgroup H) ⊓ K := by
      rw [← hP]
      exact ⟨s, hs, rfl⟩
    exact hSc _ h
  obtain ⟨z', hz'o, hz'c⟩ :=
    sylow_center_transport e S₁ (yP M) (orderOf_yP M hG.two_ne_zero) hS₁ P
  have hmem : (⟨z, hz⟩ : ↥K) ∈ Subgroup.zpowers z' := by
    rw [← hz'c]
    refine ⟨⟨⟨z, hz⟩, hzP⟩, Subgroup.mem_center_iff.2 (fun g => ?_), rfl⟩
    exact Subtype.ext (hc g.1 g.2)
  have heq : (⟨z, hz⟩ : ↥K) = z' := eq_of_mem_zpowers_of_orderOf_two hz'o hz'ord hmem
  have hcen : (Subgroup.center ↥(P : Subgroup ↥K)).map (P : Subgroup ↥K).subtype =
      Subgroup.zpowers (⟨z, hz⟩ : ↥K) := by
    rw [hz'c, heq]
  exact exists_equiv_of_center e S₁ (yP M) (orderOf_yP M hG.two_ne_zero) hS₁ P ⟨z, hz⟩ hz'ord hcen

theorem core_clauses [Finite F] {M : ModelData F} (hG : GoodModel M) (hAut : AutInner M)
    (hratio : (Nat.card ↥(Cg M) / Nat.card ↥(K1 M ⊔ K2 M)).factorization 2 = 2)
    {H : Type} [Group H] [Finite H] (K : Subgroup H) [K.Normal]
    (hC : centralizer (K : Set H) = ⊥) (e : ↥K ≃* PG M) {z : H} (hz : z ∈ K) (S : Sylow 2 H)
    (hzS : z ∈ (S : Subgroup H)) (hz2 : orderOf z = 2)
    (hSc : ∀ x ∈ (S : Subgroup H) ⊓ K, x * z = z * x) :
    (Nat.card ↥(centralizer ({z} : Set H) ⊓ K) /
      Nat.card ↥((layer ↥(centralizer ({z} : Set H) ⊓ K)).map
        (centralizer ({z} : Set H) ⊓ K).subtype)).factorization 2 = 2 ∧
    (pPrimeCore 2 ↥(centralizer ({z} : Set H) ⊓ K)).map (centralizer ({z} : Set H) ⊓ K).subtype =
      (pPrimeCore 2 ↥(centralizer ({z} : Set H))).map (centralizer ({z} : Set H)).subtype ∧
    ∀ K₁ : Subgroup H, K₁ ≤ centralizer ({z} : Set H) ⊓ K →
      IsComponent (K₁.subgroupOf (centralizer ({z} : Set H) ⊓ K)) →
        ∀ y ∈ (pPrimeCore 2 ↥(centralizer ({z} : Set H) ⊓ K)).map
            (centralizer ({z} : Set H) ⊓ K).subtype,
          ∀ g ∈ K ⊓ normalizer (K₁ : Set H), g * y = y * g := by
  obtain ⟨Φ, hΦ⟩ := exists_Phi hG K e hz S hzS hz2 hSc
  refine ⟨clause2 K hG hz Φ hΦ hratio, ?_, ?_⟩
  · exact clause3 hG hAut K hC hz Φ hΦ
  · intro K₁ hK₁ hcomp y hy g hg
    exact clause4 K hG hz Φ hΦ hK₁ hcomp hy hg

theorem pPrimeCoreOf_inf_eq_bot_of_Phi {M : ModelData F} {H : Type} [Group H] (K : Subgroup H)
    {z : H} (hz : z ∈ K) (Φ : ↥K ≃* PG M) (hΦ : Φ ⟨z, hz⟩ = yP M)
    (hbot : pPrimeCoreOf 2 (Cg M) = ⊥) :
    pPrimeCoreOf 2 (centralizer ({z} : Set H) ⊓ K) = ⊥ := by
  rw [pPrimeCoreOf_inf_eq_map K hz]
  have h := pPrimeCoreOf_map_Phi K hz Φ hΦ
  rw [hbot] at h
  have h0 : pPrimeCoreOf 2 (centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Φ.injective).1 h
  rw [h0, Subgroup.map_bot]

end CFSG.GH74.Ivk413
