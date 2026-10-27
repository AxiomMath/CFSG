module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34LocalB

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34Loc

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem normalizer_transport {Y : Type} [Group Y] {L : Subgroup G} {M : Subgroup Y}
    {S : Subgroup G} {T : Subgroup Y} (hSL : S ≤ L) (hTM : T ≤ M) (f : ↥L ≃* ↥M)
    (hf : ∀ z : ↥L, (z : G) ∈ S ↔ (f z : Y) ∈ T) (z : ↥L) :
    (z : G) ∈ Subgroup.normalizer (S : Set G) ↔ (f z : Y) ∈ Subgroup.normalizer (T : Set Y) := by
  have key : ∀ a b : ↥L, (f (a * b * a⁻¹) : Y) = (f a : Y) * (f b : Y) * (f a : Y)⁻¹ := by
    intro a b
    simp [map_mul, map_inv]
  have hfz : (f z : Y) ∈ M := (f z).2
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hz h
    by_cases hhM : h ∈ M
    · obtain ⟨s, hs⟩ := f.surjective ⟨h, hhM⟩
      have hsh : (f s : Y) = h := congrArg Subtype.val hs
      calc h ∈ T ↔ (s : G) ∈ S := by rw [← hsh]; exact (hf s).symm
        _ ↔ (z : G) * (s : G) * (z : G)⁻¹ ∈ S := hz s
        _ ↔ (f (z * s * z⁻¹) : Y) ∈ T := hf (z * s * z⁻¹)
        _ ↔ (f z : Y) * h * (f z : Y)⁻¹ ∈ T := by rw [key, hsh]
    · constructor
      · intro hhT
        exact absurd (hTM hhT) hhM
      · intro hyhT
        exfalso
        apply hhM
        have hm : (f z : Y) * h * (f z : Y)⁻¹ ∈ M := hTM hyhT
        have e : h = (f z : Y)⁻¹ * ((f z : Y) * h * (f z : Y)⁻¹) * (f z : Y) := by group
        rw [e]
        exact M.mul_mem (M.mul_mem (M.inv_mem hfz) hm) hfz
  · intro hz s
    by_cases hsL : s ∈ L
    · let s' : ↥L := ⟨s, hsL⟩
      have h1 : s ∈ S ↔ (f s' : Y) ∈ T := hf s'
      have h2 : (f s' : Y) ∈ T ↔ (f z : Y) * (f s' : Y) * (f z : Y)⁻¹ ∈ T := hz _
      have h3 : (f z : Y) * (f s' : Y) * (f z : Y)⁻¹ = (f (z * s' * z⁻¹) : Y) := (key z s').symm
      rw [h1, h2, h3]
      exact (hf _).symm
    · have hs1 : s ∉ S := fun h => hsL (hSL h)
      have hs2 : (z : G) * s * (z : G)⁻¹ ∉ S := by
        intro h
        apply hsL
        have e : s = (z : G)⁻¹ * ((z : G) * s * (z : G)⁻¹) * (z : G) := by group
        rw [e]
        exact L.mul_mem (L.mul_mem (L.inv_mem z.2) (hSL h)) z.2
      exact ⟨fun h => absurd h hs1, fun h => absurd h hs2⟩

theorem side_iso [Finite G] {Y : Type} [Group Y] [Finite Y]
    {L1 L2 S : Subgroup G} {M1 M2 T0 : Subgroup Y}
    (hS : IsSylowTwoOf S L1) (hS64 : Nat.card S = 64)
    (hQ1S : pCoreOf 2 L1 ≤ S) (hQ1e : IsElemAbelian 2 (pCoreOf 2 L1)) (hQ1c : Nat.card (pCoreOf 2 L1) = 16)
    (hQ2S : pCoreOf 2 L2 ≤ S) (hQ2e : IsElemAbelian 2 (pCoreOf 2 L2)) (hQ2c : Nat.card (pCoreOf 2 L2) = 16)
    (hE : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) = 4)
    (hnat1 : NatSec L1 ⊥ (pCoreOf 2 L1)) (hquot1 : IsL2Quot 2 (oTwoQuot ↥L1))
    (hnt1 : ∃ l ∈ L1, ∃ e ∈ pCoreOf 2 L1, ⁅l, e⁆ ∉ (⊥ : Subgroup G))
    (hT : IsSylowTwoOf T0 M1) (hT64 : Nat.card T0 = 64)
    (hM1e : IsElemAbelian 2 (pCoreOf 2 M1)) (hM1c : Nat.card (pCoreOf 2 M1) = 16)
    (hM1nat : NatSec M1 ⊥ (pCoreOf 2 M1)) (hquotM1 : IsL2Quot 2 (oTwoQuot ↥M1))
    (hM2e : IsElemAbelian 2 (pCoreOf 2 M2)) (hM2c : Nat.card (pCoreOf 2 M2) = 16)
    (hM1T : pCoreOf 2 M1 ≤ T0) (hM2T : pCoreOf 2 M2 ≤ T0)
    (hne : pCoreOf 2 M1 ≠ pCoreOf 2 M2)
    {x : Y} (hxM : x ∈ M1 ⊓ M2) (hx3 : orderOf x = 3) :
    ∃ ψ : ↥L1 ≃* ↥M1, (∀ z : ↥L1, (z : G) ∈ S ↔ (ψ z : Y) ∈ T0) ∧
      (∀ z : ↥L1, (z : G) ∈ pCoreOf 2 L1 ↔ (ψ z : Y) ∈ pCoreOf 2 M1) ∧
      (∀ z : ↥L1, (z : G) ∈ Subgroup.normalizer (S : Set G) ↔
        (ψ z : Y) ∈ Subgroup.normalizer (T0 : Set Y)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL1 : S ≤ L1 := hS.1
  obtain ⟨K1, hK1L, hK1Q, hQK1⟩ := split_of_sylow hS hS64 hQ1S hQ1e hQ1c hQ2S hQ2e hQ2c hE
  have hdecL : ∀ z ∈ L1, ∃ q ∈ pCoreOf 2 L1, ∃ k ∈ K1, q * k = z := fun z hz => by
    have hz' : z ∈ pCoreOf 2 L1 ⊔ K1 := by rw [hQK1]; exact hz
    exact mem_sup_of_le_normalizer (fun k hk => le_normalizer_pCore L1 (hK1L hk)) hz'
  have hE0 : Nat.card ↥(pCoreOf 2 M1 ⊓ pCoreOf 2 M2) = 4 :=
    card_inf_four hT64 hxM hx3 hM1e hM1c hM1nat hM1T hM2T hM2c hne
  obtain ⟨K1', hK1'M, hK1'R, hRK1'⟩ := split_of_sylow hT hT64 hM1T hM1e hM1c hM2T hM2e hM2c hE0
  have hdecM : ∀ y ∈ M1, ∃ r ∈ pCoreOf 2 M1, ∃ k ∈ K1', r * k = y := fun y hy => by
    have hy' : y ∈ pCoreOf 2 M1 ⊔ K1' := by rw [hRK1']; exact hy
    exact mem_sup_of_le_normalizer (fun k hk => le_normalizer_pCore M1 (hK1'M hk)) hy'
  obtain ⟨AL⟩ := a5model_of_natSec hQ1e hQ1c hquot1 hnat1 hnt1
  obtain ⟨AM⟩ := a5model_of_natSec hM1e hM1c hquotM1 hM1nat
    (nontriv_of_natSec hM1nat hM1c hxM.1 hx3)
  obtain ⟨β, α, hβα⟩ := alpha_beta hK1L hK1'M hK1Q hK1'R hdecL hdecM AL AM
  have hVL : pCoreOf 2 L1 ≤ L1 := CFSG.LieType.BorelTits.pCoreOf_le 2 L1
  have hV'M : pCoreOf 2 M1 ≤ M1 := CFSG.LieType.BorelTits.pCoreOf_le 2 M1
  obtain ⟨ψ, hψβ, -⟩ := semidirect_mulEquiv hVL hK1L hV'M hK1'M
    (fun h hh v hv => conj_mem_pCoreOf (Subgroup.le_normalizer hh) hv) hdecL hK1Q hdecM hK1'R β α hβα
  have hQprop : ∀ z : ↥L1, (z : G) ∈ pCoreOf 2 L1 ↔ (ψ z : Y) ∈ pCoreOf 2 M1 := by
    intro z
    constructor
    · intro hz
      rw [hψβ z hz]
      exact (β ⟨(z : G), hz⟩).2
    · intro hz
      let w : ↥(pCoreOf 2 M1) := ⟨(ψ z : Y), hz⟩
      let v : ↥(pCoreOf 2 L1) := β.symm w
      let vL : ↥L1 := ⟨(v : G), hVL v.2⟩
      have h1 : (ψ vL : Y) = (ψ z : Y) := by
        rw [hψβ vL v.2]
        have hv : β v = w := β.apply_symm_apply w
        exact congrArg Subtype.val hv
      have h2 : vL = z := ψ.injective (Subtype.ext h1)
      have h3 : (z : G) = (v : G) := by rw [← h2]
      rw [h3]
      exact v.2
  let S₁ : Subgroup Y := ((S.subgroupOf L1).map ψ.toMonoidHom).map M1.subtype
  have hS₁mem : ∀ z : ↥L1, (ψ z : Y) ∈ S₁ ↔ (z : G) ∈ S := by
    intro z
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      obtain ⟨z', hz', hz'w⟩ := Subgroup.mem_map.mp hw
      have hw1 : (ψ z' : Y) = (ψ z : Y) := by
        have a1 : ψ z' = w := hz'w
        have a2 : (w : Y) = (ψ z : Y) := hwz
        rw [a1, a2]
      have h2 : z' = z := ψ.injective (Subtype.ext hw1)
      rw [← h2]
      exact Subgroup.mem_subgroupOf.mp hz'
    · intro hz
      exact Subgroup.mem_map.mpr ⟨ψ z, Subgroup.mem_map.mpr ⟨z, Subgroup.mem_subgroupOf.mpr hz, rfl⟩, rfl⟩
  have hS₁card : Nat.card ↥S₁ = 64 := by
    have e1 : Nat.card ↥S₁ = Nat.card ↥((S.subgroupOf L1).map ψ.toMonoidHom) :=
      Subgroup.card_map_of_injective (M1.subtype_injective) 
    have e2 : Nat.card ↥((S.subgroupOf L1).map ψ.toMonoidHom) = Nat.card ↥(S.subgroupOf L1) :=
      Subgroup.card_map_of_injective ψ.injective
    have e3 : Nat.card ↥(S.subgroupOf L1) = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL1).toEquiv
    rw [e1, e2, e3, hS64]
  have hS₁le : S₁ ≤ M1 := Subgroup.map_subtype_le _
  have hS₁M : IsSylowTwoOf S₁ M1 := by
    refine ⟨hS₁le, ?_, ?_⟩
    · exact (IsPGroup.iff_card).mpr ⟨6, by rw [hS₁card]; norm_num⟩
    · have hidx1 := (S₁.subgroupOf M1).index_mul_card
      have hidx2 := (T0.subgroupOf M1).index_mul_card
      have hc1 : Nat.card ↥(S₁.subgroupOf M1) = 64 := by
        rw [← hS₁card]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₁le).toEquiv
      have hc2 : Nat.card ↥(T0.subgroupOf M1) = 64 := by
        rw [← hT64]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv
      have heq : (S₁.subgroupOf M1).index = (T0.subgroupOf M1).index := by
        have h64 : (S₁.subgroupOf M1).index * Nat.card ↥(S₁.subgroupOf M1) =
            (T0.subgroupOf M1).index * Nat.card ↥(T0.subgroupOf M1) := by
          rw [hidx1, hidx2]
        rw [hc1, hc2] at h64
        exact Nat.eq_of_mul_eq_mul_right (by norm_num) h64
      rw [heq]
      exact hT.2.2
  obtain ⟨g, hgM, hTg⟩ := B6.isSylowTwoOf_exists_conj hS₁M hT
  let gM : ↥M1 := ⟨g, hgM⟩
  let ψ' : ↥L1 ≃* ↥M1 := ψ.trans (MulAut.conj gM)
  have hψ'val : ∀ z : ↥L1, (ψ' z : Y) = g * (ψ z : Y) * g⁻¹ := fun z => rfl
  have hψ'S : ∀ z : ↥L1, (z : G) ∈ S ↔ (ψ' z : Y) ∈ T0 := by
    intro z
    rw [hTg, B6.mem_conjSub, hψ'val]
    have e : g⁻¹ * (g * (ψ z : Y) * g⁻¹) * g = (ψ z : Y) := by group
    rw [e]
    exact (hS₁mem z).symm
  have hψ'Q : ∀ z : ↥L1, (z : G) ∈ pCoreOf 2 L1 ↔ (ψ' z : Y) ∈ pCoreOf 2 M1 := by
    intro z
    rw [hQprop z, hψ'val]
    constructor
    · intro h
      exact conj_mem_pCoreOf (Subgroup.le_normalizer hgM) h
    · intro h
      have h' := conj_mem_pCoreOf (Subgroup.le_normalizer (M1.inv_mem hgM)) h
      have e : g⁻¹ * (g * (ψ z : Y) * g⁻¹) * g⁻¹⁻¹ = (ψ z : Y) := by group
      rwa [e] at h'
  exact ⟨ψ', hψ'S, hψ'Q, fun z => normalizer_transport hSL1 hT.1 ψ' hψ'S z⟩

end CFSG.GH74.QTGen4.DSGen4.L34Loc
