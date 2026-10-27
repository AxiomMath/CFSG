module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLiftCtx
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFE2Weak
public import CFSG.Quasithin.Background.C118BridgeOne

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

structure FFH0Spec (M T V : Subgroup G) (hU : IsElemAbelian 2 V)
    (L : Subgroup (MulAut (IntMod V hU))) (H₀ : Subgroup G) : Prop where
  le_M : H₀ ≤ M
  baum_le : baum T ≤ H₀
  sylow : IsSylowTwoOf (baum T) H₀
  charTwo : CharTwo H₀
  minPar : IsMinParabolicOf H₀ H₀
  solvable : Group.IsSolvable ↥H₀
  autI_eq : autI hU H₀ = L ⊔ autI hU (baum T)
  normalizes : pCoreOf 2 M ≤ Subgroup.normalizer (H₀ : Set G)
  normalizes_res : pCoreOf 2 M ≤ Subgroup.normalizer (twoResidual H₀ : Set G)
  hJ : ¬ thompsonJ (baum T) ≤ Subgroup.centralizer (VZ (baum T) H₀ : Set G)
  cyclic3 : ∀ P : Subgroup G, P ≤ H₀ → IsPGroup 3 P → IsCyclic P

theorem mem_of_pow_mem_odd {N : Subgroup G} {x : G} (hodd : Odd (orderOf x)) {k : ℕ}
    (hk : x ^ 2 ^ k ∈ N) : x ∈ N := by
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  by_cases h1 : orderOf x = 1
  · rw [orderOf_eq_one_iff.mp h1]; exact N.one_mem
  have hlt : 1 < orderOf x := by
    have := orderOf_pos x; omega
  obtain ⟨j, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hlt
  have e : x ^ (2 ^ k * j) = x := by rw [← pow_mod_orderOf, hj.2, pow_one]
  have : x = (x ^ 2 ^ k) ^ j := by rw [← pow_mul, e]
  rw [this]
  exact N.pow_mem hk j

theorem pRank_three_autI_le_two {W : Subgroup G} (hW : IsElemAbelian 2 W) {H₀ : Subgroup G}
    (hc : ∀ P : Subgroup G, P ≤ H₀ → IsPGroup 3 P → IsCyclic P) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(autI hW H₀)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (W : Set G) with hN
  let f : ↥(H₀.subgroupOf N) →* ↥(autI hW H₀) := (convI hW).subgroupMap (H₀.subgroupOf N)
  have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective _ _
  let ι : ↥(H₀.subgroupOf N) →* G := N.subtype.comp (H₀.subgroupOf N).subtype
  have hι : Function.Injective ι := N.subtype_injective.comp (H₀.subgroupOf N).subtype_injective
  have hcyc : ∀ Y : Sylow 3 ↥(autI hW H₀), IsCyclic Y := by
    intro Y
    obtain ⟨R, rfl⟩ := Sylow.mapSurjective_surjective hf 3 Y
    have hR : IsCyclic ↥(R : Subgroup ↥(H₀.subgroupOf N)) := by
      have h1 : IsCyclic ↥((R : Subgroup ↥(H₀.subgroupOf N)).map ι) := by
        refine hc _ ?_ (R.2.map ι)
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      exact isCyclic_of_injective
        (Subgroup.equivMapOfInjective (R : Subgroup ↥(H₀.subgroupOf N)) ι hι).toMonoidHom
        (Subgroup.equivMapOfInjective _ ι hι).injective
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective (f.subgroupMap (R : Subgroup ↥(H₀.subgroupOf N)))
      (MonoidHom.subgroupMap_surjective _ _)
  refine csSup_le' ?_
  intro k hk
  have hk' : ∃ E : Subgroup ↥(autI hW H₀), E ≤ ⊤ ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k := hk
  obtain ⟨E, -, hEel, hE⟩ := hk'
  have hEp : IsPGroup 3 E := IsPGroup.of_card hE
  obtain ⟨Y, hEY⟩ := hEp.exists_le_sylow
  have hEc : IsCyclic E := by
    have := hcyc Y
    exact Subgroup.isCyclic_of_le hEY
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
  have hord : orderOf g = 3 ^ k := by
    rw [← hE]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  have h3 : g ^ 3 = 1 := Subtype.ext (hEel.2 g g.2)
  have hdvd : 3 ^ k ∣ 3 := hord ▸ orderOf_dvd_of_pow_eq_one h3
  have : k ≤ 1 := by
    by_contra hk1
    have : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega : 2 ≤ k)
    have := this.trans hdvd
    omega
  omega

theorem FFH0Spec.inClassG {M T V : Subgroup G} {hU : IsElemAbelian 2 V}
    {L : Subgroup (MulAut (IntMod V hU))} {H₀ : Subgroup G} (h : FFH0Spec M T V hU L H₀) :
    InClassG H₀ (baum T) := by
  obtain ⟨MP, hMP⟩ := CFSG.Quasithin.exists_minParabolic h.sylow h.minPar
  exact CFSG.Quasithin.C1Pack.inClassG_of_solvable_minParabolic' hMP h.charTwo h.solvable
    (fun hV₀ => pRank_three_autI_le_two hV₀ h.cyclic3) h.hJ (C1GN.baum_baum T)

section Ctx

variable {M T V : Subgroup G} {hU : IsElemAbelian 2 V}
  {hMN : M ≤ Subgroup.normalizer (V : Set G)}
  {I : Finset (Subgroup (MulAut (IntMod V hU)))} (ctx : FFCtx M T V hU hMN I)
  {L : Subgroup (MulAut (IntMod V hU))} (hL : L ∈ I) {H₀ : Subgroup G}
  (h : FFH0Spec M T V hU L H₀)
include ctx hL h

theorem FFH0Spec.card_three_le :
    ∀ Q : Subgroup (MulAut (IntMod V hU)), Q ≤ autI hU H₀ → IsPGroup 3 Q → Nat.card Q ≤ 3 := by
  intro Q hQ hQ3
  have hQL : Q ≤ L := by
    intro z hz
    have hz' : z ∈ L ⊔ autI hU (baum T) := h.autI_eq ▸ hQ hz
    obtain ⟨m, hm⟩ := ctx.exists_pow_mem_L hL hz'
    have hodd : Odd (orderOf z) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hQ3 ⟨z, hz⟩
      have : orderOf z = 3 ^ n := by rw [← Subgroup.orderOf_mk z hz]; exact hn
      rw [this]; exact Odd.pow (by decide)
    exact mem_of_pow_mem_odd hodd hm
  have hdvd : Nat.card Q ∣ Nat.card L := Subgroup.card_dvd_of_le hQL
  rw [ctx.hcard L hL] at hdvd
  obtain ⟨n, hn⟩ := hQ3.exists_card_eq
  rw [hn] at hdvd ⊢
  have h6 := Nat.le_of_dvd (by norm_num) hdvd
  by_contra hcon
  have hn2 : 2 ≤ n := by
    by_contra h2
    have : n ≤ 1 := by omega
    have : 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  omega

theorem FFH0Spec.conclusion :
    H₀ ≤ M ∧ L ≤ autI hU H₀ ∧
      (∀ Q : Subgroup (MulAut (IntMod V hU)), Q ≤ autI hU H₀ → IsPGroup 3 Q → Nat.card Q ≤ 3) ∧
      InClassG H₀ (baum T) ∧
      (IsL2OrA3Block H₀ (twoResidual H₀) →
        ∃ Y : Subgroup G, Y ≤ M ∧ IsSubnormal Y M ∧ InClassXBlock Y) :=
  ⟨h.le_M, h.autI_eq ▸ le_sup_left, h.card_three_le ctx hL, h.inClassG,
    fun hb => ctx.blockLift hL h.le_M h.autI_eq h.solvable h.normalizes_res hb⟩

end Ctx

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
