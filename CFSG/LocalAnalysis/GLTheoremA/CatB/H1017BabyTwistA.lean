module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistGen
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017TwistFi22
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeAGlue

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.BabyTwist

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.H1017
open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.Existence CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.I271

section Generic

variable {G : Type} [Group G]

private theorem le_centralizer_of_mulEquiv {G' : Type} [Group G'] (ρ : G ≃* G') {s : G}
    (h : ∀ E' T' : Subgroup G', IsElemAbelian 3 E' → 3 ^ 5 ≤ Nat.card E' → IsPGroup 2 T' →
      E' ≤ Subgroup.normalizer (T' : Set G') → ρ s ∈ E' → (∀ t ∈ T', t * ρ s = ρ s * t) →
      ∀ e ∈ E', ∀ t ∈ T', e * t = t * e)
    {E T : Subgroup G} (hE : IsElemAbelian 3 E) (hcard : 3 ^ 5 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) (hsE : s ∈ E)
    (hTs : T ≤ Subgroup.centralizer ({s} : Set G)) :
    T ≤ Subgroup.centralizer (E : Set G) := by
  have key := h (E.map ρ.toMonoidHom) (T.map ρ.toMonoidHom) (isElemAbelian_map' _ hE)
    (by rwa [Subgroup.card_map_of_injective ρ.injective]) (hT.map _)
    (by rw [← Subgroup.map_equiv_normalizer_eq]; exact Subgroup.map_mono hET)
    (Subgroup.mem_map.2 ⟨s, hsE, rfl⟩)
    (by
      rintro _ ⟨t, ht, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.1 (hTs ht)])
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h' := key _ (Subgroup.mem_map.2 ⟨e, he, rfl⟩) _ (Subgroup.mem_map.2 ⟨t, ht, rfl⟩)
  rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul] at h'
  exact ρ.injective h'

end Generic

section Baby


private theorem comm_of_typeThree {v w : CVert} (hw : w ∈ sphereThree v) (E T : Subgroup Shat)
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 5 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set Shat)) (hsE : clabelS v * clabelS w ∈ E)
    (hTs : ∀ t ∈ T, t * (clabelS v * clabelS w) = clabelS v * clabelS w * t) :
    ∀ e ∈ E, ∀ t ∈ T, e * t = t * e := by
  have hHQ : cnGroup v w ≤ vStab v ⊓ vStab w := by
    obtain ⟨θ₀, -, hTT⟩ := native_order_three_common_neighbor_three_transposition_group
    exact (hTT v w hw).1
  have hcardH : Nat.card (cnGroup v w) = 64561751654400 :=
    (native_three_transposition_group_simple v w hw).2.2.1
  have hcardQ : Nat.card (vStab v ⊓ vStab w : Subgroup Shat) = 129123503308800 :=
    (native_order_three_common_neighbors_exact_3510.1 v w hw).2.2.2.2.2
  have hidx : ((cnGroup v w).subgroupOf (vStab v ⊓ vStab w)).index = 2 := by
    have h1 := ((cnGroup v w).subgroupOf (vStab v ⊓ vStab w)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHQ).toEquiv, hcardH, hcardQ] at h1
    omega
  obtain ⟨eF⟩ := native_three_transposition_group_nonempty_mulEquiv_Fi22 hw
  obtain ⟨eB⟩ : Nonempty (CFSG.Blueprint.NativeSporadic.Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic .Fi22).Group) := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have hHtw : ∀ E' T' : Subgroup Shat, E' ≤ cnGroup v w → T' ≤ cnGroup v w →
      IsElemAbelian 3 E' → 3 ^ 4 ≤ Nat.card E' → IsPGroup 2 T' →
      E' ≤ Subgroup.normalizer (T' : Set Shat) → ∀ e ∈ E', ∀ t ∈ T', e * t = t * e :=
    fun _ _ hE'H hT'H hE' hc hT' hN =>
      i1017FiTwoTwoTwist_holds.comm_of_subgroup ⟨eF.trans eB⟩ hE'H hT'H hE' hc hT' hN
  have h3 : orderOf (clabel v * clabel w) = 3 :=
    ((native_order_three_label_products_and_dihedral_triples v).1 w hw).1
  have hd2 : clabelS v * clabelS v = 1 := by
    have := pow_orderOf_eq_one (clabelS v)
    rwa [orderOf_clabelS, sq] at this
  have he2 : clabelS w * clabelS w = 1 := by
    have := pow_orderOf_eq_one (clabelS w)
    rwa [orderOf_clabelS, sq] at this
  have hso : orderOf (clabelS v * clabelS w) = 3 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, coe_clabelS, coe_clabelS]
    exact h3
  have hqs : ∀ q ∈ vStab v ⊓ vStab w, q * (clabelS v * clabelS w) =
      clabelS v * clabelS w * q := by
    intro q hq
    have h1 := commute_of_mem_vStab (Subgroup.mem_inf.1 hq).1
    have h2 := commute_of_mem_vStab (Subgroup.mem_inf.1 hq).2
    calc q * (clabelS v * clabelS w) = q * clabelS v * clabelS w := by rw [mul_assoc]
      _ = clabelS v * q * clabelS w := by rw [h1]
      _ = clabelS v * (q * clabelS w) := by rw [mul_assoc]
      _ = clabelS v * (clabelS w * q) := by rw [h2]
      _ = clabelS v * clabelS w * q := by rw [mul_assoc]
  have hcard3 := tabBThree_bThreeABound v w hw
  obtain ⟨s, hs⟩ : ∃ s : Shat, s = clabelS v * clabelS w := ⟨_, rfl⟩
  rw [← hs] at hso hqs hcard3 hsE hTs
  have hs3 : s * s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hso, pow_three'] at this
  have hQC : vStab v ⊓ vStab w ≤ Subgroup.centralizer ({s} : Set Shat) :=
    fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hqs q hq)
  have hsQ : s ∉ vStab v ⊓ vStab w := by
    intro hsQ
    have h1 := commute_of_mem_vStab (Subgroup.mem_inf.1 hsQ).1
    rw [hs] at h1
    have h2 : s * s = 1 := by
      rw [hs]
      calc clabelS v * clabelS w * (clabelS v * clabelS w)
          = clabelS v * clabelS w * clabelS v * clabelS w := by simp only [mul_assoc]
        _ = clabelS v * (clabelS v * clabelS w) * clabelS w := by rw [h1]
        _ = 1 := by rw [← mul_assoc, hd2, one_mul, he2]
    have h4 : s = 1 := by
      calc s = s * s * s * (s * s)⁻¹ := by group
        _ = 1 := by rw [hs3, h2, inv_one, one_mul]
    rw [h4, orderOf_one] at hso
    exact absurd hso (by norm_num)
  have hdecomp := mem_pow_mul_of_card_le (Subgroup.mem_centralizer_singleton_iff.2 rfl) hQC hs3
    hsQ hcard3
  have hs3' : s ^ 3 = 1 := by rw [pow_three']; exact hs3
  exact comm_of_pow_mul_index_two (r := 5) (by norm_num) hs3' hqs hdecomp hidx hHtw hE hcard hT
    hET hsE hTs

theorem le_centralizer_of_threeA {E T : Subgroup NativeSporadic.B} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 5 ≤ Nat.card E) (hT : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set NativeSporadic.B)) {s d : NativeSporadic.B}
    (hsE : s ∈ E) (hs1 : s ≠ 1) (hd : BabyInv 0 d) (hinv : d * s * d⁻¹ = s⁻¹)
    (hTs : T ≤ Subgroup.centralizer ({s} : Set NativeSporadic.B)) :
    T ≤ Subgroup.centralizer (E : Set NativeSporadic.B) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : orderOf s = 3 := orderOf_eq_prime (hE.2 s hsE) hs1
  obtain ⟨v, w, hw, hρ⟩ := tabBThree_typeThree_of_inverted hs3 hd hinv
  have hS := comm_of_typeThree hw
  rw [← hρ] at hS
  with_reducible_and_instances
    exact le_centralizer_of_mulEquiv babyToShat hS hE hcard hT hET hsE hTs

end Baby

end CFSG.LocalAnalysis.GLTheoremA.H1017.BabyTwist
