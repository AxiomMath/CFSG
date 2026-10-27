module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.Quasithin.EmptyFaithful.S1421QA24Borel

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSBA5

theorem card_eq_mul_card_map {H : Type} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    {A : Subgroup H} (hNA : N ≤ A) :
    Nat.card A = Nat.card N * Nat.card (A.map (QuotientGroup.mk' N)) := by
  have hker : (QuotientGroup.mk' N).ker ≤ A := by
    rw [QuotientGroup.ker_mk']
    exact hNA
  have hidx : (A.map (QuotientGroup.mk' N)).index = A.index :=
    A.index_map_eq (QuotientGroup.mk'_surjective N) hker
  have h1 := Subgroup.card_mul_index A
  have h2 := Subgroup.card_mul_index (A.map (QuotientGroup.mk' N))
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < A.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card A * A.index = Nat.card H := h1
    _ = Nat.card (H ⧸ N) * Nat.card N := h3
    _ = Nat.card (A.map (QuotientGroup.mk' N)) * (A.map (QuotientGroup.mk' N)).index *
          Nat.card N := by
        rw [h2]
    _ = Nat.card N * Nat.card (A.map (QuotientGroup.mk' N)) * A.index := by
        rw [hidx]
        ring

open CFSG.GH74.Uniqueness.Bender in
theorem three_and_card {G : Type} [Group G] [Finite G] {T K : Subgroup G}
    (hsyl : IsSylowTwoOf (T ⊓ K) K) (hq : IsL2Quot 2 (oTwoQuot ↥K)) :
    (∃ y ∈ borelOf K T, orderOf y = 3) ∧ Nat.card ↥(T ⊓ K) = 4 * Nat.card ↥(pCoreOf 2 K) := by
  obtain ⟨e⟩ := hq
  have hπs := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥K)
  have hP0 : IsSylowTwoOf ((T ⊓ K).subgroupOf K) ⊤ := isSylowTwoOf_top_subgroupOf hsyl
  obtain ⟨Q, hQ⟩ := QA24.exists_sylow_two_of_top
    (isSylowTwoOf_top_map_of_surjective hP0 _ hπs)
  obtain ⟨t, hcore⟩ := exists_benderCore_psl2 e (by norm_num) Q
  have hQcard : Nat.card (Q : Subgroup (OTwoQuot K)) = 4 := by
    rw [hcore.card_eq]
    norm_num
  have himg : Nat.card (((T ⊓ K).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K))) = 4 := by
    rw [← hQ]
    exact hQcard
  have hcart : Nat.card ↥(cartan (Q : Subgroup (OTwoQuot K)) t) = 3 := by
    rw [hcore.card_cartan]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(cartan (Q : Subgroup (OTwoQuot K)) t)) 3 (by rw [hcart])
  have hcb : (c : OTwoQuot K) ∈ borel (Q : Subgroup (OTwoQuot K)) := by
    have : (c : OTwoQuot K) ∈ (Q : Subgroup (OTwoQuot K)) ⊔ cartan (Q : Subgroup _) t :=
      Subgroup.mem_sup_right c.2
    rwa [hcore.sup_eq] at this
  have hcN : (c : OTwoQuot K) ∈ Subgroup.normalizer ((Q : Subgroup (OTwoQuot K)) : Set _) := hcb
  have hc3 : orderOf (c : OTwoQuot K) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hc
  obtain ⟨k, hk⟩ := hπs (c : OTwoQuot K)
  have hOle : pCoreOf 2 K ≤ T ⊓ K := F7.isSylowTwoOf_pCoreOf_le hsyl
  have hkN : (k : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    refine CFSG.RankThree.PartOne.mem_normalizer_of_conj_subset fun x hx => ?_
    have hxK : x ∈ K := hx.2
    have hxP : (⟨x, hxK⟩ : ↥K) ∈ (T ⊓ K).subgroupOf K := hx
    have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) (k * ⟨x, hxK⟩ * k⁻¹) ∈
        (Q : Subgroup (OTwoQuot K)) := by
      rw [map_mul, map_mul, map_inv, hk]
      exact (Subgroup.mem_normalizer_iff.mp hcN _).mp (hQ ▸ Subgroup.mem_map_of_mem _ hxP)
    rw [hQ] at h1
    obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp h1
    have h2 : (x'⁻¹ * (k * ⟨x, hxK⟩ * k⁻¹) : ↥K) ∈
        (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) : ↥K →* OTwoQuot K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', inv_mul_cancel]
    rw [QuotientGroup.ker_mk'] at h2
    have h3 : (((x'⁻¹ * (k * ⟨x, hxK⟩ * k⁻¹) : ↥K)) : G) ∈ T ⊓ K :=
      hOle (Subgroup.mem_map_of_mem K.subtype h2)
    have h4 : (x' : G) ∈ T ⊓ K := hx'
    have h5 : (k : G) * x * (k : G)⁻¹ =
        (x' : G) * (((x'⁻¹ * (k * ⟨x, hxK⟩ * k⁻¹) : ↥K)) : G) := by
      simp [mul_assoc]
    rw [h5]
    exact (T ⊓ K).mul_mem h4 h3
  have hk3 : 3 ∣ orderOf (k : G) := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) : ↥K →* OTwoQuot K) k
    rw [hk, hc3] at h
    rw [Subgroup.orderOf_coe]
    exact h
  have hy : (k : G) ^ (orderOf (k : G) / 3) ∈ borelOf K T :=
    ⟨Subgroup.pow_mem _ k.2 _, Subgroup.pow_mem _ hkN _⟩
  refine ⟨⟨(k : G) ^ (orderOf (k : G) / 3), hy,
    orderOf_pow_orderOf_div (orderOf_pos _).ne' hk3⟩, ?_⟩
  have hNA : CFSG.Open.pCore 2 ↥K ≤ (T ⊓ K).subgroupOf K := by
    intro x hx
    exact hOle (Subgroup.mem_map_of_mem K.subtype hx)
  haveI : (CFSG.Open.pCore 2 ↥K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hcardA : Nat.card ↥((T ⊓ K).subgroupOf K) = Nat.card ↥(T ⊓ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hcardN : Nat.card ↥(pCoreOf 2 K) = Nat.card ↥(CFSG.Open.pCore 2 ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  rw [← hcardA, card_eq_mul_card_map _ hNA, himg, hcardN, mul_comm]

theorem le_normalizer_commutator {G : Type} [Group G] {P Q L : Subgroup G}
    (hQ : P ≤ Subgroup.normalizer (Q : Set G)) (hL : P ≤ Subgroup.normalizer (L : Set G)) :
    P ≤ Subgroup.normalizer ((⁅Q, L⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ P, ∀ x ∈ ⁅Q, L⁆, g * x * g⁻¹ ∈ ⁅Q, L⁆ := by
    intro g hg
    have hle : ⁅Q, L⁆ ≤ (⁅Q, L⁆).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro q hq l hl
      rw [Subgroup.mem_comap]
      have h1 : g * q * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hQ hg) q).mp hq
      have h2 : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hL hg) l).mp hl
      have e : (MulAut.conj g).toMonoidHom ⁅q, l⁆ = ⁅g * q * g⁻¹, g * l * g⁻¹⁆ :=
        map_commutatorElement (MulAut.conj g).toMonoidHom q l
      rw [e]
      exact Subgroup.commutator_mem_commutator h1 h2
    intro x hx
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have h := key g⁻¹ (P.inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h

theorem le_of_sup_dsFrattini_eq {G : Type} [Group G] [Finite G] {Q M : Subgroup G}
    (hM : M ≤ Q) (h : M ⊔ dsFrattini Q = Q) : Q ≤ M := by
  have hA : M.subgroupOf Q ⊔ frattini ↥Q = ⊤ := by
    apply Subgroup.map_injective (f := Q.subtype) Q.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hM,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact h
  have hAtop : M.subgroupOf Q = ⊤ := frattini_nongenerating hA
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥Q) ∈ M.subgroupOf Q := by
    rw [hAtop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

end DSBA5

theorem leafDSBA5Vertex [DSLeaf LeafSylowS] [DSLeaf LeafM2] [DSLeaf LeafFrattiniChief] [DSLeaf LeafRankBounds] : LeafDSBA5Vertex := by
  intro G _ _ L1 L2 S h
  have hA : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1
  have hsyl : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := (sylow_s h.hyp).2.1
  have hQS : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := (sylow_s h.hyp).2.2
  obtain ⟨⟨d, hdB, hd3⟩, hcardS1⟩ := DSBA5.three_and_card h.hyp.hyp.h1.sylow hA.quot
  have hdN : d ∈ Subgroup.normalizer (S : Set G) :=
    DSBHyp.bnorm h ((le_sup_left.trans le_sup_left : borelOf L1 S ≤ bigB L1 L2 S) hdB)
  have hdL : d ∈ L1 := (Subgroup.mem_inf.mp hdB).1
  have hdP : d ∈ L1 ⊔ bigB L1 L2 S := Subgroup.mem_sup_left hdL
  have hrel : (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)).relIndex S = 4 :=
    (m2 hA hsyl hQS).2.2 d ⟨hdP, hdN⟩ hd3
  have hchief := frattini_chief hA
  set P := L1 ⊔ bigB L1 L2 S with hPdef
  set Q := pCoreOf 2 P with hQdef
  have hQN : P ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hLN : P ≤ Subgroup.normalizer (L1 : Set G) := hA.norm
  have hQL1 : Q ≤ Subgroup.normalizer (L1 : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans hLN
  have hL1Q : L1 ≤ Subgroup.normalizer (Q : Set G) := hA.le.trans hQN
  have hcomm : ⁅Q, L1⁆ ≤ Q ⊓ L1 := F7.commutator_le_inf_of_normalizes hQL1 hL1Q
  have hΦQ : dsFrattini Q ≤ Q := Subgroup.map_subtype_le (frattini ↥Q)
  have hX : ⁅Q, L1⁆ ⊔ dsFrattini Q ≤ Q := sup_le (hcomm.trans inf_le_left) hΦQ
  have hPX : P ≤ Subgroup.normalizer ((⁅Q, L1⁆ ⊔ dsFrattini Q : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (DSBA5.le_normalizer_commutator hQN hLN) hchief.norm_K
  have hQL : Q ≤ L1 := by
    rcases hchief.irred _ le_sup_right hX hPX with hK | hE
    · exfalso
      obtain ⟨l, hl, e, he, hne⟩ := hchief.nontriv
      apply hne
      have hmem : ⁅l, e⁆ ∈ ⁅Q, L1⁆ := by
        have := Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator he hl)
        rwa [commutatorElement_inv] at this
      have hmem' : ⁅l, e⁆ ∈ ⁅Q, L1⁆ ⊔ dsFrattini Q := Subgroup.mem_sup_left hmem
      rw [hK] at hmem'
      exact hmem'
    · have hQc : Q ≤ ⁅Q, L1⁆ := DSBA5.le_of_sup_dsFrattini_eq (hcomm.trans inf_le_left) hE
      exact hQc.trans (hcomm.trans inf_le_right)
  have hpc : pCoreOf 2 L1 = Q := by
    have h1 := F1.inf_pCoreOf_parabolic_eq h.hyp
    rw [← h1]
    exact inf_eq_left.mpr hQL
  have hcardS : Nat.card ↥S = Nat.card ↥Q * 4 := by
    have h1 := Subgroup.card_mul_index (Q.subgroupOf S)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv] at h1
    have hidx : (Q.subgroupOf S).index = 4 := hrel
    rw [← h1, hidx]
  have hSS1 : S ⊓ L1 = S := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    rw [hcardS1, hpc, hcardS, mul_comm]
  refine ⟨?_, hrel, hQL⟩
  rw [hSS1]
  exact (sup_eq_left.mpr hQS).symm

end CFSG.GH74.QTGen4.DSGen4
