module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBA5Vertex
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Surv10
public import CFSG.Quasithin.Vol2.Ch6Sec1GreenBook
public import CFSG.GH74.QTGen4.DSGen4.OpenLeavesAmal

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSUA5

variable {G : Type} [Group G]

theorem mem_sup_decomp {L S : Subgroup G} (hS : S ≤ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : x ∈ L ⊔ S) : ∃ l ∈ L, ∃ s ∈ S, x = l * s := by
  let T : Subgroup G :=
    { carrier := {x | ∃ l ∈ L, ∃ s ∈ S, x = l * s}
      one_mem' := ⟨1, L.one_mem, 1, S.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨l, hl, s, hs, rfl⟩ ⟨l', hl', s', hs', rfl⟩
        have h1 : s * l' * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hS hs) l').mp hl'
        exact ⟨l * (s * l' * s⁻¹), L.mul_mem hl h1, s * s', S.mul_mem hs hs', by group⟩
      inv_mem' := by
        rintro _ ⟨l, hl, s, hs, rfl⟩
        have h1 : s⁻¹ * l⁻¹ * s ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (hS (S.inv_mem hs)) l⁻¹).mp (L.inv_mem hl)
          simpa using this
        exact ⟨s⁻¹ * l⁻¹ * s, h1, s⁻¹, S.inv_mem hs, by group⟩ }
  have hLT : L ≤ T := fun l hl => ⟨l, hl, 1, S.one_mem, by simp⟩
  have hST : S ≤ T := fun s hs => ⟨1, L.one_mem, s, hs, by simp⟩
  have hT : L ⊔ S ≤ T := sup_le hLT hST
  exact hT hx

theorem sq_mem_of_relIndex_two {S L : Subgroup G} (h2 : (S ⊓ L).relIndex S = 2) {s : G}
    (hs : s ∈ S) : s ^ 2 ∈ L := by
  haveI : ((S ⊓ L).subgroupOf S).Normal := Subgroup.normal_of_index_eq_two h2
  have h := Subgroup.pow_index_mem ((S ⊓ L).subgroupOf S) ⟨s, hs⟩
  rw [show ((S ⊓ L).subgroupOf S).index = 2 from h2] at h
  have h3 := Subgroup.mem_subgroupOf.mp h
  simp only [Subgroup.coe_pow] at h3
  exact (Subgroup.mem_inf.mp h3).2

theorem eq_of_comm_alt5 {L : Subgroup G} {N : Subgroup ↥L}
    (π : ↥L →* ↥(alternatingGroup (Fin 5))) (hπs : Function.Surjective π)
    (hπk : π.ker = N) {y : ↥L} (hy : ∀ l : ↥L, ⁅y, l⁆ ∈ N) : y ∈ N := by
  have hc : π y ∈ Subgroup.center ↥(alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := hπs g
    have h1 : π ⁅y, l⁆ = 1 := MonoidHom.mem_ker.mp (by rw [hπk]; exact hy l)
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
  rw [← hπk]
  exact MonoidHom.mem_ker.mpr hc

theorem perm5_eq_one_of_centralizes :
    ∀ σ : Equiv.Perm (Fin 5), (∀ g : alternatingGroup (Fin 5),
      σ * (g : Equiv.Perm (Fin 5)) = (g : Equiv.Perm (Fin 5)) * σ) → σ = 1 := by
  decide +kernel

theorem conj_mem_alt5 (σ : Equiv.Perm (Fin 5)) (g : alternatingGroup (Fin 5)) :
    σ * (g : Equiv.Perm (Fin 5)) * σ⁻¹ ∈ alternatingGroup (Fin 5) :=
  Subgroup.Normal.conj_mem inferInstance (g : Equiv.Perm (Fin 5)) g.2 σ

def conjA5Aut (σ : Equiv.Perm (Fin 5)) : MulAut ↥(alternatingGroup (Fin 5)) where
  toFun g := ⟨σ * (g : Equiv.Perm (Fin 5)) * σ⁻¹, conj_mem_alt5 σ g⟩
  invFun g := ⟨σ⁻¹ * (g : Equiv.Perm (Fin 5)) * σ⁻¹⁻¹, conj_mem_alt5 σ⁻¹ g⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  map_mul' g h := Subtype.ext (by simp [mul_assoc])

def conjA5 : Equiv.Perm (Fin 5) →* MulAut ↥(alternatingGroup (Fin 5)) where
  toFun := conjA5Aut
  map_one' := MulEquiv.ext fun g => Subtype.ext (by simp [conjA5Aut])
  map_mul' σ τ := MulEquiv.ext fun g => Subtype.ext (by simp [conjA5Aut, mul_assoc])

theorem conjA5_bijective : Function.Bijective conjA5 := by
  refine ⟨fun σ τ hστ => ?_, fun f => ?_⟩
  · have hc : ∀ g : alternatingGroup (Fin 5),
        (τ⁻¹ * σ) * (g : Equiv.Perm (Fin 5)) = (g : Equiv.Perm (Fin 5)) * (τ⁻¹ * σ) := by
      intro g
      have h : σ * (g : Equiv.Perm (Fin 5)) * σ⁻¹ = τ * (g : Equiv.Perm (Fin 5)) * τ⁻¹ :=
        congrArg Subtype.val (DFunLike.congr_fun hστ g)
      have e1 : (τ⁻¹ * σ) * (g : Equiv.Perm (Fin 5)) * (τ⁻¹ * σ)⁻¹ = g := by
        calc (τ⁻¹ * σ) * (g : Equiv.Perm (Fin 5)) * (τ⁻¹ * σ)⁻¹
            = τ⁻¹ * (σ * (g : Equiv.Perm (Fin 5)) * σ⁻¹) * τ := by group
          _ = g := by rw [h]; group
      calc (τ⁻¹ * σ) * (g : Equiv.Perm (Fin 5))
          = (τ⁻¹ * σ) * (g : Equiv.Perm (Fin 5)) * (τ⁻¹ * σ)⁻¹ * (τ⁻¹ * σ) := by group
        _ = (g : Equiv.Perm (Fin 5)) * (τ⁻¹ * σ) := by rw [e1]
    have h1 := perm5_eq_one_of_centralizes _ hc
    calc σ = τ * (τ⁻¹ * σ) := by group
      _ = τ := by rw [h1, mul_one]
  · obtain ⟨σ, hσ⟩ :=
      CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le (Or.inl rfl) f
    exact ⟨σ, MulEquiv.ext fun g => Subtype.ext (hσ g).symm⟩

theorem mem_pCore_iff {H : Subgroup G} (z : ↥H) :
    z ∈ CFSG.Open.pCore 2 ↥H ↔ (z : G) ∈ pCoreOf 2 H := by
  constructor
  · intro hz
    exact Subgroup.mem_map_of_mem H.subtype hz
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
    have : w = z := Subtype.ext (by simpa using hwz)
    rw [← this]
    exact hw

end DSUA5

theorem leafUAmalExtA5 [DSLeaf LeafDSBReduce] [DSLeaf LeafDSBA5Vertex] [DSLeaf LeafDSBUQ1] [DSLeaf LeafDSBZSU] [DSLeaf LeafZiStructure] [DSLeaf LeafFaithfulA5] [DSLeaf LeafM2] [DSLeaf LeafFrattiniChief] [DSLeaf LeafRankBounds] [DSLeaf LeafSylowS] : LeafUAmalExtA5 := by
  intro G _ _ L1 L2 S h hns hs3 hb6 hS
  have hA : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 h hns
  have hsyl : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := (sylow_s h).2.1
  have hQS : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := (sylow_s h).2.2
  have hm := m2 hA hsyl hQS
  obtain ⟨e⟩ := S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hA.quot
  have hbS : borelOf L2 S = S ⊓ L2 := borelOf_eq_of_s3 h.hyp.h2.sylow hs3
  have hPS : L1 ⊔ bigB L1 L2 S = L1 ⊔ S := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      unfold bigB
      refine sup_le (sup_le ?_ ?_) le_sup_right
      · exact (inf_le_left : borelOf L1 S ≤ L1).trans le_sup_left
      · rw [hbS]
        exact inf_le_left.trans le_sup_right
    · refine sup_le le_sup_left ?_
      exact (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  set P : Subgroup G := L1 ⊔ bigB L1 L2 S with hPdef
  have hLP : L1 ≤ P := le_sup_left
  have hSP : S ≤ P := hSB.trans le_sup_right
  have hLN : P ≤ Subgroup.normalizer (L1 : Set G) := hA.norm
  have hSN : S ≤ Subgroup.normalizer (L1 : Set G) := hSP.trans hLN
  have hQN : P ≤ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hfrat : pCoreOf 2 P ≤ L1 := by
    have hchief := frattini_chief hA
    have hcomm : ⁅pCoreOf 2 P, L1⁆ ≤ pCoreOf 2 P ⊓ L1 :=
      F7.commutator_le_inf_of_normalizes ((CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans hLN)
        (hA.le.trans hQN)
    have hΦQ : dsFrattini (pCoreOf 2 P) ≤ pCoreOf 2 P := Subgroup.map_subtype_le (frattini ↥(pCoreOf 2 P))
    have hX : ⁅pCoreOf 2 P, L1⁆ ⊔ dsFrattini (pCoreOf 2 P) ≤ pCoreOf 2 P :=
      sup_le (hcomm.trans inf_le_left) hΦQ
    have hPX : P ≤ Subgroup.normalizer
        ((⁅pCoreOf 2 P, L1⁆ ⊔ dsFrattini (pCoreOf 2 P) : Subgroup G) : Set G) :=
      F1.le_normalizer_sup (DSBA5.le_normalizer_commutator hQN hLN) hchief.norm_K
    rcases hchief.irred _ le_sup_right hX hPX with hK | hE
    · exfalso
      obtain ⟨l, hl, x, hx, hne⟩ := hchief.nontriv
      apply hne
      have hmem : ⁅l, x⁆ ∈ ⁅pCoreOf 2 P, L1⁆ := by
        have := Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hx hl)
        rwa [commutatorElement_inv] at this
      have hmem' : ⁅l, x⁆ ∈ ⁅pCoreOf 2 P, L1⁆ ⊔ dsFrattini (pCoreOf 2 P) :=
        Subgroup.mem_sup_left hmem
      rw [hK] at hmem'
      exact hmem'
    · have hQc : pCoreOf 2 P ≤ ⁅pCoreOf 2 P, L1⁆ :=
        DSBA5.le_of_sup_dsFrattini_eq (hcomm.trans inf_le_left) hE
      exact hQc.trans (hcomm.trans inf_le_right)
  have hpc : pCoreOf 2 L1 = pCoreOf 2 P :=
    (F1.inf_pCoreOf_parabolic_eq h).symm.trans (inf_eq_left.mpr hfrat)
  have hcardS1 : Nat.card ↥(S ⊓ L1) = 4 * Nat.card ↥(pCoreOf 2 P) := by
    rw [← hpc]
    exact (DSBA5.three_and_card h.hyp.h1.sylow hA.quot).2
  have hQle : pCoreOf 2 P ≤ S ⊓ L1 := le_inf hQS hfrat
  have h4 : (pCoreOf 2 P).relIndex (S ⊓ L1) = 4 := by
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 P) (S ⊓ L1)
    rw [inf_eq_left.mpr hQle, hcardS1] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have htower : (pCoreOf 2 P).relIndex S =
      (pCoreOf 2 P).relIndex (S ⊓ L1) * (S ⊓ L1).relIndex S :=
    (Subgroup.relIndex_mul_relIndex _ _ _ hQle inf_le_left).symm
  have hr2 : (S ⊓ L1).relIndex S = 2 := by
    have hdvd : (S ⊓ L1).relIndex S ∣ 2 := by
      have h8 := hm.1
      rw [htower, h4] at h8
      have h8' : 4 * (S ⊓ L1).relIndex S ∣ 4 * 2 := by
        norm_num
        exact h8
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h8'
    have hne : (S ⊓ L1).relIndex S ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      exact hS (h1.trans inf_le_right)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hL1P : L1.relIndex P = 2 := by
    haveI hN : (L1.subgroupOf P).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hLP]
      intro k x hk hx
      exact (Subgroup.mem_normalizer_iff.mp (hLN hx) k).mp hk
    have hsup : S.subgroupOf P ⊔ L1.subgroupOf P = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      have hx' : x ∈ L1 ⊔ S := by
        rw [← hPS]
        exact hx
      obtain ⟨l, hl, s, hs, rfl⟩ := DSUA5.mem_sup_decomp hSN hx'
      have hlP : l ∈ P := hLP hl
      have hsP : s ∈ P := hSP hs
      have key : (⟨l, hlP⟩ * ⟨s, hsP⟩ : ↥P) = ⟨l * s, hx⟩ := Subtype.ext rfl
      rw [← key]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_right (show (⟨l, hlP⟩ : ↥P) ∈ L1.subgroupOf P from hl))
        (Subgroup.mem_sup_left (show (⟨s, hsP⟩ : ↥P) ∈ S.subgroupOf P from hs))
    have hrel := Subgroup.relIndex_sup_right (S.subgroupOf P) (L1.subgroupOf P)
    rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hSP] at hrel
    have h3 : L1.relIndex S = 2 := by
      rw [← Subgroup.inf_relIndex_right, inf_comm]
      exact hr2
    exact hrel.trans h3
  have hcard5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hE_L1 : (pCoreOf 2 L1).relIndex L1 = 60 := by
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 L1) L1
    rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L1)] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L1)
    have h3 : Nat.card ↥(pCoreOf 2 L1) = Nat.card ↥(CFSG.Open.pCore 2 ↥L1) :=
      Subgroup.card_map_of_injective L1.subtype_injective
    have h4 : Nat.card (↥L1 ⧸ CFSG.Open.pCore 2 ↥L1) = 60 := by
      rw [← hcard5]
      exact Nat.card_congr e.toEquiv
    rw [h2, h4] at h1
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hE_P : (pCoreOf 2 L1).relIndex P = 120 := by
    rw [← Subgroup.relIndex_mul_relIndex (pCoreOf 2 L1) L1 P
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L1) hLP, hE_L1, hL1P]
  set K : Subgroup G := dsCentMod P L1 (pCoreOf 2 P) with hKdef
  have hKmem : ∀ x : G, x ∈ K ↔
      x ∈ P ∧ x ∈ Subgroup.normalizer (pCoreOf 2 P : Set G) ∧ ∀ l ∈ L1, ⁅x, l⁆ ∈ pCoreOf 2 P :=
    fun x => Iff.rfl
  have hQK : pCoreOf 2 P ≤ K := by
    intro q hq
    rw [hKmem]
    refine ⟨(CFSG.LieType.BorelTits.pCoreOf_le 2 P) hq, Subgroup.le_normalizer hq, fun l hl => ?_⟩
    have hlP : l ∈ P := hLP hl
    have h1 : l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 P :=
      (Subgroup.mem_normalizer_iff.mp (hQN hlP) q⁻¹).mp ((pCoreOf 2 P).inv_mem hq)
    rw [commutatorElement_def]
    have e1 : q * l * q⁻¹ * l⁻¹ = q * (l * q⁻¹ * l⁻¹) := by group
    rw [e1]
    exact (pCoreOf 2 P).mul_mem hq h1
  have hπs : Function.Surjective
      (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L1)) :
        ↥L1 →* ↥(alternatingGroup (Fin 5))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L1)) :
        ↥L1 →* ↥(alternatingGroup (Fin 5))).ker = CFSG.Open.pCore 2 ↥L1 := by
    ext x
    simp [MulEquiv.map_eq_one_iff]
  have hcl : ∀ y ∈ K, y ∈ L1 → y ∈ pCoreOf 2 P := by
    intro y hyK hyL
    have hy : ∀ l : ↥L1, ⁅(⟨y, hyL⟩ : ↥L1), l⁆ ∈ CFSG.Open.pCore 2 ↥L1 := by
      intro l
      rw [DSUA5.mem_pCore_iff]
      have hcoe : ((⁅(⟨y, hyL⟩ : ↥L1), l⁆ : ↥L1) : G) = ⁅y, (l : G)⁆ := by
        simp [commutatorElement_def]
      rw [hcoe, hpc]
      exact ((hKmem y).mp hyK).2.2 l l.2
    have hmem := DSUA5.eq_of_comm_alt5 _ hπs hπk hy
    have hmem' := (DSUA5.mem_pCore_iff (⟨y, hyL⟩ : ↥L1)).mp hmem
    rw [hpc] at hmem'
    exact hmem'
  have hsq : ∀ x ∈ P, x ^ 2 ∈ L1 := by
    intro x hx
    have hx' : x ∈ L1 ⊔ S := by
      rw [← hPS]
      exact hx
    obtain ⟨l, hl, s, hs, rfl⟩ := DSUA5.mem_sup_decomp hSN hx'
    have hc : s * l * s⁻¹ ∈ L1 := (Subgroup.mem_normalizer_iff.mp (hSN hs) l).mp hl
    have e2 : (l * s) ^ 2 = l * (s * l * s⁻¹) * s ^ 2 := by
      simp only [sq]
      group
    rw [e2]
    exact L1.mul_mem (L1.mul_mem hl hc) (DSUA5.sq_mem_of_relIndex_two hr2 hs)
  have hKQ : K ≤ pCoreOf 2 P := by
    intro x hx
    have hxP : x ∈ P := ((hKmem x).mp hx).1
    have hx2 : x ^ 2 ∈ pCoreOf 2 P := hcl (x ^ 2) (K.pow_mem hx 2) (hsq x hxP)
    haveI hQn : ((pCoreOf 2 P).subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hQK]
      intro a k ha hk
      exact (Subgroup.mem_normalizer_iff.mp (((hKmem k).mp hk).2.1) a).mp ha
    have hsq' : (⟨x, hx⟩ : ↥K) ^ 2 ∈ (pCoreOf 2 P).subgroupOf K := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact hx2
    have hq2 : (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : ↥K ⧸ (pCoreOf 2 P).subgroupOf K) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hsq'
    have hd1 := orderOf_dvd_of_pow_eq_one hq2
    have hd2 : orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : ↥K ⧸ (pCoreOf 2 P).subgroupOf K) ∣
        (pCoreOf 2 P).relIndex K := orderOf_dvd_natCard _
    have hodd := hm.2.1
    have hord : orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : ↥K ⧸ (pCoreOf 2 P).subgroupOf K) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd1 with h1 | h1
      · exact h1
      · exfalso
        rw [h1] at hd2
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd2)
    have hq1 := orderOf_eq_one_iff.mp hord
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq1)
  have hKeq : K = pCoreOf 2 P := le_antisymm hKQ hQK
  let ρ : ↥P →* MulAut ↥L1 := (Subgroup.normalizerMonoidHom L1).comp (Subgroup.inclusion hLN)
  have hρ : ∀ (p : ↥P) (x : ↥L1), ((ρ p x : ↥L1) : G) = (p : G) * (x : G) * (p : G)⁻¹ :=
    fun p x => Subgroup.normalizerMonoidHom_apply_apply_coe L1 (Subgroup.inclusion hLN p) x
  have hρinv : ∀ (p : ↥P) (z : ↥L1), ρ p (ρ p⁻¹ z) = z := by
    intro p z
    have h1 : ρ p * ρ p⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have := congrArg (fun f : MulAut ↥L1 => f z) h1
    simpa using this
  have hfwd : ∀ (p : ↥P) (w : ↥L1), w ∈ CFSG.Open.pCore 2 ↥L1 →
      ρ p w ∈ CFSG.Open.pCore 2 ↥L1 := by
    intro p w hw
    rw [DSUA5.mem_pCore_iff, hpc] at hw
    rw [DSUA5.mem_pCore_iff, hpc, hρ]
    exact (Subgroup.mem_normalizer_iff.mp (hQN p.2) (w : G)).mp hw
  have hmapN : ∀ p : ↥P, Subgroup.map (ρ p).toMonoidHom (CFSG.Open.pCore 2 ↥L1) =
      CFSG.Open.pCore 2 ↥L1 := by
    intro p
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hfwd p w hw
    · intro z hz
      exact ⟨ρ p⁻¹ z, hfwd p⁻¹ z hz, hρinv p z⟩
  haveI hpn : (CFSG.Open.pCore 2 ↥L1).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  haveI hpnP : (CFSG.Open.pCore 2 ↥P).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  let Ψ0 : ↥P → (oTwoQuot ↥L1 ≃* oTwoQuot ↥L1) := fun p =>
    QuotientGroup.congr (CFSG.Open.pCore 2 ↥L1) (CFSG.Open.pCore 2 ↥L1) (ρ p) (hmapN p)
  have hcm : ∀ (p : ↥P) (x : ↥L1), Ψ0 p (QuotientGroup.mk x) = QuotientGroup.mk (ρ p x) :=
    fun p x => QuotientGroup.congr_mk _ _ (ρ p) (hmapN p) x
  have hΨ0one : Ψ0 1 = (1 : MulAut (oTwoQuot ↥L1)) := by
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    simp [hcm]
  have hΨ0mul : ∀ p p' : ↥P, Ψ0 (p * p') = Ψ0 p * Ψ0 p' := by
    intro p p'
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    simp only [MulAut.mul_apply, hcm, map_mul]
  let Ψ : ↥P →* MulAut (oTwoQuot ↥L1) :=
    { toFun := fun p => Ψ0 p
      map_one' := hΨ0one
      map_mul' := hΨ0mul }
  have hΨker : ∀ p : ↥P, Ψ p = 1 ↔ (p : G) ∈ pCoreOf 2 P := by
    intro p
    constructor
    · intro hp
      have key : ∀ l : ↥L1, (p : G) * (l : G)⁻¹ * (p : G)⁻¹ * (l : G) ∈ pCoreOf 2 P := by
        intro l
        have hfix : Ψ0 p (QuotientGroup.mk l) = QuotientGroup.mk l := by
          have := congrArg (fun f : MulAut (oTwoQuot ↥L1) => f (QuotientGroup.mk l)) hp
          exact this
        have h1 : (QuotientGroup.mk (ρ p l) : ↥L1 ⧸ CFSG.Open.pCore 2 ↥L1) = QuotientGroup.mk l := by
          rw [← hcm p l]
          exact hfix
        have h2 : (ρ p l)⁻¹ * l ∈ CFSG.Open.pCore 2 ↥L1 := QuotientGroup.eq.mp h1
        have h3 := (DSUA5.mem_pCore_iff _).mp h2
        rw [hpc] at h3
        have h4 : (((ρ p l)⁻¹ * l : ↥L1) : G) = (p : G) * (l : G)⁻¹ * (p : G)⁻¹ * (l : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρ]
          group
        rw [h4] at h3
        exact h3
      apply hKQ
      rw [hKmem]
      refine ⟨p.2, hQN p.2, fun m hm => ?_⟩
      have hk := key ⟨m⁻¹, L1.inv_mem hm⟩
      rw [commutatorElement_def]
      simpa using hk
    · intro hp
      apply MulEquiv.ext
      intro q
      refine QuotientGroup.induction_on q fun x => ?_
      change Ψ0 p (QuotientGroup.mk x) = QuotientGroup.mk x
      rw [hcm]
      apply QuotientGroup.eq.mpr
      have h4 : (((ρ p x)⁻¹ * x : ↥L1) : G) = (p : G) * (x : G)⁻¹ * (p : G)⁻¹ * (x : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρ]
        group
      rw [DSUA5.mem_pCore_iff, hpc, h4]
      have hk : (p : G) * (x : G)⁻¹ * (p : G)⁻¹ * (x : G) ∈ pCoreOf 2 P := by
        have := ((hKmem (p : G)).mp (hQK hp)).2.2 (x : G)⁻¹ (L1.inv_mem x.2)
        rwa [commutatorElement_def, inv_inv] at this
      exact hk
  let Θ : MulAut (oTwoQuot ↥L1) ≃* Equiv.Perm (Fin 5) :=
    (MulAut.congr e).trans (MulEquiv.ofBijective DSUA5.conjA5 DSUA5.conjA5_bijective).symm
  let ψ : ↥P →* Equiv.Perm (Fin 5) := Θ.toMonoidHom.comp Ψ
  have hψ1 : ∀ p : ↥P, ψ p = 1 ↔ Ψ p = 1 := fun p => Θ.map_eq_one_iff
  have hψker : ψ.ker = CFSG.Open.pCore 2 ↥P := by
    ext p
    rw [MonoidHom.mem_ker, hψ1, hΨker, DSUA5.mem_pCore_iff]
  have hsub : (pCoreOf 2 P).subgroupOf P = CFSG.Open.pCore 2 ↥P := by
    ext z
    rw [Subgroup.mem_subgroupOf, DSUA5.mem_pCore_iff]
  have hidx : Nat.card (↥P ⧸ CFSG.Open.pCore 2 ↥P) = 120 := by
    rw [← hsub]
    show (pCoreOf 2 P).relIndex P = 120
    rw [← hpc]
    exact hE_P
  have hcardψ : Nat.card ↥ψ.range = 120 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hψker, hidx]
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [hcardψ, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  exact ⟨hpc.symm, hr2, ⟨(QuotientGroup.quotientMulEquivOfEq hψker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)⟩⟩

end CFSG.GH74.QTGen4.DSGen4
