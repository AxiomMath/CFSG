module

public import CFSG.GH74.GLS.C3.Layer1.P34Proj
public import CFSG.Walter.AStar.Subnormal
public import CFSG.GH74.GLS.C3.Layer1.U1a
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back.Setup91

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.U1a
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_pPrimeCoreOf_iff {K : Subgroup G} {g : G} :
    g ∈ pPrimeCoreOf 2 K ↔ ∃ h : g ∈ K, (⟨g, h⟩ : ↥K) ∈ pPrimeCore 2 ↥K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem le_pPrimeCoreOf_of_normalized [Finite G] {C W : Subgroup G} (hWC : W ≤ C)
    (hnorm : ∀ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ W) (hodd : Odd (Nat.card ↥W)) :
    W ≤ pPrimeCoreOf 2 C := by
  have hN : (W.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  have hcop : Nat.Coprime 2 (Nat.card ↥(W.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : W.subgroupOf C ≤ pPrimeCore 2 ↥C :=
    CFSG.GroupTheory.le_pPrimeCore_of_normal hN hcop
  rw [← Subgroup.map_subgroupOf_eq_of_le hWC]
  exact Subgroup.map_mono hle

theorem mem_normalizer_pPrimeCoreOf_self {M : Subgroup G} {m : G} (hm : m ∈ M) :
    m ∈ normalizer (pPrimeCoreOf 2 M : Set G) :=
  mem_normalizer_pPrimeCoreOf (M := M) (L := M)
    (fun _ hm _ hl => M.mul_mem (M.mul_mem hm hl) (M.inv_mem hm)) hm

theorem factorization_two_of_odd {n : ℕ} (h : Odd n) : n.factorization 2 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd fun hd => (Nat.not_even_iff_odd.2 h) (even_iff_two_dvd.2 hd)

theorem factorization_two_card_sup [Finite G] {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) (hodd : Odd (Nat.card ↥(A ⊓ B))) :
    (Nat.card ↥(A ⊔ B)).factorization 2 =
      (Nat.card ↥A).factorization 2 + (Nat.card ↥B).factorization 2 := by
  have h := CFSG.GH74.GLS.C3.Layer1.P34.card_mul_inf A B
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hB] at h
  have h' : Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := h
  have hne : ∀ H : Subgroup G, Nat.card ↥H ≠ 0 := fun H => Nat.card_pos.ne'
  have h2 := congrArg (fun n => n.factorization 2) h'
  simp only [Nat.factorization_mul (hne _) (hne _), Finsupp.add_apply] at h2
  have h3 := factorization_two_of_odd hodd
  omega

theorem inf_pPrimeCoreOf_eq_bot [Finite G] {T : Subgroup G} (L : Subgroup G) (hT : IsPGroup 2 T) :
    T ⊓ pPrimeCoreOf 2 L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgT, hgO⟩ := hg
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT) ⟨g, hgT⟩
  have h1 : orderOf g = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have h2 : Odd (orderOf g) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd L) (Subgroup.orderOf_dvd_natCard _ hgO)
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.2 h2) (h1 ▸ Nat.even_pow.2 ⟨even_two, hk0⟩)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at h1
  exact h1

theorem inf_CMK_le {M L : Subgroup G} (hs : IsSimpleGroup (kBar L))
    (hn : ∃ a b : kBar L, a * b ≠ b * a) : L ⊓ CMK M L ≤ pPrimeCoreOf 2 L := by
  intro g hg
  obtain ⟨hgL, hgC⟩ := hg
  obtain ⟨_, _, _, hcomm⟩ := mem_CMK_iff.1 hgC
  have hcentral : (QuotientGroup.mk ⟨g, hgL⟩ : kBar L) ∈ Subgroup.center (kBar L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with | H l => ?_
    obtain ⟨_, hc⟩ := mem_pPrimeCoreOf_iff.1 (hcomm l l.2)
    have h2 : (⁅l, ⟨g, hgL⟩⁆ : ↥L) ∈ pPrimeCore 2 ↥L := hc
    have h4 : ⁅(QuotientGroup.mk' (pPrimeCore 2 ↥L)) l,
        (QuotientGroup.mk' (pPrimeCore 2 ↥L)) ⟨g, hgL⟩⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h4
  have hbot : Subgroup.center (kBar L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (kBar L)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hn
      apply hab
      exact Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a
  rw [hbot, Subgroup.mem_bot] at hcentral
  exact mem_pPrimeCoreOf_iff.2 ⟨hgL, (QuotientGroup.eq_one_iff _).1 hcentral⟩

section Hyp

variable {x : G} {K L M T Q : Subgroup G}

theorem pPrimeCoreOf_L_le [Finite G] (hh : Hyp9A x K L M T Q) :
    pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 M :=
  le_pPrimeCoreOf_of_normalized ((TwoThin.pPrimeCoreOf_le L).trans hh.L_normal.1)
    (fun _ hm _ hw => pPrimeCoreOf_norm hh.L_normal.2 hm hw) (TwoThin.card_pPrimeCoreOf_odd L)

theorem inf_pPrimeCoreOf_M_le [Finite G] (hh : Hyp9A x K L M T Q) :
    L ⊓ pPrimeCoreOf 2 M ≤ pPrimeCoreOf 2 L := by
  refine le_pPrimeCoreOf_of_normalized inf_le_left (fun c hc w hw => ?_) ?_
  · exact ⟨L.mul_mem (L.mul_mem hc hw.1) (L.inv_mem hc),
      TwoThin.pPrimeCoreOf_normalized M (hh.L_normal.1 hc) hw.2⟩
  · exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd M) (Subgroup.card_dvd_of_le inf_le_right)

theorem L_inf_pPrimeCoreOf_M [Finite G] (hh : Hyp9A x K L M T Q) :
    L ⊓ pPrimeCoreOf 2 M = pPrimeCoreOf 2 L :=
  le_antisymm (inf_pPrimeCoreOf_M_le hh)
    (le_inf (TwoThin.pPrimeCoreOf_le L) (pPrimeCoreOf_L_le hh))

theorem exists_mul_of_mem_L [Finite G] (hh : Hyp9A x K L M T Q) {l : G} (hl : l ∈ L) :
    ∃ o ∈ pPrimeCoreOf 2 L, ∃ k ∈ K, o * k = l := by
  have hKM : K ≤ M := hh.K_le_L.trans hh.L_normal.1
  have hOM : K ≤ normalizer (pPrimeCoreOf 2 M : Set G) := fun k hk =>
    mem_normalizer_pPrimeCoreOf_self (hKM hk)
  have hl' : l ∈ pPrimeCoreOf 2 M ⊔ K := by
    have : l ∈ K ⊔ pPrimeCoreOf 2 M := hh.bar_eq ▸ (le_sup_left : L ≤ L ⊔ pPrimeCoreOf 2 M) hl
    rwa [sup_comm] at this
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hOM] at hl'
  obtain ⟨o, ho, k, hk, rfl⟩ := hl'
  refine ⟨o, ?_, k, hk, rfl⟩
  have hoL : o ∈ L := by
    have : o * k * k⁻¹ ∈ L := L.mul_mem hl (L.inv_mem (hh.K_le_L hk))
    simpa using this
  rw [← L_inf_pPrimeCoreOf_M hh]
  exact ⟨hoL, ho⟩

@[expose] def toLBar (hKL : K ≤ L) : ↥K →* ↥L ⧸ pPrimeCore 2 ↥L :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥L)).comp (Subgroup.inclusion hKL)

theorem toLBar_surjective [Finite G] (hh : Hyp9A x K L M T Q) :
    Function.Surjective (toLBar hh.K_le_L) := by
  intro y
  induction y using QuotientGroup.induction_on with | H l => ?_
  obtain ⟨o, ho, k, hk, hok⟩ := exists_mul_of_mem_L hh l.2
  obtain ⟨hoL, ho'⟩ := mem_pPrimeCoreOf_iff.1 ho
  have hlk : l = ⟨o, hoL⟩ * Subgroup.inclusion hh.K_le_L ⟨k, hk⟩ := Subtype.ext hok.symm
  refine ⟨⟨k, hk⟩, ?_⟩
  show QuotientGroup.mk' (pPrimeCore 2 ↥L) (Subgroup.inclusion hh.K_le_L ⟨k, hk⟩) =
    QuotientGroup.mk l
  rw [hlk, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 ho', one_mul]
  rfl

theorem ker_toLBar [Finite G] (hh : Hyp9A x K L M T Q) :
    (toLBar hh.K_le_L).ker = pPrimeCore 2 ↥K := by
  apply le_antisymm
  · have hodd : Odd (Nat.card ↥(toLBar hh.K_le_L).ker) := by
      have himg : ((toLBar hh.K_le_L).ker).map K.subtype ≤ pPrimeCoreOf 2 L := by
        rintro _ ⟨k, hk, rfl⟩
        have hk' : toLBar hh.K_le_L k = 1 := MonoidHom.mem_ker.1 hk
        have := (QuotientGroup.eq_one_iff _).1 hk'
        exact mem_pPrimeCoreOf_iff.2 ⟨hh.K_le_L k.2, this⟩
      have := Subgroup.card_dvd_of_le himg
      rw [Subgroup.card_map_of_injective K.subtype_injective] at this
      exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd L) this
    exact CFSG.GroupTheory.le_pPrimeCore_of_normal inferInstance (Nat.coprime_two_left.2 hodd)
  · intro k hk
    have hN : ((pPrimeCore 2 ↥K).map (toLBar hh.K_le_L)).Normal :=
      Subgroup.Normal.map inferInstance _ (toLBar_surjective hh)
    have hcop : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 ↥K).map (toLBar hh.K_le_L))) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) CFSG.pPrimeCore_coprime_card
    have hle := CFSG.GroupTheory.le_pPrimeCore_of_normal hN hcop
    rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2] at hle
    have : toLBar hh.K_le_L k ∈ (⊥ : Subgroup (↥L ⧸ pPrimeCore 2 ↥L)) :=
      hle (Subgroup.mem_map_of_mem _ hk)
    exact MonoidHom.mem_ker.2 ((Subgroup.mem_bot).1 this)

theorem Q_le_T (hh : Hyp9A x K L M T Q) : Q ≤ T := by
  rw [hh.hQ]
  exact inf_le_left

theorem comm_inf_Q [Finite G] (hh : Hyp9A x K L M T Q) {p q : G}
    (hp : p ∈ T ⊓ K) (hq : q ∈ Q) : p * q = q * p := by
  obtain ⟨_, _, _, hcomm⟩ := mem_CMK_iff.1 (hh.sylowQ.le hq)
  have h1 : ⁅p, q⁆ ∈ pPrimeCoreOf 2 L := hcomm p (hh.K_le_L hp.2)
  have h2 : ⁅p, q⁆ ∈ T := by
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem hp.1 (Q_le_T hh hq)) (T.inv_mem hp.1))
      (T.inv_mem (Q_le_T hh hq))
  have h3 : ⁅p, q⁆ ∈ T ⊓ pPrimeCoreOf 2 L := ⟨h2, h1⟩
  rw [inf_pPrimeCoreOf_eq_bot L hh.sylowT.isPGroup, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h3

theorem inf_isSylowOf [Finite G] (hh : Hyp9A x K L M T Q) : IsSylowOf 2 (T ⊓ K) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := hh.twoTerminal.1.2.2
  obtain ⟨S, hS⟩ := hh.sylowT.exists_sylow_eq_subgroupOf
  obtain ⟨_, _, hsub, _, _⟩ := hK.2
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S hsub
  refine isSylowOf_of_card inf_le_right ?_
  have hle : T ⊓ K ≤ centralizer ({x} : Set G) := inf_le_right.trans hK.1
  have h1 : (T ⊓ K).subgroupOf (centralizer ({x} : Set G)) =
      (P : Subgroup ↥(K.subgroupOf (centralizer ({x} : Set G)))).map
        (K.subgroupOf (centralizer ({x} : Set G))).subtype := by
    rw [hP, hS]
    ext z
    simp [Subgroup.mem_subgroupOf]
  calc Nat.card ↥(T ⊓ K)
      = Nat.card ↥((T ⊓ K).subgroupOf (centralizer ({x} : Set G))) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm
    _ = Nat.card ↥(P : Subgroup ↥(K.subgroupOf (centralizer ({x} : Set G)))) := by
        rw [h1, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    _ = 2 ^ (Nat.card ↥(K.subgroupOf (centralizer ({x} : Set G)))).factorization 2 :=
        Sylow.card_eq_multiplicity P
    _ = 2 ^ (Nat.card ↥K).factorization 2 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv]

theorem factorization_K [Finite G] (hh : Hyp9A x K L M T Q) :
    (Nat.card ↥K).factorization 2 = (Nat.card ↥L).factorization 2 := by
  have hsup : pPrimeCoreOf 2 L ⊔ K = L := by
    refine le_antisymm (sup_le (TwoThin.pPrimeCoreOf_le L) hh.K_le_L) fun l hl => ?_
    obtain ⟨o, ho, k, hk, rfl⟩ := exists_mul_of_mem_L hh hl
    exact Subgroup.mul_mem_sup ho hk
  have hKM : K ≤ M := hh.K_le_L.trans hh.L_normal.1
  have hKN : K ≤ normalizer (pPrimeCoreOf 2 L : Set G) := fun k hk =>
    mem_normalizer_pPrimeCoreOf hh.L_normal.2 (hKM hk)
  have hodd : Odd (Nat.card ↥(pPrimeCoreOf 2 L ⊓ K)) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd L) (Subgroup.card_dvd_of_le inf_le_left)
  have h := factorization_two_card_sup hKN hodd
  rw [hsup, factorization_two_of_odd (TwoThin.card_pPrimeCoreOf_odd L), zero_add] at h
  exact h.symm

theorem factorization_D [Finite G] (hs : IsSimpleGroup (kBar L))
    (hn : ∃ a b : kBar L, a * b ≠ b * a) :
    (Nat.card ↥(L ⊔ CMK M L)).factorization 2 =
      (Nat.card ↥L).factorization 2 + (Nat.card ↥(CMK M L)).factorization 2 :=
  factorization_two_card_sup (fun _ hc => (mem_CMK_iff.1 hc).2.1)
    (Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd L)
      (Subgroup.card_dvd_of_le (inf_CMK_le hs hn)))

theorem inf_inf_Q [Finite G] (hh : Hyp9A x K L M T Q)
    (hs : IsSimpleGroup (kBar L)) (hn : ∃ a b : kBar L, a * b ≠ b * a) : (T ⊓ K) ⊓ Q = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨⟨hgT, hgK⟩, hgQ⟩ := hg
  have h1 : g ∈ pPrimeCoreOf 2 L := inf_CMK_le hs hn ⟨hh.K_le_L hgK, hh.sylowQ.le hgQ⟩
  have h2 : g ∈ T ⊓ pPrimeCoreOf 2 L := ⟨hgT, h1⟩
  rwa [inf_pPrimeCoreOf_eq_bot L hh.sylowT.isPGroup] at h2

theorem card_sup_Q [Finite G] (hh : Hyp9A x K L M T Q)
    (hs : IsSimpleGroup (kBar L)) (hn : ∃ a b : kBar L, a * b ≠ b * a) :
    Nat.card ↥((T ⊓ K) ⊔ Q) = Nat.card ↥(T ⊓ K) * Nat.card ↥Q := by
  have hnorm : Q ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    CFSG.GH74.GLS.C3.Layer1.P34.W_le_normalizer_of fun w hw q hq => by
      have h := comm_inf_Q hh hq hw
      have e : w * q * w⁻¹ = q := by
        calc w * q * w⁻¹ = q * w * w⁻¹ := by rw [h]
          _ = q := by group
      rw [e]
      exact hq
  have h := CFSG.GH74.GLS.C3.Layer1.P34.card_mul_inf (T ⊓ K) Q
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left (T ⊓ K) Q hnorm, inf_inf_Q hh hs hn,
    Subgroup.card_bot, mul_one] at h
  exact h

end Hyp

end CFSG.GH74.GLS.C3.Layer1.Back.Setup91

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

theorem _root_.CFSG.GH74.GLS.Hyp9A.kBar_equiv {G : Type} [Group G] [Finite G] {x : G}
    {K L M T Q : Subgroup G} (hh : Hyp9A x K L M T Q) : Nonempty (kBar K ≃* kBar L) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (Setup91.ker_toLBar hh).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (Setup91.toLBar_surjective hh))⟩

theorem _root_.CFSG.GH74.GLS.Hyp9A.R_eq {G : Type} [Group G] [Finite G] {x : G}
    {K L M T Q : Subgroup G} (hh : Hyp9A x K L M T Q) (hs : IsSimpleGroup (kBar L))
    (hn : ∃ a b : kBar L, a * b ≠ b * a) :
    T ⊓ (L ⊔ CMK M L) = (T ⊓ K) ⊔ Q ∧ (∀ p ∈ T ⊓ K, ∀ q ∈ Q, p * q = q * p) ∧
      (T ⊓ K) ⊓ Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, fun p hp q hq => Setup91.comm_inf_Q hh hp hq, Setup91.inf_inf_Q hh hs hn⟩
  have hS₀T : (T ⊓ K) ⊔ Q ≤ T := sup_le inf_le_left (Setup91.Q_le_T hh)
  have hS₀D : (T ⊓ K) ⊔ Q ≤ L ⊔ CMK M L :=
    sup_le (inf_le_right.trans (hh.K_le_L.trans le_sup_left)) (hh.sylowQ.le.trans le_sup_right)
  have hcard : Nat.card ↥((T ⊓ K) ⊔ Q) = 2 ^ (Nat.card ↥(L ⊔ CMK M L)).factorization 2 := by
    rw [Setup91.card_sup_Q hh hs hn, (Setup91.inf_isSylowOf hh).card_eq, hh.sylowQ.card_eq,
      Setup91.factorization_D hs hn, Setup91.factorization_K hh, pow_add]
  exact (isSylowOf_of_card hS₀D hcard).eq_of_le (le_inf hS₀T hS₀D) inf_le_right
    hh.sylowT.isPGroup.to_inf_left

end CFSG.GH74.GLS.C3.Layer1.Back
