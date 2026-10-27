module

public import CFSG.CGT.PushingUpLit.T2KSW.Structure
public import CFSG.CGT.PushingUpLit.T2KSW.Fusion
public import CFSG.CGT.PushingUpLit.T2KSW.Irred

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)
open scoped commutatorElement
open Aux

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

structure RDFacts (L T : Subgroup G) : Prop where
  ZR_le : ZR L T ≤ ZT T
  comm3_le : ⁅⁅T, T⁆, T⁆ ≤ Ec L T
  comm_le : ⁅T, T⁆ ≤ ZR L T ⊔ Ec L T
  sq_mem : ∀ t ∈ T, t ^ 2 ∈ ZR L T ⊔ Ec L T
  comm_R_le : ⁅Rl L T, T⁆ ≤ ZR L T
  cent_R_le : T ⊓ Subgroup.centralizer (Rl L T : Set G) ≤ ZR L T ⊔ Ec L T

structure ClassThreeSetup (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) : Prop where
  sec4 : Sec4 G L M T n
  MN : M ≤ Subgroup.normalizer (L : Set G)
  ME : M ≤ Subgroup.normalizer (Ec L T : Set G)
  ne_bot : Ec L T ≠ ⊥
  facts : RDFacts L T
  comm3 : ∃ x ∈ Dc L T, ∃ y ∈ Dc L T, ∃ z ∈ Dc L T, ⁅⁅x, y⁆, z⁆ ≠ 1

namespace ClassThree

omit [Finite G] in
theorem ZT_le_T : ZT T ≤ T := Subgroup.map_subtype_le _

omit [Finite G] in
theorem conj_ZT {s z : G} (hs : s ∈ T) (hz : z ∈ ZT T) : s * z * s⁻¹ = z := by
  rw [(mem_ZT.1 hz).2 s hs, mul_inv_cancel_right]

omit [Finite G] in
theorem le_normalizer_ZT : T ≤ Subgroup.normalizer (ZT T : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [conj_ZT ht hy]
    exact hy
  · intro hy
    have h1 := conj_ZT (T.inv_mem ht) hy
    have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
    rw [e] at h1
    rw [h1]
    exact hy

theorem eq_bot_of_isPGroup_of_le_of_odd {P Q : Subgroup G} (hP : IsPGroup 2 ↥P) (hPQ : P ≤ Q)
    (hQ : Odd (Nat.card ↥Q)) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hP
  have hdvd : Nat.card ↥P ∣ Nat.card ↥Q := Subgroup.card_dvd_of_le hPQ
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ Nat.card ↥P := by
      rw [hk]
      exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.2 hQ) (even_iff_two_dvd.2 (h2.trans hdvd))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

omit [Finite G] in
theorem Ec_isPGroup (hT : IsSylowOf 2 T M) : IsPGroup 2 ↥(Ec L T) :=
  hT.isPGroup.to_le inf_le_left

end ClassThree

open ClassThree

namespace ClassThreeSetup

variable (hc : ClassThreeSetup G L M T n)
include hc

theorem normalizer_Ec_eq : Subgroup.normalizer (Ec L T : Set G) = M := by
  by_contra hne
  have hlt : M < Subgroup.normalizer (Ec L T : Set G) := lt_of_le_of_ne hc.ME (Ne.symm hne)
  exact hc.sec4.hyp.maxLocal.2 _ hlt ⟨Ec L T, hc.ne_bot, Ec_isPGroup hc.sec4.sylow, rfl⟩

theorem Ec_inf_conj_eq_bot {g : G} (hg : g ∉ M) :
    Ec L T ⊓ (Ec L T).map (MulAut.conj g).toMonoidHom = ⊥ :=
  eq_bot_of_isPGroup_of_le_of_odd ((Ec_isPGroup hc.sec4.sylow).to_le inf_le_left)
    (inf_le_inf inf_le_right (Subgroup.map_mono inf_le_right)) (hc.sec4.hyp.odd_inf_conj hg)

theorem centralizer_le_M {x : G} (hx : x ∈ Ec L T) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  have hsq : x ^ 2 = 1 := hc.sec4.S_elem.2 x hx
  obtain ⟨N, hCN, hNmax⟩ :=
    RankThree.PartOne.Sec15Final.exists_isMaximalTwoLocal_ge (isPLocal_centralizer_of_sq hsq hx1)
  have hLC : L ≤ Subgroup.centralizer ({x} : Set G) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hx.2 l hl)
  have hNM : N = M := by
    have : N ∈ maximalTwoLocalsContaining (L : Set G) := ⟨hNmax, fun y hy => hCN (hLC hy)⟩
    rw [hc.sec4.hyp.unique] at this
    exact this
  rw [← hNM]
  exact hCN

theorem mem_M_of_map_conj_le {k : G} (hk : T.map (MulAut.conj k).toMonoidHom ≤ M) : k ∈ M := by
  have hP : IsPGroup 2 ↥(T.map (MulAut.conj k).toMonoidHom) := hc.sec4.sylow.isPGroup.map _
  obtain ⟨m, hm, hmT⟩ := exists_conj_le_of_isPGroup hc.sec4.sylow hP hk
  have e : (T.map (MulAut.conj k).toMonoidHom).map (MulAut.conj m).toMonoidHom =
      T.map (MulAut.conj (m * k)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [e] at hmT
  have hmk : m * k ∈ Subgroup.normalizer (T : Set G) :=
    mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hmT (by rw [card_map_conj]))
  have := M.mul_mem (M.inv_mem hm) (hc.sec4.N_T hmk)
  simpa using this

theorem conj_Ec_inf_ZT {g : G} (hg : g ∉ M) :
    (Ec L T).map (MulAut.conj g).toMonoidHom ⊓ ZT T = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyE, hyZ⟩
  rw [Subgroup.mem_bot]
  by_contra hy1
  replace hyE : g⁻¹ * y * g ∈ Ec L T := (mem_map_conj_iff g _ y).1 hyE
  have hx1 : g⁻¹ * y * g ≠ 1 := fun h => hy1 (by
    have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [e, h]
    group)
  have hcent := hc.centralizer_le_M hyE hx1
  refine hg ?_
  have hginv : g⁻¹ ∈ M := hc.mem_M_of_map_conj_le (k := g⁻¹) fun w hw => by
    rw [mem_map_conj_iff, inv_inv] at hw
    apply hcent
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : w * (g⁻¹ * y * g) = g⁻¹ * ((g * w * g⁻¹) * y) * g := by group
    have e2 : (g⁻¹ * y * g) * w = g⁻¹ * (y * (g * w * g⁻¹)) * g := by group
    rw [e1, e2, (mem_ZT.1 hyZ).2 _ hw]
  simpa using M.inv_mem hginv

theorem Ec_inf_ZT_ne_bot : Ec L T ⊓ ZT T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T := hc.sec4.sylow.isPGroup.isNilpotent
  have hTE : T ≤ Subgroup.normalizer (Ec L T : Set G) := hc.sec4.sylow.le.trans hc.ME
  have : ((Ec L T).subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hTE
  have hne : (Ec L T).subgroupOf T ≠ ⊥ := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ne_bot
    intro h
    have hmem : (⟨x, hx.1⟩ : ↥T) ∈ (Ec L T).subgroupOf T := hx
    rw [h, Subgroup.mem_bot] at hmem
    exact hx1 (Subtype.ext (by simpa using congrArg Subtype.val hmem))
  obtain ⟨⟨m, hm⟩, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hmE : (m : G) ∈ Ec L T := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hm).1
  have hmZ : (m : G) ∈ ZT T := by
    refine mem_ZT.2 ⟨m.2, fun t ht => ?_⟩
    have := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 hm).2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨(m : G), hmE, hmZ⟩, fun h => hm1 ?_⟩
  exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))

end ClassThreeSetup

namespace ClassThree

omit [Finite G] in
theorem ZR_sup_Ec_le_centralizer :
    ZR L T ⊔ Ec L T ≤ Subgroup.centralizer (Rl L T : Set G) := by
  refine sup_le (fun z hz => Subgroup.mem_centralizer_iff.2 (mem_ZR.1 hz).2) (fun e he => ?_)
  exact Subgroup.mem_centralizer_iff.2 fun r hr =>
    Subgroup.mem_centralizer_iff.1 he.2 r (Rl_le_L hr)

end ClassThree

theorem exists_comm3_ne_one (hs : Sec4 G L M T n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (f : RDFacts L T) (hRD : T ≤ Rl L T ⊔ Dc L T) (hnc : ¬ ClassLETwo T) :
    ∃ x ∈ Dc L T, ∃ y ∈ Dc L T, ∃ z ∈ Dc L T, ⁅⁅x, y⁆, z⁆ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  refine hnc ?_
  have hRn : Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
    Rl_le_T.trans (le_normalizer_Dc hMN hs.sylow.le)
  have hTZ : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ ZT T := by
    refine comm_mem_of_abelian_mod (A := Rl L T) (B := Dc L T) (N := ZT T) (S := T)
      ZT_le_T le_normalizer_ZT Rl_le_T Dc_le_T hRn hRD ?_ ?_ ?_
    · intro a ha a' ha'
      exact f.ZR_le (f.comm_R_le (Subgroup.commutator_mem_commutator ha (Rl_le_T ha')))
    · intro b hb b' hb'
      have hbE : ⁅b, b'⁆ ∈ Ec L T := Dc_comm_mem_Ec hs.hyp.natBlock hMN hs.sylow hb hb'
      refine mem_ZT.2 ⟨Ec_le_T hbE, fun t ht => ?_⟩
      obtain ⟨r, hr, d, hd, rfl⟩ := (mem_sup_iff_mul hRn).1 (hRD ht)
      have h1 : r * ⁅b, b'⁆ = ⁅b, b'⁆ * r := Subgroup.mem_centralizer_iff.1 hbE.2 r (Rl_le_L hr)
      have h2 : d * ⁅b, b'⁆ = ⁅b, b'⁆ * d :=
        (commutatorElement_eq_one_iff_mul_comm.1 (hcon b hb b' hb' d hd)).symm
      calc r * d * ⁅b, b'⁆ = r * (d * ⁅b, b'⁆) := by group
        _ = r * (⁅b, b'⁆ * d) := by rw [h2]
        _ = (r * ⁅b, b'⁆) * d := by group
        _ = (⁅b, b'⁆ * r) * d := by rw [h1]
        _ = ⁅b, b'⁆ * (r * d) := by group
    · intro a ha b hb
      exact f.ZR_le (f.comm_R_le (Subgroup.commutator_mem_commutator ha (Dc_le_T hb)))
  intro a ha b hb c hc'
  exact commutatorElement_eq_one_iff_mul_comm.2 ((mem_ZT.1 (hTZ a ha b hb)).2 c hc').symm

namespace ClassThree

omit [Finite G] in
theorem comm_mul_mul_aux (r s x y : G) (h : s * ⁅x, y⁆ = ⁅x, y⁆ * s) :
    ⁅r * x, s * y⁆ = ⁅r, x * s * y * x⁻¹⁆ * ⁅x, s⁆ * ⁅x, y⁆ := by
  have hc : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
  have h' : s⁻¹ * ⁅x, y⁆ = ⁅x, y⁆ * s⁻¹ := (Commute.inv_left (show Commute s ⁅x, y⁆ from h)).eq
  have e1 : ⁅r * x, s * y⁆ = (r * x * s * y * x⁻¹ * r⁻¹) * (y⁻¹ * s⁻¹) := by
    simp only [commutatorElement_def]
    group
  have e2 : ⁅r, x * s * y * x⁻¹⁆ * ⁅x, s⁆ * ⁅x, y⁆ =
      (r * x * s * y * x⁻¹ * r⁻¹) * ((x * y⁻¹ * x⁻¹ * s⁻¹) * ⁅x, y⁆) := by
    simp only [commutatorElement_def]
    group
  rw [e1, e2]
  congr 1
  calc y⁻¹ * s⁻¹ = (x * y⁻¹ * x⁻¹ * ⁅x, y⁆) * s⁻¹ := by rw [hc]; group
    _ = x * y⁻¹ * x⁻¹ * (⁅x, y⁆ * s⁻¹) := by group
    _ = x * y⁻¹ * x⁻¹ * (s⁻¹ * ⁅x, y⁆) := by rw [h']
    _ = (x * y⁻¹ * x⁻¹ * s⁻¹) * ⁅x, y⁆ := by group

omit [Finite G] in
theorem comm_central_mul_left {z₀ a w : G} (hz : z₀ * w = w * z₀)
    (hza : z₀ * ⁅a, w⁆ = ⁅a, w⁆ * z₀) : ⁅z₀ * a, w⁆ = ⁅a, w⁆ := by
  have e : ⁅z₀ * a, w⁆ = z₀ * ⁅a, w⁆ * z₀⁻¹ * ⁅z₀, w⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, commutatorElement_eq_one_iff_mul_comm.2 hz, mul_one, hza, mul_inv_cancel_right]

omit [Finite G] in
theorem comm_mul_right_of_commute {c t z : G} (ht : t * c = c * t)
    (htc : t * ⁅c, z⁆ = ⁅c, z⁆ * t) : ⁅c, t * z⁆ = ⁅c, z⁆ := by
  have e : ⁅c, t * z⁆ = ⁅c, t⁆ * (t * ⁅c, z⁆ * t⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, commutatorElement_eq_one_iff_mul_comm.2 ht.symm, one_mul, htc, mul_inv_cancel_right]

omit [Finite G] in
theorem le_normalizer_of_comm_mem {Q : Subgroup G} (hQT : Q ≤ T)
    (hTQ : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ Q) : T ≤ Subgroup.normalizer (Q : Set G) := by
  have key : ∀ x ∈ T, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := fun x hx y hy => by
    have h := Q.mul_mem (hTQ x hx y (hQT hy)) hy
    have e : ⁅x, y⁆ * y = x * y * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have := key x⁻¹ (T.inv_mem hx) _ hy
  simpa [mul_assoc] using this

end ClassThree

theorem exists_Q_of_not_weaklyClosed
    (hc : ClassThreeSetup G L M T n)
    (hnwc : ∃ g : G, (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T ∧
      (Ec L T).map (MulAut.conj g).toMonoidHom ≠ Ec L T) :
    ∃ Q : Subgroup G, Q ≤ T ∧ Ec L T ≤ Q ∧ ZT T ≤ Q ∧
      (∃ m ∈ Subgroup.normalizer (Q : Set G), m ∉ Subgroup.normalizer (Ec L T : Set G)) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ^ 2 ∈ Q ∧ ⁅x, y⁆ ∈ Q) ∧
      ∀ P : Subgroup G, P ≤ T →
        Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (P : Set G) → P ≤ Q ∨ P ⊔ Q = T := by
  obtain ⟨Q, hQT, hEQ, hCQ, hmove, hmax⟩ :=
    exists_good_Q T (Ec L T) hc.sec4.sylowG Ec_le_T hnwc
  have hZQ : ZT T ≤ Q := fun z hz =>
    hCQ ⟨Subgroup.mem_centralizer_iff.2 fun q hq => (mem_ZT.1 hz).2 q (hQT hq), (mem_ZT.1 hz).1⟩
  have hsup : ZR L T ⊔ Ec L T ≤ Q := sup_le (hc.facts.ZR_le.trans hZQ) hEQ
  have hTQ : ∀ x ∈ T, ∀ y ∈ T, x ^ 2 ∈ Q ∧ ⁅x, y⁆ ∈ Q := fun x hx y hy =>
    ⟨hsup (hc.facts.sq_mem x hx),
      hsup (hc.facts.comm_le (Subgroup.commutator_mem_commutator hx hy))⟩
  have hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Ec L T : Set G) :=
    hc.sec4.N_T.trans hc.ME
  obtain ⟨-, hTR⟩ := tr_of_good_Q_uniform hc.sec4.sylowG hQT hTQ hmove hmax hNT
  exact ⟨Q, hQT, hEQ, hZQ, hmove, hTQ, fun P hPT hNP => hTR P hPT (inf_le_right.trans hNP)⟩

theorem comm3_Q_eq_one (hc : ClassThreeSetup G L M T n) {Q : Subgroup G} (hQT : Q ≤ T)
    (hmove : ∃ m ∈ Subgroup.normalizer (Q : Set G), m ∉ Subgroup.normalizer (Ec L T : Set G)) :
    ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, ⁅⁅a, b⁆, c⁆ = 1 := by
  obtain ⟨m, hmQ, hmE⟩ := hmove
  have hmM : m ∉ M := fun h => hmE (hc.ME h)
  have hKE : ⁅⁅Q, Q⁆, Q⁆ ≤ Ec L T :=
    (Subgroup.commutator_mono (Subgroup.commutator_mono hQT hQT) hQT).trans hc.facts.comm3_le
  have hQm : Q.map (MulAut.conj m).toMonoidHom = Q := map_conj_eq_of_mem_normalizer hmQ
  have hKm : (⁅⁅Q, Q⁆, Q⁆).map (MulAut.conj m).toMonoidHom = ⁅⁅Q, Q⁆, Q⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hQm]
  have hK : ⁅⁅Q, Q⁆, Q⁆ ≤ Ec L T ⊓ (Ec L T).map (MulAut.conj m).toMonoidHom :=
    le_inf hKE (hKm ▸ Subgroup.map_mono hKE)
  rw [hc.Ec_inf_conj_eq_bot hmM] at hK
  intro a ha b hb c hc'
  have := hK (Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator ha hb) hc')
  simpa using this

theorem Rl_le_Q (hc : ClassThreeSetup G L M T n) {Q : Subgroup G} (hQT : Q ≤ T)
    (hTQ : ∀ x ∈ T, ∀ y ∈ T, x ^ 2 ∈ Q ∧ ⁅x, y⁆ ∈ Q)
    (hcomm3 : ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, ⁅⁅a, b⁆, c⁆ = 1)
    (hTR : ∀ P : Subgroup G, P ≤ T →
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (P : Set G) → P ≤ Q ∨ P ⊔ Q = T) :
    Rl L T ≤ Q := by
  by_contra hRQ
  have hNR : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Rl L T : Set G) :=
    fun m hm => mem_normalizer_Rl hc.MN (hc.sec4.N_T hm) hm
  have hRQT : Rl L T ⊔ Q = T := (hTR _ Rl_le_T hNR).resolve_left hRQ
  have hTN : T ≤ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_of_comm_mem hQT fun x hx y hy => (hTQ x hx y hy).2
  have hdec : ∀ x ∈ T, ∃ r ∈ Rl L T, r * x ∈ Q := fun x hx => by
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_mul (Rl_le_T.trans hTN)).1 (hRQT.ge hx)
    exact ⟨a⁻¹, (Rl L T).inv_mem ha, by rw [hab, inv_mul_cancel_left]; exact hb⟩
  obtain ⟨x, hx, y, hy, z, hz, hne⟩ := hc.comm3
  have hxT : x ∈ T := Dc_le_T hx
  have hyT : y ∈ T := Dc_le_T hy
  have hzT : z ∈ T := Dc_le_T hz
  obtain ⟨r, hr, hrx⟩ := hdec x hxT
  obtain ⟨s, hs, hsy⟩ := hdec y hyT
  obtain ⟨t, ht, htz⟩ := hdec z hzT
  have h1 := hcomm3 _ hrx _ hsy _ htz
  refine hne ?_
  have hcR : ∀ w ∈ Rl L T, w * ⁅x, y⁆ = ⁅x, y⁆ * w := fun w hw =>
    Subgroup.mem_centralizer_iff.1 (ZR_sup_Ec_le_centralizer
      (hc.facts.comm_le (Subgroup.commutator_mem_commutator hxT hyT))) w hw
  have hc2R : ∀ w ∈ Rl L T, w * ⁅⁅x, y⁆, z⁆ = ⁅⁅x, y⁆, z⁆ * w := fun w hw =>
    Subgroup.mem_centralizer_iff.1 (hc.facts.comm3_le
      (Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator hxT hyT) hzT)).2 w
      (Rl_le_L hw)
  have hZ : ∀ r ∈ Rl L T, ∀ w ∈ T, ⁅r, w⁆ ∈ ZT T := fun r hr w hw =>
    hc.facts.ZR_le (hc.facts.comm_R_le (Subgroup.commutator_mem_commutator hr hw))
  have hA := comm_mul_mul_aux r s x y (hcR s hs)
  have hz₀ : ⁅r, x * s * y * x⁻¹⁆ * ⁅x, s⁆ ∈ ZT T := by
    refine (ZT T).mul_mem (hZ r hr _ ?_) ?_
    · exact T.mul_mem (T.mul_mem (T.mul_mem hxT (Rl_le_T hs)) hyT) (T.inv_mem hxT)
    · rw [← commutatorElement_inv]
      exact (ZT T).inv_mem (hZ s hs x hxT)
  rw [hA] at h1
  set z₀ := ⁅r, x * s * y * x⁻¹⁆ * ⁅x, s⁆
  have hcT : ⁅x, y⁆ ∈ T := comm_mem_subgroup hxT hyT
  have htzT : t * z ∈ T := T.mul_mem (Rl_le_T ht) hzT
  have hB : ⁅z₀ * ⁅x, y⁆, t * z⁆ = ⁅⁅x, y⁆, t * z⁆ :=
    comm_central_mul_left ((mem_ZT.1 hz₀).2 _ htzT).symm
      ((mem_ZT.1 hz₀).2 _ (comm_mem_subgroup hcT htzT)).symm
  have hC : ⁅⁅x, y⁆, t * z⁆ = ⁅⁅x, y⁆, z⁆ :=
    comm_mul_right_of_commute (hcR t ht) (hc2R t ht)
  rw [hB, hC] at h1
  exact h1

theorem false_of_Rl_le_Q (hc : ClassThreeSetup G L M T n) {Q : Subgroup G} (hQT : Q ≤ T)
    (hZQ : ZT T ≤ Q)
    (hmove : ∃ m ∈ Subgroup.normalizer (Q : Set G), m ∉ Subgroup.normalizer (Ec L T : Set G))
    (hRQ : Rl L T ≤ Q) : False := by
  obtain ⟨m, hmQ, hmE⟩ := hmove
  have hmM : m ∉ M := fun h => hmE (hc.ME h)
  set A : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
  set E₁ : Subgroup G := Ec L T ⊓ A
  set Z : Subgroup G := ZT T
  have hZA : Z ≤ A := fun z hz =>
    ⟨hZQ hz, Subgroup.mem_centralizer_iff.2 fun q hq => (mem_ZT.1 hz).2 q (hQT hq)⟩
  have hTE : T ≤ Subgroup.normalizer (Ec L T : Set G) := hc.sec4.sylow.le.trans hc.ME
  have hZRE : ZR L T ≤ Subgroup.normalizer (Ec L T : Set G) :=
    (ZR_le_Rl.trans Rl_le_T).trans hTE
  have hAZE : A ≤ Z ⊔ E₁ := by
    intro a ha
    have haC : a ∈ T ⊓ Subgroup.centralizer (Rl L T : Set G) :=
      ⟨hQT ha.1, Subgroup.mem_centralizer_iff.2 fun r hr =>
        Subgroup.mem_centralizer_iff.1 ha.2 r (hRQ hr)⟩
    obtain ⟨z, hz, e, he, rfl⟩ := (mem_sup_iff_mul hZRE).1 (hc.facts.cent_R_le haC)
    have hzZ : z ∈ Z := hc.facts.ZR_le hz
    have heA : e ∈ A := by
      have := A.mul_mem (A.inv_mem (hZA hzZ)) ha
      simpa using this
    exact (Z ⊔ E₁).mul_mem (Subgroup.mem_sup_left hzZ) (Subgroup.mem_sup_right ⟨he, heA⟩)
  set F : Subgroup G := E₁.map (MulAut.conj m).toMonoidHom
  have hFA : F ≤ A := by
    rintro _ ⟨e, he, rfl⟩
    have hmQ' : ∀ q ∈ Q, m⁻¹ * q * m ∈ Q := fun q hq => by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (Q : Set G)).inv_mem hmQ) q).1 hq
      simpa using this
    refine ⟨(Subgroup.mem_normalizer_iff.1 hmQ e).1 he.2.1, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro q hq
    have h1 : e * (m⁻¹ * q * m) = (m⁻¹ * q * m) * e :=
      (Subgroup.mem_centralizer_iff.1 he.2.2 _ (hmQ' q hq)).symm
    have e1 : q * (MulAut.conj m).toMonoidHom e = m * ((m⁻¹ * q * m) * e) * m⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have e2 : (MulAut.conj m).toMonoidHom e * q = m * (e * (m⁻¹ * q * m)) * m⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e1, e2, h1]
  have hFZ : Z ⊓ F = ⊥ := by
    rw [eq_bot_iff, ← hc.conj_Ec_inf_ZT hmM, inf_comm]
    exact inf_le_inf (Subgroup.map_mono (inf_le_left : E₁ ≤ Ec L T)) le_rfl
  have hcentZ : ∀ f ∈ A, f ∈ Subgroup.normalizer (Z : Set G) := fun f hf =>
    Subgroup.centralizer_le_normalizer (Z : Set G) (Subgroup.mem_centralizer_iff.2 fun z hz =>
      Subgroup.mem_centralizer_iff.1 hf.2 z (hZQ hz))
  have c1 := card_sup_mul_card_inf_of_le_normalizer (fun f hf => hcentZ f (hFA hf))
  have c2 := card_sup_mul_card_inf_of_le_normalizer
    (A := Z) (B := E₁) (fun f hf => hcentZ f hf.2)
  rw [hFZ, Subgroup.card_bot, mul_one] at c1
  have hF_card : Nat.card F = Nat.card E₁ := card_map_conj E₁ m
  have hle : Nat.card (Z ⊔ F : Subgroup G) ≤ Nat.card (Z ⊔ E₁ : Subgroup G) :=
    Subgroup.card_le_of_le ((sup_le hZA hFA).trans hAZE)
  have hpos : 0 < Nat.card (Z ⊔ E₁ : Subgroup G) := Nat.card_pos
  have hZE : Nat.card (Z ⊓ E₁ : Subgroup G) = 1 := by
    have h3 : Nat.card ↥(Z ⊔ E₁) * Nat.card ↥(Z ⊓ E₁) ≤ Nat.card ↥(Z ⊔ E₁) * 1 := by
      rw [mul_one, c2, ← hF_card, ← c1]
      exact hle
    have h4 : Nat.card ↥(Z ⊓ E₁) ≤ 1 := Nat.le_of_mul_le_mul_left h3 hpos
    have h5 : 0 < Nat.card ↥(Z ⊓ E₁) := Nat.card_pos
    omega
  have hbot : Z ⊓ E₁ = ⊥ := Subgroup.eq_bot_of_card_eq _ hZE
  refine hc.Ec_inf_ZT_ne_bot (eq_bot_iff.2 fun x hx => ?_)
  have hx' : x ∈ Z ⊓ E₁ := ⟨hx.2, hx.1, hZA hx.2⟩
  rw [hbot] at hx'
  exact hx'

theorem weaklyClosed_Ec (hc : ClassThreeSetup G L M T n) (g : G)
    (hg : (Ec L T).map (MulAut.conj g).toMonoidHom ≤ T) :
    (Ec L T).map (MulAut.conj g).toMonoidHom = Ec L T := by
  by_contra hne
  obtain ⟨Q, hQT, -, hZQ, hmove, hTQ, hTR⟩ := exists_Q_of_not_weaklyClosed hc ⟨g, hg, hne⟩
  have hRQ := Rl_le_Q hc hQT hTQ (comm3_Q_eq_one hc hQT hmove) hTR
  exact false_of_Rl_le_Q hc hQT hZQ hmove hRQ

end CFSG.CGT.PushingUpLit.T2KSW
