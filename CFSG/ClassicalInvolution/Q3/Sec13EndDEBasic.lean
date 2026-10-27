module

public import CFSG.ClassicalInvolution.Q3.Sec13End12
public import CFSG.ClassicalInvolution.Q3.Sec13EndS3E8
import CFSG.ClassicalInvolution.Q3.TL4SepTwoD

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

structure DEHyp (Ω : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Ω
  two : ∀ J ∈ Ω, IsPGroup 2 J
  card : ∀ J ∈ Ω, Nat.card J = 8
  gen : pSpan Ω = ⊤
  trans : ∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L'
  center : Subgroup.center G = ⊥
  inO2 : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
    ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q
  perp : Perp9 Ω
  dNorm : ∀ L ∈ Ω, zGroup Ω ≤ Subgroup.normalizer (L : Set G)
  card_zGroup : Nat.card (zGroup Ω) = 8

private structure DEBase (Ω : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Ω
  two : ∀ J ∈ Ω, IsPGroup 2 J
  card : ∀ J ∈ Ω, Nat.card J = 8
  inO2 : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
    ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q
  perp : Perp9 Ω
  dNorm : ∀ L ∈ Ω, zGroup Ω ≤ Subgroup.normalizer (L : Set G)

private def deb_of {Ω : Set (Subgroup G)} (h : DEHyp Ω) : DEBase Ω :=
  ⟨h.hyp, h.two, h.card, h.inO2, h.perp, h.dNorm⟩

section Common

variable {Ω : Set (Subgroup G)}

private theorem deb_zGroup_normal_of (hΩ : ConjInvariant Ω) : (zGroup Ω).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : n ∈ Subgroup.closure {u : G | ∃ L ∈ Ω, IsUniqueInvolution L u} := hn
  clear hn
  induction hn' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨L, hL, hu⟩ := hx
    exact Subgroup.subset_closure ⟨conjSub g L, hΩ g L hL, hu.conj g⟩
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact (zGroup Ω).one_mem
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]
    exact (zGroup Ω).mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact (zGroup Ω).inv_mem hx

private theorem deb_zGroup_normal (B : DEBase Ω) : (zGroup Ω).Normal :=
  deb_zGroup_normal_of B.hyp.conjInvariant

private theorem deb_conjSub_eq_of_normal {X : Subgroup G} (hX : X.Normal) (g : G) :
    conjSub g X = X := by
  apply le_antisymm
  · intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 := hX.conj_mem _ hx g
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  · intro x hx
    rw [mem_conjSub_iff]
    have h1 := hX.conj_mem x hx g⁻¹
    rwa [inv_inv] at h1

private theorem deb_zGroup_le_pCore (B : DEBase Ω) : zGroup Ω ≤ pCore 2 G := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro u ⟨L, hL, hu⟩
  obtain ⟨Q, hQn, hQ2, huQ⟩ := B.inO2 L hL u hu
  exact (le_sSup ⟨hQn, hQ2⟩ : Q ≤ pCore 2 G) huQ

private theorem deb_isQuatSub (B : DEBase Ω) {L : Subgroup G} (hL : L ∈ Ω) : IsQuatSub L :=
  Sec6Gen.isQuatSub_of_mem_RSet B.hyp (TC.mem_RSet_of_isPGroup hL (B.two L hL))

private theorem deb_Q8Data (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : ∃ i j : G, Q8Data K z i j := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hz (deb_isQuatSub B hK) (B.card K hK)
  exact ⟨i, j, ⟨hz, hi, hj, hii, hjj, hji, hNF⟩⟩

private theorem deb_not_mem_USet (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω) : K ∉ USet Ω := by
  rintro ⟨R, hR, hKR, -, hrel⟩
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hRJeq : R = J := (hRJ.2.2 J le_rfl (B.two J hJ) hRJ.1).symm
  have hcard : Nat.card R = Nat.card K := by
    rw [hRJeq, B.card J hJ, B.card K hK]
  have hKR' : K = R := Subgroup.eq_of_le_of_card_ge hKR hcard.le
  rw [← hKR', Subgroup.relIndex_self] at hrel
  norm_num at hrel

private theorem deb_exists_not_commute_of_ne (B : DEBase Ω) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ Ω) {a b : G} (ha : IsUniqueInvolution K a) (hb : IsUniqueInvolution L b)
    (hab : a ≠ b) : ∃ x ∈ K, b * x ≠ x * b := by
  by_contra hcon
  push Not at hcon
  have hKc : K ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcon x hx).symm
  have hV' : IsSylow2In K (K ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [inf_eq_left.mpr hKc]
    exact ⟨le_rfl, B.two K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hnot : K ∉ twinSet Ω L := by
    rintro ⟨-, z, hLz, hKz⟩
    exact hab ((ha.eq hKz).trans (hb.eq hLz).symm)
  rcases Sec6Gen.l6_2Gen G Ω B.hyp L hL b hb K hK hnot a ha K hV' ha.mem with
    ⟨hVt, -⟩ | ⟨hVt, -⟩ | ⟨hVU, -⟩ | ⟨-, hVL⟩
  · have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha.sq) ha.ne_one
    have h8 := B.card K hK
    rw [hVt, Nat.card_zpowers, hord] at h8
    norm_num at h8
  · have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha.sq) ha.ne_one
    have h8 := B.card K hK
    rw [hVt, Nat.card_zpowers, hord] at h8
    norm_num at h8
  · exact deb_not_mem_USet B hK hVU
  · have hbot : oddCoreOf L = ⊥ := TL4.oddCoreOf_eq_bot_of_isPGroup (B.two L hL)
    have hc : Commutes K L := fun x hx y hy => by
      have hm := hVL (Subgroup.commutator_mem_commutator hx hy)
      rw [hbot, Subgroup.mem_bot] at hm
      exact commutatorElement_eq_one_iff_mul_comm.mp hm
    exact hab (B.perp K hK L hL hc a b ha hb)

private theorem deb_exists_involution_mul (B : DEBase Ω) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ Ω) {a b : G} (ha : IsUniqueInvolution K a) (hb : IsUniqueInvolution L b)
    (hab : a ≠ b) : ∃ M ∈ Ω, ∃ u : G, IsUniqueInvolution M u ∧ u = a * b := by
  have hbD : b ∈ zGroup Ω := Subgroup.subset_closure ⟨L, hL, hb⟩
  have hbN : b ∈ Subgroup.normalizer (K : Set G) := B.dNorm K hK hbD
  have htK : ∀ x ∈ K, b * x * b⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hbN x).mp hx
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen ha (deb_isQuatSub B hK) (B.card K hK)
  obtain ⟨k, -, hkb⟩ := exists_conj_eq_mul_of_not_comm ha hi hj hii hjj hji hNF hb.sq htK
    (deb_exists_not_commute_of_ne B hK hL ha hb hab)
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.sq
  have hconj : k * b * k⁻¹ = a * b := by
    have h1 : b * k⁻¹ * b⁻¹ = k⁻¹ * a := by
      calc b * k⁻¹ * b⁻¹ = (b * k * b⁻¹)⁻¹ := by group
        _ = (a * k)⁻¹ := by rw [hkb]
        _ = k⁻¹ * a := by rw [mul_inv_rev, hinv]
    calc k * b * k⁻¹ = k * (b * k⁻¹ * b⁻¹) * b := by group
      _ = a * b := by rw [h1]; group
  exact ⟨conjSub k L, B.hyp.conjInvariant k L hL, k * b * k⁻¹, hb.conj k, hconj⟩

private theorem deb_mem_zGroup_iff (B : DEBase Ω) {x : G} :
    x ∈ zGroup Ω ↔ x = 1 ∨ ∃ L ∈ Ω, IsUniqueInvolution L x := by
  have hmul : ∀ x y : G, (x = 1 ∨ ∃ L ∈ Ω, IsUniqueInvolution L x) →
      (y = 1 ∨ ∃ L ∈ Ω, IsUniqueInvolution L y) →
      (x * y = 1 ∨ ∃ L ∈ Ω, IsUniqueInvolution L (x * y)) := by
    rintro x y (rfl | ⟨K, hK, ha⟩) (rfl | ⟨L, hL, hb⟩)
    · exact Or.inl (mul_one 1)
    · exact Or.inr ⟨L, hL, by rw [one_mul]; exact hb⟩
    · exact Or.inr ⟨K, hK, by rw [mul_one]; exact ha⟩
    · by_cases hxy : x = y
      · subst hxy
        exact Or.inl ha.sq
      · obtain ⟨M, hM, u, hu, rfl⟩ := deb_exists_involution_mul B hK hL ha hb hxy
        exact Or.inr ⟨M, hM, hu⟩
  constructor
  · intro hx
    refine Subgroup.closure_induction
      (p := fun x _ => x = 1 ∨ ∃ L ∈ Ω, IsUniqueInvolution L x) ?_ ?_ ?_ ?_ hx
    · intro x hx
      exact Or.inr hx
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      exact hmul x y hx hy
    · intro x _ hx
      rcases hx with rfl | ⟨L, hL, hu⟩
      · exact Or.inl inv_one
      · exact Or.inr ⟨L, hL, by rw [inv_eq_of_mul_eq_one_right hu.sq]; exact hu⟩
  · rintro (rfl | ⟨L, hL, hu⟩)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨L, hL, hu⟩

private theorem deb_mem_zpowers_involution {K : Subgroup G} {z x : G}
    (hz : IsUniqueInvolution K z) (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  have hxK : x ∈ K := (Subgroup.zpowers_le.mpr hz.mem) hx
  have hxx : x * x = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_add, show k + k = 2 * k by ring, zpow_mul, zpow_two, hz.sq, one_zpow]
  exact hz.unique x hxK hxx

private theorem deb_mem_zpowers_of {z x : G} (h : x = 1 ∨ x = z) :
    x ∈ Subgroup.zpowers z := by
  rcases h with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _

private theorem deb_eq_one_or_eq_of_mem_zGroup (B : DEBase Ω) {K : Subgroup G} {z x : G}
    (hz : IsUniqueInvolution K z) (hxD : x ∈ zGroup Ω) (hxK : x ∈ K) : x = 1 ∨ x = z := by
  rcases (deb_mem_zGroup_iff B).mp hxD with rfl | ⟨M, hM, hu⟩
  · exact Or.inl rfl
  · exact hz.unique x hxK hu.sq

private theorem deb_eq_one_or_eq_of_centralizes (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z d : G} (hz : IsUniqueInvolution K z) (hd : d ∈ zGroup Ω)
    (hc : ∀ x ∈ K, d * x = x * d) : d = 1 ∨ d = z := by
  rcases (deb_mem_zGroup_iff B).mp hd with rfl | ⟨M, hM, hu⟩
  · exact Or.inl rfl
  · by_cases hMK : M = K
    · subst hMK
      exact Or.inr (hz.eq hu).symm
    · by_contra hne
      have hdz : d ≠ z := fun e => hne (Or.inr e)
      obtain ⟨x, hx, hxd⟩ := deb_exists_not_commute_of_ne B hK hM hz hu (fun e => hdz e.symm)
      exact hxd (hc x hx)

private theorem deb_dComm_eq_one_or (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {d k : G} (hd : d ∈ zGroup Ω) (hk : k ∈ K) :
    dComm d k = 1 ∨ dComm d k = z := by
  have hdN := B.dNorm K hK hd
  have hcK : dComm d k ∈ K := dComm_mem hdN hk
  have hcD : dComm d k ∈ zGroup Ω := by
    have e : dComm d k = d * (k * d⁻¹ * k⁻¹) := by unfold dComm; group
    rw [e]
    exact (zGroup Ω).mul_mem hd
      ((deb_zGroup_normal B).conj_mem _ ((zGroup Ω).inv_mem hd) k)
  exact deb_eq_one_or_eq_of_mem_zGroup B hz hcD hcK

private theorem deb_dComm_left_mem (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {x d : G} (hx : x ∈ K) (hd : d ∈ zGroup Ω) :
    dComm x d = 1 ∨ dComm x d = z := by
  have hdN := B.dNorm K hK hd
  have hcK : dComm x d ∈ K := by
    have e : dComm x d = x * (d * x⁻¹ * d⁻¹) := by unfold dComm; group
    rw [e]
    exact K.mul_mem hx ((Subgroup.mem_normalizer_iff.mp hdN x⁻¹).mp (K.inv_mem hx))
  have hcD : dComm x d ∈ zGroup Ω :=
    (zGroup Ω).mul_mem ((deb_zGroup_normal B).conj_mem d hd x) ((zGroup Ω).inv_mem hd)
  exact deb_eq_one_or_eq_of_mem_zGroup B hz hcD hcK

private theorem deb_dComm_mem_zpowers (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {d k : G} (hd : d ∈ zGroup Ω) (hk : k ∈ K) :
    dComm d k ∈ Subgroup.zpowers z :=
  deb_mem_zpowers_of (deb_dComm_eq_one_or B hK hz hd hk)

private theorem deb_dComm_mul_left_K {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    {x y d : G} (hx : x ∈ K) (hc : dComm y d = 1 ∨ dComm y d = z) :
    dComm (x * y) d = dComm y d * dComm x d := by
  have hxc := conj_of_mem_mem hz hx hc
  calc dComm (x * y) d = (x * dComm y d * x⁻¹) * dComm x d := by unfold dComm; group
    _ = dComm y d * dComm x d := by rw [hxc]

private theorem deb_commute_z_of_le (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {P : Subgroup G} (hP : IsPGroup 2 P) (hKP : K ≤ P) {s : G}
    (hs : s ∈ P) : s * z = z * s := by
  have hΩ := B.hyp
  have hL : conjSub s K ∈ Ω := hΩ.conjInvariant s K hK
  have hLP : conjSub s K ≤ P := (conjSub_mono hKP).trans (conjSub_eq_self_of_mem hs).le
  have hzs : z = s * z * s⁻¹ := by
    by_cases hLK : conjSub s K = K
    · have h1 := hz.conj s
      rw [hLK] at h1
      exact hz.eq h1
    · obtain ⟨S, hPS⟩ := hP.exists_le_sylow
      have hc : Commutes K (conjSub s K) :=
        Q3CP.l67Gen G Ω hΩ S K (TC.mem_RSet_of_isPGroup hK (B.two K hK)) (conjSub s K)
          (TC.mem_RSet_of_isPGroup hL (B.two _ hL)) (hKP.trans hPS) (hLP.trans hPS)
          (fun e => hLK e.symm)
      exact B.perp K hK (conjSub s K) hL hc z (s * z * s⁻¹) hz (hz.conj s)
  calc s * z = s * z * s⁻¹ * s := by group
    _ = z * s := by rw [← hzs]

private theorem deb_pCore_comm_zGroup (B : DEBase Ω) {q : G} (hq : q ∈ pCore 2 G) :
    ∀ x ∈ zGroup Ω, x * q = q * x := by
  have hle : zGroup Ω ≤ Subgroup.centralizer ({q} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨L, hL, hu⟩
    obtain ⟨S, hLS⟩ := (B.two L hL).exists_le_sylow
    have hqS : q ∈ (S : Subgroup G) := CFSG.pCore_isPGroup.le_sylow_of_normal S hq
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (deb_commute_z_of_le B hL hu S.isPGroup' hLS hqS).symm
  exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

private theorem deb_zGroup_comm (B : DEBase Ω) : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω,
    a * b = b * a :=
  fun a ha b hb => deb_pCore_comm_zGroup B (deb_zGroup_le_pCore B hb) a ha

private theorem deb_zGroup_mul_self (B : DEBase Ω) : ∀ a ∈ zGroup Ω, a * a = 1 := by
  intro a ha
  have ha' : a ∈ Subgroup.closure {u : G | ∃ L ∈ Ω, IsUniqueInvolution L u} := ha
  clear ha
  induction ha' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨L, -, hu⟩ := hx
    exact hu.sq
  | one => exact one_mul 1
  | mul x y hx hy hxx hyy =>
    have hc : x * y = y * x := deb_zGroup_comm B x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, one_mul]
  | inv x hx hxx =>
    rw [← mul_inv_rev, hxx, inv_one]

private theorem deb_pCore_le_centralizer_zGroup (B : DEBase Ω) :
    pCore 2 G ≤ Subgroup.centralizer (zGroup Ω : Set G) := by
  intro q hq
  exact Subgroup.mem_centralizer_iff.mpr fun x hx => deb_pCore_comm_zGroup B hq x hx

private noncomputable def deb_phiHom (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z i j : G} (hQ : Q8Data K z i j) :
    zGroup Ω →* ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z) where
  toFun d := (⟨dComm (d : G) i, deb_dComm_mem_zpowers B hK hQ.inv d.2 hQ.mem_i⟩,
    ⟨dComm (d : G) j, deb_dComm_mem_zpowers B hK hQ.inv d.2 hQ.mem_j⟩)
  map_one' := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show dComm ((1 : zGroup Ω) : G) i = 1
      simp [dComm]
    · show dComm ((1 : zGroup Ω) : G) j = 1
      simp [dComm]
  map_mul' a b := by
    have hb := deb_dComm_eq_one_or B hK hQ.inv b.2 hQ.mem_i
    have hb' := deb_dComm_eq_one_or B hK hQ.inv b.2 hQ.mem_j
    have ha := B.dNorm K hK a.2
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show dComm ((a * b : zGroup Ω) : G) i = dComm (a : G) i * dComm (b : G) i
      rw [Subgroup.coe_mul, dComm_mul_left hQ.inv ha hb]
      rcases hb with h1 | h1 <;>
        rcases deb_dComm_eq_one_or B hK hQ.inv a.2 hQ.mem_i with h2 | h2 <;>
        rw [h1, h2] <;> simp
    · show dComm ((a * b : zGroup Ω) : G) j = dComm (a : G) j * dComm (b : G) j
      rw [Subgroup.coe_mul, dComm_mul_left hQ.inv ha hb']
      rcases hb' with h1 | h1 <;>
        rcases deb_dComm_eq_one_or B hK hQ.inv a.2 hQ.mem_j with h2 | h2 <;>
        rw [h1, h2] <;> simp

private theorem deb_card_ker_phiHom_le (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z i j : G} (hQ : Q8Data K z i j) :
    Nat.card (deb_phiHom B hK hQ).ker ≤ 2 := by
  have key : ∀ d : zGroup Ω, deb_phiHom B hK hQ d = 1 → (d : G) = 1 ∨ (d : G) = z := by
    intro d hd
    have hi : dComm (d : G) i = 1 := congrArg Subtype.val (congrArg Prod.fst hd)
    have hj : dComm (d : G) j = 1 := congrArg Subtype.val (congrArg Prod.snd hd)
    have hdN := B.dNorm K hK d.2
    have hgen : ∀ x ∈ K, dComm (d : G) x = 1 := by
      intro x hx
      rcases hQ.nf x hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [dComm]
      · exact dComm_z hQ.inv hdN
      · exact hi
      · rw [dComm_mul_right hQ.inv hQ.inv.mem hQ.mem_i hdN
          (deb_dComm_eq_one_or B hK hQ.inv d.2 hQ.mem_i), dComm_z hQ.inv hdN, hi, one_mul]
      · exact hj
      · rw [dComm_mul_right hQ.inv hQ.inv.mem hQ.mem_j hdN
          (deb_dComm_eq_one_or B hK hQ.inv d.2 hQ.mem_j), dComm_z hQ.inv hdN, hj, one_mul]
      · rw [dComm_mul_right hQ.inv hQ.mem_i hQ.mem_j hdN
          (deb_dComm_eq_one_or B hK hQ.inv d.2 hQ.mem_j), hi, hj, one_mul]
      · rw [dComm_mul_right hQ.inv hQ.inv.mem (K.mul_mem hQ.mem_i hQ.mem_j) hdN
          (deb_dComm_eq_one_or B hK hQ.inv d.2 (K.mul_mem hQ.mem_i hQ.mem_j)),
          dComm_z hQ.inv hdN, dComm_mul_right hQ.inv hQ.mem_i hQ.mem_j hdN
          (deb_dComm_eq_one_or B hK hQ.inv d.2 hQ.mem_j), hi, hj, one_mul, one_mul]
    exact deb_eq_one_or_eq_of_centralizes B hK hQ.inv d.2
      (fun x hx => dComm_eq_one_iff.mp (hgen x hx))
  have hmem : ∀ d : (deb_phiHom B hK hQ).ker, (d.1 : G) ∈ Subgroup.zpowers z := by
    intro d
    exact deb_mem_zpowers_of (key d.1 (MonoidHom.mem_ker.mp d.2))
  have hinj : Function.Injective (fun d : (deb_phiHom B hK hQ).ker =>
      (⟨(d.1 : G), hmem d⟩ : ↥(Subgroup.zpowers z))) := by
    intro a b hab
    have hval : ((a.1 : zGroup Ω) : G) = ((b.1 : zGroup Ω) : G) := by
      have := congrArg Subtype.val hab
      simpa using this
    exact Subtype.ext (Subtype.ext hval)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [card_zpowers_of_involution hQ.inv.sq hQ.inv.ne_one] at this

private theorem deb_card_zGroup_le (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    Nat.card (zGroup Ω) ≤ 8 := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution B.hyp hK
  obtain ⟨i, j, hQ⟩ := deb_Q8Data B hK hz
  have h1 := Subgroup.card_mul_index (deb_phiHom B hK hQ).ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card (deb_phiHom B hK hQ).range ≤ 4 := by
    have := Subgroup.card_le_card_group (deb_phiHom B hK hQ).range
    rwa [card_zpowers_prod_eq_four hQ.inv.sq hQ.inv.ne_one] at this
  have h3 := deb_card_ker_phiHom_le B hK hQ
  rw [← h1]
  exact (Nat.mul_le_mul h3 h2).trans (by norm_num)

private theorem deb_phiHom_surjective (B : DEBase Ω) (hD8 : Nat.card (zGroup Ω) = 8)
    {K : Subgroup G} (hK : K ∈ Ω) {z i j : G} (hQ : Q8Data K z i j) :
    Function.Surjective (deb_phiHom B hK hQ) :=
  surjective_of_card_ker _ hD8 (card_zpowers_prod_eq_four hQ.inv.sq hQ.inv.ne_one)
    (deb_card_ker_phiHom_le B hK hQ)

private theorem deb_exists_dComm_pair (B : DEBase Ω) (hD8 : Nat.card (zGroup Ω) = 8)
    {K : Subgroup G} (hK : K ∈ Ω) {z i j : G} (hQ : Q8Data K z i j) {p q : G}
    (hp : p = 1 ∨ p = z) (hq : q = 1 ∨ q = z) :
    ∃ d ∈ zGroup Ω, dComm d i = p ∧ dComm d j = q := by
  obtain ⟨d, hd⟩ := deb_phiHom_surjective B hD8 hK hQ
    ⟨⟨p, deb_mem_zpowers_of hp⟩, ⟨q, deb_mem_zpowers_of hq⟩⟩
  exact ⟨d, d.2, congrArg (fun y => (y.1 : G)) (congrArg Prod.fst hd),
    congrArg (fun y => (y.1 : G)) (congrArg Prod.snd hd)⟩

private theorem deb_eq_one_or_eq_of_centralizes_zGroup (B : DEBase Ω)
    (hD8 : Nat.card (zGroup Ω) = 8) {K : Subgroup G} (hK : K ∈ Ω) {z i j : G}
    (hQ : Q8Data K z i j) {x : G} (hxK : x ∈ K) (hx : ∀ d ∈ zGroup Ω, d * x = x * d) :
    x = 1 ∨ x = z := by
  obtain ⟨d₁, hd₁, e1, e2⟩ := deb_exists_dComm_pair B hD8 hK hQ (p := z) (q := 1)
    (Or.inr rfl) (Or.inl rfl)
  obtain ⟨d₂, hd₂, e3, e4⟩ := deb_exists_dComm_pair B hD8 hK hQ (p := 1) (q := z)
    (Or.inl rfl) (Or.inr rfl)
  have hN1 := B.dNorm K hK hd₁
  have hN2 := B.dNorm K hK hd₂
  have c1 : dComm d₁ x = 1 := dComm_eq_one_iff.mpr (hx d₁ hd₁)
  have c2 : dComm d₂ x = 1 := dComm_eq_one_iff.mpr (hx d₂ hd₂)
  have hz1 := hQ.inv.ne_one
  rcases hQ.nf x hxK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · rw [e1] at c1
    exact absurd c1 hz1
  · rw [dComm_mul_right hQ.inv hQ.inv.mem hQ.mem_i hN1
      (deb_dComm_eq_one_or B hK hQ.inv hd₁ hQ.mem_i), dComm_z hQ.inv hN1, e1, one_mul] at c1
    exact absurd c1 hz1
  · rw [e4] at c2
    exact absurd c2 hz1
  · rw [dComm_mul_right hQ.inv hQ.inv.mem hQ.mem_j hN2
      (deb_dComm_eq_one_or B hK hQ.inv hd₂ hQ.mem_j), dComm_z hQ.inv hN2, e4, one_mul] at c2
    exact absurd c2 hz1
  · rw [dComm_mul_right hQ.inv hQ.mem_i hQ.mem_j hN1
      (deb_dComm_eq_one_or B hK hQ.inv hd₁ hQ.mem_j), e1, e2, mul_one] at c1
    exact absurd c1 hz1
  · rw [dComm_mul_right hQ.inv hQ.inv.mem (K.mul_mem hQ.mem_i hQ.mem_j) hN1
      (deb_dComm_eq_one_or B hK hQ.inv hd₁ (K.mul_mem hQ.mem_i hQ.mem_j)),
      dComm_z hQ.inv hN1, dComm_mul_right hQ.inv hQ.mem_i hQ.mem_j hN1
      (deb_dComm_eq_one_or B hK hQ.inv hd₁ hQ.mem_j), e1, e2, mul_one, one_mul] at c1
    exact absurd c1 hz1

private theorem deb_inf_centralizer_zGroup (B : DEBase Ω) (hD8 : Nat.card (zGroup Ω) = 8)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    K ⊓ Subgroup.centralizer (zGroup Ω : Set G) = Subgroup.zpowers z := by
  obtain ⟨i, j, hQ⟩ := deb_Q8Data B hK hz
  apply le_antisymm
  · rintro x ⟨hxK, hxC⟩
    have hx : ∀ d ∈ zGroup Ω, d * x = x * d :=
      fun d hd => Subgroup.mem_centralizer_iff.mp hxC d hd
    rcases deb_eq_one_or_eq_of_centralizes_zGroup B hD8 hK hQ hxK hx with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers z
  · rw [Subgroup.zpowers_le]
    have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hK, hz⟩
    exact ⟨hz.mem, Subgroup.mem_centralizer_iff.mpr fun d hd => deb_zGroup_comm B d hd z hzD⟩

private theorem deb_inf_pCore (B : DEBase Ω) (hD8 : Nat.card (zGroup Ω) = 8)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    K ⊓ pCore 2 G = Subgroup.zpowers z := by
  apply le_antisymm
  · rintro x ⟨hxK, hxP⟩
    have hxC : x ∈ K ⊓ Subgroup.centralizer (zGroup Ω : Set G) :=
      ⟨hxK, deb_pCore_le_centralizer_zGroup B hxP⟩
    rw [deb_inf_centralizer_zGroup B hD8 hK hz] at hxC
    exact hxC
  · rw [Subgroup.zpowers_le]
    have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, hK, hz⟩
    exact ⟨hz.mem, deb_zGroup_le_pCore B hzD⟩

private noncomputable def deb_kHom (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) {k : G} (hk : k ∈ K) :
    zGroup Ω →* ↥(Subgroup.zpowers z) where
  toFun d := ⟨dComm (d : G) k, deb_dComm_mem_zpowers B hK hz d.2 hk⟩
  map_one' := Subtype.ext (by simp [dComm])
  map_mul' a b := by
    apply Subtype.ext
    show dComm ((a * b : zGroup Ω) : G) k = dComm (a : G) k * dComm (b : G) k
    rw [Subgroup.coe_mul, dComm_mul_left hz (B.dNorm K hK a.2)
      (deb_dComm_eq_one_or B hK hz b.2 hk)]
    rcases deb_dComm_eq_one_or B hK hz b.2 hk with h1 | h1 <;>
      rcases deb_dComm_eq_one_or B hK hz a.2 hk with h2 | h2 <;> rw [h1, h2] <;> simp

private theorem deb_card_zGroup_inf_centralizer (B : DEBase Ω) (hD8 : Nat.card (zGroup Ω) = 8)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) {k : G} (hk : k ∈ K)
    (hkz : k ∉ Subgroup.zpowers z) :
    Nat.card ↥(zGroup Ω ⊓ Subgroup.centralizer ({k} : Set G)) = 4 := by
  set φ := deb_kHom B hK hz hk with hφ
  have hrange : φ.range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    rcases deb_mem_zpowers_involution hz hy with rfl | rfl
    · exact φ.range.one_mem
    · obtain ⟨d, hd, hdk⟩ : ∃ d ∈ zGroup Ω, dComm d k ≠ 1 := by
        by_contra hcon
        push Not at hcon
        apply hkz
        have hC : k ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
          Subgroup.mem_centralizer_iff.mpr fun d hd => dComm_eq_one_iff.mp (hcon d hd)
        rw [← deb_inf_centralizer_zGroup B hD8 hK hz]
        exact ⟨hk, hC⟩
      refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
      exact (deb_dComm_eq_one_or B hK hz hd hk).resolve_left hdk
  have hindex : φ.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, card_zpowers_of_involution hz.sq hz.ne_one]
  have hk4 : Nat.card φ.ker = 4 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [hindex, hD8] at h1
    omega
  have hmap : φ.ker.map (zGroup Ω).subtype = zGroup Ω ⊓ Subgroup.centralizer ({k} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hyk : dComm (y : G) k = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      exact dComm_eq_one_iff.mp hyk
    · rintro ⟨hxD, hxC⟩
      refine ⟨⟨x, hxD⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      apply Subtype.ext
      exact dComm_eq_one_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hxC)
  rw [← hmap, Subgroup.card_map_of_injective (zGroup Ω).subtype_injective]
  exact hk4

private theorem deb_eq_of_dComm_eq (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {d d' : G} (hd : d ∈ zGroup Ω) (hd' : d' ∈ zGroup Ω)
    (hdd : ∀ k ∈ K, dComm d k = dComm d' k) : d' * d⁻¹ ∈ Subgroup.zpowers z := by
  have hsq : d⁻¹ = d := inv_eq_of_mul_eq_one_right (deb_zGroup_mul_self B d hd)
  rw [hsq]
  have hc : ∀ k ∈ K, d' * d * k = k * (d' * d) := by
    intro k hk
    rw [← dComm_eq_one_iff, dComm_mul_left hz (B.dNorm K hK hd')
      (deb_dComm_eq_one_or B hK hz hd hk), hdd k hk]
    rcases deb_dComm_eq_one_or B hK hz hd' hk with h1 | h1 <;> rw [h1] <;> simp [hz.sq]
  exact deb_mem_zpowers_of (deb_eq_one_or_eq_of_centralizes B hK hz
    ((zGroup Ω).mul_mem hd' hd) hc)

private theorem deb_exists_dComm_eq_hom (B : DEBase Ω) (hD8 : Nat.card (zGroup Ω) = 8)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (f : K →* ↥(Subgroup.zpowers z)) (hf : f ⟨z, hz.mem⟩ = 1) :
    ∃ d ∈ zGroup Ω, ∀ k : K, dComm d (k : G) = (f k : G) := by
  obtain ⟨i, j, hQ⟩ := deb_Q8Data B hK hz
  obtain ⟨iK, hiK⟩ : ∃ iK : K, (iK : G) = i := ⟨⟨i, hQ.mem_i⟩, rfl⟩
  obtain ⟨jK, hjK⟩ : ∃ jK : K, (jK : G) = j := ⟨⟨j, hQ.mem_j⟩, rfl⟩
  obtain ⟨zK, hzK⟩ : ∃ zK : K, (zK : G) = z := ⟨⟨z, hz.mem⟩, rfl⟩
  have hfiK : (f iK : G) = 1 ∨ (f iK : G) = z := deb_mem_zpowers_involution hz (f iK).2
  have hfjK : (f jK : G) = 1 ∨ (f jK : G) = z := deb_mem_zpowers_involution hz (f jK).2
  obtain ⟨d, hd, hdi, hdj⟩ := deb_exists_dComm_pair B hD8 hK hQ hfiK hfjK
  refine ⟨d, hd, ?_⟩
  have hdN : d ∈ Subgroup.normalizer (K : Set G) := B.dNorm K hK hd
  have hmulD : ∀ x y : K, dComm d ((x * y : K) : G) = dComm d (x : G) * dComm d (y : G) := by
    intro x y
    rw [Subgroup.coe_mul]
    exact dComm_mul_right hz x.2 y.2 hdN (deb_dComm_eq_one_or B hK hz hd y.2)
  have hzK' : zK = ⟨z, hz.mem⟩ := Subtype.ext hzK
  have hdz : dComm d (zK : G) = 1 := by
    rw [hzK]
    exact dComm_z hz hdN
  have hfz : (f zK : G) = 1 := by
    simp [hzK', hf]
  have hdi' : dComm d (iK : G) = (f iK : G) := by
    rw [hiK]
    exact hdi
  have hdj' : dComm d (jK : G) = (f jK : G) := by
    rw [hjK]
    exact hdj
  have hnf : ∀ k : K, k = 1 ∨ k = zK ∨ k = iK ∨ k = zK * iK ∨ k = jK ∨ k = zK * jK ∨
      k = iK * jK ∨ k = zK * (iK * jK) := by
    intro k
    rcases hQ.nf k.1 k.2 with h | h | h | h | h | h | h | h
    · left
      exact Subtype.ext (by simp [h])
    · right; left
      exact Subtype.ext (by simp [h, hzK])
    · right; right; left
      exact Subtype.ext (by simp [h, hiK])
    · right; right; right; left
      exact Subtype.ext (by simp [h, hzK, hiK, Subgroup.coe_mul])
    · right; right; right; right; left
      exact Subtype.ext (by simp [h, hjK])
    · right; right; right; right; right; left
      exact Subtype.ext (by simp [h, hzK, hjK, Subgroup.coe_mul])
    · right; right; right; right; right; right; left
      exact Subtype.ext (by simp [h, hiK, hjK, Subgroup.coe_mul])
    · right; right; right; right; right; right; right
      exact Subtype.ext (by simp [h, hzK, hiK, hjK, Subgroup.coe_mul])
  intro k
  rcases hnf k with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [dComm]
  · simp [hdz, hfz]
  · exact hdi'
  · rw [hmulD, hdz, hdi', map_mul, Subgroup.coe_mul, hfz, one_mul]
  · exact hdj'
  · rw [hmulD, hdz, hdj', map_mul, Subgroup.coe_mul, hfz, one_mul]
  · rw [hmulD, hdi', hdj', map_mul, Subgroup.coe_mul]
  · rw [hmulD, hmulD, hdz, hdi', hdj', map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      hfz, one_mul]

private theorem deb_centralizes_of_basis {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {x : G} (h1 : ∀ m : Fin 3, x * e m = e m * x) :
    x ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
  obtain ⟨v, rfl⟩ := TL4.exists_e8Coord_eq he hd
  have hc : ∀ m : Fin 3, Commute x (e m) := fun m => h1 m
  unfold TL4.e8Coord
  exact ((((hc 0).pow_right _).mul_right ((hc 1).pow_right _)).mul_right
    ((hc 2).pow_right _)).symm.eq

private noncomputable def deb_psiHom (B : DEBase Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) {d₁ d₂ : G} (hd₁ : d₁ ∈ zGroup Ω)
    (hd₂ : d₂ ∈ zGroup Ω) : K →* ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z) where
  toFun x := (⟨dComm (x : G) d₁, deb_mem_zpowers_of (deb_dComm_left_mem B hK hz x.2 hd₁)⟩,
    ⟨dComm (x : G) d₂, deb_mem_zpowers_of (deb_dComm_left_mem B hK hz x.2 hd₂)⟩)
  map_one' := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show dComm ((1 : K) : G) d₁ = 1
      simp [dComm]
    · show dComm ((1 : K) : G) d₂ = 1
      simp [dComm]
  map_mul' a b := by
    have hb₁ := deb_dComm_left_mem B hK hz b.2 hd₁
    have hb₂ := deb_dComm_left_mem B hK hz b.2 hd₂
    have ha₁ := deb_dComm_left_mem B hK hz a.2 hd₁
    have ha₂ := deb_dComm_left_mem B hK hz a.2 hd₂
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show dComm ((a * b : K) : G) d₁ = dComm (a : G) d₁ * dComm (b : G) d₁
      rw [Subgroup.coe_mul, deb_dComm_mul_left_K hz a.2 hb₁]
      rcases hb₁ with e | e <;> rcases ha₁ with e' | e' <;> rw [e, e'] <;> simp [hz.sq]
    · show dComm ((a * b : K) : G) d₂ = dComm (a : G) d₂ * dComm (b : G) d₂
      rw [Subgroup.coe_mul, deb_dComm_mul_left_K hz a.2 hb₂]
      rcases hb₂ with e | e <;> rcases ha₂ with e' | e' <;> rw [e, e'] <;> simp [hz.sq]

private theorem deb_card_ker_psiHom_le (B : DEBase Ω) (hD8 : Nat.card (zGroup Ω) = 8)
    {K : Subgroup G} (hK : K ∈ Ω) {z a b : G} (hQ : Q8Data K z a b) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) {i j k : Fin 3} (hi : e i = z) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    Nat.card (deb_psiHom B hK hQ.inv (he.mem j) (he.mem k)).ker ≤ 2 := by
  have key : ∀ x : K, deb_psiHom B hK hQ.inv (he.mem j) (he.mem k) x = 1 →
      (x : G) = 1 ∨ (x : G) = z := by
    intro x hx
    have hxj : dComm (x : G) (e j) = 1 := congrArg Subtype.val (congrArg Prod.fst hx)
    have hxk : dComm (x : G) (e k) = 1 := congrArg Subtype.val (congrArg Prod.snd hx)
    have hxz : (x : G) * z = z * (x : G) := isUniqueInvolution_comm hQ.inv x.2
    have hcomm : ∀ m : Fin 3, (x : G) * e m = e m * (x : G) := by
      intro m
      rcases fin3_cover i j k m hij hik.symm hjk.symm with rfl | rfl | rfl
      · rw [hi]
        exact hxz
      · exact dComm_eq_one_iff.mp hxj
      · exact dComm_eq_one_iff.mp hxk
    have hC : (x : G) ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
      deb_centralizes_of_basis he (fun m => hcomm m)
    exact deb_eq_one_or_eq_of_centralizes_zGroup B hD8 hK hQ x.2
      (fun d hd => (Subgroup.mem_centralizer_iff.mp hC) d hd)
  have hmem : ∀ x : (deb_psiHom B hK hQ.inv (he.mem j) (he.mem k)).ker,
      ((x : K) : G) ∈ Subgroup.zpowers z := by
    intro x
    exact deb_mem_zpowers_of (key x.1 (MonoidHom.mem_ker.mp x.2))
  have hinj : Function.Injective (fun x : (deb_psiHom B hK hQ.inv (he.mem j) (he.mem k)).ker =>
      (⟨((x : K) : G), hmem x⟩ : ↥(Subgroup.zpowers z))) := by
    intro x y hxy
    have hval : ((x.1 : K) : G) = ((y.1 : K) : G) := by
      have := congrArg Subtype.val hxy
      simpa using this
    exact Subtype.ext (Subtype.ext hval)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [card_zpowers_of_involution hQ.inv.sq hQ.inv.ne_one] at this

private theorem deb_psiHom_surjective (B : DEBase Ω) (hD8 : Nat.card (zGroup Ω) = 8)
    {K : Subgroup G} (hK : K ∈ Ω) {z a b : G} (hQ : Q8Data K z a b) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) {i j k : Fin 3} (hi : e i = z) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    Function.Surjective (deb_psiHom B hK hQ.inv (he.mem j) (he.mem k)) :=
  surjective_of_card_ker _ (B.card K hK) (card_zpowers_prod_eq_four hQ.inv.sq hQ.inv.ne_one)
    (deb_card_ker_psiHom_le B hD8 hK hQ he hi hij hik hjk)

private theorem deb_conjMat_eq_transvection {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {x : G}
    (hxN : ∀ y ∈ zGroup Ω, x * y * x⁻¹ ∈ zGroup Ω) (hxj : dComm x (e j) = e i)
    (hxk : dComm x (e k) = 1) (hxi : dComm x (e i) = 1) :
    TL4.conjMat he x = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j 1 := by
  have hcol : ∀ c : Fin 3, x * e c * x⁻¹ =
      TL4.e8Coord e ((if c = j then Pi.single i 1 else 0) + Pi.single c 1) := by
    intro c
    by_cases hc : c = j
    · rw [hc, if_pos rfl, TL4.e8Coord_add he, TL4.e8Coord_single, TL4.e8Coord_single]
      have e1 : x * e j * x⁻¹ = dComm x (e j) * e j := by unfold dComm; group
      rw [e1, hxj]
    · rw [if_neg hc, zero_add, TL4.e8Coord_single]
      rcases fin3_cover i j k c hij hik.symm hjk.symm with rfl | rfl | rfl
      · have e1 : x * e c * x⁻¹ = dComm x (e c) * e c := by unfold dComm; group
        rw [e1, hxi, one_mul]
      · exact absurd rfl hc
      · have e1 : x * e c * x⁻¹ = dComm x (e c) * e c := by unfold dComm; group
        rw [e1, hxk, one_mul]
  have hcm : ∀ r c, TL4.conjMat he x r c = TL4.e8Inv he (x * e c * x⁻¹) r := by
    intro r c
    have h1 := TL4.conj_e8Coord he hxN (Pi.single c 1)
    rw [TL4.e8Coord_single] at h1
    rw [h1, TL4.e8Inv_e8Coord he, Matrix.mulVec_single_one]
    rfl
  ext r c
  rw [hcm, hcol c, TL4.e8Inv_e8Coord he]
  clear hcm hcol hxN hxj hxk hxi
  revert hij
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases c <;> decide

end Common

namespace EndHyp

variable {Ω : Set (Subgroup G)} (h : EndHyp Ω)
include h

theorem eGroup_le_normalizer_self {K : Subgroup G} (hK : K ∈ Ω) :
    eGroup Ω K ≤ Subgroup.normalizer (K : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro u ⟨J, hJ, hu⟩
  rcases hJ with rfl | hJ
  · exact Subgroup.le_normalizer hu.mem
  · obtain ⟨U, hU, hUJ, hUN⟩ := hJ.2.2
    have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet h.thmD.hyp hU
    obtain ⟨-, -, -, -, -, -, hcyc, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet h.thmD.hyp hU
    obtain ⟨w, hwU, hww⟩ :=
      CFSG.ClassicalInvolution.Asc77.T3.exists_sq_eq_of_cyclic hu hUJ hcyc hU2 h4
    rw [← hww]
    exact (Subgroup.normalizer (K : Set G)).mul_mem (hUN hwU) (hUN hwU)

theorem dEHyp_of_zGroup_eq (h9 : Perp9 Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hDE : zGroup Ω = eGroup Ω K) : DEHyp Ω := by
  have hnorm : (zGroup Ω).Normal := deb_zGroup_normal_of h.thmD.hyp.conjInvariant
  have hdN : ∀ L ∈ Ω, zGroup Ω ≤ Subgroup.normalizer (L : Set G) := by
    intro L hL
    obtain ⟨g, hg⟩ := h.thmD.trans K hK L hL
    have hDL : zGroup Ω = eGroup Ω L := by
      calc zGroup Ω = conjSub g (zGroup Ω) := (deb_conjSub_eq_of_normal hnorm g).symm
        _ = conjSub g (eGroup Ω K) := by rw [hDE]
        _ = eGroup Ω (conjSub g K) := (h.eGroup_conj hK g).symm
        _ = eGroup Ω L := by rw [hg]
    rw [hDL]
    exact h.eGroup_le_normalizer_self hL
  have hB : DEBase Ω :=
    ⟨h.thmD.hyp, h.thmD.two, fun J hJ => h.card_eq_eight hJ, h.thmD.inO2, h9, hdN⟩
  have hle8 : Nat.card (zGroup Ω) ≤ 8 := deb_card_zGroup_le hB hK
  have hge8 : 8 ≤ Nat.card (zGroup Ω) := by
    rw [hDE]
    exact h.eight_le_card_eGroup h9 hK
  exact ⟨h.thmD.hyp, h.thmD.two, fun J hJ => h.card_eq_eight hJ, h.thmD.gen, h.thmD.trans,
    h.center, h.thmD.inO2, h9, hdN, le_antisymm hle8 hge8⟩

end EndHyp

namespace DEHyp

variable {Ω : Set (Subgroup G)} (h : DEHyp Ω)
include h

theorem exists_isUniqueInvolution {L : Subgroup G} (hL : L ∈ Ω) :
    ∃ z : G, IsUniqueInvolution L z :=
  Sec6Gen.exists_uniqueInvolution h.hyp hL

theorem isQuatSub_of_mem {L : Subgroup G} (hL : L ∈ Ω) : IsQuatSub L :=
  deb_isQuatSub (deb_of h) hL

theorem exists_ne : ∃ L ∈ Ω, ∃ L' ∈ Ω, L ≠ L' := by
  by_contra hcon
  push Not at hcon
  rcases Set.eq_empty_or_nonempty Ω with hΩ | ⟨L0, hL0⟩
  · have hS : {u : G | ∃ L ∈ Ω, IsUniqueInvolution L u} = ∅ := by
      ext u
      simp [hΩ]
    have hD : zGroup Ω = ⊥ := by
      unfold zGroup
      rw [hS, Subgroup.closure_empty]
    have h8 := h.card_zGroup
    rw [hD, Subgroup.card_bot] at h8
    norm_num at h8
  · obtain ⟨z0, hz0⟩ := h.exists_isUniqueInvolution hL0
    have hsub : {u : G | ∃ L ∈ Ω, IsUniqueInvolution L u} ⊆ {z0} := by
      rintro u ⟨L, hL, hu⟩
      rw [hcon L hL L0 hL0] at hu
      exact hu.eq hz0
    have hle : zGroup Ω ≤ Subgroup.zpowers z0 := by
      refine (Subgroup.closure_le _).mpr ?_
      intro u hu
      have hu' : u = z0 := hsub hu
      rw [hu']
      exact Subgroup.mem_zpowers z0
    have h8 := Subgroup.card_le_of_le hle
    rw [h.card_zGroup, card_zpowers_of_involution hz0.sq hz0.ne_one] at h8
    norm_num at h8

theorem zGroup_normal : (zGroup Ω).Normal :=
  deb_zGroup_normal (deb_of h)

theorem zGroup_le_pCore : zGroup Ω ≤ pCore 2 G :=
  deb_zGroup_le_pCore (deb_of h)

theorem zGroup_comm : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a :=
  deb_zGroup_comm (deb_of h)

theorem zGroup_mul_self : ∀ a ∈ zGroup Ω, a * a = 1 :=
  deb_zGroup_mul_self (deb_of h)

theorem pCore_le_centralizer_zGroup : pCore 2 G ≤ Subgroup.centralizer (zGroup Ω : Set G) :=
  deb_pCore_le_centralizer_zGroup (deb_of h)

theorem exists_not_commute_of_ne {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω) {a b : G}
    (ha : IsUniqueInvolution K a) (hb : IsUniqueInvolution L b) (hab : a ≠ b) :
    ∃ x ∈ K, b * x ≠ x * b :=
  deb_exists_not_commute_of_ne (deb_of h) hK hL ha hb hab

theorem mem_zGroup_iff {x : G} :
    x ∈ zGroup Ω ↔ x = 1 ∨ ∃ L ∈ Ω, IsUniqueInvolution L x :=
  deb_mem_zGroup_iff (deb_of h)

theorem dComm_mem_zpowers {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {d k : G} (hd : d ∈ zGroup Ω) (hk : k ∈ K) : dComm d k ∈ Subgroup.zpowers z :=
  deb_dComm_mem_zpowers (deb_of h) hK hz hd hk

theorem inf_centralizer_zGroup {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) :
    K ⊓ Subgroup.centralizer (zGroup Ω : Set G) = Subgroup.zpowers z :=
  deb_inf_centralizer_zGroup (deb_of h) h.card_zGroup hK hz

theorem inf_pCore {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) :
    K ⊓ pCore 2 G = Subgroup.zpowers z :=
  deb_inf_pCore (deb_of h) h.card_zGroup hK hz

theorem card_zGroup_inf_centralizer {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {k : G} (hk : k ∈ K) (hkz : k ∉ Subgroup.zpowers z) :
    Nat.card ↥(zGroup Ω ⊓ Subgroup.centralizer {k}) = 4 :=
  deb_card_zGroup_inf_centralizer (deb_of h) h.card_zGroup hK hz hk hkz

theorem eq_of_dComm_eq {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {d d' : G} (hd : d ∈ zGroup Ω) (hd' : d' ∈ zGroup Ω)
    (hdd : ∀ k ∈ K, dComm d k = dComm d' k) : d' * d⁻¹ ∈ Subgroup.zpowers z :=
  deb_eq_of_dComm_eq (deb_of h) hK hz hd hd' hdd

theorem exists_dComm_eq_hom {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    (f : K →* Subgroup.zpowers z) (hf : f ⟨z, hz.mem⟩ = 1) :
    ∃ d ∈ zGroup Ω, ∀ k : K, dComm d (k : G) = (f k : G) :=
  deb_exists_dComm_eq_hom (deb_of h) h.card_zGroup hK hz f hf

theorem exists_basis : ∃ e : Fin 3 → G, TL4.E8Basis (zGroup Ω) e :=
  TL4.exists_e8Basis (deb_zGroup_mul_self (deb_of h)) h.card_zGroup

@[expose] noncomputable def rhoD {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) :
    G →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) where
  toFun x := ⟨TL4.conjMat he x,
    TL4.det_conjMat he (fun y hy => h.zGroup_normal.conj_mem y hy x)
      (fun y hy => h.zGroup_normal.conj_mem y hy x⁻¹)⟩
  map_one' := Subtype.ext (TL4.conjMat_one he)
  map_mul' x y := Subtype.ext (TL4.conjMat_mul he
    (fun z hz => h.zGroup_normal.conj_mem z hz x)
    (fun z hz => h.zGroup_normal.conj_mem z hz y))

end DEHyp

private theorem deb_transvection_mem_range {Ω : Set (Subgroup G)} (h : DEHyp Ω)
    {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) {i j : Fin 3} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ (h.rhoD he).range := by
  obtain ⟨k, hki, hkj⟩ := fin3_third i j hij
  have hik : i ≠ k := fun e' => hki e'.symm
  have hjk : j ≠ k := fun e' => hkj e'.symm
  have hne1 : ∀ m, e m ≠ 1 := by
    intro m
    fin_cases m
    · exact he.ne0
    · exact he.ne1.1
    · exact he.ne2.1
  obtain ⟨K, hK, hKz⟩ : ∃ K ∈ Ω, IsUniqueInvolution K (e i) := by
    rcases (deb_mem_zGroup_iff (deb_of h)).mp (he.mem i) with h1 | h1
    · exact absurd h1 (hne1 i)
    · exact h1
  obtain ⟨a, b, hQ⟩ := deb_Q8Data (deb_of h) hK hKz
  obtain ⟨x, hx⟩ := deb_psiHom_surjective (deb_of h) h.card_zGroup hK hQ he rfl hij hik hjk
    (⟨⟨e i, Subgroup.mem_zpowers _⟩, ⟨1, Subgroup.one_mem _⟩⟩)
  have hxj : dComm (x : G) (e j) = e i := congrArg Subtype.val (congrArg Prod.fst hx)
  have hxk : dComm (x : G) (e k) = 1 := congrArg Subtype.val (congrArg Prod.snd hx)
  have hxi : dComm (x : G) (e i) = 1 := by
    rw [dComm_eq_one_iff]
    exact isUniqueInvolution_comm hQ.inv x.2
  refine ⟨(x : G), Subtype.ext ?_⟩
  change TL4.conjMat he (x : G) = _
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  exact deb_conjMat_eq_transvection he hij hik hjk
    (fun y hy => (deb_zGroup_normal (deb_of h)).conj_mem y hy x) hxj hxk hxi

namespace DEHyp

variable {Ω : Set (Subgroup G)} (h : DEHyp Ω)
include h

theorem rhoD_ker {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) :
    (h.rhoD he).ker = Subgroup.centralizer (zGroup Ω : Set G) := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hc : TL4.conjMat he x = 1 := congrArg Subtype.val hx
    refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
    obtain ⟨v, rfl⟩ := TL4.exists_e8Coord_eq he hd
    have h1 := TL4.conj_e8Coord he (fun y hy => h.zGroup_normal.conj_mem y hy x) v
    rw [hc, Matrix.one_mulVec] at h1
    calc TL4.e8Coord e v * x = (x * TL4.e8Coord e v * x⁻¹) * x := by rw [h1]
      _ = x * TL4.e8Coord e v := by group
  · intro hx
    apply Subtype.ext
    show TL4.conjMat he x = 1
    refine TL4.matrix_ext_mulVec fun v => ?_
    rw [Matrix.one_mulVec]
    refine TL4.e8Coord_injective he ?_
    rw [← TL4.conj_e8Coord he (fun y hy => h.zGroup_normal.conj_mem y hy x) v]
    have hcomm := Subgroup.mem_centralizer_iff.mp hx (TL4.e8Coord e v) (TL4.e8Coord_mem he v)
    rw [← hcomm]
    group

theorem rhoD_range {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) :
    (h.rhoD he).range = ⊤ := by
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 3) (K := ZMod 2), Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  obtain ⟨i, j, hij, c⟩ := t
  rcases TL4.zmod_two_cases c with rfl | rfl
  · rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
    exact (h.rhoD he).range.one_mem
  · rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    exact deb_transvection_mem_range h he hij

theorem centralizer_zGroup_normal : (Subgroup.centralizer (zGroup Ω : Set G)).Normal := by
  refine ⟨fun c hc g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro d hd
  have hd' : g⁻¹ * d * g ∈ zGroup Ω := by
    have := h.zGroup_normal.conj_mem d hd g⁻¹
    rwa [inv_inv] at this
  have key := hc _ hd'
  calc d * (g * c * g⁻¹) = g * ((g⁻¹ * d * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * d * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * d := by group

theorem index_centralizer_zGroup : (Subgroup.centralizer (zGroup Ω : Set G)).index = 168 := by
  obtain ⟨e, he⟩ := h.exists_basis
  rw [← h.rhoD_ker he, Subgroup.index_ker, h.rhoD_range he, Subgroup.card_top,
    TL4.card_sl3Two]

theorem exists_conj_involution {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) {u u' : G}
    (hu : IsUniqueInvolution L u) (hu' : IsUniqueInvolution L' u') :
    ∃ g : G, g * u * g⁻¹ = u' := by
  obtain ⟨g, hg⟩ := h.trans L hL L' hL'
  refine ⟨g, ?_⟩
  have h1 : IsUniqueInvolution L' (g * u * g⁻¹) := by
    rw [← hg]
    exact hu.conj g
  exact (hu'.eq h1).symm

theorem card_zGroup_ne_one : Nat.card {x : zGroup Ω // x ≠ 1} = 7 := by
  classical
  have e := Nat.card_congr (Equiv.optionSubtypeNe (1 : zGroup Ω))
  rw [Finite.card_option, h.card_zGroup] at e
  omega

end DEHyp

end CFSG.ClassicalInvolution.Q3.Sec13
