module

public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscL62Pair
public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetupFrame

public section

namespace CFSG.ClassicalInvolution.NDB.Lift

open CFSG.ClassicalInvolution.Generic

section Odd

variable {H : Type} [Group H] [Finite H]

theorem exists_conj_le_of_le_sup {X N S : Subgroup H} [N.Normal] (hN : Odd (Nat.card N))
    (hS : IsPGroup 2 S) (hSXN : S ≤ X ⊔ N) : ∃ n ∈ N, S ≤ conjSub n X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup H := X ⊔ N with hB
  have hodd : Odd (X.subgroupOf B).index :=
    hN.of_dvd_nat (Asc77.relIndex_sup_dvd_card_of_normal X N)
  have hS' : IsPGroup 2 ↥(S.subgroupOf B) := hS.comap_subtype
  have hcard : ¬ 2 ∣ Nat.card (↥B ⧸ X.subgroupOf B) := fun h =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  obtain ⟨c, hc⟩ := hS'.nonempty_fixed_point_of_prime_not_dvd_card (↥B ⧸ X.subgroupOf B) hcard
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective c
  have hbS : S ≤ conjSub (b : H) X := by
    intro s hs
    have hsB : s ∈ B := hSXN hs
    have h1 := hc ⟨⟨s, hsB⟩, Subgroup.mem_subgroupOf.mpr hs⟩
    have h2 : (((⟨s, hsB⟩ : ↥B) * b : ↥B) : ↥B ⧸ X.subgroupOf B) =
        (b : ↥B ⧸ X.subgroupOf B) := h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
    rw [mem_conjSub_iff]
    have h3 : (b : H)⁻¹ * s⁻¹ * b ∈ X := by simpa [mul_assoc] using h2
    have h4 := X.inv_mem h3
    simpa [mul_assoc] using h4
  have hbB : (b : H) ∈ (↑(N ⊔ X) : Set H) := by
    rw [sup_comm]
    exact b.2
  rw [Subgroup.normal_mul] at hbB
  obtain ⟨n, hn, x, hx, hnx⟩ := hbB
  refine ⟨n, hn, ?_⟩
  rw [← hnx, conjSub_mul, conjSub_eq_self_of_mem hx] at hbS
  exact hbS

theorem inf_eq_bot_of_isPGroup {N P : Subgroup H} (hN : Odd (Nat.card N)) (hP : IsPGroup 2 P) :
    N ⊓ P = ⊥ := by
  have h1 : IsPGroup 2 ↥(N ⊓ P) := hP.to_le inf_le_right
  obtain ⟨k, hk⟩ := h1.exists_card_eq
  have h3 : Odd (Nat.card ↥(N ⊓ P)) := hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  rw [hk] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr h3) (even_iff_two_dvd.mpr (dvd_pow_self 2 hk0))
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])

theorem injOn_of_isPGroup (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N)) {P : Subgroup H}
    (hP : IsPGroup 2 P) {a b : H} (ha : a ∈ P) (hb : b ∈ P)
    (h : QuotientGroup.mk' N a = QuotientGroup.mk' N b) : a = b := by
  have h1 : a⁻¹ * b ∈ N := QuotientGroup.eq.mp h
  have h3 : a⁻¹ * b ∈ N ⊓ P := ⟨h1, P.mul_mem (P.inv_mem ha) hb⟩
  rw [inf_eq_bot_of_isPGroup hN hP, Subgroup.mem_bot] at h3
  exact inv_mul_eq_one.mp h3

theorem natCard_map_of_isPGroup (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N))
    {P : Subgroup H} (hP : IsPGroup 2 P) :
    Nat.card ↥(P.map (QuotientGroup.mk' N)) = Nat.card P := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp P.subtype) := fun a b h =>
    Subtype.ext (injOn_of_isPGroup N hN hP a.2 b.2 h)
  have e : P.map (QuotientGroup.mk' N) = ((QuotientGroup.mk' N).comp P.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [e]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem exists_lift_ge (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N))
    {Q : Subgroup (H ⧸ N)} (hQ : IsPGroup 2 Q) {T : Subgroup H} (hT : IsPGroup 2 T)
    (hTQ : T.map (QuotientGroup.mk' N) ≤ Q) :
    ∃ P : Subgroup H, IsPGroup 2 P ∧ T ≤ P ∧ P.map (QuotientGroup.mk' N) = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := Q.comap (QuotientGroup.mk' N) with hW
  obtain ⟨P, hP, hTP⟩ := Asc77.IsSylow2In.exists_ge hT (Subgroup.map_le_iff_le_comap.mp hTQ)
  refine ⟨P, hP.2.1, hTP, ?_⟩
  have hPQ : P.map (QuotientGroup.mk' N) ≤ Q := Subgroup.map_le_iff_le_comap.mpr hP.1
  have hWQ : W.map (QuotientGroup.mk' N) = Q :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Q
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hrel : N.relIndex W = Nat.card Q := by
    have h := Subgroup.relIndex_ker W (QuotientGroup.mk' N)
    rwa [QuotientGroup.ker_mk', hWQ] at h
  have hdvd : 2 ^ k ∣ Nat.card W := by
    rw [← hk, ← hrel, ← Subgroup.relIndex_mul_card N W]
    exact Dvd.intro _ rfl
  obtain ⟨W0, hW0⟩ := Sylow.exists_subgroup_card_pow_prime (G := W) 2 hdvd
  have hVcard : Nat.card ↥(W0.map W.subtype) = 2 ^ k := by
    rw [Subgroup.card_map_of_injective W.subtype_injective, hW0]
  have hle := hP.natCard_le (IsPGroup.of_card hVcard) (Subgroup.map_subtype_le W0)
  refine Subgroup.eq_of_le_of_card_ge hPQ ?_
  rw [natCard_map_of_isPGroup N hN hP.2.1, hk, ← hVcard]
  exact hle

end Odd

theorem isPGroup_sup_of_commute {M : Type*} [Group M] {A B : Subgroup M} (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsPGroup 2 ↥(A ⊔ B) :=
  hA.to_sup_of_normal_right' hB fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (hAB a ha b hb).symm)

section Quaternion

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem mem_of_isSylow2In {K : Subgroup G} {z : G} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hz : IsClassicalMember p f K z) {T : Subgroup G} (hT : Asc77.IsSylow2In T K) : z ∈ T := by
  have hU := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz.orderOf_eq_two, pow_one])
  obtain ⟨T', hT', hzT'⟩ := Asc77.IsSylow2In.exists_ge hz2 (Subgroup.zpowers_le.mpr hz.mem)
  have hT2 : 2 ≤ Nat.card T := by
    rw [hT.natCard_eq hT']
    calc 2 = Nat.card (Subgroup.zpowers z) := by rw [Nat.card_zpowers, hz.orderOf_eq_two]
      _ ≤ Nat.card T' := Subgroup.card_le_of_le hzT'
  exact Asc77.AscL62.mem_of_uniqueInvolution_of_pGroup hU hT.1 hT.2.1 hT2

theorem exists_sq_eq_of_isSylow2In {K : Subgroup G} {z : G} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hz : IsClassicalMember p f K z) {T : Subgroup G} (hT : Asc77.IsSylow2In T K) :
    ∃ t w : G, t ∈ T ∧ w ∈ T ∧ t * t = z ∧ w * t = t * z * w := by
  classical
  have hzT := mem_of_isSylow2In hp2 hq hz hT
  let S : Sylow 2 ↥K :=
    { toSubgroup := T.subgroupOf K
      isPGroup' := hT.2.1.comap_subtype
      is_maximal' := by
        intro Q hQ hle
        have hVQ : T ≤ Q.map K.subtype := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hT.1]
          exact Subgroup.map_mono hle
        have := hT.2.2 (Q.map K.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
        rw [← Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q, this]
        rfl }
  set z' : ↥K := ⟨z, hz.mem⟩ with hz'
  have hz'2 : orderOf z' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz.orderOf_eq_two
  have hzS : z' ∈ (S : Subgroup ↥K) := Subgroup.mem_subgroupOf.mpr hzT
  obtain ⟨r, hr, ⟨e⟩⟩ :=
    CFSG.ClassicalInvolution.Disconnected.quaternion_sylow_of_isClassicalMember hp2 hq hz S
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℕ, 0 < m ∧ 2 ^ (r - 2) = 2 * m := by
    refine ⟨2 ^ (r - 3), pow_pos (by norm_num) _, ?_⟩
    have : r - 2 = (r - 3) + 1 := by omega
    rw [this, pow_succ]
    ring
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  obtain ⟨hsq, hcomm⟩ := TypeCSetup.quaternion_aux (2 ^ (r - 2)) m hm
  set zT : ↥(S : Subgroup ↥K) := ⟨z', hzS⟩ with hzT'
  have hzT2 : orderOf zT = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz'2
  have hez : e zT = QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) :=
    CFSG.ClassicalInvolution.QuaternionStructure.quaternionGroup_eq_a_of_orderOf_eq_two
      ((e.orderOf_eq zT).trans hzT2)
  have h1 : e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.xa 0) = zT := by
    apply e.injective
    rw [map_mul, MulEquiv.apply_symm_apply, hsq, hez]
  have h2 : e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2)))) *
      e.symm (QuaternionGroup.xa 0) = e.symm (QuaternionGroup.xa 0) * zT *
        e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2)))) := by
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, hez]
    exact hcomm
  refine ⟨(((e.symm (QuaternionGroup.xa 0) : ↥(S : Subgroup ↥K)) : ↥K) : G),
    (((e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2)))) : ↥(S : Subgroup ↥K)) : ↥K) : G),
    Subgroup.mem_subgroupOf.mp (e.symm (QuaternionGroup.xa 0)).2,
    Subgroup.mem_subgroupOf.mp (e.symm (QuaternionGroup.a (m : ZMod (2 * 2 ^ (r - 2))))).2,
    ?_, ?_⟩
  · have := congrArg (fun x : ↥(S : Subgroup ↥K) => ((x : ↥K) : G)) h1
    simpa [zT, z'] using this
  · have := congrArg (fun x : ↥(S : Subgroup ↥K) => ((x : ↥K) : G)) h2
    simpa [zT, z', mul_assoc] using this

end Quaternion

end CFSG.ClassicalInvolution.NDB.Lift
