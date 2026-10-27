module

public import CFSG.CGT.Timmesfeld75.NormalClosure
public import CFSG.CGT.Timmesfeld75.StrongClosure
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G] {T : Subgroup G}

section Generation

theorem classD_le_normalClosure {x : G} (hx : x ∈ classD T) :
    x ∈ Subgroup.normalClosure (T : Set G) := by
  obtain ⟨g, t, ht, -, rfl⟩ := hx
  have := Subgroup.normalClosure_normal.conj_mem t (Subgroup.le_normalClosure ht) g⁻¹
  simpa using this

theorem exists_mem_normalClosure_of_mem_classD [Finite G] (hT : StrongWC T) {x : G}
    (hx : x ∈ classD T) :
    ∃ k ∈ Subgroup.normalClosure (T : Set G), ∃ s ∈ T, s ≠ 1 ∧ x = k * s * k⁻¹ := by
  obtain ⟨g, t, ht, ht1, rfl⟩ := hx
  obtain ⟨k, hk, hkg⟩ := exists_mem_normalClosure_conj_eq hT.isWC g⁻¹
  have hmem : g⁻¹ * t * g ∈ conjSubgroup k T := by
    rw [← hkg, mem_conjSubgroup]
    simpa [mul_assoc] using ht
  refine ⟨k, hk, k⁻¹ * (g⁻¹ * t * g) * k, mem_conjSubgroup.1 hmem, fun h1 => ht1 ?_, by group⟩
  have h2 : g⁻¹ * t * g = 1 := by
    simpa [mul_assoc] using congrArg (fun z => k * z * k⁻¹) h1
  simpa [mul_assoc] using congrArg (fun z => g * z * g⁻¹) h2

theorem mul_comm_of_mem_normalClosure {n : G}
    (h : ∀ g : G, ∀ t ∈ T, n * (g * t * g⁻¹) = g * t * g⁻¹ * n) :
    ∀ k ∈ Subgroup.normalClosure (T : Set G), n * k = k * n := by
  have hle : Subgroup.normalClosure (T : Set G) ≤ Subgroup.centralizer ({n} : Set G) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h c a ha
  intro k hk
  exact Subgroup.mem_centralizer_iff.1 (hle hk) n (Set.mem_singleton n)

theorem inv_mul_mul_mem_of_mem_normalClosure {N : Subgroup G}
    (hNn : ∀ k ∈ Subgroup.normalClosure (T : Set G), ∀ n ∈ N, k * n * k⁻¹ ∈ N) {k n : G}
    (hk : k ∈ Subgroup.normalClosure (T : Set G)) (hn : n ∈ N) : k⁻¹ * n * k ∈ N := by
  simpa using hNn k⁻¹ ((Subgroup.normalClosure _).inv_mem hk) n hn

theorem le_normalizer_of_le_normalClosure {N S : Subgroup G}
    (hS : S ≤ Subgroup.normalClosure (T : Set G))
    (hNn : ∀ k ∈ Subgroup.normalClosure (T : Set G), ∀ n ∈ N, k * n * k⁻¹ ∈ N) :
    S ≤ Subgroup.normalizer (N : Set G) := fun s hs =>
  Subgroup.mem_normalizer_iff.2 fun h =>
    ⟨fun hh => hNn s (hS hs) h hh, fun hh => by
      simpa [mul_assoc] using hNn s⁻¹ ((Subgroup.normalClosure _).inv_mem (hS hs)) _ hh⟩

end Generation

section NotNormal

theorem not_central_of_mem_T [Finite G] (hT : StrongWC T)
    (hnT : ¬ ∀ g : G, conjSubgroup g T = T) {t : G} (ht : t ∈ T) (ht1 : t ≠ 1) :
    ∃ k ∈ Subgroup.normalClosure (T : Set G), t * k ≠ k * t := by
  by_contra hcon
  push Not at hcon
  refine hnT fun g => (hT.isWC.2 t ht ht1).2 g fun x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact hcon x (conjSubgroup_le_normalClosure T g hx)

theorem mul_comm_of_commutator_central [Finite G] (hT : StrongWC T)
    (hnT : ¬ ∀ g : G, conjSubgroup g T = T) {x y : G} (hy : y ∈ classD T)
    (hz : ∀ k ∈ Subgroup.normalClosure (T : Set G), ⁅x, y⁆ * k = k * ⁅x, y⁆) :
    x * y = y * x := by
  have hyy : y * y = 1 := classD_mul_self hT hy
  have hzy : ⁅x, y⁆ * y = y * ⁅x, y⁆ := hz y (classD_le_normalClosure hy)
  have hy'eq : ⁅x, y⁆ * y = x * y * x⁻¹ := by
    rw [commutatorElement_def, inv_mul_cancel_right]
  have hy'D : ⁅x, y⁆ * y ∈ classD T := by
    have := classD_conj hy x⁻¹
    rwa [inv_inv, ← hy'eq] at this
  have hy'y : ⁅x, y⁆ * y * y = y * (⁅x, y⁆ * y) := by
    rw [mul_assoc, hyy, mul_one, ← mul_assoc, ← hzy, mul_assoc, hyy, mul_one]
  by_contra hxy
  have hz1 : ⁅x, y⁆ ≠ 1 := fun h1 => hxy (commutatorElement_eq_one_iff_mul_comm.1 h1)
  generalize ⁅x, y⁆ = z at hz hy'D hy'y hz1 hzy
  obtain ⟨g, t, ht, ht1, hyg⟩ := hy
  have hty : t = g * y * g⁻¹ := by rw [hyg]; group
  subst hty
  have ht'D : g * (z * y) * g⁻¹ ∈ classD T := by
    have := classD_conj hy'D g⁻¹
    rwa [inv_inv] at this
  have htt' : g * (z * y) * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * (z * y) * g⁻¹) :=
    calc g * (z * y) * g⁻¹ * (g * y * g⁻¹) = g * (z * y * y) * g⁻¹ := by group
      _ = g * (y * (z * y)) * g⁻¹ := by rw [hy'y]
      _ = g * y * g⁻¹ * (g * (z * y) * g⁻¹) := by group
  have ht'T : g * (z * y) * g⁻¹ ∈ T := commute_classD_le hT ht ht1 ht'D htt'
  have hz'T : g * z * g⁻¹ ∈ T := by
    have := T.mul_mem ht'T (T.inv_mem ht)
    have e : g * (z * y) * g⁻¹ * (g * y * g⁻¹)⁻¹ = g * z * g⁻¹ := by group
    rwa [e] at this
  have hz'1 : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, h]
    group
  obtain ⟨k, hk, hne⟩ := not_central_of_mem_T hT hnT hz'T hz'1
  apply hne
  have hk' : g⁻¹ * k * g ∈ Subgroup.normalClosure (T : Set G) := by
    simpa using Subgroup.normalClosure_normal.conj_mem k hk g⁻¹
  have hzk := hz _ hk'
  calc g * z * g⁻¹ * k = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by rw [hzk]
    _ = k * (g * z * g⁻¹) := by group

theorem commute_of_comm_central [Finite G] (hT : StrongWC T)
    (hnT : ¬ ∀ g : G, conjSubgroup g T = T) {x y : G} (_hx : x ∈ classD T) (hy : y ∈ classD T)
    (hz : ∀ k ∈ Subgroup.normalClosure (T : Set G), ⁅x, y⁆ * k = k * ⁅x, y⁆) :
    x * y = y * x :=
  mul_comm_of_commutator_central hT hnT hy hz

end NotNormal

section TwoCore

theorem mul_comm_of_mem_classD_of_isPGroup [Finite G] (hT : StrongWC T) {N : Subgroup G}
    (hN2 : IsPGroup 2 N) {x y : G} (hx : x ∈ classD T) (hy : y ∈ classD T) (hxN : x ∈ N)
    (hyN : y ∈ N) : x * y = y * x := by
  have hxx : x * x = 1 := classD_mul_self hT hx
  have hyy : y * y = 1 := classD_mul_self hT hy
  refine (orderOf_mul_dvd_two_iff_commute hxx hyy).1 ?_
  rcases orderOf_mul_classD hT hx hy with h | hodd
  · exact h
  · obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hN2 ⟨x * y, N.mul_mem hxN hyN⟩
    rw [Subgroup.orderOf_mk] at hj
    have hj0 : j = 0 := by
      by_contra hj0
      rw [hj] at hodd
      exact Nat.not_even_iff_odd.2 hodd (Nat.even_pow.2 ⟨even_two, hj0⟩)
    rw [hj, hj0, pow_zero]
    exact one_dvd 2

theorem mem_normalizer_conjSubgroup_of_isPGroup [Finite G] (hT : StrongWC T) {N : Subgroup G}
    (hNn : ∀ k ∈ Subgroup.normalClosure (T : Set G), ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N) (g : G) {n : G} (hn : n ∈ N) :
    n ∈ Subgroup.normalizer (conjSubgroup g T : Set G) := by
  have hTK := conjSubgroup_le_normalClosure T g
  have hT'N := le_normalizer_of_le_normalClosure hTK hNn
  have hS : IsPGroup 2 (conjSubgroup g T ⊔ N : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right'
      (isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup hT.1 g)) hN2 hT'N
  refine mem_normalizer_iff_conjSubgroup_eq.2
    (eq_of_conj_le_pGroup (hT.isWC.conj g) hS le_sup_left fun x hx => ?_)
  have ht : n⁻¹ * x * n ∈ conjSubgroup g T := mem_conjSubgroup.1 hx
  have hw : (n⁻¹ * x * n)⁻¹ * n * (n⁻¹ * x * n) * n⁻¹ ∈ N :=
    N.mul_mem (inv_mul_mul_mem_of_mem_normalClosure hNn (hTK ht) hn) (N.inv_mem hn)
  have hx' : x = (n⁻¹ * x * n) * ((n⁻¹ * x * n)⁻¹ * n * (n⁻¹ * x * n) * n⁻¹) := by group
  rw [hx']
  exact Subgroup.mul_mem_sup ht hw

theorem not_mem_of_mem_T_of_isPGroup [Finite G] (hT : StrongWC T)
    (hnT : ¬ ∀ g : G, conjSubgroup g T = T) {N : Subgroup G}
    (hNn : ∀ k ∈ Subgroup.normalClosure (T : Set G), ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N) {t : G} (ht : t ∈ T) (ht1 : t ≠ 1) : t ∉ N := by
  intro htN
  have htD : t ∈ classD T := mem_classD_of_mem ht ht1
  have hconj : ∀ k ∈ Subgroup.normalClosure (T : Set G), conjSubgroup k T = T := by
    intro k hk
    refine hT.isWC.conj_eq_of_inf_ne_bot ?_
    rw [Ne, Subgroup.eq_bot_iff_forall]
    intro hbot
    refine ht1 (hbot t ⟨ht, mem_conjSubgroup.2 ?_⟩)
    have hsN : k⁻¹ * t * k ∈ N := inv_mul_mul_mem_of_mem_normalClosure hNn hk htN
    have hsD : k⁻¹ * t * k ∈ classD T := classD_conj htD k
    exact commute_classD_le hT ht ht1 hsD
      (mul_comm_of_mem_classD_of_isPGroup hT hN2 hsD htD hsN htN)
  refine hnT fun g => ?_
  obtain ⟨k, hk, hkg⟩ := exists_mem_normalClosure_conj_eq hT.isWC g
  rw [hkg, hconj k hk]

theorem not_mem_classD_of_isPGroup [Finite G] (hT : StrongWC T)
    (hnT : ¬ ∀ g : G, conjSubgroup g T = T) {N : Subgroup G}
    (hNn : ∀ k ∈ Subgroup.normalClosure (T : Set G), ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N) {x : G} (hx : x ∈ classD T) : x ∉ N := by
  intro hxN
  obtain ⟨k, hk, s, hs, hs1, rfl⟩ := exists_mem_normalClosure_of_mem_classD hT hx
  refine not_mem_of_mem_T_of_isPGroup hT hnT hNn hN2 hs hs1 ?_
  simpa [mul_assoc] using inv_mul_mul_mem_of_mem_normalClosure hNn hk hxN

theorem twoCore_le_center [Finite G] (hT : StrongWC T)
    (hnT : ¬ ∀ g : G, conjSubgroup g T = T) (N : Subgroup G)
    (_hNK : N ≤ Subgroup.normalClosure (T : Set G))
    (hNn : ∀ k ∈ Subgroup.normalClosure (T : Set G), ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hN2 : IsPGroup 2 N) :
    ∀ n ∈ N, ∀ k ∈ Subgroup.normalClosure (T : Set G), n * k = k * n := by
  intro n hn
  refine mul_comm_of_mem_normalClosure fun g t ht => ?_
  by_cases ht1 : t = 1
  · subst ht1
    simp
  have hdD : g * t * g⁻¹ ∈ classD T := ⟨g⁻¹, t, ht, ht1, by simp⟩
  have hdT' : g * t * g⁻¹ ∈ conjSubgroup g T := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using ht
  have hcT' : ⁅n, g * t * g⁻¹⁆ ∈ conjSubgroup g T :=
    comm_mem_of_mem_normalizer (mem_normalizer_conjSubgroup_of_isPGroup hT hNn hN2 g hn) hdT'
  have hcN : ⁅n, g * t * g⁻¹⁆ ∈ N := by
    have := N.mul_mem hn (hNn (g * t * g⁻¹) (conjSubgroup_le_normalClosure T g hdT') n⁻¹
      (N.inv_mem hn))
    simpa [commutatorElement_def, mul_assoc] using this
  by_contra hne
  have hc1 : ⁅n, g * t * g⁻¹⁆ ≠ 1 := fun h => hne (commutatorElement_eq_one_iff_mul_comm.1 h)
  generalize ⁅n, g * t * g⁻¹⁆ = c at hcT' hcN hc1
  have hs : g⁻¹ * c * g ∈ T := mem_conjSubgroup.1 hcT'
  have hs1 : g⁻¹ * c * g ≠ 1 := by
    intro h
    apply hc1
    have : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    rw [this, h]
    group
  exact not_mem_classD_of_isPGroup hT hnT hNn hN2 ⟨g⁻¹, _, hs, hs1, by group⟩ hcN

end TwoCore

section OddCore

theorem eq_one_of_mem_of_odd_card {N : Subgroup G} (hT : IsElemAbelian 2 T)
    (hNodd : Odd (Nat.card N)) {x : G} (hxT : x ∈ T) (hxN : x ∈ N) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (hT.2 x hxT)
  have h2 : orderOf x ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk x hxN]
    exact orderOf_dvd_natCard (⟨x, hxN⟩ : N)
  exact orderOf_eq_one_iff.1
    (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hNodd) h1 h2)

theorem mul_comm_of_mul_comm_of_odd_card [Finite G] (hT : IsWC T) {N : Subgroup G}
    (hNn : ∀ k ∈ Subgroup.normalClosure (T : Set G), ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hNodd : Odd (Nat.card N)) {u g : G} (hu : u ∈ T) (hu1 : u ≠ 1) (hgN : g ∈ N)
    (hug : u * g = g * u) : ∀ t ∈ T, g * t = t * g := by
  have hgn : g ∈ Subgroup.normalizer (T : Set G) :=
    hT.centralizer_le_normalizer hu hu1 (Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hug)
  intro t ht
  have h1 : ⁅g, t⁆ ∈ T := comm_mem_of_mem_normalizer hgn ht
  have h2 : ⁅g, t⁆ ∈ N := by
    have := N.mul_mem hgN (hNn t (Subgroup.le_normalClosure ht) g⁻¹ (N.inv_mem hgN))
    simpa [commutatorElement_def, mul_assoc] using this
  exact commutatorElement_eq_one_iff_mul_comm.1 (eq_one_of_mem_of_odd_card hT.1 hNodd h1 h2)

theorem oddCore_le_center [Finite G] (hT : IsWC T) (h4 : 4 ≤ Nat.card T) (N : Subgroup G)
    (_hNK : N ≤ Subgroup.normalClosure (T : Set G))
    (hNn : ∀ k ∈ Subgroup.normalClosure (T : Set G), ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hNodd : Odd (Nat.card N)) :
    ∀ n ∈ N, ∀ k ∈ Subgroup.normalClosure (T : Set G), n * k = k * n := by
  have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_of_le_normalClosure Subgroup.le_normalClosure hNn
  let _ : MulDistribMulAction T N :=
    MulDistribMulAction.compHom N (N.normalizerMonoidHom.comp (Subgroup.inclusion hTN))
  have : Fact (IsPGroup 2 T) := ⟨isPGroup_two_of_isElemAbelian hT.1⟩
  let _ : CommGroup T :=
    { (inferInstance : Group T) with mul_comm := fun a b => hT.1.1.is_comm.comm a b }
  have hncyc : ¬ IsCyclic T := by
    intro hcyc
    obtain ⟨c, hc⟩ := hcyc.exists_generator
    have h1 : orderOf c = Nat.card T := orderOf_eq_card_of_forall_mem_zpowers hc
    have h2 : orderOf c ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hT.1.2 c c.2))
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have htop := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := N) (A := T) 2 (Nat.coprime_two_left.2 hNodd) hncyc
  have hle : (⨆ (a : T) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) N) ≤
      (Subgroup.centralizer (T : Set G)).comap N.subtype := by
    refine iSup₂_le fun a ha1 m hm => ?_
    rw [FixedPoints.mem_subgroup] at hm
    have h2 : (a : G) * m * (a : G)⁻¹ = m := congrArg Subtype.val (hm ⟨a, Subgroup.mem_zpowers a⟩)
    rw [mul_inv_eq_iff_eq_mul] at h2
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro t ht
    exact (mul_comm_of_mul_comm_of_odd_card hT hNn hNodd a.2 (fun h => ha1 (Subtype.ext h))
      m.2 h2 t ht).symm
  have hNT : ∀ m ∈ N, ∀ t ∈ T, m * t = t * m := by
    intro m hm t ht
    have hmem : (⟨m, hm⟩ : N) ∈ ⨆ (a : T) (_ : a ≠ 1),
        fixedPointSubgroup (↥(Subgroup.zpowers a)) N := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_centralizer_iff.1 (hle hmem) t ht).symm
  intro n hn
  refine mul_comm_of_mem_normalClosure fun g t ht => ?_
  obtain ⟨k, hk, hkg⟩ := exists_mem_normalClosure_conj_eq hT g
  have hmem : g * t * g⁻¹ ∈ conjSubgroup k T := by
    rw [← hkg, mem_conjSubgroup]
    simpa [mul_assoc] using ht
  have hsT : k⁻¹ * (g * t * g⁻¹) * k ∈ T := mem_conjSubgroup.1 hmem
  have hnk : k⁻¹ * n * k ∈ N := inv_mul_mul_mem_of_mem_normalClosure hNn hk hn
  have hcomm := hNT _ hnk _ hsT
  have e : g * t * g⁻¹ = k * (k⁻¹ * (g * t * g⁻¹) * k) * k⁻¹ := by group
  rw [e]
  calc n * (k * (k⁻¹ * (g * t * g⁻¹) * k) * k⁻¹)
      = k * ((k⁻¹ * n * k) * (k⁻¹ * (g * t * g⁻¹) * k)) * k⁻¹ := by group
    _ = k * ((k⁻¹ * (g * t * g⁻¹) * k) * (k⁻¹ * n * k)) * k⁻¹ := by rw [hcomm]
    _ = k * (k⁻¹ * (g * t * g⁻¹) * k) * k⁻¹ * n := by group

end OddCore

end CFSG.CGT.Timmesfeld75
