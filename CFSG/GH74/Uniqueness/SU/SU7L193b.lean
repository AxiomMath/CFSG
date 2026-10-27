module

public import CFSG.GH74.Uniqueness.SU.SU7L192
public import CFSG.GH74.Uniqueness.SU.SU7L193a
public import CFSG.GH74.Uniqueness.SU.SU7Tr
public import CFSG.RankThree.Coprime.CommutingActionGeneration
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace Gen

theorem odd_mem_pPrimeCore_of_mem_Op {X : Type*} [Group X] [Finite X] {x : X}
    (hx : x ∈ Op_p'p 2 X) (hodd : Odd (orderOf x)) : x ∈ pPrimeCore 2 X := by
  have h1 : QuotientGroup.mk' (pPrimeCore 2 X) x ∈ pCore 2 (X ⧸ pPrimeCore 2 X) := hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 pCore_isPGroup ⟨_, h1⟩
  have hk' : orderOf (QuotientGroup.mk' (pPrimeCore 2 X) x) = 2 ^ k := by
    have : orderOf (⟨QuotientGroup.mk' (pPrimeCore 2 X) x, h1⟩ :
        ↥(pCore 2 (X ⧸ pPrimeCore 2 X))) = 2 ^ k := by simpa using hk
    rwa [Subgroup.orderOf_mk] at this
  have hdvd : orderOf (QuotientGroup.mk' (pPrimeCore 2 X) x) ∣ orderOf x := orderOf_map_dvd _ x
  have hodd' : Odd (orderOf (QuotientGroup.mk' (pPrimeCore 2 X) x)) := Odd.of_dvd_nat hodd hdvd
  have hk0 : k = 0 := by
    by_contra hne
    rw [hk'] at hodd'
    exact (Nat.not_even_iff_odd.2 hodd') (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk'
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 hk')

end Gen

namespace L193

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

omit [Finite G] in
theorem le_core_of_normal_odd {a : G} {K : Subgroup G} (hKC : K ≤ centralizer ({a} : Set G))
    (hKn : ∀ g ∈ centralizer ({a} : Set G), ∀ w ∈ K, g * w * g⁻¹ ∈ K)
    (hKodd : Odd (Nat.card K)) : K ≤ core a := by
  set Ca : Subgroup G := centralizer ({a} : Set G) with hCa
  have hnorm : (K.subgroupOf Ca).Normal := ⟨fun n hn g => hKn g g.2 n hn⟩
  have hcop : Nat.Coprime 2 (Nat.card (K.subgroupOf Ca)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv]
    exact Nat.coprime_two_left.2 hKodd
  have hle : K.subgroupOf Ca ≤ pPrimeCore 2 ↥Ca := le_sSup ⟨hnorm, hcop⟩
  intro w hw
  exact ⟨⟨w, hKC hw⟩, hle hw, rfl⟩

theorem core_conj_le {z v h : G} (hhz : h * z * h⁻¹ = v) {w : G} (hw : w ∈ core z) :
    h * w * h⁻¹ ∈ core v := by
  set K : Subgroup G := (core z).map (MulAut.conj h).toMonoidHom with hK
  have hKC : K ≤ centralizer ({v} : Set G) := by
    rintro _ ⟨w', hw', rfl⟩
    have hw'C := core_le_cent z hw'
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hzw : z * w' = w' * z := mem_centralizer_iff.1 hw'C z (Set.mem_singleton z)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hhz]
    calc h * z * h⁻¹ * (h * w' * h⁻¹) = h * (z * w') * h⁻¹ := by group
      _ = h * (w' * z) * h⁻¹ := by rw [hzw]
      _ = h * w' * h⁻¹ * (h * z * h⁻¹) := by group
  have hKn : ∀ g ∈ centralizer ({v} : Set G), ∀ y ∈ K, g * y * g⁻¹ ∈ K := by
    intro g hg y hy
    obtain ⟨w', hw', rfl⟩ := hy
    have hg' : h⁻¹ * g * h ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hvg : v * g = g * v := mem_centralizer_iff.1 hg v (Set.mem_singleton v)
      rw [← hhz] at hvg
      calc z * (h⁻¹ * g * h) = h⁻¹ * (h * z * h⁻¹ * g) * h := by group
        _ = h⁻¹ * (g * (h * z * h⁻¹)) * h := by rw [hvg]
        _ = (h⁻¹ * g * h) * z := by group
    refine ⟨(h⁻¹ * g * h) * w' * (h⁻¹ * g * h)⁻¹, core_conj z hg' hw', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hKodd : Odd (Nat.card K) := by
    rw [hK, Subgroup.card_map_of_injective (MulAut.conj h).injective]
    exact core_odd z
  exact le_core_of_normal_odd hKC hKn hKodd ⟨w, hw, by simp [MulAut.conj_apply]⟩

theorem U_le_Nz (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    U ≤ (Op_p'p 2 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype := by
  have hR := (L192.lemma192_a hKI3 hKI4 hc).1.1
  intro u hu
  apply hR
  by_cases hu1 : u = 1
  · rw [hu1]; exact R.one_mem
  · have hu2 : u * u = 1 := by
      rw [← pow_two]; exact (isElemAbelian_iff.1 hc.hyp.four.2.1).2 u hu
    have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
    exact (hc.c19.R_invol u hord).2 (Or.inl hu)

theorem normalizer_U_le_M (hc : Ctx19 S U M V x z A B R) :
    normalizer (U : Set G) ≤ M := by
  have hA := hc.c19.isE16_A
  intro n hn
  exact Claim.normalizer_le_M_of_isE hc.hyp (E := U) (F := A) (n := 2) (m := 4)
    (Base.U_le_S hc.hyp) (Base.U_isE hc.hyp) (by norm_num)
    (fun a ha => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (hc.c19.A_le ha)).1, Base.T_le_S
      (hc.c19.A_le ha)⟩)
    ⟨hA.1, by rw [hA.2]; norm_num⟩ (by norm_num) hn

theorem comm_mem_O (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R)
    {Y : Subgroup G} (hYodd : Odd (Nat.card Y))
    (hUY : ∀ u ∈ U, ∀ y ∈ Y, u * y * u⁻¹ ∈ Y) {v : G} (hvU : v ∈ U) (hv1 : v ≠ 1) {k : G}
    (hkY : k ∈ Y) (hkv : k * v = v * k) {w : G} (hwU : w ∈ U) :
    k⁻¹ * (w * k * w⁻¹) ∈ (pPrimeCore 2 ↥M).map M.subtype := by
  classical
  obtain ⟨h, hhN, hhz⟩ := Tr.exists_conj_z hc.hyp hc.conf hc.concl hvU hv1
  have hhinv : ∀ y ∈ U, h⁻¹ * y * h ∈ U := fun y hy => by
    have := (mem_normalizer_iff.1 ((normalizer (U : Set G)).inv_mem hhN) y).1 hy
    simpa using this
  have hvT : v ∈ Tsub S U := Base.U_le_T hc.hyp hc.conf hc.concl hvU
  have hv2 : orderOf v = 2 := by
    have hvv : v * v = 1 := by
      rw [← pow_two]; exact (isElemAbelian_iff.1 hc.hyp.four.2.1).2 v hvU
    exact orderOf_eq_prime (by rw [pow_two]; exact hvv) hv1
  set c : G := k⁻¹ * (w * k * w⁻¹) with hcdef
  have hcY : c ∈ Y := Y.mul_mem (Y.inv_mem hkY) (hUY w hwU k hkY)
  have hcodd : Odd (orderOf c) := Odd.of_dvd_nat hYodd (Subgroup.orderOf_dvd_natCard Y hcY)
  have hk'C : h⁻¹ * k * h ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    rw [← hhz] at hkv
    calc z * (h⁻¹ * k * h) = h⁻¹ * (h * z * h⁻¹ * k) * h := by group
      _ = h⁻¹ * (k * (h * z * h⁻¹)) * h := by rw [← hkv]
      _ = (h⁻¹ * k * h) * z := by group
  have hw'U : h⁻¹ * w * h ∈ U := hhinv w hwU
  set c' : G := h⁻¹ * c * h with hc'def
  have hc'eq : c' = (h⁻¹ * k * h)⁻¹ * ((h⁻¹ * w * h) * (h⁻¹ * k * h) * (h⁻¹ * w * h)⁻¹) := by
    rw [hc'def, hcdef]; group
  have hUNz := U_le_Nz hKI3 hKI4 hc hw'U
  have hNzn : ∀ g ∈ centralizer ({z} : Set G),
      ∀ n ∈ (Op_p'p 2 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype,
        g * n * g⁻¹ ∈ (Op_p'p 2 ↥(centralizer ({z} : Set G))).map
          (centralizer ({z} : Set G)).subtype := by
    intro g hg n hn
    obtain ⟨n', hn', rfl⟩ := hn
    exact ⟨⟨g, hg⟩ * n' * ⟨g, hg⟩⁻¹,
      (inferInstance : (Op_p'p 2 ↥(centralizer ({z} : Set G))).Normal).conj_mem n' hn' ⟨g, hg⟩,
      rfl⟩
  have hc'N : c' ∈ (Op_p'p 2 ↥(centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype := by
    rw [hc'eq]
    have h1 := hNzn _ ((centralizer ({z} : Set G)).inv_mem hk'C) _ hUNz
    have e : (h⁻¹ * k * h)⁻¹ * ((h⁻¹ * w * h) * (h⁻¹ * k * h) * (h⁻¹ * w * h)⁻¹) =
        ((h⁻¹ * k * h)⁻¹ * (h⁻¹ * w * h) * ((h⁻¹ * k * h)⁻¹)⁻¹) * (h⁻¹ * w * h)⁻¹ := by group
    rw [e]
    exact (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hUNz))
  have hc'odd : Odd (orderOf c') := by
    have := orderOf_injective (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective c
    have e : (MulAut.conj h⁻¹).toMonoidHom c = c' := by
      simp [hc'def]
    rw [e] at this
    rw [this]; exact hcodd
  have hc'core : c' ∈ L193.core z := by
    obtain ⟨x', hx', hxc⟩ := hc'N
    have hxodd : Odd (orderOf x') := by
      have h1 : orderOf (x' : G) = orderOf x' := Subgroup.orderOf_coe x'
      have h2 : (x' : G) = c' := hxc
      rw [← h1, h2]; exact hc'odd
    exact ⟨x', Gen.odd_mem_pPrimeCore_of_mem_Op hx' hxodd, hxc⟩
  have hcv : c ∈ L193.core v := by
    have h1 := core_conj_le hhz hc'core
    have e : h * c' * h⁻¹ = c := by rw [hc'def]; group
    rw [e] at h1
    exact h1
  exact lemma193_a hKI3 hc v hvT hv2 hcv

theorem lemma193_b (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    ∀ Y : Subgroup G, Odd (Nat.card Y) → U ≤ normalizer (Y : Set G) →
      Y ≤ M ∧ ⁅Y, U⁆ ≤ (pPrimeCore 2 ↥M).map M.subtype := by
  intro Y hYodd hUY
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup G := (pPrimeCore 2 ↥M).map M.subtype with hO
  have hU4' : Nat.card U = 2 ^ 2 := hc.hyp.four.2.2
  have hUab := isElemAbelian_iff.1 hc.hyp.four.2.1
  have hU2 : ∀ a ∈ U, a * a = 1 := fun a ha => by rw [← pow_two]; exact hUab.2 a ha
  have hUY' : ∀ u ∈ U, ∀ y ∈ Y, u * y * u⁻¹ ∈ Y := fun u hu y hy =>
    (mem_normalizer_iff.1 (hUY hu) y).1 hy
  have hcommU : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hUab.1 a a.2 b b.2)⟩⟩
  have : IsElementaryAbelian 2 ↥U :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa [pow_two] using hU2 x x.2) }
  let _ : MulDistribMulAction ↥U ↥Y := Subgroup.conjMulDistribMulActionOfLeNormalizer U Y hUY
  have : U.Normalizes Y := ⟨hUY⟩
  have hsolv : Group.IsSolvable ↥Y := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hYodd
  have hcop2 : Nat.Coprime (2 ^ 2) (Nat.card ↥Y) :=
    ((Nat.coprime_two_right.2 hYodd).pow_right 2).symm
  have hcop : Nat.Coprime (Nat.card ↥Y) (Nat.card ↥U) := by
    rw [hU4']; exact hcop2.symm
  have hcopB : Nat.Coprime (Nat.card ↥U * Nat.card ↥U) (Nat.card ↥Y) := by
    rw [hU4']; exact Nat.Coprime.mul_left hcop2 hcop2
  have hcomm : ∀ (b w : ↥U) (y : ↥Y), b • w • y = w • b • y := by
    intro b w y
    apply Subtype.ext
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have hbw : (b : G) * w = w * b := hUab.1 b b.2 w w.2
    calc (b : G) * ((w : G) * (y : G) * (w : G)⁻¹) * (b : G)⁻¹
        = ((b : G) * w) * y * ((b : G) * w)⁻¹ := by group
      _ = ((w : G) * b) * y * ((w : G) * b)⁻¹ := by rw [hbw]
      _ = (w : G) * ((b : G) * (y : G) * (b : G)⁻¹) * (w : G)⁻¹ := by group
  obtain ⟨-, -, hfac, -⟩ :=
    CFSG.RankThree.Coprime.solvable_coprime_fixed_commutator_factorization (A := ↥U) (H := ↥Y)
      hsolv hcop
  have hgen := CFSG.RankThree.Coprime.solvable_commuting_action_fixed_commutator_generation
    (p := 2) (B := ↥U) (W := ↥U) (H := ↥Y) (by rw [hU4']) hsolv hcomm hcopB
  have hD : actionCommutator ↥U (⊤ : Subgroup ↥Y) ≤ O.comap Y.subtype := by
    rw [hgen]
    refine iSup₂_le fun b hb => ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, w, rfl⟩
    have hkb : b • k = k := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff b k).1 hk
    have hkb' := congrArg Subtype.val hkb
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at hkb'
    have hkv : (k : G) * b = b * k := by
      calc (k : G) * b = ((b : G) * k * (b : G)⁻¹) * b := by rw [hkb']
        _ = b * k := by group
    have hcoe : ((k⁻¹ * (w • k) : ↥Y) : G) = (k : G)⁻¹ * ((w : G) * (k : G) * (w : G)⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    show ((k⁻¹ * (w • k) : ↥Y) : G) ∈ O
    rw [hcoe]
    exact comm_mem_O hKI3 hKI4 hc hYodd hUY' b.2 (fun h => hb (Subtype.ext h)) k.2 hkv w.2
  have hcommY : ⁅Y, U⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro y hy u hu
    have hmem := gen_mem_actionCommutator (A := ↥U) (H := (⊤ : Subgroup ↥Y))
      (Subgroup.mem_top (⟨y⁻¹, Y.inv_mem hy⟩ : ↥Y)) ⟨u, hu⟩
    have h1 := hD hmem
    rw [Subgroup.mem_comap] at h1
    have e : (((⟨y⁻¹, Y.inv_mem hy⟩ : ↥Y)⁻¹ * ((⟨u, hu⟩ : ↥U) • (⟨y⁻¹, Y.inv_mem hy⟩ : ↥Y)) :
        ↥Y) : G) = ⁅y, u⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, commutatorElement_def]
      group
    rw [← e]
    exact h1
  have hOM : O ≤ M := Subgroup.map_subtype_le _
  have hYM : Y ≤ M := by
    intro y hy
    obtain ⟨d, hd, c, hcfix, hyc⟩ := hfac ⟨y, hy⟩
    have hdO : (d : G) ∈ O := by
      have := hD hd
      rwa [Subgroup.mem_comap] at this
    have hcN : (c : G) ∈ normalizer (U : Set G) := by
      apply Gen.mem_normalizer_of_conj_le
      intro u hu
      have h1 : (⟨u, hu⟩ : ↥U) • c = c := hcfix ⟨u, hu⟩
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h2
      have h3 : (c : G) * u * (c : G)⁻¹ = u := by
        have : (c : G) * u = u * c := by
          calc (c : G) * u = ((u : G) * c * (u : G)⁻¹) * u := by rw [h2]
            _ = u * c := by group
        calc (c : G) * u * (c : G)⁻¹ = (u * c) * (c : G)⁻¹ := by rw [this]
          _ = u := by group
      rw [h3]; exact hu
    have hyeq : y = (d : G) * (c : G) := congrArg Subtype.val hyc
    rw [hyeq]
    exact M.mul_mem (hOM hdO) (normalizer_U_le_M hc hcN)
  exact ⟨hYM, hcommY⟩

end L193

end CFSG.GH74.Uniqueness.SU.SU7
