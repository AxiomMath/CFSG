module

public import CFSG.GroupTheory.QuasiDihedralFusion.Defs
public import CFSG.GroupTheory.ABGDGroups.HomocyclicSylow
import CFSG.Walter.AStar.Subnormal
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.ABGDGroups

open CFSG.RankTwoShapes CFSG.QuasiDihedralFusion

private theorem oddCore_eq_pPrimeCore_two (G : Type*) [Group G] :
    CFSG.oddCore G = pPrimeCore 2 G :=
  (oddCore_eq_piCore G).trans (pPrimeCore_eq_piCore G 2).symm

private theorem odd_card_oddCore_aux (G : Type*) [Group G] [Finite G] :
    Odd (Nat.card (CFSG.oddCore G)) := by
  rw [oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

private theorem oddCore_eq_bot_of_normal {H : Type*} [Group H] [Finite H]
    (hO : CFSG.oddCore H = ⊥) (K : Subgroup H) [K.Normal] : CFSG.oddCore K = ⊥ := by
  rw [oddCore_eq_pPrimeCore_two] at hO ⊢
  have hN : ((pPrimeCore 2 K).map K.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hle : (pPrimeCore 2 K).map K.subtype ≤ pPrimeCore 2 H := by
    refine le_sSup ⟨hN, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact pPrimeCore_coprime_card
  rwa [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at hle

private theorem oddCore_quotient_oddCore_eq_bot (H : Type*) [Group H] [Finite H] :
    CFSG.oddCore (H ⧸ CFSG.oddCore H) = ⊥ := by
  rw [oddCore_eq_piCore (H ⧸ CFSG.oddCore H)]
  let f := QuotientGroup.quotientMulEquivOfEq (oddCore_eq_piCore H)
  apply (Subgroup.map_eq_bot_iff_of_injective _ (f := f.toMonoidHom) f.injective).mp
  rw [LocalCores.piCore_map_mulEquiv]
  exact LocalCores.prime_set_core_quotient {q : Nat.Primes | q.val ≠ 2}

private theorem inf_oddCore_eq_bot {H : Type*} [Group H] [Finite H] {P : Subgroup H}
    (hP : IsPGroup 2 P) : P ⊓ CFSG.oddCore H = ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
  rw [hk]
  exact (Nat.coprime_two_left.mpr (odd_card_oddCore_aux H)).pow_left k

private theorem nonempty_mulEquiv_map {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (P : Subgroup G) (hP : P ⊓ f.ker = ⊥) : Nonempty (P ≃* P.map f) := by
  have hinj : Function.Injective (f.comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ P ⊓ f.ker := ⟨x.2, hx⟩
    rw [hP, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  have hrange : (f.comp P.subtype).range = P.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

private theorem two_pow_sq (n : ℕ) : (2 ^ n) ^ 2 = 4 ^ n := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

private theorem nonempty_base_mulEquiv (m : ℕ) :
    Nonempty (Wreathed.baseSubgroup m ≃* Multiplicative (ZMod m) × Multiplicative (ZMod m)) := by
  refine ⟨MulEquiv.mk' ((Wreathed.baseCoordinateEquiv m).trans
    (Multiplicative.ofAdd.prodCongr Multiplicative.ofAdd)) fun x y => ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := (Wreathed.baseCoordinateEquiv m).symm.surjective x
  obtain ⟨⟨c, d⟩, rfl⟩ := (Wreathed.baseCoordinateEquiv m).symm.surjective y
  have hmul : (Wreathed.baseCoordinateEquiv m).symm (a, b) *
      (Wreathed.baseCoordinateEquiv m).symm (c, d) =
      (Wreathed.baseCoordinateEquiv m).symm (a + c, b + d) :=
    Subtype.ext (Wreathed.element_base_mul m a b c d 0)
  simp only [Equiv.trans_apply, hmul, Equiv.apply_symm_apply]
  rfl

private theorem not_hasSemidihedralSylow_of_hasWreathedSylow {H : Type*} [Group H] [Finite H]
    {m n : ℕ} (hW : HasWreathedSylow H n) : ¬ HasSemidihedralSylow H m := by
  rintro ⟨hm, hSD⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨f⟩ := hSD S
  obtain ⟨e⟩ := hW.2 S
  have hcard : 2 ^ m = 2 ^ (2 * n + 1) := by
    rw [← Semidihedral.card m (by omega), Nat.card_congr (f.trans e).toEquiv,
      Wreathed.card_wreath]
    ring
  have hm' : m = 2 * n + 1 := Nat.pow_right_injective le_rfl hcard
  have hord : orderOf ((f.trans e) (Semidihedral.r m)) = 2 ^ (m - 1) := by
    rw [MulEquiv.orderOf_eq, Semidihedral.orderOf_r m (by omega)]
    rfl
  have hdvd : 2 ^ (m - 1) ∣ 2 ^ (n + 1) := by
    rw [← hord, pow_succ']
    exact orderOf_dvd_of_pow_eq_one (Wreathed.element_pow_twice_modulus _ _)
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
  have := hW.1
  omega

theorem sylow_isMulCommutative_of_isDGroupData {H : Type*} [Group H] [Finite H]
    {K : Subgroup H} (hK : IsDGroupData K) {n : ℕ} (hW : HasWreathedSylow H n)
    (P : Sylow 2 K) : IsMulCommutative P := by
  rcases hK.sylow with ⟨m, hSD, -⟩ | ⟨m, -, hab⟩
  · exact absurd hSD (not_hasSemidihedralSylow_of_hasWreathedSylow hW)
  · exact hab P

private theorem nonempty_homocyclic_of_le_wreath {H : Type*} [Group H] {S U : Subgroup H} {n : ℕ}
    (hn : 2 ≤ n) (e : S ≃* Wreathed.Wreath (2 ^ n)) (hUS : U ≤ S) [IsMulCommutative U]
    (hcardU : Nat.card U = 4 ^ n) : Nonempty (U ≃* HomocyclicGroup n) := by
  have hbase : (U.subgroupOf S).map e.toMonoidHom = Wreathed.baseSubgroup (2 ^ n) := by
    have h2n : 2 < 2 ^ n := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    apply Wreathed.unique_abelian_index_two (2 ^ n) h2n
    · have := Subgroup.subgroupOf_isMulCommutative S U
      exact Subgroup.map_isMulCommutative _ _
    · have hc : Nat.card ((U.subgroupOf S).map e.toMonoidHom) = 4 ^ n := by
        rw [Subgroup.card_map_of_injective e.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv, hcardU]
      have h := ((U.subgroupOf S).map e.toMonoidHom).card_mul_index
      rw [hc, Wreathed.card_wreath, two_pow_sq, mul_comm] at h
      exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  exact ⟨(Subgroup.subgroupOfEquivOfLe hUS).symm.trans
    (((U.subgroupOf S).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hbase).trans (nonempty_base_mulEquiv (2 ^ n)).some))⟩

private theorem centralizer_eq_of_hasWreathedSylow {H : Type*} [Group H] [Finite H] {n : ℕ}
    (hW : HasWreathedSylow H n) {K U : Subgroup H} [K.Normal] (hK2 : K.index = 2)
    (hUK : U ≤ K) (hcardU : Nat.card U = 4 ^ n) (hUC : U ≤ Subgroup.centralizer (U : Set H))
    (hCK : ∀ x ∈ Subgroup.centralizer (U : Set H), x ∈ K → x ∈ U) :
    Subgroup.centralizer (U : Set H) = U := by
  have hn : 2 ≤ n := hW.1
  by_contra hne
  have hCnK : ¬ Subgroup.centralizer (U : Set H) ≤ K := fun hle =>
    hne (le_antisymm (fun x hx => hCK x hx (hle hx)) hUC)
  have hKC : K.relIndex (Subgroup.centralizer (U : Set H)) = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal K (Subgroup.centralizer (U : Set H))
    rw [hK2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h) hCnK
    · exact h
  have hKCU : K ⊓ Subgroup.centralizer (U : Set H) = U :=
    le_antisymm (fun x hx => hCK x hx.2 hx.1) (le_inf hUK hUC)
  have hcardC : Nat.card (Subgroup.centralizer (U : Set H)) = 2 * 4 ^ n := by
    have h := Subgroup.relIndex_mul_card K (Subgroup.centralizer (U : Set H))
    rw [hKC, hKCU, hcardU] at h
    exact h.symm
  have hCp : IsPGroup 2 (Subgroup.centralizer (U : Set H)) :=
    IsPGroup.of_card (n := 2 * n + 1) (by rw [hcardC, pow_succ, pow_mul]; norm_num; ring)
  obtain ⟨S', hS'⟩ := hCp.exists_le_sylow
  obtain ⟨e'⟩ := hW.2 S'
  have hcardS' : Nat.card (S' : Subgroup H) = 2 * 4 ^ n := by
    rw [Nat.card_congr e'.toEquiv, Wreathed.card_wreath, two_pow_sq]
  have hCS' : Subgroup.centralizer (U : Set H) = S' :=
    Subgroup.eq_of_le_of_card_ge hS' (by rw [hcardC, hcardS'])
  have hUS' : U ≤ S' := hCS' ▸ hUC
  have hZ : (U.subgroupOf S').map e'.toMonoidHom ≤
      Subgroup.center (Wreathed.Wreath (2 ^ n)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, rfl⟩ := e'.surjective g
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hc : (c : H) ∈ Subgroup.centralizer (U : Set H) := by
      rw [hCS']
      exact c.2
    exact (Subgroup.mem_centralizer_iff.mp hc (u : H) hu).symm
  have hle := Subgroup.card_le_of_le hZ
  rw [Subgroup.card_map_of_injective e'.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS').toEquiv, hcardU,
    Wreathed.card_center _ (Nat.one_lt_two_pow (by omega))] at hle
  have hlt : 2 ^ n < 4 ^ n := Nat.pow_lt_pow_left (by norm_num) (by omega)
  omega

private theorem mem_centralizer_of_wreath_orderOf_eq_three {H : Type*} [Group H]
    {S : Subgroup H} [S.Normal] {n : ℕ} (hn : 2 ≤ n) (e : S ≃* Wreathed.Wreath (2 ^ n))
    {g : H} (hg : orderOf g = 3) : g ∈ Subgroup.centralizer (S : Set H) := by
  have h2 : IsPGroup 2 (MulAut S) :=
    (Wreathed.wreath_automorphism_isPGroup n hn).of_equiv (MulAut.congr e).symm
  have hφ3 : MulAut.conjNormal g ^ 3 = (1 : MulAut S) := by
    rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  have hφ1 : MulAut.conjNormal g = (1 : MulAut S) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2) (MulAut.conjNormal g)
    have hdvd := orderOf_dvd_of_pow_eq_one hφ3
    rw [hk] at hdvd
    rcases k with _ | k
    · rwa [pow_zero, orderOf_eq_one_iff] at hk
    · have := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
      omega
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h1 : ((MulAut.conjNormal g ⟨s, hs⟩ : S) : H) = s := by
    rw [hφ1]
    rfl
  rw [MulAut.conjNormal_apply] at h1
  calc s * g = (g * s * g⁻¹) * g := by rw [h1]
    _ = g * s := by group

private theorem nonempty_quotient_mulEquiv_perm_three {H : Type*} [Group H] [Finite H]
    {U S : Subgroup H} [U.Normal] (hUS : U ≤ S) (hUS2 : U.relIndex S = 2) (hU6 : U.index = 6)
    (hS : ¬ S.Normal) : Nonempty (H ⧸ U ≃* Equiv.Perm (Fin 3)) := by
  have hcore : S.normalCore = U := by
    have hle : U ≤ S.normalCore := Subgroup.normal_le_normalCore.mpr hUS
    have hle2 : S.normalCore ≤ S := Subgroup.normalCore_le _
    have hmul := Subgroup.relIndex_mul_relIndex U _ _ hle hle2
    rw [hUS2] at hmul
    rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ hmul) with h | h
    · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hle
    · exfalso
      rw [h] at hmul
      have hS' : S ≤ S.normalCore := Subgroup.relIndex_eq_one.mp (by omega)
      exact hS (le_antisymm hle2 hS' ▸ Subgroup.normalCore_normal _)
  have hS3 : S.index = 3 := by
    have h := Subgroup.relIndex_mul_index hUS
    rw [hUS2, hU6] at h
    omega
  have hcardQ : Nat.card (H ⧸ S) = 3 := by
    rw [← Subgroup.index_eq_card, hS3]
  have hker : (MulAction.toPermHom H (H ⧸ S)).ker = U := by
    rw [← Subgroup.normalCore_eq_ker, hcore]
  have hsurj : Function.Surjective (MulAction.toPermHom H (H ⧸ S)) := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [← Subgroup.index_ker, hker, hU6, Nat.card_perm, hcardQ]
    rfl
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ hsurj).trans
      (Equiv.permCongrHom (Finite.equivFinOfCardEq hcardQ)))⟩

theorem wreathed_dGroup_structure {H : Type} [Group H] [Finite H]
    (hO : CFSG.oddCore H = ⊥) {K : Subgroup H}
    (hK : CFSG.QuasiDihedralFusion.IsDGroupData K) {n : ℕ}
    (hW : CFSG.QuasiDihedralFusion.HasWreathedSylow H n) :
    ∃ (U : Subgroup H) (_ : U.Normal), U ≤ K ∧ Nonempty (U ≃* HomocyclicGroup n) ∧
      Subgroup.centralizer (U : Set H) = U ∧ U.relIndex K = 3 ∧ U.index = 6 ∧
      Nonempty (H ⧸ U ≃* Equiv.Perm (Fin 3)) := by
  have hn : 2 ≤ n := hW.1
  have hKn : K.Normal := hK.normal
  have hK2 : K.index = 2 := hK.index_eq_two
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨e⟩ := hW.2 S
  have hcardS : Nat.card (S : Subgroup H) = 2 * 4 ^ n := by
    rw [Nat.card_congr e.toEquiv, Wreathed.card_wreath, two_pow_sq]
  have hSK : ¬ (S : Subgroup H) ≤ K := by
    intro hle
    apply Sylow.not_dvd_index S
    rw [← Subgroup.relIndex_mul_index hle, hK2]
    exact dvd_mul_left 2 _
  have hKS : K.relIndex S = 2 := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal K S
    rw [hK2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h) hSK
    · exact h
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup H, (S : Subgroup H) ⊓ K = U := ⟨_, rfl⟩
  have hUS : U ≤ S := by
    rw [← hUdef]
    exact inf_le_left
  have hUK : U ≤ K := by
    rw [← hUdef]
    exact inf_le_right
  have hcardU : Nat.card U = 4 ^ n := by
    have h := Subgroup.relIndex_mul_card K S
    rw [hKS, inf_comm, hUdef, hcardS] at h
    omega
  have hUS2 : U.relIndex S = 2 := by
    rw [← hUdef, Subgroup.inf_relIndex_left, hKS]
  obtain ⟨P, hP⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal S hKn.isSubnormal
  rw [hUdef] at hP
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    rw [← hP] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hc := isMulCommutative_iff.mp (sylow_isMulCommutative_of_isDGroupData hK hW P)
      ⟨a', ha'⟩ ⟨b', hb'⟩
    exact congrArg (fun x : (P : Subgroup K) => ((x : K) : H)) hc
  have : IsMulCommutative U := ⟨⟨fun a b => Subtype.ext (hUab _ a.2 _ b.2)⟩⟩
  obtain ⟨eU⟩ := nonempty_homocyclic_of_le_wreath hn e hUS hcardU
  let eP : (P : Subgroup K) ≃* HomocyclicGroup n :=
    ((P : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
      ((MulEquiv.subgroupCongr hP).trans eU)
  obtain ⟨hPn, hPC, hPi⟩ := homocyclic_sylow_normal_index_three
    (oddCore_eq_bot_of_normal hO K) (fun N _ => hK.noIndexTwo N) P hn eP
  have hUn : U.Normal := by
    have := Sylow.characteristic_of_normal P hPn
    rw [← hP]
    exact ConjAct.normal_of_characteristic_of_normal
  have hCK : ∀ x ∈ Subgroup.centralizer (U : Set H), x ∈ K → x ∈ U := by
    intro x hx hxK
    have hmem : (⟨x, hxK⟩ : K) ∈ Subgroup.centralizer (P : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      have hyU : (y : H) ∈ U := by
        rw [← hP]
        exact ⟨y, hy, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hx _ hyU
    rw [hPC] at hmem
    rw [← hP]
    exact ⟨_, hmem, rfl⟩
  have hUC : U ≤ Subgroup.centralizer (U : Set H) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hUab v hv u hu
  have hCU := centralizer_eq_of_hasWreathedSylow hW hK2 hUK hcardU hUC hCK
  have hrelK : U.relIndex K = 3 := by
    have hsub : U.subgroupOf K = (P : Subgroup K) := by
      rw [← hP]
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    change (U.subgroupOf K).index = 3
    rw [hsub, hPi]
  have hU6 : U.index = 6 := by
    rw [← Subgroup.relIndex_mul_index hUK, hrelK, hK2]
  have hSnot : ¬ (S : Subgroup H).Normal := by
    intro hSn
    have h3K : 3 ∣ Nat.card K := by
      have h := (P : Subgroup K).card_mul_index
      rw [hPi] at h
      exact Dvd.intro_left _ h
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3K
    have hgS := mem_centralizer_of_wreath_orderOf_eq_three hn e
      (show orderOf (g : H) = 3 by rw [Subgroup.orderOf_coe, hg])
    have hgU : (g : H) ∈ U := by
      rw [← hCU]
      exact Subgroup.centralizer_le hUS hgS
    have hdvd := Subgroup.orderOf_dvd_natCard U hgU
    rw [Subgroup.orderOf_coe, hg, hcardU] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  exact ⟨U, hUn, hUK, ⟨eU⟩, hCU, hrelK, hU6,
    nonempty_quotient_mulEquiv_perm_three hUS hUS2 hU6 hSnot⟩

theorem homocyclic_mem_centralizer_of_odd_fixed {G : Type*} [Group G] {n : ℕ}
    {U : Subgroup G} (e : U ≃* HomocyclicGroup n) {x : G}
    (hx : x ∈ Subgroup.normalizer (U : Set G)) (hodd : Odd (orderOf x)) {u : G} (hu : u ∈ U)
    (hu1 : u ≠ 1) (hfix : x * u * x⁻¹ = u) : x ∈ Subgroup.centralizer (U : Set G) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso
    apply hu1
    have hcard := homocyclic_card e
    rw [pow_zero, Subgroup.card_eq_one] at hcard
    rw [hcard] at hu
    exact Subgroup.mem_bot.mp hu
  · obtain ⟨v, rfl⟩ := exists_homocyclicEmbed e u hu
    have hv : v ≠ 0 := fun h => hu1 (by rw [h, homocyclicEmbed_zero])
    have hT : ∀ w, (⇑(homocyclicConj e x hx))^[orderOf x] w = w := by
      intro w
      apply homocyclicEmbed_injective e
      rw [homocyclicConj_iterate, pow_orderOf_eq_one, inv_one, one_mul, mul_one]
    have hfixv : homocyclicConj e x hx v = v := (homocyclicConj_eq_iff e x hx v).mpr hfix
    exact (homocyclicConj_eq_id_iff e x hx).mp
      (vector_odd_endomorphism_eq_id_of_fixed hn _ hodd hT v hv hfixv)

theorem odd_four_invariant_eq_bot_of_homocyclic {G : Type*} [Group G] [Finite G] {n : ℕ}
    {U : Subgroup G} [hUn : U.Normal] (e : U ≃* HomocyclicGroup n)
    (hC : Subgroup.centralizer (U : Set G) = U) (hindex : ¬ 4 ∣ U.index)
    {T X : Subgroup G} (hT : IsKleinFour T) (hX : Odd (Nat.card X))
    (hXT : T ≤ Subgroup.normalizer (X : Set G)) : X = ⊥ := by
  by_contra hX1
  obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hXU : X ⊓ U = ⊥ := by
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    rw [homocyclic_card e, show (4 : ℕ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num]
    exact (Nat.coprime_two_right.mpr hX).pow_right _
  have hNU : Subgroup.normalizer (X : Set G) ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨huN, huU⟩
    rw [Subgroup.mem_bot]
    by_contra hu1
    have hcomm : u * x * u⁻¹ * x⁻¹ = 1 := by
      have h1 : u * x * u⁻¹ * x⁻¹ ∈ X :=
        X.mul_mem ((Subgroup.mem_normalizer_iff.mp huN x).mp hxX) (X.inv_mem hxX)
      have h2 : u * x * u⁻¹ * x⁻¹ ∈ U := by
        have : x * u⁻¹ * x⁻¹ ∈ U := hUn.conj_mem _ (U.inv_mem huU) x
        simpa [mul_assoc] using U.mul_mem huU this
      have h3 : u * x * u⁻¹ * x⁻¹ ∈ X ⊓ U := ⟨h1, h2⟩
      rwa [hXU, Subgroup.mem_bot] at h3
    have hfix : x * u * x⁻¹ = u := by
      calc x * u * x⁻¹ = (u * x * u⁻¹ * x⁻¹)⁻¹ * u := by group
        _ = u := by rw [hcomm, inv_one, one_mul]
    have hxN : x ∈ Subgroup.normalizer (U : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hUn]
      exact Subgroup.mem_top x
    have hodd : Odd (orderOf x) := hX.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hxX)
    have hxC := homocyclic_mem_centralizer_of_odd_fixed e hxN hodd huU hu1 hfix
    rw [hC] at hxC
    have h3 : x ∈ X ⊓ U := ⟨hxX, hxC⟩
    rw [hXU, Subgroup.mem_bot] at h3
    exact hx1' h3
  have hrel : U.relIndex (Subgroup.normalizer (X : Set G)) =
      Nat.card (Subgroup.normalizer (X : Set G)) := by
    have h := Subgroup.relIndex_mul_card U (Subgroup.normalizer (X : Set G))
    rwa [inf_comm, hNU, Subgroup.card_bot, mul_one] at h
  have hdvd := Subgroup.relIndex_dvd_index_of_normal U (Subgroup.normalizer (X : Set G))
  rw [hrel] at hdvd
  have h4 : 4 ∣ Nat.card (Subgroup.normalizer (X : Set G)) := by
    rw [← hT.card_four]
    exact Subgroup.card_dvd_of_le hXT
  exact hindex (h4.trans hdvd)

theorem pgl_n_23_odd_four_invariant_trivial {H : Type} [Group H] [Finite H]
    {U : Subgroup H} (hUn : U.Normal) {n : ℕ} (hU : Nonempty (U ≃* HomocyclicGroup n))
    (hC : Subgroup.centralizer (U : Set H) = U) (hindex : U.index = 6)
    {T X : Subgroup H} (hT : IsKleinFour T) (hX : Odd (Nat.card X))
    (hXT : T ≤ Subgroup.normalizer (X : Set H)) : X = ⊥ :=
  odd_four_invariant_eq_bot_of_homocyclic hU.some hC (by rw [hindex]; norm_num) hT hX hXT

private theorem le_oddCore_of_quotient {H : Type*} [Group H] [Finite H]
    (h : ∀ T X : Subgroup (H ⧸ CFSG.oddCore H), IsKleinFour T → Odd (Nat.card X) →
      T ≤ Subgroup.normalizer (X : Set (H ⧸ CFSG.oddCore H)) → X = ⊥)
    {T X : Subgroup H} (hT : IsKleinFour T) (hX : Odd (Nat.card X))
    (hXT : T ≤ Subgroup.normalizer (X : Set H)) : X ≤ CFSG.oddCore H := by
  set π := QuotientGroup.mk' (CFSG.oddCore H)
  have hTO : T ⊓ π.ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    rw [hT.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_two_left.mpr (odd_card_oddCore_aux H)).pow_left 2
  obtain ⟨f⟩ := nonempty_mulEquiv_map π T hTO
  have hT' : IsKleinFour (T.map π) :=
    ⟨by rw [← Nat.card_congr f.toEquiv]; exact hT.card_four,
      by rw [← Monoid.exponent_eq_of_mulEquiv f]; exact hT.exponent_two⟩
  have hX' : Odd (Nat.card (X.map π)) := hX.of_dvd_nat (Subgroup.card_map_dvd X π)
  have hXT' : T.map π ≤ Subgroup.normalizer ((X.map π : Subgroup _) : Set _) :=
    (Subgroup.map_mono hXT).trans (Subgroup.le_normalizer_map π)
  have hbot := h _ _ hT' hX' hXT'
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

theorem isDGroupData_quotient_oddCore {H : Type*} [Group H] [Finite H] {K : Subgroup H}
    (hK : IsDGroupData K) {n : ℕ} (hW : HasWreathedSylow H n) :
    IsDGroupData (K.map (QuotientGroup.mk' (CFSG.oddCore H))) ∧
      HasWreathedSylow (H ⧸ CFSG.oddCore H) n := by
  set π := QuotientGroup.mk' (CFSG.oddCore H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hdisj : ∀ P : Subgroup H, IsPGroup 2 P → P ⊓ π.ker = ⊥ := fun P hP => by
    rw [QuotientGroup.ker_mk']
    exact inf_oddCore_eq_bot hP
  have hW' : HasWreathedSylow (H ⧸ CFSG.oddCore H) n := by
    refine ⟨hW.1, fun Q => ?_⟩
    obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hπ 2 Q
    obtain ⟨e⟩ := hW.2 P
    obtain ⟨f⟩ := nonempty_mulEquiv_map π P (hdisj P P.isPGroup')
    exact ⟨(MulEquiv.subgroupCongr (Sylow.coe_mapSurjective hπ P)).trans (f.symm.trans e)⟩
  have hKn : K.Normal := hK.normal
  have hOK : CFSG.oddCore H ≤ K := by
    have hdvd := Subgroup.relIndex_dvd_index_of_normal K (CFSG.oddCore H)
    rw [hK.index_eq_two] at hdvd
    have hodd : Odd (K.relIndex (CFSG.oddCore H)) :=
      (odd_card_oddCore_aux H).of_dvd_nat (Subgroup.relIndex_dvd_card _ _)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Subgroup.relIndex_eq_one.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  refine ⟨⟨hK.normal.map π hπ, ?_, ?_, Or.inr ⟨n, hW', fun Q => ?_⟩⟩, hW'⟩
  · rw [Subgroup.index_map_eq K hπ (by rwa [QuotientGroup.ker_mk']), hK.index_eq_two]
  · intro M hM
    apply hK.noIndexTwo (M.comap (π.subgroupMap K))
    rwa [Subgroup.index_comap_of_surjective M (π.subgroupMap_surjective K)]
  · obtain ⟨P, hPQ⟩ := Sylow.mapSurjective_surjective (π.subgroupMap_surjective K) 2 Q
    have := sylow_isMulCommutative_of_isDGroupData hK hW P
    rw [← hPQ, Sylow.coe_mapSurjective]
    exact Subgroup.map_isMulCommutative _ _

theorem wreathed_dGroup_odd_four_invariant_le_oddCore {H : Type} [Group H] [Finite H]
    {K : Subgroup H} (hK : CFSG.QuasiDihedralFusion.IsDGroupData K) {n : ℕ}
    (hW : CFSG.QuasiDihedralFusion.HasWreathedSylow H n) {T X : Subgroup H}
    (hT : IsKleinFour T) (hX : Odd (Nat.card X))
    (hXT : T ≤ Subgroup.normalizer (X : Set H)) : X ≤ CFSG.oddCore H := by
  refine le_oddCore_of_quotient (fun T' X' hT' hX' hXT' => ?_) hT hX hXT
  obtain ⟨hK', hW'⟩ := isDGroupData_quotient_oddCore hK hW
  obtain ⟨U, hUn, -, hU, hC, -, hU6, -⟩ :=
    wreathed_dGroup_structure (oddCore_quotient_oddCore_eq_bot H) hK' hW'
  exact pgl_n_23_odd_four_invariant_trivial hUn hU hC hU6 hT' hX' hXT'

theorem homocyclic_sylow_odd_four_invariant_le_oddCore {H : Type} [Group H] [Finite H]
    (U : Sylow 2 H) {n : ℕ} (hn : 2 ≤ n) (e : (U : Subgroup H) ≃* HomocyclicGroup n)
    {T X : Subgroup H} (hT : IsKleinFour T) (hX : Odd (Nat.card X))
    (hXT : T ≤ Subgroup.normalizer (X : Set H)) : X ≤ CFSG.oddCore H := by
  refine le_oddCore_of_quotient (fun T' X' hT' hX' hXT' => ?_) hT hX hXT
  set π := QuotientGroup.mk' (CFSG.oddCore H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hUO : (U : Subgroup H) ⊓ π.ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact inf_oddCore_eq_bot U.isPGroup'
  obtain ⟨f⟩ := nonempty_mulEquiv_map π U hUO
  let Ubar : Sylow 2 (H ⧸ CFSG.oddCore H) := U.mapSurjective hπ
  let ebar : (Ubar : Subgroup (H ⧸ CFSG.oddCore H)) ≃* HomocyclicGroup n :=
    (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective hπ U)).trans (f.symm.trans e)
  obtain ⟨hnormal, hcent, hindex⟩ :=
    homocyclic_sylow_normal_of_oddCore_eq_bot (oddCore_quotient_oddCore_eq_bot H) Ubar hn ebar
  have := hnormal
  exact odd_four_invariant_eq_bot_of_homocyclic ebar hcent
    (by rcases hindex with h | h <;> rw [h] <;> norm_num) hT' hX' hXT'

end CFSG.ABGDGroups
