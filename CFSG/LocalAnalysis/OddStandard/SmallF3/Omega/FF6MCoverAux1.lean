module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTransLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBXsub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {A B : Type} [Group A] [Group B] {ρ : A →* B}

private theorem ff6m_twoRes_aux (hρ : OddCentralCover ρ) :
    (twoRes (⊤ : Subgroup A)).map ρ = twoRes (⊤ : Subgroup B) := by
  unfold twoRes
  rw [MonoidHom.map_closure]
  congr 1
  ext b
  constructor
  · rintro ⟨a, ⟨-, haodd⟩, rfl⟩
    exact ⟨Subgroup.mem_top _, haodd.of_dvd_nat (orderOf_map_dvd ρ a)⟩
  · rintro ⟨-, hbodd⟩
    obtain ⟨a, ha⟩ := hρ.surjective b
    refine ⟨a, ⟨Subgroup.mem_top _, ?_⟩, ha⟩
    have hker : a ^ orderOf b ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_pow, ha, pow_orderOf_eq_one]
    have hpow : (a ^ orderOf b) ^ Nat.card ρ.ker = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard ρ.ker hker)
    have hdvd : orderOf a ∣ orderOf b * Nat.card ρ.ker := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact hpow
    exact (hbodd.mul hρ.odd_card_ker).of_dvd_nat hdvd

private theorem ff_twoPrimeRes_top_normal {H : Type} [Group H] :
    (twoPrimeRes (⊤ : Subgroup H)).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  have h := ff_map_twoPrimeRes (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    (⊤ : Subgroup H)
  rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h

private theorem ff_odd_card_of_forall_odd_order {H : Type} [Group H] [Finite H]
    (h : ∀ x : H, Odd (orderOf x)) : Odd (Nat.card H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ¬ Even (Nat.card H) := by
    intro he
    rw [even_iff_two_dvd] at he
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 he
    have hodd := h y
    rw [hy] at hodd
    exact (by norm_num : ¬ Odd (2 : ℕ)) hodd
  exact Nat.not_even_iff_odd.mp hne

theorem ff6m_cover_layer [Finite A] (hρ : OddCentralCover ρ) (E : Subgroup B) [E.Normal]
    (hE : IsSimpleGroup ↥E) (hnc : ∃ a b : ↥E, a * b ≠ b * a) (hev : 2 ∣ Nat.card ↥E)
    (h2 : IsPGroup 2 (B ⧸ E)) :
    Nonempty (↥(CFSG.layer A) ⧸ oddCore ↥(CFSG.layer A) ≃* ↥E) ∧ ffX A = CFSG.layer A := by
  haveI : Finite B := Finite.of_surjective ρ hρ.surjective
  have hEbot : oddCore ↥E = ⊥ := ff_oddCore_eq_bot_of_simple_even hE hev
  obtain ⟨hLBE, hffBE⟩ := ff_layer_ffX_eq_of_normal_simple E hE hnc hev h2
  have htwoB : twoRes (⊤ : Subgroup B) = E := by
    apply le_antisymm
    · rw [twoRes]
      refine (Subgroup.closure_le E).mpr ?_
      rintro g ⟨-, hgodd⟩
      have hx : (QuotientGroup.mk g : B ⧸ E) ^ orderOf g = 1 := by
        rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one]
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp h2) (QuotientGroup.mk g)
      have hd : orderOf (QuotientGroup.mk g : B ⧸ E) ∣ orderOf g :=
        orderOf_dvd_of_pow_eq_one hx
      rw [hj] at hd
      have hj0 : j = 0 := by
        by_contra hne
        exact (Nat.not_even_iff_odd.mpr hgodd)
          (even_iff_two_dvd.mpr ((dvd_pow_self 2 hne).trans hd))
      rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
      exact (QuotientGroup.eq_one_iff g).mp hj
    · have hle : ffX B ≤ twoRes (⊤ : Subgroup B) := by
        unfold ffX
        exact (Subgroup.closure_le _).mpr fun g hg => hg.1
      rw [← hffBE]
      exact hle
  let LA : Subgroup A := CFSG.layer A
  let T : Subgroup A := twoRes (⊤ : Subgroup A)
  haveI hLAchar : LA.Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hLAnormal : LA.Normal := inferInstance
  have hLAperf : Group.IsPerfect ↥LA := CFSG.LocalCores.layer_isPerfect
  have hmapLA : LA.map ρ = E := by
    apply le_antisymm
    · haveI : Group.IsPerfect ↥(LA.map ρ) := by
        haveI : Group.IsPerfect ↥LA := hLAperf
        exact Group.IsPerfect.map (f := ρ)
      exact ff_perfect_le_of_quot_two E h2 (LA.map ρ) inferInstance
    · have h := hρ.layer_le_map_layer
      rwa [hLBE] at h
  let ρ' : ↥LA →* ↥E :=
    { toFun := fun x => ⟨ρ (x : A), by rw [← hmapLA]; exact Subgroup.mem_map_of_mem ρ x.2⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun x y => Subtype.ext (map_mul ρ (x : A) (y : A)) }
  have hsurj : Function.Surjective ρ' := by
    intro e
    have he : (e : B) ∈ LA.map ρ := by rw [hmapLA]; exact e.2
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp he
    exact ⟨⟨a, ha⟩, Subtype.ext hae⟩
  have hρ' : OddCentralCover ρ' := by
    refine ⟨hsurj, ?_, ?_⟩
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      refine Subtype.ext ?_
      exact Subgroup.mem_center_iff.mp
        (hρ.ker_le_center (MonoidHom.mem_ker.mpr
          (congrArg Subtype.val (MonoidHom.mem_ker.mp hx)))) (y : A)
    · have hle : ρ'.ker.map LA.subtype ≤ ρ.ker := by
        rintro _ ⟨x, hx, rfl⟩
        exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
      have hcard : Nat.card ρ'.ker = Nat.card (ρ'.ker.map LA.subtype) :=
        Nat.card_congr ((ρ'.ker).equivMapOfInjective LA.subtype LA.subtype_injective).toEquiv
      rw [hcard]
      exact hρ.odd_card_ker.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hker : oddCore ↥LA = ρ'.ker := hρ'.oddCore_eq_ker hEbot
  have hLAT : LA ≤ T := aor_perfect_le_twoRes le_top hLAperf
  have hmapT : T.map ρ = twoRes (⊤ : Subgroup B) := ff6m_twoRes_aux hρ
  have hmapTE : T.map ρ = E := by rw [hmapT, htwoB]
  have hLTnormal : (LA.subgroupOf T).Normal := hLAnormal.subgroupOf T
  haveI := hLTnormal
  let q : ↥T →* ↥T ⧸ (LA.subgroupOf T) := QuotientGroup.mk' _
  have hoddOrder : ∀ x : ↥T ⧸ (LA.subgroupOf T), Odd (orderOf x) := by
    intro x
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
    change Odd (orderOf (q t))
    have hρt : ρ (t : A) ∈ E := by
      have hmem : ρ (t : A) ∈ T.map ρ := Subgroup.mem_map_of_mem ρ t.2
      rwa [hmapTE] at hmem
    obtain ⟨l, hl, hlρ⟩ := Subgroup.mem_map.mp (by rwa [← hmapLA] at hρt)
    have hk_ker : l⁻¹ * (t : A) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlρ, inv_mul_cancel]
    have hk_order : Odd (orderOf (l⁻¹ * (t : A))) :=
      hρ.odd_card_ker.of_dvd_nat (Subgroup.orderOf_dvd_natCard ρ.ker hk_ker)
    let l' : ↥T := ⟨l, hLAT hl⟩
    let k' : ↥T := ⟨l⁻¹ * (t : A), mul_mem (inv_mem (hLAT hl)) t.2⟩
    have hk'_order : Odd (orderOf k') := by
      rw [← Subgroup.orderOf_coe k']
      exact hk_order
    have hmul : t = l' * k' := by
      apply Subtype.ext
      show (t : A) = l * (l⁻¹ * (t : A))
      group
    have hq : q t = q k' := by
      rw [hmul, map_mul]
      have hql' : q l' = 1 := (QuotientGroup.eq_one_iff l').mpr hl
      rw [hql', one_mul]
    rw [hq]
    exact hk'_order.of_dvd_nat (orderOf_map_dvd q k')
  have hcard_odd : Odd (Nat.card (↥T ⧸ (LA.subgroupOf T))) :=
    ff_odd_card_of_forall_odd_order hoddOrder
  have hle1 : twoPrimeRes T ≤ LA := by
    rw [twoPrimeRes]
    refine (Subgroup.closure_le LA).mpr ?_
    intro g hg
    obtain ⟨hgT, j, hgj⟩ := hg
    let g' : ↥T := ⟨g, hgT⟩
    have h1 : orderOf (q g') ∣ 2 ^ j := by
      have h := orderOf_map_dvd q g'
      rwa [← Subgroup.orderOf_coe g', hgj] at h
    have h2 : orderOf (q g') ∣ Nat.card (↥T ⧸ (LA.subgroupOf T)) :=
      orderOf_dvd_natCard (q g')
    have hcop : Nat.Coprime (2 ^ j) (Nat.card (↥T ⧸ (LA.subgroupOf T))) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hcard_odd)
    have hone : orderOf (q g') = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have hqg : q g' = 1 := orderOf_eq_one_iff.mp hone
    exact (QuotientGroup.eq_one_iff g').mp hqg
  have hle2 : LA ≤ twoPrimeRes T := by
    let N : Subgroup ↥T := twoPrimeRes (⊤ : Subgroup ↥T)
    have hNnormal : N.Normal := ff_twoPrimeRes_top_normal
    haveI := hNnormal
    have hQodd : Odd (Nat.card (↥T ⧸ N)) := by
      apply ff_odd_card_of_forall_odd_order
      intro x
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨a, m, hm, htm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t).ne'
      have hdvd : orderOf (t ^ m) ∣ 2 ^ a := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← pow_mul]
        have : m * 2 ^ a = orderOf t := by rw [htm, mul_comm]
        rw [this, pow_orderOf_eq_one]
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hmem : t ^ m ∈ N := by
        change t ^ m ∈ twoPrimeRes (⊤ : Subgroup ↥T)
        rw [twoPrimeRes]
        exact Subgroup.subset_closure ⟨Subgroup.mem_top _, ⟨i, hi⟩⟩
      have hq : (QuotientGroup.mk t : ↥T ⧸ N) ^ m = 1 := by
        rw [← QuotientGroup.mk_pow]
        exact (QuotientGroup.eq_one_iff (t ^ m)).mpr hmem
      exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hq)
    haveI : Group.IsSolvable (↥T ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd
    have hLTperf : Group.IsPerfect ↥(LA.subgroupOf T) := by
      haveI : Group.IsPerfect ↥LA := hLAperf
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hLAT).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hLAT).symm.surjective
    have hmapq : (LA.subgroupOf T).map (QuotientGroup.mk' N) = ⊥ := by
      haveI : Group.IsPerfect ↥((LA.subgroupOf T).map (QuotientGroup.mk' N)) := by
        haveI : Group.IsPerfect ↥(LA.subgroupOf T) := hLTperf
        exact Group.IsPerfect.map (f := QuotientGroup.mk' N)
      haveI : Group.IsSolvable ↥((LA.subgroupOf T).map (QuotientGroup.mk' N)) := inferInstance
      haveI : Subsingleton ↥((LA.subgroupOf T).map (QuotientGroup.mk' N)) := by
        by_contra hns
        haveI : Nontrivial ↥((LA.subgroupOf T).map (QuotientGroup.mk' N)) :=
          not_subsingleton_iff_nontrivial.mp hns
        exact Group.IsPerfect.not_isSolvable
          ↥((LA.subgroupOf T).map (QuotientGroup.mk' N)) inferInstance
      rw [eq_bot_iff]
      intro x hx
      have hx1 : (⟨x, hx⟩ : ↥((LA.subgroupOf T).map (QuotientGroup.mk' N))) = 1 :=
        Subsingleton.elim _ _
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hx1
    have hleN : (LA.subgroupOf T) ≤ N := by
      have h := (Subgroup.map_eq_bot_iff (LA.subgroupOf T)
        (f := QuotientGroup.mk' N)).mp hmapq
      rwa [QuotientGroup.ker_mk'] at h
    intro l hl
    have hlT : l ∈ T := hLAT hl
    have hl' : (⟨l, hlT⟩ : ↥T) ∈ LA.subgroupOf T := hl
    have hmem : (⟨l, hlT⟩ : ↥T) ∈ N := hleN hl'
    rw [ff_twoPrimeRes_eq_map T]
    exact Subgroup.mem_map_of_mem T.subtype hmem
  refine ⟨⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ' hsurj)⟩, ?_⟩
  change twoPrimeRes T = LA
  exact le_antisymm hle1 hle2

end CFSG.OddStandard.SmallF3.Omega