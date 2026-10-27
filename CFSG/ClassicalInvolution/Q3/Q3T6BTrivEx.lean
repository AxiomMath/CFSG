module

public import CFSG.ClassicalInvolution.Q3.Q3T6BTwinP
public import CFSG.ClassicalInvolution.Q3.Q3TNGen
public import CFSG.ClassicalInvolution.Q3.Q3TNCore1
public import CFSG.ClassicalInvolution.Q3.Q3T6BSubN

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement MatrixGroups

variable {F : Type} [Group F] [Finite F]

theorem exists_inverted_of_act {J : Subgroup F} {t w : F} (hJ : Mem3 J t)
    (hwN : w ∈ Subgroup.normalizer (J : Set F)) (hw2 : w * w = 1)
    (hnt : ¬ ∀ k ∈ J, ⁅w, k⁆ ∈ oddCoreOf J) :
    ∃ κ ∈ J, κ * κ = t ∧ w * κ * w = κ⁻¹ := by
  classical
  set T : Subgroup F := Subgroup.zpowers w with hT
  have hT2 : IsPGroup 2 T := Balance.isPGroup_zpowers_of_mul_self_eq_one hw2
  have hTN : T ≤ Subgroup.normalizer (J : Set F) := Subgroup.zpowers_le.mpr hwN
  set H : Subgroup F := J ⊔ T with hH
  have hJH : J ≤ H := le_sup_left
  have hHN : H ≤ Subgroup.normalizer (J : Set F) := sup_le Subgroup.le_normalizer hTN
  obtain ⟨R, hRH, hTR⟩ := Asc77.IsSylow2In.exists_ge hT2 (le_sup_right : T ≤ H)
  have hR2 : IsPGroup 2 R := hRH.2.1
  have hwR : w ∈ R := hTR (Subgroup.mem_zpowers w)
  have hRJ : IsSylow2In (R ⊓ J) J := isSylow2In_inf_of_le_normalizer hRH hJH hHN
  obtain ⟨κ, hκ, hκ2, hκw⟩ := hJ.exists_inverted hR2 hRJ hwR hw2 hwN hnt
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  refine ⟨κ, hκ.2, hκ2, ?_⟩
  rw [hwi] at hκw
  exact hκw

theorem twinProd_act_mem_inn3 {K J : Subgroup F} {t : F} (hJ : Mem3 J t)
    (htK : ∀ k ∈ K, k * t = t * k) (hex : ExAt t)
    (e : J ⧸ classicalInvolutionOddCore J ≃* SL(2, ZMod 3)) {p : F}
    (hp : p ∈ twinProd K J) :
    ∃ hpN : p ∈ Subgroup.normalizer (J : Set F),
      Q3T6.normalizerToAutSL3 e ⟨p, hpN⟩ ∈ Q3T6.inn3 := by
  have hJK : J ∈ twinClass K J := ⟨1, K.one_mem, (conjSub_one J).symm⟩
  let Kin : Subgroup F :=
    (Q3T6.inn3.comap (Q3T6.normalizerToAutSL3 e)).map (Subgroup.normalizer (J : Set F)).subtype
  have hle : twinProd K J ≤ Kin := by
    refine iSup₂_le fun L hL l hl => ?_
    have hlN : l ∈ Subgroup.normalizer (J : Set F) :=
      le_normalizer_of_mem_twinClass hJ htK hJK hL hl
    refine ⟨⟨l, hlN⟩, ?_, rfl⟩
    show Q3T6.normalizerToAutSL3 e ⟨l, hlN⟩ ∈ Q3T6.inn3
    by_cases hLJ : J = L
    · subst hLJ
      rw [Q3T6.normalizerToAutSL3_of_mem e hl]
      exact Q3T6.conj_mem_inn3 _
    · have h1 : Q3T6.normalizerToAutSL3 e ⟨l, hlN⟩ = 1 := by
        rw [Q3T6.normalizerToAutSL3_eq_one_iff]
        intro y hy
        have hc : l * y = y * l := (commute_of_mem_twinClass hJ htK hex hJK hL hLJ hy hl).symm
        rw [Mem3.oddCoreOf_eq_bot hJ hex, Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hc
      rw [h1]
      exact Q3T6.inn3.one_mem
  obtain ⟨n, hn, rfl⟩ := hle hp
  exact ⟨n.2, hn⟩

theorem isSubnormal_of_le_of_le {K C M : Subgroup F} (h : IsSubnormal K C) (hM : M ≤ C)
    (hKM : K ≤ M) : IsSubnormal K M := by
  have h1 := isSubnormal_subgroupOf h M
  rw [Subgroup.subgroupOf_eq_top.mpr hM] at h1
  have h2 := CFSG.ComponentClassification.Components.chain_map M.subtype h1
  rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hKM] at h2
  exact h2

theorem Mem3.le_closure_odd {K : Subgroup F} {z : F} (hK : Mem3 K z) :
    K ≤ Subgroup.closure {g : F | g ∈ K ∧ Odd (orderOf g)} :=
  Q3T.le_of_forall_oddPrimePow_mem (hK.member.toQ3 (by norm_num)) fun g hg p k hp hp2 hgp =>
    Subgroup.subset_closure ⟨hg, ((hp.odd_of_ne_two hp2).pow).of_dvd_nat
      (orderOf_dvd_of_pow_eq_one hgp)⟩

theorem le_normalizer_twinProd_inf_centralizer {K J : Subgroup F} {z : F}
    (hzK : ∀ k ∈ K, k * z = z * k) :
    K ≤ Subgroup.normalizer
      ((twinProd K J ⊓ Subgroup.centralizer ({z} : Set F) : Subgroup F) : Set F) := by
  have key : ∀ k' ∈ K, ∀ a ∈ twinProd K J ⊓ Subgroup.centralizer ({z} : Set F),
      k' * a * k'⁻¹ ∈ twinProd K J ⊓ Subgroup.centralizer ({z} : Set F) := by
    intro k' hk' a ha
    refine ⟨conj_mem_twinProd hk' ha.1, ?_⟩
    have h1 : Commute k' z := hzK k' hk'
    have h2 : Commute a z := Subgroup.mem_centralizer_singleton_iff.mp ha.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((h1.mul_left h2).mul_left h1.inv_left)
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => key k hk a ha, fun ha => ?_⟩
  have := key k⁻¹ (K.inv_mem hk) _ ha
  simpa [mul_assoc] using this

theorem odd_mem_normalizer_of_centralizes {K J : Subgroup F} {z t : F} (hJ : Mem3 J t)
    (htex : ExAt t) (hz2 : z * z = 1) (hzJ : z ∈ Subgroup.normalizer (J : Set F))
    (hnt : ¬ ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) (htK : ∀ k ∈ K, k * t = t * k)
    (hzK : ∀ k ∈ K, k * z = z * k)
    (hcomm : ∀ g' ∈ K, Odd (orderOf g') →
      ∀ a ∈ twinProd K J ⊓ Subgroup.centralizer ({z} : Set F), g' * a = a * g')
    {g : F} (hgK : g ∈ K) (hodd : Odd (orderOf g)) : g ∈ Subgroup.normalizer (J : Set F) := by
  classical
  have hOJ : oddCoreOf J = ⊥ := Mem3.oddCoreOf_eq_bot hJ htex
  have ht2 : t * t = 1 := hJ.mul_self
  have hnt' : ∃ j ∈ J, z * j ≠ j * z := by
    by_contra hcon
    push Not at hcon
    apply hnt
    intro j hj
    rw [hOJ, Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcon j hj)
  by_contra hgJ
  have hne : conjSub g J ≠ J := fun h => hgJ (AscHypOmega.mem_normalizer_of_conjSub_eq h)
  set P : Subgroup F := twinProd K J with hP
  set A : Subgroup F := P ⊓ Subgroup.centralizer ({z} : Set F) with hA
  obtain ⟨κ, hκJ, hκ2, hκz⟩ := exists_inverted_of_act hJ hzJ hz2 hnt
  have hJK : J ∈ twinClass K J := ⟨1, K.one_mem, (conjSub_one J).symm⟩
  have hJg : conjSub g J ∈ twinClass K J := ⟨g, hgK, rfl⟩
  have hgt : g * t = t * g := htK g hgK
  have hgz : g * z = z * g := hzK g hgK
  obtain ⟨κ', hκ'⟩ : ∃ κ' : F, κ' = g * κ * g⁻¹ := ⟨_, rfl⟩
  have hκ'J : κ' ∈ conjSub g J := by rw [hκ']; exact conj_mem_conjSub hκJ
  have hzκ : z * κ * z⁻¹ = κ * t := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rw [hzi, hκz]
    calc κ⁻¹ = κ * (κ * κ)⁻¹ := by group
      _ = κ * t⁻¹ := by rw [hκ2]
      _ = κ * t := by rw [inv_eq_of_mul_eq_one_right ht2]
  have hzg : z * g * z⁻¹ = g := by rw [← hgz]; group
  have hztκ' : z * κ' * z⁻¹ = κ' * t := by
    have e1 : z * κ' * z⁻¹ = (z * g * z⁻¹) * (z * κ * z⁻¹) * (z * g * z⁻¹)⁻¹ := by
      rw [hκ']; group
    rw [e1, hzg, hzκ, hκ']
    calc g * (κ * t) * g⁻¹ = (g * κ * g⁻¹) * (g * t * g⁻¹) := by group
      _ = g * κ * g⁻¹ * t := by rw [hgt]; group
  have htκ' : t * κ' = κ' * t :=
    ((mem3_of_mem_twinClass hJ htK hJg).mul_comm_of_mem hκ'J).symm
  have hcom : κ * κ' = κ' * κ :=
    commute_of_mem_twinClass hJ htK htex hJK hJg (fun h => hne h.symm) hκJ hκ'J
  obtain ⟨δ, hδ⟩ : ∃ δ : F, δ = κ * κ' := ⟨_, rfl⟩
  have hδP : δ ∈ P := by
    rw [hδ]
    exact P.mul_mem (le_twinProd hJK hκJ) (le_twinProd hJg hκ'J)
  have hzδ : z * δ * z⁻¹ = δ := by
    have e1 : z * δ * z⁻¹ = (z * κ * z⁻¹) * (z * κ' * z⁻¹) := by rw [hδ]; group
    rw [e1, hzκ, hztκ', hδ]
    calc κ * t * (κ' * t) = κ * (t * κ') * t := by group
      _ = κ * (κ' * t) * t := by rw [htκ']
      _ = κ * κ' * (t * t) := by group
      _ = κ * κ' := by rw [ht2, mul_one]
  have hδz : δ * z = z * δ := by
    have := congrArg (· * z) hzδ
    simp only [inv_mul_cancel_right] at this
    exact this.symm
  have hδA : δ ∈ A := ⟨hδP, Subgroup.mem_centralizer_singleton_iff.mpr hδz⟩
  have hgδ : g * δ = δ * g := hcomm g hgK hodd δ hδA
  have hκnc : ∃ u ∈ J, κ * u ≠ u * κ := by
    by_contra hcon
    push Not at hcon
    refine Mem3.not_forall_comm_of_sq_eq hJ hκJ hκ2 fun u hu => ?_
    rw [hOJ, Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcon u hu)
  have hJmov : ∃ l ∈ J, l * δ ≠ δ * l := by
    obtain ⟨u, hu, hne'⟩ := hκnc
    refine ⟨u, hu, fun h => hne' ?_⟩
    have c : u * κ' = κ' * u :=
      commute_of_mem_twinClass hJ htK htex hJK hJg (fun h => hne h.symm) hu hκ'J
    have h' : u * κ * κ' = κ * u * κ' := by
      calc u * κ * κ' = u * (κ * κ') := by group
        _ = u * δ := by rw [hδ]
        _ = δ * u := h
        _ = κ * (κ' * u) := by rw [hδ]; group
        _ = κ * (u * κ') := by rw [c]
        _ = κ * u * κ' := by group
    exact (mul_right_cancel h').symm
  have hmov : ∀ L ∈ twinClass K J, (∃ l ∈ L, l * δ ≠ δ * l) → L = J ∨ L = conjSub g J := by
    rintro L hL ⟨l, hl, hne'⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply hne'
    have c1 : l * κ = κ * l := commute_of_mem_twinClass hJ htK htex hL hJK h1 hl hκJ
    have c2 : l * κ' = κ' * l := commute_of_mem_twinClass hJ htK htex hL hJg h2 hl hκ'J
    calc l * δ = l * (κ * κ') := by rw [hδ]
      _ = (l * κ) * κ' := by group
      _ = (κ * l) * κ' := by rw [c1]
      _ = κ * (l * κ') := by group
      _ = κ * (κ' * l) := by rw [c2]
      _ = δ * l := by rw [hδ]; group
  have hgi : g⁻¹ * δ = δ * g⁻¹ := by
    calc g⁻¹ * δ = g⁻¹ * (δ * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * δ) * g⁻¹ := by rw [hgδ]
      _ = δ * g⁻¹ := by group
  have hstab : ∀ L : Subgroup F, (∃ l ∈ L, l * δ ≠ δ * l) →
      (∃ l ∈ conjSub g L, l * δ ≠ δ * l) := by
    rintro L ⟨l, hl, hne'⟩
    refine ⟨g * l * g⁻¹, conj_mem_conjSub hl, fun h => hne' ?_⟩
    calc l * δ = g⁻¹ * (g * l * g⁻¹) * (g * δ) := by group
      _ = g⁻¹ * (g * l * g⁻¹) * (δ * g) := by rw [hgδ]
      _ = g⁻¹ * ((g * l * g⁻¹) * δ) * g := by group
      _ = g⁻¹ * (δ * (g * l * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * δ) * (g * l * g⁻¹ * g) := by group
      _ = (δ * g⁻¹) * (g * l) := by rw [hgi]; group
      _ = δ * l := by group
  have hJ1 : ∃ l ∈ conjSub g J, l * δ ≠ δ * l := hstab J hJmov
  have hJ2 : ∃ l ∈ conjSub g (conjSub g J), l * δ ≠ δ * l := hstab _ hJ1
  have hJg2 : conjSub g (conjSub g J) ∈ twinClass K J := conjSub_mem_twinClass hgK hJg
  rcases hmov _ hJg2 hJ2 with h | h
  ·
    have hsq : conjSub (g * g) J = J := by rw [conjSub_mul]; exact h
    exact hgJ (AscHypOmega.mem_normalizer_of_conjSub_eq (Q3T.conjSub_eq_of_sq hodd hsq))
  ·
    apply hne
    have h1 := congrArg (conjSub g⁻¹) h
    rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h1
    exact h1

theorem odd_mem_normalizer_of_exact {K J : Subgroup F} {z t : F} (hK : Mem3 K z)
    (hJ : Mem3 J t) (htex : ExAt t) (htK : ∀ k ∈ K, k * t = t * k)
    (hzJ : z ∈ Subgroup.normalizer (J : Set F)) (hnt : ¬ ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J)
    {g : F} (hgK : g ∈ K) (hodd : Odd (orderOf g)) : g ∈ Subgroup.normalizer (J : Set F) := by
  classical
  have hOJ : oddCoreOf J = ⊥ := Mem3.oddCoreOf_eq_bot hJ htex
  have hz2 : z * z = 1 := hK.mul_self
  have hzK : ∀ k ∈ K, k * z = z * k := fun k hk => hK.mul_comm_of_mem hk
  have hnt' : ∃ j ∈ J, z * j ≠ j * z := by
    by_contra hcon
    push Not at hcon
    apply hnt
    intro j hj
    rw [hOJ, Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcon j hj)
  set P : Subgroup F := twinProd K J with hP
  set A : Subgroup F := P ⊓ Subgroup.centralizer ({z} : Set F) with hA
  have hA2 : IsPGroup 2 A := isPGroup_twinProd_centralizer hJ htK htex hz2 hzJ hzK hnt'
  have hKA : K ≤ Subgroup.normalizer (A : Set F) :=
    le_normalizer_twinProd_inf_centralizer hzK
  have hAC : A ≤ Subgroup.centralizer ({z} : Set F) := inf_le_right
  have hKC : K ≤ Subgroup.centralizer ({z} : Set F) := hK.le_centralizer
  have hsub : IsSubnormal K (K ⊔ A) :=
    isSubnormal_of_le_of_le hK.subnormal (sup_le hKC hAC) le_sup_left
  have hM : ∀ m ∈ K ⊔ A, ∃ k ∈ K, ∃ a ∈ A, m = k * a := by
    intro m hm
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K A hKA] at hm
    obtain ⟨k, hk, a, ha, hka⟩ := hm
    exact ⟨k, hk, a, ha, hka.symm⟩
  have hAN : A ≤ Subgroup.normalizer (K : Set F) :=
    subnormal_odd_normalizer (Mem3.le_closure_odd hK) hA2 hsub le_sup_right hM
  obtain ⟨e⟩ := Q3T6.nonempty_equiv_of_memberU hJ.member
  have hρz : Q3T6.normalizerToAutSL3 e ⟨z, hzJ⟩ ≠ 1 := by
    intro h1
    exact hnt ((Q3T6.normalizerToAutSL3_eq_one_iff e ⟨z, hzJ⟩).mp h1)
  have hcomm : ∀ g' ∈ K, Odd (orderOf g') → ∀ a ∈ A, g' * a = a * g' := by
    intro g' hg' hg'odd a ha
    have hgz : g' * z = z * g' := hzK g' hg'
    obtain ⟨c, hc⟩ : ∃ c : F, c = g' * a * g'⁻¹ * a⁻¹ := ⟨_, rfl⟩
    have hcK : c ∈ K := by
      have h1 : a * g'⁻¹ * a⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hAN ha) g'⁻¹).mp (K.inv_mem hg')
      have : c = g' * (a * g'⁻¹ * a⁻¹) := by rw [hc]; group
      rw [this]
      exact K.mul_mem hg' h1
    have hcA : c ∈ A := by
      have h1 : g' * a * g'⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hKA hg') a).mp ha
      rw [hc]
      exact A.mul_mem h1 (A.inv_mem ha)
    have hc2 : IsPGroup 2 (Subgroup.zpowers c) := hA2.to_le (Subgroup.zpowers_le.mpr hcA)
    have hc4 : c ^ 4 = 1 := hK.pow_four_of_isPGroup hcK hc2
    have hcc : c * c = 1 ∨ c * c = z := by
      have h1 : (c * c) * (c * c) = 1 := by
        rw [← hc4, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      exact hK.isUniqueInvolution.unique (c * c) (K.mul_mem hcK hcK) h1
    have hga : g' * a * g'⁻¹ = c * a := by rw [hc]; group
    have hconj : g' * a * g'⁻¹ = a ∨ g' * a * g'⁻¹ = z * a := by
      rcases hcc with h | h
      · rcases hK.isUniqueInvolution.unique c hcK h with h' | h'
        · left
          rw [hga, h', one_mul]
        · right
          rw [hga, h']
      ·
        exfalso
        obtain ⟨hcN, hcin⟩ := twinProd_act_mem_inn3 hJ htK htex e hcA.1
        have hsq : (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) ^ 2 =
            Q3T6.normalizerToAutSL3 e ⟨z, hzJ⟩ := by
          rw [← map_pow]
          congr 1
          exact Subtype.ext (by simpa [pow_two] using h)
        have hord4 : (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) ^ 4 = 1 := by
          rw [← map_pow]
          have : (⟨c, hcN⟩ : Subgroup.normalizer (J : Set F)) ^ 4 = 1 := Subtype.ext hc4
          rw [this, map_one]
        have hdvd : orderOf (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) ∣ 4 :=
          orderOf_dvd_of_pow_eq_one hord4
        have hne2 : ¬ orderOf (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) ∣ 2 := by
          intro h2
          have := orderOf_dvd_iff_pow_eq_one.mp h2
          rw [hsq] at this
          exact hρz this
        have h4 : orderOf (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) = 4 := by
          generalize orderOf (Q3T6.normalizerToAutSL3 e ⟨c, hcN⟩) = d at hdvd hne2
          have hle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
          interval_cases d <;> omega
        exact Q3T6.orderOf_ne_four_of_mem_inn3 hcin h4
    exact comm_of_conj_eq_one_or_mul hgz hz2 hK.ne_one hg'odd hconj
  exact odd_mem_normalizer_of_centralizes hJ htex hz2 hzJ hnt htK hzK hcomm hgK hodd

theorem bal368_of_exact {K J : Subgroup F} {z t : F} (hK : Mem3 K z) (hJ : Mem3 J t)
    (hzex : ExAt z) (htex : ExAt t) (htK : ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K)
    (hzJ : z ∈ Subgroup.normalizer (J : Set F)) : ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J := by
  classical
  by_contra hnt
  have hOK : oddCoreOf K = ⊥ := Mem3.oddCoreOf_eq_bot hK hzex
  have htK' : ∀ k ∈ K, k * t = t * k := by
    intro k hk
    have h1 := htK k hk
    rw [hOK, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hz2 : z * z = 1 := hK.mul_self
  obtain ⟨ρ, hρ⟩ := exists_action hJ
  have hρz : ρ ⟨z, hzJ⟩ ≠ 1 := fun h1 => hnt ((hρ ⟨z, hzJ⟩).mp h1)
  have hS : ∀ g ∈ {g : F | g ∈ K ∧ Odd (orderOf g)},
      ∃ hg : g ∈ Subgroup.normalizer (J : Set F), ρ ⟨g, hg⟩ = 1 := by
    rintro g ⟨hgK, hodd⟩
    have hgN : g ∈ Subgroup.normalizer (J : Set F) :=
      odd_mem_normalizer_of_exact hK hJ htex htK' hzJ hnt hgK hodd
    exact ⟨hgN, act_trivial_of_odd ρ hzJ hz2 hρz hgN (hK.mul_comm_of_mem hgK) hodd⟩
  obtain ⟨_, hz1⟩ := closure_act_trivial ρ hS z (Mem3.le_closure_odd hK hK.mem)
  exact hρz hz1

end CFSG.ClassicalInvolution.Q3.Q3T6B
