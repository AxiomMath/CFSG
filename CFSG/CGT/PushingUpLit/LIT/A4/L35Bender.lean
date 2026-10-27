module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Cfg
public import CFSG.Goldschmidt.Steps.LemmaXBasic
public import CFSG.Timmesfeld.Closure.Bender

public section

namespace CFSG.CGT.PushingUpLit.A4.L35

open CFSG CFSG.Open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A4.L34

variable {G : Type} [Group G] {M : Subgroup G}

theorem SE.mem_of_even (hse : fusionStronglyEmbedded M) {S : Subgroup G} {h : G}
    (hS : S ≤ M ⊓ conjSub h M) (hev : Even (Nat.card S)) : h ∈ M := by
  by_contra hh
  have hodd := hse.2.2 h⁻¹ (fun h' => hh (by simpa using M.inv_mem h'))
  have e : M.map (MulAut.conj h⁻¹⁻¹).toMonoidHom = conjSub h M := by
    rw [inv_inv]
    rfl
  rw [e] at hodd
  have hdvd := Subgroup.card_dvd_of_le hS
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.2
    (dvd_trans (even_iff_two_dvd.1 hev) hdvd))

theorem even_card_sylow {H : Type} [Group H] [Finite H] (hH : Even (Nat.card H)) (P : Sylow 2 H) :
    Even (Nat.card (P : Subgroup H)) := by
  rw [P.card_eq_multiplicity]
  have h2 : 2 ∣ Nat.card H := even_iff_two_dvd.1 hH
  have hpos : 0 < Nat.card H := Nat.card_pos
  have h1 : 1 ≤ (Nat.card H).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos.ne').1 h2
  exact (Nat.even_pow' (by omega)).2 even_two

variable [Finite G]

theorem SE.exists_sylow_le (hse : fusionStronglyEmbedded M) :
    ∃ Q : Sylow 2 G, (Q : Subgroup G) ≤ M := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥M) := inferInstance
  let P₁ : Subgroup G := (P : Subgroup ↥M).map M.subtype
  have hP₁M : P₁ ≤ M := Subgroup.map_subtype_le _
  have hP₁2 : IsPGroup 2 P₁ := P.isPGroup'.map M.subtype
  obtain ⟨Q, hQ⟩ := hP₁2.exists_le_sylow
  refine ⟨Q, ?_⟩
  have hQM : (Q : Subgroup G) ⊓ M = P₁ := by
    apply le_antisymm
    · intro y hy
      have hy' := Subgroup.mem_inf.1 hy
      have hT2 : IsPGroup 2 ↥((Q ⊓ M : Subgroup G).subgroupOf M) := by
        have h1 : IsPGroup 2 ↥(Q ⊓ M : Subgroup G) := Q.isPGroup'.to_le inf_le_left
        exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      have hPT : (P : Subgroup ↥M) ≤ (Q ⊓ M : Subgroup G).subgroupOf M := by
        intro x hx
        rw [Subgroup.mem_subgroupOf]
        exact ⟨hQ ⟨x, hx, rfl⟩, x.2⟩
      have hTP := P.is_maximal' hT2 hPT
      have : (⟨y, hy'.2⟩ : ↥M) ∈ (Q ⊓ M : Subgroup G).subgroupOf M :=
        Subgroup.mem_subgroupOf.2 hy
      rw [hTP] at this
      exact ⟨_, this, rfl⟩
    · exact le_inf hQ hP₁M
  by_contra hQM'
  have hlt : P₁ < (Q : Subgroup G) := lt_of_le_of_ne hQ (fun e => hQM' (e ▸ hP₁M))
  have hA : P₁.subgroupOf (Q : Subgroup G) < ⊤ := by
    refine lt_of_le_of_ne le_top fun e => ?_
    apply (ne_of_lt hlt)
    apply le_antisymm hQ
    intro x hx
    have := Subgroup.mem_subgroupOf.1 (e ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥(Q : Subgroup G)))
    exact this
  have : Group.IsNilpotent ↥(Q : Subgroup G) := IsPGroup.isNilpotent Q.isPGroup'
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥(Q : Subgroup G)) _ hA
  obtain ⟨n', hn'N, hn'A⟩ := IsConcreteLE.exists_of_lt hnc
  have hn' := Subgroup.mem_normalizer_iff.1 hn'N
  have hn'inv := Subgroup.mem_normalizer_iff.1 (Subgroup.normalizer _ |>.inv_mem hn'N)
  have hnP : (n' : G) ∉ P₁ := fun h => hn'A (Subgroup.mem_subgroupOf.2 h)
  have hS : P₁ ≤ M ⊓ conjSub (n' : G) M := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨hP₁M hx, ?_⟩
    rw [mem_conjSub_iff]
    have hxQ : x ∈ (Q : Subgroup G) := hQ hx
    have h1 := (hn'inv ⟨x, hxQ⟩).1 (Subgroup.mem_subgroupOf.2 hx)
    have h2 := Subgroup.mem_subgroupOf.1 h1
    simpa using hP₁M h2
  have hev : Even (Nat.card P₁) := by
    have : Nat.card P₁ = Nat.card (P : Subgroup ↥M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [this]
    exact even_card_sylow hse.2.1 P
  have hnM : (n' : G) ∈ M := SE.mem_of_even hse hS hev
  exact hnP (hQM ▸ Subgroup.mem_inf.2 ⟨n'.2, hnM⟩)

theorem SE.normalizer_le (hse : fusionStronglyEmbedded M) {Q : Sylow 2 G}
    (hQM : (Q : Subgroup G) ≤ M) : Subgroup.normalizer ((Q : Subgroup G) : Set G) ≤ M := by
  intro n hn
  have hn' := mem_normalizer_iff_conjSub.1 hn
  have hG : Even (Nat.card G) := by
    exact even_iff_two_dvd.2
      (dvd_trans (even_iff_two_dvd.1 hse.2.1) (Subgroup.card_subgroup_dvd_card M))
  refine SE.mem_of_even hse (S := (Q : Subgroup G)) ?_ (even_card_sylow hG Q)
  intro x hx
  refine Subgroup.mem_inf.2 ⟨hQM hx, ?_⟩
  rw [mem_conjSub_iff]
  have : x ∈ conjSub n (Q : Subgroup G) := by rw [hn']; exact hx
  exact hQM (mem_conjSub_iff.1 this)

theorem even_card_of_isPGroup {R : Subgroup G} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    Even (Nat.card R) := by
  obtain ⟨m, hm⟩ := hR2.exists_card_eq
  rw [hm]
  have : m ≠ 0 := by
    rintro rfl
    apply hR1
    rw [pow_zero] at hm
    exact Subgroup.card_eq_one.1 hm
  exact (Nat.even_pow' this).2 even_two

omit [Finite G] in
theorem eq_one_of_mem_pGroup_pow_three {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G} (hx : x ∈ Q)
    (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have h4 : orderOf x = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.of_dvd_left h1 hcop |>.symm |>.symm) h2
  exact orderOf_eq_one_iff.1 h4


theorem no_stronglyEmbedded_Z3Z3 [IsSimpleGroup G] {R : Subgroup G}
    (hse : fusionStronglyEmbedded M) (hRM : R ≤ M) (hR2 : IsPGroup 2 R)
    (hRn : ∀ m ∈ M, conjSub m R = R) (hR1 : R ≠ ⊥) {a b : G} (haM : a ∈ M) (hbM : b ∈ M)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hab : a * b = b * a)
    (hb : b ∉ Subgroup.zpowers a) : False := by
  obtain ⟨Q, hQM⟩ := SE.exists_sylow_le hse
  have hQN : Subgroup.normalizer ((Q : Subgroup G) : Set G) ≤ M := SE.normalizer_le hse hQM
  have hBen := CFSG.BenderSuzuki.bender_suzuki M
    ((CFSG.Goldschmidt.LemmaX.isStronglyEmbeddedOrder_iff M).2 hse)
  obtain ⟨q, k, hB⟩ := CFSG.Timmesfeld.Connectivity.exists_fusionBenderBorel_of_isBenderGroup hBen
  obtain ⟨hBse, ⟨D, hDcyc, hDodd, hQD, hQDsup⟩, -⟩ := hB Q
  have hRQ : R ≤ (Q : Subgroup G) := by
    have hnorm : (R.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRM).2
        (fun m hm => mem_normalizer_iff_conjSub.2 (hRn m hm))
    have hR2' : IsPGroup 2 ↥(R.subgroupOf M) :=
      hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRM).symm
    have hle := hR2'.le_sylow_of_normal (Q.subtype hQM)
    intro x hx
    exact hle (Subgroup.mem_subgroupOf.2 hx : (⟨x, hRM hx⟩ : ↥M) ∈ R.subgroupOf M)
  have hMB : M ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    intro n hn
    refine SE.mem_of_even hBse (S := R) ?_ (even_card_of_isPGroup hR2 hR1)
    intro x hx
    refine Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer (hRQ hx), ?_⟩
    rw [mem_conjSub_iff]
    have : x ∈ conjSub n R := by rw [hRn n hn]; exact hx
    exact Subgroup.le_normalizer (hRQ (mem_conjSub_iff.1 this))
  have hMeq : (Q : Subgroup G) ⊔ D = M := by
    rw [hQDsup]
    exact le_antisymm hQN hMB
  have hDM : D ≤ M := hMeq ▸ le_sup_right
  have hQM' : (Q : Subgroup G) ≤ M := hMeq ▸ le_sup_left
  have hQnorm : ((Q : Subgroup G).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM').2 hMB
  have hcycD : IsCyclic ↥(D.subgroupOf M) := by
    have : IsCyclic D := hDcyc
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hDM).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hDM).symm.surjective
  let π : ↥M →* ↥M ⧸ (Q : Subgroup G).subgroupOf M := QuotientGroup.mk' _
  have hsup : (Q : Subgroup G).subgroupOf M ⊔ D.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQM' hDM, hMeq]
    exact Subgroup.subgroupOf_self M
  have hcycC : IsCyclic (↥M ⧸ (Q : Subgroup G).subgroupOf M) := by
    refine isCyclic_of_surjective (π.comp (D.subgroupOf M).subtype) ?_
    intro c
    induction c using QuotientGroup.induction_on with
    | H m =>
      have hm : m ∈ (Q : Subgroup G).subgroupOf M ⊔ D.subgroupOf M := hsup ▸ Subgroup.mem_top m
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hm
      refine ⟨⟨z, hz⟩, ?_⟩
      show π z = π m
      rw [← hyz, map_mul]
      have : π y = 1 := (QuotientGroup.eq_one_iff y).2 hy
      rw [this, one_mul]
  have hcomm : ∀ p ∈ Subgroup.zpowers a, ∀ q ∈ Subgroup.zpowers b, p * q = q * p := by
    intro p hp q hq
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
  have hcube : ∀ x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_of_commute hcomm).1 hx
    have hpq : Commute p q := hcomm p hp q hq
    have hp3 : p ^ 3 = 1 := by
      have := orderOf_dvd_of_mem_zpowers hp
      rw [ha3] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have hq3 : q ^ 3 = 1 := by
      have := orderOf_dvd_of_mem_zpowers hq
      rw [hb3] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    rw [hpq.mul_pow, hp3, hq3, one_mul]
  have hTM : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ M :=
    sup_le (Subgroup.zpowers_le.2 haM) (Subgroup.zpowers_le.2 hbM)
  let f : ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) →* (↥M ⧸ (Q : Subgroup G).subgroupOf M) :=
    π.comp (Subgroup.inclusion hTM)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : π (Subgroup.inclusion hTM x) = 1 := hx
    have hxQ : ((Subgroup.inclusion hTM x : ↥M) : G) ∈ (Q : Subgroup G) :=
      Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hx')
    exact Subtype.ext (eq_one_of_mem_pGroup_pow_three Q.isPGroup' hxQ (hcube x x.2))
  have : IsCyclic ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := isCyclic_of_injective f hfinj
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b))
  have ht3 : t ^ 3 = 1 := Subtype.ext (by simpa using hcube t t.2)
  have hcardT : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) ≤ 3 := by
    have h1 : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = orderOf t :=
      (orderOf_eq_card_of_forall_mem_zpowers ht).symm
    rw [h1]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ht3)
  have hcarda : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha3]
  have heq : Subgroup.zpowers a = Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcarda]; exact hcardT)
  exact hb (heq ▸ (le_sup_right : Subgroup.zpowers b ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (Subgroup.mem_zpowers b))

end CFSG.CGT.PushingUpLit.A4.L35
