module

public import CFSG.GF2Type.Aschbacher1976Full.Defs
public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Z4Q8

open CFSG CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


@[expose] def mulSubgroup (Z A : Subgroup G) (hcomm : ∀ c ∈ Z, ∀ a ∈ A, c * a = a * c) :
    Subgroup G where
  carrier := {x | ∃ c ∈ Z, ∃ a ∈ A, x = c * a}
  one_mem' := ⟨1, Z.one_mem, 1, A.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, hc, a, ha, rfl⟩ ⟨c', hc', a', ha', rfl⟩
    refine ⟨c * c', Z.mul_mem hc hc', a * a', A.mul_mem ha ha', ?_⟩
    calc c * a * (c' * a') = c * (a * c') * a' := by group
      _ = c * (c' * a) * a' := by rw [hcomm c' hc' a ha]
      _ = c * c' * (a * a') := by group
  inv_mem' := by
    rintro _ ⟨c, hc, a, ha, rfl⟩
    refine ⟨c⁻¹, Z.inv_mem hc, a⁻¹, A.inv_mem ha, ?_⟩
    rw [hcomm c hc a ha, mul_inv_rev]

theorem sup_eq_mulSubgroup (Z A : Subgroup G) (hcomm : ∀ c ∈ Z, ∀ a ∈ A, c * a = a * c) :
    Z ⊔ A = mulSubgroup Z A hcomm := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · intro c hc
    exact ⟨c, hc, 1, A.one_mem, (mul_one c).symm⟩
  · intro a ha
    exact ⟨1, Z.one_mem, a, ha, (one_mul a).symm⟩
  · rintro x ⟨c, hc, a, ha, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right ha)

theorem natCard_inf_mul_natCard_sup (Z A : Subgroup G)
    (hcomm : ∀ c ∈ Z, ∀ a ∈ A, c * a = a * c) :
    Nat.card ↥(Z ⊓ A) * Nat.card ↥(Z ⊔ A) = Nat.card ↥Z * Nat.card ↥A := by
  let ψ : ↥Z × ↥A →* G :=
    { toFun := fun p => (p.1 : G) * (p.2 : G)
      map_one' := by simp
      map_mul' := fun p q => by
        have h : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
          hcomm (q.1 : G) q.1.2 (p.2 : G) p.2.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (p.1 : G) * q.1 * (p.2 * q.2) = (p.1 : G) * ((q.1 : G) * p.2) * q.2 := by group
          _ = (p.1 : G) * (p.2 * q.1) * q.2 := by rw [h]
          _ = (p.1 : G) * p.2 * (q.1 * q.2) := by group }
  have hψ : ∀ p : ↥Z × ↥A, ψ p = (p.1 : G) * (p.2 : G) := fun p => rfl
  have hrange : ψ.range = Z ⊔ A := by
    rw [sup_eq_mulSubgroup Z A hcomm]
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.1.2, p.2, p.2.2, hψ p⟩
    · rintro ⟨c, hc, a, ha, rfl⟩
      exact ⟨(⟨c, hc⟩, ⟨a, ha⟩), hψ _⟩
  have hker : Nat.card ψ.ker = Nat.card ↥(Z ⊓ A) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨p.1.1, ?_⟩
        invFun := fun w => ⟨(⟨w.1, (Subgroup.mem_inf.mp w.2).1⟩,
          ⟨w.1⁻¹, A.inv_mem (Subgroup.mem_inf.mp w.2).2⟩), ?_⟩
        left_inv := fun p => ?_
        right_inv := fun w => ?_ }
    · have hp : (p.1.1 : G) * (p.1.2 : G) = 1 := p.2
      have hinv : (p.1.1 : G) = ((p.1.2 : G))⁻¹ := eq_inv_of_mul_eq_one_left hp
      exact Subgroup.mem_inf.mpr ⟨p.1.1.2, by rw [hinv]; exact A.inv_mem p.1.2.2⟩
    · show (w.1 : G) * (w.1 : G)⁻¹ = 1
      group
    · obtain ⟨⟨c, a⟩, hp⟩ := p
      have hp' : (c : G) * (a : G) = 1 := hp
      have hca : (c : G) = (a : G)⁻¹ := eq_inv_of_mul_eq_one_left hp'
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext rfl
      · exact Subtype.ext (by simp [hca])
    · apply Subtype.ext
      rfl
  have key := Subgroup.card_ker_mul_card_range ψ
  rw [hker, hrange, Nat.card_prod] at key
  exact key

@[expose] def Zc (z : G) : Subgroup G := (Subgroup.center ↥(Fz z)).map (Fz z).subtype

theorem eq_of_orderOf_eq_two_of_cyclic {P : Type} [Group P] [Finite P] [IsCyclic P] {a b : P}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  haveI : Fintype P := Fintype.ofFinite P
  have hdvd : 2 ∣ Fintype.card P := by
    rw [← ha]
    exact orderOf_dvd_card
  have hcard := IsCyclic.card_orderOf_eq_totient hdvd
  rw [Nat.totient_two] at hcard
  exact Finset.card_le_one.1 hcard.le a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩) b
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)

theorem involution_eq_one_or_eq {Z : Subgroup G} (hZc : IsCyclic Z) {z : G} (hz : orderOf z = 2)
    (hzZ : z ∈ Z) {x : G} (hx : x ∈ Z) (hx2 : x ^ 2 = 1) : x = 1 ∨ x = z := by
  by_cases h1 : x = 1
  · exact Or.inl h1
  · right
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hxord : orderOf x = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) h1
      · exact h
    have hZ' : (⟨x, hx⟩ : ↥Z) = ⟨z, hzZ⟩ :=
      eq_of_orderOf_eq_two_of_cyclic (by rw [Subgroup.orderOf_mk]; exact hxord)
        (by rw [Subgroup.orderOf_mk]; exact hz)
    exact congrArg Subtype.val hZ'

theorem mem_zpowers_of_central {A : Subgroup G} (hA : IsExtraspecialPGroup 2 A)
    (hcardA : Nat.card A = 8) {z : G} (hzA : z ∈ A) (hz : orderOf z = 2)
    (hzcent : ∀ b ∈ A, z * b = b * z) {a : G} (ha : a ∈ A)
    (hacent : ∀ b ∈ A, a * b = b * a) : a ∈ Subgroup.zpowers z := by
  set zA : ↥A := ⟨z, hzA⟩ with hzAdef
  have hzAcent : zA ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hzcent g.1 g.2).symm
  have hle : Subgroup.zpowers zA ≤ Subgroup.center ↥A := Subgroup.zpowers_le.mpr hzAcent
  have hzAord : orderOf zA = 2 := by
    rw [← hz]
    exact (Subgroup.orderOf_mk z hzA).symm ▸ rfl
  have heq : Subgroup.zpowers zA = Subgroup.center ↥A := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hA.2.2.2, Nat.card_zpowers, hzAord]
  have haA : (⟨a, ha⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hacent g.1 g.2).symm
  rw [← heq] at haA
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp haA
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  have := congrArg Subtype.val hn
  simpa [hzAdef] using this

theorem comm_of_mem_cyclic {Z : Subgroup G} (hZc : IsCyclic Z) {x y : G} (hx : x ∈ Z)
    (hy : y ∈ Z) : x * y = y * x := by
  haveI : IsMulCommutative ↥Z := inferInstance
  have h : (⟨x, hx⟩ : ↥Z) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
    IsMulCommutative.is_comm.comm _ _
  exact congrArg Subtype.val h

theorem mem_sup_iff' {Z A : Subgroup G} (hAc : ∀ c ∈ Z, ∀ a ∈ A, c * a = a * c) {x : G} :
    x ∈ Z ⊔ A ↔ ∃ c ∈ Z, ∃ a ∈ A, x = c * a := by
  rw [sup_eq_mulSubgroup Z A hAc]
  rfl

theorem sq_mem_zpowers_of_extraspecial {A : Subgroup G} (hA : IsExtraspecialPGroup 2 A)
    (hcardA : Nat.card A = 8) {z : G} (hzA : z ∈ A) (hz : orderOf z = 2)
    (hzcent : ∀ b ∈ A, z * b = b * z) {a : G} (ha : a ∈ A) : a ^ 2 ∈ Subgroup.zpowers z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hA.1
  have h1 : ((⟨a, ha⟩ : ↥A) : ↥A ⧸ frattini ↥A) ^ 2 = 1 := hpow _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  have hc : (⟨a, ha⟩ : ↥A) ^ 2 ∈ Subgroup.center ↥A := by
    rw [← hA.2.2.1]
    exact h1
  have hcomm2 : ∀ b ∈ A, a ^ 2 * b = b * a ^ 2 := by
    intro b hb
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨b, hb⟩)
    simpa using h.symm
  exact mem_zpowers_of_central hA hcardA hzA hz hzcent (A.pow_mem ha 2) hcomm2

theorem comm_mem_zpowers_of_extraspecial {A : Subgroup G} (hA : IsExtraspecialPGroup 2 A)
    (hcardA : Nat.card A = 8) {z : G} (hzA : z ∈ A) (hz : orderOf z = 2)
    (hzcent : ∀ b ∈ A, z * b = b * z) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
  have hmem : ⁅(⟨a, ha⟩ : ↥A), (⟨b, hb⟩ : ↥A)⁆ ∈ Subgroup.center ↥A := by
    rw [← hA.2.1]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hval : a * b * a⁻¹ * b⁻¹ = ((⁅(⟨a, ha⟩ : ↥A), (⟨b, hb⟩ : ↥A)⁆ : ↥A) : G) := by
    simp [commutatorElement_def]
  have hA' : a * b * a⁻¹ * b⁻¹ ∈ A := by
    rw [hval]
    exact (⁅(⟨a, ha⟩ : ↥A), (⟨b, hb⟩ : ↥A)⁆ : ↥A).2
  have hcomm : ∀ c ∈ A, (a * b * a⁻¹ * b⁻¹) * c = c * (a * b * a⁻¹ * b⁻¹) := by
    intro c hc
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨c, hc⟩)
    rw [hval]
    simpa using h.symm
  exact mem_zpowers_of_central hA hcardA hzA hz hzcent hA' hcomm

theorem exists_noncomm_of_extraspecial {A : Subgroup G} (hA : IsExtraspecialPGroup 2 A)
    (hcardA : Nat.card A = 8) : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have htop : Subgroup.center ↥A = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro g
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact (hcon g.1 g.2 h.1 h.2).symm
  have h2 := hA.2.2.2
  rw [htop, Subgroup.card_top, hcardA] at h2
  norm_num at h2

theorem unpack {z : G} (hZ : IsZ4Star z 1) (hz : orderOf z = 2) :
    ∃ Z A : Subgroup G, Zc z = Z ∧ IsCyclic Z ∧ Nat.card Z = 4 ∧ z ∈ Z ∧
      IsExtraspecialPGroup 2 A ∧ Nat.card A = 8 ∧ z ∈ A ∧
      (∀ c ∈ Z, ∀ a ∈ A, c * a = a * c) ∧ Z ⊔ A = Fz z ∧ Z ⊓ A = Subgroup.zpowers z := by
  obtain ⟨Z, A, hZc, hZcard, hzZ, hA, hAcard, hAc, hsup, hinf⟩ := hZ
  have hAcard' : Nat.card A = 8 := by norm_num at hAcard; exact hAcard
  have hAcomm : ∀ c ∈ Z, ∀ a ∈ A, c * a = a * c := fun c hc a ha =>
    Subgroup.mem_centralizer_iff.mp (hAc ha) c hc
  have hzA : z ∈ A := by
    have h : z ∈ Z ⊓ A := by rw [hinf]; exact Subgroup.mem_zpowers z
    exact (Subgroup.mem_inf.mp h).2
  have hzcent : ∀ b ∈ A, z * b = b * z := fun b hb => hAcomm z hzZ b hb
  refine ⟨Z, A, ?_, hZc, hZcard, hzZ, hA, hAcard', hzA, hAcomm, hsup, hinf⟩
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    have hwF : (w : G) ∈ Z ⊔ A := by rw [hsup]; exact w.2
    show (w : G) ∈ Z
    obtain ⟨c, hc, a, ha, hwca⟩ := (mem_sup_iff' hAcomm).mp hwF
    have hac : ∀ b ∈ A, a * b = b * a := by
      intro b hb
      have hbF : b ∈ Fz z := by rw [← hsup]; exact Subgroup.mem_sup_right hb
      have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨b, hbF⟩)
      simp only [Subgroup.coe_mul, hwca] at h
      have hcb : c * b = b * c := hAcomm c hc b hb
      have h2 : c * (b * a) = c * (a * b) := by
        calc c * (b * a) = (c * b) * a := by group
          _ = (b * c) * a := by rw [hcb]
          _ = b * (c * a) := by group
          _ = c * a * b := h
          _ = c * (a * b) := by group
      exact (mul_left_cancel h2).symm
    have haZ : a ∈ Z := (Subgroup.zpowers_le.mpr hzZ) (mem_zpowers_of_central hA hAcard' hzA hz hzcent ha hac)
    rw [hwca]
    exact Z.mul_mem hc haZ
  · intro hx
    have hxF : x ∈ Fz z := by rw [← hsup]; exact Subgroup.mem_sup_left hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxF⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgF : (g : G) ∈ Z ⊔ A := by rw [hsup]; exact g.2
    obtain ⟨c, hc, a, ha, hga⟩ := (mem_sup_iff' hAcomm).mp hgF
    simp only [Subgroup.coe_mul]
    rw [hga]
    calc c * a * x = c * (a * x) := by group
      _ = c * (x * a) := by rw [hAcomm x hx a ha]
      _ = (c * x) * a := by group
      _ = (x * c) * a := by rw [comm_of_mem_cyclic hZc hc hx]
      _ = x * (c * a) := by group

end CFSG.GF2Type.Aschbacher1976Full.Z4Q8
