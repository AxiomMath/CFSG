module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open scoped commutatorElement

variable {M : Type*} [Group M]

structure Extra27 (Q : Subgroup M) : Prop where
  card : Nat.card ↥Q = 27
  exp : ∀ x ∈ Q, x ^ 3 = 1
  cl : ∀ x ∈ Q, ∀ z ∈ Q, ∀ w ∈ Q, ⁅x, z⁆ * w = w * ⁅x, z⁆
  nc : ∃ x ∈ Q, ∃ z ∈ Q, x * z ≠ z * x

namespace Extra27

variable {Q : Subgroup M} (h : Extra27 Q)
include h

theorem finite : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [h.card]; norm_num)

theorem card_center : Nat.card (Subgroup.center ↥Q) = 3 := by
  have : Finite ↥Q := h.finite
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx, z, hz, hxz⟩ := h.nc
  set Z : Subgroup ↥Q := Subgroup.center ↥Q with hZ
  have hdvd : Nat.card Z ∣ 3 ^ 3 := by
    have := Subgroup.card_subgroup_dvd_card Z
    rwa [h.card] at this
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hm3 : m ≤ 3 := hm
  have hfull : Z ≠ ⊤ := fun htop => hxz (by
    have := Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top (⟨z, hz⟩ : ↥Q)) ⟨x, hx⟩
    simpa using congrArg Subtype.val this)
  have hnbot : Z ≠ ⊥ := by
    intro hbot
    have hc : (⁅x, z⁆ : M) ≠ 1 := fun e => hxz (commutatorElement_eq_one_iff_mul_comm.mp e)
    have hxzQ : ⁅x, z⁆ ∈ Q := by
      have e : ⁅x, z⁆ = x * z * x⁻¹ * z⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem hx hz) (Q.inv_mem hx)) (Q.inv_mem hz)
    have hmem : (⟨⁅x, z⁆, hxzQ⟩ : ↥Q) ∈ Z := by
      rw [hZ, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (by simpa using (h.cl x hx z hz g g.2).symm)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hc (congrArg Subtype.val hmem)
  have hm0 : m ≠ 0 := by
    intro h0
    apply hnbot
    apply Subgroup.eq_bot_of_card_eq
    rw [hmeq, h0]; simp
  have hm3' : m ≠ 3 := by
    intro h3
    apply hfull
    refine Subgroup.eq_top_of_card_eq Z ?_
    rw [hmeq, h3, h.card]; norm_num
  have hm2 : m = 1 ∨ m = 2 := by omega
  rcases hm2 with h1 | h2
  · rw [hmeq, h1]; norm_num
  · exfalso
    have hZ9 : Nat.card Z = 9 := by rw [hmeq, h2]; norm_num
    have hq : Nat.card (↥Q ⧸ Z) = 3 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      rw [h.card, hZ9] at this; omega
    have hcyc : IsCyclic (↥Q ⧸ Z) := isCyclic_of_prime_card hq
    have key := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' Z)
      (by rw [QuotientGroup.ker_mk']) 
    exact hxz (by simpa using congrArg Subtype.val (key.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩))

end Extra27

noncomputable def barAutFun (Q' : Type*) [Group Q'] (φ : MulAut Q') :
    MulAut (Q' ⧸ Subgroup.center Q') :=
  QuotientGroup.congr (Subgroup.center Q') (Subgroup.center Q') φ
    ((Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (Subgroup.center Q').Characteristic)) φ)

theorem barAutFun_mk {Q' : Type*} [Group Q'] (φ : MulAut Q') (x : Q') :
    barAutFun Q' φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) :=
  QuotientGroup.congr_mk _ _ _ _ _

noncomputable def barAut (Q' : Type*) [Group Q'] :
    MulAut Q' →* MulAut (Q' ⧸ Subgroup.center Q') where
  toFun := barAutFun Q'
  map_one' := MulEquiv.ext fun x => by
    induction x using QuotientGroup.induction_on with | H x =>
    rw [barAutFun_mk]; rfl
  map_mul' φ ψ := MulEquiv.ext fun x => by
    induction x using QuotientGroup.induction_on with | H x =>
    show barAutFun Q' (φ * ψ) (QuotientGroup.mk x) =
      barAutFun Q' φ (barAutFun Q' ψ (QuotientGroup.mk x))
    rw [barAutFun_mk, barAutFun_mk, barAutFun_mk]; rfl

theorem barAut_mk {Q' : Type*} [Group Q'] (φ : MulAut Q') (x : Q') :
    barAut Q' φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) :=
  barAutFun_mk φ x

namespace Extra27

variable {Q : Subgroup M} (h : Extra27 Q)
include h

theorem exists_psi :
    ∃ ψ : Subgroup.normalizer (Q : Set M) →* GL (Fin 2) (ZMod 3),
      ∀ g : Subgroup.normalizer (Q : Set M), ψ g = 1 ↔
        ∀ x ∈ Q, ∃ z ∈ Q, (∀ q ∈ Q, z * q = q * z) ∧ (g : M) * x * (g : M)⁻¹ = x * z := by
  have : Finite ↥Q := h.finite
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcard := h.card_center
  have hEcard : Nat.card (↥Q ⧸ (Subgroup.center ↥Q)) = 3 ^ 2 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Q)
    rw [h.card, hZcard] at this
    omega
  have hEcomm : ∀ a b : ↥Q ⧸ (Subgroup.center ↥Q), a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H x =>
    induction b using QuotientGroup.induction_on with | H z =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hc := h.cl (z⁻¹ : ↥Q) (z⁻¹ : ↥Q).2 (x⁻¹ : ↥Q) (x⁻¹ : ↥Q).2 g g.2
    have e : (⁅((z⁻¹ : ↥Q) : M), ((x⁻¹ : ↥Q) : M)⁆) = (((x * z)⁻¹ * (z * x) : ↥Q) : M) := by
      simp [commutatorElement_def, mul_assoc]
    rw [e] at hc
    exact hc.symm
  have hEexp : ∀ a : ↥Q ⧸ (Subgroup.center ↥Q), a ^ 3 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with | H x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : x ^ 3 = 1 := Subtype.ext (by simpa using h.exp x x.2)
    rw [this]
    exact Subgroup.one_mem _
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3) hEcomm hEexp hEcard
  refine ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp
    ((barAut ↥Q).comp (Subgroup.normalizerMonoidHom Q)), ?_⟩
  intro g
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    MonoidHom.comp_apply]
  set φ : MulAut ↥Q := Subgroup.normalizerMonoidHom Q g with hφ
  have hφx : ∀ x : ↥Q, ((φ x : ↥Q) : M) = (g : M) * x * (g : M)⁻¹ := fun x => by
    rw [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  constructor
  · intro hb x hx
    have h1 := congrArg
      (fun ψ : MulAut (↥Q ⧸ (Subgroup.center ↥Q)) => ψ (QuotientGroup.mk ⟨x, hx⟩)) hb
    simp only [barAut_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq] at h1
    have hw : ((φ ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩)⁻¹ ∈ (Subgroup.center ↥Q) := (Subgroup.center ↥Q).inv_mem h1
    refine ⟨(((φ ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩)⁻¹ : ↥Q), (((φ ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩)⁻¹ : ↥Q).2, ?_, ?_⟩
    · intro q hq
      have := Subgroup.mem_center_iff.mp hw ⟨q, hq⟩
      exact (congrArg Subtype.val this).symm
    · have e1 := hφx ⟨x, hx⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e1 ⊢
      rw [← e1]; group
  · intro hb
    refine MulEquiv.ext fun a => ?_
    induction a using QuotientGroup.induction_on with | H x =>
    rw [barAut_mk, MulAut.one_apply, QuotientGroup.eq]
    obtain ⟨z, hzQ, hzc, hgz⟩ := hb x x.2
    have hzmem : (⟨z, hzQ⟩ : ↥Q)⁻¹ ∈ (Subgroup.center ↥Q) := by
      refine (Subgroup.center ↥Q).inv_mem ?_
      rw [Subgroup.mem_center_iff]
      intro q
      exact Subtype.ext (hzc q q.2).symm
    have : (φ x)⁻¹ * x = (⟨z, hzQ⟩ : ↥Q)⁻¹ := by
      apply Subtype.ext
      have e1 := hφx x
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e1, hgz]; group
    rw [this]; exact hzmem

theorem mem_zpowers_commutator {x z' : M} (hx : x ∈ Q) (hz' : z' ∈ Q) (hnc : x * z' ≠ z' * x)
    {c : M} (hcQ : c ∈ Q) (hcc : ∀ q ∈ Q, c * q = q * c) : c ∈ Subgroup.zpowers ⁅x, z'⁆ := by
  have : Finite ↥Q := h.finite
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd0Q : ⁅x, z'⁆ ∈ Q := by
    have e : ⁅x, z'⁆ = x * z' * x⁻¹ * z'⁻¹ := by rw [commutatorElement_def]
    rw [e]; exact Q.mul_mem (Q.mul_mem (Q.mul_mem hx hz') (Q.inv_mem hx)) (Q.inv_mem hz')
  have hd0c : (⟨⁅x, z'⁆, hd0Q⟩ : ↥Q) ∈ Subgroup.center ↥Q :=
    Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (by simpa using (h.cl x hx z' hz' g g.2).symm)
  have hd01 : (⟨⁅x, z'⁆, hd0Q⟩ : ↥Q) ≠ 1 := fun e =>
    hnc (commutatorElement_eq_one_iff_mul_comm.mp (by simpa using congrArg Subtype.val e))
  have hd03 : (⟨⁅x, z'⁆, hd0Q⟩ : ↥Q) ^ 3 = 1 := Subtype.ext (by simpa using h.exp _ hd0Q)
  have hord : orderOf (⟨⁅x, z'⁆, hd0Q⟩ : ↥Q) = 3 := orderOf_eq_prime hd03 hd01
  have hle : Subgroup.zpowers (⟨⁅x, z'⁆, hd0Q⟩ : ↥Q) ≤ Subgroup.center ↥Q :=
    Subgroup.zpowers_le.mpr hd0c
  have heq : Subgroup.zpowers (⟨⁅x, z'⁆, hd0Q⟩ : ↥Q) = Subgroup.center ↥Q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, h.card_center])
  have hcmem : (⟨c, hcQ⟩ : ↥Q) ∈ Subgroup.center ↥Q :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcc g g.2).symm
  rw [← heq] at hcmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcmem
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end Extra27

end CFSG.CGT.PushingUpLit.CGT6E
