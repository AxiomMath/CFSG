module

public import CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixedCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms

public noncomputable section

namespace CFSG.GroupTheory

open Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.ExtraspecialFixed
open scoped commutatorElement

theorem commutatorElement_mul_mem_center {G : Type*} [Group G] (x y : G) {c d : G}
    (hc : c ∈ center G) (hd : d ∈ center G) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  have hc' : ∀ g : G, c * g * c⁻¹ = g := fun g => by
    rw [← mem_center_iff.1 hc g, mul_inv_cancel_right]
  have hd' : ∀ g : G, d * g * d⁻¹ = g := fun g => by
    rw [← mem_center_iff.1 hd g, mul_inv_cancel_right]
  calc ⁅x * c, y * d⁆ = x * (c * (y * d) * c⁻¹) * x⁻¹ * d⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = x * y * (d * x⁻¹ * d⁻¹) * y⁻¹ := by rw [hc']; group
    _ = ⁅x, y⁆ := by rw [hd', commutatorElement_def]

theorem mulAut_apply_eq_of_mem_center {Q : Type*} [Group Q] (hcard : Nat.card (center Q) = 2)
    (ψ : MulAut Q) {z : Q} (hz : z ∈ center Q) : ψ z = z := by
  have hψz : ψ z ∈ center Q := mem_center_iff.2 fun r => by
    obtain ⟨s, rfl⟩ := ψ.surjective r
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz s]
  by_cases h1 : z = 1
  · rw [h1, map_one]
  · have hne : (⟨ψ z, hψz⟩ : center Q) ≠ 1 := fun h => h1 (ψ.injective
      ((congrArg Subtype.val h).trans (map_one ψ).symm))
    have hne' : (⟨z, hz⟩ : center Q) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
    exact congrArg Subtype.val (eq_of_ne_one_of_card_eq_two hcard hne hne')

theorem map_mulAut_eq_of_isPGroup {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] [Finite H]
    {Q : Subgroup H} [hQn : Q.Normal] (hQp : IsPGroup p Q) (hsimple : IsSimpleGroup (H ⧸ Q))
    (hnab : ¬ IsMulCommutative (H ⧸ Q)) (α : MulAut H) : Q.map (α : H →* H) = Q := by
  set N := Q.map (α : H →* H)
  have hNn : N.Normal := hQn.map _ α.surjective
  have hNp : IsPGroup p N := hQp.map _
  set M := N.map (QuotientGroup.mk' Q)
  have hMn : M.Normal := hNn.map _ (QuotientGroup.mk'_surjective Q)
  have hMp : IsPGroup p M := hNp.map _
  rcases hsimple.eq_bot_or_eq_top_of_normal M with hM | hM
  · have hle : N ≤ Q := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hM
      exact hM
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective α.injective])
  · exfalso
    have hHp : IsPGroup p (H ⧸ Q) := by
      intro x
      have hx : x ∈ M := hM ▸ Subgroup.mem_top x
      obtain ⟨k, hk⟩ := hMp ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have : Nontrivial (H ⧸ Q) := hsimple.toNontrivial
    have hc := (hsimple.eq_bot_or_eq_top_of_normal (center (H ⧸ Q))).resolve_left
      (hHp.bot_lt_center).ne'
    exact hnab (Subgroup.center_eq_top_iff.1 hc)

theorem commutator_eq_top_of_isSimpleGroup {G : Type*} [Group G] (hsimple : IsSimpleGroup G)
    (hnab : ¬ IsMulCommutative G) : commutator G = ⊤ := by
  rcases hsimple.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exact absurd ((commutator_eq_bot_iff G).1 h) hnab
  · exact h

abbrev extraspecialQuotientModule {Q : Type*} [Group Q] (hQ : IsExtraspecialPGroup 2 Q) :
    Module (ZMod 2) (Additive (Abelianization Q)) :=
  AddCommGroup.zmodModule fun v => by
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    rw [← ofMul_pow, ← map_pow]
    have hx : x ^ 2 ∈ commutator Q :=
      hQ.2.1 ▸ sq_mem_center hQ.2.1.le (fun z hz => by
        have := pow_two_eq_one_of_card_eq_two hQ.2.2.2 ⟨z, hz⟩
        exact congrArg Subtype.val this) x
    rw [← Abelianization.ker_of] at hx
    rw [MonoidHom.mem_ker.1 hx]
    rfl

section AutAction

variable {Q : Type*} [Group Q] [Module (ZMod 2) (Additive (Abelianization Q))]

@[expose] def autAbelianizationEnd :
    MulAut Q →* Module.End (ZMod 2) (Additive (Abelianization Q)) where
  toFun ψ := (MonoidHom.toAdditive (Abelianization.map (ψ : Q →* Q))).toZModLinearMap 2
  map_one' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    rfl
  map_mul' ψ ψ' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    rfl

@[expose] def autAbelianizationGL :
    MulAut Q →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (Abelianization Q)) :=
  autAbelianizationEnd.toHomUnits

theorem autAbelianizationGL_apply (ψ : MulAut Q) (q : Q) :
    ((autAbelianizationGL ψ : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (Abelianization Q))) :
        Additive (Abelianization Q) →ₗ[ZMod 2] Additive (Abelianization Q))
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul (Abelianization.of (ψ q)) := rfl

end AutAction

theorem extraspecial_centralizer_inner_automorphisms {H : Type*} [Group H] [Finite H]
    {Q : Subgroup H} [hQn : Q.Normal] (hQ : IsExtraspecialPGroup 2 Q)
    (hCQ : centralizer (Q : Set H) = (center Q).map Q.subtype)
    [Module (ZMod 2) (Additive (Abelianization Q))]
    (χ : center Q →* Multiplicative (ZMod 2)) (hχ : Function.Injective χ)
    (hsimple : IsSimpleGroup (H ⧸ Q)) (hnab : ¬ IsMulCommutative (H ⧸ Q))
    (hinn : ∀ φ : MulAut (H ⧸ Q), ∃ g : H ⧸ Q, φ = MulAut.conj g)
    (hirr : ∀ W : Submodule (ZMod 2) (Additive (Abelianization Q)),
      (∀ h : H, ∀ w ∈ W, ((conjGL (Q := Q) h : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (Abelianization Q))) : Module.End (ZMod 2) (Additive (Abelianization Q))) w ∈
          W) → W = ⊥ ∨ W = ⊤)
    (hcent : ∀ φ ∈ bilinIsometryGroup (commForm hQ.2.1.le χ),
      (∀ h : H, φ * conjGL h = conjGL h * φ) → φ = 1) :
    Group.IsPerfect H ∧ ∀ α : MulAut H, ∃ g : H, α = MulAut.conj g := by
  classical
  have hc : commutator Q ≤ center Q := hQ.2.1.le
  have hcz : center Q ≤ commutator Q := hQ.2.1.ge
  have hcard : Nat.card (center Q) = 2 := hQ.2.2.2
  set b := commForm hQ.2.1.le χ with hbdef
  have hb : b.Nondegenerate := commForm_nondegenerate hc hcz hχ
  have hZc : ∀ z ∈ center Q, ∀ x : H, x * (z : H) * x⁻¹ = z :=
    fun z hz x => conj_eq_of_mem_center hQn hcard hz x
  set π : Q → Additive (Abelianization Q) := fun q => Additive.ofMul (Abelianization.of q)
    with hπdef
  have hπmul : ∀ x y : Q, π (x * y) = π x + π y := fun x y => by
    simp only [hπdef, map_mul, ofMul_mul]
  have hπeq : ∀ x y : Q, π x = π y ↔ x⁻¹ * y ∈ center Q := by
    intro x y
    rw [← hQ.2.1]
    constructor
    · intro h
      exact QuotientGroup.eq.1 (Additive.ofMul.injective h)
    · intro h
      exact congrArg Additive.ofMul (QuotientGroup.eq.2 h)
  have hπ1 : π 1 = 0 := by simp [hπdef]
  have hπ0 : ∀ x : Q, π x = 0 ↔ x ∈ center Q := by
    intro x
    rw [← hπ1, hπeq, mul_one, inv_mem_iff]
  have hbπ : ∀ x y : Q, b (π x) (π y) =
      Multiplicative.toAdd (χ ⟨⁅x, y⁆, hc (commutatorElement_mem_commutator x y)⟩) :=
    fun x y => commForm_apply hc χ x y
  have hconjπ : ∀ (h : H) (q : Q), ((conjGL h : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (Abelianization Q))) : Module.End (ZMod 2) (Additive (Abelianization Q))) (π q) =
        π (MulAut.conjNormal h q) := fun h q => conjGL_apply h q
  have hχ1 : ∀ z : center Q, Multiplicative.toAdd (χ z) = 0 ↔ z = 1 := by
    intro z
    constructor
    · intro h
      exact hχ ((toAdd_eq_zero.1 h).trans (map_one χ).symm)
    · rintro rfl
      rw [map_one]
      rfl
  have hbself : ∀ x : Q, b (π x) (π x) = 0 := by
    intro x
    rw [hbπ, hχ1]
    exact Subtype.ext (commutatorElement_self x)
  obtain ⟨x₁, y₁, hxy⟩ : ∃ x y : Q, ⁅x, y⁆ ≠ 1 := by
    by_contra hne
    simp only [not_exists, ne_eq, not_not] at hne
    have hbot : commutator Q = ⊥ := by
      rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      exact (Subgroup.mem_bot).2 (hne x y)
    have h1 : Nat.card (center Q) = 1 := by rw [← hQ.2.1, hbot, Subgroup.card_bot]
    omega
  have hbxy : b (π x₁) (π y₁) ≠ 0 := by
    rw [hbπ, Ne, hχ1]
    exact fun h => hxy (congrArg Subtype.val h)
  have hnontriv : ∃ (h : H) (q : Q), ((conjGL h : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (Abelianization Q))) : Module.End (ZMod 2) (Additive (Abelianization Q))) (π q) ≠
        π q := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    rcases hirr (Submodule.span (ZMod 2) {π x₁}) (fun h w hw => by
      obtain ⟨q, rfl⟩ := exists_ofMul_of w
      exact (hall h q).symm ▸ hw) with h | h
    · have hx : π x₁ ∈ Submodule.span (ZMod 2) {π x₁} := Submodule.subset_span rfl
      rw [h, Submodule.mem_bot] at hx
      exact hbxy (by rw [hx, map_zero, LinearMap.zero_apply])
    · have hy : π y₁ ∈ Submodule.span (ZMod 2) {π x₁} := h ▸ Submodule.mem_top
      obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.1 hy
      exact hbxy (by rw [← hc', map_smul, hbself, smul_zero])
  have hperf : commutator H = ⊤ := by
    set N := commutator H with hNdef
    have hNn : N.Normal := inferInstance
    have hNQ : ∀ h : H, ∃ n ∈ N, n⁻¹ * h ∈ Q := by
      have hq := commutator_eq_top_of_isSimpleGroup hsimple hnab
      have hmap : N.map (QuotientGroup.mk' Q) = commutator (H ⧸ Q) := by
        rw [hNdef, _root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)]
      intro h
      have hh : (h : H ⧸ Q) ∈ N.map (QuotientGroup.mk' Q) := by
        rw [hmap, hq]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnh⟩ := hh
      exact ⟨n, hn, QuotientGroup.eq.1 hnh⟩
    let W : Submodule (ZMod 2) (Additive (Abelianization Q)) :=
      { carrier := {v | ∃ q : Q, (q : H) ∈ N ∧ π q = v}
        add_mem' := by
          rintro _ _ ⟨q, hq, rfl⟩ ⟨r, hr, rfl⟩
          exact ⟨q * r, N.mul_mem hq hr, hπmul q r⟩
        zero_mem' := ⟨1, N.one_mem, hπ1⟩
        smul_mem' := by
          rintro c _ ⟨q, hq, rfl⟩
          rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
          · exact ⟨1, N.one_mem, by rw [hπ1, zero_smul]⟩
          · exact ⟨q, hq, (one_smul _ _).symm⟩ }
    have hWinv : ∀ h : H, ∀ w ∈ W, ((conjGL h : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (Abelianization Q))) : Module.End (ZMod 2) (Additive (Abelianization Q))) w ∈
          W := by
      rintro h _ ⟨q, hq, rfl⟩
      refine ⟨MulAut.conjNormal h q, ?_, (hconjπ h q).symm⟩
      rw [MulAut.conjNormal_apply]
      exact hNn.conj_mem _ hq h
    rcases hirr W hWinv with hW | hW
    · exfalso
      obtain ⟨h, q, hhq⟩ := hnontriv
      apply hhq
      set r : Q := ⟨h * q * h⁻¹ * (q : H)⁻¹,
        Q.mul_mem (hQn.conj_mem _ q.2 h) (Q.inv_mem q.2)⟩ with hrdef
      have hr : (r : H) ∈ N := by
        change ⁅h, (q : H)⁆ ∈ commutator H
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top h) (Subgroup.mem_top _)
      have hrW : π r ∈ W := ⟨r, hr, rfl⟩
      rw [hW, Submodule.mem_bot] at hrW
      have hconj : MulAut.conjNormal h q = r * q := Subtype.ext (by
        rw [MulAut.conjNormal_apply, Subgroup.coe_mul, hrdef]
        group)
      rw [hconjπ, hconj, hπmul, hrW, zero_add]
    · have hall : ∀ q : Q, ∃ n : Q, (n : H) ∈ N ∧ π n = π q := fun q => by
        have : π q ∈ W := hW ▸ Submodule.mem_top
        exact this
      obtain ⟨n₁, hn₁, he₁⟩ := hall x₁
      obtain ⟨n₂, hn₂, he₂⟩ := hall y₁
      have hcomm_eq : ⁅x₁, y₁⁆ = ⁅n₁, n₂⁆ := by
        have h := hbπ n₁ n₂
        rw [he₁, he₂, hbπ] at h
        exact congrArg Subtype.val (hχ (Multiplicative.toAdd.injective h))
      have hzN : ∀ z ∈ center Q, (z : H) ∈ N := by
        intro z hz
        by_cases hz1 : z = 1
        · rw [hz1]
          exact N.one_mem
        · have hne : (⟨z, hz⟩ : center Q) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
          have hne' : (⟨⁅x₁, y₁⁆, hc (commutatorElement_mem_commutator x₁ y₁)⟩ : center Q) ≠ 1 :=
            fun h => hxy (congrArg Subtype.val h)
          have hzeq : z = ⁅x₁, y₁⁆ :=
            congrArg Subtype.val (eq_of_ne_one_of_card_eq_two hcard hne hne')
          rw [hzeq, hcomm_eq]
          change Q.subtype ⁅n₁, n₂⁆ ∈ N
          rw [map_commutatorElement, hNdef, _root_.commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have hQN : ∀ q : Q, (q : H) ∈ N := by
        intro q
        obtain ⟨n, hn, he⟩ := hall q
        have hc' : n⁻¹ * q ∈ center Q := (hπeq n q).1 he
        have := N.mul_mem hn (hzN _ hc')
        simpa using this
      rw [eq_top_iff]
      intro h _
      obtain ⟨n, hn, hnq⟩ := hNQ h
      have := N.mul_mem hn (hQN ⟨_, hnq⟩)
      simpa using this
  refine ⟨⟨hperf⟩, fun α => ?_⟩
  have hαQ : Q.map (α : H →* H) = Q := map_mulAut_eq_of_isPGroup hQ.1 hsimple hnab α
  obtain ⟨gq, hgq⟩ := hinn (QuotientGroup.congr Q Q α hαQ)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gq
  set α₁ : MulAut H := (MulAut.conj g)⁻¹ * α with hα₁def
  have hα₁apply : ∀ h, α₁ h = g⁻¹ * α h * g := fun h => by
    rw [hα₁def, MulAut.mul_apply, MulAut.conj_inv_apply]
  have hα₁ : ∀ h : H, h⁻¹ * α₁ h ∈ Q := by
    intro h
    have h1 := congrArg (fun φ : MulAut (H ⧸ Q) => φ (h : H ⧸ Q)) hgq
    simp only [QuotientGroup.congr_mk, MulAut.conj_apply] at h1
    have h2 : ((g * h * g⁻¹ : H) : H ⧸ Q) = ((α h : H) : H ⧸ Q) := by
      rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h4 := hQn.conj_mem _ (QuotientGroup.eq.1 h2) g⁻¹
    rw [hα₁apply]
    convert h4 using 1
    group
  have hα₁Q : ∀ q ∈ Q, α₁ q ∈ Q := by
    intro q hq
    have := Q.mul_mem hq (hα₁ q)
    rwa [mul_inv_cancel_left] at this
  have hmap₁ : Q.map (α₁ : H →* H) = Q := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [Subgroup.card_map_of_injective α₁.injective])
    rintro _ ⟨q, hq, rfl⟩
    exact hα₁Q q hq
  set ψ : MulAut Q := (α₁.subgroupMap Q).trans (MulEquiv.subgroupCongr hmap₁) with hψdef
  have hψ : ∀ q : Q, ((ψ q : Q) : H) = α₁ q := fun q => rfl
  have hφπ : ∀ q : Q, ((autAbelianizationGL ψ : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (Abelianization Q))) : Module.End (ZMod 2) (Additive (Abelianization Q))) (π q) =
        π (ψ q) := fun q => autAbelianizationGL_apply ψ q
  have hψc : ∀ z ∈ center Q, ψ z = z := fun z hz => mulAut_apply_eq_of_mem_center hcard ψ hz
  have hφb : autAbelianizationGL ψ ∈ bilinIsometryGroup b := by
    rw [mem_bilinIsometryGroup]
    intro u v
    obtain ⟨x, rfl⟩ := exists_ofMul_of u
    obtain ⟨y, rfl⟩ := exists_ofMul_of v
    change b (((autAbelianizationGL ψ : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (Abelianization Q))) : Module.End (ZMod 2) (Additive (Abelianization Q))) (π x))
      (((autAbelianizationGL ψ : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (Abelianization Q))) : Module.End (ZMod 2) (Additive (Abelianization Q))) (π y)) =
        b (π x) (π y)
    rw [hφπ, hφπ, hbπ, hbπ]
    congr 2
    apply Subtype.ext
    change ⁅ψ x, ψ y⁆ = ⁅x, y⁆
    rw [← map_commutatorElement]
    exact hψc _ (hc (commutatorElement_mem_commutator x y))
  have hφc : ∀ h : H, autAbelianizationGL ψ * conjGL h = conjGL h * autAbelianizationGL ψ := by
    intro h
    apply Units.ext
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    change ((autAbelianizationGL ψ : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (Abelianization Q))) : Module.End (ZMod 2) (Additive (Abelianization Q)))
        (((conjGL h : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (Abelianization Q))) : Module.End (ZMod 2) (Additive (Abelianization Q)))
            (π q)) = ((conjGL h : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (Abelianization Q))) : Module.End (ZMod 2) (Additive (Abelianization Q)))
            (((autAbelianizationGL ψ : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (Abelianization Q))) : Module.End (ZMod 2) (Additive (Abelianization Q))) (π q))
    rw [hconjπ, hφπ, hφπ, hconjπ, hπeq]
    set t : Q := ⟨h⁻¹ * α₁ h, hα₁ h⟩ with htdef
    have hht : α₁ h = h * (t : H) := by
      rw [htdef]
      group
    have hcen : ⁅t, (ψ q)⁻¹⁆ ∈ center Q := hc (commutatorElement_mem_commutator _ _)
    have e3 : ((⁅t, (ψ q)⁻¹⁆ : Q) : H) = (t : H) * (α₁ q)⁻¹ * (t : H)⁻¹ * α₁ q := by
      change Q.subtype ⁅t, (ψ q)⁻¹⁆ = _
      rw [map_commutatorElement, commutatorElement_def, map_inv, inv_inv]
      rfl
    have key : (ψ (MulAut.conjNormal h q))⁻¹ * MulAut.conjNormal h (ψ q) = ⁅t, (ψ q)⁻¹⁆ := by
      apply Subtype.ext
      have hz : h * ((t : H) * (α₁ q)⁻¹ * (t : H)⁻¹ * α₁ q) * h⁻¹ =
          (t : H) * (α₁ q)⁻¹ * (t : H)⁻¹ * α₁ q := by
        rw [← e3]
        exact hZc _ hcen h
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hψ, MulAut.conjNormal_apply, MulAut.conjNormal_apply,
        hψ, map_mul, map_mul, map_inv, e3, ← hz, hht]
      group
    rw [key]
    exact hcen
  have hφ1 : autAbelianizationGL ψ = 1 := hcent _ hφb hφc
  have hψq : ∀ q : Q, q⁻¹ * ψ q ∈ center Q := by
    intro q
    have h := congrArg (fun φ : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (Abelianization Q)) =>
        ((φ : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (Abelianization Q))) :
          Module.End (ZMod 2) (Additive (Abelianization Q))) (π q)) hφ1
    simp only [Units.val_one, Module.End.one_apply] at h
    rw [hφπ] at h
    exact (hπeq q (ψ q)).1 h.symm
  let ℓ : Q →* center Q :=
    { toFun := fun q => ⟨q⁻¹ * ψ q, hψq q⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun q r => Subtype.ext (by
        change (q * r)⁻¹ * ψ (q * r) = q⁻¹ * ψ q * (r⁻¹ * ψ r)
        have hcomm := mem_center_iff.1 (hψq q) r⁻¹
        rw [map_mul, mul_inv_rev]
        calc r⁻¹ * q⁻¹ * (ψ q * ψ r) = r⁻¹ * (q⁻¹ * ψ q) * ψ r := by group
          _ = q⁻¹ * ψ q * r⁻¹ * ψ r := by rw [hcomm]
          _ = q⁻¹ * ψ q * (r⁻¹ * ψ r) := by group) }
  let ℓA : Additive (Abelianization Q) →+ ZMod 2 :=
    AddMonoidHom.mk' (fun v => Multiplicative.toAdd (Abelianization.lift (χ.comp ℓ)
      (Additive.toMul v))) fun v w => by simp
  let ℓV : Additive (Abelianization Q) →ₗ[ZMod 2] ZMod 2 :=
    @AddMonoidHom.toZModLinearMap 2 _ (ZMod 2) _ _ _ Semiring.toModule ℓA
  have hℓV : ∀ q : Q, ℓV (π q) = Multiplicative.toAdd (χ (ℓ q)) := fun q => by
    change Multiplicative.toAdd (Abelianization.lift (χ.comp ℓ) (Abelianization.of q)) = _
    rw [Abelianization.lift_apply_of]
    rfl
  obtain ⟨q₀, hq₀⟩ := exists_ofMul_of ((b.toDual hb).symm ℓV)
  have hψq₀ : ∀ q : Q, α₁ q = q₀ * q * (q₀ : H)⁻¹ := by
    intro q
    have h : b (π q₀) (π q) = ℓV (π q) := by
      rw [show π q₀ = (b.toDual hb).symm ℓV from hq₀]
      exact LinearMap.BilinForm.apply_toDual_symm_apply _ _
    rw [hbπ, hℓV] at h
    have h' : ⁅q₀, q⁆ = q⁻¹ * ψ q := congrArg Subtype.val (hχ (Multiplicative.toAdd.injective h))
    have hcen : ⁅q₀, q⁆ ∈ center Q := hc (commutatorElement_mem_commutator q₀ q)
    have e1 : ψ q = q₀ * q * q₀⁻¹ := by
      have e2 : ψ q = q * ⁅q₀, q⁆ := by rw [h', mul_inv_cancel_left]
      rw [e2, mem_center_iff.1 hcen q, commutatorElement_def]
      group
    rw [← hψ, e1]
    simp
  set α₂ : MulAut H := (MulAut.conj (q₀ : H))⁻¹ * α₁ with hα₂def
  have hα₂apply : ∀ h, α₂ h = (q₀ : H)⁻¹ * α₁ h * q₀ := fun h => by
    rw [hα₂def, MulAut.mul_apply, MulAut.conj_inv_apply]
  have hα₂Q : α₂ ∈ pointwiseFixingAut Q := by
    rw [mem_pointwiseFixingAut]
    intro q hq
    rw [hα₂apply, hψq₀ ⟨q, hq⟩]
    group
  have hCQle : centralizer (Q : Set H) ≤ Q := by
    rw [hCQ]
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hcentral : ∀ x : H, x⁻¹ * α₂ x ∈ center H := by
    intro x
    obtain ⟨hxQ, hxc⟩ := inv_mul_apply_mem_center hCQle hα₂Q x
    rw [mem_center_iff]
    intro y
    have h1 : y * (x⁻¹ * α₂ x) * y⁻¹ = x⁻¹ * α₂ x := hZc _ hxc y
    calc y * (x⁻¹ * α₂ x) = y * (x⁻¹ * α₂ x) * y⁻¹ * y := by group
      _ = x⁻¹ * α₂ x * y := by rw [h1]
  have hα₂1 : α₂ = 1 := by
    have hle : commutator H ≤ MonoidHom.eqLocus (α₂ : H →* H) (MonoidHom.id H) := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      change α₂ ⁅x, y⁆ = ⁅x, y⁆
      have h := commutatorElement_mul_mem_center x y (hcentral x) (hcentral y)
      rw [mul_inv_cancel_left, mul_inv_cancel_left] at h
      rw [map_commutatorElement, h]
    rw [hperf] at hle
    ext x
    exact hle (Subgroup.mem_top x)
  refine ⟨g * q₀, ?_⟩
  have h1 : α = MulAut.conj g * α₁ := by rw [hα₁def, mul_inv_cancel_left]
  have h2 : α₁ = MulAut.conj (q₀ : H) * α₂ := by rw [hα₂def, mul_inv_cancel_left]
  rw [h1, h2, hα₂1, mul_one, map_mul]

end CFSG.GroupTheory
