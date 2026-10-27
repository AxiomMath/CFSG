module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal] [Finite Q]
  [Module (ZMod 2) (Additive (Abelianization Q))]

@[expose] def CrossedHomVanishing (hE : IsExtraspecialPGroup 2 Q) (L : Subgroup C) : Prop :=
  ∀ d : L → Additive (Abelianization Q),
    (∀ l l' : L, d (l * l') = d l +
      ((extraspecialConjOrth hE hQn (l : C) : TauCeti.QuadraticMap.orthogonalGroup
        (extraspecialQuadForm hE)) : Additive (Abelianization Q) ≃ₗ[ZMod 2]
          Additive (Abelianization Q)) (d l')) →
    (∀ x : L, (x : C) ∈ Q → d x = 0) →
    ∃ v : Additive (Abelianization Q), ∀ l : L, d l =
      ((extraspecialConjOrth hE hQn (l : C) : TauCeti.QuadraticMap.orthogonalGroup
        (extraspecialQuadForm hE)) : Additive (Abelianization Q) ≃ₗ[ZMod 2]
          Additive (Abelianization Q)) v + v

theorem exists_conj_of_forall_mem_centerOf {L : Subgroup C} (hE : IsExtraspecialPGroup 2 Q)
    (hCQ : centralizer (Q : Set C) ≤ Q) (hQL : Q ≤ L) (hperf : commutator L = ⊤)
    (hZ : centerOf Q ≤ Subgroup.center C) (hH1 : CrossedHomVanishing hE L) (γ : L ≃* L)
    (hγ : ∀ x : L, (x : C) ∈ Q → ((γ x : L) : C) * (x : C)⁻¹ ∈ centerOf Q) :
    ∃ q ∈ Q, ∀ l : L, ((γ l : L) : C) = q * (l : C) * q⁻¹ := by
  classical
  let π : Q → Additive (Abelianization Q) := fun x => Additive.ofMul (Abelianization.of x)
  let ρ : C → (Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)) :=
    fun g => (extraspecialConjOrth hE hQn g : Additive (Abelianization Q) ≃ₗ[ZMod 2]
      Additive (Abelianization Q))
  have hπmul : ∀ x y : Q, π (x * y) = π x + π y := fun x y => ofMul_of_mul x y
  have hπzero : ∀ x : Q, π x = 0 ↔ x ∈ Subgroup.center Q := fun x => ofMul_of_eq_zero_iff hE x
  have hπinv : ∀ x : Q, π (x⁻¹) = -π x := by
    intro x
    change Additive.ofMul (Abelianization.of x⁻¹) = -Additive.ofMul (Abelianization.of x)
    rw [map_inv, ofMul_inv]
  have hπ_eq_iff : ∀ a b : Q, π a = π b ↔ (a : C) * (b : C)⁻¹ ∈ centerOf Q := by
    intro a b
    have h1 : π (a * b⁻¹) = π a - π b := by
      rw [hπmul, hπinv, sub_eq_add_neg]
    rw [← sub_eq_zero, ← h1, hπzero, ← mem_centerOf_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have gammaQ_mem : ∀ a : Q, ((γ ⟨(a : C), hQL a.2⟩ : L) : C) ∈ Q := by
    intro a
    have hz : ((γ ⟨(a : C), hQL a.2⟩ : L) : C) * (a : C)⁻¹ ∈ centerOf Q :=
      hγ ⟨(a : C), hQL a.2⟩ a.2
    have h2 : (((γ ⟨(a : C), hQL a.2⟩ : L) : C) * (a : C)⁻¹) * (a : C) ∈ Q :=
      Q.mul_mem ((show centerOf Q ≤ Q from inf_le_left) hz) a.2
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h2
  let gammaQ : Q → Q := fun a => ⟨((γ ⟨(a : C), hQL a.2⟩ : L) : C), gammaQ_mem a⟩
  have hπgammaQ : ∀ a : Q, π (gammaQ a) = π a := by
    intro a
    rw [hπ_eq_iff]
    exact hγ ⟨(a : C), hQL a.2⟩ a.2
  have hgammaQ_conj : ∀ (l : L) (a : Q),
      conjAut hQn ((γ l : L) : C) (gammaQ a) = gammaQ (conjAut hQn (l : C) a) := by
    intro l a
    let aL : L := ⟨(a : C), hQL a.2⟩
    let b : Q := conjAut hQn (l : C) a
    let bL : L := ⟨(b : C), hQL b.2⟩
    have hbL : bL = l * aL * l⁻¹ := by
      apply Subtype.ext
      simp only [bL, aL, b, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [conjAut_apply]
    have hga : (gammaQ a : C) = ((γ aL : L) : C) := rfl
    have hgb : (gammaQ b : C) = ((γ bL : L) : C) := rfl
    apply Subtype.ext
    rw [conjAut_apply, hga, hgb, hbL]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have step1O : ∀ l : L, extraspecialConjOrth hE hQn ((γ l : L) : C) =
      extraspecialConjOrth hE hQn (l : C) := by
    intro l
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    calc ρ ((γ l : L) : C) (π x)
        = ρ ((γ l : L) : C) (π (gammaQ x)) := by rw [hπgammaQ x]
      _ = π (conjAut hQn ((γ l : L) : C) (gammaQ x)) := by rw [extraspecialConjOrth_apply]
      _ = π (gammaQ (conjAut hQn (l : C) x)) := by rw [hgammaQ_conj]
      _ = π (conjAut hQn (l : C) x) := hπgammaQ _
      _ = ρ (l : C) (π x) := by rw [extraspecialConjOrth_apply]
  have step1 : ∀ l : L, ρ ((γ l : L) : C) = ρ (l : C) := fun l =>
    congrArg (fun x : TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hE) =>
      (x : Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q))) (step1O l)
  have hmem : ∀ l : L, ((γ l : L) : C) * (l : C)⁻¹ ∈ Q := by
    intro l
    refine mem_of_extraspecialConjOrth_eq_one hE hQn hCQ ?_
    rw [map_mul, map_inv, step1O l, mul_inv_cancel]
  let u : L → Q := fun l => ⟨((γ l : L) : C) * (l : C)⁻¹, hmem l⟩
  let d : L → Additive (Abelianization Q) := fun l => π (u l)
  have hd : ∀ l l' : L, d (l * l') = d l + ρ (l : C) (d l') := by
    intro l l'
    have hu : u (l * l') = u l * conjAut hQn (l : C) (u l') := by
      apply Subtype.ext
      change ((γ (l * l') : L) : C) * ((l * l' : L) : C)⁻¹ =
        (((γ l : L) : C) * (l : C)⁻¹) *
          ((l : C) * (((γ l' : L) : C) * (l' : C)⁻¹) * (l : C)⁻¹)
      rw [map_mul γ l l']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    change π (u (l * l')) = π (u l) + ρ (l : C) (π (u l'))
    rw [hu, hπmul, extraspecialConjOrth_apply]
  have hd0 : ∀ x : L, (x : C) ∈ Q → d x = 0 := by
    intro x hx
    change π (u x) = 0
    rw [hπzero]
    exact (mem_centerOf_iff (u x)).1 (hγ x hx)
  obtain ⟨v, hv⟩ := hH1 d hd hd0
  obtain ⟨q, hq⟩ := exists_ofMul_of v
  have hv' : ∀ l : L, d l = ρ (l : C) (π q) + π q := by
    intro l
    have h := hv l
    rw [← hq] at h
    exact h
  have hVaddself : ∀ vv : Additive (Abelianization Q), vv + vv = 0 := by
    intro vv
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [← two_smul (ZMod 2) vv, h2, zero_smul]
  have hVneg : ∀ vv : Additive (Abelianization Q), -vv = vv := by
    intro vv
    calc -vv = -vv + 0 := (add_zero _).symm
      _ = -vv + (vv + vv) := by rw [hVaddself vv]
      _ = (-vv + vv) + vv := by rw [add_assoc]
      _ = 0 + vv := by rw [neg_add_cancel]
      _ = vv := by rw [zero_add]
  let μ : L → C := fun l => (q : C)⁻¹ * ((γ l : L) : C) * (q : C) * (l : C)⁻¹
  have hμmem : ∀ l : L, μ l ∈ centerOf Q := by
    intro l
    let w : Q := ⟨(q : C) * (l : C) * (q : C)⁻¹ * (l : C)⁻¹, by
      have h1 : (l : C) * (q : C)⁻¹ * (l : C)⁻¹ ∈ Q :=
        hQn.conj_mem (q : C)⁻¹ (Q.inv_mem q.2) (l : C)
      have h2 : (q : C) * ((l : C) * (q : C)⁻¹ * (l : C)⁻¹) ∈ Q := Q.mul_mem q.2 h1
      simpa only [mul_assoc] using h2⟩
    have hw_decomp : w = q * (conjAut hQn (l : C) q)⁻¹ := by
      apply Subtype.ext
      change (q : C) * (l : C) * (q : C)⁻¹ * (l : C)⁻¹ =
        (q : C) * ((l : C) * (q : C) * (l : C)⁻¹)⁻¹
      group
    have hπw : π w = π q - π (conjAut hQn (l : C) q) := by
      rw [hw_decomp, hπmul, hπinv, sub_eq_add_neg]
    have hπw2 : π w = π (conjAut hQn (l : C) q * q) := by
      rw [hπw, hπmul, sub_eq_add_neg, hVneg, add_comm]
    have hπuw : π (u l) = π w := by
      have h1 : π (u l) = π (conjAut hQn (l : C) q * q) := by
        change d l = π (conjAut hQn (l : C) q * q)
        rw [hv' l, extraspecialConjOrth_apply, ← hπmul]
      rw [h1, hπw2]
    let z : Q := u l * w⁻¹
    have hz0 : π z = 0 := by
      change π (u l * w⁻¹) = 0
      rw [hπmul, hπinv, hπuw, add_neg_cancel]
    have hzQ : z ∈ Subgroup.center Q := (hπzero z).1 hz0
    have hu_eq : u l = z * w := by
      apply Subtype.ext
      change ((γ l : L) : C) * (l : C)⁻¹ =
        (((γ l : L) : C) * (l : C)⁻¹ * (w : C)⁻¹) * (w : C)
      group
    have hγl : ((γ l : L) : C) = (u l : C) * (l : C) := by
      change ((γ l : L) : C) = (((γ l : L) : C) * (l : C)⁻¹) * (l : C)
      group
    have hwq : (w : C) * ((l : C) * (q : C) * (l : C)⁻¹) = (q : C) := by
      change ((q : C) * (l : C) * (q : C)⁻¹ * (l : C)⁻¹) *
        ((l : C) * (q : C) * (l : C)⁻¹) = (q : C)
      group
    have hzq : (q : C)⁻¹ * (z : C) * (q : C) = (z : C) := by
      have h : (q : C) * (z : C) = (z : C) * (q : C) := by
        simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hzQ q)
      calc (q : C)⁻¹ * (z : C) * (q : C) = (q : C)⁻¹ * ((z : C) * (q : C)) := by group
        _ = (q : C)⁻¹ * ((q : C) * (z : C)) := by rw [← h]
        _ = (z : C) := by group
    have hμl : μ l = (z : C) := by
      dsimp only [μ]
      rw [hγl]
      calc (q : C)⁻¹ * ((u l : C) * (l : C)) * (q : C) * (l : C)⁻¹
          = (q : C)⁻¹ * (u l : C) * ((l : C) * (q : C) * (l : C)⁻¹) := by group
        _ = (q : C)⁻¹ * ((z : C) * (w : C)) * ((l : C) * (q : C) * (l : C)⁻¹) := by
              rw [show (u l : C) = (z : C) * (w : C) by rw [hu_eq, Subgroup.coe_mul]]
        _ = (q : C)⁻¹ * (z : C) * ((w : C) * ((l : C) * (q : C) * (l : C)⁻¹)) := by group
        _ = (q : C)⁻¹ * (z : C) * (q : C) := by rw [hwq]
        _ = (z : C) := hzq
    rw [hμl]
    exact (mem_centerOf_iff z).2 hzQ
  have hμmul : ∀ l l' : L, μ (l * l') = μ l * μ l' := by
    intro l l'
    have hcomm : μ l' * (l : C)⁻¹ = (l : C)⁻¹ * μ l' :=
      ((Subgroup.mem_center_iff.mp (hZ (hμmem l'))) (l : C)⁻¹).symm
    have h1 : μ (l * l') =
        (q : C)⁻¹ * ((γ l : L) : C) * (q : C) * μ l' * (l : C)⁻¹ := by
      dsimp only [μ]
      rw [map_mul γ l l']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    calc μ (l * l')
        = (q : C)⁻¹ * ((γ l : L) : C) * (q : C) * μ l' * (l : C)⁻¹ := h1
      _ = (q : C)⁻¹ * ((γ l : L) : C) * (q : C) * (μ l' * (l : C)⁻¹) := by group
      _ = (q : C)⁻¹ * ((γ l : L) : C) * (q : C) * ((l : C)⁻¹ * μ l') := by rw [hcomm]
      _ = ((q : C)⁻¹ * ((γ l : L) : C) * (q : C) * (l : C)⁻¹) * μ l' := by group
      _ = μ l * μ l' := rfl
  let M : L →* Subgroup.center C :=
    { toFun := fun l => ⟨μ l, hZ (hμmem l)⟩
      map_one' := by
        apply Subtype.ext
        show μ 1 = 1
        dsimp only [μ]
        simp
      map_mul' := fun l l' => Subtype.ext (hμmul l l') }
  have hker : commutator L ≤ M.ker := Abelianization.commutator_subset_ker M
  have hM1 : ∀ l : L, M l = 1 := fun l =>
    MonoidHom.mem_ker.1 (hker (by rw [hperf]; exact Subgroup.mem_top l))
  refine ⟨(q : C), q.2, fun l => ?_⟩
  have h1 : μ l = 1 := by
    have h := congrArg Subtype.val (hM1 l)
    dsimp only [M] at h
    exact h
  have h1' : (q : C)⁻¹ * ((γ l : L) : C) * (q : C) * (l : C)⁻¹ = 1 := by
    dsimp only [μ] at h1
    exact h1
  calc ((γ l : L) : C)
      = (q : C) * ((q : C)⁻¹ * ((γ l : L) : C) * (q : C) * (l : C)⁻¹) *
          (l : C) * (q : C)⁻¹ := by group
    _ = (q : C) * 1 * (l : C) * (q : C)⁻¹ := by rw [h1']
    _ = (q : C) * (l : C) * (q : C)⁻¹ := by group

end CFSG.EvenSporadicStandard.HNRecog
