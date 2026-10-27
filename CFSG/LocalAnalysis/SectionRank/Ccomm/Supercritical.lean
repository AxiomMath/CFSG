module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.Torsion
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.SectionRank.Ccomm

open Subgroup
open scoped commutatorElement

variable {p : ℕ} [hp : Fact p.Prime] {P : Type*} [Group P] [Finite P]

theorem relative_elementary_centralizer_torsion (hp2 : p ≠ 2) (hP : IsPGroup p P)
    {N E : Subgroup P} [N.Normal] [E.Normal] (hEN : E ≤ N)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hmax : ∀ B : Subgroup P, B.Normal → B ≤ N → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x ^ p = 1) → E ≤ B → B = E) :
    closure {x : P | x ∈ N ⊓ centralizer (E : Set P) ∧ x ^ p = 1} = E := by
  set S := {x : P | x ∈ N ⊓ centralizer (E : Set P) ∧ x ^ p = 1} with hSdef
  set X := closure S with hXdef
  let SA : Set (Subgroup P) :=
    {B | B.Normal ∧ B ≤ N ∧ (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ E ≤ B}
  obtain ⟨A, hAmax⟩ := SA.toFinite.exists_maximal ⟨E, inferInstance, hEN, hEab, le_rfl⟩
  obtain ⟨hAn, hAN, hAab, hEA⟩ := hAmax.prop
  have hCA : N ⊓ centralizer (A : Set P) = A :=
    relative_abelian_centralizer hP hAN hAab fun B hBn hBN hBab hAB =>
      le_antisymm (hAmax.2 ⟨hBn, hBN, hBab, hEA.trans hAB⟩ hAB) hAB
  let Ap : Subgroup P :=
    { carrier := {a | a ∈ A ∧ a ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [Commute.mul_pow (hAab a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem A, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hApn : Ap.Normal := ⟨fun a ha g => ⟨hAn.conj_mem a ha.1 g, by
    rw [conj_pow, ha.2, mul_one, mul_inv_cancel]⟩⟩
  have hApE : Ap = E := hmax Ap hApn (fun a ha => hAN ha.1)
    (fun x hx y hy => hAab x hx.1 y hy.1) (fun x hx => hx.2) (fun e he => ⟨hEA he, hEp e he⟩)
  have hAE : ∀ a ∈ A, a ^ p = 1 → a ∈ E := fun a ha hap => by
    rw [← hApE]
    exact ⟨ha, hap⟩
  have hXN : X ≤ N := (closure_le _).2 fun x hx => hx.1.1
  have hXcen : X ≤ centralizer (E : Set P) := (closure_le _).2 fun x hx => hx.1.2
  have hEX : E ≤ X := fun e he => subset_closure
    ⟨⟨hEN he, mem_centralizer_iff.2 fun y hy => hEab y hy e he⟩, hEp e he⟩
  have hXn : X.Normal := by
    refine ⟨fun x hx g => ?_⟩
    induction hx using closure_induction with
    | mem x hx =>
      exact subset_closure ⟨⟨(inferInstance : N.Normal).conj_mem x hx.1.1 g,
        (inferInstance : (centralizer (E : Set P)).Normal).conj_mem x hx.1.2 g⟩, by
          rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩
    | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
    | mul x y _ _ hx hy =>
      have h := mul_mem hx hy
      rwa [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group] at h
    | inv x _ hx =>
      have h := inv_mem hx
      rwa [show (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ by group] at h
  have : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAab a a.2 b b.2)⟩⟩
  let : CommGroup A := IsMulCommutative.instCommGroup
  set ρ : P →* MulAut A := MulAut.conjNormal with hρ
  have hρapp : ∀ (g : P) (a : A), ((ρ g a : A) : P) = g * a * g⁻¹ := fun g a =>
    MulAut.conjNormal_apply g a
  set D := sectionAutomorphisms (E.subgroupOf A) with hD
  have hXD : X ≤ D.comap ρ := by
    rw [closure_le]
    intro x hx
    have hpow : ρ x ^ p = 1 := by rw [← map_pow, hx.2, map_one]
    have hfix : ∀ a : A, a ^ p = 1 → ρ x a = a := fun a ha => by
      have haE : (a : P) ∈ E := hAE a a.2 (by rw [← coe_pow, ha, coe_one])
      apply Subtype.ext
      rw [hρapp, (mem_centralizer_iff.1 hx.1.2 a haE).symm, mul_inv_cancel_right]
    have hodd := odd_abelian_order_p_automorphism hp2 (hP.to_subgroup A) (ρ x) hpow hfix
    refine ⟨fun e he => hfix e ?_, fun a => ?_⟩
    · have := hEp _ (mem_subgroupOf.1 he)
      exact Subtype.ext (by rw [coe_pow, this, coe_one])
    · rw [mem_subgroupOf]
      exact hAE _ (a⁻¹ * ρ x a).2 (by rw [← coe_pow, hodd a, coe_one])
  have hAX : ∀ a ∈ A, ∀ y ∈ X, ⁅a, y⁆ ∈ E := by
    intro a ha y hy
    have h := (hXD hy).2 ⟨a⁻¹, inv_mem ha⟩
    rw [mem_subgroupOf, coe_mul, coe_inv, hρapp] at h
    rw [commutatorElement_def]
    simpa [mul_assoc] using h
  have hXA : ∀ y ∈ X, ∀ z ∈ X, ⁅y, z⁆ ∈ A := by
    intro y hy z hz
    have hcomm : ρ ⁅y, z⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact sectionAutomorphisms_comm _ (hXD hy) (hXD hz)
    have hcen : ⁅y, z⁆ ∈ centralizer (A : Set P) := by
      rw [mem_centralizer_iff]
      intro a ha
      have h := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : P)) hcomm
      simp only [hρapp, MulAut.one_apply] at h
      calc a * ⁅y, z⁆ = ⁅y, z⁆ * a * ⁅y, z⁆⁻¹ * ⁅y, z⁆ := by rw [h]
        _ = ⁅y, z⁆ * a := by group
    have hyz : ⁅y, z⁆ ∈ X := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hy hz) (inv_mem hy)) (inv_mem hz)
    rw [← hCA]
    exact ⟨hXN hyz, hcen⟩
  have hXexp : ∀ x ∈ X, x ^ p = 1 := by
    have hA₀c : ∀ a ∈ A.subgroupOf X, ∀ b ∈ A.subgroupOf X, a * b = b * a := fun a ha b hb =>
      Subtype.ext (hAab _ (mem_subgroupOf.1 ha) _ (mem_subgroupOf.1 hb))
    have hX₀A : commutator X ≤ A.subgroupOf X := by
      rw [_root_.commutator_def, commutator_le]
      intro y _ z _
      rw [mem_subgroupOf]
      exact hXA y y.2 z z.2
    have hE₀ : ∀ a : X, a ∈ E.subgroupOf X ↔ a ∈ A.subgroupOf X ∧ a ^ p = 1 := by
      intro a
      rw [mem_subgroupOf, mem_subgroupOf, ← Subtype.val_inj, coe_pow, coe_one]
      exact ⟨fun h => ⟨hEA h, hEp _ h⟩, fun h => hAE _ h.1 h.2⟩
    have hE₀Z : E.subgroupOf X ≤ center X := by
      intro e he
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 (hXcen g.2) e (mem_subgroupOf.1 he)).symm
    have hA₀E : ⁅A.subgroupOf X, (⊤ : Subgroup X)⁆ ≤ E.subgroupOf X := by
      rw [commutator_le]
      intro a ha g _
      rw [mem_subgroupOf]
      exact hAX a (mem_subgroupOf.1 ha) g g.2
    have hgen : closure {x : X | x ^ p = 1} = ⊤ := by
      have h := closure_closure_coe_preimage (G := P) (k := S)
      rw [eq_top_iff, ← h]
      refine closure_mono fun x hx => ?_
      exact Subtype.ext (by rw [coe_pow, hx.2, coe_one])
    obtain ⟨-, hexp⟩ := odd_torsion_generated_exponent hp2 (A.subgroupOf X) hA₀c hX₀A
      (E.subgroupOf X) hE₀ hE₀Z hA₀E hgen
    intro x hx
    have h := congrArg Subtype.val (hexp ⟨x, hx⟩)
    rwa [coe_pow, coe_one] at h
  by_contra hne
  have hlt : E < X := lt_of_le_of_ne hEX (Ne.symm hne)
  obtain ⟨b, hbX, -, -, B, hBn, hEB, hBX, -, hform, -⟩ := exists_central_extension hP hlt
  have hBab := comm_of_forall_eq_zpow_mul hEab (hXcen hbX) hform
  exact hEB.ne (hmax B hBn (hBX.trans hXN) hBab (fun x hx => hXexp x (hBX hx)) hEB.le).symm

theorem mem_of_relative_elementary_centralizer (hp2 : p ≠ 2) (hP : IsPGroup p P)
    {N E : Subgroup P} [N.Normal] [E.Normal] (hEN : E ≤ N)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hmax : ∀ B : Subgroup P, B.Normal → B ≤ N → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x ^ p = 1) → E ≤ B → B = E) :
    ∀ x ∈ N ⊓ centralizer (E : Set P), x ^ p = 1 → x ∈ E := fun x hx hxp => by
  rw [← relative_elementary_centralizer_torsion hp2 hP hEN hEab hEp hmax]
  exact subset_closure ⟨hx, hxp⟩

theorem normal_central_torsion_enlargement (hp2 : p ≠ 2) (hP : IsPGroup p P)
    {N E : Subgroup P} [N.Normal] [E.Normal] (hEZ : E ≤ N ⊓ centralizer (N : Set P))
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEp : ∀ x ∈ E, x ^ p = 1)
    (hx : ∃ x ∈ N, orderOf x = p ∧ x ∉ E) :
    ∃ Y : Subgroup P, Y.Normal ∧ E < Y ∧ Y ≤ N ∧ (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) ∧
      (∀ x ∈ Y, x ^ p = 1) ∧ ⁅(⊤ : Subgroup P), Y⁆ ≤ E := by
  obtain ⟨x, hxN, hxo, hxE⟩ := hx
  have hEN : E ≤ N := hEZ.trans inf_le_left
  have hnmax : ∃ B : Subgroup P, B.Normal ∧ B ≤ N ∧ (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧
      (∀ x ∈ B, x ^ p = 1) ∧ E < B := by
    by_contra hcon
    push Not at hcon
    have hmax : ∀ B : Subgroup P, B.Normal → B ≤ N → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
        (∀ x ∈ B, x ^ p = 1) → E ≤ B → B = E := fun B hBn hBN hBab hBp hEB =>
      (eq_of_le_of_not_lt hEB (hcon B hBn hBN hBab hBp)).symm
    have hxC : x ∈ N ⊓ centralizer (E : Set P) :=
      ⟨hxN, mem_centralizer_iff.2 fun h hh => (mem_centralizer_iff.1 (hEZ hh).2 x hxN).symm⟩
    exact hxE (mem_of_relative_elementary_centralizer hp2 hP hEN hEab hEp hmax x hxC
      (by rw [← hxo]; exact pow_orderOf_eq_one x))
  obtain ⟨B, hBn, hBN, hBab, hBp, hEB⟩ := hnmax
  obtain ⟨b, -, -, -, Y, hYn, hEY, hYB, -, -, hYcomm⟩ := exists_central_extension hP hEB
  refine ⟨Y, hYn, hEY, hYB.trans hBN, fun x hx y hy => hBab x (hYB hx) y (hYB hy),
    fun x hx => hBp x (hYB hx), ?_⟩
  rw [commutator_le]
  intro g _ y hy
  exact commutatorElement_mem_swap (hYcomm y hy g)

theorem characteristic_torsion_enlargement (hp2 : p ≠ 2) (hP : IsPGroup p P)
    {D : Subgroup P} [hD : D.Characteristic] (hDp : ∀ x ∈ D, x ^ p = 1)
    (hDZ : ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ centralizer (D : Set P))
    (hx : ∃ x ∈ centralizer (D : Set P), orderOf x = p ∧ x ∉ D) :
    ∃ D₁ : Subgroup P, D₁.Characteristic ∧ D < D₁ ∧ (∀ x ∈ D₁, x ^ p = 1) ∧
      ⁅D₁, (⊤ : Subgroup P)⁆ ≤ D₁ ⊓ centralizer (D₁ : Set P) := by
  set N := centralizer (D : Set P) with hNdef
  set E := D ⊓ N with hEdef
  have hNc : N.Characteristic := characteristic_centralizer D
  have hEc : E.Characteristic := characteristic_inf D N
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.1 hy.2 x hx.1
  have hEp : ∀ x ∈ E, x ^ p = 1 := fun x hx => hDp x hx.1
  have hEcenN : E ≤ centralizer (N : Set P) := by
    rw [le_centralizer_iff]
    exact centralizer_le (SetLike.coe_subset_coe.2 inf_le_left)
  have hEZ : E ≤ N ⊓ centralizer (N : Set P) := le_inf inf_le_right hEcenN
  obtain ⟨x, hxN, hxo, hxD⟩ := hx
  obtain ⟨Y, -, hEY, hYN, -, hYp, hYE⟩ :=
    normal_central_torsion_enlargement hp2 hP hEZ hEab hEp ⟨x, hxN, hxo, fun h => hxD h.1⟩
  have hcenE : ∀ {z : P},
      (∀ g : P, ⁅z, g⁆ ∈ E) ↔ z ∈ (center (P ⧸ E)).comap (QuotientGroup.mk' E) :=
    fun {z} => (mk_mem_center_iff (N := E) (x := z)).symm
  set B := closure {z : P | ∃ α : MulAut P, ∃ y ∈ Y, α y = z} with hBdef
  have hBc : B.Characteristic := by
    refine characteristic_of_forall_mem fun φ z hz => ?_
    induction hz using closure_induction with
    | mem z hz =>
      obtain ⟨α, y, hy, rfl⟩ := hz
      exact subset_closure ⟨φ * α, y, hy, rfl⟩
    | one => rw [map_one]; exact one_mem _
    | mul z w _ _ hz hw => rw [map_mul]; exact mul_mem hz hw
    | inv z _ hz => rw [map_inv]; exact inv_mem hz
  have hYB : Y ≤ B := fun y hy => subset_closure ⟨1, y, hy, rfl⟩
  have hgenN : ∀ α : MulAut P, ∀ y ∈ Y, α y ∈ N := fun α y hy => char_apply_mem hNc α (hYN hy)
  have hgenE : ∀ α : MulAut P, ∀ y ∈ Y, ∀ g : P, ⁅α y, g⁆ ∈ E := by
    intro α y hy g
    have h1 : ⁅y, α.symm g⁆ ∈ E :=
      commutatorElement_mem_swap (hYE (commutator_mem_commutator (mem_top _) hy))
    have h2 := char_apply_mem hEc α h1
    rwa [map_commutatorElement, MulEquiv.apply_symm_apply] at h2
  have hBN : B ≤ N := (closure_le _).2 fun z ⟨α, y, hy, hz⟩ => hz ▸ hgenN α y hy
  have hBE' : B ≤ (center (P ⧸ E)).comap (QuotientGroup.mk' E) := (closure_le _).2 (by
    rintro z ⟨α, y, hy, rfl⟩
    exact hcenE.1 (hgenE α y hy))
  have hBE : ∀ z ∈ B, ∀ g : P, ⁅z, g⁆ ∈ E := fun z hz => hcenE.2 (hBE' hz)
  have hregular : ∀ u ∈ N, ∀ v ∈ N, ⁅v, u⁆ ∈ E → (u * v) ^ p = u ^ p * v ^ p := by
    intro u hu v hv hc
    exact mul_pow_prime_eq_of_commute hp.out hp2 (mem_centralizer_iff.1 (hEcenN hc) u hu)
      (mem_centralizer_iff.1 (hEcenN hc) v hv) (hEp _ hc)
  have hBp : ∀ z ∈ B, z ^ p = 1 := by
    let T : Subgroup P :=
      { carrier := {z | z ∈ B ∧ z ^ p = 1}
        mul_mem' := fun {u v} hu hv => ⟨mul_mem hu.1 hv.1, by
          rw [hregular u (hBN hu.1) v (hBN hv.1) (hBE v hv.1 u), hu.2, hv.2, one_mul]⟩
        one_mem' := ⟨one_mem B, one_pow p⟩
        inv_mem' := fun {u} hu => ⟨inv_mem hu.1, by rw [inv_pow, hu.2, inv_one]⟩ }
    have hBT : B ≤ T := (closure_le _).2 fun z hz => by
      obtain ⟨α, y, hy, rfl⟩ := hz
      exact ⟨subset_closure ⟨α, y, hy, rfl⟩, by rw [← map_pow, hYp y hy, map_one]⟩
    exact fun z hz => (hBT hz).2
  set D₁ := D ⊔ B with hD₁def
  have hD₁c : D₁.Characteristic := characteristic_sup D B
  have hEcen : E ≤ centralizer (D₁ : Set P) := by
    rw [le_centralizer_iff, sup_le_iff]
    refine ⟨?_, hBN.trans (le_centralizer_iff.1 hEcenN)⟩
    exact le_centralizer_iff.1 (inf_le_right : E ≤ N)
  have hD₁E' : D₁ ≤ (center (P ⧸ E)).comap (QuotientGroup.mk' E) := by
    rw [sup_le_iff]
    exact ⟨fun d hd => hcenE.1 fun g => hDZ (commutator_mem_commutator hd (mem_top g)), hBE'⟩
  have hD₁E : ∀ z ∈ D₁, ∀ g : P, ⁅z, g⁆ ∈ E := fun z hz => hcenE.2 (hD₁E' hz)
  have hD₁p : ∀ z ∈ D₁, z ^ p = 1 := by
    let T : Subgroup P :=
      { carrier := {z | z ∈ D₁ ∧ z ^ p = 1}
        mul_mem' := fun {u v} hu hv => ⟨mul_mem hu.1 hv.1, by
          have hc := hD₁E v hv.1 u
          rw [mul_pow_prime_eq_of_commute hp.out hp2 (mem_centralizer_iff.1 (hEcen hc) u hu.1)
            (mem_centralizer_iff.1 (hEcen hc) v hv.1) (hEp _ hc), hu.2, hv.2, one_mul]⟩
        one_mem' := ⟨one_mem D₁, one_pow p⟩
        inv_mem' := fun {u} hu => ⟨inv_mem hu.1, by rw [inv_pow, hu.2, inv_one]⟩ }
    have hD₁T : D₁ ≤ T := by
      rw [sup_le_iff]
      exact ⟨fun d hd => ⟨mem_sup_left hd, hDp d hd⟩, fun z hz => ⟨mem_sup_right hz, hBp z hz⟩⟩
    exact fun z hz => (hD₁T hz).2
  obtain ⟨y, hyY, hyE⟩ := IsConcreteLE.exists_of_lt hEY
  have hyD₁ : y ∈ D₁ := mem_sup_right (hYB hyY)
  have hyD : y ∉ D := fun h => hyE ⟨h, hYN hyY⟩
  refine ⟨D₁, hD₁c, lt_of_le_of_ne le_sup_left fun h => hyD (h ▸ hyD₁), hD₁p, ?_⟩
  rw [commutator_le]
  intro z hz g _
  have hzg := hD₁E z hz g
  exact ⟨mem_sup_left hzg.1, hEcen hzg⟩

theorem maximal_detecting_supercritical (hp2 : p ≠ 2) (hP : IsPGroup p P)
    {D₀ : Subgroup P} [D₀.Characteristic] (hD₀p : ∀ x ∈ D₀, x ^ p = 1)
    (hD₀Z : ⁅D₀, (⊤ : Subgroup P)⁆ ≤ D₀ ⊓ centralizer (D₀ : Set P))
    (hC₀ : IsPGroup p (fixingSubgroup (MulAut P) (D₀ : Set P))) :
    ∃ D : Subgroup P, ∃ _ : D.Characteristic, D₀ ≤ D ∧ (∀ x ∈ D, x ^ p = 1) ∧
      ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ centralizer (D : Set P) ∧
      (∀ x ∈ centralizer (D : Set P), orderOf x = p → x ∈ D) ∧
      IsPGroup p (frattiniAction D).ker ∧ (Nontrivial P → D ≠ ⊥) := by
  let SF : Set (Subgroup P) := {U | U.Characteristic ∧ D₀ ≤ U ∧ (∀ x ∈ U, x ^ p = 1) ∧
    ⁅U, (⊤ : Subgroup P)⁆ ≤ U ⊓ centralizer (U : Set P)}
  obtain ⟨D, hDmax⟩ := SF.toFinite.exists_maximal ⟨D₀, inferInstance, le_rfl, hD₀p, hD₀Z⟩
  obtain ⟨hDc, hD₀D, hDp, hDZ⟩ := hDmax.prop
  have htors : ∀ x ∈ centralizer (D : Set P), orderOf x = p → x ∈ D := by
    intro x hx hxo
    by_contra hxD
    obtain ⟨D₁, hD₁c, hDD₁, hD₁p, hD₁Z⟩ :=
      characteristic_torsion_enlargement hp2 hP hDp hDZ ⟨x, hx, hxo, hxD⟩
    exact hDD₁.not_ge (hDmax.2 ⟨hD₁c, hD₀D.trans hDD₁.le, hD₁p, hD₁Z⟩ hDD₁.le)
  refine ⟨D, hDc, hD₀D, hDp, hDZ, htors, ?_, ?_⟩
  · rintro ⟨α, hα⟩
    have hr : MulAut.characteristic D α ∈ (autQuotient (frattini D)).ker := hα
    obtain ⟨a, ha⟩ := isPGroup_ker_autQuotient_frattini (hP.to_subgroup D) ⟨_, hr⟩
    have h1 : MulAut.characteristic D (α ^ p ^ a) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    have hfixD : α ^ p ^ a ∈ fixingSubgroup (MulAut P) (D₀ : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact congrArg (fun β : MulAut D => ((β ⟨y, hD₀D hy⟩ : D) : P)) h1
    obtain ⟨b, hb⟩ := hC₀ ⟨_, hfixD⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have h2 := congrArg Subtype.val hb
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2 ⊢
    rw [pow_add, pow_mul]
    exact h2
  · intro hnt hDbot
    obtain ⟨n, hn0, hn⟩ := hP.nontrivial_iff_card.1 hnt
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (hn ▸ dvd_pow_self p hn0.ne')
    have hxcen : x ∈ centralizer (D : Set P) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [hDbot, SetLike.mem_coe, mem_bot] at hh
      rw [hh, one_mul, mul_one]
    have hxD := htors x hxcen hx
    rw [hDbot, mem_bot] at hxD
    rw [hxD, orderOf_one] at hx
    exact hp.out.one_lt.ne hx

theorem supercritical_witness (hp2 : p ≠ 2) {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) [Nontrivial Q] :
    ∃ D : Subgroup Q, ∃ _ : D.Characteristic, D ≠ ⊥ ∧ (∀ x ∈ D, x ^ p = 1) ∧
      ⁅D, (⊤ : Subgroup Q)⁆ ≤ D ⊓ centralizer (D : Set Q) ∧
      (∀ x ∈ centralizer (D : Set Q), orderOf x = p → x ∈ D) ∧
      IsPGroup p (frattiniAction D).ker := by
  obtain ⟨D₀, hD₀c, hD₀ne, hD₀Z, hD₀p, hC₀⟩ := odd_critical_exponent_subgroup hp2 hQ
  obtain ⟨D, hDc, hD₀D, hDp, hDZ, htors, hker, -⟩ :=
    maximal_detecting_supercritical hp2 hQ hD₀p hD₀Z hC₀
  exact ⟨D, hDc, fun h => hD₀ne (le_bot_iff.1 (h ▸ hD₀D)), hDp, hDZ, htors, hker⟩

end CFSG.SectionRank.Ccomm
