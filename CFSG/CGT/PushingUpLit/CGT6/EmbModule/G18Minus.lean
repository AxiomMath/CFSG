module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.G18Prop
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.G18Split
public import CFSG.RankThree.PartOne.KFCL.L4Block

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6X
  CFSG.CGT.PushingUpLit.CGT6.TwoEight CFSG.SL2MinimalFaithful

namespace G18

section Flag

variable {n : ℕ}

@[expose] def IsW0 (n : ℕ) (w : Wd (Fz n) (Fq (2 * n))) : Prop :=
  w.2.2 = 0 ∧ sigR n w.2.1 = w.2.1

theorem isW0_sigFun_sub [NeZero n] {x : Fq (2 * n)} (hx : sigR n x = x)
    (w : Wd (Fz n) (Fq (2 * n))) : IsW0 n (sigFun (minusData n) x w - w) := by
  refine ⟨sub_self _, ?_⟩
  show sigR n ((w.2.1 + w.2.2 • x) - w.2.1) = (w.2.1 + w.2.2 • x) - w.2.1
  rw [add_sub_cancel_left, Fz_smul, map_mul, sigR_Fz, hx]

theorem sigFun_eq_of_isW0 [NeZero n] {x : Fq (2 * n)} (hx : sigR n x = x)
    {w : Wd (Fz n) (Fq (2 * n))} (hw : IsW0 n w) : sigFun (minusData n) x w = w := by
  obtain ⟨h1, h2⟩ := hw
  have hB : (minusData n).B x w.2.1 = 0 := by
    apply Subtype.ext
    show x * sigR n w.2.1 + sigR n x * w.2.1 = 0
    rw [h2, hx]
    exact CharTwo.add_self_eq_zero _
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · show w.1 + (minusData n).B x w.2.1 + (minusData n).Q x * w.2.2 = w.1
    rw [hB, h1, mul_zero, add_zero, add_zero]
  · show w.2.1 + w.2.2 • x = w.2.1
    rw [h1, zero_smul, add_zero]

theorem exists_sigFun_sub_eq [NeZero n] {x : Fq (2 * n)} (hx : x ∈ Fz n) (hx0 : x ≠ 0)
    {w : Wd (Fz n) (Fq (2 * n))} (hw : IsW0 n w) :
    ∃ w' : Wd (Fz n) (Fq (2 * n)), sigFun (minusData n) x w' - w' = w := by
  obtain ⟨h1, h2⟩ := hw
  let x' : Fz n := ⟨x, hx⟩
  let γ' : Fz n := ⟨w.2.1, h2⟩
  have hx'0 : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨s0, hs0⟩ : ∃ s0 : Fz n, (s0 : Fq (2 * n)) * x = w.2.1 := by
    refine ⟨γ' * x'⁻¹, ?_⟩
    have h : γ' * x'⁻¹ * x' = γ' := by field_simp
    exact congrArg (fun z : Fz n => (z : Fq (2 * n))) h
  obtain ⟨y, hy⟩ := B_surj (minusData n) hx0 (w.1 + Qval n x * s0)
  refine ⟨(0, y, s0), Prod.ext ?_ (Prod.ext ?_ ?_)⟩
  · show (0 + (minusData n).B x y + Qval n x * s0) - 0 = w.1
    rw [hy]
    have h := CharTwo.add_self_eq_zero (Qval n x * s0)
    linear_combination h
  · show (y + s0 • x) - y = w.2.1
    rw [add_sub_cancel_left, Fz_smul, hs0]
  · show s0 - s0 = w.2.2
    rw [sub_self, h1]

end Flag

section USub

variable {n : ℕ}

theorem ofAdd_mul_inv_ofAdd {G : Type*} [AddGroup G] (a b : G) :
    Multiplicative.ofAdd a * (Multiplicative.ofAdd b)⁻¹ = Multiplicative.ofAdd (a - b) := by
  rw [← ofAdd_neg, ← ofAdd_add, sub_eq_add_neg]

theorem aut_mul_mul_inv {V : Type*} [CommGroup V] (g : MulAut V) (a b : V) :
    g (a * b) * (a * b)⁻¹ = (g a * a⁻¹) * (g b * b⁻¹) := by
  rw [map_mul, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

variable (n) in
@[expose] def uSub : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) where
  carrier := {A | ∃ x ∈ Fz n, A = unipotent x}
  one_mem' := ⟨0, (Fz n).zero_mem, unipotent_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, (Fz n).add_mem hx hy, (unipotent_add x y).symm⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨-x, (Fz n).neg_mem hx, inv_eq_of_mul_eq_one_right ?_⟩
    rw [← unipotent_add, add_neg_cancel, unipotent_zero]

theorem uSub_comm {A B : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))} (hA : A ∈ uSub n)
    (hB : B ∈ uSub n) : A * B = B * A := by
  obtain ⟨x, -, rfl⟩ := hA
  obtain ⟨y, -, rfl⟩ := hB
  rw [← unipotent_add, ← unipotent_add, add_comm]

theorem uSub_sq {A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))} (hA : A ∈ uSub n) :
    A ^ 2 = 1 := by
  obtain ⟨x, -, rfl⟩ := hA
  rw [sq, ← unipotent_add, CharTwo.add_self_eq_zero, unipotent_zero]

theorem card_uSub [NeZero n] : Nat.card (uSub n) = 2 ^ n := by
  rw [← card_Fz n]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : Fz n => (⟨unipotent (x : Fq (2 * n)), x, x.2, rfl⟩ : uSub n)) ⟨?_, ?_⟩)).symm
  · intro a b h
    exact Subtype.ext (unipotent_injective (congrArg Subtype.val h))
  · rintro ⟨A, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

end USub

section Common

variable {n : ℕ}

@[expose] def W0 (n : ℕ) : Subgroup (NMod n) where
  carrier := {m | IsW0 n (Multiplicative.toAdd m)}
  one_mem' := ⟨rfl, map_zero _⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · show (Multiplicative.toAdd a).2.2 + (Multiplicative.toAdd b).2.2 = 0
      rw [ha1, hb1, add_zero]
    · show sigR n ((Multiplicative.toAdd a).2.1 + (Multiplicative.toAdd b).2.1) =
        (Multiplicative.toAdd a).2.1 + (Multiplicative.toAdd b).2.1
      rw [map_add, ha2, hb2]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · show -(Multiplicative.toAdd a).2.2 = 0
      rw [ha1, neg_zero]
    · show sigR n (-(Multiplicative.toAdd a).2.1) = -(Multiplicative.toAdd a).2.1
      rw [map_neg, ha2]

theorem mem_W0 {m : NMod n} : m ∈ W0 n ↔ IsW0 n (Multiplicative.toAdd m) := Iff.rfl

end Common

end G18

open G18

theorem omegaMinus_commonImage {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {n : ℕ} (hn : 2 ≤ n) {Y : Subgroup (MulAut V)}
    (hY : IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥) :
    ∃ (E : Subgroup (MulAut V)) (W : Subgroup V), E ≤ Y ∧ IsElemAbelian2 E ∧ 4 ≤ Nat.card E ∧
      (∀ e ∈ E, ∀ v : V, e v * v⁻¹ ∈ W) ∧ (∀ e ∈ E, ∀ w ∈ W, e w = w) ∧
      (∀ e ∈ E, e ≠ 1 → ∀ w ∈ W, ∃ v : V, w = e v * v⁻¹) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨C, hCfix, -, hCsup⟩ := exists_complement_of_natSection hV hY
  obtain ⟨hinv, θ, φ, hφ⟩ := exists_equiv_of_natSection hY
  obtain ⟨ι, hι⟩ : ∃ ι : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)) →* MulAut V,
      ∀ A, ι A = ((θ.symm A : ↥Y) : MulAut V) :=
    ⟨Y.subtype.comp θ.symm.toMonoidHom, fun A => rfl⟩
  have hι_inj : Function.Injective ι := fun A B h =>
    θ.symm.injective (Subtype.ext (by rw [← hι A, ← hι B]; exact h))
  obtain ⟨E, hE⟩ : ∃ E : Subgroup (MulAut V), E = (uSub n).map ι := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Subgroup V,
      W = ((W0 n).comap φ.toMonoidHom).map (commV Y).subtype := ⟨_, rfl⟩
  have hEmem : ∀ e, e ∈ E ↔ ∃ A ∈ uSub n, ι A = e := fun e => by
    rw [hE]; exact Subgroup.mem_map
  have hWmem : ∀ w, w ∈ W ↔ ∃ t : ↥(commV Y), φ t ∈ W0 n ∧ (t : V) = w := fun w => by
    rw [hW]; exact Subgroup.mem_map
  have hEY : E ≤ Y := by
    intro e he
    obtain ⟨A, -, rfl⟩ := (hEmem e).mp he
    rw [hι]
    exact (θ.symm A).2
  have hEab : IsElemAbelian2 E := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb
      obtain ⟨A, hA, rfl⟩ := (hEmem a).mp ha
      obtain ⟨B, hB, rfl⟩ := (hEmem b).mp hb
      rw [← map_mul, ← map_mul, uSub_comm hA hB]
    · intro a ha
      obtain ⟨A, hA, rfl⟩ := (hEmem a).mp ha
      rw [← map_pow, uSub_sq hA, map_one]
  have hE4 : 4 ≤ Nat.card E := by
    rw [hE, Subgroup.card_map_of_injective hι_inj, card_uSub]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hact : ∀ (x : Fq (2 * n)) (u : ↥(commV Y))
      (hp : ((θ.symm (unipotent x) : ↥Y) : MulAut V) u ∈ commV Y),
      φ ⟨((θ.symm (unipotent x) : ↥Y) : MulAut V) u, hp⟩ =
        Multiplicative.ofAdd (sigFun (minusData n) x (Multiplicative.toAdd (φ u))) := by
    intro x u hp
    rw [hφ (θ.symm (unipotent x)) u hp, MulEquiv.apply_symm_apply, rhoW_apply, minusHom_unip,
      sigPerm_apply]
  have hE_mem : ∀ e ∈ E, ∃ x ∈ Fz n, e = ((θ.symm (unipotent x) : ↥Y) : MulAut V) := by
    intro e he
    obtain ⟨A, ⟨x, hx, rfl⟩, rfl⟩ := (hEmem e).mp he
    exact ⟨x, hx, hι _⟩
  have hdecomp : ∀ v : V, ∃ (c : V) (u : ↥(commV Y)), c ∈ C ∧ v = c * u := by
    intro v
    have hv : v ∈ C ⊔ commV Y := by rw [hCsup]; exact Subgroup.mem_top v
    obtain ⟨c, hc, u, hu, h⟩ := Subgroup.mem_sup.mp hv
    exact ⟨c, ⟨u, hu⟩, hc, h.symm⟩
  have hW1 : ∀ e ∈ E, ∀ v : V, e v * v⁻¹ ∈ W := by
    intro e he v
    obtain ⟨x, hx, rfl⟩ := hE_mem e he
    obtain ⟨c, u, hc, rfl⟩ := hdecomp v
    have hcfix : ((θ.symm (unipotent x) : ↥Y) : MulAut V) c = c :=
      hCfix _ (θ.symm (unipotent x)).2 c hc
    have hp : ((θ.symm (unipotent x) : ↥Y) : MulAut V) u ∈ commV Y :=
      hinv _ (θ.symm (unipotent x)).2 u u.2
    rw [aut_mul_mul_inv, hcfix, mul_inv_cancel, one_mul]
    have hφt : φ (⟨((θ.symm (unipotent x) : ↥Y) : MulAut V) u, hp⟩ * (u : ↥(commV Y))⁻¹) =
        Multiplicative.ofAdd (sigFun (minusData n) x (Multiplicative.toAdd (φ u)) -
          Multiplicative.toAdd (φ u)) := by
      rw [map_mul, map_inv, hact x u hp]
      exact ofAdd_mul_inv_ofAdd _ _
    exact (hWmem _).mpr ⟨_, by
      rw [mem_W0, hφt]
      exact isW0_sigFun_sub ((mem_Fz n x).mp hx) _, rfl⟩
  have hW2 : ∀ e ∈ E, ∀ w ∈ W, e w = w := by
    intro e he w hw
    obtain ⟨x, hx, rfl⟩ := hE_mem e he
    obtain ⟨t, ht, rfl⟩ := (hWmem w).mp hw
    have hp : ((θ.symm (unipotent x) : ↥Y) : MulAut V) t ∈ commV Y :=
      hinv _ (θ.symm (unipotent x)).2 t t.2
    have h1 : φ ⟨((θ.symm (unipotent x) : ↥Y) : MulAut V) t, hp⟩ = φ t := by
      rw [hact x t hp]
      exact congrArg Multiplicative.ofAdd (sigFun_eq_of_isW0 ((mem_Fz n x).mp hx) ht)
    exact congrArg Subtype.val (φ.injective h1)
  have hW3 : ∀ e ∈ E, e ≠ 1 → ∀ w ∈ W, ∃ v : V, w = e v * v⁻¹ := by
    intro e he he1 w hw
    obtain ⟨x, hx, rfl⟩ := hE_mem e he
    obtain ⟨t, ht, rfl⟩ := (hWmem w).mp hw
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact he1 (by simp [unipotent_zero])
    obtain ⟨w', hw'⟩ := exists_sigFun_sub_eq hx hx0 ht
    obtain ⟨u, hu⟩ := φ.surjective (Multiplicative.ofAdd w')
    have hp : ((θ.symm (unipotent x) : ↥Y) : MulAut V) u ∈ commV Y :=
      hinv _ (θ.symm (unipotent x)).2 u u.2
    refine ⟨(u : V), ?_⟩
    have h1 : φ (⟨((θ.symm (unipotent x) : ↥Y) : MulAut V) u, hp⟩ * (u : ↥(commV Y))⁻¹) =
        φ t := by
      rw [map_mul, map_inv, hact x u hp, hu]
      have h2 := ofAdd_mul_inv_ofAdd (sigFun (minusData n) x w') w'
      rw [hw'] at h2
      exact h2
    exact (congrArg Subtype.val (φ.injective h1)).symm
  exact ⟨E, W, hEY, hEab, hE4, hW1, hW2, hW3⟩

theorem omegaMinus_oddInvariant_le_centralizer {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) {Y : Subgroup (MulAut V)}
    (hY : IsNatSectionBy (omegaMinusAct n) Y (commV Y) ⊥) {X : Subgroup (MulAut V)}
    (hX : ¬ 2 ∣ Nat.card X) (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut V))) :
    X ≤ Subgroup.centralizer (Y : Set (MulAut V)) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨E, W, hEY, hEab, hE4, hW1, hW2, hW3⟩ := omegaMinus_commonImage hV hn hY
  have hEc : X ≤ Subgroup.centralizer (E : Set (MulAut V)) :=
    le_centralizer_of_commonImage hV hEab hE4 hW1 hW2 hW3 hX (hEY.trans hYX)
  obtain ⟨-, θ, -⟩ := exists_equiv_of_natSection hY
  have h4 : 4 ≤ Nat.card (Fq (2 * n)) := by
    rw [GaloisField.card 2 (2 * n) (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsimple : IsSimpleGroup ↥Y := by
    have := CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup (K := Fq (2 * n)) h4
    exact θ.isSimpleGroup
  have : Subgroup.Normalizes Y X := ⟨hYX⟩
  let ρ : ↥Y →* MulAut ↥X := MulDistribMulAction.toMulAut ↥Y ↥X
  have hker : ρ.ker ≠ ⊥ := by
    have hE1 : 1 < Nat.card E := by omega
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := E)).mp
      ((Subgroup.one_lt_card_iff_ne_bot E).mp hE1)
    intro hbot
    have hmem : (⟨(a : MulAut V), hEY a.2⟩ : ↥Y) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      refine MulEquiv.ext fun x => Subtype.ext ?_
      have hc := Subgroup.mem_centralizer_iff.mp (hEc x.2) (a : MulAut V) a.2
      show (a : MulAut V) * (x : MulAut V) * (a : MulAut V)⁻¹ = x
      rw [hc, mul_inv_cancel_right]
    rw [hbot] at hmem
    have h1 : (⟨(a : MulAut V), hEY a.2⟩ : ↥Y) = 1 := Subgroup.mem_bot.mp hmem
    have h2 : (a : MulAut V) = 1 := congrArg Subtype.val h1
    exact ha (Subtype.ext h2)
  have htop : ρ.ker = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker).resolve_left hker
  intro x hx
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hk : (⟨y, hy⟩ : ↥Y) ∈ ρ.ker := by rw [htop]; exact Subgroup.mem_top _
  have h1 := congrArg (fun f : MulAut ↥X => ((f ⟨x, hx⟩ : ↥X) : MulAut V)) (MonoidHom.mem_ker.mp hk)
  have h2 : y * x * y⁻¹ = x := h1
  exact mul_inv_eq_iff_eq_mul.mp h2

end CFSG.CGT.PushingUpLit.CGT6
