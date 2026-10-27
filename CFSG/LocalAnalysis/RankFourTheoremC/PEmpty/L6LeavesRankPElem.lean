module

public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.GroupTheory.ElemAbelianClosure

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open Subgroup
open scoped commutatorElement

section Nil

variable {M : Type*} [CommGroup M] [Finite M]

theorem card_le_card_ker_pow (T : M →* M) (n : ℕ) :
    ∀ W : Subgroup M, (∀ w ∈ W, T w ∈ W) → (∀ w ∈ W, (⇑T)^[n] w = 1) →
      Nat.card W ≤ Nat.card (W ⊓ T.ker : Subgroup M) ^ n := by
  induction n with
  | zero =>
    intro W _ hW
    have hWb : W = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      simpa using hW w hw
    subst hWb
    simp
  | succ n ih =>
    intro W hinv hW
    let φ : W →* M := T.comp W.subtype
    have hW₁inv : ∀ w ∈ φ.range, T w ∈ φ.range := by
      rintro _ ⟨w, rfl⟩
      exact ⟨⟨T w, hinv w w.2⟩, rfl⟩
    have hW₁n : ∀ w ∈ φ.range, (⇑T)^[n] w = 1 := by
      rintro _ ⟨w, rfl⟩
      have := hW w w.2
      rw [Function.iterate_succ_apply] at this
      exact this
    have hW₁le : φ.range ≤ W := by
      rintro _ ⟨w, rfl⟩
      exact hinv w w.2
    have h1 := ih φ.range hW₁inv hW₁n
    have h2 : Nat.card φ.ker * Nat.card φ.range = Nat.card W := Subgroup.card_ker_mul_card_range φ
    have h3 : Nat.card φ.ker = Nat.card (W ⊓ T.ker : Subgroup M) := by
      apply Nat.card_congr
      exact
        { toFun := fun x => ⟨(x.1 : M), x.1.2, x.2⟩
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    have h4 : Nat.card (φ.range ⊓ T.ker : Subgroup M) ≤ Nat.card (W ⊓ T.ker : Subgroup M) :=
      Subgroup.card_le_of_le (inf_le_inf_right _ hW₁le)
    calc Nat.card W = Nat.card φ.ker * Nat.card φ.range := h2.symm
      _ ≤ Nat.card (W ⊓ T.ker : Subgroup M) * Nat.card (W ⊓ T.ker : Subgroup M) ^ n := by
          rw [h3]
          exact Nat.mul_le_mul_left _ (h1.trans (Nat.pow_le_pow_left h4 n))
      _ = Nat.card (W ⊓ T.ker : Subgroup M) ^ (n + 1) := by ring

end Nil

section Unipotent

theorem iterate_unipotent_add {A : Type*} [AddCommGroup A] {f : ℕ} [Fact f.Prime]
    [Module (ZMod f) A] (u T : A →+ A) (hu : ∀ a, (⇑u)^[f] a = a) (hT : ∀ a, T a = u a - a) :
    ∀ a, (⇑T)^[f] a = 0 := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · intro a
    exact Subsingleton.elim _ _
  let ul : A →ₗ[ZMod f] A := u.toZModLinearMap f
  let Tl : A →ₗ[ZMod f] A := ul - 1
  have hTliter : ∀ (k : ℕ) (a : A), (⇑Tl)^[k] a = (⇑T)^[k] a := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih =>
      intro a
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      congr 1
      rw [hT]
      rfl
  haveI : CharP (Module.End (ZMod f) A) f :=
    charP_of_injective_algebraMap (algebraMap (ZMod f) (Module.End (ZMod f) A)).injective f
  have hulpow : ul ^ f = 1 := by
    apply LinearMap.ext
    intro x
    rw [Module.End.pow_apply]
    exact hu x
  have hTlpow : Tl ^ f = 0 := by
    have := sub_pow_char_of_commute (R := Module.End (ZMod f) A) f
      (x := ul) (y := (1 : Module.End (ZMod f) A)) (Commute.one_right ul)
    rw [one_pow, hulpow, sub_self] at this
    exact this
  intro a
  have h1 := LinearMap.congr_fun hTlpow a
  rw [Module.End.pow_apply, hTliter] at h1
  exact h1

variable {V : Type*} [CommGroup V]

theorem iterate_unipotent_eq_one {f : ℕ} [Fact f.Prime] (hexp : ∀ v : V, v ^ f = 1)
    (u T : V →* V) (hu : ∀ v, (⇑u)^[f] v = v) (hT : ∀ v, T v = u v * v⁻¹) :
    ∀ v, (⇑T)^[f] v = 1 := by
  haveI : NeZero f := ⟨(Fact.out : f.Prime).ne_zero⟩
  letI : Module (ZMod f) (Additive V) := AddCommGroup.zmodModule (n := f) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hexp, ofMul_one]
  have hiter : ∀ (g : V →* V) (k : ℕ) (v : V),
      (⇑(MonoidHom.toAdditive g))^[k] (Additive.ofMul v) = Additive.ofMul ((⇑g)^[k] v) := by
    intro g k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih (g v)
  have key := iterate_unipotent_add (A := Additive V) (f := f) (MonoidHom.toAdditive u)
    (MonoidHom.toAdditive T) (fun a => by rw [← ofMul_toMul a, hiter, hu])
    (fun a => by
      show Additive.ofMul (T (Additive.toMul a)) = _
      rw [hT]
      simp only [ofMul_mul, ofMul_inv]
      exact (sub_eq_add_neg _ _).symm)
  intro v
  have := key (Additive.ofMul v)
  rw [hiter] at this
  exact this

end Unipotent

section AutBound

variable {G : Type*} [Group G] [Finite G]

@[expose] def fixSub (α : MulAut G) : Subgroup G where
  carrier := {g | α g = g}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv, ha]

theorem mem_fixSub {α : MulAut G} {g : G} : g ∈ fixSub α ↔ α g = g := Iff.rfl

@[expose] def d1Sub {V : Type*} [Group V] (π : G →* V) (hz : π.ker ≤ center G) (α : MulAut G) :
    Subgroup G where
  carrier := {g | π (α g * g⁻¹) = 1}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    have hb' : α b * b⁻¹ ∈ center G := hz hb
    have hc : a⁻¹ * (α b * b⁻¹) = (α b * b⁻¹) * a⁻¹ := mem_center_iff.mp hb' a⁻¹
    have h : α (a * b) * (a * b)⁻¹ = (α a * a⁻¹) * (α b * b⁻¹) := by
      rw [map_mul, mul_inv_rev]
      calc α a * α b * (b⁻¹ * a⁻¹) = α a * ((α b * b⁻¹) * a⁻¹) := by simp only [mul_assoc]
        _ = α a * (a⁻¹ * (α b * b⁻¹)) := by rw [hc]
        _ = (α a * a⁻¹) * (α b * b⁻¹) := by simp only [mul_assoc]
    rw [h, map_mul, ha, hb, one_mul]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at *
    have ha' : α a * a⁻¹ ∈ center G := hz ha
    have hzc : (α a * a⁻¹)⁻¹ ∈ center G := inv_mem ha'
    have h : α a⁻¹ * (a⁻¹)⁻¹ = (α a * a⁻¹)⁻¹ := by
      have hc : a⁻¹ * (α a * a⁻¹)⁻¹ = (α a * a⁻¹)⁻¹ * a⁻¹ := mem_center_iff.mp hzc a⁻¹
      rw [map_inv, inv_inv]
      calc (α a)⁻¹ * a = a⁻¹ * (a * (α a)⁻¹) * a := by group
        _ = a⁻¹ * (α a * a⁻¹)⁻¹ * a := by rw [mul_inv_rev, inv_inv]
        _ = (α a * a⁻¹)⁻¹ * a⁻¹ * a := by rw [hc]
        _ = (α a * a⁻¹)⁻¹ := by group
    rw [h, map_inv, ha, inv_one]

theorem mem_d1Sub {V : Type*} [Group V] {π : G →* V} {hz : π.ker ≤ center G} {α : MulAut G}
    {g : G} : g ∈ d1Sub π hz α ↔ π (α g * g⁻¹) = 1 := Iff.rfl

theorem fixSub_le_d1Sub {V : Type*} [Group V] (π : G →* V) (hz : π.ker ≤ center G)
    (α : MulAut G) : fixSub α ≤ d1Sub π hz α := fun g hg => by
  rw [mem_d1Sub, mem_fixSub.mp hg, mul_inv_cancel, map_one]

theorem card_d1Sub_le {V : Type*} [Group V] (π : G →* V) (hz : π.ker ≤ center G)
    (α : MulAut G) :
    Nat.card (d1Sub π hz α) ≤ Nat.card (fixSub α) * Nat.card π.ker := by
  let φ : d1Sub π hz α →* G := MonoidHom.mk' (fun g => α g * (g : G)⁻¹) (fun a b => by
    have hb : α (b : G) * (b : G)⁻¹ ∈ center G := hz (mem_d1Sub.mp b.2)
    have hc : (a : G)⁻¹ * (α (b : G) * (b : G)⁻¹) = (α (b : G) * (b : G)⁻¹) * (a : G)⁻¹ :=
      mem_center_iff.mp hb (a : G)⁻¹
    rw [Subgroup.coe_mul, map_mul, mul_inv_rev]
    calc α a * α b * ((b : G)⁻¹ * (a : G)⁻¹)
        = α a * ((α b * (b : G)⁻¹) * (a : G)⁻¹) := by simp only [mul_assoc]
      _ = α a * ((a : G)⁻¹ * (α b * (b : G)⁻¹)) := by rw [hc]
      _ = (α a * (a : G)⁻¹) * (α b * (b : G)⁻¹) := by simp only [mul_assoc])
  have hker : Nat.card φ.ker = Nat.card (fixSub α) := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨(x.1 : G), by
          have := x.2
          rw [MonoidHom.mem_ker] at this
          exact mem_fixSub.mpr (mul_inv_eq_one.mp this)⟩
        invFun := fun y => ⟨⟨y.1, fixSub_le_d1Sub π hz α y.2⟩, by
          rw [MonoidHom.mem_ker]
          show α (y : G) * (y : G)⁻¹ = 1
          rw [mem_fixSub.mp y.2, mul_inv_cancel]⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hrange : Nat.card φ.range ≤ Nat.card π.ker := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, rfl⟩
    exact mem_d1Sub.mp x.2
  have := Subgroup.card_ker_mul_card_range φ
  rw [← this, hker]
  exact Nat.mul_le_mul_left _ hrange

theorem card_comap_of_surjective {V : Type*} [Group V] (π : G →* V) (hπ : Function.Surjective π)
    (K : Subgroup V) : Nat.card (K.comap π) = Nat.card π.ker * Nat.card K := by
  haveI : Finite V := Finite.of_surjective π hπ
  have h1 : Nat.card (K.comap π) * (K.comap π).index = Nat.card G := Subgroup.card_mul_index _
  have h2 : (K.comap π).index = K.index := Subgroup.index_comap_of_surjective K hπ
  have h3 : Nat.card K * K.index = Nat.card V := Subgroup.card_mul_index _
  have h4 : Nat.card π.ker * Nat.card V = Nat.card G :=
    Subgroup.card_ker_mul_card_of_surjective hπ
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card (K.comap π) * K.index = Nat.card (K.comap π) * (K.comap π).index := by rw [h2]
    _ = Nat.card π.ker * Nat.card V := h1.trans h4.symm
    _ = Nat.card π.ker * (Nat.card K * K.index) := by rw [h3]
    _ = Nat.card π.ker * Nat.card K * K.index := by ring

theorem two_le_card_fixSub {f : ℕ} [Fact f.Prime] {V : Type*} [CommGroup V]
    (π : G →* V) (hπ : Function.Surjective π) (hz : π.ker ≤ center G)
    (hexp : ∀ v : V, v ^ f = 1) (α : MulAut G) (u : V →* V) (hu : ∀ g, π (α g) = u (π g))
    (huf : ∀ v : V, (⇑u)^[f] v = v) (hdim : f ^ (f + 1) * Nat.card π.ker ≤ Nat.card G) :
    f ^ 2 ≤ Nat.card (fixSub α) := by
  haveI : Finite V := Finite.of_surjective π hπ
  have hfp : f.Prime := Fact.out
  let T : V →* V := MonoidHom.mk' (fun v => u v * v⁻¹) (fun a b => by
    rw [map_mul, mul_inv_rev]
    ac_rfl)
  have hT : ∀ v, T v = u v * v⁻¹ := fun v => rfl
  have hTf := iterate_unipotent_eq_one hexp u T huf hT
  have hnil := card_le_card_ker_pow T f ⊤ (fun _ _ => Subgroup.mem_top _) (fun w _ => hTf w)
  rw [Subgroup.card_top, top_inf_eq] at hnil
  have h4 : Nat.card π.ker * Nat.card V = Nat.card G :=
    Subgroup.card_ker_mul_card_of_surjective hπ
  have hkerpos : 0 < Nat.card π.ker := Nat.card_pos
  have hV : f ^ (f + 1) ≤ Nat.card V := by
    apply Nat.le_of_mul_le_mul_left _ hkerpos
    calc Nat.card π.ker * f ^ (f + 1) = f ^ (f + 1) * Nat.card π.ker := mul_comm _ _
      _ ≤ Nat.card G := hdim
      _ = Nat.card π.ker * Nat.card V := h4.symm
  have hVT : f ^ (f + 1) ≤ Nat.card T.ker ^ f := hV.trans hnil
  have hker_p : IsPGroup f T.ker := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hexp (x : V)⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := f)).mp hker_p
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    have : Nat.card T.ker ^ f ≤ f ^ f := by
      rw [hm, ← pow_mul]
      exact Nat.pow_le_pow_right hfp.pos (by nlinarith)
    have h5 := hVT.trans this
    have := Nat.pow_le_pow_iff_right hfp.one_lt |>.mp h5
    omega
  have hd1 : d1Sub π hz α = T.ker.comap π := by
    ext g
    rw [mem_d1Sub, Subgroup.mem_comap, MonoidHom.mem_ker, hT, map_mul, map_inv, hu]
  have hcard := card_d1Sub_le π hz α
  rw [hd1, card_comap_of_surjective π hπ] at hcard
  have hle : Nat.card T.ker ≤ Nat.card (fixSub α) := by
    apply Nat.le_of_mul_le_mul_left _ hkerpos
    calc Nat.card π.ker * Nat.card T.ker ≤ Nat.card (fixSub α) * Nat.card π.ker := hcard
      _ = Nat.card π.ker * Nat.card (fixSub α) := mul_comm _ _
  calc f ^ 2 ≤ f ^ m := Nat.pow_le_pow_right hfp.pos hm2
    _ = Nat.card T.ker := hm.symm
    _ ≤ Nat.card (fixSub α) := hle

end AutBound


section CentralClassTwo

variable {G : Type*} [Group G] [Finite G]

theorem fixSub_conj (g : G) : fixSub (MulAut.conj g) = Subgroup.centralizer {g} := by
  ext h
  rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff]
  show g * h * g⁻¹ = h ↔ h * g = g * h
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem card_le_centralizer_mul_commutator (hcl : commutator G ≤ center G) (g : G) :
    Nat.card G ≤ Nat.card (Subgroup.centralizer ({g} : Set G)) * Nat.card (commutator G) := by
  have hz : (Abelianization.of : G →* Abelianization G).ker ≤ center G := by
    rw [Abelianization.ker_of]
    exact hcl
  have htop : d1Sub Abelianization.of hz (MulAut.conj g) = ⊤ := by
    rw [eq_top_iff]
    intro h _
    rw [mem_d1Sub, ← MonoidHom.mem_ker, Abelianization.ker_of]
    show g * h * g⁻¹ * h⁻¹ ∈ commutator G
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)
  have := card_d1Sub_le (Abelianization.of : G →* Abelianization G) hz (MulAut.conj g)
  rw [htop, Subgroup.card_top, fixSub_conj, Abelianization.ker_of] at this
  exact this

end CentralClassTwo

section Helpers

variable {X : Type*} [Group X] [Finite X] {f : ℕ}

theorem isPGroup_of_exp (hf : f.Prime) {A : Subgroup X} (hA : ∀ a ∈ A, a ^ f = 1) :
    IsPGroup f A := fun g => ⟨1, by
  apply Subtype.ext
  simpa using hA g g.2⟩

theorem exists_card_eq_pow (hf : f.Prime) {A : Subgroup X} (hA : ∀ a ∈ A, a ^ f = 1) :
    ∃ n : ℕ, Nat.card A = f ^ n := by
  haveI := Fact.mk hf
  exact IsPGroup.iff_card.mp (isPGroup_of_exp hf hA)

theorem mul_card_le_of_lt (hf : f.Prime) {A B : Subgroup X} (hA : ∀ a ∈ A, a ^ f = 1)
    (hBA : B < A) : f * Nat.card B ≤ Nat.card A := by
  obtain ⟨j, hj⟩ := exists_card_eq_pow hf hA
  obtain ⟨i, hi⟩ := exists_card_eq_pow hf (A := B) (fun b hb => hA b (hBA.le hb))
  have hle : Nat.card B ≤ Nat.card A := Subgroup.card_le_of_le hBA.le
  have hne : Nat.card B ≠ Nat.card A := fun h =>
    hBA.ne (Subgroup.eq_of_le_of_card_ge hBA.le h.ge)
  have hlt : i < j := by
    rw [hi, hj] at hle hne
    exact (Nat.pow_lt_pow_iff_right hf.one_lt).mp (lt_of_le_of_ne hle hne)
  rw [hi, hj]
  calc f * f ^ i = f ^ (i + 1) := by ring
    _ ≤ f ^ j := Nat.pow_le_pow_right hf.pos hlt

theorem exists_elemAbelian_card (hf : f.Prime) {A : Subgroup X}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : ∀ a ∈ A, a ^ f = 1) {m : ℕ}
    (hm : f ^ m ≤ Nat.card A) :
    ∃ E : Subgroup X, E ≤ A ∧ CFSG.Open.IsElemAbelian f E ∧ Nat.card E = f ^ m := by
  obtain ⟨n, hn⟩ := exists_card_eq_pow hf he
  have hAel : CFSG.Open.IsElemAbelian f A :=
    ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, he⟩
  have hmn : m ≤ n := by
    rw [hn] at hm
    exact (Nat.pow_le_pow_iff_right hf.one_lt).mp hm
  exact CFSG.GH74.Uniqueness.SU.SU1.exists_subgroup_card hf hAel hmn hn

theorem isElemAbelian_zpowers {x : X} (hx : x ^ f = 1) :
    CFSG.Open.IsElemAbelian f (Subgroup.zpowers x) := by
  rw [Subgroup.zpowers_eq_closure]
  exact CFSG.Open.IsElemAbelian.closure_of_commute (by simp) (by simp [hx])

theorem commutator_le_center_of_forall {C : Subgroup X}
    (hcl : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ⁅a, b⁆ * c = c * ⁅a, b⁆) :
    commutator C ≤ center C := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro _ ⟨a, b, rfl⟩
  rw [SetLike.mem_coe, mem_center_iff]
  intro c
  exact Subtype.ext (hcl a a.2 b b.2 c c.2).symm

theorem exists_abelian_two (hf : f.Prime) {C : Subgroup X} (he : ∀ a ∈ C, a ^ f = 1)
    (hC : f ^ 2 ≤ Nat.card C) :
    ∃ A : Subgroup X, A ≤ C ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ f ^ 2 ≤ Nat.card A := by
  haveI := Fact.mk hf
  have hCp : IsPGroup f C := isPGroup_of_exp hf he
  have h1 : 1 < Nat.card C := lt_of_lt_of_le (Nat.one_lt_pow (by norm_num) hf.one_lt) hC
  haveI : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp h1
  haveI := hCp.center_nontrivial
  obtain ⟨⟨u, hu⟩, hu1⟩ := exists_ne (1 : center C)
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huf : (u : X) ^ f = 1 := he u u.2
  have hu1X : (u : X) ≠ 1 := fun h => hu1' (Subtype.ext h)
  have hord : orderOf (u : X) = f := orderOf_eq_prime huf hu1X
  have hzcard : Nat.card (Subgroup.zpowers (u : X)) = f := by rw [Nat.card_zpowers, hord]
  obtain ⟨w, hwC, hw⟩ : ∃ w ∈ C, w ∉ Subgroup.zpowers (u : X) := by
    by_contra hall
    push Not at hall
    have hle : C ≤ Subgroup.zpowers (u : X) := hall
    have := Subgroup.card_le_of_le hle
    rw [hzcard] at this
    have h2 : f < f ^ 2 := by nlinarith [hf.two_le]
    omega
  have hcomm : (u : X) * w = w * (u : X) := by
    have := mem_center_iff.mp hu ⟨w, hwC⟩
    exact (congrArg Subtype.val this).symm
  have hclos : CFSG.Open.IsElemAbelian f (Subgroup.closure {(u : X), w}) := by
    apply CFSG.Open.IsElemAbelian.closure_of_commute
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;>
        first | rfl | exact hcomm | exact hcomm.symm
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with h | h
      · rw [h]
        exact huf
      · rw [h]
        exact he w hwC
  refine ⟨Subgroup.closure {(u : X), w}, ?_, fun a ha b hb => hclos.comm ha hb, ?_⟩
  · rw [Subgroup.closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with h | h
    · rw [h]
      exact u.2
    · rw [h]
      exact hwC
  · have hlt : Subgroup.zpowers (u : X) < Subgroup.closure {(u : X), w} := by
      refine lt_of_le_of_ne ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp)
      · intro h
        apply hw
        rw [h]
        exact Subgroup.subset_closure (by simp)
    have := mul_card_le_of_lt hf (fun a ha => hclos.2 a ha) hlt
    rw [hzcard] at this
    calc f ^ 2 = f * f := by ring
      _ ≤ _ := this

theorem exists_abelian_three (hf : f.Prime) {C : Subgroup X} (he : ∀ a ∈ C, a ^ f = 1)
    (hcl : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ⁅a, b⁆ * c = c * ⁅a, b⁆) (hC : f ^ 4 ≤ Nat.card C) :
    ∃ A : Subgroup X, A ≤ C ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ f ^ 3 ≤ Nat.card A := by
  haveI := Fact.mk hf
  classical
  have hCp : IsPGroup f C := isPGroup_of_exp hf he
  have hf1 := hf.one_lt
  set Z : Subgroup X := (center C).map C.subtype with hZ
  have hZC : Z ≤ C := Subgroup.map_subtype_le _
  have hZmem : ∀ z ∈ Z, ∀ c ∈ C, c * z = z * c := by
    rintro _ ⟨z, hz, rfl⟩ c hc
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨c, hc⟩)
  have hZexp : ∀ z ∈ Z, z ^ f = 1 := fun z hz => he z (hZC hz)
  have hZcard : Nat.card Z = Nat.card (center C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  by_cases habel : ∀ x ∈ C, x ∈ Z
  · refine ⟨C, le_rfl, fun a ha b hb => hZmem b (habel b hb) a ha, ?_⟩
    calc f ^ 3 ≤ f ^ 4 := Nat.pow_le_pow_right hf.pos (by norm_num)
      _ ≤ _ := hC
  · push Not at habel
    obtain ⟨x, hxC, hxZ⟩ := habel
    have hx1 : x ^ f = 1 := he x hxC
    have hZel : CFSG.Open.IsElemAbelian f Z :=
      ⟨⟨⟨fun a b => Subtype.ext (hZmem b b.2 a (hZC a.2))⟩⟩, hZexp⟩
    have hxel := isElemAbelian_zpowers hx1
    have hxle : Subgroup.zpowers x ≤ C := Subgroup.zpowers_le.mpr hxC
    have hcommZx : ∀ a ∈ Z, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := fun a ha b hb =>
      (hZmem a ha b (hxle hb)).symm
    set A₀ : Subgroup X := Z ⊔ Subgroup.zpowers x with hA₀
    have hA₀el : CFSG.Open.IsElemAbelian f A₀ :=
      CFSG.Open.IsElemAbelian.sup_of_commute hZel hxel hcommZx
    have hA₀C : A₀ ≤ C := sup_le hZC hxle
    have hxA₀ : x ∈ A₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hZA₀ : Z < A₀ :=
      lt_of_le_of_ne le_sup_left (fun h => hxZ (by rw [h]; exact hxA₀))
    have hA₀card : f * Nat.card Z ≤ Nat.card A₀ :=
      mul_card_le_of_lt hf (fun a ha => hA₀el.2 a ha) hZA₀
    by_cases hbig : f ^ 2 ≤ Nat.card Z
    · refine ⟨A₀, hA₀C, fun a ha b hb => hA₀el.comm ha hb, ?_⟩
      calc f ^ 3 = f * f ^ 2 := by ring
        _ ≤ f * Nat.card Z := Nat.mul_le_mul_left _ hbig
        _ ≤ _ := hA₀card
    · push Not at hbig
      have h1C : 1 < Nat.card C := lt_of_lt_of_le (Nat.one_lt_pow (by norm_num) hf1) hC
      haveI : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp h1C
      haveI := hCp.center_nontrivial
      have hZgt1 : 1 < Nat.card Z := by
        rw [hZcard]
        exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      obtain ⟨i, hi⟩ := exists_card_eq_pow hf hZexp
      have hZf : Nat.card Z = f := by
        have hi1 : 1 < f ^ i := hi ▸ hZgt1
        have hi2 : f ^ i < f ^ 2 := hi ▸ hbig
        have hi0 : 0 < i := by
          rcases Nat.eq_zero_or_pos i with h | h
          · rw [h, pow_zero] at hi1
            exact absurd hi1 (lt_irrefl _)
          · exact h
        have hi3 : i < 2 := (Nat.pow_lt_pow_iff_right hf1).mp hi2
        have : i = 1 := by omega
        rw [hi, this, pow_one]
      have hcl' : commutator C ≤ center C := commutator_le_center_of_forall hcl
      have hcomm_card : Nat.card (commutator C) ≤ f := by
        calc Nat.card (commutator C) ≤ Nat.card (center C) := Subgroup.card_le_of_le hcl'
          _ = Nat.card Z := hZcard.symm
          _ = f := hZf
      have hB := card_le_centralizer_mul_commutator hcl' (⟨x, hxC⟩ : C)
      set BG : Subgroup C := Subgroup.centralizer ({(⟨x, hxC⟩ : C)} : Set C) with hBG
      have hBGcard : f ^ 3 ≤ Nat.card BG := by
        apply Nat.le_of_mul_le_mul_right _ hf.pos
        calc f ^ 3 * f = f ^ 4 := by ring
          _ ≤ Nat.card C := hC
          _ ≤ Nat.card BG * Nat.card (commutator C) := hB
          _ ≤ Nat.card BG * f := Nat.mul_le_mul_left _ hcomm_card
      set B : Subgroup X := BG.map C.subtype with hB'
      have hBcard : Nat.card B = Nat.card BG := Subgroup.card_map_of_injective C.subtype_injective
      have hBC : B ≤ C := Subgroup.map_subtype_le _
      have hBx : ∀ b ∈ B, b * x = x * b := by
        rintro _ ⟨b, hb, rfl⟩
        have := Subgroup.mem_centralizer_singleton_iff.mp hb
        exact congrArg Subtype.val this
      by_cases h3 : f ^ 3 ≤ Nat.card A₀
      · exact ⟨A₀, hA₀C, fun a ha b hb => hA₀el.comm ha hb, h3⟩
      · push Not at h3
        obtain ⟨b, hbB, hbA⟩ : ∃ b ∈ B, b ∉ A₀ := by
          by_contra hall
          push Not at hall
          have hle : B ≤ A₀ := hall
          have := Subgroup.card_le_of_le hle
          omega
        have hb1 : b ^ f = 1 := he b (hBC hbB)
        have hA₀cb : A₀ ≤ Subgroup.centralizer ({b} : Set X) := by
          apply sup_le
          · intro z hz
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact (hZmem z hz b (hBC hbB)).symm
          · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
            exact (hBx b hbB).symm
        have hcomm_b : ∀ a ∈ A₀, ∀ c ∈ Subgroup.zpowers b, a * c = c * a := by
          intro a ha c hc
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
          have hab : Commute a b := Subgroup.mem_centralizer_singleton_iff.mp (hA₀cb ha)
          exact (hab.zpow_right k).eq
        have hA₁el := CFSG.Open.IsElemAbelian.sup_of_commute hA₀el
          (isElemAbelian_zpowers hb1) hcomm_b
        have hA₁C : A₀ ⊔ Subgroup.zpowers b ≤ C := sup_le hA₀C (Subgroup.zpowers_le.mpr (hBC hbB))
        have hA₀A₁ : A₀ < A₀ ⊔ Subgroup.zpowers b :=
          lt_of_le_of_ne le_sup_left
            (fun h => hbA (by rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)))
        have hmul := mul_card_le_of_lt hf (fun a ha => hA₁el.2 a ha) hA₀A₁
        refine ⟨A₀ ⊔ Subgroup.zpowers b, hA₁C, fun a ha c hc => hA₁el.comm ha hc, ?_⟩
        calc f ^ 3 = f * (f * f) := by ring
          _ ≤ f * Nat.card A₀ := Nat.mul_le_mul_left _ (by rw [← hZf] at hA₀card ⊢; exact hA₀card)
          _ ≤ _ := hmul

end Helpers

section Step0

variable {X : Type*} [Group X] [Finite X] {f : ℕ}

theorem step0 (hf : f.Prime) (hf3 : 3 ≤ f) {D : Subgroup X} (hexp : ∀ d ∈ D, d ^ f = 1)
    (hcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hdim : f ^ (f + 1) * Nat.card (commutator D) ≤ Nat.card D) {y : X} (hy : orderOf y = f)
    (hyD : y ∈ Subgroup.normalizer (D : Set X)) :
    3 ≤ CFSG.Open.pRank f (Subgroup.centralizer ({y} : Set X)) := by
  haveI := Fact.mk hf
  have hf1 := hf.one_lt
  have hyf : y ^ f = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hcl' : commutator D ≤ center D := commutator_le_center_of_forall hcl
  have hf4 : f ^ 4 ≤ f ^ (f + 1) := Nat.pow_le_pow_right hf.pos (by omega)
  by_cases hyDmem : y ∈ D
  ·
    set g₀ : D := ⟨y, hyDmem⟩ with hg₀
    have hB := card_le_centralizer_mul_commutator hcl' g₀
    set C : Subgroup X := (Subgroup.centralizer ({g₀} : Set D)).map D.subtype with hC
    have hCcard : Nat.card C = Nat.card (Subgroup.centralizer ({g₀} : Set D)) :=
      Subgroup.card_map_of_injective D.subtype_injective
    have hCD : C ≤ D := Subgroup.map_subtype_le _
    have hCy : C ≤ Subgroup.centralizer ({y} : Set X) := by
      rintro _ ⟨c, hc, rfl⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val this
    have hkpos : 0 < Nat.card (commutator D) := Nat.card_pos
    have hCbig : f ^ 4 ≤ Nat.card C := by
      rw [hCcard]
      apply Nat.le_of_mul_le_mul_right _ hkpos
      calc f ^ 4 * Nat.card (commutator D) ≤ f ^ (f + 1) * Nat.card (commutator D) :=
            Nat.mul_le_mul_right _ hf4
        _ ≤ Nat.card D := hdim
        _ ≤ _ := hB
    obtain ⟨A, hAC, hAc, hAbig⟩ := exists_abelian_three hf (fun a ha => hexp a (hCD ha))
      (fun a ha b hb c hc => hcl a (hCD ha) b (hCD hb) c (hCD hc)) hCbig
    obtain ⟨E, hEA, hEel, hEcard⟩ := exists_elemAbelian_card hf hAc
      (fun a ha => hexp a (hCD (hAC ha))) hAbig
    exact CFSG.GH74.Uniqueness.SU.SU1.le_pRank hf1 (hEA.trans (hAC.trans hCy)) hEel hEcard
  ·
    let g : MulAut D := D.normalizerMonoidHom ⟨y, hyD⟩
    have hg_apply : ∀ d : D, ((g d : D) : X) = y * d * y⁻¹ := fun d => rfl
    have hg_iter : ∀ (k : ℕ) (d : D), (((⇑g)^[k] d : D) : X) = y ^ k * d * (y ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => intro d; simp
      | succ k ih =>
        intro d
        rw [Function.iterate_succ_apply, ih, hg_apply, pow_succ, mul_inv_rev]
        group
    have hgf : ∀ d : D, (⇑g)^[f] d = d := fun d => by
      apply Subtype.ext
      rw [hg_iter, hyf]
      simp
    have hz : (Abelianization.of : D →* Abelianization D).ker ≤ center D := by
      rw [Abelianization.ker_of]
      exact hcl'
    have hexpV : ∀ v : Abelianization D, v ^ f = 1 := by
      intro v
      obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective v
      show Abelianization.of d ^ f = 1
      rw [← map_pow]
      have : d ^ f = 1 := Subtype.ext (by simpa using hexp d d.2)
      rw [this, map_one]
    let u : Abelianization D →* Abelianization D := Abelianization.map g.toMonoidHom
    have hu : ∀ d : D, (Abelianization.of : D →* Abelianization D) (g d) =
        u (Abelianization.of d) := fun d => (Abelianization.map_of g.toMonoidHom d).symm
    have hu_iter : ∀ (k : ℕ) (d : D), (⇑u)^[k] (Abelianization.of d) =
        Abelianization.of ((⇑g)^[k] d) := by
      intro k
      induction k with
      | zero => intro d; rfl
      | succ k ih =>
        intro d
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hu, ih]
    have huf : ∀ v : Abelianization D, (⇑u)^[f] v = v := by
      intro v
      obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective v
      show (⇑u)^[f] (Abelianization.of d) = Abelianization.of d
      rw [hu_iter, hgf]
    have hdim' : f ^ (f + 1) * Nat.card (Abelianization.of : D →* Abelianization D).ker ≤
        Nat.card D := by
      rw [Abelianization.ker_of]
      exact hdim
    have hfix := two_le_card_fixSub (f := f) (Abelianization.of : D →* Abelianization D)
      QuotientGroup.mk_surjective hz hexpV g u hu huf hdim'
    set C : Subgroup X := (fixSub g).map D.subtype with hC
    have hCcard : Nat.card C = Nat.card (fixSub g) :=
      Subgroup.card_map_of_injective D.subtype_injective
    have hCD : C ≤ D := Subgroup.map_subtype_le _
    have hCy : C ≤ Subgroup.centralizer ({y} : Set X) := by
      rintro _ ⟨c, hc, rfl⟩
      have h1 := mem_fixSub.mp hc
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      show (c : X) * y = y * c
      rw [hg_apply] at h2
      calc (c : X) * y = (y * (c : X) * y⁻¹) * y := by rw [h2]
        _ = y * c := by group
    obtain ⟨A, hAC, hAc, hAbig⟩ := exists_abelian_two hf (fun a ha => hexp a (hCD ha))
      (hCcard ▸ hfix)
    obtain ⟨E₂, hE₂A, hE₂el, hE₂card⟩ := exists_elemAbelian_card hf hAc
      (fun a ha => hexp a (hCD (hAC ha))) (le_refl _ |>.trans' hAbig)
    have hyel := isElemAbelian_zpowers (x := y) hyf
    have hcommy : ∀ a ∈ E₂, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hab : Commute a y :=
        Subgroup.mem_centralizer_singleton_iff.mp (hCy (hAC (hE₂A ha)))
      exact (hab.zpow_right k).eq
    have hEel := CFSG.Open.IsElemAbelian.sup_of_commute hE₂el hyel hcommy
    have hlt : E₂ < E₂ ⊔ Subgroup.zpowers y := by
      refine lt_of_le_of_ne le_sup_left fun h => ?_
      have hymem : y ∈ E₂ := by
        rw [h]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      exact hyDmem (hCD (hAC (hE₂A hymem)))
    have hmul := mul_card_le_of_lt hf (fun a ha => hEel.2 a ha) hlt
    rw [hE₂card] at hmul
    obtain ⟨E, hEle, hEel', hEcard⟩ := exists_elemAbelian_card hf
      (fun a ha b hb => hEel.comm ha hb) (fun a ha => hEel.2 a ha) (m := 3)
      (by calc f ^ 3 = f * f ^ 2 := by ring
            _ ≤ _ := hmul)
    have hEcy : E₂ ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({y} : Set X) := by
      apply sup_le
      · exact hE₂A.trans (hAC.trans hCy)
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.GH74.Uniqueness.SU.SU1.le_pRank hf1 (hEle.trans hEcy) hEel' hEcard

end Step0

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
