module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Defs
public import CFSG.GH74.QTGen4.Recog.G23.HSL

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.Cor37

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.P7

section PartA

theorem inverts_of_fixed_free {X : Type*} [Group X] [Finite X] (α : X ≃* X)
    (hα : ∀ x, α (α x) = x) (hfix : ∀ x, α x = x → x = 1) (x : X) :
    α x = x⁻¹ := by
  have hinj : Function.Injective (fun y : X => y⁻¹ * α y) := by
    intro a b hab
    have hab' : a⁻¹ * α a = b⁻¹ * α b := hab
    have h1 : α a = a * b⁻¹ * α b := by
      calc α a = a * (a⁻¹ * α a) := by group
        _ = a * (b⁻¹ * α b) := by rw [hab']
        _ = a * b⁻¹ * α b := by group
    have h2 : α (a * b⁻¹) = a * b⁻¹ := by
      rw [map_mul, map_inv, h1]
      group
    have h3 := hfix _ h2
    exact (mul_inv_eq_one.mp h3)
  have hsurj : Function.Surjective (fun y : X => y⁻¹ * α y) :=
    Finite.injective_iff_surjective.mp hinj
  obtain ⟨w, hw⟩ := hsurj x
  have hw' : w⁻¹ * α w = x := hw
  rw [← hw']
  rw [map_mul, map_inv, hα]
  group

theorem commute_of_inverts {X : Type*} [Group X] (α : X ≃* X)
    (h : ∀ x, α x = x⁻¹) (a b : X) : a * b = b * a := by
  have h1 := h (a * b)
  rw [map_mul, h a, h b, mul_inv_rev] at h1
  have h2 := congrArg (fun y => y⁻¹) h1
  simp only [inv_inv, mul_inv_rev] at h2
  exact h2.symm

theorem exists_fixed_in_coset {G : Type*} [Group G] [Finite G] (τ x : G) (hττ : τ * τ = 1)
    (P : Subgroup G) (hPodd : Odd (Nat.card P)) (hτP : ∀ p ∈ P, τ * p * τ⁻¹ ∈ P)
    (hx : ∃ p ∈ P, τ * x * τ⁻¹ = x * p) :
    ∃ p ∈ P, τ * (x * p) * τ⁻¹ = x * p := by
  classical
  obtain ⟨p₀, hp₀, hxp₀⟩ := hx
  have hτinv : τ⁻¹ = τ := (eq_inv_of_mul_eq_one_left hττ).symm
  let C : Type _ := {y : G // ∃ p ∈ P, y = x * p}
  haveI : Fintype C := Fintype.ofFinite C
  have hmem : ∀ c : C, τ * c.1 * τ⁻¹ ∈ {y : G | ∃ p ∈ P, y = x * p} := by
    rintro ⟨c, p, hp, rfl⟩
    refine ⟨p₀ * (τ * p * τ⁻¹), P.mul_mem hp₀ (hτP p hp), ?_⟩
    calc τ * (x * p) * τ⁻¹ = (τ * x * τ⁻¹) * (τ * p * τ⁻¹) := by group
      _ = x * p₀ * (τ * p * τ⁻¹) := by rw [hxp₀]
      _ = x * (p₀ * (τ * p * τ⁻¹)) := by group
  let F : C → C := fun c => ⟨τ * c.1 * τ⁻¹, hmem c⟩
  have hFF : ∀ c, F (F c) = c := by
    rintro ⟨c, hc⟩
    apply Subtype.ext
    simp only [F]
    rw [hτinv]
    calc τ * (τ * c * τ) * τ = (τ * τ) * c * (τ * τ) := by group
      _ = c := by rw [hττ]; group
  let f : Function.End C := F
  have hf : f ^ 2 ^ 1 = 1 := by
    funext c
    show (F^[2]) c = c
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    exact hFF c
  have hcard : Fintype.card C = Nat.card P := by
    rw [← Nat.card_eq_fintype_card]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun p : P => (⟨x * p.1, p.1, p.2, rfl⟩ : C)) ⟨?_, ?_⟩)).symm
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (mul_left_cancel this)
    · rintro ⟨c, p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf
  rw [hcard] at hmod
  have hodd : Nat.card P % 2 = 1 := Nat.odd_iff.mp hPodd
  obtain ⟨c, hcF⟩ : ∃ c : C, F c = c := by
    by_contra hno
    push_neg at hno
    have h0 : Fintype.card (Function.fixedPoints f) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨c, hc⟩ => hno c hc⟩
    rw [h0] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨p, hp, hcp⟩ := c.2
  refine ⟨p, hp, ?_⟩
  have h : τ * c.1 * τ⁻¹ = c.1 := congrArg Subtype.val hcF
  rw [← hcp]
  exact h

theorem card_sup_zpowers_of_commute {G : Type*} [Group G] [Finite G] (σ : G)
    (hσ : orderOf σ = 3) (A : Subgroup G) (hA : ∀ a ∈ A, a * σ = σ * a)
    (hdisj : A ⊓ Subgroup.zpowers σ = ⊥) :
    Nat.card ↥(A ⊔ Subgroup.zpowers σ) = 3 * Nat.card A := by
  classical
  have hcomm : ∀ a ∈ A, ∀ s ∈ Subgroup.zpowers σ, a * s = s * a := by
    intro a ha s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hc : Commute a σ := hA a ha
    exact ((hc.zpow_right k)).eq
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ s ∈ Subgroup.zpowers σ, a * s = x}
      one_mem' := ⟨1, A.one_mem, 1, Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, s, hs, rfl⟩ ⟨a', ha', s', hs', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', s * s', Subgroup.mul_mem _ hs hs', ?_⟩
        calc a * a' * (s * s') = a * (a' * s) * s' := by group
          _ = a * (s * a') * s' := by rw [hcomm a' ha' s hs]
          _ = a * s * (a' * s') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, s, hs, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, s⁻¹, Subgroup.inv_mem _ hs, ?_⟩
        have hc : a * s = s * a := hcomm a ha s hs
        have hc' : s⁻¹ * a⁻¹ = a⁻¹ * s⁻¹ := by
          have := congrArg (fun y => y⁻¹) hc
          simp only [mul_inv_rev] at this
          exact this
        rw [mul_inv_rev]
        exact hc'.symm }
  have hA_le : A ≤ A ⊔ Subgroup.zpowers σ := le_sup_left
  have hs_le : Subgroup.zpowers σ ≤ A ⊔ Subgroup.zpowers σ := le_sup_right
  have hQS : A ⊔ Subgroup.zpowers σ ≤ S := by
    refine sup_le ?_ ?_
    · intro a ha
      exact ⟨a, ha, 1, Subgroup.one_mem _, by simp⟩
    · intro s hs
      exact ⟨1, A.one_mem, s, hs, by simp⟩
  let f : A × Subgroup.zpowers σ → ↥(A ⊔ Subgroup.zpowers σ) :=
    fun p => ⟨p.1.1 * p.2.1, Subgroup.mul_mem _ (hA_le p.1.2) (hs_le p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, s⟩ ⟨a', s'⟩ h
      have h' : a.1 * s.1 = a'.1 * s'.1 := congrArg Subtype.val h
      have key : a'.1⁻¹ * a.1 = s'.1 * s.1⁻¹ := by
        calc a'.1⁻¹ * a.1 = a'.1⁻¹ * (a.1 * s.1) * s.1⁻¹ := by group
          _ = a'.1⁻¹ * (a'.1 * s'.1) * s.1⁻¹ := by rw [h']
          _ = s'.1 * s.1⁻¹ := by group
      have hmem : a'.1⁻¹ * a.1 ∈ A ⊓ Subgroup.zpowers σ := by
        refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
        rw [key]
        exact Subgroup.mul_mem _ s'.2 (Subgroup.inv_mem _ s.2)
      rw [hdisj, Subgroup.mem_bot] at hmem
      have hA' : a'.1 = a.1 := inv_mul_eq_one.mp hmem
      have hs2 : s'.1 * s.1⁻¹ = 1 := by rw [← key]; exact hmem
      have hs' : s'.1 = s.1 := mul_inv_eq_one.mp hs2
      exact Prod.ext (Subtype.ext hA'.symm) (Subtype.ext hs'.symm)
    · rintro ⟨q, hq⟩
      have hqS : q ∈ S := hQS hq
      obtain ⟨a, ha, s, hs, has⟩ := hqS
      exact ⟨(⟨a, ha⟩, ⟨s, hs⟩), Subtype.ext has⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_zpowers, hσ, mul_comm]

theorem jordan_card_le {W : Type*} [AddCommGroup W] [Finite W] (σ : W ≃+ W)
    (h3 : ∀ w : W, (3 : ℕ) • w = 0) (hσ : ∀ w, σ (σ (σ w)) = w) :
    Nat.card W ≤ (Nat.card {w : W // σ w = w}) ^ 3 := by
  let δ : W →+ W := σ.toAddMonoidHom - AddMonoidHom.id W
  have hδ : ∀ w, δ w = σ w - w := fun w => rfl
  have hK : ∀ w, w ∈ δ.ker ↔ σ w = w := by
    intro w
    rw [AddMonoidHom.mem_ker, hδ, sub_eq_zero]
  have hcube : ∀ w, δ (δ (δ w)) = 0 := by
    intro w
    have e : δ (δ (δ w)) = (3 : ℕ) • σ w - (3 : ℕ) • σ (σ w) := by
      simp only [hδ, map_sub, AddEquiv.coe_toAddMonoidHom, map_sub, hσ]
      abel_nf
    rw [e, h3 (σ w), h3 (σ (σ w)), sub_zero]
  let I := δ.range
  let δ' : I →+ W := δ.comp I.subtype
  have h1 : Nat.card W = Nat.card δ.ker * Nat.card I :=
    (AddSubgroup.card_ker_mul_card_range δ).symm
  have h2 : Nat.card I = Nat.card δ'.ker * Nat.card δ'.range :=
    (AddSubgroup.card_ker_mul_card_range δ').symm
  have hr : δ'.range ≤ δ.ker := by
    rintro x ⟨i, rfl⟩
    obtain ⟨w, hw⟩ := i.2
    show δ (i : W) ∈ δ.ker
    rw [← hw]
    exact AddMonoidHom.mem_ker.mpr (hcube w)
  have hk : Nat.card δ'.ker ≤ Nat.card δ.ker := by
    refine Nat.card_le_card_of_injective
      (fun x : δ'.ker => (⟨x.1.1, AddMonoidHom.mem_ker.mpr (AddMonoidHom.mem_ker.mp x.2)⟩ :
        δ.ker)) ?_
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hr' : Nat.card δ'.range ≤ Nat.card δ.ker :=
    AddSubgroup.card_le_of_le hr
  have hmain : Nat.card W ≤ Nat.card δ.ker ^ 3 := by
    rw [h1, h2]
    calc Nat.card δ.ker * (Nat.card δ'.ker * Nat.card δ'.range)
        ≤ Nat.card δ.ker * (Nat.card δ.ker * Nat.card δ.ker) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hk hr')
      _ = Nat.card δ.ker ^ 3 := by ring
  have hKe : Nat.card δ.ker = Nat.card {w : W // σ w = w} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun w => hK w))
  rw [hKe] at hmain
  exact hmain

@[expose] def stabSub {L V : Type*} [Group L] [Group V] (ρ : L →* MulAut V) (v : V) : Subgroup L where
  carrier := {g : L | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, MulAut.mul_apply, hb, ha]
  one_mem' := by simp [Set.mem_setOf_eq]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = ρ (a⁻¹ * a) v := by rw [map_mul, MulAut.mul_apply]
      _ = v := by simp

theorem stab_card_dvd_three {L V : Type*} [Group L] [Finite L] [Group V]
    (ρ : L →* MulAut V) (z : L) (hzfix : ∀ v : V, ρ z v = v → v = 1)
    (hinv : ∀ u : L, u * u = 1 → u ≠ 1 → u = z) (hL : Nat.card L = 24) (v : V) (hv : v ≠ 1) :
    Nat.card ↥(stabSub ρ v) ∣ 3 := by
  have hdvd : Nat.card ↥(stabSub ρ v) ∣ 24 := hL ▸ Subgroup.card_subgroup_dvd_card _
  have hodd : ¬ 2 ∣ Nat.card ↥(stabSub ρ v) := by
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hu2 : (u : L) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one u
      rw [hu] at h
      have := congrArg Subtype.val h
      simpa using this
    have hu1 : (u : L) ≠ 1 := by
      intro h1
      have hu1' : u = 1 := Subtype.ext h1
      rw [hu1', orderOf_one] at hu
      norm_num at hu
    have hsq : (u : L) * (u : L) = 1 := by rw [← sq]; exact hu2
    have hzu : (u : L) = z := hinv _ hsq hu1
    have hzv : ρ z v = v := by
      have hmem := u.2
      rw [← hzu]
      exact hmem
    exact hv (hzfix v hzv)
  have hc : Nat.Coprime (Nat.card ↥(stabSub ρ v)) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
  have hc3 : Nat.Coprime (Nat.card ↥(stabSub ρ v)) (2 ^ 3) := Nat.Coprime.pow_right 3 hc
  have h24 : Nat.card ↥(stabSub ρ v) ∣ 2 ^ 3 * 3 := by
    norm_num
    exact hdvd
  exact hc3.dvd_of_dvd_mul_left h24

theorem act_mul_apply {L V : Type*} [Group L] [Group V] (ρ : L →* MulAut V) (a b : L) (w : V) :
    ρ (a * b) w = ρ a (ρ b w) := by
  rw [map_mul, MulAut.mul_apply]

theorem act_inv_cancel {L V : Type*} [Group L] [Group V] (ρ : L →* MulAut V) (g : L) (w : V) :
    ρ g⁻¹ (ρ g w) = w := by
  rw [← act_mul_apply, inv_mul_cancel, map_one]
  rfl

theorem act_cancel' {L V : Type*} [Group L] [Group V] (ρ : L →* MulAut V) (g : L) (w : V) :
    ρ g (ρ g⁻¹ w) = w := by
  rw [← act_mul_apply, mul_inv_cancel, map_one]
  rfl

theorem fix_iff_inv {L V : Type*} [Group L] [Group V] (ρ : L →* MulAut V) (σ : L) (v : V) :
    ρ σ⁻¹ v = v ↔ ρ σ v = v := by
  constructor
  · intro h
    calc ρ σ v = ρ σ (ρ σ⁻¹ v) := by rw [h]
      _ = v := act_cancel' ρ σ v
  · intro h
    calc ρ σ⁻¹ v = ρ σ⁻¹ (ρ σ v) := by rw [h]
      _ = v := act_inv_cancel ρ σ v

theorem fix_card_conj {L V : Type*} [Group L] [Group V] [Fintype V] [DecidableEq V]
    (ρ : L →* MulAut V) (g σ : L) :
    (Finset.univ.filter (fun v : V => ρ (g * σ * g⁻¹) v = v)).card =
      (Finset.univ.filter (fun v : V => ρ σ v = v)).card := by
  have hexp : ∀ w, ρ (g * σ * g⁻¹) w = ρ g (ρ σ (ρ g⁻¹ w)) := by
    intro w
    rw [act_mul_apply, act_mul_apply]
  apply Finset.card_nbij' (fun v => ρ g⁻¹ v) (fun v => ρ g v)
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq,
      Finset.mem_univ, true_and] at hv ⊢
    rw [hexp] at hv
    calc ρ σ (ρ g⁻¹ v) = ρ g⁻¹ (ρ g (ρ σ (ρ g⁻¹ v))) := (act_inv_cancel ρ g _).symm
      _ = ρ g⁻¹ v := by rw [hv]
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq,
      Finset.mem_univ, true_and] at hv ⊢
    rw [hexp, act_inv_cancel, hv]
  · intro v _
    exact act_cancel' ρ g v
  · intro v _
    exact act_inv_cancel ρ g v

theorem orbit_bound {L V : Type*} [Group L] [Fintype L] [DecidableEq L] [Group V] [Fintype V]
    [DecidableEq V] (ρ : L →* MulAut V) (z : L) (hzfix : ∀ v : V, ρ z v = v → v = 1)
    (hinv : ∀ u : L, u * u = 1 → u ≠ 1 → u = z) (hL : Nat.card L = 24)
    (hT8 : (Finset.univ.filter (fun x : L => x ^ 3 = 1 ∧ x ≠ 1)).card = 8) (σ : L)
    (hconj : ∀ x : L, x ^ 3 = 1 → x ≠ 1 → ∃ g : L, x = g * σ * g⁻¹ ∨ x = g * σ⁻¹ * g⁻¹) :
    4 * ((Finset.univ.filter (fun v : V => ρ σ v = v)).card - 1) ≤ Fintype.card V - 1 := by
  classical
  set T := Finset.univ.filter (fun x : L => x ^ 3 = 1 ∧ x ≠ 1) with hTdef
  set m := (Finset.univ.filter (fun v : V => ρ σ v = v)).card with hm
  have hinvfix : (Finset.univ.filter (fun v : V => ρ σ⁻¹ v = v)).card = m := by
    rw [Finset.filter_congr (fun v _ => fix_iff_inv ρ σ v)]
  have hfix : ∀ x ∈ T, (Finset.univ.filter (fun v : V => ρ x v = v)).card = m := by
    intro x hx
    rw [hTdef, Finset.mem_filter] at hx
    obtain ⟨g, hg | hg⟩ := hconj x hx.2.1 hx.2.2
    · rw [hg, fix_card_conj]
    · rw [hg, fix_card_conj, hinvfix]
  have hstab : ∀ v : V, v ≠ 1 → (T.filter (fun x => ρ x v = v)).card ≤ 2 := by
    intro v hv
    have hsub : insert 1 (T.filter (fun x => ρ x v = v)) ⊆
        Finset.univ.filter (fun g : L => ρ g v = v) := by
      intro g hg
      rw [Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · simp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (Finset.mem_filter.mp hg).2
    have h1 : (1 : L) ∉ T.filter (fun x => ρ x v = v) := by
      intro h
      have h' := (Finset.mem_filter.mp h).1
      rw [hTdef, Finset.mem_filter] at h'
      exact h'.2.2 rfl
    have h2 := Finset.card_insert_of_notMem (s := T.filter (fun x => ρ x v = v)) h1
    have h3 : Nat.card ↥(stabSub ρ v) = (Finset.univ.filter (fun g : L => ρ g v = v)).card := by
      calc Nat.card ↥(stabSub ρ v) = Nat.card {g : L // ρ g v = v} :=
            Nat.card_congr (Equiv.subtypeEquivRight (fun g => Iff.rfl))
        _ = Fintype.card {g : L // ρ g v = v} := Nat.card_eq_fintype_card
        _ = (Finset.univ.filter (fun g : L => ρ g v = v)).card := Fintype.card_subtype _
    have h4 := stab_card_dvd_three ρ z hzfix hinv hL v hv
    have h5 : Nat.card ↥(stabSub ρ v) ≤ 3 := Nat.le_of_dvd (by norm_num) h4
    have h6 := Finset.card_le_card hsub
    omega
  have hsum : ∑ x ∈ T, (((Finset.univ : Finset V).erase 1).filter (fun v => ρ x v = v)).card =
      ∑ v ∈ (Finset.univ : Finset V).erase 1, (T.filter (fun x => ρ x v = v)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hval : ∀ x ∈ T, (((Finset.univ : Finset V).erase 1).filter (fun v => ρ x v = v)).card = m - 1 := by
    intro x hx
    have heq : ((Finset.univ : Finset V).erase 1).filter (fun v => ρ x v = v) =
        (Finset.univ.filter (fun v => ρ x v = v)).erase 1 := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
      tauto
    rw [heq, Finset.card_erase_of_mem (by simp), hfix x hx]
  have hL' : ∑ x ∈ T, (((Finset.univ : Finset V).erase 1).filter (fun v => ρ x v = v)).card = 8 * (m - 1) := by
    rw [Finset.sum_congr rfl hval, Finset.sum_const, hT8, smul_eq_mul]
  have hR : ∑ v ∈ (Finset.univ : Finset V).erase 1, (T.filter (fun x => ρ x v = v)).card ≤
      ∑ v ∈ (Finset.univ : Finset V).erase 1, 2 :=
    Finset.sum_le_sum (fun v hv => hstab v (Finset.ne_of_mem_erase hv))
  have hR' : ∑ v ∈ (Finset.univ : Finset V).erase 1, (2 : ℕ) = 2 * (Fintype.card V - 1) := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      smul_eq_mul]
    ring
  have key : 8 * (m - 1) ≤ 2 * (Fintype.card V - 1) := by
    rw [← hL', hsum]
    rw [← hR']
    exact hR
  omega

section Quot

variable {G : Type*} [Group G]

@[expose] def conjM (M : Subgroup G) (g : G) (hg : ∀ m ∈ M, g * m * g⁻¹ ∈ M) : ↥M →* ↥M where
  toFun m := ⟨g * m * g⁻¹, hg m m.2⟩
  map_one' := by
    ext
    simp
  map_mul' m n := by
    ext
    simp only [Subgroup.coe_mul, MulMemClass.coe_mul]
    group

theorem conjM_coe (M : Subgroup G) (g : G) (hg : ∀ m ∈ M, g * m * g⁻¹ ∈ M) (m : ↥M) :
    ((conjM M g hg m : ↥M) : G) = g * m * g⁻¹ := rfl

theorem normal_subgroupOf_of_central (M P : Subgroup G)
    (hc : ∀ m ∈ M, ∀ p ∈ P, m * p = p * m) : (P.subgroupOf M).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hcomm : (g : G) * (n : G) = (n : G) * (g : G) := hc g g.2 n hn
  have : ((g * n * g⁻¹ : ↥M) : G) = (n : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcomm]
    group
  rw [this]
  exact hn

variable (M P : Subgroup G) [hN : (P.subgroupOf M).Normal]

@[expose] def actQ (g : G) (hg : ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hgP : ∀ p ∈ P, g * p * g⁻¹ ∈ P) :
    (↥M ⧸ P.subgroupOf M) →* (↥M ⧸ P.subgroupOf M) :=
  QuotientGroup.map (P.subgroupOf M) (P.subgroupOf M) (conjM M g hg) (by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hx
    exact hgP _ hx)

theorem actQ_mk (g : G) (hg : ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hgP : ∀ p ∈ P, g * p * g⁻¹ ∈ P)
    (x : ↥M) : actQ M P g hg hgP (QuotientGroup.mk x) = QuotientGroup.mk (conjM M g hg x) :=
  rfl

end Quot

section Action

variable {G : Type*} [Group G]

structure NormH (M P : Subgroup G) (g : G) : Prop where
  conjM : ∀ m ∈ M, g * m * g⁻¹ ∈ M
  conjM' : ∀ m ∈ M, g⁻¹ * m * g ∈ M
  conjP : ∀ p ∈ P, g * p * g⁻¹ ∈ P
  conjP' : ∀ p ∈ P, g⁻¹ * p * g ∈ P

theorem NormH.mul' {M P : Subgroup G} {g g' : G} (h : NormH M P g) (h' : NormH M P g') :
    NormH M P (g * g') where
  conjM m hm := by
    have := h.conjM _ (h'.conjM m hm)
    simpa [mul_assoc] using this
  conjM' m hm := by
    have := h'.conjM' _ (h.conjM' m hm)
    simpa [mul_assoc] using this
  conjP p hp := by
    have := h.conjP _ (h'.conjP p hp)
    simpa [mul_assoc] using this
  conjP' p hp := by
    have := h'.conjP' _ (h.conjP' p hp)
    simpa [mul_assoc] using this

theorem NormH.inv' {M P : Subgroup G} {g : G} (h : NormH M P g) : NormH M P g⁻¹ where
  conjM m hm := by simpa using h.conjM' m hm
  conjM' m hm := by simpa using h.conjM m hm
  conjP p hp := by simpa using h.conjP' p hp
  conjP' p hp := by simpa using h.conjP p hp

theorem NormH.one' (M P : Subgroup G) : NormH M P 1 where
  conjM m hm := by simpa using hm
  conjM' m hm := by simpa using hm
  conjP p hp := by simpa using hp
  conjP' p hp := by simpa using hp

variable (M P : Subgroup G) [hN : (P.subgroupOf M).Normal]

@[expose] def actV (g : G) (h : NormH M P g) :
    (↥M ⧸ P.subgroupOf M) →* (↥M ⧸ P.subgroupOf M) :=
  actQ M P g h.conjM h.conjP

theorem actV_congr {g g' : G} (e : g = g') (h : NormH M P g) (h' : NormH M P g') (v : ↥M ⧸ P.subgroupOf M) :
    actV M P g h v = actV M P g' h' v := by
  subst e
  rfl

theorem actV_mul {g g' : G} (h : NormH M P g) (h' : NormH M P g') (v : ↥M ⧸ P.subgroupOf M) :
    actV M P (g * g') (h.mul' h') v = actV M P g h (actV M P g' h' v) := by
  induction v using QuotientGroup.induction_on with
  | H x =>
    simp only [actV, actQ_mk]
    congr 1
    ext
    simp only [conjM_coe]
    group

theorem actV_one (v : ↥M ⧸ P.subgroupOf M) : actV M P 1 (NormH.one' M P) v = v := by
  induction v using QuotientGroup.induction_on with
  | H x =>
    simp only [actV, actQ_mk]
    congr 1
    ext
    simp [conjM_coe]

@[expose] def actE (g : G) (h : NormH M P g) : (↥M ⧸ P.subgroupOf M) ≃* (↥M ⧸ P.subgroupOf M) where
  toFun v := actV M P g h v
  invFun v := actV M P g⁻¹ h.inv' v
  left_inv v := by
    show actV M P g⁻¹ h.inv' (actV M P g h v) = v
    rw [← actV_mul M P h.inv' h]
    rw [actV_congr M P (inv_mul_cancel g) _ (NormH.one' M P)]
    exact actV_one M P v
  right_inv v := by
    show actV M P g h (actV M P g⁻¹ h.inv' v) = v
    rw [← actV_mul M P h h.inv']
    rw [actV_congr M P (mul_inv_cancel g) _ (NormH.one' M P)]
    exact actV_one M P v
  map_mul' v w := (actV M P g h).map_mul v w

theorem actE_congr {g g' : G} (e : g = g') (h : NormH M P g) (h' : NormH M P g') :
    actE M P g h = actE M P g' h' := by
  subst e
  rfl

@[expose] def actHomK (K : Subgroup G) (hK : ∀ k ∈ K, NormH M P k) :
    K →* MulAut (↥M ⧸ P.subgroupOf M) where
  toFun k := actE M P (k : G) (hK k k.2)
  map_one' := by
    ext v
    rw [actE_congr M P (Subgroup.coe_one K) (hK 1 K.one_mem) (NormH.one' M P)]
    exact actV_one M P v
  map_mul' a b := by
    ext v
    rw [actE_congr M P (Subgroup.coe_mul K a b) (hK (a * b) (K.mul_mem a.2 b.2))
      ((hK a a.2).mul' (hK b b.2)), MulAut.mul_apply]
    exact actV_mul M P (hK a a.2) (hK b b.2) v

end Action

section Central

variable {G : Type*} [Group G]

theorem mem_zpowers_commute {a b : G} (h : a * b = b * a) {p : G} (hp : p ∈ Subgroup.zpowers b) :
    a * p = p * a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  have hc : Commute a b := h
  exact (hc.zpow_right k).eq

theorem actV_fixed_free [Finite G] {M : Subgroup G} {τ z : G} (hτM : τ ∈ M)
    [((Subgroup.zpowers τ).subgroupOf M).Normal]
    (hzz : z * z = 1) (hzn : NormH M (Subgroup.zpowers τ) z)
    (hodd : Odd (Nat.card (Subgroup.zpowers τ)))
    (hCz : ∀ x ∈ M, z * x * z⁻¹ = x → x ∈ Subgroup.zpowers τ) :
    ∀ v : ↥M ⧸ (Subgroup.zpowers τ).subgroupOf M, actV M (Subgroup.zpowers τ) z hzn v = v →
      v = 1 := by
  intro v hv
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  rw [actV, actQ_mk, QuotientGroup.eq] at hv
  rw [Subgroup.mem_subgroupOf] at hv
  have hq : (z * (x : G) * z⁻¹)⁻¹ * x ∈ Subgroup.zpowers τ := by
    simpa [conjM_coe] using hv
  have hfixcoset : ∃ p ∈ Subgroup.zpowers τ, z * (x : G) * z⁻¹ = x * p := by
    refine ⟨((z * (x : G) * z⁻¹)⁻¹ * x)⁻¹, Subgroup.inv_mem _ hq, ?_⟩
    group
  obtain ⟨p, hp, hfixp⟩ := exists_fixed_in_coset z (x : G) hzz (Subgroup.zpowers τ) hodd
    (fun q hq => hzn.conjP q hq) hfixcoset
  have hτM' : Subgroup.zpowers τ ≤ M := (Subgroup.zpowers_le).mpr hτM
  have hxpM : (x : G) * p ∈ M := M.mul_mem x.2 (hτM' hp)
  have hxp : (x : G) * p ∈ Subgroup.zpowers τ := hCz _ hxpM hfixp
  have hxz : (x : G) ∈ Subgroup.zpowers τ := by
    have := Subgroup.mul_mem _ hxp (Subgroup.inv_mem _ hp)
    simpa using this
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hxz

@[expose] def cmt (σ x : G) : G := σ * x * σ⁻¹ * x⁻¹

theorem cmt_mul (σ a b : G) : cmt σ (a * b) = cmt σ a * (a * cmt σ b * a⁻¹) := by
  unfold cmt
  group

theorem cmt_inv (σ a : G) : cmt σ a⁻¹ = a⁻¹ * (cmt σ a)⁻¹ * a := by
  have h := cmt_mul σ a a⁻¹
  rw [mul_inv_cancel] at h
  have h1 : cmt σ (1 : G) = 1 := by unfold cmt; group
  rw [h1] at h
  have h2 : cmt σ a * (a * cmt σ a⁻¹ * a⁻¹) = 1 := h.symm
  have h3 : a * cmt σ a⁻¹ * a⁻¹ = (cmt σ a)⁻¹ := eq_inv_of_mul_eq_one_right h2
  calc cmt σ a⁻¹ = a⁻¹ * (a * cmt σ a⁻¹ * a⁻¹) * a := by group
    _ = a⁻¹ * (cmt σ a)⁻¹ * a := by rw [h3]

theorem cmt_zpowers (σ τ : G) (hστ : σ * τ = τ * σ) {q : G} (hq : q ∈ Subgroup.zpowers τ) :
    cmt σ q = 1 := by
  have hc : σ * q = q * σ := mem_zpowers_commute hστ hq
  unfold cmt
  calc σ * q * σ⁻¹ * q⁻¹ = q * σ * σ⁻¹ * q⁻¹ := by rw [hc]
    _ = 1 := by group

theorem cmt_conj_z (σ z a : G) (hσz : σ * z = z * σ) :
    cmt σ (z * a * z⁻¹) = z * cmt σ a * z⁻¹ := by
  have hσz2 : z⁻¹ * σ * z = σ := by
    calc z⁻¹ * σ * z = z⁻¹ * (σ * z) := by group
      _ = z⁻¹ * (z * σ) := by rw [hσz]
      _ = σ := by group
  have hσz3 : z⁻¹ * σ⁻¹ * z = σ⁻¹ := by
    calc z⁻¹ * σ⁻¹ * z = (z⁻¹ * σ * z)⁻¹ := by group
      _ = σ⁻¹ := by rw [hσz2]
  unfold cmt
  calc σ * (z * a * z⁻¹) * σ⁻¹ * (z * a * z⁻¹)⁻¹
      = z * (z⁻¹ * σ * z) * a * (z⁻¹ * σ⁻¹ * z) * z⁻¹ * (z * a⁻¹ * z⁻¹) := by group
    _ = z * σ * a * σ⁻¹ * z⁻¹ * (z * a⁻¹ * z⁻¹) := by rw [hσz2, hσz3]
    _ = z * (σ * a * σ⁻¹ * a⁻¹) * z⁻¹ := by group

theorem pow_three_eq_one_of_mem_zpowers {τ c : G} (hτ3 : orderOf τ = 3)
    (hc : c ∈ Subgroup.zpowers τ) : c ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h3 : τ ^ (3 : ℕ) = 1 := by
    rw [← hτ3]
    exact pow_orderOf_eq_one τ
  have hcomm : Commute (τ ^ k) (τ ^ k) := Commute.refl _
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  have : τ ^ ((3 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast]
    exact h3
  rw [this, one_zpow]

theorem cmt_eq_one_of_mem_zpowers {M : Subgroup G} {τ z σ : G}
    (hcentM : ∀ m ∈ M, m * τ = τ * m) (hτ3 : orderOf τ = 3)
    (hστ : σ * τ = τ * σ) (hσz : σ * z = z * σ) (hzτ : z * τ = τ * z)
    (hzM : ∀ m ∈ M, z * m * z⁻¹ ∈ M)
    (hQ2 : ∀ x ∈ M, x * (z * x * z⁻¹) ∈ Subgroup.zpowers τ)
    (x : G) (hx : x ∈ M) (hc : cmt σ x ∈ Subgroup.zpowers τ) : cmt σ x = 1 := by
  set c := cmt σ x with hcdef
  have hxy : x * (z * x * z⁻¹) ∈ Subgroup.zpowers τ := hQ2 x hx
  have hxcomm : x * c = c * x := mem_zpowers_commute (hcentM x hx) hc
  have hA : cmt σ (z * x * z⁻¹) = c⁻¹ := by
    have e1 : z * x * z⁻¹ = x⁻¹ * (x * (z * x * z⁻¹)) := by group
    rw [e1, cmt_mul, cmt_zpowers σ τ hστ hxy, cmt_inv]
    have h' : c⁻¹ * x = x * c⁻¹ := by
      calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hxcomm]
        _ = x * c⁻¹ := by group
    have hcinv : x⁻¹ * c⁻¹ * x = c⁻¹ := by
      calc x⁻¹ * c⁻¹ * x = x⁻¹ * (c⁻¹ * x) := by group
        _ = x⁻¹ * (x * c⁻¹) := by rw [h']
        _ = c⁻¹ := by group
    rw [hcinv]
    group
  have hB : cmt σ (z * x * z⁻¹) = c := by
    rw [cmt_conj_z σ z x hσz]
    have hzc : z * c = c * z := mem_zpowers_commute hzτ hc
    calc z * c * z⁻¹ = c * z * z⁻¹ := by rw [hzc]
      _ = c := by group
  have hinv : c⁻¹ = c := hA.symm.trans hB
  have hc2 : c * c = 1 := by
    nth_rewrite 2 [← hinv]
    exact mul_inv_cancel c
  have hc3 : c ^ 3 = 1 := pow_three_eq_one_of_mem_zpowers hτ3 hc
  calc c = c ^ 3 * (c * c)⁻¹ := by group
    _ = 1 := by rw [hc3, hc2]; simp

theorem actV_inv_of [Finite G] {M : Subgroup G} {τ z : G} (hτM : τ ∈ M)
    [((Subgroup.zpowers τ).subgroupOf M).Normal]
    (hzz : z * z = 1) (hzn : NormH M (Subgroup.zpowers τ) z)
    (hodd : Odd (Nat.card (Subgroup.zpowers τ)))
    (hCz : ∀ x ∈ M, z * x * z⁻¹ = x → x ∈ Subgroup.zpowers τ)
    (v : ↥M ⧸ (Subgroup.zpowers τ).subgroupOf M) :
    actV M (Subgroup.zpowers τ) z hzn v = v⁻¹ := by
  have hα : ∀ x, actV M (Subgroup.zpowers τ) z hzn (actV M (Subgroup.zpowers τ) z hzn x) = x := by
    intro x
    rw [← actV_mul M (Subgroup.zpowers τ) hzn hzn,
      actV_congr M (Subgroup.zpowers τ) hzz _ (NormH.one' M _), actV_one]
  have hfix : ∀ x, actE M (Subgroup.zpowers τ) z hzn x = x → x = 1 := fun x hx =>
    actV_fixed_free hτM hzz hzn hodd hCz x hx
  exact inverts_of_fixed_free (actE M (Subgroup.zpowers τ) z hzn) hα hfix v

theorem inv_mem_of_quot [Finite G] {M : Subgroup G} {τ z : G} (hτM : τ ∈ M)
    [((Subgroup.zpowers τ).subgroupOf M).Normal]
    (hzz : z * z = 1) (hzn : NormH M (Subgroup.zpowers τ) z)
    (hodd : Odd (Nat.card (Subgroup.zpowers τ)))
    (hCz : ∀ x ∈ M, z * x * z⁻¹ = x → x ∈ Subgroup.zpowers τ)
    (x : G) (hx : x ∈ M) : x * (z * x * z⁻¹) ∈ Subgroup.zpowers τ := by
  have h := actV_inv_of hτM hzz hzn hodd hCz (QuotientGroup.mk ⟨x, hx⟩)
  rw [actV, actQ_mk, ← QuotientGroup.mk_inv, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  have h2 : ((conjM M z hzn.conjM ⟨x, hx⟩)⁻¹ * (⟨x, hx⟩ : ↥M)⁻¹ : ↥M) = ((conjM M z hzn.conjM ⟨x, hx⟩)⁻¹ * (⟨x, hx⟩ : ↥M)⁻¹ : ↥M) := rfl
  have h3 : ((conjM M z hzn.conjM ⟨x, hx⟩)⁻¹ * (⟨x, hx⟩ : ↥M)⁻¹ : ↥M).1 ∈ Subgroup.zpowers τ := h
  have h4 : x * (z * x * z⁻¹) = (((conjM M z hzn.conjM ⟨x, hx⟩)⁻¹ * (⟨x, hx⟩ : ↥M)⁻¹ : ↥M) : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjM_coe]
    group
  rw [h4]
  exact Subgroup.inv_mem _ h3

theorem card_centralizer_eq_three_mul_fix [Finite G] {M : Subgroup G} {τ z σ : G}
    (hτM : τ ∈ M) (hcentM : ∀ m ∈ M, m * τ = τ * m) (hτ3 : orderOf τ = 3)
    [((Subgroup.zpowers τ).subgroupOf M).Normal]
    (hστ : σ * τ = τ * σ) (hσz : σ * z = z * σ) (hzτ : z * τ = τ * z) (hzz : z * z = 1)
    (hzn : NormH M (Subgroup.zpowers τ) z) (hσn : NormH M (Subgroup.zpowers τ) σ)
    (hCz : ∀ x ∈ M, z * x * z⁻¹ = x → x ∈ Subgroup.zpowers τ) :
    Nat.card {x : ↥M // (x : G) * σ = σ * (x : G)} =
      3 * Nat.card {v : ↥M ⧸ (Subgroup.zpowers τ).subgroupOf M //
        actV M (Subgroup.zpowers τ) σ hσn v = v} := by
  have hPM : Subgroup.zpowers τ ≤ M := (Subgroup.zpowers_le).mpr hτM
  have hodd : Odd (Nat.card (Subgroup.zpowers τ)) := by
    rw [Nat.card_zpowers, hτ3]
    decide
  have hQ2 : ∀ x ∈ M, x * (z * x * z⁻¹) ∈ Subgroup.zpowers τ :=
    fun x hx => inv_mem_of_quot hτM hzz hzn hodd hCz x hx
  let Csub : Subgroup ↥M := (Subgroup.centralizer {σ}).subgroupOf M
  have hCsub : ∀ x : ↥M, x ∈ Csub ↔ (x : G) * σ = σ * (x : G) := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  let π : Csub →* (↥M ⧸ (Subgroup.zpowers τ).subgroupOf M) :=
    (QuotientGroup.mk' ((Subgroup.zpowers τ).subgroupOf M)).comp Csub.subtype
  have hπ : ∀ x : Csub, π x = QuotientGroup.mk (x : ↥M) := fun x => rfl
  have hrange : ∀ v, v ∈ π.range ↔ actV M (Subgroup.zpowers τ) σ hσn v = v := by
    intro v
    constructor
    · rintro ⟨x, rfl⟩
      rw [hπ, actV, actQ_mk]
      congr 1
      ext
      simp only [conjM_coe]
      have hx := (hCsub x.1).mp x.2
      calc σ * (x : G) * σ⁻¹ = (x : G) * σ * σ⁻¹ := by rw [← hx]
        _ = (x : G) := by group
    · intro hfix
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
      rw [actV, actQ_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hfix
      have hq : cmt σ (y : G)⁻¹ ∈ Subgroup.zpowers τ := by
        unfold cmt
        simpa [conjM_coe, mul_assoc] using hfix
      have hyM : (y : G) ∈ M := y.2
      have hcomm' : (y : G) * cmt σ (y : G)⁻¹ * (y : G)⁻¹ = cmt σ (y : G)⁻¹ :=
        (mem_zpowers_commute (hcentM _ hyM) hq).symm ▸ by group
      have hcy : cmt σ (y : G) ∈ Subgroup.zpowers τ := by
        have hinv : (cmt σ (y : G))⁻¹ = (y : G) * cmt σ (y : G)⁻¹ * (y : G)⁻¹ := by
          rw [cmt_inv]
          group
        have : (cmt σ (y : G))⁻¹ ∈ Subgroup.zpowers τ := by
          rw [hinv, hcomm']
          exact hq
        simpa using Subgroup.inv_mem _ this
      have h1 := cmt_eq_one_of_mem_zpowers (M := M) hcentM hτ3 hστ hσz hzτ
        (fun m hm => hzn.conjM m hm) hQ2 (y : G) hyM hcy
      have hyC : (y : G) * σ = σ * (y : G) := by
        unfold cmt at h1
        have : σ * (y : G) * σ⁻¹ = (y : G) := by
          calc σ * (y : G) * σ⁻¹ = σ * (y : G) * σ⁻¹ * (y : G)⁻¹ * (y : G) := by group
            _ = (y : G) := by rw [h1]; group
        calc (y : G) * σ = σ * (y : G) * σ⁻¹ * σ := by rw [this]
          _ = σ * (y : G) := by group
      exact ⟨⟨y, (hCsub y).mpr hyC⟩, rfl⟩
  have hmemk : ∀ x : π.ker, ((x.1 : ↥M) : G) ∈ Subgroup.zpowers τ := by
    intro x
    have h := MonoidHom.mem_ker.mp x.2
    rw [hπ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact h
  have hbij : Function.Bijective
      (fun x : π.ker => (⟨((x.1 : ↥M) : G), hmemk x⟩ : Subgroup.zpowers τ)) := by
    constructor
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      have h' : (x.1 : ↥M) = (y.1 : ↥M) := Subtype.ext h
      exact Subtype.ext (Subtype.ext h')
    · intro q
      obtain ⟨q, hq⟩ := q
      have hqM : q ∈ M := hPM hq
      have hqC : q * σ = σ * q := (mem_zpowers_commute hστ hq).symm
      refine ⟨⟨⟨⟨q, hqM⟩, (hCsub _).mpr hqC⟩, ?_⟩, ?_⟩
      · rw [MonoidHom.mem_ker, hπ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hq
      · rfl
  have hker : Nat.card π.ker = 3 := by
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_zpowers, hτ3]
  have hcard := Subgroup.card_ker_mul_card_range π
  have hC : Nat.card Csub = Nat.card {x : ↥M // (x : G) * σ = σ * (x : G)} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => hCsub x))
  have hR : Nat.card π.range = Nat.card {v : ↥M ⧸ (Subgroup.zpowers τ).subgroupOf M //
      actV M (Subgroup.zpowers τ) σ hσn v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight hrange)
  rw [← hC, ← hcard, hker, hR]

end Central

section FixCount

variable {V : Type*} [Group V]

@[expose] def fixSub (α : MulAut V) : Subgroup V where
  carrier := {v | α v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

theorem fix_card_dvd [Finite V] (α : MulAut V) :
    Nat.card {v // α v = v} ∣ Nat.card V :=
  Subgroup.card_subgroup_dvd_card (fixSub α)

theorem fix_card_modEq_three [Finite V] (α : MulAut V) (h3 : ∀ v, α (α (α v)) = v) :
    Nat.card V ≡ Nat.card {v // α v = v} [MOD 3] := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  let F : V → V := fun v => α v
  let f : Function.End V := F
  have hf : f ^ 3 ^ 1 = 1 := by
    funext v
    show (F^[3]) v = v
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    exact h3 v
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf
  have e1 : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  have e2 : Nat.card {v // α v = v} = Fintype.card (Function.fixedPoints f) := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [e1, e2]
  exact hmod

end FixCount

end PartA

section PartB

abbrev SL23 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

theorem det_of_sl (A : SL23) : (A : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe A

def negOne23 : SL23 := ⟨-1, by
  have h : (-1 : M2).det = 1 := by decide +kernel
  exact h⟩

theorem sl_inv_eq (A : SL23) (h : A * A = 1) (h1 : A ≠ 1) : A = negOne23 := by
  have hM : (A : M2) * (A : M2) = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  have hA1 : (A : M2) ≠ 1 := fun e => h1 (Subtype.ext (by simpa using e))
  have h2 : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 := sl_unique_invol (A : M2) (det_of_sl A) hM hA1
  exact Subtype.ext (by simpa [negOne23] using h2)

theorem sl_central_eq (A : SL23) (hA : ∀ B : SL23, A * B = B * A) :
    A = 1 ∨ A = negOne23 := by
  have key : ∀ q : M2, q.det = 1 → q ^ 4 = 1 → (A : M2) * q = q * (A : M2) := by
    intro q hq _
    have := congrArg Subtype.val (hA ⟨q, hq⟩)
    exact this
  rcases centralizer_Q8 (A : M2) (det_of_sl A) key with h | h
  · left
    exact Subtype.ext (by simpa using h)
  · right
    have h2 : (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 := h
    exact Subtype.ext (by simpa [negOne23] using h2)

theorem negOne23_mul_self : negOne23 * negOne23 = 1 := by
  apply Subtype.ext
  simp [negOne23]
  decide +kernel

theorem card_sl23 : Nat.card SL23 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_L {G : Type*} [Group G] (L : Subgroup G) (φ : L ≃* SL23) : Nat.card L = 24 := by
  rw [Nat.card_congr φ.toEquiv, card_sl23]

theorem unique_invol_L {G : Type*} [Group G] (L : Subgroup G) (φ : L ≃* SL23) (z : G)
    (hzL : z ∈ L) (hz1 : z ≠ 1) (hzc : ∀ g ∈ L, g * z = z * g) :
    ∀ u : G, u ∈ L → u * u = 1 → u ≠ 1 → u = z := by
  have hc : ∀ B : SL23, φ ⟨z, hzL⟩ * B = B * φ ⟨z, hzL⟩ := by
    intro B
    obtain ⟨g, rfl⟩ := φ.surjective B
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hzc g g.2).symm
  have hzz : φ ⟨z, hzL⟩ = negOne23 := by
    rcases sl_central_eq _ hc with h | h
    · exfalso
      apply hz1
      have : (⟨z, hzL⟩ : L) = 1 := φ.injective (by rw [h, map_one])
      exact congrArg Subtype.val this
    · exact h
  intro u hu hu2 hu1
  let uL : L := ⟨u, hu⟩
  have huL : uL * uL = 1 := Subtype.ext (by simpa using hu2)
  have huL1 : uL ≠ 1 := fun e => hu1 (congrArg Subtype.val e)
  by_cases h1 : φ uL = 1
  · exfalso
    exact huL1 (φ.injective (by rw [h1, map_one]))
  · have hsq : φ uL * φ uL = 1 := by rw [← map_mul, huL, map_one]
    have hneg := sl_inv_eq (φ uL) hsq h1
    have : uL = ⟨z, hzL⟩ := φ.injective (by rw [hneg, hzz])
    exact congrArg Subtype.val this

theorem card_T8_L {G : Type*} [Group G] (L : Subgroup G) (φ : L ≃* SL23) [Fintype L]
    [DecidableEq L] :
    (Finset.univ.filter (fun x : L => x ^ 3 = 1 ∧ x ≠ 1)).card = 8 := by
  have hM2 : ((Finset.univ : Finset M2).filter (fun A => A.det = 1 ∧ A * A * A = 1 ∧ A ≠ 1)).card
      = 8 := by decide +kernel
  have hSL : ((Finset.univ : Finset SL23).filter (fun A => A * A * A = 1 ∧ A ≠ 1)).card = 8 := by
    rw [← hM2]
    apply Finset.card_nbij (fun A : SL23 => (A : M2))
    · intro A hA
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hA ⊢
      refine ⟨det_of_sl A, ?_, fun e => hA.2 (Subtype.ext e)⟩
      have := congrArg Subtype.val hA.1
      exact this
    · intro A _ B _ hAB
      exact Subtype.ext hAB
    · intro M hM
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hM
      refine ⟨⟨M, hM.1⟩, ?_, rfl⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      refine ⟨?_, fun e => hM.2.2 (congrArg Subtype.val e)⟩
      apply Subtype.ext
      exact hM.2.1
  rw [← hSL]
  apply Finset.card_nbij (fun x : L => φ x)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨?_, fun e => hx.2 (φ.injective (by rw [e, map_one]))⟩
    have h3 : φ x * φ x * φ x = φ (x ^ 3) := by
      rw [map_pow]
      simp only [pow_three, mul_assoc]
    rw [h3, hx.1, map_one]
  · intro x _ y _ hxy
    exact φ.injective hxy
  · intro A hA
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    refine ⟨φ.symm A, ?_, by simp⟩
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · have h3 : (φ.symm A) ^ 3 = φ.symm (A * A * A) := by
        simp only [pow_three, mul_assoc, map_mul]
      rw [h3, hA.1, map_one]
    · intro e
      apply hA.2
      rw [← MulEquiv.apply_symm_apply φ A, e, map_one]

theorem conj23 : ∀ s ∈ (Finset.univ : Finset M2).filter (fun s => s.det = 1 ∧ s * s * s = 1 ∧ s ≠ 1),
    ∀ x ∈ (Finset.univ : Finset M2).filter (fun x => x.det = 1 ∧ x * x * x = 1 ∧ x ≠ 1),
    ∃ h ∈ (Finset.univ : Finset M2).filter (fun h => h.det = 1),
      (h * s = x * h ∨ h * s = (x * x) * h) := by
  decide +kernel

theorem conj_L {G : Type*} [Group G] (L : Subgroup G) (φ : L ≃* SL23) (σ' : L)
    (hσ3 : σ' ^ 3 = 1) (hσ1 : σ' ≠ 1) :
    ∀ x : L, x ^ 3 = 1 → x ≠ 1 → ∃ g : L, x = g * σ' * g⁻¹ ∨ x = g * σ'⁻¹ * g⁻¹ := by
  intro x hx3 hx1
  have hs3 : φ σ' * φ σ' * φ σ' = 1 := by
    have h3 : φ σ' * φ σ' * φ σ' = φ (σ' ^ 3) := by
      rw [map_pow]
      simp only [pow_three, mul_assoc]
    rw [h3, hσ3, map_one]
  have hs1 : φ σ' ≠ 1 := fun e => hσ1 (φ.injective (by rw [e, map_one]))
  have hy3 : φ x * φ x * φ x = 1 := by
    have h3 : φ x * φ x * φ x = φ (x ^ 3) := by
      rw [map_pow]
      simp only [pow_three, mul_assoc]
    rw [h3, hx3, map_one]
  have hy1 : φ x ≠ 1 := fun e => hx1 (φ.injective (by rw [e, map_one]))
  have hmem1 : (φ σ' : M2) ∈ (Finset.univ : Finset M2).filter
      (fun s => s.det = 1 ∧ s * s * s = 1 ∧ s ≠ 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨det_of_sl _, ?_, fun e => hs1 (Subtype.ext e)⟩
    exact congrArg Subtype.val hs3
  have hmem2 : (φ x : M2) ∈ (Finset.univ : Finset M2).filter
      (fun s => s.det = 1 ∧ s * s * s = 1 ∧ s ≠ 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨det_of_sl _, ?_, fun e => hy1 (Subtype.ext e)⟩
    exact congrArg Subtype.val hy3
  obtain ⟨h, hhD, hh⟩ := conj23 _ hmem1 _ hmem2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hhD
  let H' : SL23 := ⟨h, hhD⟩
  refine ⟨φ.symm H', ?_⟩
  have key : φ (φ.symm H' * σ' * (φ.symm H')⁻¹) = H' * φ σ' * H'⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have key2 : φ (φ.symm H' * σ'⁻¹ * (φ.symm H')⁻¹) = H' * (φ σ')⁻¹ * H'⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
  rcases hh with hh | hh
  · left
    apply φ.injective
    rw [key]
    have hSL : H' * φ σ' = φ x * H' := Subtype.ext hh
    rw [hSL]
    group
  · right
    apply φ.injective
    rw [key2]
    have hSL : H' * φ σ' = φ x * φ x * H' := Subtype.ext hh
    have hconj : H' * φ σ' * H'⁻¹ = φ x * φ x := by
      rw [hSL]
      group
    have heq : φ x * φ x = (φ x)⁻¹ := eq_inv_of_mul_eq_one_left hy3
    have : H' * (φ σ')⁻¹ * H'⁻¹ = (H' * φ σ' * H'⁻¹)⁻¹ := by group
    rw [this, hconj, heq, inv_inv]

theorem sq_one_of_central_L {G : Type*} [Group G] (L : Subgroup G) (φ : L ≃* SL23) (z : G)
    (hzL : z ∈ L) (hz1 : z ≠ 1) (hzc : ∀ g ∈ L, g * z = z * g) : z * z = 1 := by
  have hc : ∀ B : SL23, φ ⟨z, hzL⟩ * B = B * φ ⟨z, hzL⟩ := by
    intro B
    obtain ⟨g, rfl⟩ := φ.surjective B
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hzc g g.2).symm
  have hzz : φ ⟨z, hzL⟩ = negOne23 := by
    rcases sl_central_eq _ hc with h | h
    · exfalso
      apply hz1
      have : (⟨z, hzL⟩ : L) = 1 := φ.injective (by rw [h, map_one])
      exact congrArg Subtype.val this
    · exact h
  have hsq : (⟨z, hzL⟩ : L) * ⟨z, hzL⟩ = 1 := by
    apply φ.injective
    rw [map_mul, hzz, negOne23_mul_self, map_one]
  exact congrArg Subtype.val hsq

end PartB

section PartC

variable {G : Type} [Group G]

theorem conj_pow_eq (g x : G) (n : ℕ) : (g * x * g⁻¹) ^ n = g * x ^ n * g⁻¹ := by
  have h := map_pow (MulAut.conj g).toMonoidHom x n
  exact h.symm

theorem pow_three_of_card_nine_cent [Finite G] {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}
    (hF : HFacts H H₁ H₂ e) (hO : OneClass e)
    (hHC : ∀ y : G, y ∈ H ↔ y * zOf e = zOf e * y)
    (u : G) (S : Subgroup G) (hS : S ≤ Subgroup.centralizer {u})
    (hS9 : Nat.card S = 9) (hu : orderOf u = 2) (x : G) (hx : x ∈ S) : x ^ 3 = 1 := by
  obtain ⟨g, hg⟩ := (isConj_iff.mp (hO u hu))
  have hz : g⁻¹ * u * g = zOf e := by
    rw [← hg]
    group
  let S' : Subgroup G := S.map (MulAut.conj g⁻¹).toMonoidHom
  have hS'H : S' ≤ H := by
    rintro y ⟨w, hw, rfl⟩
    rw [hHC]
    have hwu : w * u = u * w := Subgroup.mem_centralizer_singleton_iff.mp (hS hw)
    show g⁻¹ * w * g⁻¹⁻¹ * zOf e = zOf e * (g⁻¹ * w * g⁻¹⁻¹)
    rw [inv_inv]
    calc g⁻¹ * w * g * zOf e = g⁻¹ * (w * u) * g := by
          rw [← hg]
          group
      _ = g⁻¹ * (u * w) * g := by rw [hwu]
      _ = zOf e * (g⁻¹ * w * g) := by
          rw [← hz]
          group
  have hS'card : Nat.card S' = 9 := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective]
    exact hS9
  have hodd : Odd (Nat.card S') := by
    rw [hS'card]
    decide
  obtain ⟨_, hex⟩ := hF.odd_sub S' hS'H hodd
  obtain ⟨h, hhH, hP⟩ := hex hS'card
  have hP' : (Psub e).map (MulAut.conj h).toMonoidHom = S' := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨p, hp, rfl⟩
      exact hP p hp
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom)
        (MulAut.conj h).injective, hS'card, hF.card_P]
  have hy : (MulAut.conj g⁻¹) x ∈ S' := ⟨x, hx, rfl⟩
  rw [← hP'] at hy
  obtain ⟨p, hp, hpy⟩ := hy
  have hp3 : p ^ 3 = 1 := hF.elem_P.2 p hp
  have hy3 : ((MulAut.conj g⁻¹) x) ^ 3 = 1 := by
    rw [← hpy]
    show (h * p * h⁻¹) ^ 3 = 1
    rw [conj_pow_eq, hp3]
    group
  have hxy : x = g * ((MulAut.conj g⁻¹) x) * g⁻¹ := by
    show x = g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹
    rw [inv_inv]
    group
  generalize hyy : (MulAut.conj g⁻¹) x = y at hy3 hxy
  rw [hxy]
  rw [conj_pow_eq, hy3]
  group

end PartC

section PartD

variable {G : Type*} [Group G]

theorem fix_lift [Finite G] {M P : Subgroup G} [(P.subgroupOf M).Normal] (hPodd : Odd (Nat.card P))
    (hPM : P ≤ M) (τ' : G) (hττ : τ' * τ' = 1) (hn : NormH M P τ')
    (v : ↥M ⧸ P.subgroupOf M) (hv : actV M P τ' hn v = v) :
    ∃ x : ↥M, τ' * (x : G) * τ'⁻¹ = (x : G) ∧ (QuotientGroup.mk x : ↥M ⧸ P.subgroupOf M) = v := by
  obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective v
  rw [actV, actQ_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hv
  have hq : (τ' * (x0 : G) * τ'⁻¹)⁻¹ * x0 ∈ P := by
    simpa [conjM_coe] using hv
  have hfix : ∃ p ∈ P, τ' * (x0 : G) * τ'⁻¹ = (x0 : G) * p := by
    refine ⟨((τ' * (x0 : G) * τ'⁻¹)⁻¹ * x0)⁻¹, Subgroup.inv_mem _ hq, ?_⟩
    group
  obtain ⟨p, hp, hfixp⟩ := exists_fixed_in_coset τ' (x0 : G) hττ P hPodd
    (fun q hq' => hn.conjP q hq') hfix
  have hxM : (x0 : G) * p ∈ M := M.mul_mem x0.2 (hPM hp)
  refine ⟨⟨(x0 : G) * p, hxM⟩, hfixp, ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  show ((x0 : G) * p)⁻¹ * (x0 : G) ∈ P
  have : ((x0 : G) * p)⁻¹ * (x0 : G) = p⁻¹ := by group
  rw [this]
  exact Subgroup.inv_mem _ hp

theorem exp3_of_fixed [Finite G] {M P : Subgroup G} [(P.subgroupOf M).Normal]
    (hPodd : Odd (Nat.card P)) (hPM : P ≤ M) (τ' : G) (hττ : τ' * τ' = 1) (hn : NormH M P τ')
    (hcube : ∀ x : ↥M, τ' * (x : G) * τ'⁻¹ = (x : G) → x ^ 3 = 1)
    (v : ↥M ⧸ P.subgroupOf M) (hv : actV M P τ' hn v = v) : v ^ 3 = 1 := by
  obtain ⟨x, hx, rfl⟩ := fix_lift hPodd hPM τ' hττ hn v hv
  rw [← QuotientGroup.mk_pow, hcube x hx]
  rfl

theorem exp3_quot [Finite G] {M P : Subgroup G} [(P.subgroupOf M).Normal]
    (hPodd : Odd (Nat.card P)) (hPM : P ≤ M)
    (t z : G) (htt : t * t = 1) (htz : t * z = z * t) (htz2 : (t * z) * (t * z) = 1)
    (ht : NormH M P t) (hz : NormH M P z) (htz' : NormH M P (t * z))
    (hinvz : ∀ v : ↥M ⧸ P.subgroupOf M, actV M P z hz v = v⁻¹)
    (hexpt : ∀ x : ↥M, t * (x : G) * t⁻¹ = (x : G) → x ^ 3 = 1)
    (hexptz : ∀ x : ↥M, (t * z) * (x : G) * (t * z)⁻¹ = (x : G) → x ^ 3 = 1)
    (hcomm : ∀ a b : ↥M ⧸ P.subgroupOf M, a * b = b * a)
    (hcard : Nat.card (↥M ⧸ P.subgroupOf M) = 81) :
    ∀ v : ↥M ⧸ P.subgroupOf M, v ^ 3 = 1 := by
  intro v
  have hinvt : ∀ u, actV M P t ht (actV M P t ht u) = u := by
    intro u
    rw [← actV_mul M P ht ht, actV_congr M P htt _ (NormH.one' M P), actV_one]
  have hinvtz : ∀ u, actV M P (t * z) htz' u = actV M P t ht (actV M P z hz u) := by
    intro u
    exact actV_mul M P ht hz u
  have ha : actV M P t ht (v * actV M P t ht v) = v * actV M P t ht v := by
    rw [(actV M P t ht).map_mul, hinvt]
    exact hcomm _ _
  have hb : actV M P (t * z) htz' (v * (actV M P t ht v)⁻¹) = v * (actV M P t ht v)⁻¹ := by
    have e1 : actV M P (t * z) htz' (v * (actV M P t ht v)⁻¹) =
        actV M P t ht ((v * (actV M P t ht v)⁻¹)⁻¹) := by
      rw [hinvtz, hinvz]
    have e3 : actV M P t ht (v * (actV M P t ht v)⁻¹) = actV M P t ht v * v⁻¹ := by
      rw [(actV M P t ht).map_mul, (actV M P t ht).map_inv, hinvt]
    rw [e1, (actV M P t ht).map_inv, e3]
    group
  have ha3 : (v * actV M P t ht v) ^ 3 = 1 :=
    exp3_of_fixed hPodd hPM t htt ht hexpt _ ha
  have hb3 : (v * (actV M P t ht v)⁻¹) ^ 3 = 1 :=
    exp3_of_fixed hPodd hPM (t * z) htz2 htz' hexptz _ hb
  have hsq : (v * actV M P t ht v) * (v * (actV M P t ht v)⁻¹) = v ^ 2 := by
    calc (v * actV M P t ht v) * (v * (actV M P t ht v)⁻¹)
        = v * (actV M P t ht v * v) * (actV M P t ht v)⁻¹ := by group
      _ = v * (v * actV M P t ht v) * (actV M P t ht v)⁻¹ := by
          rw [hcomm (actV M P t ht v) v]
      _ = v ^ 2 := by
          rw [pow_two]
          group
  have hab : Commute (v * actV M P t ht v) (v * (actV M P t ht v)⁻¹) := hcomm _ _
  have h6 : v ^ 6 = 1 := by
    have h6' : (v ^ 2) ^ 3 = 1 := by
      rw [← hsq, hab.mul_pow, ha3, hb3, mul_one]
    rw [← pow_mul] at h6'
    simpa using h6'
  have h1 : orderOf v ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have h2 : orderOf v ∣ 81 := by
    rw [← hcard]
    exact orderOf_dvd_natCard v
  have h3 : orderOf v ∣ 3 := by
    have := Nat.dvd_gcd h1 h2
    norm_num at this
    exact this
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem card_le_fix_cube {V : Type*} [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (α : MulAut V) (h3 : ∀ v : V, v ^ 3 = 1) (hα3 : ∀ v, α (α (α v)) = v) :
    Nat.card V ≤ (Nat.card {v // α v = v}) ^ 3 := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  let σ' : Additive V ≃+ Additive V := MulEquiv.toAdditive α
  have h3' : ∀ w : Additive V, (3 : ℕ) • w = 0 := by
    intro w
    have hw : w = Additive.ofMul (Additive.toMul w) := rfl
    rw [hw, ← ofMul_pow, h3, ofMul_one]
  have hσ' : ∀ w : Additive V, σ' (σ' (σ' w)) = w := by
    intro w
    show Additive.ofMul (α (α (α (Additive.toMul w)))) = w
    rw [hα3]
    rfl
  have hJ := jordan_card_le σ' h3' hσ'
  have e1 : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.ofMul.symm
  have e2 : Nat.card {w : Additive V // σ' w = w} = Nat.card {v : V // α v = v} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv Additive.toMul ?_
    intro w
    show Additive.ofMul (α (Additive.toMul w)) = w ↔ α (Additive.toMul w) = Additive.toMul w
    constructor
    · intro h
      exact congrArg Additive.toMul h
    · intro h
      rw [h]
      rfl
  rw [e1, e2] at hJ
  exact hJ

theorem orbit_app [Finite G] {M P : Subgroup G} [(P.subgroupOf M).Normal] {L : Subgroup G}
    (hLn : ∀ k ∈ L, NormH M P k) (φ : L ≃* SL23) (z : G) (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hzc : ∀ g ∈ L, g * z = z * g)
    (hzfix : ∀ v : ↥M ⧸ P.subgroupOf M, actV M P z (hLn z hzL) v = v → v = 1)
    (σ : G) (hσL : σ ∈ L) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    4 * (Nat.card {v : ↥M ⧸ P.subgroupOf M // actV M P σ (hLn σ hσL) v = v} - 1) ≤
      Nat.card (↥M ⧸ P.subgroupOf M) - 1 := by
  classical
  haveI : Fintype L := Fintype.ofFinite L
  haveI : Fintype (↥M ⧸ P.subgroupOf M) := Fintype.ofFinite _
  let ρ : L →* MulAut (↥M ⧸ P.subgroupOf M) := actHomK M P L hLn
  let z' : L := ⟨z, hzL⟩
  let σ' : L := ⟨σ, hσL⟩
  have hinv : ∀ u : L, u * u = 1 → u ≠ 1 → u = z' := by
    intro u hu hu1
    apply Subtype.ext
    apply unique_invol_L L φ z hzL hz1 hzc (u : G) u.2
    · have := congrArg Subtype.val hu
      simpa using this
    · intro e
      exact hu1 (Subtype.ext e)
  have hL24 : Nat.card L = 24 := card_L L φ
  have hT8 : (Finset.univ.filter (fun x : L => x ^ 3 = 1 ∧ x ≠ 1)).card = 8 :=
    card_T8_L L φ
  have hσ3' : σ' ^ 3 = 1 := Subtype.ext (by simpa using hσ3)
  have hσ1' : σ' ≠ 1 := fun e => hσ1 (congrArg Subtype.val e)
  have hconj := conj_L L φ σ' hσ3' hσ1'
  have hzfix' : ∀ v, ρ z' v = v → v = 1 := fun v hv => hzfix v hv
  have key := orbit_bound ρ z' hzfix' hinv hL24 hT8 σ' hconj
  have hfixeq : (Finset.univ.filter (fun v : ↥M ⧸ P.subgroupOf M => ρ σ' v = v)).card =
      Nat.card {v : ↥M ⧸ P.subgroupOf M // actV M P σ (hLn σ hσL) v = v} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [← hfixeq, Nat.card_eq_fintype_card]
  exact key

theorem fix_eq_c (c V m : ℕ) (hc : c = 1 ∨ c = 3 ∨ c = 9) (hV : V = c ^ 2) (hm1 : 1 ≤ m)
    (hdvd : m ∣ V) (hmod : V ≡ m [MOD 3]) (horb : 4 * (m - 1) ≤ V - 1)
    (hjord : c = 9 → V ≤ m ^ 3) : m = c := by
  rcases hc with rfl | rfl | rfl
  · have hV1 : V = 1 := by rw [hV]; norm_num
    subst hV1
    exact Nat.dvd_one.mp hdvd
  · have hV9 : V = 9 := by rw [hV]; norm_num
    subst hV9
    have hm9 : m ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod
    interval_cases m <;> omega
  · have hV81 : V = 81 := by rw [hV]; norm_num
    subst hV81
    have hcube := hjord rfl
    have hm21 : m ≤ 21 := by omega
    interval_cases m <;> revert hcube hdvd <;> norm_num

theorem vertex_count [Finite G] {M : Subgroup G} {τ z σ t : G} {L : Subgroup G} {c : ℕ}
    (hτM : τ ∈ M) (hcentM : ∀ m ∈ M, m * τ = τ * m) (hτ3 : orderOf τ = 3)
    [((Subgroup.zpowers τ).subgroupOf M).Normal]
    (hM : Nat.card M = 3 * c ^ 2) (hc : c = 1 ∨ c = 3 ∨ c = 9)
    (φ : L ≃* SL23) (hLn : ∀ k ∈ L, NormH M (Subgroup.zpowers τ) k)
    (hzz : z * z = 1) (hzL : z ∈ L) (hz1 : z ≠ 1) (hzc : ∀ g ∈ L, g * z = z * g)
    (hzτ : z * τ = τ * z) (hCz : ∀ x ∈ M, z * x * z⁻¹ = x → x ∈ Subgroup.zpowers τ)
    (hLτ : ∀ k ∈ L, k * τ = τ * k)
    (hσL : σ ∈ L) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (htt : t * t = 1) (htz : t * z = z * t) (htz2 : (t * z) * (t * z) = 1)
    (ht : NormH M (Subgroup.zpowers τ) t)
    (hexpt : c = 9 → ∀ x : ↥M, t * (x : G) * t⁻¹ = (x : G) → x ^ 3 = 1)
    (hexptz : c = 9 → ∀ x : ↥M, (t * z) * (x : G) * (t * z)⁻¹ = (x : G) → x ^ 3 = 1) :
    Nat.card {x : ↥M // (x : G) * σ = σ * (x : G)} = 3 * c := by
  have hPM : Subgroup.zpowers τ ≤ M := (Subgroup.zpowers_le).mpr hτM
  have hPodd : Odd (Nat.card (Subgroup.zpowers τ)) := by
    rw [Nat.card_zpowers, hτ3]
    decide
  have hzn := hLn z hzL
  have hσn := hLn σ hσL
  have hinvz : ∀ v, actV M (Subgroup.zpowers τ) z hzn v = v⁻¹ :=
    actV_inv_of hτM hzz hzn hPodd hCz
  have hcomm : ∀ a b : ↥M ⧸ (Subgroup.zpowers τ).subgroupOf M, a * b = b * a :=
    fun a b => commute_of_inverts (actE M (Subgroup.zpowers τ) z hzn) hinvz a b
  have hVcard : Nat.card (↥M ⧸ (Subgroup.zpowers τ).subgroupOf M) = c ^ 2 := by
    have h1 := Subgroup.card_mul_index ((Subgroup.zpowers τ).subgroupOf M)
    have h2 : Nat.card ((Subgroup.zpowers τ).subgroupOf M) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, Nat.card_zpowers, hτ3]
    have h4 : ((Subgroup.zpowers τ).subgroupOf M).index =
        Nat.card (↥M ⧸ (Subgroup.zpowers τ).subgroupOf M) := rfl
    rw [h2, h4, hM] at h1
    omega
  have hσ3V : ∀ v, actV M (Subgroup.zpowers τ) σ hσn (actV M (Subgroup.zpowers τ) σ hσn
      (actV M (Subgroup.zpowers τ) σ hσn v)) = v := by
    intro v
    have e : σ * σ * σ = 1 := by
      rw [← pow_three']
      exact hσ3
    rw [← actV_mul M (Subgroup.zpowers τ) hσn hσn,
      ← actV_mul M (Subgroup.zpowers τ) (hσn.mul' hσn) hσn]
    rw [actV_congr M (Subgroup.zpowers τ) e _ (NormH.one' M _), actV_one]
  have hzfixV : ∀ v, actV M (Subgroup.zpowers τ) z hzn v = v → v = 1 :=
    actV_fixed_free hτM hzz hzn hPodd hCz
  have horb := orbit_app hLn φ z hzL hz1 hzc hzfixV σ hσL hσ3 hσ1
  have hdvd := fix_card_dvd (actE M (Subgroup.zpowers τ) σ hσn)
  have hmod := fix_card_modEq_three (actE M (Subgroup.zpowers τ) σ hσn) hσ3V
  have hcen := card_centralizer_eq_three_mul_fix hτM hcentM hτ3 (hLτ σ hσL) (hzc σ hσL)
    hzτ hzz hzn hσn hCz
  have hm1 : 1 ≤ Nat.card {v : ↥M ⧸ (Subgroup.zpowers τ).subgroupOf M //
      actV M (Subgroup.zpowers τ) σ hσn v = v} := by
    have hpos : 0 < Nat.card {v : ↥M ⧸ (Subgroup.zpowers τ).subgroupOf M //
        actV M (Subgroup.zpowers τ) σ hσn v = v} :=
      Nat.card_pos_iff.mpr ⟨⟨⟨1, map_one _⟩⟩, inferInstance⟩
    exact hpos
  have hjord : c = 9 → Nat.card (↥M ⧸ (Subgroup.zpowers τ).subgroupOf M) ≤
      (Nat.card {v : ↥M ⧸ (Subgroup.zpowers τ).subgroupOf M //
        actV M (Subgroup.zpowers τ) σ hσn v = v}) ^ 3 := by
    intro h9
    have hcard81 : Nat.card (↥M ⧸ (Subgroup.zpowers τ).subgroupOf M) = 81 := by
      rw [hVcard, h9]
      norm_num
    have hexp := exp3_quot hPodd hPM t z htt htz htz2 ht hzn (ht.mul' hzn) hinvz
      (hexpt h9) (hexptz h9) hcomm hcard81
    exact card_le_fix_cube hcomm (actE M (Subgroup.zpowers τ) σ hσn) hexp hσ3V
  have hm := fix_eq_c c _ _ hc hVcard hm1 hdvd hmod horb hjord
  rw [hcen, hm]

end PartD

end CFSG.GH74.QTGen4.Recog.G23.P7.Cor37
