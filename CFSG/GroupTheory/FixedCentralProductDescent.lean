module

public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {S : Type*} [Group S] {ι : Type*} {H : ι → Subgroup S}

theorem coe_pi_apply_congr (s : ∀ i, H i) {a b : ι} (h : a = b) : (s a : S) = s b := by
  subst h
  rfl

theorem apply_mem_of_map_eq {F : MulAut S} {π : Equiv.Perm ι}
    (hF : ∀ i, (H i).map F.toMonoidHom = H (π i)) {i : ι} {x : S} (hx : x ∈ H i) :
    F x ∈ H (π i) := by
  rw [← hF i]
  exact Subgroup.mem_map_of_mem _ hx

theorem symm_apply_mem_of_map_eq {F : MulAut S} {π : Equiv.Perm ι}
    (hF : ∀ i, (H i).map F.toMonoidHom = H (π i)) {i : ι} {x : S} (hx : x ∈ H (π i)) :
    F.symm x ∈ H i := by
  rw [← hF i, Subgroup.mem_map_equiv] at hx
  exact hx

variable (H) in
@[expose] def centralProductAut (F : MulAut S) (π : Equiv.Perm ι)
    (hF : ∀ i, (H i).map F.toMonoidHom = H (π i)) : MulAut (∀ i, H i) where
  toFun s j := ⟨F (s (π.symm j)), by
    have h := apply_mem_of_map_eq hF (s (π.symm j)).2
    rwa [Equiv.apply_symm_apply] at h⟩
  invFun t i := ⟨F.symm (t (π i)), symm_apply_mem_of_map_eq hF (t (π i)).2⟩
  left_inv s := by
    funext i
    apply Subtype.ext
    change F.symm (F (s (π.symm (π i)) : S)) = (s i : S)
    rw [MulEquiv.symm_apply_apply]
    exact coe_pi_apply_congr s (π.symm_apply_apply i)
  right_inv t := by
    funext j
    apply Subtype.ext
    change F (F.symm (t (π (π.symm j)) : S)) = (t j : S)
    rw [MulEquiv.apply_symm_apply]
    exact coe_pi_apply_congr t (π.apply_symm_apply j)
  map_mul' s t := by
    funext j
    apply Subtype.ext
    change F ((s (π.symm j) : S) * t (π.symm j)) = F (s (π.symm j)) * F (t (π.symm j))
    rw [map_mul]

variable {F : MulAut S} {π : Equiv.Perm ι} {hF : ∀ i, (H i).map F.toMonoidHom = H (π i)}

theorem centralProductAut_apply (s : ∀ i, H i) (j : ι) :
    (centralProductAut H F π hF s j : S) = F (s (π.symm j)) :=
  rfl

theorem centralProductAut_apply_perm (s : ∀ i, H i) (i : ι) :
    (centralProductAut H F π hF s (π i) : S) = F (s i) := by
  rw [centralProductAut_apply]
  exact congrArg F (coe_pi_apply_congr s (π.symm_apply_apply i))

variable [Fintype ι] (hcomm : Pairwise fun i j : ι => ∀ x y : S, x ∈ H i → y ∈ H j → Commute x y)

include hcomm in
theorem noncommPiCoprod_centralProductAut (s : ∀ i, H i) :
    Subgroup.noncommPiCoprod hcomm (centralProductAut H F π hF s) =
      F (Subgroup.noncommPiCoprod hcomm s) := by
  classical
  have h : (Subgroup.noncommPiCoprod hcomm).comp (centralProductAut H F π hF).toMonoidHom =
      F.toMonoidHom.comp (Subgroup.noncommPiCoprod hcomm) := by
    refine MonoidHom.pi_ext fun i x => ?_
    have e : centralProductAut H F π hF (Pi.mulSingle i x) =
        Pi.mulSingle (π i) ⟨F x, apply_mem_of_map_eq hF x.2⟩ := by
      funext j
      apply Subtype.ext
      rw [centralProductAut_apply]
      by_cases hj : j = π i
      · subst hj
        rw [Pi.mulSingle_eq_same, coe_pi_apply_congr _ (π.symm_apply_apply i),
          Pi.mulSingle_eq_same]
      · have hj' : π.symm j ≠ i := fun h => hj (by rw [← h, Equiv.apply_symm_apply])
        rw [Pi.mulSingle_eq_of_ne hj', Pi.mulSingle_eq_of_ne hj]
        simp
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, e,
      Subgroup.noncommPiCoprod_mulSingle]
  exact DFunLike.congr_fun h s

include hcomm in
theorem commute_of_noncommPiCoprod_eq_one {z : ∀ i, H i}
    (hz : Subgroup.noncommPiCoprod hcomm z = 1) (j : ι) {y : S} (hy : y ∈ H j) :
    Commute (z j : S) y := by
  classical
  set w : ∀ i, H i := z * (Pi.mulSingle j (z j))⁻¹ with hw
  have hwy : Commute y (Subgroup.noncommPiCoprod hcomm w) := by
    rw [Subgroup.noncommPiCoprod_apply]
    refine Finset.noncommProd_commute _ _ _ _ fun i _ => ?_
    by_cases hij : i = j
    · subst hij
      have h1 : w i = 1 := by simp [hw]
      rw [h1, OneMemClass.coe_one]
      exact Commute.one_right y
    · exact (hcomm hij _ _ (w i).2 hy).symm
  have hzw : z = w * Pi.mulSingle j (z j) := by simp [hw]
  have h1 : Subgroup.noncommPiCoprod hcomm w * (z j : S) = 1 := by
    rw [← Subgroup.noncommPiCoprod_mulSingle (hcomm := hcomm) j (z j), ← map_mul, ← hzw, hz]
  rw [eq_inv_of_mul_eq_one_right h1]
  exact hwy.symm.inv_left

include hcomm in
theorem mul_comm_of_noncommPiCoprod_eq_one {z : ∀ i, H i}
    (hz : Subgroup.noncommPiCoprod hcomm z = 1) (p : ∀ i, H i) : z * p = p * z := by
  funext j
  apply Subtype.ext
  exact (commute_of_noncommPiCoprod_eq_one hcomm hz j (p j).2).eq

theorem commutatorElement_central_mul_left {G : Type*} [Group G] {z : G}
    (hz : ∀ p, z * p = p * z) (a b : G) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * b * (z * a)⁻¹ * b⁻¹ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * z * z⁻¹ * b⁻¹ := by rw [hz]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_central_right {G : Type*} [Group G] {z : G}
    (hz : ∀ p, z * p = p * z) (a b : G) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (z * b) * a⁻¹ * (z * b)⁻¹ = a * z * b * a⁻¹ * b⁻¹ * z⁻¹ := by group
    _ = z * a * b * a⁻¹ * b⁻¹ * z⁻¹ := by rw [← hz a]
    _ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ * z * z⁻¹ := by rw [hz]
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Fintype ι] in
theorem map_pow_eq_of_map_eq (hF : ∀ i, (H i).map F.toMonoidHom = H (π i)) (n : ℕ) (i : ι) :
    (H i).map (F ^ n).toMonoidHom = H ((π ^ n) i) := by
  induction n generalizing i with
  | zero =>
    ext x
    simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, ← hF, ← ih, Subgroup.map_map]
    rfl

omit [Fintype ι] in
theorem perm_pow_minimalPeriod_apply (π : Equiv.Perm ι) (i : ι) :
    (π ^ Function.minimalPeriod π i) i = i := by
  rw [← Equiv.Perm.iterate_eq_pow]
  exact Function.isPeriodicPt_minimalPeriod π i

theorem mulAut_pow_apply_eq_self {g : MulAut S} {x : S} (h : g x = x) (q : ℕ) :
    (g ^ q) x = x := by
  induction q with
  | zero => rfl
  | succ q ih => rw [pow_succ, MulAut.mul_apply, h, ih]

omit [Fintype ι] in
theorem coe_apply_perm_pow_of_fixed {t : ∀ i, H i} (ht : centralProductAut H F π hF t = t)
    (n : ℕ) (i : ι) : (t ((π ^ n) i) : S) = (F ^ n) (t i) := by
  have hstep : ∀ i, (t (π i) : S) = F (t i) := fun i => by
    have h := congrArg (fun s : ∀ i, H i => (s (π i) : S)) ht
    simp only [centralProductAut_apply_perm] at h
    exact h.symm
  induction n generalizing i with
  | zero => exact coe_pi_apply_congr t (by rw [pow_zero, Equiv.Perm.one_apply])
  | succ n ih =>
    rw [coe_pi_apply_congr t (by rw [pow_succ', Equiv.Perm.mul_apply]), hstep, ih, pow_succ',
      MulAut.mul_apply]

omit [Fintype ι] in
theorem pow_apply_eq_of_perm_pow_apply_eq {c : ι} {x : S}
    (hx : (F ^ Function.minimalPeriod π c) x = x) {a b : ℕ} (h : (π ^ a) c = (π ^ b) c) :
    (F ^ a) x = (F ^ b) x := by
  have key : ∀ a b : ℕ, a ≤ b → (π ^ a) c = (π ^ b) c → (F ^ a) x = (F ^ b) x := by
    intro a b hab h
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
    have hm : (π ^ m) c = c := by
      rw [pow_add, Equiv.Perm.mul_apply] at h
      exact ((π ^ a).injective h).symm
    have hd : Function.minimalPeriod π c ∣ m := by
      apply Function.IsPeriodicPt.minimalPeriod_dvd
      change π^[m] c = c
      rw [Equiv.Perm.iterate_eq_pow]
      exact hm
    obtain ⟨q, rfl⟩ := hd
    rw [pow_add, MulAut.mul_apply, pow_mul, mulAut_pow_apply_eq_self hx q]
  rcases le_total a b with hab | hab
  · exact key a b hab h
  · exact (key b a hab h.symm).symm

theorem fixed_central_product_abelian_descent (H : ι → Subgroup S)
    (hcomm : Pairwise fun i j : ι => ∀ x y : S, x ∈ H i → y ∈ H j → Commute x y)
    (hgen : ⨆ i, H i = ⊤) (F : MulAut S) (π : Equiv.Perm ι)
    (hF : ∀ i, (H i).map F.toMonoidHom = H (π i)) :
    (∀ (s : ∀ i, H i) (i : ι), (centralProductAut H F π hF s (π i) : S) = F (s i)) ∧
    ((centralProductAut H F π hF).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (Subgroup.noncommPiCoprod hcomm) ≤ F.toMonoidHom.eqLocus (MonoidHom.id S) ∧
    ((((centralProductAut H F π hF).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (Subgroup.noncommPiCoprod hcomm)).subgroupOf
          (F.toMonoidHom.eqLocus (MonoidHom.id S))).Normal ∧
    ⁅F.toMonoidHom.eqLocus (MonoidHom.id S), F.toMonoidHom.eqLocus (MonoidHom.id S)⁆ ≤
      ((centralProductAut H F π hF).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (Subgroup.noncommPiCoprod hcomm) ∧
    (∀ [((((centralProductAut H F π hF).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (Subgroup.noncommPiCoprod hcomm)).subgroupOf
          (F.toMonoidHom.eqLocus (MonoidHom.id S))).Normal],
      IsMulCommutative (F.toMonoidHom.eqLocus (MonoidHom.id S) ⧸
        (((centralProductAut H F π hF).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (Subgroup.noncommPiCoprod hcomm)).subgroupOf
            (F.toMonoidHom.eqLocus (MonoidHom.id S)))) ∧
    (∀ i, (H i).map (F ^ Function.minimalPeriod π i).toMonoidHom = H i) ∧
    ∀ C : Set ι, (∀ j, ∃! c, c ∈ C ∧ π.SameCycle c j) →
      ∃ e : (centralProductAut H F π hF).toMonoidHom.eqLocus (MonoidHom.id _) ≃*
          ((c : C) → (H c ⊓ (F ^ Function.minimalPeriod π c).toMonoidHom.eqLocus
            (MonoidHom.id S) : Subgroup S)),
        ∀ t (c : C), (e t c : S) = ((t : ∀ i, H i) c : S) := by
  classical
  set μ := Subgroup.noncommPiCoprod hcomm with hμ
  set Ft := centralProductAut H F π hF with hFt
  set R := F.toMonoidHom.eqLocus (MonoidHom.id S) with hR
  set PF := Ft.toMonoidHom.eqLocus (MonoidHom.id (∀ i, H i)) with hPF
  set U := PF.map μ with hU
  have hμF : ∀ s, μ (Ft s) = F (μ s) := noncommPiCoprod_centralProductAut hcomm
  have hsurj : ∀ r : S, ∃ l, μ l = r := by
    intro r
    have hr : r ∈ μ.range := by
      rw [hμ, Subgroup.noncommPiCoprod_range, hgen]
      trivial
    exact hr
  have hcorr : ∀ r ∈ R, ∀ l, μ l = r → ∀ p, Ft l * l⁻¹ * p = p * (Ft l * l⁻¹) := by
    intro r hr l hl p
    have hr' : F r = r := hr
    refine mul_comm_of_noncommPiCoprod_eq_one hcomm ?_ p
    rw [map_mul, map_inv, hμF, hl, hr', mul_inv_cancel]
  have hUR : U ≤ R := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : Ft t = t := ht
    change F (μ t) = μ t
    rw [← hμF, ht']
  have hnorm : (U.subgroupOf R).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨t, ht, htn⟩ := hn
    have ht' : Ft t = t := ht
    obtain ⟨l, hl⟩ := hsurj g
    have hz := hcorr g g.2 l hl
    refine ⟨l * t * l⁻¹, ?_, ?_⟩
    · change Ft (l * t * l⁻¹) = l * t * l⁻¹
      calc Ft (l * t * l⁻¹) = Ft l * t * (Ft l)⁻¹ := by rw [map_mul, map_mul, map_inv, ht']
        _ = (Ft l * l⁻¹) * (l * t * l⁻¹) * (Ft l * l⁻¹)⁻¹ := by group
        _ = (l * t * l⁻¹) * (Ft l * l⁻¹) * (Ft l * l⁻¹)⁻¹ := by rw [hz]
        _ = l * t * l⁻¹ := by group
    · rw [map_mul, map_mul, map_inv, hl, htn]
      rfl⟩
  have hder : ⁅R, R⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro r₁ hr₁ r₂ hr₂
    obtain ⟨l₁, hl₁⟩ := hsurj r₁
    obtain ⟨l₂, hl₂⟩ := hsurj r₂
    have hz₁ := hcorr r₁ hr₁ l₁ hl₁
    have hz₂ := hcorr r₂ hr₂ l₂ hl₂
    refine ⟨⁅l₁, l₂⁆, ?_, by rw [map_commutatorElement, hl₁, hl₂]⟩
    change Ft ⁅l₁, l₂⁆ = ⁅l₁, l₂⁆
    have e₁ : Ft l₁ = (Ft l₁ * l₁⁻¹) * l₁ := by group
    have e₂ : Ft l₂ = (Ft l₂ * l₂⁻¹) * l₂ := by group
    rw [map_commutatorElement, e₁, e₂, commutatorElement_central_mul_left hz₁,
      commutatorElement_mul_central_right hz₂]
  refine ⟨fun s i => centralProductAut_apply_perm s i, hUR, hnorm, hder, ?_,
    fun i => by rw [map_pow_eq_of_map_eq hF, perm_pow_minimalPeriod_apply], ?_⟩
  ·
    intro _
    refine ⟨⟨fun a b => ?_⟩⟩
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : ((x * y)⁻¹ * (y * x) : R) = ⁅y⁻¹, x⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact hder (Subgroup.commutator_mem_commutator (inv_mem y.2) (inv_mem x.2))
  ·
    intro C hC
    have hrep : ∀ j, ∃ c : C, ∃ n : ℕ, (π ^ n) c = j := fun j => by
      obtain ⟨c, ⟨hcC, hcj⟩, -⟩ := hC j
      obtain ⟨n, hn⟩ := hcj.exists_nat_pow_eq
      exact ⟨⟨c, hcC⟩, n, hn⟩
    choose rc rn hrn using hrep
    have hsame : ∀ j, π.SameCycle (rc j) j := fun j => ⟨(rn j : ℤ), by
      rw [zpow_natCast]
      exact hrn j⟩
    have hrc_self : ∀ c : C, rc c = c := by
      intro c
      obtain ⟨d, -, huniq⟩ := hC c
      exact Subtype.ext ((huniq _ ⟨(rc c).2, hsame c⟩).trans
        (huniq _ ⟨c.2, Equiv.Perm.SameCycle.refl _ _⟩).symm)
    have hrc_perm : ∀ j, rc (π j) = rc j := by
      intro j
      obtain ⟨d, -, huniq⟩ := hC (π j)
      exact Subtype.ext ((huniq _ ⟨(rc (π j)).2, hsame (π j)⟩).trans
        (huniq _ ⟨(rc j).2, Equiv.Perm.sameCycle_apply_right.2 (hsame j)⟩).symm)
    let proj : PF →* ((c : C) → (H c ⊓ (F ^ Function.minimalPeriod π c).toMonoidHom.eqLocus
        (MonoidHom.id S) : Subgroup S)) :=
      { toFun := fun t c => ⟨((t : ∀ i, H i) c : S), ((t : ∀ i, H i) c).2, by
          have h := coe_apply_perm_pow_of_fixed (hF := hF) (t := (t : ∀ i, H i)) t.2
            (Function.minimalPeriod π c) c
          rw [coe_pi_apply_congr _ (perm_pow_minimalPeriod_apply π c)] at h
          exact h.symm⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hproj : ∀ t (c : C), (proj t c : S) = ((t : ∀ i, H i) c : S) := fun _ _ => rfl
    have hinj : Function.Injective proj := by
      intro s t hst
      apply Subtype.ext
      funext j
      apply Subtype.ext
      have hs := coe_apply_perm_pow_of_fixed (hF := hF) (t := (s : ∀ i, H i)) s.2 (rn j) (rc j)
      have ht := coe_apply_perm_pow_of_fixed (hF := hF) (t := (t : ∀ i, H i)) t.2 (rn j) (rc j)
      rw [coe_pi_apply_congr _ (hrn j)] at hs ht
      rw [hs, ht]
      congr 1
      have := congrArg (fun x => (x (rc j) : S)) hst
      simpa only [hproj] using this
    have hsurj' : Function.Surjective proj := by
      intro x
      have hxc : ∀ {c c' : C}, c = c' → (x c : S) = x c' := by
        rintro _ _ rfl
        rfl
      have hmem : ∀ j, (F ^ rn j) (x (rc j) : S) ∈ H j := by
        intro j
        have h := Subgroup.mem_map_of_mem (F ^ rn j).toMonoidHom (x (rc j)).2.1
        rwa [map_pow_eq_of_map_eq hF, hrn] at h
      have hfix : ∀ c : C, (F ^ Function.minimalPeriod π c) (x c : S) = x c := fun c =>
        (x c).2.2
      let t : ∀ i, H i := fun j => ⟨(F ^ rn j) (x (rc j) : S), hmem j⟩
      have htF : Ft t = t := by
        funext j
        apply Subtype.ext
        rw [hFt, centralProductAut_apply]
        change F ((F ^ rn (π.symm j)) (x (rc (π.symm j)) : S)) = (F ^ rn j) (x (rc j) : S)
        have hj : rc j = rc (π.symm j) := by
          rw [← hrc_perm (π.symm j), Equiv.apply_symm_apply]
        rw [hxc hj, ← MulAut.mul_apply, ← pow_succ']
        refine pow_apply_eq_of_perm_pow_apply_eq (hfix _) ?_
        rw [pow_succ', Equiv.Perm.mul_apply, hrn, Equiv.apply_symm_apply, ← hj, hrn]
      refine ⟨⟨t, htF⟩, funext fun c => Subtype.ext ?_⟩
      rw [hproj]
      change (F ^ rn c) (x (rc c) : S) = x c
      rw [hxc (hrc_self c)]
      have hc : (π ^ rn c) c = (π ^ 0) c := by
        have h := hrn c
        rw [hrc_self c] at h
        rw [pow_zero, Equiv.Perm.one_apply]
        exact h
      calc (F ^ rn c) (x c : S) = (F ^ 0) (x c : S) :=
            pow_apply_eq_of_perm_pow_apply_eq (hfix c) hc
        _ = x c := rfl
    exact ⟨MulEquiv.ofBijective proj ⟨hinj, hsurj'⟩, fun t c => hproj t c⟩

end CFSG.GroupTheory
