module

public import CFSG.CGT.PushingUpLit.CGT6X.End3Irr
public import CFSG.CGT.PushingUpLit.CGT6.EmbNatBase

public section

open scoped commutatorElement

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6X.End3
  CFSG.CGT.PushingUpLit.BHS6

variable {V : Type} [CommGroup V]

theorem t_fixes_commV [Finite V] {G T Y : Subgroup (MulAut V)}
    (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y) {t : MulAut V} (ht : t ∈ T)
    (ht2 : t * t = 1) : ∀ u ∈ commV Y, t u = u := by
  have hsq := simpleQuot_of_cfg hV cfg
  have hgen := commGen_of_perfect cfg.adm.hperf
  have hcomm : ∀ y ∈ Y, t * y = y * t := fun y hy => cfg_comm_ty cfg ht hy
  have h2 : t ^ 2 = 1 := by rw [pow_two]; exact ht2
  exact ms_three hgen hcomm (ms_two hV hsq hcomm h2)

theorem commV_le_fixV_of_centralizing {S Y : Subgroup (MulAut V)}
    (hc : ∀ s ∈ S, ∀ y ∈ Y, s * y = y * s) (hf : ∀ s ∈ S, ∀ u ∈ commV Y, s u = u) :
    commV S ≤ fixV Y := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨s, hs, v, rfl⟩ y hy
  obtain ⟨a, ha⟩ : ∃ a : V, a = y v * v⁻¹ := ⟨_, rfl⟩
  have hyv : a ∈ commV Y := ha ▸ Subgroup.subset_closure ⟨y, hy, v, rfl⟩
  have e1 : y (s v) = s (y v) := (apply_comm (hc s hs y hy) v).symm
  have e2 : y v = a * v := by rw [ha, inv_mul_cancel_right]
  have e3 : s (y v) = a * s v := by rw [e2, map_mul, hf s hs a hyv]
  have e4 : (y v)⁻¹ = a⁻¹ * v⁻¹ := by rw [e2, mul_inv]
  show y (s v * v⁻¹) = s v * v⁻¹
  rw [map_mul, map_inv, e1, e3, e4, mul_mul_mul_comm, mul_inv_cancel, one_mul]

@[expose] def actTrivMod (F : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ v : V, g v * v⁻¹ ∈ F}
  one_mem' := fun v => by simp
  mul_mem' := by
    intro g₁ g₂ h₁ h₂ v
    have e : (g₁ * g₂) v * v⁻¹ = (g₁ (g₂ v) * (g₂ v)⁻¹) * (g₂ v * v⁻¹) := by
      simp [MulAut.mul_apply]
    rw [e]
    exact mul_mem (h₁ _) (h₂ v)
  inv_mem' := by
    intro g h v
    have e : g⁻¹ v * v⁻¹ = (g (g⁻¹ v) * (g⁻¹ v)⁻¹)⁻¹ := by simp
    rw [e]
    exact inv_mem (h _)

theorem commV_zpowers_fix_of_inv {t x n : MulAut V} (ht2 : t * t = 1)
    (hinv : t * x * t⁻¹ = x⁻¹) (hx : Odd (orderOf x)) (hnx : n * x = x * n)
    (hE : ∀ w ∈ commV (Subgroup.zpowers t), n w = w) :
    ∀ u ∈ commV (Subgroup.zpowers x), n u = u := by
  let F : Subgroup V :=
    { carrier := {v | n v = v}
      one_mem' := map_one n
      mul_mem' := fun {a b} ha hb => by
        show n (a * b) = a * b
        rw [map_mul, show n a = a from ha, show n b = b from hb]
      inv_mem' := fun {a} ha => by
        show n a⁻¹ = a⁻¹
        rw [map_inv, show n a = a from ha] }
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hxx : x * x = (x * t * x⁻¹) * t := by
    have h1 : t * x⁻¹ * t = x := by
      have := congrArg (fun z => z⁻¹) hinv
      simp only [mul_inv_rev, inv_inv, ht'] at this
      rw [mul_assoc]
      exact this
    calc x * x = x * (t * x⁻¹ * t) := by rw [h1]
      _ = (x * t * x⁻¹) * t := by group
  have hxxS : x * x ∈ actTrivMod F := by
    intro v
    obtain ⟨u, hu⟩ : ∃ u : V, u = x⁻¹ (t v) := ⟨_, rfl⟩
    have h1 : (x * x) v = x (t u) := by
      rw [hxx]
      simp only [MulAut.mul_apply]
      rw [hu]
    have h2 : x u = t v := by rw [hu]; exact MulAut.apply_inv_self V x _
    have e : (x * x) v * v⁻¹ = x (t u * u⁻¹) * (t v * v⁻¹) := by
      rw [h1, map_mul, map_inv, h2, mul_assoc, inv_mul_cancel_left]
    rw [e]
    have hE1 : t u * u⁻¹ ∈ commV (Subgroup.zpowers t) :=
      Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, u, rfl⟩
    have hE2 : t v * v⁻¹ ∈ commV (Subgroup.zpowers t) :=
      Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, v, rfl⟩
    refine mul_mem ?_ ?_
    · show n (x (t u * u⁻¹)) = x (t u * u⁻¹)
      rw [apply_comm hnx, hE _ hE1]
    · exact hE _ hE2
  obtain ⟨k, hk⟩ := hx
  have hxk : x = (x * x) ^ (k + 1) := by
    have h1 : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    calc x = x ^ (2 * k + 1) * x := by rw [h1, one_mul]
      _ = x ^ (2 * (k + 1)) := by rw [← pow_succ]; exact congrArg (x ^ ·) (by omega)
      _ = (x * x) ^ (k + 1) := by rw [pow_mul, pow_two]
  have hxS : x ∈ actTrivMod F := by
    rw [hxk]
    exact pow_mem hxxS _
  refine fun u hu => ?_
  have : commV (Subgroup.zpowers x) ≤ F := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨s, hs, v, rfl⟩
    exact Subgroup.zpowers_le.mpr hxS hs v
  exact this hu

section Central

variable [Finite V] {G T Y : Subgroup (MulAut V)}

theorem eq_one_of_central_fix (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y) {c : MulAut V}
    (hcL : ∀ l ∈ CGT6.conjClosure Y G, c * l = l * c) (hcU : ∀ u ∈ commV Y, c u = u) :
    c = 1 := by
  let W : Subgroup V :=
    { carrier := {v | c v = v}
      one_mem' := map_one c
      mul_mem' := fun {a b} ha hb => by
        show c (a * b) = a * b
        rw [map_mul, show c a = a from ha, show c b = b from hb]
      inv_mem' := fun {a} ha => by
        show c a⁻¹ = a⁻¹
        rw [map_inv, show c a = a from ha] }
  have hinv : GInv (CGT6.conjClosure Y G) W := by
    intro l hl a ha
    show c (l a) = l a
    rw [apply_comm (hcL l hl) a, show c a = a from ha]
  have hne : commV Y ≠ ⊥ := fun h => (simpleQuot_of_cfg hV cfg).1 (by rw [h]; simp)
  rcases irreducible_of_cfg hV cfg hinv with h | h
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro u hu
    have : u ∈ W := hcU u hu
    rw [h] at this
    exact this
  · ext v
    have : v ∈ W := by rw [h]; exact Subgroup.mem_top v
    exact this

theorem t_comm_center (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y) {t : MulAut V}
    (ht : t ∈ T) (ht2 : t * t = 1) {z : MulAut V}
    (hz : ∀ l ∈ CGT6.conjClosure Y G, z * l = l * z) : t * z = z * t := by
  have hYL : Y ≤ CGT6.conjClosure Y G := CGT6.le_conjClosure
  have hG : t ∈ G := cfg.adm.hTG ht
  have hzY : ∀ y ∈ Y, z * y = y * z := fun y hy => hz y (hYL hy)
  have hz' : ∀ l ∈ CGT6.conjClosure Y G, z⁻¹ * l = l * z⁻¹ := fun l hl => comm_inv hz l hl
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htU : ∀ u ∈ commV Y, t u = u := t_fixes_commV hV cfg ht ht2
  have hcU : ∀ u ∈ commV Y, (z * t * z⁻¹ * t⁻¹) u = u := by
    intro u hu
    have h1 : z⁻¹ u ∈ commV Y := apply_mem_commV_of_comm (comm_inv hzY) hu
    simp only [MulAut.mul_apply, ht']
    rw [htU u hu, htU _ h1]
    exact MulAut.apply_inv_self V z u
  have hcL : ∀ l ∈ CGT6.conjClosure Y G, (z * t * z⁻¹ * t⁻¹) * l = l * (z * t * z⁻¹ * t⁻¹) := by
    intro l hl
    have hl1 := End3.conj_inv_mem_conjClosure (Y := Y) hG hl
    calc (z * t * z⁻¹ * t⁻¹) * l = z * t * (z⁻¹ * (t⁻¹ * l * t)) * t⁻¹ := by group
      _ = z * t * ((t⁻¹ * l * t) * z⁻¹) * t⁻¹ := by rw [hz' _ hl1]
      _ = z * l * (t * z⁻¹ * t⁻¹) := by group
      _ = l * z * (t * z⁻¹ * t⁻¹) := by rw [hz l hl]
      _ = l * (z * t * z⁻¹ * t⁻¹) := by group
  have h1 := eq_one_of_central_fix hV cfg hcL hcU
  calc t * z = (z * t * z⁻¹ * t⁻¹) * (t * z) := by rw [h1, one_mul]
    _ = z * t := by group

end Central

section Cover

variable {Γ Q : Type*} [Group Γ] [Group Q]

theorem commutatorElement_mul_central_left {a b z : Γ} (hz : z ∈ Subgroup.center Γ) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hz b
  calc ⁅a * z, b⁆ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by simp only [commutatorElement_def]; group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h]
    _ = ⁅a, b⁆ := by simp only [commutatorElement_def]; group

theorem commutatorElement_mul_central_right {a b z : Γ} (hz : z ∈ Subgroup.center Γ) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hz a
  calc ⁅a, b * z⁆ = a * (b * z) * a⁻¹ * z⁻¹ * b⁻¹ := by simp only [commutatorElement_def]; group
    _ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [Subgroup.mem_center_iff.mp hz a⁻¹]
    _ = ⁅a, b⁆ := by simp only [commutatorElement_def]; group

theorem eq_top_of_map_eq_top_central [Group.IsPerfect Γ] (π : Γ →* Q)
    (hker : π.ker ≤ Subgroup.center Γ) {H : Subgroup Γ} (h : H.map π = ⊤) : H = ⊤ := by
  have hdec : ∀ g : Γ, ∃ h₀ ∈ H, ∃ z ∈ Subgroup.center Γ, g = h₀ * z := by
    intro g
    have : π g ∈ H.map π := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨h₀, hh₀, e⟩ := this
    refine ⟨h₀, hh₀, h₀⁻¹ * g, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
  have hcomm : commutator Γ ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hdec g₁
    obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := hdec g₂
    rw [commutatorElement_mul_central_left hz₁, commutatorElement_mul_central_right hz₂]
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha₁ ha₂) (H.inv_mem ha₁)) (H.inv_mem ha₂)
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := Γ)]
  exact hcomm

section Invert

variable {K : Subgroup Γ}

theorem exists_sq_eq_of_odd (hodd : Odd (Nat.card K)) (k : K) : ∃ z : K, z ^ 2 = k := by
  have : Finite K := Nat.finite_of_card_ne_zero (Odd.pos hodd).ne'
  exact (Nat.Coprime.pow_left_bijective (n := 2) (G := K)
    (Nat.coprime_two_right.mpr hodd)).2 k

theorem eq_one_of_sq_eq_one_odd (hodd : Odd (Nat.card K)) {k : K} (hk : k ^ 2 = 1) : k = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (Odd.pos hodd).ne'
  have h1 : orderOf k ∣ Nat.gcd (Nat.card K) 2 :=
    Nat.dvd_gcd (orderOf_dvd_natCard k) (orderOf_dvd_of_pow_eq_one hk)
  rw [show Nat.gcd (Nat.card K) 2 = 1 from Nat.coprime_two_right.mpr hodd, Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact h1

theorem commutator_eq_one_of_inverted (hK : K ≤ Subgroup.center Γ) (hodd : Odd (Nat.card K))
    (τ : MulAut Γ) (hτK : ∀ k ∈ K, τ k = k) {x a : Γ} (hxa : ⁅x, a⁆ ∈ K) (hx : τ x = x⁻¹)
    (ha : τ a = a) : ⁅x, a⁆ = 1 := by
  have hz : ⁅x, a⁆ ∈ Subgroup.center Γ := hK hxa
  have h1 : τ ⁅x, a⁆ = ⁅x⁻¹, a⁆ := by
    simp only [commutatorElement_def, map_mul, map_inv, hx, ha]
  have h2 : ⁅x⁻¹, a⁆ = ⁅x, a⁆⁻¹ := by
    have hc' := Subgroup.mem_center_iff.mp (inv_mem hz)
    have e : ⁅x⁻¹, a⁆ = x⁻¹ * ⁅x, a⁆⁻¹ * x := by simp only [commutatorElement_def]; group
    rw [e, mul_assoc, ← hc' x, inv_mul_cancel_left]
  have h3 : ⁅x, a⁆ = ⁅x, a⁆⁻¹ := by rw [← h2, ← h1, hτK _ hxa]
  have h4 : (⟨⁅x, a⁆, hxa⟩ : K) ^ 2 = 1 := by
    apply Subtype.ext
    simp only [pow_two]
    show ⁅x, a⁆ * ⁅x, a⁆ = 1
    nth_rewrite 1 [h3]
    exact inv_mul_cancel _
  exact congrArg Subtype.val (eq_one_of_sq_eq_one_odd hodd h4)

theorem exists_inverted_lift (hK : K ≤ Subgroup.center Γ) (hodd : Odd (Nat.card K))
    (τ : MulAut Γ) (hτK : ∀ k ∈ K, τ k = k) {c : Γ} (hc : c * τ c ∈ K) :
    ∃ x : Γ, x * c⁻¹ ∈ K ∧ τ x = x⁻¹ := by
  obtain ⟨z₂, hz₂⟩ := exists_sq_eq_of_odd hodd (⟨c * τ c, hc⟩ : K)⁻¹
  have hcen := Subgroup.mem_center_iff.mp (hK z₂.2)
  have hcen' := Subgroup.mem_center_iff.mp (hK (inv_mem z₂.2))
  have hz : (z₂ : Γ) * z₂ = (c * τ c)⁻¹ := by
    have := congrArg Subtype.val hz₂
    simpa [pow_two] using this
  refine ⟨c * z₂, ?_, ?_⟩
  · have : c * (z₂ : Γ) * c⁻¹ = z₂ := by rw [hcen c]; group
    rw [this]
    exact z₂.2
  · have h1 : τ c = c⁻¹ * (c * τ c) := by group
    have h2 : c * τ c = (z₂ : Γ)⁻¹ * (z₂ : Γ)⁻¹ := by
      have := congrArg (fun g => g⁻¹) hz
      simpa [mul_inv_rev] using this.symm
    rw [map_mul, hτK _ z₂.2, h1, h2]
    calc c⁻¹ * ((z₂ : Γ)⁻¹ * (z₂ : Γ)⁻¹) * z₂ = c⁻¹ * (z₂ : Γ)⁻¹ := by group
      _ = (z₂ : Γ)⁻¹ * c⁻¹ := by rw [← hcen' c⁻¹]
      _ = (c * z₂)⁻¹ := by group

end Invert

end Cover

@[expose] def a5s1 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def a5s2 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap (2 : Fin 5) 3 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def a5w0 : G6.PermMod 5 :=
  Multiplicative.ofAdd (fun i : Fin 5 => if i = 0 ∨ i = 1 then 1 else 0)

theorem a5w0_mem : a5w0 ∈ G6.coreMod 5 := by
  rw [G6.mem_coreMod]
  decide

theorem a5w0_ne_one : a5w0 ≠ 1 := by
  intro h
  have := congrArg (fun z : G6.PermMod 5 => Multiplicative.toAdd z 0) h
  simp [a5w0] at this

theorem fix_a5_pair (f : Fin 5 → ZMod 2) (hf : ∑ i, f i = 0)
    (h1 : ∀ i, f ((Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 5))⁻¹ i) = f i)
    (h2 : ∀ i, f ((Equiv.swap (2 : Fin 5) 3 * Equiv.swap 3 4 : Equiv.Perm (Fin 5))⁻¹ i) = f i) :
    f = 0 ∨ f = fun i => if i = 0 ∨ i = 1 then 1 else 0 := by
  revert f
  decide

theorem fix_a5_core (q : ↥(G6.coreMod 5)) (h1 : altAct 5 a5s1 q = q) (h2 : altAct 5 a5s2 q = q) :
    q = 1 ∨ (q : G6.PermMod 5) = a5w0 := by
  have hf := G6.mem_coreMod.mp q.2
  have e1 : ∀ i, Multiplicative.toAdd (q : G6.PermMod 5) ((a5s1 : Equiv.Perm (Fin 5))⁻¹ i) =
      Multiplicative.toAdd (q : G6.PermMod 5) i := fun i => by
    have := congrArg (fun z : ↥(G6.coreMod 5) => Multiplicative.toAdd (z : G6.PermMod 5) i) h1
    exact this
  have e2 : ∀ i, Multiplicative.toAdd (q : G6.PermMod 5) ((a5s2 : Equiv.Perm (Fin 5))⁻¹ i) =
      Multiplicative.toAdd (q : G6.PermMod 5) i := fun i => by
    have := congrArg (fun z : ↥(G6.coreMod 5) => Multiplicative.toAdd (z : G6.PermMod 5) i) h2
    exact this
  rcases fix_a5_pair _ hf e1 e2 with h | h
  · left
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact h
  · right
    apply Multiplicative.toAdd.injective
    exact h

theorem altAct_a5s1_w0 : altAct 5 a5s1 ⟨a5w0, a5w0_mem⟩ = ⟨a5w0, a5w0_mem⟩ := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  show (fun i : Fin 5 => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0)
      ((Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 5))⁻¹ i) =
    (fun i : Fin 5 => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) i
  revert i
  decide

theorem altAct_a5s2_w0 : altAct 5 a5s2 ⟨a5w0, a5w0_mem⟩ = ⟨a5w0, a5w0_mem⟩ := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  show (fun i : Fin 5 => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0)
      ((Equiv.swap (2 : Fin 5) 3 * Equiv.swap 3 4 : Equiv.Perm (Fin 5))⁻¹ i) =
    (fun i : Fin 5 => if i = 0 ∨ i = 1 then (1 : ZMod 2) else 0) i
  revert i
  decide

section Schur

variable {V : Type} [CommGroup V] {Y : Subgroup (MulAut V)}

theorem trivQ_of_typeA (hsq : SimpleQuot Y)
    (hnat : IsNatSectionBy (altAct 5) Y (commV Y) (commV Y ⊓ fixV Y)) {g : MulAut V}
    (hg : ∀ y ∈ Y, g * y = y * g) : TrivQ Y g := by
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := hnat
  have hgU : ∀ u ∈ commV Y, g u ∈ commV Y := fun u hu => apply_mem_commV_of_comm hg hu
  have hgU' : ∀ u ∈ commV Y, g⁻¹ u ∈ commV Y := fun u hu =>
    apply_mem_commV_of_comm (comm_inv hg) hu
  let ψ : MulAut ↥(commV Y) := restrictAut g (commV Y) hgU hgU'
  have hψ : ∀ u : ↥(commV Y), ((ψ u : ↥(commV Y)) : V) = g u := fun u => rfl
  have hker : ∀ u : ↥(commV Y), u ∈ β.ker → ψ u ∈ β.ker := by
    intro u hu
    rw [hβk, Subgroup.mem_subgroupOf] at hu ⊢
    exact ⟨hgU _ u.2, apply_mem_fixV_of_comm hg hu.2⟩
  have hkerinv : ∀ u : ↥(commV Y), ψ u ∈ β.ker → u ∈ β.ker := by
    intro u hu
    rw [hβk, Subgroup.mem_subgroupOf] at hu ⊢
    refine ⟨u.2, ?_⟩
    have := apply_mem_fixV_of_comm' hg (show g (u : V) ∈ fixV Y from hu.2)
    rwa [MulAut.inv_apply_self] at this
  have hβe' : ∀ (h : ↥Y) (p : ↥(commV Y)), β (resHom Y h p) = altAct 5 (θ h) (β p) :=
    fun h p => hβe h p (hinv h h.2 p p.2)
  have hcomm : ∀ (h : ↥Y) (p : ↥(commV Y)), ψ (resHom Y h p) = resHom Y h (ψ p) := by
    intro h p
    exact Subtype.ext (apply_comm (hg h h.2) p)
  let w₀ : ↥(G6.coreMod 5) := ⟨a5w0, a5w0_mem⟩
  obtain ⟨u₀, hu₀⟩ := hβs w₀
  have hstab : ∀ σ : alternatingGroup (Fin 5), altAct 5 σ w₀ = w₀ →
      altAct 5 σ (β (ψ u₀)) = β (ψ u₀) := by
    intro σ hσ
    have h1 : β (resHom Y (θ.symm σ) u₀) = β u₀ := by
      rw [hβe', MulEquiv.apply_symm_apply, hu₀, hσ]
    have hc : resHom Y (θ.symm σ) u₀ * u₀⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1]
      exact mul_inv_cancel _
    have e : resHom Y (θ.symm σ) u₀ = u₀ * (resHom Y (θ.symm σ) u₀ * u₀⁻¹) := by
      rw [mul_comm, inv_mul_cancel_right]
    calc altAct 5 σ (β (ψ u₀)) = altAct 5 (θ (θ.symm σ)) (β (ψ u₀)) := by
          rw [MulEquiv.apply_symm_apply]
      _ = β (resHom Y (θ.symm σ) (ψ u₀)) := (hβe' _ _).symm
      _ = β (ψ (resHom Y (θ.symm σ) u₀)) := by rw [hcomm]
      _ = β (ψ (u₀ * (resHom Y (θ.symm σ) u₀ * u₀⁻¹))) := by rw [← e]
      _ = β (ψ u₀) := by
        rw [map_mul, map_mul]
        have := hker _ hc
        rw [MonoidHom.mem_ker.mp this, mul_one]
  have hq := fix_a5_core (β (ψ u₀)) (hstab a5s1 altAct_a5s1_w0) (hstab a5s2 altAct_a5s2_w0)
  have hu₀W : ¬ (u₀ : V) ∈ commV Y ⊓ fixV Y := by
    intro hmem
    have : u₀ ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact hmem
    rw [MonoidHom.mem_ker, hu₀] at this
    exact a5w0_ne_one (congrArg Subtype.val this)
  have hgu₀ : g (u₀ : V) * (u₀ : V)⁻¹ ∈ fixV Y := by
    rcases hq with hq | hq
    · exfalso
      have h1 : ψ u₀ ∈ β.ker := hq
      have h2 := hkerinv u₀ h1
      apply hu₀W
      rw [hβk, Subgroup.mem_subgroupOf] at h2
      exact h2
    · have h1 : β (ψ u₀) = β u₀ := by rw [hu₀]; exact Subtype.ext hq
      have h2 : ψ u₀ * u₀⁻¹ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1]
        exact mul_inv_cancel _
      rw [hβk, Subgroup.mem_subgroupOf] at h2
      exact h2.2
  set S : Subgroup V := commV Y ⊓ (fixV Y).comap (dlt g) with hS
  have hSinv : ∀ y ∈ Y, ∀ n ∈ S, y n ∈ S := by
    intro y hy n hn
    refine ⟨commV_invariant hy hn.1, ?_⟩
    have h1 : dlt g (y n) = y (dlt g n) := by
      simp only [dlt_apply, map_mul, map_inv, apply_comm (hg y hy)]
    have h2 : dlt g n ∈ fixV Y := hn.2
    show dlt g (y n) ∈ fixV Y
    rw [h1, h2 y hy]
    exact h2
  have hWS : commV Y ⊓ fixV Y ≤ S := by
    intro w hw
    refine ⟨hw.1, ?_⟩
    show dlt g w ∈ fixV Y
    rw [dlt_apply]
    exact mul_mem (apply_mem_fixV_of_comm hg hw.2) (inv_mem hw.2)
  have hSU : S ≤ commV Y := inf_le_left
  have hu₀S : (u₀ : V) ∈ S := ⟨u₀.2, hgu₀⟩
  rcases hsq.2 S hSinv hWS hSU with h | h
  · exact absurd (h ▸ hu₀S) hu₀W
  · intro u hu
    have : u ∈ S := by rw [h]; exact hu
    exact this.2

end Schur

section Center

variable [Finite V] {G T Y : Subgroup (MulAut V)}

theorem center_trivial_of_typeA (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y)
    (hnat : IsNatSectionBy (altAct 5) Y (commV Y) (commV Y ⊓ fixV Y)) {z : MulAut V}
    (hz : ∀ l ∈ CGT6.conjClosure Y G, z * l = l * z) : z = 1 := by
  have hYL : Y ≤ CGT6.conjClosure Y G := CGT6.le_conjClosure
  have hzY : ∀ y ∈ Y, z * y = y * z := fun y hy => hz y (hYL hy)
  have h := trivQ_of_typeA (simpleQuot_of_cfg hV cfg) hnat hzY
  exact eq_one_of_central_fix hV cfg hz (ms_three (commGen_of_perfect cfg.adm.hperf) hzY h)

theorem exists_involution_of_T (cfg : EndCfg4 G T Y) : ∃ t ∈ T, t * t = 1 ∧ t ≠ 1 := by
  have hT2 := cfg.adm.hT2
  have hT1 := cfg.adm.hT1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  have hn1 : n ≠ 0 := by
    rintro rfl
    apply hT1
    rw [Subgroup.eq_bot_iff_card, hn]
    rfl
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2
    (by rw [hn]; exact dvd_pow_self 2 hn1)
  refine ⟨(g : MulAut V), g.2, ?_, ?_⟩
  · have h := pow_orderOf_eq_one g
    rw [hg] at h
    have := congrArg Subtype.val h
    simpa [pow_two] using this
  · intro h1
    have : g = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hg
    omega

end Center

end CFSG.CGT.PushingUpLit.CGT6X.End4
