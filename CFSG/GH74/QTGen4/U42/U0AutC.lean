module

public import CFSG.GH74.QTGen4.U42.U0Aut
public import CFSG.GH74.QTGen4.U42.U0AutB

public section

namespace CFSG.GH74.QTGen4.U42.U0AutC

open CFSG.GH74.QTGen4.U42 CFSG.GH74.QTGen4.U42.U0Aut CFSG.GH74.QTGen4.U42.U0AutB

theorem xorFact : ∀ a, a < 16 → ∀ b, b < 16 → a ^^^ b = 0 → a = b := by
  decide +kernel

theorem xor3_fact : ∀ a, a < 16 → ∀ b, b < 16 → (a ^^^ b) ^^^ a = b := by
  decide +kernel

theorem ap_one_fact : ∀ u, u < 16 → ap one u = u := by
  decide +kernel

theorem cU_inv (x : U0) : cU x⁻¹ = cU x := by
  have h0 : cU (x * x⁻¹) = 0 := by
    rw [mul_inv_cancel, cU_one]
  rw [cU_mul] at h0
  exact (xorFact _ (cU_lt16 x) _ (cU_lt16 x⁻¹) h0).symm

theorem cU_zpow_zc (k : ℤ) : cU (zc ^ k) = 0 := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero, cU_one]
  | succ n ih =>
    rw [zpow_add_one, cU_mul, ih, cU_zc]
    decide
  | pred n ih =>
    rw [zpow_sub_one, cU_mul, cU_inv, ih, cU_zc]
    decide

theorem zc_central : zc ∈ Subgroup.center U0 := by
  rw [center_U0]
  exact Subgroup.mem_zpowers zc

theorem zc_comm (g : U0) : g * zc = zc * g :=
  Subgroup.mem_center_iff.1 zc_central g

theorem cU_central (x : U0) (hx : x ∈ Subgroup.center U0) : cU x = 0 := by
  rw [center_U0] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact cU_zpow_zc k

theorem alpha_zc_central (α : MulAut U0) : α zc ∈ Subgroup.center U0 := by
  rw [Subgroup.mem_center_iff]
  intro y
  have h := congrArg α (zc_comm (α.symm y))
  simp only [map_mul, MulEquiv.apply_symm_apply] at h
  exact h

theorem cU_alpha_zc (α : MulAut U0) : cU (α zc) = 0 :=
  cU_central _ (alpha_zc_central α)

instance instDecEqMcC : DecidableEq Mc := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    ⟨fun h => by
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only at h
      rw [h.1, h.2], fun h => by rw [h]; exact ⟨rfl, rfl⟩⟩

theorem zc_ne_one : zc ≠ 1 := by
  decide +kernel

theorem alpha_zc (α : MulAut U0) : α zc = zc := by
  rcases (cU_eq_zero_iff _).1 (cU_alpha_zc α) with h | h
  · have h1 : zc = 1 := α.injective (by rw [map_one]; exact h)
    exact absurd h1 zc_ne_one
  · exact h

def tupF (α : MulAut U0) : T4 :=
  (cU (α E1), cU (α E2), cU (α E4), cU (α E8))

theorem cU_alpha_one (α : MulAut U0) : cU (α 1) = 0 := by
  rw [map_one]
  exact cU_one

theorem cU_alpha_mul (α : MulAut U0) (x y : U0) :
    cU (α (x * y)) = Nat.xor (cU (α x)) (cU (α y)) := by
  rw [map_mul, cU_mul]

theorem cU_alpha_ite {b : Prop} [Decidable b] (α : MulAut U0) (E : U0) :
    cU (α (if b then E else 1)) = if b then cU (α E) else 0 := by
  split_ifs
  · rfl
  · exact cU_alpha_one α

theorem cU_alpha_elU (α : MulAut U0) (u : Nat) : cU (α (elU u)) = ap (tupF α) u := by
  dsimp only [elU]
  simp only [cU_alpha_mul, cU_alpha_ite]
  unfold ap tupF
  rfl

theorem cU_alpha (α : MulAut U0) (x : U0) : cU (α x) = ap (tupF α) (cU x) := by
  have hu : cU x < 16 := cU_lt16 x
  have hk : cU (x * elU (cU x)) = 0 := by
    rw [cU_mul, cU_elU _ hu]
    simp
  have hkα : cU (α (x * elU (cU x))) = 0 := by
    rcases (cU_eq_zero_iff _).1 hk with h | h
    · rw [h, map_one, cU_one]
    · rw [h, cU_alpha_zc]
  have hinv : cU (α (elU (cU x))⁻¹) = cU (α (elU (cU x))) := by
    rw [map_inv, cU_inv]
  have hx : x = (x * elU (cU x)) * (elU (cU x))⁻¹ := (mul_inv_cancel_right x _).symm
  have h1 : cU (α x) = cU (α ((x * elU (cU x)) * (elU (cU x))⁻¹)) :=
    congrArg (fun y => cU (α y)) hx
  rw [map_mul, cU_mul, hkα, hinv, cU_alpha_elU] at h1
  rw [h1]
  exact Nat.zero_xor _

theorem ite_alpha_eq (α β : MulAut U0) (E : U0) (hE : α E = β E) {b : Prop} [Decidable b] :
    α (if b then E else 1) = β (if b then E else 1) := by
  split_ifs
  · exact hE
  · rw [map_one, map_one]

theorem elU_alpha_eq (α β : MulAut U0) (hE1 : α E1 = β E1) (hE2 : α E2 = β E2)
    (hE4 : α E4 = β E4) (hE8 : α E8 = β E8) (u : Nat) : α (elU u) = β (elU u) := by
  dsimp only [elU]
  simp only [map_mul, ite_alpha_eq α β E1 hE1, ite_alpha_eq α β E2 hE2,
    ite_alpha_eq α β E4 hE4, ite_alpha_eq α β E8 hE8]

theorem eq_of_gens (α β : MulAut U0) (hz : α zc = β zc) (hE1 : α E1 = β E1)
    (hE2 : α E2 = β E2) (hE4 : α E4 = β E4) (hE8 : α E8 = β E8) : α = β := by
  have hEl := elU_alpha_eq α β hE1 hE2 hE4 hE8
  refine MulEquiv.ext fun x => ?_
  have hk0 : cU (x * elU (cU x)) = 0 := by
    rw [cU_mul, cU_elU _ (cU_lt16 x)]
    simp
  have hαk : α (x * elU (cU x)) = β (x * elU (cU x)) := by
    rcases (cU_eq_zero_iff _).1 hk0 with h | h
    · rw [h, map_one, map_one]
    · rw [h, hz]
  have hαe : α (elU (cU x))⁻¹ = β (elU (cU x))⁻¹ := by
    rw [map_inv, map_inv, hEl]
  have hx : x = (x * elU (cU x)) * (elU (cU x))⁻¹ := (mul_inv_cancel_right x _).symm
  calc α x = α (x * elU (cU x) * (elU (cU x))⁻¹) := congrArg α hx
    _ = α (x * elU (cU x)) * α (elU (cU x))⁻¹ := map_mul _ _ _
    _ = β (x * elU (cU x)) * β (elU (cU x))⁻¹ := by rw [hαk, hαe]
    _ = β (x * elU (cU x) * (elU (cU x))⁻¹) := (map_mul _ _ _).symm
    _ = β x := by rw [← hx]

theorem patternFact (y1 y2 y4 y8 : U0) (h1 : y1 = E1 ∨ y1 = zc * E1)
    (h2 : y2 = E2 ∨ y2 = zc * E2) (h4 : y4 = E4 ∨ y4 = zc * E4) (h8 : y8 = E8 ∨ y8 = zc * E8) :
    ∃ v < 16, elU v * E1 * (elU v)⁻¹ = y1 ∧ elU v * E2 * (elU v)⁻¹ = y2 ∧
      elU v * E4 * (elU v)⁻¹ = y4 ∧ elU v * E8 * (elU v)⁻¹ = y8 := by
  letI : DecidableEq U0 := fun x y =>
    if h : (x : Mc).left = (y : Mc).left ∧ (x : Mc).right = (y : Mc).right then
      isTrue (Subtype.ext (SemidirectProduct.ext h.1 h.2))
    else
      isFalse (fun hxy => h ⟨congrArg (fun u : U0 => (u : Mc).left) hxy,
        congrArg (fun u : U0 => (u : Mc).right) hxy⟩)
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    rcases h4 with rfl | rfl <;> rcases h8 with rfl | rfl <;> decide

def Inn0 : Subgroup (MulAut U0) := (MulAut.conj : U0 →* MulAut U0).range

theorem mem_Inn0_iff (α : MulAut U0) : α ∈ Inn0 ↔ ∃ u : U0, MulAut.conj u = α :=
  Iff.rfl

theorem conj_zc (g : U0) : MulAut.conj g zc = zc := by
  rw [MulAut.conj_apply, zc_comm g, mul_inv_cancel_right]

theorem cU_conj (g x : U0) : cU (MulAut.conj g x) = cU x := by
  rw [MulAut.conj_apply, cU_mul, cU_mul, cU_inv]
  exact xor3_fact (cU g) (cU_lt16 g) (cU x) (cU_lt16 x)

theorem tupF_conj (g : U0) : tupF (MulAut.conj g) = one := by
  unfold tupF one
  simp only [cU_conj, cU_E1, cU_E2, cU_E4, cU_E8]

theorem Inn0_tupF (α : MulAut U0) (h : α ∈ Inn0) : tupF α = one := by
  unfold Inn0 at h
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 h
  exact tupF_conj g

theorem tupF_eq_one_mem (α : MulAut U0) (h : tupF α = one) : α ∈ Inn0 := by
  have hid : ∀ x : U0, cU (α x) = cU x := by
    intro x
    rw [cU_alpha, h]
    exact ap_one_fact _ (cU_lt16 x)
  have key : ∀ x : U0, α x = x ∨ α x = zc * x := by
    intro x
    have h0 : cU (α x * x⁻¹) = 0 := by
      rw [cU_mul, cU_inv, hid]
      simp
    rcases (cU_eq_zero_iff _).1 h0 with h' | h'
    · exact Or.inl (mul_inv_eq_one.1 h')
    · exact Or.inr (mul_inv_eq_iff_eq_mul.1 h')
  obtain ⟨v, -, h1, h2, h4, h8⟩ :=
    patternFact (α E1) (α E2) (α E4) (α E8) (key E1) (key E2) (key E4) (key E8)
  unfold Inn0
  rw [MonoidHom.mem_range]
  refine ⟨elU v, eq_of_gens _ _ ?_ ?_ ?_ ?_ ?_⟩
  · rw [conj_zc, alpha_zc]
  · rw [MulAut.conj_apply]
    exact h1
  · rw [MulAut.conj_apply]
    exact h2
  · rw [MulAut.conj_apply]
    exact h4
  · rw [MulAut.conj_apply]
    exact h8

theorem tupF_eq_one_iff (α : MulAut U0) : tupF α = one ↔ α ∈ Inn0 :=
  ⟨tupF_eq_one_mem α, Inn0_tupF α⟩

theorem tupF_mul (α β : MulAut U0) : tupF (α * β) = comp (tupF α) (tupF β) := by
  have key : ∀ E : U0, cU ((α * β) E) = ap (tupF α) (cU (β E)) := fun E => by
    rw [MulAut.mul_apply, cU_alpha]
  show (cU ((α * β) E1), cU ((α * β) E2), cU ((α * β) E4), cU ((α * β) E8)) =
    (ap (tupF α) (tupF β).1, ap (tupF α) (tupF β).2.1, ap (tupF α) (tupF β).2.2.1,
      ap (tupF α) (tupF β).2.2.2)
  rw [key E1, key E2, key E4, key E8]
  rfl

theorem sq_elU : ∀ u, u < 16 → elU u * elU u = if qf u then zc else 1 := by
  letI : DecidableEq U0 := fun x y =>
    if h : (x : Mc).left = (y : Mc).left ∧ (x : Mc).right = (y : Mc).right then
      isTrue (Subtype.ext (SemidirectProduct.ext h.1 h.2))
    else
      isFalse (fun hxy => h ⟨congrArg (fun u : U0 => (u : Mc).left) hxy,
        congrArg (fun u : U0 => (u : Mc).right) hxy⟩)
  decide

theorem zc_sq : zc * zc = 1 := by
  letI : DecidableEq U0 := fun x y =>
    if h : (x : Mc).left = (y : Mc).left ∧ (x : Mc).right = (y : Mc).right then
      isTrue (Subtype.ext (SemidirectProduct.ext h.1 h.2))
    else
      isFalse (fun hxy => h ⟨congrArg (fun u : U0 => (u : Mc).left) hxy,
        congrArg (fun u : U0 => (u : Mc).right) hxy⟩)
  decide

theorem central_sq (z e : U0) (hz : z * z = 1) (hc : e * z = z * e) :
    (z * e) * (z * e) = (z * z) * (e * e) := by
  simp only [mul_assoc]
  rw [← mul_assoc e z e, hc]
  simp only [mul_assoc]

theorem sq_aux (x : U0) (u : Nat) (hu : u < 16) (hcu : cU x = u) :
    x * x = if qf u then zc else 1 := by
  have hk : cU (x * (elU u)⁻¹) = 0 := by
    rw [cU_mul, cU_inv, cU_elU u hu, hcu]
    exact Nat.xor_self u
  rcases (cU_eq_zero_iff _).1 hk with h | h
  · have hx : x = elU u := mul_inv_eq_one.1 h
    rw [hx, sq_elU u hu]
  · have hx : x = zc * elU u := mul_inv_eq_iff_eq_mul.1 h
    rw [hx, central_sq zc (elU u) zc_sq (zc_comm _), zc_sq, one_mul, sq_elU u hu]

theorem sq_fact (x : U0) : x * x = if qf (cU x) then zc else 1 :=
  sq_aux x (cU x) (cU_lt16 x) rfl

theorem qf_alpha (α : MulAut U0) (x : U0) : qf (cU (α x)) = qf (cU x) := by
  have h1 : α (x * x) = α x * α x := map_mul α x x
  have h2 : α x * α x = if qf (cU x) then zc else 1 := by
    rw [← h1, sq_fact x]
    split_ifs with hq <;> simp [alpha_zc]
  rw [sq_fact (α x)] at h2
  generalize qf (cU x) = p at h2 ⊢
  generalize qf (cU (α x)) = q at h2 ⊢
  cases p <;> cases q <;> simp_all [zc_ne_one, zc_ne_one.symm]

theorem tupF_iso (α : MulAut U0) : IsIso (tupF α) = true := by
  simp only [IsIso, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro u hu
  rw [← cU_alpha_elU α u, qf_alpha α (elU u), cU_elU u hu]

theorem tupF_mem_isoList (α : MulAut U0) : tupF α ∈ isoList :=
  isoList_mem _ (cU_lt16 (α E1)) (cU_lt16 (α E2)) (cU_lt16 (α E4)) (cU_lt16 (α E8))
    (tupF_iso α)

theorem compT_one (g : T4) : comp g one = g := by
  obtain ⟨a, b, c, d⟩ := g
  simp [comp, one, ap_u1, ap_u2, ap_u4, ap_u8]

theorem tupF_one : tupF 1 = one := by
  unfold tupF one
  simp only [MulAut.one_apply, cU_E1, cU_E2, cU_E4, cU_E8]

theorem tupF_pow (α : MulAut U0) (n : ℕ) : tupF (α ^ n) = pw (tupF α) n := by
  induction n with
  | zero => rw [pow_zero, tupF_one]; rfl
  | succ k ih => rw [pow_succ', tupF_mul, ih]; rfl

theorem conj_aux (n : MulAut U0) (g : U0) : n * MulAut.conj g * n⁻¹ = MulAut.conj (n g) := by
  refine MulEquiv.ext fun x => ?_
  show n (g * n.symm x * g⁻¹) = n g * x * (n g)⁻¹
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

instance Inn0_normal : Inn0.Normal where
  conj_mem := by
    intro m hm n
    unfold Inn0 at hm ⊢
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hm
    exact MonoidHom.mem_range.2 ⟨n g, (conj_aux n g).symm⟩

theorem pow9_of (X : Subgroup (MulAut U0)) (hX : Nat.card X = 9) (p : MulAut U0) (hp : p ∈ X) :
    p ^ 9 = 1 := by
  have h := pow_card_eq_one' (G := ↥X) (x := ⟨p, hp⟩)
  rw [hX] at h
  simpa using congrArg Subtype.val h

theorem tupF_mem_p3 (X : Subgroup (MulAut U0)) (hX : Nat.card X = 9) (p : MulAut U0)
    (hp : p ∈ X) : tupF p ∈ p3List := by
  have hmem : tupF p ∈ isoList := tupF_mem_isoList p
  have h9 : pw (tupF p) 9 = one := by
    rw [← tupF_pow, pow9_of X hX p hp, tupF_one]
  have h3 : pw (tupF p) 3 = one := by
    have hc : isoList.all (fun g => pw g 9 != one || pw g 3 == one) = true := chkPow9_true
    have := List.all_eq_true.1 hc (tupF p) hmem
    simpa [h9] using this
  unfold p3List
  exact List.mem_filter.2 ⟨hmem, by simpa using h3⟩

theorem inf_Inn0_card (X : Subgroup (MulAut U0)) (hX : Nat.card X = 9) :
    Nat.card ↥(X ⊓ Inn0) = 1 := by
  have h1 := Subgroup.card_dvd_of_le (inf_le_left : X ⊓ Inn0 ≤ X)
  rw [hX] at h1
  have h2 := Subgroup.card_dvd_of_le (inf_le_right : X ⊓ Inn0 ≤ Inn0)
  have h3 : Nat.card ↥Inn0 ∣ 32 := by
    have h := Subgroup.card_range_dvd (MulAut.conj : U0 →* MulAut U0)
    rw [card_U0] at h
    exact h
  have h4 := Nat.dvd_gcd h1 (h2.trans h3)
  have h5 : Nat.gcd 9 32 = 1 := by norm_num
  rw [h5] at h4
  exact Nat.dvd_one.1 h4

theorem tupF_inj_on (X : Subgroup (MulAut U0)) (hX : Nat.card X = 9) (p q : X)
    (h : tupF (p : MulAut U0) = tupF (q : MulAut U0)) : p = q := by
  apply Subtype.ext
  have hk : (p : MulAut U0)⁻¹ * (q : MulAut U0) ∈ Inn0 := by
    apply (tupF_eq_one_iff _).1
    rw [tupF_mul, ← h, ← tupF_mul, inv_mul_cancel, tupF_one]
  have hX' : (p : MulAut U0)⁻¹ * (q : MulAut U0) ∈ X := X.mul_mem (X.inv_mem p.2) q.2
  have hmem : (p : MulAut U0)⁻¹ * (q : MulAut U0) ∈ X ⊓ Inn0 := ⟨hX', hk⟩
  have hsub : Subsingleton ↥(X ⊓ Inn0) := (Nat.card_eq_one_iff_unique.1 (inf_Inn0_card X hX)).1
  have hEq : (⟨_, hmem⟩ : ↥(X ⊓ Inn0)) = ⟨1, (X ⊓ Inn0).one_mem⟩ := Subsingleton.elim _ _
  have h1 : (p : MulAut U0)⁻¹ * (q : MulAut U0) = 1 := congrArg Subtype.val hEq
  exact inv_mul_eq_one.1 h1

theorem p3List_length : p3List.length = 9 := by
  have h := chkP3Card_true
  unfold chkP3Card at h
  simpa using h

theorem exists_of_p3 (X : Subgroup (MulAut U0)) (hX : Nat.card X = 9) (g : T4)
    (hg : g ∈ p3List) : ∃ p ∈ X, tupF p = g := by
  have hinj : Function.Injective (fun p : X => tupF (p : MulAut U0)) :=
    fun p q h => tupF_inj_on X hX p q h
  have hrange : (Set.range (fun p : X => tupF (p : MulAut U0))).ncard = 9 := by
    rw [Set.ncard_range_of_injective hinj]
    exact hX
  have hsub : Set.range (fun p : X => tupF (p : MulAut U0)) ⊆ ↑p3List.toFinset := by
    rintro _ ⟨p, rfl⟩
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact tupF_mem_p3 X hX p p.2
  have hcard : (↑p3List.toFinset : Set T4).ncard ≤
      (Set.range (fun p : X => tupF (p : MulAut U0))).ncard := by
    rw [Set.ncard_coe_finset, hrange, List.card_toFinset]
    exact (List.dedup_sublist _).length_le.trans p3List_length.le
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard
  have hg' : g ∈ (↑p3List.toFinset : Set T4) := by simpa using hg
  rw [← heq] at hg'
  obtain ⟨p, hp⟩ := hg'
  exact ⟨p, p.2, hp⟩

theorem tupF_of_sup (X : Subgroup (MulAut U0)) (α : MulAut U0) (hα : α ∈ X ⊔ Inn0) :
    ∃ p ∈ X, tupF α = tupF p := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hα
  refine ⟨y, hy, ?_⟩
  rw [tupF_mul, Inn0_tupF z hz, compT_one]

theorem sup_le_aux (X Y : Subgroup (MulAut U0)) (hX : Nat.card X = 9) (hY : Nat.card Y = 9) :
    X ⊔ Inn0 ≤ Y ⊔ Inn0 := by
  intro α hα
  obtain ⟨p, hp, hpα⟩ := tupF_of_sup X α hα
  obtain ⟨p', hp', hp'eq⟩ := exists_of_p3 Y hY (tupF p) (tupF_mem_p3 X hX p hp)
  have hk : p'⁻¹ * α ∈ Inn0 := by
    apply (tupF_eq_one_iff _).1
    rw [tupF_mul, hpα, ← hp'eq, ← tupF_mul, inv_mul_cancel, tupF_one]
  have hmul := Subgroup.mul_mem_sup hp' hk
  rwa [mul_inv_cancel_left] at hmul

theorem three_part_unique (P P' : Subgroup (MulAut U0)) (hP : Nat.card P = 9)
    (hP' : Nat.card P' = 9) : P ⊔ Inn0 = P' ⊔ Inn0 :=
  le_antisymm (sup_le_aux P P' hP hP') (sup_le_aux P' P hP' hP)

theorem three_part_cube (P : Subgroup (MulAut U0)) (hP : Nat.card P = 9) :
    ∀ α ∈ P ⊔ Inn0, α ^ 3 ∈ Inn0 := by
  intro α hα
  obtain ⟨p, hp, hpα⟩ := tupF_of_sup P α hα
  rw [← tupF_eq_one_iff, tupF_pow, hpα]
  have h3 : pw (tupF p) 3 = one := by
    have := (List.mem_filter.1 (tupF_mem_p3 P hP p hp)).2
    simpa using this
  exact h3

end CFSG.GH74.QTGen4.U42.U0AutC
