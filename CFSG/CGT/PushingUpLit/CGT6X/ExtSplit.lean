module

public import CFSG.CGT.PushingUpLit.CGT6X.ExtDual

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

section Restrict

variable {H E : Type*} [Group H] [CommGroup E]

@[expose] def SInv (τ : H →* MulAut E) (S : Subgroup E) : Prop := ∀ h : H, ∀ x ∈ S, τ h x ∈ S

@[expose] def resAut (τ : H →* MulAut E) (S : Subgroup E) (hS : SInv τ S) (h : H) : MulAut ↥S where
  toFun x := ⟨τ h x, hS h x x.2⟩
  invFun x := ⟨τ h⁻¹ x, hS h⁻¹ x x.2⟩
  left_inv x := by
    apply Subtype.ext
    show τ h⁻¹ (τ h x) = x
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv x := by
    apply Subtype.ext
    show τ h (τ h⁻¹ x) = x
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    show τ h (x * y : E) = τ h x * τ h y
    exact map_mul _ _ _

@[expose] def resAct (τ : H →* MulAut E) (S : Subgroup E) (hS : SInv τ S) : H →* MulAut ↥S where
  toFun := resAut τ S hS
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    apply Subtype.ext
    show τ 1 (x : E) = x
    rw [map_one]
    rfl
  map_mul' h h' := by
    refine MulEquiv.ext fun x => ?_
    apply Subtype.ext
    show τ (h * h') (x : E) = τ h (τ h' (x : E))
    rw [map_mul]
    rfl

end Restrict

section Complement

variable {E : Type*} [CommGroup E]

theorem comm_cancel (a b c : E) : a * b⁻¹ * (c * a⁻¹) = c * b⁻¹ := by
  have : a * b⁻¹ * (c * a⁻¹) = (c * b⁻¹) * (a * a⁻¹) := by ac_rfl
  rw [this, mul_inv_cancel, mul_one]

theorem zpow_eq_one_or_self (hE : ∀ x : E, x ^ 2 = 1) (w : E) (k : ℤ) : w ^ k = 1 ∨ w ^ k = w := by
  have hw2 : w * w = 1 := by rw [← pow_two]; exact hE w
  induction k using Int.induction_on with
  | zero => left; simp
  | succ k ih =>
    rw [zpow_add_one]
    rcases ih with h | h
    · right; rw [h, one_mul]
    · left; rw [h, hw2]
  | pred k ih =>
    rw [zpow_sub_one, inv_eq_of_mul_eq_one_right hw2]
    rcases ih with h | h
    · right; rw [h, one_mul]
    · left; rw [h, hw2]

theorem sup_zpowers_inf_eq_bot (hE : ∀ x : E, x ^ 2 = 1) {C D : Subgroup E} {w : E}
    (hCD : C ⊓ D = ⊥) (hw : w ∉ C ⊔ D) : (C ⊔ Subgroup.zpowers w) ⊓ D = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxC', hxD⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hxC'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rcases zpow_eq_one_or_self hE w k with hk | hk
  · rw [hk, mul_one] at hxD ⊢
    have : y ∈ C ⊓ D := ⟨hy, hxD⟩
    rw [hCD] at this
    exact this
  · rw [hk] at hxD
    exfalso
    apply hw
    have : w = y⁻¹ * (y * w) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ hy))
      (Subgroup.mem_sup_right hxD)

theorem lt_sup_zpowers {C : Subgroup E} {w : E} (hw : w ∉ C) : C < C ⊔ Subgroup.zpowers w := by
  refine lt_of_le_of_ne le_sup_left fun h => hw ?_
  rw [h]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)

variable [Finite E]

theorem exists_complement (hE : ∀ x : E, x ^ 2 = 1) (D W : Subgroup E) (hDW : D ≤ W) :
    ∃ C : Subgroup E, C ≤ W ∧ C ⊓ D = ⊥ ∧ C ⊔ D = W := by
  classical
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨C, ⟨hCW, hCD⟩, hmax⟩ := Set.exists_max_image {C : Subgroup E | C ≤ W ∧ C ⊓ D = ⊥}
    (fun C : Subgroup E => Nat.card C) (Set.toFinite _) ⟨⊥, bot_le, bot_inf_eq _⟩
  refine ⟨C, hCW, hCD, le_antisymm (sup_le hCW hDW) ?_⟩
  intro w hw
  by_contra hwn
  have hwC : w ∉ C := fun h => hwn (Subgroup.mem_sup_left h)
  have hC'W : C ⊔ Subgroup.zpowers w ≤ W := sup_le hCW ((Subgroup.zpowers_le).2 hw)
  have h1 := hmax (C ⊔ Subgroup.zpowers w) ⟨hC'W, sup_zpowers_inf_eq_bot hE hCD hwn⟩
  have h2 : Nat.card C < Nat.card ↥(C ⊔ Subgroup.zpowers w) :=
    Subgroup.card_lt_of_lt (lt_sup_zpowers hwC)
  omega

end Complement

section Top

variable {H E : Type*} [Group H] [CommGroup E] [Finite E]

theorem exists_inv_complement_top (hE : ∀ x : E, x ^ 2 = 1) (τ : H →* MulAut E)
    (N' : Subgroup E) (hN' : SInv τ N') (htriv : ∀ (h : H) (x : E), τ h x * x⁻¹ ∈ N')
    (hcoh : ∀ c : H → ↥N', IsCocycle (resAct τ N' hN') c → IsCoboundary (resAct τ N' hN') c) :
    ∃ C : Subgroup E, SInv τ C ∧ C ⊓ N' = ⊥ ∧ C ⊔ N' = ⊤ := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hbot : SInv τ (⊥ : Subgroup E) := fun h x hx => by
    rw [Subgroup.mem_bot.1 hx, map_one]
    exact Subgroup.one_mem _
  obtain ⟨C, ⟨hCinv, hCN⟩, hmax⟩ := Set.exists_max_image
    {C : Subgroup E | SInv τ C ∧ C ⊓ N' = ⊥} (fun C : Subgroup E => Nat.card C)
    (Set.toFinite _) ⟨⊥, hbot, bot_inf_eq _⟩
  refine ⟨C, hCinv, hCN, ?_⟩
  by_contra hne
  obtain ⟨e, he⟩ := not_forall.1 (fun h => hne ((Subgroup.eq_top_iff' (C ⊔ N')).2 h))
  let c : H → ↥N' := fun h => ⟨τ h e * e⁻¹, htriv h e⟩
  have hcoc : IsCocycle (resAct τ N' hN') c := by
    intro h h'
    apply Subtype.ext
    show τ (h * h') e * e⁻¹ = (τ h e * e⁻¹) * τ h (τ h' e * e⁻¹)
    rw [map_mul, MulAut.mul_apply, (τ h).map_mul, (τ h).map_inv]
    exact (comm_cancel _ _ _).symm
  obtain ⟨m, hm⟩ := hcoh c hcoc
  have hfix : ∀ h : H, τ h (e * (m : E)⁻¹) = e * (m : E)⁻¹ := by
    intro h
    have h1 : τ h e * e⁻¹ = τ h (m : E) * (m : E)⁻¹ := congrArg Subtype.val (hm h)
    rw [(τ h).map_mul, (τ h).map_inv]
    have h2 : τ h e = τ h (m : E) * (m : E)⁻¹ * e := (mul_inv_eq_iff_eq_mul.1 h1)
    rw [h2]
    have : τ h (m : E) * (m : E)⁻¹ * e * (τ h (m : E))⁻¹ =
        e * (m : E)⁻¹ * (τ h (m : E) * (τ h (m : E))⁻¹) := by ac_rfl
    rw [this, mul_inv_cancel, mul_one]
  set e' : E := e * (m : E)⁻¹ with he'
  have he'C : e' ∉ C ⊔ N' := by
    intro h
    apply he
    have : e = e' * (m : E) := by rw [he']; group
    rw [this]
    exact Subgroup.mul_mem _ h (Subgroup.mem_sup_right m.2)
  have he'C0 : e' ∉ C := fun h => he'C (Subgroup.mem_sup_left h)
  have hinv' : SInv τ (C ⊔ Subgroup.zpowers e') := by
    intro h x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [map_mul, map_zpow, hfix h]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hCinv h y hy))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩))
  have h1 := hmax (C ⊔ Subgroup.zpowers e') ⟨hinv', sup_zpowers_inf_eq_bot hE hCN he'C⟩
  have h2 : Nat.card C < Nat.card ↥(C ⊔ Subgroup.zpowers e') :=
    Subgroup.card_lt_of_lt (lt_sup_zpowers he'C0)
  omega

end Top

section Two

theorem zmod_two_cases' : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem zmod2m_cases (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) := by
  obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective x
  rcases zmod_two_cases' c with rfl | rfl
  · left; rfl
  · right; rfl

theorem zmod2m_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

theorem zmod2m_mul_self (x : Multiplicative (ZMod 2)) : x * x = 1 := by
  rcases zmod2m_cases x with rfl | rfl
  · exact one_mul 1
  · decide

variable {E : Type*} [CommGroup E]

@[expose] noncomputable def nuHom (d₀ : E) (hd₀ : d₀ * d₀ = 1) : Multiplicative (ZMod 2) →* E := by
  classical
  exact
  { toFun := fun x => if x = 1 then 1 else d₀
    map_one' := by simp
    map_mul' := fun x y => by
      rcases zmod2m_cases x with rfl | rfl <;> rcases zmod2m_cases y with rfl | rfl
      · simp
      · simp
      · simp
      · rw [zmod2m_mul_self]
        simp [hd₀] }

theorem nuHom_one (d₀ : E) (hd₀ : d₀ * d₀ = 1) : nuHom d₀ hd₀ 1 = 1 := map_one _

theorem nuHom_gen (d₀ : E) (hd₀ : d₀ * d₀ = 1) :
    nuHom d₀ hd₀ (Multiplicative.ofAdd (1 : ZMod 2)) = d₀ := by
  classical
  show (if Multiplicative.ofAdd (1 : ZMod 2) = 1 then 1 else d₀) = d₀
  simp

theorem nuHom_cases (d₀ : E) (hd₀ : d₀ * d₀ = 1) (x : Multiplicative (ZMod 2)) :
    nuHom d₀ hd₀ x = 1 ∨ nuHom d₀ hd₀ x = d₀ := by
  rcases zmod2m_cases x with rfl | rfl
  · left; exact nuHom_one d₀ hd₀
  · right; exact nuHom_gen d₀ hd₀

end Two

section Bottom

variable {H E M : Type*} [Group H] [CommGroup E] [CommGroup M]

structure ExtData (τ : H →* MulAut E) (σ : H →* MulAut M) (A : Subgroup E) (β : E →* M) : Prop where
  inv : SInv τ A
  triv : ∀ (h : H), ∀ a ∈ A, τ h a = a
  surj : Function.Surjective β
  ker : ∀ e, β e = 1 ↔ e ∈ A
  equiv : ∀ (h : H) (e : E), β (τ h e) = σ h (β e)

section Step

variable [Finite E]

theorem step_bottom (hE : ∀ x : E, x ^ 2 = 1) {τ : H →* MulAut E} {σ : H →* MulAut M}
    {A : Subgroup E} {β : E →* M} (hD : ExtData τ σ A β)
    (hdual : ∀ γ : H → Dual M, IsCocycle (dualAct σ) γ → IsCoboundary (dualAct σ) γ)
    (hA : A ≠ ⊥) :
    ∃ A₀ E₁ : Subgroup E, A₀ < A ∧ SInv τ E₁ ∧ E₁ ⊓ A = A₀ ∧ E₁ ⊔ A = ⊤ := by
  classical
  obtain ⟨d₀, hd₀A, hd₀1⟩ : ∃ d₀ ∈ A, d₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hA ((Subgroup.eq_bot_iff_forall A).2 h)
  have hd₀sq : d₀ * d₀ = 1 := by rw [← pow_two]; exact hE d₀
  obtain ⟨χ, hχ⟩ := exists_char_eq_ofAdd_one (A := ↥A) (fun a => Subtype.ext (hE a))
    (a := ⟨d₀, hd₀A⟩) (fun h => hd₀1 (congrArg Subtype.val h))
  let χ' : E → Multiplicative (ZMod 2) := fun e => if he : e ∈ A then χ ⟨e, he⟩ else 1
  have hχ'a : ∀ (e : E) (he : e ∈ A), χ' e = χ ⟨e, he⟩ := fun e he => by simp [χ', he]
  have hχ'mul : ∀ a ∈ A, ∀ b ∈ A, χ' (a * b) = χ' a * χ' b := fun a ha b hb => by
    rw [hχ'a _ (A.mul_mem ha hb), hχ'a a ha, hχ'a b hb]
    exact map_mul χ ⟨a, ha⟩ ⟨b, hb⟩
  have hχ'one : χ' 1 = 1 := by
    rw [hχ'a 1 A.one_mem]
    exact map_one χ
  have hχ'inv : ∀ a ∈ A, χ' a⁻¹ = (χ' a)⁻¹ := fun a ha => by
    rw [hχ'a _ (A.inv_mem ha), hχ'a a ha]
    exact map_inv χ ⟨a, ha⟩
  have hχ'd₀ : χ' d₀ = Multiplicative.ofAdd 1 := by rw [hχ'a d₀ hd₀A]; exact hχ
  let A₀ : Subgroup E :=
    { carrier := {x | x ∈ A ∧ χ' x = 1}
      one_mem' := ⟨A.one_mem, hχ'one⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨A.mul_mem ha.1 hb.1, by rw [hχ'mul a ha.1 b hb.1, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [hχ'inv a ha.1, ha.2, inv_one]⟩ }
  have hA₀A : A₀ ≤ A := fun x hx => hx.1
  have hA₀lt : A₀ < A := by
    refine lt_of_le_of_ne hA₀A fun h => ?_
    have : d₀ ∈ A₀ := h ▸ hd₀A
    have h1 : χ' d₀ = 1 := this.2
    rw [hχ'd₀] at h1
    exact zmod2m_ne_one h1
  obtain ⟨C₀, -, hC₀A, hC₀sup⟩ := exists_complement hE A ⊤ le_top
  let b : ↥C₀ →* M := β.comp C₀.subtype
  have hbinj : Function.Injective b := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have : (c : E) ∈ C₀ ⊓ A := ⟨c.2, (hD.ker c).1 hc⟩
    rw [hC₀A] at this
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  have hbsurj : Function.Surjective b := by
    intro q
    obtain ⟨e, rfl⟩ := hD.surj q
    have he : e ∈ C₀ ⊔ A := by rw [hC₀sup]; exact Subgroup.mem_top e
    obtain ⟨c, hc, a, ha, rfl⟩ := Subgroup.mem_sup.1 he
    refine ⟨⟨c, hc⟩, ?_⟩
    show β c = β (c * a)
    rw [map_mul, (hD.ker a).2 ha, mul_one]
  let bE : ↥C₀ ≃* M := MulEquiv.ofBijective b ⟨hbinj, hbsurj⟩
  let s : M →* E := C₀.subtype.comp bE.symm.toMonoidHom
  have hs : ∀ q, β (s q) = q := fun q => bE.apply_symm_apply q
  have hsβ : ∀ c ∈ C₀, s (β c) = c := fun c hc =>
    congrArg Subtype.val (bE.symm_apply_apply ⟨c, hc⟩)
  let δ : H → M → E := fun h q => τ h (s (σ h⁻¹ q)) * (s q)⁻¹
  have hδ : ∀ h q, δ h q = τ h (s (σ h⁻¹ q)) * (s q)⁻¹ := fun _ _ => rfl
  have hδA : ∀ h q, δ h q ∈ A := fun h q => by
    rw [← hD.ker, hδ, map_mul β, β.map_inv, hD.equiv, hs, hs, act_act_inv σ h q, mul_inv_cancel]
  have hδmul : ∀ h q q', δ h (q * q') = δ h q * δ h q' := fun h q q' => by
    simp only [hδ, map_mul, mul_inv_rev]
    ac_rfl
  have hδone : ∀ h, δ h 1 = 1 := fun h => by simp [hδ]
  have hδcoc : ∀ h h' q, δ (h * h') q = δ h q * δ h' (σ h⁻¹ q) := fun h h' q => by
    have e1 : τ h' (s (σ h'⁻¹ (σ h⁻¹ q))) = δ h' (σ h⁻¹ q) * s (σ h⁻¹ q) := by
      rw [hδ, inv_mul_cancel_right]
    have e2 : σ (h * h')⁻¹ q = σ h'⁻¹ (σ h⁻¹ q) := by rw [mul_inv_rev, map_mul]; rfl
    have e3 : τ (h * h') (s (σ h'⁻¹ (σ h⁻¹ q))) = τ h (τ h' (s (σ h'⁻¹ (σ h⁻¹ q)))) := by
      rw [map_mul]; rfl
    calc δ (h * h') q = τ h (τ h' (s (σ h'⁻¹ (σ h⁻¹ q)))) * (s q)⁻¹ := by
          rw [hδ, e2, e3]
      _ = τ h (δ h' (σ h⁻¹ q) * s (σ h⁻¹ q)) * (s q)⁻¹ := by rw [e1]
      _ = (δ h' (σ h⁻¹ q) * τ h (s (σ h⁻¹ q))) * (s q)⁻¹ := by
          rw [map_mul, hD.triv h _ (hδA h' _)]
      _ = δ h q * δ h' (σ h⁻¹ q) := by rw [hδ h q]; ac_rfl
  let γ : H → Dual M := fun h =>
    { toFun := fun q => χ' (δ h q)
      map_one' := by rw [hδone, hχ'one]
      map_mul' := fun q q' => by rw [hδmul, hχ'mul _ (hδA h q) _ (hδA h q')] }
  have hγ : IsCocycle (dualAct σ) γ := by
    intro h h'
    refine MonoidHom.ext fun q => ?_
    show χ' (δ (h * h') q) = (γ h * dualAct σ h (γ h')) q
    rw [dual_mul_apply, dualAct_apply]
    show χ' (δ (h * h') q) = χ' (δ h q) * χ' (δ h' (σ h⁻¹ q))
    rw [hδcoc, hχ'mul _ (hδA h q) _ (hδA h' _)]
  obtain ⟨ψ, hψ⟩ := hdual γ hγ
  have hψδ : ∀ h q, χ' (δ h q) = ψ (σ h⁻¹ q) * (ψ q)⁻¹ := fun h q => by
    have := congrArg (fun f : Dual M => f q) (hψ h)
    simp only [dual_mul_apply, dualAct_apply, dual_inv_apply] at this
    exact this
  let ν := nuHom d₀ hd₀sq
  let u : M →* E := ν.comp ψ
  have hu_mem : ∀ q, u q ∈ A := fun q => by
    rcases nuHom_cases d₀ hd₀sq (ψ q) with h | h
    · show ν (ψ q) ∈ A
      rw [h]
      exact A.one_mem
    · show ν (ψ q) ∈ A
      rw [h]
      exact hd₀A
  have hu_β : ∀ q, β (u q) = 1 := fun q => (hD.ker _).2 (hu_mem q)
  have hu_χ : ∀ q, χ' (u q) = ψ q := fun q => by
    rcases zmod2m_cases (ψ q) with h | h
    · show χ' (ν (ψ q)) = ψ q
      rw [h, nuHom_one, hχ'one]
    · show χ' (ν (ψ q)) = ψ q
      rw [h, nuHom_gen, hχ'd₀]
  have hu_fix : ∀ h q, τ h (u q) = u q := fun h q => hD.triv h _ (hu_mem q)
  let s' : M →* E := s * u
  have hs' : ∀ q, s' q = s q * u q := fun q => rfl
  have hβs' : ∀ q, β (s' q) = q := fun q => by rw [hs', map_mul β, hs, hu_β, mul_one]
  let E₁ : Subgroup E := s'.range ⊔ A₀
  have hE₁A : E₁ ⊓ A = A₀ := by
    apply le_antisymm
    · rintro x ⟨hx1, hxA⟩
      obtain ⟨r, ⟨q, rfl⟩, a, ha, rfl⟩ := Subgroup.mem_sup.1 hx1
      have hq : q = 1 := by
        have h1 := (hD.ker _).2 hxA
        rw [map_mul β, hβs', (hD.ker a).2 ha.1, mul_one] at h1
        exact h1
      rw [hq, map_one, one_mul]
      exact ha
    · exact le_inf le_sup_right hA₀A
  have hE₁top : E₁ ⊔ A = ⊤ := by
    refine eq_top_iff.2 fun e _ => ?_
    have he : e ∈ C₀ ⊔ A := by rw [hC₀sup]; exact Subgroup.mem_top e
    obtain ⟨c, hc, a, ha, rfl⟩ := Subgroup.mem_sup.1 he
    refine Subgroup.mem_sup.2 ⟨s' (β c), Subgroup.mem_sup_left ⟨β c, rfl⟩,
      (u (β c))⁻¹ * a, A.mul_mem (A.inv_mem (hu_mem _)) ha, ?_⟩
    rw [hs', ← mul_assoc, mul_assoc (s (β c)), mul_inv_cancel, mul_one, hsβ c hc]
  have hSInv : SInv τ E₁ := by
    intro h x hx
    obtain ⟨r, ⟨q, rfl⟩, a, ha, rfl⟩ := Subgroup.mem_sup.1 hx
    have hτs : τ h (s q) = δ h (σ h q) * s (σ h q) := by
      rw [hδ, act_inv_act σ h q, inv_mul_cancel_right]
    have key : τ h (s' q) = s' (σ h q) * (δ h (σ h q) * u q * (u (σ h q))⁻¹) := by
      simp only [hs']
      rw [map_mul, hτs, hu_fix]
      have e : s (σ h q) * u (σ h q) * (δ h (σ h q) * u q * (u (σ h q))⁻¹) =
          (δ h (σ h q) * s (σ h q) * u q) * (u (σ h q) * (u (σ h q))⁻¹) := by ac_rfl
      rw [e, mul_inv_cancel, mul_one]
    have ha₁ : δ h (σ h q) * u q * (u (σ h q))⁻¹ ∈ A₀ := by
      refine ⟨A.mul_mem (A.mul_mem (hδA _ _) (hu_mem _)) (A.inv_mem (hu_mem _)), ?_⟩
      rw [hχ'mul _ (A.mul_mem (hδA _ _) (hu_mem _)) _ (A.inv_mem (hu_mem _)),
        hχ'mul _ (hδA _ _) _ (hu_mem _), hχ'inv _ (hu_mem _), hψδ, act_inv_act σ h q,
        hu_χ, hu_χ]
      have := zmod2m_mul_self (ψ q * (ψ (σ h q))⁻¹)
      rw [← this]
      ac_rfl
    show τ h (s' q * a) ∈ E₁
    rw [map_mul, hD.triv h a ha.1, key, mul_assoc]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨σ h q, rfl⟩)
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right ha₁) (Subgroup.mem_sup_right ha))
  exact ⟨A₀, E₁, hA₀lt, hSInv, hE₁A, hE₁top⟩

end Step

universe u

section Induction

variable {H : Type*} [Group H] {M : Type*} [CommGroup M]

theorem exists_inv_complement_bottom {σ : H →* MulAut M}
    (hdual : ∀ γ : H → Dual M, IsCocycle (dualAct σ) γ → IsCoboundary (dualAct σ) γ) :
    ∀ (k : ℕ) (E : Type u) [CommGroup E] [Finite E], (∀ x : E, x ^ 2 = 1) →
      ∀ (τ : H →* MulAut E) (A : Subgroup E) (β : E →* M), ExtData τ σ A β → Nat.card A = k →
        ∃ C : Subgroup E, SInv τ C ∧ C ⊓ A = ⊥ ∧ C ⊔ A = ⊤ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro E _ _ hE τ A β hD hk
  by_cases hA : A = ⊥
  · refine ⟨⊤, fun h x _ => Subgroup.mem_top _, ?_, ?_⟩
    · rw [hA]; exact inf_bot_eq _
    · rw [hA]; exact sup_bot_eq _
  obtain ⟨A₀, E₁, hlt, hinv, hinf, hsup⟩ := step_bottom hE hD hdual hA
  have hA₀E₁ : A₀ ≤ E₁ := hinf ▸ inf_le_left
  have hA₀A : A₀ ≤ A := hlt.le
  let τ' : H →* MulAut ↥E₁ := resAct τ E₁ hinv
  let A' : Subgroup ↥E₁ := A₀.subgroupOf E₁
  let β' : ↥E₁ →* M := β.comp E₁.subtype
  have hmemA' : ∀ x : ↥E₁, x ∈ A' ↔ (x : E) ∈ A₀ := fun x => Iff.rfl
  have hD' : ExtData τ' σ A' β' := by
    refine ⟨fun h x hx => ?_, fun h a ha => ?_, fun m => ?_, fun x => ?_, fun h x => ?_⟩
    · rw [hmemA'] at hx ⊢
      show τ h (x : E) ∈ A₀
      rw [hD.triv h _ (hA₀A hx)]
      exact hx
    · apply Subtype.ext
      exact hD.triv h _ (hA₀A ha)
    · obtain ⟨e, rfl⟩ := hD.surj m
      have he : e ∈ E₁ ⊔ A := by rw [hsup]; exact Subgroup.mem_top e
      obtain ⟨x, hx, a, ha, rfl⟩ := Subgroup.mem_sup.1 he
      refine ⟨⟨x, hx⟩, ?_⟩
      show β x = β (x * a)
      rw [map_mul, (hD.ker a).2 ha, mul_one]
    · rw [hmemA']
      show β (x : E) = 1 ↔ (x : E) ∈ A₀
      rw [hD.ker, ← hinf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    · exact hD.equiv h x
  have hcard : Nat.card A' < k := by
    have h1 : Nat.card A' = Nat.card A₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀E₁).toEquiv
    rw [h1, ← hk]
    exact Subgroup.card_lt_of_lt hlt
  have : Finite ↥E₁ := inferInstance
  obtain ⟨C', hC'inv, hC'A, hC'sup⟩ := ih _ hcard ↥E₁ (fun x => Subtype.ext (hE x)) τ' A' β' hD' rfl
  refine ⟨C'.map E₁.subtype, ?_, ?_, ?_⟩
  · intro h x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.mem_map.2 ⟨τ' h c, hC'inv h c hc, rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hxA⟩
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx1
    have hc₀ : (c : E) ∈ A₀ := by rw [← hinf]; exact ⟨c.2, hxA⟩
    have : c ∈ C' ⊓ A' := ⟨hc, (hmemA' c).2 hc₀⟩
    rw [hC'A] at this
    have := Subgroup.mem_bot.1 this
    rw [this]
    exact Subgroup.one_mem _
  · refine eq_top_iff.2 fun e _ => ?_
    have he : e ∈ E₁ ⊔ A := by rw [hsup]; exact Subgroup.mem_top e
    obtain ⟨x, hx, a, ha, rfl⟩ := Subgroup.mem_sup.1 he
    have hx' : (⟨x, hx⟩ : ↥E₁) ∈ C' ⊔ A' := by rw [hC'sup]; exact Subgroup.mem_top _
    obtain ⟨c, hc, a', ha', hca⟩ := Subgroup.mem_sup.1 hx'
    refine Subgroup.mem_sup.2 ⟨(c : E), Subgroup.mem_map.2 ⟨c, hc, rfl⟩, (a' : E) * a,
      A.mul_mem (hA₀A ((hmemA' a').1 ha')) ha, ?_⟩
    have := congrArg Subtype.val hca
    rw [← mul_assoc]
    exact congrArg (· * a) this

end Induction

end Bottom

end CFSG.CGT.PushingUpLit.CGT6X
