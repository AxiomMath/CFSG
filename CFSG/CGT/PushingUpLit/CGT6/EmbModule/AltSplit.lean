module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.AltBasic
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv Equiv.Perm Subgroup

theorem alt_retraction {Γ : Type*} [Group Γ] {V : Type*} [CommGroup V] (ρ : Γ →* MulAut V)
    {n : ℕ} (hn : Odd n) (θ : Γ →* Perm (Fin n)) (hev : ∀ g, θ g ∈ alternatingGroup (Fin n))
    (hsurj : ∀ σ ∈ alternatingGroup (Fin n), ∃ g, θ g = σ)
    (hV : ∀ v : V, v ^ 2 = 1) (A B : Subgroup V) (hAB : A ≤ B)
    (hB : ∀ g, ∀ b ∈ B, ρ g b ∈ B) (hAt : ∀ g, ∀ a ∈ A, ρ g a = a)
    (β : ↥B →* ↥(coreMod n)) (hβs : Function.Surjective β) (hβk : β.ker = A.subgroupOf B)
    (hβe : ∀ g (b : ↥B), β ⟨ρ g b, hB g b b.2⟩ = coreAct n (θ g) (β b))
    (hker : ∀ k, θ k = 1 → ∀ b ∈ B, ρ k b = b) :
    ∃ r : ↥B →* V, (∀ b, r b ∈ A) ∧ (∀ a (ha : a ∈ A), r ⟨a, hAB ha⟩ = a) ∧
      (∀ g (b : ↥B), r ⟨ρ g b, hB g b b.2⟩ = r b) := by
  classical
  have hn0 : 0 < n := hn.pos
  let x₀ : Fin n := ⟨0, hn0⟩
  obtain ⟨b₀, hb₀⟩ := hβs (fvec hn x₀)
  have hχA : ∀ h, θ h x₀ = x₀ → ρ h (b₀ : V) * (b₀ : V)⁻¹ ∈ A := by
    intro h hh
    have h1 : β ⟨ρ h b₀, hB h b₀ b₀.2⟩ = β b₀ := by
      rw [hβe, hb₀, coreAct_fvec, hh]
    have h2 : (⟨ρ h b₀, hB h b₀ b₀.2⟩ : ↥B) * b₀⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hstab : ∀ h, θ h x₀ = x₀ → ρ h (b₀ : V) = b₀ := by
    intro h hh
    have key := stab_hom_trivial (M := V) θ hev hsurj hV x₀
      (fun h => ρ h (b₀ : V) * (b₀ : V)⁻¹)
      (fun g h hg hh => by
        have h1 := hAt g _ (hχA h hh)
        have h2 : ρ (g * h) (b₀ : V) = ρ g (ρ h (b₀ : V)) := by
          rw [map_mul]; rfl
        have h3 : ρ h (b₀ : V) = (ρ h (b₀ : V) * (b₀ : V)⁻¹) * b₀ := by group
        rw [h2]
        conv_lhs => rw [h3]
        rw [map_mul, h1]
        ac_rfl)
      (fun k hk => by
        rw [hker k hk b₀ b₀.2, mul_inv_cancel]) h hh
    exact mul_inv_eq_one.mp key
  have hex : ∀ x : Fin n, ∃ g : Γ, θ g x₀ = x := by
    intro x
    obtain ⟨σ, hσ, hσx⟩ := exists_alt_apply hn x₀ x
    obtain ⟨g, hg⟩ := hsurj σ hσ
    exact ⟨g, by rw [hg]; exact hσx⟩
  choose gx hgx using hex
  let bb : Fin n → V := fun x => ρ (gx x) (b₀ : V)
  have hbb_wd : ∀ g x, θ g x₀ = x → ρ g (b₀ : V) = bb x := by
    intro g x hg
    have hst : θ ((gx x)⁻¹ * g) x₀ = x₀ := by
      rw [map_mul, map_inv, Perm.mul_apply, hg, Perm.inv_eq_iff_eq]
      exact (hgx x).symm
    have h1 := hstab _ hst
    have h2 : ρ g (b₀ : V) = ρ (gx x) (ρ ((gx x)⁻¹ * g) (b₀ : V)) := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [h2, h1]
  have hbb_mem : ∀ x, bb x ∈ B := fun x => hB _ _ b₀.2
  have hbb_sq : ∀ x, bb x * bb x = 1 := fun x => by rw [← pow_two]; exact hV _
  have hbb_eq : ∀ g x, ρ g (bb x) = bb (θ g x) := by
    intro g x
    have : θ (g * gx x) x₀ = θ g x := by rw [map_mul, Perm.mul_apply, hgx x]
    rw [← hbb_wd (g * gx x) (θ g x) this, map_mul]
    rfl
  have hβbb : ∀ x, β ⟨bb x, hbb_mem x⟩ = fvec hn x := by
    intro x
    have h1 := hβe (gx x) b₀
    rw [hb₀, coreAct_fvec, hgx x] at h1
    exact h1
  let bB : Fin n → ↥B := fun x => ⟨bb x, hbb_mem x⟩
  let Φ : PermMod n →* ↥B :=
    { toFun := fun v => ∏ x : Fin n, if Multiplicative.toAdd v x = 1 then bB x else 1
      map_one' := by simp
      map_mul' := by
        intro v w
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun x _ => ?_
        have hsq : bB x * bB x = 1 := Subtype.ext (hbb_sq x)
        rcases zmod_two_cases (Multiplicative.toAdd v x) with h1 | h1 <;>
        rcases zmod_two_cases (Multiplicative.toAdd w x) with h2 | h2 <;>
        simp [h1, h2, hsq, zmod_two_one_add_one] }
  have hΦapp : ∀ v, Φ v = ∏ x : Fin n, if Multiplicative.toAdd v x = 1 then bB x else 1 :=
    fun v => rfl
  have hΦe : ∀ g v, ρ g (Φ v : V) = (Φ (permAct n (θ g) v) : V) := by
    intro g v
    have h1 : ((Φ v : ↥B) : V) = ∏ x : Fin n, if Multiplicative.toAdd v x = 1 then bb x else 1 := by
      rw [hΦapp, show (((∏ x : Fin n, if Multiplicative.toAdd v x = 1 then bB x else 1 : ↥B)) : V) =
        ∏ x : Fin n, ((if Multiplicative.toAdd v x = 1 then bB x else 1 : ↥B) : V) from
          map_prod B.subtype _ _]
      refine Finset.prod_congr rfl fun x _ => ?_
      split_ifs <;> rfl
    have h2 : ((Φ (permAct n (θ g) v) : ↥B) : V) = ∏ y : Fin n,
        if Multiplicative.toAdd v ((θ g)⁻¹ y) = 1 then bb y else 1 := by
      rw [hΦapp, show (((∏ x : Fin n, if Multiplicative.toAdd (permAct n (θ g) v) x = 1 then bB x
        else 1 : ↥B)) : V) = ∏ x : Fin n, ((if Multiplicative.toAdd (permAct n (θ g) v) x = 1
          then bB x else 1 : ↥B) : V) from map_prod B.subtype _ _]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [permAct_apply]
      split_ifs <;> rfl
    rw [h1, h2, map_prod]
    rw [← Equiv.prod_comp (θ g) (fun y => if Multiplicative.toAdd v ((θ g)⁻¹ y) = 1 then bb y
      else 1)]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp only [Perm.inv_def, Equiv.symm_apply_apply]
    split_ifs
    · exact hbb_eq g x
    · exact map_one _
  have hΦβ : ∀ v : ↥(coreMod n), β (Φ (v : PermMod n)) = v := by
    intro v
    rw [hΦapp, map_prod]
    have : ∀ x : Fin n, β (if Multiplicative.toAdd (v : PermMod n) x = 1 then bB x else 1) =
        if Multiplicative.toAdd (v : PermMod n) x = 1 then fvec hn x else 1 := by
      intro x
      split_ifs
      · exact hβbb x
      · exact map_one _
    rw [Finset.prod_congr rfl (fun x _ => this x)]
    exact prod_fvec hn v
  let r : ↥B →* V :=
    B.subtype * (B.subtype.comp (Φ.comp ((coreMod n).subtype.comp β)))⁻¹
  have hr : ∀ b : ↥B, r b = (b : V) * ((Φ ((β b : ↥(coreMod n)) : PermMod n) : ↥B) : V)⁻¹ :=
    fun b => rfl
  have hrA : ∀ b : ↥B, r b ∈ A := by
    intro b
    have h1 : b * (Φ ((β b : ↥(coreMod n)) : PermMod n))⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hΦβ, mul_inv_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at h1
    rw [hr]
    simpa using h1
  refine ⟨r, hrA, ?_, ?_⟩
  · intro a ha
    have h1 : β ⟨a, hAB ha⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]; exact ha
    rw [hr, h1]
    simp
  · intro g b
    rw [hr, hr]
    have h1 : ((Φ ((β ⟨ρ g b, hB g b b.2⟩ : ↥(coreMod n)) : PermMod n) : ↥B) : V) =
        ρ g ((Φ ((β b : ↥(coreMod n)) : PermMod n) : ↥B) : V) := by
      rw [hβe, coreAct_coe, hΦe]
    rw [h1, ← map_inv, ← map_mul]
    have := hAt g _ (hrA b)
    rw [hr] at this
    exact this

theorem alt_exists_ker {V : Type*} [CommGroup V] {n : ℕ} (A B : Subgroup V) (hAB : A ≤ B)
    (β : ↥B →* ↥(coreMod n)) (hβs : Function.Surjective β) (hβk : β.ker = A.subgroupOf B)
    (r : ↥B →* V) (hrA : ∀ b, r b ∈ A) (hr1 : ∀ a (ha : a ∈ A), r ⟨a, hAB ha⟩ = a)
    (w : ↥(coreMod n)) : ∃ b : ↥B, β b = w ∧ r b = 1 := by
  obtain ⟨b', hb'⟩ := hβs w
  let a' : ↥B := ⟨r b', hAB (hrA b')⟩
  have hβa' : β a' = 1 := by
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]; exact hrA b'
  have hra' : r a' = r b' := hr1 _ (hrA b')
  refine ⟨b' * a'⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, hβa', inv_one, mul_one, hb']
  · rw [map_mul, map_inv, hra', mul_inv_cancel]

theorem zmod_two_neg (a : ZMod 2) : -a = a := by
  revert a
  decide

theorem zmod_two_aux (a d s : ZMod 2) : (a + s) + (d + s) = d + a := by
  revert a d s
  decide

theorem alt_fixed_lift {Γ : Type*} [Group Γ] {V : Type*} [CommGroup V] (ρ : Γ →* MulAut V)
    {n : ℕ} (hn : Odd n) (θ : Γ →* Perm (Fin n)) (hθi : Function.Injective θ)
    (hev : ∀ g, θ g ∈ alternatingGroup (Fin n))
    (hsurj : ∀ σ ∈ alternatingGroup (Fin n), ∃ g, θ g = σ)
    (A B : Subgroup V) (hAB : A ≤ B) (hB : ∀ g, ∀ b ∈ B, ρ g b ∈ B)
    (β : ↥B →* ↥(coreMod n)) (hβs : Function.Surjective β) (hβk : β.ker = A.subgroupOf B)
    (hβe : ∀ g (b : ↥B), β ⟨ρ g b, hB g b b.2⟩ = coreAct n (θ g) (β b))
    (r : ↥B →* V) (hrA : ∀ b, r b ∈ A) (hr1 : ∀ a (ha : a ∈ A), r ⟨a, hAB ha⟩ = a)
    (hrg : ∀ g (b : ↥B), r ⟨ρ g b, hB g b b.2⟩ = r b)
    (v : V) (hv : ∀ g, ρ g v * v⁻¹ ∈ B) (hv1 : ∀ g, r ⟨ρ g v * v⁻¹, hv g⟩ = 1) :
    ∃ b : ↥B, r b = 1 ∧ ∀ g, ρ g (v * (b : V)⁻¹) = v * (b : V)⁻¹ := by
  classical
  let x₀ : Fin n := ⟨0, hn.pos⟩
  let u : Γ → ↥B := fun g => ⟨ρ g v * v⁻¹, hv g⟩
  let c : Γ → Fin n → ZMod 2 := fun g => Multiplicative.toAdd ((β (u g) : ↥(coreMod n)) : PermMod n)
  have hu : ∀ g h, u (g * h) = ⟨ρ g (u h : V), hB g _ (u h).2⟩ * u g := by
    intro g h
    apply Subtype.ext
    show ρ (g * h) v * v⁻¹ = ρ g (ρ h v * v⁻¹) * (ρ g v * v⁻¹)
    rw [map_mul, MulAut.mul_apply, map_mul, map_inv]
    group
  have hc : ∀ g h y, c (g * h) y = c g y + c h ((θ g)⁻¹ y) := by
    intro g h y
    have h1 := congrArg (fun w : ↥B => Multiplicative.toAdd ((β w : ↥(coreMod n)) : PermMod n) y)
      (hu g h)
    simp only [map_mul, hβe] at h1
    rw [Subgroup.coe_mul, toAdd_mul, Pi.add_apply, coreAct_coe, permAct_apply] at h1
    show _ = c g y + c h ((θ g)⁻¹ y)
    rw [add_comm]
    exact h1
  have hker : ∀ k, θ k = 1 → c k x₀ = 0 := by
    intro k hk
    have : k = 1 := hθi (by rw [hk, map_one])
    subst this
    have : u 1 = 1 := by
      apply Subtype.ext
      show ρ 1 v * v⁻¹ = 1
      simp
    show Multiplicative.toAdd ((β (u 1) : ↥(coreMod n)) : PermMod n) x₀ = 0
    rw [this, map_one]
    rfl
  obtain ⟨m, hm⟩ := cocycle_perm hn θ hev hsurj x₀ c hc hker
  let s : ZMod 2 := ∑ i, m i
  have hmN : ∑ y, (m y + s) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    obtain ⟨k, hk⟩ := hn
    have h1 : (n : ZMod 2) = 1 := by
      rw [hk]; push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul, zero_add]
    rw [h1, one_mul]
    exact zmod_two_add_self s
  let mN : ↥(coreMod n) := ⟨Multiplicative.ofAdd (fun y => m y + s), by
    rw [mem_coreMod]; exact hmN⟩
  obtain ⟨b', hb'⟩ := hβs mN
  let a' : ↥B := ⟨r b', hAB (hrA b')⟩
  have hβa' : β a' = 1 := by
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]; exact hrA b'
  have hra' : r a' = r b' := hr1 _ (hrA b')
  let b : ↥B := b' * a'⁻¹
  have hβb : β b = mN := by
    rw [show b = b' * a'⁻¹ from rfl, map_mul, map_inv, hβa', inv_one, mul_one, hb']
  have hrb : r b = 1 := by
    rw [show b = b' * a'⁻¹ from rfl, map_mul, map_inv, hra', mul_inv_cancel]
  refine ⟨b, hrb, fun g => ?_⟩
  let w₁ : ↥B := ⟨ρ g (b : V), hB g b b.2⟩ * b⁻¹
  have hβw : β w₁ = β (u g) := by
    rw [show w₁ = ⟨ρ g (b : V), hB g b b.2⟩ * b⁻¹ from rfl, map_mul, map_inv, hβe, hβb]
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext y
    have hy := hm g y
    show Multiplicative.toAdd ((coreAct n (θ g) mN * mN⁻¹ : ↥(coreMod n)) : PermMod n) y = c g y
    rw [hy, Subgroup.coe_mul, toAdd_mul, Pi.add_apply, coreAct_coe, permAct_apply,
      Subgroup.coe_inv, toAdd_inv, Pi.neg_apply]
    show (m ((θ g)⁻¹ y) + s) + -(m y + s) = m y + m ((θ g)⁻¹ y)
    simp only [zmod_two_neg]
    exact zmod_two_aux _ _ _
  have hrw : r w₁ = 1 := by
    rw [show w₁ = ⟨ρ g (b : V), hB g b b.2⟩ * b⁻¹ from rfl, map_mul, map_inv, hrg, hrb]
    simp
  have heq : w₁ = u g := by
    have hx : w₁ * (u g)⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβw, mul_inv_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at hx
    have h2 := hr1 _ hx
    rw [map_mul, map_inv, hrw, hv1] at h2
    have h3 : (1 : V) * 1⁻¹ = ((w₁ * (u g)⁻¹ : ↥B) : V) := by simpa using h2
    have h4 : w₁ * (u g)⁻¹ = 1 := Subtype.ext (by simpa using h3.symm)
    exact mul_inv_eq_one.mp h4
  have hg2 : ρ g (b : V) * (b : V)⁻¹ = ρ g v * v⁻¹ := congrArg (fun w : ↥B => (w : V)) heq
  rw [map_mul, map_inv]
  have h3 : ρ g v = ρ g (b : V) * (b : V)⁻¹ * v := by
    rw [hg2]; group
  rw [h3, mul_comm (ρ g (b : V)) (b : V)⁻¹, mul_right_comm, mul_inv_cancel_right, mul_comm]

theorem alt_chain {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (G : Subgroup (MulAut V))
    {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n)
    (hind : ∀ A B : Subgroup V, (∀ g ∈ G, ∀ a ∈ A, g a ∈ A) → (∀ g ∈ G, ∀ a ∈ B, g a ∈ B) →
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥)
    (A B : Subgroup V) (hAB : A ≤ B) (hB : ∀ g ∈ G, ∀ b ∈ B, g b ∈ B)
    (hAt : ∀ g ∈ G, ∀ a ∈ A, g a = a) (hVB : ∀ g ∈ G, ∀ v : V, g v * v⁻¹ ∈ B)
    (θ : ↥G ≃* alternatingGroup (Fin n)) (β : ↥B →* ↥(coreMod n)) (hβs : Function.Surjective β)
    (hβk : β.ker = A.subgroupOf B)
    (hβe : ∀ (x : ↥G) (p : ↥B) (hp : (x : MulAut V) p ∈ B),
      β ⟨(x : MulAut V) p, hp⟩ =
        coreAct n ((θ x : alternatingGroup (Fin n)) : Perm (Fin n)) (β p)) :
    A = ⊥ ∧ B = ⊤ := by
  classical
  let ρ : ↥G →* MulAut V := G.subtype
  let θ' : ↥G →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp θ.toMonoidHom
  have hθi : Function.Injective θ' := by
    intro a b h
    exact θ.injective (Subtype.ext h)
  have hev : ∀ g, θ' g ∈ alternatingGroup (Fin n) := fun g => (θ g).2
  have hsurj : ∀ σ ∈ alternatingGroup (Fin n), ∃ g, θ' g = σ := fun σ hσ =>
    ⟨θ.symm ⟨σ, hσ⟩, by simp [θ']⟩
  have hB' : ∀ g : ↥G, ∀ b ∈ B, ρ g b ∈ B := fun g b hb => hB g g.2 b hb
  have hAt' : ∀ g : ↥G, ∀ a ∈ A, ρ g a = a := fun g a ha => hAt g g.2 a ha
  have hβe' : ∀ (g : ↥G) (b : ↥B), β ⟨ρ g b, hB' g b b.2⟩ = coreAct n (θ' g) (β b) :=
    fun g b => hβe g b (hB' g b b.2)
  have hker1 : ∀ k : ↥G, θ' k = 1 → k = 1 := fun k hk => hθi (by rw [hk, map_one])
  obtain ⟨r, hrA, hr1, hrg⟩ := alt_retraction ρ hn θ' hev hsurj hV A B hAB hB' hAt' β hβs hβk hβe'
    (fun k hk b _ => by rw [hker1 k hk]; rfl)
  have hv : ∀ (v : V) (g : ↥G), ρ g v * v⁻¹ ∈ B := fun v g => hVB g g.2 v
  have hu : ∀ (v : V) (g h : ↥G), (⟨ρ (g * h) v * v⁻¹, hv v (g * h)⟩ : ↥B) =
      ⟨ρ g (ρ h v * v⁻¹), hB' g _ (hv v h)⟩ * ⟨ρ g v * v⁻¹, hv v g⟩ := by
    intro v g h
    apply Subtype.ext
    show ρ (g * h) v * v⁻¹ = ρ g (ρ h v * v⁻¹) * (ρ g v * v⁻¹)
    rw [map_mul, MulAut.mul_apply, map_mul, map_inv]
    group
  have hv1 : ∀ (v : V) (g : ↥G), r ⟨ρ g v * v⁻¹, hv v g⟩ = 1 := by
    intro v
    refine alt_hom_trivial θ' hev hsurj (M := V) hV (fun g => r ⟨ρ g v * v⁻¹, hv v g⟩)
      (fun g h => ?_) (fun k hk => ?_)
    · show r ⟨ρ (g * h) v * v⁻¹, hv v (g * h)⟩ = _
      have h1 : r ⟨ρ g (ρ h v * v⁻¹), hB' g _ (hv v h)⟩ = r ⟨ρ h v * v⁻¹, hv v h⟩ :=
        hrg g ⟨ρ h v * v⁻¹, hv v h⟩
      rw [hu, map_mul, h1]
      exact mul_comm _ _
    · rw [hker1 k hk]
      have : (⟨ρ 1 v * v⁻¹, hv v 1⟩ : ↥B) = 1 := by apply Subtype.ext; simp [ρ]
      show r _ = 1
      rw [this, map_one]
  let B₁ : Subgroup V := r.ker.map B.subtype
  let C : Subgroup V := fixV G
  have hB₁ : ∀ g ∈ G, ∀ a ∈ B₁, g a ∈ B₁ := by
    intro g hg a ha
    obtain ⟨b, hb, rfl⟩ := ha
    refine ⟨⟨g b, hB g hg b b.2⟩, ?_, rfl⟩
    have := hrg ⟨g, hg⟩ b
    exact this.trans hb
  have hC : ∀ g ∈ G, ∀ a ∈ C, g a ∈ C := by
    intro g hg a ha
    rw [show g a = a from ha g hg]
    exact ha
  have hinf : B₁ ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨b, hb, rfl⟩, hxC⟩
    have hfix : ∀ σ ∈ alternatingGroup (Fin n), coreAct n σ (β b) = β b := by
      intro σ hσ
      obtain ⟨g, hg⟩ := hsurj σ hσ
      rw [← hg, ← hβe' g b]
      congr 1
      exact Subtype.ext (hxC g.1 g.2)
    have hb1 : β b = 1 := core_fixed_eq_one hn _ hfix
    have hbA : (b : V) ∈ A := by
      have : b ∈ β.ker := hb1
      rw [hβk, Subgroup.mem_subgroupOf] at this
      exact this
    have h2 := hr1 (b : V) hbA
    have h3 : r b = 1 := hb
    rw [Subgroup.mem_bot]
    have h4 : r ⟨(b : V), hAB hbA⟩ = 1 := h3
    rw [h2] at h4
    exact h4
  have hsup : B₁ ⊔ C = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨b, hrb, hbfix⟩ := alt_fixed_lift ρ hn θ' hθi hev hsurj A B hAB hB' β hβs hβk hβe' r
      hrA hr1 hrg v (hv v) (hv1 v)
    have h1 : (b : V) ∈ B₁ := ⟨b, hrb, rfl⟩
    have h2 : v * (b : V)⁻¹ ∈ C := fun g hg => hbfix ⟨g, hg⟩
    have h3 := Subgroup.mul_mem_sup h1 h2
    have e : (b : V) * (v * (b : V)⁻¹) = v := by rw [mul_comm v, mul_inv_cancel_left]
    rwa [e] at h3
  rcases hind B₁ C hB₁ hC hinf hsup with h1 | h2
  · exfalso
    obtain ⟨x₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn.pos⟩⟩
    obtain ⟨b, hbw, hrb⟩ := alt_exists_ker A B hAB β hβs hβk r hrA hr1 (fvec hn x₀)
    have hb : (b : V) ∈ B₁ := ⟨b, hrb, rfl⟩
    rw [h1, Subgroup.mem_bot] at hb
    have : b = 1 := Subtype.ext hb
    rw [this, map_one] at hbw
    exact fvec_ne_one hn hn3 x₀ hbw.symm
  · rw [h2, sup_bot_eq] at hsup
    refine ⟨?_, ?_⟩
    · rw [eq_bot_iff]
      intro a ha
      have hmem : a ∈ B₁ := by rw [hsup]; trivial
      obtain ⟨b, hb, rfl⟩ := hmem
      have h2 := hr1 (b : V) ha
      have h3 : r b = 1 := hb
      rw [Subgroup.mem_bot]
      have h4 : r ⟨(b : V), hAB ha⟩ = 1 := h3
      rw [h2] at h4
      exact h4
    · rw [eq_top_iff]
      intro v _
      have hmem : v ∈ B₁ := by rw [hsup]; trivial
      obtain ⟨b, -, rfl⟩ := hmem
      exact b.2

end CFSG.CGT.PushingUpLit.CGT6
