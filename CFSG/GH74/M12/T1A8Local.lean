module

public import CFSG.GH74.M12.T1Syl

public section

namespace CFSG.GH74.M12.Thm1

open Subgroup CFSG.Quasithin
open CFSG.GH74.M12 (Asc03Hyp q8Subgroups)

variable {G : Type*} [Group G] {z : G}

theorem perm3_comm_cube : ∀ σ τ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 → τ * τ * τ = 1 →
    τ ≠ 1 → (σ * τ * σ * τ⁻¹) * (σ * τ * σ * τ⁻¹) * (σ * τ * σ * τ⁻¹) = 1 := by
  decide +kernel

theorem perm3_comm_ne : ∀ σ τ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 → τ * τ * τ = 1 →
    τ ≠ 1 → σ * τ * σ * τ⁻¹ ≠ 1 := by
  decide +kernel

theorem perm3_comm_order (σ τ : Equiv.Perm (Fin 3)) (hσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hτ : τ * τ * τ = 1) (hτ1 : τ ≠ 1) :
    (σ * τ * σ * τ⁻¹) ^ 3 = 1 ∧ σ * τ * σ * τ⁻¹ ≠ 1 := by
  refine ⟨?_, perm3_comm_ne σ τ hσ hσ1 hτ hτ1⟩
  rw [pow_three, ← mul_assoc]
  exact perm3_comm_cube σ τ hσ hσ1 hτ hτ1

theorem exists_inverted_three [Finite G] (hyp : Asc03Hyp G z) {v : G} (hvH : v ∈ ascH z)
    (hvQ : v ∉ ascQ z) (hv2 : v * v = 1) :
    ∃ y ∈ ascH z, orderOf y = 3 ∧ v * y * v⁻¹ = y⁻¹ := by
  obtain ⟨y₀, hy₀H, hy₀3⟩ := exists_order_three hyp
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  set w := v * (y₀ * v * y₀⁻¹) with hw
  have hwH : w ∈ ascH z := (ascH z).mul_mem hvH
    ((ascH z).mul_mem ((ascH z).mul_mem hy₀H hvH) ((ascH z).inv_mem hy₀H))
  have hvw : v * w * v⁻¹ = w⁻¹ := by
    rw [hw, hvinv]
    calc v * (v * (y₀ * v * y₀⁻¹)) * v = (v * v) * (y₀ * v * y₀⁻¹) * v := by group
      _ = y₀ * v * y₀⁻¹ * v := by rw [hv2, one_mul]
      _ = (v * (y₀ * v * y₀⁻¹))⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, hvinv]; group
  have hρv1 : rho hyp ⟨v, hvH⟩ ≠ 1 := by rw [Ne, rho_eq_one_iff]; exact hvQ
  have hρy1 : rho hyp ⟨y₀, hy₀H⟩ ≠ 1 := by
    rw [Ne, rho_eq_one_iff]; exact not_mem_ascQ_of_order_three hyp hy₀3
  have hρv2 : rho hyp ⟨v, hvH⟩ * rho hyp ⟨v, hvH⟩ = 1 := by
    rw [← map_mul]
    have : (⟨v, hvH⟩ : ↥(ascH z)) * ⟨v, hvH⟩ = 1 := Subtype.ext hv2
    rw [this, map_one]
  have hρy3 : rho hyp ⟨y₀, hy₀H⟩ * rho hyp ⟨y₀, hy₀H⟩ * rho hyp ⟨y₀, hy₀H⟩ = 1 := by
    rw [← map_mul, ← map_mul]
    have : (⟨y₀, hy₀H⟩ : ↥(ascH z)) * ⟨y₀, hy₀H⟩ * ⟨y₀, hy₀H⟩ = 1 :=
      Subtype.ext (mul_self_mul_self_eq_one hy₀3)
    rw [this, map_one]
  obtain ⟨h3, h31⟩ := perm3_comm_order _ _ hρv2 hρv1 hρy3 hρy1
  have hρw : rho hyp ⟨w, hwH⟩ = rho hyp ⟨v, hvH⟩ * rho hyp ⟨y₀, hy₀H⟩ * rho hyp ⟨v, hvH⟩ *
      (rho hyp ⟨y₀, hy₀H⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hw]
    group
  have hord3 : orderOf (rho hyp ⟨w, hwH⟩) = 3 := by
    rw [hρw]; exact orderOf_eq_prime h3 h31
  have hdvd : 3 ∣ orderOf w := by
    have := orderOf_map_dvd (rho hyp) ⟨w, hwH⟩
    rw [hord3, Subgroup.orderOf_mk] at this
    exact this
  have hw0 : orderOf w ≠ 0 := (orderOf_pos w).ne'
  refine ⟨w ^ (orderOf w / 3), (ascH z).pow_mem hwH _,
    orderOf_pow_orderOf_div hw0 hdvd, ?_⟩
  rw [← conj_pow, hvw, inv_pow]

theorem cent_inv_facts [Finite G] (hyp : Asc03Hyp G z) {y : G} {K₁ K₂ : Subgroup G}
    (hd : Q8Data z y K₁ K₂) {v : G} (hvH : v ∈ ascH z) (hv2 : v * v = 1)
    (hK : K₁.map (MulAut.conj v).toMonoidHom = K₂) :
    Nat.card ↥(ascQ z ⊓ centralizer ({v} : Set G)) = 8 ∧
      ∀ a ∈ ascQ z ⊓ centralizer ({v} : Set G), ∀ b ∈ ascQ z ⊓ centralizer ({v} : Set G),
        a * a = 1 ∧ a * b = b * a := by
  have hE := extraspecialAt_ascQ hyp
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hvK : ∀ k ∈ K₁, v * k * v⁻¹ ∈ K₂ := fun k hk => by rw [← hK]; exact ⟨k, hk, rfl⟩
  have hvz : v * z = z * v := Subgroup.mem_centralizer_singleton_iff.1 hvH
  have hkk : ∀ k ∈ K₁, k * k = 1 ∨ k * k = z := fun k hk => hE.sq_mem k (hd.le1 hk)
  let φ : ↥K₁ →* G :=
    { toFun := fun k => (k : G) * (v * k * v⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        show ((a : G) * b) * (v * ((a : G) * b) * v⁻¹) = ((a : G) * (v * a * v⁻¹)) *
          ((b : G) * (v * b * v⁻¹))
        have hc := hd.comm b b.2 _ (hvK a a.2)
        calc ((a : G) * b) * (v * ((a : G) * b) * v⁻¹) =
            a * ((b : G) * (v * a * v⁻¹)) * (v * b * v⁻¹) := by group
          _ = a * ((v * a * v⁻¹) * b) * (v * b * v⁻¹) := by rw [hc]
          _ = ((a : G) * (v * a * v⁻¹)) * ((b : G) * (v * b * v⁻¹)) := by group }
  have hφ : ∀ k : ↥K₁, φ k = (k : G) * (v * k * v⁻¹) := fun k => rfl
  set C := ascQ z ⊓ centralizer ({v} : Set G) with hCdef
  have hmemC : ∀ x : G, x ∈ C ↔ x ∈ ascQ z ∧ x * v = v * x := by
    intro x
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hφC : ∀ k : ↥K₁, φ k ∈ C := by
    intro k
    rw [hmemC, hφ]
    refine ⟨(ascQ z).mul_mem (hd.le1 k.2) (hd.le2 (hvK k k.2)), ?_⟩
    have hc := hd.comm k k.2 _ (hvK k k.2)
    rw [hvinv] at hc ⊢
    calc (k : G) * (v * k * v) * v = (v * k * v) * k * v := by rw [hc]
      _ = v * ((k : G) * (v * k * v)) := by group
  have hK1C : ∀ k ∈ K₁, k ∈ C → k = 1 ∨ k = z := by
    intro k hk hkC
    have hkv := ((hmemC k).1 hkC).2
    have : v * k * v⁻¹ = k := by
      calc v * k * v⁻¹ = k * v * v⁻¹ := by rw [hkv]
        _ = k := by group
    exact hd.inter k hk (this ▸ hvK k hk)
  have hker : ∀ k : ↥K₁, φ k = 1 → (k : G) = 1 ∨ (k : G) = z := by
    intro k hk
    rw [hφ] at hk
    have h1 : v * k * v⁻¹ = (k : G)⁻¹ := eq_inv_of_mul_eq_one_right hk
    have h2 : (k : G)⁻¹ ∈ K₂ := h1 ▸ hvK k k.2
    rcases hd.inter _ (K₁.inv_mem k.2) h2 with h | h
    · left; exact inv_eq_one.1 h
    · right
      calc (k : G) = (k : G)⁻¹⁻¹ := by rw [inv_inv]
        _ = z⁻¹ := by rw [h]
        _ = z := inv_eq_of_mul_eq_one_right hE.sq_eq
  have hzK : φ ⟨z, hd.z1⟩ = 1 := by
    rw [hφ]
    show z * (v * z * v⁻¹) = 1
    rw [hvz, mul_inv_cancel_right, hE.sq_eq]
  have hkercard : Nat.card ↥φ.ker = 2 := by
    have hle : Nat.card ↥φ.ker ≤ 2 := card_le_two_of_forall (z := (⟨z, hd.z1⟩ : ↥K₁))
      (fun k hk => by
        rcases hker k hk with h | h
        · left; exact Subtype.ext h
        · right; exact Subtype.ext h)
    have hne : φ.ker ≠ ⊥ := by
      intro h
      have : (⟨z, hd.z1⟩ : ↥K₁) ∈ φ.ker := hzK
      rw [h, Subgroup.mem_bot] at this
      exact hE.ne_one (congrArg Subtype.val this)
    have hlt := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    omega
  have hrange : Nat.card ↥φ.range = 4 := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hkercard, hd.card1] at h1
    omega
  have hzR : z ∉ φ.range := by
    rintro ⟨k, hk⟩
    rw [hφ] at hk
    have h1 : v * k * v⁻¹ = (k : G)⁻¹ * z := by
      calc v * k * v⁻¹ = (k : G)⁻¹ * ((k : G) * (v * k * v⁻¹)) := by group
        _ = (k : G)⁻¹ * z := by rw [hk]
    have h2 : (k : G)⁻¹ * z ∈ K₂ := h1 ▸ hvK k k.2
    rcases hd.inter _ (K₁.mul_mem (K₁.inv_mem k.2) hd.z1) h2 with h | h
    ·
      have hkz : (k : G) = z := inv_mul_eq_one.1 h
      rw [hkz, hvz, mul_inv_cancel_right, hE.sq_eq] at hk
      exact hE.ne_one hk.symm
    ·
      have hk1 : (k : G) = 1 := inv_eq_one.1 (mul_eq_right.1 h)
      rw [hk1] at hk
      simp at hk
      exact hE.ne_one hk.symm
  have hRC : φ.range ≤ C := by rintro _ ⟨k, rfl⟩; exact hφC k
  have hzC : z ∈ C := (hmemC z).2 ⟨hE.mem, hvz.symm⟩
  have hRzC : φ.range ⊔ zpowers z ≤ C := sup_le hRC ((Subgroup.zpowers_le).2 hzC)
  have hinf : Nat.card ↥(φ.range ⊓ zpowers z) = 1 := by
    have hle : φ.range ⊓ zpowers z ≤ zpowers z := inf_le_right
    have hzo : orderOf z = 2 := hyp.orderTwo
    have hdvd : Nat.card ↥(φ.range ⊓ zpowers z) ∣ 2 := by
      rw [← hzo, ← Nat.card_zpowers]; exact Subgroup.card_dvd_of_le hle
    have hne : Nat.card ↥(φ.range ⊓ zpowers z) ≠ 2 := by
      intro h
      have heq : φ.range ⊓ zpowers z = zpowers z :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h, Nat.card_zpowers, hzo])
      exact hzR (by
        have : z ∈ φ.range ⊓ zpowers z := by rw [heq]; exact Subgroup.mem_zpowers z
        exact this.1)
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card ↥(φ.range ⊓ zpowers z) <;> simp_all
  have hC8 : Nat.card ↥C = 8 := by
    apply le_antisymm
    · have hi : Nat.card ↥(K₁ ⊓ C) ≤ 2 :=
        card_le_two_of_forall (fun k hk => hK1C k hk.1 hk.2)
      have := card_mul_card_le_inf hd.le1 (inf_le_left : C ≤ ascQ z)
      rw [hd.card1, hE.card_eq] at this
      nlinarith
    · have h1 := card_mul_card_le_sup φ.range (zpowers z)
      rw [hrange, Nat.card_zpowers, hyp.orderTwo, hinf] at h1
      have h2 := Subgroup.card_le_of_le hRzC
      omega
  have hCeq : φ.range ⊔ zpowers z = C := by
    apply Subgroup.eq_of_le_of_card_ge hRzC
    have h1 := card_mul_card_le_sup φ.range (zpowers z)
    rw [hrange, Nat.card_zpowers, hyp.orderTwo, hinf] at h1
    omega
  have hgen : φ.range ⊔ zpowers z = Subgroup.closure ((φ.range : Set G) ∪ {z}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  have hsq : ∀ k : ↥K₁, φ k * φ k = 1 := by
    intro k
    rw [hφ]
    have hc := hd.comm k k.2 _ (hvK k k.2)
    have hvkk : v * k * v⁻¹ * (v * k * v⁻¹) = (k : G) * k := by
      calc v * k * v⁻¹ * (v * k * v⁻¹) = v * ((k : G) * k) * v⁻¹ := by group
        _ = (k : G) * k := by
          rcases hkk k k.2 with h | h
          · rw [h]; group
          · rw [h, hvz, mul_inv_cancel_right]
    calc (k : G) * (v * k * v⁻¹) * ((k : G) * (v * k * v⁻¹)) =
        (k : G) * ((v * k * v⁻¹) * k) * (v * k * v⁻¹) := by group
      _ = (k : G) * (k * (v * k * v⁻¹)) * (v * k * v⁻¹) := by rw [hc]
      _ = ((k : G) * k) * (v * k * v⁻¹ * (v * k * v⁻¹)) := by group
      _ = 1 := by
        rw [hvkk]
        rcases hkk k k.2 with h | h
        · rw [h, one_mul]
        · rw [h, hE.sq_eq]
  have hcommR : ∀ a ∈ φ.range, ∀ b ∈ φ.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    rcases hE.comm_mem a (hd.le1 a.2) b (hd.le1 b.2) with h | h
    · congr 1
      apply Subtype.ext
      show (a : G) * b = b * a
      calc (a : G) * b = (a * b * (a : G)⁻¹ * (b : G)⁻¹) * (b * a) := by group
        _ = b * a := by rw [h, one_mul]
    · have hab : a * b = b * a * ⟨z, hd.z1⟩ := by
        apply Subtype.ext
        show (a : G) * b = b * a * z
        calc (a : G) * b = (a * b * (a : G)⁻¹ * (b : G)⁻¹) * (b * a) := by group
          _ = z * (b * a) := by rw [h]
          _ = b * a * z := (hE.central _ ((ascQ z).mul_mem (hd.le1 b.2) (hd.le1 a.2))).symm
      rw [hab, map_mul, hzK, mul_one]
  have hT : ∀ a ∈ (φ.range : Set G) ∪ {z}, ∀ b ∈ (φ.range : Set G) ∪ {z}, a * b = b * a := by
    rintro a (ha | ha) b (hb | hb)
    · exact hcommR a ha b hb
    · rw [Set.mem_singleton_iff.1 hb]; exact hE.central a (hRC ha).1
    · rw [Set.mem_singleton_iff.1 ha]; exact (hE.central b (hRC hb).1).symm
    · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
  have hT2 : ∀ a ∈ (φ.range : Set G) ∪ {z}, a * a = 1 := by
    rintro a (⟨k, rfl⟩ | ha)
    · exact hsq k
    · rw [Set.mem_singleton_iff.1 ha]; exact hE.sq_eq
  have he := closure_elem hT hT2
  refine ⟨hC8, ?_⟩
  rw [← hCeq, hgen]
  exact he

theorem a8_local [Finite G] (hyp : Asc03Hyp G z)
    (hA8 : ¬ ∃ K ∈ q8Subgroups (CFSG.pCore 2 ↥(ascH z)), K.Normal)
    {g : G} (hgz : g * z * g⁻¹ ≠ z) (hsQ : g * z * g⁻¹ ∈ ascQ z) :
    (∀ h ∈ ascH z, ∀ e ∈ ascE z g, h * e * h⁻¹ ∈ ascE z g) ∧
    ∃ v₀ : G, v₀ ∈ ascH z ∧ v₀ ∉ ascQ z ∧ orderOf v₀ = 2 ∧
      ∃ K : Subgroup G, ascE z g ⊓ K = ⊥ ∧ ascE z g ⊔ K = ascQ z ⊔ zpowers v₀ := by
  have hE := extraspecialAt_ascQ hyp
  obtain ⟨hzQg', hE8, hEe, -, v₀, hv₀, hv₀o, hv₀Q⟩ := config_of_conj hyp hgz hsQ
  have hEg : ExtraspecialAt ((ascQ z).map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) := hE.conj g
  set s := g * z * g⁻¹ with hs
  set Qg := (ascQ z).map (MulAut.conj g).toMonoidHom with hQg
  set E := ascE z g with hEset
  have hE8' : Nat.card ↥E = 8 := hE8
  have hEe' : ∀ a ∈ E, ∀ b ∈ E, a * a = 1 ∧ a * b = b * a :=
    fun a ha b hb => ⟨(hEe a ha).1, (hEe a ha).2 b hb⟩
  have hv₀H : v₀ ∈ ascH z := hv₀.1
  have hv₀Qg : v₀ ∈ Qg := hv₀.2
  have hv₀2 : v₀ * v₀ = 1 := by
    have := pow_orderOf_eq_one v₀; rwa [hv₀o, pow_two] at this
  have hv₀inv : v₀⁻¹ = v₀ := inv_eq_of_mul_eq_one_right hv₀2
  have hzQg : z ∈ Qg := (mem_map_conj_iff _ g z).2 hzQg'
  have hzE : z ∈ E := ⟨hE.mem, hzQg⟩
  have hsE : s ∈ E := ⟨hsQ, hEg.mem⟩
  have hEQ : E ≤ ascQ z := inf_le_left
  have hEQg : E ≤ Qg := inf_le_right
  have hs1 : s ≠ 1 := hEg.ne_one
  have hs2 : s * s = 1 := hEg.sq_eq
  have hvz : v₀ * z * v₀⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hv₀H
    calc v₀ * z * v₀⁻¹ = z * v₀ * v₀⁻¹ := by rw [this]
      _ = z := by group
  obtain ⟨y, hyH, hy3, hvy⟩ := exists_inverted_three hyp hv₀H hv₀Q hv₀2
  obtain ⟨K₁, K₂, hd⟩ := exists_q8Data hyp hyH hy3
  have hK := conj_eq_K₂ hyp hd hyH hy3 hA8 hv₀H hv₀Q hv₀2
  obtain ⟨hC8, hCe⟩ := cent_inv_facts hyp hd hv₀H hv₀2 hK
  set C := ascQ z ⊓ centralizer ({v₀} : Set G) with hCdef
  have hCQ : C ≤ ascQ z := inf_le_left
  have hmemC : ∀ x : G, x ∈ C ↔ x ∈ ascQ z ∧ x * v₀ = v₀ * x := by
    intro x
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hsC : s ∈ C := (hmemC s).2 ⟨hsQ, (hEg.central v₀ hv₀Qg).symm⟩
  have hEC : E ≠ C := by
    intro h
    have hvc : ∀ e ∈ E, e * v₀ = v₀ * e := fun e he => ((hmemC e).1 (h ▸ he)).2
    have hS : ∀ a ∈ (E : Set G) ∪ {v₀}, ∀ b ∈ (E : Set G) ∪ {v₀}, a * b = b * a := by
      rintro a (ha | ha) b (hb | hb)
      · exact (hEe' a ha b hb).2
      · rw [Set.mem_singleton_iff.1 hb]; exact hvc a ha
      · rw [Set.mem_singleton_iff.1 ha]; exact (hvc b hb).symm
      · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]
    have hcl := Subgroup.isMulCommutative_closure (k := (E : Set G) ∪ {v₀})
      (fun u hu w hw _ => hS u hu w hw)
    set B := Subgroup.closure ((E : Set G) ∪ {v₀}) with hB
    have hBab : ∀ u ∈ B, ∀ w ∈ B, u * w = w * u := by
      intro u hu w hw
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨u, hu⟩ : B) ⟨w, hw⟩)
    have hBQg : B ≤ Qg := (Subgroup.closure_le _).2
      (Set.union_subset (fun x hx => hEQg hx) (Set.singleton_subset_iff.2 hv₀Qg))
    have hv₀E : v₀ ∉ E := fun h => hv₀Q h.1
    have hlt : E < B := lt_of_le_of_ne (fun x hx => Subgroup.subset_closure (Or.inl hx))
      (fun h => hv₀E (h ▸ Subgroup.subset_closure (Or.inr rfl)))
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := hEg.card_abelian_le hBQg hBab
    omega
  have hCy : ¬ ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
    intro hinv
    have h1 : v₀ * y⁻¹ * v₀⁻¹ = y := by
      calc v₀ * y⁻¹ * v₀⁻¹ = (v₀ * y * v₀⁻¹)⁻¹ := by group
        _ = y := by rw [hvy, inv_inv]
    have hvy' : y * v₀ * y⁻¹ = y * y * v₀ := by
      calc y * v₀ * y⁻¹ = y * (v₀ * y⁻¹ * v₀⁻¹) * v₀ := by group
        _ = y * y * v₀ := by rw [h1]
    have hyyy := mul_self_mul_self_eq_one hy3
    have hy4 : (y * y) * (y * y) = y := by
      calc (y * y) * (y * y) = (y * y * y) * y := by group
        _ = y := by rw [hyyy, one_mul]
    have hyc : ∀ c ∈ C, c * y = y * c := by
      intro c hc
      have hc' : y⁻¹ * c * y ∈ C := inv_conj_mem hy3 hinv hc
      have h1 : (y⁻¹ * c * y) * v₀ = v₀ * (y⁻¹ * c * y) := ((hmemC _).1 hc').2
      have h2 : c * v₀ = v₀ * c := ((hmemC c).1 hc).2
      have h3 : c * (y * v₀ * y⁻¹) = (y * v₀ * y⁻¹) * c := by
        calc c * (y * v₀ * y⁻¹) = y * ((y⁻¹ * c * y) * v₀) * y⁻¹ := by group
          _ = y * (v₀ * (y⁻¹ * c * y)) * y⁻¹ := by rw [h1]
          _ = (y * v₀ * y⁻¹) * c := by group
      rw [hvy'] at h3
      have h4 : c * (y * y) = (y * y) * c := by
        calc c * (y * y) = c * (y * y * v₀) * v₀⁻¹ := by group
          _ = (y * y * v₀) * c * v₀⁻¹ := by rw [h3]
          _ = y * y * (v₀ * c) * v₀⁻¹ := by group
          _ = y * y * (c * v₀) * v₀⁻¹ := by rw [h2]
          _ = (y * y) * c := by group
      calc c * y = c * ((y * y) * (y * y)) := by rw [hy4]
        _ = (c * (y * y)) * (y * y) := by group
        _ = ((y * y) * c) * (y * y) := by rw [h4]
        _ = (y * y) * (c * (y * y)) := by group
        _ = (y * y) * ((y * y) * c) := by rw [h4]
        _ = ((y * y) * (y * y)) * c := by group
        _ = y * c := by rw [hy4]
    have hall : ∀ c ∈ C, c = 1 ∨ c = z := fun c hc =>
      cent_of_order_three hyp hyH hy3 (hCQ hc) (hyc c hc)
    have := card_le_two_of_forall hall
    omega
  obtain ⟨hLQ, hL8, hLe, hzL, hsL, -, hLy⟩ := lineOf_facts hyp hyH hy3 hsQ hs2 hs1 hgz
  have hEL : E = lineOf z s y := by
    rcases eq_or_eq_of_three hE hsQ hs2 hs1 hgz hEQ hCQ hLQ hE8' hC8 hL8 hEe' hCe hLe hsE hsC
      hsL with h | h | h
    · exact absurd h hEC
    · exact h
    · exact absurd (h ▸ hLy) hCy
  have hEy : ∀ e ∈ E, y * e * y⁻¹ ∈ E := by rw [hEL]; exact hLy
  have hEv : ∀ e ∈ E, v₀ * e * v₀⁻¹ ∈ E := fun e he =>
    ⟨conj_mem_ascQ hv₀H he.1, Qg.mul_mem (Qg.mul_mem hv₀Qg he.2) (Qg.inv_mem hv₀Qg)⟩
  have hEH : ∀ h ∈ ascH z, ∀ e ∈ E, h * e * h⁻¹ ∈ E := by
    have hN := ascH_le_of_gens hyp (N := normalizer (E : Set G))
      (fun q hq => mem_normalizer_of_conj fun e he => conj_mem_of_z_mem hE hEQ hzE hq he)
      hyH hy3 (mem_normalizer_of_conj hEy) hv₀H hv₀Q hv₀2 (mem_normalizer_of_conj hEv)
    intro h hh e he
    exact (Subgroup.mem_normalizer_iff.1 (hN hh) e).1 he
  refine ⟨hEH, v₀, hv₀H, hv₀Q, hv₀o, ?_⟩
  have hCE : ¬ C ≤ E := fun hle =>
    hEC (Subgroup.eq_of_le_of_card_ge hle (by rw [hE8', hC8])).symm
  obtain ⟨t, htC, htE⟩ := IsConcreteLE.not_le_iff_exists.1 hCE
  have htQ := hCQ htC
  have ht2 : t * t = 1 := (hCe t htC t htC).1
  have ht1 : t ≠ 1 := fun h => htE (h ▸ E.one_mem)
  have htz : t ≠ z := fun h => htE (h ▸ hzE)
  obtain ⟨hFQ, hF8, hFe, hzF, htF, -, hFy⟩ := lineOf_facts hyp hyH hy3 htQ ht2 ht1 htz
  have hvt : v₀ * t * v₀⁻¹ = t := by
    have := ((hmemC t).1 htC).2
    calc v₀ * t * v₀⁻¹ = t * v₀ * v₀⁻¹ := by rw [this]
      _ = t := by group
  have hFv : ∀ f ∈ lineOf z t y, v₀ * f * v₀⁻¹ ∈ lineOf z t y := by
    intro f hf
    induction hf using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rw [hvz]; exact hzF
      · rw [hvt]; exact htF
      · have : v₀ * (y * t * y⁻¹) * v₀⁻¹ = y⁻¹ * t * y := by
          calc v₀ * (y * t * y⁻¹) * v₀⁻¹ =
              (v₀ * y * v₀⁻¹) * (v₀ * t * v₀⁻¹) * (v₀ * y * v₀⁻¹)⁻¹ := by group
            _ = y⁻¹ * t * y := by rw [hvy, hvt, inv_inv]
        rw [this]; exact inv_conj_mem hy3 hFy htF
    | one => simp
    | mul a b _ _ iha ihb =>
      have : v₀ * (a * b) * v₀⁻¹ = (v₀ * a * v₀⁻¹) * (v₀ * b * v₀⁻¹) := by group
      rw [this]; exact mul_mem iha ihb
    | inv a _ iha =>
      have : v₀ * a⁻¹ * v₀⁻¹ = (v₀ * a * v₀⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem iha
  have hFEy : ∀ x ∈ lineOf z t y ⊓ E, y * x * y⁻¹ ∈ lineOf z t y ⊓ E :=
    fun x hx => ⟨hFy x hx.1, hEy x hx.2⟩
  have hFE2 : Nat.card ↥(lineOf z t y ⊓ E) = 2 := by
    rcases card_of_inv hyp hyH hy3 (inf_le_right.trans hEQ) ⟨hzF, hzE⟩ hFEy with h | h | h
    · exact h
    · exfalso
      have heq : lineOf z t y ⊓ E = lineOf z t y :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hF8])
      have : t ∈ lineOf z t y ⊓ E := by rw [heq]; exact htF
      exact htE this.2
    · exfalso
      have := Subgroup.card_le_of_le (inf_le_left : lineOf z t y ⊓ E ≤ lineOf z t y)
      omega
  have hFE : ∀ x ∈ lineOf z t y, x ∈ E → x = 1 ∨ x = z := by
    intro x hxF hxE
    have := eq_one_or_eq_of_card_two hFE2 (a := ⟨z, hzF, hzE⟩)
      (by intro h; exact hE.ne_one (congrArg Subtype.val h)) ⟨x, hxF, hxE⟩
    rcases this with h | h
    · left; exact congrArg Subtype.val h
    · right; exact congrArg Subtype.val h
  obtain ⟨A, hAF, hA4, hzA, hAv⟩ := exists_compl_four hyp hyH hy3 hFQ hF8 hFe hzF hFy
  have hAv₀ := hAv v₀ hFv hvy
  have hAv₀' : ∀ a ∈ A, v₀⁻¹ * a * v₀ ∈ A := by
    intro a ha
    have := hAv₀ a ha
    rw [hv₀inv] at this ⊢
    exact this
  let K : Subgroup G :=
    { carrier := {x | x ∈ A ∨ x * v₀ ∈ A}
      one_mem' := Or.inl A.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (A.mul_mem ha hb)
        · right; rw [mul_assoc]; exact A.mul_mem ha hb
        · right
          have : a * b * v₀ = (a * v₀) * (v₀⁻¹ * b * v₀) := by group
          rw [this]; exact A.mul_mem ha (hAv₀' b hb)
        · left
          have : a * b = (a * v₀) * (v₀⁻¹ * (b * v₀) * v₀⁻¹) := by group
          rw [this]
          refine A.mul_mem ha ?_
          have := hAv₀' _ hb
          rw [hv₀inv] at this ⊢
          exact this
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (A.inv_mem hx)
        · right
          have : x⁻¹ * v₀ = v₀⁻¹ * (x * v₀)⁻¹ * v₀ := by rw [hv₀inv]; group
          rw [this]; exact hAv₀' _ (A.inv_mem hx) }
  have hmemK : ∀ x : G, x ∈ K ↔ x ∈ A ∨ x * v₀ ∈ A := fun x => Iff.rfl
  have hAQ : A ≤ ascQ z := hAF.trans hFQ
  have hEK1 : E ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxE, hxK⟩
    rw [Subgroup.mem_bot]
    rcases (hmemK x).1 hxK with hx | hx
    · rcases hFE x (hAF hx) hxE with h | h
      · exact h
      · exact absurd (h ▸ hx) hzA
    · exfalso
      apply hv₀Q
      have : v₀ = x⁻¹ * (x * v₀) := by group
      rw [this]
      exact (ascQ z).mul_mem ((ascQ z).inv_mem (hEQ hxE)) (hAQ hx)
  obtain ⟨-, -, hT64⟩ := sup_zpowers_facts hyp hv₀H hv₀Q hv₀o
  have hKT : K ≤ ascQ z ⊔ zpowers v₀ := by
    intro x hx
    rcases (hmemK x).1 hx with hx | hx
    · exact le_sup_left (a := ascQ z) (hAQ hx)
    · have : x = (x * v₀) * v₀⁻¹ := by group
      rw [this]
      exact mul_mem (le_sup_left (a := ascQ z) (hAQ hx))
        (inv_mem (le_sup_right (a := ascQ z) (Subgroup.mem_zpowers v₀)))
  have hET : E ≤ ascQ z ⊔ zpowers v₀ := hEQ.trans le_sup_left
  have hK8 : 8 ≤ Nat.card ↥K := by
    have hAK : A ≤ K := fun x hx => Or.inl hx
    have hv₀K : v₀ ∈ K := Or.inr (by rw [hv₀2]; exact A.one_mem)
    have hv₀A : v₀ ∉ A := fun h => hv₀Q (hAQ h)
    have hlt : A < K := lt_of_le_of_ne hAK (fun h => hv₀A (h ▸ hv₀K))
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 : Nat.card ↥A ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hAK
    rw [hA4] at h1 h2
    obtain ⟨k, hk⟩ := h2
    omega
  refine ⟨K, hEK1, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge (sup_le hET hKT)
  have h1 := card_mul_card_le_sup E K
  rw [hEK1, Subgroup.card_bot, mul_one, hE8'] at h1
  rw [hT64]
  omega

end CFSG.GH74.M12.Thm1
