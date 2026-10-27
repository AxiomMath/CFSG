module

public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open Subgroup
open scoped commutatorElement

theorem i271on_conj_injective {G : Type*} [Group G] (hc : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  have : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun φ : MulAut G => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rwa [hc, Subgroup.mem_bot] at this

theorem i271on_alt6_simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem i271on_alt6_nonabelian : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  have h1 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have h2 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 3 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have hne : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 * (Equiv.swap 0 1 * Equiv.swap 1 3) ≠
      Equiv.swap 0 1 * Equiv.swap 1 3 * (Equiv.swap 0 1 * Equiv.swap 1 2) := by decide
  exact ⟨⟨_, h1⟩, ⟨_, h2⟩, fun h => hne (congrArg Subtype.val h)⟩

theorem i271on_card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

section AltSix

variable {H : Type*} [Group H]

theorem i271on_alt_simple (e : H ≃* alternatingGroup (Fin 6)) : IsSimpleGroup H :=
  haveI := i271on_alt6_simple
  e.isSimpleGroup

theorem i271on_alt_card (e : H ≃* alternatingGroup (Fin 6)) : Nat.card H = 360 := by
  rw [Nat.card_congr e.toEquiv, i271on_card_alt6]

theorem i271on_alt_center (e : H ≃* alternatingGroup (Fin 6)) : Subgroup.center H = ⊥ := by
  haveI := i271on_alt_simple e
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := i271on_alt6_nonabelian
    apply hab
    have h1 : e.symm a ∈ Subgroup.center H := by rw [h]; exact Subgroup.mem_top _
    have h2 := Subgroup.mem_center_iff.1 h1 (e.symm b)
    have h3 := congrArg e h2
    simp only [map_mul, MulEquiv.apply_symm_apply] at h3
    exact h3.symm

theorem i271on_balanceH (e : H ≃* alternatingGroup (Fin 6)) {E : Subgroup H}
    (hE : IsElemAbelian 3 E) (hE9 : 9 ≤ Nat.card E) {T : Subgroup (MulAut H)}
    (hT : Nat.Coprime 3 (Nat.card T))
    (hET : ∀ g ∈ E, (MulAut.conj g : MulAut H) ∈ Subgroup.normalizer (T : Set (MulAut H))) :
    T = ⊥ := by
  have hinj := i271on_conj_injective (i271on_alt_center e)
  let c := MulAut.congr e
  let A' : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
    (E.map (MulAut.conj : H →* MulAut H)).map c.toMonoidHom
  let T' : Subgroup (MulAut (alternatingGroup (Fin 6))) := T.map c.toMonoidHom
  have hA'ab : IsElemAbelian 3 A' :=
    CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.map hE _) _
  have hcardE : Nat.card (E.map (MulAut.conj : H →* MulAut H)) = Nat.card E :=
    Subgroup.card_map_of_injective hinj
  have hA'card : 3 ^ 2 ≤ Nat.card A' := by
    have : Nat.card A' = Nat.card E := by
      rw [Subgroup.card_map_of_injective c.injective, hcardE]
    rw [this]
    simpa using hE9
  have hT'card : Nat.card T' = Nat.card T := Subgroup.card_map_of_injective c.injective
  have hAT' : A' ≤ Subgroup.normalizer (T' : Set (MulAut (alternatingGroup (Fin 6)))) := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro t'
    have hg' := Subgroup.mem_normalizer_iff.1 (hET g hg)
    have key : ∀ s : MulAut H, c.toMonoidHom (MulAut.conj g) * c.toMonoidHom s *
        (c.toMonoidHom (MulAut.conj g))⁻¹ =
          c.toMonoidHom (MulAut.conj g * s * (MulAut.conj g)⁻¹) := by
      intro s
      simp only [map_mul, map_inv]
    obtain ⟨s, rfl⟩ := c.surjective t'
    show c s ∈ T' ↔ _
    have e1 : c s ∈ T' ↔ s ∈ T := by
      constructor
      · rintro ⟨s', hs', hss'⟩
        have : s' = s := c.injective hss'
        rwa [this] at hs'
      · intro hs
        exact ⟨s, hs, rfl⟩
    have e2 : c.toMonoidHom (MulAut.conj g) * c s * (c.toMonoidHom (MulAut.conj g))⁻¹ ∈ T' ↔
        MulAut.conj g * s * (MulAut.conj g)⁻¹ ∈ T := by
      rw [show c s = c.toMonoidHom s from rfl, key s]
      constructor
      · rintro ⟨s', hs', hss'⟩
        have : s' = MulAut.conj g * s * (MulAut.conj g)⁻¹ := c.injective hss'
        rwa [this] at hs'
      · intro hs
        exact ⟨_, hs, rfl⟩
    rw [e1, e2]
    exact hg' s
  have hT'bot := i271AutBalanceAltSix_holds A' hA'ab hA'card T' (by rwa [hT'card]) hAT'
  rw [eq_bot_iff]
  intro t ht
  have : c.toMonoidHom t ∈ T' := ⟨t, ht, rfl⟩
  rw [hT'bot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact c.injective (by simpa using this)

theorem i271on_closure_threePrime (e : H ≃* alternatingGroup (Fin 6)) :
    Subgroup.closure {h : H | Nat.Coprime 3 (orderOf h)} = ⊤ := by
  haveI := i271on_alt_simple e
  have h360 := i271on_alt_card e
  haveI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [h360]; norm_num : 2 ∣ Nat.card H)
  have hg1 : g ≠ 1 := fun h => by simp [h] at hg
  have hN : Subgroup.normalClosure ({g} : Set H) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({g} : Set H))
      with h | h
    · exfalso
      have : g ∈ Subgroup.normalClosure ({g} : Set H) := Subgroup.subset_normalClosure rfl
      rw [h, Subgroup.mem_bot] at this
      exact hg1 this
    · exact h
  rw [eq_top_iff, ← hN]
  refine Subgroup.closure_mono ?_
  intro y hy
  obtain ⟨b, hb, hbc⟩ := Group.mem_conjugatesOfSet_iff.1 hy
  rw [Set.mem_singleton_iff] at hb
  subst hb
  obtain ⟨c, hc⟩ := isConj_iff.1 hbc
  show Nat.Coprime 3 (orderOf y)
  have : orderOf y = 2 := by
    rw [← hc, ← hg]
    exact (MulEquiv.orderOf_eq (MulAut.conj c) b)
  rw [this]
  norm_num

end AltSix

section Restrict

variable {S : Type*} [Group S]

@[expose] def i271onStab (H : Subgroup S) : Subgroup (MulAut S) where
  carrier := {σ | ∀ x, σ x ∈ H ↔ x ∈ H}
  mul_mem' := by
    intro σ τ hσ hτ x
    rw [MulAut.mul_apply, hσ, hτ]
  one_mem' := by
    intro x
    rfl
  inv_mem' := by
    intro σ hσ x
    rw [← hσ ((σ⁻¹) x)]
    simp

theorem i271onStab_mem {H : Subgroup S} {σ : MulAut S} :
    σ ∈ i271onStab H ↔ ∀ x, σ x ∈ H ↔ x ∈ H := Iff.rfl

@[expose] def i271onRes (H : Subgroup S) : ↥(i271onStab H) →* MulAut ↥H where
  toFun σ :=
    { toFun := fun x => ⟨(σ : MulAut S) x, ((i271onStab_mem.1 σ.2) x).2 x.2⟩
      invFun := fun x => ⟨(σ : MulAut S)⁻¹ x,
        ((i271onStab_mem.1 ((i271onStab H).inv_mem σ.2)) x).2 x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun x => by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp }
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

theorem i271onRes_apply (H : Subgroup S) (σ : ↥(i271onStab H)) (x : ↥H) :
    ((i271onRes H σ x : ↥H) : S) = (σ : MulAut S) (x : S) := rfl

theorem i271on_conj_mem_stab (H : Subgroup S) {h : S} (hh : h ∈ H) :
    (MulAut.conj h : MulAut S) ∈ i271onStab H := by
  intro x
  rw [MulAut.conj_apply]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)

theorem i271onRes_conj (H : Subgroup S) {h : S} (hh : h ∈ H) :
    i271onRes H ⟨MulAut.conj h, i271on_conj_mem_stab H hh⟩ = MulAut.conj (⟨h, hh⟩ : ↥H) := by
  ext x
  rfl

@[expose] def i271onFix (σ : MulAut S) : Subgroup S where
  carrier := {y | σ y = y}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := map_one σ
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

end Restrict

section Comm

variable {G : Type*} [Group G]

@[expose] def i271onCommHom {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) (a : G) (U : Subgroup G)
    (hU : ∀ m ∈ U, ⁅m, a⁆ ∈ Z) : ↥U →* ↥Z where
  toFun m := ⟨⁅(m : G), a⁆, hU m m.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' m₁ m₂ := by
    apply Subtype.ext
    have hw : ∀ g, g * ⁅(m₂ : G), a⁆ = ⁅(m₂ : G), a⁆ * g := fun g =>
      Subgroup.mem_center_iff.1 (hZ (hU m₂ m₂.2)) g
    have hw1 : ∀ g, g * ⁅(m₁ : G), a⁆ = ⁅(m₁ : G), a⁆ * g := fun g =>
      Subgroup.mem_center_iff.1 (hZ (hU m₁ m₁.2)) g
    show ⁅((m₁ : G) * (m₂ : G)), a⁆ = ⁅(m₁ : G), a⁆ * ⁅(m₂ : G), a⁆
    calc ⁅((m₁ : G) * (m₂ : G)), a⁆
        = (m₁ : G) * ⁅(m₂ : G), a⁆ * (a * (m₁ : G)⁻¹ * a⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = ⁅(m₂ : G), a⁆ * (m₁ : G) * (a * (m₁ : G)⁻¹ * a⁻¹) := by rw [hw (m₁ : G)]
      _ = ⁅(m₂ : G), a⁆ * ⁅(m₁ : G), a⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅(m₁ : G), a⁆ * ⁅(m₂ : G), a⁆ := hw1 _

theorem i271onCommHom_apply {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) (a : G) (U : Subgroup G)
    (hU : ∀ m ∈ U, ⁅m, a⁆ ∈ Z) (m : ↥U) : ((i271onCommHom hZ a U hU m : ↥Z) : G) = ⁅(m : G), a⁆ :=
  rfl

theorem i271on_card_le_comm [Finite G] {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) (a : G)
    (U : Subgroup G) (hU : ∀ m ∈ U, ⁅m, a⁆ ∈ Z) :
    Nat.card U ≤ Nat.card Z * Nat.card ↥(U ⊓ Subgroup.centralizer ({a} : Set G)) := by
  let φ := i271onCommHom hZ a U hU
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.range ≤ Nat.card Z := Subgroup.card_le_card_group φ.range
  have h3 : Nat.card φ.ker ≤ Nat.card ↥(U ⊓ Subgroup.centralizer ({a} : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun m => (⟨(m.1 : G), Subgroup.mem_inf.2 ⟨m.1.2, ?_⟩⟩ :
        ↥(U ⊓ Subgroup.centralizer ({a} : Set G)))) ?_
    · have hm : φ m.1 = 1 := m.2
      have := congrArg Subtype.val hm
      rw [i271onCommHom_apply] at this
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commutatorElement_eq_one_iff_mul_comm.1 (by simpa using this)
    · intro m₁ m₂ h
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      exact h'
  calc Nat.card U = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ Nat.card ↥(U ⊓ Subgroup.centralizer ({a} : Set G)) * Nat.card Z :=
        Nat.mul_le_mul h3 h2
    _ = _ := mul_comm _ _

end Comm

section SupZpowers

variable {G : Type*} [Group G]

theorem i271on_mem_sup_zpowers {a : G} {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({a} : Set G)) {m : G} (hm : m ∈ Subgroup.zpowers a ⊔ K) :
    ∃ i : ℤ, ∃ k ∈ K, m = a ^ i * k := by
  have hcomm : ∀ k ∈ K, ∀ j : ℤ, a ^ j * k = k * a ^ j := by
    intro k hk j
    have h : k * a = a * k := Subgroup.mem_centralizer_singleton_iff.1 (hK hk)
    exact ((show Commute k a from h).zpow_right j).eq.symm
  let Q : Subgroup G :=
    { carrier := {m | ∃ i : ℤ, ∃ k ∈ K, m = a ^ i * k}
      mul_mem' := by
        rintro _ _ ⟨i, k, hk, rfl⟩ ⟨j, l, hl, rfl⟩
        refine ⟨i + j, k * l, K.mul_mem hk hl, ?_⟩
        rw [zpow_add]
        calc a ^ i * k * (a ^ j * l) = a ^ i * (k * a ^ j) * l := by group
          _ = a ^ i * (a ^ j * k) * l := by rw [hcomm k hk j]
          _ = a ^ i * a ^ j * (k * l) := by group
      one_mem' := ⟨0, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, k, hk, rfl⟩
        refine ⟨-i, k⁻¹, K.inv_mem hk, ?_⟩
        rw [mul_inv_rev, zpow_neg]
        have h := hcomm k⁻¹ (K.inv_mem hk) (-i)
        rw [zpow_neg] at h
        exact h.symm }
  have hle : Subgroup.zpowers a ⊔ K ≤ Q := by
    refine sup_le ?_ ?_
    · rintro _ ⟨j, rfl⟩
      exact ⟨j, 1, K.one_mem, by simp⟩
    · intro k hk
      exact ⟨0, k, hk, by simp⟩
  exact hle hm

theorem i271on_mem_sup_fin3 {a : G} (ha : a ^ 3 = 1) {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({a} : Set G)) {m : G} (hm : m ∈ Subgroup.zpowers a ⊔ K) :
    ∃ i : Fin 3, ∃ k ∈ K, m = a ^ (i : ℕ) * k := by
  obtain ⟨j, k, hk, rfl⟩ := i271on_mem_sup_zpowers hK hm
  refine ⟨⟨(j % 3).toNat, ?_⟩, k, hk, ?_⟩
  · have h0 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
    have h1 : j % 3 < 3 := Int.emod_lt_of_pos j (by norm_num)
    omega
  · congr 1
    have h0 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
    have hz : a ^ (3 : ℤ) = 1 := by simpa using ha
    have e1 : a ^ ((j % 3).toNat : ℕ) = a ^ (j % 3) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg h0]
    rw [e1]
    conv_lhs => rw [← Int.emod_add_mul_ediv j 3]
    rw [zpow_add, zpow_mul, hz, one_zpow, mul_one]

theorem i271on_card_inf_le [Finite G] {a : G} (ha : a ^ 3 = 1) {K P : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({a} : Set G)) (haP : a ∈ P) :
    Nat.card ↥(P ⊓ (Subgroup.zpowers a ⊔ K)) ≤ 3 * Nat.card ↥(K ⊓ P) := by
  let f : Fin 3 × ↥(K ⊓ P) → ↥(P ⊓ (Subgroup.zpowers a ⊔ K)) := fun p =>
    ⟨a ^ (p.1 : ℕ) * (p.2 : G), Subgroup.mem_inf.2 ⟨P.mul_mem (P.pow_mem haP _)
      (Subgroup.mem_inf.1 p.2.2).2,
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _))
        (Subgroup.mem_sup_right (Subgroup.mem_inf.1 p.2.2).1)⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨m, hmP, hm⟩
    obtain ⟨i, k, hk, rfl⟩ := i271on_mem_sup_fin3 ha hK hm
    refine ⟨(i, ⟨k, Subgroup.mem_inf.2 ⟨hk, ?_⟩⟩), rfl⟩
    have : k = (a ^ (i : ℕ))⁻¹ * (a ^ (i : ℕ) * k) := by group
    rw [this]
    exact P.mul_mem (P.inv_mem (P.pow_mem haP _)) hmP
  have := Nat.card_le_card_of_surjective f hf
  simpa [Nat.card_prod, mul_comm] using this

theorem i271on_card_sup_le [Finite G] {a : G} (ha : a ^ 3 = 1) {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({a} : Set G)) :
    Nat.card ↥(Subgroup.zpowers a ⊔ K) ≤ 3 * Nat.card K := by
  simpa using i271on_card_inf_le ha hK (Subgroup.mem_top a)

end SupZpowers

end CFSG.HardMathSupport.Solomon.Coordinator
