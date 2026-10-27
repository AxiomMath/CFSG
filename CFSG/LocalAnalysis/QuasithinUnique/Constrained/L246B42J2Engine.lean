module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeGen

public section

namespace CFSG.QuasithinUnique.Bridge.J2Excl

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family

section Gen

variable {G : Type*} [Group G]

theorem closure_conjSet_mono {cs : List G} {T T' : Set G} (h : ∀ t ∈ T, t ∈ Subgroup.closure T') :
    Subgroup.closure (conjSet cs T) ≤ Subgroup.closure (conjSet cs T') := by
  rw [Subgroup.closure_le]
  rintro _ ⟨c, hc, t, ht, rfl⟩
  have h1 : c * t * c⁻¹ ∈ (Subgroup.closure T').map (MulAut.conj c).toMonoidHom :=
    ⟨t, h t ht, rfl⟩
  rw [MonoidHom.map_closure] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨t', ht', rfl⟩
  exact ⟨c, hc, t', ht', rfl⟩

@[expose] def GenSet (P : Subgroup G) (k : ℕ) (T : Set G) : Prop :=
  ∃ gs : List G, gs.length = k ∧ (∀ g ∈ gs, g ∈ P) ∧ P ≤ Subgroup.closure (conjSet gs T)

theorem GenSet.mono {P : Subgroup G} {k : ℕ} {T T' : Set G}
    (h : ∀ t ∈ T', t ∈ Subgroup.closure T) (hg : GenSet P k T') : GenSet P k T := by
  obtain ⟨gs, hlen, hgs, hle⟩ := hg
  exact ⟨gs, hlen, hgs, hle.trans (closure_conjSet_mono h)⟩

theorem GenSet.transfer {P : Subgroup G} {k : ℕ} {T T' : Set G} {s : G}
    (hs : ∀ p ∈ P, s * p * s⁻¹ ∈ P) (hs' : ∀ p ∈ P, s⁻¹ * p * s ∈ P)
    (hT : ∀ t' ∈ T', s⁻¹ * t' * s ∈ Subgroup.closure T) (hg : GenSet P k T') : GenSet P k T := by
  obtain ⟨gs, hlen, hgs, hle⟩ := hg
  refine ⟨gs.map (fun c => s⁻¹ * c * s), by simp [hlen], ?_, fun p hp => ?_⟩
  · intro g hg
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg
    exact hs' c (hgs c hc)
  · have hsp : s * p * s⁻¹ ∈ Subgroup.closure (conjSet gs T') := hle (hs p hp)
    have key : ∀ y ∈ Subgroup.closure (conjSet gs T'),
        s⁻¹ * y * s ∈ Subgroup.closure (conjSet (gs.map (fun c => s⁻¹ * c * s)) T) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨c, hc, t', ht', rfl⟩ := hy
        have h1 : (s⁻¹ * c * s) * (s⁻¹ * t' * s) * (s⁻¹ * c * s)⁻¹ ∈
            Subgroup.closure (conjSet (gs.map (fun c => s⁻¹ * c * s)) T) := by
          have h2 : (s⁻¹ * c * s) * (s⁻¹ * t' * s) * (s⁻¹ * c * s)⁻¹ ∈
              (Subgroup.closure T).map (MulAut.conj (s⁻¹ * c * s)).toMonoidHom :=
            ⟨s⁻¹ * t' * s, hT t' ht', rfl⟩
          rw [MonoidHom.map_closure] at h2
          refine Subgroup.closure_mono ?_ h2
          rintro _ ⟨t'', ht'', rfl⟩
          exact ⟨s⁻¹ * c * s, List.mem_map.2 ⟨c, hc, rfl⟩, t'', ht'', rfl⟩
        have e : s⁻¹ * (c * t' * c⁻¹) * s = (s⁻¹ * c * s) * (s⁻¹ * t' * s) * (s⁻¹ * c * s)⁻¹ := by
          group
        rw [e]
        exact h1
      | one => simp
      | mul a b _ _ ha hb =>
        have e : s⁻¹ * (a * b) * s = (s⁻¹ * a * s) * (s⁻¹ * b * s) := by group
        rw [e]
        exact Subgroup.mul_mem _ ha hb
      | inv a _ ha =>
        have e : s⁻¹ * a⁻¹ * s = (s⁻¹ * a * s)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ ha
    have := key _ hsp
    simpa [mul_assoc] using this

end Gen

section Trans

variable {G : Type*} [Group G] {S : Type*} [Group S]

theorem genSub_of_equiv {H A : Subgroup G} (hAH : A ≤ H) (Φ : ↥H ≃* MulAut S) (θ : S ≃* ↥A)
    (hΦ : ∀ s : S, Φ ⟨(θ s : G), hAH (θ s).2⟩ = MulAut.conj s) {ρ : ℕ}
    (hgen : ∀ B : Subgroup G, B ≤ H → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → B ≠ ⊥ → ∃ gs : List G, (∀ g ∈ gs, g ∈ A) ∧
        Nat.card B ^ gs.length < 2 ^ ρ ∧
        A ≤ Subgroup.closure {y | ∃ c ∈ gs, ∃ b ∈ B, y = c * b * c⁻¹}) :
    ∀ B' : Subgroup (MulAut S), (∀ x ∈ B', ∀ y ∈ B', x * y = y * x) → (∀ x ∈ B', x * x = 1) →
      B' ≠ ⊥ → ∃ cs : List (MulAut S), (∀ c ∈ cs, c ∈ (MulAut.conj : S →* MulAut S).range) ∧
        Nat.card B' ^ cs.length < 2 ^ ρ ∧
        ∀ s : S, MulAut.conj s ∈ Subgroup.closure {y | ∃ c ∈ cs, ∃ b ∈ B', y = c * b * c⁻¹} := by
  intro B' hcomm hsq hne
  set Bh : Subgroup ↥H := B'.comap Φ.toMonoidHom with hBh
  set B : Subgroup G := Bh.map H.subtype with hB
  have hBH : B ≤ H := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hBmem : ∀ x ∈ B, ∃ a : ↥H, Φ a ∈ B' ∧ (a : G) = x := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  have hcard : Nat.card B = Nat.card B' := by
    rw [hB, Subgroup.card_map_of_injective H.subtype_injective]
    exact Nat.card_congr (Φ.toEquiv.subtypeEquiv (fun a => Iff.rfl))
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := hBmem x hx
    obtain ⟨b, hb, rfl⟩ := hBmem y hy
    have : a * b = b * a := Φ.injective (by rw [map_mul, map_mul]; exact hcomm _ ha _ hb)
    exact congrArg Subtype.val this
  have hBsq : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hBmem x hx
    have : a * a = 1 := Φ.injective (by rw [map_mul, map_one]; exact hsq _ ha)
    exact congrArg Subtype.val this
  have hBne : B ≠ ⊥ := by
    obtain ⟨⟨b', hb'⟩, hb'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    intro h
    have hmem : (Φ.symm b' : G) ∈ B := ⟨Φ.symm b', by simpa [hBh] using hb', rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    apply hb'1
    have h1 : Φ.symm b' = 1 := Subtype.ext hmem
    apply Subtype.ext
    have := congrArg Φ h1
    simpa using this
  obtain ⟨gs, hgs, hlt, hA⟩ := hgen B hBH hBcomm hBsq hBne
  let cs : List (MulAut S) := gs.attach.map fun g => Φ ⟨g.1, hAH (hgs g.1 g.2)⟩
  have hΦA : ∀ (g : G) (hg : g ∈ A), Φ ⟨g, hAH hg⟩ = MulAut.conj (θ.symm ⟨g, hg⟩) := by
    intro g hg
    rw [← hΦ]
    congr 1
    apply Subtype.ext
    simp
  refine ⟨cs, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨θ.symm ⟨g.1, hgs g.1 g.2⟩, (hΦA g.1 (hgs g.1 g.2)).symm⟩
  · simpa [cs, ← hcard] using hlt
  · intro s
    set K' : Subgroup (MulAut S) := Subgroup.closure
      {y | ∃ c ∈ cs, ∃ b ∈ B', y = c * b * c⁻¹} with hK'
    set Kp : Subgroup G := (K'.comap Φ.toMonoidHom).map H.subtype with hKp
    have hsub : {y | ∃ c ∈ gs, ∃ b ∈ B, y = c * b * c⁻¹} ⊆ (Kp : Set G) := by
      rintro _ ⟨c, hc, b, hb, rfl⟩
      have hcA : c ∈ A := hgs c hc
      obtain ⟨b0, hb0, rfl⟩ := hBmem b hb
      refine ⟨⟨c, hAH hcA⟩ * b0 * ⟨c, hAH hcA⟩⁻¹, ?_, rfl⟩
      show Φ (⟨c, hAH hcA⟩ * b0 * ⟨c, hAH hcA⟩⁻¹) ∈ K'
      rw [map_mul, map_mul, map_inv]
      refine Subgroup.subset_closure ⟨Φ ⟨c, hAH hcA⟩, ?_, Φ b0, hb0, rfl⟩
      exact List.mem_map.2 ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩
    have hAKp : A ≤ Kp := hA.trans ((Subgroup.closure_le Kp).2 hsub)
    obtain ⟨y, hy, hyθ⟩ := hAKp (θ s).2
    have hy' : y = ⟨(θ s : G), hAH (θ s).2⟩ := Subtype.ext hyθ
    rw [← hΦ s, ← hy']
    exact hy

end Trans

section Main

variable {W : Type} [CommGroup W] [Finite W]

theorem weight_lt_of_genSub (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] [Nontrivial S] (e : CQ L ≃* S) {ρ : ℕ}
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥)
    (hGen : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → B ≠ ⊥ → ∃ cs : List (MulAut S),
        (∀ c ∈ cs, c ∈ (MulAut.conj : S →* MulAut S).range) ∧ Nat.card B ^ cs.length < 2 ^ ρ ∧
        ∀ s : S, MulAut.conj s ∈ Subgroup.closure {y | ∃ c ∈ cs, ∃ b ∈ B, y = c * b * c⁻¹})
    (hDim : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
      ∀ σ : S →* MulAut V, Function.Injective σ → 2 ^ ρ ≤ Nat.card V) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := even_iff_two_dvd.1 hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hcommZ : ∀ l ∈ L, l * ((x : ↥L) : MulAut W) = ((x : ↥L) : MulAut W) * l := by
      intro l hl
      have := Subgroup.mem_center_iff.1 x.2 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hxW : orderOf ((x : ↥L) : MulAut W) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hodd2 := odd_orderOf_of_commutes hW hirr hcommZ
    rw [hxW] at hodd2
    exact absurd hodd2 (by decide)
  have hker : (redHom L e).ker = Subgroup.center ↥L := by
    ext x
    exact redHom_eq_one_iff L e x
  have hker1 : (redHom L e).ker = ⊥ :=
    hCover ↥L (redHom L e) (redHom_surjective L e) (by rw [hker]) (by rw [hker]; exact hZodd)
  have hcent : Subgroup.center ↥L = ⊥ := by rw [← hker]; exact hker1
  have hinj : Function.Injective (redHom L e) := (MonoidHom.ker_eq_bot_iff _).1 hker1
  let eqv : ↥L ≃* S := MulEquiv.ofBijective (redHom L e) ⟨hinj, redHom_surjective L e⟩
  let σ : S →* MulAut W := L.subtype.comp eqv.symm.toMonoidHom
  have hσinj : Function.Injective σ := by
    intro x y hxy
    exact eqv.symm.injective (Subtype.ext hxy)
  have hdim : 2 ^ ρ ≤ Nat.card W := hDim W hW σ hσinj
  have hL : L ≠ ⊥ := by
    intro h
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨l, rfl⟩ := redHom_surjective L e s
    apply hs
    have hall : ∀ x ∈ L, x = 1 := fun x hx => by
      rw [h] at hx
      exact Subgroup.mem_bot.1 hx
    have : l = 1 := Subtype.ext (hall l l.2)
    rw [this, map_one]
  have hact : Function.Injective (actS hE e) :=
    actS_injective_of_center hW hperf hirr hE hEel e hcent
  let ε : ↥E →* MulAut S := (actS hE e).comp (Subgroup.inclusion (le_sup_right : E ≤ L ⊔ E))
  have hεinj : Function.Injective ε := hact.comp (Subgroup.inclusion_injective _)
  have hBcard : Nat.card ε.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hεinj).toEquiv).symm
  have hBcomm : ∀ x ∈ ε.range, ∀ y ∈ ε.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEel.1 a a.2 b b.2)
  have hBsq : ∀ x ∈ ε.range, x * x = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by simpa [sq] using hEel.2 a a.2)
    rw [this, map_one]
  have hBne : ε.range ≠ ⊥ := by
    intro h
    have h1 : Nat.card ε.range = 1 := by rw [h]; simp
    rw [hBcard] at h1
    exact hEne (Subgroup.card_eq_one.1 h1)
  obtain ⟨cs, hcsin, hlt, hcsgen⟩ := hGen ε.range hBcomm hBsq hBne
  rw [hBcard] at hlt
  have hcsr : ∀ c ∈ cs, c ∈ (actS hE e).range := by
    intro c hc
    obtain ⟨s, rfl⟩ := hcsin c hc
    exact conj_mem_range_actS hE e s
  have hgen : ∀ s : S, MulAut.conj s ∈ Subgroup.closure {y : MulAut S | ∃ c ∈ cs,
      ∃ b : ↥(L ⊔ E), (b : MulAut W) ∈ E ∧ y = c * actS hE e b * c⁻¹} := by
    intro s
    refine Subgroup.closure_mono ?_ (hcsgen s)
    rintro _ ⟨c, hc, _, ⟨a, rfl⟩, rfl⟩
    exact ⟨c, hc, Subgroup.inclusion (le_sup_right : E ≤ L ⊔ E) a, a.2, rfl⟩
  have hbound := card_le_index_pow_of_inn_le hW hperf hirr hL hE hEel e cs hcsr hgen
  apply weight_lt_of_lt_index E
  by_contra hcon
  push Not at hcon
  have h1 : (fixV E).index ^ cs.length ≤ Nat.card E ^ cs.length :=
    Nat.pow_le_pow_left hcon cs.length
  omega

end Main

end CFSG.QuasithinUnique.Bridge.J2Excl
