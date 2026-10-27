module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeGen

public section

namespace CFSG.QuasithinUnique.Bridge.HSExcl

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family

theorem exists_mem_of_index_two {A : Type*} [Group A] [Finite A] {N B : Subgroup A}
    (hN : N.index ≤ 2) (hB : 4 ≤ Nat.card B) : ∃ x ∈ B, x ≠ 1 ∧ x ∈ N := by
  by_contra hcon
  push Not at hcon
  have hbot : B ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    exact hcon x hx.1 hx1 hx.2
  have hinj : Function.Injective (fun x : B => (QuotientGroup.mk (x : A) : A ⧸ N)) := by
    intro x y hxy
    have h1 : (x : A)⁻¹ * (y : A) ∈ N := by
      have := QuotientGroup.eq.1 hxy
      exact this
    have h2 : (x : A)⁻¹ * (y : A) ∈ B := B.mul_mem (B.inv_mem x.2) y.2
    have h3 : (x : A)⁻¹ * (y : A) ∈ B ⊓ N := ⟨h2, h1⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact Subtype.ext h3
  have hle := Nat.card_le_card_of_injective _ hinj
  have hcard : Nat.card (A ⧸ N) = N.index := rfl
  rw [hcard] at hle
  omega

section Trans

variable {G : Type*} [Group G] {S : Type*} [Group S]

theorem gen_inner_of_equiv {H A : Subgroup G} (hAH : A ≤ H) (Φ : ↥H ≃* MulAut S) (θ : S ≃* ↥A)
    (hΦ : ∀ s : S, Φ ⟨(θ s : G), hAH (θ s).2⟩ = MulAut.conj s) {k : ℕ}
    (hgen : ∀ x ∈ A, x * x = 1 → x ≠ 1 → ∃ gs : List G, gs.length = k ∧ (∀ g ∈ gs, g ∈ A) ∧
      A ≤ Subgroup.closure (X1.conjSet gs {x})) :
    ∀ ψ : MulAut S, ψ * ψ = 1 → ψ ≠ 1 → ψ ∈ (MulAut.conj : S →* MulAut S).range →
      ∃ cs : List (MulAut S), cs.length = k ∧
        (∀ c ∈ cs, c ∈ (MulAut.conj : S →* MulAut S).range) ∧
        ∀ s : S, MulAut.conj s ∈ Subgroup.closure (X1.conjSet cs {ψ}) := by
  intro ψ hψ2 hψ1 hψinn
  obtain ⟨s₀, rfl⟩ := hψinn
  set xh : ↥H := Φ.symm (MulAut.conj s₀) with hxh
  have hxhA : (xh : G) ∈ A := by
    have : xh = ⟨(θ s₀ : G), hAH (θ s₀).2⟩ := (MulEquiv.symm_apply_eq Φ).2 (hΦ s₀).symm
    rw [this]
    exact (θ s₀).2
  have hx2 : xh * xh = 1 := by
    apply Φ.injective
    rw [map_mul, hxh, MulEquiv.apply_symm_apply, hψ2, map_one]
  have hx1 : xh ≠ 1 := by
    intro h
    apply hψ1
    rw [← MulEquiv.apply_symm_apply Φ (MulAut.conj s₀), ← hxh, h, map_one]
  obtain ⟨gs, hlen, hgs, hA⟩ := hgen (xh : G) hxhA (by simpa using congrArg Subtype.val hx2)
    (fun h => hx1 (Subtype.ext h))
  let cs : List (MulAut S) := gs.attach.map fun g => Φ ⟨g.1, hAH (hgs g.1 g.2)⟩
  have hΦA : ∀ (g : G) (hg : g ∈ A), Φ ⟨g, hAH hg⟩ = MulAut.conj (θ.symm ⟨g, hg⟩) := by
    intro g hg
    rw [← hΦ]
    congr 1
    apply Subtype.ext
    simp
  refine ⟨cs, by simp [cs, hlen], ?_, ?_⟩
  · intro c hc
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hc
    exact ⟨θ.symm ⟨g.1, hgs g.1 g.2⟩, (hΦA g.1 (hgs g.1 g.2)).symm⟩
  · intro s
    set K' : Subgroup (MulAut S) := Subgroup.closure (X1.conjSet cs {MulAut.conj s₀}) with hK'
    set Kp : Subgroup G := (K'.comap Φ.toMonoidHom).map H.subtype with hKp
    have hsub : X1.conjSet gs {(xh : G)} ⊆ (Kp : Set G) := by
      rintro _ ⟨g, hg, t, ht, rfl⟩
      have ht' : t = (xh : G) := by simpa using ht
      subst ht'
      have hgA : g ∈ A := hgs g hg
      refine ⟨⟨g, hAH hgA⟩ * xh * ⟨g, hAH hgA⟩⁻¹, ?_, rfl⟩
      show Φ (⟨g, hAH hgA⟩ * xh * ⟨g, hAH hgA⟩⁻¹) ∈ K'
      rw [map_mul, map_mul, map_inv, hxh, MulEquiv.apply_symm_apply]
      refine Subgroup.subset_closure ⟨Φ ⟨g, hAH hgA⟩, ?_, MulAut.conj s₀, rfl, rfl⟩
      exact List.mem_map.2 ⟨⟨g, hg⟩, List.mem_attach _ _, rfl⟩
    have hAKp : A ≤ Kp := hA.trans ((Subgroup.closure_le Kp).2 hsub)
    obtain ⟨y, hy, hyθ⟩ := hAKp (θ s).2
    have hy' : y = ⟨(θ s : G), hAH (θ s).2⟩ := Subtype.ext hyθ
    rw [← hΦ s, ← hy']
    exact hy

end Trans

section Main

variable {W : Type} [CommGroup W] [Finite W]

theorem weight_lt_of_gen34 (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] [Nontrivial S] (e : CQ L ≃* S) {r ρ : ℕ} (hρ3 : 3 * r < ρ)
    (hρ4 : 3 ^ 4 < 2 ^ ρ)
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥)
    (hRank : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r)
    (hInn : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → 4 ≤ Nat.card B →
      ∃ ψ ∈ B, ψ ≠ 1 ∧ ψ ∈ (MulAut.conj : S →* MulAut S).range)
    (hGen3 : ∀ ψ : MulAut S, ψ * ψ = 1 → ψ ≠ 1 → ψ ∈ (MulAut.conj : S →* MulAut S).range →
      ∃ cs : List (MulAut S), cs.length = 3 ∧
        (∀ c ∈ cs, c ∈ (MulAut.conj : S →* MulAut S).range) ∧
        ∀ s : S, MulAut.conj s ∈ Subgroup.closure (conjSet cs {ψ}))
    (hGen4 : ∀ ψ : MulAut S, ψ * ψ = 1 → ψ ≠ 1 →
      ∃ cs : List (MulAut S), cs.length = 4 ∧
        (∀ c ∈ cs, c ∈ (MulAut.conj : S →* MulAut S).range) ∧
        ∀ s : S, MulAut.conj s ∈ Subgroup.closure (conjSet cs {ψ}))
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
  have hEcard : Nat.card E ≤ 2 ^ r := by
    rw [← hBcard]
    exact hRank ε.range hBcomm hBsq
  have hinvol : ∀ a : ↥(L ⊔ E), (a : MulAut W) ∈ E → a ≠ 1 →
      actS hE e a ≠ 1 ∧ actS hE e a * actS hE e a = 1 := by
    intro a haE ha1
    refine ⟨fun h => ha1 (hact (h.trans (map_one _).symm)), ?_⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by simpa [sq] using hEel.2 (a : MulAut W) haE)
    rw [this, map_one]
  have key : ∀ a : ↥(L ⊔ E), (a : MulAut W) ∈ E → ∀ cs : List (MulAut S),
      (∀ c ∈ cs, c ∈ (MulAut.conj : S →* MulAut S).range) →
      (∀ s : S, MulAut.conj s ∈ Subgroup.closure (conjSet cs {actS hE e a})) →
      Nat.card W ≤ (fixV E).index ^ cs.length := by
    intro a haE cs hcsin hcsgen
    have hcsr : ∀ c ∈ cs, c ∈ (actS hE e).range := by
      intro c hc
      obtain ⟨s, rfl⟩ := hcsin c hc
      exact conj_mem_range_actS hE e s
    have hgen : ∀ s : S, MulAut.conj s ∈ Subgroup.closure {y : MulAut S | ∃ c ∈ cs,
        ∃ b : ↥(L ⊔ E), (b : MulAut W) ∈ E ∧ y = c * actS hE e b * c⁻¹} := by
      intro s
      refine Subgroup.closure_mono ?_ (hcsgen s)
      rintro _ ⟨c, hc, t, ht, rfl⟩
      have : t = actS hE e a := by simpa using ht
      subst this
      exact ⟨c, hc, a, haE, rfl⟩
    exact card_le_index_pow_of_inn_le hW hperf hirr hL hE hEel e cs hcsr hgen
  by_cases h4 : 4 ≤ Nat.card E
  ·
    obtain ⟨ψ, hψB, hψ1, hψinn⟩ := hInn ε.range hBcomm hBsq (by rw [hBcard]; exact h4)
    obtain ⟨a, rfl⟩ := hψB
    set a' : ↥(L ⊔ E) := Subgroup.inclusion (le_sup_right : E ≤ L ⊔ E) a with ha'
    have ha'E : (a' : MulAut W) ∈ E := a.2
    have hεa : ε a = actS hE e a' := rfl
    have ha'1 : a' ≠ 1 := fun h => hψ1 (by rw [hεa, h, map_one])
    obtain ⟨-, hψ2⟩ := hinvol a' ha'E ha'1
    rw [hεa] at hψ1 hψinn
    obtain ⟨cs, hlen, hcsin, hcsgen⟩ := hGen3 _ hψ2 hψ1 hψinn
    have hbound := key a' ha'E cs hcsin hcsgen
    rw [hlen] at hbound
    have hlt : Nat.card E < (fixV E).index := by
      by_contra hcon
      push Not at hcon
      have h1 : (fixV E).index ^ 3 ≤ (2 ^ r) ^ 3 := Nat.pow_le_pow_left (hcon.trans hEcard) 3
      rw [← pow_mul] at h1
      have h2 : 2 ^ (r * 3) < 2 ^ ρ := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    exact weight_lt_of_lt_index E hlt
  ·
    push Not at h4
    obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
    set b' : ↥(L ⊔ E) := ⟨b, Subgroup.mem_sup_right hbE⟩ with hb'
    have hb'1 : b' ≠ 1 := fun h => hb1 (Subtype.ext (by
      have := congrArg Subtype.val h
      simpa [hb'] using this))
    obtain ⟨hψ1, hψ2⟩ := hinvol b' hbE hb'1
    obtain ⟨cs, hlen, hcsin, hcsgen⟩ := hGen4 _ hψ2 hψ1
    have hbound := key b' hbE cs hcsin hcsgen
    rw [hlen] at hbound
    have hlt : Nat.card E < (fixV E).index := by
      by_contra hcon
      push Not at hcon
      have h1 : (fixV E).index ^ 4 ≤ 3 ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    exact weight_lt_of_lt_index E hlt

end Main

end CFSG.QuasithinUnique.Bridge.HSExcl
