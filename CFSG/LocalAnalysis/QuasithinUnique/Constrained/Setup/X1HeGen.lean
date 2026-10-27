module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Out2
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family

section Act

variable {W : Type} [CommGroup W] [Finite W]

theorem actS_injective_of_center (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hEn : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S) (hcent : Subgroup.center ↥L = ⊥) :
    Function.Injective (actS hEn e) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : actionOnCQ (le_sup_left : L ≤ L ⊔ E) (normal_sup_of_le_normalizer hEn) x = 1 := by
    have : actS hEn e x = 1 := hx
    rw [actS_apply] at this
    exact (MulAut.congr e).injective (by rw [this, map_one])
  have h2 := (actionOnCQ_eq_one_iff (le_sup_left : L ≤ L ⊔ E) (normal_sup_of_le_normalizer hEn)
    hperf x).1 h1
  have h3 : (x : MulAut W) ∈ L := centralizer_inf_le hW hirr hEn hEel ⟨x.2, h2⟩
  have h4 : (⟨(x : MulAut W), h3⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 z z.2)
  rw [hcent, Subgroup.mem_bot] at h4
  have h5 : (x : MulAut W) = 1 := Subtype.ext_iff.1 h4
  exact Subtype.ext h5

theorem mem_center_of_actS_eq_one (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hEn : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S) {x : ↥(L ⊔ E)} (hx : actS hEn e x = 1) :
    ∃ h3 : (x : MulAut W) ∈ L, (⟨(x : MulAut W), h3⟩ : ↥L) ∈ Subgroup.center ↥L := by
  have h1 : actionOnCQ (le_sup_left : L ≤ L ⊔ E) (normal_sup_of_le_normalizer hEn) x = 1 := by
    rw [actS_apply] at hx
    exact (MulAut.congr e).injective (by rw [hx, map_one])
  have h2 := (actionOnCQ_eq_one_iff (le_sup_left : L ≤ L ⊔ E) (normal_sup_of_le_normalizer hEn)
    hperf x).1 h1
  have h3 : (x : MulAut W) ∈ L := centralizer_inf_le hW hirr hEn hEel ⟨x.2, h2⟩
  refine ⟨h3, ?_⟩
  rw [Subgroup.mem_center_iff]
  intro z
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 z z.2)

theorem card_le_index_pow_of_inn_le (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L) (hL : L ≠ ⊥)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S) (cs : List (MulAut S))
    (hcs : ∀ c ∈ cs, c ∈ (actS hE e).range)
    (hgen : ∀ s : S, MulAut.conj s ∈ Subgroup.closure {y : MulAut S | ∃ c ∈ cs,
      ∃ b : ↥(L ⊔ E), (b : MulAut W) ∈ E ∧ y = c * actS hE e b * c⁻¹}) :
    Nat.card W ≤ (fixV E).index ^ cs.length := by
  obtain ⟨cs', rfl⟩ := exists_list_map_eq (actS hE e) cs hcs
  set φ : ↥(L ⊔ E) →* MulAut S := actS hE e with hφ
  set J : Subgroup ↥(L ⊔ E) := Subgroup.closure (conjGen E cs') with hJ
  have hφJ : J.map φ = Subgroup.closure {y : MulAut S | ∃ c ∈ cs'.map φ, ∃ b : ↥(L ⊔ E),
      (b : MulAut W) ∈ E ∧ y = c * φ b * c⁻¹} := map_closure_conjGen φ E cs'
  set incl : ↥L →* ↥(L ⊔ E) := Subgroup.inclusion (le_sup_left : L ≤ L ⊔ E) with hincl
  have hJ' : ∀ l : ↥L, ∃ z ∈ Subgroup.center ↥L, incl (l * z) ∈ J := by
    intro l
    have hl : MulAut.conj (redHom L e l) ∈ J.map φ := by
      rw [hφJ]
      exact hgen _
    obtain ⟨j, hjJ, hj⟩ := hl
    have hx : φ (incl l) = MulAut.conj (redHom L e l) := actS_of_mem hE e l
    have hg : φ ((incl l)⁻¹ * j) = 1 := by
      rw [map_mul, map_inv, hx, hj]
      simp
    obtain ⟨h3, h4⟩ := mem_center_of_actS_eq_one hW hperf hirr hE hEel e hg
    refine ⟨⟨(((incl l)⁻¹ * j : ↥(L ⊔ E)) : MulAut W), h3⟩, h4, ?_⟩
    have : incl (l * ⟨(((incl l)⁻¹ * j : ↥(L ⊔ E)) : MulAut W), h3⟩) = j := by
      apply Subtype.ext
      show (l : MulAut W) * (((incl l)⁻¹ * j : ↥(L ⊔ E)) : MulAut W) = (j : MulAut W)
      have e1 : (l : MulAut W) = ((incl l : ↥(L ⊔ E)) : MulAut W) := rfl
      rw [e1, ← Subgroup.coe_mul]
      simp
    rw [this]
    exact hjJ
  have hJtop : J.comap incl = ⊤ := by
    apply eq_top_of_sup_center_eq_top hperf
    rw [eq_top_iff]
    intro l _
    obtain ⟨z, hz, hlz⟩ := hJ' l
    have : l = (l * z) * z⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem_sup hlz ((Subgroup.center ↥L).inv_mem hz)
  have hLle : L ≤ conjSup E (liftW cs') := by
    intro g hg
    apply map_closure_conjGen_le E cs'
    have : incl ⟨g, hg⟩ ∈ J := by
      have h1 : (⟨g, hg⟩ : ↥L) ∈ J.comap incl := by rw [hJtop]; exact Subgroup.mem_top _
      exact h1
    exact Subgroup.mem_map.2 ⟨incl ⟨g, hg⟩, this, rfl⟩
  have hfix : fixV (conjSup E (liftW cs')) = ⊥ :=
    eq_bot_iff.2 (fun v hv => by
      have : v ∈ fixV L := fixV_anti hLle hv
      rw [fixV_eq_bot_of_irr hirr hL] at this
      exact this)
  have h3 := index_fixV_conjSup_le E (liftW cs')
  rw [hfix, Subgroup.index_bot, length_liftW] at h3
  rw [List.length_map]
  exact h3

end Act

section Main

variable {W : Type} [CommGroup W] [Finite W]

theorem weight_lt_of_three_conj (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] [Nontrivial S] (e : CQ L ≃* S) {r k ρ : ℕ} (hρ : r * k < ρ)
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥)
    (hRank : ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ r)
    (hGen : ∀ ψ : MulAut S, ψ * ψ = 1 → ψ ≠ 1 → ∃ cs : List (MulAut S), cs.length = k ∧
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
  have hEcard : Nat.card E ≤ 2 ^ r := by
    have hB : Nat.card ε.range = Nat.card E :=
      (Nat.card_congr (MonoidHom.ofInjective hεinj).toEquiv).symm
    rw [← hB]
    refine hRank ε.range ?_ ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEel.1 a a.2 b b.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_mul]
      have : a * a = 1 := Subtype.ext (by simpa [sq] using hEel.2 a a.2)
      rw [this, map_one]
  obtain ⟨⟨b, hbE⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
  set b' : ↥(L ⊔ E) := ⟨b, Subgroup.mem_sup_right hbE⟩ with hb'
  have hb'1 : b' ≠ 1 := fun h => hb1 (Subtype.ext (by
    have := congrArg Subtype.val h
    simpa [hb'] using this))
  have hψ1 : actS hE e b' ≠ 1 := fun h => hb'1 (hact (h.trans (map_one _).symm))
  have hψ2 : actS hE e b' * actS hE e b' = 1 := by
    rw [← map_mul]
    have : b' * b' = 1 := Subtype.ext (by simpa [sq] using hEel.2 b hbE)
    rw [this, map_one]
  obtain ⟨cs, hcslen, hcsin, hcsgen⟩ := hGen _ hψ2 hψ1
  have hcsr : ∀ c ∈ cs, c ∈ (actS hE e).range := by
    intro c hc
    obtain ⟨s, rfl⟩ := hcsin c hc
    exact conj_mem_range_actS hE e s
  have hgen : ∀ s : S, MulAut.conj s ∈ Subgroup.closure {y : MulAut S | ∃ c ∈ cs,
      ∃ b : ↥(L ⊔ E), (b : MulAut W) ∈ E ∧ y = c * actS hE e b * c⁻¹} := by
    intro s
    refine Subgroup.closure_mono ?_ (hcsgen s)
    rintro _ ⟨c, hc, t, ht, rfl⟩
    have : t = actS hE e b' := by simpa using ht
    subst this
    exact ⟨c, hc, b', hbE, rfl⟩
  have hbound := card_le_index_pow_of_inn_le hW hperf hirr hL hE hEel e cs hcsr hgen
  rw [hcslen] at hbound
  have hlt : Nat.card E < (fixV E).index := by
    by_contra hcon
    push Not at hcon
    have h1 : (fixV E).index ^ k ≤ (2 ^ r) ^ k := Nat.pow_le_pow_left (hcon.trans hEcard) k
    rw [← pow_mul] at h1
    have h2 : 2 ^ (r * k) < 2 ^ ρ := Nat.pow_lt_pow_right (by norm_num) hρ
    omega
  exact weight_lt_of_lt_index E hlt

end Main

end CFSG.QuasithinUnique.Setup.X1
