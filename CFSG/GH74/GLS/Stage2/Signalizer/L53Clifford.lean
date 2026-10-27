module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Chief

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup
open scoped commutatorElement

variable {M : Type*} [Group M]

theorem exists_normalizing_of_lt [Finite M] {p : ℕ} [Fact p.Prime] {N C R : Subgroup M} (hC : C.Normal)
    (hp : ∀ d ∈ N, ∃ k : ℕ, d ^ (p ^ k) ∈ C) (hCR : C ≤ R) (hRN : R ≤ N) (hne : R ≠ N) :
    ∃ x ∈ N, x ∈ normalizer (R : Set M) ∧ x ∉ R := by
  have hCn : (C.subgroupOf N).Normal := Subgroup.normal_subgroupOf
  have hQ : IsPGroup p (N ⧸ C.subgroupOf N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H d =>
      obtain ⟨k, hk⟩ := hp d d.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
  have hnil : Group.IsNilpotent (N ⧸ C.subgroupOf N) := hQ.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := N ⧸ C.subgroupOf N)
  set π : N →* N ⧸ C.subgroupOf N := QuotientGroup.mk' (C.subgroupOf N) with hπ
  set R' : Subgroup (N ⧸ C.subgroupOf N) := (R.subgroupOf N).map π with hR'
  have hmem : ∀ y : N, π y ∈ R' → (y : M) ∈ R := by
    intro y hy
    obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp hy
    have : r⁻¹ * y ∈ C.subgroupOf N := by
      rw [← QuotientGroup.eq]
      exact hry
    rw [Subgroup.mem_subgroupOf] at this hr
    have hmul : (y : M) = (r : M) * ((r : M)⁻¹ * (y : M)) := by group
    rw [hmul]
    exact R.mul_mem hr (hCR this)
  have htop : R' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm hRN (fun n hn => ?_)
    have : π ⟨n, hn⟩ ∈ R' := by rw [htop]; exact Subgroup.mem_top _
    exact hmem ⟨n, hn⟩ this
  obtain ⟨q, hq, hqR'⟩ := IsConcreteLE.exists_of_lt (hnc R' htop)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hx' : π x ∈ normalizer (R' : Set (N ⧸ C.subgroupOf N)) := hq
  have key : ∀ y : N, π y ∈ normalizer (R' : Set (N ⧸ C.subgroupOf N)) →
      ∀ h ∈ R, (y : M) * h * (y : M)⁻¹ ∈ R := by
    intro y hy h hh
    have hhN : h ∈ N := hRN hh
    have hh' : π ⟨h, hhN⟩ ∈ R' := Subgroup.mem_map_of_mem _ (by
      rw [Subgroup.mem_subgroupOf]; exact hh)
    have h2 := (Subgroup.mem_normalizer_iff.mp hy (π ⟨h, hhN⟩)).mp hh'
    have h3 : π (y * ⟨h, hhN⟩ * y⁻¹) ∈ R' := by simpa using h2
    exact hmem _ h3
  refine ⟨x, x.2, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact key x hx' h
    · intro hxh
      have hinv : π x⁻¹ ∈ normalizer (R' : Set (N ⧸ C.subgroupOf N)) := by
        rw [map_inv]; exact Subgroup.inv_mem _ hx'
      have h1 := key x⁻¹ hinv _ hxh
      rw [Subgroup.coe_inv, inv_inv] at h1
      have e : (x : M)⁻¹ * ((x : M) * h * (x : M)⁻¹) * (x : M) = h := by group
      rwa [e] at h1
  · intro hxR
    apply hqR'
    exact Subgroup.mem_map_of_mem _ (by rw [Subgroup.mem_subgroupOf]; exact hxR)

@[expose] def cj (r : M) (V : Subgroup M) : Subgroup M where
  carrier := {x | r⁻¹ * x * r ∈ V}
  mul_mem' := fun {a b} ha hb => by
    have : r⁻¹ * (a * b) * r = (r⁻¹ * a * r) * (r⁻¹ * b * r) := by group
    show r⁻¹ * (a * b) * r ∈ V
    rw [this]; exact V.mul_mem ha hb
  one_mem' := by show r⁻¹ * 1 * r ∈ V; simp
  inv_mem' := fun {a} ha => by
    have : r⁻¹ * a⁻¹ * r = (r⁻¹ * a * r)⁻¹ := by group
    show r⁻¹ * a⁻¹ * r ∈ V
    rw [this]; exact V.inv_mem ha

theorem mem_cj {r x : M} {V : Subgroup M} : x ∈ cj r V ↔ r⁻¹ * x * r ∈ V := Iff.rfl

theorem cj_one (V : Subgroup M) : cj 1 V = V := by
  ext x; simp [mem_cj]

theorem cj_cj_inv (r : M) (V : Subgroup M) : cj r (cj r⁻¹ V) = V := by
  ext x
  simp only [mem_cj, inv_inv]
  rw [conj_inv_conj]

theorem cj_normal {r : M} {Y : Subgroup M} (hY : Y.Normal) : cj r Y = Y := by
  ext x
  rw [mem_cj]
  exact nconj_inv_iff hY r

theorem cj_mem_normalizer {R V : Subgroup M} (hV : R ≤ normalizer (V : Set M)) {r : M}
    (hr : ∀ x, x ∈ R ↔ r * x * r⁻¹ ∈ R) : R ≤ normalizer (cj r V : Set M) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hs₀ : r⁻¹ * s * r ∈ R := by
    rw [hr, conj_inv_conj]; exact hs
  have h1 := Subgroup.mem_normalizer_iff.mp (hV hs₀) (r⁻¹ * h * r)
  show r⁻¹ * h * r ∈ V ↔ r⁻¹ * (s * h * s⁻¹) * r ∈ V
  have e : r⁻¹ * (s * h * s⁻¹) * r = (r⁻¹ * s * r) * (r⁻¹ * h * r) * (r⁻¹ * s * r)⁻¹ := by group
  rw [e]
  exact h1

@[expose] def RMin (R Y X U : Subgroup M) : Prop :=
  Y < U ∧ U ≤ X ∧ R ≤ normalizer (U : Set M) ∧
    ∀ V : Subgroup M, Y ≤ V → V ≤ U → R ≤ normalizer (V : Set M) → V = Y ∨ V = U

theorem exists_rmin [Finite M] {R Y X W : Subgroup M} (hYW : Y < W) (hWX : W ≤ X)
    (hR : R ≤ normalizer (W : Set M)) : ∃ V, V ≤ W ∧ RMin R Y X V := by
  have hne : {V : Subgroup M | Y < V ∧ V ≤ W ∧ R ≤ normalizer (V : Set M)}.Nonempty :=
    ⟨W, hYW, le_rfl, hR⟩
  obtain ⟨V, hV⟩ := (Set.toFinite _).exists_minimal hne
  obtain ⟨hYV, hVW, hRV⟩ := hV.prop
  refine ⟨V, hVW, hYV, hVW.trans hWX, hRV, fun V' hYV' hV'V hRV' => ?_⟩
  by_cases h : V' = Y
  · exact Or.inl h
  · right
    have hlt : Y < V' := lt_of_le_of_ne hYV' (Ne.symm h)
    exact hV.eq_of_le ⟨hlt, hV'V.trans hVW, hRV'⟩ hV'V

theorem rmin_cj {R Y X V : Subgroup M} (hY : Y.Normal) (hX : X.Normal) {r : M}
    (hr : ∀ x, x ∈ R ↔ r * x * r⁻¹ ∈ R) (hV : RMin R Y X V) : RMin R Y X (cj r V) := by
  obtain ⟨hYV, hVX, hRV, hmin⟩ := hV
  have hr' : ∀ x, x ∈ R ↔ r⁻¹ * x * r⁻¹⁻¹ ∈ R := by
    intro x
    rw [inv_inv, hr (r⁻¹ * x * r), conj_inv_conj]
  refine ⟨?_, ?_, cj_mem_normalizer hRV hr, ?_⟩
  · refine lt_of_le_of_ne (fun y hy => ?_) ?_
    · rw [mem_cj]
      exact hYV.le (nconj_inv hY hy r)
    · intro heq
      obtain ⟨v, hv, hvY⟩ := IsConcreteLE.exists_of_lt hYV
      apply hvY
      have h1 : r * v * r⁻¹ ∈ cj r V := by rw [mem_cj, inv_conj_conj]; exact hv
      rw [← heq] at h1
      exact (nconj_iff hY r).mp h1
  · intro x hx
    rw [mem_cj] at hx
    have := nconj hX (hVX hx) r
    rwa [conj_inv_conj] at this
  · intro V' hYV' hV'V hRV'
    have hY1 : Y ≤ cj r⁻¹ V' := fun y hy => by
      rw [mem_cj]
      exact hYV' (by simpa using nconj hY hy r)
    have hV1 : cj r⁻¹ V' ≤ V := fun x hx => by
      rw [mem_cj, inv_inv] at hx
      have := hV'V hx
      rw [mem_cj, inv_conj_conj] at this
      exact this
    have hR1 : R ≤ normalizer (cj r⁻¹ V' : Set M) := cj_mem_normalizer hRV' hr'
    rcases hmin _ hY1 hV1 hR1 with h | h
    · left
      rw [← cj_cj_inv r V', h, cj_normal hY]
    · right
      rw [← cj_cj_inv r V', h]

theorem exists_orbit_sum [Finite M] {R R' Y X U : Subgroup M} (hRR : R ≤ R') (hU : RMin R' Y X U) :
    ∃ V₀, RMin R Y X V₀ ∧ U ≤ ⨆ r ∈ R', cj r V₀ := by
  obtain ⟨hYU, hUX, hR'U, hmin⟩ := hU
  obtain ⟨V₀, hV₀U, hV₀⟩ := exists_rmin hYU hUX (hRR.trans hR'U)
  refine ⟨V₀, hV₀, ?_⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : Subgroup M, σ = ⨆ r ∈ R', cj r V₀ := ⟨_, rfl⟩
  have hσU : σ ≤ U := by
    rw [hσ]
    refine iSup₂_le fun r hr x hx => ?_
    rw [mem_cj] at hx
    have h1 := hV₀U hx
    have h2 := (Subgroup.mem_normalizer_iff.mp (hR'U hr) _).mp h1
    rwa [conj_inv_conj] at h2
  have hVσ : V₀ ≤ σ := by
    rw [hσ]
    exact le_iSup₂_of_le (1 : M) R'.one_mem (by rw [cj_one])
  have hσinv : ∀ s ∈ R', σ ≤ cj s⁻¹ σ := by
    intro s hs
    rw [hσ]
    refine iSup₂_le fun r hr x hx => ?_
    rw [mem_cj] at hx
    rw [mem_cj, inv_inv]
    have h1 : s * x * s⁻¹ ∈ cj (s * r) V₀ := by
      rw [mem_cj]
      have e : (s * r)⁻¹ * (s * x * s⁻¹) * (s * r) = r⁻¹ * x * r := by group
      rw [e]; exact hx
    have h2 : cj (s * r) V₀ ≤ ⨆ r ∈ R', cj r V₀ :=
      le_iSup₂_of_le (s * r) (R'.mul_mem hs hr) le_rfl
    exact h2 h1
  have hσnorm : R' ≤ normalizer (σ : Set M) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := hσinv s hs hx
      rwa [mem_cj, inv_inv] at this
    · intro hx
      have := hσinv s⁻¹ (R'.inv_mem hs) hx
      rw [mem_cj, inv_inv, inv_inv] at this
      rwa [inv_conj_conj] at this
  rcases hmin σ (hV₀.1.le.trans hVσ) hσU hσnorm with h | h
  · exfalso
    exact hV₀.1.not_ge (hVσ.trans h.le)
  · rw [← hσ, h]

@[expose] def phiSub (Y : Subgroup M) (hY : Y.Normal) (g : M) : Subgroup M where
  carrier := {w | ⁅w, g⁆ ∈ Y}
  mul_mem' := fun {a b} ha hb => by
    show ⁅a * b, g⁆ ∈ Y
    have e : ⁅a * b, g⁆ = (a * ⁅b, g⁆ * a⁻¹) * ⁅a, g⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Y.mul_mem (nconj hY hb a) ha
  one_mem' := by show ⁅(1 : M), g⁆ ∈ Y; simp
  inv_mem' := fun {a} ha => by
    show ⁅a⁻¹, g⁆ ∈ Y
    have e : ⁅a⁻¹, g⁆ = a⁻¹ * ⁅a, g⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact nconj_inv hY (Y.inv_mem ha) a

theorem mem_phiSub {Y : Subgroup M} {hY : Y.Normal} {g w : M} :
    w ∈ phiSub Y hY g ↔ ⁅w, g⁆ ∈ Y := Iff.rfl

theorem le_phiSub {Y : Subgroup M} (hY : Y.Normal) (g : M) : Y ≤ phiSub Y hY g := by
  intro y hy
  rw [mem_phiSub]
  have e : ⁅y, g⁆ = y * (g * y⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact Y.mul_mem hy (nconj hY (Y.inv_mem hy) g)

theorem comm_mem_normal {X : Subgroup M} (hX : X.Normal) {x : M} (hx : x ∈ X) (g : M) :
    ⁅x, g⁆ ∈ X := by
  have e : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact X.mul_mem hx (nconj hX (X.inv_mem hx) g)

@[expose] def quadSub (X Y : Subgroup M) (hX : X.Normal) (hY : Y.Normal) (hXY : ⁅X, X⁆ ≤ Y)
    (g : M) : Subgroup M where
  carrier := {x | x ∈ X ∧ ⁅⁅x, g⁆, g⁆ ∈ Y}
  mul_mem' := by
    rintro a b ⟨haX, ha⟩ ⟨hbX, hb⟩
    refine ⟨X.mul_mem haX hbX, ?_⟩
    have hbw : ⁅b, g⁆ ∈ X := comm_mem_normal hX hbX g
    have h1 : ⁅a, ⁅b, g⁆⁆ ∈ Y := hXY (Subgroup.commutator_mem_commutator haX hbw)
    have e : ⁅a * b, g⁆ = (⁅a, ⁅b, g⁆⁆ * ⁅b, g⁆) * ⁅a, g⁆ := by
      simp only [commutatorElement_def]; group
    show ⁅a * b, g⁆ ∈ phiSub Y hY g
    rw [e]
    exact (phiSub Y hY g).mul_mem ((phiSub Y hY g).mul_mem (le_phiSub hY g h1) hb) ha
  one_mem' := ⟨X.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨haX, ha⟩
    refine ⟨X.inv_mem haX, ?_⟩
    have haw : ⁅a, g⁆⁻¹ ∈ X := X.inv_mem (comm_mem_normal hX haX g)
    have h1 : ⁅a⁻¹, ⁅a, g⁆⁻¹⁆ ∈ Y := hXY (Subgroup.commutator_mem_commutator (X.inv_mem haX) haw)
    have e : ⁅a⁻¹, g⁆ = ⁅a⁻¹, ⁅a, g⁆⁻¹⁆ * ⁅a, g⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    show ⁅a⁻¹, g⁆ ∈ phiSub Y hY g
    rw [e]
    exact (phiSub Y hY g).mul_mem (le_phiSub hY g h1) ((phiSub Y hY g).inv_mem ha)

theorem quad_step [Finite M] {R R' Y X : Subgroup M} {g : M} (hY : Y.Normal) (hX : X.Normal)
    (hXY : ⁅X, X⁆ ≤ Y) (hRR : R ≤ R') (hnorm : R' ≤ normalizer (R : Set M))
    (hQ : ∀ V, RMin R Y X V → ∀ u ∈ V, ⁅⁅u, g⁆, g⁆ ∈ Y) :
    ∀ U, RMin R' Y X U → ∀ u ∈ U, ⁅⁅u, g⁆, g⁆ ∈ Y := by
  intro U hU
  obtain ⟨V₀, hV₀, hUσ⟩ := exists_orbit_sum hRR hU
  have hle : (⨆ r ∈ R', cj r V₀) ≤ quadSub X Y hX hY hXY g := by
    refine iSup₂_le fun r hr x hx => ?_
    have hr' : ∀ y, y ∈ R ↔ r * y * r⁻¹ ∈ R := fun y => Subgroup.mem_normalizer_iff.mp (hnorm hr) y
    have hmin := rmin_cj hY hX hr' hV₀
    exact ⟨hmin.2.1 hx, hQ _ hmin x hx⟩
  exact fun u hu => ((hle (hUσ hu)) : _ ∧ _).2

theorem quad_chain [Finite M] {p : ℕ} [Fact p.Prime] {N C L Y X : Subgroup M} {g : M}
    (hCn : C.Normal) (hY : Y.Normal) (hX : X.Normal) (hXY : ⁅X, X⁆ ≤ Y)
    (hp : ∀ d ∈ N, ∃ k : ℕ, d ^ (p ^ k) ∈ C) (hCL : C ≤ L) (hLN : L ≤ N)
    (hQ : ∀ V, RMin L Y X V → ∀ u ∈ V, ⁅⁅u, g⁆, g⁆ ∈ Y) :
    ∀ U, RMin N Y X U → ∀ u ∈ U, ⁅⁅u, g⁆, g⁆ ∈ Y := by
  have hne : {R : Subgroup M | L ≤ R ∧ R ≤ N ∧
      ∀ V, RMin R Y X V → ∀ u ∈ V, ⁅⁅u, g⁆, g⁆ ∈ Y}.Nonempty := ⟨L, le_rfl, hLN, hQ⟩
  obtain ⟨R, hR⟩ := (Set.toFinite _).exists_maximal hne
  obtain ⟨hLR, hRN, hRQ⟩ := hR.prop
  have hRN' : R = N := by
    by_contra hne'
    obtain ⟨x, hxN, hxn, hxR⟩ := exists_normalizing_of_lt hCn hp (hCL.trans hLR) hRN hne'
    have hRle : R ≤ R ⊔ zpowers x := le_sup_left
    have hnormR : R ⊔ zpowers x ≤ normalizer (R : Set M) :=
      sup_le (Subgroup.le_normalizer) ((Subgroup.zpowers_le).mpr hxn)
    have hQ' := quad_step hY hX hXY hRle hnormR hRQ
    have hmem : R ⊔ zpowers x ∈ {R : Subgroup M | L ≤ R ∧ R ≤ N ∧
        ∀ V, RMin R Y X V → ∀ u ∈ V, ⁅⁅u, g⁆, g⁆ ∈ Y} :=
      ⟨hLR.trans hRle, sup_le hRN ((Subgroup.zpowers_le).mpr hxN), hQ'⟩
    have := hR.le_of_ge hmem hRle
    exact hxR (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  rw [hRN'] at hRQ
  exact hRQ

theorem exists_pow_mem_centralizer [Finite M] {p : ℕ} [Fact p.Prime] {Z : Subgroup M} (hZn : Z.Normal)
    (hZp : IsPGroup p ↥Z) {d : M} (hd : d ∈ stabAll Z) :
    ∃ k : ℕ, d ^ (p ^ k) ∈ centralizer (Z : Set M) := by
  obtain ⟨e, m, hm, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos d).ne'
    p (Fact.out : p.Prime).ne_one
  refine ⟨e, ?_⟩
  have hord : orderOf (d ^ (p ^ e)) = m := by
    have hp0 : p ^ e ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    rw [orderOf_pow' d hp0, hem]
    have hg : (p ^ e * m).gcd (p ^ e) = p ^ e := Nat.gcd_eq_right (dvd_mul_right _ _)
    rw [hg, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp0)]
  have hcop : ¬ p ∣ orderOf (d ^ (p ^ e)) := by rw [hord]; exact hm
  have h1 := centralizes_of_stabAll hZn hZp hcop ((stabAll Z).pow_mem hd _)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (mul_inv_eq_iff_eq_mul.mp (h1 h hh)).symm

theorem normalizer_top_of_normal {H : Subgroup M} (hH : H.Normal) :
    (⊤ : Subgroup M) ≤ normalizer (H : Set M) := by
  have : normalizer (H : Set M) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hH
  rw [this]

theorem quad_of_chief [Finite M] {p : ℕ} [Fact p.Prime] {T Z X Y : Subgroup M} {g : M}
    (hTn : T.Normal) (hT : IsPGroup p ↥T) (hZn : Z.Normal) (hZT : Z ≤ T) (hXT : X ≤ T)
    (hc : IsChiefPair X Y) (hgZ : g ∈ stabAll Z)
    (hQ : ∀ V, RMin (centralizer (Z : Set M) ⊔ zpowers g) Y X V → ∀ u ∈ V, ⁅⁅u, g⁆, g⁆ ∈ Y) :
    ∀ x ∈ X, ⁅⁅x, g⁆, g⁆ ∈ Y := by
  have hXn := hc.1
  have hYn := hc.2.1
  have hZp : IsPGroup p ↥Z := hT.to_le hZT
  have hXY : ⁅X, X⁆ ≤ Y := comm_self_le hT.isNilpotent hTn hXT hc
  have hCn : (centralizer (Z : Set M)).Normal := Subgroup.normal_centralizer
  have hCN : centralizer (Z : Set M) ≤ stabAll Z := by
    intro c hcC X' Y' hcp hX'Z x hx
    have hxc : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hcC) x (hX'Z hx)
    have : ⁅x, c⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]; exact hxc
    rw [this]; exact Y'.one_mem
  have hLN : centralizer (Z : Set M) ⊔ zpowers g ≤ stabAll Z :=
    sup_le hCN ((Subgroup.zpowers_le).mpr hgZ)
  have hp := fun d (hd : d ∈ stabAll Z) => exists_pow_mem_centralizer hZn hZp hd
  have h1 := quad_chain hCn hYn hXn hXY hp le_sup_left hLN hQ
  have h2 := quad_step (R := stabAll Z) (R' := ⊤) hYn hXn hXY le_top
    (normalizer_top_of_normal inferInstance) h1
  refine h2 X ⟨hc.2.2.1, le_rfl, normalizer_top_of_normal hXn, ?_⟩
  intro V hYV hVX hV
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hV)
  exact hc.2.2.2 V hVn hYV hVX

theorem phiSub_conj {Y : Subgroup M} {hY : Y.Normal} {g w : M} (hw : w ∈ phiSub Y hY g) :
    g * w * g⁻¹ ∈ phiSub Y hY g := by
  rw [mem_phiSub] at hw ⊢
  have e : ⁅g * w * g⁻¹, g⁆ = g * ⁅w, g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact nconj hY hw g

theorem comm_comm_le_of_quad [Finite M] {X Y : Subgroup M} (hY : Y.Normal) {g : M}
    (h : ∀ x ∈ X, ⁅⁅x, g⁆, g⁆ ∈ Y) : ⁅⁅X, zpowers g⁆, zpowers g⁆ ≤ Y := by
  have step : ∀ x ∈ X, ∀ n : ℕ, ⁅x, g ^ n⁆ ∈ phiSub Y hY g := by
    intro x hx n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ⁅x, g ^ (n + 1)⁆ = ⁅x, g⁆ * (g * ⁅x, g ^ n⁆ * g⁻¹) := by
        simp only [commutatorElement_def, pow_succ']; group
      rw [e]
      exact (phiSub Y hY g).mul_mem (h x hx) (phiSub_conj ih)
  have hE : ⁅X, zpowers g⁆ ≤ phiSub Y hY g := by
    rw [Subgroup.commutator_le]
    intro x hx m hm
    obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hm
    exact step x hx n
  rw [comm_zpowers_le_iff hY]
  intro e he
  exact hE he

end CFSG.GH74.GLS.Stage2.Signalizer.L53
