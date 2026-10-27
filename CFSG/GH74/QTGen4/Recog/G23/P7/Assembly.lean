module

public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves
public import CFSG.GH74.QTGen4.Recog.G23.HLettersB
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23
  CFSG.CosetTable
open scoped MatrixGroups

theorem card_closure_le_of_words {X : Type*} [Group X] {ws : List (List (Fin 6 × Bool))} {B : ℕ}
    (hPG : Finite (PG 6 ws) ∧ Nat.card (PG 6 ws) ≤ B) (ρ : Fin 6 → X) (h : SatWords ws ρ) :
    Nat.card (Subgroup.closure (Set.range ρ)) ≤ B := by
  obtain ⟨hfin, hc⟩ := hPG
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ ws.map FreeGroup.mk},
      FreeGroup.lift ρ r = 1 := by
    rintro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact h w hw
  let φ : PG 6 ws →* X := PresentedGroup.toGroup hrel
  have hrange : φ.range = Subgroup.closure (Set.range ρ) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
      {r : FreeGroup (Fin 6) | r ∈ ws.map FreeGroup.mk}, MonoidHom.map_closure]
    congr 1
    ext x
    simp [φ, PresentedGroup.toGroup.of]
  rw [← hrange]
  exact (Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective).trans hc

theorem nonempty_mulEquiv_of_words {Y : Type*} [Group Y] [Finite Y]
    {ws : List (List (Fin 6 × Bool))}
    (hPG : Finite (PG 6 ws) ∧ Nat.card (PG 6 ws) ≤ 7371 * 576)
    (hsimp : IsSimpleGroup Ghat) (hcard : Nat.card Ghat = 7371 * 576)
    (u : Fin 6 → Ghat) (hu : SatWords ws u) (hugen : Subgroup.closure (Set.range u) = ⊤)
    (g : Fin 6 → Y) (hg : SatWords ws g) (hne : ∃ i, g i ≠ 1) :
    Nonempty (↥(Subgroup.closure (Set.range g)) ≃* Ghat) := by
  classical
  have hfinG : Finite Ghat := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set f : Fin 6 → Y × Ghat := fun i => (g i, u i) with hf
  set D : Subgroup (Y × Ghat) := Subgroup.closure (Set.range f) with hD
  have hrelD : SatWords ws f := by
    intro r hr
    have h1 : (MonoidHom.fst Y Ghat) (FreeGroup.lift f (FreeGroup.mk r)) =
        FreeGroup.lift g (FreeGroup.mk r) := by
      have : (MonoidHom.fst Y Ghat).comp (FreeGroup.lift f) = FreeGroup.lift g := by
        ext i; simp [hf]
      exact congrArg (fun φ => φ (FreeGroup.mk r)) this
    have h2 : (MonoidHom.snd Y Ghat) (FreeGroup.lift f (FreeGroup.mk r)) =
        FreeGroup.lift u (FreeGroup.mk r) := by
      have : (MonoidHom.snd Y Ghat).comp (FreeGroup.lift f) = FreeGroup.lift u := by
        ext i; simp [hf]
      exact congrArg (fun φ => φ (FreeGroup.mk r)) this
    refine Prod.ext ?_ ?_
    · simpa [hg r hr] using h1
    · simpa [hu r hr] using h2
  have hcardD : Nat.card D ≤ 7371 * 576 := card_closure_le_of_words hPG f hrelD
  have hmap₁ : D.map (MonoidHom.fst Y Ghat) = Subgroup.closure (Set.range g) := by
    rw [hD, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hmap₂ : D.map (MonoidHom.snd Y Ghat) = ⊤ := by
    rw [hD, MonoidHom.map_closure, ← Set.range_comp]
    simpa [hf, Function.comp_def] using hugen
  let p₂ : D →* Ghat := (MonoidHom.snd Y Ghat).comp D.subtype
  have hp₂ : Function.Surjective p₂ := by
    intro x
    have : x ∈ D.map (MonoidHom.snd Y Ghat) := by rw [hmap₂]; trivial
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨d, hd⟩, rfl⟩
  have hle : Nat.card D ≤ Nat.card Ghat := by rw [hcard]; exact hcardD
  have hbij₂ : Function.Bijective p₂ := hp₂.bijective_of_nat_card_le hle
  let ψ : D ≃* Ghat := MulEquiv.ofBijective p₂ hbij₂
  have hDsimp : IsSimpleGroup D := MulEquiv.isSimpleGroup ψ
  have hmem : ∀ d : D, (d : Y × Ghat).1 ∈ Subgroup.closure (Set.range g) := by
    intro d
    rw [← hmap₁]
    exact Subgroup.mem_map.mpr ⟨d, d.2, rfl⟩
  let q : D →* ↥(Subgroup.closure (Set.range g)) :=
    ((MonoidHom.fst Y Ghat).comp D.subtype).codRestrict _ hmem
  have hq : Function.Surjective q := by
    intro y
    have : (y : Y) ∈ D.map (MonoidHom.fst Y Ghat) := by rw [hmap₁]; exact y.2
    obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨d, hd⟩, Subtype.ext hdy⟩
  have hqinj : Function.Injective q := by
    have := q.normal_ker
    rcases hDsimp.eq_bot_or_eq_top_of_normal q.ker with hker | hker
    · exact (MonoidHom.ker_eq_bot_iff q).mp hker
    · exfalso
      obtain ⟨i, hi⟩ := hne
      have hfi : f i ∈ D := Subgroup.subset_closure ⟨i, rfl⟩
      have : (⟨f i, hfi⟩ : D) ∈ q.ker := by rw [hker]; trivial
      rw [MonoidHom.mem_ker] at this
      exact hi (congrArg Subtype.val this)
  exact ⟨(MulEquiv.ofBijective q ⟨hqinj, hq⟩).symm.trans ψ⟩

theorem card_inf_centralizer_of_mulEquiv {G Y : Type*} [Group G] [Group Y] {X : Subgroup G}
    (ψ : ↥X ≃* Y) {x : G} (hx : x ∈ X) :
    Nat.card ↥(X ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({ψ ⟨x, hx⟩} : Set Y)) := by
  have h1 : Nat.card ↥(X ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥((X ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf X) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  rw [h1]
  refine Nat.card_congr (ψ.toEquiv.subtypeEquiv fun a => ?_)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  simp only [a.2, true_and]
  constructor
  · intro h
    have h' : (a : ↥X) * ⟨x, hx⟩ = ⟨x, hx⟩ * a := Subtype.ext h
    show ψ a * ψ ⟨x, hx⟩ = ψ ⟨x, hx⟩ * ψ a
    rw [← map_mul, ← map_mul, h']
  · intro h
    have h' : ψ ((a : ↥X) * ⟨x, hx⟩) = ψ (⟨x, hx⟩ * a) := by
      rw [map_mul, map_mul]; exact h
    exact congrArg Subtype.val (ψ.injective h')


theorem g23AtInv_tail
    (hsimp : IsSimpleGroup Ghat) (hcard : Nat.card Ghat = 7371 * 576)
    (hPG : LeafTriCosetBound) (hlet : LeafTriNative)
    (hconj : ∀ a b : Ghat, orderOf a = 2 → orderOf b = 2 → ∃ g, b = g * a * g⁻¹)
    (hcent : LeafGhatInvolCent)
    (hlie : ∀ {Y : Type} [Group Y], (Y ≃* Ghat) → LieModel Y .G2 0 3 1)
    (hSL : ¬ Group.IsSolvable SL(3, ZMod 2))
    {G : Type} [Group G] [Finite G] {T H H₁ H₂ M : Subgroup G} (hctx : G23Ctx G T H H₁ H₂ M)
    (f : Fin 6 → G) (hf : SatWords triWords f)
    (hK : Subgroup.closure ({f 0, f 1, f 2, f 3} : Set G) = H₁ ⊔ H₂) :
    LieModel G .G2 0 3 1 := by
  obtain ⟨u, hu, hugen⟩ := hlet
  set X : Subgroup G := Subgroup.closure (Set.range f) with hX
  have hKX : H₁ ⊔ H₂ ≤ X := by
    rw [← hK]
    exact Subgroup.closure_mono (by
      rintro _ (rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩)
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ↥(H₁ ⊓ H₂), orderOf z₀ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact exists_prime_orderOf_dvd_card' 2 (by rw [hctx.one.card_inf])
  have hz2 : orderOf (z₀ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz₀
  have hz₁ : (z₀ : G) ≠ 1 := fun h1 => by
    have : orderOf (1 : G) = 2 := h1 ▸ hz2
    simp at this
  have hzH : (z₀ : G) ∈ H := hctx.one.le_one z₀.2.1
  have hzK : (z₀ : G) ∈ H₁ ⊔ H₂ := Subgroup.mem_sup_left z₀.2.1
  have hzX : (z₀ : G) ∈ X := hKX hzK
  have hC0 : Subgroup.centralizer ({(z₀ : G)} : Set G) ≤ H := by
    intro c hc
    rw [hctx.one.eq_centralizer, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(H₁ ⊓ H₂))).mp hctx.one.card_inf
    have : y = 1 ∨ y = (z₀ : G) := by
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · right
        have h1 := huniq ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))
        have h2 := huniq z₀ (fun h => hz₁ (congrArg Subtype.val h))
        exact congrArg Subtype.val (h1.trans h2.symm)
    rcases this with rfl | rfl
    · simp
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  have hne : ∃ i, f i ≠ 1 := by
    by_contra hall1
    push Not at hall1
    have hbot : H₁ ⊔ H₂ = ⊥ := by
      rw [← hK]
      refine (Subgroup.closure_eq_bot_iff).mpr ?_
      rintro _ (rfl | rfl | rfl | rfl) <;> exact hall1 _
    exact hz₁ (by simpa [hbot] using hzK)
  obtain ⟨ψ⟩ := nonempty_mulEquiv_of_words hPG hsimp hcard u hu hugen f hf hne
  have hCX : Nat.card ↥(X ⊓ Subgroup.centralizer ({(z₀ : G)} : Set G)) = 576 := by
    rw [card_inf_centralizer_of_mulEquiv ψ hzX]
    refine hcent _ ?_
    rw [MulEquiv.orderOf_eq]
    rw [Subgroup.orderOf_mk]
    exact hz2
  have hHcard : Nat.card ↥H = 576 := card_H_of_G23One hctx.one
  have hCle : X ⊓ Subgroup.centralizer ({(z₀ : G)} : Set G) ≤ H := inf_le_right.trans hC0
  have hCH : X ⊓ Subgroup.centralizer ({(z₀ : G)} : Set G) = H :=
    Subgroup.eq_of_le_of_card_ge hCle (by rw [hCX, hHcard])
  have hHX : H ≤ X := by
    rw [← hCH]
    exact inf_le_left
  have hconjX : ∀ t ∈ X, orderOf t = 2 → ∃ x ∈ X, x * (z₀ : G) * x⁻¹ = t := by
    intro t htX ht2
    have h1 : orderOf ((⟨t, htX⟩ : X)) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
    have h2 : orderOf ((⟨(z₀ : G), hzX⟩ : X)) = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
    obtain ⟨g, hg⟩ := hconj (ψ ⟨(z₀ : G), hzX⟩) (ψ ⟨t, htX⟩)
      (by rw [MulEquiv.orderOf_eq]; exact h2) (by rw [MulEquiv.orderOf_eq]; exact h1)
    refine ⟨(ψ.symm g : X), (ψ.symm g).2, ?_⟩
    have := congrArg (fun y => (ψ.symm y : X)) hg
    simp only [map_mul, MulEquiv.symm_apply_apply, map_inv] at this
    exact (congrArg Subtype.val this).symm
  obtain ⟨hel, hc8, θ, hθ, hker⟩ := hctx.two
  have hU2 : IsPGroup 2 (quasithinGenFitting M) := by
    intro x
    exact ⟨1, Subtype.ext (by simpa using hel.2 (x : G) x.2)⟩
  have hU : quasithinGenFitting M ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hc8
    omega
  have hUM : quasithinGenFitting M ≤ M := CFSG.Quasithin.quasithinGenFitting_le M
  have hY : M ≤ Subgroup.normalizer (quasithinGenFitting M : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hnorm : (quasithinGenFitting M).subgroupOf M |>.Normal := hker ▸ θ.normal_ker
    constructor
    · intro hx
      have := hnorm.conj_mem ⟨x, hUM hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨m, hm⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hx
      have hxM : x ∈ M := by
        have h2 : m * x * m⁻¹ ∈ M := hUM hx
        have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
        rw [this]
        exact M.mul_mem (M.mul_mem (M.inv_mem hm) h2) hm
      have := hnorm.conj_mem ⟨m * x * m⁻¹, hUM hx⟩
        (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨m⁻¹, M.inv_mem hm⟩
      simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
  have hYns : ¬ Group.IsSolvable ↥M := fun hs =>
    hSL (Group.isSolvable_of_surjective hθ)
  have := hctx.simple
  have hXtop : X = ⊤ :=
    eq_top_of_one_class hz2 hzX (hC0.trans hHX) hconjX hU hU2 hY hYns
  have hGX : G ≃* X := by
    rw [hXtop]
    exact (Subgroup.topEquiv).symm
  exact hlie (hGX.trans ψ)

end CFSG.GH74.QTGen4.Recog.G23.P7
