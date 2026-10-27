module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic
public import CFSG.ClassicalInvolution.Asc77.WP1Section7
import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonStarEng
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonClass

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.Thompson

variable (p f : ℕ) [Fact p.Prime]

@[expose] def L7_1Full : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ u r v t : G,
      Subgroup.zpowers u = R ⊓ W → R = Subgroup.closure {u, r} →
      Subgroup.zpowers v = T ⊓ W → T = Subgroup.closure {v, t} →
        (R ⊔ T ⊔ OCW W) ⊓ W = Subgroup.closure {u, v} ∧
        ((∃ J ∈ Ω, R ≤ J ∧ T ≤ J) ∧ T ≤ R ⊔ W ⊔ OCW W ∧ R ≤ T ⊔ W ⊔ OCW W ∨
          (∃ J ∈ Ω, ∃ J' ∈ Ω, R ≤ J ∧ T ≤ J' ∧ J' ∈ omegaNbr Ω J) ∧
            (∀ a ∈ R, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ OCW W) ∨
          (∃ J ∈ Ω, ∃ J' ∈ Ω, R ≤ J ∧ T ≤ J' ∧ J' ∈ omegaStarNbr Ω J ∧ J' ∉ omegaNbr Ω J) ∧
            (∃ v' : G, Subgroup.zpowers v' = Subgroup.zpowers v ∧
              t⁻¹ * u * t * (u * v')⁻¹ ∈ OCW W ∧ r⁻¹ * v' * r * (v' * u)⁻¹ ∈ OCW W) ∧
            (r * t) ^ 3 ∈ Subgroup.closure {u, v} ⊔ OCW W ∧ r * t ∉ W ⊔ OCW W ∧
              r ∉ W ⊔ OCW W ∧ t ∉ W ⊔ OCW W)

@[expose] def ThompsonCube : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ r ∈ R, ∀ t ∈ T, r ∉ W → t ∉ W →
      r * t * r⁻¹ * t⁻¹ ∈ W ⊔ OCW W ∨ (r * t) ^ 3 ∈ W ⊔ OCW W

@[expose] def ThompsonStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ S ∈ DSet Ω W,
      ∀ r ∈ R, ∀ t ∈ T, ∀ s ∈ S, r ∉ W → t ∉ W → s ∉ W →
        r * t * r⁻¹ * t⁻¹ ∉ W ⊔ OCW W →
          s * r * s⁻¹ * r⁻¹ ∈ W ⊔ OCW W ∨ s * t * s⁻¹ * t⁻¹ ∈ W ⊔ OCW W ∨
            s * (r * t * r⁻¹) * s⁻¹ * (r * t * r⁻¹)⁻¹ ∈ W ⊔ OCW W

@[expose] def ThompsonClique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ W ∈ WSet Ω, ¬ DbarConnected Ω W → ∀ d ∈ muDelta Ω W,
      (Star3T.cent (muDelta Ω W) d).ncard = 1 ∨ (Star3T.cent (muDelta Ω W) d).ncard = 2 ∨
        ((Star3T.cent (muDelta Ω W) d).ncard = 4 ∧
          16 ≤ Nat.card ↥(Subgroup.closure (Star3T.cent (muDelta Ω W) d)))

@[expose] def muDeltaCent {G : Type} [Group G] (Ω : Set (Subgroup G)) (W : Subgroup G) (x : G) :
    Set ↥(muGroup Ω W) :=
  muDeltaOf Ω W {T | T ∈ DSet Ω W ∧ T ≤ Subgroup.centralizer ({x} : Set G)}

@[expose] def ThompsonSub : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W →
      ∀ R₁ ∈ DSet Ω W, ∀ R₂ ∈ DSet Ω W, DComm W R₁ R₂ →
        ∀ w ∈ R₁ ⊓ W, ∀ v ∈ R₂ ⊓ W, orderOf w = 4 → orderOf v = 4 →
          ∃ ψ : ↥(Subgroup.closure (muDeltaCent Ω W (w * v))) ≃* Equiv.Perm (Fin 4),
            ∀ (x : ↥(muGroup Ω W)) (hx : x ∈ Subgroup.closure (muDeltaCent Ω W (w * v))),
              x ∈ muDeltaCent Ω W (w * v) ↔ (ψ ⟨x, hx⟩).IsSwap

@[expose] def ThompsonGraph : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ K ∈ Ω, dComp Ω K ≠ dstarComp Ω K → ∃ W ∈ WSet Ω, ¬ DbarConnected Ω W

variable {p f}

namespace Thompson

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem muDelta_comm_or_cube
    (hcube : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ r ∈ R, ∀ t ∈ T, r ∉ W → t ∉ W →
      r * t * r⁻¹ * t⁻¹ ∈ W ⊔ OCW W ∨ (r * t) ^ 3 ∈ W ⊔ OCW W) :
    ∀ a ∈ muDelta Ω W, ∀ b ∈ muDelta Ω W, a * b = b * a ∨ (a * b) ^ 3 = 1 := by
  rintro a ⟨R, hR, r, hr, hrW, hra⟩ b ⟨T, hT, t, ht, htW, htb⟩
  rcases hcube R hR T hT r hr t ht hrW htW with h | h
  · left
    apply Subtype.ext
    show (a : NQuot (W ⊔ OCW W)) * b = b * a
    rw [hra, htb]
    exact (piG_comm_iff (hR.2 hr) (hT.2 ht)).mpr h
  · right
    apply Subtype.ext
    show ((a : NQuot (W ⊔ OCW W)) * b) ^ 3 = 1
    rw [hra, htb]
    exact (piG_cube_iff (hR.2 hr) (hT.2 ht)).mpr h

theorem isStar_muDelta (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) [Finite G]
    (hW : W ∈ WSet Ω)
    (hstar : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ S ∈ DSet Ω W, ∀ r ∈ R, ∀ t ∈ T, ∀ s ∈ S,
      r ∉ W → t ∉ W → s ∉ W → r * t * r⁻¹ * t⁻¹ ∉ W ⊔ OCW W →
        s * r * s⁻¹ * r⁻¹ ∈ W ⊔ OCW W ∨ s * t * s⁻¹ * t⁻¹ ∈ W ⊔ OCW W ∨
          s * (r * t * r⁻¹) * s⁻¹ * (r * t * r⁻¹)⁻¹ ∈ W ⊔ OCW W) :
    Star3T.IsStar (muDelta Ω W) := by
  exact isStar_muDeltaE (fun ha => muDelta_mul_self hp hq hΩ hW ha) hstar

section Generators

variable [Finite G]

theorem exists_zpowers_eq_inf_W {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)} (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) : ∃ u : G, Subgroup.zpowers u = R ⊓ W := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  have hcyc := (inf_W_of_mem_D hp hq hΩ hW hR hK hRK).2.2.1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(R ⊓ W))
  refine ⟨g, le_antisymm (Subgroup.zpowers_le.mpr g.2) fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  exact ⟨k, congrArg Subtype.val hk⟩

theorem eq_closure_pair {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)} (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G}
    (hR : R ∈ DSet Ω W) {u r : G} (hu : Subgroup.zpowers u = R ⊓ W) (hr : r ∈ R) (hrW : r ∉ W) :
    R = Subgroup.closure {u, r} := by
  have hu' : u ∈ R ⊓ W := hu ▸ Subgroup.mem_zpowers u
  apply le_antisymm
  · intro x hx
    by_cases hxW : x ∈ W
    · have : x ∈ Subgroup.zpowers u := hu ▸ ⟨hx, hxW⟩
      exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert u _))) this
    · have h1 : r⁻¹ * x ∈ Subgroup.zpowers u :=
        hu ▸ ⟨R.mul_mem (R.inv_mem hr) hx, D_inv_mul_mem hp hq hΩ hW hR hr hx hrW hxW⟩
      have h2 : x = r * (r⁻¹ * x) := by group
      rw [h2]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton r)))
        ((Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert u _))) h1)
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hu'.1
    · exact hr

end Generators

theorem isTT_muDelta (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) [Finite G]
    (hW : W ∈ WSet Ω)
    (hcube : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ r ∈ R, ∀ t ∈ T, r ∉ W → t ∉ W →
      r * t * r⁻¹ * t⁻¹ ∈ W ⊔ OCW W ∨ (r * t) ^ 3 ∈ W ⊔ OCW W) :
    Star3T.IsTT (muDelta Ω W) where
  mul_self _ ha := muDelta_mul_self hp hq hΩ hW ha
  ne_one _ ha := muDelta_ne_one hW ha
  conj_mem _ ha g := muDelta_conj_mem hΩ ha g
  closure_eq_top := closure_muDelta_eq_top Ω W
  comm_or_cube := muDelta_comm_or_cube hcube

theorem muDelta_classification (h1 : ThompsonCube p f) (h2 : ThompsonStar p f)
    (h3 : ThompsonClique p f) [Finite G] (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω)
    (hnc : ¬ DbarConnected Ω W) :
    (∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 3), ∀ x, x ∈ muDelta Ω W ↔ (e x).IsSwap) ∨
    (∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4), ∀ x, x ∈ muDelta Ω W ↔ (e x).IsSwap) ∨
    MuIsoWylD4 Ω W := by
  obtain ⟨hp, hq, hΩ, hA⟩ := hP
  have hTT := isTT_muDelta hp hq hΩ hW (h1 G Ω ⟨hp, hq, hΩ, hA⟩ W hW)
  have hS := isStar_muDelta hp hq hΩ hW (h2 G Ω ⟨hp, hq, hΩ, hA⟩ W hW)
  obtain ⟨d, hd, a, ha, hconn⟩ := exists_not_conn_of_not_connected hp hq hΩ hW hnc
  rcases h3 G Ω ⟨hp, hq, hΩ, hA⟩ W hW hnc d hd with hk | hk | ⟨hk, hcard⟩
  · exact Or.inl (Star3T.exists_mulEquiv_perm_three hTT hS hd ha hconn hk)
  · exact Or.inr (Or.inl (Star3T.exists_mulEquiv_perm_four hTT hS hd ha hconn hk))
  · refine Or.inr (Or.inr ?_)
    exact Star3T.nonempty_mulEquiv_of_card_four hTT hS hd ha hconn hk hcard
      (M := coxeterD4) (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
      coxeterD4.toCoxeterSystem

end Thompson

theorem thompsonCube_of_l7_1Full (h : L7_1Full p f) : ThompsonCube p f := by
  intro G _ _ Ω hP W hW R hR T hT r hr t ht hrW htW
  obtain ⟨hp, hq, hΩ, hA⟩ := hP
  obtain ⟨u, hu⟩ := Thompson.exists_zpowers_eq_inf_W hp hq hΩ hW hR
  obtain ⟨v, hv⟩ := Thompson.exists_zpowers_eq_inf_W hp hq hΩ hW hT
  have hRcl := Thompson.eq_closure_pair hp hq hΩ hW hR hu hr hrW
  have hTcl := Thompson.eq_closure_pair hp hq hΩ hW hT hv ht htW
  obtain ⟨-, hcases⟩ := h G Ω ⟨hp, hq, hΩ, hA⟩ W hW R hR T hT u r v t hu hRcl hv hTcl
  rcases hcases with ⟨-, hTR, -⟩ | ⟨-, hcomm⟩ | ⟨-, -, hcube, -, -, -⟩
  · left
    have heq := Thompson.piG_eq_of_le_sup hp hq hΩ hW hR hT hTR hr ht hrW htW
    exact (Thompson.piG_comm_iff (hR.2 hr) (hT.2 ht)).mp (by rw [heq])
  · left
    exact Subgroup.mem_sup_right (hcomm r hr t ht)
  · right
    have hle : Subgroup.closure {u, v} ≤ W := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact (hu ▸ Subgroup.mem_zpowers y : y ∈ R ⊓ W).2
      · exact (hv ▸ Subgroup.mem_zpowers y : y ∈ T ⊓ W).2
    exact sup_le_sup_right hle _ hcube

theorem l7_10_of_inputs (h1 : ThompsonCube p f) (h2 : ThompsonStar p f)
    (h3 : ThompsonClique p f) : L7_10 p f := by
  intro G _ _ Ω hP W hW hnc
  rcases Thompson.muDelta_classification h1 h2 h3 hP hW hnc with ⟨e, -⟩ | ⟨e, -⟩ | h
  · exact Or.inl ⟨e⟩
  · exact Or.inr (Or.inl ⟨e⟩)
  · exact Or.inr (Or.inr h)

theorem l7_17_of_inputs (h710 : L7_10 p f) (h752 : L7_5_2 p f) (h5 : ThompsonGraph p f) :
    L7_17 p f := by
  intro G _ _ Ω hP K hK
  by_cases h : dComp Ω K = dstarComp Ω K
  · exact Or.inl h
  · right
    obtain ⟨W₀, hW₀, hnc⟩ := h5 G Ω hP K hK h
    have hmu := h710 G Ω hP W₀ hW₀ hnc
    intro W hW
    obtain ⟨e⟩ := h752 hP.1 hP.2.1 G Ω hP.2.2.1 W₀ hW₀ W hW
    rcases hmu with h' | h' | h'
    · obtain ⟨e'⟩ := h'
      exact Or.inl ⟨e.symm.trans e'⟩
    · obtain ⟨e'⟩ := h'
      exact Or.inr (Or.inl ⟨e.symm.trans e'⟩)
    · obtain ⟨e'⟩ := h'
      exact Or.inr (Or.inr ⟨e.symm.trans e'⟩)

end CFSG.ClassicalInvolution.Asc77
