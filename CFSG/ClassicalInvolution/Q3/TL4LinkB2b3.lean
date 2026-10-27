module

public import CFSG.ClassicalInvolution.Asc77.AscE184Cent
public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b1

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_sylow_le_of_fullyCentralized (hΩ : TypeRFam r Ω) {L : Subgroup G} (hL : L ∈ Ω)
    {y : G} (hy : IsUniqueInvolution L y) {S : Sylow 2 G}
    (hfc : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G))
      (Subgroup.centralizer ({y} : Set G))) :
    ∃ A : Subgroup G, IsSylow2In A L ∧ A ≤ (S : Subgroup G) :=
  ⟨_, Asc77.isSylow2In_inf_of_le_normalizer hfc (hΩ.le_centralizer hL hy) (hΩ.tight L hL y hy),
    inf_le_left.trans inf_le_left⟩

omit [Finite G] in
private theorem conjSub_layerY_of_mem_centralizer (hΩ : ConjInvariant Ω) {x c : G}
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) : conjSub c (layerY Ω x) = layerY Ω x := by
  have key : ∀ d ∈ Subgroup.centralizer ({x} : Set G), conjSub d (layerY Ω x) ≤ layerY Ω x := by
    intro d hd
    unfold layerY
    rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun C hC => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_layerY (conjSub_mem_coreFam hΩ hC hd)
  refine le_antisymm (key c hc) ?_
  have h := conjSub_mono (n := c) (key c⁻¹ ((Subgroup.centralizer ({x} : Set G)).inv_mem hc))
  rwa [conjSub_conjSub_inv] at h

omit [Finite G] in
private theorem inv_mul_mul_mem_conjSub_layerQ (hΩ : ConjInvariant Ω) {t g c μ : G}
    (hc : c ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set G))
    (hμ : μ ∈ conjSub g (layerQ Ω t)) : c⁻¹ * μ * c ∈ conjSub g (layerQ Ω t) := by
  rw [mem_conjSub_iff] at hμ ⊢
  have hd : g⁻¹ * c⁻¹ * g ∈ Subgroup.centralizer ({t} : Set G) := by
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp
      ((Subgroup.centralizer ({g * t * g⁻¹} : Set G)).inv_mem hc)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * c⁻¹ * g * t = g⁻¹ * (c⁻¹ * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * c⁻¹) * g := by rw [hc']
      _ = t * (g⁻¹ * c⁻¹ * g) := by group
  have h := conj_mem_conjSub (n := g⁻¹ * c⁻¹ * g) hμ
  unfold layerQ at h ⊢
  rw [← Thompson.oddCoreOf_conjSub_eq, conjSub_layerY_of_mem_centralizer hΩ hd] at h
  have e : g⁻¹ * (c⁻¹ * μ * c) * g =
      g⁻¹ * c⁻¹ * g * (g⁻¹ * μ * g) * (g⁻¹ * c⁻¹ * g)⁻¹ := by group
  rw [e]
  exact h

private theorem odd_natCard_conjSub_layerQ (g t : G) :
    Odd (Nat.card ↥(conjSub g (layerQ Ω t))) := by
  unfold layerQ
  rw [← Thompson.oddCoreOf_conjSub_eq]
  exact oddCoreOf_odd_natCard _

private theorem conj_eq_of_odd {N X : Subgroup G} (hN : Odd (Nat.card ↥N)) (hX : IsPGroup 2 X)
    {c μ : G} (hc : c ∈ X) (hμ : μ ∈ N) (hcN : c⁻¹ * μ * c ∈ N) (hμc : μ * c * μ⁻¹ ∈ X) :
    μ * c * μ⁻¹ = c := by
  have h2 : c⁻¹ * (μ * c * μ⁻¹) ∈ N := by
    have := N.mul_mem hcN (N.inv_mem hμ)
    simpa [mul_assoc] using this
  have h3 : IsPGroup 2 (Subgroup.zpowers (c⁻¹ * (μ * c * μ⁻¹))) :=
    hX.to_le (Subgroup.zpowers_le.mpr (X.mul_mem (X.inv_mem hc) hμc))
  exact (inv_mul_eq_one.mp (eq_one_of_isPGroup_of_mem_odd hN h2 h3)).symm

private theorem Tri.exists_conj_of_mem_omegaNbr {K J M : Subgroup G} {t u : G}
    (h : Tri r Ω K J M t u) {g : G} {L : Subgroup G} (hL : L ∈ omegaNbr Ω (conjSub g K)) {l : G}
    (hl : IsUniqueInvolution L l) :
    ∃ μ ∈ conjSub g (layerQ Ω t),
      l = μ * (g * u * g⁻¹) * μ⁻¹ ∨ l = μ * (g * (t * u) * g⁻¹) * μ⁻¹ := by
  have hL' : conjSub g⁻¹ L ∈ omegaNbr Ω K := by
    have := omegaNbr_conj h.fam.hyp.conjInvariant hL g⁻¹
    rwa [conjSub_inv_conjSub] at this
  obtain ⟨ν, hν, hLν | hLν⟩ := h.h7 _ hL'
  · refine ⟨g * ν * g⁻¹, conj_mem_conjSub hν, Or.inl ?_⟩
    have h' : IsUniqueInvolution L (g * (ν * u * ν⁻¹) * g⁻¹) := by
      have e : L = conjSub g (conjSub ν J) := by rw [← hLν, conjSub_conjSub_inv]
      rw [e]
      exact (h.inv_J.conj ν).conj g
    rw [hl.eq h']
    group
  · refine ⟨g * ν * g⁻¹, conj_mem_conjSub hν, Or.inr ?_⟩
    have h' : IsUniqueInvolution L (g * (ν * (t * u) * ν⁻¹) * g⁻¹) := by
      have e : L = conjSub g (conjSub ν M) := by rw [← hLν, conjSub_conjSub_inv]
      rw [e]
      exact (h.inv_M.conj ν).conj g
    rw [hl.eq h']
    group

private theorem Tri.eq_or_eq_of_mem_omegaNbr {K J M : Subgroup G} {t u : G}
    (h : Tri r Ω K J M t u) {g : G} {A : Subgroup G} (hg : conjSub g K = A) {a : G}
    (ha : IsUniqueInvolution A a) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXa : X ≤ Subgroup.centralizer ({a} : Set G)) {P₁ P₂ : Subgroup G}
    (hP₁ : P₁ ∈ omegaNbr Ω A) (hP₂ : P₂ ∈ omegaNbr Ω A) {p₁ p₂ : G}
    (hp₁ : IsUniqueInvolution P₁ p₁) (hp₂ : IsUniqueInvolution P₂ p₂) (hne : p₁ ≠ p₂)
    (hp₁X : p₁ ∈ X) (hp₂X : p₂ ∈ X) {B : Subgroup G} (hB : B ∈ omegaNbr Ω A) {b : G}
    (hb : IsUniqueInvolution B b) (hbX : b ∈ X) : b = p₁ ∨ b = p₂ := by
  subst hg
  have hag : a = g * t * g⁻¹ := ha.eq (h.inv_K.conj g)
  subst hag
  have hN := odd_natCard_conjSub_layerQ (Ω := Ω) g t
  have key : ∀ c μ μ' : G, μ ∈ conjSub g (layerQ Ω t) → μ' ∈ conjSub g (layerQ Ω t) →
      μ * c * μ⁻¹ ∈ X → μ' * c * μ'⁻¹ ∈ X → μ * c * μ⁻¹ = μ' * c * μ'⁻¹ := by
    intro c μ μ' hμ hμ' h1 h2
    have hμμ : μ' * μ⁻¹ ∈ conjSub g (layerQ Ω t) :=
      Subgroup.mul_mem _ hμ' (Subgroup.inv_mem _ hμ)
    have e : μ' * c * μ'⁻¹ = μ' * μ⁻¹ * (μ * c * μ⁻¹) * (μ' * μ⁻¹)⁻¹ := by group
    rw [e] at h2 ⊢
    exact (conj_eq_of_odd hN hX h1 hμμ
      (inv_mul_mul_mem_conjSub_layerQ h.fam.hyp.conjInvariant (hXa h1) hμμ) h2).symm
  obtain ⟨μ₁, hμ₁, e₁ | e₁⟩ := h.exists_conj_of_mem_omegaNbr hP₁ hp₁ <;>
  obtain ⟨μ₂, hμ₂, e₂ | e₂⟩ := h.exists_conj_of_mem_omegaNbr hP₂ hp₂ <;>
  obtain ⟨μ, hμ, e | e⟩ := h.exists_conj_of_mem_omegaNbr hB hb <;>
  subst e₁ e₂ e <;>
  first
    | exact absurd (key _ _ _ hμ₁ hμ₂ hp₁X hp₂X) hne
    | exact Or.inl (key _ _ _ hμ hμ₁ hbX hp₁X)
    | exact Or.inr (key _ _ _ hμ hμ₂ hbX hp₂X)

theorem Tri.mem_E_of_adj {K J M : Subgroup G} {t u : G} (h : Tri r Ω K J M t u) {A : Subgroup G}
    (hA : A = K ∨ A = J ∨ A = M) {a : G} (ha : IsUniqueInvolution A a) {B : Subgroup G}
    (hB : B ∈ omegaNbr Ω A) {b : G} (hb : IsUniqueInvolution B b) {X : Subgroup G}
    (hX : IsPGroup 2 X) (hXa : X ≤ Subgroup.centralizer ({a} : Set G)) (htX : t ∈ X)
    (huX : u ∈ X) (hbX : b ∈ X) : b ∈ Subgroup.closure ({t, u} : Set G) := by
  have hΩ := h.fam.hyp
  have htE : t ∈ Subgroup.closure ({t, u} : Set G) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set G) := Subgroup.subset_closure (by simp)
  have htuE : t * u ∈ Subgroup.closure ({t, u} : Set G) := Subgroup.mul_mem _ htE huE
  have htuX : t * u ∈ X := X.mul_mem htX huX
  have hKJ : K ∈ omegaNbr Ω J := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ h.mem h.adj_J.1 h.adj_J
  have hKM : K ∈ omegaNbr Ω M := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ h.mem h.adj_M.1 h.adj_M
  have hJM : J ∈ omegaNbr Ω M :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ h.adj_J.1 h.adj_M.1 h.adj_MJ
  rcases hA with rfl | rfl | rfl
  · have hne : u ≠ t * u := fun e => h.inv_K.ne_one (by
      have := congrArg (· * u⁻¹) e
      simpa using this.symm)
    rcases h.eq_or_eq_of_mem_omegaNbr (conjSub_one _) ha hX hXa h.adj_J h.adj_M h.inv_J h.inv_M
      hne huX htuX hB hb hbX with rfl | rfl
    · exact huE
    · exact htuE
  · obtain ⟨g, hg⟩ := h.trans _ h.mem _ h.adj_J.1
    have hne : t ≠ t * u := fun e => h.inv_J.ne_one (by
      have := congrArg (t⁻¹ * ·) e
      simpa using this.symm)
    rcases h.eq_or_eq_of_mem_omegaNbr hg ha hX hXa hKJ h.adj_MJ h.inv_K h.inv_M hne htX htuX
      hB hb hbX with rfl | rfl
    · exact htE
    · exact htuE
  · obtain ⟨g, hg⟩ := h.trans _ h.mem _ h.adj_M.1
    rcases h.eq_or_eq_of_mem_omegaNbr hg ha hX hXa hKM hJM h.inv_K h.inv_J h.ne_tu htX huX
      hB hb hbX with rfl | rfl
    · exact htE
    · exact huE

@[expose] def FrameW (Ω : Set (Subgroup G)) (S : Sylow 2 G) (W : Subgroup G) : Prop :=
  W ≤ (S : Subgroup G) ∧ IsMulCommutative W ∧
    ∀ A ∈ Ω, 2 < Nat.card ↥(A ⊓ (S : Subgroup G)) → A ⊓ W ∈ USet Ω

theorem exists_frameW (hΩ : HypOmegaGen Ω) (S : Sylow 2 G) : ∃ W : Subgroup G, FrameW Ω S W := by
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hC := Sec6Gen.cyc66 hΩ
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hη.1 hV).2
  have habel := (Sec6Gen.eta_abelian_of_cyc66 hΩ hC hη hinv).1
  refine ⟨⨆ V ∈ η, V, iSup₂_le hηS, ⟨⟨fun x y => Subtype.ext (habel x x.2 y y.2)⟩⟩,
    fun A hA h2 => ?_⟩
  exact (hη.1 (Sec6Gen.eta_inf_mem_of_cyc66 hΩ hC ⟨S, hη, hinv⟩ hηS hA h2)).1

theorem exists_gen_of_mem_USet (hΩ : TypeRFam r Ω) {A U : Subgroup G} (hA : A ∈ Ω) {a : G}
    (ha : IsUniqueInvolution A a) (hU : U ∈ USet Ω) (hUA : U ≤ A) :
    ∃ x : G, U = Subgroup.zpowers x ∧ orderOf x = 2 ^ (r - 1) ∧ x ^ 2 ^ (r - 2) = a := by
  obtain ⟨R, -, J, hJ, hRJ, -, hcyc, hcard, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ.hyp hU
  obtain ⟨e⟩ := hΩ.quat J hJ R hRJ
  have hR : Nat.card R = 4 * 2 ^ (r - 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hr : 1 ≤ r - 2 := by
    by_contra hlt
    have h0 : r - 2 = 0 := by omega
    rw [h0] at hR
    omega
  have hpow : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hUcard : Nat.card U = 2 ^ (r - 1) := by
    rw [hpow]
    omega
  obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top U).mp hcyc
  have hox : orderOf x = 2 ^ (r - 1) := by
    rw [← Nat.card_zpowers, hx, hUcard]
  refine ⟨x, hx.symm, hox, ?_⟩
  have hmem : x ^ 2 ^ (r - 2) ∈ A := hUA (hx ▸ Subgroup.npow_mem_zpowers x _)
  have hsq : x ^ 2 ^ (r - 2) * x ^ 2 ^ (r - 2) = 1 := by
    rw [← pow_add, ← two_mul, ← hpow, ← hox, pow_orderOf_eq_one]
  have hne : x ^ 2 ^ (r - 2) ≠ 1 := by
    intro h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hox, hpow] at hdvd
    have := Nat.le_of_dvd (by positivity) hdvd
    have : 0 < 2 ^ (r - 2) := by positivity
    omega
  exact (ha.unique _ hmem hsq).resolve_left hne

theorem two_lt_card_inf_of_sylow (hΩ : TypeRFam r Ω) {A P : Subgroup G} (hA : A ∈ Ω)
    (hP : IsSylow2In P A) {S : Subgroup G} (hPS : P ≤ S) : 2 < Nat.card ↥(A ⊓ S) := by
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ.hyp (mem_RSet_of_isSylow2In hA hP)
  have := Subgroup.card_le_of_le (le_inf hP.1 hPS)
  omega

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b
