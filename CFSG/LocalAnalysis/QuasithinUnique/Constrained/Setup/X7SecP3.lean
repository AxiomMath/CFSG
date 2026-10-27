module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aRankTwo
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneAux

public section

namespace CFSG.QuasithinUnique.Setup.X7Sec

open scoped MatrixGroups Matrix IsMulCommutative

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.X3 CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

section Elem

variable {N : Type*} [Group N] {A : Subgroup N}

theorem sq_of_mem [CFSG.IsElementaryAbelian 2 ↥A] {a : N} (ha : a ∈ A) : a * a = 1 := by
  rw [← pow_two]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha

theorem comm_of_mem [CFSG.IsElementaryAbelian 2 ↥A] {a b : N} (ha : a ∈ A) (hb : b ∈ A) :
    a * b = b * a :=
  congrArg Subtype.val ((inferInstance : IsMulCommutative A).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem isElementaryAbelian_two_of_forall' {X : Type*} [Group X] (H : Subgroup X)
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hs : ∀ x ∈ H, x * x = 1) :
    CFSG.IsElementaryAbelian 2 ↥H := CFSG.IsElementaryAbelian.two_of_forall_mul_self hc hs

end Elem

section Rank

variable {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem finrank_range_conj (ρ : Representation (ZMod 2) G U) (z s t : G) (hst : s = z * t * z⁻¹) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ s - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
  have h1 : ρ z * ρ z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h2 : ρ z⁻¹ * ρ z = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hrel : ρ s - 1 = ρ z * (ρ t - 1) * ρ z⁻¹ := by
    rw [hst, map_mul, map_mul]
    calc ρ z * ρ t * ρ z⁻¹ - 1 = ρ z * ρ t * ρ z⁻¹ - ρ z * ρ z⁻¹ := by rw [h1]
      _ = ρ z * (ρ t - 1) * ρ z⁻¹ := by noncomm_ring
  let e : U ≃ₗ[ZMod 2] U := LinearEquiv.ofLinearMap (ρ z) (ρ z⁻¹)
    (by rw [← Module.End.mul_eq_comp]; exact h1) (by rw [← Module.End.mul_eq_comp]; exact h2)
  have hsurj : LinearMap.range (ρ z⁻¹) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x
    refine ⟨ρ z x, ?_⟩
    rw [← Module.End.mul_apply, h2]
    rfl
  have hcomp : ρ z * (ρ t - 1) * ρ z⁻¹ = (e : U →ₗ[ZMod 2] U) ∘ₗ ((ρ t - 1) ∘ₗ ρ z⁻¹) := rfl
  rw [hrel, hcomp, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ hsurj,
    LinearEquiv.finrank_map_eq]

end Rank

section TypePres

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ} {N : Type} [Group N]
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem alphaP_semilinear_of_stable (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) [L.Normal] {φ : SL(3, F) →* ↥L} (h : Cover φ)
    {A : Subgroup N} {U₀ : Submodule (ZMod 2) V} (hU₀ : IsLSimple σ L U₀)
    (hA₀ : Offender.IsInvariant σ A U₀)
    (hns : ¬ Nonempty (Representation.Equiv (srep σ L φ U₀ hU₀.1) (srep σ L φ U₀ hU₀.1).dual))
    {a : N} (ha : a ∈ A) : alphaP h a ∈ semilinearAutGroup 3 F := by
  by_contra hn
  obtain ⟨B, j, hex⟩ := exists_exchange_lift h hF hf a hn
  have hUU : U₀ = U₀.map (σ a : V →ₗ[ZMod 2] V) := by
    apply le_antisymm
    · intro u hu
      refine ⟨σ a⁻¹ u, hA₀ a⁻¹ (A.inv_mem ha) u hu, ?_⟩
      show σ a (σ a⁻¹ u) = u
      exact ρ_apply_inv σ a u
    · rintro _ ⟨u, hu, rfl⟩
      exact hA₀ a ha u hu
  exact hns (srep_dual_equiv' hf hF σ L φ h.surjective a B j hex U₀ U₀ hU₀.1 hU₀.1 hUU hU₀)

theorem exists_dual_partner (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) [L.Normal] {φ : SL(3, F) →* ↥L} (h : Cover φ)
    (hex : ∃ (g : N) (B : GL (Fin 3) F) (j : ℕ), ∀ x : SL(3, F),
      g * ((φ x : ↥L) : N) * g⁻¹ = ((φ (graphFieldHom B j x) : ↥L) : N))
    (𝒰 : Finset (Submodule (ZMod 2) V)) (h𝒰 : ∀ U ∈ 𝒰, IsLSimple σ L U)
    (hfam : ∀ n, ∀ U ∈ 𝒰, U.map (σ n : V →ₗ[ZMod 2] V) ∈ 𝒰) {U₀ : Submodule (ZMod 2) V}
    (h0 : U₀ ∈ 𝒰)
    (hns : ¬ Nonempty (Representation.Equiv (srep σ L φ U₀ (h𝒰 U₀ h0).1)
      (srep σ L φ U₀ (h𝒰 U₀ h0).1).dual)) :
    ∃ (U₁ : Submodule (ZMod 2) V) (h1 : U₁ ∈ 𝒰), Disjoint U₀ U₁ ∧
      Nonempty (Representation.Equiv (srep σ L φ U₀ (h𝒰 U₀ h0).1)
        (srep σ L φ U₁ (h𝒰 U₁ h1).1).dual) := by
  obtain ⟨g, B, j, hg⟩ := hex
  have hU₁𝒰 : U₀.map (σ g : V →ₗ[ZMod 2] V) ∈ 𝒰 := hfam g U₀ h0
  have hs₀ := h𝒰 U₀ h0
  have hs₁ := h𝒰 _ hU₁𝒰
  have hequiv := srep_dual_equiv hf hF σ L φ h.surjective g B j hg U₀ hs₀.1 hs₁.1 hs₁
  refine ⟨U₀.map (σ g : V →ₗ[ZMod 2] V), hU₁𝒰, ?_, hequiv⟩
  rw [disjoint_iff]
  rcases hs₀.2.2 (U₀ ⊓ U₀.map (σ g : V →ₗ[ZMod 2] V)) (X3.isInvariant_inf hs₀.1 hs₁.1)
    inf_le_left
    with hbot | hfull
  · exact hbot
  · exfalso
    have hle : U₀ ≤ U₀.map (σ g : V →ₗ[ZMod 2] V) := hfull.symm.le.trans inf_le_right
    rcases hs₁.2.2 U₀ hs₀.1 hle with hb | heq
    · exact hs₀.2.1 hb
    · exact hns (srep_dual_equiv' hf hF σ L φ h.surjective g B j hg U₀ U₀ hs₀.1 hs₀.1 heq hs₀)

end TypePres

section Main

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {N : Type} [Group N] [Finite N]
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [Finite N] [Finite V] in
theorem centSub_eq_of_simple (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) [L.Normal]
    (hLq : CFSG.IsQuasisimple ↥L) {A : Subgroup N} [CFSG.IsElementaryAbelian 2 ↥A]
    {U : Submodule (ZMod 2) V} (hU : IsNontrivialLSimple σ L U) (hUA : Offender.IsInvariant σ A U) :
    centSub (σ.comp A.subtype) U = (Subgroup.centralizer (L : Set N)).subgroupOf A := by
  ext a
  rw [mem_centSub, Subgroup.mem_subgroupOf]
  exact fix_iff_centralizer σ L hLq hU (sq_of_mem a.2) (fun u hu => hUA a a.2 u hu)

theorem false_of_dual_pair {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f)
    (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) [L.Normal] (hLq : CFSG.IsQuasisimple ↥L)
    {φ : SL(3, F) →* ↥L} (h : Cover φ) {A : Subgroup N} [CFSG.IsElementaryAbelian 2 ↥A]
    (hquad : QuadAct σ A) (hnc : ¬ A ≤ Subgroup.centralizer (L : Set N))
    {M : Submodule (ZMod 2) V} (hMA : Offender.IsInvariant σ A M)
    (hoff : Nat.card ↥M ≤
      weight (MonoidHom.id (↥M ≃ₗ[ZMod 2] ↥M)) (resSub σ A M hMA).range)
    (hkerM : ∀ a ∈ A, (∀ m ∈ M, σ a m = m) ↔ a ∈ Subgroup.centralizer (L : Set N))
    {U₀ U₁ : Submodule (ZMod 2) V} (hU₀ : IsNontrivialLSimple σ L U₀)
    (hU₁ : IsNontrivialLSimple σ L U₁) (hA₀ : Offender.IsInvariant σ A U₀)
    (hA₁ : Offender.IsInvariant σ A U₁)
    (h0M : U₀ ≤ M) (h1M : U₁ ≤ M) (hdis : Disjoint U₀ U₁)
    (e : Representation.Equiv (srep σ L φ U₀ hU₀.1.1) (srep σ L φ U₁ hU₁.1.1).dual)
    (htp : ∀ a ∈ A, alphaP h a ∈ semilinearAutGroup 3 F) : False := by
  classical
  have hf1 : 1 ≤ f := by omega
  have : Group.IsPerfect ↥L := hLq.1
  set τ : ↥A →* (V ≃ₗ[ZMod 2] V) := σ.comp A.subtype with hτ
  have hMτ : ∀ g : ↥A, ∀ m ∈ M, τ g m ∈ M := fun g m hm => hMA g g.2 m hm
  have h0τ : ∀ g : ↥A, ∀ u ∈ U₀, τ g u ∈ U₀ := fun g u hu => hA₀ g g.2 u hu
  have h1τ : ∀ g : ↥A, ∀ u ∈ U₁, τ g u ∈ U₁ := fun g u hu => hA₁ g g.2 u hu
  set Kc : Subgroup ↥A := (Subgroup.centralizer (L : Set N)).subgroupOf A with hKc
  have hK0 : centSub τ U₀ = Kc := centSub_eq_of_simple σ L hLq hU₀ hA₀
  have hK1 : centSub τ U₁ = Kc := centSub_eq_of_simple σ L hLq hU₁ hA₁
  have hKM : centSub τ M = Kc := by
    ext a
    rw [mem_centSub, hKc, Subgroup.mem_subgroupOf]
    exact hkerM a a.2
  have hoff' : Nat.card ↥M ≤ Kc.index * Nat.card ↥(M ⊓ fixSub τ ⊤) := by
    have h1 := weightId_range τ M hMτ
    rw [hKM] at h1
    rw [← h1]
    exact hoff
  set A₁ : Subgroup ↥A := (OuterAutomorphisms.inner (projectiveSL 3 F)).comap
    ((alphaP h).comp A.subtype) with hA₁def
  have hA1idx : A₁.index ≤ 2 :=
    index_inner_le_two hF hf1 ((alphaP h).comp A.subtype) (fun a => htp a a.2)
      (fun a => Subtype.ext (sq_of_mem a.2))
  have hKA1 : Kc ≤ A₁ := by
    intro a ha
    rw [hKc, Subgroup.mem_subgroupOf] at ha
    rw [hA₁def, Subgroup.mem_comap]
    have h1 : alphaP h (a : N) = 1 := (alphaP_eq_one_iff h (a : N)).2 ha
    show alphaP h (a : N) ∈ _
    rw [h1]
    exact Subgroup.one_mem _
  have hKidx : Kc.relIndex A₁ * A₁.index = Kc.index := Subgroup.relIndex_mul_index hKA1
  have hXM : U₀ ⊔ U₁ ≤ M := sup_le h0M h1M
  have hlift : ∀ a : ↥A, a ∈ A₁ → ∃ s : SL(3, F), s * s = 1 ∧
      (∀ u ∈ U₀, σ a u = σ ((φ s : ↥L) : N) u) ∧ (∀ u ∈ U₁, σ a u = σ ((φ s : ↥L) : N) u) := by
    intro a ha
    obtain ⟨s, hs2, hs⟩ := exists_lift_involution hF hf1 σ L hLq h (a := (a : N))
      (sq_of_mem a.2) ha (fun U => U = U₀ ∨ U = U₁) (by
        rintro U (rfl | rfl)
        · exact ⟨hU₀.1, fun u hu => hA₀ a a.2 u hu⟩
        · exact ⟨hU₁.1, fun u hu => hA₁ a a.2 u hu⟩)
    exact ⟨s, hs2, hs U₀ (Or.inl rfl), hs U₁ (Or.inr rfl)⟩
  by_cases hb : A₁ ≤ Kc
  ·
    have hKeq : A₁ = Kc := le_antisymm hb hKA1
    obtain ⟨a₀, ha₀, ha₀c⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (L : Set N) := by
      by_contra hcon
      push Not at hcon
      exact hnc hcon
    set a : ↥A := ⟨a₀, ha₀⟩ with ha
    have haK : a ∉ Kc := by
      rw [hKc, Subgroup.mem_subgroupOf]
      exact ha₀c
    have hKne : Kc ≠ ⊤ := fun hh => haK (hh ▸ Subgroup.mem_top a)
    have hKidx2 : Kc.index = 2 := by
      have h1 : Kc.index ≠ 1 := fun h1 => hKne (Subgroup.index_eq_one.1 h1)
      have h2 : Kc.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h3 : Kc.index ≤ 2 := by rw [← hKeq]; exact hA1idx
      omega
    set B : Subgroup ↥A := Subgroup.zpowers a with hB
    have haB : a ∈ B := Subgroup.mem_zpowers a
    have hfixB : fixSub τ ⊤ ≤ fixSub τ B := fixSub_anti τ le_top
    have hM2 : Nat.card ↥M ≤ 2 * 1 * Nat.card ↥(M ⊓ fixSub τ B) := by
      calc Nat.card ↥M ≤ Kc.index * Nat.card ↥(M ⊓ fixSub τ ⊤) := hoff'
        _ = 2 * Nat.card ↥(M ⊓ fixSub τ ⊤) := by rw [hKidx2]
        _ ≤ 2 * Nat.card ↥(M ⊓ fixSub τ B) :=
          Nat.mul_le_mul_left _ (card_le_of_le (inf_le_inf_left M hfixB))
        _ = 2 * 1 * Nat.card ↥(M ⊓ fixSub τ B) := by ring
    have hlt : ∀ {U : Submodule (ZMod 2) V}, centSub τ U = Kc → U ⊓ fixSub τ B < U := by
      intro U hU
      refine lt_of_le_of_ne inf_le_left fun heq => ?_
      have hn : a ∉ centSub τ U := by rw [hU]; exact haK
      apply hn
      rw [mem_centSub]
      intro u hu
      have : u ∈ U ⊓ fixSub τ B := by rw [heq]; exact hu
      exact this.2 a haB
    have hU0lt := two_mul_card_le_of_lt (hlt hK0)
    have hU1lt := two_mul_card_le_of_lt (hlt hK1)
    have hfx := card_sup_inf_fix_le τ B hdis (fun b _ => h0τ b) (fun b _ => h1τ b)
    have hXb : 4 * 1 * Nat.card ↥((U₀ ⊔ U₁) ⊓ fixSub τ B) ≤ Nat.card ↥(U₀ ⊔ U₁) := by
      rw [card_sup_of_disjoint hdis]
      have := Nat.mul_le_mul hU0lt hU1lt
      nlinarith [hfx]
    exact fix_codim_contradiction hXM one_pos hM2 hXb
  ·
    have : Finite (↥U₁ ≃ₗ[ZMod 2] ↥U₁) := finite_linearEquiv
    set G₁ : Subgroup (↥U₁ ≃ₗ[ZMod 2] ↥U₁) := A₁.map (resHom τ U₁ h1τ) with hG₁
    have hG₁ea : CFSG.IsElementaryAbelian 2 ↥G₁ := by
      refine isElementaryAbelian_two_of_forall' G₁ ?_ ?_
      · rintro _ ⟨a, -, rfl⟩ _ ⟨c, -, rfl⟩
        rw [← map_mul, ← map_mul, show a * c = c * a from Subtype.ext (comm_of_mem a.2 c.2)]
      · rintro _ ⟨a, -, rfl⟩
        rw [← map_mul, show a * a = 1 from Subtype.ext (sq_of_mem a.2), map_one]
    have := hG₁ea
    obtain ⟨b, hbcard⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 ↥G₁).exists_card_eq
    have hG₁card : Nat.card ↥G₁ = Kc.relIndex A₁ := by
      have h1 := Subgroup.relIndex_ker (K := A₁) (resHom τ U₁ h1τ)
      rw [ker_resHom, hK1] at h1
      exact h1.symm
    obtain ⟨a, ha, haK⟩ : ∃ a ∈ A₁, a ∉ Kc := by
      by_contra hcon
      push Not at hcon
      exact hb hcon
    have hG₁ne : G₁ ≠ ⊥ := by
      intro hbot
      have hmem : resHom τ U₁ h1τ a ∈ G₁ := Subgroup.mem_map.2 ⟨a, ha, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      apply haK
      rw [← hK1, mem_centSub]
      intro u hu
      have := congrArg (fun g : ↥U₁ ≃ₗ[ZMod 2] ↥U₁ => ((g ⟨u, hu⟩ : ↥U₁) : V)) hmem
      simpa [coe_resHom_apply] using this
    have hliftG : ∀ g ∈ G₁, ∃ s : SL(3, F), s * s = 1 ∧
        (g : ↥U₁ →ₗ[ZMod 2] ↥U₁) = srep σ L φ U₁ hU₁.1.1 s := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨s, hs2, -, hs1⟩ := hlift a ha
      refine ⟨s, hs2, LinearMap.ext fun u => Subtype.ext ?_⟩
      rw [srep_apply]
      exact hs1 u u.2
    have hquadG : ∀ g ∈ G₁, ∀ h' ∈ G₁,
        ((g : ↥U₁ →ₗ[ZMod 2] ↥U₁) - 1) ∘ₗ ((h' : ↥U₁ →ₗ[ZMod 2] ↥U₁) - 1) = 0 := by
      rintro _ ⟨a, -, rfl⟩ _ ⟨c, -, rfl⟩
      refine LinearMap.ext fun u => Subtype.ext ?_
      have h2 := hquad c c.2 a a.2 (u : V)
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
        LinearMap.zero_apply, Submodule.coe_sub, Submodule.coe_zero, LinearEquiv.coe_coe,
        coe_resHom_apply]
      rw [map_sub, sub_eq_zero]
      rw [map_sub] at h2
      exact h2
    obtain ⟨g₀, hg₀G, hg₀1⟩ : ∃ g ∈ G₁, g ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hG₁ne ((Subgroup.eq_bot_iff_forall G₁).2 hcon)
    have hne1 : ∀ s : SL(3, F), ∀ g : ↥U₁ ≃ₗ[ZMod 2] ↥U₁, g ≠ 1 →
        (g : ↥U₁ →ₗ[ZMod 2] ↥U₁) = srep σ L φ U₁ hU₁.1.1 s → s ≠ 1 := by
      rintro s g hg1 hgs rfl
      apply hg1
      apply LinearEquiv.ext
      intro u
      have := congrArg (fun T : ↥U₁ →ₗ[ZMod 2] ↥U₁ => T u) hgs
      simpa [srep] using this
    obtain ⟨s₀, hs₀2, hs₀⟩ := hliftG g₀ hg₀G
    have hs₀1 : s₀ ≠ 1 := hne1 s₀ g₀ hg₀1 hs₀
    set r := Module.finrank (ZMod 2) (LinearMap.range ((g₀ : ↥U₁ →ₗ[ZMod 2] ↥U₁) - 1)) with hr
    have hker : ∀ g : SL(3, F), srep σ L φ U₁ hU₁.1.1 g = 1 →
        ∃ a : F, (g : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) a := by
      intro g hg
      obtain ⟨c, -, hc⟩ := srep_ker_scalars σ L hLq h hU₁ g hg
      exact ⟨(c : F), hc⟩
    have hr2 : 2 ≤ r := by
      rw [hr, hs₀]
      exact involution_rank_ge_two hf hF (srep σ L φ U₁ hU₁.1.1) hker s₀ hs₀1 hs₀2
    have hrank : ∀ g ∈ G₁, g ≠ 1 →
        Module.finrank (ZMod 2) (LinearMap.range ((g : ↥U₁ →ₗ[ZMod 2] ↥U₁) - 1)) = r := by
      intro g hg hg1
      obtain ⟨s, hs2, hs⟩ := hliftG g hg
      have hs1 : s ≠ 1 := hne1 s g hg1 hs
      obtain ⟨x, hx⟩ := exists_conj_transvection s hs1 hs2
      obtain ⟨y, hy⟩ := exists_conj_transvection s₀ hs₀1 hs₀2
      have hconj : s = (x * y⁻¹) * s₀ * (x * y⁻¹)⁻¹ := by
        calc s = x * (x⁻¹ * s * x) * x⁻¹ := by group
          _ = x * (y⁻¹ * s₀ * y) * x⁻¹ := by rw [hx, hy]
          _ = (x * y⁻¹) * s₀ * (x * y⁻¹)⁻¹ := by group
      rw [hs, hr, hs₀]
      exact finrank_range_conj (srep σ L φ U₁ hU₁.1.1) (x * y⁻¹) s s₀ hconj
    have he : ∀ γ ∈ A₁, ∀ u : ↥U₀, e.toLinearEquiv (resHom τ U₀ h0τ γ u) =
        (idRep ↥U₁).dual (resHom τ U₁ h1τ γ) (e.toLinearEquiv u) := by
      intro γ hγ u
      obtain ⟨s, hs2, hs0, hs1⟩ := hlift γ hγ
      have h0eq : resHom τ U₀ h0τ γ u = srep σ L φ U₀ hU₀.1.1 s u :=
        Subtype.ext (by rw [srep_apply]; exact hs0 u u.2)
      have hg : resHom τ U₁ h1τ γ = resSub σ L U₁ hU₁.1.1 (φ s) :=
        LinearEquiv.ext fun w => Subtype.ext (by rw [resSub_apply]; exact hs1 w w.2)
      rw [h0eq]
      have hint := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap s u
      refine hint.trans ?_
      have hinv : resSub σ L U₁ hU₁.1.1 (φ s⁻¹) = (resSub σ L U₁ hU₁.1.1 (φ s))⁻¹ := by
        rw [map_inv, map_inv]
      have hdual : (srep σ L φ U₁ hU₁.1.1).dual s =
          (idRep ↥U₁).dual (resSub σ L U₁ hU₁.1.1 (φ s)) := by
        apply LinearMap.ext
        intro w
        apply LinearMap.ext
        intro x
        show w ((resSub σ L U₁ hU₁.1.1 (φ s⁻¹) : ↥U₁ ≃ₗ[ZMod 2] ↥U₁) x) =
          w (((resSub σ L U₁ hU₁.1.1 (φ s))⁻¹ : ↥U₁ ≃ₗ[ZMod 2] ↥U₁) x)
        rw [hinv]
      rw [hg]
      exact congrArg (fun T => T (e.toLinearEquiv u)) hdual
    have hdp := dual_pair_codim τ A₁ h0τ h1τ hdis hG₁ne hquadG hr2 hbcard hrank e.toLinearEquiv he
    have hbp : 0 < 2 ^ b := pow_pos (by norm_num) b
    have hrel : Kc.relIndex A₁ = 2 ^ b := by rw [← hG₁card, hbcard]
    have hM2 : Nat.card ↥M ≤ 2 * 2 ^ b * Nat.card ↥(M ⊓ fixSub τ A₁) := by
      calc Nat.card ↥M ≤ Kc.index * Nat.card ↥(M ⊓ fixSub τ ⊤) := hoff'
        _ = (Kc.relIndex A₁ * A₁.index) * Nat.card ↥(M ⊓ fixSub τ ⊤) := by rw [hKidx]
        _ ≤ (2 ^ b * 2) * Nat.card ↥(M ⊓ fixSub τ A₁) := by
            rw [hrel]
            exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hA1idx)
              (card_le_of_le (inf_le_inf_left M (fixSub_anti τ le_top)))
        _ = 2 * 2 ^ b * Nat.card ↥(M ⊓ fixSub τ A₁) := by ring
    exact fix_codim_contradiction hXM hbp hM2 hdp

theorem selfDual_of_mem {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f)
    (σ : N →* (V ≃ₗ[ZMod 2] V)) (L : Subgroup N) [L.Normal] (hLq : CFSG.IsQuasisimple ↥L)
    {φ : SL(3, F) →* ↥L} (h : Cover φ) {A : Subgroup N} [CFSG.IsElementaryAbelian 2 ↥A]
    (hquad : QuadAct σ A)
    (hex : ∃ (g : N) (B : GL (Fin 3) F) (j : ℕ), ∀ x : SL(3, F),
      g * ((φ x : ↥L) : N) * g⁻¹ = ((φ (graphFieldHom B j x) : ↥L) : N))
    (hnc : ¬ A ≤ Subgroup.centralizer (L : Set N))
    {M : Submodule (ZMod 2) V} (hMA : Offender.IsInvariant σ A M)
    (hoff : Nat.card ↥M ≤
      weight (MonoidHom.id (↥M ≃ₗ[ZMod 2] ↥M)) (resSub σ A M hMA).range)
    (hkerM : ∀ a ∈ A, (∀ m ∈ M, σ a m = m) ↔ a ∈ Subgroup.centralizer (L : Set N))
    (𝒰 : Finset (Submodule (ZMod 2) V))
    (h𝒰 : ∀ U ∈ 𝒰, IsNontrivialLSimple σ L U ∧ Offender.IsInvariant σ A U)
    (hfam : ∀ n, ∀ U ∈ 𝒰, U.map (σ n : V →ₗ[ZMod 2] V) ∈ 𝒰) (hUM : ∀ U ∈ 𝒰, U ≤ M)
    {U₀ : Submodule (ZMod 2) V} (h0 : U₀ ∈ 𝒰) :
    Nonempty (Representation.Equiv (srep σ L φ U₀ (h𝒰 U₀ h0).1.1.1)
      (srep σ L φ U₀ (h𝒰 U₀ h0).1.1.1).dual) := by
  by_contra hns
  have hf1 : 1 ≤ f := by omega
  have hsimp : ∀ U ∈ 𝒰, IsLSimple σ L U := fun U hU => (h𝒰 U hU).1.1
  obtain ⟨U₁, h1, hdis, ⟨e⟩⟩ := exists_dual_partner hF hf1 σ L h hex 𝒰 hsimp hfam h0 hns
  have htp : ∀ a ∈ A, alphaP h a ∈ semilinearAutGroup 3 F := fun a ha =>
    alphaP_semilinear_of_stable hF hf1 σ L h (hsimp U₀ h0) (h𝒰 U₀ h0).2 hns ha
  exact false_of_dual_pair hf hF σ L hLq h hquad hnc hMA hoff hkerM (h𝒰 U₀ h0).1 (h𝒰 U₁ h1).1
    (h𝒰 U₀ h0).2 (h𝒰 U₁ h1).2 (hUM U₀ h0) (hUM U₁ h1) hdis e htp

end Main

end CFSG.QuasithinUnique.Setup.X7Sec
