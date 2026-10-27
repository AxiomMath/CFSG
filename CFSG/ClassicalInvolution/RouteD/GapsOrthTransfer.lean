module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthFacts
public import CFSG.ClassicalInvolution.RouteD.GapsOrthExcl
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open scoped commutatorElement MatrixGroups

section Commute

variable {G : Type} [Group G]

theorem commute_of_commutator_central {L : Subgroup G} (hL : ⁅L, L⁆ = L) {b : G}
    (hc : ∀ a ∈ L, ⁅a, b⁆ ∈ Subgroup.center G) : ∀ a ∈ L, a * b = b * a := by
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  let f : ↥L →* Subgroup.center G :=
    { toFun := fun a => ⟨⁅(a : G), b⁆, hc a a.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a a'
        have hc' := Subgroup.mem_center_iff.mp (hc a' a'.2)
        apply Subtype.ext
        change ⁅((a * a' : ↥L) : G), b⁆ = ⁅(a : G), b⁆ * ⁅(a' : G), b⁆
        have e : ⁅((a * a' : ↥L) : G), b⁆ = (a : G) * ⁅(a' : G), b⁆ * (a : G)⁻¹ * ⁅(a : G), b⁆ := by
          simp only [Subgroup.coe_mul, commutatorElement_def]
          group
        rw [e, hc' (a : G)]
        have h3 := hc' ⁅(a : G), b⁆
        calc ⁅(a' : G), b⁆ * (a : G) * (a : G)⁻¹ * ⁅(a : G), b⁆ = ⁅(a' : G), b⁆ * ⁅(a : G), b⁆ := by
              group
          _ = ⁅(a : G), b⁆ * ⁅(a' : G), b⁆ := h3.symm }
  have hrange : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  intro a ha
  have h1 : (⟨f ⟨a, ha⟩, ⟨a, ha⟩, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  have h2 : ⁅a, b⁆ = 1 := by
    have := congrArg (fun x : f.range => ((x : Subgroup.center G) : G)) h1
    simpa [f] using this
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

variable {X : Type} [Group X] {π : G →* X}

theorem commutes_of_map_commutes (hker : π.ker ≤ Subgroup.center G) {L M : Subgroup G}
    (hL : ⁅L, L⁆ = L) (h : Commutes (L.map π) (M.map π)) : Commutes L M := by
  intro a ha b hb
  refine commute_of_commutator_central hL (b := b) (fun a' ha' => hker ?_) a ha
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
    h _ ⟨a', ha', rfl⟩ _ ⟨b, hb, rfl⟩]
  group

theorem commutes_map_iff (hker : π.ker ≤ Subgroup.center G) {L M : Subgroup G} (hL : ⁅L, L⁆ = L) :
    Commutes (L.map π) (M.map π) ↔ Commutes L M := by
  refine ⟨commutes_of_map_commutes hker hL, ?_⟩
  rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, h x hx y hy]

end Commute

section StdPair

variable {F : Type} [Field F] {KY X : Type} [Group KY] [Group X]

theorem commutator_top_specialLinear_three :
    ⁅(⊤ : Subgroup SL(3, F)), (⊤ : Subgroup SL(3, F))⁆ = (⊤ : Subgroup SL(3, F)) := by
  have h : Group.IsPerfect SL(3, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3) le_rfl
  have h1 := h.commutator_eq_top
  rwa [commutator_def] at h1

theorem linearBlockStandardPair_map (π : KY →* X) (hker : π.ker ≤ Subgroup.center KY)
    {W U V : Subgroup KY} (h : LinearBlockStandardPair F W U V) :
    LinearBlockStandardPair F (W.map π) (U.map π) (V.map π) := by
  obtain ⟨θ, c, hrange, hθ, hUV⟩ := h
  refine ⟨π.comp θ, c, by rw [MonoidHom.range_comp, hrange], ?_, ?_⟩
  · intro s hs
    have hsc : θ s ∈ Subgroup.center KY := hker hs
    have hcomm := commute_of_commutator_central (L := (⊤ : Subgroup SL(3, F)))
      commutator_top_specialLinear_three (b := s) (fun t _ => hθ (by
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
          Subgroup.mem_center_iff.mp hsc (θ t)]
        group))
    rw [Subgroup.mem_center_iff]
    intro t
    exact hcomm t (Subgroup.mem_top t)
  · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [← Subgroup.map_map, h1], by rw [← Subgroup.map_map, h2]⟩
    · exact Or.inr ⟨by rw [← Subgroup.map_map, h1], by rw [← Subgroup.map_map, h2]⟩

theorem blocks_perfect [Finite F] (h4 : 4 ≤ Nat.card F) :
    ⁅B12 F, B12 F⁆ = B12 F ∧ ⁅B23 F, B23 F⁆ = B23 F := by
  have : Group.IsPerfect SL(2, F) := sl2_isPerfect h4
  exact ⟨Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _),
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)⟩

theorem map_blocks_perfect [Finite F] (h4 : 4 ≤ Nat.card F) (α : SL(3, F) →* KY) :
    ⁅(B12 F).map α, (B12 F).map α⁆ = (B12 F).map α ∧
      ⁅(B23 F).map α, (B23 F).map α⁆ = (B23 F).map α := by
  obtain ⟨h1, h2⟩ := blocks_perfect h4
  exact ⟨by rw [← Subgroup.map_commutator, h1], by rw [← Subgroup.map_commutator, h2]⟩

theorem exists_lin_of_map {p : ℕ} [Fact p.Prime] [Finite F] [CharP F p] (h4 : 4 ≤ Nat.card F)
    [Finite KY] (hC : ¬ p ∣ Nat.card (Subgroup.center KY)) (ψ : KY →* X)
    (hker : ψ.ker ≤ Subgroup.center KY) {R₁ R₂ : Subgroup KY} (hR₁ : ⁅R₁, R₁⁆ = R₁)
    (hR₂ : ⁅R₂, R₂⁆ = R₂) (h : ∃ W, LinearBlockStandardPair F W (R₁.map ψ) (R₂.map ψ)) :
    ∃ W, LinearBlockStandardPair F W R₁ R₂ := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨θ, hrange, hθ, hU, hV⟩ := WeakCT.pair_normalize hW
  have hWsup := linear_eq_sup hW
  have hle : θ.range ≤ ψ.range := by
    rw [hrange, hWsup]
    exact sup_le (Subgroup.map_le_range ψ R₁) (Subgroup.map_le_range ψ R₂)
  let θ' : SL(3, F) →* ψ.range := θ.codRestrict ψ.range fun s => hle ⟨s, rfl⟩
  have hπ : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hπker : ψ.rangeRestrict.ker ≤ Subgroup.center KY := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hπC : ¬ p ∣ Nat.card ψ.rangeRestrict.ker := fun hd =>
    hC (hd.trans (Subgroup.card_dvd_of_le hπker))
  obtain ⟨α, hα, -⟩ := ModelFacts.LinearAut.sl_existsUnique_lift (n := 3) (K := F) (p := p)
    (by norm_num) hπ hπker hπC θ'
  have hαψ : ∀ s, ψ (α s) = θ s := fun s => congrArg Subtype.val (DFunLike.congr_fun hα s)
  have hψα : ψ.comp α = θ := MonoidHom.ext hαψ
  obtain ⟨hp₁, hp₂⟩ := map_blocks_perfect h4 α
  have hR₁' : (B12 F).map α = R₁ :=
    ModelFacts.eq_of_map_eq_of_isPerfect ψ hker hp₁ hR₁ (by rw [Subgroup.map_map, hψα, hU])
  have hR₂' : (B23 F).map α = R₂ :=
    ModelFacts.eq_of_map_eq_of_isPerfect ψ hker hp₂ hR₂ (by rw [Subgroup.map_map, hψα, hV])
  have hid : (MulAut.conj (1 : SL(3, F))⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext; simp
  refine ⟨α.range, α, 1, rfl, fun s hs => hθ ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.mem_ker, ← hαψ, hs, map_one]
  · rw [hid, Subgroup.map_id, hR₁']
  · rw [hid, Subgroup.map_id, hR₂']

end StdPair

section Quot

variable {KY X : Type} [Group KY] [Group X] {F : Type} [Field F] [Finite F]

structure CentralQuot (π : KY →* X) (𝓕 : Set (Subgroup KY)) (𝓕' : Set (Subgroup X))
    (Z' : Subgroup X) : Prop where
  ker_le : π.ker ≤ Subgroup.center KY
  center_le : ∀ z ∈ Subgroup.center KY, π z ∈ Z'
  perf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R
  inj : ∀ R ∈ 𝓕, ∀ r ∈ R, π r = 1 → r = 1
  map_mem : ∀ R ∈ 𝓕, R.map π ∈ 𝓕'
  surj : ∀ L ∈ 𝓕', ∃ R ∈ 𝓕, R.map π = L

variable {π : KY →* X} {𝓕 : Set (Subgroup KY)} {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

namespace CentralQuot

theorem map_inj (h : CentralQuot π 𝓕 𝓕' Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    (e : R.map π = R'.map π) : R = R' :=
  ModelFacts.eq_of_map_eq_of_isPerfect π h.ker_le (h.perf R hR) (h.perf R' hR') e

theorem commutes_iff (h : CentralQuot π 𝓕 𝓕' Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕) :
    Commutes (R.map π) (R'.map π) ↔ Commutes R R' :=
  commutes_map_iff h.ker_le (h.perf R hR)

theorem invOf (h : CentralQuot π 𝓕 𝓕' Z') {R : Subgroup KY} (hR : R ∈ 𝓕) {r : KY}
    (hr : InvOf R r) : InvOf (R.map π) (π r) := by
  refine ⟨⟨r, hr.1, rfl⟩, ?_⟩
  have h1 : π r ≠ 1 := fun h1 => by
    have h2 := h.inj R hR r hr.1 h1
    have h3 := hr.2
    rw [h2, orderOf_one] at h3
    omega
  have h2 : π r ^ 2 = 1 := by
    rw [← map_pow, ← hr.2, pow_orderOf_eq_one, map_one]
  exact orderOf_eq_prime h2 h1

theorem modelInvComm (h : CentralQuot π 𝓕 𝓕' Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕)
    (hR' : R' ∈ 𝓕) (hm : ModelInvComm (Subgroup.center KY) R R') :
    ModelInvComm Z' (R.map π) (R'.map π) := by
  obtain ⟨r, r', hr, hr', hc⟩ := hm
  refine ⟨π r, π r', h.invOf hR hr, h.invOf hR' hr', ?_⟩
  rw [← map_commutatorElement]
  exact h.center_le _ hc

theorem modelAdj (h : CentralQuot π 𝓕 𝓕' Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    (ha : ModelAdj (Subgroup.center KY) R R') : ModelAdj Z' (R.map π) (R'.map π) := by
  obtain ⟨hne, hnc, r, r', hr, hr', hc, hnorm⟩ := ha
  refine ⟨fun e => hne (h.map_inj hR hR' e), fun hc' => hnc ((h.commutes_iff hR).mp hc'), π r,
    π r', h.invOf hR hr, h.invOf hR' hr', ?_, ?_⟩
  · rw [← map_commutatorElement]
    exact h.center_le _ hc
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨r' * x * r'⁻¹, hnorm x hx, ?_⟩
    simp [map_mul, map_inv]

theorem modelIndist (h : CentralQuot π 𝓕 𝓕' Z') {R R' : Subgroup KY} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    (hne : R ≠ R') (hi : ModelIndist Z' 𝓕' (R.map π) (R'.map π)) :
    ModelIndist (Subgroup.center KY) 𝓕 R R' := by
  refine ⟨hne, fun S hS hSR hSR' hI hI' => ?_⟩
  have := hi.2 (S.map π) (h.map_mem S hS) (fun e => hSR (h.map_inj hS hR e))
    (fun e => hSR' (h.map_inj hS hR' e)) (h.modelInvComm hS hR hI) (h.modelInvComm hS hR' hI')
  rwa [h.commutes_iff hS, h.commutes_iff hS] at this

theorem orthGeom (h : CentralQuot π 𝓕 𝓕' Z') (hG : OrthGeom Z' 𝓕' F)
    (hlift : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, (∃ W, LinearBlockStandardPair F W (R₁.map π) (R₂.map π)) →
      ∃ W, LinearBlockStandardPair F W R₁ R₂) :
    OrthGeom (Subgroup.center KY) 𝓕 F where
  star := by
    intro c hc l₁ h₁ l₂ h₂ l₃ h₃ a₁ a₂ a₃ n12 n13 n23 k12 k13 k23
    have := hG.star (c.map π) (h.map_mem c hc) (l₁.map π) (h.map_mem l₁ h₁) (l₂.map π)
      (h.map_mem l₂ h₂) (l₃.map π) (h.map_mem l₃ h₃) (h.modelAdj hc h₁ a₁) (h.modelAdj hc h₂ a₂)
      (h.modelAdj hc h₃ a₃) (fun e => n12 (h.map_inj h₁ h₂ e)) (fun e => n13 (h.map_inj h₁ h₃ e))
      (fun e => n23 (h.map_inj h₂ h₃ e)) ((h.commutes_iff h₁).mpr k12)
      ((h.commutes_iff h₁).mpr k13) ((h.commutes_iff h₂).mpr k23)
    rcases this with hi | hi | hi
    · exact Or.inl (h.modelIndist h₁ h₂ n12 hi)
    · exact Or.inr (Or.inl (h.modelIndist h₁ h₃ n13 hi))
    · exact Or.inr (Or.inr (h.modelIndist h₂ h₃ n23 hi))
  sign := by
    intro R₁ h₁ R₂ h₂ R₃ h₃ a₁ a₃ k13 ⟨W, hW⟩
    obtain ⟨W', hW'⟩ := hG.sign (R₁.map π) (h.map_mem R₁ h₁) (R₂.map π) (h.map_mem R₂ h₂)
      (R₃.map π) (h.map_mem R₃ h₃) (h.modelAdj h₁ h₂ a₁) (h.modelAdj h₃ h₂ a₃)
      ((h.commutes_iff h₁).mpr k13) ⟨_, linearBlockStandardPair_map π h.ker_le hW⟩
    exact hlift R₂ h₂ R₃ h₃ ⟨W', hW'⟩
  perp2 := by
    intro R₁ h₁ R₂ h₂ ha ⟨W, hW⟩
    obtain ⟨S₁', hS₁', S₂', hS₂', hne, c₁, c₂, n₁, n₂⟩ := hG.perp2 (R₁.map π)
      (h.map_mem R₁ h₁) (R₂.map π) (h.map_mem R₂ h₂) (h.modelAdj h₁ h₂ ha)
      ⟨_, linearBlockStandardPair_map π h.ker_le hW⟩
    obtain ⟨S₁, hS₁, rfl⟩ := h.surj S₁' hS₁'
    obtain ⟨S₂, hS₂, rfl⟩ := h.surj S₂' hS₂'
    exact ⟨S₁, hS₁, S₂, hS₂, fun e => hne (by rw [e]), (h.commutes_iff h₁).mp c₁,
      (h.commutes_iff h₁).mp c₂, fun hc => n₁ ((h.commutes_iff h₂).mpr hc),
      fun hc => n₂ ((h.commutes_iff h₂).mpr hc)⟩

theorem orthFacts {p : ℕ} [Fact p.Prime] [CharP F p] (h4 : 4 ≤ Nat.card F) [Finite KY]
    (hC : ¬ p ∣ Nat.card (Subgroup.center KY)) (h : CentralQuot π 𝓕 𝓕' Z')
    (hG : OrthGeom Z' 𝓕' F) : OrthFacts 𝓕 F :=
  { toOrthGeom := h.orthGeom hG fun R₁ h₁ R₂ h₂ hl =>
      exists_lin_of_map h4 hC π h.ker_le (h.perf R₁ h₁) (h.perf R₂ h₂) hl
    lift := fun ψ hψ R₁ h₁ R₂ h₂ hl =>
      exists_lin_of_map h4 hC ψ hψ (h.perf R₁ h₁) (h.perf R₂ h₂) hl }

end CentralQuot

end Quot

end CFSG.ClassicalInvolution.RouteD.Gaps
