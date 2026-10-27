module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Engine
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.OddExact

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
open scoped commutatorElement

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

abbrev SecQ (Z₀ Z₁ : Submodule (ZMod 2) W) : Type _ := ↥Z₁ ⧸ Z₀.comap Z₁.subtype

section Rep

variable (ρ : Representation (ZMod 2) G W) (H : Subgroup G) {Z₀ Z₁ : Submodule (ZMod 2) W}
  (h₀ : GeneralFF.IsInvariant ρ H Z₀) (h₁ : GeneralFF.IsInvariant ρ H Z₁)

@[expose] noncomputable def secOp (h : ↥H) : Module.End (ZMod 2) (SecQ Z₀ Z₁) :=
  (Z₀.comap Z₁.subtype).mapQ (Z₀.comap Z₁.subtype)
    ((ρ h).restrict (fun x hx => h₁ h h.2 x hx)) (fun _ hz => h₀ h h.2 _ hz)

@[expose] noncomputable def secRep : Representation (ZMod 2) ↥H (SecQ Z₀ Z₁) where
  toFun := secOp ρ H h₀ h₁
  map_one' := by
    ext z
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    simp
  map_mul' a b := by
    ext z
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    simp

theorem secRep_mk (h : ↥H) (z : ↥Z₁) :
    secRep ρ H h₀ h₁ h (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨ρ h z, h₁ h h.2 z z.2⟩ := rfl

end Rep

section Dim

variable [Finite W]

theorem finrank_secQ {Z₀ Z₁ : Submodule (ZMod 2) W} (hle : Z₀ ≤ Z₁) :
    Module.finrank (ZMod 2) (SecQ Z₀ Z₁) + Module.finrank (ZMod 2) Z₀ =
      Module.finrank (ZMod 2) Z₁ := by
  have h1 : Module.finrank (ZMod 2) (SecQ Z₀ Z₁) +
      Module.finrank (ZMod 2) ↥(Z₀.comap Z₁.subtype) = Module.finrank (ZMod 2) Z₁ :=
    Submodule.finrank_quotient_add_finrank (Z₀.comap Z₁.subtype)
  have h2 : Module.finrank (ZMod 2) ↥(Z₀.comap Z₁.subtype) = Module.finrank (ZMod 2) Z₀ :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  omega

theorem finrank_comap_mkQ {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (P : Submodule (ZMod 2) V) (F : Submodule (ZMod 2) (V ⧸ P)) :
    Module.finrank (ZMod 2) ↥(F.comap P.mkQ) =
      Module.finrank (ZMod 2) ↥F + Module.finrank (ZMod 2) ↥P := by
  let g : ↥(F.comap P.mkQ) →ₗ[ZMod 2] ↥F := P.mkQ.restrict (fun x hx => hx)
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hrange : LinearMap.range g = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hPle : P ≤ F.comap P.mkQ := fun x hx => by
    simp [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hx]
  have hker : LinearMap.ker g = P.comap (F.comap P.mkQ).subtype := by
    ext ⟨x, hx⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      have h' : P.mkQ x = 0 := congrArg Subtype.val h
      exact (Submodule.Quotient.mk_eq_zero P).1 h'
    · intro h
      refine Subtype.ext ?_
      exact (Submodule.Quotient.mk_eq_zero P).2 h
  have key := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, finrank_top, hker] at key
  have e : Module.finrank (ZMod 2) ↥(P.comap (F.comap P.mkQ).subtype) =
      Module.finrank (ZMod 2) ↥P := (Submodule.comapSubtypeEquivOfLe hPle).finrank_eq
  omega

variable {ρ : Representation (ZMod 2) G W} {H : Subgroup G} {Z₀ Z₁ : Submodule (ZMod 2) W}

theorem secCod_eq (h₀ : GeneralFF.IsInvariant ρ H Z₀) (h₁ : GeneralFF.IsInvariant ρ H Z₁) (hle : Z₀ ≤ Z₁)
    {B : Subgroup G} (hBH : B ≤ H) :
    secCod ρ B Z₀ Z₁ = Module.finrank (ZMod 2) (SecQ Z₀ Z₁) -
      Module.finrank (ZMod 2) ↥(fixSub (secRep ρ H h₀ h₁) (B.subgroupOf H)) := by
  set P := Z₀.comap Z₁.subtype with hP
  set F := fixSub (secRep ρ H h₀ h₁) (B.subgroupOf H) with hF
  have hrel : relFix ρ B Z₀ Z₁ = (F.comap P.mkQ).map Z₁.subtype := by
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      refine ⟨⟨y, hy1⟩, ?_, rfl⟩
      intro a ha
      show secRep ρ H h₀ h₁ a (Submodule.Quotient.mk ⟨y, hy1⟩) = Submodule.Quotient.mk ⟨y, hy1⟩
      rw [secRep_mk, Submodule.Quotient.eq]
      exact hy2 a ha
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, fun b hb => ?_⟩
      have := hz ⟨b, hBH hb⟩ hb
      change secRep ρ H h₀ h₁ ⟨b, hBH hb⟩ (Submodule.Quotient.mk z) = Submodule.Quotient.mk z
        at this
      rw [secRep_mk, Submodule.Quotient.eq] at this
      exact this
  have h1 : Module.finrank (ZMod 2) ↥(relFix ρ B Z₀ Z₁) =
      Module.finrank (ZMod 2) ↥F + Module.finrank (ZMod 2) ↥P := by
    rw [hrel, Submodule.finrank_map_subtype_eq, finrank_comap_mkQ]
  have h2 := finrank_secQ hle
  have h3 : Module.finrank (ZMod 2) ↥P = Module.finrank (ZMod 2) Z₀ :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  unfold secCod
  omega

theorem kerDim_sub_eq (h₀ : GeneralFF.IsInvariant ρ H Z₀) (h₁ : GeneralFF.IsInvariant ρ H Z₁) (hle : Z₀ ≤ Z₁)
    {f g : Polynomial (ZMod 2)} (hcop : IsCoprime f g) {x : G} (hx : x ∈ H)
    (hfg : Polynomial.aeval (ρ x) (f * g) = 0) :
    (kerDim ρ f x Z₁ : ℤ) - kerDim ρ f x Z₀ =
      Module.finrank (ZMod 2) ↥(LinearMap.ker (Polynomial.aeval (secRep ρ H h₀ h₁ ⟨x, hx⟩) f)) := by
  have key := finrank_inf_ker_aeval_eq hcop hfg hle (fun y hy => h₀ x hx y hy)
    (fun y hy => h₁ x hx y hy)
  have key' : kerDim ρ f x Z₁ = kerDim ρ f x Z₀ +
      Module.finrank (ZMod 2) ↥(LinearMap.ker (Polynomial.aeval (secRep ρ H h₀ h₁ ⟨x, hx⟩) f)) :=
    key
  omega

omit [Finite W] in
theorem secTrivial_iff (h₀ : GeneralFF.IsInvariant ρ H Z₀) (h₁ : GeneralFF.IsInvariant ρ H Z₁) {K : Subgroup G}
    (hKH : K ≤ H) :
    SecTrivial ρ K Z₀ Z₁ ↔ ∀ k ∈ K.subgroupOf H, ∀ q, secRep ρ H h₀ h₁ k q = q := by
  constructor
  · intro h k hk q
    induction q using Submodule.Quotient.induction_on with
    | _ z =>
      rw [secRep_mk, Submodule.Quotient.eq]
      exact h k hk z z.2
  · intro h k hk v hv
    have := h ⟨k, hKH hk⟩ hk (Submodule.Quotient.mk ⟨v, hv⟩)
    rw [secRep_mk, Submodule.Quotient.eq] at this
    exact this

omit [Finite W] in
theorem secRep_irreducible (hmin : IsMinSec ρ H Z₀ Z₁) :
    Nontrivial (SecQ Z₀ Z₁) ∧ ∀ N : Submodule (ZMod 2) (SecQ Z₀ Z₁),
      (∀ h : ↥H, ∀ q ∈ N, secRep ρ H hmin.1 hmin.2.1 h q ∈ N) → N = ⊥ ∨ N = ⊤ := by
  obtain ⟨hZ₀, hZ₁, hlt, hbetween⟩ := hmin
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz1, hz0⟩ := Set.exists_of_ssubset hlt
    refine ⟨⟨Submodule.Quotient.mk ⟨z, hz1⟩, 0, ?_⟩⟩
    intro h
    have := (Submodule.Quotient.mk_eq_zero (Z₀.comap Z₁.subtype)).1 h
    exact hz0 this
  · intro N hN
    let Z : Submodule (ZMod 2) W := (N.comap (Z₀.comap Z₁.subtype).mkQ).map Z₁.subtype
    have hZ0Z : Z₀ ≤ Z := by
      intro z hz
      refine ⟨⟨z, hlt.le hz⟩, ?_, rfl⟩
      show (Z₀.comap Z₁.subtype).mkQ ⟨z, hlt.le hz⟩ ∈ N
      have h0 : (Submodule.Quotient.mk (⟨z, hlt.le hz⟩ : ↥Z₁) : SecQ Z₀ Z₁) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hz
      rw [Submodule.mkQ_apply, h0]
      exact N.zero_mem
    have hZZ1 : Z ≤ Z₁ := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have hZinv : GeneralFF.IsInvariant ρ H Z := by
      rintro a ha _ ⟨y, hy, rfl⟩
      refine ⟨⟨ρ a y, hZ₁ a ha y y.2⟩, ?_, rfl⟩
      have := hN ⟨a, ha⟩ _ hy
      exact this
    rcases hbetween Z hZinv hZ0Z hZZ1 with h | h
    · left
      rw [eq_bot_iff]
      intro q hq
      induction q using Submodule.Quotient.induction_on with
      | _ y =>
        have hy : (y : W) ∈ Z := ⟨y, hq, rfl⟩
        rw [h] at hy
        rw [Submodule.mem_bot]
        exact (Submodule.Quotient.mk_eq_zero _).2 hy
    · right
      rw [eq_top_iff]
      intro q _
      induction q using Submodule.Quotient.induction_on with
      | _ y =>
        have hy : (y : W) ∈ Z := by rw [h]; exact y.2
        obtain ⟨y', hy', hyy⟩ := hy
        have : y' = y := Subtype.ext hyy
        subst this
        exact hy'

end Dim

section Min

variable [Finite W] {ρ : Representation (ZMod 2) G W}

theorem exists_isMinSec_not_secTrivial {K B : Subgroup G} (hK : ⁅K, K⁆ = K)
    {Y₀ Y₁ : Submodule (ZMod 2) W} (h₀ : GeneralFF.IsInvariant ρ (K ⊔ B) Y₀)
    (h₁ : GeneralFF.IsInvariant ρ (K ⊔ B) Y₁) (hle : Y₀ ≤ Y₁) (hnt : ¬ SecTrivial ρ K Y₀ Y₁) :
    ∃ Z₀ Z₁, Y₀ ≤ Z₀ ∧ Z₁ ≤ Y₁ ∧ IsMinSec ρ (K ⊔ B) Z₀ Z₁ ∧ ¬ SecTrivial ρ K Z₀ Z₁ := by
  suffices H : ∀ n : ℕ, ∀ Z₀ Z₁ : Submodule (ZMod 2) W,
      Module.finrank (ZMod 2) Z₁ - Module.finrank (ZMod 2) Z₀ = n → Z₀ ≤ Z₁ →
      GeneralFF.IsInvariant ρ (K ⊔ B) Z₀ → GeneralFF.IsInvariant ρ (K ⊔ B) Z₁ → ¬ SecTrivial ρ K Z₀ Z₁ →
      ∃ A₀ A₁, Z₀ ≤ A₀ ∧ A₁ ≤ Z₁ ∧ IsMinSec ρ (K ⊔ B) A₀ A₁ ∧ ¬ SecTrivial ρ K A₀ A₁ from
    H _ Y₀ Y₁ rfl hle h₀ h₁ hnt
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Z₀ Z₁ hn hle hZ₀ hZ₁ hnt
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq
    exfalso
    apply hnt
    intro k hk v hv
    exact Z₀.sub_mem (hZ₀ k (Subgroup.mem_sup_left hk) v hv) hv
  · by_cases hex : ∃ Z, GeneralFF.IsInvariant ρ (K ⊔ B) Z ∧ Z₀ < Z ∧ Z < Z₁
    · obtain ⟨Z, hZ, h0Z, hZ1⟩ := hex
      have hfr0 : Module.finrank (ZMod 2) Z₀ < Module.finrank (ZMod 2) Z :=
        Submodule.finrank_lt_finrank_of_lt h0Z
      have hfr1 : Module.finrank (ZMod 2) Z < Module.finrank (ZMod 2) Z₁ :=
        Submodule.finrank_lt_finrank_of_lt hZ1
      by_cases ht : SecTrivial ρ K Z₀ Z
      · have hnt' : ¬ SecTrivial ρ K Z Z₁ := fun ht' => hnt (secTrivial_trans hK ht ht')
        obtain ⟨A₀, A₁, hA₀, hA₁, hmin, hAnt⟩ := ih (Module.finrank (ZMod 2) Z₁ -
          Module.finrank (ZMod 2) Z) (by omega) Z Z₁ rfl hZ1.le hZ hZ₁ hnt'
        exact ⟨A₀, A₁, h0Z.le.trans hA₀, hA₁, hmin, hAnt⟩
      · obtain ⟨A₀, A₁, hA₀, hA₁, hmin, hAnt⟩ := ih (Module.finrank (ZMod 2) Z -
          Module.finrank (ZMod 2) Z₀) (by omega) Z₀ Z rfl h0Z.le hZ₀ hZ ht
        exact ⟨A₀, A₁, hA₀, hA₁.trans hZ1.le, hmin, hAnt⟩
    · refine ⟨Z₀, Z₁, le_rfl, le_rfl, ⟨hZ₀, hZ₁, hlt, fun Z hZ h1 h2 => ?_⟩, hnt⟩
      by_contra hne
      push Not at hne
      exact hex ⟨Z, hZ, lt_of_le_of_ne h1 hne.1.symm, lt_of_le_of_ne h2 hne.2⟩

end Min

section Offender

variable [Finite W] {ρ : Representation (ZMod 2) G W}

theorem two_pow_secCod_le {K B : Subgroup G} {U : Submodule (ZMod 2) W}
    (hb : IsBestOffenderOn ρ B U)
    (hcen : ∀ b ∈ B, (∀ k ∈ K, b * k = k * b) → ∀ u ∈ U, ρ b u = u) :
    2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card B := by
  set C := B ⊓ Subgroup.centralizer (K : Set G) with hC
  have h1 := hb.2 C inf_le_left
  have hfixC : fixOn ρ C U = U := by
    ext v
    constructor
    · exact fun h => h.1
    · intro hv
      refine ⟨hv, fun a ha => ?_⟩
      exact hcen a ha.1 (fun k hk => (Subgroup.mem_centralizer_iff.1 ha.2 k hk).symm) v hv
  have hrel : relFix ρ B ⊥ U = fixOn ρ B U := by
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨hy1, fun b hb' => sub_eq_zero.1 (Submodule.mem_bot _ |>.1 (hy2 b hb'))⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨hy1, fun b hb' => by rw [hy2 b hb', sub_self]; exact Submodule.zero_mem _⟩
  have hcard : ∀ S : Submodule (ZMod 2) W, Nat.card ↥S = 2 ^ Module.finrank (ZMod 2) ↥S := by
    intro S
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hle : fixOn ρ B U ≤ U := fun v hv => hv.1
  have hc : Module.finrank (ZMod 2) ↥(fixOn ρ B U) ≤ Module.finrank (ZMod 2) ↥U :=
    Submodule.finrank_mono hle
  have hsc : secCod ρ B ⊥ U =
      Module.finrank (ZMod 2) ↥U - Module.finrank (ZMod 2) ↥(fixOn ρ B U) := by
    unfold secCod
    rw [hrel]
  rw [hfixC, hcard U, hcard (fixOn ρ B U)] at h1
  have hpos : 0 < 2 ^ Module.finrank (ZMod 2) ↥(fixOn ρ B U) := by positivity
  apply Nat.le_of_mul_le_mul_right _ hpos
  rw [hsc]
  calc 2 ^ (Module.finrank (ZMod 2) ↥U - Module.finrank (ZMod 2) ↥(fixOn ρ B U)) * Nat.card ↥C *
        2 ^ Module.finrank (ZMod 2) ↥(fixOn ρ B U)
      = Nat.card ↥C * 2 ^ Module.finrank (ZMod 2) ↥U := by
        rw [mul_comm _ (Nat.card ↥C), mul_assoc, ← pow_add, Nat.sub_add_cancel hc]
    _ ≤ _ := h1

end Offender

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
