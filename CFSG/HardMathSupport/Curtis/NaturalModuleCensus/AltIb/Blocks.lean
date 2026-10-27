module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Core
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Quasisimple
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Transfer
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Reduce

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbedding.LieOut
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open scoped commutatorElement

theorem noAp_center_quotient_of_surjective {p : ℕ} {A B : Type} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (h : NoAp p (B ⧸ Subgroup.center B)) :
    NoAp p (A ⧸ Subgroup.center A) := by
  have hc : Subgroup.center A ≤ Subgroup.comap f (Subgroup.center B) := by
    intro a ha
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro b
    obtain ⟨a', rfl⟩ := hf b
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 ha a']
  let g : A ⧸ Subgroup.center A →* B ⧸ Subgroup.center B := QuotientGroup.map _ _ f hc
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨QuotientGroup.mk a, rfl⟩
  intro R _ _ ι hι φ hφ
  exact h R ι hι (g.comp φ) (hg.comp hφ)

theorem commute_of_map_commute {Γ : Type*} [Group Γ] {A B : Subgroup Γ} (hA : ⁅A, A⁆ = A)
    (h : ∀ a ∈ A, ∀ b ∈ B, (QuotientGroup.mk a : Γ ⧸ Subgroup.center Γ) *
      QuotientGroup.mk b = QuotientGroup.mk b * QuotientGroup.mk a) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have hcen : ∀ g ∈ A, ⁅g, b⁆ ∈ Subgroup.center Γ := by
    intro g hg
    rw [← QuotientGroup.ker_mk' (Subgroup.center Γ), MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact h g hg b hb
  have hle : ⁅A, A⁆ ≤ Subgroup.centralizer ({b} : Set Γ) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := commutator_commutator_eq_one_of_central (hcen g₁ hg₁) (hcen g₂ hg₂)
    rw [commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  rw [hA] at hle
  exact (Subgroup.mem_centralizer_iff.1 (hle ha) b (Set.mem_singleton b)).symm


@[expose] def AltIbCell (𝔉 : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → 𝔉 (↥L ⧸ Subgroup.center ↥L) →
    IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, (p = 5 ∨ p = 7) → PerfectSectionsAltSqC p J →
    ∀ x ∈ L, x ^ p = 1 → (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
    ∀ W : Subgroup Y, ⁅W, W⁆ = W → W ≤ Subgroup.normalizer (L : Set Y) →
      W ≤ Subgroup.centralizer ({x} : Set Y) →
    (∃ E : Subgroup Y, E ≤ W ⊓ L ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2) → False

@[expose] def AltIbBarCell (𝔉 : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝔉 G →
    ∀ Jb : Subgroup G, (∃ T : Subgroup G, IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set G) ≤ Jb) → Jb ≠ ⊤ →
    ∀ p : ℕ, (p = 5 ∨ p = 7) →
    (∀ X : Subgroup G, X ≤ Jb → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X) →
    (∀ X₁ X₂ : Subgroup G, X₁ ≤ Jb → X₂ ≤ Jb → CFSG.Open.IsQuasisimple ↥X₁ →
      CFSG.Open.IsQuasisimple ↥X₂ → X₂ ≤ Subgroup.centralizer (X₁ : Set G) →
      p ∣ Nat.card X₁ → p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False) →
    ∀ x : G, x ^ p = 1 → (∀ g : G, g * x = x * g → g ∈ Jb) →
    ∀ V E : Subgroup G, V ≤ Jb → V ≤ Subgroup.centralizer ({x} : Set G) → ⁅V, V⁆ = V →
      E ≤ V → IsElemAbelian p E → Nat.card E = p ^ 2 → False

section Bridge

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem card_map_mk_of_pGroup {L : Subgroup Y} {p : ℕ} (hp : p.Prime)
    (hpZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {E : Subgroup ↥L} (hE : ∀ e ∈ E, e ^ p = 1) :
    Nat.card (E.map (QuotientGroup.mk' (Subgroup.center ↥L))) = Nat.card E := by
  have hinj : Function.Injective ((QuotientGroup.mk' (Subgroup.center ↥L)).subgroupMap E) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    have h1 : QuotientGroup.mk' (Subgroup.center ↥L) (e : ↥L) = 1 := congrArg Subtype.val he
    have hz : (e : ↥L) ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).1 h1
    have hep : (e : ↥L) ^ p = 1 := hE e e.2
    have h2 : orderOf (e : ↥L) ∣ p := orderOf_dvd_of_pow_eq_one hep
    have h3 : orderOf (e : ↥L) ∣ Nat.card (Subgroup.center ↥L) := by
      have := orderOf_dvd_natCard (⟨(e : ↥L), hz⟩ : ↥(Subgroup.center ↥L))
      simpa using this
    rcases (Nat.dvd_prime hp).1 h2 with h | h
    · rw [Subgroup.mem_bot]
      exact Subtype.ext (orderOf_eq_one_iff.1 h)
    · exact absurd (h ▸ h3) hpZ
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, MonoidHom.subgroupMap_surjective _ E⟩)).symm


omit [Finite Y] in
theorem commutator_subgroupOf_eq {L X : Subgroup Y} (hXL : X ≤ L) (hX : ⁅X, X⁆ = X) :
    ⁅X.subgroupOf L, X.subgroupOf L⁆ = X.subgroupOf L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hXL, hX]

omit [Finite Y] in
theorem exists_surjective_to_image {L X : Subgroup Y} (hXL : X ≤ L)
    {Xb : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (hXb : (X.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) = Xb) :
    ∃ f : ↥X →* ↥Xb, Function.Surjective f := by
  let e1 : ↥X ≃* ↥(X.subgroupOf L) := (Subgroup.subgroupOfEquivOfLe hXL).symm
  let f0 : ↥(X.subgroupOf L) →* ↥((X.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) :=
    (QuotientGroup.mk' (Subgroup.center ↥L)).subgroupMap _
  let e2 := MulEquiv.subgroupCongr hXb
  refine ⟨e2.toMonoidHom.comp (f0.comp e1.toMonoidHom), ?_⟩
  exact e2.surjective.comp ((MonoidHom.subgroupMap_surjective _ _).comp e1.surjective)

theorem altIbCell_of_barCell (hSch : KFactCatalogSchreier)
    (hGA : CFSG.Open.GriessAllModelsStatement) {𝔉 : ∀ (X : Type) [Group X], Prop}
    (h𝔉 : ∀ (X : Type) [Group X], 𝔉 X → IsRestTwoOrG2 X) (hbar : AltIbBarCell 𝔉) :
    AltIbCell 𝔉 := by
  intro Y _ _ L J hL htype hX hpar hJL hnB p hp57 hAlt x hxL hxp hfix W hW hWN hWx hE
  obtain ⟨E, hEW, hEel, hEcard⟩ := hE
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp5 : 5 ≤ p := by rcases hp57 with rfl | rfl <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  obtain ⟨hpZ, V, hVle, hV, hEV⟩ := exists_perfect_core_in_parabolic hSch hGA hL htype
    (h𝔉 _ hX) hp hp5 hxL hfix hW hWN hWx hEW hEp
  have hcomp : CompParabE L J := ⟨hL, htype, hpar, hJL, hnB⟩
  obtain ⟨S₀, hNS, -, hJtop⟩ := exists_sylow_parab_central hcomp
  have hVJ : V ≤ J := fun v hv => (hVle hv).1
  have hVC : V ≤ Subgroup.centralizer ({x} : Set Y) := fun v hv => (hVle hv).2
  have hVL : V ≤ L := hVJ.trans hpar.1
  have hEL : E ≤ L := fun e he => (hEW he).2
  set ψ : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hψ
  set x' : ↥L := ⟨x, hxL⟩ with hx'
  have hx'p : x' ^ p = 1 := Subtype.ext (by simpa using hxp)
  refine hbar (↥L ⧸ Subgroup.center ↥L) hX (jBar L J)
    ⟨_, isSylowTwoOf_top_of_sylow' S₀, hNS⟩ hJtop p hp57 ?_ ?_ (QuotientGroup.mk x') ?_ ?_
    ((V.subgroupOf L).map ψ) ((E.subgroupOf L).map ψ) ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro Xb hXJ hq hd
    obtain ⟨X, hXJ', -, hXq, -, hk⟩ := exists_quasisimple_lift_of_not_dvd hpar hp hpZ hXJ hq
    exact not_sq_dvd_card_of_quasisimple hp57 hAlt hXJ' hXq ((hk 2).2 hd)
  ·
    intro Xb₁ Xb₂ h₁ h₂ hq₁ hq₂ hc hp₁ hp₂ hn₁ hn₂
    obtain ⟨X₁, h₁J, h₁L, hq₁', hm₁, hk₁⟩ := exists_quasisimple_lift_of_not_dvd hpar hp hpZ h₁ hq₁
    obtain ⟨X₂, h₂J, h₂L, hq₂', hm₂, hk₂⟩ := exists_quasisimple_lift_of_not_dvd hpar hp hpZ h₂ hq₂
    have hcomm : ∀ a ∈ X₁.subgroupOf L, ∀ b ∈ X₂.subgroupOf L,
        (QuotientGroup.mk a : ↥L ⧸ Subgroup.center ↥L) * QuotientGroup.mk b =
          QuotientGroup.mk b * QuotientGroup.mk a := by
      intro a ha b hb
      have ha' : (QuotientGroup.mk a : ↥L ⧸ Subgroup.center ↥L) ∈ Xb₁ :=
        hm₁ ▸ Subgroup.mem_map_of_mem ψ ha
      have hb' : (QuotientGroup.mk b : ↥L ⧸ Subgroup.center ↥L) ∈ Xb₂ :=
        hm₂ ▸ Subgroup.mem_map_of_mem ψ hb
      exact Subgroup.mem_centralizer_iff.1 (hc hb') _ ha'
    have hX₁perf : ⁅X₁.subgroupOf L, X₁.subgroupOf L⁆ = X₁.subgroupOf L :=
      commutator_subgroupOf_eq h₁L (commutator_eq_self_of_open_isQuasisimple hq₁')
    have hcX : X₂ ≤ Subgroup.centralizer (X₁ : Set Y) := by
      intro y₂ hy₂
      rw [Subgroup.mem_centralizer_iff]
      intro y₁ hy₁
      have := commute_of_map_commute hX₁perf hcomm ⟨y₁, h₁L hy₁⟩
        (Subgroup.mem_subgroupOf.2 hy₁) ⟨y₂, h₂L hy₂⟩ (Subgroup.mem_subgroupOf.2 hy₂)
      exact congrArg Subtype.val this
    obtain ⟨f₁, hf₁⟩ := exists_surjective_to_image h₁L hm₁
    obtain ⟨f₂, hf₂⟩ := exists_surjective_to_image h₂L hm₂
    exact false_of_commuting_noAp hp57 hAlt h₁J h₂J hq₁' hq₂' hcX
      (by simpa using (hk₁ 1).2 (by simpa using hp₁)) (by simpa using (hk₂ 1).2 (by simpa using hp₂))
      (noAp_center_quotient_of_surjective f₁ hf₁ hn₁)
      (noAp_center_quotient_of_surjective f₂ hf₂ hn₂)
  ·
    rw [← QuotientGroup.mk_pow, hx'p, QuotientGroup.mk_one]
  ·
    intro g hg
    exact fix_all_bar hp hpZ hxL hxp hfix g hg
  ·
    exact Subgroup.map_mono fun v hv => hVJ hv
  ·
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    show ψ x' * ψ v = ψ v * ψ x'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hVC (Subgroup.mem_subgroupOf.1 hv)) x
      (Set.mem_singleton x))
  ·
    rw [← Subgroup.map_commutator, commutator_subgroupOf_eq hVL hV]
  · exact Subgroup.map_mono fun e he => Subgroup.mem_subgroupOf.2 (hEV (Subgroup.mem_subgroupOf.1 he))
  ·
    have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hEel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, a, ha, rfl⟩ := a
      obtain ⟨_, b, hb, rfl⟩ := b
      apply Subtype.ext
      show ψ a * ψ b = ψ b * ψ a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm a (Subgroup.mem_subgroupOf.1 ha) b (Subgroup.mem_subgroupOf.1 hb))
    · rintro _ ⟨e, he, rfl⟩
      show ψ e ^ p = 1
      rw [← map_pow]
      have : (e : Y) ^ p = 1 := hEel.2 _ (Subgroup.mem_subgroupOf.1 he)
      have : e ^ p = 1 := Subtype.ext (by simpa using this)
      rw [this, map_one]
  ·
    rw [card_map_mk_of_pGroup hp hpZ (E := E.subgroupOf L) (fun e he => by
      have : (e : Y) ^ p = 1 := hEel.2 _ (Subgroup.mem_subgroupOf.1 he)
      exact Subtype.ext (by simpa using this)), ← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv

end Bridge

section Cores

structure FlagBlocks (p : ℕ) (J : Type*) [Group J] where
  ι : Type
  H : ι → Type
  [grp : ∀ i, Group (H i)]
  ρ : ∀ i, J →* H i
  inj_of_pow : ∀ e : J, e ^ p = 1 → (∀ i, ρ i e = 1) → e = 1

attribute [instance] FlagBlocks.grp

variable {J : Type*} [Group J] {p : ℕ}

theorem isPGroup_of_pow_eq_one {A : Subgroup J} (hA : ∀ a ∈ A, a ^ p = 1) :
    IsPGroup p A := fun a => ⟨1, Subtype.ext (by simpa using hA a a.2)⟩

theorem FlagBlocks.exists_two_ne_bot_map (B : FlagBlocks p J) (hp : p.Prime) {E : Subgroup J}
    [Finite E] (hE : ∀ e ∈ E, e ^ p = 1) (hEc : p ^ 2 ≤ Nat.card E)
    (hcyc : ∀ i, IsCyclic ↥(E.map (B.ρ i))) :
    ∃ i j, i ≠ j ∧ E.map (B.ρ i) ≠ ⊥ ∧ E.map (B.ρ j) ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  have hmapbot : ∀ i, E.map (B.ρ i) = ⊥ → ∀ e ∈ E, B.ρ i e = 1 := fun i hi e he => by
    have : B.ρ i e ∈ E.map (B.ρ i) := Subgroup.mem_map_of_mem _ he
    rwa [hi, Subgroup.mem_bot] at this
  have hpp : p < p ^ 2 := by
    have := hp.two_le
    nlinarith
  by_cases hex : ∃ i, E.map (B.ρ i) ≠ ⊥
  · obtain ⟨i₀, hi₀⟩ := hex
    have hinj : ∀ e ∈ E, B.ρ i₀ e = 1 → e = 1 := by
      intro e he h1
      refine B.inj_of_pow e (hE e he) fun i => ?_
      by_cases hi : i = i₀
      · rw [hi]; exact h1
      · exact hmapbot i (hcon i₀ i (Ne.symm hi) hi₀) e he
    have hcard : Nat.card (E.map (B.ρ i₀)) = Nat.card E := by
      symm
      refine Nat.card_congr (Equiv.ofBijective
        (fun e : E => (⟨B.ρ i₀ e, Subgroup.mem_map_of_mem _ e.2⟩ : E.map (B.ρ i₀))) ⟨?_, ?_⟩)
      · intro a b hab
        have h1 : B.ρ i₀ ((a : J)⁻¹ * b) = 1 := by
          have := congrArg Subtype.val hab
          simp only at this
          rw [map_mul, map_inv, this, inv_mul_cancel]
        have h2 := hinj ((a : J)⁻¹ * b) (E.mul_mem (E.inv_mem a.2) b.2) h1
        exact Subtype.ext (inv_mul_eq_one.1 h2)
      · rintro ⟨_, e, he, rfl⟩
        exact ⟨⟨e, he⟩, rfl⟩
    have hexp : ∀ y ∈ E.map (B.ρ i₀), y ^ p = 1 := by
      rintro _ ⟨e, he, rfl⟩
      rw [← map_pow, hE e he, map_one]
    have hdvd : Monoid.exponent ↥(E.map (B.ρ i₀)) ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun y => Subtype.ext (by simpa using hexp y y.2)
    have hle : Nat.card (E.map (B.ρ i₀)) ∣ p := by
      have := hcyc i₀
      rw [← IsCyclic.exponent_eq_card]
      exact hdvd
    have := Nat.le_of_dvd hp.pos hle
    omega
  · push Not at hex
    have hE1 : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 fun e he =>
      B.inj_of_pow e (hE e he) fun i => hmapbot i (hex i) e he
    rw [hE1, Subgroup.card_bot] at hEc
    have := hp.two_le
    omega


theorem map_eq_bot_of_transfer {H : Type*} [Group H] [Finite H] (ρ : J →* H) (hp : p.Prime)
    (hH : ¬ p ^ 2 ∣ Nat.card H) {V E : Subgroup J} (hV : ⁅V, V⁆ = V) (hEV : E ≤ V)
    (hE : ∀ e ∈ E, e ^ p = 1) {x : J} (hx : x ^ p = 1) (hxV : ∀ v ∈ V, v * x = x * v)
    (hesc : ρ x = 1 → p ∣ Nat.card (V.map ρ) → False) : E.map ρ = ⊥ := by
  by_contra hne
  obtain ⟨⟨y, ⟨e, he, rfl⟩⟩, hne1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hne1 : ρ e ≠ 1 := fun h => hne1 (Subtype.ext h)
  have heV : ρ e ∈ V.map ρ := Subgroup.mem_map_of_mem _ (hEV he)
  have hord : orderOf (ρ e) = p := by
    have h1 : (ρ e) ^ p = 1 := by rw [← map_pow, hE e he, map_one]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne1
    · exact h
  have hpV : p ∣ Nat.card (V.map ρ) := by
    have := orderOf_dvd_natCard (⟨ρ e, heV⟩ : ↥(V.map ρ))
    rwa [Subgroup.orderOf_mk, hord] at this
  have hperf : ⁅V.map ρ, V.map ρ⁆ = V.map ρ := by
    rw [← Subgroup.map_commutator, hV]
  have hy : ρ x = 1 := by
    refine eq_one_of_commute_of_perfect_of_not_sq_dvd hp hH hperf hpV (y := ρ x)
      (by rw [← map_pow, hx, map_one]) ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul, hxV v hv]
  exact hesc hy hpV

theorem FlagBlocks.false_of_nonsplit (B : FlagBlocks p J) (hp : p.Prime) [∀ i, Finite (B.H i)]
    (hH : ∀ i, ¬ p ^ 2 ∣ Nat.card (B.H i)) (top : B.ι → Prop)
    (htop : ∀ i j, top i → top j → i = j) {V E : Subgroup J} [Finite E] (hV : ⁅V, V⁆ = V)
    (hEV : E ≤ V) (hE : ∀ e ∈ E, e ^ p = 1) (hEc : p ^ 2 ≤ Nat.card E) {x : J} (hx : x ^ p = 1)
    (hxV : ∀ v ∈ V, v * x = x * v)
    (hesc : ∀ i, ¬ top i → B.ρ i x = 1 → p ∣ Nat.card (V.map (B.ρ i)) → False) : False := by
  have hbot : ∀ i, ¬ top i → E.map (B.ρ i) = ⊥ := fun i hi =>
    map_eq_bot_of_transfer (B.ρ i) hp (hH i) hV hEV hE hx hxV (hesc i hi)
  have hcyc : ∀ i, IsCyclic ↥(E.map (B.ρ i)) := by
    intro i
    by_cases hi : top i
    · exact isCyclic_of_isPGroup_of_not_sq_dvd hp (hH i)
        (isPGroup_of_pow_eq_one (by
          rintro _ ⟨e, he, rfl⟩
          rw [← map_pow, hE e he, map_one]))
    · rw [hbot i hi]
      infer_instance
  obtain ⟨i, j, hij, hi, hj⟩ := B.exists_two_ne_bot_map hp hE hEc hcyc
  have hti : top i := by_contra fun h => hi (hbot i h)
  have htj : top j := by_contra fun h => hj (hbot j h)
  exact hij (htop i j hti htj)

theorem FlagBlocks.false_of_split (B : FlagBlocks p J) (hp : p.Prime) {E : Subgroup J} [Finite E]
    (hE : ∀ e ∈ E, e ^ p = 1) (hEc : p ^ 2 ≤ Nat.card E)
    (hcyc : ∀ i, IsCyclic ↥(E.map (B.ρ i)))
    (hA2 : ∀ i j, i ≠ j → E.map (B.ρ i) ≠ ⊥ → E.map (B.ρ j) ≠ ⊥ → False) : False := by
  obtain ⟨i, j, hij, hi, hj⟩ := B.exists_two_ne_bot_map hp hE hEc hcyc
  exact hA2 i j hij hi hj

end Cores

section Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_fixed_of_trivial_step {p : ℕ} (hp : (p : K) ≠ 0) {g : V →ₗ[K] V}
    (hg : g ^ p = 1) {A B : Submodule K V} (hAB : A ≤ B) (hstep : ∀ b ∈ B, g b - b ∈ A) {b : V}
    (hb : b ∈ B) (hbA : b ∉ A) : ∃ a ∈ B, a ≠ 0 ∧ g a = a := by
  have hmem : ∀ j : ℕ, (g ^ j) b ∈ B ∧ (g ^ j) b - b ∈ A := by
    intro j
    induction j with
    | zero => exact ⟨by simpa using hb, by simp⟩
    | succ j ih =>
      have h1 : g ((g ^ j) b) - (g ^ j) b ∈ A := hstep _ ih.1
      have h2 : (g ^ (j + 1)) b = g ((g ^ j) b) := by rw [pow_succ', Module.End.mul_apply]
      refine ⟨?_, ?_⟩
      · rw [h2]
        have : g ((g ^ j) b) = (g ((g ^ j) b) - (g ^ j) b) + (g ^ j) b := by abel
        rw [this]
        exact B.add_mem (hAB h1) ih.1
      · rw [h2]
        have : g ((g ^ j) b) - b = (g ((g ^ j) b) - (g ^ j) b) + ((g ^ j) b - b) := by abel
        rw [this]
        exact A.add_mem h1 ih.2
  set a : V := ∑ j ∈ Finset.range p, (g ^ j) b with ha
  have haB : a ∈ B := B.sum_mem fun j _ => (hmem j).1
  have hgsum : g a = a := by
    obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by
      have : p ≠ 0 := fun h0 => hp (by simp [h0])
      omega⟩
    have hpb : (g ^ p) b = b := by rw [hg]; rfl
    have h1 : g a = ∑ j ∈ Finset.range p, (g ^ (j + 1)) b := by
      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ', Module.End.mul_apply]
    rw [h1, ha, hn, Finset.sum_range_succ, Finset.sum_range_succ' (fun j => (g ^ j) b) n]
    have : (g ^ (n + 1)) b = (g ^ 0) b := by rw [← hn, hpb]; simp
    rw [this]
  have hdiff : a - (p : K) • b ∈ A := by
    have : a - (p : K) • b = ∑ j ∈ Finset.range p, ((g ^ j) b - b) := by
      rw [Finset.sum_sub_distrib, ha]
      simp [Nat.cast_smul_eq_nsmul K]
    rw [this]
    exact A.sum_mem fun j _ => (hmem j).2
  refine ⟨a, haB, ?_, hgsum⟩
  intro ha0
  rw [ha0, zero_sub] at hdiff
  have : (p : K) • b ∈ A := by simpa using A.neg_mem hdiff
  apply hbA
  have := A.smul_mem (p : K)⁻¹ this
  rwa [smul_smul, inv_mul_cancel₀ hp, one_smul] at this

theorem fixes_of_chain {p : ℕ} (hp : (p : K) ≠ 0) {g : V →ₗ[K] V} (hg : g ^ p = 1)
    (U : ℕ → Submodule K V) (hU0 : U 0 = ⊥) (n : ℕ)
    (hstep : ∀ j < n, ∀ v ∈ U (j + 1), g v - v ∈ U j) : ∀ v ∈ U n, g v = v := by
  have key : ∀ j ≤ n, ∀ v ∈ U j, g v = v := by
    intro j
    induction j with
    | zero =>
      intro _ v hv
      rw [hU0, Submodule.mem_bot] at hv
      rw [hv, map_zero]
    | succ j ih =>
      intro hj v hv
      have hu : g v - v ∈ U j := hstep j (by omega) v hv
      have hgu : g (g v - v) = g v - v := ih (by omega) _ hu
      have hpow : ∀ k : ℕ, (g ^ k) v = v + (k : K) • (g v - v) := by
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [pow_succ', Module.End.mul_apply, ihk, map_add, map_smul, hgu]
          have : g v = v + (g v - v) := by abel
          rw [this]
          simp only [add_sub_cancel_left, Nat.cast_succ, add_smul, one_smul]
          abel
      have h1 : (g ^ p) v = v := by rw [hg]; rfl
      rw [hpow p] at h1
      have h2 : (p : K) • (g v - v) = 0 := by simpa using h1
      have h3 : g v - v = 0 := by
        rcases smul_eq_zero.1 h2 with h | h
        · exact absurd h hp
        · exact h
      exact sub_eq_zero.1 h3
  exact key n le_rfl

end Linear

open Matrix

section Levels

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem submatrix_mul_of_blockTriangular {lev : ι → ℕ} {M N : Matrix ι ι K}
    (hM : M.BlockTriangular lev) (hN : N.BlockTriangular lev) {κ : Type*} [Fintype κ]
    {σ : κ → ι} (hσ : Function.Injective σ) {ℓ : ℕ} (hr : ∀ u, lev u = ℓ ↔ u ∈ Set.range σ) :
    (M * N).submatrix σ σ = M.submatrix σ σ * N.submatrix σ σ := by
  classical
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have ha : lev (σ a) = ℓ := (hr _).2 ⟨a, rfl⟩
  have hb : lev (σ b) = ℓ := (hr _).2 ⟨b, rfl⟩
  have hsub : ∀ c ∈ (Finset.univ : Finset ι), c ∉ Finset.univ.image σ →
      M (σ a) c * N c (σ b) = 0 := by
    intro c _ hc
    have hc' : lev c ≠ ℓ := fun h => hc (Finset.mem_image.2 (by
      obtain ⟨k, hk⟩ := (hr c).1 h
      exact ⟨k, Finset.mem_univ _, hk⟩))
    rcases lt_or_gt_of_ne hc' with h | h
    · rw [hM (by rw [ha]; exact h), zero_mul]
    · rw [hN (by rw [hb]; exact h), mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image σ)) hsub,
    Finset.sum_image (fun x _ y _ h => hσ h)]

@[expose] noncomputable def levelHom {J : Type*} [Group J] (π : J →* GL ι K) {lev : ι → ℕ}
    (hπ : ∀ g, ((π g : GL ι K) : Matrix ι ι K).BlockTriangular lev) {κ : Type*} [Fintype κ]
    [DecidableEq κ] {σ : κ → ι} (hσ : Function.Injective σ) {ℓ : ℕ}
    (hr : ∀ u, lev u = ℓ ↔ u ∈ Set.range σ) : J →* GL κ K :=
  MonoidHom.toHomUnits
    { toFun := fun g => ((π g : GL ι K) : Matrix ι ι K).submatrix σ σ
      map_one' := by simp [Matrix.submatrix_one _ hσ]
      map_mul' := fun g h => by
        simp only [map_mul, Units.val_mul]
        exact submatrix_mul_of_blockTriangular (hπ g) (hπ h) hσ hr }

theorem coe_levelHom {J : Type*} [Group J] (π : J →* GL ι K) {lev : ι → ℕ}
    (hπ : ∀ g, ((π g : GL ι K) : Matrix ι ι K).BlockTriangular lev) {κ : Type*} [Fintype κ]
    [DecidableEq κ] {σ : κ → ι} (hσ : Function.Injective σ) {ℓ : ℕ}
    (hr : ∀ u, lev u = ℓ ↔ u ∈ Set.range σ) (g : J) :
    ((levelHom π hπ hσ hr g : GL κ K) : Matrix κ κ K) =
      ((π g : GL ι K) : Matrix ι ι K).submatrix σ σ := by
  simp [levelHom]

@[expose] def levelSpace (lev : ι → ℕ) (j : ℕ) : Submodule K (ι → K) where
  carrier := {v | ∀ u, j ≤ lev u → v u = 0}
  add_mem' := fun ha hb u hu => by simp [ha u hu, hb u hu]
  zero_mem' := fun u _ => rfl
  smul_mem' := fun c v hv u hu => by simp [hv u hu]

omit [Fintype ι] [DecidableEq ι] in
theorem mem_levelSpace {lev : ι → ℕ} {j : ℕ} {v : ι → K} :
    v ∈ levelSpace (K := K) lev j ↔ ∀ u, j ≤ lev u → v u = 0 := Iff.rfl

theorem mulVecLin_pow_apply (M : Matrix ι ι K) (k : ℕ) (v : ι → K) :
    (M.mulVecLin ^ k) v = (M ^ k) *ᵥ v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      ← pow_succ']

theorem mulVecLin_pow_eq_one {M : Matrix ι ι K} {p : ℕ} (h : M ^ p = 1) :
    M.mulVecLin ^ p = 1 := by
  refine LinearMap.ext fun v => ?_
  rw [mulVecLin_pow_apply, h]
  simp

theorem mulVec_sub_mem_levelSpace {lev : ι → ℕ} {M : Matrix ι ι K} (hM : M.BlockTriangular lev)
    {j : ℕ} (hblk : ∀ u v, lev u = j → lev v = j → M u v = (1 : Matrix ι ι K) u v)
    {v : ι → K} (hv : v ∈ levelSpace (K := K) lev (j + 1)) :
    M *ᵥ v - v ∈ levelSpace (K := K) lev j := by
  rw [mem_levelSpace]
  intro u hu
  show (M *ᵥ v) u - v u = 0
  rcases Nat.eq_or_lt_of_le hu with huj | huj
  ·
    have h1 : (M *ᵥ v) u = ((1 : Matrix ι ι K) *ᵥ v) u := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hw : lev u = lev w
      · rw [hblk u w huj.symm (by omega)]
      · rcases lt_or_gt_of_ne hw with h | h
        · have hvw : v w = 0 := hv w (by omega)
          rw [hvw, mul_zero, mul_zero]
        · have hMuw : M u w = 0 := hM (show lev w < lev u by omega)
          have hone : (1 : Matrix ι ι K) u w = 0 := by
            rw [Matrix.one_apply_ne]; intro h'; exact hw (by rw [h'])
          rw [hMuw, hone]
    rw [h1, Matrix.one_mulVec, sub_self]
  ·
    have hvu : v u = 0 := hv u (by omega)
    have : (M *ᵥ v) u = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun w _ => ?_
      by_cases hvw : v w = 0
      · rw [hvw, mul_zero]
      · have : lev w < j + 1 := by
          by_contra hcon
          exact hvw (hv w (by omega))
        have hMuw : M u w = 0 := hM (show lev w < lev u by omega)
        rw [hMuw, zero_mul]
    rw [this, hvu, sub_zero]

theorem mulVec_eq_of_blocks_one {lev : ι → ℕ} {M : Matrix ι ι K} (hM : M.BlockTriangular lev)
    {p : ℕ} (hp : (p : K) ≠ 0) (hMp : M ^ p = 1) (n : ℕ)
    (hblk : ∀ u v, lev u = lev v → lev u < n → M u v = (1 : Matrix ι ι K) u v) :
    ∀ v ∈ levelSpace (K := K) lev n, M *ᵥ v = v := by
  have key := fixes_of_chain hp (mulVecLin_pow_eq_one hMp) (fun j => levelSpace (K := K) lev j)
    (by
      ext v
      rw [Submodule.mem_bot]
      constructor
      · intro hv
        funext u
        exact hv u (Nat.zero_le _)
      · rintro rfl
        intro u _
        rfl) n (by
    intro j hj v hv
    exact mulVec_sub_mem_levelSpace hM (fun u w h1 h2 => hblk u w (h1.trans h2.symm)
      (by omega)) hv)
  intro v hv
  exact key v hv

@[expose] def extendId (P : ι → Prop) [DecidablePred P] (A : Matrix {u // P u} {u // P u} K) :
    Matrix ι ι K :=
  Matrix.of fun u v => if h : P u ∧ P v then A ⟨u, h.1⟩ ⟨v, h.2⟩ else (1 : Matrix ι ι K) u v

omit [Fintype ι] in
theorem extendId_apply_pos {P : ι → Prop} [DecidablePred P] (A : Matrix {u // P u} {u // P u} K)
    {u v : ι} (hu : P u) (hv : P v) : extendId P A u v = A ⟨u, hu⟩ ⟨v, hv⟩ := by
  simp [extendId, hu, hv]

omit [Fintype ι] in
theorem extendId_apply_neg {P : ι → Prop} [DecidablePred P] (A : Matrix {u // P u} {u // P u} K)
    {u v : ι} (h : ¬ (P u ∧ P v)) : extendId P A u v = (1 : Matrix ι ι K) u v := by
  simp [extendId, h]

omit [Fintype ι] in
theorem extendId_one (P : ι → Prop) [DecidablePred P] :
    extendId P (1 : Matrix {u // P u} {u // P u} K) = 1 := by
  ext u v
  by_cases h : P u ∧ P v
  · rw [extendId_apply_pos _ h.1 h.2]
    by_cases huv : u = v
    · subst huv; simp
    · have : (⟨u, h.1⟩ : {u // P u}) ≠ ⟨v, h.2⟩ := fun h' => huv (congrArg Subtype.val h')
      simp [Matrix.one_apply_ne huv, Matrix.one_apply_ne this]
  · rw [extendId_apply_neg _ h]

theorem extendId_mul (P : ι → Prop) [DecidablePred P] (A B : Matrix {u // P u} {u // P u} K) :
    extendId P (A * B) = extendId P A * extendId P B := by
  ext u v
  rw [Matrix.mul_apply]
  by_cases hu : P u
  · by_cases hv : P v
    · rw [extendId_apply_pos _ hu hv, Matrix.mul_apply]
      rw [← Fintype.sum_subtype_add_sum_subtype P]
      have h0 : ∑ c : {c // ¬ P c}, extendId P A u c * extendId P B c v = 0 :=
        Finset.sum_eq_zero fun c _ => by
          have hne : u ≠ (c : ι) := fun h => c.2 (h ▸ hu)
          rw [extendId_apply_neg A (fun h => c.2 h.2), Matrix.one_apply_ne hne, zero_mul]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [extendId_apply_pos _ hu c.2, extendId_apply_pos _ c.2 hv]
    · have hne : u ≠ v := fun h => hv (h ▸ hu)
      rw [extendId_apply_neg _ (fun h => hv h.2), Matrix.one_apply_ne hne]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      by_cases hc : P c
      · have hne' : c ≠ v := fun h => hv (h ▸ hc)
        rw [extendId_apply_neg B (fun h => hv h.2), Matrix.one_apply_ne hne', mul_zero]
      · have hne' : u ≠ c := fun h => hc (h ▸ hu)
        rw [extendId_apply_neg A (fun h => hc h.2), Matrix.one_apply_ne hne', zero_mul]
  · rw [extendId_apply_neg _ (fun h => hu h.1)]
    have : ∀ c, extendId P A u c = (1 : Matrix ι ι K) u c := fun c =>
      extendId_apply_neg A (fun h => hu h.1)
    simp only [this]
    rw [← Matrix.mul_apply, Matrix.one_mul, extendId_apply_neg _ (fun h => hu h.1)]

@[expose] def extendIdHom (P : ι → Prop) [DecidablePred P] :
    Matrix {u // P u} {u // P u} K →* Matrix ι ι K where
  toFun := extendId P
  map_one' := extendId_one P
  map_mul' := extendId_mul P

omit [Fintype ι] in
theorem submatrix_extendId (P : ι → Prop) [DecidablePred P] (A : Matrix {u // P u} {u // P u} K) :
    (extendId P A).submatrix Subtype.val Subtype.val = A := by
  ext u v
  simp [extendId_apply_pos _ u.2 v.2]

@[expose] noncomputable def extendGL (P : ι → Prop) [DecidablePred P] :
    GL {u // P u} K →* GL ι K :=
  Units.map (extendIdHom P)

theorem coe_extendGL (P : ι → Prop) [DecidablePred P] (A : GL {u // P u} K) :
    ((extendGL P A : GL ι K) : Matrix ι ι K) = extendId P (A : Matrix {u // P u} {u // P u} K) := rfl

theorem extendGL_injective (P : ι → Prop) [DecidablePred P] :
    Function.Injective (extendGL (K := K) P) := by
  intro A B h
  apply Units.ext
  have := congrArg (fun M : GL ι K => ((M : Matrix ι ι K).submatrix Subtype.val Subtype.val :
    Matrix {u // P u} {u // P u} K)) h
  simpa [coe_extendGL, submatrix_extendId] using this

end Levels


section Levels2

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem extendId_ne_one {P : ι → Prop} [DecidablePred P] (A : Matrix {u // P u} {u // P u} K)
    {u v : ι} (h : extendId P A u v ≠ (1 : Matrix ι ι K) u v) : P u ∧ P v := by
  by_contra hn
  exact h (extendId_apply_neg A hn)

omit [Fintype ι] in
theorem extendId_submatrix_sumCompl (P : ι → Prop) [DecidablePred P]
    (A : Matrix {u // P u} {u // P u} K) :
    (extendId P A).submatrix (Equiv.sumCompl P) (Equiv.sumCompl P) =
      Matrix.fromBlocks A 0 0 1 := by
  ext u v
  rcases u with u | u <;> rcases v with v | v
  · simp [extendId_apply_pos _ u.2 v.2]
  · have h : ¬ (P (u : ι) ∧ P (v : ι)) := fun h => v.2 h.2
    have hne : (u : ι) ≠ (v : ι) := fun h' => v.2 (h' ▸ u.2)
    simp [extendId_apply_neg _ h, Matrix.one_apply_ne hne]
  · have h : ¬ (P (u : ι) ∧ P (v : ι)) := fun h => u.2 h.1
    have hne : (u : ι) ≠ (v : ι) := fun h' => u.2 (h' ▸ v.2)
    simp [extendId_apply_neg _ h, Matrix.one_apply_ne hne]
  · have h : ¬ (P (u : ι) ∧ P (v : ι)) := fun h => u.2 h.1
    simp [extendId_apply_neg _ h, Matrix.one_apply, Subtype.ext_iff]

theorem extendId_isometry {P : ι → Prop} [DecidablePred P] {G : Matrix ι ι K}
    (hG : ∀ u v, G u v ≠ 0 → (P u ↔ P v)) {A : Matrix {u // P u} {u // P u} K}
    (hA : Aᵀ * G.submatrix Subtype.val Subtype.val * A = G.submatrix Subtype.val Subtype.val) :
    (extendId P A)ᵀ * G * extendId P A = G := by
  classical
  set e := Equiv.sumCompl P with he
  have hGb : G.submatrix e e = Matrix.fromBlocks (G.submatrix Subtype.val Subtype.val) 0 0
      (G.submatrix Subtype.val Subtype.val) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v
    · simp [he]
    · have : G (u : ι) (v : ι) = 0 := by
        by_contra hne
        exact v.2 ((hG _ _ hne).1 u.2)
      simp [he, this]
    · have : G (u : ι) (v : ι) = 0 := by
        by_contra hne
        exact u.2 ((hG _ _ hne).2 v.2)
      simp [he, this]
    · simp [he]
  have key : ((extendId P A)ᵀ * G * extendId P A).submatrix e e = G.submatrix e e := by
    have h1 : ((extendId P A)ᵀ * G * extendId P A).submatrix e e =
        ((extendId P A).submatrix e e)ᵀ * G.submatrix e e * (extendId P A).submatrix e e := by
      rw [Matrix.submatrix_mul _ _ _ _ _ e.bijective, Matrix.submatrix_mul _ _ _ _ _ e.bijective,
        ← Matrix.transpose_submatrix]
    rw [h1, extendId_submatrix_sumCompl, hGb]
    simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hA]
  ext u v
  have := congrFun (congrFun key (e.symm u)) (e.symm v)
  simpa using this


theorem commute_of_supp {M N : Matrix ι ι K} {D E : ι → Prop}
    (hM : ∀ u v, M u v ≠ (1 : Matrix ι ι K) u v → D u ∧ D v)
    (hN : ∀ u v, N u v ≠ (1 : Matrix ι ι K) u v → E u ∧ E v) (hDE : ∀ u, ¬ (D u ∧ E u)) :
    M * N = N * M := by
  set X : Matrix ι ι K := M - 1 with hX
  set Y : Matrix ι ι K := N - 1 with hY
  have hXY : ∀ {A B : Matrix ι ι K} {D E : ι → Prop},
      (∀ u v, A u v ≠ 0 → D u ∧ D v) → (∀ u v, B u v ≠ 0 → E u ∧ E v) →
      (∀ u, ¬ (D u ∧ E u)) → A * B = 0 := by
    intro A B D E hA hB hDE
    ext u v
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h1 : A u c = 0
    · rw [h1, zero_mul]
    · by_cases h2 : B c v = 0
      · rw [h2, mul_zero]
      · exact absurd ⟨(hA u c h1).2, (hB c v h2).1⟩ (hDE c)
  have hXs : ∀ u v, X u v ≠ 0 → D u ∧ D v := fun u v h =>
    hM u v (fun h' => h (by simp [hX, h']))
  have hYs : ∀ u v, Y u v ≠ 0 → E u ∧ E v := fun u v h =>
    hN u v (fun h' => h (by simp [hY, h']))
  have h1 : X * Y = 0 := hXY hXs hYs hDE
  have h2 : Y * X = 0 := hXY hYs hXs fun u h => hDE u ⟨h.2, h.1⟩
  have hM' : M = 1 + X := by rw [hX]; abel
  have hN' : N = 1 + Y := by rw [hY]; abel
  rw [hM', hN']
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, h1, h2]
  abel

end Levels2

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem map_symm_le {θ : G ≃* G'} {Jb : Subgroup G} {X' : Subgroup G'}
    (h : X' ≤ Jb.map θ.toMonoidHom) : X'.map θ.symm.toMonoidHom ≤ Jb := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨j, hj, rfl⟩ := h hy
  simpa using hj

theorem quasisimple_map_symm {θ : G ≃* G'} {X' : Subgroup G'}
    (h : CFSG.Open.IsQuasisimple ↥X') : CFSG.Open.IsQuasisimple ↥(X'.map θ.symm.toMonoidHom) :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.equivMapOfInjective X' θ.symm.toMonoidHom θ.symm.injective).symm h

theorem card_map_symm {θ : G ≃* G'} (X' : Subgroup G') :
    Nat.card ↥(X'.map θ.symm.toMonoidHom) = Nat.card ↥X' :=
  Subgroup.card_map_of_injective θ.symm.injective

theorem isElemAbelian_map {p : ℕ} {G G' : Type} [Group G] [Group G'] (θ : G ≃* G')
    {E : Subgroup G} (h : IsElemAbelian p E) : IsElemAbelian p (E.map θ.toMonoidHom) :=
  CFSG.SectionRank.isElemAbelian_map h _

theorem transport_a1 {p : ℕ} (θ : G ≃* G') {Jb : Subgroup G}
    (hA1 : ∀ X : Subgroup G, X ≤ Jb → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X) :
    ∀ X' : Subgroup G', X' ≤ Jb.map θ.toMonoidHom → CFSG.Open.IsQuasisimple ↥X' →
      ¬ p ^ 2 ∣ Nat.card X' := by
  intro X' hX' hq hd
  exact hA1 _ (map_symm_le hX') (quasisimple_map_symm hq) (by rw [card_map_symm]; exact hd)

theorem transport_a2 {p : ℕ} (θ : G ≃* G') {Jb : Subgroup G}
    (hA2 : ∀ X₁ X₂ : Subgroup G, X₁ ≤ Jb → X₂ ≤ Jb → CFSG.Open.IsQuasisimple ↥X₁ →
      CFSG.Open.IsQuasisimple ↥X₂ → X₂ ≤ Subgroup.centralizer (X₁ : Set G) →
      p ∣ Nat.card X₁ → p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False) :
    ∀ X₁ X₂ : Subgroup G', X₁ ≤ Jb.map θ.toMonoidHom → X₂ ≤ Jb.map θ.toMonoidHom →
      CFSG.Open.IsQuasisimple ↥X₁ → CFSG.Open.IsQuasisimple ↥X₂ →
      X₂ ≤ Subgroup.centralizer (X₁ : Set G') → p ∣ Nat.card X₁ → p ∣ Nat.card X₂ →
      NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) → NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False := by
  intro X₁ X₂ h₁ h₂ hq₁ hq₂ hc hp₁ hp₂ hn₁ hn₂
  refine hA2 (X₁.map θ.symm.toMonoidHom) (X₂.map θ.symm.toMonoidHom) (map_symm_le h₁)
    (map_symm_le h₂) (quasisimple_map_symm hq₁) (quasisimple_map_symm hq₂) ?_
    (by rw [card_map_symm]; exact hp₁) (by rw [card_map_symm]; exact hp₂)
    (noAp_center_quotient_of_surjective
      (Subgroup.equivMapOfInjective X₁ θ.symm.toMonoidHom θ.symm.injective).symm.toMonoidHom
      (MulEquiv.surjective _) hn₁)
    (noAp_center_quotient_of_surjective
      (Subgroup.equivMapOfInjective X₂ θ.symm.toMonoidHom θ.symm.injective).symm.toMonoidHom
      (MulEquiv.surjective _) hn₂)
  rintro _ ⟨b', hb', rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨a', ha', rfl⟩
  have := Subgroup.mem_centralizer_iff.1 (hc hb') a' ha'
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← map_mul, ← map_mul, this]

end Transport

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
