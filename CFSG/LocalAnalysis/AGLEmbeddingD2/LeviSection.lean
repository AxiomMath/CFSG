module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.AGLEmbeddingD2.LeviSection

@[expose] def HasSubquotient {G : Type*} [Group G] (H : Subgroup G) (Q : Type*) [Group Q] : Prop :=
  ∃ X : Subgroup G, X ≤ H ∧ ∃ ψ : ↥X →* Q, Function.Surjective ψ

section Basic

variable {G G' : Type*} [Group G] [Group G'] {Q Q' : Type*} [Group Q] [Group Q']

theorem HasSubquotient.mono {H H' : Subgroup G} (h : HasSubquotient H Q) (hle : H ≤ H') :
    HasSubquotient H' Q := by
  obtain ⟨X, hX, ψ, hψ⟩ := h
  exact ⟨X, hX.trans hle, ψ, hψ⟩

theorem HasSubquotient.of_map (f : G →* G') {H : Subgroup G} (h : HasSubquotient (H.map f) Q) :
    HasSubquotient H Q := by
  obtain ⟨X, hX, ψ, hψ⟩ := h
  refine ⟨X.comap f ⊓ H, inf_le_right,
    ψ.comp ((f.domRestrict (X.comap f ⊓ H)).codRestrict X fun x => x.2.1), ?_⟩
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ := hψ q
  obtain ⟨g, hg, rfl⟩ := hX hy
  exact ⟨⟨g, hy, hg⟩, rfl⟩

theorem HasSubquotient.map (f : G →* G') {H X : Subgroup G} (hX : X ≤ H) (ψ : ↥X →* Q)
    (hψ : Function.Surjective ψ) (hker : ∀ x : ↥X, f x = 1 → ψ x = 1) :
    HasSubquotient (H.map f) Q := by
  have hsurj : Function.Surjective (f.subgroupMap X) := f.subgroupMap_surjective X
  have hle : (f.subgroupMap X).ker ≤ ψ.ker := by
    intro x hx
    refine hker x ?_
    have := congrArg Subtype.val ((MonoidHom.mem_ker).mp hx)
    simpa using this
  refine ⟨X.map f, Subgroup.map_mono hX,
    (f.subgroupMap X).liftOfRightInverse (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨ψ, hle⟩, ?_⟩
  intro q
  obtain ⟨x, rfl⟩ := hψ q
  exact ⟨f.subgroupMap X x, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩

theorem HasSubquotient.map_of_injective (f : G →* G') (hf : Function.Injective f) {H : Subgroup G}
    (h : HasSubquotient H Q) : HasSubquotient (H.map f) Q := by
  obtain ⟨X, hX, ψ, hψ⟩ := h
  refine HasSubquotient.map f hX ψ hψ fun x hx => ?_
  have hx1 : x = 1 := Subtype.ext (hf (by simpa using hx))
  rw [hx1, map_one]

theorem HasSubquotient.commutator (hQ : _root_.commutator Q = ⊤) {H : Subgroup G}
    (h : HasSubquotient H Q) : HasSubquotient ⁅H, H⁆ Q := by
  obtain ⟨X, hX, ψ, hψ⟩ := h
  have hrange : (_root_.commutator ↥X).map ψ = ⊤ := by
    have h1 : (_root_.commutator ↥X).map ψ = _root_.commutator Q := by
      have h2 : (⊤ : Subgroup ↥X).map ψ = ⊤ := by
        rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hψ]
      rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator, h2]
    rw [h1, hQ]
  have h3 : HasSubquotient (_root_.commutator ↥X) Q := by
    refine ⟨_root_.commutator ↥X, le_rfl, ψ.domRestrict _, ?_⟩
    rw [← MonoidHom.range_eq_top, MonoidHom.domRestrict_range, hrange]
  have h4 := h3.map_of_injective X.subtype X.subtype_injective
  rw [Subgroup.map_subtype_commutator] at h4
  exact h4.mono (Subgroup.commutator_mono hX hX)

theorem HasSubquotient.map_mk_of_isPGroup {N : Type*} [Group N] {p : ℕ} (W : Subgroup N) [W.Normal]
    (hW : IsPGroup p W) (hQ : ∀ R : Subgroup Q, R.Normal → IsPGroup p R → R = ⊥)
    {H : Subgroup N} (h : HasSubquotient H Q) :
    HasSubquotient (H.map (QuotientGroup.mk' W)) Q := by
  obtain ⟨X, hX, ψ, hψ⟩ := h
  refine HasSubquotient.map _ hX ψ hψ fun x hx => ?_
  have hxW : x ∈ W.subgroupOf X := by
    simpa [Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff] using hx
  have hbot := hQ ((W.subgroupOf X).map ψ)
    ((inferInstance : (W.subgroupOf X).Normal).map ψ hψ) (hW.comap_subtype.map ψ)
  have hmem : ψ x ∈ (W.subgroupOf X).map ψ := ⟨x, hxW, rfl⟩
  rw [hbot] at hmem
  simpa using hmem

theorem HasSubquotient.of_sup_normal_pGroup {G : Type*} [Group G] {Q : Type*} [Group Q] {p : ℕ}
    {V M N : Subgroup G} (hVN : V ≤ N) (hMN : M ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (V : Set G)) (hsup : N ≤ V ⊔ M) (hV : IsPGroup p V)
    (hQ : ∀ R : Subgroup Q, R.Normal → IsPGroup p R → R = ⊥) (h : HasSubquotient N Q) :
    HasSubquotient M Q := by
  have : (V.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVN).mpr hnorm
  have h1 : HasSubquotient (⊤ : Subgroup ↥N) Q := by
    refine HasSubquotient.of_map N.subtype ?_
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 := h1.map_mk_of_isPGroup (V.subgroupOf N) hV.comap_subtype hQ
  have h3 : (⊤ : Subgroup ↥N).map (QuotientGroup.mk' (V.subgroupOf N)) =
      (M.subgroupOf N).map (QuotientGroup.mk' (V.subgroupOf N)) := by
    have htop : V.subgroupOf N ⊔ M.subgroupOf N = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hVN hMN, Subgroup.subgroupOf_eq_top]
      exact hsup
    rw [← htop, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  rw [h3] at h2
  have h4 := (h2.of_map (QuotientGroup.mk' (V.subgroupOf N))).map_of_injective N.subtype
    N.subtype_injective
  rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hMN] at h4

end Basic

section Obstruction

variable {G : Type*} [Group G] {Q : Type*} [Group Q]

theorem HasSubquotient.exists_isPGroup_surjective [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (h : HasSubquotient H Q) (R : Subgroup Q) (hR : IsPGroup p R) :
    ∃ P : Subgroup G, P ≤ H ∧ IsPGroup p P ∧ ∃ f : ↥P →* ↥R, Function.Surjective f := by
  obtain ⟨X, hX, ψ, hψ⟩ := h
  have hsurj : Function.Surjective (ψ.subgroupComap R) := ψ.subgroupComap_surjective R hψ
  obtain ⟨S, hSp, hS⟩ : ∃ S : Subgroup ↥(R.comap ψ), IsPGroup p S ∧
      S.map (ψ.subgroupComap R) = ⊤ := by
    obtain ⟨S⟩ : Nonempty (Sylow p ↥(R.comap ψ)) := Sylow.nonempty
    have htop : IsPGroup p ↥(⊤ : Subgroup ↥R) := fun g => by
      obtain ⟨k, hk⟩ := hR g.1
      exact ⟨k, Subtype.ext hk⟩
    refine ⟨S, S.isPGroup', ?_⟩
    rw [← Sylow.coe_mapSurjective hsurj S]
    exact ((Sylow.mapSurjective hsurj S).is_maximal' htop le_top).symm
  let ρ : ↥(R.comap ψ) →* G := X.subtype.comp (R.comap ψ).subtype
  have hρ : Function.Injective ρ := X.subtype_injective.comp (R.comap ψ).subtype_injective
  have hg : Function.Surjective ((ψ.subgroupComap R).domRestrict S) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.domRestrict_range, hS]
  refine ⟨S.map ρ, ?_, hSp.map ρ, ((ψ.subgroupComap R).domRestrict S).comp
    (Subgroup.equivMapOfInjective S ρ hρ).symm.toMonoidHom, hg.comp (MulEquiv.surjective _)⟩
  rintro _ ⟨s, -, rfl⟩
  exact hX s.1.2

theorem HasSubquotient.isCyclic_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hcyc : ∀ P : Subgroup G, P ≤ H → IsPGroup p P → IsCyclic P) (h : HasSubquotient H Q)
    (R : Subgroup Q) (hR : IsPGroup p R) : IsCyclic R := by
  obtain ⟨P, hPH, hP, f, hf⟩ := h.exists_isPGroup_surjective R hR
  have := hcyc P hPH hP
  exact isCyclic_of_surjective f hf

theorem HasSubquotient.false_of_isCyclic [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hcyc : ∀ P : Subgroup G, P ≤ H → IsPGroup p P → IsCyclic P) (h : HasSubquotient H Q)
    (hR : ∃ R : Subgroup Q, IsPGroup p R ∧ ¬ IsCyclic R) : False := by
  obtain ⟨R, hRp, hRc⟩ := hR
  exact hRc (h.isCyclic_of_isPGroup hcyc R hRp)

end Obstruction

section AltFive

local notation "A₅" => alternatingGroup (Fin 5)

theorem card_alt_five : Nat.card A₅ = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem commutator_alt_five : _root_.commutator A₅ = ⊤ :=
  commutator_alternatingGroup_eq_top (by simp)

theorem commutator_alt_five_sq : _root_.commutator (A₅ × A₅) = ⊤ := by
  have h5 : ⁅(⊤ : Subgroup A₅), ⊤⁆ = ⊤ := commutator_alt_five
  change ⁅(⊤ : Subgroup (A₅ × A₅)), ⊤⁆ = ⊤
  rw [← Subgroup.top_prod_top, Subgroup.commutator_prod_prod, h5]

theorem not_isPGroup_two_alt_five : ¬ IsPGroup 2 A₅ := by
  intro h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  have h5 : 5 ∣ 2 ^ n := by
    rw [← hn, card_alt_five]
    norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5
  omega

theorem eq_bot_of_normal_isPGroup_two :
    ∀ R : Subgroup (A₅ × A₅), R.Normal → IsPGroup 2 R → R = ⊥ := by
  intro R hR hp
  have key : ∀ π : A₅ × A₅ →* A₅, Function.Surjective π → R.map π = ⊥ := by
    intro π hπ
    have : (R.map π).Normal := hR.map π hπ
    rcases Subgroup.Normal.eq_bot_or_eq_top (R.map π) with h | h
    · exact h
    · exfalso
      have hP : IsPGroup 2 ↥(R.map π) := hp.map π
      rw [h] at hP
      exact not_isPGroup_two_alt_five (hP.of_surjective (Subgroup.topEquiv (G := A₅)).toMonoidHom
        (Subgroup.topEquiv (G := A₅)).surjective)
  rw [Subgroup.eq_bot_iff_forall]
  rintro ⟨a, b⟩ hab
  have ha : a = 1 := by
    have h1 : a ∈ R.map (MonoidHom.fst _ _) := ⟨(a, b), hab, rfl⟩
    rw [key _ fun x => ⟨(x, 1), rfl⟩] at h1
    exact Subgroup.mem_bot.mp h1
  have hb : b = 1 := by
    have h1 : b ∈ R.map (MonoidHom.snd _ _) := ⟨(a, b), hab, rfl⟩
    rw [key _ fun x => ⟨(1, x), rfl⟩] at h1
    exact Subgroup.mem_bot.mp h1
  rw [ha, hb]
  rfl

theorem exists_not_isCyclic_of_orderOf {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {c : G}
    (hc : orderOf c = p) : ∃ R : Subgroup (G × G), IsPGroup p R ∧ ¬ IsCyclic R := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcard : Nat.card ↥((Subgroup.zpowers c).prod (Subgroup.zpowers c)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_zpowers, hc]
    ring
  refine ⟨(Subgroup.zpowers c).prod (Subgroup.zpowers c), IsPGroup.of_card hcard, fun hcyc => ?_⟩
  have hpow : ∀ x ∈ Subgroup.zpowers c, x ^ p = 1 := fun x hx => by
    rw [← orderOf_dvd_iff_pow_eq_one, ← hc]
    exact orderOf_dvd_of_mem_zpowers hx
  have hexp : Monoid.exponent ↥((Subgroup.zpowers c).prod (Subgroup.zpowers c)) ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    exact Subtype.ext (Prod.ext (hpow _ g.2.1) (hpow _ g.2.2))
  rw [IsCyclic.exponent_eq_card, hcard] at hexp
  have := Nat.le_of_dvd (by omega) hexp
  nlinarith

theorem exists_orderOf_alt_five {p : ℕ} [Fact p.Prime] (hp : p ∣ 60) :
    ∃ c : A₅, orderOf c = p :=
  exists_prime_orderOf_dvd_card' p (by rw [card_alt_five]; exact hp)

theorem exists_not_isCyclic_five : ∃ R : Subgroup (A₅ × A₅), IsPGroup 5 R ∧ ¬ IsCyclic R := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨c, hc⟩ := exists_orderOf_alt_five (p := 5) (by norm_num)
  exact exists_not_isCyclic_of_orderOf hc

theorem exists_not_isCyclic_three : ∃ R : Subgroup (A₅ × A₅), IsPGroup 3 R ∧ ¬ IsCyclic R := by
  obtain ⟨c, hc⟩ := exists_orderOf_alt_five (p := 3) (by norm_num)
  exact exists_not_isCyclic_of_orderOf hc

end AltFive

end CFSG.AGLEmbeddingD2.LeviSection
