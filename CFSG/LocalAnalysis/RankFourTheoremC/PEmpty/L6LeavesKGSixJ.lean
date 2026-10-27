module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGSix

open CFSG.Open Subgroup

variable {G : Type} [Group G]

@[expose] def IsEmax (T E : Subgroup G) : Prop :=
  E ≤ T ∧ IsElemAbelian 2 E ∧
    ∀ E' : Subgroup G, E' ≤ T → IsElemAbelian 2 E' → Nat.card E' ≤ Nat.card E

@[expose] def thompson (T : Subgroup G) : Subgroup G :=
  closure {g | ∃ E : Subgroup G, IsEmax T E ∧ g ∈ E}

theorem thompson_le {T : Subgroup G} : thompson T ≤ T := by
  refine (closure_le _).mpr ?_
  rintro g ⟨E, hE, hg⟩
  exact hE.1 hg

theorem le_thompson {T E : Subgroup G} (hE : IsEmax T E) : E ≤ thompson T :=
  fun _ hg => subset_closure ⟨E, hE, hg⟩

theorem IsEmax.conj {T E : Subgroup G} (h : IsEmax T E) {g : G}
    (hg : g ∈ normalizer (T : Set G)) : IsEmax T (E.map (MulAut.conj g).toMonoidHom) := by
  have hcard : Nat.card ↥(E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  refine ⟨?_, h.2.1.map _, fun E' h1 h2 => hcard ▸ h.2.2 E' h1 h2⟩
  rintro _ ⟨e, he, rfl⟩
  have := (mem_normalizer_iff.mp hg e).mp (h.1 he)
  simpa [MulAut.conj_apply] using this

theorem mem_normalizer_thompson {T : Subgroup G} {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g ∈ normalizer (thompson T : Set G) := by
  have key : ∀ g ∈ normalizer (T : Set G), ∀ x ∈ thompson T, g * x * g⁻¹ ∈ thompson T := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨E, hE, hxE⟩ := hx
      exact le_thompson (hE.conj hg) ⟨x, hxE, by simp [MulAut.conj_apply]⟩
    | one => simp
    | mul x y _ _ ihx ihy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact mul_mem ihx ihy
    | inv x _ ih =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem ih
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

variable [Finite G]

theorem exists_isEmax (T : Subgroup G) : ∃ E, IsEmax T E := by
  obtain ⟨E, ⟨hET, hEe⟩, hmax⟩ :=
    Set.exists_max_image {E : Subgroup G | E ≤ T ∧ IsElemAbelian 2 E} (fun E => Nat.card E)
      (Set.toFinite _) ⟨⊥, bot_le, isElemAbelian_bot 2⟩
  exact ⟨E, hET, hEe, fun E' h1 h2 => hmax E' ⟨h1, h2⟩⟩

theorem thompson_char (T : Subgroup G) : ((thompson T).subgroupOf T).Characteristic := by
  rw [characteristic_iff_le_comap]
  intro ϕ x hx
  have key : ∀ g ∈ thompson T, ∃ hg : g ∈ T, ((ϕ ⟨g, hg⟩ : ↥T) : G) ∈ thompson T := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨E, hE, hgE⟩ := hg
      have hgT : g ∈ T := hE.1 hgE
      refine ⟨hgT, ?_⟩
      set E' : Subgroup G := ((E.subgroupOf T).map ϕ.toMonoidHom).map T.subtype with hE'
      have hcard : Nat.card E' = Nat.card E := by
        rw [hE', Subgroup.card_map_of_injective T.subtype_injective,
          Subgroup.card_map_of_injective ϕ.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE.1).toEquiv]
      have hE'max : IsEmax T E' :=
        ⟨Subgroup.map_subtype_le _, ((hE.2.1.subgroupOf T).map ϕ.toMonoidHom).map _,
          fun E'' h1 h2 => hcard ▸ hE.2.2 E'' h1 h2⟩
      refine le_thompson hE'max ?_
      exact ⟨ϕ ⟨g, hgT⟩, ⟨⟨g, hgT⟩, hgE, rfl⟩, rfl⟩
    | one =>
      refine ⟨T.one_mem, ?_⟩
      have : (⟨1, T.one_mem⟩ : ↥T) = 1 := rfl
      rw [this, map_one, Subgroup.coe_one]
      exact (thompson T).one_mem
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxT, hx⟩ := ihx
      obtain ⟨hyT, hy⟩ := ihy
      refine ⟨T.mul_mem hxT hyT, ?_⟩
      have : (⟨x * y, T.mul_mem hxT hyT⟩ : ↥T) = ⟨x, hxT⟩ * ⟨y, hyT⟩ := rfl
      rw [this, map_mul, Subgroup.coe_mul]
      exact mul_mem hx hy
    | inv x _ ih =>
      obtain ⟨hxT, hx⟩ := ih
      refine ⟨T.inv_mem hxT, ?_⟩
      have : (⟨x⁻¹, T.inv_mem hxT⟩ : ↥T) = (⟨x, hxT⟩ : ↥T)⁻¹ := rfl
      rw [this, map_inv, Subgroup.coe_inv]
      exact inv_mem hx
  obtain ⟨hxT, h⟩ := key (x : G) hx
  exact h

theorem thompson_eq_of_forall {S D : Subgroup G} (hDS : D ≤ S)
    (hD : ∀ E, IsEmax S E → E ≤ D) : thompson S = thompson D := by
  obtain ⟨E₀, hE₀⟩ := exists_isEmax S
  have hiff : ∀ E, IsEmax S E ↔ IsEmax D E := by
    intro E
    constructor
    · intro h
      exact ⟨hD E h, h.2.1, fun E' h1 h2 => h.2.2 E' (h1.trans hDS) h2⟩
    · intro h
      refine ⟨h.1.trans hDS, h.2.1, fun E' h1 h2 => ?_⟩
      exact (hE₀.2.2 E' h1 h2).trans (h.2.2 E₀ (hD E₀ hE₀) hE₀.2.1)
  unfold thompson
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, hiff]

theorem exists_sq_eq_one_ne_one {S : Subgroup G} (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) :
    ∃ s ∈ S, s ^ 2 = 1 ∧ s ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hS1 (Subgroup.card_eq_one.mp (by simpa using hk))
  have h2 : 2 ∣ Nat.card ↥S := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 2 h2
  refine ⟨x, x.2, ?_, ?_⟩
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  · intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    omega

theorem exists_isEmax_not_le {S D H L M : Subgroup G} (hDS : D ≤ S)
    (hHD : H ≤ normalizer (D : Set G)) (hLH : L ≤ H) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hchar : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
      normalizer (S₀ : Set G) ≤ M) (hL : ¬ L ≤ M) :
    ∃ E, IsEmax S E ∧ ¬ E ≤ D := by
  by_contra hcon
  push Not at hcon
  have hJ := thompson_eq_of_forall hDS hcon
  have hJne : thompson S ≠ ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨s, hsS, hs2, hs1⟩ := exists_sq_eq_one_ne_one hS2 hS1
    obtain ⟨E, hE⟩ := exists_isEmax S
    have hzs : Nat.card ↥(zpowers s) ≤ Nat.card E :=
      hE.2.2 _ (zpowers_le.mpr hsS) (isElemAbelian_zpowers hs2)
    rw [Nat.card_zpowers, orderOf_eq_prime hs2 hs1] at hzs
    intro h
    have hEbot : E = ⊥ := le_bot_iff.mp (h ▸ le_thompson hE)
    rw [hEbot, Subgroup.card_bot] at hzs
    omega
  have hNM := hchar (thompson S) thompson_le hJne (thompson_char S)
  apply hL
  intro l hl
  apply hNM
  rw [hJ]
  exact mem_normalizer_thompson (hHD (hLH hl))

theorem card_le_two_mul {T A₀ V : Subgroup G} (hA : IsEmax T A₀) (hV : IsElemAbelian 2 V)
    (hVT : V ≤ T)
    (hidx : Nat.card A₀ ≤ 2 * Nat.card ↥(A₀ ⊓ centralizer (V : Set G))) {a : G} (ha : a ∈ A₀) :
    Nat.card V ≤ 2 * Nat.card ↥(V ⊓ centralizer ({a} : Set G)) := by
  set C : Subgroup G := A₀ ⊓ centralizer (V : Set G) with hC
  have hc : ∀ x ∈ C, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp hx.2 y hy).symm
  have hCe : IsElemAbelian 2 C := hA.2.1.mono inf_le_left
  have hsup : IsElemAbelian 2 (C ⊔ V) := hCe.sup_of_commute hV hc
  have hle : Nat.card ↥(C ⊔ V) ≤ Nat.card A₀ :=
    hA.2.2 _ (sup_le (inf_le_left.trans hA.1) hVT) hsup
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C V hc).1
  have hCV : C ⊓ V ≤ V ⊓ centralizer ({a} : Set G) := fun x hx =>
    ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.mpr (hA.2.1.comm hx.1.1 ha)⟩
  have hCV' : Nat.card ↥(C ⊓ V) ≤ Nat.card ↥(V ⊓ centralizer ({a} : Set G)) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hCV)
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have h1 : Nat.card C * Nat.card V ≤
      Nat.card C * (2 * Nat.card ↥(V ⊓ centralizer ({a} : Set G))) := by
    calc Nat.card C * Nat.card V = Nat.card ↥(C ⊔ V) * Nat.card ↥(C ⊓ V) := hprod.symm
      _ ≤ Nat.card A₀ * Nat.card ↥(V ⊓ centralizer ({a} : Set G)) := Nat.mul_le_mul hle hCV'
      _ ≤ (2 * Nat.card C) * Nat.card ↥(V ⊓ centralizer ({a} : Set G)) :=
          Nat.mul_le_mul_right _ hidx
      _ = Nat.card C * (2 * Nat.card ↥(V ⊓ centralizer ({a} : Set G))) := by ring
  exact Nat.le_of_mul_le_mul_left h1 hCpos

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGSix
