module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Aux
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma68
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Weak

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open Lemma68Aux

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

theorem outerLemma112 (h : OuterE G L z t T E) (hW : WFacts L t E) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hzS : z ∈ S) (hD8 : Nonempty (S ≃* DihedralGroup 4))
    (hcent : ∀ v ∈ centralizer (E : Set G), v * z = z * v →
      v = 1 ∨ v = z ∨ v = t ∨ v = t * z)
    (h67 : ∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t)
    (hX : ∀ u ∈ S ⊔ E, u * u = 1 → u ∉ zpowers t →
      ∃ X : Subgroup G, X ≤ S ⊔ E ∧ Nonempty (E ≃* X) ∧ u ∉ X ∧ ∀ x ∈ X, u * x = x * u) :
    ∀ g : G, g * z * g⁻¹ ∈ S ⊔ E →
      ∃ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), m * z * m⁻¹ = g * z * g⁻¹ := by
  intro g hgU
  have hcfg := h.cfg
  have hE := h.econfig
  have hE2 : IsPGroup 2 E := hcfg.T_pgroup.to_le h.E_le_T
  have hU2 : IsPGroup 2 (S ⊔ E : Subgroup G) :=
    hS2.to_sup_of_normal_right' hE2 (hSC.trans (centralizer_le_normalizer E))
  have hzE : ∀ e ∈ E, e * z = z * e := fun e he => hcfg.z_comm_of_mem_A (h.E_le_L he)
  have hzE' : z ∉ E := fun hz => hcfg.z_not_mem_A (h.E_le_L hz)
  have hS8 : Nat.card S = 8 := by
    rw [Nat.card_congr hD8.some.toEquiv, DihedralGroup.nat_card]
  have hE32 : Nat.card E = 32 := hW.card_E
  have htE : t ∈ E := hE.t_mem
  have htc : ∀ e ∈ E, e * t = t * e := fun e he => hcfg.t_central e (h.E_le_T he)
  have htS : t ∈ S := mem_of_maximal hS2 hSC hSmax hcfg.t_sq htE htc
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ = g * z * g⁻¹ := ⟨_, rfl⟩
  rw [← hz₀] at hgU ⊢
  have hz₀2 : z₀ * z₀ = 1 := by
    rw [hz₀]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hcfg.z_sq]; group
  have hz₀1 : z₀ ≠ 1 := by
    intro h1
    apply hcfg.z_ne
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [← hz₀, h1]; group
  have hz₀t : z₀ ≠ t := fun h1 => hcfg.conj_z_ne_t g (hz₀ ▸ h1)
  have hz₀nt : z₀ ∉ zpowers t := fun hm => by
    rcases mem_zpowers_sq_eq_one hcfg.t_sq hm with h1 | h1
    exacts [hz₀1 h1, hz₀t h1]
  obtain ⟨X, hXU, ⟨eEX⟩, hz₀X, hXc⟩ := hX z₀ hgU hz₀2 hz₀nt
  have hX32 : Nat.card X = 32 := (Nat.card_congr eEX.toEquiv).symm.trans hE32
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : Subgroup G, X₁ = X ⊔ zpowers z₀ := ⟨_, rfl⟩
  have hX₁card : Nat.card X₁ = 64 := by
    rw [hX₁, card_sup_zpowers_of_comm hz₀2 hz₀X hXc, hX32]
  have hzU : zpowers z₀ ≤ S ⊔ E := zpowers_le.2 hgU
  have hX₁U : X₁ ≤ S ⊔ E := hX₁ ▸ sup_le hXU hzU
  have hX₁c : X₁ ≤ centralizer ({z₀} : Set G) := by
    rw [hX₁]
    refine sup_le (fun y hy => mem_centralizer_singleton_iff.2 (hXc y hy).symm) ?_
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl
  have hY2 : IsPGroup 2 (X₁.map (MulAut.conj g⁻¹).toMonoidHom) := (hU2.to_le hX₁U).map _
  have hYz : X₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff, conj_toMonoidHom_apply]
    have hyc := mem_centralizer_singleton_iff.1 (hX₁c hy)
    calc g⁻¹ * y * g⁻¹⁻¹ * z = g⁻¹ * (y * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (y * z₀) * g := by rw [hz₀]
      _ = g⁻¹ * (z₀ * y) * g := by rw [hyc]
      _ = z * (g⁻¹ * y * g⁻¹⁻¹) := by rw [hz₀]; group
  obtain ⟨c, hcz, hcT⟩ := hcfg.exists_conj_le_T hY2 hYz
  have hcz' : c * z = z * c := mem_centralizer_singleton_iff.1 hcz
  obtain ⟨g', hg'⟩ : ∃ g', g' = g * c := ⟨_, rfl⟩
  have hg'z : g' * z * g'⁻¹ = z₀ := by
    rw [hg', hz₀]
    calc g * c * z * (g * c)⁻¹ = g * (c * z) * c⁻¹ * g⁻¹ := by group
      _ = g * (z * c) * c⁻¹ * g⁻¹ := by rw [hcz']
      _ = g * z * g⁻¹ := by group
  have hg'T : ∀ y ∈ X₁, g'⁻¹ * y * g' ∈ T := by
    intro y hy
    have h1 := hcT _ ⟨y, hy, rfl⟩
    rw [conj_toMonoidHom_apply] at h1
    have e : g'⁻¹ * y * g' = c⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) * c := by rw [hg']; group
    rw [e]
    exact h1
  obtain ⟨P, hP⟩ : ∃ P : Subgroup G, P = X.map (MulAut.conj g'⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hPT : P ≤ T := by
    rw [hP]
    rintro _ ⟨y, hy, rfl⟩
    rw [conj_toMonoidHom_apply]
    have := hg'T y (hX₁ ▸ mem_sup_left hy)
    simpa using this
  have hPiso : Nonempty (E ≃* P) := by
    rw [hP]
    exact ⟨eEX.trans (X.equivMapOfInjective (MulAut.conj g'⁻¹).toMonoidHom
      (MulAut.conj g'⁻¹).injective)⟩
  have hPle : P ≤ E ⊔ zpowers z := h.le_sup_of_equiv hPT hPiso
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : Subgroup G, E₀ = E.map (MulAut.conj g').toMonoidHom := ⟨_, rfl⟩
  have hKeq : (E ⊔ zpowers z).map (MulAut.conj g').toMonoidHom = E₀ ⊔ zpowers z₀ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, conj_toMonoidHom_apply, hg'z, hE₀]
  have hKcard : Nat.card (E₀ ⊔ zpowers z₀ : Subgroup G) = 64 := by
    rw [← hKeq, Subgroup.card_map_of_injective (MulAut.conj g').injective,
      card_sup_zpowers_of_comm hcfg.z_sq hzE' (fun e he => (hzE e he).symm), hE32]
  have hXK : X ≤ E₀ ⊔ zpowers z₀ := by
    intro y hy
    rw [← hKeq, mem_map_conj_iff]
    have hyP : (MulAut.conj g'⁻¹).toMonoidHom y ∈ P := by
      rw [hP]
      exact ⟨y, hy, rfl⟩
    have := hPle hyP
    rw [conj_toMonoidHom_apply] at this
    simpa using this
  have hX₁K : X₁ = E₀ ⊔ zpowers z₀ := by
    refine Subgroup.eq_of_le_of_card_ge (hX₁ ▸ sup_le hXK le_sup_right) ?_
    rw [hKcard, hX₁card]
  have hE₀U : E₀ ≤ S ⊔ E := le_sup_left.trans (hX₁K ▸ hX₁U)
  have hE₀iso : Nonempty (E ≃* E₀) := by
    rw [hE₀]
    exact ⟨E.equivMapOfInjective (MulAut.conj g').toMonoidHom (MulAut.conj g').injective⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Subgroup G, S₀ = (S ⊔ E) ⊓ centralizer (E₀ : Set G) := ⟨_, rfl⟩
  have hS₀2 : IsPGroup 2 S₀ := hS₀ ▸ hU2.to_le inf_le_left
  have hS₀card : 8 ≤ Nat.card S₀ :=
    hS₀ ▸ eight_le_card_cent_gen hE hE32 hcfg.t_sq hcfg.t_ne htc hSC htS hD8 hE₀U hE₀iso
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Subgroup G, P₀ = S₀.map (MulAut.conj g'⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hP₀mem : ∀ y, y ∈ P₀ ↔ g' * y * g'⁻¹ ∈ S₀ := by
    intro y
    rw [hP₀, mem_map_conj_iff, inv_inv]
  have hP₀2 : IsPGroup 2 P₀ := hP₀ ▸ hS₀2.map _
  have hP₀C : P₀ ≤ centralizer (E : Set G) := by
    intro s hs
    rw [mem_centralizer_iff]
    intro e he
    have hs' : g' * s * g'⁻¹ ∈ centralizer (E₀ : Set G) := (hS₀ ▸ (hP₀mem s).1 hs).2
    have hs'' := mem_centralizer_iff.1 hs' (g' * e * g'⁻¹) (hE₀ ▸ ⟨e, he, rfl⟩)
    calc e * s = g'⁻¹ * ((g' * e * g'⁻¹) * (g' * s * g'⁻¹)) * g' := by group
      _ = g'⁻¹ * ((g' * s * g'⁻¹) * (g' * e * g'⁻¹)) * g' := by rw [hs'']
      _ = s * e := by group
  have hP₀card : 8 ≤ Nat.card P₀ := by
    rw [hP₀, Subgroup.card_map_of_injective (MulAut.conj g'⁻¹).injective]
    exact hS₀card
  obtain ⟨h', hh'C, hh'⟩ := exists_conj_map_of_maximal hS2 hSC hP₀2 hP₀C hSmax (by omega)
  have hh'E : ∀ e ∈ E, h' * e = e * h' := fun e he => (mem_centralizer_iff.1 hh'C e he).symm
  have hSmem : ∀ s ∈ S, g' * (h' * s * h'⁻¹) * g'⁻¹ ∈ S₀ := by
    intro s hs
    have : h' * s * h'⁻¹ ∈ P₀ := by
      rw [hh']
      exact ⟨s, hs, by rw [conj_toMonoidHom_apply]⟩
    exact (hP₀mem _).1 this
  obtain ⟨m, hm⟩ : ∃ m, m = g' * h' := ⟨_, rfl⟩
  have hmle : (S ⊔ E).map (MulAut.conj m).toMonoidHom ≤ S ⊔ E := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      rw [conj_toMonoidHom_apply]
      have e : m * s * m⁻¹ = g' * (h' * s * h'⁻¹) * g'⁻¹ := by rw [hm]; group
      rw [e]
      exact (hS₀ ▸ hSmem s hs : _ ∈ (S ⊔ E) ⊓ centralizer (E₀ : Set G)).1
    · rintro _ ⟨e, he, rfl⟩
      rw [conj_toMonoidHom_apply]
      have e' : m * e * m⁻¹ = g' * e * g'⁻¹ := by
        rw [hm]
        calc g' * h' * e * (g' * h')⁻¹ = g' * (h' * e) * h'⁻¹ * g'⁻¹ := by group
          _ = g' * (e * h') * h'⁻¹ * g'⁻¹ := by rw [hh'E e he]
          _ = g' * e * g'⁻¹ := by group
      rw [e']
      exact hE₀U (hE₀ ▸ ⟨e, he, rfl⟩)
  have hmeq : (S ⊔ E).map (MulAut.conj m).toMonoidHom = S ⊔ E :=
    Subgroup.eq_of_le_of_card_ge hmle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj m).injective])
  have hmN : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact hmle ⟨u, hu, rfl⟩
    · intro hu
      rw [← hmeq] at hu
      obtain ⟨u', hu', hu'e⟩ := hu
      have : u' = u := by
        have h2 : m * u' * m⁻¹ = m * u * m⁻¹ := hu'e
        exact mul_left_cancel (mul_right_cancel h2)
      rwa [← this]
  have hz₀S₀ : z₀ ∈ S₀ := by
    rw [hS₀]
    refine ⟨hgU, mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨e, he, rfl⟩ := (hE₀ ▸ hy : y ∈ E.map (MulAut.conj g').toMonoidHom)
    rw [conj_toMonoidHom_apply, ← hg'z]
    calc g' * e * g'⁻¹ * (g' * z * g'⁻¹) = g' * (e * z) * g'⁻¹ := by group
      _ = g' * (z * e) * g'⁻¹ := by rw [hzE e he]
      _ = g' * z * g'⁻¹ * (g' * e * g'⁻¹) := by group
  have hzP₀ : z ∈ P₀ := (hP₀mem z).2 (by rw [hg'z]; exact hz₀S₀)
  rw [hh'] at hzP₀
  obtain ⟨s₁, hs₁S, hs₁⟩ := hzP₀
  rw [conj_toMonoidHom_apply] at hs₁
  have hconjS : h'⁻¹ * z * h'⁻¹⁻¹ ∈ S := by
    have : h'⁻¹ * z * h'⁻¹⁻¹ = s₁ := by rw [← hs₁]; group
    rw [this]
    exact hs₁S
  rcases h67 h'⁻¹ hconjS with hz | hzt
  · have hz'' : h'⁻¹ * z * h' = z := by simpa using hz
    have hz' : h' * z * h'⁻¹ = z := by
      calc h' * z * h'⁻¹ = h' * (h'⁻¹ * z * h') * h'⁻¹ := by rw [hz'']
        _ = z := by group
    refine ⟨m, hmN, ?_⟩
    calc m * z * m⁻¹ = g' * (h' * z * h'⁻¹) * g'⁻¹ := by rw [hm]; group
      _ = g' * z * g'⁻¹ := by rw [hz']
      _ = z₀ := hg'z
  · obtain ⟨s, hsS, hs⟩ := exists_conj_z_eq_zt_outer hSC hD8 hcent h67 hzS hcfg.t_comm_z
    have hzt' : h'⁻¹ * z * h' = z * t := by simpa using hzt
    have hz' : h' * (z * t) * h'⁻¹ = z := by
      calc h' * (z * t) * h'⁻¹ = h' * (h'⁻¹ * z * h') * h'⁻¹ := by rw [hzt']
        _ = z := by group
    refine ⟨m * s, mul_mem hmN (le_normalizer (mem_sup_left hsS)), ?_⟩
    calc m * s * z * (m * s)⁻¹ = m * (s * z * s⁻¹) * m⁻¹ := by group
      _ = m * (z * t) * m⁻¹ := by rw [hs]
      _ = g' * (h' * (z * t) * h'⁻¹) * g'⁻¹ := by rw [hm]; group
      _ = g' * z * g'⁻¹ := by rw [hz']
      _ = z₀ := hg'z

end CFSG.EvenSporadicStandard.Fin76b
