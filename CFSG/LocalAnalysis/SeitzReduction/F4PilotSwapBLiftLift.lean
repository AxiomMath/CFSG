module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLift
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup
open scoped commutatorElement
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Lift

variable {H : Type} [Group H]

theorem map_conj_oddCoreLift [Finite H] (E : Subgroup (H ⧸ oddCore H)) (t : H) :
    (oddCoreLift E).map (MulAut.conj t).toMonoidHom =
      oddCoreLift (E.map (MulAut.conj (QuotientGroup.mk' (oddCore H) t)).toMonoidHom) := by
  unfold oddCoreLift
  rw [CFSG.Quasithin.map_perfectCore]
  congr 1
  ext x
  simp only [mem_map, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, hy, by simp only [map_mul, map_inv]⟩
  · rintro ⟨e, he, hex⟩
    refine ⟨t⁻¹ * x * t, ?_, by group⟩
    have : QuotientGroup.mk' (oddCore H) (t⁻¹ * x * t) = e := by
      rw [map_mul, map_mul, map_inv, ← hex]
      group
    rw [this]
    exact he

theorem odd_card_oddCore_subgroupOf [Finite H] (A : Subgroup H) :
    Odd (Nat.card ((oddCore H).subgroupOf A)) := by
  have hO : Odd (Nat.card (oddCore H)) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have h1 : Nat.card ((oddCore H).subgroupOf A) = Nat.card ((oddCore H ⊓ A : Subgroup H)) := by
    rw [← card_map_of_injective A.subtype_injective, subgroupOf_map_subtype]
  rw [h1]
  exact hO.of_dvd_nat (card_dvd_of_le inf_le_left)

end Lift

@[expose] def OddSchurTrivial (K : Type) [Group K] : Prop :=
  ∀ (P : Type) [Group P] [Finite P], Group.IsPerfect P → ∀ η : P →* K, Function.Surjective η →
    η.ker ≤ center P → Odd (Nat.card η.ker) → Function.Injective η

theorem OddSchurTrivial.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : OddSchurTrivial K) : OddSchurTrivial K' := by
  intro P _ _ hP η hη hcen hodd
  have hη' : Function.Surjective (e.symm.toMonoidHom.comp η) := e.symm.surjective.comp hη
  have hker : (e.symm.toMonoidHom.comp η).ker = η.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, MulEquiv.symm_apply_eq, map_one]
  have hinj := h P hP (e.symm.toMonoidHom.comp η) hη' (hker ▸ hcen) (hker ▸ hodd)
  intro a b hab
  exact hinj (by simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    hab])

section Decomposition

variable {H : Type} [Group H] [Finite H]

theorem oddCore_quotient_oddCore_eq_bot_of_finite : oddCore (H ⧸ oddCore H) = ⊥ := by
  have hodd : ∀ (X : Type) [Group X] [Finite X], Odd (Nat.card (oddCore X)) := fun X _ _ =>
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set N := (oddCore (H ⧸ oddCore H)).comap π with hN
  have hNn : N.Normal := (CFSG.oddCore_normal _).comap π
  have hidx : N.index = (oddCore (H ⧸ oddCore H)).index :=
    index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h1 := N.card_mul_index
  have h2 := (oddCore (H ⧸ oddCore H)).card_mul_index
  have h3 := card_eq_card_quotient_mul_card_subgroup (oddCore H)
  have hcard : Nat.card N = Nat.card (oddCore (H ⧸ oddCore H)) * Nat.card (oddCore H) := by
    have hidx0 : N.index ≠ 0 := index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx0)
    rw [h1, h3, ← h2, hidx]
    ring
  have hNodd : Odd (Nat.card N) := by
    rw [hcard]
    exact (hodd _).mul (hodd H)
  have hNle : N ≤ oddCore H := le_sSup ⟨hNn, hNodd⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (oddCore H) x
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hNle hx

theorem perfect_le_of_forall_exists_commute {A : Type*} [Group A] {P M : Subgroup A}
    (hP : ⁅P, P⁆ = P) (hMP : M ≤ P)
    (h : ∀ a ∈ P, ∃ m ∈ M, ∃ z : A, a = m * z ∧ ∀ b ∈ P, z * b = b * z) : P ≤ M := by
  rw [← hP, commutator_le]
  intro a ha b hb
  obtain ⟨m₁, hm₁, z₁, rfl, hz₁⟩ := h a ha
  obtain ⟨m₂, hm₂, z₂, rfl, hz₂⟩ := h b hb
  have c1 : z₁ * (m₂ * z₂) = m₂ * z₂ * z₁ := hz₁ _ hb
  have c2 : z₂ * m₁⁻¹ = m₁⁻¹ * z₂ := by
    have := hz₂ _ (inv_mem (hMP hm₁))
    exact this
  have e : ⁅m₁ * z₁, m₂ * z₂⁆ = ⁅m₁, m₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc m₁ * z₁ * (m₂ * z₂) * (m₁ * z₁)⁻¹ * (m₂ * z₂)⁻¹ =
        m₁ * (z₁ * (m₂ * z₂)) * z₁⁻¹ * m₁⁻¹ * (m₂ * z₂)⁻¹ := by group
      _ = m₁ * (m₂ * z₂ * z₁) * z₁⁻¹ * m₁⁻¹ * (m₂ * z₂)⁻¹ := by rw [c1]
      _ = m₁ * m₂ * (z₂ * m₁⁻¹) * z₂⁻¹ * m₂⁻¹ := by group
      _ = m₁ * m₂ * (m₁⁻¹ * z₂) * z₂⁻¹ * m₂⁻¹ := by rw [c2]
      _ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by group
  rw [e, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hm₁ hm₂) (inv_mem hm₁)) (inv_mem hm₂)

theorem swapLift_decomposition {t : H} (ht : t * t = 1)
    (hC : ∀ c ∈ oddCore H, c * t = t * c → c ∈ center H)
    {Kb Db : Subgroup (H ⧸ oddCore H)}
    (h : SwapComponentData (QuotientGroup.mk' (oddCore H) t) Kb Db)
    (hOut : Group.IsSolvable (Outer Kb)) (hSchur : OddSchurTrivial Kb) :
    (oddCoreLift Kb).map (MulAut.conj t).toMonoidHom ≤ centralizer (oddCoreLift Kb : Set H) ∧
      oddCoreLift Kb ⊓ (oddCoreLift Kb).map (MulAut.conj t).toMonoidHom = ⊥ ∧
      oddCoreLift Kb ⊔ (oddCoreLift Kb).map (MulAut.conj t).toMonoidHom =
        perfectCore (⊤ : Subgroup H) ∧
      ⁅oddCoreLift Kb, oddCoreLift Kb⁆ = oddCoreLift Kb ∧
      oddCoreLift Kb ⊓ oddCore H = ⊥ ∧ Nat.card (oddCoreLift Kb) = Nat.card Kb := by
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set τ := π t with hτ
  set Kh := oddCoreLift Kb with hKh
  have hO := oddCore_quotient_oddCore_eq_bot_of_finite (H := H)
  have hKp : ⁅Kb, Kb⁆ = Kb := isPerfect_iff.mp h.isComponent.1.1
  have hKτp : ⁅Kb.map (MulAut.conj τ).toMonoidHom, Kb.map (MulAut.conj τ).toMonoidHom⁆ =
      Kb.map (MulAut.conj τ).toMonoidHom := by
    rw [← map_commutator, hKp]
  obtain ⟨hBsup, hBK⟩ := hasBLift_sup_conj_of_le_center ht hKp h.commute hC
  have hKt : Kh.map (MulAut.conj t).toMonoidHom =
      oddCoreLift (Kb.map (MulAut.conj τ).toMonoidHom) :=
    map_conj_oddCoreLift Kb t
  have hKhp : ⁅Kh, Kh⁆ = Kh := commutator_oddCoreLift Kb
  have hKhtp : ⁅Kh.map (MulAut.conj t).toMonoidHom, Kh.map (MulAut.conj t).toMonoidHom⁆ =
      Kh.map (MulAut.conj t).toMonoidHom := by
    rw [← map_commutator, hKhp]
  have hπK : Kh.map π = Kb := map_oddCoreLift hKp
  have hπKt : (Kh.map (MulAut.conj t).toMonoidHom).map π = Kb.map (MulAut.conj τ).toMonoidHom := by
    rw [hKt]
    exact map_oddCoreLift hKτp
  have hOK : oddCore H ≤ centralizer (Kh : Set H) := le_centralizer_iff.1 hBK
  have hcomm : ⁅Kh, Kh.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
    apply CFSG.LocalCores.perfect_double_commutator (isPerfect_iff.mpr hKhp)
    have h1 : ⁅Kh, Kh.map (MulAut.conj t).toMonoidHom⁆ ≤ oddCore H := by
      have h2 : (⁅Kh, Kh.map (MulAut.conj t).toMonoidHom⁆).map π = ⊥ := by
        rw [map_commutator, hπK, hπKt]
        exact h.commute
      have h3 := (Subgroup.map_eq_bot_iff _).1 h2
      rwa [hπ, QuotientGroup.ker_mk'] at h3
    exact commutator_eq_bot_iff_le_centralizer.2 (h1.trans hOK)
  set η : Kh →* Kb := (MulEquiv.subgroupCongr hπK).toMonoidHom.comp (π.subgroupMap Kh) with hη
  have hηapp : ∀ x : Kh, ((η x : Kb) : H ⧸ oddCore H) = π x := fun x => rfl
  have hηsurj : Function.Surjective η :=
    (MulEquiv.subgroupCongr hπK).surjective.comp (π.subgroupMap_surjective Kh)
  have hηker : η.ker = (oddCore H).subgroupOf Kh := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h1
      have h2 : π x = 1 := by rw [← hηapp, h1]; rfl
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    · intro h1
      apply Subtype.ext
      rw [hηapp, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 h1]
      rfl
  have hηinj : Function.Injective η :=
    hSchur Kh (isPerfect_iff.mpr hKhp) η hηsurj (hηker ▸ hBK.inf_le_center)
      (hηker ▸ odd_card_oddCore_subgroupOf Kh)
  have hKO : Kh ⊓ oddCore H = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxO⟩
    have h1 : η ⟨x, hxK⟩ = η 1 := by
      rw [map_one]
      exact (MonoidHom.mem_ker).1 (hηker ▸ (mem_subgroupOf.2 hxO))
    exact mem_bot.2 (congrArg Subtype.val (hηinj h1))
  have hcard : Nat.card Kh = Nat.card Kb :=
    Nat.card_congr (MulEquiv.ofBijective η ⟨hηinj, hηsurj⟩).toEquiv
  have hdisj : Kh ⊓ Kh.map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hxt⟩
    have h1 : π x ∈ Kb ⊓ Kb.map (MulAut.conj τ).toMonoidHom :=
      ⟨hπK ▸ mem_map_of_mem π hx, hπKt ▸ mem_map_of_mem π hxt⟩
    rw [h.inf_eq_bot hO, mem_bot] at h1
    have hxO : x ∈ oddCore H := by
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hKO.le ⟨hx, hxO⟩
  have hle : Kh ⊔ Kh.map (MulAut.conj t).toMonoidHom ≤ perfectCore (⊤ : Subgroup H) :=
    sup_le (CFSG.Quasithin.le_perfectCore_of_perfect le_top hKhp)
      (CFSG.Quasithin.le_perfectCore_of_perfect le_top hKhtp)
  have hsup : Kh ⊔ Kh.map (MulAut.conj t).toMonoidHom = perfectCore (⊤ : Subgroup H) := by
    refine le_antisymm hle ?_
    have hPp := CFSG.Quasithin.perfectCore_perfect (⊤ : Subgroup H)
    have hPmap : (perfectCore (⊤ : Subgroup H)).map π ≤
        Kb ⊔ Kb.map (MulAut.conj τ).toMonoidHom := by
      rw [CFSG.Quasithin.map_perfectCore, map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
      exact h.perfectCore_top_le hO hOut
    have hPO : perfectCore (⊤ : Subgroup H) ≤ centralizer (oddCore H : Set H) :=
      (le_oddCoreLift_of_perfect hPp hPmap).trans hBsup
    refine perfect_le_of_forall_exists_commute hPp hle fun a ha => ?_
    have hπa : π a ∈ (Kh ⊔ Kh.map (MulAut.conj t).toMonoidHom).map π := by
      rw [Subgroup.map_sup, hπK, hπKt]
      exact hPmap (mem_map_of_mem π ha)
    obtain ⟨m, hm, hma⟩ := hπa
    refine ⟨m, hm, m⁻¹ * a, by group, fun b hb => ?_⟩
    have hz : m⁻¹ * a ∈ oddCore H := by
      have h2 : π (m⁻¹ * a) = 1 := by rw [map_mul, map_inv, hma, inv_mul_cancel]
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact mem_centralizer_iff.1 (hPO hb) _ hz
  exact ⟨le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm), hdisj, hsup, hKhp,
    hKO, hcard⟩

end Decomposition

end CFSG.SeitzReduction.F4Pilot
