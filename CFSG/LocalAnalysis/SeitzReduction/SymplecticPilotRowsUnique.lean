module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRowsTransport
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDetOrders

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

@[expose] def kindOrder (m f : ℕ) : Sp2mKind → ℕ
  | .field => F4Pilot.evenLieOrder .PSp m (2 * f)
  | .swap => 0
  | .linearEven => F4Pilot.evenLieOrder .PSL (2 * m) f
  | .unitaryEven => F4Pilot.evenLieOrder .PSU (2 * m) f
  | .linearOdd => F4Pilot.evenLieOrder .PSL (2 * m + 1) f
  | .unitaryOdd => F4Pilot.evenLieOrder .PSU (2 * m + 1) f
  | .omegaPlus => F4Pilot.evenLieOrder .POmegaPlus (m + 1) f
  | .omegaMinus => F4Pilot.evenLieOrder .POmegaMinus (m + 1) f

@[expose] def KindAdmissible (m f : ℕ) : Sp2mKind → Prop
  | .field => 2 ≤ m ∧ 1 ≤ f
  | .swap => False
  | .linearEven => 1 ≤ m ∧ 1 ≤ f
  | .unitaryEven => 2 ≤ m ∧ 1 ≤ f
  | .linearOdd => 1 ≤ m ∧ 1 ≤ f
  | .unitaryOdd => 1 ≤ m ∧ 1 ≤ f
  | .omegaPlus => 3 ≤ m ∧ 1 ≤ f
  | .omegaMinus => 3 ≤ m ∧ 1 ≤ f

@[expose] def kindTwoLin (m : ℕ) : Sp2mKind → ℕ
  | .field => 2 * m
  | .swap => 0
  | .linearEven => 2 * m - 1
  | .unitaryEven => 2 * m - 1
  | .linearOdd => 2 * m + 1
  | .unitaryOdd => 2 * m + 1
  | .omegaPlus => m + 1
  | .omegaMinus => m + 1

theorem card_eq_kindOrder {S : Type} [Group S] {m f : ℕ} {κ : Sp2mKind}
    (h : Sp2mKindType S m f κ) : KindAdmissible m f κ ∧ Nat.card S = kindOrder m f κ := by
  cases κ
  · obtain ⟨-, hf, hm, -⟩ := F4Pilot.statedLieAdmissible_of_lieModel h
    exact ⟨⟨hm, by omega⟩, F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) h⟩
  · exact h.elim
  · obtain ⟨-, hf, hm, -⟩ := F4Pilot.statedLieAdmissible_of_lieModel h
    exact ⟨⟨by omega, hf⟩, F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) h⟩
  · obtain ⟨-, hf, hm, -⟩ := F4Pilot.statedLieAdmissible_of_lieModel h
    exact ⟨⟨by omega, hf⟩, F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) h⟩
  · obtain ⟨-, hf, hm, -⟩ := F4Pilot.statedLieAdmissible_of_lieModel h
    exact ⟨⟨by omega, hf⟩, F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) h⟩
  · obtain ⟨-, hf, hm, -⟩ := F4Pilot.statedLieAdmissible_of_lieModel h
    exact ⟨⟨by omega, hf⟩, F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) h⟩
  · obtain ⟨-, hf, hm⟩ := F4Pilot.statedLieAdmissible_of_lieModel h
    exact ⟨⟨by omega, hf⟩, F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) h⟩
  · obtain ⟨-, hf, hm⟩ := F4Pilot.statedLieAdmissible_of_lieModel h
    exact ⟨⟨by omega, hf⟩, F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) h⟩

theorem tri_two_mul_sub_one {m : ℕ} (hm : 1 ≤ m) :
    (2 * m - 1) * (2 * m - 1 + 1) / 2 = m * (2 * m - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [h]
  exact Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)

theorem tri_two_mul (m : ℕ) : 2 * m * (2 * m + 1) / 2 = m * (2 * m + 1) :=
  Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)

theorem exists_profile_kindOrder {m f : ℕ} {κ : Sp2mKind} (hadm : KindAdmissible m f κ) :
    ∃ Z : ℕ → Prop, Profile (kindOrder m f κ) (f * (m * kindTwoLin m κ)) Z := by
  cases κ
  · obtain ⟨hm, hf⟩ := hadm
    have h := profile_ordBC (n := m) (f := 2 * f) (by omega)
    have he : 2 * f * (m * m) = f * (m * (2 * m)) := by ring
    rw [he] at h
    exact ⟨_, h⟩
  · exact hadm.elim
  · obtain ⟨hm, hf⟩ := hadm
    have h := profile_ordA (n := 2 * m - 1) (by omega) hf
    rw [tri_two_mul_sub_one hm] at h
    exact ⟨_, h⟩
  · obtain ⟨hm, hf⟩ := hadm
    have h := profile_ordTwistedA (n := 2 * m - 1) (by omega) hf
    rw [tri_two_mul_sub_one (by omega)] at h
    exact ⟨_, h⟩
  · obtain ⟨hm, hf⟩ := hadm
    have h := profile_ordA (n := 2 * m) (by omega) hf
    rw [tri_two_mul m] at h
    exact ⟨_, h⟩
  · obtain ⟨hm, hf⟩ := hadm
    have h := profile_ordTwistedA (n := 2 * m) (by omega) hf
    rw [tri_two_mul m] at h
    exact ⟨_, h⟩
  · obtain ⟨hm, hf⟩ := hadm
    have h := profile_ordD (n := m + 1) (by omega) hf
    rw [Nat.add_sub_cancel, mul_comm (m + 1) m] at h
    exact ⟨_, h⟩
  · obtain ⟨hm, hf⟩ := hadm
    have h := profile_ordTwistedD (n := m + 1) (by omega) hf
    rw [Nat.add_sub_cancel, mul_comm (m + 1) m] at h
    exact ⟨_, h⟩

theorem kindOrder_injective {m f : ℕ} {κ κ' : Sp2mKind} (hκ : KindAdmissible m f κ)
    (hκ' : KindAdmissible m f κ') (h : kindOrder m f κ = kindOrder m f κ') : κ = κ' := by
  obtain ⟨Z, hZ⟩ := exists_profile_kindOrder hκ
  obtain ⟨Z', hZ'⟩ := exists_profile_kindOrder hκ'
  rw [h] at hZ
  obtain ⟨r, hr, hr'⟩ := hZ.two
  obtain ⟨r', hr2, hr2'⟩ := hZ'.two
  have hN := eq_of_two_pow_mul_odd hr hr2 (hr'.symm.trans hr2')
  have hfm : 1 ≤ m ∧ 1 ≤ f := by
    cases κ <;> simp only [KindAdmissible] at hκ <;> omega
  have hlin : kindTwoLin m κ = kindTwoLin m κ' :=
    Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) (Nat.eq_of_mul_eq_mul_left (by omega) hN)
  obtain ⟨hm, hf⟩ := hfm
  cases κ <;> cases κ' <;> simp only [kindTwoLin] at hlin <;>
    simp only [KindAdmissible] at hκ hκ' <;>
    simp only [kindOrder, F4Pilot.evenLieOrder] at h <;> first
    | rfl
    | omega
    | exact absurd h (ordA_ne_ordTwistedA (by omega) hf (by omega) hf)
    | exact absurd h.symm (ordA_ne_ordTwistedA (by omega) hf (by omega) hf)
    | exact absurd h (OmegaPilot.ordTwistedD_ne_ordD (by omega) hf (by omega) hf).symm
    | exact absurd h (OmegaPilot.ordTwistedD_ne_ordD (by omega) hf (by omega) hf)

theorem eq_of_sp2mKindType {S : Type} [Group S] {m f : ℕ} {κ κ' : Sp2mKind}
    (h : Sp2mKindType S m f κ) (h' : Sp2mKindType S m f κ') : κ = κ' := by
  obtain ⟨hadm, hc⟩ := card_eq_kindOrder h
  obtain ⟨hadm', hc'⟩ := card_eq_kindOrder h'
  exact kindOrder_injective hadm hadm' (hc.symm.trans hc')

section Components

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem map_conj_map_conj_of_sq_eq_one {s : Y} (hs : s ^ 2 = 1) (A : Subgroup Y) :
    (A.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s).toMonoidHom = A := by
  have hs' : s * s = 1 := by rw [← sq]; exact hs
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs'
  have h : (MulAut.conj s).toMonoidHom.comp (MulAut.conj s).toMonoidHom = MonoidHom.id Y := by
    ext x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply, hsi]
    rw [show s * (s * x * s) * s = (s * s) * x * (s * s) by group, hs', one_mul, mul_one]
  rw [Subgroup.map_map, h, Subgroup.map_id]

theorem eq_or_eq_map_conj_of_le_sup {s : Y} (hs : s ^ 2 = 1) {D : Subgroup Y}
    (hDperf : ⁅D, D⁆ = D) (hD1 : D ≠ ⊥) {Kc Kc' : Subgroup Y} (hK : IsComponent Kc)
    (hK' : IsComponent Kc') (hDK : D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom)
    (hDK' : D ≤ Kc' ⊔ Kc'.map (MulAut.conj s).toMonoidHom) :
    Kc' = Kc ∨ Kc' = Kc.map (MulAut.conj s).toMonoidHom := by
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  have hKs : IsComponent (Kc.map (MulAut.conj s).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hK
  have hK's : IsComponent (Kc'.map (MulAut.conj s).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hK'
  have h3 : Kc'.map (MulAut.conj s).toMonoidHom ≠ Kc := fun h => by
    apply h2
    rw [← h, map_conj_map_conj_of_sq_eq_one hs]
  have h4 : Kc'.map (MulAut.conj s).toMonoidHom ≠ Kc.map (MulAut.conj s).toMonoidHom := fun h =>
    h1 (map_injective (MulAut.conj s).injective h)
  have hc : ∀ A : Subgroup Y, IsComponent A → A ≠ Kc → A ≠ Kc.map (MulAut.conj s).toMonoidHom →
      A ≤ centralizer (D : Set Y) := by
    intro A hA hA1 hA2
    have hc1 := (CFSG.LocalCores.distinct_components_commute hA hK).resolve_left hA1
    have hc2 := (CFSG.LocalCores.distinct_components_commute hA hKs).resolve_left hA2
    have hle : Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ≤ centralizer (A : Set Y) :=
      sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc1))
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc2))
    exact le_centralizer_iff.mp (hDK.trans hle)
  have hA1 := hc Kc' hK' h1 h2
  have hA2 := hc (Kc'.map (MulAut.conj s).toMonoidHom) hK's h3 h4
  have hDc : D ≤ centralizer (D : Set Y) := hDK'.trans (sup_le hA1 hA2)
  apply hD1
  rw [← hDperf]
  exact commutator_eq_bot_iff_le_centralizer.mpr hDc

theorem NeighbourOvergroupSp2mKind.unique {s : Y} (hs : s ^ 2 = 1) {D : Subgroup Y}
    (hDperf : ⁅D, D⁆ = D) (hD1 : D ≠ ⊥) {m f : ℕ} {κ κ' : Sp2mKind}
    (h : NeighbourOvergroupSp2mKind s D m f κ) (h' : NeighbourOvergroupSp2mKind s D m f κ') :
    κ = κ' := by
  obtain ⟨Kc, hKc, hDK, h1 | h2⟩ := h <;> obtain ⟨Kc', hKc', hDK', h1' | h2'⟩ := h'
  · obtain ⟨-, hKt, -, -, -, -, hty⟩ := h1
    obtain ⟨-, -, -, -, -, -, hty'⟩ := h1'
    have hKK : Kc' = Kc := by
      rcases eq_or_eq_map_conj_of_le_sup hs hDperf hD1 hKc hKc' hDK hDK' with h | h
      · exact h
      · exact h.trans hKt
    subst hKK
    exact eq_of_sp2mKindType hty hty'
  · obtain ⟨-, hKt, -⟩ := h1
    obtain ⟨-, hKt', -⟩ := h2'
    exfalso
    rcases eq_or_eq_map_conj_of_le_sup hs hDperf hD1 hKc hKc' hDK hDK' with h | h
    · exact hKt' (h ▸ hKt)
    · exact hKt' (by rw [h, hKt, hKt])
  · obtain ⟨-, hKt, -⟩ := h2
    obtain ⟨-, hKt', -⟩ := h1'
    exfalso
    rcases eq_or_eq_map_conj_of_le_sup hs hDperf hD1 hKc hKc' hDK hDK' with h | h
    · exact hKt (h ▸ hKt')
    · apply hKt
      have e1 : Kc'.map (MulAut.conj s).toMonoidHom = Kc := by
        rw [h, map_conj_map_conj_of_sq_eq_one hs]
      rw [← h]
      exact (e1.symm.trans hKt').symm
  · rw [h2.1, h2'.1]

end Components

section Root

theorem commutator_eq_self_of_isQuasisimple {Y : Type*} [Group Y] {D : Subgroup Y}
    (h : CFSG.Open.IsQuasisimple D) : ⁅D, D⁆ = D := by
  have h1 : commutator D = ⊤ := h.1
  have hD : (⊤ : Subgroup D).map D.subtype = D := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  calc ⁅D, D⁆ = ⁅(⊤ : Subgroup D).map D.subtype, (⊤ : Subgroup D).map D.subtype⁆ := by rw [hD]
    _ = (commutator D).map D.subtype := by rw [commutator_def, map_commutator]
    _ = D := by rw [h1, hD]

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem eq_of_rootKindSp {n f : ℕ} (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hn : 3 ≤ n) (e : L ≃* StatedSp n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {k l : Fin n} {κ κ' : Sp2mKind}
    (h : RootKindSp e t f k κ) (h' : RootKindSp e t f l κ') : κ = κ' := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  rw [rootKindSp_iff e htC f l k] at h'
  obtain ⟨htX, hK⟩ := h
  obtain ⟨htX', hK'⟩ := h'
  obtain ⟨htX'', hcomp, -⟩ := neighbour_rootTorusSp_of_three_le hset hq hn e htC ht k
    (X := modelToG e (rootTorusSp K k)) rfl (D := modelToG e (complSp K k)) rfl
  have h2 : (⟨t, htX⟩ : centralizer (modelToG e (rootTorusSp K k) : Set G)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← ht]
    exact pow_orderOf_eq_one t
  have hs : (QuotientGroup.mk' (oddCore (centralizer (modelToG e (rootTorusSp K k) : Set G)))
      ⟨t, htX⟩) ^ 2 = 1 := by
    rw [← map_pow, h2, map_one]
  exact NeighbourOvergroupSp2mKind.unique hs (commutator_eq_self_of_isQuasisimple hcomp.2.2)
    (ne_bot_of_isQuasisimple hcomp.2.2) hK hK'

theorem existsUnique_rootKindSp {n f : ℕ} (hcat : Sp2mCatalogueClausesAt (n - 1))
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hn : 3 ≤ n)
    (e : L ≃* StatedSp n K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∃! κ : Sp2mKind, ∀ k : Fin n, RootKindSp e t f k κ := by
  obtain ⟨κ, hκ⟩ := exists_rootKindSp hcat hset hKc hf hn e htC ht ⟨0, by omega⟩
  exact ⟨κ, fun k => (rootKindSp_iff e htC f _ k κ).1 hκ, fun κ' hκ' =>
    eq_of_rootKindSp hset hKc hf hn e htC ht (hκ' ⟨0, by omega⟩) hκ⟩

end Root

end CFSG.SeitzReduction.SymplecticPilot
