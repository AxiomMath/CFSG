module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section Setting

variable {G : Type} [Group G] [Finite G]
variable {m p : ℕ} {M D L : Subgroup G}

theorem map_pCoreOf_subgroupOf (hLM : L ≤ M) :
    (pCoreOf 2 (L.subgroupOf M)).map M.subtype = pCoreOf 2 L := by
  have he : (CFSG.pCore 2 ↥(L.subgroupOf M)).map (Subgroup.subgroupOfEquivOfLe hLM).toMonoidHom
      = CFSG.pCore 2 ↥L := CFSG.pCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hLM)
  unfold pCoreOf
  rw [Subgroup.map_map, ← he, Subgroup.map_map]
  rfl

private theorem blk_chief_le {V U : Subgroup G} (h : IsChiefFactorOf L V U) : V ≤ U := by
  unfold IsChiefFactorOf at h
  exact h.1.le

private theorem blk_subgroupOf_le_iff {A B : Subgroup G} (hA : A ≤ M) :
    A.subgroupOf M ≤ B.subgroupOf M ↔ A ≤ B := by
  refine ⟨fun h x hx => ?_, fun h => Subgroup.subgroupOf_mono M h⟩
  have hxM : (⟨x, hA hx⟩ : ↥M) ∈ A.subgroupOf M := Subgroup.mem_subgroupOf.2 hx
  exact Subgroup.mem_subgroupOf.1 (h hxM)

private theorem blk_subgroupOf_lt {V U : Subgroup G} (hVM : V ≤ M) (hUM : U ≤ M) (hVU : V < U) :
    V.subgroupOf M < U.subgroupOf M := by
  refine lt_of_le_of_ne ((blk_subgroupOf_le_iff hVM).2 hVU.le) fun h => hVU.ne ?_
  exact le_antisymm hVU.le ((blk_subgroupOf_le_iff hUM).1 h.ge)

private theorem blk_map_subgroupOf_self (X : Subgroup ↥M) :
    (X.map M.subtype).subgroupOf M = X :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective X

private theorem blk_mem_pCoreOf_iff (hLM : L ≤ M) (x : ↥M) :
    x ∈ pCoreOf 2 (L.subgroupOf M) ↔ (x : G) ∈ pCoreOf 2 L := by
  rw [← map_pCoreOf_subgroupOf hLM]
  exact (Subgroup.mem_map_iff_mem M.subtype_injective).symm

private theorem blk_commutator_iff {U V : Subgroup G} (hUM : U ≤ M) (hLM : L ≤ M) :
    ⁅U.subgroupOf M, L.subgroupOf M⁆ ≤ V.subgroupOf M ↔ ⁅U, L⁆ ≤ V := by
  have hmap : (⁅U.subgroupOf M, L.subgroupOf M⁆ : Subgroup ↥M).map M.subtype = ⁅U, L⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUM,
      Subgroup.map_subgroupOf_eq_of_le hLM]
  rw [← hmap, Subgroup.map_le_iff_le_comap, Subgroup.comap_subtype]

private theorem blk_normalizer_iff {K : Subgroup G} (hKM : K ≤ M) (Y : Subgroup ↥M) :
    K.subgroupOf M ≤ Subgroup.normalizer (Y : Set ↥M) ↔
      K ≤ Subgroup.normalizer ((Y.map M.subtype : Subgroup G) : Set G) := by
  have hYle : Y.map M.subtype ≤ M.subtype.range := by
    rw [Subgroup.range_subtype]
    exact Subgroup.map_subtype_le Y
  have key : Subgroup.normalizer (Y : Set ↥M) =
      (Subgroup.normalizer ((Y.map M.subtype : Subgroup G) : Set G)).comap M.subtype := by
    rw [Subgroup.comap_normalizer_eq_of_le_range hYle,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective Y]
  rw [key, ← Subgroup.map_le_iff_le_comap, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKM]

private theorem blk_isChiefFactorOf {V U : Subgroup G} (hLM : L ≤ M) (hVM : V ≤ M) (hUM : U ≤ M)
    (h : IsChiefFactorOf L V U) :
    IsChiefFactorOf (L.subgroupOf M) (V.subgroupOf M) (U.subgroupOf M) := by
  unfold IsChiefFactorOf at h ⊢
  obtain ⟨hVU, hLV, hLU, hmax⟩ := h
  refine ⟨blk_subgroupOf_lt hVM hUM hVU, ?_, ?_, ?_⟩
  · exact (blk_normalizer_iff hLM _).2 (by rw [Subgroup.map_subgroupOf_eq_of_le hVM]; exact hLV)
  · exact (blk_normalizer_iff hLM _).2 (by rw [Subgroup.map_subgroupOf_eq_of_le hUM]; exact hLU)
  · intro W' hVW hWU hLW
    have hVW' : V ≤ W'.map M.subtype := by
      have := Subgroup.map_mono (f := M.subtype) hVW
      rwa [Subgroup.map_subgroupOf_eq_of_le hVM] at this
    have hWU' : W'.map M.subtype ≤ U := by
      have := Subgroup.map_mono (f := M.subtype) hWU
      rwa [Subgroup.map_subgroupOf_eq_of_le hUM] at this
    have hLW' := (blk_normalizer_iff hLM W').1 hLW
    rcases hmax (W'.map M.subtype) hVW' hWU' hLW' with h1 | h1
    · left
      calc W' = (W'.map M.subtype).subgroupOf M := (blk_map_subgroupOf_self W').symm
        _ = V.subgroupOf M := by rw [h1]
    · right
      calc W' = (W'.map M.subtype).subgroupOf M := (blk_map_subgroupOf_self W').symm
        _ = U.subgroupOf M := by rw [h1]

private theorem blk_chiefSeries_le (hLM : L ≤ M) {n : ℕ} {S : Fin (n + 1) → Subgroup G}
    (hS : IsChiefSeriesIn L (pCoreOf 2 L) S) (j : Fin (n + 1)) : S j ≤ M := by
  unfold IsChiefSeriesIn at hS
  have hmono : Monotone S := Fin.monotone_iff_le_succ.2 fun i => blk_chief_le (hS.2.2 i)
  have hlast : S (Fin.last n) ≤ M := by
    rw [hS.2.1]
    exact (CFSG.openPCoreOf_le 2 L).trans hLM
  exact (hmono (Fin.le_last j)).trans hlast

private theorem blk_chiefSeries_subgroupOf (hLM : L ≤ M) {n : ℕ} {S : Fin (n + 1) → Subgroup G}
    (hS : IsChiefSeriesIn L (pCoreOf 2 L) S) :
    IsChiefSeriesIn (L.subgroupOf M) (pCoreOf 2 (L.subgroupOf M))
      (fun j => (S j).subgroupOf M) := by
  have hS' := hS
  unfold IsChiefSeriesIn at hS' ⊢
  refine ⟨?_, ?_, fun i => blk_isChiefFactorOf hLM (blk_chiefSeries_le hLM hS i.castSucc)
    (blk_chiefSeries_le hLM hS i.succ) (hS'.2.2 i)⟩
  · show (S 0).subgroupOf M = ⊥
    rw [hS'.1, Subgroup.bot_subgroupOf]
  · show (S (Fin.last n)).subgroupOf M = pCoreOf 2 (L.subgroupOf M)
    rw [hS'.2.1, ← map_pCoreOf_subgroupOf hLM, blk_map_subgroupOf_self]

theorem glBlock_residual_of_subgroupOf (hLM : L ≤ M)
    (h : ∀ (N : Subgroup ↥(L.subgroupOf M)) [N.Normal], IsPGroup 2 (↥(L.subgroupOf M) ⧸ N) → N = ⊤) :
    ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤ := by
  intro N hN hq
  let e : ↥(L.subgroupOf M) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLM
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have hmap : (N.comap e.toMonoidHom).map e.toMonoidHom = N :=
    Subgroup.map_comap_eq_self_of_surjective hsurj N
  have hiso : (↥(L.subgroupOf M) ⧸ N.comap e.toMonoidHom) ≃* (↥L ⧸ N) :=
    QuotientGroup.congr (N.comap e.toMonoidHom) N e hmap
  have htop : N.comap e.toMonoidHom = ⊤ := by
    apply h
    exact hq.of_equiv hiso.symm
  rw [eq_top_iff]
  intro x _
  have hx : e.symm x ∈ N.comap e.toMonoidHom := by
    rw [htop]
    exact Subgroup.mem_top _
  simpa using hx

theorem glBlock_simple_of_subgroupOf (hLM : L ≤ M)
    (h : IsSimpleGroup (↥(L.subgroupOf M) ⧸ CFSG.pCore 2 ↥(L.subgroupOf M))) :
    IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  haveI := h
  let e : ↥(L.subgroupOf M) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLM
  have hmap : (CFSG.pCore 2 ↥(L.subgroupOf M)).map e.toMonoidHom = CFSG.pCore 2 ↥L :=
    CFSG.pCore_map_iso 2 e
  exact (QuotientGroup.congr (CFSG.pCore 2 ↥(L.subgroupOf M)) (CFSG.pCore 2 ↥L) e hmap).symm.isSimpleGroup

theorem glBlock_commutator_of_subgroupOf (hLM : L ≤ M)
    (h : ∀ x ∈ ⁅L.subgroupOf M, pCoreOf 2 (L.subgroupOf M)⁆,
      x ∈ pCoreOf 2 (L.subgroupOf M) ∧ x ^ 2 = 1 ∧ ∀ r ∈ pCoreOf 2 (L.subgroupOf M), x * r = r * x) :
    ∀ x ∈ ⁅L, pCoreOf 2 L⁆, x ∈ pCoreOf 2 L ∧ x ^ 2 = 1 ∧ ∀ r ∈ pCoreOf 2 L, x * r = r * x := by
  intro x hx
  have hmap : (⁅L.subgroupOf M, pCoreOf 2 (L.subgroupOf M)⁆ : Subgroup ↥M).map M.subtype
      = ⁅L, pCoreOf 2 L⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLM,
      map_pCoreOf_subgroupOf hLM]
  rw [← hmap] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨h1, h2, h3⟩ := h y hy
  refine ⟨(blk_mem_pCoreOf_iff hLM y).1 h1, ?_, ?_⟩
  · have := congrArg Subtype.val h2
    simpa using this
  · intro r hr
    rw [← map_pCoreOf_subgroupOf hLM] at hr
    obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.1 hr
    have := congrArg Subtype.val (h3 r' hr')
    simpa using this

theorem glBlock_unique_noncentral_of_subgroupOf (hLM : L ≤ M)
    (h : ∀ (n : ℕ) (S : Fin (n + 1) → Subgroup ↥M),
      IsChiefSeriesIn (L.subgroupOf M) (pCoreOf 2 (L.subgroupOf M)) S →
        ∃! i : Fin n, ¬ ⁅S i.succ, L.subgroupOf M⁆ ≤ S i.castSucc) :
    ∀ (n : ℕ) (S : Fin (n + 1) → Subgroup G), IsChiefSeriesIn L (pCoreOf 2 L) S →
      ∃! i : Fin n, ¬ ⁅S i.succ, L⁆ ≤ S i.castSucc := by
  intro n S hS
  have hSM := blk_chiefSeries_le hLM hS
  obtain ⟨i, hi, hu⟩ := h n (fun j => (S j).subgroupOf M) (blk_chiefSeries_subgroupOf hLM hS)
  have key : ∀ j : Fin n,
      (¬ ⁅(S j.succ).subgroupOf M, L.subgroupOf M⁆ ≤ (S j.castSucc).subgroupOf M ↔
        ¬ ⁅S j.succ, L⁆ ≤ S j.castSucc) := fun j =>
    not_congr (blk_commutator_iff (hSM _) hLM)
  exact ⟨i, (key i).1 hi, fun j hj => hu j ((key j).2 hj)⟩

theorem isNoncentralChiefFactor_subgroupOf (hLM : L ≤ M) {V U : Subgroup G}
    (h : IsNoncentralChiefFactor L (pCoreOf 2 L) V U) :
    IsNoncentralChiefFactor (L.subgroupOf M) (pCoreOf 2 (L.subgroupOf M)) (V.subgroupOf M)
      (U.subgroupOf M) := by
  unfold IsNoncentralChiefFactor at h ⊢
  obtain ⟨hch, hUR, hnc⟩ := h
  have hUL : U ≤ L := hUR.trans (CFSG.openPCoreOf_le 2 L)
  have hUM : U ≤ M := hUL.trans hLM
  have hVM : V ≤ M := (blk_chief_le hch).trans hUM
  refine ⟨blk_isChiefFactorOf hLM hVM hUM hch, fun x hx => ?_, ?_⟩
  · exact (blk_mem_pCoreOf_iff hLM x).2 (hUR (Subgroup.mem_subgroupOf.1 hx))
  · rw [blk_commutator_iff hUM hLM]
    exact hnc

private theorem blk_chiefFactorIso_of_le {A N : Type*} [Group A] [AddCommGroup N] (hLM : L ≤ M)
    (V U : Subgroup G) (hUM : U ≤ M) (ρ : ↥(L.subgroupOf M) →* A) (a : A → N → N)
    (h : ChiefFactorIso (L.subgroupOf M) (U.subgroupOf M) (V.subgroupOf M) ρ a) :
    ChiefFactorIso L U V (ρ.comp (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom) a := by
  unfold ChiefFactorIso at h ⊢
  obtain ⟨φ, hsurj, hker, hequiv⟩ := h
  let f : ↥U ≃* ↥(U.subgroupOf M) := (Subgroup.subgroupOfEquivOfLe hUM).symm
  refine ⟨φ.comp f.toMonoidHom, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨z', hz'⟩ := hsurj z
    refine ⟨Subgroup.subgroupOfEquivOfLe hUM z', ?_⟩
    show φ ((Subgroup.subgroupOfEquivOfLe hUM).symm (Subgroup.subgroupOfEquivOfLe hUM z')) = z
    rw [MulEquiv.symm_apply_apply]
    exact hz'
  · intro u
    exact hker (f u)
  · intro ℓ u u' huu'
    exact hequiv ((Subgroup.subgroupOfEquivOfLe hLM).symm ℓ) (f u) (f u') (Subtype.ext huu')

theorem chiefFactorIso_of_subgroupOf {A N : Type*} [Group A] [AddCommGroup N] (hLM : L ≤ M)
    (V U : Subgroup G) (hU : U ≤ M) (ρ : ↥(L.subgroupOf M) →* A) (a : A → N → N)
    (h : ChiefFactorIso (L.subgroupOf M) (U.subgroupOf M) (V.subgroupOf M) ρ a) :
    ChiefFactorIso L U V (ρ.comp (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom) a :=
  blk_chiefFactorIso_of_le hLM V U hU ρ a h

theorem toBar_comp_subgroupOfEquiv (hLM : L ≤ M) :
    (toBar (CFSG.pCore 2 ↥M) (L.subgroupOf M)).comp
        (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom = toTl M L hLM := by
  refine MonoidHom.ext fun ℓ => ?_
  apply Subtype.ext
  rfl

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
