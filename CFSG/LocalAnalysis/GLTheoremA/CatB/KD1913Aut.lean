module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.AutCore
public import CFSG.LocalAnalysis.GLTheoremA.CatB.MathieuAutData
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KD1913Holds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

theorem nonempty_equiv_m12 {S : Type} [Group S] (h : catalogIs S isM12) :
    Nonempty (S ≃* ↥CFSG.Blueprint.NativeSporadic.M12) := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | cyclic p hp => exact (hi : False).elim
  | alternating n hn => exact (hi : False).elim
  | lie j => exact (hi : False).elim
  | sporadic s =>
    have hs : s = TauCeti.SporadicName.M12 := hi
    subst hs
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
    exact ⟨f.trans b.symm⟩

theorem nonempty_equiv_m22 {S : Type} [Group S] (h : catalogIs S isM22) :
    Nonempty (S ≃* ↥CFSG.Blueprint.NativeSporadic.M22) := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | cyclic p hp => exact (hi : False).elim
  | alternating n hn => exact (hi : False).elim
  | lie j => exact (hi : False).elim
  | sporadic s =>
    have hs : s = TauCeti.SporadicName.M22 := hi
    subst hs
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    exact ⟨f.trans b.symm⟩

theorem m12_cent3
    (t : ↥CFSG.Blueprint.NativeSporadic.M12)
    (ht : orderOf t = 3) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M12)) = 36 ∨
      Nat.card ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M12)) = 54 := by
  have ho : orderOf (t : Equiv.Perm (Fin 12)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact ht
  obtain ⟨r, hr, hcard⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinM12.card_centralizerIn Nat.prime_three
      (by norm_num) t.2 ho
  have hc := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinM22.card_centralizer_subtype
    CFSG.Blueprint.NativeSporadic.M12 t
  have h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M12)) := by
    have hmem : t ∈ Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M12) :=
      Subgroup.mem_centralizer_singleton_iff.2 rfl
    have hd := orderOf_dvd_natCard
      (⟨t, hmem⟩ : ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M12)))
    rw [Subgroup.orderOf_mk, ht] at hd
    exact hd
  rw [hc.trans hcard] at h3 ⊢
  rcases CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinM12.rows_ord r hr with h | h | h | h <;>
    rw [h] at h3 ⊢ <;> omega

theorem m22_cent3
    (t : ↥CFSG.Blueprint.NativeSporadic.M22) (ht : orderOf t = 3) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M22)) = 36 := by
  have hx : (t : Equiv.Perm (Fin 22)) ∈ CFSG.Blueprint.NativeSporadic.M22 := t.2
  have hx3 : orderOf (t : Equiv.Perm (Fin 22)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact ht
  obtain ⟨c, hc, hcard⟩ := CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_sound
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data
    CFSG.HardMathSupport.Solomon.Coordinator.rep_m22A
    CFSG.HardMathSupport.Solomon.Coordinator.rep_m22B
    Certificates.certificate13511.2.2.1 (t : Equiv.Perm (Fin 22)) hx hx3
  have h36 : ∀ c < CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data.cases.size,
      CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data.cases[c]!.card = 36 := by
    decide +kernel
  have key : Nat.card ↥((Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M22)).map
      CFSG.Blueprint.NativeSporadic.M22.subtype) =
      Nat.card ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M22)) :=
    Subgroup.card_map_of_injective CFSG.Blueprint.NativeSporadic.M22.subtype_injective
  rw [← key, CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype]
  exact hcard.trans (h36 c hc)

theorem card_centralizerIn_eq {M : Type*} [Group M] (H : Subgroup M) (u : H) :
    Nat.card ↥(CFSG.Sporadic.Schreier.centralizerIn H (u : M)) =
      Nat.card ↥(Subgroup.centralizer ({u} : Set H)) := by
  rw [← CFSG.Sporadic.Schreier.map_centralizer_subtype H u,
    Subgroup.card_map_of_injective H.subtype_injective]

theorem m22_fixSub_card
    (w : MulAut ↥CFSG.Blueprint.NativeSporadic.M22) (hw : orderOf w = 2) :
    ¬ 9 ∣ Nat.card ↥(CFSG.Sporadic.Schreier.fixSub w) := by
  by_cases hin : w ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥CFSG.Blueprint.NativeSporadic.M22
  · refine fixSub_card_inner CFSG.Sporadic.Schreier.m22_center_eq_bot' (fun u hu => ?_) w hw hin
    rw [← card_centralizerIn_eq]
    exact m22_inner_card u.1 u.2 (by rw [Subgroup.orderOf_coe]; exact hu)
  · have hw2 : w * w = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one w
      rwa [hw] at this
    exact fixSub_card_outer CFSG.Blueprint.NativeSporadic.M22 CFSG.Sporadic.Schreier.m22Delta
      CFSG.Sporadic.Schreier.m22_delta_normalizes CFSG.Sporadic.Schreier.m22_delta_sq
      CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_delta_outer
      CFSG.Sporadic.Schreier.m22_mulAut_card m22_outer_card w hw2 hin

theorem m12_fixSub_card
    (w : MulAut ↥CFSG.Blueprint.NativeSporadic.M12) (hw : orderOf w = 2) :
    ¬ 9 ∣ Nat.card ↥(CFSG.Sporadic.Schreier.fixSub w) := by
  by_cases hin : w ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥CFSG.Blueprint.NativeSporadic.M12
  · refine fixSub_card_inner CFSG.Sporadic.Schreier.m12_center_eq_bot' (fun u hu => ?_) w hw hin
    rw [← card_centralizerIn_eq]
    exact m12_inner_card u.1 u.2 (by rw [Subgroup.orderOf_coe]; exact hu)
  · have hw2 : w * w = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one w
      rwa [hw] at this
    set e := CFSG.Sporadic.Schreier.m12EquivD with he
    have hw'2 : MulAut.congr e w * MulAut.congr e w = 1 := by
      rw [← map_mul, hw2, map_one]
    have hw'out : MulAut.congr e w ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥CFSG.Sporadic.Schreier.m12D.originalSubgroup := by
      intro h
      apply hin
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at h
      obtain ⟨β, hβ, hβα⟩ := h
      rwa [(MulAut.congr e).injective hβα] at hβ
    have key := fixSub_card_outer CFSG.Sporadic.Schreier.m12D.originalSubgroup
      CFSG.Sporadic.Schreier.m12Sigma CFSG.Sporadic.Schreier.m12D_sigma_normalizes
      CFSG.Sporadic.Schreier.m12D_sigma_sq CFSG.Sporadic.Schreier.m12D_center
      CFSG.Sporadic.Schreier.m12D_sigma_outer CFSG.Sporadic.Schreier.m12D_mulAut_card
      m12D_outer_card (MulAut.congr e w) hw'2 hw'out
    rwa [← CFSG.Sporadic.Schreier.map_fixSub_equiv e w,
      Subgroup.card_map_of_injective e.injective] at key

theorem core_of_equiv {S M : Type} [Group S] [Finite S] [Group M] (e : S ≃* M)
    (hZ : Subgroup.center M = ⊥) (hcard : Nat.card (MulAut M) ≤ 2 * Nat.card M)
    (hcent : ∀ t : M, orderOf t = 3 → Nat.card ↥(Subgroup.centralizer ({t} : Set M)) = 36 ∨
      Nat.card ↥(Subgroup.centralizer ({t} : Set M)) = 54)
    (hinvol : ∀ w : MulAut M, orderOf w = 2 → ¬ 9 ∣ Nat.card ↥(CFSG.Sporadic.Schreier.fixSub w))
    (H : Subgroup (MulAut S)) (hH : (MulAut.conj : S →* MulAut S).range ≤ H)
    (x : MulAut S) (hxH : x ∈ H) (hx : orderOf x = 3) :
    Nat.card (GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))) ≤ 4 := by
  refine core_card_le_four ?_ (CFSG.Sporadic.Schreier.mulAut_card_of_equiv e hcard) ?_ ?_ H hH x hxH hx
  · rw [eq_bot_iff]
    intro z hz
    have h1 := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e
    rw [hZ] at h1
    have h2 : e z ∈ (Subgroup.center S).map e.toMonoidHom := ⟨z, hz, rfl⟩
    rw [h1, Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot]
    exact e.injective (h2.trans (map_one e).symm)
  · intro s hs
    have h1 := CFSG.Sporadic.Schreier.map_centralizer_equiv e s
    have h2 : Nat.card ↥(Subgroup.centralizer ({s} : Set S)) =
        Nat.card ↥(Subgroup.centralizer ({e s} : Set M)) := by
      rw [← h1, Subgroup.card_map_of_injective e.injective]
    rw [h2]
    exact hcent (e s) (by rw [MulEquiv.orderOf_eq]; exact hs)
  · intro w hw
    have h1 := CFSG.Sporadic.Schreier.map_fixSub_equiv e w
    have h2 : Nat.card ↥(CFSG.Sporadic.Schreier.fixSub w) = Nat.card ↥(CFSG.Sporadic.Schreier.fixSub (MulAut.congr e w)) := by
      rw [← h1, Subgroup.card_map_of_injective e.injective]
    rw [h2]
    exact hinvol _ (by rw [MulEquiv.orderOf_eq]; exact hw)

section Holds


theorem kd1913MathieuAut_holds : KD1913MathieuAut := by
  intro S _ _ hS H hlt x hx hord
  have hH : (MulAut.conj : S →* MulAut S).range ≤ H := hlt.le
  rcases hS with h12 | h22
  · obtain ⟨e⟩ := nonempty_equiv_m12 h12
    exact core_of_equiv e CFSG.Sporadic.Schreier.m12_center_eq_bot'
      CFSG.Sporadic.Schreier.m12_mulAut_card (fun t ht => m12_cent3 t ht)
      (fun w hw => m12_fixSub_card w hw) H hH x hx hord
  · obtain ⟨e⟩ := nonempty_equiv_m22 h22
    exact core_of_equiv e CFSG.Sporadic.Schreier.m22_center_eq_bot'
      CFSG.Sporadic.Schreier.m22_mulAut_card (fun t ht => Or.inl (m22_cent3 t ht))
      (fun w hw => m22_fixSub_card w hw) H hH x hx hord

end Holds

end CFSG.LocalAnalysis.GLTheoremA.CatB
