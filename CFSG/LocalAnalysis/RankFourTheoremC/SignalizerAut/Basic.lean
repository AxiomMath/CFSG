module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigBase
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

@[expose] def SignalizerInnAt (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) → ∀ B Y : Subgroup K,
    IsElemAbelian p B → Nat.card B = p ^ 2 → p.Coprime (Nat.card Y) →
    B ≤ normalizer (Y : Set K) → B ≤ centralizer (Y : Set K)

theorem centralizes_of_inner {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hZ : center K = ⊥)
    (hK : ∀ B Y : Subgroup K, IsElemAbelian p B → Nat.card B = p ^ 2 →
      p.Coprime (Nat.card Y) → B ≤ normalizer (Y : Set K) → B ≤ centralizer (Y : Set K))
    {B Y : Subgroup (MulAut K)} (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hY : p.Coprime (Nat.card Y)) (hBY : B ≤ normalizer (Y : Set (MulAut K)))
    (hin : B ≤ (MulAut.conj : K →* MulAut K).range) :
    B ≤ centralizer (Y : Set (MulAut K)) := by
  set c : K →* MulAut K := MulAut.conj with hc
  haveI : c.range.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal K
  have hinj : Function.Injective c := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    have h : k * g * k⁻¹ = g := by
      simpa only [hc, MulAut.conj_apply, MulAut.one_apply] using congrArg (fun φ => φ g) hk
    calc g * k = k * g * k⁻¹ * k := by rw [h]
      _ = k * g := by group
  have hCY : ⁅Y, B⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hBY
  have hCin : ⁅Y, B⁆ ≤ c.range :=
    (Subgroup.commutator_mono le_top hin).trans (Subgroup.commutator_le_right ⊤ c.range)
  have hBC : B ≤ normalizer ((⁅Y, B⁆ : Subgroup (MulAut K)) : Set (MulAut K)) :=
    Subgroup.normalizer_commutator_ge_right Y B
  have hcard {H : Subgroup (MulAut K)} (hH : H ≤ c.range) : Nat.card (H.comap c) = Nat.card H := by
    have h := Subgroup.card_map_of_injective (K := H.comap c) hinj
    rw [Subgroup.map_comap_eq_self hH] at h
    exact h.symm
  have hcop : p.Coprime (Nat.card ((⁅Y, B⁆ : Subgroup (MulAut K)).comap c)) := by
    rw [hcard hCin]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hCY) hY
  have hnorm : B.comap c ≤ normalizer
      (((⁅Y, B⁆ : Subgroup (MulAut K)).comap c : Subgroup K) : Set K) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hBC hb) (c x)
  have hcent := hK _ _ (hB.comap hinj) ((hcard hin).trans hBc) hcop hnorm
  have hBCc : B ≤ centralizer ((⁅Y, B⁆ : Subgroup (MulAut K)) : Set (MulAut K)) := by
    intro β hβ
    obtain ⟨b, rfl⟩ := hin hβ
    rw [Subgroup.mem_centralizer_iff]
    intro γ hγ
    obtain ⟨x, rfl⟩ := hCin hγ
    have h := Subgroup.mem_centralizer_iff.mp (hcent (show b ∈ B.comap c from hβ)) x hγ
    rw [← map_mul, ← map_mul, h]
  have hBp : IsPGroup p B := fun b => ⟨1, by simpa using Subtype.ext (hB.2 b b.2)⟩
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp B Y hBp
    ((Nat.Prime.coprime_iff_not_dvd hp).1 hY) hBY
  have hbot : ⁅Y, B⁆ = ⊥ := by
    rw [← hidem, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hBCc
  rw [Subgroup.commutator_comm] at hbot
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot

theorem signalizerAutAt_of_signalizerInnAt {p : ℕ} (hp : p.Prime) {i : TauCeti.CFSGIndex}
    (hZ : ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) → center K = ⊥)
    (hout : ¬ GL83OuterType24 p i) (h : SignalizerInnAt p i) : SignalizerAutAt p i :=
  fun K _ _ e _ _ hB hBc hY hBY hin =>
    centralizes_of_inner hp (hZ K e) (h K e) hB hBc hY hBY (hin.resolve_right hout)

theorem center_eq_bot_of_mulEquiv {K X : Type*} [Group K] [Group X] (e : K ≃* X)
    (hX : center X = ⊥) : center K = ⊥ := by
  rw [eq_bot_iff]
  intro k hk
  have h : e k ∈ center X := Subgroup.mem_center_iff.mpr fun g => by
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hk g]
  rw [hX, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.mpr (e.injective (by rw [h, map_one]))

theorem signalizerInnAt_of_model_weakTI {p : ℕ} (hp : p.Prime) {i : TauCeti.CFSGIndex}
    {X : Type*} [Group X] [Finite X] (eX : X ≃* i.Group) {R : Subgroup X}
    (hR : Nat.card R = p ^ (Nat.card X).factorization p) (hTI : WeakTI R) :
    SignalizerInnAt p i := fun _ _ _ ⟨e⟩ _ _ hB hBc hY hBY =>
  centralizes_of_equiv_weakTI hp (eX.trans e.symm) hR hTI hB hBc
    ((Nat.Prime.coprime_iff_not_dvd hp).1 hY) hBY

theorem signalizerAutAt_of_model_weakTI {p : ℕ} (hp : p.Prime) {i : TauCeti.CFSGIndex}
    (hout : ¬ GL83OuterType24 p i) {X : Type*} [Group X] [Finite X] (eX : X ≃* i.Group)
    (hZ : center X = ⊥) {R : Subgroup X} (hR : Nat.card R = p ^ (Nat.card X).factorization p)
    (hTI : WeakTI R) : SignalizerAutAt p i :=
  signalizerAutAt_of_signalizerInnAt hp
    (fun _ _ _ ⟨e⟩ => center_eq_bot_of_mulEquiv (e.trans eX.symm) hZ) hout
    (signalizerInnAt_of_model_weakTI hp eX hR hTI)

end CFSG.LocalAnalysis.RankFourTheoremC
