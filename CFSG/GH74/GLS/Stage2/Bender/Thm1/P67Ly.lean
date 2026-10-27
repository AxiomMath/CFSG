module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67FamSpor

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def LyAllInner : Prop :=
  ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .Ly →
    ∀ φ : MulAut Y, ∃ g : Y, φ = MulAut.conj g

@[expose] def LyCentralizerCore : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], NativeSporadic.IsSporadic Y .Ly →
    ∀ (r : ℕ), r.Prime → Odd r →
      ∀ V : Subgroup Y, IsElementaryAbelian r ↥V → Nat.card ↥V = r ^ 2 →
        ∃ g ∈ V, g ≠ 1 ∧
          ∀ W : Subgroup Y, W ≤ Subgroup.centralizer ({g} : Set Y) →
            (∀ c : Y, c * g = g * c → ∀ w ∈ W, c * w * c⁻¹ ∈ W) →
              Nat.Coprime (Nat.card ↥W) r → W = ⊥

@[expose] def LyMultTrivial : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J →
    NativeSporadic.IsSporadic (J ⧸ Subgroup.center J) .Ly → Subsingleton ↥(Subgroup.center J)

theorem cf67Ly_of_atlas (hA : LyAllInner) (hB : LyCentralizerCore) (hC : LyMultTrivial) :
    CF67Ly := by
  refine cf67Fam_of_core ?_ ?_
  · intro Y _ _ hLy hs hn r V Z h2 h3
    obtain ⟨a₀, b₀, hab₀⟩ := hn
    have hcen : Subgroup.center Y = ⊥ := by
      rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
      · exact h
      · exfalso
        apply hab₀
        have ha : a₀ ∈ Subgroup.center Y := h ▸ Subgroup.mem_top a₀
        exact (Subgroup.mem_center_iff.mp ha b₀).symm
    have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
      mulAut_conj_injective_of_center_bot hcen
    have hsurj : Function.Surjective (MulAut.conj : Y →* MulAut Y) := fun φ =>
      (hA Y hLy φ).imp fun g hg => hg.symm
    obtain ⟨hr, hr2, hVe, hVc, -, -, hZcop, hZbot, hcomm⟩ := h2
    have : Fact r.Prime := ⟨hr⟩
    have := hVe
    obtain ⟨e, he⟩ : ∃ e : Y ≃* MulAut Y, ∀ x : Y, e x = MulAut.conj x :=
      ⟨MulEquiv.ofBijective (MulAut.conj : Y →* MulAut Y) ⟨hinj, hsurj⟩, fun _ => rfl⟩
    have hV₀e : IsElementaryAbelian r ↥(V.map e.symm.toMonoidHom) :=
      IsElementaryAbelian.map e.symm.toMonoidHom
    have hV₀c : Nat.card ↥(V.map e.symm.toMonoidHom) = r ^ 2 :=
      (Subgroup.card_map_of_injective e.symm.injective).trans hVc
    obtain ⟨g, hgV₀, hg1, hW⟩ := hB Y hLy r hr hr2 _ hV₀e hV₀c
    have hvV : MulAut.conj g ∈ V := by
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgV₀
      have : MulAut.conj g = x := by
        rw [← he, ← hxg]
        exact e.apply_symm_apply x
      rw [this]
      exact hx
    have hv1 : MulAut.conj g ≠ 1 := fun h => hg1 (hinj (by rw [h, map_one]))
    have hfix : ∀ c : Y, c ∈ fixSub (MulAut.conj g) ↔ c * g = g * c := by
      intro c
      rw [mem_fixSub, MulAut.conj_apply]
      exact ⟨fun h => (mul_inv_eq_iff_eq_mul.mp h).symm, fun h => mul_inv_eq_iff_eq_mul.mpr h.symm⟩
    set W : Subgroup Y := Z.comap (MulAut.conj : Y →* MulAut Y)
    have hWmem : ∀ w : Y, w ∈ W ↔ MulAut.conj w ∈ Z := fun w => Iff.rfl
    have hWmap : W.map (MulAut.conj : Y →* MulAut Y) = Z :=
      Subgroup.map_comap_eq_self_of_surjective hsurj Z
    have hWcard : Nat.card ↥W = Nat.card ↥Z := by
      have := Subgroup.card_map_of_injective (K := W) hinj
      rw [hWmap] at this
      exact this.symm
    have hWle : W ≤ Subgroup.centralizer ({g} : Set Y) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have h1 := hcomm _ hvV _ ((hWmem w).mp hw)
      apply hinj
      rw [map_mul, map_mul]
      exact h1
    have hWnorm : ∀ c : Y, c * g = g * c → ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
      intro c hc w hw
      have hn := h3 _ hvV hv1 c ((hfix c).mpr hc)
      have h1 := (Subgroup.mem_normalizer_iff.mp hn (MulAut.conj w)).mp ((hWmem w).mp hw)
      rw [hWmem, map_mul, map_mul, map_inv]
      exact h1
    have hWcop : Nat.Coprime (Nat.card ↥W) r := hWcard ▸ hZcop
    have hWbot : W = ⊥ := hW W hWle hWnorm hWcop
    apply hZbot
    rw [← hWmap, hWbot, Subgroup.map_bot]
  · intro J _ _ hJ hLy r hr _ hdvd
    exfalso
    have hsub := hC J hJ hLy
    have hcard : Nat.card ↥(Subgroup.center J) = 1 := Nat.card_of_subsingleton 1
    rw [hcard] at hdvd
    exact hr.one_lt.ne' (Nat.dvd_one.mp hdvd)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
