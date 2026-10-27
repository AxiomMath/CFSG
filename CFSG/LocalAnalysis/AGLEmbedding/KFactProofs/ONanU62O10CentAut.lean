module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.AGLEmbedding.U62O10Cent

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def CentAlt {L : Type} [Group L] (x : L) : Prop :=
  (∃ D : Subgroup L, D ≤ Subgroup.centralizer ({x} : Set L) ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D) ∨
    Nat.card (Subgroup.centralizer ({MulAut.conj x} : Set (MulAut L))) ∣ 2 ^ 7 * 3 ^ 7

theorem centAlt_map {L L' : Type} [Group L] [Group L'] (e : L ≃* L') {x : L} (h : CentAlt x) :
    CentAlt (e x) := by
  rcases h with ⟨D, hDc, hDp, hD3⟩ | h
  · refine Or.inl ⟨D.map e.toMonoidHom, ?_, ?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hDc hd)
      rw [Subgroup.mem_centralizer_singleton_iff]
      change e d * e x = e x * e d
      rw [← map_mul, ← map_mul, h1]
    · rw [← Subgroup.map_commutator, hDp]
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hD3
  · refine Or.inr ?_
    have hcard : Nat.card (Subgroup.centralizer ({MulAut.conj (e x)} : Set (MulAut L'))) =
        Nat.card (Subgroup.centralizer ({MulAut.conj x} : Set (MulAut L))) := by
      refine (Nat.card_congr ((MulAut.congr e).toEquiv.subtypeEquiv fun s => ?_)).symm
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
        ← congr_conj e x]
      change _ ↔ MulAut.congr e s * MulAut.congr e (MulAut.conj x) =
        MulAut.congr e (MulAut.conj x) * MulAut.congr e s
      rw [← map_mul, ← map_mul]
      exact ⟨fun h => by rw [h], fun h => (MulAut.congr e).injective h⟩
    rw [hcard]
    exact h

theorem conj_injective_of_center_eq_bot {T : Type} [Group T] (hc : Subgroup.center T = ⊥) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxc : x ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun f : MulAut T => f z) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * x = (x * z * x⁻¹) * x := by rw [this]
      _ = x * z := by group
  rw [hc] at hxc
  exact hxc

theorem card_centralizer_conj_dvd {L : Type} [Group L] [Finite L]
    (hc : Subgroup.center L = ⊥) (x : L) :
    Nat.card (Subgroup.centralizer ({MulAut.conj x} : Set (MulAut L))) ∣
      Nat.card (Subgroup.centralizer ({x} : Set L)) * Nat.card (Outer L) := by
  classical
  have hfin : Finite (MulAut L) :=
    Finite.of_injective (fun α : MulAut L => (α : L → L)) fun _ _ h => MulEquiv.ext (congrFun h)
  set S := Subgroup.centralizer ({MulAut.conj x} : Set (MulAut L)) with hS
  let φ : S →* Outer L := (QuotientGroup.mk' (inner L)).comp S.subtype
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.range ∣ Nat.card (Outer L) := Subgroup.card_subgroup_dvd_card φ.range
  have hinj := conj_injective_of_center_eq_bot hc
  have h3 : Nat.card φ.ker = Nat.card (Subgroup.centralizer ({x} : Set L)) := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun g : Subgroup.centralizer ({x} : Set L) =>
        (⟨⟨MulAut.conj (g : L), ?_⟩, ?_⟩ : φ.ker)) ⟨?_, ?_⟩)).symm
    · rw [hS, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.1 g.2]
    · rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk' (inner L)) (MulAut.conj (g : L)) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨g, rfl⟩
    · intro g g' hgg
      apply Subtype.ext
      apply hinj
      exact congrArg (fun t : φ.ker => (t.1 : MulAut L)) hgg
    · rintro ⟨⟨s, hsS⟩, hsk⟩
      rw [MonoidHom.mem_ker] at hsk
      change (QuotientGroup.mk' (inner L)) s = 1 at hsk
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hsk
      obtain ⟨g, rfl⟩ := hsk
      have hsS' := Subgroup.mem_centralizer_singleton_iff.1 hsS
      refine ⟨⟨g, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
      rw [← map_mul, ← map_mul] at hsS'
      exact hinj hsS'
  rw [← h1, h3]
  exact mul_dvd_mul_left _ h2

theorem centAlt_of_dvd {L : Type} [Group L] [Finite L] (hc : Subgroup.center L = ⊥) (x : L)
    {n m : ℕ} (hn : Nat.card (Subgroup.centralizer ({x} : Set L)) ∣ n)
    (hm : Nat.card (Outer L) ∣ m) (hnm : n * m ∣ 2 ^ 7 * 3 ^ 7) : CentAlt x :=
  Or.inr ((card_centralizer_conj_dvd hc x).trans ((mul_dvd_mul hn hm).trans hnm))

end CFSG.AGLEmbedding.U62O10Cent
