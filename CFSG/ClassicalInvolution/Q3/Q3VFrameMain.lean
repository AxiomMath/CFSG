module

public import CFSG.ClassicalInvolution.Q3.Q3VFrameTrans
public import CFSG.ClassicalInvolution.Q3.Q3PBranch

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Frame

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane form
  isHyperbolicPlane_stdPlane planeGroup_stdPlane commute_longRootSp2 exists_conj_planeGroup
  longBlock)

variable {m : ℕ} {G : Type} [Group G]

theorem exists_labLift (hm : 3 ≤ m) {Ω : Set (Subgroup G)} (hnonab : ∀ M ∈ Ω, ¬ Commutes M M)
    {K : Fin (m + 1) → Subgroup G} (hK : IsMemberFrame Ω K) {l : Fin (m + 1)}
    {Θ' : StatedSp m (GaloisField 3 1) →* G} (h : IsLocLift m Ω (K l) Θ') :
    ∃ Θ : StatedSp m (GaloisField 3 1) →* G, IsLabLift m Ω K l Θ := by
  have hex : ∀ c : Fin (m + 1), ∃ P : Submodule (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1),
      c ≠ l → IsHyperbolicPlane P ∧ K c = (planeGroup P).map Θ' := by
    intro c
    by_cases hc : c = l
    · exact ⟨⊥, fun h' => absurd hc h'⟩
    · have hne : K c ≠ K l := by
        intro heq
        apply hnonab (K l) (hK.mem l)
        have := hK.comm c l hc
        rwa [heq] at this
      obtain ⟨P, hP, hKP⟩ := h.members (K c) (hK.mem c) hne (hK.comm c l hc)
      exact ⟨P, fun _ => ⟨hP, hKP⟩⟩
  choose Pl hPl using hex
  have hhyp : ∀ j : Fin m, IsHyperbolicPlane (Pl (l.succAbove j)) := fun j =>
    (hPl _ (Fin.succAbove_ne l j)).1
  have horth : ∀ j j' : Fin m, j ≠ j' → ∀ x ∈ Pl (l.succAbove j), ∀ y ∈ Pl (l.succAbove j'),
      form x y = 0 := by
    intro j j' hjj'
    refine (commutes_map_planeGroup_iff hm h.ker_le (hhyp j) (hhyp j')).1 ?_
    rw [← (hPl _ (Fin.succAbove_ne l j)).2, ← (hPl _ (Fin.succAbove_ne l j')).2]
    exact hK.comm _ _ (fun h' => hjj' (Fin.succAbove_right_injective h'))
  obtain ⟨γ, hγ⟩ := exists_conj_planeGroup (P := fun j => Pl (l.succAbove j)) hhyp horth
  refine ⟨Θ'.comp (MulAut.conj γ).toMonoidHom, IsLocLift.relabel h γ, fun j => ?_⟩
  rw [← Subgroup.map_map, planeGroup_stdPlane]
  have h2 : planeGroup (Pl (l.succAbove j)) =
      (longBlock (GaloisField 3 1) m j).range.map (MulAut.conj γ).toMonoidHom := (hγ j).2
  have h1 : ((longBlock (GaloisField 3 1) m j).range.map (MulAut.conj γ).toMonoidHom).map Θ' =
      K (l.succAbove j) := by
    rw [← h2, ← (hPl _ (Fin.succAbove_ne l j)).2]
  exact h1

theorem exists_frame_lifts (hm : 3 ≤ m) {K₀ : Subgroup G} (hK₀ : ¬ Commutes K₀ K₀)
    {Θ₀ : StatedSp m (GaloisField 3 1) →* G} (h : IsLocLift m (conjClass3 K₀) K₀ Θ₀) :
    ∃ (K : Fin (m + 1) → Subgroup G) (Θ : Fin (m + 1) → (StatedSp m (GaloisField 3 1) →* G)),
      K 0 = K₀ ∧ IsMemberFrame (conjClass3 K₀) K ∧
        ∀ l, IsLabLift m (conjClass3 K₀) K l (Θ l) := by
  have hinv : ConjInvariant (conjClass3 K₀) := by
    rintro n M ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul n g K₀⟩
  have hmemK₀ : K₀ ∈ conjClass3 K₀ := ⟨1, conjSub_one K₀⟩
  have hnonab : ∀ M ∈ conjClass3 K₀, ¬ Commutes M M := by
    rintro M ⟨g, rfl⟩ hM
    exact hK₀ ((commutes_conjSub_iff g).1 hM)
  let K : Fin (m + 1) → Subgroup G :=
    Fin.cons K₀ fun j => (planeGroup (stdPlane (GaloisField 3 1) m j)).map Θ₀
  have hK0 : K 0 = K₀ := Fin.cons_zero _ _
  have hKs : ∀ j : Fin m, K j.succ = (planeGroup (stdPlane (GaloisField 3 1) m j)).map Θ₀ :=
    fun j => Fin.cons_succ _ _ _
  have hcomm0 : ∀ j : Fin m, Commutes K₀ (K j.succ) := fun j x hx y hy => by
    rw [hKs] at hy
    exact (h.comm y (Subgroup.map_le_range _ _ hy) x hx).symm
  have hframe : IsMemberFrame (conjClass3 K₀) K := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · rw [hK0]
        exact hmemK₀
      · rw [hKs]
        exact h.plane_mem _ (isHyperbolicPlane_stdPlane j)
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact absurd rfl hij
      · rw [hK0]
        exact hcomm0 j'
      · rw [hK0]
        exact (hcomm0 i').symm
      · have hij' : i' ≠ j' := fun e => hij (by rw [e])
        rw [hKs, hKs]
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul]
        rw [planeGroup_stdPlane] at hx hy
        rw [(commute_longRootSp2 hij' hx hy).eq]
  have hlab : ∀ l, ∃ Θ : StatedSp m (GaloisField 3 1) →* G,
      IsLabLift m (conjClass3 K₀) K l Θ := by
    intro l
    obtain ⟨g, hg⟩ := hframe.mem l
    have hg' : conjSub g K₀ = K l := hg
    have hlift : IsLocLift m (conjClass3 K₀) (K l) ((MulAut.conj g).toMonoidHom.comp Θ₀) := by
      rw [← hg']
      exact IsLocLift.conj hinv h g
    exact exists_labLift hm hnonab hframe hlift
  choose Θ hΘ using hlab
  exact ⟨K, Θ, hK0, hframe, hΘ⟩

end CFSG.ClassicalInvolution.Q3.Q3V.Frame
