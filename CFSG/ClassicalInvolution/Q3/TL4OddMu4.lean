module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4D
public import CFSG.ClassicalInvolution.Q3.TL4OddFrGen
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4F

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Orbit

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_closure_three {a b c g : G}
    (ha : g * a * g⁻¹ ∈ Subgroup.closure ({a, b, c} : Set G))
    (hb : g * b * g⁻¹ ∈ Subgroup.closure ({a, b, c} : Set G))
    (hc : g * c * g⁻¹ ∈ Subgroup.closure ({a, b, c} : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.closure ({a, b, c} : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  have hle : conjSub g (Subgroup.closure ({a, b, c} : Set G)) ≤
      Subgroup.closure ({a, b, c} : Set G) := by
    rw [conjSub, map_conj_closure_three, Subgroup.closure_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  exact Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.closure ({a, b, c} : Set G))
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv

omit [Finite G] in
theorem hyp51_of_coset {t u s a b : G} (ht : t * t = 1) (hu : u * u = 1) (hs : s * s = 1)
    (htu : t * u = u * t) (hts : t * s = s * t) (hus : u * s = s * u)
    (hE : IsElemAbelian 2 (Subgroup.closure ({t, u, s} : Set G)))
    (h8 : Nat.card ↥(Subgroup.closure ({t, u, s} : Set G)) = 8)
    (ha : a ∈ Subgroup.normalizer ((Subgroup.closure ({t, u, s} : Set G) : Subgroup G) : Set G))
    (has : a * s * a⁻¹ = t * s) (hau : a * u * a⁻¹ = u)
    (hb : b ∈ Subgroup.normalizer ((Subgroup.closure ({t, u, s} : Set G) : Subgroup G) : Set G))
    (hbs : b * s * b⁻¹ = u * s)
    (vt : Hyp51At (Subgroup.closure ({t, u, s} : Set G)) t)
    (vu : Hyp51At (Subgroup.closure ({t, u, s} : Set G)) u)
    (vtu : Hyp51At (Subgroup.closure ({t, u, s} : Set G)) (t * u))
    (vs : Hyp51At (Subgroup.closure ({t, u, s} : Set G)) s) :
    Hyp51 (Subgroup.closure ({t, u, s} : Set G)) := by
  set B := Subgroup.closure ({t, u, s} : Set G) with hBdef
  have hmv : ∀ {g c c' : G}, g ∈ Subgroup.normalizer (B : Set G) → Hyp51At B c →
      g * c * g⁻¹ = c' → Hyp51At B c' := by
    intro g c c' hg h e
    have h1 := ExactLayer.hyp51At_of_normalizes hg h
    rwa [e] at h1
  have vts : Hyp51At B (t * s) := hmv ha vs has
  have vus : Hyp51At B (u * s) := hmv hb vs hbs
  have vtus : Hyp51At B (t * u * s) := hmv ha vus (by
    calc a * (u * s) * a⁻¹ = (a * u * a⁻¹) * (a * s * a⁻¹) := by group
      _ = t * u * s := by rw [hau, has, ← mul_assoc, ← htu])
  refine ⟨hE, h8, fun c hc hc1 => ?_⟩
  rcases mem_closure_three_cases hs hts hus hc with h | ⟨e, he, rfl⟩
  · rcases T3CII.closure_pair_cases ht hu htu h with rfl | rfl | rfl | rfl
    · exact absurd rfl hc1
    · exact vt
    · exact vu
    · exact vtu
  · rcases T3CII.closure_pair_cases ht hu htu he with rfl | rfl | rfl | rfl
    · rwa [one_mul]
    · exact vts
    · exact vus
    · exact vtus

end Orbit

section Frames

variable {Y : Type} [Group Y] {R : Subgroup Y} {t : Y} {J K' : Subgroup Y} {u x y x' : Y}

theorem E4FrameAt.conj_a (hF : E4FrameAt R t J K' u x y x') (ht : t * t = 1) {a : Y}
    (hax : a * x * a⁻¹ = x⁻¹) (hay : a * y = y * a) (hax' : a * x' = x' * a) :
    a * t * a⁻¹ = t ∧ a * u * a⁻¹ = u ∧ a * (x * y * x') * a⁻¹ = t * (x * y * x') := by
  have hxi : x⁻¹ = t * x := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [mul_assoc, hF.sqx, ht]
  have hay' : a * y * a⁻¹ = y := by rw [hay, mul_inv_cancel_right]
  have hax'' : a * x' * a⁻¹ = x' := by rw [hax', mul_inv_cancel_right]
  refine ⟨?_, ?_, ?_⟩
  · calc a * t * a⁻¹ = (a * x * a⁻¹) * (a * x * a⁻¹) := by rw [← hF.sqx]; group
      _ = (t * x) * (t * x) := by rw [hax, hxi]
      _ = t := by
        have h1 := hF.commute_t.1
        rw [mul_assoc, ← mul_assoc x t x, ← h1.eq, mul_assoc, hF.sqx, ← mul_assoc, ht,
          one_mul]
  · calc a * u * a⁻¹ = (a * y * a⁻¹) * (a * y * a⁻¹) := by rw [← hF.sqy]; group
      _ = u := by rw [hay', hF.sqy]
  · calc a * (x * y * x') * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) * (a * x' * a⁻¹) := by group
      _ = t * (x * y * x') := by rw [hax, hay', hax'', hxi]; group

theorem E4FrameAt.conj_b (hF : E4FrameAt R t J K' u x y x') (hu : u * u = 1) {b : Y}
    (hby : b * y * b⁻¹ = y⁻¹) (hbx : b * x = x * b) (hbx' : b * x' = x' * b) :
    b * t * b⁻¹ = t ∧ b * u * b⁻¹ = u ∧ b * (x * y * x') * b⁻¹ = u * (x * y * x') := by
  have hyi : y⁻¹ = u * y := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [mul_assoc, hF.sqy, hu]
  have hbx'' : b * x * b⁻¹ = x := by rw [hbx, mul_inv_cancel_right]
  have hbx''' : b * x' * b⁻¹ = x' := by rw [hbx', mul_inv_cancel_right]
  refine ⟨?_, ?_, ?_⟩
  · calc b * t * b⁻¹ = (b * x * b⁻¹) * (b * x * b⁻¹) := by rw [← hF.sqx]; group
      _ = t := by rw [hbx'', hF.sqx]
  · calc b * u * b⁻¹ = (b * y * b⁻¹) * (b * y * b⁻¹) := by rw [← hF.sqy]; group
      _ = (u * y) * (u * y) := by rw [hby, hyi]
      _ = u := by
        have h1 := hF.commute_u.2.1
        rw [mul_assoc, ← mul_assoc y u y, ← h1.eq, mul_assoc, hF.sqy, ← mul_assoc, hu,
          one_mul]
  · calc b * (x * y * x') * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) * (b * x' * b⁻¹) := by group
      _ = x * (u * y) * x' := by rw [hbx'', hby, hbx''', hyi]
      _ = u * (x * y * x') := by
        have h1 := hF.commute_u.1
        rw [← mul_assoc x u y, ← h1.eq]; group

@[expose] def e4FramePred (R : Subgroup Y) (t : Y) : Subgroup Y → Y → Y → Prop :=
  fun J u s => ∃ (K' : Subgroup Y) (x y x' : Y), E4FrameAt R t J K' u x y x' ∧ s = x * y * x'

end Frames

section Cit3


@[expose] def TightE4VtxSR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      LinkE4 R t → ¬ TriNbrAll R t → ∀ (J K' : Subgroup Y) (u x y x' : Y),
        E4FrameAt R t J K' u x y x' →
          Hyp51At (Subgroup.closure ({t, u, x * y * x'} : Set Y)) (x * y * x')

@[expose] def TightE4FrameR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      LinkE4 R t → ¬ TriNbrAll R t →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        ∀ u : Y, IsUniqueInvolution J u →
          ∃ (K' : Subgroup Y) (x y x' : Y), E4FrameAt R t J K' u x y x'

@[expose] def TightE4GenR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      LinkE4 R t → ¬ TriNbrAll R t →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
          Relation.ReflTransGen (FrameLinkStepP (e4FramePred R t) t) J J'


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J K' : Subgroup Y} {u x y x' : Y}

theorem hyp51_e4Frame (h4 : Thm4RBelow 3 n) (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n)
    (hOm : OmegaAutOddFreeR) (hs : TightE4VtxSR 3 n) (hL : TightLargeHypR 3 n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) (hA : ¬ TriNbrAll R t)
    (hcase : LinkE4 R t) (hF : E4FrameAt R t J K' u x y x') :
    Hyp51 (Subgroup.closure ({t, u, x * y * x'} : Set Y)) := by
  have ht := hL.datum.isUniqueInvolution_core
  have hE := hF.isElemAbelian hL
  have hm := mem_closure_three_left t u (x * y * x')
  obtain ⟨vt, vu, vtu⟩ := hyp51At_of_commonNbr h4 htw hOm hL hF.memJ hF.memK hF.memKJ hF.invJ
    hF.invK hE hm.1 hm.2.1
  obtain ⟨a, hax, hay, hax'⟩ := hF.invx
  obtain ⟨b, hby, hbx, hbx'⟩ := hF.invy
  obtain ⟨hat, hau, has⟩ := hF.conj_a ht.sq hax hay hax'
  obtain ⟨hbt, hbu, hbs⟩ := hF.conj_b hF.invJ.sq hby hbx hbx'
  have haN := mem_normalizer_closure_three (by rw [hat]; exact hm.1) (by rw [hau]; exact hm.2.1)
    (by rw [has]; exact Subgroup.mul_mem _ hm.1 hm.2.2)
  have hbN := mem_normalizer_closure_three (by rw [hbt]; exact hm.1) (by rw [hbu]; exact hm.2.1)
    (by rw [hbs]; exact Subgroup.mul_mem _ hm.2.1 hm.2.2)
  exact hyp51_of_coset ht.sq hF.invJ.sq (hF.sq_s ht.sq hF.invJ.sq) hF.comm_tu hF.comm_ts
    hF.comm_us hE (hF.natCard hL) haN has hau hbN hbs vt vu vtu
    (hs Y R S t hL hc hcase hA J K' u x y x' hF)

theorem alphaOf_eq_bot_of_e4 (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hs : TightE4VtxSR 3 n) (hfr : TightE4FrameR 3 n) (hg : TightE4GenR 3 n)
    (hL : TightLargeHypR 3 n Y R S t) (hc : DConnected (CoreAssembly.conjClass (tightCore R)))
    (hA : ¬ TriNbrAll R t) (hcase : LinkE4 R t) :
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ := by
  refine alphaOf_eq_bot_of_framesP hL hc ?_ ?_ ?_ (hg Y R S t hL hc hcase hA)
  · rintro J u s ⟨K', x, y, x', hF, -⟩
    exact ⟨hF.memJ, hF.invJ⟩
  · rintro J u s ⟨K', x, y, x', hF, rfl⟩
    exact hyp51_e4Frame h4 htw hOm hs hL hc hA hcase hF
  · intro J hJ u hu
    obtain ⟨K', x, y, x', hF⟩ := hfr Y R S t hL hc hcase hA J hJ u hu
    exact ⟨_, K', x, y, x', hF, rfl⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
