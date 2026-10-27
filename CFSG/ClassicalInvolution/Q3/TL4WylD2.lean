module

public import CFSG.ClassicalInvolution.Q3.TL4WylD
public import CFSG.ClassicalInvolution.Q3.Q3T7K00
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Main

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Wyl

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)

section Sec

variable {X : Type} [Group X] [Finite X] {r n : ℕ} {Φ : Set (Subgroup X)}

omit [Finite X] in
theorem tri_of_frame {B : Fin 4 → Subgroup X} (hne : ∀ i j, i ≠ j → B i ≠ B j)
    (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr Φ (B i)) {e : Fin 3 → Fin 4}
    (he : Function.Injective e) :
    Function.Injective (fun a => B (e a)) ∧
      ∀ a b, a ≠ b → B (e b) ∈ omegaNbr Φ (B (e a)) := by
  refine ⟨fun a b hab => ?_, fun a b hab => hadj _ _ (he.ne hab)⟩
  by_contra h
  exact hne _ _ (he.ne h) hab

theorem frame_facts (hS : TightSecFrameR r n) (hn : Nat.card X < n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤) (hA : ∀ L ∈ Φ, AEmpty Φ L)
    (hc : ¬ DConnected Φ) {B : Fin 4 → Subgroup X} {u : Fin 4 → X} (hB : ∀ i, B i ∈ Φ)
    (hne : ∀ i j, i ≠ j → B i ≠ B j) (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr Φ (B i))
    (hu : ∀ i, IsUniqueInvolution (B i) (u i)) :
    (∀ j, u 0 * u j ∈ Subgroup.center X) ∧ ∀ M ∈ omegaNbr Φ (B 0), ∃ j, M = B j := by
  have app := fun (e : Fin 3 → Fin 4) (he : Function.Injective e) =>
    hS X hn Φ h hO hgen hA hc (fun a => B (e a)) (fun a => hB (e a)) (tri_of_frame hne hadj he).1
      (tri_of_frame hne hadj he).2 (fun a => u (e a)) (fun a => hu (e a))
  refine ⟨fun j => ?_, fun M hM => ?_⟩
  · fin_cases j
    · show u 0 * u 0 ∈ Subgroup.center X
      rw [(hu 0).sq]
      exact (Subgroup.center X).one_mem
    · exact (app ![0, 1, 2] (by decide)).1
    · exact (app ![0, 2, 1] (by decide)).1
    · exact (app ![0, 3, 1] (by decide)).1
  · obtain ⟨-, B₃, hB₃, h1, h2, hall⟩ := app ![0, 1, 2] (by decide)
    have e3 : B 3 = B₃ := by
      rcases hall (B 3) (hadj 0 3 (by decide)) with h | h | h
      · exact absurd h (hne 3 1 (by decide))
      · exact absurd h (hne 3 2 (by decide))
      · exact h
    rcases hall M hM with h | h | h
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h.trans e3.symm⟩

omit [Finite X] in
theorem exists_eq_frame_mul_of_conj (hΦ : HypOmegaGen Φ) {B : Fin 4 → Subgroup X} {u : Fin 4 → X}
    (hu : ∀ i, IsUniqueInvolution (B i) (u i)) (hcen : ∀ j, u 0 * u j ∈ Subgroup.center X)
    (hnb : ∀ M ∈ omegaNbr Φ (B 0), ∃ j, M = B j) {g : X} {L' : Subgroup X}
    (hL' : L' ∈ omegaNbr Φ (conjSub g (B 0))) {v v' : X}
    (hv : IsUniqueInvolution (conjSub g (B 0)) v) (hv' : IsUniqueInvolution L' v') :
    ∃ j, v * v' = u 0 * u j := by
  have h1 := omegaNbr_conj hΦ.conjInvariant hL' g⁻¹
  rw [conjSub_inv_conjSub] at h1
  obtain ⟨j, hj⟩ := hnb _ h1
  have hL'j : L' = conjSub g (B j) := by
    rw [← hj, conjSub_conjSub_inv]
  rw [hL'j] at hv'
  have e1 : v = g * u 0 * g⁻¹ := hv.eq ((hu 0).conj g)
  have e2 : v' = g * u j * g⁻¹ := hv'.eq ((hu j).conj g)
  refine ⟨j, ?_⟩
  have hc := Subgroup.mem_center_iff.mp (hcen j) g
  rw [e1, e2]
  calc g * u 0 * g⁻¹ * (g * u j * g⁻¹) = (g * (u 0 * u j)) * g⁻¹ := by group
    _ = (u 0 * u j * g) * g⁻¹ := by rw [hc]
    _ = u 0 * u j := by group

theorem exists_eq_frame_mul (hT4 : Thm4RBelow r n) (hT : T4Hyp r X Φ) (hn : Nat.card X < n)
    {B : Fin 4 → Subgroup X} {u : Fin 4 → X} (hB : ∀ i, B i ∈ Φ)
    (hu : ∀ i, IsUniqueInvolution (B i) (u i)) (hcen : ∀ j, u 0 * u j ∈ Subgroup.center X)
    (hnb : ∀ M ∈ omegaNbr Φ (B 0), ∃ j, M = B j) {L L' : Subgroup X} (hL : L ∈ Φ)
    (hL' : L' ∈ omegaNbr Φ L) {v v' : X} (hv : IsUniqueInvolution L v)
    (hv' : IsUniqueInvolution L' v') : ∃ i j, v * v' = u i * u j := by
  have hΦ := hT.hyp
  have hout : ∀ {M : Subgroup X}, M ∈ Φ → (¬ ∃ g : X, conjSub g (B 0) = M) → ∃ j, M = B j := by
    intro M hM hnc
    have hne : M ≠ B 0 := fun e => hnc ⟨1, by rw [conjSub_one, e]⟩
    exact hnb M (mem_omegaNbr_of_commutes hM hne (hT4 X hn Φ hT (B 0) (hB 0) M hM hnc))
  by_cases hLc : ∃ g : X, conjSub g (B 0) = L
  · obtain ⟨g, rfl⟩ := hLc
    obtain ⟨j, hj⟩ := exists_eq_frame_mul_of_conj hΦ hu hcen hnb hL' hv hv'
    exact ⟨0, j, hj⟩
  · obtain ⟨i, rfl⟩ := hout hL hLc
    have hvi : v = u i := hv.eq (hu i)
    by_cases hL'c : ∃ g : X, conjSub g (B 0) = L'
    · obtain ⟨g, rfl⟩ := hL'c
      have hLL' := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ hL hL'.1 hL'
      obtain ⟨k, hk⟩ := exists_eq_frame_mul_of_conj hΦ hu hcen hnb hLL' hv' hv
      refine ⟨k, 0, ?_⟩
      have h1 : (v' * v)⁻¹ = (u 0 * u k)⁻¹ := by rw [hk]
      rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right hv.sq,
        inv_eq_of_mul_eq_one_right hv'.sq, inv_eq_of_mul_eq_one_right (hu 0).sq,
        inv_eq_of_mul_eq_one_right (hu k).sq] at h1
      exact h1
    · obtain ⟨j, rfl⟩ := hout hL'.1 hL'c
      exact ⟨i, j, by rw [hvi, hv'.eq (hu j)]⟩

end Sec

section Frattini

variable {G : Type} [Group G] [Finite G] {r n : ℕ} {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem frattini (hS : TightSecFrameR r n) (hT4 : Thm4RBelow r n) (h : TypeRFam r Ω)
    (hs : Std8Core Ω K J S R T W z t) (hn : Nat.card (SecQuot Ω (z * t)) < n)
    (hnc : ¬ DConnected (secFam Ω (z * t))) (F : FrameData Ω W K J z t) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z * t} : Set G)) :
    ∃ o ∈ oddCoreOf (layerY Ω (z * t)), conjSub (o * c) (vGrp F) = vGrp F := by
  classical
  have hcl := h.hyp.conjInvariant
  have c0 := Q3CL.T8.ctxOf (partIHyp_of_std8 hs) hs.hW.1
  have hT : T4Hyp r (SecQuot Ω (z * t)) (secFam Ω (z * t)) :=
    t4Hyp_of h.secFam (aEmpty_secFam h) secQuot_oddCore_eq_bot
  have hzY : ∀ i, F.zz i ∈ layerY Ω (z * t) := fun i =>
    mem_layerY_of_isUniqueInvolution h (frame_xMem hs F i) (F.hz i)
  obtain ⟨hcen, hnb⟩ := frame_facts hS hn h.secFam secQuot_oddCore_eq_bot omegaGen_secFam
    (aEmpty_secFam h) hnc (fun i => secImg_mem (frame_xMem hs F i))
    (fun i j hij => frame_secImg_ne h hs F hij) (fun i j hij => frame_secImg_nbr h hs F hij)
    (fun i => isUniqueInvolution_secImg h (frame_xMem hs F i) (F.hz i))
  have key : ∀ i j : Fin 4,
      c * (F.zz i * F.zz j) * c⁻¹ ∈ vGrp F ⊔ oddCoreOf (layerY Ω (z * t)) := by
    intro i j
    by_cases hij : i = j
    · rw [hij, (F.hz j).sq, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hLi := XMem.conj' hcl (frame_xMem hs F i) hc
    have hLj := XMem.conj' hcl (frame_xMem hs F j) hc
    have hvi := (F.hz i).conj c
    have hvj := (F.hz j).conj c
    have hcomm : c * F.zz i * c⁻¹ * (c * F.zz j * c⁻¹) =
        c * F.zz j * c⁻¹ * (c * F.zz i * c⁻¹) := by
      calc c * F.zz i * c⁻¹ * (c * F.zz j * c⁻¹) = c * (F.zz i * F.zz j) * c⁻¹ := by group
        _ = c * (F.zz j * F.zz i) * c⁻¹ := by rw [zz_comm c0 F i j]
        _ = c * F.zz j * c⁻¹ * (c * F.zz i * c⁻¹) := by group
    have hne : c * F.zz i * c⁻¹ ≠ c * F.zz j * c⁻¹ := fun e =>
      F.hinj i j hij (by simpa using e)
    have hPx : conjSub c (F.ρ j).R ≤ Subgroup.centralizer ({z * t} : Set G) := by
      intro y hy
      rw [mem_conjSub_iff] at hy
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (frame_rep_le_centralizer c0 F j hy)
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc y * (z * t) = c * (c⁻¹ * y * c * (c⁻¹ * (z * t) * c)) * c⁻¹ := by group
        _ = c * (c⁻¹ * y * c * (z * t)) * c⁻¹ := by
          rw [show c⁻¹ * (z * t) * c = z * t by rw [mul_assoc, ← h2]; group]
        _ = c * ((z * t) * (c⁻¹ * y * c)) * c⁻¹ := by rw [h1]
        _ = c * (c⁻¹ * (z * t) * c * (c⁻¹ * y * c)) * c⁻¹ := by
          rw [show c⁻¹ * (z * t) * c = z * t by rw [mul_assoc, ← h2]; group]
        _ = z * t * y := by group
    have hPN : conjSub c (F.ρ j).R ≤ Subgroup.normalizer (conjSub c (F.ρ i).K : Set G) := by
      have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
        T8.noTwins_of_mem hcl hs.stand.trans hs.noTwins hM
      have hRN : (F.ρ j).R ≤ Subgroup.normalizer ((F.ρ i).K : Set G) := fun y hy =>
        T8.centralizer_le_normalizer_of_noTwins hcl (F.ρ i).hK (hnt _ (F.ρ i).hK) (F.hz i)
          (rep_le_centralizer_gen c0 (F.ρ j) (F.ρ i) (Or.inr (F.hadj j i (Ne.symm hij)))
            (F.hz i) hy)
      intro y hy
      rw [mem_conjSub_iff] at hy
      have h1 := mem_normalizer_iff_conjSub_eq.mp (hRN hy)
      rw [mem_normalizer_iff_conjSub_eq]
      calc conjSub y (conjSub c (F.ρ i).K)
          = conjSub c (conjSub (c⁻¹ * y * c) (F.ρ i).K) := by
            rw [← conjSub_mul, ← conjSub_mul]; congr 1; group
        _ = conjSub c (F.ρ i).K := by rw [h1]
    have hadj := secImg_mem_omegaNbr hLi hLj ((F.ρ j).hRK.conj c) hPx hPN
      (secImg_ne h hLi hLj hvi hvj hcomm hne)
    obtain ⟨p, q, hpq⟩ := exists_eq_frame_mul hT4 hT hn
      (fun i => secImg_mem (frame_xMem hs F i))
      (fun i => isUniqueInvolution_secImg h (frame_xMem hs F i) (F.hz i)) hcen hnb
      (secImg_mem hLi) hadj (isUniqueInvolution_secImg h hLi hvi)
      (isUniqueInvolution_secImg h hLj hvj)
    set N := classicalInvolutionOddCore ↥(layerY Ω (z * t))
    set w : ↥(layerY Ω (z * t)) := ⟨F.zz p * F.zz q, (layerY Ω (z * t)).mul_mem (hzY p) (hzY q)⟩
    set v : ↥(layerY Ω (z * t)) :=
      ⟨c * F.zz i * c⁻¹, mem_layerY_of_isUniqueInvolution h hLi hvi⟩ *
        ⟨c * F.zz j * c⁻¹, mem_layerY_of_isUniqueInvolution h hLj hvj⟩
    have hwv : (QuotientGroup.mk' N) w = (QuotientGroup.mk' N) v := by
      simp only [w, v, map_mul]
      rw [hpq]
      rfl
    have hm : w⁻¹ * v ∈ N := QuotientGroup.eq.mp hwv
    have e : c * (F.zz i * F.zz j) * c⁻¹ = (w : G) * ((w⁻¹ * v : ↥(layerY Ω (z * t))) : G) := by
      simp only [w, v, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact Subgroup.mul_mem_sup (mul_mem_vGrp c0 F p q) ⟨w⁻¹ * v, hm, rfl⟩
  have hle : conjSub c (vGrp F) ≤ vGrp F ⊔ oddCoreOf (layerY Ω (z * t)) := by
    unfold vGrp
    rw [T7A.conjSub_closure_pair, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact key 0 1
    · exact key 0 2
  have hVab := isElemAbelian2_vGrp c0 F
  have hV2 : IsPGroup 2 (vGrp F) := IsPGroup.of_card hVab.1
  have hcard : Nat.card (conjSub c (vGrp F)) = Nat.card (vGrp F) :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hV'2 : IsPGroup 2 (conjSub c (vGrp F)) := IsPGroup.of_card (hcard.trans hVab.1)
  have hVO : vGrp F ≤ Subgroup.normalizer (oddCoreOf (layerY Ω (z * t)) : Set G) := by
    intro v hv
    have hvc : v ∈ Subgroup.centralizer ({z * t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hzt := zt_mem_vGrp F
      have hv2 : (v * (z * t)) * (v * (z * t)) = 1 := hVab.2 _ ((vGrp F).mul_mem hv hzt)
      calc v * (z * t) = (v * (z * t))⁻¹ := (inv_eq_of_mul_eq_one_right hv2).symm
        _ = (z * t)⁻¹ * v⁻¹ := mul_inv_rev _ _
        _ = (z * t) * v := by
          rw [inv_eq_of_mul_eq_one_right (hVab.2 _ hzt), inv_eq_of_mul_eq_one_right (hVab.2 v hv)]
    rw [mem_normalizer_iff_conjSub_eq, ← oddCoreOf_conjSub_eq, layerY_conjSub_eq hcl hvc]
  have hVO0 : vGrp F ⊓ oddCoreOf (layerY Ω (z * t)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).mpr (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hx.2
      (hV2.to_le (Subgroup.zpowers_le.mpr hx.1)))
  obtain ⟨o, ho, hoV⟩ := Q3T7M.CentQ.exists_conjSub_of_le_sup_odd hVO
    (oddCoreOf_odd_natCard _) hVO0 hV2 hV'2 hcard (by rwa [sup_comm] at hle)
  refine ⟨o⁻¹, (oddCoreOf _).inv_mem ho, ?_⟩
  rw [conjSub_mul, ← hoV, conjSub_inv_conjSub]

end Frattini

end CFSG.ClassicalInvolution.Q3.TL4.Wyl
