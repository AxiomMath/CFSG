module

public import CFSG.ClassicalInvolution.Q3.Q3VF4SLayer
public import CFSG.ClassicalInvolution.Q3.Q3WASTClosure
public import CFSG.ClassicalInvolution.Q3.Q3E8BShape
public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinPerpLayer
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCGeneration
public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternShape

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.Q3.Q3V.Lift
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  planeGroup_stdPlane isHyperbolicPlane_stdPlane longBlock longInv form form_single_inl_inr coords
  suppGroup mem_suppGroup mem_suppGroup_iff isSupp_longBlock commute_suppGroup_compl
  parClosed_coords ParClosed pairEmbed pairMap pairMap_injective spEmbed_longBlock
  planeGroup_map_conj mulVec_eq_iff mem_coords exists_sp_apply_eq_two_at)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

local notation "F₃" => GaloisField 3 1


variable {G : Type} [Group G]

theorem ncEdge_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {x y : G}
    (hy : y * x * y⁻¹ = x) {A B : Subgroup G} (h : NCEdge Ω x A B) :
    NCEdge Ω x (conjSub y A) (conjSub y B) := by
  have hcm : ∀ {N : Subgroup G}, N ∈ centralizingMembers Ω {x} →
      conjSub y N ∈ centralizingMembers Ω {x} := by
    rintro N ⟨hN, hNc⟩
    refine ⟨hΩ y N hN, fun u hu => ?_⟩
    rw [mem_conjSub_iff] at hu
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hNc hu)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * x = u * (y * x * y⁻¹) := by rw [hy]
      _ = y * ((y⁻¹ * u * y) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * u * y)) * y⁻¹ := by rw [h1]
      _ = (y * x * y⁻¹) * u := by group
      _ = x * u := by rw [hy]
  exact ⟨hcm h.1, hcm h.2.1, fun hc => h.2.2 ((commutes_conjSub_iff y).mp hc)⟩

theorem linked_conj [Finite G] {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {x y : G}
    (hy : y * x * y⁻¹ = x) {A B : Subgroup G} (h : Linked Ω x A B) :
    Linked Ω x (conjSub y A) (conjSub y B) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (ncEdge_conj hΩ hy hbc)

theorem conjSub_eq_of_forall_commute {A : Subgroup G} {y : G} (hc : ∀ a ∈ A, y * a = a * y) :
    conjSub y A = A := by
  ext u
  rw [mem_conjSub_iff]
  have key : ∀ a ∈ A, y⁻¹ * a * y = a := fun a ha => by
    rw [mul_assoc, ← hc a ha]
    group
  constructor
  · intro hu
    have h := hc _ hu
    have e : u = y⁻¹ * u * y :=
      calc u = y * (y⁻¹ * u * y) * y⁻¹ := by group
        _ = (y⁻¹ * u * y) * y * y⁻¹ := by rw [h]
        _ = y⁻¹ * u * y := by group
    rw [e]
    exact hu
  · intro hu
    rw [key u hu]
    exact hu

section Witt

theorem mat_apply_of_fix {n : ℕ} {h : StatedSp n F₃} {t : Fin n ⊕ Fin n}
    (hf : mat n F₃ h *ᵥ (Pi.single t 1 : Fin n ⊕ Fin n → F₃) = Pi.single t 1)
    (r : Fin n ⊕ Fin n) :
    mat n F₃ h r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F₃) r t := by
  have := congrFun hf r
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using this

theorem exists_sp_fix_plane_two {P P' : Submodule F₃ (Fin 3 ⊕ Fin 3 → F₃)}
    (hP : IsHyperbolicPlane P) (hP' : IsHyperbolicPlane P')
    (hPo : ∀ u ∈ P, ∀ v ∈ stdPlane F₃ 3 2, form u v = 0)
    (hPo' : ∀ u ∈ P', ∀ v ∈ stdPlane F₃ 3 2, form u v = 0) :
    ∃ h : StatedSp 3 F₃, h ∈ suppGroup (coords (2 : Fin 3))ᶜ ∧
      P.map (Matrix.mulVecLin (mat 3 F₃ h)) = P' := by
  obtain ⟨u, w, huw, rfl⟩ := hP
  obtain ⟨u', w', huw', rfl⟩ := hP'
  have he : (Pi.single (Sum.inl (2 : Fin 3)) 1 : Fin 3 ⊕ Fin 3 → F₃) ∈ stdPlane F₃ 3 2 := by
    rw [stdPlane]
    exact Submodule.subset_span (by simp)
  have hf : (Pi.single (Sum.inr (2 : Fin 3)) 1 : Fin 3 ⊕ Fin 3 → F₃) ∈ stdPlane F₃ 3 2 := by
    rw [stdPlane]
    exact Submodule.subset_span (by simp)
  have hu : u ∈ Submodule.span F₃ {u, w} := Submodule.subset_span (by simp)
  have hw : w ∈ Submodule.span F₃ {u, w} := Submodule.subset_span (by simp)
  have hu' : u' ∈ Submodule.span F₃ {u', w'} := Submodule.subset_span (by simp)
  have hw' : w' ∈ Submodule.span F₃ {u', w'} := Submodule.subset_span (by simp)
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  obtain ⟨g₁, a1, a2, a3, a4⟩ := exists_sp_apply_eq_two_at h02 u w (Pi.single (Sum.inl 2) 1)
    (Pi.single (Sum.inr 2) 1) huw (form_single_inl_inr 2) (hPo _ hu _ he) (hPo _ hu _ hf)
    (hPo _ hw _ he) (hPo _ hw _ hf)
  obtain ⟨g₂, b1, b2, b3, b4⟩ := exists_sp_apply_eq_two_at h02 u' w' (Pi.single (Sum.inl 2) 1)
    (Pi.single (Sum.inr 2) 1) huw' (form_single_inl_inr 2) (hPo' _ hu' _ he) (hPo' _ hu' _ hf)
    (hPo' _ hw' _ he) (hPo' _ hw' _ hf)
  have fixe : mat 3 F₃ (g₂ * g₁⁻¹) *ᵥ (Pi.single (Sum.inl (2 : Fin 3)) 1 : Fin 3 ⊕ Fin 3 → F₃) =
      Pi.single (Sum.inl 2) 1 := by
    rw [map_mul, ← Matrix.mulVec_mulVec, Models.SymplecticPairs.mulVec_inv_eq_self a3, b3]
  have fixf : mat 3 F₃ (g₂ * g₁⁻¹) *ᵥ (Pi.single (Sum.inr (2 : Fin 3)) 1 : Fin 3 ⊕ Fin 3 → F₃) =
      Pi.single (Sum.inr 2) 1 := by
    rw [map_mul, ← Matrix.mulVec_mulVec, Models.SymplecticPairs.mulVec_inv_eq_self a4, b4]
  refine ⟨g₂ * g₁⁻¹, ?_, ?_⟩
  · refine (mem_suppGroup_iff (Models.SymplecticPairs.ParClosed.compl (parClosed_coords 2))).2
      fun t ht r => ?_
    have ht' : t ∈ coords (2 : Fin 3) := by simpa using ht
    rcases mem_coords.1 ht' with rfl | rfl
    · exact mat_apply_of_fix fixe r
    · exact mat_apply_of_fix fixf r
  · have c1 : mat 3 F₃ (g₂ * g₁⁻¹) *ᵥ u = u' := by
      rw [map_mul, ← Matrix.mulVec_mulVec, ((mulVec_eq_iff g₁ _ _).1 a1).symm, b1]
    have c2 : mat 3 F₃ (g₂ * g₁⁻¹) *ᵥ w = w' := by
      rw [map_mul, ← Matrix.mulVec_mulVec, ((mulVec_eq_iff g₁ _ _).1 a2).symm, b2]
    rw [Submodule.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton, Matrix.mulVecLin_apply, c1, c2]

end Witt

theorem pairEmbed_negOne {i j : Fin 3} (hij : i ≠ j) :
    pairEmbed F₃ hij (Q3Z.negOne 2 F₃) = longInv F₃ 3 i * longInv F₃ 3 j := by
  rw [Q3Z.negOne_two_eq, map_mul]
  congr 1
  · exact spEmbed_longBlock (pairMap_injective hij) 0 (-1)
  · exact spEmbed_longBlock (pairMap_injective hij) 1 (-1)

theorem layer03_le_centralizer {Ω : Set (Subgroup G)} (hnonab : ∀ M ∈ Ω, ¬ Commutes M M)
    {Kf : Fin 4 → Subgroup G} (hK : IsMemberFrame Ω Kf) {Θ1 : StatedSp 3 F₃ →* G}
    (h1 : IsLabLift 3 Ω Kf 1 Θ1) {z₀ z₃ : G} (hz₀ : IsClassicalMember3 (Kf 0) z₀)
    (hz₃ : IsClassicalMember3 (Kf 3) z₃) :
    layerSub Ω Kf 0 3 ≤ Subgroup.centralizer ({z₀ * z₃} : Set G) := by
  have hij : (0 : Fin 3) ≠ 2 := by decide
  have e0 : (1 : Fin 4).succAbove (0 : Fin 3) = 0 := by decide
  have e2 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have hL := Frame.IsLabLift.layerSub_eq (by norm_num) hnonab hK h1 hij e0 e2
  have hz₀' : z₀ = Θ1 (longInv F₃ 3 0) :=
    eq_map_longInv_of_involution h1.loc.ker_le (by rw [h1.lab 0, e0]; exact hz₀.mem)
      hz₀.orderOf_eq_two
  have hz₃' : z₃ = Θ1 (longInv F₃ 3 2) :=
    eq_map_longInv_of_involution h1.loc.ker_le (by rw [h1.lab 2, e2]; exact hz₃.mem)
      hz₃.orderOf_eq_two
  have hx : z₀ * z₃ = Θ1 (pairEmbed F₃ hij (Q3Z.negOne 2 F₃)) := by
    rw [hz₀', hz₃', pairEmbed_negOne hij, map_mul]
  rw [hL]
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, hx]
  have hc : pairEmbed F₃ hij s * pairEmbed F₃ hij (Q3Z.negOne 2 F₃) =
      pairEmbed F₃ hij (Q3Z.negOne 2 F₃) * pairEmbed F₃ hij s := by
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp Q3Z.negOne_mem_center s]
  calc Θ1 (pairEmbed F₃ hij s) * Θ1 (pairEmbed F₃ hij (Q3Z.negOne 2 F₃))
      = Θ1 (pairEmbed F₃ hij s * pairEmbed F₃ hij (Q3Z.negOne 2 F₃)) := (map_mul _ _ _).symm
    _ = Θ1 (pairEmbed F₃ hij (Q3Z.negOne 2 F₃) * pairEmbed F₃ hij s) := by rw [hc]
    _ = Θ1 (pairEmbed F₃ hij (Q3Z.negOne 2 F₃)) * Θ1 (pairEmbed F₃ hij s) := map_mul _ _ _

theorem linked_visible_f4 [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω)
    (hnonab : ∀ M ∈ Ω, ¬ Commutes M M) {Kf : Fin 4 → Subgroup G} (hK : IsMemberFrame Ω Kf)
    {z₀ : G} {c : CCoreR 3 Ω (Kf 0) z₀} (l : LayerR c) (h0 : IsLabLift 3 Ω Kf 0 l.Θ)
    {Θ1 Θ3 : StatedSp 3 F₃ →* G} (h1 : IsLabLift 3 Ω Kf 1 Θ1) (h3 : IsLabLift 3 Ω Kf 3 Θ3)
    {z₃ : G} (hz₃ : IsClassicalMember3 (Kf 3) z₃) {M N : Subgroup G} (hM : M ∈ Ω)
    (hM1 : Commutes M (Kf 1)) (hM2 : Commutes M (Kf 2)) (hN : N ∈ Ω) (hN0 : Commutes N (Kf 0))
    (hN3 : Commutes N (Kf 3)) (hMN : ¬ Commutes M N) :
    Linked Ω (z₀ * z₃) (Kf 0) (Kf 3) ∧ Linked Ω (z₀ * z₃) (Kf 0) N ∧
      ∀ N' ∈ centralizingMembers Ω {z₀ * z₃, z₀}, Linked Ω (z₀ * z₃) (Kf 0) N' := by
  classical
  have hz₀ : IsClassicalMember3 (Kf 0) z₀ := c.hz
  have e03 : (0 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have hK3 : (planeGroup (stdPlane F₃ 3 2)).map l.Θ = Kf 3 := (h0.lab 2).trans (congrArg Kf e03)
  have hz₃' : z₃ = l.Θ (longInv F₃ 3 2) :=
    eq_map_longInv_of_involution l.ker_le (by rw [hK3]; exact hz₃.mem) hz₃.orderOf_eq_two
  have hL03 := layer03_le_centralizer hnonab hK h1 hz₀ hz₃
  have hMall : ∀ d : Fin 4, d ≠ 0 → d ≠ 3 → Commutes M (Kf d) := by
    intro d hd0 hd3
    fin_cases d
    · exact absurd rfl hd0
    · exact hM1
    · exact hM2
    · exact absurd rfl hd3
  have hMx : M ∈ centralizingMembers Ω {z₀ * z₃} := ⟨hM, (le_layerSub hM hMall).trans hL03⟩
  have hKx : Kf 0 ∈ centralizingMembers Ω {z₀ * z₃} :=
    ⟨hK.mem 0, le_centralizer_mul_of_le3 (isSubnormal_le hz₀.subnormal)
      (le_centralizer_of_commutes3 (hK.comm 0 3 (by decide)) hz₃.mem)⟩
  have hK3x : Kf 3 ∈ centralizingMembers Ω {z₀ * z₃} :=
    ⟨hK.mem 3, le_centralizer_mul_of_le3
      (le_centralizer_of_commutes3 (hK.comm 3 0 (by decide)) hz₀.mem)
      (isSubnormal_le hz₃.subnormal)⟩
  have hNx : N ∈ centralizingMembers Ω {z₀ * z₃} :=
    ⟨hN, le_centralizer_mul_of_le3 (le_centralizer_of_commutes3 hN0 hz₀.mem)
      (le_centralizer_of_commutes3 hN3 hz₃.mem)⟩
  have hnc0 : ¬ Commutes M (Kf 0) := by
    intro hc
    have := eq_fourth_of_commutes (m := 3) (by norm_num) hnonab hK h0 (c := 3) (by decide) hM hc
      (fun d hd3 hd0 => hMall d hd0 hd3)
    rw [this] at hMN
    exact hMN hN3.symm
  have hnc3 : ¬ Commutes M (Kf 3) := by
    intro hc
    have := eq_fourth_of_commutes (m := 3) (by norm_num) hnonab hK h3 (c := 0) (by decide) hM hc
      (fun d hd0 hd3 => hMall d hd0 hd3)
    rw [this] at hMN
    exact hMN hN0.symm
  have e1 : NCEdge Ω (z₀ * z₃) (Kf 0) M := ⟨hKx, hMx, fun hc => hnc0 hc.symm⟩
  have e2 : NCEdge Ω (z₀ * z₃) M N := ⟨hMx, hNx, hMN⟩
  have e3 : NCEdge Ω (z₀ * z₃) M (Kf 3) := ⟨hMx, hK3x, hnc3⟩
  have hL3 : Linked Ω (z₀ * z₃) (Kf 0) (Kf 3) := (Linked.single e1).trans (Linked.single e3)
  have hLN : Linked Ω (z₀ * z₃) (Kf 0) N := (Linked.single e1).trans (Linked.single e2)
  refine ⟨hL3, hLN, fun N' hN' => ?_⟩
  rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair] at hN'
  obtain ⟨hN'z, hN'w⟩ := hN'
  by_cases hN'K : N' = Kf 0
  · rw [hN'K]
    exact Relation.ReflTransGen.refl
  by_cases hN'3 : N' = Kf 3
  · rw [hN'3]
    exact hL3
  obtain ⟨P', hP', hN'P⟩ := l.exists_plane_of_ne hN'z hN'K
  have hN0z : N ∈ centralizingMembers Ω {z₀} := ⟨hN, le_centralizer_of_commutes3 hN0 hz₀.mem⟩
  have hN0K : N ≠ Kf 0 := by
    intro e
    rw [e] at hN0
    exact hnonab (Kf 0) (hK.mem 0) hN0
  obtain ⟨P₀, hP₀, hNP₀⟩ := l.exists_plane_of_ne hN0z hN0K
  have hP₀o : ∀ u ∈ P₀, ∀ v ∈ stdPlane F₃ 3 2, form u v = 0 :=
    (Frame.commutes_map_planeGroup_iff (by norm_num) l.ker_le hP₀
      (isHyperbolicPlane_stdPlane 2)).1 (by rw [← hNP₀, hK3]; exact hN3)
  have hle : planeGroup P' ≤ Subgroup.centralizer ({longInv F₃ 3 2} : Set (StatedSp 3 F₃)) :=
    (le_centralizer_iff_map3 l.Θ l.ker_le (layerKerCop l)
      (pow3_planeGroupR (by norm_num) hP') (longInv F₃ 3 2)).mpr (by
        rw [← hz₃', ← hN'P]
        exact hN'w)
  have hne : planeGroup P' ≠ planeGroup (stdPlane F₃ 3 2) := by
    intro e
    apply hN'3
    rw [hN'P, e, hK3]
  have hP'o : ∀ u ∈ P', ∀ v ∈ stdPlane F₃ 3 2, form u v = 0 :=
    (Q3Z.commute_planeGroup_iff Q3Z.gf3_two_ne_zero (by norm_num) hP'
      (isHyperbolicPlane_stdPlane 2)).1
      (commutes_planeGroup_stdPlane_of_le_centralizer Q3Z.gf3_two_ne_zero 2 hP' hle hne)
  obtain ⟨h, hh, hPh⟩ := exists_sp_fix_plane_two hP₀ hP' hP₀o hP'o
  have hconj : conjSub (l.Θ h) N = N' := by
    rw [hNP₀, conjSub_map l.Θ h, hN'P]
    congr 1
    rw [← hPh]
    exact (planeGroup_map_conj h P₀).symm
  have hy0 : l.Θ h * z₀ = z₀ * l.Θ h := l.commutes_K h hz₀.mem
  have hy3 : l.Θ h * z₃ = z₃ * l.Θ h := by
    rw [hz₃', ← map_mul, ← map_mul]
    refine congrArg l.Θ ?_
    exact (commute_suppGroup_compl (mem_suppGroup.2 (isSupp_longBlock 2 (-1))) hh).symm.eq
  have hyx : l.Θ h * (z₀ * z₃) * (l.Θ h)⁻¹ = z₀ * z₃ := by
    rw [mul_inv_eq_iff_eq_mul]
    calc l.Θ h * (z₀ * z₃) = (l.Θ h * z₀) * z₃ := by group
      _ = (z₀ * l.Θ h) * z₃ := by rw [hy0]
      _ = z₀ * (l.Θ h * z₃) := by group
      _ = z₀ * (z₃ * l.Θ h) := by rw [hy3]
      _ = z₀ * z₃ * l.Θ h := by group
  have hKy : conjSub (l.Θ h) (Kf 0) = Kf 0 :=
    conjSub_eq_of_forall_commute fun a ha => l.commutes_K h ha
  have := linked_conj hΩ.conjInvariant hyx hLN
  rw [hKy, hconj] at this
  exact this

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
