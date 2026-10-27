module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellUtil
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section Centrality

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

omit [Finite G] in
theorem Zfix_sup_aimg_le_centralizer (α : (S : Subgroup G) ≃* (S : Subgroup G)) :
    Zfix S ⊔ aimg (S : Subgroup G) α (Zfix S) ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
  sup_le (fun _ hz => Subgroup.mem_centralizer_iff.mpr fun _ hs => IsSeed.Zfix_central hz hs)
    (fun _ hz => Subgroup.mem_centralizer_iff.mpr fun _ hs => aimg_Zfix_central α hs hz)



namespace IsSeed

variable (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem normalizer_le_Mnorm {Z' : Subgroup G}
    (hZ'S : ∀ s ∈ (S : Subgroup G), ∀ z ∈ Z', s * z = z * s)
    (hnc : ¬ Hone S ≤ Subgroup.centralizer (Z' : Set G)) {y : G}
    (hy : y ∈ Subgroup.normalizer (Z' : Set G)) : y ∈ Mnorm S ρ := by
  by_contra hyM
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  rw [mem_Mnorm_iff hℓ] at hyM
  set Y : Subgroup G := Subgroup.normalizer (Z' : Set G) with hY
  have hSY : (S : Subgroup G) ≤ Y := by
    intro s hs
    have hsc : s ∈ Subgroup.centralizer (Z' : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz => (hZ'S s hs z hz).symm
    exact Subgroup.centralizer_le_normalizer _ hsc
  have h1 : rootGrp ℓ ≤ Y.map ρ := by rw [← hℓ]; exact Subgroup.map_mono hSY
  have h2 : rootGrp (ρ y • ℓ) ≤ Y.map ρ := by
    rw [rootGrp_smul_eq_map]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨u', hu', rfl⟩ := h1 hu
    exact ⟨y * u' * y⁻¹, Y.mul_mem (Y.mul_mem hy hu') (Y.inv_mem hy),
      by simp [MulAut.conj_apply, map_mul, map_inv]⟩
  have hsup := h.sup_core_eq_top (fun e => hyM e.symm) h1 h2
  apply hnc
  unfold Hone
  rw [Subgroup.normalClosure]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  obtain ⟨t, ht, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
  have hc : c ∈ Y ⊔ CFSG.pCore 2 G := by rw [hsup]; trivial
  obtain ⟨j, hj, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hc
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro z hz
  have ht' : q * t * q⁻¹ ∈ thompsonJ (S : Subgroup G) :=
    thompsonJ_conj_mem_sylow (core_le_sylow S hq) ht
  have hz' : j⁻¹ * z * j ∈ Z' := by
    have := (Subgroup.mem_normalizer_iff.mp (Y.inv_mem hj) z).mp hz
    simpa using this
  have hcomm := hZ'S _ (thompsonJ_le_self' _ ht') _ hz'
  calc z * (j * q * t * (j * q)⁻¹)
      = j * ((j⁻¹ * z * j) * (q * t * q⁻¹)) * j⁻¹ := by group
    _ = j * ((q * t * q⁻¹) * (j⁻¹ * z * j)) * j⁻¹ := by rw [← hcomm]
    _ = j * q * t * (j * q)⁻¹ * z := by group

theorem exists_Hone_not_mem_Mnorm : ∃ g ∈ Hone S, g ∉ Mnorm S ρ := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  obtain ⟨m, hm⟩ := exists_ne_point ℓ
  obtain ⟨s, hs⟩ := exists_smul_eq' ℓ m
  have hmap := h.Hone_map_eq_top
  have : s ∈ (Hone S).map ρ := by rw [hmap]; trivial
  obtain ⟨g, hg, rfl⟩ := this
  refine ⟨g, hg, fun hgM => hm ?_⟩
  rw [mem_Mnorm_iff hℓ] at hgM
  rw [← hs, hgM]

theorem aimg_commutator_eq_of_ne_bot (α : (S : Subgroup G) ≃* (S : Subgroup G)) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A)
    (hne : ⁅A, aimg (S : Subgroup G) α (Fcore G)⁆ ≠ ⊥) :
    ⁅A, aimg (S : Subgroup G) α (Fcore G)⁆ = aimg (S : Subgroup G) α (Zfix S) := by
  have hA1 : IsMaxElemAbelian (cj (S : Subgroup G) 1) A := by rwa [cj_one]
  have hne1 : ⁅A, tr (S : Subgroup G) α 1 (Fcore G)⁆ ≠ ⊥ := by rwa [tr_one]
  have := (h.tr_commutator_eq_of_ne_bot α 1 hA1 hne1).1
  rwa [tr_one, tr_one] at this

theorem aimg_commutator_le (α : (S : Subgroup G) ≃* (S : Subgroup G)) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) :
    ⁅A, aimg (S : Subgroup G) α (Fcore G)⁆ ≤ aimg (S : Subgroup G) α (Zfix S) := by
  have hA1 : IsMaxElemAbelian (cj (S : Subgroup G) 1) A := by rwa [cj_one]
  have := h.tr_commutator_A_Fcore_le α 1 hA1
  rwa [tr_one, tr_one] at this

theorem aimg_Zfix_le_Fcore (α : (S : Subgroup G) ≃* (S : Subgroup G)) :
    aimg (S : Subgroup G) α (Zfix S) ≤ Fcore G := by
  intro z hz
  exact h.mem_Fcore_of_central_involution (aimg_le hz) (fun t ht => (aimg_Zfix_central α ht hz).symm)
    ((isElemAbelian_iff.mp (isElemAbelian_aimg_Zfix α)).2 z hz)

theorem Zfix_le_Fcore : Zfix S ≤ Fcore G :=
  (inf_le_left : Zfix S ≤ Vmod G).trans (Vmod_le_Ecore.trans h.Ecore_le_Fcore)

theorem Zfix_sup_aimg_le_Fcore (α : (S : Subgroup G) ≃* (S : Subgroup G)) :
    Zfix S ⊔ aimg (S : Subgroup G) α (Zfix S) ≤ Fcore G :=
  sup_le h.Zfix_le_Fcore (h.aimg_Zfix_le_Fcore α)

end IsSeed

@[expose] def Bzero (A : Subgroup G) : Subgroup G := (A ⊓ CFSG.pCore 2 G) ⊔ Fcore G

@[expose] def Bone (S : Sylow 2 G) (α : (S : Subgroup G) ≃* (S : Subgroup G)) (A : Subgroup G) :
    Subgroup G :=
  aimg (S : Subgroup G) α (Fcore G) ⊔
    (Bzero A ⊓ Subgroup.centralizer ((aimg (S : Subgroup G) α (Fcore G) : Subgroup G) : Set G))

@[expose] def Ctr (S : Sylow 2 G) (α : (S : Subgroup G) ≃* (S : Subgroup G)) (A : Subgroup G)
    (g : G) : Subgroup G :=
  Bone S α A ⊓ Subgroup.centralizer ((tr (S : Subgroup G) α g (Fcore G) : Subgroup G) : Set G)

namespace IsSeed

variable (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem Bzero_isMax {A : Subgroup G} (hA : IsMaxElemAbelian (S : Subgroup G) A) :
    IsMaxElemAbelian (CFSG.pCore 2 G) (Bzero A) ∧ IsMaxElemAbelian (S : Subgroup G) (Bzero A) :=
  h.isMaxElemAbelian_core_sup_Fcore hA

theorem Bone_isMax (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) :
    IsMaxElemAbelian (S : Subgroup G) (Bone S α A) ∧ Bone S α A ≤ CFSG.pCore 2 G ∧
      IsMaxElemAbelian (CFSG.pCore 2 G) (Bone S α A) := by
  have h1 := h.isMaxElemAbelian_tr_Fcore_sup α 1 (A' := Bzero A)
    (by rw [cj_one]; exact (h.Bzero_isMax hA).2)
  rw [cj_one] at h1
  simp only [tr_one] at h1
  have hS : IsMaxElemAbelian (S : Subgroup G) (Bone S α A) := h1
  have hQ : Bone S α A ≤ CFSG.pCore 2 G :=
    sup_le (h.aimg_Fcore_le_core α hV) (inf_le_left.trans (h.Bzero_isMax hA).1.1)
  exact ⟨hS, hQ, isMaxElemAbelian_core_of_le hS hQ⟩

theorem Fcore_le_Bone (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) (A : Subgroup G) :
    Fcore G ≤ Bone S α A := by
  intro f hf
  apply Subgroup.mem_sup_right
  refine ⟨Subgroup.mem_sup_right hf, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  exact Fcore_commute_thompsonJ_core hf (h.aimg_Fcore_le_thompsonJ_core α hV hw)

omit [Field k] [Finite k] h in
theorem Bzero_normalized {A : Subgroup G} (hA : IsMaxElemAbelian (S : Subgroup G) A) {a : G}
    (ha : a ∈ A) {x : G} (hx : x ∈ Bzero A) : a * x * a⁻¹ ∈ Bzero A := by
  have : Bzero A ≤ cj (Bzero A) a := by
    refine sup_le (fun x hx => mem_cj.mpr ?_) (fun x hx => mem_cj.mpr ?_)
    · have hc : a * x = x * a := (isElemAbelian_iff.mp hA.2.1).1 a ha x hx.1
      have : a * x * a⁻¹ = x := by rw [hc]; group
      rw [this]
      exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right ((inferInstance : (Fcore G).Normal).conj_mem x hx a)
  exact mem_cj.mp (this hx)

omit [Field k] [Finite k] h in
theorem Bone_normalized (α : (S : Subgroup G) ≃* (S : Subgroup G)) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) {a : G} (ha : a ∈ A) {b : G}
    (hb : b ∈ Bone S α A) : a * b * a⁻¹ ∈ Bone S α A := by
  have : Bone S α A ≤ cj (Bone S α A) a := by
    refine sup_le (fun x hx => mem_cj.mpr ?_) (fun x hx => mem_cj.mpr ?_)
    · exact Subgroup.mem_sup_left (aimg_Fcore_normal_mem α (hA.1 ha) hx)
    · obtain ⟨hxB0, hxc⟩ := hx
      apply Subgroup.mem_sup_right
      refine ⟨Bzero_normalized hA ha hxB0, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hw' : a⁻¹ * w * a⁻¹⁻¹ ∈ aimg (S : Subgroup G) α (Fcore G) :=
        aimg_Fcore_normal_mem α ((S : Subgroup G).inv_mem (hA.1 ha)) hw
      have hcomm := Subgroup.mem_centralizer_iff.mp hxc _ hw'
      calc w * (a * x * a⁻¹) = a * ((a⁻¹ * w * a⁻¹⁻¹) * x) * a⁻¹ := by group
        _ = a * (x * (a⁻¹ * w * a⁻¹⁻¹)) * a⁻¹ := by rw [hcomm]
        _ = a * x * a⁻¹ * w := by group
  exact mem_cj.mp (this hb)

open scoped commutatorElement in
theorem commutator_A_Bone_le (α : (S : Subgroup G) ≃* (S : Subgroup G))
    {A : Subgroup G} (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) :
    ⁅A, Bone S α A⁆ ≤ Zfix S ⊔ aimg (S : Subgroup G) α (Zfix S) := by
  have hZZ := Zfix_sup_aimg_le_centralizer (S := S) α
  have hNV : ∀ n ∈ (S : Subgroup G), ∀ v ∈ Zfix S ⊔ aimg (S : Subgroup G) α (Zfix S),
      n * v * n⁻¹ ∈ Zfix S ⊔ aimg (S : Subgroup G) α (Zfix S) := fun n hn v hv =>
    mem_of_central_conj hZZ hn hv
  have hNV' : ∀ n ∈ (S : Subgroup G), ∀ v ∈ Zfix S, n * v * n⁻¹ ∈ Zfix S := fun n hn v hv =>
    mem_of_central_conj (fun z hz => Subgroup.mem_centralizer_iff.mpr fun s hs =>
      IsSeed.Zfix_central hz hs) hn hv
  have hB0 : ⁅A, Bzero A⁆ ≤ Zfix S := by
    refine commutator_sup_le hNV' (inf_le_left.trans hA.1) (Fcore_le_sylow (S := S)) ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha x hx
      have hc : a * x = x * a := (isElemAbelian_iff.mp hA.2.1).1 a ha x hx.1
      have : ⁅a, x⁆ = 1 := by
        simp only [commutatorElement_def]; rw [hc]; group
      rw [this]; exact one_mem _
    · rw [h.commutator_A_Fcore hA hAQ]
  refine commutator_sup_le hNV (aimg_le : aimg (S : Subgroup G) α (Fcore G) ≤ (S : Subgroup G))
    (inf_le_left.trans (h.Bzero_isMax hA).2.1) ?_ ?_
  · exact (h.aimg_commutator_le α hA).trans le_sup_right
  · exact ((Subgroup.commutator_mono le_rfl inf_le_left).trans hB0).trans le_sup_left

theorem tr_Fcore_le_core (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) (g : G) :
    tr (S : Subgroup G) α g (Fcore G) ≤ CFSG.pCore 2 G := by
  have h1 := cj_mono (g := g) (h.aimg_Fcore_le_core α hV)
  rw [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at h1
  exact h1

theorem tr_Fcore_le_thompsonJ_core (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) (g : G) :
    tr (S : Subgroup G) α g (Fcore G) ≤ thompsonJ (CFSG.pCore 2 G) := by
  have h1 := cj_mono (g := g) (h.aimg_Fcore_le_thompsonJ_core α hV)
  rw [cj_eq_self_of_normal (Y := thompsonJ (CFSG.pCore 2 G))] at h1
  exact h1

theorem Fcore_commute_tr (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) (g : G) {f w : G}
    (hf : f ∈ Fcore G) (hw : w ∈ tr (S : Subgroup G) α g (Fcore G)) : f * w = w * f :=
  (Fcore_commute_thompsonJ_core hf (h.tr_Fcore_le_thompsonJ_core α hV g hw)).symm

omit [Field k] [Finite k] h in
theorem cj_tr_Fcore_of_mem_thompsonJ_core (α : (S : Subgroup G) ≃* (S : Subgroup G)) (g : G)
    {a : G} (ha : a ∈ thompsonJ (CFSG.pCore 2 G)) {x : G}
    (hx : x ∈ tr (S : Subgroup G) α g (Fcore G)) :
    a * x * a⁻¹ ∈ tr (S : Subgroup G) α g (Fcore G) := by
  unfold tr at hx ⊢
  rw [mem_cj] at hx ⊢
  have hga : g * a * g⁻¹ ∈ thompsonJ (CFSG.pCore 2 G) := thompsonJ_conj_mem ha g
  have := aimg_Fcore_normal_mem α (core_le_sylow S (thompsonJ_le_self' _ hga)) hx
  have e : g * (a * x * a⁻¹) * g⁻¹ = (g * a * g⁻¹) * (g * x * g⁻¹) * (g * a * g⁻¹)⁻¹ := by group
  rw [e]
  exact this

open scoped commutatorElement in
theorem commutator_A_Bone_le_C (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) (g : G) :
    ⁅A, Bone S α A⁆ ≤ Ctr S α A g := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hmem : ⁅a, b⁆ ∈ (⁅A, Bone S α A⁆ : Subgroup G) := Subgroup.commutator_mem_commutator ha hb
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  · have h1 : a * b * a⁻¹ ∈ Bone S α A := Bone_normalized α hA ha hb
    have : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact mul_mem h1 ((Bone S α A).inv_mem hb)
  · have hF : ⁅a, b⁆ ∈ Fcore G :=
      h.Zfix_sup_aimg_le_Fcore α (h.commutator_A_Bone_le α hA hAQ hmem)
    exact (h.Fcore_commute_tr α hV g hF hw).symm

open scoped commutatorElement in
theorem cj_Ctr_eq (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) (g : G) {a : G}
    (ha : a ∈ A) : cj (Ctr S α A g) a = Ctr S α A g := by
  apply cj_eq_of_forall_mem
  intro x hx
  have hcomm : ⁅a, x⁆ ∈ Ctr S α A g :=
    h.commutator_A_Bone_le_C α hV hA hAQ g (Subgroup.commutator_mem_commutator ha hx.1)
  have : a * x * a⁻¹ = ⁅a, x⁆ * x := by simp only [commutatorElement_def]; group
  rw [this]
  exact mul_mem hcomm hx

theorem Ctr_le_centralizer_cj (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) (g : G) {a : G}
    (ha : a ∈ A) :
    Ctr S α A g ≤ Subgroup.centralizer ((cj (tr (S : Subgroup G) α g (Fcore G)) a : Subgroup G) : Set G) := by
  have h1 : Ctr S α A g ≤
      Subgroup.centralizer ((tr (S : Subgroup G) α g (Fcore G) : Subgroup G) : Set G) := inf_le_right
  have h2 := cj_mono (g := a) h1
  rw [h.cj_Ctr_eq α hV hA hAQ g ha, ← centralizer_cj] at h2
  exact h2

theorem Ctr_sup_isMax (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (g : G) :
    IsMaxElemAbelian (CFSG.pCore 2 G) (tr (S : Subgroup G) α g (Fcore G) ⊔ Ctr S α A g) := by
  obtain ⟨hBS, hBQ, hBQmax⟩ := h.Bone_isMax α hV hA
  have h1 := h.isMaxElemAbelian_tr_Fcore_sup α g (A' := Bone S α A)
    (h.isMaxElemAbelian_cj_of_core hBQmax g)
  have hQ : tr (S : Subgroup G) α g (Fcore G) ⊔ Ctr S α A g ≤ CFSG.pCore 2 G :=
    sup_le (h.tr_Fcore_le_core α hV g) (inf_le_left.trans hBQ)
  exact isMaxElemAbelian_core_of_le_cj (core_le_sylow S) h1 hQ

open scoped commutatorElement in
theorem tr_Zfix_eq_of_commutator_ne_bot (α : (S : Subgroup G) ≃* (S : Subgroup G)) (g x : G)
    {C : Subgroup G}
    (hA₁ : IsMaxElemAbelian (cj (S : Subgroup G) g)
      (cj (tr (S : Subgroup G) α g (Fcore G)) x ⊔ C))
    (hA₂ : IsMaxElemAbelian (cj (S : Subgroup G) (g * x)) (tr (S : Subgroup G) α g (Fcore G) ⊔ C))
    (hCX : ∀ c ∈ C, ∀ w ∈ tr (S : Subgroup G) α g (Fcore G), c * w = w * c)
    (hCX' : ∀ c ∈ C, ∀ w ∈ cj (tr (S : Subgroup G) α g (Fcore G)) x, c * w = w * c)
    (hne : ⁅tr (S : Subgroup G) α g (Fcore G), cj (tr (S : Subgroup G) α g (Fcore G)) x⁆ ≠ ⊥) :
    tr (S : Subgroup G) α g (Zfix S) = tr (S : Subgroup G) α (g * x) (Zfix S) := by
  have hX' : cj (tr (S : Subgroup G) α g (Fcore G)) x =
      tr (S : Subgroup G) α (g * x) (Fcore G) := by
    unfold tr; rw [cj_cj]
  have h1 : ⁅cj (tr (S : Subgroup G) α g (Fcore G)) x ⊔ C, tr (S : Subgroup G) α g (Fcore G)⁆ =
      ⁅cj (tr (S : Subgroup G) α g (Fcore G)) x, tr (S : Subgroup G) α g (Fcore G)⁆ := by
    apply le_antisymm
    · exact commutator_sup_of_commute (fun p hp c hc => (hCX' c hc p hp).symm) hCX
    · exact Subgroup.commutator_mono le_sup_left le_rfl
  have hne1 : ⁅cj (tr (S : Subgroup G) α g (Fcore G)) x ⊔ C,
      tr (S : Subgroup G) α g (Fcore G)⁆ ≠ ⊥ := by
    rw [h1, Subgroup.commutator_comm]; exact hne
  have e1 := (h.tr_commutator_eq_of_ne_bot α g hA₁ hne1).1
  rw [h1, Subgroup.commutator_comm] at e1
  have h2 : ⁅tr (S : Subgroup G) α g (Fcore G) ⊔ C, cj (tr (S : Subgroup G) α g (Fcore G)) x⁆ =
      ⁅tr (S : Subgroup G) α g (Fcore G), cj (tr (S : Subgroup G) α g (Fcore G)) x⁆ := by
    apply le_antisymm
    · exact commutator_sup_of_commute (fun p hp c hc => (hCX c hc p hp).symm) hCX'
    · exact Subgroup.commutator_mono le_sup_left le_rfl
  have hne2 : ⁅tr (S : Subgroup G) α g (Fcore G) ⊔ C,
      tr (S : Subgroup G) α (g * x) (Fcore G)⁆ ≠ ⊥ := by
    rw [← hX', h2]; exact hne
  have e2 := (h.tr_commutator_eq_of_ne_bot α (g * x) hA₂ hne2).1
  rw [← hX', h2] at e2
  exact e1.symm.trans e2

open scoped commutatorElement in
theorem commutator_tr_cj_eq_bot (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) {g : G}
    (hgM : g ∉ Mnorm S ρ)
    (hN : ∀ y ∈ Subgroup.normalizer
      ((aimg (S : Subgroup G) α (Zfix S) : Subgroup G) : Set G), y ∈ Mnorm S ρ)
    {x : G} (hx : x ∈ A) (hxQ : x ∉ CFSG.pCore 2 G) :
    ⁅tr (S : Subgroup G) α g (Fcore G), cj (tr (S : Subgroup G) α g (Fcore G)) x⁆ = ⊥ := by
  by_contra hne
  have hxS : x ∈ (S : Subgroup G) := hA.1 hx
  have hXC := h.Ctr_sup_isMax α hV hA g
  have hCx := h.cj_Ctr_eq α hV hA hAQ g hx
  have hA₂ : IsMaxElemAbelian (cj (S : Subgroup G) (g * x))
      (tr (S : Subgroup G) α g (Fcore G) ⊔ Ctr S α A g) :=
    h.isMaxElemAbelian_cj_of_core hXC (g * x)
  have hA₁ : IsMaxElemAbelian (cj (S : Subgroup G) g)
      (cj (tr (S : Subgroup G) α g (Fcore G)) x ⊔ Ctr S α A g) := by
    have h1 := isMaxElemAbelian_cj x hXC
    rw [cj_eq_self_of_normal (Y := CFSG.pCore 2 G), cj_sup, hCx] at h1
    exact h.isMaxElemAbelian_cj_of_core h1 g
  have hCX : ∀ c ∈ Ctr S α A g, ∀ w ∈ tr (S : Subgroup G) α g (Fcore G), c * w = w * c :=
    fun c hc w hw => (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm
  have hCX' : ∀ c ∈ Ctr S α A g, ∀ w ∈ cj (tr (S : Subgroup G) α g (Fcore G)) x,
      c * w = w * c := fun c hc w hw =>
    (Subgroup.mem_centralizer_iff.mp (h.Ctr_le_centralizer_cj α hV hA hAQ g hx hc) w hw).symm
  have hZ := h.tr_Zfix_eq_of_commutator_ne_bot α g x hA₁ hA₂ hCX hCX' hne
  have hcj : cj (cj (aimg (S : Subgroup G) α (Zfix S)) g) x =
      cj (aimg (S : Subgroup G) α (Zfix S)) g := by
    have : cj (cj (aimg (S : Subgroup G) α (Zfix S)) g) x =
        cj (aimg (S : Subgroup G) α (Zfix S)) (g * x) := cj_cj
    rw [this]
    exact hZ.symm
  have hmem := mem_normalizer_of_cj_cj_eq hcj
  exact hgM (h.mem_Mnorm_of_conj_mem hxS hxQ (hN _ hmem))

open scoped commutatorElement in
theorem tr_Fcore_le_Bone (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) {g : G}
    (hgM : g ∉ Mnorm S ρ)
    (hN : ∀ y ∈ Subgroup.normalizer
      ((aimg (S : Subgroup G) α (Zfix S) : Subgroup G) : Set G), y ∈ Mnorm S ρ) :
    tr (S : Subgroup G) α g (Fcore G) ≤ Bone S α A := by
  obtain ⟨hBS, hBQ, hBQmax⟩ := h.Bone_isMax α hV hA
  have hXQ := h.tr_Fcore_le_core α hV g
  have hXC := h.Ctr_sup_isMax α hV hA g
  have hXel : CFSG.Open.IsElemAbelian 2 (tr (S : Subgroup G) α g (Fcore G)) :=
    isElemAbelian_tr isElemAbelian_Fcore
  have hCle : Ctr S α A g ≤ Bone S α A := inf_le_left
  have hCX : ∀ c ∈ Ctr S α A g, ∀ w ∈ tr (S : Subgroup G) α g (Fcore G), c * w = w * c :=
    fun c hc w hw => (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm
  have hcomm : ∀ a ∈ A, ∀ w ∈ tr (S : Subgroup G) α g (Fcore G),
      ∀ y ∈ cj (tr (S : Subgroup G) α g (Fcore G)) a, w * y = y * w := by
    intro a ha w hw y hy
    by_cases haQ : a ∈ CFSG.pCore 2 G
    · have haJ : a ∈ thompsonJ (CFSG.pCore 2 G) :=
        maxElem_le_thompsonJ (h.Bzero_isMax hA).1 (Subgroup.mem_sup_left ⟨ha, haQ⟩)
      have hcjX : cj (tr (S : Subgroup G) α g (Fcore G)) a = tr (S : Subgroup G) α g (Fcore G) :=
        cj_eq_of_forall_mem fun z hz => cj_tr_Fcore_of_mem_thompsonJ_core α g haJ hz
      rw [hcjX] at hy
      exact (isElemAbelian_iff.mp hXel).1 w hw y hy
    · exact mul_comm_of_commutator_eq_bot
        (h.commutator_tr_cj_eq_bot α hV hA hAQ hgM hN ha haQ) hw hy
  have hXa : ∀ a ∈ A, cj (tr (S : Subgroup G) α g (Fcore G)) a ≤
      tr (S : Subgroup G) α g (Fcore G) ⊔ Ctr S α A g := by
    intro a ha
    refine maxElem_le_of_commute hXC ?_ (isElemAbelian_cj hXel a) ?_
    · have h1 := cj_mono (g := a) hXQ
      rw [cj_eq_self_of_normal (Y := CFSG.pCore 2 G)] at h1
      exact h1
    · intro y hy u hu
      obtain ⟨w, hw, c, hc, rfl⟩ := mem_sup_of_commute
        (fun x hx c hc => (hCX c hc x hx).symm) hu
      have h1 : w * y = y * w := hcomm a ha w hw y hy
      have h2 : y * c = c * y :=
        Subgroup.mem_centralizer_iff.mp (h.Ctr_le_centralizer_cj α hV hA hAQ g ha hc) y hy
      calc y * (w * c) = (y * w) * c := by group
        _ = (w * y) * c := by rw [h1]
        _ = w * (y * c) := by group
        _ = w * (c * y) := by rw [h2]
        _ = w * c * y := by group
  have hNbot : ⁅Bone S α A, tr (S : Subgroup G) α g (Fcore G)⁆ = ⊥ := by
    by_contra hne
    have hBg : IsMaxElemAbelian (cj (S : Subgroup G) g) (Bone S α A) :=
      h.isMaxElemAbelian_cj_of_core hBQmax g
    have e := (h.tr_commutator_eq_of_ne_bot α g hBg hne).1
    have hinv : ∀ a ∈ A, cj ⁅Bone S α A, tr (S : Subgroup G) α g (Fcore G)⁆ a =
        ⁅Bone S α A, tr (S : Subgroup G) α g (Fcore G)⁆ := by
      intro a ha
      have h1 : cj ⁅Bone S α A, tr (S : Subgroup G) α g (Fcore G)⁆ a =
          ⁅cj (Bone S α A) a, cj (tr (S : Subgroup G) α g (Fcore G)) a⁆ := cj_commutator
      have h2 : cj (Bone S α A) a = Bone S α A :=
        cj_eq_of_forall_mem fun b hb => Bone_normalized α hA ha hb
      have hle : cj ⁅Bone S α A, tr (S : Subgroup G) α g (Fcore G)⁆ a ≤
          ⁅Bone S α A, tr (S : Subgroup G) α g (Fcore G)⁆ := by
        rw [h1, h2]
        calc ⁅Bone S α A, cj (tr (S : Subgroup G) α g (Fcore G)) a⁆
            ≤ ⁅Bone S α A, tr (S : Subgroup G) α g (Fcore G) ⊔ Ctr S α A g⁆ :=
              Subgroup.commutator_mono le_rfl (hXa a ha)
          _ = ⁅tr (S : Subgroup G) α g (Fcore G) ⊔ Ctr S α A g, Bone S α A⁆ :=
              Subgroup.commutator_comm _ _
          _ ≤ ⁅tr (S : Subgroup G) α g (Fcore G), Bone S α A⁆ :=
              commutator_sup_of_commute (fun p hp c hc => (hCX c hc p hp).symm)
                (fun c hc b hb => (isElemAbelian_iff.mp hBS.2.1).1 c (hCle hc) b hb)
          _ = ⁅Bone S α A, tr (S : Subgroup G) α g (Fcore G)⁆ := Subgroup.commutator_comm _ _
      exact cj_eq_of_le hle
    obtain ⟨a, ha, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
    have hcj : cj (cj (aimg (S : Subgroup G) α (Zfix S)) g) a =
        cj (aimg (S : Subgroup G) α (Zfix S)) g := by
      have := hinv a ha
      rw [e] at this
      exact this
    exact hgM (h.mem_Mnorm_of_conj_mem (hA.1 ha) haQ (hN _ (mem_normalizer_of_cj_cj_eq hcj)))
  exact maxElem_le_of_commute hBQmax hXQ hXel fun y hy b hb =>
    (mul_comm_of_commutator_eq_bot hNbot hb hy).symm

theorem exists_core_max_not_commute (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) :
    ∃ A₀ : Subgroup G, IsMaxElemAbelian (CFSG.pCore 2 G) A₀ ∧
      ⁅A₀, aimg (S : Subgroup G) α (Fcore G)⁆ ≠ ⊥ := by
  by_contra hall
  push Not at hall
  apply hF
  have hle : aimg (S : Subgroup G) α (Fcore G) ≤ Fcore G := by
    intro f hf
    have hfJ : f ∈ thompsonJ (CFSG.pCore 2 G) := h.aimg_Fcore_le_thompsonJ_core α hV hf
    refine mem_centerTorsion_iff.mpr ⟨hfJ, fun k hk => ?_,
      (isElemAbelian_iff.mp (isElemAbelian_aimg α (isElemAbelian_Fcore (G := G)))).2 f hf⟩
    have hcent : thompsonJ (CFSG.pCore 2 G) ≤ Subgroup.centralizer (({f} : Set G)) := by
      refine thompsonJ_le_of_forall fun A₀ hA₀ a ha => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (mul_comm_of_commutator_eq_bot (hall A₀ hA₀) ha hf).symm
    exact (Subgroup.mem_centralizer_iff.mp (hcent hk) f (Set.mem_singleton f)).symm
  exact Subgroup.eq_of_le_of_card_ge hle (card_aimg (Fcore_le_sylow (S := S))).ge

open scoped commutatorElement in
theorem contained_translate_fixed_space_centrality (α : (S : Subgroup G) ≃* (S : Subgroup G))
    (hV : aimg (S : Subgroup G) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (S : Subgroup G) α (Fcore G) ≠ Fcore G) :
    aimg (S : Subgroup G) α (Zfix S) ≤ Hone S ⊓ Subgroup.centralizer (Hone S : Set G) := by
  classical
  by_contra hcon
  have hZT : Zfix S ≤ thompsonJ (S : Subgroup G) :=
    h.Zfix_le_Fcore.trans (Fcore_le_thompsonJ.trans h.thompsonJ_core_le_thompsonJ_sylow)
  have hZaT : aimg (S : Subgroup G) α (Zfix S) ≤ thompsonJ (S : Subgroup G) := by
    have := aimg_mono (S := (S : Subgroup G)) (α := α) hZT
    rwa [aimg_thompsonJ] at this
  have hZaH : aimg (S : Subgroup G) α (Zfix S) ≤ Hone S :=
    hZaT.trans Subgroup.le_normalClosure
  have hnc : ¬ Hone S ≤ Subgroup.centralizer ((aimg (S : Subgroup G) α (Zfix S) : Subgroup G) : Set G) := by
    intro hle
    apply hcon
    exact le_inf hZaH (Subgroup.le_centralizer_iff.mp hle)
  have hZaS : ∀ s ∈ (S : Subgroup G), ∀ z ∈ aimg (S : Subgroup G) α (Zfix S), s * z = z * s :=
    fun s hs z hz => aimg_Zfix_central α hs hz
  have hN : ∀ y ∈ Subgroup.normalizer ((aimg (S : Subgroup G) α (Zfix S) : Subgroup G) : Set G),
      y ∈ Mnorm S ρ := fun y hy => h.normalizer_le_Mnorm hZaS hnc hy
  obtain ⟨g, hgH, hgM⟩ := h.exists_Hone_not_mem_Mnorm
  obtain ⟨A, hA, hAQ⟩ := h.exists_max_outside
  have hXB := h.tr_Fcore_le_Bone α hV hA hAQ hgM hN
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  have hFa : aimg (S : Subgroup G) α (Fcore G) = cj (tr (S : Subgroup G) α g (Fcore G)) g⁻¹ := by
    unfold tr; rw [cj_inv_cj]
  have hAX : ⁅A, tr (S : Subgroup G) α g (Fcore G)⁆ ≤ Fcore G :=
    calc ⁅A, tr (S : Subgroup G) α g (Fcore G)⁆ ≤ ⁅A, Bone S α A⁆ :=
          Subgroup.commutator_mono le_rfl hXB
      _ ≤ Zfix S ⊔ aimg (S : Subgroup G) α (Zfix S) := h.commutator_A_Bone_le α hA hAQ
      _ ≤ Fcore G := h.Zfix_sup_aimg_le_Fcore α
  have hcjA : ⁅cj A g⁻¹, aimg (S : Subgroup G) α (Fcore G)⁆ ≤ Fcore G := by
    have h1 : ⁅cj A g⁻¹, aimg (S : Subgroup G) α (Fcore G)⁆ =
        cj ⁅A, tr (S : Subgroup G) α g (Fcore G)⁆ g⁻¹ := by
      rw [hFa, cj_commutator]
    rw [h1]
    calc cj ⁅A, tr (S : Subgroup G) α g (Fcore G)⁆ g⁻¹ ≤ cj (Fcore G) g⁻¹ := cj_mono hAX
      _ = Fcore G := cj_eq_self_of_normal
  have hTFa := h.commutator_thompsonJ_aimg_Fcore α
  have hTnorm : ∀ t ∈ thompsonJ (S : Subgroup G),
      t ∈ Subgroup.normalizer ((Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G) : Subgroup G) : Set G) := by
    intro t ht
    refine mem_normalizer_sup_of_commutator (mem_normalizer_of_normal _ t) fun w hw => ?_
    have h1 : ⁅t, w⁆ ∈ (⁅thompsonJ (S : Subgroup G), aimg (S : Subgroup G) α (Fcore G)⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator ht hw
    rw [hTFa] at h1
    exact h.aimg_Zfix_le_Fcore α h1
  have hAnorm : ∀ y ∈ cj A g⁻¹,
      y ∈ Subgroup.normalizer ((Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G) : Subgroup G) : Set G) := by
    intro y hy
    refine mem_normalizer_sup_of_commutator (mem_normalizer_of_normal _ y) fun w hw => ?_
    exact hcjA (Subgroup.commutator_mem_commutator hy hw)
  have hJsup : Subgroup.normalizer ((Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G) : Subgroup G) : Set G) ⊔
      CFSG.pCore 2 G = ⊤ := by
    obtain ⟨hmapA, -⟩ := h.max_outside hA hAQ
    have hne : ℓ ≠ ρ g • ℓ := fun e => hgM ((mem_Mnorm_iff hℓ).mpr e.symm)
    refine h.sup_core_eq_top hne ?_ ?_
    · rw [← hℓ, ← hmapA]
      exact Subgroup.map_mono fun a ha => hTnorm a (maxElem_le_thompsonJ hA ha)
    · rw [rootGrp_smul_eq_map, ← hℓ, ← hmapA]
      rintro _ ⟨u, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨g * a * g⁻¹, hAnorm _ ?_, by simp [MulAut.conj_apply, map_mul, map_inv]⟩
      rw [mem_cj]
      simpa [mul_assoc] using ha
  have hH1 : Hone S ≤ Subgroup.normalizer
      ((Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G) : Subgroup G) : Set G) :=
    Hone_le_of_sup_core_eq_top (fun t ht => hTnorm t ht) hJsup
  have hZaCent : aimg (S : Subgroup G) α (Zfix S) ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
    fun z hz => Subgroup.mem_centralizer_iff.mpr fun s hs => aimg_Zfix_central α hs hz
  have hRle : thompsonJ (CFSG.pCore 2 G) ≤ thompsonJ (S : Subgroup G) :=
    h.thompsonJ_core_le_thompsonJ_sylow
  have hupper : ⁅thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G)⁆ ≤
      aimg (S : Subgroup G) α (Zfix S) := by
    refine commutator_sup_le (N := (S : Subgroup G))
      (fun n hn v hv => mem_of_central_conj hZaCent hn hv) (Fcore_le_sylow (S := S))
      (aimg_le : aimg (S : Subgroup G) α (Fcore G) ≤ (S : Subgroup G)) ?_ ?_
    · rw [commutator_eq_bot_of_commute fun r hr f hf =>
        (Fcore_commute_thompsonJ_core hf hr)]
      exact bot_le
    · rw [← hTFa]
      exact Subgroup.commutator_mono hRle le_rfl
  have hlower : aimg (S : Subgroup G) α (Zfix S) ≤
      ⁅thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G)⁆ := by
    obtain ⟨A₀, hA₀Q, hA₀ne⟩ := h.exists_core_max_not_commute α hV hF
    have hA₀S := h.max_core_facts.1 A₀ hA₀Q
    have e := h.aimg_commutator_eq_of_ne_bot α hA₀S hA₀ne
    rw [← e]
    exact Subgroup.commutator_mono (maxElem_le_thompsonJ hA₀Q) le_sup_right
  have hRW : ⁅thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G)⁆ =
      aimg (S : Subgroup G) α (Zfix S) := le_antisymm hupper hlower
  have hHZ : ∀ y ∈ Hone S,
      y ∈ Subgroup.normalizer ((aimg (S : Subgroup G) α (Zfix S) : Subgroup G) : Set G) := by
    intro y hy
    have hyW : cj (Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G)) y =
        Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G) := by
      apply cj_eq_of_forall_mem
      intro x hx
      exact (Subgroup.mem_normalizer_iff.mp (hH1 hy) x).mp hx
    have h1 : cj ⁅thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G)⁆ y =
        ⁅thompsonJ (CFSG.pCore 2 G), Fcore G ⊔ aimg (S : Subgroup G) α (Fcore G)⁆ := by
      rw [cj_commutator, cj_eq_self_of_normal (Y := thompsonJ (CFSG.pCore 2 G)), hyW]
    rw [hRW] at h1
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : x ∈ cj (aimg (S : Subgroup G) α (Zfix S)) y := by rw [h1]; exact hx
      exact mem_cj.mp this
    · intro hx
      have : x ∈ cj (aimg (S : Subgroup G) α (Zfix S)) y := mem_cj.mpr hx
      rwa [h1] at this
  exact hgM (hN g (hHZ g hgH))

end IsSeed

end Centrality

end CFSG.QuasithinUnique.Setup.Campbell
