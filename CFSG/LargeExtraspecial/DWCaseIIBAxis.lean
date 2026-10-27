module

public import CFSG.LargeExtraspecial.DWCaseIIGBasic
public import CFSG.LargeExtraspecial.DW2AStruct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}

variable (S) in
@[expose] noncomputable def axisA (A : Subgroup G) (g : G) : Submodule (ZMod 2) S.Qt :=
  S.clSub (A ⊓ conjSub A g)

theorem finiteDimensional_Qt : FiniteDimensional (ZMod 2) S.Qt := by
  have : Finite (Additive S.Q) := inferInstanceAs (Finite S.Q)
  exact Module.Finite.of_finite

namespace MaxEA

variable [IsElementaryAbelian 2 A] (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
  (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)

omit [Finite G] [IsElementaryAbelian 2 A] in
include hII in
theorem cl_conj_mem_clSub {h : G} (hh : h * S.z * h⁻¹ ∈ S.QG) :
    S.cl (h * S.z * h⁻¹) ∈ S.clSub A :=
  S.cl_mem_clSub (hII h hh) hh

omit [Finite G] [IsElementaryAbelian 2 A] in
include hII in
theorem spanD_le_clSub : spanD S ≤ S.clSub A := by
  rw [spanD, Submodule.span_le]
  rintro _ ⟨h, hh, rfl⟩
  exact cl_conj_mem_clSub hII hh

include hII in
theorem q_spanD : ∀ v ∈ spanD S, S.q v = 0 := fun _ hv => q_clSub (spanD_le_clSub hII hv)

omit [Finite G] [IsElementaryAbelian 2 A] in
theorem conjSub_le_Qa (hA : MaxEA S A) (g : G) : conjSub A g ≤ S.Qa g := by
  rw [Setting.Qa_eq_map]
  exact Subgroup.map_mono hA.le_QG

omit [IsElementaryAbelian 2 A] in
theorem mem_Lbar {g : G} {t : S.O} :
    t ∈ S.Lbar g ↔ ∃ k, ∃ hk : k ∈ S.L0 g, S.ρ ⟨k, hk.2⟩ = t := by
  constructor
  · rintro ⟨⟨k, hkM⟩, hk, rfl⟩
    exact ⟨k, mem_subgroupOf.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk.2⟩, mem_subgroupOf.mpr hk, rfl⟩

omit [Finite G] [IsElementaryAbelian 2 A] in
theorem commute_of_mem_L0 {g k : G} (hk : k ∈ S.L0 g) :
    k * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * k :=
  mem_centralizer_singleton_iff.mp ((S.conjBy g).QG_le_M hk.1)

omit [IsElementaryAbelian 2 A] in
theorem Lbar_apply_cl {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (ht : t ∈ S.Lbar g) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  obtain ⟨k, hk, rfl⟩ := mem_Lbar.mp ht
  rw [S.ρ_cl _ hxQ]
  change S.cl (k * (g * S.z * g⁻¹) * k⁻¹) = _
  rw [commute_of_mem_L0 hk, mul_inv_cancel_right]

omit [IsElementaryAbelian 2 A] in
theorem ρ_cl_sub {k : G} (hk : k ∈ S.M) {a : G} (ha : a ∈ S.QG) :
    ((S.ρ ⟨k, hk⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a) - S.cl a =
      S.cl (k * a * k⁻¹ * a⁻¹) := by
  rw [S.ρ_cl _ ha, S.cl_mul (S.conj_mem_QG hk ha) (S.QG.inv_mem ha), S.cl_inv ha,
    sub_eq_add_neg, ZModModule.neg_eq_self]

variable {g : G} (hxA : g * S.z * g⁻¹ ∈ A) (hxz : g * S.z * g⁻¹ ≠ S.z)

include hA hM hII hxA hxz

omit hM hII hxz in
theorem cl_mem_axisA : S.cl (g * S.z * g⁻¹) ∈ axisA S A g :=
  S.cl_mem_clSub ⟨hxA, conj_mem_conjSub hA.z_mem⟩ (hA.le_QG hxA)

omit hII in
theorem z_mem_conjSub : S.z ∈ conjSub A g := by
  have := z_mem_conjSub_of_mem (isMbarInvariant_clSub hM) (hA.le_QG hxA)
    (S.cl_mem_clSub hxA (hA.le_QG hxA)) hxz
  rwa [hA.clPre_clSub] at this


omit hII in
theorem conjSub_le_M : conjSub A g ≤ S.M := by
  have := conjSub_le_M_of_mem (hW := isMbarInvariant_clSub hM) (fun v hv => q_clSub hv)
    (hA.le_QG hxA) (S.cl_mem_clSub hxA (hA.le_QG hxA)) hxz
  rwa [hA.clPre_clSub] at this

theorem fix_Abar_iff {u : S.Qt} (hu : u ∈ S.clSub A) :
    (∀ t ∈ Abar S A g, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) ↔ u ∈ axisA S A g := by
  have := fix_iff_mem_clSub_inf (isMbarInvariant_clSub hM) (fun h hh => cl_conj_mem_clSub hII hh)
    (fun v hv => q_clSub hv) (hA.le_QG hxA) (S.cl_mem_clSub hxA (hA.le_QG hxA)) hxz hu
  rwa [hA.clPre_clSub] at this

theorem Abar_sub_mem_span {t : S.O} (ht : t ∈ Abar S A g) {w : S.Qt} (hw : w ∈ S.clSub A) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨a, ha, rfl⟩ := mem_Abar.mp ht
  have ha' : a ∈ conjSub (S.clPre (S.clSub A)) g := by rw [hA.clPre_clSub]; exact ha.1
  exact ρ_sub_mem_span (isMbarInvariant_clSub hM) (fun h hh => cl_conj_mem_clSub hII hh)
    (fun v hv => q_clSub hv) (hA.le_QG hxA) (S.cl_mem_clSub hxA (hA.le_QG hxA)) hxz ha' hw

theorem exists_Abar_eq (φ : Module.Dual (ZMod 2) (S.clSub A))
    (hφ : ∀ w : S.clSub A, (w : S.Qt) ∈ axisA S A g → φ w = 0) :
    ∃ t ∈ Abar S A g, ∀ w : S.clSub A,
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + φ w • S.cl (g * S.z * g⁻¹) := by
  have := finiteDimensional_Qt (S := S)
  set c := S.cl (g * S.z * g⁻¹)
  set T := (Abar S A g).map S.O.subtype
  have hc0 : c ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff (hA.le_QG hxA)).mp h with h1 | h1
    · exact S.s12_conj_z_ne_one g h1
    · exact hxz h1
  have hcW : c ∈ S.clSub A := S.cl_mem_clSub hxA (hA.le_QG hxA)
  have hTW : ∀ t ∈ T, ∀ w ∈ S.clSub A, t w - w ∈ ZMod 2 ∙ c := by
    rintro _ ⟨t, ht, rfl⟩ w hw
    exact hA.Abar_sub_mem_span hM hII hxA hxz ht hw
  have hTc : ∀ t ∈ T, t c = c := by
    intro t ht
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp (hTW t ht c hcW)
    rcases zmod2_cases μ with rfl | rfl
    · rw [zero_smul, eq_comm, sub_eq_zero] at hμ
      exact hμ
    · exfalso
      rw [one_smul, eq_comm, sub_eq_iff_eq_add, add_self_zmod2] at hμ
      exact hc0 ((LinearEquiv.map_eq_zero_iff t).mp hμ)
  obtain ⟨t, ⟨τ, hτ, rfl⟩, htw⟩ := exists_eq_add_smul_of_dual hc0 hTc hTW φ fun w hw => by
    refine hφ w ((hA.fix_Abar_iff hM hII hxA hxz w.2).mp fun t ht => ?_)
    exact hw.2 _ ⟨t, ht, rfl⟩
  exact ⟨τ, hτ, htw⟩

theorem axisA_sup_spanD : axisA S A g ⊔ spanD S = S.clSub A := by
  have := finiteDimensional_Qt (S := S)
  have hle : axisA S A g ⊔ spanD S ≤ S.clSub A :=
    sup_le (S.clSub_mono inf_le_left) (spanD_le_clSub hII)
  by_contra hne
  set P : Submodule (ZMod 2) (S.clSub A) := (axisA S A g ⊔ spanD S).comap (S.clSub A).subtype
  have hP : P < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hle fun v hv => ?_)
    have : (⟨v, hv⟩ : S.clSub A) ∈ P := by rw [h]; exact Submodule.mem_top
    exact this
  obtain ⟨φ, hφ0, hPφ⟩ := P.exists_le_ker_of_lt_top hP
  obtain ⟨t, ht, htw⟩ := hA.exists_Abar_eq hM hII hxA hxz φ fun w hw =>
    hPφ (show w ∈ P from Submodule.mem_sup_left hw)
  have hφD : ∀ w : S.clSub A, (w : S.Qt) ∈ spanD S → φ w = 0 := fun w hw =>
    hPφ (show w ∈ P from Submodule.mem_sup_right hw)
  have ht1 : t = 1 := by
    refine hA.eq_one_of_fix_of_sub_mem hM isMbarInvariant_spanD (Abar_le_Mbar A g ht)
      (fun w hw => ?_) fun v hv => ?_
    · have := htw ⟨w, spanD_le_clSub hII hw⟩
      rwa [hφD _ hw, zero_smul, add_zero] at this
    · have := htw ⟨v, hv⟩
      simp only at this
      rw [this, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (cl_conj_mem_spanD (hA.le_QG hxA))
  apply hφ0
  ext w
  have h1 := htw w
  rw [ht1] at h1
  change (w : S.Qt) = w + φ w • S.cl (g * S.z * g⁻¹) at h1
  have h2 : φ w • S.cl (g * S.z * g⁻¹) = 0 := by
    have := congrArg (· - (w : S.Qt)) h1
    simpa using this.symm
  rcases zmod2_cases (φ w) with h | h
  · rw [h]
    rfl
  · exfalso
    rw [h, one_smul, S.cl_eq_zero_iff (hA.le_QG hxA)] at h2
    rcases h2 with h2 | h2
    · exact S.s12_conj_z_ne_one g h2
    · exact hxz h2

omit hxA hxz in
theorem mem_conjSub_of_mem_Qa' {y : G} (hyQ : y ∈ S.Qa g) (hy : y ∈ A) : y ∈ conjSub A g := by
  have := mem_conjSub_of_mem_Qa (isMbarInvariant_clSub hM)
    (fun h hh => cl_conj_mem_clSub hII hh) hyQ (by rw [hA.clPre_clSub]; exact hy)
  rwa [hA.clPre_clSub] at this

omit hxz in
theorem Lbar_sub_mem_axisA {t : S.O} (ht : t ∈ S.Lbar g) {v : S.Qt} (hv : v ∈ S.clSub A) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ axisA S A g := by
  obtain ⟨k, hk, rfl⟩ := mem_Lbar.mp ht
  obtain ⟨a, haA, haQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [ρ_cl_sub hk.2 haQ]
  have hbA : k * a * k⁻¹ * a⁻¹ ∈ A :=
    A.mul_mem ((mem_normalizer_iff.mp (hM hk.2) a).mp haA) (A.inv_mem haA)
  have haM : a ∈ (S.conjBy g).M := by
    rw [(S.conjBy g).mem_M_iff, Setting.conjBy_z]
    exact comm_of_mem haA hxA
  have hbQ : k * a * k⁻¹ * a⁻¹ ∈ S.Qa g := by
    rw [show k * a * k⁻¹ * a⁻¹ = k * (a * k⁻¹ * a⁻¹) by group]
    exact (S.Qa g).mul_mem hk.1 ((S.conjBy g).conj_mem_QG haM ((S.Qa g).inv_mem hk.1))
  exact S.cl_mem_clSub ⟨hbA, hA.mem_conjSub_of_mem_Qa' hM hII hbQ hbA⟩ (hA.le_QG hbA)

omit [IsElementaryAbelian 2 A] hM hII hxA hxz in
theorem Lbar_sub_mem_span {t : S.O} (ht : t ∈ S.Lbar g) {v : S.Qt} (hv : v ∈ axisA S A g) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ ZMod 2 ∙ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨k, hk, rfl⟩ := mem_Lbar.mp ht
  obtain ⟨b, hb, hbQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [ρ_cl_sub hk.2 hbQ]
  rcases (S.conjBy g).commutator_eq_one_or_z hk.1 (hA.conjSub_le_Qa g hb.2) with h | h
  · rw [h, S.cl_one]
    exact zero_mem _
  · rw [h, Setting.conjBy_z]
    exact Submodule.mem_span_singleton_self _

theorem Lbar_eq_one_of_fix_spanD {t : S.O} (ht : t ∈ S.Lbar g)
    (hfix : ∀ w ∈ spanD S, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) : t = 1 := by
  refine hA.eq_one_of_fix_of_sub_mem hM isMbarInvariant_spanD (S.Lbar_le_Mbar g ht) hfix
    fun v hv => ?_
  rw [← hA.axisA_sup_spanD hM hII hxA hxz] at hv
  obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hfix w hw, show (t : S.Qt ≃ₗ[ZMod 2] S.Qt) c + w - (c + w) =
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) c - c by abel]
  have h1 := hA.Lbar_sub_mem_span ht hc
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp h1
  rw [← hμ]
  exact Submodule.smul_mem _ _ (cl_conj_mem_spanD (hA.le_QG hxA))

omit hM in
theorem axisD_eq : axisD S g = axisA S A g ⊓ spanD S := by
  have hxQ := hA.le_QG hxA
  have hA0 : S.clPre (spanD S) ≤ A := by
    rw [← hA.clPre_clSub]
    exact S.clPre_mono (spanD_le_clSub hII)
  refine le_antisymm (le_inf (S.clSub_mono (inf_le_inf hA0 (Subgroup.map_mono hA0)))
    (axisD_le_spanD g)) fun v ⟨hvC, hvD⟩ => ?_
  rcases exists_conj_of_mem_spanD isMbarInvariant_spanD (fun h hh => cl_conj_mem_spanD hh)
    (q_spanD hII) hvD with rfl | ⟨h, hhQ, rfl⟩
  · exact zero_mem _
  refine (cl_mem_axisD_iff hxQ hxz hhQ).mpr ?_
  obtain ⟨b, hb, hbQ, hbe⟩ := S.mem_clSub_iff.mp hvC
  have hbQa : b ∈ S.Qa g := hA.conjSub_le_Qa g hb.2
  rcases (S.cl_eq_cl_iff hbQ hhQ).mp hbe with e | e
  · rw [e]
    exact hbQa
  · rw [e]
    exact (S.Qa g).mul_mem hbQa (S.z_mem_Qa_of_mem_QG rfl hxQ hxz)

theorem axisD_ne_spanD (hbad : ¬ A ≤ S.Qa g) : axisD S g ≠ spanD S := by
  intro heq
  have hle : spanD S ≤ axisA S A g := by
    rw [← heq, hA.axisD_eq hII hxA hxz]
    exact inf_le_left
  have htop : axisA S A g = S.clSub A := by
    rw [← hA.axisA_sup_spanD hM hII hxA hxz, sup_eq_left.mpr hle]
  have hzI : S.z ∈ A ⊓ conjSub A g := ⟨hA.z_mem, hA.z_mem_conjSub hM hxA hxz⟩
  have hI : A ⊓ conjSub A g = A := by
    rw [← S.clPre_clSub (inf_le_left.trans hA.le_QG) hzI, ← hA.clPre_clSub]
    exact congrArg S.clPre (by rw [hA.clPre_clSub]; exact htop)
  exact hbad fun a ha => hA.conjSub_le_Qa g (by rw [← hI] at ha; exact ha.2)

end MaxEA

end CFSG.LargeExtraspecial.DW
