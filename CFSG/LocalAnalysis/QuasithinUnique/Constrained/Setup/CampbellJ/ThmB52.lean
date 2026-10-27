module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.JLocal
public import CFSG.Quasithin.Background.C118PartnerB

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}
  {Fp Zp : Subgroup G}

namespace PartnerCoreJ

theorem BoneP_isMax (h : IsSeed S ρ (Ecore G) ψ) (hp : PartnerCoreJ (S : Subgroup G) Fp Zp)
    (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) :
    CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) (CFSG.Quasithin.BoneP Fp A) ∧
      CFSG.Quasithin.BoneP Fp A ≤ CFSG.pCore 2 G ∧
      CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (CFSG.Quasithin.BoneP Fp A) := by
  have hS : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) (CFSG.Quasithin.BoneP Fp A) :=
    hp.sup_max _ (h.Bzero_isMax hA).2
  have hQ : CFSG.Quasithin.BoneP Fp A ≤ CFSG.pCore 2 G :=
    sup_le hFQ (inf_le_left.trans (h.Bzero_isMax hA).1.1)
  exact ⟨hS, hQ, IsSeed.isMaxElemAbelian_core_of_le hS hQ⟩

theorem BoneP_normalized (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) {a : G} (ha : a ∈ A) {b : G}
    (hb : b ∈ CFSG.Quasithin.BoneP Fp A) : a * b * a⁻¹ ∈ CFSG.Quasithin.BoneP Fp A := by
  have : CFSG.Quasithin.BoneP Fp A ≤ cj (CFSG.Quasithin.BoneP Fp A) a := by
    refine sup_le (fun x hx => mem_cj.mpr ?_) (fun x hx => mem_cj.mpr ?_)
    · exact Subgroup.mem_sup_left (hp.normal a (maxElem_le_thompsonJ hA ha) x hx)
    · obtain ⟨hxB0, hxc⟩ := hx
      apply Subgroup.mem_sup_right
      refine ⟨IsSeed.Bzero_normalized hA ha hxB0, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hw' : a⁻¹ * w * a⁻¹⁻¹ ∈ Fp :=
        hp.normal a⁻¹ ((CFSG.Quasithin.thompsonJ (S : Subgroup G)).inv_mem
          (maxElem_le_thompsonJ hA ha)) w hw
      have hcomm := Subgroup.mem_centralizer_iff.mp hxc _ hw'
      calc w * (a * x * a⁻¹) = a * ((a⁻¹ * w * a⁻¹⁻¹) * x) * a⁻¹ := by group
        _ = a * (x * (a⁻¹ * w * a⁻¹⁻¹)) * a⁻¹ := by rw [hcomm]
        _ = a * x * a⁻¹ * w := by group
  exact mem_cj.mp (this hb)

theorem commutator_A_BoneP_le (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G) :
    ⁅A, CFSG.Quasithin.BoneP Fp A⁆ ≤ Zfix S ⊔ Zp := by
  have hZZ : Zfix S ⊔ Zp ≤ Subgroup.centralizer
      ((CFSG.Quasithin.thompsonJ (S : Subgroup G)) : Set G) :=
    sup_le
      (fun z hz => Subgroup.mem_centralizer_iff.mpr fun j hj =>
        IsSeed.Zfix_central hz (thompsonJ_le_self' _ hj))
      (fun z hz => Subgroup.mem_centralizer_iff.mpr fun j hj => hp.zcentral j hj z hz)
  have hNV : ∀ n ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G),
      ∀ v ∈ Zfix S ⊔ Zp, n * v * n⁻¹ ∈ Zfix S ⊔ Zp :=
    fun n hn v hv => mem_of_central_conj hZZ hn hv
  have hNV' : ∀ n ∈ CFSG.Quasithin.thompsonJ (S : Subgroup G),
      ∀ v ∈ Zfix S, n * v * n⁻¹ ∈ Zfix S := fun n hn v hv =>
    mem_of_central_conj (fun z hz => Subgroup.mem_centralizer_iff.mpr fun j hj =>
      IsSeed.Zfix_central hz (thompsonJ_le_self' _ hj)) hn hv
  have hB0 : ⁅A, Bzero A⁆ ≤ Zfix S := by
    refine commutator_sup_le hNV' (inf_le_left.trans (maxElem_le_thompsonJ hA))
      (Fcore_le_thompsonJ.trans h.thompsonJ_core_le_thompsonJ_sylow) ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha x hx
      have hc : a * x = x * a := (isElemAbelian_iff.mp hA.2.1).1 a ha x hx.1
      have : ⁅a, x⁆ = 1 := by
        simp only [commutatorElement_def]; rw [hc]; group
      rw [this]; exact one_mem _
    · rw [h.commutator_A_Fcore hA hAQ]
  have hB0J : Bzero A ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    sup_le (inf_le_left.trans (maxElem_le_thompsonJ hA))
      (Fcore_le_thompsonJ.trans h.thompsonJ_core_le_thompsonJ_sylow)
  refine commutator_sup_le hNV hp.fp_le_thompsonJ (inf_le_left.trans hB0J) ?_ ?_
  · exact (hp.commA_le hA).trans le_sup_right
  · exact ((Subgroup.commutator_mono le_rfl inf_le_left).trans hB0).trans le_sup_left

theorem Fcore_le_BoneP (h : IsSeed S ρ (Ecore G) ψ) (hp : PartnerCoreJ (S : Subgroup G) Fp Zp)
    (hFQ : Fp ≤ CFSG.pCore 2 G) (A : Subgroup G) : Fcore G ≤ CFSG.Quasithin.BoneP Fp A := by
  intro f hf
  apply Subgroup.mem_sup_right
  refine ⟨Subgroup.mem_sup_right hf, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  exact Fcore_commute_thompsonJ_core hf (fp_le_thompsonJ_core h hp hFQ hw)

private theorem Zfix_sup_zp_le_FcoreJ (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) : Zfix S ⊔ Zp ≤ Fcore G :=
  sup_le h.Zfix_le_Fcore (zp_le_Fcore h hp)

private theorem Fcore_commute_cjJ (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) (g : G)
    {f w : G} (hf : f ∈ Fcore G) (hw : w ∈ cj Fp g) : f * w = w * f :=
  (Fcore_commute_thompsonJ_core hf
    (CFSG.Quasithin.PartnerCore.cj_fp_le_thompsonJ_core
      (fp_le_thompsonJ_core h hp hFQ) g hw)).symm

private theorem cj_mem_of_mem_thompsonJ_coreJ (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (g : G) {a : G}
    (ha : a ∈ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)) {x : G} (hx : x ∈ cj Fp g) :
    a * x * a⁻¹ ∈ cj Fp g := by
  rw [mem_cj] at hx ⊢
  have hga : g * a * g⁻¹ ∈ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
    thompsonJ_conj_mem ha g
  have := hp.normal _ (h.thompsonJ_core_le_thompsonJ_sylow hga) _ hx
  have e : g * (a * x * a⁻¹) * g⁻¹ =
      (g * a * g⁻¹) * (g * x * g⁻¹) * (g * a * g⁻¹)⁻¹ := by group
  rw [e]
  exact this

private theorem commutator_A_BoneP_le_CJ (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G)
    (g : G) : ⁅A, CFSG.Quasithin.BoneP Fp A⁆ ≤ CFSG.Quasithin.CtrP Fp A g := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hmem : ⁅a, b⁆ ∈ (⁅A, CFSG.Quasithin.BoneP Fp A⁆ : Subgroup G) :=
    Subgroup.commutator_mem_commutator ha hb
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  · have h1 : a * b * a⁻¹ ∈ CFSG.Quasithin.BoneP Fp A := BoneP_normalized hp hA ha hb
    have : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact mul_mem h1 ((CFSG.Quasithin.BoneP Fp A).inv_mem hb)
  · have hF : ⁅a, b⁆ ∈ Fcore G :=
      Zfix_sup_zp_le_FcoreJ h hp (commutator_A_BoneP_le h hp hA hAQ hmem)
    exact (Fcore_commute_cjJ h hp hFQ g hF hw).symm

private theorem cj_CtrP_eqJ (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G)
    (g : G) {a : G} (ha : a ∈ A) :
    cj (CFSG.Quasithin.CtrP Fp A g) a = CFSG.Quasithin.CtrP Fp A g := by
  apply cj_eq_of_forall_mem
  intro x hx
  have hcomm : ⁅a, x⁆ ∈ CFSG.Quasithin.CtrP Fp A g :=
    commutator_A_BoneP_le_CJ h hp hFQ hA hAQ g
      (Subgroup.commutator_mem_commutator ha hx.1)
  have : a * x * a⁻¹ = ⁅a, x⁆ * x := by simp only [commutatorElement_def]; group
  rw [this]
  exact mul_mem hcomm hx

private theorem CtrP_le_centralizer_cjJ (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G)
    (g : G) {a : G} (ha : a ∈ A) :
    CFSG.Quasithin.CtrP Fp A g ≤
      Subgroup.centralizer ((cj (cj Fp g) a : Subgroup G) : Set G) := by
  have h1 : CFSG.Quasithin.CtrP Fp A g ≤
      Subgroup.centralizer ((cj Fp g : Subgroup G) : Set G) := inf_le_right
  have h2 := cj_mono (g := a) h1
  rw [cj_CtrP_eqJ h hp hFQ hA hAQ g ha, ← centralizer_cj] at h2
  exact h2

private theorem CtrP_sup_isMaxJ (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) (g : G) :
    CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G)
      (cj Fp g ⊔ CFSG.Quasithin.CtrP Fp A g) := by
  obtain ⟨hBS, hBQ, hBQmax⟩ := BoneP_isMax h hp hFQ hA
  have h1 := hp.sup_max_cj g (A' := CFSG.Quasithin.BoneP Fp A)
    (h.isMaxElemAbelian_cj_of_core hBQmax g)
  have hQ : cj Fp g ⊔ CFSG.Quasithin.CtrP Fp A g ≤ CFSG.pCore 2 G :=
    sup_le (CFSG.Quasithin.PartnerCore.cj_fp_le_core hFQ g) (inf_le_left.trans hBQ)
  exact isMaxElemAbelian_core_of_le_cj (core_le_sylow S) h1 hQ

private theorem cj_zp_eq_of_commutator_ne_botJ (hp : PartnerCoreJ (S : Subgroup G) Fp Zp)
    (g x : G) {C : Subgroup G}
    (hA₁ : CFSG.Quasithin.IsMaxElemAbelian (cj (S : Subgroup G) g) (cj (cj Fp g) x ⊔ C))
    (hA₂ : CFSG.Quasithin.IsMaxElemAbelian (cj (S : Subgroup G) (g * x)) (cj Fp g ⊔ C))
    (hCX : ∀ c ∈ C, ∀ w ∈ cj Fp g, c * w = w * c)
    (hCX' : ∀ c ∈ C, ∀ w ∈ cj (cj Fp g) x, c * w = w * c)
    (hne : ⁅cj Fp g, cj (cj Fp g) x⁆ ≠ ⊥) :
    cj Zp g = cj Zp (g * x) := by
  have hX' : cj (cj Fp g) x = cj Fp (g * x) := cj_cj
  have h1 : ⁅cj (cj Fp g) x ⊔ C, cj Fp g⁆ = ⁅cj (cj Fp g) x, cj Fp g⁆ := by
    apply le_antisymm
    · exact commutator_sup_of_commute (fun p hp c hc => (hCX' c hc p hp).symm) hCX
    · exact Subgroup.commutator_mono le_sup_left le_rfl
  have hne1 : ⁅cj (cj Fp g) x ⊔ C, cj Fp g⁆ ≠ ⊥ := by
    rw [h1, Subgroup.commutator_comm]; exact hne
  have e1 : ⁅cj (cj Fp g) x ⊔ C, cj Fp g⁆ = cj Zp g :=
    (hp.commA_cj g hA₁).resolve_left hne1
  rw [h1, Subgroup.commutator_comm] at e1
  have h2 : ⁅cj Fp g ⊔ C, cj (cj Fp g) x⁆ = ⁅cj Fp g, cj (cj Fp g) x⁆ := by
    apply le_antisymm
    · exact commutator_sup_of_commute (fun p hp c hc => (hCX c hc p hp).symm) hCX'
    · exact Subgroup.commutator_mono le_sup_left le_rfl
  have hne2 : ⁅cj Fp g ⊔ C, cj Fp (g * x)⁆ ≠ ⊥ := by
    rw [← hX', h2]; exact hne
  have e2 : ⁅cj Fp g ⊔ C, cj Fp (g * x)⁆ = cj Zp (g * x) :=
    (hp.commA_cj (g * x) hA₂).resolve_left hne2
  rw [← hX', h2] at e2
  exact e1.symm.trans e2

theorem commutator_cj_eq_bot (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G)
    {g : G} (hgM : g ∉ Mnorm S ρ)
    (hN : ∀ y ∈ Subgroup.normalizer ((Zp : Subgroup G) : Set G), y ∈ Mnorm S ρ)
    {x : G} (hx : x ∈ A) (hxQ : x ∉ CFSG.pCore 2 G) :
    ⁅cj Fp g, cj (cj Fp g) x⁆ = ⊥ := by
  by_contra hne
  have hxS : x ∈ (S : Subgroup G) := hA.1 hx
  have hXC := CtrP_sup_isMaxJ h hp hFQ hA g
  have hCx := cj_CtrP_eqJ h hp hFQ hA hAQ g hx
  have hA₂ : CFSG.Quasithin.IsMaxElemAbelian (cj (S : Subgroup G) (g * x))
      (cj Fp g ⊔ CFSG.Quasithin.CtrP Fp A g) :=
    h.isMaxElemAbelian_cj_of_core hXC (g * x)
  have hA₁ : CFSG.Quasithin.IsMaxElemAbelian (cj (S : Subgroup G) g)
      (cj (cj Fp g) x ⊔ CFSG.Quasithin.CtrP Fp A g) := by
    have h1 := isMaxElemAbelian_cj x hXC
    rw [cj_eq_self_of_normal (Y := CFSG.pCore 2 G), cj_sup, hCx] at h1
    exact h.isMaxElemAbelian_cj_of_core h1 g
  have hCX : ∀ c ∈ CFSG.Quasithin.CtrP Fp A g, ∀ w ∈ cj Fp g, c * w = w * c :=
    fun c hc w hw => (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm
  have hCX' : ∀ c ∈ CFSG.Quasithin.CtrP Fp A g, ∀ w ∈ cj (cj Fp g) x, c * w = w * c :=
    fun c hc w hw =>
      (Subgroup.mem_centralizer_iff.mp
        (CtrP_le_centralizer_cjJ h hp hFQ hA hAQ g hx hc) w hw).symm
  have hZ := cj_zp_eq_of_commutator_ne_botJ hp g x hA₁ hA₂ hCX hCX' hne
  have hcj : cj (cj Zp g) x = cj Zp g := by
    have : cj (cj Zp g) x = cj Zp (g * x) := cj_cj
    rw [this]
    exact hZ.symm
  have hmem := mem_normalizer_of_cj_cj_eq hcj
  exact hgM (h.mem_Mnorm_of_conj_mem hxS hxQ (hN _ hmem))

private theorem cj_conj_le_supJ (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G)
    {g : G} (hgM : g ∉ Mnorm S ρ)
    (hN : ∀ y ∈ Subgroup.normalizer ((Zp : Subgroup G) : Set G), y ∈ Mnorm S ρ) :
    ∀ a ∈ A, cj (cj Fp g) a ≤ cj Fp g ⊔ CFSG.Quasithin.CtrP Fp A g := by
  have hXQ := CFSG.Quasithin.PartnerCore.cj_fp_le_core hFQ g
  have hXC := CtrP_sup_isMaxJ h hp hFQ hA g
  have hXel : CFSG.Open.IsElemAbelian 2 (cj Fp g) := isElemAbelian_cj hp.isElemAbelian_fp g
  have hCX : ∀ c ∈ CFSG.Quasithin.CtrP Fp A g, ∀ w ∈ cj Fp g, c * w = w * c :=
    fun c hc w hw => (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm
  have hcomm : ∀ a ∈ A, ∀ w ∈ cj Fp g, ∀ y ∈ cj (cj Fp g) a, w * y = y * w := by
    intro a ha w hw y hy
    by_cases haQ : a ∈ CFSG.pCore 2 G
    · have haJ : a ∈ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) :=
        maxElem_le_thompsonJ (h.Bzero_isMax hA).1 (Subgroup.mem_sup_left ⟨ha, haQ⟩)
      have hcjX : cj (cj Fp g) a = cj Fp g :=
        cj_eq_of_forall_mem fun z hz => cj_mem_of_mem_thompsonJ_coreJ h hp g haJ hz
      rw [hcjX] at hy
      exact (isElemAbelian_iff.mp hXel).1 w hw y hy
    · exact mul_comm_of_commutator_eq_bot
        (commutator_cj_eq_bot h hp hFQ hA hAQ hgM hN ha haQ) hw hy
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
      Subgroup.mem_centralizer_iff.mp (CtrP_le_centralizer_cjJ h hp hFQ hA hAQ g ha hc) y hy
    calc y * (w * c) = (y * w) * c := by group
      _ = (w * y) * c := by rw [h1]
      _ = w * (y * c) := by group
      _ = w * (c * y) := by rw [h2]
      _ = w * c * y := by group

private theorem boneP_commutator_cj_eq_botJ (h : IsSeed S ρ (Ecore G) ψ)
    (hp : PartnerCoreJ (S : Subgroup G) Fp Zp) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G)
    {g : G} (hgM : g ∉ Mnorm S ρ)
    (hN : ∀ y ∈ Subgroup.normalizer ((Zp : Subgroup G) : Set G), y ∈ Mnorm S ρ)
    (hBS : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) (CFSG.Quasithin.BoneP Fp A))
    (hBQmax : CFSG.Quasithin.IsMaxElemAbelian (CFSG.pCore 2 G) (CFSG.Quasithin.BoneP Fp A))
    (hCle : CFSG.Quasithin.CtrP Fp A g ≤ CFSG.Quasithin.BoneP Fp A)
    (hCX : ∀ c ∈ CFSG.Quasithin.CtrP Fp A g, ∀ w ∈ cj Fp g, c * w = w * c)
    (hXa : ∀ a ∈ A, cj (cj Fp g) a ≤ cj Fp g ⊔ CFSG.Quasithin.CtrP Fp A g) :
    ⁅CFSG.Quasithin.BoneP Fp A, cj Fp g⁆ = ⊥ := by
  by_contra hne
  have hBg : CFSG.Quasithin.IsMaxElemAbelian (cj (S : Subgroup G) g)
      (CFSG.Quasithin.BoneP Fp A) :=
    h.isMaxElemAbelian_cj_of_core hBQmax g
  have e : ⁅CFSG.Quasithin.BoneP Fp A, cj Fp g⁆ = cj Zp g :=
    (hp.commA_cj g hBg).resolve_left hne
  have hinv : ∀ a ∈ A,
      cj ⁅CFSG.Quasithin.BoneP Fp A, cj Fp g⁆ a =
        ⁅CFSG.Quasithin.BoneP Fp A, cj Fp g⁆ := by
    intro a ha
    have h1 : cj ⁅CFSG.Quasithin.BoneP Fp A, cj Fp g⁆ a =
        ⁅cj (CFSG.Quasithin.BoneP Fp A) a, cj (cj Fp g) a⁆ := cj_commutator
    have h2 : cj (CFSG.Quasithin.BoneP Fp A) a = CFSG.Quasithin.BoneP Fp A :=
      cj_eq_of_forall_mem fun b hb => BoneP_normalized hp hA ha hb
    have hle : cj ⁅CFSG.Quasithin.BoneP Fp A, cj Fp g⁆ a ≤
        ⁅CFSG.Quasithin.BoneP Fp A, cj Fp g⁆ := by
      rw [h1, h2]
      calc ⁅CFSG.Quasithin.BoneP Fp A, cj (cj Fp g) a⁆
          ≤ ⁅CFSG.Quasithin.BoneP Fp A, cj Fp g ⊔ CFSG.Quasithin.CtrP Fp A g⁆ :=
            Subgroup.commutator_mono le_rfl (hXa a ha)
        _ = ⁅cj Fp g ⊔ CFSG.Quasithin.CtrP Fp A g, CFSG.Quasithin.BoneP Fp A⁆ :=
            Subgroup.commutator_comm _ _
        _ ≤ ⁅cj Fp g, CFSG.Quasithin.BoneP Fp A⁆ :=
            commutator_sup_of_commute (fun p hp c hc => (hCX c hc p hp).symm)
              (fun c hc b hb => (isElemAbelian_iff.mp hBS.2.1).1 c (hCle hc) b hb)
        _ = ⁅CFSG.Quasithin.BoneP Fp A, cj Fp g⁆ := Subgroup.commutator_comm _ _
    exact cj_eq_of_le hle
  obtain ⟨a, ha, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
  have hcj : cj (cj Zp g) a = cj Zp g := by
    have := hinv a ha
    rw [e] at this
    exact this
  exact hgM (h.mem_Mnorm_of_conj_mem (hA.1 ha) haQ
    (hN _ (mem_normalizer_of_cj_cj_eq hcj)))

theorem cj_fp_le_BoneP (h : IsSeed S ρ (Ecore G) ψ) (hp : PartnerCoreJ (S : Subgroup G) Fp Zp)
    (hFQ : Fp ≤ CFSG.pCore 2 G) {A : Subgroup G}
    (hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A) (hAQ : ¬ A ≤ CFSG.pCore 2 G)
    {g : G} (hgM : g ∉ Mnorm S ρ)
    (hN : ∀ y ∈ Subgroup.normalizer ((Zp : Subgroup G) : Set G), y ∈ Mnorm S ρ) :
    cj Fp g ≤ CFSG.Quasithin.BoneP Fp A := by
  obtain ⟨hBS, hBQ, hBQmax⟩ := BoneP_isMax h hp hFQ hA
  have hXQ := CFSG.Quasithin.PartnerCore.cj_fp_le_core hFQ g
  have hXel : CFSG.Open.IsElemAbelian 2 (cj Fp g) := isElemAbelian_cj hp.isElemAbelian_fp g
  have hCle : CFSG.Quasithin.CtrP Fp A g ≤ CFSG.Quasithin.BoneP Fp A := inf_le_left
  have hCX : ∀ c ∈ CFSG.Quasithin.CtrP Fp A g, ∀ w ∈ cj Fp g, c * w = w * c :=
    fun c hc w hw => (Subgroup.mem_centralizer_iff.mp hc.2 w hw).symm
  have hXa := cj_conj_le_supJ h hp hFQ hA hAQ hgM hN
  have hNbot := boneP_commutator_cj_eq_botJ h hp hA hAQ hgM hN hBS hBQmax hCle hCX hXa
  exact maxElem_le_of_commute hBQmax hXQ hXel fun y hy b hb =>
    (mul_comm_of_commutator_eq_bot hNbot hb hy).symm

end PartnerCoreJ

end CFSG.QuasithinUnique.Setup.CampbellJ

end