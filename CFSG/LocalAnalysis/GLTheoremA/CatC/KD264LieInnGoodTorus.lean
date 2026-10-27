module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPieces

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.LieType.SeitzGeneration

theorem exists_perfect_le_centralizer_of_conj {G : Type*} [Group G] {p : ℕ} {g x : G}
    (h : ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({x} : Set G) ∧ ⁅P, P⁆ = P ∧
      p ∣ Nat.card P) :
    ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({g * x * g⁻¹} : Set G) ∧ ⁅P, P⁆ = P ∧
      p ∣ Nat.card P := by
  obtain ⟨P, hPC, hPperf, hPdvd⟩ := h
  refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (hPC hy)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hcomm]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  · rw [← Subgroup.map_commutator, hPperf]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hPdvd

theorem exists_good_of_mem_map_conj {G : Type*} [Group G] {p : ℕ} {E : Subgroup G} {g : G}
    (h : ∃ d ∈ E.map (MulAut.conj g).toMonoidHom, d ≠ 1 ∧
      ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({d} : Set G) ∧ ⁅P, P⁆ = P ∧
        p ∣ Nat.card P) :
    ∃ x ∈ E, x ≠ 1 ∧ ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({x} : Set G) ∧
      ⁅P, P⁆ = P ∧ p ∣ Nat.card P := by
  obtain ⟨d, hd, hd1, P, hPC, hPperf, hPdvd⟩ := h
  obtain ⟨x, hxE, hxd⟩ := hd
  refine ⟨x, hxE, ?_, ?_⟩
  · intro hx1
    apply hd1
    rw [← hxd, hx1, map_one]
  · obtain ⟨P', hP'c, hP'p, hP'd⟩ := exists_perfect_le_centralizer_of_conj (g := g⁻¹) (x := d)
      ⟨P, hPC, hPperf, hPdvd⟩
    have hx : g⁻¹ * d * (g⁻¹)⁻¹ = x := by
      rw [← hxd]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact ⟨P', by rwa [hx] at hP'c, hP'p, hP'd⟩

theorem PerfectCentralizerPlanes.of_conj_le {G : Type} [Group G] {p : ℕ} {Γ E : Subgroup G}
    (hconj : ∀ F : Subgroup G, F ≤ Γ → (∀ x ∈ F, x ^ p = 1) → Nat.card F = p ^ 2 →
      ∃ h ∈ Γ, F.map (MulAut.conj h).toMonoidHom ≤ E)
    (hwit : ∀ D : Subgroup G, D ≤ E → (∀ x ∈ D, x ^ p = 1) → Nat.card D = p ^ 2 →
      ∃ d ∈ D, d ≠ 1 ∧ ∃ R : Subgroup G, R ≤ Γ ⊓ Subgroup.centralizer {d} ∧
        ⁅R, R⁆ = R ∧ p ∣ Nat.card R) :
    PerfectCentralizerPlanes p Γ := by
  classical
  intro F hF hFcard
  set F' : Subgroup G := F.map Γ.subtype with hF'
  have hF'Γ : F' ≤ Γ := Subgroup.map_subtype_le F
  have hF'pow : ∀ x ∈ F', x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hF.2 x hx, map_one]
  have hF'card : Nat.card F' = p ^ 2 := by
    rw [hF', Subgroup.card_map_of_injective Γ.subtype_injective, hFcard]
  obtain ⟨h, hhΓ, hhE⟩ := hconj F' hF'Γ hF'pow hF'card
  set D : Subgroup G := F'.map (MulAut.conj h).toMonoidHom with hD
  have hDpow : ∀ x ∈ D, x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hF'pow y hy, map_one]
  have hDcard : Nat.card D = p ^ 2 := by
    rw [hD, Subgroup.card_map_of_injective (MulAut.conj h).injective, hF'card]
  obtain ⟨d, hdD, hd1, R, hRle, hRperf, hRdvd⟩ := hwit D hhE hDpow hDcard
  have hDΓ : D ≤ Γ := by
    rintro _ ⟨y, hy, rfl⟩
    exact Γ.mul_mem (Γ.mul_mem hhΓ (hF'Γ hy)) (Γ.inv_mem hhΓ)
  have hdΓ : d ∈ Γ := hDΓ hdD
  have hRΓ : R ≤ Γ := fun z hz => (Subgroup.mem_inf.1 (hRle hz)).1
  have hRcent : R ≤ Subgroup.centralizer ({d} : Set G) :=
    fun z hz => (Subgroup.mem_inf.1 (hRle hz)).2
  obtain ⟨y, hyF', hdy⟩ := hdD
  obtain ⟨x, hxF, hxe⟩ := hyF'
  have hdy' : h * (x : G) * h⁻¹ = d := by
    rw [← hxe] at hdy
    simpa only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hdy
  let k : ↥Γ := ⟨h, hhΓ⟩
  let δ : ↥Γ := ⟨d, hdΓ⟩
  set Rc : Subgroup ↥Γ := R.subgroupOf Γ with hRc
  have hRc_cent : Rc ≤ Subgroup.centralizer ({δ} : Set ↥Γ) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hzR : (z : G) ∈ R := by
      rw [hRc] at hz
      exact Subgroup.mem_subgroupOf.1 hz
    have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (hRcent hzR)
    simpa [δ] using hcomm
  have hRc_perf : ⁅Rc, Rc⁆ = Rc :=
    CFSG.SeitzReduction.OmegaPilot.commutator_subgroupOf_eq_of_le_perfect hRΓ hRperf
  have hRc_dvd : p ∣ Nat.card Rc := by
    rw [hRc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRΓ).toEquiv]
    exact hRdvd
  have hkx : k⁻¹ * δ * k = x := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    show h⁻¹ * d * h = (x : G)
    rw [← hdy']
    group
  obtain ⟨P, hPcent, hPperf, hPdvd⟩ :=
    exists_perfect_le_centralizer_of_conj (g := k⁻¹) (x := δ)
      ⟨Rc, hRc_cent, hRc_perf, hRc_dvd⟩
  refine ⟨x, hxF, ?_, P, ?_, hPperf, hPdvd⟩
  · intro hx1
    apply hd1
    have hx1' : (x : G) = 1 := by rw [hx1]; rfl
    rw [← hdy', hx1']
    simp
  · simpa [hkx] using hPcent

theorem PerfectCentralizerPlanes.of_rankLE1 {p : ℕ} (hp : p.Prime) {G : Type} [Group G]
    (h : RankLE1 p G) : PerfectCentralizerPlanes p G := by
  intro E hE hcard
  have hle := h E hE
  have hp2 : p < p ^ 2 := by nlinarith [hp.two_le]
  omega

section Toral

variable {τ : Tag} {K : Type} [Field K] [Finite K]


theorem exists_perfect_le_centralizer_toralComponent {p : ℕ} (hp : p.Prime) {t : Kˣ}
    (htp : orderOf t = p) (ht : t ^ 2 ≠ 1) {B : Subgroup (ModGL τ K)}
    (hBT : B ≤ torusGroup τ K) (hBpow : ∀ x ∈ B, x ^ p = 1) (hBcard : p < Nat.card B)
    (k : Fin τ.rank) :
    ∃ d ∈ B, d ≠ 1 ∧ ∃ P : Subgroup (ModGL τ K),
      P ≤ Subgroup.centralizer ({d} : Set (ModGL τ K)) ∧ P ≤ adjointGroup τ K ∧
        ⁅P, P⁆ = P ∧ p ∣ Nat.card P := by
  classical
  have hα : IsRoot τ (Pi.single k 1) := IsRoot.basis k
  obtain ⟨a, hdaB, hda1, hχ⟩ := exists_rootChar_eq_one hp hBT hBpow hBcard (Pi.single k 1)
  let χ : Multiplicative (Fin τ.rank → ℤ) →* Kˣ := rootCharHom a
  have hαk : Pi.single k 1 ∈ kernelRoots χ := ⟨hα, hχ⟩
  let i : KernelComponent χ := ⟦⟨Pi.single k 1, hαk⟩⟧
  have hS_quasi : CFSG.IsQuasisimple ↥(componentRootSpan K χ i) :=
    isQuasisimple_componentRootSpan_of_sq_ne_one ht i
  have hS_le : componentRootSpan K χ i ≤ toralCentralizer τ K a :=
    componentRootSpan_le_toralCentralizer a i
  have hS_perf : ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ =
      componentRootSpan K χ i := by
    haveI : Group.IsPerfect ↥(componentRootSpan K χ i) := hS_quasi.1
    exact Subgroup.commutator_eq_self
  have hmem : canonicalRep (coxeterSystem τ) K 1 * torusElt τ K k t *
      (canonicalRep (coxeterSystem τ) K 1)⁻¹ ∈ componentTorus K χ i :=
    canonicalRep_conj_torusElt_mem (χ := χ) (i := i) (w := 1) (k := k)
      (by simpa using (show Pi.single k 1 ∈ componentRoots χ i from ⟨hαk, rfl⟩)) t
  have hdiv : p ∣ Nat.card ↥(componentRootSpan K χ i) := by
    have h1 := orderOf_dvd_natCard
      (⟨_, componentTorus_le_componentRootSpan K χ i hmem⟩ : componentRootSpan K χ i)
    rw [Subgroup.orderOf_mk,
      orderOf_canonicalRep_conj_torusElt hp (1 : WeylGroup τ) k htp ht] at h1
    exact h1
  exact ⟨rootDiagUnit τ a, hdaB, hda1, componentRootSpan K χ i, hS_le.trans inf_le_right,
    hS_le.trans inf_le_left, hS_perf, hdiv⟩

theorem perfectCentralizerPlanes_of_conj_into_torus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1)
    (hconj : ∀ A : Subgroup (ModGL τ K), A ≤ adjointGroup τ K → (∀ x ∈ A, x ^ p = 1) →
      ∃ g ∈ adjointGroup τ K, A.map (MulAut.conj g).toMonoidHom ≤ torusGroup τ K) :
    PerfectCentralizerPlanes p (adjointGroup τ K) := by
  classical
  obtain ⟨t, htp, ht⟩ := exists_orderOf_units_of_dvd hp hp2 hpK
  let k : Fin τ.rank := ⟨0, CFSG.LieType.Chevalley.Tag.rank_pos τ⟩
  refine PerfectCentralizerPlanes.of_conj_le (Γ := adjointGroup τ K)
    (E := torusGroup τ K) ?_ ?_
  · intro F hF hFpow _
    exact hconj F hF hFpow
  · intro D hDT hDpow hDcard
    have hDcard' : p < Nat.card D := by rw [hDcard]; nlinarith [hp.two_le]
    obtain ⟨d, hdD, hd1, P, hPC, hPadj, hPperf, hPdvd⟩ :=
      exists_perfect_le_centralizer_toralComponent hp htp ht hDT hDpow hDcard' k
    exact ⟨d, hdD, hd1, P, le_inf hPadj hPC, hPperf, hPdvd⟩

end Toral

section ConjLe

variable {τ : Tag} {K₂ : Type} [Field K₂] [Finite K₂]


private theorem exists_component_of_toralPlane {p : ℕ} (hp : p.Prime)
    {Γ E : Subgroup (ModGL τ K₂)} (hET : E ≤ torusGroup τ K₂)
    (hcomp : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → ∀ a : Fin τ.rank → K₂ˣ,
      rootDiagUnit τ a ∈ E → rootDiagUnit τ a ≠ 1 → rootChar a β = 1 →
      ∃ L : Subgroup (ModGL τ K₂), L ≤ Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
        CFSG.IsQuasisimple L ∧ ¬ Nat.Coprime p (Nat.card L))
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {B : Subgroup (ModGL τ K₂)} (hBE : B ≤ E)
    (hBpow : ∀ x ∈ B, x ^ p = 1) (hBcard : p < Nat.card B) :
    ∃ a : Fin τ.rank → K₂ˣ, rootDiagUnit τ a ∈ B ∧ rootDiagUnit τ a ≠ 1 ∧
      ∃ L : Subgroup (ModGL τ K₂), L ≤ Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
        CFSG.IsQuasisimple L ∧ ¬ Nat.Coprime p (Nat.card L) := by
  obtain ⟨a, hdaB, hda1, hχ⟩ := exists_rootChar_eq_one hp (hBE.trans hET) hBpow hBcard β
  exact ⟨a, hdaB, hda1, hcomp β hβ a (hBE hdaB) hda1 hχ⟩

theorem perfectCentralizerPlanes_of_conj_le_of_components {p : ℕ} (hp : p.Prime)
    {Γ E : Subgroup (ModGL τ K₂)} (hET : E ≤ torusGroup τ K₂)
    (hsylow : ∀ F : Subgroup (ModGL τ K₂), F ≤ Γ → (∀ x ∈ F, x ^ p = 1) → Nat.card F = p ^ 2 →
      ∃ h ∈ Γ, F.map (MulAut.conj h).toMonoidHom ≤ E)
    (hcomp : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → ∀ a : Fin τ.rank → K₂ˣ,
      rootDiagUnit τ a ∈ E → rootDiagUnit τ a ≠ 1 → rootChar a β = 1 →
      ∃ L : Subgroup (ModGL τ K₂), L ≤ Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} ∧
        CFSG.IsQuasisimple L ∧ ¬ Nat.Coprime p (Nat.card L))
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : PerfectCentralizerPlanes p Γ := by
  classical
  refine PerfectCentralizerPlanes.of_conj_le (Γ := Γ) (E := E) hsylow ?_
  intro D hDE hDpow hDcard
  have hDcard' : p < Nat.card D := by rw [hDcard]; nlinarith [hp.two_le]
  obtain ⟨a, hdaD, hda1, L, hLle, hLq, hLnc⟩ :=
    exists_component_of_toralPlane hp hET hcomp hβ hDE hDpow hDcard'
  have hLperf : ⁅L, L⁆ = L := by
    haveI : Group.IsPerfect ↥L := hLq.1
    exact Subgroup.commutator_eq_self
  exact ⟨rootDiagUnit τ a, hdaD, hda1, L, hLle, hLperf,
    (Nat.Prime.dvd_iff_not_coprime hp).mpr hLnc⟩

end ConjLe

section LangFrame

variable {τ : Tag} {K₂ : Type} [Field K₂] [Finite K₂]


theorem perfectCentralizerPlanes_of_isLangFrame {p : ℕ} (hp : p.Prime)
    {Γ E : Subgroup (ModGL τ K₂)} (hF : IsLangFrame τ K₂ p Γ E)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : PerfectCentralizerPlanes p Γ :=
  perfectCentralizerPlanes_of_conj_le_of_components hp hF.E_le_torus hF.sylow
    (fun β hβ a h1 h2 h3 => by
      obtain ⟨L, -, hLle, hLq, -, hLnc⟩ := hF.component β hβ a h1 h2 h3
      exact ⟨L, hLle, hLq, hLnc⟩) hβ

end LangFrame

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
