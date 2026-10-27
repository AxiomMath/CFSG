module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDescent
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Ind
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient_apply_mk)
open CFSG.GroupActions (subgroupStabAut subgroupStabRestrict subgroupStabRestrict_apply)
open scoped commutatorElement

section Generic

variable {C : Type} [Group C] [Finite C]

theorem exists_le_of_glaPComponent_le_iSup {q : ℕ} (hq : q.Prime) {X J : Subgroup C}
    (hJ : GLAPComponent q X J) {ι : Type*} (N : ι → Subgroup C)
    (hN : ∀ i, CFSG.Open.IsComponentOf (N i) X) (hle : J ≤ ⨆ i, N i) : ∃ i, J ≤ N i := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hJX, hJp⟩ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hq).1 hJ
  have hNX : ∀ i, N i ≤ X := fun i => (hN i).1
  have hNs : ∀ i, ((N i).subgroupOf X).IsSubnormal := fun i =>
    (CFSG.Open.IsSubnormal.iff_subgroupOf (hNX i)).1 (hN i).2.1
  have hle' : J.subgroupOf X ≤ ⨆ i, (N i).subgroupOf X := by
    rw [← Subgroup.map_le_map_iff_of_injective X.subtype_injective, Subgroup.map_iSup,
      Subgroup.map_subgroupOf_eq_of_le hJX]
    exact hle.trans (le_of_eq (iSup_congr fun i => (Subgroup.map_subgroupOf_eq_of_le (hNX i)).symm))
  obtain ⟨i, hi⟩ := CFSG.ComponentClassification.CatalogueBPrimeJoin.exists_le_of_le_iSup q
    (J.subgroupOf X) hJp (fun i => (N i).subgroupOf X) hNs hle'
  refine ⟨i, ?_⟩
  have h2 := Subgroup.map_mono (f := X.subtype) hi
  rwa [Subgroup.map_subgroupOf_eq_of_le hJX, Subgroup.map_subgroupOf_eq_of_le (hNX i)] at h2

theorem glaPComponent_eq_of_le_component {q : ℕ} {X J K : Subgroup C}
    (hJ : GLAPComponent q X J) (hK : CFSG.Open.IsComponentOf K X) (hJK : J ≤ K) : J = K := by
  have hperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hne : J ≠ ⊥ := CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hJ
  have hsub : CFSG.Open.IsSubnormal J K :=
    CFSG.LocalAnalysis.GLTheoremB.isSubnormal_of_le_of_le hJ.2.1 hJK hK.1
  rcases CFSG.Fischer.Classification.Recognition.IsSubnormal.eq_or_le_center hsub hK.2.2 with h | h
  · exact h
  · exfalso
    have hcomm : ⁅J, J⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨x', hx', rfl⟩ := h hx
      obtain ⟨y', hy', rfl⟩ := h hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hx' y')
    exact hne (hperf ▸ hcomm)

end Generic

section Lang


theorem glaPComponent_map_eq_rationalComponent {τ : Tag} {Lf : Type} [Field Lf] [IsAlgClosed Lf]
    {p₀ p : ℕ} (S : LangSetup τ Lf p₀) (hp : p.Prime) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ Lf) (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    {a : Fin τ.rank → Lfˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {q : ℕ} (hq : q.Prime) {J : Subgroup C} (hJ : GLAPComponent q (fixSubgroup β) J) :
    ∃ i, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      J.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  set d : ModGL τ Lf := rootDiagUnit τ a
  set R : KernelComponent (rootCharHom a) → Subgroup (ModGL τ Lf) :=
    fun i => rationalComponent S.ρ S.Γ (rootCharHom a) i
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hι β d hβ, hrange]
  have hcomapfix : (S.Γ ⊓ Subgroup.centralizer {d}).comap ι = fixSubgroup β := by
    rw [← hfix]
    exact Subgroup.comap_map_eq_self_of_injective hι _
  have hCdrange : S.Γ ⊓ Subgroup.centralizer {d} ≤ ι.range := fun x hx => by
    rw [hrange]
    exact (Subgroup.mem_inf.1 hx).1
  let Q := {i : KernelComponent (rootCharHom a) // CFSG.IsQuasisimple (R i)}
  have hcompR : ∀ i : Q, IsComponentOf (R i.1) (S.Γ ⊓ Subgroup.centralizer {d}) := by
    intro i
    obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT i.1
    exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub,
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple i.2⟩
  have hRrange : ∀ i : Q, R i.1 ≤ ι.range := fun i => (hcompR i).1.trans hCdrange
  let F : Q → Subgroup C := fun i => (R i.1).comap ι
  have hF : ∀ i : Q, IsComponentOf (F i) (fixSubgroup β) := by
    intro i
    have := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isComponentOf_comap_of_injective ι hι
      (hRrange i) hCdrange (hcompR i)
    rwa [hcomapfix] at this
  have hperfJ : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJmap : J.map ι ≤ S.Γ ⊓ Subgroup.centralizer {d} := by
    rw [← hfix]
    exact Subgroup.map_mono hJ.1
  have h2 := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.perfect_le_iSup_rationalComponent_of_prime
    S hp hT hap h1 hTame (J.map ι) hJmap (by rw [← Subgroup.map_commutator, hperfJ])
  have hmapF : (⨆ i, F i).map ι = ⨆ i : Q, R i.1 := by
    rw [Subgroup.map_iSup]
    exact iSup_congr fun i => Subgroup.map_comap_eq_self (hRrange i)
  have hJF : J ≤ ⨆ i, F i := (Subgroup.map_le_map_iff_of_injective hι).1 (h2.trans hmapF.ge)
  obtain ⟨i, hi⟩ := exists_le_of_glaPComponent_le_iSup hq hJ F hF hJF
  refine ⟨i.1, i.2, ?_⟩
  rw [glaPComponent_eq_of_le_component hJ (hF i) hi]
  exact Subgroup.map_comap_eq_self (hRrange i)

theorem map_le_iSup_rationalComponent {G : Type} [Group G] {τ : Tag} {Lf : Type} [Field Lf]
    [IsAlgClosed Lf] {p₀ p : ℕ} (S : LangSetup τ Lf p₀) (hp : p.Prime) {L : Subgroup G} {d : G}
    {C : Type} [Group C] (θ : ↥L ⧸ Subgroup.center ↥L ≃* C) {β : MulAut C}
    (hind : CFSG.Assembly.LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * (l : G) * d) β)
    (ι : C →* ModGL τ Lf) (hι : Function.Injective ι) (hrange : ι.range = S.Γ) {a : Fin τ.rank → Lfˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {K : Subgroup G} (hK : K ≤ L ⊓ Subgroup.centralizer ({d} : Set G)) (hKperf : ⁅K, K⁆ = K) :
    ((K.subgroupOf L).map (T171Sh.piCenterQuot θ)).map ι ≤
      ⨆ i : {i : KernelComponent (rootCharHom a) //
          CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)},
        rationalComponent S.ρ S.Γ (rootCharHom a) i.1 := by
  have hKL : K ≤ L := hK.trans inf_le_left
  have hKfix : (K.subgroupOf L).map (T171Sh.piCenterQuot θ) ≤ fixSubgroup β := by
    rintro _ ⟨k, hk, rfl⟩
    have hkc : (k : G) ∈ Subgroup.centralizer ({d} : Set G) := (hK (Subgroup.mem_subgroupOf.1 hk)).2
    have hkd : (k : G) = d⁻¹ * (k : G) * d := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hkc
      rw [mul_assoc, hkc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hind k k hkd
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hι β _ hβ, hrange]
  have hKperf' : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKL, hKperf]
  have hPle : ((K.subgroupOf L).map (T171Sh.piCenterQuot θ)).map ι ≤
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [← hfix]
    exact Subgroup.map_mono hKfix
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.perfect_le_iSup_rationalComponent_of_prime
    S hp hT hap h1 hTame _ hPle (by rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hKperf'])

end Lang

section Descent

variable {G : Type} [Group G] [Finite G]

theorem langData_of_centralSurjection {X J : Subgroup G} {b : G} (hJ : GLAPComponent 3 X J)
    (hb : b ∈ Subgroup.normalizer (J : Set G)) {H : Type} [Group H] {K : Subgroup H}
    (hK : CFSG.IsQuasisimple ↥K) (f : ↥J →* ↥K) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center ↥J) {y : H} (hyStab : MulAut.conj y ∈ subgroupStabAut K)
    (hfy : ∀ j j' : ↥J, (j' : G) = b⁻¹ * (j : G) * b → (f j' : H) = y * (f j : H) * y⁻¹) :
    CFSG.Open.IsQuasisimple ↥J ∧ Nonempty (PSimple 3 J ≃* (↥K ⧸ Subgroup.center ↥K)) ∧
      (centerQuotientHom ↥K (subgroupStabRestrict K ⟨MulAut.conj y, hyStab⟩) ∈
          innAutDerived (↥K ⧸ Subgroup.center ↥K) →
        MI.indAut 3 J b hb ∈ innAutDerived (PSimple 3 J)) := by
  haveI : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.2 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  let e₀ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.ComponentClassification.PerfectCentralQuotient.equivalence f hf hker
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    ⟨Group.IsPerfect.commutator_eq_top, (MulEquiv.isSimpleGroup_congr e₀).2 hK.2.1⟩
  obtain ⟨e₁, he₁⟩ := T171Sh.exists_pSimpleEquivCenterQuot_mk Nat.prime_three hJq
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.three_dvd_card_of_glaPComponent hJ)
  refine ⟨hJq, ⟨e₁.symm.trans e₀⟩, fun hmem => ?_⟩
  let αb : MulAut ↥J := J.normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hb⟩
  have hαb : ∀ x : ↥J, ((αb x : ↥J) : G) = b⁻¹ * (x : G) * b := fun x => by
    simp [αb]
  have hαγ : ∀ j : ↥J, subgroupStabRestrict K ⟨MulAut.conj y, hyStab⟩ (f j) = f (αb j) := by
    intro j
    apply Subtype.ext
    rw [subgroupStabRestrict_apply, hfy j (αb j) (hαb j)]
    rfl
  have h1 : centerQuotientHom ↥J αb ∈ innAutDerived (↥J ⧸ Subgroup.center ↥J) :=
    (CFSG.ComponentClassification.PerfectCentralQuotient.centerQuotientHom_mem_innAutDerived_iff_of_surjective
      f hf hker hαγ).1 hmem
  have hcompat : MulAut.congr e₁ (centerQuotientHom ↥J αb) = MI.indAut 3 J b hb := by
    ext x
    obtain ⟨z, rfl⟩ := e₁.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    have hrel : indRel 3 J b (QuotientGroup.mk l) (QuotientGroup.mk (αb l)) :=
      ⟨l, αb l, rfl, rfl, hαb l⟩
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, he₁ l,
      MI.indAut_apply_mk hb hrel]
    have h2 : centerQuotientHom ↥J αb (QuotientGroup.mk l) = QuotientGroup.mk (αb l) :=
      onCenterQuotient_apply_mk αb l
    rw [h2, he₁]
  rw [← hcompat]
  exact (mem_innAutDerived_congr e₁).2 h1

theorem mem_inner_of_inducesInnerMod {L : Subgroup G} {d : G} (hcore : GLAPPrimeCore 3 ↥L = ⊥)
    {C : Type} [Group C] (θ : ↥L ⧸ Subgroup.center ↥L ≃* C) {β : MulAut C}
    (hind : CFSG.Assembly.LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * (l : G) * d) β)
    (h : InducesInnerMod 3 L d) : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner C := by
  obtain ⟨l, hl, hly⟩ := h
  have hcoreOf : GLAPPrimeCoreOf 3 L = ⊥ := by
    unfold GLAPPrimeCoreOf
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).2 hcore
  have heq : ∀ x ∈ L, d⁻¹ * x * d = l⁻¹ * x * l := by
    intro x hx
    have h0 := hly x hx
    rw [hcoreOf, Subgroup.mem_bot] at h0
    exact (inv_mul_eq_one.1 h0).symm
  let l' : ↥L := ⟨l, hl⟩
  refine ⟨(θ (QuotientGroup.mk l'))⁻¹, ?_⟩
  ext c
  obtain ⟨q, rfl⟩ := θ.surjective c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hmem : d⁻¹ * (x : G) * d ∈ L := by
    rw [heq x x.2]
    exact L.mul_mem (L.mul_mem (L.inv_mem hl) x.2) hl
  have hx : (⟨d⁻¹ * (x : G) * d, hmem⟩ : ↥L) = l'⁻¹ * x * l' := Subtype.ext (heq x x.2)
  rw [MulAut.conj_apply, hind x ⟨d⁻¹ * (x : G) * d, hmem⟩ rfl, hx, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, map_mul, map_mul, map_inv, inv_inv]

end Descent

section Main


theorem t158E6LangData_of_modelData {G : Type} [Group G] [Finite G] {L J A : Subgroup G} {d b : G}
    (hP : PreSetup 3 L J A d b) {C : Type} [Group C] [Finite C] {θ : ↥L ⧸ Subgroup.center ↥L ≃* C}
    {β φ : MulAut C} {Lf : Type} [Field Lf] [IsAlgClosed Lf] [CharP Lf 2] {S : LangSetup Tag.E6 Lf 5}
    {a : Fin Tag.E6.rank → Lfˣ} {ι : C →* ModGL Tag.E6 Lf} {y : ModGL Tag.E6 Lf}
    (hβind : CFSG.Assembly.LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * (l : G) * d) β)
    (hφind : CFSG.Assembly.LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ)
    (hshape : E6ShapeSetup S) (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (hι : Function.Injective ι) (hrange : ι.range = S.Γ)
    (hβ : ∀ c, ι (β c) = rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹)
    (hφ : ∀ c, ι (φ c) = y * ι c * y⁻¹) (hyC : y ∈ toralCentralizer Tag.E6 Lf a) (hyF : S.D.step y = y)
    (hout : rootDiagUnit Tag.E6 a ∉ S.Γ → β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner C) :
    ∃ (i : KernelComponent (rootCharHom a))
      (hyStab : MulAut.conj y ∈ subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
      E6ShapeSetup S ∧ rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      y ∈ toralCentralizer Tag.E6 Lf a ∧ S.D.step y = y ∧
      Nonempty (PSimple 3 J ≃* (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) ∧
      (centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
          (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i) ⟨MulAut.conj y, hyStab⟩) ∈
          innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
        MI.indAut 3 J b hP.b_norm ∈ innAutDerived (PSimple 3 J)) ∧
      ((∀ j, CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) j) →
          rationalComponent S.ρ S.Γ (rootCharHom a) j = rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
          GLALayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J) ∧
      (rootDiagUnit Tag.E6 a ∉ S.Γ → ¬ InducesInnerMod 3 L d) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hdL : d ∈ Subgroup.normalizer (L : Set G) := hP.norm hP.d_mem
  have hbL : b ∈ Subgroup.normalizer (L : Set G) := hP.norm hP.b_mem
  have hJL : J ≤ L := hP.pcomp.1.trans inf_le_left
  set Jc : Subgroup C := (J.subgroupOf L).map (T171Sh.piCenterQuot θ)
  have hJcomp : GLAPComponent 3 (fixSubgroup β) Jc :=
    glaPComponent_fixSubgroup_map_piCenterQuot hp hdL hP.pcomp θ hβind
  have hpL : ((3 : ℕ) : Lf) ≠ 0 := by
    intro h0
    have h23 := (CharP.cast_eq_zero_iff Lf 2 3).1 h0
    omega
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S hp hpL
    (fun h => by cases h) hT hap h1
  obtain ⟨i, hqs, hRi⟩ := glaPComponent_map_eq_rationalComponent S hp ι hι hrange β hβ hT hap h1 hTame hp
    hJcomp
  set R : Subgroup (ModGL Tag.E6 Lf) := rationalComponent S.ρ S.Γ (rootCharHom a) i
  have hyStab : MulAut.conj y ∈ subgroupStabAut R := by
    rw [← hRi]
    exact conj_mem_subgroupStabAut_map ι hφ (map_piCenterQuot_eq_of_normalizes hbL hP.b_norm θ hφind)
  obtain ⟨f, hf, hker, hfj⟩ := exists_centralSurjection hJL θ ι hι hRi
  have hfy : ∀ j j' : ↥J, (j' : G) = b⁻¹ * (j : G) * b →
      (f j' : ModGL Tag.E6 Lf) = y * (f j : ModGL Tag.E6 Lf) * y⁻¹ := by
    intro j j' hjj'
    rw [hfj, hfj, ← hφ]
    exact congrArg ι (hφind (Subgroup.inclusion hJL j) (Subgroup.inclusion hJL j') hjj').symm
  obtain ⟨hJq, hiso, hInn⟩ := langData_of_centralSurjection hP.pcomp hP.b_norm hqs f hf hker hyStab hfy
  refine ⟨i, hyStab, hshape, hT, hap, h1, hqs, hyC, hyF, hiso, hInn, fun huniq => ?_, fun hnot hinn =>
      hout hnot (mem_inner_of_inducesInnerMod hP.core θ hβind hinn)⟩
  have hcompJ : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    ⟨hP.pcomp.1, hP.pcomp.2.1, hJq⟩
  refine ⟨hcompJ, le_antisymm (I142N.GLALayer_le_of fun K hK => ?_) (I142N.le_GLALayer hcompJ)⟩
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.2.2.1⟩
  refine le_of_map_piCenterQuot_le hJL (hK.1.trans inf_le_left) hKperf θ
    ((Subgroup.map_le_map_iff_of_injective hι).1 ?_)
  rw [hRi]
  exact (map_le_iSup_rationalComponent S hp θ hβind ι hι hrange hβ hT hap h1 hTame hK.1 hKperf).trans
    (iSup_le fun j => (huniq j.1 j.2).le)

theorem t158E6LangData_of_model (h : T158E6ModelOf) : T158E6LangData := by
  intro G _ _ L J A d b hP hcat
  obtain ⟨C, _, _, θ, β, φ, Lf, _, _, _, S, a, ι, y, -, hβind, hφind, hshape, hT, hap, h1, hι, hrange,
    hβ, hφ, hyC, hyF, hout⟩ := h G L J A d b hP hcat
  obtain ⟨i, hyStab, hdata⟩ :=
    t158E6LangData_of_modelData hP hβind hφind hshape hT hap h1 hι hrange hβ hφ hyC hyF hout
  exact ⟨Lf, inferInstance, inferInstance, inferInstance, S, a, i, y, hyStab, hdata⟩

end Main

end CFSG.LocalAnalysis.GLTheoremA.T158

end
