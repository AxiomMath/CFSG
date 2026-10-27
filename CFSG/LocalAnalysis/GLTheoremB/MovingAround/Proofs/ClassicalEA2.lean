module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims139
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.ClassicalEA
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA2

open Module CFSG.Open CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA

local notation "fixV" => CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.fixSub

theorem mem_fixV {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {E : Subgroup (V ≃ₗ[K] V)} {v : V} : v ∈ fixV E ↔ ∀ g ∈ E, g v = v :=
  Iff.rfl

theorem apply_mem_fixV_of_commute {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {E : Subgroup (V ≃ₗ[K] V)} {g : V ≃ₗ[K] V} (hc : ∀ h ∈ E, g * h = h * g) {v : V}
    (hv : v ∈ fixV E) : g v ∈ fixV E :=
  CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.apply_mem_fixSub_of_commute hc hv

section Transport

variable {X : Type} [Group X] [Finite X]

theorem core_of_model {p : ℕ} (hp : p.Prime) {M : Type*} [Group M] {J F : Subgroup X}
    (ι : ↥J →* M) (hι : Function.Injective ι) (hFJ : F ≤ J) {F₀' L' : Subgroup M}
    (hF₀' : F₀' ≤ (F.subgroupOf J).map ι)
    (hcard : Nat.card ↥((F.subgroupOf J).map ι) = p ^ 2 * Nat.card ↥F₀')
    (hLι : L' ≤ ι.range) (hLC : ∀ x ∈ L', ∀ f ∈ F₀', x * f = f * x)
    (hLN : ∀ g ∈ ι.range, (∀ f ∈ F₀', g * f = f * g) → ∀ x ∈ L', g * x * g⁻¹ ∈ L')
    (hs : IsSimpleGroup ↥L') (hnc : ∃ a b : ↥L', a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L') :
    ∃ F₀ : Subgroup X, F₀ ≤ F ∧ Nat.card F = p ^ 2 * Nat.card ↥F₀ ∧
      GLAPLayer p (J ⊓ Subgroup.centralizer (F₀ : Set X)) ≠ ⊥ := by
  set F₀ : Subgroup X := (F₀'.comap ι).map J.subtype with hF₀
  set L : Subgroup X := (L'.comap ι).map J.subtype with hL
  have hF₀F : F₀ ≤ F := by
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨k, hk, hkj⟩ := hF₀' hj
    rw [← hι hkj]
    exact Subgroup.mem_subgroupOf.1 hk
  have hcF₀ : Nat.card F₀ = Nat.card F₀' := by
    rw [hF₀, Subgroup.card_map_of_injective J.subtype_injective]
    have h1 : (F₀'.comap ι).map ι = F₀' :=
      Subgroup.map_comap_eq_self (hF₀'.trans (Subgroup.map_le_range ι _))
    conv_rhs => rw [← h1]
    rw [Subgroup.card_map_of_injective hι]
  have hcF : Nat.card F = Nat.card ↥((F.subgroupOf J).map ι) := by
    rw [Subgroup.card_map_of_injective hι]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFJ).toEquiv).symm
  set Y : Subgroup X := J ⊓ Subgroup.centralizer (F₀ : Set X) with hY
  have hLY : L ≤ Y := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_inf.2 ⟨j.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have h1 : ι (k * j) = ι (j * k) := by
      rw [map_mul, map_mul]
      exact (hLC _ hj _ hk).symm
    exact congrArg Subtype.val (hι h1)
  have hLn : (L.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hLY]
    rintro _ g ⟨j, hj, rfl⟩ hg
    obtain ⟨hgJ, hgC⟩ := Subgroup.mem_inf.1 hg
    have hcomm : ∀ f ∈ F₀', ι ⟨g, hgJ⟩ * f = f * ι ⟨g, hgJ⟩ := by
      intro f hf
      obtain ⟨k, -, rfl⟩ := hF₀' hf
      have hkF₀ : (k : X) ∈ F₀ := ⟨k, hf, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.1 hgC _ hkF₀
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h1.symm
    have h2 := hLN _ ⟨⟨g, hgJ⟩, rfl⟩ hcomm _ hj
    refine ⟨⟨g, hgJ⟩ * j * ⟨g, hgJ⟩⁻¹, ?_, by simp⟩
    show ι (⟨g, hgJ⟩ * j * ⟨g, hgJ⟩⁻¹) ∈ L'
    rw [map_mul, map_mul, map_inv]
    exact h2
  have hmapL : (L'.comap ι).map ι = L' := Subgroup.map_comap_eq_self hLι
  let eL : ↥L ≃* ↥L' :=
    (Subgroup.equivMapOfInjective _ J.subtype J.subtype_injective).symm.trans
      ((Subgroup.equivMapOfInjective _ ι hι).trans (MulEquiv.subgroupCongr hmapL))
  haveI : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hncL : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eL.symm a, eL.symm b, fun h => hab (eL.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hpL' : p ∣ Nat.card ↥L := by rwa [Nat.card_congr eL.toEquiv]
  have hcomp := GL83.PiGen.glaPComponent_of_normal_simple hp hLY hLn hncL hpL'
  refine ⟨F₀, hF₀F, by rw [hcF, hcard, hcF₀], fun hb => ?_⟩
  have hLb : L ≤ GLAPLayer p Y := le_sSup hcomp
  rw [hb] at hLb
  obtain ⟨a, b, hab⟩ := hncL
  exact hab (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 (hLb a.2),
    Subgroup.mem_bot.1 (hLb b.2)]))

theorem model_data {p : ℕ} (hp : p.Prime) {M : Type*} [Group M] {J F : Subgroup X}
    (ι : ↥J →* M) (hι : Function.Injective ι) (hFJ : F ≤ J) (hF : IsElemAbelian p F)
    (hrk : CFSG.Open.pRank p F = CFSG.Open.pRank p J) :
    IsElemAbelian p ((F.subgroupOf J).map ι) ∧
      Nat.card ↥((F.subgroupOf J).map ι) = p ^ CFSG.Open.pRank p J ∧
      ∀ A : Subgroup M, A ≤ ι.range → IsElemAbelian p A →
        Nat.card A ≤ Nat.card ↥((F.subgroupOf J).map ι) := by
  have hcF : Nat.card ↥((F.subgroupOf J).map ι) = Nat.card F := by
    rw [Subgroup.card_map_of_injective hι]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFJ).toEquiv
  refine ⟨(hF.subgroupOf J).map ι, by rw [hcF, Claims139.card_eq_pow_pRank hp hF, hrk],
    fun A hA hAel => ?_⟩
  set A' : Subgroup X := (A.comap ι).map J.subtype with hA'
  have hA'J : A' ≤ J := Subgroup.map_subtype_le _
  have hA'el : IsElemAbelian p A' := (hAel.comap hι).map J.subtype
  have hcA : Nat.card A' = Nat.card A := by
    rw [hA', Subgroup.card_map_of_injective J.subtype_injective]
    conv_rhs => rw [← Subgroup.map_comap_eq_self hA]
    rw [Subgroup.card_map_of_injective hι]
  rw [hcF, ← hcA, Claims139.card_eq_pow_pRank hp hA'el, Claims139.card_eq_pow_pRank hp hF, hrk]
  exact Nat.pow_le_pow_right hp.pos (CFSG.SectionRank.pRank_mono hp.one_lt hA'J)

end Transport

section Lin

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}

theorem two_le_finrank (hBa : ∀ x, B x x = 0) {W : Submodule (ZMod 2) V} (hW : Nondeg B W)
    (hW0 : W ≠ ⊥) : 2 ≤ finrank (ZMod 2) W := by
  have h1 : 1 ≤ finrank (ZMod 2) W := Submodule.one_le_finrank_iff.2 hW0
  by_contra h
  obtain ⟨w, hw0, hspan⟩ := finrank_eq_one_iff'.1 (by omega : finrank (ZMod 2) W = 1)
  apply hw0
  apply Subtype.ext
  rw [nondeg_iff] at hW
  refine hW w w.2 fun u hu => ?_
  obtain ⟨c, hc⟩ := hspan ⟨u, hu⟩
  have hu' : u = c • (w : V) := by
    have := congrArg Subtype.val hc
    simpa using this.symm
  rw [hu', map_smul, LinearMap.smul_apply, hBa, smul_zero]

theorem nondeg_fixV (hB : B.Nondegenerate) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEiso : ∀ g ∈ E, IsIsom B g) (hodd : Odd (Nat.card E)) : Nondeg B (fixV E) := by
  classical
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  haveI : Fintype ↥E := Fintype.ofFinite _
  rw [nondeg_iff]
  intro v hv hperp
  refine hB.2 v fun x => ?_
  have hs : (∑ g : E, (g : V ≃ₗ[ZMod 2] V) x) ∈ fixV E := by
    intro h hh
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : E)) _ _ fun g => rfl
  have h1 := hperp _ hs
  rw [map_sum, LinearMap.sum_apply] at h1
  have h2 : ∀ g : E, B ((g : V ≃ₗ[ZMod 2] V) x) v = B x v := fun g => by
    conv_lhs => rw [← (hv g g.2 : (g : V ≃ₗ[ZMod 2] V) v = v)]
    exact hEiso g g.2 x v
  simp only [h2, Finset.sum_const, Finset.card_univ] at h1
  rwa [← Nat.card_eq_fintype_card, nsmul_odd hodd] at h1

theorem commute_of_isCompl {Y Y' : Submodule (ZMod 2) V} (hc : IsCompl Y Y')
    {f x : V ≃ₗ[ZMod 2] V} (hfY : ∀ y ∈ Y, f y = y) (hfY' : ∀ z ∈ Y', f z ∈ Y')
    (hxY : ∀ y ∈ Y, x y ∈ Y) (hxY' : ∀ z ∈ Y', x z = z) : x * f = f * x := by
  refine linearEquiv_ext_of_isCompl hc (fun y hy => ?_) (fun z hz => ?_)
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfY y hy, hfY _ (hxY y hy)]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxY' _ (hfY' z hz), hxY' z hz]

theorem odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsElemAbelian p E) : Odd (Nat.card E) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

variable (hBs : ∀ x y, B x y = B y x) (hB : B.Nondegenerate)
include hBs hB

theorem two_steps {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hG : IsRestrClosed B G) {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEG : E ≤ G)
    (hE : IsElemAbelian p E)
    (hmax : ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), A ≤ G → IsElemAbelian p A → Nat.card A ≤ Nat.card E)
    (h2 : p ^ 2 ≤ Nat.card E) :
    ∃ (b₀ b₁ : V ≃ₗ[ZMod 2] V) (W₀ W₁ : Submodule (ZMod 2) V) (E₂ : Subgroup (V ≃ₗ[ZMod 2] V)),
      b₀ ∈ E ∧ b₁ ∈ E ∧ IsBlock B b₀ W₀ ∧ IsBlock B b₁ W₁ ∧ W₁ ≤ B.orthogonal W₀ ∧ E₂ ≤ E ∧
      Nat.card E = p ^ 2 * Nat.card E₂ ∧ (∀ g ∈ E₂, ∀ w ∈ W₀, g w = w) ∧
      (∀ g ∈ E₂, ∀ w ∈ W₁, g w = w) := by
  classical
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hp1 := hp.one_lt
  have hsupp : G ⊓ ptw (B.orthogonal ⊤) = G := by
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot hB, inf_eq_left]
    intro g _ x hx
    rw [(Submodule.mem_bot _).1 hx, map_zero]
  have hne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h2
    nlinarith
  obtain ⟨b₀, W₀, hb₀E, hbl₀, -, hU₁nd, -, hE₁supp, hE₁max, -, hcard₁⟩ :=
    exists_block_step hBs hB hp hp2 hG (nondeg_top hBs hB) (hEG.trans hsupp.symm.le) hE
      (fun F hF hFa => hmax F (hF.trans inf_le_left) hFa) hne
  have hne₁ : E ⊓ ptw W₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot, mul_one] at hcard₁
    rw [hcard₁] at h2
    nlinarith
  obtain ⟨b₁, W₁, hb₁E, hbl₁, hW₁U, -, -, -, -, -, hcard₂⟩ :=
    exists_block_step hBs hB hp hp2 hG hU₁nd hE₁supp (hE.mono inf_le_left) hE₁max hne₁
  refine ⟨b₀, b₁, W₀, W₁, (E ⊓ ptw W₀) ⊓ ptw W₁, hb₀E, (Subgroup.mem_inf.1 hb₁E).1, hbl₀, hbl₁,
    fun w hw => (Submodule.mem_inf.1 (hW₁U hw)).2, inf_le_left.trans inf_le_left, ?_,
    fun g hg => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2,
    fun g hg => (Subgroup.mem_inf.1 hg).2⟩
  rw [hcard₁, hcard₂]
  ring

end Lin

section SpSub

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (restrictHom)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}

@[expose] def spPtw (B : LinearMap.BilinForm (ZMod 2) V) (Y : Submodule (ZMod 2) V) :
    Subgroup (V ≃ₗ[ZMod 2] V) :=
  TauCeti.BilinForm.isometryGroup B ⊓ ptw (B.orthogonal Y)

theorem mem_spPtw {Y : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ spPtw B Y ↔ IsIsom B g ∧ ∀ x ∈ B.orthogonal Y, g x = x := by
  unfold spPtw
  rw [Subgroup.mem_inf, TauCeti.BilinForm.mem_isometryGroup_iff, mem_ptw]
  rfl

theorem J_eq_fromBlocks (m : ℕ) :
    Matrix.J (Fin m) (ZMod 2) = Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with a | a <;> rcases j with c | c <;>
    simp [Matrix.J, ZMod.neg_eq_self_mod_two]

theorem congr_equivFun_eq_spForm {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {C : LinearMap.BilinForm (ZMod 2) W} {m : ℕ} (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) W)
    (hb : LinearMap.BilinForm.toMatrix b C = Matrix.J (Fin m) (ZMod 2)) :
    LinearMap.BilinForm.congr b.equivFun C = spForm m := by
  classical
  have hsym : ∀ i, b.equivFun.symm (Pi.single i 1) = b i := by
    intro i
    rw [LinearEquiv.symm_apply_eq]
    funext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun (ZMod 2) (Fin m ⊕ Fin m)) fun i j => ?_
  rw [LinearMap.BilinForm.congr_apply, Pi.basisFun_apply, Pi.basisFun_apply, hsym, hsym]
  have h1 := congrFun (congrFun hb i) j
  rw [LinearMap.BilinForm.toMatrix_apply] at h1
  rw [h1, J_eq_fromBlocks, spForm, Matrix.toBilin'_single]

theorem exists_statedSp_equiv {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {C : LinearMap.BilinForm (ZMod 2) W} (hCa : C.IsAlt)
    (hC : C.Nondegenerate) :
    ∃ m : ℕ, finrank (ZMod 2) W = 2 * m ∧
      Nonempty (↥(TauCeti.BilinForm.isometryGroup C) ≃* ↥(StatedSp m (ZMod 2))) := by
  obtain ⟨m, b, hb⟩ := hCa.exists_basis_toMatrix_eq_J hC
  refine ⟨m, ?_, ?_⟩
  · rw [finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin]
    ring
  · obtain ⟨Φ⟩ := nonempty_statedSp_mulEquiv m
    exact ⟨(TauCeti.BilinForm.isometryGroupCongr C b.equivFun).trans
      ((MulEquiv.subgroupCongr (congrArg TauCeti.BilinForm.isometryGroup
        (congr_equivFun_eq_spForm b hb))).trans Φ.symm)⟩

variable (hBs : ∀ x y, B x y = B y x) (hB : B.Nondegenerate)
include hBs hB

theorem spPtw_le_stabSub {Y : Submodule (ZMod 2) V} :
    spPtw B Y ≤ CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.stabSub Y := by
  intro g hg w
  obtain ⟨hgi, hgY⟩ := mem_spPtw.1 hg
  obtain ⟨hgi', hgY'⟩ := mem_spPtw.1 ((spPtw B Y).inv_mem hg)
  constructor
  · intro hw
    exact apply_mem_of_ptw hBs hB hgi hgY hw
  · intro hw
    have := apply_mem_of_ptw hBs hB hgi' hgY' hw
    rwa [inv_apply_eq_of_apply_eq rfl] at this

theorem nonempty_spPtw_mulEquiv {Y : Submodule (ZMod 2) V} (hY : Nondeg B Y) :
    Nonempty (↥(spPtw B Y) ≃* ↥(TauCeti.BilinForm.isometryGroup (B.restrict Y))) := by
  classical
  have hc : IsCompl Y (B.orthogonal Y) := isCompl_of_nondeg hBs hY
  let ρ : ↥(spPtw B Y) →* (↥Y ≃ₗ[ZMod 2] ↥Y) :=
    (restrictHom Y).comp (Subgroup.inclusion (spPtw_le_stabSub hBs hB))
  have hρ : ∀ (g : ↥(spPtw B Y)) (y : ↥Y), ((ρ g y : ↥Y) : V) = (g : V ≃ₗ[ZMod 2] V) y :=
    fun g y => rfl
  have hmem : ∀ g, ρ g ∈ TauCeti.BilinForm.isometryGroup (B.restrict Y) := by
    intro g
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    intro x y
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.BilinForm.restrict_apply,
      LinearMap.domRestrict_apply, LinearMap.domRestrict_apply, hρ, hρ]
    exact (mem_spPtw.1 g.2).1 x y
  let ρ' : ↥(spPtw B Y) →* ↥(TauCeti.BilinForm.isometryGroup (B.restrict Y)) :=
    ρ.codRestrict _ hmem
  have hinj : Function.Injective ρ' := by
    intro g h hgh
    have h1 : ∀ y : ↥Y, (g : V ≃ₗ[ZMod 2] V) y = (h : V ≃ₗ[ZMod 2] V) y := fun y => by
      have := congrArg (fun σ : ↥(TauCeti.BilinForm.isometryGroup (B.restrict Y)) =>
        (((σ : ↥Y ≃ₗ[ZMod 2] ↥Y) y : ↥Y) : V)) hgh
      exact this
    apply Subtype.ext
    exact linearEquiv_ext_of_isCompl hc (fun w hw => h1 ⟨w, hw⟩)
      (fun x hx => by rw [(mem_spPtw.1 g.2).2 x hx, (mem_spPtw.1 h.2).2 x hx])
  have hsurj : Function.Surjective ρ' := by
    rintro ⟨σ, hσ⟩
    rw [TauCeti.BilinForm.mem_isometryGroup_iff] at hσ
    let e := Submodule.prodEquivOfIsCompl Y (B.orthogonal Y) hc
    let g : V ≃ₗ[ZMod 2] V := e.symm.trans ((σ.prodCongr (LinearEquiv.refl _ _)).trans e)
    have hgY : ∀ y : ↥Y, g y = σ y := fun y => by
      simp [g, e, Submodule.prodEquivOfIsCompl_symm_apply_left]
    have hgY' : ∀ z : ↥(B.orthogonal Y), g z = z := fun z => by
      simp [g, e, Submodule.prodEquivOfIsCompl_symm_apply_right]
    have hgiso : IsIsom B g := by
      intro v v'
      obtain ⟨y, hy, z, hz, rfl⟩ := exists_add_of_isCompl hc v
      obtain ⟨y', hy', z', hz', rfl⟩ := exists_add_of_isCompl hc v'
      have e1 := hgY ⟨y, hy⟩
      have e2 := hgY ⟨y', hy'⟩
      have e3 := hgY' ⟨z, hz⟩
      have e4 := hgY' ⟨z', hz'⟩
      simp only at e1 e2 e3 e4
      have hσyy := hσ ⟨y, hy⟩ ⟨y', hy'⟩
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.BilinForm.restrict_apply,
        LinearMap.domRestrict_apply, LinearMap.domRestrict_apply] at hσyy
      have o1 : ∀ u ∈ Y, ∀ w ∈ B.orthogonal Y, B u w = 0 := fun u hu w hw => hw u hu
      have o2 : ∀ u ∈ Y, ∀ w ∈ B.orthogonal Y, B w u = 0 := fun u hu w hw => by
        rw [hBs]; exact hw u hu
      rw [map_add g y z, map_add g y' z', e1, e2, e3, e4]
      simp only [map_add, LinearMap.add_apply]
      rw [hσyy, o1 _ (σ ⟨y, hy⟩).2 _ hz', o2 _ (σ ⟨y', hy'⟩).2 _ hz, o1 _ hy _ hz',
        o2 _ hy' _ hz]
    have hgmem : g ∈ spPtw B Y := mem_spPtw.2 ⟨hgiso, fun x hx => hgY' ⟨x, hx⟩⟩
    refine ⟨⟨g, hgmem⟩, Subtype.ext (LinearEquiv.ext fun y => Subtype.ext ?_)⟩
    show g y = (σ y : V)
    exact hgY y
  exact ⟨MulEquiv.ofBijective ρ' ⟨hinj, hsurj⟩⟩

end SpSub

section SpFacts

theorem sp_comm_facts {m : ℕ} (hm : 2 ≤ m) :
    IsSimpleGroup ↥(commutator ↥(StatedSp m (ZMod 2))) ∧
      (∃ a b : ↥(commutator ↥(StatedSp m (ZMod 2))), a * b ≠ b * a) ∧
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card ↥(StatedSp m (ZMod 2)) →
        q ∣ Nat.card ↥(commutator ↥(StatedSp m (ZMod 2))) := by
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
  · obtain ⟨e0⟩ := OmegaFacts.nonempty_statedSp_two_mulEquiv_perm_six
    have hmap : (commutator ↥(StatedSp 2 (ZMod 2))).map e0.toMonoidHom =
        alternatingGroup (Fin 6) := by
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e0.surjective, ← _root_.commutator_def,
        alternatingGroup.commutator_perm_eq (by simp)]
    let f : ↥(commutator ↥(StatedSp 2 (ZMod 2))) ≃* ↥(alternatingGroup (Fin 6)) :=
      (Subgroup.equivMapOfInjective _ e0.toMonoidHom e0.injective).trans
        (MulEquiv.subgroupCongr hmap)
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have hA : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      have h := CFSG.HardMathSupport.Curtis.Coordinator.PLType.two_mul_card_alt_fin 6 (by norm_num)
      have h6 : Nat.factorial 6 = 720 := by decide
      omega
    have hS : Nat.card ↥(StatedSp 2 (ZMod 2)) = 720 := by
      rw [OmegaFacts.card_statedSp_zmod_two]
      decide
    refine ⟨f.isSimpleGroup, ?_, fun q hq hq2 hdvd => ?_⟩
    · by_contra hcon
      push Not at hcon
      have hZ : Subgroup.center (alternatingGroup (Fin 6)) = ⊤ :=
        eq_top_iff.2 fun a _ => Subgroup.mem_center_iff.2 fun b => by
          apply f.symm.injective
          rw [map_mul, map_mul]
          exact hcon _ _
      rw [alternatingGroup.center_eq_bot (by simp)] at hZ
      haveI : Nontrivial (alternatingGroup (Fin 6)) :=
        alternatingGroup.nontrivial_of_three_le_card (by simp)
      exact bot_ne_top hZ
    · rw [Nat.card_congr f.toEquiv, hA]
      rw [hS, show (720 : ℕ) = 2 * 360 by norm_num] at hdvd
      exact Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hq Nat.prime_two).2 hq2) hdvd
  · haveI : IsSimpleGroup ↥(StatedSp m (ZMod 2)) := OmegaFacts.isSimpleGroup_statedSp_zmod_two h3
    have hperf : commutator ↥(StatedSp m (ZMod 2)) = ⊤ :=
      (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp m (ZMod 2)
        (Or.inr (Or.inr ⟨Nat.card_zmod 2, h3⟩))).commutator_eq_top
    let f : ↥(commutator ↥(StatedSp m (ZMod 2))) ≃* ↥(StatedSp m (ZMod 2)) :=
      (MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv
    refine ⟨f.isSimpleGroup, ?_, fun q _ _ hdvd => by rwa [Nat.card_congr f.toEquiv]⟩
    obtain ⟨a, b, hab⟩ :=
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_noncomm_of_perfect hperf
    exact ⟨f.symm a, f.symm b, fun h => hab (f.symm.injective (by rw [map_mul, map_mul, h]))⟩

end SpFacts

section SpGeom

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}

theorem ne_one_of_isBlock {b : V ≃ₗ[ZMod 2] V} {W : Submodule (ZMod 2) V} (hW : IsBlock B b W) :
    b ≠ 1 := by
  intro h
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.2.1
  exact hw0 (hW.2.2.2.2.1 w hw (by rw [h]; rfl))

theorem fixV_facts (hBs : ∀ x y, B x y = B y x) (hB : B.Nondegenerate) (hBa : B.IsAlt) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E E₂ : Subgroup (V ≃ₗ[ZMod 2] V)} (hEiso : ∀ g ∈ E, IsIsom B g)
    (hE : IsElemAbelian p E) (hE₂E : E₂ ≤ E) {b₀ b₁ : V ≃ₗ[ZMod 2] V} {W₀ W₁ : Submodule (ZMod 2) V}
    (hbl₀ : IsBlock B b₀ W₀) (hbl₁ : IsBlock B b₁ W₁) (hW₁₀ : W₁ ≤ B.orthogonal W₀)
    (hE₂W₀ : ∀ g ∈ E₂, ∀ w ∈ W₀, g w = w) (hE₂W₁ : ∀ g ∈ E₂, ∀ w ∈ W₁, g w = w) :
    Nondeg B (fixV E₂) ∧ W₀ ≤ fixV E₂ ∧ W₁ ≤ fixV E₂ ∧ W₀ ⊓ W₁ = ⊥ ∧
      4 ≤ finrank (ZMod 2) ↥(W₀ ⊔ W₁) ∧ 4 ≤ finrank (ZMod 2) ↥(fixV E₂) := by
  have hYnd : Nondeg B (fixV E₂) := nondeg_fixV hB (fun g hg => hEiso g (hE₂E hg))
    (odd_card_of_isElemAbelian hp hp2 (hE.mono hE₂E))
  have hW₀Y : W₀ ≤ fixV E₂ := fun w hw g hg => hE₂W₀ g hg w hw
  have hW₁Y : W₁ ≤ fixV E₂ := fun w hw g hg => hE₂W₁ g hg w hw
  have hd₀ := two_le_finrank hBa hbl₀.1 hbl₀.2.1
  have hd₁ := two_le_finrank hBa hbl₁.1 hbl₁.2.1
  have hinf : W₀ ⊓ W₁ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    exact (Submodule.disjoint_def.1 hbl₀.1) w hw.1 (hW₁₀ hw.2)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W₀ W₁
  rw [hinf, finrank_bot] at h1
  have h2 := Submodule.finrank_mono (sup_le hW₀Y hW₁Y)
  exact ⟨hYnd, hW₀Y, hW₁Y, hinf, by omega, by omega⟩

theorem sp_geom (hBs : ∀ x y, B x y = B y x) (hB : B.Nondegenerate) (hBa : B.IsAlt) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEG : E ≤ TauCeti.BilinForm.isometryGroup B) (hE : IsElemAbelian p E)
    (hmax : ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), A ≤ TauCeti.BilinForm.isometryGroup B →
      IsElemAbelian p A → Nat.card A ≤ Nat.card E) (h2 : p ^ 2 ≤ Nat.card E) :
    ∃ F₀' L' : Subgroup (V ≃ₗ[ZMod 2] V), F₀' ≤ E ∧ Nat.card E = p ^ 2 * Nat.card F₀' ∧
      L' ≤ TauCeti.BilinForm.isometryGroup B ∧ (∀ x ∈ L', ∀ f ∈ F₀', x * f = f * x) ∧
      (∀ g ∈ TauCeti.BilinForm.isometryGroup B, (∀ f ∈ F₀', g * f = f * g) →
        ∀ x ∈ L', g * x * g⁻¹ ∈ L') ∧
      IsSimpleGroup ↥L' ∧ (∃ a b : ↥L', a * b ≠ b * a) ∧ p ∣ Nat.card ↥L' := by
  classical
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  set G := TauCeti.BilinForm.isometryGroup B with hG
  have hGiso : ∀ g ∈ G, IsIsom B g := fun g hg => TauCeti.BilinForm.mem_isometryGroup_iff.1 hg
  obtain ⟨b₀, b₁, W₀, W₁, E₂, hb₀E, hb₁E, hbl₀, hbl₁, hW₁₀, hE₂E, hcard, hE₂W₀, hE₂W₁⟩ :=
    two_steps hBs hB hp hp2 (isRestrClosed_isometryGroup hBs) hEG hE hmax h2
  obtain ⟨hYnd, hW₀Y, -, -, -, hdY⟩ := fixV_facts hBs hB hBa hp hp2
    (fun g hg => hGiso g (hEG hg)) hE hE₂E hbl₀ hbl₁ hW₁₀ hE₂W₀ hE₂W₁
  set Y := fixV E₂ with hY
  set H := spPtw B Y with hH
  obtain ⟨ψ₁⟩ := nonempty_spPtw_mulEquiv hBs hB hYnd
  have hBYa : (B.restrict Y).IsAlt := fun x => hBa x
  have hBYnd : (B.restrict Y).Nondegenerate :=
    B.nondegenerate_restrict_of_disjoint_orthogonal (isRefl_of_symm hBs) hYnd
  obtain ⟨m, hm, ⟨ψ₂⟩⟩ := exists_statedSp_equiv hBYa hBYnd
  let ψ : ↥H ≃* ↥(StatedSp m (ZMod 2)) := ψ₁.trans ψ₂
  obtain ⟨hsS, hncS, hdvdS⟩ := sp_comm_facts (m := m) (by omega)
  set L' := ⁅H, H⁆ with hL'
  have h1 : (commutator ↥H).map H.subtype = L' := Subgroup.map_subtype_commutator H
  have h1' : (commutator ↥H).map ψ.toMonoidHom = commutator ↥(StatedSp m (ZMod 2)) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ ψ.surjective, ← _root_.commutator_def]
  let eL : ↥L' ≃* ↥(commutator ↥(StatedSp m (ZMod 2))) :=
    (MulEquiv.subgroupCongr h1.symm).trans
      ((Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).symm.trans
        ((Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
          (MulEquiv.subgroupCongr h1')))
  have hLH : L' ≤ H := by
    rw [← h1]
    exact Subgroup.map_subtype_le _
  have hb₀H : b₀ ∈ H := mem_spPtw.2 ⟨hGiso b₀ (hEG hb₀E),
    fun x hx => hbl₀.2.2.2.1 x (LinearMap.BilinForm.orthogonal_le hW₀Y hx)⟩
  have hb₀1 := ne_one_of_isBlock hbl₀
  have hpH : p ∣ Nat.card ↥H := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (⟨b₀, hb₀H⟩ : ↥H) = p :=
      orderOf_eq_prime (Subtype.ext (hE.2 b₀ hb₀E)) (fun h => hb₀1 (congrArg Subtype.val h))
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hpL : p ∣ Nat.card ↥L' := by
    rw [Nat.card_congr eL.toEquiv]
    exact hdvdS p hp hp2 (by rwa [← Nat.card_congr ψ.toEquiv])
  have hc : IsCompl Y (B.orthogonal Y) := isCompl_of_nondeg hBs hYnd
  have hHE₂ : ∀ x ∈ H, ∀ f ∈ E₂, x * f = f * x := by
    intro x hx f hf
    obtain ⟨hxi, hxY⟩ := mem_spPtw.1 hx
    have hfY : ∀ y ∈ Y, f y = y := fun y hy => mem_fixV.1 hy f hf
    exact commute_of_isCompl hc hfY
      (fun z hz => apply_mem_orth_of_ptw hBs (hGiso f (hEG (hE₂E hf))) hfY hz)
      (fun y hy => apply_mem_of_ptw hBs hB hxi hxY hy) hxY
  haveI := hsS
  refine ⟨E₂, L', hE₂E, hcard, hLH.trans inf_le_left, fun x hx f hf => hHE₂ x (hLH hx) f hf,
    ?_, eL.isSimpleGroup, ?_, hpL⟩
  ·
    intro g hg hgc x hx
    have hg'c : ∀ f ∈ E₂, g⁻¹ * f = f * g⁻¹ := fun f hf =>
      (Commute.inv_left (hgc f hf : Commute g f)).eq
    have hg'Y : ∀ y ∈ Y, g⁻¹ y ∈ Y := fun y hy => apply_mem_fixV_of_commute hg'c hy
    have hHg : H.map (MulAut.conj g).toMonoidHom = H := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨h, hh, rfl⟩
        obtain ⟨hhi, hhY⟩ := mem_spPtw.1 hh
        refine mem_spPtw.2 ⟨hGiso _ (G.mul_mem (G.mul_mem hg
          (TauCeti.BilinForm.mem_isometryGroup_iff.2 hhi)) (G.inv_mem hg)), fun z hz => ?_⟩
        have hz' : g⁻¹ z ∈ B.orthogonal Y :=
          apply_mem_orth_of_invariant hBs (hGiso _ (G.inv_mem hg)) hg'Y hz
        show g (h (g⁻¹ z)) = z
        rw [hhY _ hz', apply_inv_apply]
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hmap := Subgroup.map_commutator H H (MulAut.conj g).toMonoidHom
    rw [hHg] at hmap
    have hx' : (MulAut.conj g).toMonoidHom x ∈ L'.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [hL', hmap] at hx'
    simpa [MulAut.conj_apply] using hx'
  · obtain ⟨a, b, hab⟩ := hncS
    exact ⟨eL.symm a, eL.symm b, fun h => hab (eL.symm.injective (by rw [map_mul, map_mul, h]))⟩

end SpGeom

section CoreSp

variable {X : Type} [Group X] [Finite X]

theorem not_pow_three_dvd_720 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 3 ∣ 720 := by
  intro hd
  have hle : p ^ 3 ≤ 720 := Nat.le_of_dvd (by norm_num) hd
  have hp8 : p ≤ 8 := by
    by_contra h9
    have : 9 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases p <;> first | exact hp2 rfl | (revert hd; decide) | (revert hp; decide)

theorem card_statedSp_dvd_720 {n : ℕ} (hn : n ≤ 2) : Nat.card ↥(StatedSp n (ZMod 2)) ∣ 720 := by
  rw [OmegaFacts.card_statedSp_zmod_two]
  interval_cases n <;> decide

theorem core_sp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} {J F : Subgroup X}
    (e : ↥J ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ :
      Subgroup (GL (Fin n ⊕ Fin n) (ZMod 2))))
    (hFJ : F ≤ J) (hF : IsElemAbelian p F) (hrk : CFSG.Open.pRank p F = CFSG.Open.pRank p J)
    (h3 : 3 ≤ CFSG.Open.pRank p J) :
    ∃ F₀ : Subgroup X, F₀ ≤ F ∧ Nat.card F = p ^ 2 * Nat.card ↥F₀ ∧
      GLAPLayer p (J ⊓ Subgroup.centralizer (F₀ : Set X)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set S := StatedSp n (ZMod 2) with hS
  have hSS' : Nat.card ↥(⁅S, S⁆) ∣ Nat.card ↥S := by
    rw [← Subgroup.map_subtype_commutator S, Subgroup.card_map_of_injective S.subtype_injective]
    exact Subgroup.card_subgroup_dvd_card _
  have hp3 : p ^ 3 ∣ Nat.card ↥J := by
    obtain ⟨A, hAJ, -, hAc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h3
    rw [← hAc]
    exact Subgroup.card_dvd_of_le hAJ
  rcases Nat.lt_or_ge n 3 with hn | hn
  · exfalso
    refine not_pow_three_dvd_720 hp hp2 (hp3.trans ?_)
    rw [Nat.card_congr e.toEquiv]
    exact hSS'.trans (card_statedSp_dvd_720 (by omega))
  haveI hSs : IsSimpleGroup ↥S := OmegaFacts.isSimpleGroup_statedSp_zmod_two hn
  have hperf : commutator ↥S = ⊤ :=
    (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n (ZMod 2)
      (Or.inr (Or.inr ⟨Nat.card_zmod 2, hn⟩))).commutator_eq_top
  have hSS : ⁅S, S⁆ = S := by
    rw [← Subgroup.map_subtype_commutator S, hperf, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  let e₁ : ↥J ≃* ↥S := e.trans (MulEquiv.subgroupCongr hSS)
  obtain ⟨Φ₀⟩ := nonempty_statedSp_mulEquiv n
  set G := TauCeti.BilinForm.isometryGroup (spForm n) with hG
  let Φ : ↥J ≃* ↥G := e₁.trans Φ₀
  let ι : ↥J →* ((Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2)) :=
    G.subtype.comp Φ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp Φ.injective
  have hrange : ι.range = G := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (Φ x).2
    · intro hg
      exact ⟨Φ.symm ⟨g, hg⟩, by simp [ι]⟩
  obtain ⟨hF'el, hF'card, hF'max⟩ := model_data hp ι hι hFJ hF hrk
  have hF'G : (F.subgroupOf J).map ι ≤ G := by
    rw [← hrange]
    exact Subgroup.map_le_range ι _
  have h2 : p ^ 2 ≤ Nat.card ↥((F.subgroupOf J).map ι) := by
    rw [hF'card]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  obtain ⟨F₀', L', hF₀', hcard, hLG, hLC, hLN, hs, hnc, hpL⟩ :=
    sp_geom (spForm_symm n) (spForm_nondegenerate n) (spForm_isAlt n) hp hp2 hF'G hF'el
      (fun A hA hAel => hF'max A (hA.trans hrange.ge) hAel) h2
  exact core_of_model hp ι hι hFJ hF₀' hcard (hLG.trans hrange.ge) hLC
    (fun g hg => hLN g (hrange.le hg)) hs hnc hpL

end CoreSp

section Prod

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}

theorem exists_prod_blocks {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} {b : Fin r → V ≃ₗ[ZMod 2] V}
    {W : Fin r → Submodule (ZMod 2) V} (hbE : ∀ i, b i ∈ E) (hbl : ∀ i, IsBlock B (b i) (W i))
    (horth : ∀ i j, i ≠ j → W i ≤ B.orthogonal (W j)) (S : Finset (Fin r)) :
    ∃ g ∈ E, (∀ i ∈ S, ∀ w ∈ W i, g w = b i w) ∧ (∀ i ∉ S, ∀ w ∈ W i, g w = w) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, fun i hi => by simp at hi, fun i _ w _ => rfl⟩
  | insert a S haS ih =>
    obtain ⟨g, hgE, hg1, hg2⟩ := ih
    refine ⟨b a * g, mul_mem (hbE a) hgE, fun i hi w hw => ?_, fun i hi w hw => ?_⟩
    · rw [LinearEquiv.mul_apply]
      rcases Finset.mem_insert.1 hi with rfl | hiS
      · rw [hg2 i haS w hw]
      · have hia : i ≠ a := fun h => haS (h ▸ hiS)
        rw [hg1 i hiS w hw]
        exact (hbl a).2.2.2.1 _ (horth i a hia ((hbl i).2.2.1 w hw))
    · have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self a S)
      have hiS : i ∉ S := fun h => hi (Finset.mem_insert_of_mem h)
      rw [LinearEquiv.mul_apply, hg2 i hiS w hw]
      exact (hbl a).2.2.2.1 w (horth i a hia hw)

theorem mem_fixV_of_prod (hBs : ∀ x y, B x y = B y x) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEiso : ∀ e ∈ E, IsIsom B e) {r : ℕ} {b : Fin r → V ≃ₗ[ZMod 2] V}
    {W : Fin r → Submodule (ZMod 2) V} (hbl : ∀ i, IsBlock B (b i) (W i))
    (hcl : E = Subgroup.closure (Set.range b)) {g : V ≃ₗ[ZMod 2] V} (hgE : g ∈ E)
    (hg : ∀ i, ∀ w ∈ W i, g w = b i w) {v : V} (hv : g v = v) : v ∈ fixV E := by
  have hbv : ∀ i, b i v = v := by
    intro i
    obtain ⟨w, hw, x, hx, rfl⟩ := exists_add_of_isCompl (isCompl_of_nondeg hBs (hbl i).1) v
    have hgW : ∀ u ∈ W i, g u ∈ W i := fun u hu => by
      rw [hg i u hu]
      exact (hbl i).2.2.1 u hu
    have hgx : g x ∈ B.orthogonal (W i) := apply_mem_orth_of_invariant hBs (hEiso g hgE) hgW hx
    rw [map_add, hg i w hw] at hv
    have h1 : b i w - w = x - g x := by
      calc b i w - w = (b i w + g x) - (w + g x) := by abel
        _ = (w + x) - (w + g x) := by rw [hv]
        _ = x - g x := by abel
    have h2 : b i w - w ∈ W i := sub_mem ((hbl i).2.2.1 w hw) hw
    have h3 : b i w - w ∈ B.orthogonal (W i) := h1 ▸ sub_mem hx hgx
    have h4 : b i w - w = 0 := (Submodule.disjoint_def.1 (hbl i).1) _ h2 h3
    have hw0 : w = 0 := (hbl i).2.2.2.2.1 w hw (sub_eq_zero.1 h4)
    subst hw0
    rw [zero_add]
    exact (hbl i).2.2.2.1 x hx
  rw [hcl]
  intro e he
  induction he using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hbv i
  | one => rfl
  | mul a c _ _ iha ihc => rw [LinearEquiv.mul_apply, ihc, iha]
  | inv a _ iha => exact inv_apply_eq_of_apply_eq iha

theorem exists_fpf_of_fixV_eq_bot (hBs : ∀ x y, B x y = B y x) (hB : B.Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {G : Subgroup (V ≃ₗ[ZMod 2] V)} (hG : IsRestrClosed B G)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEG : E ≤ G) (hE : IsElemAbelian p E)
    (hmax : ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), A ≤ G → IsElemAbelian p A → Nat.card A ≤ Nat.card E)
    (hbot : fixV E = ⊥) : ∃ g ∈ E, ∀ v, g v = v → v = 0 := by
  classical
  have hsupp : G ⊓ ptw (B.orthogonal ⊤) = G := by
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot hB, inf_eq_left]
    intro g _ x hx
    rw [(Submodule.mem_bot _).1 hx, map_zero]
  obtain ⟨r, b, W, hbE, hbl, -, horth, hcl, -⟩ :=
    hasBlocks_of_max hBs hB hp hp2 hG _ ⊤ rfl (nondeg_top hBs hB) E (hEG.trans hsupp.symm.le) hE
      (fun F hF hFa => hmax F (hF.trans inf_le_left) hFa)
  obtain ⟨g, hgE, hg, -⟩ := exists_prod_blocks hbE hbl horth Finset.univ
  refine ⟨g, hgE, fun v hv => ?_⟩
  have h1 := mem_fixV_of_prod hBs (fun e he => hG.1 e (hEG he)) hbl hcl hgE
    (fun i w hw => hg i (Finset.mem_univ i) w hw) hv
  rw [hbot] at h1
  exact (Submodule.mem_bot _).1 h1

end Prod

section OmegaGeom

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (orthJ orthJEquiv orthJRestrict
  orthJRestrict_surjective apply_eq_of_mem_orthJ orthJ_le_stabSub orthJ_le_elementaryGroup
  conj_mem_orthJ perpSub isCompl_perpSub IsStdSpace)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem mem_elementaryGroup_of_pow {ε : Bool} {m : ℕ} (hm : 2 ≤ m) (hε : ε = true → 3 ≤ m)
    (hstd : IsStdSpace ε Q m) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {N : ℕ} (hN : Odd N) (hgN : g ^ N = 1) :
    g ∈ elementaryGroup Q := by
  cases ε
  · exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.mem_elementaryGroup_of_odd_pow_of_isMinusSpace
      hm hstd hg hN hgN
  · exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.mem_elementaryGroup_of_odd_pow_of_isPlusSpace
      (hε rfl) hstd hg hN hgN

theorem perpSub_eq_orthogonal (W : Submodule (ZMod 2) V) :
    perpSub Q W = LinearMap.BilinForm.orthogonal (polarBilin Q) W := by
  ext v
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun w _ => ?_
  rw [polarBilin_apply_apply, polar_comm]

theorem fixV_ne_bot (hQ : (polarBilin Q).Nondegenerate) {ε : Bool} {n : ℕ} (hn : 1 ≤ n)
    (hstd : IsStdSpace ε Q (n + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfp : HasFixedPointFreeOrder ε n p) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hE : IsElemAbelian p E)
    (hmax : ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), A ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      IsElemAbelian p A → Nat.card A ≤ Nat.card E) : fixV E ≠ ⊥ := by
  intro hbot
  obtain ⟨g, hgE, hfix⟩ := exists_fpf_of_fixV_eq_bot (polarBilin_symm Q) hQ hp hp2
    (isRestrClosed_orthogonalGroup Q) hEO hE hmax hbot
  have hdvd := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.dvd_of_fpf hstd
    (fun _ => by omega) hp g (fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hEO hgE) v)
    (hE.2 g hgE) hfix
  exact OmegaFacts2.not_dvd_sign_succ hp hp2 hn hfp hdvd

theorem omega_geom (hQ : (polarBilin Q).Nondegenerate) {ε : Bool} {n : ℕ} (hn : 1 ≤ n)
    (hstd : IsStdSpace ε Q (n + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfp : HasFixedPointFreeOrder ε n p) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEG : E ≤ elementaryGroup Q) (hE : IsElemAbelian p E)
    (hmax : ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), A ≤ elementaryGroup Q → IsElemAbelian p A →
      Nat.card A ≤ Nat.card E) (h2 : p ^ 2 ≤ Nat.card E) :
    ∃ F₀' L' : Subgroup (V ≃ₗ[ZMod 2] V), F₀' ≤ E ∧ Nat.card E = p ^ 2 * Nat.card F₀' ∧
      L' ≤ elementaryGroup Q ∧ (∀ x ∈ L', ∀ f ∈ F₀', x * f = f * x) ∧
      (∀ g ∈ elementaryGroup Q, (∀ f ∈ F₀', g * f = f * g) → ∀ x ∈ L', g * x * g⁻¹ ∈ L') ∧
      IsSimpleGroup ↥L' ∧ (∃ a b : ↥L', a * b ≠ b * a) ∧ p ∣ Nat.card ↥L' := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hε : ε = true → 2 ≤ n := by
    rintro rfl
    by_contra h
    obtain rfl : n = 1 := by omega
    exact CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2 hfp
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hBs := polarBilin_symm Q
  have hBa : (polarBilin Q).IsAlt := fun x => by
    rw [polarBilin_apply_apply]
    exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.polar_self_f2 x
  have hOiso : ∀ g ∈ O, IsIsom (polarBilin Q) g := fun g hg => isIsom_of_mem hg
  have hEO : E ≤ O := hEG.trans (elementaryGroup_le_orthogonalGroup Q)
  have hmaxO : ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), A ≤ O → IsElemAbelian p A →
      Nat.card A ≤ Nat.card E := fun A hA hAel =>
    hmax A (fun g hg => mem_elementaryGroup_of_pow (by omega) (fun h => by have := hε h; omega)
      hstd (hA hg) hpo (hAel.2 g hg)) hAel
  obtain ⟨b₀, b₁, W₀, W₁, E₂, hb₀E, hb₁E, hbl₀, hbl₁, hW₁₀, hE₂E, hcard, hE₂W₀, hE₂W₁⟩ :=
    two_steps hBs hQ hp hp2 (isRestrClosed_orthogonalGroup Q) hEO hE hmaxO h2
  obtain ⟨hYnd, hW₀Y, hW₁Y, -, -, -⟩ := fixV_facts hBs hQ hBa hp hp2
    (fun g hg => hOiso g (hEO hg)) hE hE₂E hbl₀ hbl₁ hW₁₀ hE₂W₀ hE₂W₁
  set Y := fixV E₂ with hY
  have hCne := fixV_ne_bot hQ hn hstd hp hp2 hfp hEO hE hmaxO
  have hCnd : Nondeg (polarBilin Q) (fixV E) := nondeg_fixV hQ (fun g hg => hOiso g (hEO hg))
    (odd_card_of_isElemAbelian hp hp2 hE)
  have hdC := two_le_finrank hBa hCnd hCne
  have hd₀ := two_le_finrank hBa hbl₀.1 hbl₀.2.1
  have hd₁ := two_le_finrank hBa hbl₁.1 hbl₁.2.1
  have hCY : fixV E ≤ Y := fun v hv g hg => mem_fixV.1 hv g (hE₂E hg)
  have hinf : W₀ ⊓ W₁ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    exact (Submodule.disjoint_def.1 hbl₀.1) w hw.1 (hW₁₀ hw.2)
  have hinfC : (W₀ ⊔ W₁) ⊓ fixV E = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := Submodule.mem_sup.1 hv1
    have h1 : b₀ (w₀ + w₁) = w₀ + w₁ := mem_fixV.1 hv2 b₀ hb₀E
    rw [map_add, hbl₀.2.2.2.1 w₁ (hW₁₀ hw₁), add_left_inj] at h1
    have hw₀0 : w₀ = 0 := hbl₀.2.2.2.2.1 w₀ hw₀ h1
    subst hw₀0
    rw [zero_add] at hv2 ⊢
    exact (Submodule.mem_bot _).2 (hbl₁.2.2.2.2.1 w₁ hw₁ (mem_fixV.1 hv2 b₁ hb₁E))
  have hdY : 6 ≤ finrank (ZMod 2) ↥Y := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W₀ W₁
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (W₀ ⊔ W₁) (fixV E)
    rw [hinf, finrank_bot] at h1
    rw [hinfC, finrank_bot] at h2
    have h3 := Submodule.finrank_mono (sup_le (sup_le hW₀Y hW₁Y) hCY)
    omega
  have hYp : PolarNondegOn Q Y := by
    intro x hx hxx
    rw [nondeg_iff] at hYnd
    exact hYnd x hx fun u hu => by rw [polarBilin_apply_apply, polar_comm]; exact hxx u hu
  obtain ⟨ε', m', hstd', hm'⟩ := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_isStdSpace
    (Q.restrict Y) (nondegenerate_polarBilin_restrict hYp)
  have hfr := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.finrank_of_isStdSpace_arf hstd' hm'
  obtain ⟨k, rfl⟩ : ∃ k, m' = k + 1 := ⟨m' - 1, by omega⟩
  have hk : 2 ≤ k := by omega
  have hsimp := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.isSimpleGroup_of_isStdSpace
    (n := k) (by omega) (fun _ => hk) hstd'
  obtain ⟨a, b, hab⟩ := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_noncomm_of_isStdSpace
    (n := k) (by omega) (fun _ => hk) hstd'
  set L' := orthJ Q Y with hL'
  let eJ := orthJEquiv hYp
  have hb₀O : b₀ ∈ O := hEO hb₀E
  have hb₀c : ∀ f ∈ E₂, b₀ * f = f * b₀ := fun f hf => hE.comm hb₀E (hE₂E hf)
  have hb₀c' : ∀ f ∈ E₂, b₀⁻¹ * f = f * b₀⁻¹ := fun f hf =>
    (Commute.inv_left (hb₀c f hf : Commute b₀ f)).eq
  have hstab : b₀ ∈ CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.stabSub Y := fun w =>
    ⟨fun hw => apply_mem_fixV_of_commute hb₀c hw, fun hw => by
      have := apply_mem_fixV_of_commute hb₀c' hw
      rwa [inv_apply_eq_of_apply_eq rfl] at this⟩
  set r₀ := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.restrictHom Y ⟨b₀, hstab⟩ with hr₀
  have hr₀O : r₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict Y) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x =>
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hb₀O (x : V)
  have hr₀p : r₀ ^ p = 1 := by
    rw [hr₀, ← map_pow]
    have : (⟨b₀, hstab⟩ : ↥(CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.stabSub Y)) ^ p =
        1 := Subtype.ext (by simpa using hE.2 b₀ hb₀E)
    rw [this, map_one]
  have hr₀E : r₀ ∈ elementaryGroup (Q.restrict Y) :=
    mem_elementaryGroup_of_pow (by omega) (fun _ => by omega) hstd' hr₀O hpo hr₀p
  obtain ⟨x, hx⟩ := orthJRestrict_surjective (Q := Q) (W := Y) ⟨r₀, hr₀E⟩
  have hperp : ∀ z ∈ perpSub Q Y, b₀ z = z := fun z hz => by
    refine hbl₀.2.2.2.1 z ?_
    rw [← perpSub_eq_orthogonal]
    exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.mem_perpSub.2 fun w hw =>
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.mem_perpSub.1 hz w (hW₀Y hw)
  have hxb : (x : V ≃ₗ[ZMod 2] V) = b₀ := by
    refine linearEquiv_ext_of_isCompl (isCompl_perpSub hYp) (fun w hw => ?_) (fun z hz => ?_)
    · have := congrArg (fun f : ↥Y ≃ₗ[ZMod 2] ↥Y => (f ⟨w, hw⟩ : V)) hx
      exact this
    · rw [apply_eq_of_mem_orthJ x.2 hz, hperp z hz]
  have hb₀L : b₀ ∈ L' := hxb ▸ x.2
  have hpL : p ∣ Nat.card ↥L' := by
    have hord : orderOf (⟨b₀, hb₀L⟩ : ↥L') = p :=
      orderOf_eq_prime (Subtype.ext (hE.2 b₀ hb₀E))
        (fun h => ne_one_of_isBlock hbl₀ (congrArg Subtype.val h))
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hLC : ∀ x ∈ L', ∀ f ∈ E₂, x * f = f * x := by
    intro x hx f hf
    have hfY : ∀ y ∈ Y, f y = y := fun y hy => mem_fixV.1 hy f hf
    have hfc : ∀ h ∈ E₂, f * h = h * f := fun h hh => hE.comm (hE₂E hf) (hE₂E hh)
    exact commute_of_isCompl (isCompl_perpSub hYp) hfY
      (fun z hz => CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.apply_mem_perpSub_fixSub_of_commute
        (hEO (hE₂E hf)) hfc hz)
      (fun y hy => (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.mem_stabSub.1
        (orthJ_le_stabSub hx) y).1 hy)
      (fun z hz => apply_eq_of_mem_orthJ hx hz)
  haveI := hsimp
  refine ⟨E₂, L', hE₂E, hcard, orthJ_le_elementaryGroup Q Y, hLC,
    fun g hg hgc x hx => conj_mem_orthJ (elementaryGroup_le_orthogonalGroup Q hg)
      (fun w hw => apply_mem_fixV_of_commute hgc hw) hx,
    eJ.isSimpleGroup, ⟨eJ.symm a, eJ.symm b, fun h => hab (eJ.symm.injective (by
      rw [map_mul, map_mul, h]))⟩, hpL⟩

theorem core_omega {X : Type} [Group X] [Finite X] (hQ : (polarBilin Q).Nondegenerate) {ε : Bool}
    {n : ℕ} (hn : 1 ≤ n) (hstd : IsStdSpace ε Q (n + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfp : HasFixedPointFreeOrder ε n p) {J F : Subgroup X} (φ : ↥J ≃* ↥(elementaryGroup Q))
    (hFJ : F ≤ J) (hF : IsElemAbelian p F) (hrk : CFSG.Open.pRank p F = CFSG.Open.pRank p J)
    (h3 : 3 ≤ CFSG.Open.pRank p J) :
    ∃ F₀ : Subgroup X, F₀ ≤ F ∧ Nat.card F = p ^ 2 * Nat.card ↥F₀ ∧
      GLAPLayer p (J ⊓ Subgroup.centralizer (F₀ : Set X)) ≠ ⊥ := by
  let ι : ↥J →* (V ≃ₗ[ZMod 2] V) := (elementaryGroup Q).subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp φ.injective
  have hrange : ι.range = elementaryGroup Q := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (φ x).2
    · intro hg
      exact ⟨φ.symm ⟨g, hg⟩, by simp [ι]⟩
  obtain ⟨hF'el, hF'card, hF'max⟩ := model_data hp ι hι hFJ hF hrk
  have h2 : p ^ 2 ≤ Nat.card ↥((F.subgroupOf J).map ι) := by
    rw [hF'card]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  obtain ⟨F₀', L', hF₀', hcard, hLG, hLC, hLN, hs, hnc, hpL⟩ :=
    omega_geom hQ hn hstd hp hp2 hfp ((Subgroup.map_le_range ι _).trans hrange.le) hF'el
      (fun A hA hAel => hF'max A (hA.trans hrange.ge) hAel) h2
  exact core_of_model hp ι hι hFJ hF₀' hcard (hLG.trans hrange.ge) hLC
    (fun g hg => hLN g (hrange.le hg)) hs hnc hpL

end OmegaGeom

section Main

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap CFSG.LieType.Universal.Spin

theorem inputI2710Core_holds : Claims139.InputI2710Core := by
  intro X _ _ p hp hp2 J F _ hcl hFJ hF hrk h3
  rcases hcl with ⟨n, ⟨e⟩⟩ | ⟨ε, n, hn, hΩ, hfp⟩
  · exact core_sp hp hp2 e hFJ hF hrk h3
  · cases ε
    · obtain ⟨φ⟩ := hΩ
      have hm : 2 ≤ n + 1 := by omega
      have hstd : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsStdSpace false
          (quadMinus (n + 1) (ZMod 2) 1 1) (n + 1) := ⟨LinearEquiv.refl _ _, fun v => rfl⟩
      have hnd : (polarBilin (quadMinus (n + 1) (ZMod 2) 1 1)).Nondegenerate :=
        nondegenerate_polarBilin_quadMinus_of_finite (n + 1) (ZMod 2)
          (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)
      exact core_omega hnd hn hstd hp hp2 hfp
        (φ.trans (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmegaMinusEquiv hm))
        hFJ hF hrk h3
    · obtain ⟨φ⟩ := hΩ
      have hn2 : 2 ≤ n := by
        by_contra h
        obtain rfl : n = 1 := by omega
        exact CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2 hfp
      have hm : 3 ≤ n + 1 := by omega
      have hstd : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsStdSpace true
          (quadPlus (n + 1) (ZMod 2)) (n + 1) := ⟨LinearEquiv.refl _ _, fun v => rfl⟩
      have hnd := nondegenerate_polarBilin_quadPlus (n + 1) (ZMod 2)
      exact core_omega hnd hn hstd hp hp2 hfp
        (φ.trans (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmegaPlusEquiv hm))
        hFJ hF hrk h3

end Main

section SpConj

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (IsStdSpace)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V}

theorem exists_quadForm_of_polar (hBa : B.IsAlt) (hB : B.Nondegenerate) :
    ∃ Q₀ : QuadraticForm (ZMod 2) V, ∀ x y, polar Q₀ x y = B x y := by
  obtain ⟨m, b, hb⟩ := hBa.exists_basis_toMatrix_eq_J hB
  have hc := congr_equivFun_eq_spForm b hb
  refine ⟨(quadPlus m (ZMod 2)).comp b.equivFun.toLinearMap, fun x y => ?_⟩
  have h1 : B x y = spForm m (b.equivFun x) (b.equivFun y) := by
    rw [← hc, LinearMap.BilinForm.congr_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  have h2 : polar ((quadPlus m (ZMod 2)).comp b.equivFun.toLinearMap) x y =
      polar (quadPlus m (ZMod 2)) (b.equivFun x) (b.equivFun y) := by
    simp only [polar, QuadraticMap.comp_apply, LinearEquiv.coe_coe, map_add]
  rw [h1, h2, polar_quadPlus, spForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two, mul_comm (b.equivFun x (Sum.inr i))]

theorem exists_invariant_quadForm (hBa : B.IsAlt) (hB : B.Nondegenerate)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEiso : ∀ g ∈ E, IsIsom B g) (hodd : Odd (Nat.card E)) :
    ∃ Q : QuadraticForm (ZMod 2) V, (∀ x y, polar Q x y = B x y) ∧
      ∀ g ∈ E, ∀ v, Q (g v) = Q v := by
  classical
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  haveI : Fintype ↥E := Fintype.ofFinite _
  obtain ⟨Q₀, hQ₀⟩ := exists_quadForm_of_polar hBa hB
  set Q : QuadraticForm (ZMod 2) V := ∑ g : E, Q₀.comp (g : V ≃ₗ[ZMod 2] V).toLinearMap with hQ
  have hQv : ∀ v, Q v = ∑ g : E, Q₀ ((g : V ≃ₗ[ZMod 2] V) v) := fun v => by
    rw [hQ, ← QuadraticMap.evalAddMonoidHom_apply, map_sum]
    rfl
  refine ⟨Q, fun x y => ?_, fun h hh v => ?_⟩
  · have h1 : polar Q x y = ∑ g : E, polar Q₀ ((g : V ≃ₗ[ZMod 2] V) x) ((g : V ≃ₗ[ZMod 2] V) y) := by
      simp only [polar, hQv, map_add, Finset.sum_sub_distrib]
    have h2 : ∀ g : E, polar Q₀ ((g : V ≃ₗ[ZMod 2] V) x) ((g : V ≃ₗ[ZMod 2] V) y) = B x y :=
      fun g => by rw [hQ₀]; exact hEiso g g.2 x y
    rw [h1, Finset.sum_congr rfl fun g _ => h2 g, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_odd hodd]
  · rw [hQv, hQv]
    exact Fintype.sum_equiv (Equiv.mulRight (⟨h, hh⟩ : E)) _ _ fun g => rfl

theorem exists_one_of_nondeg {Q : QuadraticForm (ZMod 2) V} (hQB : ∀ x y, polar Q x y = B x y)
    {W : Submodule (ZMod 2) V} (hW : Nondeg B W) (hW0 : W ≠ ⊥) : ∃ c ∈ W, Q c = 1 := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  rw [nondeg_iff] at hW
  by_contra hcon
  push Not at hcon
  have h0 : ∀ c ∈ W, Q c = 0 := fun c hc =>
    (by decide : ∀ a : ZMod 2, a ≠ 1 → a = 0) _ (hcon c hc)
  apply hw0
  refine hW w hw fun u hu => ?_
  rw [← hQB]
  show Q (u + w) - Q u - Q w = 0
  rw [h0 _ (W.add_mem hu hw), h0 u hu, h0 w hw, sub_zero, sub_zero]

theorem exists_flip {Q : QuadraticForm (ZMod 2) V} (hQB : ∀ x y, polar Q x y = B x y)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEiso : ∀ g ∈ E, IsIsom B g)
    (hQE : ∀ g ∈ E, ∀ v, Q (g v) = Q v) {c : V} (hc : c ∈ fixV E) (hQc : Q c = 1) :
    ∃ Q' : QuadraticForm (ZMod 2) V, (∀ x y, polar Q' x y = B x y) ∧
      (∀ g ∈ E, ∀ v, Q' (g v) = Q' v) ∧
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs Q' =
        -CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs Q := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Fintype V := Fintype.ofFinite V
  have hsq : ∀ a : ZMod 2, a * a = a := by decide
  set ℓ : V →ₗ[ZMod 2] ZMod 2 := B.flip c with hℓ
  set Q' : QuadraticForm (ZMod 2) V := Q + QuadraticMap.linMulLin ℓ ℓ with hQ'
  have hQ'v : ∀ v, Q' v = Q v + B v c := fun v => by
    show Q v + ℓ v * ℓ v = Q v + B v c
    rw [hsq]
    rfl
  refine ⟨Q', fun x y => ?_, fun g hg v => ?_, ?_⟩
  · have h1 : polar Q' x y = polar Q x y := by
      simp only [polar, hQ'v, map_add, LinearMap.add_apply]
      ring
    rw [h1, hQB]
  · rw [hQ'v, hQ'v, hQE g hg v]
    congr 1
    conv_lhs => rw [← mem_fixV.1 hc g hg]
    exact hEiso g hg v c
  · rw [CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs_eq_sum,
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs_eq_sum]
    have h1 : ∀ v, Q' v = Q (v + c) + 1 := fun v => by
      rw [hQ'v, QuadraticMap.map_add Q v c, hQc, hQB]
      generalize Q v = a
      generalize B v c = b
      revert a b
      decide
    simp_rw [h1, CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.neg_one_pow_val_add]
    have h2 : (1 : ZMod 2).val = 1 := rfl
    simp only [h2, pow_one, mul_neg, mul_one, Finset.sum_neg_distrib, neg_inj]
    exact Fintype.sum_equiv (Equiv.addRight c) _ _ fun v => rfl

theorem exists_isometry_of_isStdSpace {Q₁ Q₂ : QuadraticForm (ZMod 2) V} {ε : Bool} {m : ℕ}
    (h₁ : IsStdSpace ε Q₁ m) (h₂ : IsStdSpace ε Q₂ m) :
    ∃ ψ : V ≃ₗ[ZMod 2] V, ∀ v, Q₂ (ψ v) = Q₁ v := by
  cases ε
  · obtain ⟨φ₁, hφ₁⟩ := h₁
    obtain ⟨φ₂, hφ₂⟩ := h₂
    exact ⟨φ₁.trans φ₂.symm, fun v => by
      rw [← hφ₂, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hφ₁]⟩
  · obtain ⟨φ₁, hφ₁⟩ := h₁
    obtain ⟨φ₂, hφ₂⟩ := h₂
    exact ⟨φ₁.trans φ₂.symm, fun v => by
      rw [← hφ₂, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hφ₁]⟩

theorem not_dvd_both {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) (h1 : p ∣ 2 ^ m - 1)
    (h2 : p ∣ 2 ^ m + 1) : False := by
  have h3 : p ∣ (2 ^ m - 1) + 2 := by
    rwa [show 2 ^ m - 1 + 2 = 2 ^ m + 1 by have := Nat.one_le_two_pow (n := m); omega]
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((Nat.dvd_add_right h1).1 h3))

theorem conj_maxEA_isometryGroup (hBs : ∀ x y, B x y = B y x) (hBa : B.IsAlt)
    (hB : B.Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E₁ E₂ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE₁G : E₁ ≤ TauCeti.BilinForm.isometryGroup B) (hE₂G : E₂ ≤ TauCeti.BilinForm.isometryGroup B)
    (hE₁ : IsElemAbelian p E₁) (hE₂ : IsElemAbelian p E₂)
    (hm₁ : ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), A ≤ TauCeti.BilinForm.isometryGroup B →
      IsElemAbelian p A → Nat.card A ≤ Nat.card E₁)
    (hm₂ : ∀ A : Subgroup (V ≃ₗ[ZMod 2] V), A ≤ TauCeti.BilinForm.isometryGroup B →
      IsElemAbelian p A → Nat.card A ≤ Nat.card E₂) :
    ∃ g ∈ TauCeti.BilinForm.isometryGroup B, E₂ = E₁.map (MulAut.conj g).toMonoidHom := by
  classical
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  set G := TauCeti.BilinForm.isometryGroup B with hGdef
  have hGiso : ∀ g ∈ G, IsIsom B g := fun g hg => TauCeti.BilinForm.mem_isometryGroup_iff.1 hg
  have hG : IsRestrClosed B G := isRestrClosed_isometryGroup hBs
  have hnd : ∀ Q : QuadraticForm (ZMod 2) V, (∀ x y, polar Q x y = B x y) →
      (polarBilin Q).Nondegenerate := by
    intro Q hQ
    have : polarBilin Q = B := LinearMap.ext₂ fun x y => by rw [polarBilin_apply_apply, hQ]
    rw [this]
    exact hB
  have hstd : ∀ Q : QuadraticForm (ZMod 2) V, (∀ x y, polar Q x y = B x y) →
      ∃ (ε : Bool) (m : ℕ), IsStdSpace ε Q m ∧ (ε = false → 1 ≤ m) ∧
        finrank (ZMod 2) V = 2 * m := by
    intro Q hQ
    obtain ⟨ε, m, h, hm⟩ :=
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_isStdSpace Q (hnd Q hQ)
    exact ⟨ε, m, h, hm,
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.finrank_of_isStdSpace_arf h hm⟩
  have hiso₁ : ∀ g ∈ E₁, IsIsom B g := fun g hg => hGiso g (hE₁G hg)
  have hiso₂ : ∀ g ∈ E₂, IsIsom B g := fun g hg => hGiso g (hE₂G hg)
  obtain ⟨Q₁, hQ₁B, hQ₁E⟩ := exists_invariant_quadForm hBa hB hiso₁
    (odd_card_of_isElemAbelian hp hp2 hE₁)
  obtain ⟨Q₂, hQ₂B, hQ₂E⟩ := exists_invariant_quadForm hBa hB hiso₂
    (odd_card_of_isElemAbelian hp hp2 hE₂)
  obtain ⟨Q₁', Q₂', hQ₁'B, hQ₁'E, hQ₂'B, hQ₂'E, hcs⟩ : ∃ Q₁' Q₂' : QuadraticForm (ZMod 2) V,
      (∀ x y, polar Q₁' x y = B x y) ∧ (∀ g ∈ E₁, ∀ v, Q₁' (g v) = Q₁' v) ∧
      (∀ x y, polar Q₂' x y = B x y) ∧ (∀ g ∈ E₂, ∀ v, Q₂' (g v) = Q₂' v) ∧
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs Q₁' =
        CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs Q₂' := by
    obtain ⟨ε₁, m₁, h₁, hm₁', hf₁⟩ := hstd Q₁ hQ₁B
    obtain ⟨ε₂, m₂, h₂, hm₂', hf₂⟩ := hstd Q₂ hQ₂B
    obtain rfl : m₁ = m₂ := by omega
    have hc₁ := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs_of_isStdSpace h₁ hm₁'
    have hc₂ := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs_of_isStdSpace h₂ hm₂'
    by_cases hε : ε₁ = ε₂
    · subst hε
      exact ⟨Q₁, Q₂, hQ₁B, hQ₁E, hQ₂B, hQ₂E, by rw [hc₁, hc₂]⟩
    have hneg : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs Q₁ =
        -CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs Q₂ := by
      rw [hc₁, hc₂]
      cases ε₁ <;> cases ε₂ <;> simp_all
    by_cases hF₁ : fixV E₁ = ⊥
    · by_cases hF₂ : fixV E₂ = ⊥
      · exfalso
        obtain ⟨g₁, hg₁E, hg₁⟩ := exists_fpf_of_fixV_eq_bot hBs hB hp hp2 hG hE₁G hE₁ hm₁ hF₁
        obtain ⟨g₂, hg₂E, hg₂⟩ := exists_fpf_of_fixV_eq_bot hBs hB hp hp2 hG hE₂G hE₂ hm₂ hF₂
        have hd₁ := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.dvd_of_fpf h₁ hm₁' hp g₁
          (hQ₁E g₁ hg₁E) (hE₁.2 g₁ hg₁E) hg₁
        have hd₂ := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.dvd_of_fpf h₂ hm₂' hp g₂
          (hQ₂E g₂ hg₂E) (hE₂.2 g₂ hg₂E) hg₂
        cases ε₁ <;> cases ε₂
        · exact hε rfl
        · exact not_dvd_both hp hp2 _ (by simpa using hd₂) (by simpa using hd₁)
        · exact not_dvd_both hp hp2 _ (by simpa using hd₁) (by simpa using hd₂)
        · exact hε rfl
      · obtain ⟨c, hc, hQc⟩ := exists_one_of_nondeg hQ₂B
          (nondeg_fixV hB hiso₂ (odd_card_of_isElemAbelian hp hp2 hE₂)) hF₂
        obtain ⟨Q₂', h1, h2, h3⟩ := exists_flip hQ₂B hiso₂ hQ₂E hc hQc
        exact ⟨Q₁, Q₂', hQ₁B, hQ₁E, h1, h2, by rw [h3, hneg]⟩
    · obtain ⟨c, hc, hQc⟩ := exists_one_of_nondeg hQ₁B
        (nondeg_fixV hB hiso₁ (odd_card_of_isElemAbelian hp hp2 hE₁)) hF₁
      obtain ⟨Q₁', h1, h2, h3⟩ := exists_flip hQ₁B hiso₁ hQ₁E hc hQc
      exact ⟨Q₁', Q₂, h1, h2, hQ₂B, hQ₂E, by rw [h3, hneg, neg_neg]⟩
  obtain ⟨ε₁, m₁, h₁, hm₁', -⟩ := hstd Q₁' hQ₁'B
  obtain ⟨ε₂, m₂, h₂, hm₂', -⟩ := hstd Q₂' hQ₂'B
  obtain ⟨rfl, rfl⟩ := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs_sign_inj
    ((CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs_of_isStdSpace h₁ hm₁').symm.trans
      (hcs.trans (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.cs_of_isStdSpace h₂ hm₂')))
  obtain ⟨ψ, hψ⟩ := exists_isometry_of_isStdSpace h₁ h₂
  have hψG : ψ ∈ G := by
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    intro x y
    rw [← hQ₂'B, ← hQ₁'B]
    show Q₂' (ψ x + ψ y) - Q₂' (ψ x) - Q₂' (ψ y) = Q₁' (x + y) - Q₁' x - Q₁' y
    rw [← map_add, hψ, hψ, hψ]
  have hOG : TauCeti.QuadraticMap.orthogonalGroup Q₂' ≤ G := fun g hg =>
    TauCeti.BilinForm.mem_isometryGroup_iff.2 fun x y => by
      rw [← hQ₂'B, ← hQ₂'B]
      exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg x y
  have hψinv : ∀ w, Q₁' (ψ⁻¹ w) = Q₂' w := fun w => by rw [← hψ, apply_inv_apply]
  have hE₁'O : E₁.map (MulAut.conj ψ).toMonoidHom ≤ TauCeti.QuadraticMap.orthogonalGroup Q₂' := by
    rintro _ ⟨g, hg, rfl⟩
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    show Q₂' (ψ (g (ψ⁻¹ v))) = Q₂' v
    rw [hψ, hQ₁'E g hg, hψinv]
  have hE₂O : E₂ ≤ TauCeti.QuadraticMap.orthogonalGroup Q₂' := fun g hg =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 (hQ₂'E g hg)
  have hcE₁' : Nat.card ↥(E₁.map (MulAut.conj ψ).toMonoidHom) = Nat.card E₁ :=
    Subgroup.card_map_of_injective (MulAut.conj ψ).injective
  obtain ⟨g, hgO, hg⟩ := conj_maxEA_orthogonalGroup (hnd Q₂' hQ₂'B) hp hp2 _ E₂ hE₁'O hE₂O
    (hE₁.map _) hE₂ (fun F hF hFa => hcE₁' ▸ hm₁ F (hF.trans hOG) hFa)
    (fun F hF hFa => hm₂ F (hF.trans hOG) hFa)
  refine ⟨g * ψ, G.mul_mem (hOG hgO) hψG, ?_⟩
  rw [hg, Subgroup.map_map]
  congr 1

theorem conjMaxEA_isometryGroup {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {C : LinearMap.BilinForm (ZMod 2) W}
    (hCs : ∀ x y, C x y = C y x) (hCa : C.IsAlt) (hC : C.Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : Claims137.ConjMaxEA p ↥(TauCeti.BilinForm.isometryGroup C) := by
  haveI : Finite (W ≃ₗ[ZMod 2] W) := finite_linearEquiv
  set G := TauCeti.BilinForm.isometryGroup C with hG
  intro F₁ F₂ hF₁ hF₂ hm₁ hm₂
  have hcard : ∀ F : Subgroup ↥G, Nat.card ↥(F.map G.subtype) = Nat.card ↥F := fun F =>
    Subgroup.card_map_of_injective G.subtype_injective
  have hmax : ∀ F' : Subgroup ↥G,
      (∀ F : Subgroup ↥G, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥F') →
      ∀ A : Subgroup (W ≃ₗ[ZMod 2] W), A ≤ G → IsElemAbelian p A →
        Nat.card A ≤ Nat.card ↥(F'.map G.subtype) := by
    intro F' hm A hA hAel
    rw [hcard]
    have h1 := hm (A.comap G.subtype) (hAel.comap G.subtype_injective)
    have h2 : Nat.card ↥(A.comap G.subtype) = Nat.card A := by
      conv_rhs => rw [← Subgroup.map_comap_eq_self (show A ≤ G.subtype.range by
        rwa [Subgroup.range_subtype])]
      rw [Subgroup.card_map_of_injective G.subtype_injective]
    rwa [h2] at h1
  obtain ⟨g, hgG, hg⟩ := conj_maxEA_isometryGroup hCs hCa hC hp hp2 (Subgroup.map_subtype_le F₁)
    (Subgroup.map_subtype_le F₂) (hF₁.map _) (hF₂.map _) (hmax F₁ hm₁) (hmax F₂ hm₂)
  refine ⟨(⟨g, hgG⟩ : ↥G)⁻¹, Subgroup.map_injective G.subtype_injective ?_⟩
  rw [Claims137.map_gLBConj, hg]
  unfold GLBConj
  simp

theorem conjMaxEA_statedSp (n : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Claims137.ConjMaxEA p ↥(StatedSp n (ZMod 2)) := by
  haveI : Finite ((Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2)) :=
    finite_linearEquiv
  obtain ⟨Φ⟩ := nonempty_statedSp_mulEquiv n
  exact Claims137.ConjMaxEA.of_mulEquiv Φ.symm
    (conjMaxEA_isometryGroup (spForm_symm n) (spForm_isAlt n) (spForm_nondegenerate n) hp hp2)

theorem conjMaxEA_commutator_statedSp {n : ℕ} (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Claims137.ConjMaxEA p ↥(commutator ↥(StatedSp n (ZMod 2))) := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · obtain ⟨e0⟩ := OmegaFacts.nonempty_statedSp_two_mulEquiv_perm_six
    have hmap : (commutator ↥(StatedSp 2 (ZMod 2))).map e0.toMonoidHom =
        alternatingGroup (Fin 6) := by
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e0.surjective, ← _root_.commutator_def,
        alternatingGroup.commutator_perm_eq (by simp)]
    let f : ↥(commutator ↥(StatedSp 2 (ZMod 2))) ≃* ↥(alternatingGroup (Fin 6)) :=
      (Subgroup.equivMapOfInjective _ e0.toMonoidHom e0.injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact Claims137.ConjMaxEA.of_mulEquiv f.symm (Claims137.conjMaxEA_alt hp hp2 (by norm_num))
  · have hperf : commutator ↥(StatedSp n (ZMod 2)) = ⊤ :=
      (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n (ZMod 2)
        (Or.inr (Or.inr ⟨Nat.card_zmod 2, h3⟩))).commutator_eq_top
    exact Claims137.ConjMaxEA.of_mulEquiv
      ((MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv).symm (conjMaxEA_statedSp n hp hp2)

end SpConj

section Frattini

variable {G : Type} [Group G] [Finite G]

theorem le_sup_normalizer_of_conj {p : ℕ} {K N P : Subgroup G} (hKN : K ≤ N)
    (hNK : N ≤ Subgroup.normalizer (K : Set G)) (hP : Sec13h.IsMaxEA p K P)
    (hconj : Claims137.ConjMaxEA p ↥K) : N ≤ K ⊔ (N ⊓ Subgroup.normalizer (P : Set G)) := by
  intro g hg
  obtain ⟨hPK, hPel, hPmax⟩ := hP
  have hgK : GLBConj g K = K := mem_normalizer_iff_gLBConj_eq.1 (hNK hg)
  have hA : Sec13h.IsMaxEA p K (GLBConj g P) := by
    refine ⟨hgK ▸ gLBConj_mono g hPK, sec9_isElemAbelian_gLBConj g hPel, fun F hF hFel => ?_⟩
    rw [sec9_card_gLBConj]
    exact hPmax F hF hFel
  obtain ⟨k, hkK, hk⟩ := Claims137.conj_of_conjMaxEA hconj ⟨hPK, hPel, hPmax⟩ hA
  have hgk : g * k⁻¹ ∈ Subgroup.normalizer (P : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    have h1 := congrArg (GLBConj k⁻¹) hk
    rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at h1
    exact h1.symm
  have hgkN : g * k⁻¹ ∈ N := N.mul_mem hg (N.inv_mem (hKN hkK))
  rw [show g = (g * k⁻¹) * k by group]
  exact mul_mem (Subgroup.mem_sup_right ⟨hgkN, hgk⟩) (Subgroup.mem_sup_left hkK)

@[expose] def InputConjKstar139 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T : Subgroup G},
    Sec13 G m p B M E A D T → B ≤ Nof T → Claims137.ConjMaxEA p ↥(Claims139.KstarOf p M D T)

@[expose] def InputMaxBKstar139 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T : Subgroup G},
    Sec13 G m p B M E A D T → B ≤ Nof T →
      Sec13h.IsMaxEA p (Claims139.KstarOf p M D T) (B ⊓ Claims139.KstarOf p M D T)

@[expose] def InputFactKstar139 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T : Subgroup G},
    Sec13 G m p B M E A D T → B ≤ Nof T →
      Claims139.KstarOf p M D T ≤
        (GLAPPrimeCoreOf p (Claims139.KstarOf p M D T) ⊔ Prop139.KBig p M D T) ⊔
          (Claims139.KstarOf p M D T ⊓
            Subgroup.centralizer ((B ⊓ Prop139.KBig p M D T : Subgroup G) : Set G))

theorem kstar_le_and_normal (p : ℕ) (M D T : Subgroup G) :
    Claims139.KstarOf p M D T ≤ Nof T ∧
      Nof T ≤ Subgroup.normalizer ((Claims139.KstarOf p M D T : Subgroup G) : Set G) := by
  have hKBN : Prop139.KBig p M D T ≤ Nof T :=
    iSup₂_le fun L _ => (Sec13d.derivedInf_le _).trans inf_le_left
  refine ⟨iSup₂_le fun n hn => ?_, fun n hn => ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact (Nof T).mul_mem ((Nof T).mul_mem ((Nof T).inv_mem hn) (hKBN hk)) hn
  · have hle : ∀ n ∈ Nof T, GLBConj n (Claims139.KstarOf p M D T) ≤ Claims139.KstarOf p M D T := by
      intro n hn
      unfold Claims139.KstarOf
      rw [gLBConj_iSup_eq]
      refine iSup_le fun g => ?_
      rw [gLBConj_iSup_eq]
      refine iSup_le fun hg => ?_
      rw [gLBConj_gLBConj]
      exact le_iSup₂_of_le (f := fun n (_ : n ∈ Nof T) => GLBConj n (Prop139.KBig p M D T))
        (g * n) ((Nof T).mul_mem hg hn) le_rfl
    rw [mem_normalizer_iff_gLBConj_eq]
    refine le_antisymm (hle n hn) ?_
    have := gLBConj_mono n (hle n⁻¹ ((Nof T).inv_mem hn))
    rwa [gLBConj_gLBConj_inv] at this

theorem inputFrattini139_of_inputs (hC : InputConjKstar139) (hM : InputMaxBKstar139)
    (hF : InputFactKstar139) : Claims139.InputFrattini139 := by
  intro G _ _ m p B M E A D T h hBN
  obtain ⟨hKN, hNK⟩ := kstar_le_and_normal p M D T
  exact (le_sup_normalizer_of_conj hKN hNK (hM h hBN) (hC h hBN)).trans
    (sup_le_sup_right (hF h hBN) _)

end Frattini

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA2
