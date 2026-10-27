module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwConjLift
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

theorem exists_fixed_lift_of_mem_commutator {G₁ G : Type*} [Group G₁] [Group G] (π : G₁ →* G)
    (hker : ∀ z, π z = 1 → z ∈ Subgroup.center G₁) (F₁ : G₁ →* G₁) (F : G →* G)
    (hcomm : ∀ x, π (F₁ x) = F (π x)) (M : Subgroup G) (hMπ : ∀ y ∈ M, ∃ x, π x = y)
    (hMF : ∀ y ∈ M, F y = y) : ∀ γ ∈ ⁅M, M⁆, ∃ x, F₁ x = x ∧ π x = γ := by
  intro γ hγ
  rw [Subgroup.commutator_def] at hγ
  induction hγ using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨h, hh, k, hk, rfl⟩ := hg
    obtain ⟨xh, rfl⟩ := hMπ h hh
    obtain ⟨xk, rfl⟩ := hMπ k hk
    obtain ⟨zh, hzh⟩ : ∃ z, z = xh⁻¹ * F₁ xh := ⟨_, rfl⟩
    obtain ⟨zk, hzk⟩ : ∃ z, z = xk⁻¹ * F₁ xk := ⟨_, rfl⟩
    have ch := Subgroup.mem_center_iff.1 (hker zh (by
      rw [hzh, map_mul, map_inv, hcomm, hMF _ hh, inv_mul_cancel]))
    have ck := Subgroup.mem_center_iff.1 (hker zk (by
      rw [hzk, map_mul, map_inv, hcomm, hMF _ hk, inv_mul_cancel]))
    have e1 : F₁ xh = xh * zh := by rw [hzh]; group
    have e2 : F₁ xk = xk * zk := by rw [hzk]; group
    refine ⟨⁅xh, xk⁆, ?_, by rw [map_commutatorElement]⟩
    rw [map_commutatorElement, e1, e2, commutatorElement_def, commutatorElement_def]
    calc xh * zh * (xk * zk) * (xh * zh)⁻¹ * (xk * zk)⁻¹
        = xh * (zh * (xk * zk)) * zh⁻¹ * xh⁻¹ * (xk * zk)⁻¹ := by group
      _ = xh * ((xk * zk) * zh) * zh⁻¹ * xh⁻¹ * (xk * zk)⁻¹ := by rw [ch (xk * zk)]
      _ = xh * xk * (zk * xh⁻¹) * zk⁻¹ * xk⁻¹ := by group
      _ = xh * xk * (xh⁻¹ * zk) * zk⁻¹ * xk⁻¹ := by rw [ck xh⁻¹]
      _ = xh * xk * xh⁻¹ * xk⁻¹ := by group
  | one => exact ⟨1, map_one _, map_one _⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨xa, hxa, rfl⟩ := iha
    obtain ⟨xb, hxb, rfl⟩ := ihb
    exact ⟨xa * xb, by rw [map_mul, hxa, hxb], map_mul _ _ _⟩
  | inv a _ iha =>
    obtain ⟨xa, hxa, rfl⟩ := iha
    exact ⟨xa⁻¹, by rw [map_inv, hxa], map_inv _ _⟩

section Lift


variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem exists_fixed_lift_of_mem_Γ (S : LangSetup Tag.E6 L p₀) {ω : List (Fin Tag.E6.rank)}
    (hω : (coxeterSystem Tag.E6).IsReduced ω)
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L ((coxeterSystem Tag.E6).wordProd ω))
    {K : Type} [Field K] [Finite K] (ι : K →+* L)
    (hdesc : ∀ y ∈ S.D.model, ∃ y₃ ∈ adjointGroup Tag.E6 K, baseChangeGL ι y₃ = y)
    (Φ₁ : e6Data_valid.minGroup K →* e6Data_valid.minGroup K)
    (Φ₃ : ModGL Tag.E6 K →* ModGL Tag.E6 K)
    (h₁ : ∀ x, ((e6Isogeny K (Φ₁ x) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      Φ₃ ((e6Isogeny K x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K))
    (h₂ : ∀ g, baseChangeGL ι (Φ₃ g) = S.D.Φ (baseChangeGL ι g)) :
    ∀ γ ∈ S.Γ, ∃ x : e6Data_valid.minGroup K,
      e6NWord K ω * Φ₁ x * (e6NWord K ω)⁻¹ = x ∧
        baseChangeGL ι ((e6Isogeny K x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = γ := by
  set π : e6Data_valid.minGroup K →* ModGL Tag.E6 L :=
    (baseChangeGL ι).comp ((adjointGroup Tag.E6 K).subtype.comp (e6Isogeny K)) with hπ
  set F₁ : e6Data_valid.minGroup K →* e6Data_valid.minGroup K :=
    (MulAut.conj (e6NWord K ω)).toMonoidHom.comp Φ₁ with hF₁
  have hπN : ((e6Isogeny K (e6NWord K ω) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).wordProd ω) :=
    e6Isogeny_nWord_eq_canonicalRep hω
  have hker : ∀ z, π z = 1 → z ∈ Subgroup.center (e6Data_valid.minGroup K) := by
    intro z hz
    refine CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.mem_center_of_isogeny_eq_one ?_
    apply baseChangeGL_injective ι
    rw [map_one]
    exact hz
  have hcomm : ∀ x, π (F₁ x) = S.D.step (π x) := by
    intro x
    simp only [hπ, hF₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hπN, h₁, baseChangeGL_canonicalRep, h₂, LangDatum.step,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hn]
  have hMπ : ∀ y ∈ S.D.model, ∃ x, π x = y := by
    intro y hy
    obtain ⟨y₃, hy₃, rfl⟩ := hdesc y hy
    obtain ⟨x, hx⟩ := e6Isogeny_surjective K ⟨y₃, hy₃⟩
    exact ⟨x, by simp only [hπ, MonoidHom.comp_apply, Subgroup.coe_subtype, hx]⟩
  have hMF : ∀ y ∈ S.D.model, S.D.step y = y := fun y hy => ((S.D.mem_model).1 hy).2
  intro γ hγ
  obtain ⟨x, hx, hxγ⟩ :=
    exists_fixed_lift_of_mem_commutator π hker F₁ S.D.step hcomm S.D.model hMπ hMF γ hγ
  exact ⟨x, hx, hxγ⟩

theorem minTorus_inv_mul_mem_center {K : Type} [Field K] [Finite K] (u : Fin Tag.E6.rank → Kˣ)
    {x : e6Data_valid.minGroup K}
    (hπ : ((e6Isogeny K x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      rootDiagUnit Tag.E6 (e6RootParams u)) :
    (minTorus e6Data_valid K u)⁻¹ * x ∈ Subgroup.center (e6Data_valid.minGroup K) := by
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.mem_center_of_isogeny_eq_one ?_
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hπ, e6Isogeny_minTorus, inv_mul_cancel]

theorem nWord_conj_minTorus_of_fixed {K : Type} [Field K] [Finite K] (φ : K →+* K)
    (hφ : ∀ c : Kˣ, c ^ 3 = 1 → Units.map φ.toMonoidHom c = c) (ω : List (Fin Tag.E6.rank))
    (u : Fin Tag.E6.rank → Kˣ) (hu : ∀ l, u l ^ 3 = 1) (x : e6Data_valid.minGroup K)
    (hx : e6NWord K ω * minBC e6Data_valid φ x * (e6NWord K ω)⁻¹ = x)
    (hπ : ((e6Isogeny K x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      rootDiagUnit Tag.E6 (e6RootParams u)) :
    e6NWord K ω * minTorus e6Data_valid K u * (e6NWord K ω)⁻¹ = minTorus e6Data_valid K u := by
  set T := minTorus e6Data_valid K u with hT
  set N := e6NWord K ω with hN
  obtain ⟨z, hz⟩ : ∃ z, z = T⁻¹ * x := ⟨_, rfl⟩
  have hzc : z ∈ Subgroup.center (e6Data_valid.minGroup K) := hz ▸ minTorus_inv_mul_mem_center u hπ
  obtain ⟨u', hu'eq, hu'3⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.exists_minTorus_of_mem_center_E6 hzc
  have hFz : minBC e6Data_valid φ z = z := by
    rw [hu'eq, CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.minBC_minTorus_E6]
    congr 1
    funext j
    exact hφ _ (hu'3 j)
  have hFT : minBC e6Data_valid φ T = T := by
    rw [hT, CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.minBC_minTorus_E6]
    congr 1
    funext j
    exact hφ _ (hu j)
  have hxe : x = T * z := by rw [hz]; group
  have hc := Subgroup.mem_center_iff.1 hzc
  rw [hxe, map_mul, hFT, hFz] at hx
  have key : N * T * N⁻¹ * z = T * z := by
    calc N * T * N⁻¹ * z = N * T * (N⁻¹ * z) := by group
      _ = N * T * (z * N⁻¹) := by rw [hc N⁻¹]
      _ = N * (T * z) * N⁻¹ := by group
      _ = T * z := hx
  exact mul_right_cancel key

theorem e6NWord_append (K : Type) [Field K] (ω ω' : List (Fin Tag.E6.rank)) :
    e6NWord K (ω ++ ω') = e6NWord K ω * e6NWord K ω' := by
  rw [e6NWord, e6NWord, e6NWord, List.map_append, List.prod_append]

theorem nWord_w0_conj_minTorus_of_fixed {K : Type} [Field K] [Finite K] (φ : K →+* K) (q : ℕ)
    (hφq : ∀ c, φ c = c ^ q) (hq : q % 3 = 2) (ω : List (Fin Tag.E6.rank))
    (u : Fin Tag.E6.rank → Kˣ) (hu : ∀ l, u l ^ 3 = 1) (x : e6Data_valid.minGroup K)
    (hx : e6NWord K ω * CFSG.LieType.Steinberg.TwistedE6.sigma K φ x * (e6NWord K ω)⁻¹ = x)
    (hπ : ((e6Isogeny K x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      rootDiagUnit Tag.E6 (e6RootParams u)) :
    e6NWord K (ω ++ CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6W0FourWord) *
        minTorus e6Data_valid K u *
          (e6NWord K (ω ++ CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6W0FourWord))⁻¹ =
      minTorus e6Data_valid K u := by
  set T := minTorus e6Data_valid K u with hT
  set N := e6NWord K ω with hN
  set N₀ := e6NWord K CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.e6W0FourWord with hN₀
  obtain ⟨z, hz⟩ : ∃ z, z = T⁻¹ * x := ⟨_, rfl⟩
  have hzc : z ∈ Subgroup.center (e6Data_valid.minGroup K) := hz ▸ minTorus_inv_mul_mem_center u hπ
  have hFz : CFSG.LieType.Steinberg.TwistedE6.sigma K φ z = z :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.twl_sigma_center φ q hφq hq hzc
  have hinv : ∀ c : Kˣ, c ^ 3 = 1 → Units.map φ.toMonoidHom c = c⁻¹ := by
    intro c hc
    have h1 : Units.map φ.toMonoidHom c = c ^ q := Units.ext (by simp [hφq])
    rw [h1, pow_eq_pow_mod q hc, hq]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hc)
  have hFT : CFSG.LieType.Steinberg.TwistedE6.sigma K φ T = N₀ * T * N₀⁻¹ := by
    rw [hT, CFSG.LieType.SeitzGeneration.ExcHighThree.twl_sigma_minTorus, hN₀,
      nWord_conj_minTorus, CFSG.LieType.SeitzGeneration.ExcHighThree.twl_foldr_e6StarS_w0]
    congr 1
    funext l
    exact hinv _ (hu _)
  have hxe : x = T * z := by rw [hz]; group
  have hc := Subgroup.mem_center_iff.1 hzc
  rw [hxe, map_mul, hFT, hFz] at hx
  have key : N * N₀ * T * (N * N₀)⁻¹ * z = T * z := by
    calc N * N₀ * T * (N * N₀)⁻¹ * z = N * (N₀ * T * N₀⁻¹) * (N⁻¹ * z) := by group
      _ = N * (N₀ * T * N₀⁻¹) * (z * N⁻¹) := by rw [hc N⁻¹]
      _ = N * (N₀ * T * N₀⁻¹ * z) * N⁻¹ := by group
      _ = T * z := hx
  rw [e6NWord_append]
  exact mul_right_cancel key

end Lift

end CFSG.LocalAnalysis.GLTheoremA.T158

end
