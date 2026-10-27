module

public import CFSG.CGT.PushingUpLit.BHS6.SixTwelveC

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E F : Subgroup Γ}

theorem pCoreOf_le_pCoreOf_G (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E) :
    pCoreOf 2 E ≤ pCoreOf 2 G := by
  have h1 := (six_four_a hG hT hE).2
  rw [blockW_eq_pCoreOf hE] at h1
  exact h1.trans (omegaOneCenter_le_pCoreOf G)

theorem pCoreOf_le_of_le_block (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hF : F ∈ btBlocksG G T) (hFE : F ≤ E) : pCoreOf 2 F ≤ pCoreOf 2 E := by
  obtain ⟨s, hs, hFs⟩ := hF
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hS : IsSylowOf 2 (A1b.conjSub s T) G :=
    isSylowOf_of_isSylowTwoOf (isSylowTwoOf_conjSub_of_mem hT' hs)
  rcases six_seven_of_le_R hG hT hE ⟨s, hs, hFs⟩ (hFE.trans Subgroup.le_normalizer)
    (hFE.trans le_sup_right) with h | ⟨-, h⟩
  · exfalso
    have hle : ⁅pCoreOf 2 F, F⁆ ≤ ⁅E, F⁆ :=
      Subgroup.commutator_mono ((pCoreOf_le_self F).trans hFE) le_rfl
    rw [h, le_bot_iff, hFs.perfect] at hle
    exact pCoreOf_ne_bot hFs (charTwo_of_isBTBlock hG hS hFs) hle
  · exact h

theorem inf_centralizer_pCoreOf_nested (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) (hF : F ∈ btBlocksG G T) (hFE : F ≤ E) :
    F ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Γ) = pCoreOf 2 F := by
  have hW := pCoreOf_le_of_le_block hG hT hE hF hFE
  have hchar := charTwo_of_isBTBlock hG hT hE
  have hWab : ∀ x ∈ pCoreOf 2 E, ∀ y ∈ pCoreOf 2 E, x * y = y * x := hE.elemAbelian.1
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxW : x ∈ pCoreOf 2 E := hchar ⟨hFE hx.1, hx.2⟩
    have hN : F ⊓ pCoreOf 2 E ≤ pCoreOf 2 F := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 E).to_le inf_le_right)
      intro f hf
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hf, hFE.trans (le_normalizer_pCoreOf_self E) hf⟩
    exact hN ⟨hx.1, hxW⟩
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 F hx,
      Subgroup.mem_centralizer_iff.mpr fun w hw => (hWab x (hW hx) w hw).symm⟩

theorem commutator_pCoreOf_le_nested (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) (hF : F ∈ btBlocksG G T) :
    ⁅F, pCoreOf 2 E⁆ ≤ pCoreOf 2 F := by
  obtain ⟨s, hs, hFs⟩ := hF
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hS : IsSylowOf 2 (A1b.conjSub s T) G :=
    isSylowOf_of_isSylowTwoOf (isSylowTwoOf_conjSub_of_mem hT' hs)
  exact (Subgroup.commutator_mono le_rfl (pCoreOf_le_pCoreOf_G hG hT hE)).trans
    (commutator_pCoreOf_le hS hFs)

omit [Finite Γ] in
theorem exists_mul_of_mem_autPre {V F : Subgroup Γ} {x : Γ} (hx : x ∈ autPre V (autOn F V)) :
    ∃ f ∈ F, x * f⁻¹ ∈ Subgroup.centralizer (V : Set Γ) := by
  obtain ⟨hxN, hxE⟩ := mem_autPre.mp hx
  obtain ⟨e, he, hee⟩ := mem_autOn_iff.mp hxE
  refine ⟨e, he, ?_⟩
  have hact : ∀ v : ↥V, (e : Γ) * v * (e : Γ)⁻¹ = x * v * x⁻¹ := fun v =>
    (conjAct_apply' V e v).trans ((congrArg (fun a : MulAut ↥V => ((a v : ↥V) : Γ)) hee).trans
      (conjAct_apply' V ⟨x, hxN⟩ v).symm)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hu : (e : Γ)⁻¹ * v * (e : Γ) ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set Γ)).inv_mem e.2) v).mp
      hv
    simpa using this
  have h : (e : Γ) * ((e : Γ)⁻¹ * v * (e : Γ)) * (e : Γ)⁻¹ =
      x * ((e : Γ)⁻¹ * v * (e : Γ)) * x⁻¹ := hact ⟨_, hu⟩
  have h1 : (e : Γ) * ((e : Γ)⁻¹ * v * (e : Γ)) * (e : Γ)⁻¹ = v := by group
  rw [h1] at h
  have h2 : v * x = x * ((e : Γ)⁻¹ * v * (e : Γ)) := by
    calc v * x = (x * ((e : Γ)⁻¹ * v * (e : Γ)) * x⁻¹) * x := by rw [← h]
      _ = x * ((e : Γ)⁻¹ * v * (e : Γ)) := by group
  calc v * (x * (e : Γ)⁻¹) = (v * x) * (e : Γ)⁻¹ := by group
    _ = (x * ((e : Γ)⁻¹ * v * (e : Γ))) * (e : Γ)⁻¹ := by rw [h2]
    _ = (x * (e : Γ)⁻¹) * v := by group

omit [Finite Γ] in
theorem conj_mem_autPre_of_mem_normalizer {V : Subgroup Γ} {U : Subgroup (MulAut ↥V)} {n x : Γ}
    (hnV : n ∈ Subgroup.normalizer (V : Set Γ))
    (hn : conjAct V ⟨n, hnV⟩ ∈ Subgroup.normalizer (U : Set (MulAut ↥V)))
    (hx : x ∈ autPre V U) : n * x * n⁻¹ ∈ autPre V U := by
  obtain ⟨hxN, hxE⟩ := mem_autPre.mp hx
  have hnxN : n * x * n⁻¹ ∈ Subgroup.normalizer (V : Set Γ) :=
    (Subgroup.normalizer (V : Set Γ)).mul_mem
      ((Subgroup.normalizer (V : Set Γ)).mul_mem hnV hxN)
      ((Subgroup.normalizer (V : Set Γ)).inv_mem hnV)
  refine mem_autPre.mpr ⟨hnxN, ?_⟩
  have e : conjAct V ⟨n * x * n⁻¹, hnxN⟩ =
      conjAct V ⟨n, hnV⟩ * conjAct V ⟨x, hxN⟩ * (conjAct V ⟨n, hnV⟩)⁻¹ := by
    show conjAct V (⟨n, hnV⟩ * ⟨x, hxN⟩ * ⟨n, hnV⟩⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp hn _).mp hxE

theorem mem_normalizer_of_conjAct (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hF : F ∈ btBlocksG G T) (hFE : F ≤ E) {y : Γ} (hyE : y ∈ Subgroup.normalizer (E : Set Γ))
    (hyW : y ∈ Subgroup.normalizer (pCoreOf 2 E : Set Γ))
    (hy : conjAct (pCoreOf 2 E) ⟨y, hyW⟩ ∈
      Subgroup.normalizer (autOn F (pCoreOf 2 E) : Set (MulAut ↥(pCoreOf 2 E)))) :
    y ∈ Subgroup.normalizer (F : Set Γ) := by
  classical
  have hF' := hF
  obtain ⟨s, hs, hFs⟩ := hF'
  have hchar := charTwo_of_isBTBlock hG hT hE
  have hFres : opResidual 2 F = F := opResidual_eq_of_isBTBlock hFs
  have hcomm := commutator_pCoreOf_le_nested hG hT hE hF
  have hWab : ∀ x ∈ pCoreOf 2 E, ∀ y ∈ pCoreOf 2 E, x * y = y * x := hE.elemAbelian.1
  have hW2 : ∀ x ∈ pCoreOf 2 E, x ^ 2 = 1 := hE.elemAbelian.2
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  set Pre : Subgroup Γ := E ⊓ autPre W (autOn F W) with hPre
  have hFPre : F ≤ Pre := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hFE hx, mem_autPre.mpr
      ⟨(hFE.trans (le_normalizer_pCoreOf_self E)) hx,
        mem_autOn_iff.mpr ⟨⟨x, (hFE.trans (le_normalizer_pCoreOf_self E)) hx⟩, hx, rfl⟩⟩⟩
  have hsq : ∀ x ∈ Pre, x ^ 2 ∈ F := by
    intro x hx
    obtain ⟨f, hf, hc⟩ := exists_mul_of_mem_autPre hx.2
    have hcE : x * f⁻¹ ∈ E := E.mul_mem hx.1 (E.inv_mem (hFE hf))
    have hcW : x * f⁻¹ ∈ W := hchar ⟨hcE, hc⟩
    set c := x * f⁻¹ with hcdef
    have hx' : x = c * f := by rw [hcdef]; group
    have hfc : ⁅f, c⁆ ∈ F := hcomm (Subgroup.commutator_mem_commutator hf hcW) |>
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 F
    have hcinv : c⁻¹ = c := by
      have := hW2 c hcW
      rw [pow_two] at this
      exact inv_eq_of_mul_eq_one_right this
    have hcf : ⁅c, f⁆ = ⁅f, c⁆⁻¹ := (commutatorElement_inv f c).symm
    have e : x ^ 2 = ⁅c, f⁆ * f ^ 2 := by
      rw [hx', pow_two, pow_two]
      simp only [commutatorElement_def, hcinv]
      group
    rw [e]
    exact F.mul_mem (by rw [hcf]; exact F.inv_mem hfc) (F.pow_mem hf 2)
  have hFeq : opResidual 2 Pre = F := by
    refine le_antisymm (opResidual_le_of_pow_mem fun x hx => ⟨1, ?_⟩) ?_
    · rw [pow_one]
      exact hsq x hx
    · calc F = opResidual 2 F := hFres.symm
        _ ≤ opResidual 2 Pre := opResidual_mono 2 hFPre
  have hPreN : ∀ (z : Γ) (hzE : z ∈ Subgroup.normalizer (E : Set Γ))
      (hzW : z ∈ Subgroup.normalizer (W : Set Γ)),
      conjAct W ⟨z, hzW⟩ ∈ Subgroup.normalizer (autOn F W : Set (MulAut ↥W)) →
      ∀ x ∈ Pre, z * x * z⁻¹ ∈ Pre := by
    intro z hzE hzW hz x hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hzE x).mp hx.1,
      conj_mem_autPre_of_mem_normalizer hzW hz hx.2⟩
  have h1 : A1b.conjSub y Pre ≤ Pre := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPreN y hyE hyW hy x hx
  have hyi : y⁻¹ ∈ Subgroup.normalizer (W : Set Γ) := (Subgroup.normalizer (W : Set Γ)).inv_mem hyW
  have hyiE : y⁻¹ ∈ Subgroup.normalizer (E : Set Γ) :=
    (Subgroup.normalizer (E : Set Γ)).inv_mem hyE
  have hyi' : conjAct W ⟨y⁻¹, hyi⟩ ∈ Subgroup.normalizer (autOn F W : Set (MulAut ↥W)) := by
    have : conjAct W ⟨y⁻¹, hyi⟩ = (conjAct W ⟨y, hyW⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [this]
    exact (Subgroup.normalizer (autOn F W : Set (MulAut ↥W))).inv_mem hy
  have h2 : A1b.conjSub y⁻¹ Pre ≤ Pre := by
    rintro _ ⟨x, hx, rfl⟩
    exact hPreN y⁻¹ hyiE hyi hyi' x hx
  refine mem_normalizer_of_conjSub_le ?_ ?_
  · rw [← hFeq, ← opResidual_conjSub]
    exact opResidual_mono 2 h1
  · rw [← hFeq, ← opResidual_conjSub]
    exact opResidual_mono 2 h2

end CFSG.CGT.PushingUpLit.BHS6
