module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCases
import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}

@[expose] def scalarOnGL (U : Submodule K (ι → K)) : Subgroup (GL ι K) where
  carrier := {g | ∃ c : K, ∀ u ∈ U, glEquiv g u = c • u}
  one_mem' := ⟨1, fun u _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, fun u hu => ?_⟩
    rw [map_mul, LinearEquiv.mul_apply, hd u hu, map_smul, hc u hu, smul_smul, mul_comm]
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, fun u hu => ?_⟩
    apply (glEquiv g).injective
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_smul, hc u hu,
      smul_smul]
    by_cases h0 : c = 0
    · have h1 : glEquiv g u = 0 := by rw [hc u hu, h0, zero_smul]
      have hu0 : u = 0 := (LinearEquiv.map_eq_zero_iff _).mp h1
      simp [hu0]
    · rw [inv_mul_cancel₀ h0, one_smul]
      rfl

theorem glEquiv_scalar_apply (c : Kˣ) (v : ι → K) :
    glEquiv (Matrix.GeneralLinearGroup.scalar ι c) v = (c : K) • v := by
  rw [glEquiv_apply]
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem scalarGL_mul_comm (c : Kˣ) (g : GL ι K) :
    Matrix.GeneralLinearGroup.scalar ι c * g = g * Matrix.GeneralLinearGroup.scalar ι c := by
  apply glEquiv.injective
  refine LinearEquiv.ext fun v => ?_
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, glEquiv_scalar_apply,
    glEquiv_scalar_apply, map_smul]

private theorem card_comap_eq_mul_ker {G N : Type*} [Group G] [Finite G] [Group N] (f : G →* N)
    {E : Subgroup N} (hE : E ≤ f.range) :
    Nat.card (E.comap f) = Nat.card E * Nat.card f.ker := by
  let g : ↥(E.comap f) →* ↥E := (f.domRestrict (E.comap f)).codRestrict E fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨e, he⟩
    obtain ⟨x, hx⟩ := hE he
    exact ⟨⟨x, by rw [Subgroup.mem_comap, hx]; exact he⟩, Subtype.ext hx⟩
  have hle : f.ker ≤ E.comap f := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact E.one_mem
  have hk : g.ker = f.ker.subgroupOf (E.comap f) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, ← Subtype.val_inj]
    rfl
  have hcard := Subgroup.card_ker_mul_card_range g
  rw [MonoidHom.range_eq_top.mpr hg, Subgroup.card_top, hk,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hcard
  rw [← hcard, mul_comm]

section Weights

open scoped IsMulCommutative

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
variable {H : Subgroup (GL ι K)} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

theorem concA_of_weights_scal (hp : p.Prime) [hSn : S.Normal] (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hcore : GLAPPrimeCore p ↥S = ⊥)
    [Finite K] (h2 : (2 : K) ≠ 0) (hpK : (p : K) ≠ 0) (Dat : ClsInner p S B H β)
    (hHβ : H ≤ isomGL β) {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε]
    (hA : ∀ a : ↥Aε, a ^ p = 1) (hle : liftGroup Dat ≤ Aε)
    (hdec : ∀ g ∈ Aε, ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ Aε ∧
      Matrix.GeneralLinearGroup.scalar ι c * g ∈ liftGroup Dat)
    (hAεβ : Aε ≤ isomGL β) (hAε𝒮 : Aε ≤ centGL (fieldSet Dat))
    (hmaxE : IsMaxElem β (glRep Aε) p (fieldSet Dat))
    [DecidableEq (Hyperplane ↥Aε p)] (I : Finset (Hyperplane ↥Aε p))
    (hI : ∀ H' ∈ I, weightSpace (glRep Aε) H'.1 ≠ ⊥) (hI1 : 1 ≤ I.card)
    {H₀ : Hyperplane ↥Aε p} (hH₀ : H₀ ∉ I) (hW₀ : weightSpace (glRep Aε) H₀.1 ≠ ⊥)
    (hrank : p ^ (3 + I.card) ≤ Nat.card B)
    {z : GL ι K} (hzH : z ∈ H) {s : K} (hs : s * s = 1)
    (hzU : ∀ u ∈ wtU Aε I, glEquiv z u = s • u) (hzW : ∀ w ∈ wtW Aε I, glEquiv z w = (-s) • w)
    (hIH : blkI β (wtU Aε I) (wtW Aε I) ≤ H)
    (hIq : CFSG.Open.IsQuasisimple ↥(blkI β (wtU Aε I) (wtW Aε I)))
    (hpI : p ∣ Nat.card ↥(blkI β (wtU Aε I) (wtW Aε I)))
    (hSchur : ∀ y : GL ι K, (∀ u ∈ wtU Aε I, glEquiv y u ∈ wtU Aε I) →
      (∀ j ∈ blkI β (wtU Aε I) (wtW Aε I), y * j = j * y) →
      ∃ c : K, ∀ u ∈ wtU Aε I, glEquiv y u = c • u)
    (hfield : FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ →
      ∀ y : GL ι K, (∀ u ∈ wtU Aε I, glEquiv y u ∈ wtU Aε I) →
        (∀ w ∈ wtW Aε I, glEquiv y w ∈ wtW Aε I) → ∀ k : ℕ, 0 < k → k < p →
          ¬ ∀ j ∈ blkI β (wtU Aε I) (wtW Aε I),
            y * (ModelGen.semiConj Dat.A Dat.σ ^ k) j * y⁻¹ = j)
    (hscal : ∀ y ∈ Aε, ∀ c : K, (∀ u ∈ wtU Aε I, glEquiv y u = c • u) →
      ∃ c' : Kˣ, (c' : K) = c ∧ Matrix.GeneralLinearGroup.scalar ι c' ∈ Aε)
    (hE : I.card = 1 →
      (∃ a ∈ Aε, (¬ ∃ c : K, ∀ u ∈ wtU Aε I, glEquiv a u = c • u) ∧
        GLAPLayer p (blkI β (wtU Aε I) (wtW Aε I) ⊓ Subgroup.centralizer {a}) ≠ ⊥) ∨
      (FieldElt p S B Dat.φ β Dat.θ Dat.b Dat.A Dat.σ ∧
        GLAPLayer p (blkI β (wtU Aε I) (wtW Aε I) ⊓
          centGL {(ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom}) ≠ ⊥)) :
    S267ConcA p S B := by
  classical
  haveI : Fintype (Hyperplane ↥Aε p) := Fintype.ofFinite _
  set ρ := glRep Aε with hρdef
  set U := wtU Aε I with hUdef
  set W := wtW Aε I with hWdef
  set L := liftGroup Dat with hLdef
  have hρ : IsIsomRep β ρ := isIsomRep_glRep hAεβ
  have h𝒮 : ∀ s ∈ fieldSet Dat, ∀ a v, s (ρ a v) = ρ a (s v) := by
    intro s hs a v
    rw [glRep_apply_eq_glEquiv, glRep_apply_eq_glEquiv]
    exact ((mem_centGL.mp (hAε𝒮 a.2)) s hs v).symm
  have h𝒮W : ∀ s ∈ fieldSet Dat, ∀ i, ∀ v ∈ weightFamily (p := p) ρ i,
      s v ∈ weightFamily (p := p) ρ i := by
    rintro s ⟨hF, rfl⟩ i v hv
    exact preserves_weightFamily_of_semilinear ρ (Dat.σ : K →+* K) _
      (fun c v => ModelGen.semiMap_smul Dat.A Dat.σ c v) (h𝒮 _ ⟨hF, rfl⟩) i hv
  have hρW : ∀ (a : ↥Aε) i, ∀ v ∈ weightFamily (p := p) ρ i,
      (ρ a).toAddMonoidHom v ∈ weightFamily (p := p) ρ i := fun a i v hv =>
    preserves_weightFamily_of_semilinear ρ (RingHom.id K) (ρ a).toAddMonoidHom
      (fun c v => map_smul (ρ a) c v)
      (fun a' v => by
        show ρ a (ρ a' v) = ρ a' (ρ a v)
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]) i hv
  have hUW : IsCompl U W := isCompl_ker_range_projI ρ hp hA hpK I
  have hpres : ∀ f : (ι → K) →+ (ι → K), (∀ i, ∀ v ∈ weightFamily (p := p) ρ i,
      f v ∈ weightFamily (p := p) ρ i) →
      (∀ u ∈ U, f u ∈ U) ∧ ∀ w ∈ W, f w ∈ W := by
    intro f hf
    refine ⟨fun u hu => ?_, fun w hw => ?_⟩
    · rw [hUdef, LinearMap.mem_ker] at hu ⊢
      rw [projI_comm_of_preserves ρ hp hA hpK I f hf, hu, map_zero]
    · obtain ⟨v, rfl⟩ := hw
      exact ⟨f v, projI_comm_of_preserves ρ hp hA hpK I f hf v⟩
  have hθmem : ∀ x : ↥(innerPart S B), ((Dat.θ x : ↥H) : GL ι K) ∈ Aε := fun x =>
    hle ⟨Dat.θ x, ⟨x, rfl⟩, rfl⟩
  have hθpres : ∀ x : ↥(innerPart S B),
      (∀ u ∈ U, glEquiv (Dat.θ x : GL ι K) u ∈ U) ∧ ∀ w ∈ W, glEquiv (Dat.θ x : GL ι K) w ∈ W :=
    fun x => by
      have := hpres (ρ ⟨_, hθmem x⟩).toAddMonoidHom (hρW ⟨_, hθmem x⟩)
      simpa only [LinearMap.toAddMonoidHom_coe, hρdef, glRep_apply_eq_glEquiv] using this
  set T : Finset (Hyperplane ↥Aε p) :=
    Finset.univ.filter fun H' => weightSpace ρ H'.1 ≠ ⊥ with hTdef
  have hT : ∀ H' : Hyperplane ↥Aε p, H' ∈ T ↔ weightSpace ρ H'.1 ≠ ⊥ := fun H' => by
    simp [hTdef]
  have hIT : I ⊆ T := fun H' hH' => (hT H').mpr (hI H' hH')
  have hfixU : ∀ a : ↥Aε, (∀ u ∈ U, ρ a u = u) ↔ a ∈ ⨅ H' ∈ T \ I, H'.1 := by
    intro a
    rw [Subgroup.mem_iInf]
    constructor
    · intro ha H'
      rw [Subgroup.mem_iInf]
      intro hH'
      obtain ⟨hH'T, hH'I⟩ := Finset.mem_sdiff.mp hH'
      by_contra haH'
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ((hT H').mp hH'T)
      have hvU : v ∈ U := by
        rw [hUdef, LinearMap.mem_ker]
        have hi : ∀ H₁ ∈ I, (some H' : Option (Hyperplane ↥Aε p)) ≠ some H₁ := by
          intro H₁ hH₁ h
          exact hH'I (by rw [Option.some.inj h]; exact hH₁)
        exact projI_apply_of_not_mem ρ hp hA hpK hi (by rw [weightFamily_some]; exact hv)
      exact hv0 (eq_zero_of_mem_weightSpace_of_fixed ρ hp hA hpK haH' hv (ha v hvU))
    · intro ha u hu
      have h0 : ∀ H₁ ∈ I, ρ.asAlgebraHom (eps K (↥Aε) p (some H₁)) u = 0 :=
        (projI_eq_zero_iff ρ hp hA hpK I u).mp hu
      conv_lhs => rw [← sum_eps_apply ρ hp hA hpK u, map_sum]
      conv_rhs => rw [← sum_eps_apply ρ hp hA hpK u]
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases i with _ | H₁
      · exact apply_asAlgebraHom_eSub ρ (Subgroup.mem_top a) u
      · by_cases hH₁ : H₁ ∈ I
        · rw [h0 H₁ hH₁, map_zero]
        · by_cases hbot : weightSpace ρ H₁.1 = ⊥
          · have h1 : ρ.asAlgebraHom (eps K (↥Aε) p (some H₁)) u = 0 := by
              have hmem : ρ.asAlgebraHom (eps K (↥Aε) p (some H₁)) u ∈ weightSpace ρ H₁.1 :=
                ⟨u, rfl⟩
              rw [hbot, Submodule.mem_bot] at hmem
              exact hmem
            rw [h1, map_zero]
          · have ha' := ha H₁
            rw [Subgroup.mem_iInf] at ha'
            exact apply_eq_of_mem_weightSpace ρ
              (ha' (Finset.mem_sdiff.mpr ⟨(hT H₁).mpr hbot, hH₁⟩)) ⟨u, rfl⟩
  have hcardU : Nat.card ↥(⨅ H' ∈ T \ I, H'.1) = p ^ I.card :=
    card_biInf_sdiff β ρ hp hA hpK hρ hmaxE h𝒮 h𝒮W (glRep_injective Aε) T hT hIT
  have hU0 : U ≠ ⊥ := by
    intro hbot
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₀
    have hvU : v ∈ U := by
      rw [hUdef, LinearMap.mem_ker]
      have hi : ∀ H₁ ∈ I, (some H₀ : Option (Hyperplane ↥Aε p)) ≠ some H₁ := by
        intro H₁ hH₁ h
        exact hH₀ (by rw [Option.some.inj h]; exact hH₁)
      exact projI_apply_of_not_mem ρ hp hA hpK hi (by rw [weightFamily_some]; exact hv)
    rw [hbot, Submodule.mem_bot] at hvU
    exact hv0 hvU
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hscal1 : ∀ c : Kˣ, (∀ u ∈ U, glEquiv (Matrix.GeneralLinearGroup.scalar ι c) u = u) →
      c = 1 := by
    intro c hc
    have h1 := hc u₀ hu₀
    rw [glEquiv_scalar_apply] at h1
    have h1' : ((c : K) - 1) • u₀ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp h1').resolve_right hu₀0))
  have hLscal : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ L → c = 1 := by
    rintro c ⟨y, ⟨x, rfl⟩, hy⟩
    have hk : Dat.θ x ∈ Dat.φ.ker := by
      rw [Dat.ker_eq, Subgroup.mem_subgroupOf]
      exact ⟨c, hy.symm⟩
    have hθ1 : Dat.θ x = 1 := by
      have hmem : Dat.θ x ∈ Dat.θ.range ⊓ Dat.φ.ker := ⟨⟨x, rfl⟩, hk⟩
      rw [Dat.range_inf_ker, Subgroup.mem_bot] at hmem
      exact hmem
    have hsc : Matrix.GeneralLinearGroup.scalar ι c = 1 := by
      rw [← hy]
      show ((Dat.θ x : ↥H) : GL ι K) = 1
      rw [hθ1]
      rfl
    apply hscal1 c
    intro u _
    rw [hsc, map_one]
    rfl
  set F : Subgroup (GL ι K) := (⨅ H' ∈ T \ I, H'.1).map Aε.subtype with hFdef
  set A₀ : Subgroup (GL ι K) := Aε ⊓ StatedScalars ι K with hA₀def
  set M : Subgroup (GL ι K) := scalarOnGL U ⊓ Aε with hMdef
  have hmemF : ∀ g : GL ι K, g ∈ F ↔ g ∈ Aε ∧ ∀ u ∈ U, glEquiv g u = u := by
    intro g
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, fun u hu => ?_⟩
      have := (hfixU a).mpr ha u hu
      rwa [hρdef, glRep_apply_eq_glEquiv] at this
    · rintro ⟨hg, hgU⟩
      refine ⟨⟨g, hg⟩, (hfixU ⟨g, hg⟩).mp fun u hu => ?_, rfl⟩
      rw [hρdef, glRep_apply_eq_glEquiv]
      exact hgU u hu
  have hcardF : Nat.card F = p ^ I.card := by
    rw [hFdef, Subgroup.card_map_of_injective Aε.subtype_injective, hcardU]
  have hcommA : ∀ g₁ ∈ Aε, ∀ g₂ ∈ Aε, g₁ * g₂ = g₂ * g₁ := fun g₁ h₁ g₂ h₂ =>
    congrArg Subtype.val (mul_comm (⟨g₁, h₁⟩ : ↥Aε) ⟨g₂, h₂⟩)
  have hA₀scal : ∀ g ∈ A₀, ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = g := by
    rintro g ⟨-, c, hc⟩
    exact ⟨c, hc⟩
  have hFA₀ : F ⊓ A₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgF, hgA₀⟩
    obtain ⟨c, rfl⟩ := hA₀scal g hgA₀
    rw [Subgroup.mem_bot, hscal1 c ((hmemF _).mp hgF).2, map_one]
  have hLA₀ : (M ⊓ L) ⊓ A₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨⟨-, hgL⟩, hgA₀⟩
    obtain ⟨c, rfl⟩ := hA₀scal g hgA₀
    rw [Subgroup.mem_bot, hLscal c hgL, map_one]
  have hMF : M = F ⊔ A₀ := by
    apply le_antisymm
    · rintro g ⟨⟨c, hc⟩, hgA⟩
      obtain ⟨c', hc', hc'A⟩ := hscal g hgA c hc
      have hgF : (Matrix.GeneralLinearGroup.scalar ι c')⁻¹ * g ∈ F := by
        refine (hmemF _).mpr ⟨Aε.mul_mem (Aε.inv_mem hc'A) hgA, fun u hu => ?_⟩
        rw [map_mul, LinearEquiv.mul_apply, hc u hu, map_smul, ← map_inv, glEquiv_scalar_apply,
          smul_smul, ← hc', Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero c'),
          one_smul]
      have h1 : g = Matrix.GeneralLinearGroup.scalar ι c' *
          ((Matrix.GeneralLinearGroup.scalar ι c')⁻¹ * g) := by group
      rw [h1, sup_comm]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hc'A, c', rfl⟩)
        (Subgroup.mem_sup_right hgF)
    · refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · obtain ⟨hgA, hgU⟩ := (hmemF g).mp hg
        exact ⟨⟨1, fun u hu => by rw [hgU u hu, one_smul]⟩, hgA⟩
      · obtain ⟨c, rfl⟩ := hA₀scal g hg
        exact ⟨⟨c, fun u _ => glEquiv_scalar_apply c u⟩, hg.1⟩
  have hML : M = (M ⊓ L) ⊔ A₀ := by
    apply le_antisymm
    · rintro g hg
      obtain ⟨c, hcA, hcL⟩ := hdec g hg.2
      have hcM : Matrix.GeneralLinearGroup.scalar ι c ∈ M :=
        ⟨⟨c, fun u _ => glEquiv_scalar_apply c u⟩, hcA⟩
      have h1 : g = (Matrix.GeneralLinearGroup.scalar ι c)⁻¹ *
          (Matrix.GeneralLinearGroup.scalar ι c * g) := by group
      rw [h1, sup_comm]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (A₀.inv_mem ⟨hcA, c, rfl⟩))
        (Subgroup.mem_sup_right ⟨M.mul_mem hcM hg, hcL⟩)
    · refine sup_le inf_le_left (fun g hg => ?_)
      obtain ⟨c, rfl⟩ := hA₀scal g hg
      exact ⟨⟨c, fun u _ => glEquiv_scalar_apply c u⟩, hg.1⟩
  have hcomm₀ : ∀ X : Subgroup (GL ι K), ∀ g ∈ X, ∀ g₀ ∈ A₀, g * g₀ = g₀ * g := by
    intro X g _ g₀ hg₀
    obtain ⟨c, rfl⟩ := hA₀scal g₀ hg₀
    exact (scalarGL_mul_comm c g).symm
  have hcardML : Nat.card ↥(M ⊓ L) = p ^ I.card := by
    have h1 : Nat.card M = Nat.card F * Nat.card A₀ := by
      conv_lhs => rw [hMF]
      exact CFSG.CGT.T75P.card_sup_of_commute (hcomm₀ F) hFA₀
    have h2 : Nat.card M = Nat.card ↥(M ⊓ L) * Nat.card A₀ := by
      conv_lhs => rw [hML]
      exact CFSG.CGT.T75P.card_sup_of_commute (hcomm₀ _) hLA₀
    have hpos : 0 < Nat.card A₀ := Nat.card_pos
    rw [← hcardF]
    exact Nat.eq_of_mul_eq_mul_right hpos (h2.symm.trans h1)
  let θ' : ↥(innerPart S B) →* GL ι K := H.subtype.comp Dat.θ
  have hrange : θ'.range = L := by rw [hLdef, MonoidHom.range_comp]
  let D : Subgroup Ω := ((scalarOnGL U).comap θ').map (innerPart S B).subtype
  have hDB : D ≤ innerPart S B := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hD : ∀ x : ↥(innerPart S B),
      (x : Ω) ∈ D ↔ ∃ c : K, ∀ u ∈ U, glEquiv (Dat.θ x : GL ι K) u = c • u := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro h
      exact ⟨x, h, rfl⟩
  have hcardD : Nat.card D = p ^ (1 + I.card) := by
    have h1 : Nat.card D = Nat.card ↥((scalarOnGL U).comap θ') :=
      Subgroup.card_map_of_injective (innerPart S B).subtype_injective
    have h2 : (scalarOnGL U).comap θ' = (scalarOnGL U ⊓ θ'.range).comap θ' := by
      rw [Subgroup.comap_inf, MonoidHom.comap_range_self, inf_top_eq]
    have h3 := card_comap_eq_mul_ker θ' (E := scalarOnGL U ⊓ θ'.range) inf_le_right
    have h4 : scalarOnGL U ⊓ θ'.range = M ⊓ L := by
      rw [hrange, hMdef, inf_assoc, inf_eq_right.mpr hle]
    have h5 : Nat.card θ'.ker = p := by
      have hk : θ'.ker = Dat.θ.ker := by
        ext x
        rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
        exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      have hBC' : Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) = p := by
        rw [← ModelGen.inf_centMod_eq_inf_centralizer hSn hcore]
        exact hBC
      have hinf : innerPart S B ⊓ Subgroup.centralizer (S : Set Ω) =
          B ⊓ Subgroup.centralizer (S : Set Ω) := by
        rw [inf_assoc, inf_eq_right.mpr (le_sup_right : Subgroup.centralizer (S : Set Ω) ≤
          S ⊔ Subgroup.centralizer (S : Set Ω))]
      have hker : Dat.θ.ker = (innerPart S B ⊓ Subgroup.centralizer (S : Set Ω)).subgroupOf
          (innerPart S B) := by
        ext x
        rw [MonoidHom.mem_ker, Dat.θ_eq_one, Subgroup.mem_subgroupOf]
        exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
      rw [hk, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hinf,
        hBC']
    rw [h1, h2, h3, h4, hcardML, h5, pow_add, pow_one, mul_comm]
  obtain ⟨xI, hxI, hxI'⟩ := exists_supported_element β ρ hp hA hpK hρ hmaxE h𝒮 h𝒮W I hI
  have hxIU : ∀ u ∈ U, glEquiv (xI : GL ι K) u = u := fun u hu => by
    have := (apply_eq_self_iff_projI ρ hp hA hpK hxI hxI' u).mpr hu
    rwa [hρdef, glRep_apply_eq_glEquiv] at this
  obtain ⟨c₁, hc₁A, hc₁L⟩ := hdec xI xI.2
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ↥(innerPart S B),
      θ' x₁ = Matrix.GeneralLinearGroup.scalar ι c₁ * (xI : GL ι K) := by
    have : Matrix.GeneralLinearGroup.scalar ι c₁ * (xI : GL ι K) ∈ θ'.range := by
      rw [hrange]
      exact hc₁L
    exact this
  have hx₁D : (x₁ : Ω) ∈ D := by
    rw [hD]
    refine ⟨c₁, fun u hu => ?_⟩
    rw [show (Dat.θ x₁ : GL ι K) = θ' x₁ from rfl, hx₁, map_mul, LinearEquiv.mul_apply,
      hxIU u hu, glEquiv_scalar_apply]
  have hCpres : ∀ g ∈ H, (∀ x : ↥(innerPart S B), (x : Ω) ∈ D →
      g * (Dat.θ x : GL ι K) = Dat.θ x * g) →
      (∀ u ∈ U, glEquiv g u ∈ U) ∧ ∀ w ∈ W, glEquiv g w ∈ W := by
    intro g _ hg
    have hg₁ : g * (Matrix.GeneralLinearGroup.scalar ι c₁ * (xI : GL ι K)) =
        Matrix.GeneralLinearGroup.scalar ι c₁ * (xI : GL ι K) * g := by
      rw [← hx₁]
      exact hg x₁ hx₁D
    have hgx : g * (xI : GL ι K) = xI * g := by
      have h1 : Matrix.GeneralLinearGroup.scalar ι c₁ * (g * (xI : GL ι K)) =
          Matrix.GeneralLinearGroup.scalar ι c₁ * ((xI : GL ι K) * g) := by
        rw [← mul_assoc, scalarGL_mul_comm c₁ g, mul_assoc, hg₁, mul_assoc]
      exact mul_left_cancel h1
    have hcomm : ∀ v, (glEquiv g : (ι → K) →ₗ[K] (ι → K)) (ρ xI v) = ρ xI (glEquiv g v) := by
      intro v
      simp only [hρdef, glRep_apply_eq_glEquiv, LinearEquiv.coe_coe]
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, hgx]
    exact preserves_of_comm_supported ρ hp hA hpK hxI hxI' _ hcomm
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hs
    exact zero_ne_one hs
  have hz2 : z ^ 2 = 1 := by
    apply glEquiv.injective
    rw [map_pow, map_one, pow_two]
    refine linearEquiv_ext_of_isCompl hUW (fun u hu => ?_) fun w hw => ?_
    · rw [LinearEquiv.mul_apply, hzU u hu, map_smul, hzU u hu, smul_smul, hs, one_smul]
      rfl
    · rw [LinearEquiv.mul_apply, hzW w hw, map_smul, hzW w hw, smul_smul, neg_mul_neg, hs,
        one_smul]
      rfl
  have hε : s ≠ -s := by
    intro h
    apply hs0
    have h' : (2 : K) * s = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h2
  have hW0 : W ≠ ⊥ := by
    obtain ⟨H₁, hH₁⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hI H₁ hH₁)
    intro hbot
    have : v ∈ W := ⟨v, projI_apply_of_mem ρ hp hA hpK hH₁ hv⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hv0 this
  refine concA_of_block hp hB hBC Dat hHβ hUW hIH hIq hpI hDB hD (fun x => (hθpres x).1)
    (fun x => (hθpres x).2) hCpres hSchur (fun hF => ⟨fun u hu => ?_, fun w hw => ?_,
      hfield hF⟩) ?_ ?_ ?_ hzH hz2 hε hzU hzW hU0 hW0
  · exact (hpres _ (h𝒮W _ ⟨hF, rfl⟩)).1 u hu
  · exact (hpres _ (h𝒮W _ ⟨hF, rfl⟩)).2 w hw
  · rw [hcardD]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  · rw [hcardD, ← pow_add]
    exact (Nat.pow_le_pow_right hp.pos (by omega)).trans hrank
  · intro hD2
    rw [hcardD] at hD2
    have hI' : I.card = 1 := by
      have := Nat.pow_right_injective hp.two_le hD2
      omega
    rcases hE hI' with ⟨a, haA, hau, hlay⟩ | ⟨hF, hlay⟩
    · left
      obtain ⟨c, hcA, hcL⟩ := hdec a haA
      obtain ⟨x, hx⟩ : ∃ x : ↥(innerPart S B),
          θ' x = Matrix.GeneralLinearGroup.scalar ι c * a := by
        have : Matrix.GeneralLinearGroup.scalar ι c * a ∈ θ'.range := by
          rw [hrange]
          exact hcL
        exact this
      have hxa : (Dat.θ x : GL ι K) = Matrix.GeneralLinearGroup.scalar ι c * a := hx
      refine ⟨x, fun hxD => hau ?_, ?_⟩
      · obtain ⟨d, hd⟩ := (hD x).mp hxD
        refine ⟨(c : K)⁻¹ * d, fun u hu => ?_⟩
        have h1 := hd u hu
        rw [hxa, map_mul, LinearEquiv.mul_apply, glEquiv_scalar_apply] at h1
        rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ (Units.ne_zero c), one_smul]
      · have hC : Subgroup.centralizer {(Dat.θ x : GL ι K)} = Subgroup.centralizer {a} := by
          ext g
          simp only [Subgroup.mem_centralizer_singleton_iff, hxa]
          have e1 : g * (Matrix.GeneralLinearGroup.scalar ι c * a) =
              Matrix.GeneralLinearGroup.scalar ι c * (g * a) := by
            rw [← mul_assoc, ← scalarGL_mul_comm c g, mul_assoc]
          have e2 : Matrix.GeneralLinearGroup.scalar ι c * a * g =
              Matrix.GeneralLinearGroup.scalar ι c * (a * g) := mul_assoc _ _ _
          rw [e1, e2, mul_right_inj]
        rw [hC]
        exact hlay
    · exact Or.inr ⟨hF, hlay⟩

end Weights

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
