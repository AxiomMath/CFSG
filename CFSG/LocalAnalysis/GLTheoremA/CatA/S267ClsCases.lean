module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsMaxEng
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt

section Decomp

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] [Finite A] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V] (ρ : Representation K A V)
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hp hA hpK

theorem isCompl_ker_range_projI (I : Finset (Hyperplane A p)) :
    IsCompl (LinearMap.ker (projI ρ I)) (LinearMap.range (projI ρ I)) := by
  have hidem : IsIdempotentElem (projI ρ I) :=
    LinearMap.ext fun v => projI_projI ρ hp hA hpK I v
  exact (LinearMap.IsIdempotentElem.isCompl hidem).symm

theorem projI_eq_zero_iff (I : Finset (Hyperplane A p)) (v : V) :
    projI ρ I v = 0 ↔ ∀ H ∈ I, ρ.asAlgebraHom (eps K A p (some H)) v = 0 := by
  classical
  constructor
  · intro h H hH
    have h1 : projI ρ I (ρ.asAlgebraHom (eps K A p (some H)) v) =
        ρ.asAlgebraHom (eps K A p (some H)) v :=
      projI_apply_of_mem ρ hp hA hpK hH ⟨v, rfl⟩
    rw [← h1, ← Module.End.mul_apply, show projI ρ I * ρ.asAlgebraHom (eps K A p (some H)) =
      ρ.asAlgebraHom (eps K A p (some H)) * projI ρ I from LinearMap.ext fun w =>
        (projI_comm_of_preserves ρ hp hA hpK I
          (ρ.asAlgebraHom (eps K A p (some H))).toAddMonoidHom
          (fun i u hu => ?_) w)]
    · rw [Module.End.mul_apply, h, map_zero]
    · rcases eq_or_ne i (some H) with rfl | hne
      · exact ⟨u, rfl⟩
      · have := eps_apply_of_mem_ne ρ hp hA hpK hne.symm hu
        simp only [LinearMap.toAddMonoidHom_coe, this]
        exact Submodule.zero_mem _
  · intro h
    rw [projI_apply]
    exact Finset.sum_eq_zero h

theorem apply_eq_self_iff_projI {I : Finset (Hyperplane A p)} {x : A} (hx : ∀ H ∈ I, x ∉ H.1)
    (hx' : ∀ H' : Hyperplane A p, H' ∉ I → weightSpace ρ H'.1 ≠ ⊥ → x ∈ H'.1) (v : V) :
    ρ x v = v ↔ projI ρ I v = 0 := by
  rw [apply_eq_self_iff_of_supported ρ hp hA hpK hx hx', projI_eq_zero_iff ρ hp hA hpK]

theorem preserves_of_comm_supported [FiniteDimensional K V] {I : Finset (Hyperplane A p)}
    {x : A} (hx : ∀ H ∈ I, x ∉ H.1)
    (hx' : ∀ H' : Hyperplane A p, H' ∉ I → weightSpace ρ H'.1 ≠ ⊥ → x ∈ H'.1)
    (g : V →ₗ[K] V) (hg : ∀ v, g (ρ x v) = ρ x (g v)) :
    (∀ u ∈ LinearMap.ker (projI ρ I), g u ∈ LinearMap.ker (projI ρ I)) ∧
      ∀ w ∈ LinearMap.range (projI ρ I), g w ∈ LinearMap.range (projI ρ I) := by
  have hfix := apply_eq_self_iff_projI ρ hp hA hpK hx hx'
  have hρW : ∀ w ∈ LinearMap.range (projI ρ I), ρ x w ∈ LinearMap.range (projI ρ I) := by
    rintro _ ⟨v, rfl⟩
    refine ⟨ρ x v, ?_⟩
    have := projI_comm_of_preserves ρ hp hA hpK I (ρ x).toAddMonoidHom
      (fun i u hu => preserves_weightFamily_of_semilinear ρ (RingHom.id K) (ρ x).toAddMonoidHom
        (fun c w => map_smul (ρ x) c w)
        (fun a w => by
          show ρ x (ρ a w) = ρ a (ρ x w)
          rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply])
        i hu) v
    exact this
  refine ⟨fun u hu => ?_, fun w hw => ?_⟩
  · rw [LinearMap.mem_ker, ← hfix] at hu ⊢
    rw [← hg, hu]
  ·
    set W := LinearMap.range (projI ρ I) with hWdef
    have hT : ∀ w ∈ W, (ρ x - 1) w ∈ W := fun w hw =>
      W.sub_mem (hρW w hw) (by simpa using hw)
    let T : W →ₗ[K] W := (ρ x - 1).restrict hT
    have hTinj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨w, hw⟩ h0
      have h1 : ρ x w = w := by
        have := congrArg Subtype.val h0
        simp only [T, LinearMap.restrict_coe_apply, LinearMap.sub_apply, Module.End.one_apply,
          ZeroMemClass.coe_zero] at this
        exact sub_eq_zero.mp this
      have h2 : projI ρ I w = 0 := (hfix w).mp h1
      obtain ⟨v, rfl⟩ := hw
      apply Subtype.ext
      simpa [projI_projI ρ hp hA hpK] using h2
    obtain ⟨⟨w', hw'⟩, hTw'⟩ := (LinearMap.injective_iff_surjective.mp hTinj) ⟨w, hw⟩
    have hww' : w = ρ x w' - w' := by
      have := congrArg Subtype.val hTw'
      simp only [T, LinearMap.restrict_coe_apply, LinearMap.sub_apply, Module.End.one_apply] at this
      exact this.symm
    rw [hww', map_sub, hg]
    have hsub : ∀ v, ρ x v - v ∈ W := by
      intro v
      have hv : v = (v - projI ρ I v) + projI ρ I v := by abel
      have hu : ρ x (v - projI ρ I v) = v - projI ρ I v := by
        rw [hfix, map_sub, projI_projI ρ hp hA hpK, sub_self]
      rw [hv, map_add, hu, add_sub_add_left_eq_sub]
      exact W.sub_mem (hρW _ ⟨v, rfl⟩) ⟨v, rfl⟩
    exact hsub _

end Decomp

section Weights

open scoped IsMulCommutative

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}
variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
variable {H : Subgroup (GL ι K)} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

noncomputable abbrev wtU (Aε : Subgroup (GL ι K)) [IsMulCommutative Aε] (I : Finset (Hyperplane ↥Aε p)) :
    Submodule K (ι → K) :=
  LinearMap.ker (projI (glRep Aε) I)

noncomputable abbrev wtW (Aε : Subgroup (GL ι K)) [IsMulCommutative Aε] (I : Finset (Hyperplane ↥Aε p)) :
    Submodule K (ι → K) :=
  LinearMap.range (projI (glRep Aε) I)

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

theorem concA_of_weights (hp : p.Prime) [hSn : S.Normal] (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hcore : GLAPPrimeCore p ↥S = ⊥)
    [Finite K] (h2 : (2 : K) ≠ 0) (hpK : (p : K) ≠ 0) (Dat : ClsInner p S B H β)
    (hHβ : H ≤ isomGL β) {Aε : Subgroup (GL ι K)} [IsMulCommutative Aε]
    (hA : ∀ a : ↥Aε, a ^ p = 1) (hAεL : Aε = liftGroup Dat) (hAεβ : Aε ≤ isomGL β)
    (hAε𝒮 : Aε ≤ centGL (fieldSet Dat)) (hmaxE : IsMaxElem β (glRep Aε) p (fieldSet Dat))
    [DecidableEq (Hyperplane ↥Aε p)] (I : Finset (Hyperplane ↥Aε p))
    (hI : ∀ H' ∈ I, weightSpace (glRep Aε) H'.1 ≠ ⊥) (hI1 : 1 ≤ I.card)
    {H₀ : Hyperplane ↥Aε p} (hH₀ : H₀ ∉ I) (hW₀ : weightSpace (glRep Aε) H₀.1 ≠ ⊥)
    (hrank : p ^ (3 + I.card) ≤ Nat.card B)
    (hzH : glEquiv.symm (invol (glRep Aε) hp hA hpK I) ∈ H)
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
    (hscal : ∀ y ∈ Aε, ∀ c : K, (∀ u ∈ wtU Aε I, glEquiv y u = c • u) → c = 1)
    (hE : I.card = 1 →
      (∃ a ∈ Aε, (∃ u ∈ wtU Aε I, glEquiv a u ≠ u) ∧
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
  have hθmem : ∀ x : ↥(innerPart S B), ((Dat.θ x : ↥H) : GL ι K) ∈ Aε := fun x => by
    rw [hAεL]
    exact ⟨Dat.θ x, ⟨x, rfl⟩, rfl⟩
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
  let θ' : ↥(innerPart S B) →* GL ι K := H.subtype.comp Dat.θ
  let FixU : Subgroup (GL ι K) := (fixGL U).comap glEquiv.toMonoidHom
  have hmemFix : ∀ g : GL ι K, g ∈ FixU ↔ ∀ u ∈ U, glEquiv g u = u := fun g => Iff.rfl
  let D : Subgroup Ω := (FixU.comap θ').map (innerPart S B).subtype
  have hDB : D ≤ innerPart S B := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hmemD : ∀ x : ↥(innerPart S B), (x : Ω) ∈ D ↔ ∀ u ∈ U, glEquiv (θ' x) u = u := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro h
      exact ⟨x, h, rfl⟩
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
  have hD : ∀ x : ↥(innerPart S B),
      (x : Ω) ∈ D ↔ ∃ c : K, ∀ u ∈ U, glEquiv (Dat.θ x : GL ι K) u = c • u := by
    intro x
    rw [hmemD]
    constructor
    · intro h
      exact ⟨1, fun u hu => by rw [one_smul]; exact h u hu⟩
    · rintro ⟨c, hc⟩
      have hc1 := hscal _ (hθmem x) c hc
      intro u hu
      rw [show θ' x = (Dat.θ x : GL ι K) from rfl, hc u hu, hc1, one_smul]
  have hcardD : Nat.card D = p ^ (1 + I.card) := by
    have h1 : Nat.card D = Nat.card ↥(FixU.comap θ') :=
      Subgroup.card_map_of_injective (innerPart S B).subtype_injective
    have hrange : θ'.range = Aε := by
      rw [hAεL, MonoidHom.range_comp]
    have h2 : FixU.comap θ' = (FixU ⊓ θ'.range).comap θ' := by
      rw [Subgroup.comap_inf, MonoidHom.comap_range_self, inf_top_eq]
    have h3 := card_comap_eq_mul_ker θ' (E := FixU ⊓ θ'.range) inf_le_right
    have h4 : FixU ⊓ θ'.range = (⨅ H' ∈ T \ I, H'.1).map Aε.subtype := by
      ext g
      rw [Subgroup.mem_inf, hrange]
      constructor
      · rintro ⟨hgU, hgA⟩
        refine ⟨⟨g, hgA⟩, (hfixU ⟨g, hgA⟩).mp fun u hu => ?_, rfl⟩
        rw [hρdef, glRep_apply_eq_glEquiv]
        exact hgU u hu
      · rintro ⟨a, ha, rfl⟩
        refine ⟨fun u hu => ?_, a.2⟩
        have := (hfixU a).mpr ha u hu
        rwa [hρdef, glRep_apply_eq_glEquiv] at this
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
    rw [h1, h2, h3, h4, Subgroup.card_map_of_injective Aε.subtype_injective, hcardU, h5,
      pow_add, pow_one, mul_comm]
  obtain ⟨xI, hxI, hxI'⟩ := exists_supported_element β ρ hp hA hpK hρ hmaxE h𝒮 h𝒮W I hI
  have hxIU : ∀ u ∈ U, ρ xI u = u := fun u hu =>
    (apply_eq_self_iff_projI ρ hp hA hpK hxI hxI' u).mpr hu
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ↥(innerPart S B), θ' x₁ = (xI : GL ι K) := by
    have : (xI : GL ι K) ∈ θ'.range := by
      rw [show θ'.range = Aε by rw [hAεL, MonoidHom.range_comp]]
      exact xI.2
    exact this
  have hx₁D : (x₁ : Ω) ∈ D := by
    rw [hmemD, hx₁]
    intro u hu
    have := hxIU u hu
    rwa [hρdef, glRep_apply_eq_glEquiv] at this
  have hCpres : ∀ g ∈ H, (∀ x : ↥(innerPart S B), (x : Ω) ∈ D →
      g * (Dat.θ x : GL ι K) = Dat.θ x * g) →
      (∀ u ∈ U, glEquiv g u ∈ U) ∧ ∀ w ∈ W, glEquiv g w ∈ W := by
    intro g _ hg
    have hgx : g * (xI : GL ι K) = xI * g := by rw [← hx₁]; exact hg x₁ hx₁D
    have hcomm : ∀ v, (glEquiv g : (ι → K) →ₗ[K] (ι → K)) (ρ xI v) = ρ xI (glEquiv g v) := by
      intro v
      simp only [hρdef, glRep_apply_eq_glEquiv, LinearEquiv.coe_coe]
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, hgx]
    exact preserves_of_comm_supported ρ hp hA hpK hxI hxI' _ hcomm
  set z : GL ι K := glEquiv.symm (invol ρ hp hA hpK I) with hzdef
  have hgz : glEquiv z = invol ρ hp hA hpK I := MulEquiv.apply_symm_apply _ _
  have hz2 : z ^ 2 = 1 := by
    apply glEquiv.injective
    rw [map_pow, hgz, map_one, pow_two]
    exact LinearEquiv.ext fun v => invol_invol ρ hp hA hpK I v
  have hzU : ∀ u ∈ U, glEquiv z u = (1 : K) • u := by
    intro u hu
    rw [hgz, invol_apply, one_smul, show projI ρ I u = 0 from hu, smul_zero, sub_zero]
  have hzW : ∀ w ∈ W, glEquiv z w = (-1 : K) • w := by
    rintro _ ⟨v, rfl⟩
    rw [hgz, invol_apply, projI_projI ρ hp hA hpK, neg_one_smul]
    module
  have hε : (1 : K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have hW0 : W ≠ ⊥ := by
    obtain ⟨H₁, hH₁⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hI H₁ hH₁)
    intro hbot
    have : v ∈ W := ⟨v, projI_apply_of_mem ρ hp hA hpK hH₁ hv⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hv0 this
  refine concA_of_block hp hB hBC Dat hHβ hUW hIH hIq hpI hDB hD (fun x => (hθpres x).1)
    (fun x => (hθpres x).2) hCpres hSchur (fun hF => ⟨fun u hu => ?_, fun w hw => ?_,
      hfield hF⟩) ?_ ?_ ?_ (z := z) (by rw [hzdef]; exact hzH) hz2 hε hzU hzW hU0 hW0
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
    rcases hE hI' with ⟨a, haA, ⟨u, hu, hau⟩, hlay⟩ | ⟨hF, hlay⟩
    · left
      obtain ⟨x, hx⟩ : ∃ x : ↥(innerPart S B), θ' x = a := by
        have : a ∈ θ'.range := by
          rw [show θ'.range = Aε by rw [hAεL, MonoidHom.range_comp]]
          exact haA
        exact this
      refine ⟨x, fun hxD => hau ?_, ?_⟩
      · have := (hmemD x).mp hxD u hu
        rwa [hx] at this
      · rw [show (Dat.θ x : GL ι K) = a from hx]
        exact hlay
    · exact Or.inr ⟨hF, hlay⟩

end Weights

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
