module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellOrbit
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellSpBlock
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellMult
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut

public section

open Matrix Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KCSpComm CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

section SemiMap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def semiMap (A : GL ι K) (σ : K ≃+* K) : (ι → K) →ₛₗ[(σ : K →+* K)] (ι → K) where
  toFun v := (A : Matrix ι ι K) *ᵥ (fun i => σ (v i))
  map_add' u v := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp
  map_smul' c v := by
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp

theorem semiMap_apply (A : GL ι K) (σ : K ≃+* K) (v : ι → K) :
    semiMap A σ v = (A : Matrix ι ι K) *ᵥ (fun i => σ (v i)) := rfl

theorem semiMap_injective (A : GL ι K) (σ : K ≃+* K) : Function.Injective (semiMap A σ) := by
  intro v w h
  rw [semiMap_apply, semiMap_apply] at h
  have h1 := congrArg (fun u => ((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ u) h
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at h1
  funext i
  exact σ.injective (congrFun h1 i)

theorem semiMap_bijective [Finite K] (A : GL ι K) (σ : K ≃+* K) :
    Function.Bijective (semiMap A σ) := by
  have : Finite (ι → K) := inferInstance
  exact ⟨semiMap_injective A σ, Finite.injective_iff_surjective.1 (semiMap_injective A σ)⟩

theorem semiMap_mulVec (A : GL ι K) (σ : K ≃+* K) (B : Matrix ι ι K) (v : ι → K) :
    semiMap A σ (B *ᵥ v) =
      ((A : Matrix ι ι K) * B.map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K)) *ᵥ semiMap A σ v := by
  have h1 : ((A⁻¹ : GL ι K) : Matrix ι ι K) * (A : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (fun i => σ ((B *ᵥ v) i)) = B.map σ *ᵥ (fun i => σ (v i)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  rw [semiMap_apply, semiMap_apply, Matrix.mulVec_mulVec, h2, Matrix.mulVec_mulVec]
  congr 1
  rw [Matrix.mul_assoc ((A : Matrix ι ι K) * B.map σ) ((A⁻¹ : GL ι K) : Matrix ι ι K)
    (A : Matrix ι ι K), h1, Matrix.mul_one]

end SemiMap

section SpGlue

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def projEquiv (hn : 1 ≤ n) [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    StatedSp n K ≃* StatedProj (StatedSp n K) :=
  MulEquiv.ofBijective (proj n K)
    ⟨(injective_iff_map_eq_one _).2 fun g hg => by
      have : g ∈ (proj n K).ker := hg
      rw [ker_proj_eq_bot hn hf hK] at this
      exact Subgroup.mem_bot.1 this, proj_surjective⟩

theorem projEquiv_apply (hn : 1 ≤ n) [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (g : StatedSp n K) : projEquiv hn hf hK g = proj n K g := rfl

theorem spPsi_proj (M : gsp n K) (σ : K ≃+* K) (g : StatedSp n K) :
    spPsi n K ⟨M, σ⟩ (proj n K g) = proj n K (conjSp n K M (fieldSp n K σ g)) := by
  rw [spPsi_mk]
  rfl

end SpGlue

section SpInner

variable {n : ℕ} {K : Type} [Field K]

open scoped IsMulCommutative

@[expose] noncomputable def linE (n : ℕ) (K : Type) [Field K] :
    StatedSp n K →* ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n ⊕ Fin n → K)).toMonoidHom.comp
    (spLin n K)

@[expose] def smat (g : StatedSp n K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)

theorem smat_mul (g h : StatedSp n K) : smat (g * h) = smat g * smat h := rfl

theorem linE_injective : Function.Injective (linE n K) := by
  intro a b hab
  apply spLin_injective
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n ⊕ Fin n → K)).injective hab

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem not_isSolvable_statedSp_of {s : ℕ} (hs : 2 ≤ s) {K : Type} [Field K] [Finite K]
    (hne : ¬ (s = 2 ∧ Nat.card K = 2)) : ¬ Group.IsSolvable (StatedSp s K) := by
  intro h
  obtain ⟨hsimple, hperf⟩ := simple_perfect_statedProj (r := s) (k := K) hs hne
  have hsolv : Group.IsSolvable (StatedProj (StatedSp s K)) :=
    Group.isSolvable_of_surjective (SymplecticHigher.proj_surjective (r := s) (K := K))
  have : Nontrivial (StatedProj (StatedSp s K)) := hsimple.toNontrivial
  exact CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect hsolv

theorem sp_inner_false (hn : 2 ≤ n) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hrq : ¬ (n = 2 ∧ 2 ^ f = 2))
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : ¬ r ∣ p - 1)
    (x : StatedSp n K) (hxp : x ^ p = 1)
    (Ē : Subgroup (StatedProj (StatedSp n K))) (hE : CFSG.Open.IsElemAbelian p Ē)
    (hcard : Nat.card Ē = p ^ 4)
    (hxE : ∀ y ∈ Ē, proj n K x * y * (proj n K x)⁻¹ = y)
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (StatedSp n K))))
    (g : SemiGSp n K) (k : ℕ) (hγ : spPsi n K g ^ r ^ k = 1)
    (hγE : ∀ y ∈ Ē, spPsi n K g y ∈ Ē)
    (hcomm : ∀ y, spPsi n K g (proj n K x * y * (proj n K x)⁻¹) =
      proj n K x * spPsi n K g y * (proj n K x)⁻¹)
    (hnt : ∃ y ∈ Ē, spPsi n K g y ≠ y) : False := by
  classical
  have hn1 : 1 ≤ n := by omega
  have : Fact p.Prime := ⟨hp⟩
  by_cases hx1 : x = 1
  · subst hx1
    have htop : Subgroup.centralizer ({1} : Set (StatedSp n K)) = ⊤ := by
      ext y; simp [Subgroup.mem_centralizer_iff]
    rw [htop] at hsolv
    apply not_isSolvable_statedSp_of hn (by rwa [hK]) 
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := StatedSp n K)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := StatedSp n K)).symm.injective
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  let ι := projEquiv hn1 hf hK
  have : IsMulCommutative ↥Ē := hE.1
  have : Fintype ↥Ē := Fintype.ofFinite _
  have hpK : (p : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm
  have hGp : ∀ e : ↥Ē, e ^ p = 1 := fun e => Subtype.ext (hE.2 e e.2)
  have hGK : ((Fintype.card ↥Ē : ℕ) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    push_cast
    exact pow_ne_zero _ hpK
  have hmap : Ē.map ((spPsi n K g : MulAut (StatedProj (StatedSp n K))) : _ →* _) = Ē := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hγE y hy
    · rw [Subgroup.card_map_of_injective (spPsi n K g).injective]
  let γE : MulAut ↥Ē :=
    ((spPsi n K g : MulAut (StatedProj (StatedSp n K))).subgroupMap Ē).trans
      (MulEquiv.subgroupCongr hmap)
  have hγE_apply : ∀ e : ↥Ē, ((γE e : ↥Ē) : StatedProj (StatedSp n K)) = spPsi n K g e :=
    fun e => rfl
  have hγpow_apply : ∀ (m : ℕ) (e : ↥Ē), (((γE ^ m) e : ↥Ē) : StatedProj (StatedSp n K)) =
      ((spPsi n K g) ^ m) e := by
    intro m
    induction m with
    | zero => intro e; rfl
    | succ m ih =>
      intro e
      rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, ih, hγE_apply]
  have hγE_pow : γE ^ r ^ k = 1 := by
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [hγpow_apply, hγ]
    rfl
  let ρ : ↥Ē →* ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
    (linE n K).comp (ι.symm.toMonoidHom.comp Ē.subtype)
  have hρ_apply : ∀ (e : ↥Ē) (v : Fin n ⊕ Fin n → K), ρ e v =
      smat (ι.symm (e : StatedProj (StatedSp n K))) *ᵥ v :=
    fun e v => rfl
  have hρinj : Function.Injective ρ :=
    linE_injective.comp (ι.symm.injective.comp Subtype.val_injective)
  let z : Module.End K (Fin n ⊕ Fin n → K) := spEnd x
  have hz_apply : ∀ v, z v = smat x *ᵥ v := fun v => rfl
  have hxlift : ∀ e : ↥Ē, smat x * smat (ι.symm (e : StatedProj (StatedSp n K))) =
      smat (ι.symm (e : StatedProj (StatedSp n K))) * smat x := by
    intro e
    have h1 := hxE e e.2
    have h3 : x * ι.symm (e : StatedProj (StatedSp n K)) * x⁻¹ =
        ι.symm (e : StatedProj (StatedSp n K)) := by
      apply ι.injective
      rw [map_mul, map_mul, map_inv, ι.apply_symm_apply, projEquiv_apply hn1 hf hK x]
      exact h1
    have h4 : x * ι.symm (e : StatedProj (StatedSp n K)) =
        ι.symm (e : StatedProj (StatedSp n K)) * x := by
      rw [mul_inv_eq_iff_eq_mul] at h3
      exact h3
    rw [← smat_mul, ← smat_mul, h4]
  have hcommz : ∀ e : ↥Ē, Commute z ((ρ e : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :
      Module.End K (Fin n ⊕ Fin n → K)) := by
    intro e
    refine LinearMap.ext fun v => ?_
    change z (ρ e v) = ρ e (z v)
    rw [hz_apply, hz_apply, hρ_apply, hρ_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hxlift]
  have hzp : z ^ p = 1 := by
    have h1 : (spLin n K x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K) =>
      (u : Module.End K (Fin n ⊕ Fin n → K))) h1
    simpa [z, spEnd, Units.val_pow_eq_pow_val] using h2
  let M : gsp n K := g.left
  let σ : K ≃+* K := g.right
  let fM := semiMap (M : GL (Fin n ⊕ Fin n) K) σ
  have hfbij : Function.Bijective fM := semiMap_bijective _ σ
  have hlift : ∀ e : ↥Ē, ι.symm (((γE e : ↥Ē)) : StatedProj (StatedSp n K)) =
      conjSp n K M (fieldSp n K σ (ι.symm (e : StatedProj (StatedSp n K)))) := by
    intro e
    apply ι.injective
    rw [ι.apply_symm_apply, projEquiv_apply hn1 hf hK, hγE_apply]
    have he : proj n K (ι.symm (e : StatedProj (StatedSp n K))) = (e : StatedProj (StatedSp n K)) := by
      rw [← projEquiv_apply hn1 hf hK, ι.apply_symm_apply]
    have := spPsi_proj M σ (ι.symm (e : StatedProj (StatedSp n K)))
    rw [he] at this
    exact this
  have hfρ : ∀ (e : ↥Ē) (v : Fin n ⊕ Fin n → K), fM (ρ e v) = ρ (γE e) (fM v) := by
    intro e v
    rw [hρ_apply, hρ_apply, hlift]
    change semiMap (M : GL (Fin n ⊕ Fin n) K) σ _ = smat _ *ᵥ _
    rw [semiMap_mulVec]
    congr 1
  have hconjAut : conjAut n K (spXg x) = MulAut.conj (proj n K x) := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨g', rfl⟩ := proj_surjective y
    rw [conjAut_proj]
    change proj n K (x * g' * x⁻¹) = _
    simp [MulAut.conj_apply]
  have hgcomm : spPsi n K g * conjAut n K (spXg x) * (spPsi n K g)⁻¹ = conjAut n K (spXg x) := by
    rw [mul_inv_eq_iff_eq_mul]
    refine MulEquiv.ext fun y => ?_
    change spPsi n K g (conjAut n K (spXg x) y) = conjAut n K (spXg x) (spPsi n K g y)
    rw [hconjAut]
    exact hcomm y
  have hXp : (spXg x) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have e : ((spXg x : gsp n K) : GL (Fin n ⊕ Fin n) K) =
        ((x : StatedSp n K) : GL (Fin n ⊕ Fin n) K) := rfl
    rw [e, ← Subgroup.coe_pow, hxp, Subgroup.coe_one]
  have hMX := sp_semilin_conj_eq_self hn1 (hp.odd_of_ne_two hp2)
    (show ((spXg x : gsp n K) : GL (Fin n ⊕ Fin n) K) ∈ StatedSp n K from x.2) hXp g hgcomm
  have hMXmat : ((M : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
      (smat x).map σ * (((M : GL (Fin n ⊕ Fin n) K)⁻¹ : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = smat x := by
    have h2 := congrArg (fun A : gsp n K => ((A : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hMX
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_gspAut,
      coe_glFieldEquiv] at h2
    exact h2
  have hfz : ∀ v, fM (z v) = z (fM v) := by
    intro v
    rw [hz_apply, hz_apply]
    change semiMap (M : GL (Fin n ⊕ Fin n) K) σ _ = _
    rw [semiMap_mulVec, hMXmat]
  have hσpow : σ ^ r ^ k = 1 := by
    have h1 : spPsi n K (g ^ r ^ k) = 1 := by rw [map_pow]; exact hγ
    obtain ⟨hr1, -⟩ := (spPsi_eq_one_iff hn1 _).1 h1
    have : (g ^ r ^ k).right = g.right ^ r ^ k :=
      map_pow (SemidirectProduct.rightHom : SemiGSp n K →* (K ≃+* K)) g (r ^ k)
    rw [this] at hr1
    exact hr1
  have hσ : ∀ h : K[X], h.Monic → Irreducible h → h ∣ X ^ p - 1 →
      h.map (σ : K →+* K) = h := fun h hm hi hd =>
    map_eq_of_irreducible_dvd hp hp2 hr hrp hK σ hσpow hm hi hd
  obtain ⟨y, hyE, hy⟩ := hnt
  have hg₀ : γE ⟨y, hyE⟩ ≠ ⟨y, hyE⟩ := fun h => hy (congrArg Subtype.val h)
  obtain ⟨h, hirr, hmon, hdvd, Mi, hMne, hMh, hMz, hMind⟩ :=
    exists_five_pieces hp hr hr5 hrp hpK hGp hGK ρ hρinj z hcommz hzp γE k hγE_pow ⟨y, hyE⟩ hg₀
      σ fM hfbij hfρ hfz hσ
  obtain ⟨v, hvM, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hMne 0)
  have hdvdmin : h ∣ minpoly K z := dvd_minpoly_of_aeval_eq_zero z hirr hv0 (hMh 0 v hvM)
  have hmem : h ∈ primaryFactors (spEnd x) := mem_primaryFactors.2 ⟨hirr, hmon, hdvdmin⟩
  have hmult : 5 ≤ primaryMultiplicity (spEnd x) h :=
    five_le_primaryMultiplicity z hirr Mi hMne hMh hMz hMind
  exact not_isSolvable_centralizer_of_mult hn1 hf hK hp hp2 hxord ⟨h, hmem⟩ hmult hsolv

end SpInner

section SpOuter

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

omit [CharP K 2] in
theorem sp_outer_false (hn : 2 ≤ n) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Ē : Subgroup (StatedProj (StatedSp n K))) (hcard : Nat.card Ē = p ^ 4)
    (ζ : MulAut (StatedProj (StatedSp n K)))
    (hζ : ζ ∈ spSemilinearAutGroup n K) (hζD : ζ ∉ spLinearAutGroup n K) (hζp : ζ ^ p = 1)
    (hζE : ∀ y ∈ Ē, ζ y = y) (hsolv : Group.IsSolvable ↥(autFix ζ)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have O := spOuter Nat.prime_two hf hn hK
  have hζ1 : ζ ≠ 1 := fun h1 => hζD (h1 ▸ one_mem _)
  have hord : orderOf ζ = p := orderOf_eq_prime hζp hζ1
  obtain ⟨-, σ, hσo, h, hhD, hζeq⟩ := O.descent p hp ζ hζ hζD hord
  have hσp : σ ^ p = 1 := by rw [← hσo]; exact pow_orderOf_eq_one σ
  have hrad := solvableRadical_fixedGroup hn (hp.odd_of_ne_two hp2) hσp
  let hh : MulAut (StatedProj (StatedSp n K)) := h
  let ψ : ↥(spFixedGroup (fieldAut n K σ)) →* ↥(autFix ζ) :=
    { toFun := fun a => ⟨hh a.1, by
        have ha : fieldAut n K σ a.1 = a.1 := a.2
        change ζ (hh a.1) = hh a.1
        rw [hζeq]
        change hh (fieldAut n K σ (hh⁻¹ (hh a.1))) = hh a.1
        rw [MulAut.inv_apply, MulEquiv.symm_apply_apply, ha]⟩
      map_one' := by
        apply Subtype.ext
        exact map_one hh
      map_mul' := fun a b => by
        apply Subtype.ext
        exact map_mul hh a.1 b.1 }
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    exact hh.injective (congrArg Subtype.val hab)
  have hsolvB : Group.IsSolvable ↥(spFixedGroup (fieldAut n K σ)) :=
    Group.isSolvable_of_isSolvable_injective (f := ψ) hψinj
  have htop : (⊤ : Subgroup ↥(spFixedGroup (fieldAut n K σ))) ≤
      CFSG.solvableRadical ↥(spFixedGroup (fieldAut n K σ)) :=
    le_sSup ⟨inferInstance, inferInstance⟩
  rw [hrad] at htop
  have hnt : ∃ e : ↥Ē, e ≠ 1 := by
    have : 1 < Nat.card Ē := by
      rw [hcard]
      exact Nat.one_lt_pow (by norm_num) hp.one_lt
    have hnt' := Finite.one_lt_card_iff_nontrivial.1 this
    obtain ⟨e, he⟩ := exists_ne (1 : ↥Ē)
    exact ⟨e, he⟩
  obtain ⟨e, he⟩ := hnt
  have hmemB : hh⁻¹ (e : StatedProj (StatedSp n K)) ∈ spFixedGroup (fieldAut n K σ) := by
    change fieldAut n K σ (hh⁻¹ e) = hh⁻¹ e
    have h1 := hζE e e.2
    rw [hζeq] at h1
    change hh (fieldAut n K σ (hh⁻¹ e)) = e at h1
    have := congrArg (fun y => hh⁻¹ y) h1
    simpa using this
  have h2 : (⟨hh⁻¹ (e : StatedProj (StatedSp n K)), hmemB⟩ :
      ↥(spFixedGroup (fieldAut n K σ))) ∈ (⊥ : Subgroup _) :=
    htop (Subgroup.mem_top _)
  rw [Subgroup.mem_bot] at h2
  have h3 : hh⁻¹ (e : StatedProj (StatedSp n K)) = 1 := congrArg Subtype.val h2
  apply he
  apply Subtype.ext
  have := congrArg (fun y => hh y) h3
  simpa using this

theorem sp_cell_P (hn : 2 ≤ n) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hrq : ¬ (n = 2 ∧ 2 ^ f = 2))
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : ¬ r ∣ p - 1)
    (Ē : Subgroup (StatedProj (StatedSp n K))) (hE : CFSG.Open.IsElemAbelian p Ē)
    (hcard : Nat.card Ē = p ^ 4) (ζ γ : MulAut (StatedProj (StatedSp n K)))
    (hζp : ζ ^ p = 1) (hζE : ∀ y ∈ Ē, ζ y = y) (hsolv : Group.IsSolvable ↥(autFix ζ))
    (hγ : ∃ k : ℕ, γ ^ r ^ k = 1) (hγE : ∀ y ∈ Ē, γ y ∈ Ē) (hcomm : γ * ζ = ζ * γ)
    (hnt : ∃ y ∈ Ē, γ y ≠ y) : False := by
  obtain ⟨k, hk⟩ := hγ
  have hn1 : 1 ≤ n := by omega
  have O := spOuter Nat.prime_two hf hn hK
  have hrodd : Odd (r ^ k) := (hr.odd_of_ne_two (by omega)).pow
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hγmem : γ ∈ spSemilinearAutGroup n K :=
    mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd
      (Odd.of_dvd_nat hrodd (orderOf_dvd_of_pow_eq_one hk))
  have hζmem : ζ ∈ spSemilinearAutGroup n K :=
    mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd
      (Odd.of_dvd_nat hpodd (orderOf_dvd_of_pow_eq_one hζp))
  by_cases hD : ζ ∈ spLinearAutGroup n K
  · obtain ⟨-, -, hconjinj⟩ := CFSG.RankThree.PartOne.spProj_facts (K := K) Nat.prime_two hf hK hn hrq
    have : (inner (StatedProj (StatedSp n K))).Normal := inner_normal _
    have hin : ζ ∈ inner (StatedProj (StatedSp n K)) :=
      mem_of_pow_eq_one_of_relIndex_dvd_two (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hp hp2
        hD hζp
    obtain ⟨y, rfl⟩ := hin
    let ι := projEquiv hn1 hf hK
    have hyp : y ^ p = 1 := by
      apply hconjinj
      rw [map_pow, hζp, map_one]
    let x : StatedSp n K := ι.symm y
    have hxp : x ^ p = 1 := by
      apply ι.injective
      rw [map_pow, ι.apply_symm_apply, hyp, map_one]
    have hpx : proj n K x = y := by
      rw [← projEquiv_apply hn1 hf hK]
      exact ι.apply_symm_apply y
    obtain ⟨g, hg⟩ : ∃ g : SemiGSp n K, spPsi n K g = γ := by
      have := hγmem
      rw [← range_spPsi] at this
      exact this
    refine sp_inner_false hn hf hK hrq hp hp2 hr hr5 hrp x hxp Ē hE hcard ?_ ?_ g k ?_ ?_ ?_ ?_
    · intro y' hy'
      have := hζE y' hy'
      rw [hpx]
      simpa [MulAut.conj_apply] using this
    ·
      let ψ : ↥(Subgroup.centralizer ({x} : Set (StatedSp n K))) →* ↥(autFix (MulAut.conj y)) :=
        { toFun := fun g' => ⟨proj n K g', by
            change MulAut.conj y (proj n K g') = proj n K g'
            rw [MulAut.conj_apply, ← hpx, ← map_inv, ← map_mul, ← map_mul]
            have hc : x * g' * x⁻¹ = g' := by
              have := Subgroup.mem_centralizer_iff.1 g'.2 x rfl
              rw [mul_inv_eq_iff_eq_mul]
              exact this
            rw [hc]⟩
          map_one' := by
            apply Subtype.ext
            exact map_one _
          map_mul' := fun a b => by
            apply Subtype.ext
            exact map_mul _ _ _ }
      have hinj : Function.Injective ψ := by
        intro a b hab
        apply Subtype.ext
        apply ι.injective
        exact congrArg Subtype.val hab
      exact Group.isSolvable_of_isSolvable_injective (f := ψ) hinj
    · rw [hg]; exact hk
    · intro y' hy'; rw [hg]; exact hγE y' hy'
    · intro y'
      rw [hg]
      have := congrArg (fun a : MulAut (StatedProj (StatedSp n K)) => a y') hcomm
      rw [← hg] at this
      simp only [MulAut.mul_apply] at this
      rw [hpx]
      simpa [MulAut.conj_apply, ← hg] using this
    · rw [hg]; exact hnt
  · exact sp_outer_false hn hf hK hp hp2 Ē hcard ζ hζmem hD hζp hζE hsolv

end SpOuter

end CFSG.HardMathSupport.Curtis.Coordinator.SPLCell
