module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21B02
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Mu

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc



section Frame

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {K K' J W : Subgroup Y}
  {z u t : Y}

theorem exists_reps (hP : Q3CL.PartIHypG Ω) (d : Data Ω K K' z u J t W) :
    ∃ ρ ρ' : Rep Ω W, ρ.K = K ∧ ρ'.K = J ∧ ρ'.K ∈ omegaNbr Ω ρ.K := by
  have hf := d.frame
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP d.hW
  obtain ⟨ρ, hρ⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hf.mem hf.hz d.hzW
  obtain ⟨ρ', hρ'⟩ := TL4.exists_rep_of_involution_mem_gen c hP.cls hf.hJ.1 hf.ht d.htW
  refine ⟨ρ, ρ', hρ, hρ', ?_⟩
  rw [hρ, hρ']
  exact hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)

theorem dSet_le_centralizer_tz (hP : Q3CL.PartIHypG Ω) (d : Data Ω K K' z u J t W)
    (hnc : ¬ DbarConnected Ω W) :
    ∀ R ∈ DSet Ω W, R ≤ Subgroup.centralizer ({t * z} : Set Y) := by
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP d.hW
  obtain ⟨ρ, ρ', hρ, hρ', hnbr⟩ := exists_reps hP d
  exact c.le_centralizer_mul_involutions hP.cls hnc ρ ρ' hnbr (hρ ▸ d.frame.hz) (hρ' ▸ d.frame.ht)

theorem mGrp_le_rLayer_tz (hP : Q3CL.PartIHypG Ω) (d : Data Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : MGrp Ω W ≤ rLayer Ω (t * z) := by
  have hle := dSet_le_centralizer_tz hP d (Q3T6.Mu.thompsonGraphAll hP d.frame.mem hne d.hW)
  exact iSup₂_le fun R hR => le_iSup₂_of_le R hR.1 (le_iSup_of_le (hle R hR) le_rfl)

theorem exists_mem_conj_of_dstarComp (hP : Q3CL.PartIHypG Ω) (d : Data Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {H : Subgroup Y} (hM : MGrp Ω W ≤ H)
    (hN : Subgroup.normalizer (K : Set Y) ≤ H) :
    ∀ L ∈ dstarComp Ω K, ∃ x ∈ H, conjSub x K = L := by
  have hΩ : HypOmegaGen Ω := hP.hyp
  have hK : K ∈ Ω := d.frame.mem
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP d.hW
  have hnc : ¬ DbarConnected Ω W := Q3T6.Mu.thompsonGraphAll hP hK hne d.hW
  obtain ⟨ρ, ρ', hρ, -, -⟩ := exists_reps hP d
  have hA : ∀ J₁ ∈ omegaStarNbr Ω K, ∃ x ∈ H, conjSub x K = J₁ := by
    intro J₁ hJ₁
    obtain ⟨g, ρ₁, σ₁, hρ₁, hσ₁⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hK hJ₁
    obtain ⟨m₁, hm₁, hm₁K⟩ := c.exists_conj_of_rep hP.cls hnc ρ ρ₁
    obtain ⟨m₂, hm₂, hm₂K⟩ := c.exists_conj_of_rep hP.cls hnc ρ σ₁
    rw [hρ, hρ₁] at hm₁K
    rw [hρ, hσ₁] at hm₂K
    have hg' : conjSub (m₁⁻¹ * g) K = K := by
      rw [conjSub_mul, ← hm₁K, conjSub_inv_conjSub]
    have hg'N : m₁⁻¹ * g ∈ Subgroup.normalizer (K : Set Y) :=
      mem_normalizer_iff_conjSub_eq.mpr hg'
    refine ⟨(m₁⁻¹ * g)⁻¹ * (m₁⁻¹ * m₂), H.mul_mem (H.inv_mem (hN hg'N))
      (H.mul_mem (H.inv_mem (hM hm₁)) (hM hm₂)), ?_⟩
    have e : (m₁⁻¹ * g)⁻¹ * (m₁⁻¹ * m₂) = g⁻¹ * m₂ := by group
    rw [e, conjSub_mul, hm₂K, conjSub_inv_conjSub]
  intro L hL
  have hL' : Relation.ReflTransGen (dstarAdj Ω) K L := hL
  clear hL
  induction hL' with
  | refl => exact ⟨1, H.one_mem, conjSub_one K⟩
  | @tail b c' _ hbc ih =>
    obtain ⟨x, hxH, hx⟩ := ih
    have hbΩ : b ∈ Ω := hx ▸ hΩ.conjInvariant x K hK
    have hc'Ω : c' ∈ Ω := hbc.1
    have hnbr : c' ∈ omegaStarNbr Ω b := by
      rcases hbc.2 with h1 | h1
      · exact h1
      · exact Q3T6.Mu.omegaStarNbr_symm hΩ hc'Ω hbΩ h1
    have h2 := omegaStarNbr_conj hΩ.conjInvariant hnbr x⁻¹
    rw [← hx, conjSub_inv_conjSub] at h2
    obtain ⟨y, hyH, hy⟩ := hA _ h2
    refine ⟨x * y, H.mul_mem hxH hyH, ?_⟩
    rw [conjSub_mul, hy, conjSub_conjSub_inv]

theorem not_rLayer_le_sigmaGen (hP : Q3CL.PartIHypG Ω) (d : Data Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K := by
  intro hD
  have hΩ : HypOmegaGen Ω := hP.hyp
  have hK : K ∈ Ω := d.frame.mem
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP d.hW
  have hnc : ¬ DbarConnected Ω W := Q3T6.Mu.thompsonGraphAll hP hK hne d.hW
  obtain ⟨ρ, ρ', hρ, -, -⟩ := exists_reps hP d
  have hMN : MGrp Ω W ≤ sigmaNorm Ω K :=
    (mGrp_le_rLayer_tz hP d hne).trans
      (hD.trans (T7A.sigmaGen_le_sigmaNorm hΩ.conjInvariant hK))
  obtain ⟨K₁, hK₁d, J₁, hJ₁, hJ₁n⟩ := Q3T6.Mu.exists_boundary_of_dComp_ne hΩ hK hne
  have hK₁Ω : K₁ ∈ Ω := mem_of_mem_dComp' hK hK₁d
  obtain ⟨g, ρ₁, σ₁, hρ₁, hσ₁⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hK₁Ω hJ₁
  obtain ⟨m₁, hm₁, hm₁K⟩ := c.exists_conj_of_rep hP.cls hnc ρ ρ₁
  obtain ⟨m₂, hm₂, hm₂K⟩ := c.exists_conj_of_rep hP.cls hnc ρ σ₁
  rw [hρ, hρ₁] at hm₁K
  rw [hρ, hσ₁] at hm₂K
  have h1 : conjSub g K₁ ∈ dComp Ω K := by
    rw [← hm₁K]
    exact (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).mp (hMN hm₁)
  have h2 : conjSub g J₁ ∈ dComp Ω K := by
    rw [← hm₂K]
    exact (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).mp (hMN hm₂)
  have hgN : g ∈ sigmaNorm Ω K :=
    T8.mem_sigmaNorm_of_mem_dComp hΩ.conjInvariant hK hK₁d h1
  exact hJ₁n ((hgN J₁).mpr h2)

theorem dComp_eq_dstarComp_of_rLayer_le (hP : Q3CL.PartIHypG Ω) (d : Data Ω K K' z u J t W)
    (hD : rLayer Ω (t * z) ≤ sigmaGen Ω K) : dComp Ω K = dstarComp Ω K := by
  by_contra hne
  exact not_rLayer_le_sigmaGen hP d hne hD

theorem involution_eq_of_mem_omegaNbr (hP : Q3CL.PartIHypG Ω) (d : Data Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hSigC : ∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set Y))
    {J₁ : Subgroup Y} {t₁ : Y} (hJ₁ : J₁ ∈ omegaNbr Ω K) (ht₁ : IsUniqueInvolution J₁ t₁)
    (hJ₁K' : J₁ ≠ K') (hJ₁J : J₁ ≠ J) : t₁ = t := by
  classical
  have hf := d.frame
  have hΩ : HypOmegaGen Ω := hP.hyp
  have hK : K ∈ Ω := hf.mem
  have hK'Ω : K' ∈ Ω := hf.hK'.1
  have hz : IsUniqueInvolution K z := hf.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hf.hK'
  have hJΩ : J ∈ Ω := hf.hJ.1
  have hJK : J ∈ omegaNbr Ω K := hf.hJ.2 K (mem_twinSet_self hK hz)
  have hJK' : J ∈ omegaNbr Ω K' := hf.hJ.2 K' hf.hK'
  have hK'K : K' ∈ omegaNbr Ω K := Q3CL.T3.twin_mem_omegaNbr hΩ hK hK'Ω hf.hne hz hzK'
  have hJ₁Ω : J₁ ∈ Ω := hJ₁.1

  have hdc : ∀ L ∈ omegaNbr Ω K, L ≤ Subgroup.centralizer ({t * z} : Set Y) := fun L hL =>
    hSigC L (Relation.ReflTransGen.single ⟨hL.1, Or.inl hL⟩)
  have hKc : K ≤ Subgroup.centralizer ({t * z} : Set Y) := hSigC K Relation.ReflTransGen.refl
  have hKt : K ≤ Subgroup.centralizer ({t} : Set Y) :=
    le_centralizer_of_le_centralizer_mul hKc fun x hx =>
      commute_involution_of_conjSub_eq hz (conjSub_eq_self_of_mem hx)
  have hK't : K' ≤ Subgroup.centralizer ({t} : Set Y) :=
    le_centralizer_of_le_centralizer_mul (hdc K' hK'K) fun x hx =>
      commute_involution_of_conjSub_eq hzK' (conjSub_eq_self_of_mem hx)
  have hdJ₁ := hdc J₁ hJ₁
  have hJ₁K : J₁ ∈ omegaNbr Ω K := hJ₁

  obtain ⟨-, -, R₁, hR₁, hR₁J₁, hR₁N⟩ := hJ₁
  have hR₁S : IsSylow2In R₁ J₁ := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJ₁Ω hR₁ hR₁J₁
  have hR₁2 : IsPGroup 2 R₁ := hR₁S.2.1
  have h8₁ : 8 ≤ Nat.card R₁ := Sec6Gen.eight_le_of_mem_RSet hΩ hR₁
  have hR₁z : R₁ ≤ Subgroup.centralizer ({z} : Set Y) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_involution_of_conjSub_eq hz (mem_normalizer_iff_conjSub_eq.mp (hR₁N hx))
  have hR₁t : R₁ ≤ Subgroup.centralizer ({t} : Set Y) :=
    le_centralizer_of_le_centralizer_mul (hR₁J₁.trans hdJ₁) fun x hx =>
      commute_involution_of_conjSub_eq hz (mem_normalizer_iff_conjSub_eq.mp (hR₁N hx))

  have hR₁K' : R₁ ≤ Subgroup.normalizer (K' : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK'Ω hJ₁Ω (fun e => hJ₁K' e.symm) hzK' hR₁J₁ hR₁2
      (by omega) hR₁z
  have hR₁J : R₁ ≤ Subgroup.normalizer (J : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hJ₁Ω (fun e => hJ₁J e.symm) hf.ht hR₁J₁ hR₁2
      (by omega) hR₁t

  obtain ⟨R_K, hRKS, hP₁⟩ := exists_isPGroup_sup_sylow hR₁2 hR₁N
  have hKN : K ≤ Subgroup.normalizer (K' : Set Y) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK'Ω hf.hne.symm hz hzK'
  have hP₁N : R₁ ⊔ R_K ≤ Subgroup.normalizer (K' : Set Y) := sup_le hR₁K' (hRKS.1.trans hKN)
  obtain ⟨R_K', hRK'S, hP₂⟩ := exists_isPGroup_sup_sylow hP₁ hP₁N
  have hRKset : R_K ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRKS
  have hRK'set : R_K' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hRK'S
  have h8K : 8 ≤ Nat.card R_K := Sec6Gen.eight_le_of_mem_RSet hΩ hRKset
  have h8K' : 8 ≤ Nat.card R_K' := Sec6Gen.eight_le_of_mem_RSet hΩ hRK'set
  have hRKJ : R_K ≤ Subgroup.normalizer (J : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hK hJK.2.1 hf.ht hRKS.1 hRKS.2.1 (by omega)
      (hRKS.1.trans hKt)
  have hRK'J : R_K' ≤ Subgroup.normalizer (J : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hK'Ω hJK'.2.1 hf.ht hRK'S.1 hRK'S.2.1
      (by omega) (hRK'S.1.trans hK't)
  have hP₂N : R₁ ⊔ R_K ⊔ R_K' ≤ Subgroup.normalizer (J : Set Y) :=
    sup_le (sup_le hR₁J hRKJ) hRK'J
  obtain ⟨R_J, hRJS, hP₃⟩ := exists_isPGroup_sup_sylow hP₂ hP₂N
  have hRJset : R_J ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hRJS

  obtain ⟨W₁, hW₁, hD⟩ := Q3T8.Asc77.exists_W_of_isPGroup hΩ hP₃
  have hR₁D : R₁ ∈ DSet Ω W₁ :=
    hD R₁ hR₁ (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hRKD : R_K ∈ DSet Ω W₁ :=
    hD R_K hRKset (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hRK'D : R_K' ∈ DSet Ω W₁ := hD R_K' hRK'set (le_sup_right.trans le_sup_left)
  have hRJD : R_J ∈ DSet Ω W₁ := hD R_J hRJset le_sup_right
  obtain ⟨ρK, hρK, -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW₁ hK hRKS hRKD
  obtain ⟨ρK', hρK', -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW₁ hK'Ω hRK'S
      hRK'D
  obtain ⟨ρJ, hρJ, -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW₁ hJΩ hRJS hRJD
  obtain ⟨ρJ₁, hρJ₁, -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW₁ hJ₁Ω hR₁S
      hR₁D
  have c₁ : Q3CL.Thompson.Ctx Ω W₁ := Q3CL.T8.ctxOf hP hW₁
  have hnc₁ : ¬ DbarConnected Ω W₁ :=
    Q3T6.Mu.thompsonGraphAll hP hf.mem hne hW₁
  have h4 := c₁.mul_four_eq_one hP.cls hnc₁ ρK ρK' ρJ ρJ₁ (by rw [hρK, hρK']; exact hK'K)
    (by rw [hρK, hρJ]; exact hJK) (by rw [hρK', hρJ]; exact hJK') (by rw [hρK, hρJ₁]; exact hJ₁K)
    (by rw [hρK', hρJ₁]; exact hJ₁K') (by rw [hρJ, hρJ₁]; exact hJ₁J)
    (by rw [hρK]; exact hz) (by rw [hρK']; exact hzK') (by rw [hρJ]; exact hf.ht)
    (by rw [hρJ₁]; exact ht₁)
  rw [hz.sq, one_mul] at h4
  have h5 : t₁ = t⁻¹ := eq_inv_of_mul_eq_one_right h4
  rw [h5]
  exact inv_eq_of_mul_eq_one_left hf.ht.sq


theorem normalizer_le_centralizer_tz (hP : Q3CL.PartIHypG Ω) (d : Data Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hSigC : ∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set Y)) :
    Subgroup.normalizer (K : Set Y) ≤ Subgroup.centralizer ({t * z} : Set Y) := by
  have hf := d.frame
  have hΩ : HypOmegaGen Ω := hP.hyp
  have hK : K ∈ Ω := hf.mem
  have hz : IsUniqueInvolution K z := hf.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hf.hK'
  have htz : t ≠ z := by
    intro htz
    have hJV : J ∈ twinSet Ω K := ⟨hf.hJ.1, z, hz, htz ▸ hf.ht⟩
    exact (hf.hJ.2 J hJV).2.1 rfl
  intro n hn
  have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hn
  have hnz : n * z = z * n := commute_involution_of_conjSub_eq hz hnK
  have hJ₁ : conjSub n J ∈ omegaNbr Ω K := by
    have := omegaNbr_conj hΩ.conjInvariant (hf.hJ.2 K (mem_twinSet_self hK hz)) n
    rwa [hnK] at this
  have ht₁ : IsUniqueInvolution (conjSub n J) (n * t * n⁻¹) := hf.ht.conj n
  have htt : n * t * n⁻¹ = t := by
    by_cases hJK' : conjSub n J = K'
    · exfalso
      have e1 : n * t * n⁻¹ = z := ht₁.eq (by rw [hJK']; exact hzK')
      apply htz
      have e2 : n * t = z * n := (mul_inv_eq_iff_eq_mul.mp e1).trans rfl
      calc t = n⁻¹ * (n * t) := by group
        _ = n⁻¹ * (z * n) := by rw [e2]
        _ = n⁻¹ * (n * z) := by rw [hnz]
        _ = z := by group
    · by_cases hJJ : conjSub n J = J
      · exact (hf.ht.eq (by rw [← hJJ]; exact ht₁)).symm
      · exact involution_eq_of_mem_omegaNbr hP d hne hSigC hJ₁ ht₁ hJK' hJJ
  have hnt : n * t = t * n := mul_inv_eq_iff_eq_mul.mp htt
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * (t * z) = (n * t) * z := by rw [mul_assoc]
    _ = (t * n) * z := by rw [hnt]
    _ = t * (n * z) := by rw [mul_assoc]
    _ = t * (z * n) := by rw [hnz]
    _ = (t * z) * n := by rw [mul_assoc]

end Frame

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
