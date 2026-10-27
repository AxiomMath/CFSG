module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryPPD

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model

section Lambda

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

omit [Fact p.Prime] in
theorem exists_ne_one_scalar (hq : 2 < p ^ f) :
    ∃ k : Kˣ, (k : K) * (J.conj (k : K))⁻¹ ^ 2 ≠ 1 := by
  have hconj := huppert_II_10_4_conj_eq_frobenius J (p ^ f) hK hfix
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,
      CFSG.ClassicalGroups.Unitary.card_units_of_card hK]
  have h1 := hcon g
  rw [hconj] at h1
  have hg0 : (g : K) ≠ 0 := g.ne_zero
  have h2 : (g : K) ^ (2 * p ^ f) = g := by
    have : ((g : K) ^ p ^ f) ≠ 0 := pow_ne_zero _ hg0
    rw [pow_mul']
    field_simp at h1
    linear_combination -h1
  have h3 : g ^ (2 * p ^ f - 1) = 1 := by
    have hq1 : 1 ≤ 2 * p ^ f := by omega
    have h4 : g ^ (2 * p ^ f) = g := Units.ext (by simpa using h2)
    have h5 : g ^ (2 * p ^ f - 1) * g = 1 * g := by
      rw [← pow_succ, Nat.sub_add_cancel hq1, h4, one_mul]
    exact mul_right_cancel h5
  have h6 := orderOf_dvd_of_pow_eq_one h3
  rw [hord] at h6
  have h7 := Nat.le_of_dvd (by omega) h6
  generalize p ^ f = q at hq h7
  have h8 : 2 * q - 1 < q ^ 2 - 1 := by
    have h9 : 3 * q ≤ q * q := Nat.mul_le_mul_right q hq
    have h10 : 1 ≤ q := by omega
    have h11 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h10
    rw [sq] at h11 ⊢
    omega
  omega

end Lambda

section Regular

variable {K : Type} [Field K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

theorem exists_mem_rootGroup_smul_pzero_eq (y : IsoPoint J) (hy : y ≠ pinf J hJ) :
    ∃ r ∈ rootGroup J hJ, r • pzero J hJ = y := by
  obtain ⟨z, hz⟩ := exists_root_smul_pzero_eq J hJ y hy
  exact ⟨root J hJ z, root_mem_rootGroup J hJ z, hz⟩

theorem eq_of_smul_pzero_eq {r₁ r₂ : ProjectiveSpecialUnitaryMatrixGroup J}
    (h₁ : r₁ ∈ rootGroup J hJ) (h₂ : r₂ ∈ rootGroup J hJ)
    (h : r₁ • pzero J hJ = r₂ • pzero J hJ) : r₁ = r₂ := by
  obtain ⟨z₂, rfl⟩ := (mem_rootGroup J hJ).1 h₂
  have hne : (root J hJ z₂) • pzero J hJ ≠ pinf J hJ := root_smul_pzero_ne_pinf J hJ z₂
  have hne0 : pzero J hJ ≠ pinf J hJ := (pinf_ne_pzero J hJ).symm
  obtain ⟨r, -, hr⟩ := rootGroup_regular J hJ (pzero J hJ) (root J hJ z₂ • pzero J hJ) hne0 hne
  have e1 := hr ⟨r₁, h₁⟩ h
  have e2 := hr ⟨root J hJ z₂, h₂⟩ rfl
  exact congrArg Subtype.val (e1.trans e2.symm)

end Regular

section Centralizer

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem mem_rootGroup_of_forall_comm (hq : 2 < p ^ f) {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : ∀ r ∈ rootGroup J hJ, r * g = g * r) : g ∈ rootGroup J hJ := by
  have hσ := isUnitaryInvolution_conj J hK hfix
  have hgN : g ∈ Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hg)
  rw [normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq] at hgN
  have hgB : g • pinf J hJ = pinf J hJ := hgN
  have hgi : g⁻¹ • pinf J hJ = pinf J hJ := inv_smul_eq_iff.2 hgB.symm
  have hg0 : g • pzero J hJ ≠ pinf J hJ := by
    intro h
    apply pinf_ne_pzero J hJ
    rw [← inv_smul_smul g (pzero J hJ), h, hgi]
  obtain ⟨r, hrR, hr⟩ := exists_mem_rootGroup_smul_pzero_eq J hJ _ hg0
  obtain ⟨z₀, rfl⟩ := (mem_rootGroup J hJ).1 hrR
  set t := (root J hJ z₀)⁻¹ * g with ht
  have ht_inf : t • pinf J hJ = pinf J hJ := by
    rw [ht, mul_smul, hgB, ← map_inv, root_smul_pinf]
  have ht_zero : t • pzero J hJ = pzero J hJ := by
    rw [ht, mul_smul, ← hr, ← mul_smul, inv_mul_cancel, one_smul]
  have htT : t ∈ torusGroup J hJ := by
    rw [← stabilizer_pinf_inf_stabilizer_pzero J hJ (p ^ f) hK hfix]
    exact ⟨ht_inf, ht_zero⟩
  obtain ⟨k, hk⟩ := (mem_torusGroup J hJ).1 htT
  have hconj : ∀ z : Coord J, hermitianTorusAction J k z = z₀⁻¹ * z * z₀ := by
    intro z
    apply root_injective J hJ
    rw [← torus_mul_root_mul_inv, hk, ht, map_mul, map_mul, map_inv]
    have hcomm := hg (root J hJ z) (root_mem_rootGroup J hJ z)
    calc (root J hJ z₀)⁻¹ * g * root J hJ z * ((root J hJ z₀)⁻¹ * g)⁻¹
        = (root J hJ z₀)⁻¹ * (g * root J hJ z * g⁻¹) * root J hJ z₀ := by group
      _ = (root J hJ z₀)⁻¹ * root J hJ z * root J hJ z₀ := by
        rw [← hcomm]; group
  obtain ⟨z₁, hz₁⟩ := exists_coord_fst J hσ 1
  have hlam : (k : K) * (J.conj (k : K))⁻¹ ^ 2 = 1 := by
    have h1 := congrArg (fun y : Coord J => (y : K × K).1) (hconj z₁)
    simp only [torusAction_val, coord_mul_val, coord_inv_val, hz₁] at h1
    linear_combination h1
  obtain ⟨b₀, hb₀, hb₀t⟩ := hσ.exists_traceZero
  have hnorm : (J.conj (k : K))⁻¹ * (k : K)⁻¹ = 1 := by
    have h1 := congrArg (fun y : Coord J => (y : K × K).2) (hconj (skewCoord J b₀ hb₀t))
    have h2 : z₀⁻¹ * skewCoord J b₀ hb₀t * z₀ = skewCoord J b₀ hb₀t := by
      rw [mul_assoc, skewCoord_central, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h2] at h1
    simp only [torusAction_val, skewCoord] at h1
    have h3 : b₀ * ((J.conj (k : K))⁻¹ * (k : K)⁻¹) = b₀ * 1 := by
      rw [mul_one, ← mul_assoc]; exact h1
    exact mul_left_cancel₀ hb₀ h3
  have hact : ∀ z : Coord J, hermitianTorusAction J k z = z := by
    intro z
    apply coord_ext
    · rw [torusAction_val]
      dsimp only
      rw [mul_assoc, hlam, mul_one]
    · rw [torusAction_val]
      dsimp only
      rw [mul_assoc, hnorm, mul_one]
  have hfix_all : ∀ x : IsoPoint J, torus J hJ k • x = x := by
    intro x
    by_cases hx : x = pinf J hJ
    · rw [hx]; exact torus_smul_pinf J hJ k
    · obtain ⟨z, rfl⟩ := exists_root_smul_pzero_eq J hJ x hx
      rw [torus_smul_root_smul_pzero, hact]
  have ht1 : torus J hJ k = 1 := by
    have := faithfulSMul_isoPoint J hJ (p ^ f) hK hfix
    exact eq_of_smul_eq_smul (fun x => by rw [hfix_all x, one_smul])
  have ht1' : (root J hJ z₀)⁻¹ * g = 1 := by rw [← ht, ← hk, ht1]
  rw [(inv_mul_eq_one.1 ht1').symm]
  exact root_mem_rootGroup J hJ z₀

theorem eq_conj_of_fixes_rootGroup (hq : 2 < p ^ f)
    (α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hα : ∀ r ∈ rootGroup J hJ, α r = r) :
    ∃ r ∈ rootGroup J hJ, α = MulAut.conj r := by
  have hBN := normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq
  have hmapR : (rootGroup J hJ).map α.toMonoidHom = rootGroup J hJ := by
    ext y
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro h
      have := hα _ h
      rw [MulEquiv.apply_symm_apply] at this
      rw [this]
      exact h
    · intro h
      rwa [α.symm_apply_eq.2 (hα y h).symm]
  have hN : (Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))).map
      α.toMonoidHom = Subgroup.normalizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [Subgroup.map_equiv_normalizer_eq, hmapR]
  have hαB : ∀ g, α g • pinf J hJ = pinf J hJ ↔ g • pinf J hJ = pinf J hJ := by
    intro g
    have := mem_map_iff α (Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) g
    rw [hN, hBN] at this
    exact this
  have hw : α (weyl J hJ) • pinf J hJ ≠ pinf J hJ := fun h =>
    weyl_not_mem_stabilizer J hJ ((hαB _).1 h)
  obtain ⟨u₀, hu₀R, hu₀⟩ := exists_mem_rootGroup_smul_pzero_eq J hJ _ hw
  have hu₀inf : u₀ • pinf J hJ = pinf J hJ := rootGroup_le_stabilizer J hJ hu₀R
  have hu₀Z : u₀ ∈ rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    obtain ⟨k₀, hk₀⟩ := exists_ne_one_scalar J hK hfix hq
    set t := torus J hJ k₀ with ht
    have htN : t ∈ Subgroup.normalizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
      torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ k₀)
    have htz : t • pzero J hJ = pzero J hJ := torus_smul_pzero J hJ k₀
    have hti : t • pinf J hJ = pinf J hJ := torus_smul_pinf J hJ k₀
    have hgt : ∀ r ∈ rootGroup J hJ, r * (t⁻¹ * α t) = (t⁻¹ * α t) * r := by
      intro r hr
      have h1 : α t * r * (α t)⁻¹ = t * r * t⁻¹ := by
        have h2 : α (t * r * t⁻¹) = t * r * t⁻¹ :=
          hα _ ((Subgroup.mem_normalizer_iff.1 htN r).1 hr)
        rw [map_mul, map_mul, map_inv, hα r hr] at h2
        exact h2
      calc r * (t⁻¹ * α t) = t⁻¹ * (t * r * t⁻¹) * α t := by group
        _ = t⁻¹ * (α t * r * (α t)⁻¹) * α t := by rw [h1]
        _ = (t⁻¹ * α t) * r := by group
    have hgtR : t⁻¹ * α t ∈ rootGroup J hJ :=
      mem_rootGroup_of_forall_comm J hJ hK hfix hq hgt
    obtain ⟨zg, hzg⟩ := (mem_rootGroup J hJ).1 hgtR
    have hzg0 : zg.1.1 = 0 := by
      refine (root_mem_center_iff J hJ hK hfix zg).1 ?_
      rw [hzg]
      exact Subgroup.mem_inf.2 ⟨hgtR, Subgroup.mem_centralizer_iff.2 hgt⟩
    have hs : ((weyl J hJ)⁻¹ * t * weyl J hJ) • pinf J hJ = pinf J hJ := by
      rw [mul_smul, mul_smul, weyl_smul_pinf, htz, weyl_inv, weyl_smul_pzero]
    have hαt : α t • (α (weyl J hJ) • pinf J hJ) = α (weyl J hJ) • pinf J hJ := by
      rw [← mul_smul, ← map_mul]
      have h3 : t * weyl J hJ = weyl J hJ * ((weyl J hJ)⁻¹ * t * weyl J hJ) := by group
      rw [h3, map_mul, mul_smul, (hαB _).2 hs]
    obtain ⟨zu, rfl⟩ := (mem_rootGroup J hJ).1 hu₀R
    have h4 : (t * (root J hJ zg * root J hJ zu) * t⁻¹) • pzero J hJ =
        root J hJ zu • pzero J hJ := by
      have h5 : α t = t * root J hJ zg := by rw [hzg]; group
      rw [← hu₀, h5, ← mul_smul] at hαt
      calc (t * (root J hJ zg * root J hJ zu) * t⁻¹) • pzero J hJ
          = (t * root J hJ zg * root J hJ zu) • (t⁻¹ • pzero J hJ) := by rw [← mul_smul]; group
        _ = (t * root J hJ zg * root J hJ zu) • pzero J hJ := by
          rw [inv_smul_eq_iff.2 htz.symm]
        _ = root J hJ zu • pzero J hJ := hαt
    have hr' : root J hJ zg * root J hJ zu ∈ rootGroup J hJ :=
      Subgroup.mul_mem _ (root_mem_rootGroup J hJ zg) (root_mem_rootGroup J hJ zu)
    have h6 := eq_of_smul_pzero_eq J hJ ((Subgroup.mem_normalizer_iff.1 htN _).1 hr')
      (root_mem_rootGroup J hJ zu) h4
    rw [← map_mul, ht, torus_mul_root_mul_inv, (root_injective J hJ).eq_iff] at h6
    have h7 := congrArg (fun y : Coord J => (y : K × K).1) h6
    simp only [torusAction_val, coord_mul_val, hzg0, zero_add] at h7
    have h8 : zu.1.1 * ((k₀ : K) * (J.conj (k₀ : K))⁻¹ ^ 2 - 1) = 0 := by linear_combination h7
    have h9 : zu.1.1 = 0 :=
      (mul_eq_zero.mp h8).resolve_right (sub_ne_zero.mpr hk₀)
    exact (root_mem_center_iff J hJ hK hfix zu).2 h9
  have hu₀c : ∀ r ∈ rootGroup J hJ, r * u₀ = u₀ * r := fun r hr =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hu₀Z).2 r hr
  let β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) := α.trans (MulAut.conj u₀⁻¹)
  have hβ : ∀ g, β g = u₀⁻¹ * α g * u₀ := fun g => by
    simp [β]
  have hβR : ∀ r ∈ rootGroup J hJ, β r = r := by
    intro r hr
    rw [hβ, hα r hr, mul_assoc, hu₀c r hr, inv_mul_cancel_left]
  have hβB : ∀ g, g • pinf J hJ = pinf J hJ → β g • pinf J hJ = pinf J hJ := by
    intro g hg
    rw [hβ, mul_smul, mul_smul, hu₀inf, (hαB g).2 hg, inv_smul_eq_iff.2 hu₀inf.symm]
  have hβw : β (weyl J hJ) • pinf J hJ = pzero J hJ := by
    rw [hβ, mul_smul, mul_smul, hu₀inf, ← hu₀, inv_smul_smul]
  have key : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J, β x • pinf J hJ = x • pinf J hJ := by
    intro x
    by_cases hx : x • pinf J hJ = pinf J hJ
    · rw [hx]
      exact hβB x hx
    · obtain ⟨z, hz⟩ := exists_root_smul_pzero_eq J hJ (x • pinf J hJ) hx
      have hh : (root J hJ z * weyl J hJ) • pinf J hJ = x • pinf J hJ := by
        rw [mul_smul, weyl_smul_pinf, hz]
      have hβh : β (root J hJ z * weyl J hJ) • pinf J hJ = x • pinf J hJ := by
        rw [map_mul, mul_smul, hβw, hβR _ (root_mem_rootGroup J hJ z), hz]
      have hb : ((root J hJ z * weyl J hJ)⁻¹ * x) • pinf J hJ = pinf J hJ := by
        rw [mul_smul, ← hh, inv_smul_smul]
      calc β x • pinf J hJ
          = β ((root J hJ z * weyl J hJ) * ((root J hJ z * weyl J hJ)⁻¹ * x)) • pinf J hJ := by
            rw [mul_inv_cancel_left]
        _ = β (root J hJ z * weyl J hJ) • (β ((root J hJ z * weyl J hJ)⁻¹ * x) • pinf J hJ) := by
            rw [map_mul, mul_smul]
        _ = β (root J hJ z * weyl J hJ) • pinf J hJ := by rw [hβB _ hb]
        _ = x • pinf J hJ := hβh
  have hall : ∀ (g : ProjectiveSpecialUnitaryMatrixGroup J) (y : IsoPoint J),
      β g • y = g • y := by
    intro g y
    obtain ⟨h, rfl⟩ : ∃ h : ProjectiveSpecialUnitaryMatrixGroup J, h • pinf J hJ = y := by
      by_cases hy : y = pinf J hJ
      · exact ⟨1, by rw [one_smul, hy]⟩
      · obtain ⟨z, hz⟩ := exists_root_smul_pzero_eq J hJ y hy
        exact ⟨root J hJ z * weyl J hJ, by rw [mul_smul, weyl_smul_pinf, hz]⟩
    calc β g • h • pinf J hJ = β g • β h • pinf J hJ := by rw [key h]
      _ = β (g * h) • pinf J hJ := by rw [map_mul, mul_smul]
      _ = (g * h) • pinf J hJ := key _
      _ = g • h • pinf J hJ := by rw [mul_smul]
  have hβid : ∀ g, β g = g := fun g => by
    have := faithfulSMul_isoPoint J hJ (p ^ f) hK hfix
    exact eq_of_smul_eq_smul (hall g)
  refine ⟨u₀, hu₀R, MulEquiv.ext fun g => ?_⟩
  have h1 := hβid g
  rw [hβ] at h1
  rw [MulAut.conj_apply]
  calc α g = u₀ * (u₀⁻¹ * α g * u₀) * u₀⁻¹ := by group
    _ = u₀ * g * u₀⁻¹ := by rw [h1]

end Centralizer

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding

open CFSG.UnitaryThreeRecognition.Model (rootGroup)

theorem kFactUnitaryUnipotentCentralizer : KFactUnitaryUnipotentCentralizer := by
  intro L _ _ p _ d hd h U α hα
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  let αP : MulAut _ := (e'.symm.trans α).trans e'
  have hαP : ∀ r ∈ rootGroup J hJ, αP r = r := by
    intro r hr
    have hr' : e'.symm r ∈ (U : Subgroup L) := by
      have : r ∈ (U : Subgroup L).map e'.toMonoidHom := hU ▸ hr
      exact Subgroup.mem_map_equiv.1 this
    show e' (α (e'.symm r)) = r
    rw [hα _ hr', MulEquiv.apply_symm_apply]
  obtain ⟨r₀, hr₀, hconj⟩ := UnitaryModel.eq_conj_of_fixes_rootGroup J hJ hK hfix hq αP hαP
  refine ⟨e'.symm r₀, ?_, ?_⟩
  · have : r₀ ∈ (U : Subgroup L).map e'.toMonoidHom := hU ▸ hr₀
    exact Subgroup.mem_map_equiv.1 this
  · ext x
    have h1 := congrArg (fun φ : MulAut _ => φ (e' x)) hconj
    simp only [αP, MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    apply e'.injective
    rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end CFSG.AGLEmbedding
