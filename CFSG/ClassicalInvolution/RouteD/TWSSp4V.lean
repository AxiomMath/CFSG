module

public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSp4

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSp4

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Steinberg.Sp TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem sl2_mul_self_eq_neg_one {A : SL(2, F)} (h : (A : Matrix (Fin 2) (Fin 2) F) * A = -1) :
    A * A = (-1 : SL(2, F)) :=
  Subtype.ext (by simpa using h)

theorem commute_longBlock_rev (k : Fin 2) (A B : SL(2, F)) :
    Commute (longBlock F 2 k A) (longBlock F 2 (Fin.rev k) B) := by
  fin_cases k
  · exact commute_longBlock_01 A B
  · exact (commute_longBlock_01 B A).symm

theorem mat_sq_conj_ut (k : Fin 2) {A A' : SL(2, F)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1) (g : StatedSp 2 F) :
    mat 2 F ((g * (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A') * g⁻¹) *
      (g * (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A') * g⁻¹)) = -1 := by
  have hc := commute_longBlock_rev k A A'
  have e1 : (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A') *
      (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A') =
      longInv F 2 k * longInv F 2 (Fin.rev k) := by
    calc (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A') *
          (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A')
        = longBlock F 2 k A * (longBlock F 2 (Fin.rev k) A' * longBlock F 2 k A) *
            longBlock F 2 (Fin.rev k) A' := by group
      _ = longBlock F 2 k A * (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A') *
            longBlock F 2 (Fin.rev k) A' := by rw [hc.symm.eq]
      _ = (longBlock F 2 k A * longBlock F 2 k A) *
            (longBlock F 2 (Fin.rev k) A' * longBlock F 2 (Fin.rev k) A') := by group
      _ = longInv F 2 k * longInv F 2 (Fin.rev k) := by
        rw [← map_mul, ← map_mul, sl2_mul_self_eq_neg_one hA, sl2_mul_self_eq_neg_one hA',
          longInv, longInv]
  have e2 : mat 2 F (longInv F 2 k * longInv F 2 (Fin.rev k)) = -1 := by
    have hDD : mat 2 F (longInv F 2 k) * mat 2 F (longInv F 2 k) = 1 := by
      rw [← map_mul, longInv, ← map_mul]
      have : (-1 : SL(2, F)) * -1 = 1 := Subtype.ext (by simp)
      rw [this, map_one, map_one]
    rw [map_mul, CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4.mat_longInv_rev, mul_neg,
      hDD]
  have e3 : (g * (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A') * g⁻¹) *
      (g * (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A') * g⁻¹) =
      g * (longInv F 2 k * longInv F 2 (Fin.rev k)) * g⁻¹ := by
    rw [← e1]
    group
  rw [e3, map_mul, map_mul, e2]
  have : mat 2 F g * (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * mat 2 F g⁻¹ =
      -(mat 2 F g * mat 2 F g⁻¹) := by
    simp
  rw [this, ← map_mul, mul_inv_cancel, map_one]


theorem sp4_not_centralizes [Finite F] (h2 : (2 : F) ≠ 0)
    {R R' : Subgroup (StatedSp 2 F)} (hR : ∃ i, IsLongRootSp2 R i)
    (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R') {x x' : StatedSp 2 F} (hxR : x ∈ R)
    (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (StatedSp 2 F)) {a a' : StatedSp 2 F} (ha : a ∈ R)
    (ha' : a' ∈ R') (hsq : a * a * x⁻¹ ∈ Subgroup.center (StatedSp 2 F))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (StatedSp 2 F))
    {S : Subgroup (StatedSp 2 F)} (hS : ∃ i, IsLongRootSp2 S i)
    (hc : ∀ s ∈ S, (a * a') * s = s * (a * a')) : False := by
  have hx2 : x * x = 1 := sp4_mul_self_eq_one_of_center hR hxR hxc
  have hx'2 : x' * x' = 1 := sp4_mul_self_eq_one_of_center hR' hx'R' hx'c
  have hc0 : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
    have := (Subgroup.center (StatedSp 2 F)).inv_mem hsame
    simpa using this
  obtain ⟨g, k, hRg, hR'g⟩ := CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4.twin_std_sp h2
    hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc0
  have hxg : x = g * longInv F 2 k * g⁻¹ := by
    have hi : IsLongRootSp2 R (g * longInv F 2 k * g⁻¹) := by
      rw [hRg]
      exact (isLongRootSp2_standard k).conj g
    exact hi.eq_of_orderOf_eq_two h2 hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  rw [hRg] at ha
  rw [hR'g] at ha'
  obtain ⟨a₀, ⟨A, hA⟩, hae⟩ := ha
  obtain ⟨a₀', ⟨A', hA'⟩, hae'⟩ := ha'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hae hae'
  have hsq'' : a' * a' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
    have := (Subgroup.center (StatedSp 2 F)).mul_mem hsq' hc0
    simpa [mul_assoc] using this
  have hA₁ : longBlock F 2 k A * longBlock F 2 k A * (longInv F 2 k)⁻¹ ∈
      Subgroup.center (StatedSp 2 F) := by
    refine CFSG.ClassicalInvolution.RouteD.SCRSL4.mem_center_of_conj (g := g) ?_
    have e : g * (longBlock F 2 k A * longBlock F 2 k A * (longInv F 2 k)⁻¹) * g⁻¹ =
        a * a * x⁻¹ := by
      rw [← hae, hA, hxg]
      group
    rw [e]
    exact hsq
  have hA₂ : longBlock F 2 (Fin.rev k) A' * longBlock F 2 (Fin.rev k) A' * (longInv F 2 k)⁻¹ ∈
      Subgroup.center (StatedSp 2 F) := by
    refine CFSG.ClassicalInvolution.RouteD.SCRSL4.mem_center_of_conj (g := g) ?_
    have e : g * (longBlock F 2 (Fin.rev k) A' * longBlock F 2 (Fin.rev k) A' *
        (longInv F 2 k)⁻¹) * g⁻¹ = a' * a' * x⁻¹ := by
      rw [← hae', hA', hxg]
      group
    rw [e]
    exact hsq''
  have hAA := sq_neg_one_of_center_same k hA₁
  have hAA' := sq_neg_one_of_center_other k hA₂
  have e2 : a * a' = g * (longBlock F 2 k A * longBlock F 2 (Fin.rev k) A') * g⁻¹ := by
    rw [← hae, ← hae', hA, hA']
    group
  have hsqu : mat 2 F ((a * a') * (a * a')) = -1 := by
    rw [e2]
    exact mat_sq_conj_ut k hAA hAA' g
  obtain ⟨iS, hiS⟩ := hS
  have hiSmem : iS ∈ S := (hiS.isClassicalSL2 h2).mem
  have hũC : (a * a') ∈ Subgroup.centralizer ({iS} : Set (StatedSp 2 F)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hc iS hiSmem)
  obtain ⟨a₁, ha₁, b, hb, hũb⟩ := hiS.exists_mul_of_mem_centralizer h2 hũC
  have hbS : ∀ s ∈ S, s * b = b * s := fun s hs =>
    (hiS.commute_of_mem_complGroup h2 hs hb).eq
  have ha₁c : ∀ s ∈ S, a₁ * s = s * a₁ := by
    intro s hs
    have hsb : s * b⁻¹ = b⁻¹ * s := ((hiS.commute_of_mem_complGroup h2 hs hb).inv_right).eq
    have ha₁e : a₁ = (a * a') * b⁻¹ := eq_mul_inv_of_mul_eq hũb.symm
    rw [ha₁e]
    calc a * a' * b⁻¹ * s = a * a' * (b⁻¹ * s) := by group
      _ = a * a' * (s * b⁻¹) := by rw [hsb]
      _ = (a * a' * s) * b⁻¹ := by group
      _ = (s * (a * a')) * b⁻¹ := by rw [hc s hs]
      _ = s * (a * a' * b⁻¹) := by group
  have ha₁sq : a₁ * a₁ = 1 := sp4_mul_self_eq_one_of_center ⟨iS, hiS⟩ ha₁ ha₁c
  have hab : a₁ * b = b * a₁ := (hiS.commute_of_mem_complGroup h2 ha₁ hb).eq
  have hbb : (a * a') * (a * a') = b * b := by
    rw [hũb]
    calc a₁ * b * (a₁ * b) = a₁ * (b * a₁) * b := by group
      _ = a₁ * (a₁ * b) * b := by rw [← hab]
      _ = (a₁ * a₁) * (b * b) := by group
      _ = b * b := by rw [ha₁sq, one_mul]
  have hmem : b * b ∈ complGroup iS := (complGroup iS).mul_mem hb hb
  have hmat : mat 2 F (b * b) = -1 := by rw [← hbb]; exact hsqu
  obtain ⟨j, g', -, hig'⟩ := hiS
  let e : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl j) (1 : F)
  have hw : mat 2 F g' *ᵥ e ∈ minusSpace iS := by
    rw [hig', mem_minusSpace_conj, mulVec_inv_mulVec, mem_minusSpace_longInv h2]
    intro t ht
    simp only [e, Pi.single_apply]
    split_ifs with h
    · subst h
      exact (ht (inl_mem_coords j)).elim
    · rfl
  have h1 := (mem_complGroup.mp hmem) _ hw
  rw [hmat, Matrix.neg_mulVec, Matrix.one_mulVec] at h1
  have hw0 : mat 2 F g' *ᵥ e = 0 := by
    funext t
    have h3 := congrFun h1 t
    simp only [Pi.neg_apply] at h3
    have h5 : (2 : F) * (mat 2 F g' *ᵥ e) t = 0 := by linear_combination -h3
    simpa using (mul_eq_zero.1 h5).resolve_left h2
  have he0 : e = 0 := by
    rw [← mulVec_inv_mulVec g' e, hw0, Matrix.mulVec_zero]
  have h6 := congrFun he0 (Sum.inl j)
  simp [e] at h6

end CFSG.ClassicalInvolution.RouteD.SCRSp4

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal

variable {p : ℕ} [Fact p.Prime]

theorem twinMFNotCentralizing_psp2 (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    {R R' : Subgroup (modelUniv .PSp 2 p e Fact.out).K}
    {x x' : (modelUniv .PSp 2 p e Fact.out).K}
    (hd : TwinDatumOn .PSp (modelUniv .PSp 2 p e Fact.out) R R' x x')
    {a a' : (modelUniv .PSp 2 p e Fact.out).K} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .PSp 2 p e Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .PSp 2 p e Fact.out).K)
    {S : Subgroup (modelUniv .PSp 2 p e Fact.out).K}
    (hS : S ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 p e Fact.out).D)
    (hc : ∀ s ∈ S, (a * a') * s = s * (a * a')) : False := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .PSp 2 p e :=
    ⟨Fact.out, he, le_refl 2, fun h => by
      have : p ^ e = 2 := congrArg Prod.snd h
      omega⟩
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hR := (exists_isLongRootSp2_iff h2 R).mpr
    ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hd.mem)
  have hR' := (exists_isLongRootSp2_iff h2 R').mpr
    ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hd.mem')
  have hS' := (exists_isLongRootSp2_iff h2 S).mpr
    ((mem_fundamentalSubgroups_PSp_iff hadm S).mp hS)
  exact CFSG.ClassicalInvolution.RouteD.SCRSp4.sp4_not_centralizes h2 hR hR' hd.ne hd.hx hd.cx
    hd.nx hd.hx' hd.cx' hd.nx' hd.same ha ha' hsq hsq' hS' hc

theorem twinMFCentralizingOn_psp2 (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) :
    TwinMFCentralizingOn .PSp (modelUniv .PSp 2 p e Fact.out) :=
  fun _ _ _ _ hd _ ha _ ha' hsq hsq' _ hS hc =>
    (twinMFNotCentralizing_psp2 hp2 hq hd ha ha' hsq hsq' hS hc).elim

theorem twinMFCentralizing_psp2 (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) :
    TwinMFCentralizing p e .PSp 2 :=
  twinMFCentralizing_of_on (twinMFCentralizingOn_psp2 hp2 hq)

end CFSG.ClassicalInvolution.RouteD.TwinY
