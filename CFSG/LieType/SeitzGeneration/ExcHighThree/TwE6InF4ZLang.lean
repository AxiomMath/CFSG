module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.Purity
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZPlane

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Chevalley CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

set_option linter.unusedSectionVars false


theorem lang_core_three_elt {K : Type} [Field K] [Finite K] {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] {p f : ℕ} [Fact p.Prime] [CharP Ω p] (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq : Nat.card K = p ^ f) (ω : Ωˣ) (hω : orderOf ω = 3)
    (Dz Q : ModGL Tag.F4 Ω) (hDz : Dz ∈ adjointGroup Tag.F4 Ω) (hQ : Q ∈ adjointGroup Tag.F4 Ω)
    {s : ℕ} (hs : ¬ 3 ∣ s)
    (hFDz : entrywiseFrobGL Tag.F4 Ω p f Dz = Dz * Q)
    (hQd : Q * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Q⁻¹ =
      rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) ^ s)
    (z : adjointGroup Tag.F4 K)
    (hz : baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) =
      Dz * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * Dz⁻¹)
    (e₀ : adjointGroup Tag.F4 K) (P : ModGL Tag.F4 Ω) (hP : P ∈ adjointGroup Tag.F4 Ω)
    (hē : baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.F4 K) =
      P * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * P⁻¹) :
    ∃ g : adjointGroup Tag.F4 K, g * e₀ * g⁻¹ = z := by
  classical
  have hFr : ∀ c : Ω, iterateFrobenius Ω p f c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hq]
  have hbij : Function.Bijective (iterateFrobenius Ω p f) := by
    refine ⟨(iterateFrobenius Ω p f).injective, fun y => ?_⟩
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (Fact.out : p.Prime).pos f)
    exact ⟨x, by rw [iterateFrobenius_def]; exact hx⟩
  have hrat : ∀ w : ModGL Tag.F4 K,
      entrywiseFrobGL Tag.F4 Ω p f (baseChangeGL (algebraMap K Ω) w) =
        baseChangeGL (algebraMap K Ω) w :=
    fun w => CFSG.RankThree.PartOne.KE8F.baseChangeGL_frob_fixed (iterateFrobenius Ω p f) hFr w
  have hFmem : ∀ g ∈ adjointGroup Tag.F4 Ω,
      entrywiseFrobGL Tag.F4 Ω p f g ∈ adjointGroup Tag.F4 Ω := by
    intro g hg
    have h := CFSG.HardMathSupport.Lang.AnisoE6.baseChangeGL_mem_adjointGroup_of_mem
      (iterateFrobenius Ω p f) hg
    rwa [← units_map_entrywiseHom_eq_baseChangeGL_self] at h
  have hconj' : baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.F4 K) =
      (P * Dz⁻¹) * baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) * (P * Dz⁻¹)⁻¹ := by
    rw [hz, hē]
    group
  have hh : P * Dz⁻¹ ∈ adjointGroup Tag.F4 Ω := mul_mem hP (inv_mem hDz)
  have hlang : ∀ c ∈ adjointGroup Tag.F4 Ω,
      c * baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) =
        baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) * c →
      ∃ y ∈ adjointGroup Tag.F4 Ω,
        y * baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) =
          baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K) * y ∧
        y⁻¹ * entrywiseFrobGL Tag.F4 Ω p f y = c := by
    intro c hc hcz
    rw [hz] at hcz ⊢
    exact lang_centralizer hp3 hf ω hω Dz Q hQ hs hDz hFDz hQd c hc hcz
  obtain ⟨g, hgG, hgF, hgconj⟩ := lang_fix (entrywiseFrobGL Tag.F4 Ω p f) (adjointGroup Tag.F4 Ω)
    (baseChangeGL (algebraMap K Ω) (z : ModGL Tag.F4 K))
    (baseChangeGL (algebraMap K Ω) (e₀ : ModGL Tag.F4 K))
    (P * Dz⁻¹) hh (hFmem _ hh) (hrat _) (hrat _) hconj' hlang
  have hgmem : g ∈ (adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K Ω)) :=
    mem_map_adjointGroup_of_frobenius_fixed (τ := Tag.F4) (Or.inr rfl) (iterateFrobenius Ω p f)
      hFr hbij hgG hgF
  obtain ⟨e₁, he₁, he₁g⟩ := Subgroup.mem_map.1 hgmem
  have hconjK : e₁ * (z : ModGL Tag.F4 K) * e₁⁻¹ = (e₀ : ModGL Tag.F4 K) := by
    apply baseChangeGL_injective (algebraMap K Ω)
    rw [map_mul, map_mul, map_inv, he₁g]
    exact hgconj
  refine ⟨⟨e₁⁻¹, inv_mem he₁⟩, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  rw [← hconjK]
  group


theorem zpow_eq_of_emod_three_f4 {K : Type} [Field K] (ω : Kˣ) (hω : orderOf ω = 3) (m n : ℤ)
    (h : m % 3 = n % 3) : ω ^ m = ω ^ n := by
  have h3 : ω ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hω, pow_orderOf_eq_one]
  have hmn : m = n + 3 * ((m - n) / 3) := by omega
  rw [hmn, zpow_add, zpow_mul, h3, one_zpow, mul_one]

theorem f4_cube_root_data {Ω : Type} [Field Ω] (ω : Ωˣ) (hω : orderOf ω = 3) :
    ((ω ^ 2 : Ωˣ) : Ω) ^ 2 + ((ω ^ 2 : Ωˣ) : Ω) + 1 = 0 ∧ ((ω ^ 2 : Ωˣ) : Ω) ≠ 1 ∧
      (fun j => (ω ^ 2) ^ f4Exp j) = Pi.mulSingle f4One ω := by
  have hprim : IsPrimitiveRoot (ω : Ω) 3 := by
    have h := IsPrimitiveRoot.orderOf (ω : Ω)
    rwa [orderOf_units, hω] at h
  have hsum : (ω : Ω) ^ 2 + ω + 1 = 0 := by
    have h := hprim.geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
    linear_combination h
  have h3 : (ω : Ω) ^ 3 = 1 := hprim.pow_eq_one
  have hne1 : (ω : Ω) ≠ 1 := hprim.ne_one (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_pow_eq_pow_val]
    linear_combination (ω : Ω) * h3 + hsum
  · rw [Units.val_pow_eq_pow_val]
    intro h
    apply hne1
    linear_combination (-(ω : Ω)) * h + h3
  · funext j
    have hj : ∀ m : ℤ, (ω ^ 2) ^ m = ω ^ (2 * m) := fun m => by
      rw [← zpow_natCast, ← zpow_mul]; norm_num
    rw [hj]
    fin_cases j
    · show ω ^ (2 * (-3 : ℤ)) = (Pi.mulSingle f4One ω : Fin Tag.F4.rank → Ωˣ) ⟨0, by decide⟩
      rw [Pi.mulSingle_eq_of_ne (by decide)]
      rw [zpow_eq_of_emod_three_f4 ω hω _ 0 (by norm_num), zpow_zero]
    · show ω ^ (2 * (2 : ℤ)) = (Pi.mulSingle f4One ω : Fin Tag.F4.rank → Ωˣ) ⟨1, by decide⟩
      rw [show (⟨1, by decide⟩ : Fin Tag.F4.rank) = f4One from rfl, Pi.mulSingle_eq_same]
      rw [zpow_eq_of_emod_three_f4 ω hω _ 1 (by norm_num), zpow_one]
    · show ω ^ (2 * (0 : ℤ)) = (Pi.mulSingle f4One ω : Fin Tag.F4.rank → Ωˣ) ⟨2, by decide⟩
      rw [Pi.mulSingle_eq_of_ne (by decide)]
      simp
    · show ω ^ (2 * (0 : ℤ)) = (Pi.mulSingle f4One ω : Fin Tag.F4.rank → Ωˣ) ⟨3, by decide⟩
      rw [Pi.mulSingle_eq_of_ne (by decide)]
      simp

theorem twisted_z_conj_f4Z (k : Type) [Field k] [Finite k] (hq : Nat.card k % 3 = 2)
    (D₁ : LangLevi TwClass.f4Six.tag k TwClass.f4Six.w) (ω : D₁.Lˣ) (hω : orderOf ω = 3)
    (z : adjointGroup TwClass.f4Six.tag k)
    (hz : baseChangeGL (algebraMap k D₁.L) (z : ModGL TwClass.f4Six.tag k) =
      D₁.g * rootDiagUnit TwClass.f4Six.tag (Pi.mulSingle (⟨1, by decide⟩ : Fin
        TwClass.f4Six.tag.rank) ω) * D₁.g⁻¹) :
    ∃ f : adjointGroup Tag.F4 k, f * (⟨f4Z k, f4Z_mem_adjointGroup⟩ : adjointGroup Tag.F4 k) *
      f⁻¹ = z := by
  have hnd : ¬ 3 ∣ Nat.card k := by omega
  obtain ⟨f, hf1, hq', hp⟩ := card_eq_ringChar_pow k
  haveI : Fact (ringChar k).Prime := ⟨hp⟩
  have hp3 : ringChar k ≠ 3 := ringChar_ne_three k hf1 hq' hnd
  haveI : IsAlgClosed D₁.L := IsAlgClosure.isAlgClosed k
  haveI : CharP D₁.L (ringChar k) :=
    charP_of_injective_algebraMap (algebraMap k D₁.L).injective (ringChar k)
  have hFr_eq : iterateFrobenius D₁.L (ringChar k) f = D₁.Fr :=
    RingHom.ext fun x => by rw [iterateFrobenius_def, D₁.hFr, hq']
  have hFDz : entrywiseFrobGL TwClass.f4Six.tag D₁.L (ringChar k) f D₁.g =
      D₁.g * canonicalRep (coxeterSystem TwClass.f4Six.tag) D₁.L TwClass.f4Six.w := by
    show Units.map (entrywiseHom (iterateFrobenius D₁.L (ringChar k) f)) D₁.g = _
    rw [hFr_eq, D₁.lang]
  have hDz : D₁.g ∈ adjointGroup TwClass.f4Six.tag D₁.L :=
    parabolicLevi_le_adjointGroup (K := D₁.L) (τ := TwClass.f4Six.tag) _ D₁.g_mem
  have hQ : canonicalRep (coxeterSystem TwClass.f4Six.tag) D₁.L TwClass.f4Six.w ∈
      adjointGroup TwClass.f4Six.tag D₁.L :=
    canonicalRep_mem_adjointGroup (τ := TwClass.f4Six.tag) (coxeterSystem TwClass.f4Six.tag) D₁.L _
  have hQd : canonicalRep (coxeterSystem TwClass.f4Six.tag) D₁.L TwClass.f4Six.w *
      rootDiagUnit TwClass.f4Six.tag
        (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) *
      (canonicalRep (coxeterSystem TwClass.f4Six.tag) D₁.L TwClass.f4Six.w)⁻¹ =
      rootDiagUnit TwClass.f4Six.tag
        (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) ^ 2 := by
    have hconj := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit
      (K := D₁.L) TwClass.f4Six.w
      (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω)
    rw [weylAct_twice_threeA ω hω] at hconj
    refine hconj.trans ?_
    exact map_pow (rootDiagUnitHom TwClass.f4Six.tag D₁.L) _ 2
  obtain ⟨hr2, hr1, htuple⟩ := f4_cube_root_data ω hω
  obtain ⟨P, hP, hPd⟩ := f4Z_diag (ω ^ 2) hr2 hr1
  rw [htuple] at hPd
  have hē : baseChangeGL (algebraMap k D₁.L)
      ((⟨f4Z k, f4Z_mem_adjointGroup⟩ : adjointGroup Tag.F4 k) : ModGL Tag.F4 k) =
      P * rootDiagUnit Tag.F4 (Pi.mulSingle 1 ω) * P⁻¹ := by
    show baseChangeGL (algebraMap k D₁.L) (f4Z k) = _
    rw [baseChangeGL_f4Z]
    calc f4Z D₁.L = P * (P⁻¹ * f4Z D₁.L * P) * P⁻¹ := by group
      _ = _ := by rw [hPd]; rfl
  obtain ⟨g, hg⟩ := lang_core_three_elt hp3 hf1 hq' ω hω D₁.g
    (canonicalRep (coxeterSystem TwClass.f4Six.tag) D₁.L TwClass.f4Six.w) hDz hQ (s := 2)
    (by decide) hFDz hQd z hz _ P hP hē
  exact ⟨g, hg⟩

end CFSG.LieType.SeitzGeneration.ExcHighThree
