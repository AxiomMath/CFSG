module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightNextNormalizerLinear

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

theorem le_sixtyFour_of_dvd {c : ℕ} (h : c ∣ 128) (hne : c ≠ 128) : c ≤ 64 := by
  have key : ∀ c, c ≤ 128 → c ∣ 128 → c ≠ 128 → c ≤ 64 := by decide
  exact key c (Nat.le_of_dvd (by norm_num) h) h hne

theorem le_or_le_of_isElementaryAbelian {G : Type*} [Group G] {z : G} (hz : orderOf z = 2)
    {C A D : Subgroup G} (hCe : IsElementaryAbelian 2 C) (hAC : A ≤ C)
    (hCz : ∀ c ∈ C, c * z = z * c ↔ c ∈ A) (hD : ((zpowers z : Set G) * (C : Set G)) = D)
    {E : Subgroup G} (hE : E ≤ D) (hEe : IsElementaryAbelian 2 E) :
    E ≤ C ∨ E ≤ A ⊔ zpowers z := by
  by_cases hEC : E ≤ C
  · exact Or.inl hEC
  right
  have hz2 : z * z = 1 := by
    rw [← sq, ← hz]
    exact pow_orderOf_eq_one z
  have hout : ∀ x ∈ E, x ∉ C → ∃ c ∈ A, x = z * c := by
    intro x hx hxC
    have hxD : x ∈ (D : Set G) := hE hx
    rw [← hD] at hxD
    obtain ⟨t, ht, c, hc, rfl⟩ := Set.mem_mul.1 hxD
    rcases eq_one_or_eq_of_mem_zpowers hz ht with rfl | rfl
    · exact absurd (by rwa [one_mul]) hxC
    · refine ⟨c, (hCz c hc).1 ?_, rfl⟩
      have hx2 : t * c * (t * c) = 1 := mul_self_of_isElementaryAbelian hEe hx
      have hc2 : c * c = 1 := mul_self_of_isElementaryAbelian hCe hc
      calc c * t = c * t * (t * c * (t * c)) := by rw [hx2, mul_one]
        _ = c * (t * t) * c * t * c := by group
        _ = t * c := by rw [hz2, mul_one, hc2, one_mul]
  obtain ⟨x, hx, hxC⟩ := IsConcreteLE.not_le_iff_exists.1 hEC
  obtain ⟨c, hcA, rfl⟩ := hout x hx hxC
  intro y hy
  by_cases hyC : y ∈ C
  · have h1 : y * (z * c) = z * c * y := mul_comm_of_isElementaryAbelian hEe hy hx
    have h2 : y * c = c * y := mul_comm_of_isElementaryAbelian hCe hyC (hAC hcA)
    have h3 : y * z = z * y := by
      have h4 : y * z * c = z * y * c := by
        calc y * z * c = y * (z * c) := by group
          _ = z * c * y := h1
          _ = z * (y * c) := by rw [h2]; group
          _ = z * y * c := by group
      exact mul_right_cancel h4
    exact mem_sup_left ((hCz y hyC).1 h3)
  · obtain ⟨c', hc'A, rfl⟩ := hout y hy hyC
    exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left hc'A)

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
  (halt : AltOrbit z φ e)

local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒮" => (𝒩 ⊓ centralizer (Singleton.singleton z : Set G) : Subgroup G)
local notation "𝒟" => CFSG.Assembly.pCoreOf 2 𝒩

include hzC hsup hinf hz hb hnd hV he halt in
theorem setting_facts :
    Nat.card 𝒟 = 1024 ∧ ((𝒟 : Set G) * (𝒮 : Set G)) = 𝒩 ∧
      𝒟 ⊓ centralizer ({z} : Set G) = ℛ ∧ 𝒟 ≤ 𝒩 ∧ ℛ ≤ 𝒟 ∧
      (∀ n ∈ 𝒩, ∀ x ∈ 𝒟, n * x * n⁻¹ ∈ 𝒟) ∧
      ∃ μ : 𝒩 →* GL (Fin 3) (ZMod 2), Function.Surjective μ ∧ μ.ker = (𝒟).subgroupOf 𝒩 := by
  have h8 : Nat.card (conjClass 𝒩 z) = 8 := by
    have h : conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0) :=
      halt
    rw [h, ← DegreeEight.range_alt_labels φ he,
      Nat.card_range_of_injective (DegreeEight.alt_labels_injective φ he)]
    simp
  obtain ⟨-, _, -, -, _, -, -, -, -, -, -, D, -, hDpcore, hcardD, hRD, hDN, -, -, hDS, hDH, -,
    μ, hμs, hμk, -⟩ :=
    DegreeEight.degree_eight_structure hzC hsup hinf hz hb hnd hV φ he 𝒩 inf_le_left le_rfl h8
  subst hDpcore
  refine ⟨hcardD, hDS, hDH, hDN, hRD, fun n hn x hx => ?_, μ, hμs, hμk⟩
  obtain ⟨d', hd', rfl⟩ := hx
  exact ⟨⟨n, hn⟩ * d' * ⟨n, hn⟩⁻¹,
    (CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_normal_assembly 2 𝒩).conj_mem d' hd'
      ⟨n, hn⟩, rfl⟩

include hzC hsup hinf hz hb hnd hV he halt in
theorem exists_nu_sigma :
    ∃ (ν : 𝒟 →* Multiplicative ↥BinarySymThreeOrbit.altSym) (σ : 𝒮 →* GL (Fin 3) (ZMod 2)),
      (∀ d : 𝒟, z⁻¹ * (d : G)⁻¹ * z * d = tauHom φ he (Multiplicative.ofAdd
        ((Multiplicative.toAdd (ν d) : ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3))) ∧
      Function.Surjective ν ∧ ν.ker = (ℛ).subgroupOf 𝒟 ∧ (center 𝒟).map (𝒟).subtype = 𝒜 ∧
      Function.Surjective σ ∧ σ.ker = (ℛ).subgroupOf 𝒮 ∧
      (∀ (m : 𝒮) (B : binarySymMatrices 3), (m : G) * tauHom φ he (Multiplicative.ofAdd B) *
        (m : G)⁻¹ = tauHom φ he (Multiplicative.ofAdd (symThreeCongr (σ m) B))) ∧
      (∀ (m : 𝒮) (d : 𝒟) (hd : (m : G) * d * (m : G)⁻¹ ∈ 𝒟),
        ((Multiplicative.toAdd (ν ⟨(m : G) * d * (m : G)⁻¹, hd⟩) :
          ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3) =
          symThreeCongr (σ m) ((Multiplicative.toAdd (ν d) : ↥BinarySymThreeOrbit.altSym) :
            binarySymMatrices 3)) ∧
      ∀ g : GL (Fin 3) (ZMod 2),
        σ ⟨leviHom φ he g, leviHom_mem_stab hzC hsup hinf hb hnd hV φ he g⟩ = g := by
  obtain ⟨ν, hν1, hν2, hν3, -, hν5, -, -⟩ :=
    translation_group_structure hzC hsup hinf hz hb hnd hV φ he halt
  have hν1' : ∀ d : 𝒟, z⁻¹ * (d : G)⁻¹ * z * d = tauHom φ he (Multiplicative.ofAdd
      ((Multiplicative.toAdd (ν d) : ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3)) := by
    intro d
    have h := hν1 d
    rw [coe_radLabel_symm_apply, RadicalLabels.zPow_zero, mul_one] at h
    exact h
  obtain ⟨σ, hσs, hσker, -, hσ⟩ := exists_sigma hzC hsup hinf hb hnd hV φ he
  have hconj : ∀ (m : 𝒮) (B : binarySymMatrices 3), (m : G) * tauHom φ he
      (Multiplicative.ofAdd B) * (m : G)⁻¹ =
        tauHom φ he (Multiplicative.ofAdd (symThreeCongr (σ m) B)) := by
    intro m B
    have h := RadicalLabels.conj_radHom_of_sigma φ he hzC hz (fun _ hx => (mem_inf.1 hx).2) σ hσ
      m B 0
    rwa [RadicalLabels.radHom_apply, RadicalLabels.radHom_apply, RadicalLabels.zPow_zero,
      mul_one, mul_one] at h
  refine ⟨ν, σ, hν1', hν2, hν3, hν5, hσs, hσker, hconj, fun m d hd => ?_, fun g => ?_⟩
  · have hmz : (m : G) * z = z * m := mem_centralizer_singleton_iff.1 (mem_inf.1 m.2).2
    have hm' : (m : G)⁻¹ * z * m = z := by
      rw [mul_assoc, ← hmz, ← mul_assoc, inv_mul_cancel, one_mul]
    have hzm : z⁻¹ * (m : G) = (m : G) * z⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hmz, mul_assoc, mul_inv_cancel, mul_one]
    have h1 := hν1' ⟨(m : G) * d * (m : G)⁻¹, hd⟩
    have h2 : z⁻¹ * ((m : G) * d * (m : G)⁻¹)⁻¹ * z * ((m : G) * d * (m : G)⁻¹) =
        (m : G) * (z⁻¹ * (d : G)⁻¹ * z * d) * (m : G)⁻¹ := by
      calc z⁻¹ * ((m : G) * d * (m : G)⁻¹)⁻¹ * z * ((m : G) * d * (m : G)⁻¹) =
          z⁻¹ * (m : G) * (d : G)⁻¹ * ((m : G)⁻¹ * z * m) * d * (m : G)⁻¹ := by group
        _ = z⁻¹ * (m : G) * (d : G)⁻¹ * z * d * (m : G)⁻¹ := by rw [hm']
        _ = (m : G) * (z⁻¹ * (d : G)⁻¹ * z * d) * (m : G)⁻¹ := by rw [hzm]; group
    rw [h2, hν1' d, hconj] at h1
    exact Multiplicative.ofAdd.injective (tauHom_injective φ he h1).symm
  · symm
    apply symThreeCongrHom_injective
    refine LinearEquiv.ext fun B => ?_
    rw [symThreeCongrHom_apply, symThreeCongrHom_apply]
    have h1 := hconj ⟨leviHom φ he g, leviHom_mem_stab hzC hsup hinf hb hnd hV φ he g⟩ B
    rw [RadicalLabels.leviHom_conj_tauHom'] at h1
    exact Multiplicative.ofAdd.injective (tauHom_injective φ he h1)

include hzC hsup hinf hz hb hnd hV he halt in
theorem card_inf_centralizer_le {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    {f : G} (hf : f ∈ 𝒩) (hfD : f ∉ 𝒟) :
    Nat.card (C₂ ⊓ centralizer ({f} : Set G) : Subgroup G) ≤ 64 := by
  classical
  obtain ⟨-, hDS, -, -, hRD, hDn, -⟩ := setting_facts hzC hsup hinf hz hb hnd hV φ he halt
  obtain ⟨ν, σ, -, -, hν3, hν5, -, hσker, hconj, hequiv, -⟩ :=
    exists_nu_sigma hzC hsup hinf hz hb hnd hV φ he halt
  have hfmem : f ∈ (𝒟 : Set G) * (𝒮 : Set G) := by
    rw [hDS]
    exact hf
  obtain ⟨d, hd, m, hm, rfl⟩ := Set.mem_mul.1 hfmem
  set m' : 𝒮 := ⟨m, hm⟩ with hm'
  have hσm : σ m' ≠ 1 := by
    intro h
    have h1 : m' ∈ σ.ker := h
    rw [hσker, mem_subgroupOf] at h1
    exact hfD (mul_mem hd (hRD h1))
  have hdA : ∀ a ∈ 𝒜, d * a = a * d := by
    intro a ha
    rw [← hν5] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    exact congrArg Subtype.val (mem_center_iff.1 hc ⟨d, hd⟩)
  set S := (C₂ ⊓ centralizer ({d * m} : Set G) : Subgroup G) with hS
  have hSD : S ≤ 𝒟 := inf_le_left.trans hC₂D
  have hsc : ∀ s : S, d * m * (s : G) = s * (d * m) := fun s =>
    (mem_centralizer_singleton_iff.1 (mem_inf.1 s.2).2).symm
  set ψ : S →* Multiplicative ↥BinarySymThreeOrbit.altSym := ν.comp (inclusion hSD) with hψ
  have h1 := ψ.ker.card_mul_index
  rw [Subgroup.index_ker] at h1
  have hfix : ∀ s : S, ((Multiplicative.toAdd (ψ s) : ↥BinarySymThreeOrbit.altSym) :
      binarySymMatrices 3) ∈ fixSym (σ m') := by
    intro s
    have hms : m * (s : G) * m⁻¹ ∈ 𝒟 := hDn m (mem_inf.1 hm).1 s (hSD s.2)
    have hds : d * (m * (s : G) * m⁻¹) * d⁻¹ = s := by
      calc d * (m * (s : G) * m⁻¹) * d⁻¹ = d * m * (s : G) * (d * m)⁻¹ := by group
        _ = s := by rw [hsc s]; group
    have hν : ν ⟨s, hSD s.2⟩ = ν ⟨m * (s : G) * m⁻¹, hms⟩ := by
      have h2 : (⟨s, hSD s.2⟩ : 𝒟) = ⟨d, hd⟩ * ⟨m * (s : G) * m⁻¹, hms⟩ * ⟨d, hd⟩⁻¹ :=
        Subtype.ext hds.symm
      rw [h2, map_mul, map_mul, map_inv, mul_comm (ν ⟨d, hd⟩), mul_inv_cancel_right]
    rw [mem_fixSym]
    have h2 := hequiv m' ⟨s, hSD s.2⟩ hms
    change symThreeCongr (σ m') ((Multiplicative.toAdd (ν ⟨s, hSD s.2⟩) :
      ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3) =
        ((Multiplicative.toAdd (ν ⟨s, hSD s.2⟩) : ↥BinarySymThreeOrbit.altSym) :
          binarySymMatrices 3)
    rw [← h2, ← hν]
  have hmemR : ∀ x : ψ.range, ((Multiplicative.toAdd (x : Multiplicative
      ↥BinarySymThreeOrbit.altSym) : ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3) ∈
        (fixSym (σ m') ⊓ BinarySymThreeOrbit.altSym : AddSubgroup (binarySymMatrices 3)) := by
    rintro ⟨_, s, rfl⟩
    exact AddSubgroup.mem_inf.2 ⟨hfix s, (Multiplicative.toAdd (ψ s)).2⟩
  have hrange : Nat.card ψ.range ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective (fun x => (⟨_, hmemR x⟩ :
      (fixSym (σ m') ⊓ BinarySymThreeOrbit.altSym : AddSubgroup (binarySymMatrices 3))))
      fun x y h => ?_) (card_fixAlt_le hσm)
    have h2 := congrArg Subtype.val h
    exact Subtype.ext (Multiplicative.toAdd.injective (Subtype.ext h2))
  have hker : Nat.card ψ.ker ≤ 16 := by
    have key : ∀ k : ψ.ker, ∃ B : binarySymMatrices 3, B ∈ fixSym (σ m') ∧
        tauHom φ he (Multiplicative.ofAdd B) = ((k : S) : G) := by
      intro k
      have hkR : ((k : S) : G) ∈ ℛ := by
        have h2 : (⟨(k : S), hSD (k : S).2⟩ : 𝒟) ∈ ν.ker := k.2
        rw [hν3, mem_subgroupOf] at h2
        exact h2
      have hkA : ((k : S) : G) ∈ 𝒜 := hC₂R.le (mem_inf.2 ⟨(mem_inf.1 (k : S).2).1, hkR⟩)
      obtain ⟨B, hB⟩ := (mem_pullSub_iff φ he).1 hkA
      refine ⟨Multiplicative.toAdd B, ?_, hB⟩
      rw [mem_fixSym]
      have h2 := hsc (k : S)
      rw [← hB] at h2
      have hc : m * tauHom φ he B * m⁻¹ = tauHom φ he (Multiplicative.ofAdd
          (symThreeCongr (σ m') (Multiplicative.toAdd B))) := by
        have h := hconj m' (Multiplicative.toAdd B)
        rwa [ofAdd_toAdd] at h
      have h3 : tauHom φ he (Multiplicative.ofAdd (symThreeCongr (σ m')
          (Multiplicative.toAdd B))) = tauHom φ he B := by
        rw [← hc]
        have h4 : d * (m * tauHom φ he B * m⁻¹) = (m * tauHom φ he B * m⁻¹) * d :=
          hdA _ (by rw [hc]; exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩)
        calc m * tauHom φ he B * m⁻¹ = (m * tauHom φ he B * m⁻¹ * d) * d⁻¹ := by group
          _ = (d * (m * tauHom φ he B * m⁻¹)) * d⁻¹ := by rw [h4]
          _ = (d * m * tauHom φ he B) * (d * m)⁻¹ := by group
          _ = (tauHom φ he B * (d * m)) * (d * m)⁻¹ := by rw [h2]
          _ = tauHom φ he B := by group
      exact Multiplicative.ofAdd.injective (tauHom_injective φ he h3)
    choose B hBfix hB using key
    refine le_trans (Nat.card_le_card_of_injective (fun k => (⟨B k, hBfix k⟩ : fixSym (σ m')))
      fun k k' h => ?_) (card_fixSym_le hσm)
    have h2 : B k = B k' := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    rw [← hB k, ← hB k', h2]
  rw [← h1]
  calc Nat.card ψ.ker * Nat.card ψ.range ≤ 16 * 4 := Nat.mul_le_mul hker hrange
    _ = 64 := rfl

include hzC hsup hinf hz hb hnd hV he halt in
theorem eq_C₂_of_isElementaryAbelian {C₂ : Subgroup G} (hC₂D : C₂ ≤ 𝒟)
    (hC₂c : Nat.card C₂ = 512) (hC₂R : C₂ ⊓ ℛ = 𝒜)
    (hC₂z' : ((zpowers z : Set G) * (C₂ : Set G)) = 𝒟)
    (hC₂z : ∀ c ∈ C₂, c * z = z * c ↔ c ∈ 𝒜) (hC₂e : IsElementaryAbelian 2 C₂)
    {F : Subgroup G} (hFN : F ≤ 𝒩) (hFe : IsElementaryAbelian 2 F) (hFc : Nat.card F = 512) :
    F = C₂ := by
  obtain ⟨hAe, hAc, hAC, -⟩ := pullSub_radical hb hnd hV φ (isTotallyIsotropic_lagrangianOf he)
    finrank_lagrangianOf
  obtain ⟨-, -, hRc⟩ := sup_facts hzC hinf hz (pullSub_le φ _) hAe hAc
  have hRC : centralizer (ℛ : Set G) = ℛ :=
    centralizer_sup_eq hzC hsup hinf hz (pullSub_le φ _) hAe hAc hAC
  obtain ⟨-, -, -, -, hRD, -, μ, -, hμk⟩ := setting_facts hzC hsup hinf hz hb hnd hV φ he halt
  have hAC₂ : 𝒜 ≤ C₂ := hC₂R ▸ inf_le_left
  have hdich : ∀ E : Subgroup G, E ≤ 𝒟 → IsElementaryAbelian 2 E → E ≤ C₂ ∨ E ≤ ℛ :=
    fun E hE hEe => le_or_le_of_isElementaryAbelian hz hC₂e hAC₂ hC₂z hC₂z' hE hEe
  by_cases hFD : F ≤ 𝒟
  · rcases hdich F hFD hFe with h | h
    · exact Subgroup.eq_of_le_of_card_ge h (by rw [hC₂c, hFc])
    · exfalso
      have h2 := Subgroup.card_le_of_le h
      rw [hFc, hRc] at h2
      norm_num at h2
  exfalso
  obtain ⟨f, hfF, hfD⟩ := IsConcreteLE.not_le_iff_exists.1 hFD
  set μF : F →* GL (Fin 3) (ZMod 2) := μ.comp (inclusion hFN) with hμF
  have h1 := μF.ker.card_mul_index
  rw [Subgroup.index_ker] at h1
  have hrange : Nat.card μF.range ≤ 4 := by
    refine card_le_four_of_mul_self _ ?_
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (mul_self_of_isElementaryAbelian hFe x.2),
      map_one]
  have hkerD : μF.ker = (𝒟).subgroupOf F := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hμF, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hμk,
      mem_subgroupOf]
    rfl
  have hkercard : Nat.card μF.ker = Nat.card (F ⊓ 𝒟 : Subgroup G) := by
    rw [hkerD, ← Subgroup.card_map_of_injective F.subtype_injective, subgroupOf_map_subtype,
      inf_comm]
  have hFDe : IsElementaryAbelian 2 (F ⊓ 𝒟 : Subgroup G) :=
    isElementaryAbelian_of_forall (fun x hx y hy => mul_comm_of_isElementaryAbelian hFe hx.1 hy.1)
      fun x hx => mul_self_of_isElementaryAbelian hFe hx.1
  have hcen : F ⊓ 𝒟 ≤ centralizer ({f} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mul_comm_of_isElementaryAbelian hFe hx.1 hfF)
  have hbound : Nat.card (F ⊓ 𝒟 : Subgroup G) ≤ 64 := by
    rcases hdich _ inf_le_right hFDe with h | h
    · exact le_trans (Subgroup.card_le_of_le (le_inf h hcen))
        (card_inf_centralizer_le hzC hsup hinf hz hb hnd hV φ he halt hC₂D hC₂R (hFN hfF) hfD)
    · have hne : ℛ ⊓ centralizer ({f} : Set G) ≠ ℛ := by
        intro heq
        apply hfD
        apply hRD
        rw [← hRC, mem_centralizer_iff]
        intro r hr
        have hr' : r ∈ ℛ ⊓ centralizer ({f} : Set G) := by
          rw [heq]
          exact hr
        exact mem_centralizer_singleton_iff.1 (mem_inf.1 hr').2
      have hdvd : Nat.card (ℛ ⊓ centralizer ({f} : Set G) : Subgroup G) ∣ 128 := by
        rw [← hRc]
        exact Subgroup.card_dvd_of_le inf_le_left
      have hlt : Nat.card (ℛ ⊓ centralizer ({f} : Set G) : Subgroup G) ≠ 128 := fun h128 =>
        hne (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h128, hRc]))
      exact (Subgroup.card_le_of_le (le_inf h hcen)).trans (le_sixtyFour_of_dvd hdvd hlt)
  have h2 : Nat.card F ≤ 256 := by
    rw [← h1, hkercard]
    calc Nat.card (F ⊓ 𝒟 : Subgroup G) * Nat.card μF.range ≤ 64 * 4 :=
          Nat.mul_le_mul hbound hrange
      _ = 256 := rfl
  omega

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
