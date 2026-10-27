module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormC1
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNFour
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB2

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem false_of_outer_conj [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {W K T : Subgroup G} (hKL : IsL34Type (K ⧸ Open.fusionZStar K))
    (hKZ : zStarIn K = oddIn K) (hTsyl : IsSylowTwoIn T (normalizer (W : Set G)))
    (hTG : ∃ P : Sylow 2 G, (P : Subgroup G) = T)
    (hWT : ∀ F : Subgroup G, F ≤ T → IsEightGroup F →
      (∃ t ∈ T, t * t = 1 ∧ (∀ e ∈ F, t * e = e * t) ∧ t ∉ F) → wGroup F = W)
    {t : G} (htT : t ∈ T) (htK : t ∉ normalizer (K : Set G))
    (hr2 : ∀ m ∈ normalizer (W : Set G), conjugate K m = K ∨ conjugate K m = conjugate K t)
    (hinv : ∀ y ∈ normalizer (W : Set G), orderOf y = 2 → y ∈ normalizer (K : Set G))
    {a : G} (haT : a ∈ T) (ha2 : orderOf a = 2) (haK : a ∈ coreActionKernel K)
    (hout : t * a * t⁻¹ ∉ withKernel K) {F : Subgroup G}
    (hFa : F ≤ T ⊓ centralizer ({a} : Set G)) (hF : IsEightGroup F) {s : G}
    (hsa : s ∈ T ⊓ centralizer ({a} : Set G)) (hss : s * s = 1)
    (hsF : ∀ e ∈ F, s * e = e * s) (hsn : s ∉ F) : False := by
  have hsq2 : ∀ x : Multiplicative (ZMod 2), x * x = 1 := by decide
  have hval2 : ∀ x y : Multiplicative (ZMod 2), x ≠ 1 → y ≠ 1 → x * y = 1 := by decide
  classical
  set M : Subgroup G := normalizer (W : Set G) with hM
  set N : Subgroup G := normalizer (K : Set G) with hN
  have hT2 := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  have hTM := hTsyl.1
  have htM := hTM htT
  have haM := hTM haT
  have hKne : ∀ {y : G}, y ∈ M → y ∉ N → conjugate K y = conjugate K t :=
    fun {y} hy hyK => (hr2 y hy).resolve_left fun e => hyK (mem_normalizer_of_conjugate_eq e)
  have hsqN : ∀ y ∈ M, y * y ∈ N := by
    intro y hy
    by_cases hyK : y ∈ N
    · exact mul_mem hyK hyK
    · rcases hr2 (y * y) (mul_mem hy hy) with h1 | h1
      · exact mem_normalizer_of_conjugate_eq h1
      · exfalso
        apply hyK
        apply mem_normalizer_of_conjugate_eq
        have h3 : conjugate (conjugate K y) y = conjugate K y := by
          rw [conjugate_conjugate, h1, hKne hy hyK]
        have h4 := congrArg (fun H => conjugate H y⁻¹) h3
        simpa only [conjugate_conjugate, mul_inv_cancel_right, mul_inv_cancel, conjugate_one]
          using h4
  have htt : t * t ∈ N := hsqN t htM
  have httM : t * t ∈ M := mul_mem htM htM
  have hidx := HeSN.relIndex_eq_two htM htK htt hr2
  have hidx' : ((M ⊓ N).subgroupOf M).index = 2 := hidx
  have hmulK : ∀ x ∈ M, ∀ y ∈ M, (x * y ∈ N ↔ (x ∈ N ↔ y ∈ N)) := by
    intro x hx y hy
    have h1 := Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
    simp only [mem_subgroupOf, Subgroup.coe_mul, mem_inf] at h1
    simpa [hx, hy, mul_mem hx hy] using h1
  have htN' : t⁻¹ ∉ N := fun h => htK (by simpa using inv_mem h)
  have hconjiff : ∀ g ∈ M, (t * g * t⁻¹ ∈ N ↔ g ∈ N) := by
    intro g hg
    rw [hmulK _ (mul_mem htM hg) _ (inv_mem htM), hmulK _ htM _ hg]
    by_cases hgK : g ∈ N <;> simp [hgK, htK, htN']
  have hoffiff : ∀ g ∈ M, (g * t⁻¹ ∈ N ↔ g ∉ N) := by
    intro g hg
    rw [hmulK _ hg _ (inv_mem htM)]
    tauto
  have hU : ∀ y ∈ M, y ∈ N → t * y * t⁻¹ ∈ N := fun y hy hyK => (hconjiff y hy).mpr hyK
  obtain ⟨θ, hθC, hθin⟩ := exists_outerAct hKL hKZ
  have haN : a ∈ N := (mem_coreActionKernel.mp haK).1
  have hy₀N : t * a * t⁻¹ ∈ N := hU a haM haN
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hy₀2 : t * a * t⁻¹ * (t * a * t⁻¹) = 1 := by
    rw [show t * a * t⁻¹ * (t * a * t⁻¹) = t * (a * a) * t⁻¹ by group, haa]
    group
  have hθy₀ : θ ⟨t * a * t⁻¹, hy₀N⟩ ≠ 1 := fun h => hout (hθin _ hy₀N hy₀2 h)
  obtain ⟨e, he⟩ : ∃ e : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →*
      Multiplicative (ZMod 2), e (θ ⟨t * a * t⁻¹, hy₀N⟩) ≠ 1 := by
    by_cases h1 : (θ ⟨t * a * t⁻¹, hy₀N⟩).1 = 1
    · exact ⟨MonoidHom.snd _ _, fun h2 => hθy₀ (Prod.ext h1 h2)⟩
    · exact ⟨MonoidHom.fst _ _, h1⟩
  set φ₀ : ↥N →* Multiplicative (ZMod 2) := e.comp θ with hφ₀
  have hφeq : ∀ (x x' : G) (hx : x ∈ N) (hx' : x' ∈ N), x = x' → φ₀ ⟨x, hx⟩ = φ₀ ⟨x', hx'⟩ := by
    intro x x' hx hx' h
    subst h
    rfl
  have hφconj : ∀ (x g : G) (hx : x ∈ N) (hg : g ∈ N) (hgx : g⁻¹ * x * g ∈ N),
      φ₀ ⟨g⁻¹ * x * g, hgx⟩ = φ₀ ⟨x, hx⟩ := by
    intro x g hx hg hgx
    have e1 : (⟨g⁻¹ * x * g, hgx⟩ : ↥N) = (⟨g, hg⟩ : ↥N)⁻¹ * ⟨x, hx⟩ * ⟨g, hg⟩ := Subtype.ext rfl
    rw [e1, map_mul, map_mul, map_inv]
    exact inv_mul_cancel_comm _ _
  have hφa : φ₀ ⟨a, haN⟩ = 1 := by
    rw [hφ₀, MonoidHom.comp_apply, hθC a haN haK, map_one]
  obtain ⟨φh, hφhN, hφh1⟩ : ∃ φh : G → Multiplicative (ZMod 2),
      (∀ (g : G) (hg : g ∈ N), φh g = φ₀ ⟨g, hg⟩) ∧ ∀ g : G, g ∉ N → φh g = 1 :=
    ⟨fun g => if hg : g ∈ N then φ₀ ⟨g, hg⟩ else 1, fun g hg => dite_eq_left hg,
      fun g hg => dite_eq_right hg⟩
  obtain ⟨Fc, hFcd⟩ : ∃ Fc : G → Multiplicative (ZMod 2),
      ∀ y, Fc y = φh y * φh (t * y * t⁻¹) := ⟨fun y => φh y * φh (t * y * t⁻¹), fun y => rfl⟩
  have hFcN : ∀ (y : G) (hyM : y ∈ M) (hy : y ∈ N),
      Fc y = φ₀ ⟨y, hy⟩ * φ₀ ⟨t * y * t⁻¹, hU y hyM hy⟩ := by
    intro y hyM hy
    rw [hFcd, hφhN y hy, hφhN _ (hU y hyM hy)]
  have hFc1 : ∀ y ∈ M, y ∉ N → Fc y = 1 := by
    intro y hyM hy
    rw [hFcd, hφh1 y hy, hφh1 _ (fun h => hy ((hconjiff y hyM).mp h)), one_mul]
  have hF1 : ∀ y ∈ M, y ∈ N → ∀ z ∈ M, z ∈ N → Fc (y * z) = Fc y * Fc z := by
    intro y hyM hyK z hzM hzK
    rw [hFcN y hyM hyK, hFcN z hzM hzK, hFcN (y * z) (mul_mem hyM hzM) (mul_mem hyK hzK)]
    have e1 : (⟨y * z, mul_mem hyK hzK⟩ : ↥N) = ⟨y, hyK⟩ * ⟨z, hzK⟩ := rfl
    have e2 : (⟨t * (y * z) * t⁻¹, hU _ (mul_mem hyM hzM) (mul_mem hyK hzK)⟩ : ↥N) =
        ⟨t * y * t⁻¹, hU y hyM hyK⟩ * ⟨t * z * t⁻¹, hU z hzM hzK⟩ :=
      Subtype.ext (show t * (y * z) * t⁻¹ = t * y * t⁻¹ * (t * z * t⁻¹) by group)
    rw [e1, e2, map_mul, map_mul, mul_mul_mul_comm]
  have hF2 : ∀ y ∈ M, y ∈ N → Fc (t * y * t⁻¹) = Fc y := by
    intro y hyM hyK
    have h1 := hU y hyM hyK
    have h1M : t * y * t⁻¹ ∈ M := mul_mem (mul_mem htM hyM) (inv_mem htM)
    have h2 := hU _ h1M h1
    rw [hFcN _ h1M h1, hFcN y hyM hyK, mul_comm (φ₀ ⟨y, hyK⟩)]
    congr 1
    have hmem : (t * t)⁻¹⁻¹ * y * (t * t)⁻¹ ∈ N := by
      rw [inv_inv]
      exact mul_mem (mul_mem htt hyK) (inv_mem htt)
    exact (hφeq _ _ h2 hmem (by simp only [mul_assoc, inv_inv, mul_inv_rev])).trans
      (hφconj y (t * t)⁻¹ hyK (inv_mem htt) hmem)
  have hF3 : Fc (t * t) = 1 := by
    rw [hFcN _ httM htt, hφeq _ (t * t) (hU _ httM htt) htt (by group)]
    exact hsq2 _
  have hFca : Fc a = φ₀ ⟨t * a * t⁻¹, hy₀N⟩ := by
    rw [hFcN a haM haN, hφa, one_mul]
  have hFc11 : Fc 1 = 1 := by
    have h1 := hF1 1 (one_mem _) (one_mem _) 1 (one_mem _) (one_mem _)
    rwa [one_mul, hsq2] at h1
  have hF6 : ∀ n ∈ M, n ∈ N → ∀ y ∈ M, y ∈ N → Fc (n⁻¹ * y * n) = Fc y := by
    intro n hnM hnK y hyM hyK
    have hn' : n⁻¹ ∈ M := inv_mem hnM
    have hnK' : n⁻¹ ∈ N := inv_mem hnK
    rw [hF1 _ (mul_mem hn' hyM) (mul_mem hnK' hyK) _ hnM hnK, hF1 _ hn' hnK' _ hyM hyK,
      mul_comm (Fc n⁻¹), mul_assoc, ← hF1 _ hn' hnK' _ hnM hnK, inv_mul_cancel, hFc11, mul_one]
  have hFtinv : ∀ y ∈ M, y ∈ N → Fc (t⁻¹ * y * t) = Fc y := by
    intro y hyM hyK
    have h1M : t⁻¹ * y * t ∈ M := mul_mem (mul_mem (inv_mem htM) hyM) htM
    have h1K : t⁻¹ * y * t ∈ N := (hconjiff _ h1M).mp (by
      rw [show t * (t⁻¹ * y * t) * t⁻¹ = y by group]
      exact hyK)
    have h2 := hF2 _ h1M h1K
    rw [show t * (t⁻¹ * y * t) * t⁻¹ = y by group] at h2
    exact h2.symm
  have hF5 : ∀ m ∈ M, Fc (m⁻¹ * a * m) = Fc a := by
    intro m hmM
    by_cases hmK : m ∈ N
    · exact hF6 m hmM hmK a haM haN
    · have hnK : m * t⁻¹ ∈ N := (hoffiff m hmM).mpr hmK
      have hnM : m * t⁻¹ ∈ M := mul_mem hmM (inv_mem htM)
      have h1M : (m * t⁻¹)⁻¹ * a * (m * t⁻¹) ∈ M := mul_mem (mul_mem (inv_mem hnM) haM) hnM
      have h1K : (m * t⁻¹)⁻¹ * a * (m * t⁻¹) ∈ N := mul_mem (mul_mem (inv_mem hnK) haN) hnK
      rw [show m⁻¹ * a * m = t⁻¹ * ((m * t⁻¹)⁻¹ * a * (m * t⁻¹)) * t by group,
        hFtinv _ h1M h1K, hF6 _ hnM hnK a haM haN]
  have hχmul : ∀ y z : ↥T, Fc ((y * z : ↥T) : G) * Fc (((y * z : ↥T) : G) * t⁻¹) =
      Fc y * Fc ((y : G) * t⁻¹) * (Fc z * Fc ((z : G) * t⁻¹)) := by
    intro y z
    have hyM := hTM y.2
    have hzM := hTM z.2
    have hytM : (y : G) * t⁻¹ ∈ M := mul_mem hyM (inv_mem htM)
    have hztM : (z : G) * t⁻¹ ∈ M := mul_mem hzM (inv_mem htM)
    have hyzM : (y : G) * z ∈ M := mul_mem hyM hzM
    have hyztM : (y : G) * z * t⁻¹ ∈ M := mul_mem hyzM (inv_mem htM)
    simp only [Subgroup.coe_mul]
    by_cases hyK : (y : G) ∈ N <;> by_cases hzK : (z : G) ∈ N
    · have hyzK : (y : G) * z ∈ N := mul_mem hyK hzK
      rw [hFc1 _ hytM (fun h => ((hoffiff _ hyM).mp h) hyK),
        hFc1 _ hztM (fun h => ((hoffiff _ hzM).mp h) hzK),
        hFc1 _ hyztM (fun h => ((hoffiff _ hyzM).mp h) hyzK), hF1 _ hyM hyK _ hzM hzK]
      simp only [mul_one]
    · have hyzK : (y : G) * z ∉ N := fun h => hzK (((hmulK _ hyM _ hzM).mp h).mp hyK)
      rw [hFc1 _ hyzM hyzK, hFc1 _ hzM hzK, hFc1 _ hytM (fun h => ((hoffiff _ hyM).mp h) hyK),
        show (y : G) * z * t⁻¹ = y * (z * t⁻¹) by group,
        hF1 _ hyM hyK _ hztM ((hoffiff _ hzM).mpr hzK)]
      simp only [one_mul, mul_one]
    · have hyzK : (y : G) * z ∉ N := fun h => hyK (((hmulK _ hyM _ hzM).mp h).mpr hzK)
      have hzt : t * (z : G) * t⁻¹ ∈ M := mul_mem (mul_mem htM hzM) (inv_mem htM)
      rw [hFc1 _ hyzM hyzK, hFc1 _ hyM hyK, hFc1 _ hztM (fun h => ((hoffiff _ hzM).mp h) hzK),
        show (y : G) * z * t⁻¹ = y * t⁻¹ * (t * z * t⁻¹) by group,
        hF1 _ hytM ((hoffiff _ hyM).mpr hyK) _ hzt (hU _ hzM hzK), hF2 _ hzM hzK]
      simp only [one_mul, mul_one]
    · have hyzK : (y : G) * z ∈ N :=
        (hmulK _ hyM _ hzM).mpr ⟨fun h => absurd h hyK, fun h => absurd h hzK⟩
      have hyt := (hoffiff _ hyM).mpr hyK
      have hzt := (hoffiff _ hzM).mpr hzK
      have hzt' : t * ((z : G) * t⁻¹) * t⁻¹ ∈ N := hU _ hztM hzt
      have hzt'M : t * ((z : G) * t⁻¹) * t⁻¹ ∈ M := mul_mem (mul_mem htM hztM) (inv_mem htM)
      rw [hFc1 _ hyM hyK, hFc1 _ hzM hzK, hFc1 _ hyztM (fun h => ((hoffiff _ hyzM).mp h) hyzK),
        show (y : G) * z = y * t⁻¹ * (t * (z * t⁻¹) * t⁻¹) * (t * t) by group,
        hF1 _ (mul_mem hytM hzt'M) (mul_mem hyt hzt') _ httM htt,
        hF1 _ hytM hyt _ hzt'M hzt', hF2 _ hztM hzt, hF3]
      simp only [one_mul, mul_one]
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥T →* Multiplicative (ZMod 2),
      ∀ y : ↥T, χ y = Fc y * Fc ((y : G) * t⁻¹) :=
    ⟨MonoidHom.mk' (fun y : ↥T => Fc y * Fc ((y : G) * t⁻¹)) hχmul, fun y => rfl⟩
  have hFat : Fc (a * t⁻¹) = 1 :=
    hFc1 _ (mul_mem haM (inv_mem htM)) (fun h => ((hoffiff _ haM).mp h) haN)
  have hχa : χ ⟨a, haT⟩ ≠ 1 := by
    have h1 : χ ⟨a, haT⟩ = Fc a * Fc (a * t⁻¹) := hχ ⟨a, haT⟩
    rw [h1, hFat, mul_one, hFca]
    exact he
  have hker : χ.ker.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haT⟩, fun b => ?_⟩
    rw [xor_iff_iff_not, MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul]
    by_cases hb : χ b = 1
    · rw [hb, one_mul]
      exact iff_of_false hχa (not_not.mpr rfl)
    · exact iff_of_true (hval2 _ _ hb hχa) hb
  set H : Subgroup G := χ.ker.map T.subtype with hH
  have hHT : H ≤ T := map_subtype_le _
  have hHidx : H.relIndex T = 2 := by
    have h1 : H.subgroupOf T = χ.ker := comap_map_eq_self_of_injective T.subtype_injective _
    rw [relIndex, h1, hker]
  obtain ⟨P₀, hP₀⟩ := hTG
  rcases goldschmidtTransferInput_holds G P₀ a (hP₀ ▸ haT) ha2 with hall | hres
  · obtain ⟨g, hgH, hgext⟩ := hall H (by rw [hP₀]; exact hHT) (by rw [hP₀]; exact hHidx)
    rw [hP₀] at hgext
    obtain ⟨m, hmM, hm⟩ := exists_conj_of_witness hT2 hWT hgext hFa hF hsa hss hsF hsn
    rw [hm] at hgH
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hgH
    have hyeq' : (y : G) = m⁻¹ * a * m := hyeq
    have hcM : m⁻¹ * a * m ∈ M := mul_mem (mul_mem (inv_mem hmM) haM) hmM
    have hc2 : orderOf (m⁻¹ * a * m) = 2 := by
      rw [← ha2]
      exact (SemiconjBy.orderOf_eq m⁻¹ (show m⁻¹ * a = m⁻¹ * a * m * m⁻¹ by group)).symm
    have hcN : m⁻¹ * a * m ∈ N := hinv _ hcM hc2
    have h1 : χ y = Fc (m⁻¹ * a * m) * Fc (m⁻¹ * a * m * t⁻¹) := by
      rw [hχ, hyeq']
    have h3 : χ y = 1 := MonoidHom.mem_ker.mp hy
    rw [h1, hFc1 _ (mul_mem hcM (inv_mem htM)) (fun h => ((hoffiff _ hcM).mp h) hcN), mul_one,
      hF5 m hmM] at h3
    have h4 : χ ⟨a, haT⟩ = Fc a * Fc (a * t⁻¹) := hχ ⟨a, haT⟩
    rw [hFat, mul_one, h3] at h4
    exact hχa h4
  · exact hres (HeSN.mem_twoResidualOf_top' hnab a)

end CFSG.ComponentClassification.GrSLit.KSw
