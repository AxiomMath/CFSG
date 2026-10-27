module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB1
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNDouble
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_witness {T W : Subgroup G} (hT2 : IsPGroup 2 T)
    (hWT : ∀ F : Subgroup G, F ≤ T → IsEightGroup F →
      (∃ t ∈ T, t * t = 1 ∧ (∀ e ∈ F, t * e = e * t) ∧ t ∉ F) → wGroup F = W)
    {b g : G} (hext : IsExtremalIn T (g⁻¹ * b * g)) {E : Subgroup G}
    (hET : E ≤ T ⊓ centralizer ({b} : Set G)) (hE : IsEightGroup E) {w : G}
    (hwT : w ∈ T ⊓ centralizer ({b} : Set G)) (hww : w * w = 1)
    (hwE : ∀ e ∈ E, w * e = e * w) (hwnE : w ∉ E) :
    ∃ m ∈ normalizer (W : Set G), g⁻¹ * b * g = m⁻¹ * b * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set b' : G := g⁻¹ * b * g with hb'
  have hsylC : IsSylowTwoIn (T ⊓ centralizer ({b'} : Set G)) (centralizer ({b'} : Set G)) :=
    ⟨inf_le_right, hext.2⟩
  set P : Subgroup G := (T ⊓ centralizer ({b} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom
    with hP
  have hP2 : IsPGroup 2 P := (hT2.to_le inf_le_left).map _
  have hPC : P ≤ centralizer ({b'} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyb : y * b = b * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hb']
    calc g⁻¹ * y * g * (g⁻¹ * b * g) = g⁻¹ * (y * b) * g := by group
      _ = g⁻¹ * (b * y) * g := by rw [hyb]
      _ = g⁻¹ * b * g * (g⁻¹ * y * g) := by group
  obtain ⟨c, hcC, hcP⟩ := hsylC.exists_conj_le hPC hP2
  set k : G := c * g⁻¹ with hk
  have hkT : ∀ y ∈ T ⊓ centralizer ({b} : Set G), k * y * k⁻¹ ∈ T := by
    intro y hy
    have h1 := hcP (g⁻¹ * y * g⁻¹⁻¹) ⟨y, hy, rfl⟩
    rw [hk, show c * g⁻¹ * y * (c * g⁻¹)⁻¹ = c * (g⁻¹ * y * g⁻¹⁻¹) * c⁻¹ by group]
    exact (mem_inf.mp h1).1
  have hWE : wGroup E = W :=
    hWT E (hET.trans inf_le_left) hE ⟨w, (mem_inf.mp hwT).1, hww, hwE, hwnE⟩
  set E' : Subgroup G := E.map (MulAut.conj k).toMonoidHom with hE'
  have hE'T : E' ≤ T := by
    rintro _ ⟨e, he, rfl⟩
    exact hkT e (hET he)
  have hE'8 : IsEightGroup E' :=
    ⟨hE.1.map_conj k, by rw [hE', card_map_of_injective (MulAut.conj k).injective, hE.2]⟩
  have hw' : ∃ t ∈ T, t * t = 1 ∧ (∀ e ∈ E', t * e = e * t) ∧ t ∉ E' := by
    refine ⟨k * w * k⁻¹, hkT w hwT, ?_, ?_, ?_⟩
    · rw [show k * w * k⁻¹ * (k * w * k⁻¹) = k * (w * w) * k⁻¹ by group, hww]
      group
    · rintro _ ⟨e, he, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show k * w * k⁻¹ * (k * e * k⁻¹) = k * (w * e) * k⁻¹ by group, hwE e he]
      group
    · rintro ⟨e, he, hee⟩
      apply hwnE
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hee
      have : e = w := mul_left_cancel (mul_right_cancel hee)
      rw [← this]
      exact he
  have hWE' := hWT E' hE'T hE'8 hw'
  rw [hE', wGroup_map_conj, hWE] at hWE'
  have hkN : k ∈ normalizer (W : Set G) := mem_normalizer_iff_map_conj_eq.mpr hWE'
  refine ⟨k⁻¹, inv_mem hkN, ?_⟩
  have hcb : c * b' = b' * c := mem_centralizer_singleton_iff.mp hcC
  calc g⁻¹ * b * g = c * b' * c⁻¹ := by rw [hcb, mul_inv_cancel_right]
    _ = k⁻¹⁻¹ * b * k⁻¹ := by rw [hb', hk]; group

theorem exists_sylow_of_wT {T W : Subgroup G} (hTsyl : IsSylowTwoIn T (normalizer (W : Set G)))
    (hWT : ∀ F : Subgroup G, F ≤ T → IsEightGroup F →
      (∃ t ∈ T, t * t = 1 ∧ (∀ e ∈ F, t * e = e * t) ∧ t ∉ F) → wGroup F = W)
    {F : Subgroup G} (hFT : F ≤ T) (hF : IsEightGroup F) {s : G} (hsT : s ∈ T)
    (hss : s * s = 1) (hsF : ∀ e ∈ F, s * e = e * s) (hsn : s ∉ F) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hFW : wGroup F = W := hWT F hFT hF ⟨s, hsT, hss, hsF, hsn⟩
  obtain ⟨Q, hTQ⟩ := (GrS4.isPGroup_of_isSylowTwoIn hTsyl).exists_le_sylow
  refine ⟨Q, le_antisymm ?_ hTQ⟩
  by_contra hQT
  have hlt : T.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hQT fun q hq => ?_
    have : (⟨q, hq⟩ : Q) ∈ T.subgroupOf Q := by rw [htop]; exact mem_top _
    exact mem_subgroupOf.mp this
  have hnil : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
  obtain ⟨y, hyN, hyT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hconj : ∀ z ∈ T, (y : G) * z * (y : G)⁻¹ ∈ T := by
    intro z hz
    have hzQ : z ∈ Q := hTQ hz
    have hz' : (⟨z, hzQ⟩ : Q) ∈ T.subgroupOf Q := mem_subgroupOf.mpr hz
    have := (mem_normalizer_iff.mp hyN _).mp hz'
    exact mem_subgroupOf.mp this
  have hFy : F.map (MulAut.conj (y : G)).toMonoidHom ≤ T := by
    rintro _ ⟨z, hz, rfl⟩
    exact hconj z (hFT hz)
  have hyM : (y : G) ∈ M := by
    have hns : ∃ t ∈ T, t * t = 1 ∧
        (∀ e ∈ F.map (MulAut.conj (y : G)).toMonoidHom, t * e = e * t) ∧
        t ∉ F.map (MulAut.conj (y : G)).toMonoidHom := by
      refine ⟨(y : G) * s * (y : G)⁻¹, hconj s hsT, ?_, ?_, ?_⟩
      · rw [show (y : G) * s * (y : G)⁻¹ * ((y : G) * s * (y : G)⁻¹) =
          (y : G) * (s * s) * (y : G)⁻¹ by group, hss]
        group
      · rintro _ ⟨e, he, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show (y : G) * s * (y : G)⁻¹ * ((y : G) * e * (y : G)⁻¹) =
          (y : G) * (s * e) * (y : G)⁻¹ by group, hsF e he]
        group
      · rintro ⟨e, he, hee⟩
        apply hsn
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hee
        have : e = s := mul_left_cancel (mul_right_cancel hee)
        rw [← this]
        exact he
    have hFy8 : IsEightGroup (F.map (MulAut.conj (y : G)).toMonoidHom) :=
      ⟨hF.1.map_conj _, by rw [card_map_of_injective (MulAut.conj (y : G)).injective, hF.2]⟩
    have h1 := hWT _ hFy hFy8 hns
    rw [wGroup_map_conj, hFW] at h1
    exact mem_normalizer_iff_map_conj_eq.mpr h1
  have hQ' : IsPGroup 2 ↥(T ⊔ zpowers (y : G)) :=
    Q.isPGroup'.to_le (sup_le hTQ (zpowers_le.mpr y.2))
  have heq := hTsyl.eq_of_le le_sup_left (sup_le hTsyl.1 (zpowers_le.mpr hyM)) hQ'
  have hyT' : (y : G) ∈ T ⊔ zpowers (y : G) :=
    (le_sup_right : zpowers (y : G) ≤ T ⊔ zpowers (y : G)) (mem_zpowers (y : G))
  rw [heq] at hyT'
  exact hyT (mem_subgroupOf.mpr hyT')

theorem exists_witness_of_involution {W K : Subgroup G} (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKC : Odd (Nat.card ↥(K ⊓ coreActionKernel K))) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTM : T ≤ normalizer (W : Set G)) {s : G} (hsT : s ∈ T) (hss : s * s = 1)
    (hKs : conjugate K s ≠ K) {E : Subgroup G} (hET : E ≤ T ⊓ K) (hE : IsElemTwo E)
    (hE16 : Nat.card E = 16) :
    ∃ F ≤ T ⊓ centralizer ({s} : Set G), IsEightGroup F ∧
      ∃ w ∈ T ⊓ centralizer ({s} : Set G), w * w = 1 ∧ (∀ e ∈ F, w * e = e * w) ∧ w ∉ F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : ∀ y ∈ T ⊓ K, ∀ y' ∈ T ⊓ K, Commute y (s⁻¹ * y' * s) := fun y hy y' hy' =>
    commute_conj_one hKM hKc hT2 hTM hy hy' hsT hKs
  set ψ : ↥(T ⊓ K) →* G := HeSN.doubleHom hY with hψ
  have hψinj : Function.Injective ψ := HeSN.doubleHom_injective hY (P := coreActionKernel K)
    (fun y hy => conj_mem_coreActionKernel_of_ne hKM hKc (mem_inf.mp hy).2 (hTM hsT) hKs)
    (fun y hy hyk => by
      have hb := eq_bot_of_le_two_group_of_le_odd hT2 hKC
        (zpowers_le.mpr (mem_inf.mp hy).1) (zpowers_le.mpr (mem_inf.mpr ⟨(mem_inf.mp hy).2, hyk⟩))
      have h1 : y ∈ zpowers y := mem_zpowers _
      rwa [hb, mem_bot] at h1)
  have hψT : ∀ y : ↥(T ⊓ K), ψ y ∈ T ⊓ centralizer ({s} : Set G) := by
    intro y
    refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr
      (HeSN.commute_doubleHom_self hY hss y).eq.symm⟩
    rw [HeSN.doubleHom_apply]
    have hyT := (mem_inf.mp y.2).1
    exact mul_mem hyT (mul_mem (mul_mem (inv_mem hsT) hyT) hsT)
  obtain ⟨E₈, hE₈E, hE₈c⟩ := exists_le_card_eight hE.isPGroup (by omega)
  have hE₈e : IsElemTwo E₈ := hE.mono hE₈E
  obtain ⟨e₀, he₀E, he₀n⟩ : ∃ e₀ ∈ E, e₀ ∉ E₈ := by
    by_contra h
    push Not at h
    have := card_le_of_le (h : E ≤ E₈)
    omega
  set ψ₈ : ↥E₈ →* G := ψ.comp (inclusion (hE₈E.trans hET)) with hψ₈
  have hψ₈inj : Function.Injective ψ₈ := hψinj.comp (inclusion_injective _)
  refine ⟨ψ₈.range, ?_, ⟨HeSN.isElemTwo_range hE₈e ψ₈, ?_⟩, ψ ⟨e₀, hET he₀E⟩, hψT _, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hψT _
  · rw [HeSN.card_range_of_injective hψ₈inj, hE₈c]
  · rw [← map_mul]
    have : (⟨e₀, hET he₀E⟩ : ↥(T ⊓ K)) * ⟨e₀, hET he₀E⟩ = 1 := Subtype.ext (hE.2 e₀ he₀E)
    rw [this, map_one]
  · rintro _ ⟨y, rfl⟩
    simp only [hψ₈, MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hE.1 e₀ he₀E _ (hE₈E y.2))
  · rintro ⟨y, hy⟩
    simp only [hψ₈, MonoidHom.comp_apply] at hy
    have h1 := hψinj hy
    apply he₀n
    have h2 := congrArg Subtype.val h1
    simp only [coe_inclusion] at h2
    rw [← h2]
    exact y.2

end CFSG.ComponentClassification.GrSLit.KSw
