module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3A6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58S

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

namespace Eight2.Three

variable {X : Type} [Group X]

theorem le_of_open {H K : Subgroup X} (h : Open.IsSubnormal H K) : H ≤ K :=
  h.le

theorem open_trans {A B C : Subgroup X} (h₁ : Open.IsSubnormal A B)
    (h₂ : Open.IsSubnormal B C) : Open.IsSubnormal A C :=
  h₁.trans h₂

theorem open_inf {A B : Subgroup X} (h : Open.IsSubnormal A B) (K : Subgroup X) :
    Open.IsSubnormal (A ⊓ K) (B ⊓ K) :=
  h.inf K

theorem open_sup {A H O : Subgroup X} (h : Open.IsSubnormal A H)
    (hO : H ≤ normalizer (O : Set X)) : Open.IsSubnormal (A ⊔ O) (H ⊔ O) := by
  induction h with
  | refl => exact .refl _
  | @step A M H hAM hn hMH ih =>
    have hMH' : M ≤ H := le_of_open hMH
    have hconj : ∀ y : X, (∀ x ∈ A, y * x * y⁻¹ ∈ A ⊔ O) → (∀ x ∈ O, y * x * y⁻¹ ∈ A ⊔ O) →
        ∀ x ∈ A ⊔ O, y * x * y⁻¹ ∈ A ⊔ O := by
      intro y hA hO' x hx
      have hle : A ⊔ O ≤ (A ⊔ O).comap (MulAut.conj y).toMonoidHom :=
        sup_le (fun w hw => mem_comap.mpr (hA w hw)) (fun w hw => mem_comap.mpr (hO' w hw))
      exact mem_comap.mp (hle hx)
    have hnorm : M ⊔ O ≤ normalizer ((A ⊔ O : Subgroup X) : Set X) := by
      refine sup_le (le_normalizer_iff.mpr fun m hm => hconj m ?_ ?_)
        (le_normalizer_iff.mpr fun o ho => hconj o ?_ ?_)
      · intro x hx
        exact mem_sup_left ((normal_subgroupOf_iff hAM).mp hn x m hx hm)
      · intro x hx
        exact mem_sup_right ((mem_normalizer_iff.mp (hO (hMH' hm)) x).mp hx)
      · intro x hx
        have hxH : x⁻¹ ∈ normalizer (O : Set X) := hO (hMH' (hAM (inv_mem hx)))
        have h1 : x⁻¹ * o * x ∈ O := by
          have := (mem_normalizer_iff.mp hxH o).mp ho
          rwa [inv_inv] at this
        rw [show o * x * o⁻¹ = x * (x⁻¹ * o * x) * o⁻¹ by group]
        exact mul_mem (mul_mem (mem_sup_left hx) (mem_sup_right h1)) (mem_sup_right (inv_mem ho))
      · intro x hx
        exact mem_sup_right (mul_mem (mul_mem ho hx) (inv_mem ho))
    refine .step (sup_le_sup_right hAM O) ?_ (ih hO)
    rw [normal_subgroupOf_iff (sup_le_sup_right hAM O)]
    intro x k hx hk
    exact (mem_normalizer_iff.mp (hnorm hk) x).mp hx

theorem open_of_isSubnormal {C N : Subgroup X} (hNC : N ≤ C) (h : (N.subgroupOf C).IsSubnormal) :
    Open.IsSubnormal N C :=
  (Open.IsSubnormal.iff_subgroupOf hNC).2 h

theorem isSubnormal_of_open {N C : Subgroup X} (h : Open.IsSubnormal N C) :
    (N.subgroupOf C).IsSubnormal :=
  h.subgroupOf

theorem open_map {Y : Type} [Group Y] (f : X →* Y) {H K : Subgroup X}
    (h : Open.IsSubnormal H K) : Open.IsSubnormal (H.map f) (K.map f) :=
  h.map f

theorem map_pPrimeCore_le_coreActionKernel (J : Subgroup X) :
    (pPrimeCore 2 ↥J).map J.subtype ≤ coreActionKernel J := by
  rintro _ ⟨w, hw, rfl⟩
  refine mem_coreActionKernel.mpr ⟨le_normalizer w.2, fun j hj => ?_⟩
  have h1 : (⟨j, hj⟩ : ↥J)⁻¹ * w⁻¹ * ⟨j, hj⟩ * w ∈ pPrimeCore 2 ↥J := by
    refine mul_mem ?_ hw
    have := (inferInstance : (pPrimeCore 2 ↥J).Normal).conj_mem w⁻¹ (inv_mem hw)
      (⟨j, hj⟩ : ↥J)⁻¹
    rwa [inv_inv] at this
  exact ⟨_, h1, rfl⟩

theorem normal_hat {a : X} {J : Subgroup X}
    (hCJ : centralizer ({a} : Set X) ≤ normalizer (J : Set X)) :
    ((centralizer ({a} : Set X) ⊓ coreActionKernel J).subgroupOf
      (centralizer ({a} : Set X))).Normal := by
  rw [normal_subgroupOf_iff inf_le_left]
  intro k c hk hc
  refine mem_inf.mpr ⟨mul_mem (mul_mem hc (mem_inf.mp hk).1) (inv_mem hc), ?_⟩
  have hkN : k ∈ normalizer (J : Set X) := hCJ (mem_inf.mp hk).1
  have hcN : c ∈ normalizer (J : Set X) := hCJ hc
  have h1 : (⟨k, hkN⟩ : normalizer (J : Set X)) ∈ (Eight.oddBarAction J).ker :=
    Eight.mem_ker_oddBarAction.mpr (mem_inf.mp hk).2
  have h2 : (⟨c, hcN⟩ * ⟨k, hkN⟩ * (⟨c, hcN⟩ : normalizer (J : Set X))⁻¹ :
      normalizer (J : Set X)) ∈ (Eight.oddBarAction J).ker :=
    (inferInstance : (Eight.oddBarAction J).ker.Normal).conj_mem _ h1 _
  exact Eight.mem_ker_oddBarAction.mp h2

variable [Finite X]

theorem exists_mem_centralizer {J : Subgroup X} {z c : X} (hzJ : z ∈ J) (hzz : z * z = 1)
    (hc : c ∈ coreActionKernel J) :
    ∃ m ∈ (pPrimeCore 2 ↥J).map J.subtype, c * m⁻¹ ∈ centralizer ({z} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcN, hcJ⟩ := mem_coreActionKernel.mp hc
  have hvJ : c⁻¹ * z * c ∈ J := by
    have := (mem_normalizer_iff.mp (inv_mem hcN) z).mp hzJ
    rwa [inv_inv] at this
  have hu : IsPGroup 2 (zpowers (⟨z, hzJ⟩ : ↥J)) :=
    GrSLit.ONanBal.isPGroup_zpowers_of_pow_two (k := 1) (Subtype.ext (by simpa [sq] using hzz))
  have hv : IsPGroup 2 (zpowers (⟨c⁻¹ * z * c, hvJ⟩ : ↥J)) := by
    refine GrSLit.ONanBal.isPGroup_zpowers_of_pow_two (k := 1) (Subtype.ext ?_)
    change (c⁻¹ * z * c) ^ 2 ^ 1 = 1
    rw [pow_one, sq, show c⁻¹ * z * c * (c⁻¹ * z * c) = c⁻¹ * (z * z) * c by group, hzz, mul_one,
      inv_mul_cancel]
  have huv : (⟨z, hzJ⟩ : ↥J)⁻¹ * ⟨c⁻¹ * z * c, hvJ⟩ ∈ pPrimeCore 2 ↥J := by
    obtain ⟨w, hw, hwe⟩ := hcJ z hzJ
    have : w = (⟨z, hzJ⟩ : ↥J)⁻¹ * ⟨c⁻¹ * z * c, hvJ⟩ := by
      apply Subtype.ext
      change (w : X) = z⁻¹ * (c⁻¹ * z * c)
      rw [show z⁻¹ * (c⁻¹ * z * c) = z⁻¹ * c⁻¹ * z * c by group]
      exact hwe
    rw [← this]
    exact hw
  obtain ⟨m, hm, hmv⟩ := GrSLit.ONanBal.exists_conj_of_inv_mul_mem
    (Nat.coprime_two_left.1 pPrimeCore_coprime_card) hu hv huv
  refine ⟨(m : X), mem_map_of_mem _ hm, ?_⟩
  have h1 : (m : X) * (c⁻¹ * z * c) * (m : X)⁻¹ = z := congrArg Subtype.val hmv
  rw [mem_centralizer_singleton_iff]
  calc c * (m : X)⁻¹ * z = c * (m : X)⁻¹ * ((m : X) * (c⁻¹ * z * c) * (m : X)⁻¹) := by rw [h1]
    _ = z * (c * (m : X)⁻¹) := by group

theorem isSubnormal_sup {a z : X} {J N : Subgroup X}
    (hJt : IsSec8JType (↥J ⧸ pPrimeCore 2 ↥J) 3 1) (hJa : J ≤ centralizer ({a} : Set X))
    (hCJ : centralizer ({a} : Set X) ≤ normalizer (J : Set X)) (hzJ : z ∈ J) (hzz : z * z = 1)
    (hz1 : z ≠ 1) (hNs : Open.IsSubnormal N (centralizer ({a} : Set X) ⊓ centralizer ({z} : Set X)))
    (eN : ↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, ZMod 3)) :
    Open.IsSubnormal (N ⊔ (pPrimeCore 2 ↥J).map J.subtype) (centralizer ({a} : Set X)) := by
  set Oj := (pPrimeCore 2 ↥J).map J.subtype with hOj
  set Ch := centralizer ({a} : Set X) ⊓ coreActionKernel J with hCh
  have hNX := le_of_open hNs
  have hNK : N ≤ coreActionKernel J := le_coreActionKernel hJt hzJ hzz hz1
    (hNX.trans (inf_le_left.trans hCJ)) (hNX.trans inf_le_right) eN
  have hNCh : N ≤ Ch ⊓ centralizer ({z} : Set X) :=
    le_inf (le_inf (hNX.trans inf_le_left) hNK) (hNX.trans inf_le_right)
  have hOCh : Oj ≤ Ch :=
    le_inf ((map_subtype_le _).trans hJa) (map_pPrimeCore_le_coreActionKernel J)
  have hN1 : Open.IsSubnormal N (Ch ⊓ centralizer ({z} : Set X)) := by
    have h1 := open_inf hNs (Ch ⊓ centralizer ({z} : Set X))
    rwa [inf_eq_left.mpr hNCh, inf_eq_right.mpr (inf_le_inf_right _ inf_le_left)] at h1
  have hnO : Ch ⊓ centralizer ({z} : Set X) ≤ normalizer (Oj : Set X) :=
    (inf_le_left.trans inf_le_left).trans
      (hCJ.trans (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J _))
  have hN2 := open_sup hN1 hnO
  have hsup : (Ch ⊓ centralizer ({z} : Set X)) ⊔ Oj = Ch := by
    refine le_antisymm (sup_le inf_le_left hOCh) fun c hc => ?_
    obtain ⟨m, hm, hcm⟩ := exists_mem_centralizer hzJ hzz (mem_inf.mp hc).2
    have hmCh : m⁻¹ ∈ Ch := inv_mem (hOCh hm)
    rw [show c = c * m⁻¹ * m by group]
    exact mul_mem (mem_sup_left (mem_inf.mpr ⟨mul_mem hc hmCh, hcm⟩)) (mem_sup_right hm)
  rw [hsup] at hN2
  exact open_trans hN2 (.step inf_le_left (normal_hat hCJ) (.refl _))

theorem nonempty_quotient_sup_equiv {J N : Subgroup X} (hNJ : N ≤ normalizer (J : Set X)) :
    Nonempty (↥(N ⊔ (pPrimeCore 2 ↥J).map J.subtype) ⧸
      pPrimeCore 2 ↥(N ⊔ (pPrimeCore 2 ↥J).map J.subtype) ≃* ↥N ⧸ pPrimeCore 2 ↥N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Oj := (pPrimeCore 2 ↥J).map J.subtype with hOj
  set A := N ⊔ Oj with hA
  have hNO : N ≤ normalizer (Oj : Set X) :=
    hNJ.trans (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J _)
  have hAO : A ≤ normalizer (Oj : Set X) := sup_le hNO le_normalizer
  have hOn : (Oj.subgroupOf A).Normal := by
    rw [normal_subgroupOf_iff le_sup_right]
    intro h k hh hk
    exact (mem_normalizer_iff.mp (hAO hk) h).mp hh
  have hOodd : Odd (Nat.card (Oj.subgroupOf A)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact UnbalancedGS.odd_card_map_pPrimeCore_two J
  set f₁ := QuotientGroup.mk' (Oj.subgroupOf A) with hf₁
  have hf₁s : Function.Surjective f₁ := QuotientGroup.mk'_surjective _
  have hk₁ : f₁.ker ≤ pPrimeCore 2 ↥A := by
    rw [hf₁, QuotientGroup.ker_mk']
    exact UnbalancedGS.le_pPrimeCore_two_of_normal_odd hOn hOodd
  obtain ⟨e₁⟩ := HarrisLit.T1.nonempty_quotient_pPrimeCore_equiv_of_ker_le f₁ hf₁s hk₁
  set f₂ : ↥N →* ↥A ⧸ Oj.subgroupOf A := f₁.comp (inclusion le_sup_left) with hf₂
  have htop : N.subgroupOf A ⊔ Oj.subgroupOf A = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hf₂s : Function.Surjective f₂ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Oj.subgroupOf A) y
    have hx : x ∈ ((N.subgroupOf A ⊔ Oj.subgroupOf A : Subgroup ↥A) : Set ↥A) := by
      rw [htop]
      trivial
    rw [mul_normal] at hx
    obtain ⟨n, hn, o, ho, rfl⟩ := hx
    refine ⟨⟨(n : X), mem_subgroupOf.mp hn⟩, ?_⟩
    have ho1 : QuotientGroup.mk' (Oj.subgroupOf A) o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
    rw [map_mul, ho1, mul_one]
    rfl
  have hk₂ : f₂.ker ≤ pPrimeCore 2 ↥N := by
    intro n hn
    have h1 : (n : X) ∈ Oj := by
      have h2 : inclusion le_sup_left n ∈ Oj.subgroupOf A := by
        rw [← QuotientGroup.eq_one_iff]
        exact hn
      exact h2
    obtain ⟨w, hw, hwn⟩ := UnbalancedGS.inf_le_map_pPrimeCore_two hNO
      (UnbalancedGS.odd_card_map_pPrimeCore_two J) (mem_inf.mpr ⟨n.2, h1⟩)
    rw [show n = w from Subtype.ext hwn.symm]
    exact hw
  obtain ⟨e₂⟩ := HarrisLit.T1.nonempty_quotient_pPrimeCore_equiv_of_ker_le f₂ hf₂s hk₂
  exact ⟨e₁.trans e₂.symm⟩

end Eight2.Three

end CFSG.ComponentClassification.GSThmB
