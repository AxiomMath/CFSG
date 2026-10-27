module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBWit
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJKer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement IsMulCommutative

theorem y7c_gen_of_fpf {Γ : Type} [Group Γ] [Finite Γ] {W J : Subgroup Γ}
    (hW : IsElemAbelian 2 W) {k : Γ} (hk : k ∈ J) (hkW : ∀ m ∈ W, k * m * k⁻¹ ∈ W)
    (hfpf : ∀ m ∈ W, k * m * k⁻¹ = m → m = 1) : W ≤ ⁅J, W⁆ := by
  haveI : IsMulCommutative ↥W := hW.1
  let φ : ↥W →* ↥W :=
    { toFun := fun x => ⟨k * (x : Γ) * k⁻¹, hkW x x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp only [Subgroup.coe_mul]; group }
  let ψ : ↥W →* ↥W :=
    { toFun := fun x => φ x * x⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        show φ (x * y) * (x * y)⁻¹ = (φ x * x⁻¹) * (φ y * y⁻¹)
        rw [map_mul φ x y, mul_inv_rev]
        ac_rfl }
  have hker : ∀ x : ↥W, ψ x = 1 → x = 1 := by
    intro x hx
    have hx' : φ x * x⁻¹ = 1 := hx
    have hφ : φ x = x := by
      calc φ x = (φ x * x⁻¹) * x := by group
        _ = 1 * x := by rw [hx']
        _ = x := one_mul x
    have hfix : k * (x : Γ) * k⁻¹ = (x : Γ) := congrArg Subtype.val hφ
    exact Subtype.ext (hfpf (x : Γ) x.2 hfix)
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : ψ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hker (x * y⁻¹) h1)
  intro m hm
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj ⟨m, hm⟩
  have hy' : (ψ y : Γ) = m := congrArg Subtype.val hy
  rw [← hy']
  have hval : (ψ y : Γ) = ⁅k, (y : Γ)⁆ := by
    change ((φ y * y⁻¹ : ↥W) : Γ) = ⁅k, (y : Γ)⁆
    rw [commutatorElement_def]
    rfl
  rw [hval]
  exact Subgroup.commutator_mem_commutator hk y.2

theorem y7c_fpf_of_cent_t {Γ : Type} [Group Γ] {W A : Subgroup Γ} (hW : IsElemAbelian 2 W)
    {t k : Γ} (ht2 : t ^ 2 = 1) (htW : ∀ m ∈ W, t * m * t⁻¹ ∈ W)
    (hcentA : ∀ m ∈ W, m * t = t * m → m ∈ A) (hkt : k * t = t * k)
    (hkW : ∀ m ∈ W, k * m * k⁻¹ ∈ W) (hkA : ∀ a ∈ A, k * a * k⁻¹ = a → a = 1) :
    ∀ m ∈ W, k * m * k⁻¹ = m → m = 1 := by
  intro m hm hfix
  obtain ⟨hcW, hct⟩ := y7c_comm_cent_t hW ht2 htW hm
  have hcA : ⁅m, t⁆ ∈ A := hcentA ⁅m, t⁆ hcW hct
  have hkt' : k * t * k⁻¹ = t := by rw [hkt, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : k * ⁅m, t⁆ * k⁻¹ = ⁅m, t⁆ := by
    have h := map_commutatorElement (MulAut.conj k) m t
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply] at h
    rw [h, hfix, hkt']
  have hc1 : ⁅m, t⁆ = 1 := hkA ⁅m, t⁆ hcA hconj
  exact hkA m (hcentA m hm (commutatorElement_eq_one_iff_mul_comm.mp hc1)) hfix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7c_zL_le_normIn {X : Subgroup G} (hX : X ≤ L) : zL L ≤ normIn L X := by
  intro z hz
  obtain ⟨hzL, hzC⟩ := mem_zL_iff.mp hz
  refine Subgroup.mem_inf.mpr ⟨hzL, ?_⟩
  exact Subgroup.centralizer_le_normalizer (X : Set G)
    (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_iff.mp hzC x (hX hx))

private theorem y7c_NLB_le_NLF {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normIn L s.fr.B ≤ normIn L s.fr.F := by
  obtain ⟨⟨_, _, _⟩, ⟨_, h3b, _, _, _, _⟩, _, _⟩ := hH.hLF.fact18
  exact h3b

private theorem y7c_le_NC3 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normIn L s.fr.B ≤ normalizer (C3 s : Set G) := by
  intro g hg
  obtain ⟨hgL, -⟩ := Subgroup.mem_inf.mp hg
  have hgH : g ∈ s.H := s3_L_le_H s hH.hS hgL
  have hgt : g * s.t * g⁻¹ = s.t :=
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp hgH)
  have hgF : g ∈ normalizer (s.fr.F : Set G) :=
    (Subgroup.mem_inf.mp (y7c_NLB_le_NLF hH hg)).2
  have hFt : g ∈ normalizer ((s.fr.F ⊔ zpowers s.t : Subgroup G) : Set G) :=
    mem_normalizer_sup hgF (mem_normalizer_zpowers hgt)
  have hcent : g ∈ normalizer
      ((centIn (normalizer ((s.fr.F ⊔ zpowers s.t : Subgroup G) : Set G)) s.fr.F :
        Subgroup G) : Set G) := by
    rw [centIn]
    exact mem_normalizer_inf (mem_normalizer_normalizer hFt) (mem_normalizer_centralizer hgF)
  have hHF : g ∈ normalizer ((normIn s.H s.fr.F : Subgroup G) : Set G) := by
    rw [normIn]
    exact mem_normalizer_inf (Subgroup.le_normalizer hgH) (mem_normalizer_normalizer hgF)
  have hpc : g ∈ normalizer ((pCoreOf 2
      ⁅centIn (normalizer ((s.fr.F ⊔ zpowers s.t : Subgroup G) : Set G)) s.fr.F,
        normIn s.H s.fr.F⁆ : Subgroup G) : Set G) :=
    mem_normalizer_pCoreOf (mem_normalizer_commutator hcent hHF)
  rw [C3]
  exact mem_normalizer_sup hpc hFt

private theorem y7c_le_NM3 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normIn L s.fr.B ≤ normalizer (M3 s : Set G) := by
  intro g hg
  obtain ⟨hgL, -⟩ := Subgroup.mem_inf.mp hg
  have hgF : g ∈ normalizer (s.fr.F : Set G) :=
    (Subgroup.mem_inf.mp (y7c_NLB_le_NLF hH hg)).2
  have hgC3 : g ∈ normalizer (C3 s : Set G) := y7c_le_NC3 hH hg
  have hgNL : g ∈ normalizer (L : Set G) := Subgroup.le_normalizer hgL
  have hgNF : g ∈ normalizer ((normIn L s.fr.F : Subgroup G) : Set G) := by
    rw [normIn]
    exact mem_normalizer_inf hgNL (mem_normalizer_normalizer hgF)
  have hcomm : g ∈ normalizer ((⁅C3 s, normIn L s.fr.F⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator hgC3 hgNF
  rw [M3]
  exact mem_normalizer_sup hcomm hgF

private theorem y7c_le_NX7 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normIn L s.fr.B ≤ normalizer (X7 s : Set G) := by
  intro g hg
  obtain ⟨_, hgB⟩ := Subgroup.mem_inf.mp hg
  have hgC3 : g ∈ normalizer (C3 s : Set G) := y7c_le_NC3 hH hg
  have hgM3 : g ∈ normalizer (M3 s : Set G) := y7c_le_NM3 hH hg
  have hBC3 : g ∈ normalizer ((s.fr.B ⊔ C3 s : Subgroup G) : Set G) :=
    mem_normalizer_sup hgB hgC3
  have hBM3 : g ∈ normalizer ((s.fr.B ⊔ M3 s : Subgroup G) : Set G) :=
    mem_normalizer_sup hgB hgM3
  rw [X7]
  exact mem_normalizer_inf
    (mem_normalizer_inf (mem_normalizer_normalizer hBC3) (mem_normalizer_normalizer hgM3))
    (mem_normalizer_centralizerSection hBM3 hgM3)

private theorem y7c_le_NC7 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normIn L s.fr.B ≤ normalizer (C7 s : Set G) := by
  intro g hg
  obtain ⟨hgL, hgB⟩ := Subgroup.mem_inf.mp hg
  have hgH : g ∈ s.H := s3_L_le_H s hH.hS hgL
  have hgX7 : g ∈ normalizer (X7 s : Set G) := y7c_le_NX7 hH hg
  have hgC3 : g ∈ normalizer (C3 s : Set G) := y7c_le_NC3 hH hg
  have hgNHB : g ∈ normalizer ((normIn s.H s.fr.B : Subgroup G) : Set G) := by
    rw [normIn]
    exact mem_normalizer_inf (Subgroup.le_normalizer hgH) (mem_normalizer_normalizer hgB)
  have hcomm : g ∈ normalizer ((⁅X7 s, normIn s.H s.fr.B⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator hgX7 hgNHB
  have hBC3 : g ∈ normalizer ((s.fr.B ⊔ C3 s : Subgroup G) : Set G) :=
    mem_normalizer_sup hgB hgC3
  rw [C7]
  exact mem_normalizer_sup (mem_normalizer_pCoreOf hcomm) hBC3

theorem y7c_exists_yA {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ k ∈ normIn L s.fr.A ⊓ normIn L s.fr.F, IsPGroup 3 ↥(zpowers k) ∧ k ≠ 1 := by
  obtain ⟨⟨_, _, _⟩, ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _, _⟩, ⟨_, _, _, _, h5e, _⟩⟩ := hH.hLF.fact18
  have hAL : s.fr.A ≤ L := s3_A_le_L s
  have hFL : s.fr.F ≤ L := (s3_F_le_A s).trans hAL
  have hAF : s.fr.A ≤ normIn L s.fr.F := (s3_A_le_S s).trans (y54_S_le_N hH)
  have hKN : zL L ⊔ s.fr.A ≤ normIn L s.fr.A ⊓ normIn L s.fr.F :=
    sup_le (le_inf (y7c_zL_le_normIn hAL) (y7c_zL_le_normIn hFL))
      (le_inf (le_inf hAL Subgroup.le_normalizer) hAF)
  obtain ⟨k, hk, hk3, hkz⟩ := exists_threeElem_not_mem_of_secProp_perm3 hKN h5e
  exact ⟨k, hk, hk3, fun hk1 => hkz (by rw [hk1]; exact (zL L ⊔ s.fr.A).one_mem)⟩

theorem y7c_exists_yB {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ k ∈ normIn L s.fr.B, IsPGroup 3 ↥(zpowers k) ∧ k ≠ 1 := by
  obtain ⟨⟨_, _, _⟩, ⟨_, _, _, h3d, _, _⟩, _, _⟩ := hH.hLF.fact18
  obtain ⟨k, hk, hk3, hkz⟩ := h3d
  exact ⟨k, hk, hk3, fun hk1 => hkz (by rw [hk1]; exact (zL L).one_mem)⟩

theorem y7c_NLB_le_NM7 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normIn L s.fr.B ≤ normalizer (M7 s : Set G) := by
  intro g hg
  obtain ⟨hgL, hgB⟩ := Subgroup.mem_inf.mp hg
  have hgM3 : g ∈ normalizer (M3 s : Set G) := y7c_le_NM3 hH hg
  have hgC7 : g ∈ normalizer (C7 s : Set G) := y7c_le_NC7 hH hg
  have hgNL : g ∈ normalizer (L : Set G) := Subgroup.le_normalizer hgL
  have hgNLB : g ∈ normalizer ((normIn L s.fr.B : Subgroup G) : Set G) := by
    rw [normIn]
    exact mem_normalizer_inf hgNL (mem_normalizer_normalizer hgB)
  have hcomm : g ∈ normalizer ((⁅C7 s, normIn L s.fr.B⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator hgC7 hgNLB
  have hBM3 : g ∈ normalizer ((s.fr.B ⊔ M3 s : Subgroup G) : Set G) :=
    mem_normalizer_sup hgB hgM3
  rw [M7]
  exact mem_normalizer_sup hcomm hBM3

end CFSG.OddStandard.HigherRank.YamadaG23
