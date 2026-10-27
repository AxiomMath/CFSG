module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Fine
public import CFSG.GH74.GLS.C3.Layer1.St1P89Tools
public import CFSG.GH74.GLS.C3.Layer1.BackBasic
public import CFSG.GH74.GLS.C3.Layer1.Back91Setup
public import CFSG.GH74.GLS.TwoThin.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L3

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_le [Finite G] {H : Subgroup G} {c : G}
    (h : ∀ j ∈ H, c * j * c⁻¹ ∈ H) : c ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj c).toMonoidHom ≤ H := by
    rintro _ ⟨j, hj, rfl⟩
    simpa [MulAut.conj_apply] using h j hj
  have heq : H.map (MulAut.conj c).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj c).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq

theorem mem_cSec_of_centralizes_layer {I J : Subgroup G} (hsup : J = I ⊔ pPrimeCoreOf 2 J) {c : G}
    (hcJ : c ∈ normalizer (J : Set G)) (hcI : ∀ i ∈ I, c * i = i * c) :
    c ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  refine ⟨hcJ, TwoThin.mem_normalizer_pPrimeCoreOf hcJ, ?_⟩
  have hNn : ∀ k ∈ J, ∀ n ∈ pPrimeCoreOf 2 J, k * n * k⁻¹ ∈ pPrimeCoreOf 2 J := fun k hk n hn =>
    (Subgroup.mem_normalizer_iff.mp (Back.Setup91.mem_normalizer_pPrimeCoreOf_self hk) n).mp hn
  have hcN : ∀ n ∈ pPrimeCoreOf 2 J, c * n * c⁻¹ ∈ pPrimeCoreOf 2 J := fun n hn =>
    TwoThin.mul_mem_pPrimeCoreOf_of_mem_normalizer hcJ hn
  have hIJ : I ≤ J := le_sup_left.trans hsup.ge
  let S : Subgroup G :=
    { carrier := {k | k ∈ J ∧ ⁅k, c⁆ ∈ pPrimeCoreOf 2 J}
      one_mem' := ⟨J.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨haJ, ha⟩ ⟨hbJ, hb⟩
        refine ⟨J.mul_mem haJ hbJ, ?_⟩
        have h1 : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
          simp only [commutatorElement_def]; group
        rw [h1]
        exact (pPrimeCoreOf 2 J).mul_mem (hNn a haJ _ hb) ha
      inv_mem' := by
        rintro a ⟨haJ, ha⟩
        refine ⟨J.inv_mem haJ, ?_⟩
        have h1 : ⁅a⁻¹, c⁆ = a⁻¹ * (⁅a, c⁆)⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [h1]
        have := hNn a⁻¹ (J.inv_mem haJ) _ ((pPrimeCoreOf 2 J).inv_mem ha)
        simpa using this }
  have hIS : I ≤ S := fun i hi => ⟨hIJ hi, by
    have : ⁅i, c⁆ = 1 := by
      rw [commutatorElement_def, ← hcI i hi]; group
    rw [this]; exact (pPrimeCoreOf 2 J).one_mem⟩
  have hNS : pPrimeCoreOf 2 J ≤ S := fun n hn => ⟨Thm1.pPrimeCoreOf_le_self J hn, by
    have h1 : ⁅n, c⁆ = n * (c * n * c⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact (pPrimeCoreOf 2 J).mul_mem hn ((pPrimeCoreOf 2 J).inv_mem (hcN n hn))⟩
  intro k hk
  have hk' : k ∈ I ⊔ pPrimeCoreOf 2 J := by rw [← hsup]; exact hk
  exact (sup_le hIS hNS hk').2

theorem card_le_of_isPGroup_of_isSylowOf [Finite G] {V C T : Subgroup G} (hV : IsPGroup 2 ↥V)
    (hVC : V ≤ C) (hT : IsSylowOf 2 T C) : Nat.card ↥V ≤ Nat.card ↥T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hVS, hSC, hSp, hSidx⟩ := P34.exists_sylow_ge hVC hV
  have hS : IsSylowOf 2 S C := isSylowOf_iff.2 ⟨hSC, hSp, hSidx⟩
  calc Nat.card ↥V ≤ Nat.card ↥S := Subgroup.card_le_of_le hVS
    _ = Nat.card ↥T := by rw [hS.card_eq, hT.card_eq]

end CFSG.GH74.GLS.C3.Layer1.Thm1L3

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1

section Cfg

variable {G : Type} [Group G] {x y : G} {K T V W : Subgroup G} {f z : G}

theorem Cfg3.hu2 (cfg : Cfg3 x y K T V W f z) : Is2TerminalU2Triple x y K :=
  cfg.fmax.1.1.1.1

theorem Cfg3.hx2 (cfg : Cfg3 x y K T V W f z) : orderOf x = 2 := cfg.hu2.1.1.1

theorem Cfg3.hf2 (cfg : Cfg3 x y K T V W f z) : orderOf f = 2 := cfg.mem.2.1

theorem Cfg3.hKx (cfg : Cfg3 x y K T V W f z) : K ≤ centralizer ({x} : Set G) :=
  cfg.hu2.1.1.2.1

theorem Cfg3.hxf (cfg : Cfg3 x y K T V W f z) [Finite G] : x * f = f * x :=
  (mem_centralizer_singleton_iff.1 (cfg.setup.sylowT.le cfg.mem.1)).symm

theorem Cfg3.x_mem_T [Finite G] (cfg : Cfg3 x y K T V W f z) : x ∈ T :=
  Back.mem_of_isSylowOf_of_central cfg.setup.sylowT (mem_centralizer_singleton_iff.2 rfl)
    (fun _ hs => mem_centralizer_singleton_iff.1 hs) cfg.hx2

theorem Cfg3.x_mem_V [Finite G] (cfg : Cfg3 x y K T V W f z) : x ∈ V :=
  cfg.CTf_le x cfg.x_mem_T (cfg.hxf.symm)

theorem Cfg3.f_mem_V [Finite G] (cfg : Cfg3 x y K T V W f z) : f ∈ V :=
  Back.mem_of_isSylowOf_of_central cfg.sylowV (mem_centralizer_singleton_iff.2 rfl)
    (fun _ hs => mem_centralizer_singleton_iff.1 hs) cfg.hf2

theorem layerI_le_K (K : Subgroup G) (f : G) : layerI K f ≤ K :=
  (TwoThin.pLayerOf_le 2 _).trans inf_le_left

theorem layerI_le_centralizer (K : Subgroup G) (f : G) : layerI K f ≤ centralizer ({f} : Set G) :=
  (TwoThin.pLayerOf_le 2 _).trans inf_le_right

theorem Cfg3.x_mem_secD [Finite G] (cfg : Cfg3 x y K T V W f z)
    (hsup : pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f))
    (hJn : ∀ c ∈ centralizer ({f} : Set G), ∀ j ∈ pumpJ K f, c * j * c⁻¹ ∈ pumpJ K f) :
    x ∈ secD K f V := by
  refine ⟨cfg.x_mem_V, ?_⟩
  rw [← hsup]
  have hxC : x ∈ centralizer ({f} : Set G) := mem_centralizer_singleton_iff.2 cfg.hxf
  refine C3.Layer1.Thm1L3.mem_cSec_of_centralizes_layer hsup (C3.Layer1.Thm1L3.mem_normalizer_of_conj_le (hJn x hxC)) ?_
  intro i hi
  exact (mem_centralizer_singleton_iff.1 (cfg.hKx (layerI_le_K K f hi))).symm

theorem Cfg3.f_mem_secD [Finite G] (cfg : Cfg3 x y K T V W f z)
    (hsup : pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f))
    (hJn : ∀ c ∈ centralizer ({f} : Set G), ∀ j ∈ pumpJ K f, c * j * c⁻¹ ∈ pumpJ K f) :
    f ∈ secD K f V := by
  refine ⟨cfg.f_mem_V, ?_⟩
  rw [← hsup]
  have hfC : f ∈ centralizer ({f} : Set G) := mem_centralizer_singleton_iff.2 rfl
  refine C3.Layer1.Thm1L3.mem_cSec_of_centralizes_layer hsup (C3.Layer1.Thm1L3.mem_normalizer_of_conj_le (hJn f hfC)) ?_
  intro i hi
  exact (mem_centralizer_singleton_iff.1 (layerI_le_centralizer K f hi)).symm

theorem Cfg3.four_le_card_secD [Finite G] (cfg : Cfg3 x y K T V W f z)
    (hsup : pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f))
    (hJn : ∀ c ∈ centralizer ({f} : Set G), ∀ j ∈ pumpJ K f, c * j * c⁻¹ ∈ pumpJ K f) :
    4 ≤ Nat.card ↥(secD K f V) := by
  have hle : zpowers x ⊔ zpowers f ≤ secD K f V :=
    sup_le ((zpowers_le).2 (cfg.x_mem_secD hsup hJn)) ((zpowers_le).2 (cfg.f_mem_secD hsup hJn))
  have hx2 : x ^ 2 = 1 := by rw [← cfg.hx2]; exact pow_orderOf_eq_one x
  have hf2 : f ^ 2 = 1 := by rw [← cfg.hf2]; exact pow_orderOf_eq_one f
  have hx1 : x ≠ 1 := by
    intro h
    have := cfg.hx2
    rw [h, orderOf_one] at this
    omega
  have hf1 : f ≠ 1 := by
    intro h
    have := cfg.hf2
    rw [h, orderOf_one] at this
    omega
  have hne : x ≠ f := Ne.symm cfg.mem.2.2.2.1
  have hcard := P89.card_klein hx2 hf2 cfg.hxf hx1 hf1 hne
  calc 4 = Nat.card ↥(zpowers x ⊔ zpowers f) := hcard.symm
    _ ≤ Nat.card ↥(secD K f V) := Subgroup.card_le_of_le hle

end Cfg

end CFSG.GH74.GLS
