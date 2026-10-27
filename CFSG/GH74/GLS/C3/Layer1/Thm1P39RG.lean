module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RF
public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RStmt
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3L34
import CFSG.GH74.GLS.C3.Layer1.Thm1L3Aux
import CFSG.GH74.GLS.C3.Layer1.Th2P72cR5
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelLeaves

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P39R

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.GH74.GLS.C3.Layer1

variable {G : Type} [Group G]

theorem exists_conj_centralizing [Finite G] {J V S₂ : Subgroup G} {f₁ x : G}
    (hJC : J ≤ centralizer ({f₁} : Set G))
    (hJn : ∀ c ∈ centralizer ({f₁} : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (hV : IsSylowOf 2 V (centralizer ({f₁} : Set G)))
    (hxC : x ∈ centralizer ({f₁} : Set G)) (hx2 : x * x = 1)
    (hS₂ : IsSylowOf 2 S₂ J) (hxS : ∀ s ∈ S₂, x * s = s * x) :
    ∃ c ∈ centralizer ({f₁} : Set G), c * x * c⁻¹ ∈ V ∧
      ∀ p ∈ V ⊓ J, (c * x * c⁻¹) * p = p * (c * x * c⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := V ⊓ J with hP
  have hVC : V ≤ centralizer ({f₁} : Set G) := hV.le
  have hCN : centralizer ({f₁} : Set G) ≤ normalizer ((J : Subgroup G) : Set G) :=
    fun c hc => Thm1L3.mem_normalizer_of_conj_le (hJn c hc)
  have hVN : V ≤ normalizer (P : Set G) := fun v hv =>
    Thm1L3.mem_normalizer_of_conj_le fun p hp =>
      ⟨V.mul_mem (V.mul_mem hv hp.1) (V.inv_mem hv), hJn v (hVC hv) p hp.2⟩
  have hPsyl : IsSylowOf 2 P J :=
    hV.inf_of_le_normalizer hJC (fun c hc => hCN hc)
  obtain ⟨j, hjJ, hj⟩ := hPsyl.exists_mem_conj hS₂
  have hx₃P : ∀ p ∈ P, (j⁻¹ * x * j) * p = p * (j⁻¹ * x * j) := by
    intro p hp
    have hy : j * p * j⁻¹ ∈ S₂ := (hj _).2 (by simpa [mul_assoc] using hp)
    have h1 := hxS _ hy
    calc (j⁻¹ * x * j) * p = j⁻¹ * (x * (j * p * j⁻¹)) * j := by group
      _ = j⁻¹ * ((j * p * j⁻¹) * x) * j := by rw [h1]
      _ = p * (j⁻¹ * x * j) := by group
  set Ns : Subgroup G := centralizer ({f₁} : Set G) ⊓ normalizer (P : Set G) with hNs
  have hVNs : V ≤ Ns := le_inf hVC hVN
  have hVsyl : IsSylowOf 2 V Ns := hV.of_le hVNs inf_le_left
  have hx₃C : j⁻¹ * x * j ∈ centralizer ({f₁} : Set G) := by
    have hjC : j ∈ centralizer ({f₁} : Set G) := hJC hjJ
    exact (centralizer ({f₁} : Set G)).mul_mem
      ((centralizer ({f₁} : Set G)).mul_mem ((centralizer ({f₁} : Set G)).inv_mem hjC) hxC) hjC
  have hx₃N : j⁻¹ * x * j ∈ normalizer (P : Set G) :=
    Thm1L3.mem_normalizer_of_conj_le fun p hp => by
      have := hx₃P p hp
      have e : (j⁻¹ * x * j) * p * (j⁻¹ * x * j)⁻¹ = p := by
        calc (j⁻¹ * x * j) * p * (j⁻¹ * x * j)⁻¹ = (p * (j⁻¹ * x * j)) * (j⁻¹ * x * j)⁻¹ := by
              rw [this]
          _ = p := by group
      rw [e]
      exact hp
  have hx₃Ns : j⁻¹ * x * j ∈ Ns := ⟨hx₃C, hx₃N⟩
  have hx₃2 : (j⁻¹ * x * j) * (j⁻¹ * x * j) = 1 := by
    calc (j⁻¹ * x * j) * (j⁻¹ * x * j) = j⁻¹ * (x * x) * j := by group
      _ = 1 := by rw [hx2]; group
  have hzp : IsPGroup 2 ↥(zpowers (j⁻¹ * x * j)) :=
    Thm1.isPGroup_zpowers_of_pow_eq_one ⟨1, by simpa [sq] using hx₃2⟩
  obtain ⟨V', hxV', hV'N, hV'p, hV'idx⟩ :=
    P34.exists_sylow_ge (N := Ns) (zpowers_le.2 hx₃Ns) hzp
  have hV' : IsSylowOf 2 V' Ns := isSylowOf_iff.2 ⟨hV'N, hV'p, hV'idx⟩
  obtain ⟨n, hnNs, hn⟩ := hVsyl.exists_mem_conj hV'
  have hnV : n⁻¹ * (j⁻¹ * x * j) * n ∈ V := (hn _).1 (hxV' (mem_zpowers _))
  have hnC : n ∈ centralizer ({f₁} : Set G) := hnNs.1
  have hnN : n ∈ normalizer (P : Set G) := hnNs.2
  refine ⟨n⁻¹ * j⁻¹, ?_, ?_, ?_⟩
  · exact (centralizer ({f₁} : Set G)).mul_mem ((centralizer ({f₁} : Set G)).inv_mem hnC)
      ((centralizer ({f₁} : Set G)).inv_mem (hJC hjJ))
  · have e : n⁻¹ * j⁻¹ * x * (n⁻¹ * j⁻¹)⁻¹ = n⁻¹ * (j⁻¹ * x * j) * n := by group
    rw [e]
    exact hnV
  · intro p hp
    have hnp : n * p * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hnN p).1 hp
    have h1 := hx₃P _ hnp
    have e : n⁻¹ * j⁻¹ * x * (n⁻¹ * j⁻¹)⁻¹ = n⁻¹ * (j⁻¹ * x * j) * n := by group
    rw [e]
    calc n⁻¹ * (j⁻¹ * x * j) * n * p = n⁻¹ * ((j⁻¹ * x * j) * (n * p * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * p * n⁻¹) * (j⁻¹ * x * j)) * n := by rw [h1]
      _ = p * (n⁻¹ * (j⁻¹ * x * j) * n) := by group

theorem not_isSolvable_of_l2 {F : Type} [Field F] [Finite F] {K : Type} [Group K] (hF : L2Field F)
    (e : K ≃* L2 F) : ¬ Group.IsSolvable K := by
  have h3 : 3 < Nat.card F := hF.2
  have hp : Group.IsPerfect (PSL2 F) := psl2_isPerfect_of_card_gt_three F h3
  let e' : K ≃* PSL2 F := e.trans (L2.equivPSL F)
  have hX : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := e'.symm.toMonoidHom) e'.symm.surjective
  have : Nontrivial K := e'.symm.injective.nontrivial
  exact Group.IsPerfect.not_isSolvable K

theorem not_isSolvable_of_hasL2Model {K : Type} [Group K] {r : ℕ} (hr : Odd r)
    (h : HasL2Model K (fun q => q = r)) : ¬ Group.IsSolvable K := by
  obtain ⟨F, _, _, hF, -, ⟨e⟩⟩ :=
    exists_l2Field_of_hasL2Model_pred (P := fun q => q = r) (fun q hq => hq ▸ hr) h
  exact not_isSolvable_of_l2 hF e


theorem pLayerOf_conj_ne_bot [Finite G] {J : Subgroup G} {f₁ x c : G}
    (hcC : c ∈ centralizer ({f₁} : Set G))
    (hJn : ∀ c ∈ centralizer ({f₁} : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (hl : pLayerOf 2 (J ⊓ centralizer ({x} : Set G)) ≠ ⊥) :
    pLayerOf 2 (J ⊓ centralizer ({c * x * c⁻¹} : Set G)) ≠ ⊥ := by
  have hJc : Stage1.Thm3.Sec4.cmap c J = J := by
    ext y
    rw [Stage1.Thm3.Sec4.mem_cmap]
    constructor
    · intro h
      have := hJn c hcC _ h
      simpa [mul_assoc] using this
    · intro hy
      have := hJn c⁻¹ ((centralizer ({f₁} : Set G)).inv_mem hcC) y hy
      simpa [mul_assoc] using this
  have hcen : Subgroup.map (MulAut.conj c).toMonoidHom (centralizer ({x} : Set G)) =
      centralizer ({c * x * c⁻¹} : Set G) := Stage1.Thm2.Recip.map_centralizer_singleton_conj x c
  have heq : J ⊓ centralizer ({c * x * c⁻¹} : Set G) =
      Stage1.Thm3.Sec4.cmap c (J ⊓ centralizer ({x} : Set G)) := by
    rw [← hcen]
    conv_lhs => rw [← hJc]
    exact (Subgroup.map_inf J _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).symm
  rw [heq, Stage1.Thm3.Sec4.pLayerOf_cmap]
  intro hbot
  apply hl
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c).injective).1 hbot

theorem thm1_L39_third_of_rel (hL32 : B_thm1_L32'_rel) (hP31c : B_thm1_P31c_rel) :
    B_thm1_L39_third_rel := by
  intro G _ _ hG hN x y K T V₁ W₁ f₁ z cfg hlt w₁ hw₁ hcard hnotA7 h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJc, hJn, r, hrodd, hr5, hI, hKshape, hJshape, -⟩ :=
    hL32 G hG hN x y K f₁ cfg.fmax h5
  have hKL2 : HasL2Model (kBar K) (fun q => q = r ^ 2) :=
    hKshape.resolve_right (fun h => hnotA7 h.2)
  have hIJ : layerI K f₁ ≤ pumpJ K f₁ := Thm1.layerI_le_pumpJ K f₁
  have hJ2 : HasL2Model (kBar (pumpJ K f₁)) (fun q => q = r ^ 2) := by
    rcases hJshape with h | h | h
    · exact absurd (Thm1L34.sup_eq_of_hasL2Model hIJ hI h) (ne_of_lt hlt)
    · exact h
    · exfalso
      have h1 := Thm1L34.card_kBar_of_alt7 h
      rw [hcard, Thm1L34.card_kBar_of_hasL2Model hKL2] at h1
      exact Thm1L34.ordA_one_ne_2520 hrodd.pow h1
  obtain ⟨F, _, _, hF, hFq, ⟨e⟩⟩ :=
    exists_l2Field_of_hasL2Model_pred (P := fun q => q = r ^ 2) (fun q hq => hq ▸ hrodd.pow) hJ2
  have h9 : Nat.card F ≠ 9 := by
    have : 5 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hr5 2
    omega
  have hSyl : IsSylowOf 2 (zpowers f₁) (CxK f₁ (pumpJ K f₁)) :=
    hP31c G hG hN f₁ w₁ _ hw₁ (not_hasL2Model_five_of_sq hrodd hr5 hJ2)
  have hxC : x ∈ centralizer ({f₁} : Set G) := mem_centralizer_singleton_iff.2 cfg.hxf
  have hxf : x ≠ f₁ := fun h => cfg.mem.2.2.2.1 h.symm
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [cfg.hx2, sq] at this
  have hIx : ∀ c ∈ layerI K f₁, x * c = c * x := fun c hc =>
    (mem_centralizer_singleton_iff.1 (cfg.hKx (layerI_le_K K f₁ hc))).symm
  have hIns : ¬ Group.IsSolvable (kBar (layerI K f₁)) := not_isSolvable_of_hasL2Model hrodd hI
  obtain ⟨e', hσ, hσ2⟩ :=
    exists_fieldAut_actHom hIJ hJn hxC cfg.hx2 cfg.hf2 hxf hSyl hIx hIns hF e
  obtain ⟨S₂, hS₂, hxS⟩ := exists_isSylowOf_centralized hJn hxC cfg.hx2 hF e' hσ hσ2
  obtain ⟨c, hcC, hcV, hcP⟩ :=
    exists_conj_centralizing hJc.1 hJn cfg.sylowV hxC hxx hS₂ hxS
  have hord : orderOf (c * x * c⁻¹) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj c) x
    rw [MulAut.conj_apply] at h
    rw [h]
    exact cfg.hx2
  have hne : c * x * c⁻¹ ≠ f₁ := by
    intro h
    apply hxf
    have hcf : c * f₁ * c⁻¹ = f₁ := by
      have := mem_centralizer_singleton_iff.1 hcC
      rw [this]
      group
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = c⁻¹ * (c * f₁ * c⁻¹) * c := by rw [h, hcf]
      _ = f₁ := by group
  have hlayer : pLayerOf 2 (pumpJ K f₁ ⊓ centralizer ({c * x * c⁻¹} : Set G)) ≠ ⊥ :=
    pLayerOf_conj_ne_bot hcC hJn
      (Thm1.layer_ne_bot_of_good hJn hxC cfg.hx2 (Thm1.goodC_of_fieldAut hF h9 e' hσ hσ2))
  exact ⟨c * x * c⁻¹, isConj_iff.2 ⟨c, rfl⟩, hcV, hord, hcP, hne, hlayer⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1P39R
