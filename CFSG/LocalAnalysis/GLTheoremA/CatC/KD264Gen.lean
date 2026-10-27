module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

variable {Y : Type} [Group Y]

@[expose] def conjKequiv (K : Subgroup Y) (hK : K.Normal) (y : Y) : K ≃* K where
  toFun k := ⟨y * k * y⁻¹, hK.conj_mem k.1 k.2 y⟩
  invFun k := ⟨y⁻¹ * k * y, by simpa using hK.conj_mem k.1 k.2 y⁻¹⟩
  left_inv k := by ext; simp [mul_assoc]
  right_inv k := by ext; simp [mul_assoc]
  map_mul' k l := by ext; simp [mul_assoc]

theorem conjKequiv_apply (K : Subgroup Y) (hK : K.Normal) (y : Y) (k : K) :
    ((conjKequiv K hK y k : K) : Y) = y * k * y⁻¹ := rfl

variable {T : Type} [Group T] (K : Subgroup Y) (hK : K.Normal) (e : K ≃* T)

@[expose] def alphaEquiv (y : Y) : T ≃* T :=
  e.symm.trans ((conjKequiv K hK y).trans e)

@[expose] def alphaHom : Y →* MulAut (T) where
  toFun y := alphaEquiv K hK e y
  map_one' := by
    ext x
    simp [alphaEquiv, conjKequiv]
  map_mul' y z := by
    ext x
    simp [alphaEquiv, conjKequiv, mul_assoc]

theorem alphaHom_apply_coe (y : Y) (k : K) :
    alphaHom K hK e y (e k) = e (conjKequiv K hK y k) := by
  simp [alphaHom, alphaEquiv]

theorem conj_injective_of_center (hZT : Subgroup.center T = ⊥) {x x' : T}
    (h : MulAut.conj x = MulAut.conj x') : x = x' := by
  have hc : x'⁻¹ * x ∈ Subgroup.center (T) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg' : x * g * x⁻¹ = x' * g * x'⁻¹ := by
      have := DFunLike.congr_fun h g
      simpa only [MulAut.conj_apply] using this
    have : x'⁻¹ * x * g = g * (x'⁻¹ * x) := by
      calc x'⁻¹ * x * g = x'⁻¹ * (x * g * x⁻¹) * x := by group
        _ = x'⁻¹ * (x' * g * x'⁻¹) * x := by rw [hg']
        _ = g * (x'⁻¹ * x) := by group
    exact this.symm
  rw [hZT, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

@[expose] def InnerAt (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ α : MulAut T, α ^ p = 1 → ∃ x : T, α = MulAut.conj x

theorem alphaHom_pow_eq_one (p : ℕ) {b : Y} (hb : b ^ p = 1) :
    (alphaHom K hK e b) ^ p = 1 := by
  rw [← map_pow, hb, map_one]

@[expose] noncomputable def psiFun {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) : T :=
  Classical.choose (hin (alphaHom K hK e (b : Y)) (alphaHom_pow_eq_one K hK e p (hB b b.2)))

theorem psiFun_spec {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) :
    MulAut.conj (psiFun K hK e hp hp2 hZT hin B hB b) = alphaHom K hK e (b : Y) :=
  (Classical.choose_spec (hin (alphaHom K hK e (b : Y)) (alphaHom_pow_eq_one K hK e p (hB b b.2)))).symm

@[expose] noncomputable def psiHom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) : B →* T :=
  MonoidHom.mk' (psiFun K hK e hp hp2 hZT hin B hB) (fun b c => by
    apply conj_injective_of_center hZT
    simp only [map_mul (MulAut.conj), psiFun_spec, Subgroup.coe_mul, map_mul (alphaHom K hK e)])

theorem psiHom_apply {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) :
    psiHom K hK e hp hp2 hZT hin B hB b = psiFun K hK e hp hp2 hZT hin B hB b := by
  simp only [psiHom, MonoidHom.mk'_apply]

theorem alpha_apply_eq_conj {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) (x : T) :
    alphaEquiv K hK e (b : Y) x = psiFun K hK e hp hp2 hZT hin B hB b * x *
      (psiFun K hK e hp hp2 hZT hin B hB b)⁻¹ := by
  have h := DFunLike.congr_fun (psiFun_spec K hK e hp hp2 hZT hin B hB b) x
  simp only [MulAut.conj_apply] at h
  exact h.symm

theorem psiHom_conj {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) (k : K) :
    (b : Y) * (k : Y) * (b : Y)⁻¹ =
      ((e.symm (psiHom K hK e hp hp2 hZT hin B hB b) : K) : Y) * (k : Y) *
        ((e.symm (psiHom K hK e hp hp2 hZT hin B hB b) : K) : Y)⁻¹ := by
  have h1 : e (conjKequiv K hK (b : Y) k) =
      psiHom K hK e hp hp2 hZT hin B hB b * e k * (psiHom K hK e hp hp2 hZT hin B hB b)⁻¹ := by
    rw [psiHom_apply K hK e hp hp2 hZT hin B hB b, ← alphaHom_apply_coe K hK e (b : Y) k]
    exact alpha_apply_eq_conj K hK e hp hp2 hZT hin B hB b (e k)
  have h2 : conjKequiv K hK (b : Y) k =
      e.symm (psiHom K hK e hp hp2 hZT hin B hB b) * k * (e.symm (psiHom K hK e hp hp2 hZT hin B hB b))⁻¹ := by
    apply e.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h3 := congrArg (fun z : K => (z : Y)) h2
  simpa only [conjKequiv_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h3

theorem psiHom_eq_one_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) :
    psiHom K hK e hp hp2 hZT hin B hB b = 1 ↔ (b : Y) ∈ Subgroup.centralizer (K : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have hc := psiHom_conj K hK e hp hp2 hZT hin B hB b ⟨k, hk⟩
    rw [h, map_one] at hc
    simp only [Subgroup.coe_one, one_mul, inv_one, mul_one] at hc
    calc (k : Y) * (b : Y) = ((b : Y) * k * (b : Y)⁻¹) * (b : Y) := by rw [hc]
      _ = (b : Y) * k := by group
  · intro h
    apply conj_injective_of_center hZT
    have hal : alphaHom K hK e (b : Y) = 1 := by
      ext x
      obtain ⟨k, rfl⟩ := e.surjective x
      rw [alphaHom_apply_coe K hK e (b : Y) k, MulAut.one_apply]
      have hk := h k k.2
      have hbk : (b : Y) * k * (b : Y)⁻¹ = k := by
        rw [← hk]; group
      have hcoe : ((conjKequiv K hK (b : Y) k : K) : Y) = (k : Y) := by
        rw [conjKequiv_apply, hbk]
      rw [Subtype.ext hcoe]
    rw [map_one, psiHom_apply K hK e hp hp2 hZT hin B hB b, psiFun_spec K hK e hp hp2 hZT hin B hB b, hal]

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open

variable {Y : Type} [Group Y] [Finite Y]

theorem isElemAbelian_map {p : ℕ} {A : Type*} [Group A] {f : A →* Y} (hf : Function.Injective f)
    {S : Subgroup A} (hS : IsElemAbelian p S) : IsElemAbelian p (S.map f) := by
  have hcomm : ∀ u ∈ S.map f, ∀ v ∈ S.map f, u * v = v * u := by
    intro u hu v hv
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hv
    have hst : s * t = t * s := by
      have := hS.1.is_comm.comm (⟨s, hs⟩ : S) ⟨t, ht⟩
      exact congrArg Subtype.val this
    rw [← map_mul, ← map_mul, hst]
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, ?_⟩
  intro x hx
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 hx
  rw [← hsx, ← map_pow, hS.2 s hs, map_one]

theorem map_ker_psiHom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T : Type} [Group T] (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T)
    (K : Subgroup Y) (hK : K.Normal) (e : K ≃* T) (B : Subgroup Y)
    (hB : IsElemAbelian p B) :
    (psiHom K hK e hp hp2 hZT hin B (fun b hb => hB.2 b hb)).ker.map B.subtype =
      B ⊓ Subgroup.centralizer (K : Set Y) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hb1 : psiHom K hK e hp hp2 hZT hin B (fun b hb => hB.2 b hb) b = 1 := hb
    have hcen := (psiHom_eq_one_iff K hK e hp hp2 hZT hin B (fun b hb => hB.2 b hb) b).1 hb1
    exact ⟨b.2, hcen⟩
  · rintro ⟨hyB, hcen⟩
    refine ⟨⟨y, hyB⟩, ?_, rfl⟩
    exact (psiHom_eq_one_iff K hK e hp hp2 hZT hin B (fun b hb => hB.2 b hb) ⟨y, hyB⟩).2 hcen

theorem card_inf_centralizer_eq_ker {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T : Type} [Group T] (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T)
    (K : Subgroup Y) (hK : K.Normal) (e : K ≃* T) (B : Subgroup Y)
    (hB : IsElemAbelian p B) :
    Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) =
      Nat.card (psiHom K hK e hp hp2 hZT hin B (fun b hb => hB.2 b hb)).ker := by
  rw [← map_ker_psiHom hp hp2 hZT hin K hK e B hB, Subgroup.card_map_of_injective B.subtype_injective]

theorem card_le_range_of_elemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T : Type} [Group T] (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T)
    (K : Subgroup Y) (hK : K.Normal) (hZ : Subgroup.center ↥K = ⊥)
    (e : K ≃* T) (B : Subgroup Y) (hB : IsElemAbelian p B)
    (hmax : IsMaxRankIn p B ⊤) (S : Subgroup (T))
    (hS : IsElemAbelian p S) :
    Nat.card S ≤ Nat.card (psiHom K hK e hp hp2 hZT hin B (fun b hb => hB.2 b hb)).range := by
  classical
  set ψ := psiHom K hK e hp hp2 hZT hin B (fun b hb => hB.2 b hb) with hψ
  let f : T →* Y := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  set S' : Subgroup Y := S.map f with hS'def
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  have hS' : IsElemAbelian p S' := isElemAbelian_map hf hS
  have hC : IsElemAbelian p C := isElemAbelian_mono hB inf_le_left
  have hS'K : ∀ y ∈ S', y ∈ K := by
    intro y hy
    obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.1 hy
    exact (e.symm s).2
  have hSC : S' ≤ Subgroup.centralizer (C : Set Y) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcK : c ∈ Subgroup.centralizer (K : Set Y) := hc.2
    rw [Subgroup.mem_centralizer_iff] at hcK
    exact (hcK y (hS'K y hy)).symm
  have hT : IsElemAbelian p (S' ⊔ C) :=
    CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_sup_of_commute hS' hC hSC
  have hTle : Nat.card ↥(S' ⊔ C) ≤ Nat.card B := hmax (S' ⊔ C) le_top hT
  have hCN : C ≤ Subgroup.normalizer (S' : Set Y) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hcK : c ∈ Subgroup.centralizer (K : Set Y) := hc.2
    rw [Subgroup.mem_centralizer_iff] at hcK
    have key : y ∈ K → c * y * c⁻¹ = y := fun hyK => by
      have hcomm : c * y = y * c := (hcK y hyK).symm
      rw [hcomm]
      group
    constructor
    · intro hy
      rw [key (hS'K y hy)]
      exact hy
    · intro hy
      have hyK' : c * y * c⁻¹ ∈ K := hS'K _ hy
      have hyK : y ∈ K := by
        have h1 := hK.conj_mem _ hyK' c⁻¹
        have h2 : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
        rwa [h2] at h1
      rw [← key hyK]
      exact hy
  have hinf : S' ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyK : y ∈ K := hS'K y hy.1
    have hcen : (⟨y, hyK⟩ : K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hc : y ∈ Subgroup.centralizer (K : Set Y) := hy.2.2
      rw [Subgroup.mem_centralizer_iff] at hc
      exact hc g g.2
    rw [hZ, Subgroup.mem_bot] at hcen
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hcen
  have hS'card : Nat.card S' = Nat.card S := Subgroup.card_map_of_injective hf
  have hprod := card_sup_mul_card_inf_of_le_normalizer hCN
  rw [hinf, Subgroup.card_bot, mul_one, hS'card] at hprod
  have hCker : Nat.card C = Nat.card ψ.ker := card_inf_centralizer_eq_ker hp hp2 hZT hin K hK e B hB
  have hkr := Subgroup.card_ker_mul_card_range ψ
  have hkr := Subgroup.card_ker_mul_card_range ψ
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hmain : Nat.card S * Nat.card C ≤ Nat.card ψ.range * Nat.card C := by
    calc Nat.card S * Nat.card C = Nat.card ↥(S' ⊔ C) := hprod.symm
      _ ≤ Nat.card B := hTle
      _ = Nat.card ψ.ker * Nat.card ψ.range := hkr.symm
      _ = Nat.card ψ.range * Nat.card C := by rw [← hCker]; ring
  exact Nat.le_of_mul_le_mul_right hmain hCpos

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open Subgroup

variable {Y : Type} [Group Y] [Finite Y]

section

variable {T : Type} [Group T] (K : Subgroup Y) (hK : K.Normal) (e : K ≃* T)
variable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZT : Subgroup.center T = ⊥) (hin : InnerAt p T)
variable (B : Subgroup Y) (hB : ∀ b ∈ B, b ^ p = 1)

theorem comm_iff_psi (b : B) (k : K) :
    (b : Y) * (k : Y) = (k : Y) * (b : Y) ↔
      psiHom K hK e hp hp2 hZT hin B hB b * e k = e k * psiHom K hK e hp hp2 hZT hin B hB b := by
  have hc := psiHom_conj K hK e hp hp2 hZT hin B hB b k
  set s : K := e.symm (psiHom K hK e hp hp2 hZT hin B hB b) with hs
  have hpsi : psiHom K hK e hp hp2 hZT hin B hB b = e s := by
    rw [hs, MulEquiv.apply_symm_apply]
  rw [hpsi]
  constructor
  · intro h
    have h1 : (b : Y) * (k : Y) * (b : Y)⁻¹ = (k : Y) := by rw [h]; simp
    have h2 : (s : Y) * (k : Y) * (s : Y)⁻¹ = (k : Y) := by rw [← hc, h1]
    have h3 : s * k * s⁻¹ = k := Subtype.ext (by simpa using h2)
    have h4 := congrArg e h3
    rw [map_mul, map_mul, map_inv] at h4
    exact mul_inv_eq_iff_eq_mul.1 h4
  · intro h
    have h1 : e (s * k * s⁻¹) = e k := by
      rw [map_mul, map_mul, map_inv, h]
      group
    have h2 : s * k * s⁻¹ = k := e.injective h1
    have h3 : (s : Y) * (k : Y) * (s : Y)⁻¹ = (k : Y) := by
      have := congrArg (fun z : K => (z : Y)) h2
      simpa using this
    have h4 : (b : Y) * (k : Y) * (b : Y)⁻¹ = (k : Y) := hc.trans h3
    calc (b : Y) * (k : Y) = ((b : Y) * (k : Y) * (b : Y)⁻¹) * (b : Y) := by group
      _ = (k : Y) * (b : Y) := by rw [h4]

@[expose] noncomputable def psiImage (E : Subgroup Y) : Subgroup (T) :=
  (E.subgroupOf B).map (psiHom K hK e hp hp2 hZT hin B hB)

theorem centralizer_psiImage_map (E : Subgroup Y) (hEB : E ≤ B) :
    (Subgroup.centralizer ((psiImage K hK e hp hp2 hZT hin B hB E : Subgroup _) :
        Set (T))).map (K.subtype.comp e.symm.toMonoidHom) =
      K ⊓ Subgroup.centralizer (E : Set Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨(e.symm x).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwB : w ∈ B := hEB hw
    have hmem : psiHom K hK e hp hp2 hZT hin B hB ⟨w, hwB⟩ ∈
        psiImage K hK e hp hp2 hZT hin B hB E :=
      Subgroup.mem_map.2 ⟨⟨w, hwB⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
    have hk := (comm_iff_psi K hK e hp hp2 hZT hin B hB ⟨w, hwB⟩ (e.symm x)).2 (by
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_centralizer_iff.1 hx _ hmem)
    exact hk
  · intro hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyK, hyc⟩ := hy
    refine ⟨e ⟨y, hyK⟩, Subgroup.mem_centralizer_iff.2 ?_, ?_⟩
    · intro g hg
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
      have hwE : (w : Y) ∈ E := Subgroup.mem_subgroupOf.1 hw
      rw [Subgroup.mem_centralizer_iff] at hyc
      have hc : (w : Y) * y = y * (w : Y) := hyc w hwE
      exact (comm_iff_psi K hK e hp hp2 hZT hin B hB w ⟨y, hyK⟩).1 hc
    · show (e.symm (e ⟨y, hyK⟩) : Y) = y
      rw [MulEquiv.symm_apply_apply]

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA

variable {Y : Type} [Group Y] [Finite Y]

theorem glaPLayer_ne_bot_of_comp {T : Type} [Group T] [Finite T] (K : Subgroup Y) (hK : K.Normal)
    (e : K ≃* T) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZT : Subgroup.center T = ⊥)
    (hin : InnerAt p T) (B : Subgroup Y) (hB : ∀ b ∈ B, b ^ p = 1) (E : Subgroup Y) (hEB : E ≤ B)
    {J0 : Subgroup T}
    (hJ : GLAPComponent p (Subgroup.centralizer ((psiImage K hK e hp hp2 hZT hin B hB E :
      Subgroup T) : Set T)) J0) :
    GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥ := by
  set f : T →* Y := K.subtype.comp e.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := K.subtype_injective.comp e.symm.injective
  have hker : Nat.Coprime p (Nat.card ↥((Subgroup.centralizer
      ((psiImage K hK e hp hp2 hZT hin B hB E : Subgroup T) : Set T)) ⊓ f.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff f).2 hfinj, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hmap := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp f hker hJ
  rw [centralizer_psiImage_map K hK e hp hp2 hZT hin B hB E hEB] at hmap
  have hne : J0.map f ≠ ⊥ := fun hb =>
    CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hJ
      ((Subgroup.map_eq_bot_iff_of_injective _ hfinj).1 hb)
  intro hbot
  have hle : J0.map f ≤ GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) := le_sSup hmap
  rw [hbot] at hle
  exact hne (le_bot_iff.1 hle)

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
