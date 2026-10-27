module

public import CFSG.LocalAnalysis.EvenBN.U4.Setup
public import CFSG.LocalAnalysis.EvenBN.U4.Model.RankAut
public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolution
public import CFSG.LocalAnalysis.EvenBN.U4.Model.CentralizerZ2
public import CFSG.LocalAnalysis.EvenBN.U4.Model.OrbitsTwo
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotZStar

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup G}
    (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {z : G} (hz : z ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, z = a * b := by
  have hle : A ≤ normalizer (B : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun b hb => (hc a ha b hb).symm)
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A B hle] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_normalizer_of_conj_le {K : Subgroup G} [Finite K] {g : G}
    (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : g ∈ normalizer (K : Set G) := by
  have hinj : Function.Injective (fun k : K => (⟨g * k * g⁻¹, h k k.2⟩ : K)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only at this
    exact Subtype.ext (by simpa using this)
  have hsurj := Finite.injective_iff_surjective.1 hinj
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h n, fun hn => ?_⟩
  obtain ⟨k, hk⟩ := hsurj ⟨g * n * g⁻¹, hn⟩
  have : (k : G) = n := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [← this]
  exact k.2

variable [Finite G]

theorem exists_conj_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {T H X : Subgroup G}
    (hT : IsSylowOf p T H) (hXH : X ≤ H) (hX : IsPGroup p X) :
    ∃ c ∈ H, ∀ x ∈ X, c⁻¹ * x * c ∈ T := by
  obtain ⟨S, rfl⟩ := hT
  obtain ⟨Q, hQ⟩ := (hX.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H S Q
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hXH hx⟩ : H) ∈ (Q : Subgroup H) := hQ hx
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  refine ⟨s, hs, ?_⟩
  have : (c : G) * s * (c : G)⁻¹ = x := by
    have := congrArg Subtype.val hsx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [Subgroup.subtype_apply, ← this]
  group

theorem exists_normalizer_conj_eq_of_weakly_closed_in {p : ℕ} [Fact p.Prime] {x g : G}
    {T R : Subgroup G} (hT : IsSylowOf p T (centralizer ({x} : Set G))) (hRT : R ≤ T)
    (hwc : ∀ c : G, (∀ r ∈ R, c⁻¹ * r * c ∈ T) → ∀ r ∈ R, c⁻¹ * r * c ∈ R)
    (hy : ∀ r ∈ R, r * (g⁻¹ * x * g) = (g⁻¹ * x * g) * r) :
    ∃ n ∈ normalizer (R : Set G), n⁻¹ * x * n = g⁻¹ * x * g := by
  set y := g⁻¹ * x * g with hydef
  have hT' : IsSylowOf p (T.map (MulAut.conj g⁻¹).toMonoidHom)
      (centralizer ({y} : Set G)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hT ⊢
    obtain ⟨hle, hP, hdvd⟩ := hT
    have hC : (centralizer ({x} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
        centralizer ({y} : Set G) := by
      ext z
      constructor
      · intro hz
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
        have hw' : w * x = x * w := mem_centralizer_singleton_iff.1 hw
        refine mem_centralizer_singleton_iff.2 ?_
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hydef]
        calc g⁻¹ * w * g * (g⁻¹ * x * g) = g⁻¹ * (w * x) * g := by group
          _ = g⁻¹ * (x * w) * g := by rw [hw']
          _ = g⁻¹ * x * g * (g⁻¹ * w * g) := by group
      · intro hz
        have hz' : z * y = y * z := mem_centralizer_singleton_iff.1 hz
        refine Subgroup.mem_map.2 ⟨g * z * g⁻¹, mem_centralizer_singleton_iff.2 ?_,
          by simp; group⟩
        calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [← hydef, hz']
          _ = x * (g * z * g⁻¹) := by group
    refine ⟨?_, hP.map _, ?_⟩
    · rw [← hC]
      exact Subgroup.map_mono hle
    · rw [← hC, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hdvd
  have hRy : R ≤ centralizer ({y} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.2 (hy r hr)
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_isSylowOf hT' hRy
    ((hT.isPGroup).to_le hRT)
  have hmT : ∀ r ∈ R, (c * g⁻¹)⁻¹ * r * (c * g⁻¹) ∈ T := by
    intro r hr
    obtain ⟨s, hs, hsr⟩ := hc r hr
    have : (c * g⁻¹)⁻¹ * r * (c * g⁻¹) = s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hsr
      rw [mul_inv_rev, inv_inv]
      calc g * c⁻¹ * r * (c * g⁻¹) = g * (c⁻¹ * r * c) * g⁻¹ := by group
        _ = g * (g⁻¹ * s * g) * g⁻¹ := by rw [hsr]
        _ = s := by group
    rw [this]
    exact hs
  have hmR := hwc _ hmT
  have hmN : (c * g⁻¹)⁻¹ ∈ normalizer (R : Set G) :=
    mem_normalizer_of_conj_le fun r hr => by
      have := hmR r hr
      simpa using this
  refine ⟨(c * g⁻¹)⁻¹, hmN, ?_⟩
  have hcy : c * y = y * c := mem_centralizer_singleton_iff.1 hcC
  calc ((c * g⁻¹)⁻¹)⁻¹ * x * (c * g⁻¹)⁻¹ = c * (g⁻¹ * x * g) * c⁻¹ := by group
    _ = y := by rw [← hydef, hcy]; group

end Generic

section ModelFacts

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem glAut_eq_map (φ : K ≃+* K) (g : GL (Fin 4) K) :
    glAut φ g = Matrix.GeneralLinearGroup.map (φ : K →+* K) g :=
  Units.ext rfl

theorem glAut_mem_P (φ : K ≃+* K) {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h) :
    glAut φ g ∈ miyamotoP h := by
  obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hg
  rw [glAut_miyamotoXGL, miyamotoXGL_mem_P]
  refine ⟨by rw [← map_bar_comm, hb], ?_⟩
  have := congrArg φ hd
  simpa [map_bar_comm h φ] using this

theorem glAut_mem_P_iff (φ : K ≃+* K) {g : GL (Fin 4) K} :
    glAut φ g ∈ miyamotoP h ↔ g ∈ miyamotoP h := by
  refine ⟨fun hg => ?_, glAut_mem_P h φ⟩
  have := glAut_mem_P h φ⁻¹ hg
  rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this

theorem miyamotoZ1_comm_miyamotoXGL [CharP K 2] {a b c d : K} (hb : h.bar b = b) :
    miyamotoXGL h 0 0 0 1 * miyamotoXGL h a b c d =
      miyamotoXGL h a b c d * miyamotoXGL h 0 0 0 1 := by
  rw [miyamotoXGL_mul h (map_zero _), miyamotoXGL_mul h hb, miyamotoXGL_inj]
  refine ⟨by ring, by ring, by ring, by simp only [map_zero]; ring⟩

theorem glAut_bar_of_mem_N2 {m : GL (Fin 4) K} (hm : m ∈ miyamotoN2 h) :
    glAut (miyamotoBarEquiv h) m = m := by
  obtain ⟨M, -, hbar, hmM⟩ := (mem_miyamotoN2 h).1 hm
  apply Units.ext
  rw [coe_glAut, hmM]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoN2Mat, hbar]

theorem exists_lang_data (hf : 2 ≤ f) {β : MulAut (gramSU h (miyamotoJ4 K))}
    (hβ : β = miyamotoFieldAut h (miyamotoBarEquiv h) ∨
      β = MulAut.conj (miyamotoZ1S h) * miyamotoFieldAut h (miyamotoBarEquiv h)) :
    ∃ n v w : gramSU h (miyamotoJ4 K), (n : GL (Fin 4) K) ∈ miyamotoN2 h ∧ β v = v ∧
      (∀ m : gramSU h (miyamotoJ4 K), (m : GL (Fin 4) K) ∈ miyamotoN2 h → β m = m) ∧
      (β w)⁻¹ * w = n * v * n⁻¹ * v⁻¹ ∧ n * v * n⁻¹ * v⁻¹ ≠ 1 := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hbb := h.bar_bar
  have hβy : ∀ y : gramSU h (miyamotoJ4 K),
      miyamotoXGL h 0 0 0 1 * glAut (miyamotoBarEquiv h) (y : GL (Fin 4) K) =
        glAut (miyamotoBarEquiv h) (y : GL (Fin 4) K) * miyamotoXGL h 0 0 0 1 →
      ((β y : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) = glAut (miyamotoBarEquiv h) y := by
    intro y hy
    rcases hβ with rfl | rfl
    · rfl
    · rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_miyamotoFieldAut_apply]
      change miyamotoXGL h 0 0 0 1 * _ * (miyamotoXGL h 0 0 0 1)⁻¹ = _
      rw [hy, mul_inv_cancel_right]
  obtain ⟨μ, hμF, hμ2⟩ := exists_fixed_unit_sq_ne_one h hf
  have hμ1 : (μ : K) + 1 ≠ 0 := by
    intro e
    apply hμ2
    rw [show (μ : K) = 1 by linear_combination e - h2, one_pow]
  set c : K := ((μ : K) + 1)⁻¹ with hc
  have hcF : h.bar c = c := by rw [hc, map_inv₀, map_add, hμF, map_one]
  obtain ⟨c₀, hc₀⟩ := exists_add_bar_eq_one h
  have hvP : miyamotoXGL h 0 0 c 0 ∈ miyamotoP h :=
    (miyamotoXGL_mem_P h).2 ⟨map_zero _, by simp⟩
  have hwP : miyamotoXGL h 1 1 c₀ c₀ ∈ miyamotoP h := (miyamotoXGL_mem_P h).2 ⟨map_one _, by
    simp only [map_one, one_mul]
    linear_combination (c₀ + h.bar c₀) * h2⟩
  have hnN : (miyamotoIHom h (1, μ))⁻¹ ∈ miyamotoN2 h := inv_mem (miyamotoIHom_one_mem_N2 h hμF)
  set n : gramSU h (miyamotoJ4 K) := ⟨_, miyamotoN2_le_gramSU h hnN⟩ with hn
  set v : gramSU h (miyamotoJ4 K) := ⟨_, miyamotoUnipotent_le_SU h false false hvP⟩ with hv
  set w : gramSU h (miyamotoJ4 K) := ⟨_, miyamotoUnipotent_le_SU h false false hwP⟩ with hw
  have hnv : ((n * v * n⁻¹ * v⁻¹ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      miyamotoXGL h 0 0 1 0 := by
    change (miyamotoIHom h (1, μ))⁻¹ * miyamotoXGL h 0 0 c 0 * ((miyamotoIHom h (1, μ))⁻¹)⁻¹ *
      (miyamotoXGL h 0 0 c 0)⁻¹ = _
    rw [inv_inv, diagN2_conj_A2 h hμF, miyamotoXGL_inv h (map_zero _),
      miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
    refine ⟨by simp, by simp, ?_, by simp⟩
    rw [hc]
    field_simp
    ring
  have hβw : ((β w : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      miyamotoXGL h 1 1 (h.bar c₀) (h.bar c₀) := by
    have e : glAut (miyamotoBarEquiv h) (miyamotoXGL h 1 1 c₀ c₀) =
        miyamotoXGL h 1 1 (h.bar c₀) (h.bar c₀) := by
      rw [glAut_miyamotoXGL]
      simp
    rw [hβy w (by
      change _ * glAut _ (miyamotoXGL h 1 1 c₀ c₀) = glAut _ (miyamotoXGL h 1 1 c₀ c₀) * _
      rw [e]
      exact miyamotoZ1_comm_miyamotoXGL h (map_one _))]
    exact e
  have hwz : (((β w)⁻¹ * w : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      miyamotoXGL h 0 0 1 0 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hβw, miyamotoXGL_inv h (map_one _),
      miyamotoXGL_mul h (map_one _), miyamotoXGL_inj]
    refine ⟨by linear_combination h2, by linear_combination h2, ?_, ?_⟩
    · linear_combination hc₀ + h2
    · simp only [map_add, map_mul, map_one, hbb]
      linear_combination (2 * c₀ + h.bar c₀ + 1) * h2
  refine ⟨n, v, w, hnN, ?_, fun m hm => ?_, Subtype.ext (hwz.trans hnv.symm), ?_⟩
  ·
    have e : glAut (miyamotoBarEquiv h) (miyamotoXGL h 0 0 c 0) = miyamotoXGL h 0 0 c 0 := by
      rw [glAut_miyamotoXGL]
      simp [hcF]
    apply Subtype.ext
    rw [hβy v (by
      change _ * glAut _ (miyamotoXGL h 0 0 c 0) = glAut _ (miyamotoXGL h 0 0 c 0) * _
      rw [e]
      exact miyamotoZ1_comm_miyamotoXGL h (map_zero _))]
    exact e
  ·
    have hz : miyamotoXGL h 0 0 0 1 ∈ miyamotoZ h := ⟨1, map_one _, rfl⟩
    apply Subtype.ext
    rw [hβy m (by rw [glAut_bar_of_mem_N2 h hm]; exact (miyamotoN2_commute_Z h hm hz).symm),
      glAut_bar_of_mem_N2 h hm]
  ·
    intro e
    have e' := congrArg Subtype.val e
    rw [hnv, OneMemClass.coe_one, ← miyamotoXGL_zero h, miyamotoXGL_inj] at e'
    exact one_ne_zero e'.2.2.1

end ModelFacts

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem zpow_t_eq (hS : Setting h L η t Q T) (i : ℤ) : t ^ i = 1 ∨ t ^ i = t := by
  have hk : t ^ i = t ^ (i % 2) := by
    rw [← zpow_mod_orderOf, hS.t_two]
    norm_cast
  rcases Int.emod_two_eq_zero_or_one i with h0 | h0
  · left; rw [hk, h0, zpow_zero]
  · right; rw [hk, h0, zpow_one]

theorem L_comm_centralizer (_hS : Setting h L η t Q T) :
    ∀ x ∈ L, ∀ y ∈ centralizer (L : Set G), x * y = y * x :=
  fun x hx _ hy => mem_centralizer_iff.1 hy x hx

theorem L_comm_kernel (_hS : Setting h L η t Q T) :
    ∀ x ∈ L, ∀ y ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G), x * y = y * x :=
  fun x hx _ hy => mem_centralizer_iff.1 (mem_inf.1 hy).1 x hx

theorem comm_t_of_mem_L (hS : Setting h L η t Q T) {x : G} (hx : x ∈ L) : x * t = t * x :=
  mem_centralizer_iff.1 hS.t_mem x hx

theorem kernel_le_T (hS : Setting h L η t Q T) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := centralizer (L : Set G) ⊓ centralizer ({t} : Set G)
  have hSN : T ≤ normalizer (S : Set G) := by
    intro x hx
    have hn := hS.kernel.2.2.2
    rw [mem_normalizer_iff]
    intro y
    have hxC := hS.T_le hx
    constructor
    · intro hy
      exact hn.conj_mem ⟨y, hy.2⟩ hy ⟨x, hxC⟩
    · intro hy
      have h1 := hn.conj_mem ⟨x * y * x⁻¹, hy.2⟩ hy ⟨x, hxC⟩⁻¹
      have h2 : ((⟨x, hxC⟩⁻¹ * ⟨x * y * x⁻¹, hy.2⟩ * (⟨x, hxC⟩⁻¹)⁻¹ :
          centralizer ({t} : Set G)) : G) = y := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [← h2]
      exact h1
  have h2 : IsPGroup 2 (T ⊔ S : Subgroup G) :=
    hS.isPGroup_T.to_sup_of_normal_right' hS.isPGroup_kernel hSN
  have hle : T ⊔ S ≤ centralizer ({t} : Set G) := sup_le hS.T_le inf_le_right
  rw [← hS.T_sylow.eq_of_le le_sup_left hle h2]
  exact le_sup_right

theorem T_inf_L (hS : Setting h L η t Q T) : T ⊓ L = miyamotoPG h L η := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hS.isSylowOf_P.eq_of_le (le_inf hS.P_le_T (miyamotoPull_le h L η _)) inf_le_right
    hS.isPGroup_T.to_inf_left

theorem T_le_normalizer (hS : Setting h L η t Q T) : T ≤ normalizer (L : Set G) :=
  hS.T_le.trans hS.centralizer_le_normalizer

theorem T_le_normalizer_P (hS : Setting h L η t Q T) :
    T ≤ normalizer (miyamotoPG h L η : Set G) := by
  intro x hx
  rw [← hS.T_inf_L, mem_normalizer_iff]
  intro y
  have hxL := hS.T_le_normalizer hx
  constructor
  · intro hy
    obtain ⟨hyT, hyL⟩ := mem_inf.1 hy
    exact mem_inf.2 ⟨mul_mem (mul_mem hx hyT) (inv_mem hx), (mem_normalizer_iff.1 hxL y).1 hyL⟩
  · intro hy
    obtain ⟨hyT, hyL⟩ := mem_inf.1 hy
    refine mem_inf.2 ⟨?_, (mem_normalizer_iff.1 hxL y).2 hyL⟩
    have := mul_mem (mul_mem (inv_mem hx) hyT) hx
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this

theorem mem_P_of_mul (hS : Setting h L η t Q T) {x l c : G} (hxT : x ∈ T) (hl : l ∈ L)
    (hc : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) (hx : x = l * c) :
    l ∈ miyamotoPG h L η := by
  rw [← hS.T_inf_L]
  refine ⟨?_, hl⟩
  have : x * c⁻¹ ∈ T := mul_mem hxT (inv_mem (hS.kernel_le_T hc))
  rwa [hx, mul_inv_cancel_right] at this

theorem mem_P_sup_zpowers_of_mul (hS : Setting h L η t Q T) {x l c : G} (hxT : x ∈ T)
    (hx2 : x * x = 1) (hl : l ∈ L) (hc : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G))
    (hx : x = l * c) : x ∈ miyamotoPG h L η ⊔ zpowers t := by
  have hlP := hS.mem_P_of_mul hxT hl hc hx
  have hcL : c ∈ centralizer (L : Set G) := (mem_inf.1 hc).1
  have hlc : l * c = c * l := mem_centralizer_iff.1 hcL l hl
  have hsq : (l * l) * (c * c) = 1 := by
    calc (l * l) * (c * c) = l * (l * c) * c := by group
      _ = l * (c * l) * c := by rw [hlc]
      _ = (l * c) * (l * c) := by group
      _ = 1 := by rw [← hx]; exact hx2
  have hll : l * l = 1 := by
    have hmem : l * l ∈ L ⊓ centralizer (L : Set G) := by
      refine mem_inf.2 ⟨mul_mem hl hl, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hsq]
      exact inv_mem (mul_mem hcL hcL)
    rw [hS.inf_centralizer_eq_bot, mem_bot] at hmem
    exact hmem
  have hcc : c * c = 1 := by rwa [hll, one_mul] at hsq
  have hct : c ∈ zpowers t := by
    by_cases h1 : c = 1
    · rw [h1]
      exact one_mem _
    · rw [hS.eq_t_of_mem_kernel hc (orderOf_eq_prime (by rw [sq]; exact hcc) h1)]
      exact mem_zpowers _
  rw [hx]
  exact mul_mem (mem_sup_left hlP) (mem_sup_right hct)

theorem P_comm_zpowers (hS : Setting h L η t Q T) :
    ∀ x ∈ miyamotoPG h L η, ∀ y ∈ zpowers t, x * y = y * x := by
  intro x hx y hy
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hy
  exact (Commute.zpow_right (hS.comm_t_of_mem_L (miyamotoPull_le h L η _ hx)) i).eq

theorem card_le_two_mul_card_inf_P (hS : Setting h L η t Q T) {H : Subgroup G}
    (hH : H ≤ miyamotoPG h L η ⊔ zpowers t) :
    Nat.card H ≤ 2 * Nat.card (H ⊓ miyamotoPG h L η : Subgroup G) := by
  classical
  have hdec : ∀ x ∈ miyamotoPG h L η ⊔ zpowers t, x ∉ miyamotoPG h L η →
      ∃ p ∈ miyamotoPG h L η, x = p * t := by
    intro x hx hxP
    obtain ⟨p, hp, u, hu, rfl⟩ := exists_mul_of_mem_sup_of_commute hS.P_comm_zpowers hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
    rcases hS.zpow_t_eq i with h1 | h1
    · rw [h1, mul_one] at hxP
      exact absurd hp hxP
    · exact ⟨p, hp, by rw [h1]⟩
  have key := card_le_card_inf_mul_ncard (H := H) (N := miyamotoPG h L η)
    (fun x : G => decide (x ∈ miyamotoPG h L η)) (T := (Set.univ : Set Bool)) (Set.toFinite _)
    (fun _ _ => Set.mem_univ _) ?_
  · have h2 : (Set.univ : Set Bool).ncard = 2 := by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool]
    rw [h2, mul_comm] at key
    exact key
  · intro x hx y hy e
    by_cases hxP : x ∈ miyamotoPG h L η
    · have hyP : y ∈ miyamotoPG h L η := by simpa [hxP] using e
      exact mul_mem (inv_mem hxP) hyP
    · have hyP : y ∉ miyamotoPG h L η := by simpa [hxP] using e
      obtain ⟨p, hp, rfl⟩ := hdec x (hH hx) hxP
      obtain ⟨p', hp', rfl⟩ := hdec y (hH hy) hyP
      have hc := hS.P_comm_zpowers _ (mul_mem (inv_mem hp) hp') t (mem_zpowers t)
      rw [show (p * t)⁻¹ * (p' * t) = t⁻¹ * ((p⁻¹ * p') * t) by group, hc, ← mul_assoc,
        inv_mul_cancel, one_mul]
      exact mul_mem (inv_mem hp) hp'

theorem exists_act_eq_twisted (hS : Setting h L η t Q T) {x : G} (hxT : x ∈ T) :
    ∃ (p : Kˣ × Kˣ) (g : GL (Fin 4) K), g ∈ miyamotoP h ∧
      ∀ y : gramSU h (miyamotoJ4 K), ((hS.act ⟨x, hS.T_le hxT⟩ y : gramSU h (miyamotoJ4 K)) :
        GL (Fin 4) K) = (miyamotoIHom h p * g)⁻¹ *
          Matrix.GeneralLinearGroup.map ((hS.fieldFactor ⟨x, hS.T_le hxT⟩ : K ≃+* K) : K →+* K)
            (y : GL (Fin 4) K) * (miyamotoIHom h p * g) := by
  have : CharP K 2 := h.charP
  set xc : centralizer ({t} : Set G) := ⟨x, hS.T_le hxT⟩ with hxc
  set φ := hS.fieldFactor xc with hφ
  obtain ⟨s, hs⟩ := hS.exists_act_eq xc
  have hact : ∀ y : gramSU h (miyamotoJ4 K), ((hS.act xc y : gramSU h (miyamotoJ4 K)) :
      GL (Fin 4) K) = s * glAut φ (y : GL (Fin 4) K) * (s : GL (Fin 4) K)⁻¹ := by
    intro y
    rw [hs, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_miyamotoFieldAut_apply]
  have hxP : x ∈ normalizer (miyamotoPull h L η (miyamotoP h) : Set G) :=
    hS.T_le_normalizer_P hxT
  have hsN : (s : GL (Fin 4) K) ∈ normalizer (miyamotoP h : Set (GL (Fin 4) K)) := by
    rw [mem_normalizer_iff]
    intro g
    by_cases hgS : g ∈ gramSU h (miyamotoJ4 K)
    · set y := (miyamotoFieldAut h φ)⁻¹ ⟨g, hgS⟩ with hy
      have hgy : glAut φ (y : GL (Fin 4) K) = g := by
        rw [← coe_miyamotoFieldAut_apply, hy, MulAut.apply_inv_self]
      have e : s * g * (s : GL (Fin 4) K)⁻¹ = ((hS.act xc y : gramSU h (miyamotoJ4 K)) :
          GL (Fin 4) K) := by
        rw [hact, hgy]
      rw [e, act_apply, miyamotoAct_mem_iff_of_mem_normalizer h L η _ hxP, ← hgy,
        glAut_mem_P_iff]
    · constructor
      · intro hg
        exact absurd (miyamotoUnipotent_le_SU h false false hg) hgS
      · intro hg
        exfalso
        apply hgS
        have := mul_mem (mul_mem (inv_mem s.2) (miyamotoUnipotent_le_SU h false false hg)) s.2
        rwa [show (s : GL (Fin 4) K)⁻¹ * (s * g * (s : GL (Fin 4) K)⁻¹) * s = g by group]
          at this
  have hsPI : (s : GL (Fin 4) K)⁻¹ ∈ miyamotoI h ⊔ miyamotoP h := by
    rw [sup_comm, ← normalizer_miyamotoP h]
    exact inv_mem ⟨s.2, hsN⟩
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    (miyamotoI_le_normalizer_unipotent h false false)] at hsPI
  obtain ⟨D, ⟨p, -, rfl⟩, g, hg, hDg⟩ := hsPI
  refine ⟨p, g, hg, fun y => ?_⟩
  rw [hact, show miyamotoIHom h p * g = (s : GL (Fin 4) K)⁻¹ from hDg, inv_inv, glAut_eq_map]

theorem exists_ne_of_fieldFactor_ne_one (_hS : Setting h L η t Q T) {φ : K ≃+* K}
    (hφ : φ ≠ 1) : ∃ k, (φ : K →+* K) k ≠ k := by
  by_contra hcon
  push Not at hcon
  exact hφ (RingEquiv.ext fun k => hcon k)

theorem two_mul_card_lt_of_commute (hS : Setting h L η t Q T) {x : G} (hxT : x ∈ T)
    (hσ : hS.fieldFactor ⟨x, hS.T_le hxT⟩ ≠ 1) {W : Subgroup G} (hWP : W ≤ miyamotoPG h L η)
    (hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hxW : ∀ w ∈ W, x * w = w * x) :
    2 * Nat.card W < (2 ^ f) ^ 4 := by
  have : CharP K 2 := h.charP
  obtain ⟨p, g, hg, hact⟩ := hS.exists_act_eq_twisted hxT
  obtain ⟨M, hMS, rfl⟩ := exists_eq_miyamotoPull h L η (hWP.trans (miyamotoPull_le h L η _))
  have hMP : M ≤ miyamotoP h := (miyamotoPull_le_miyamotoPull_iff h L η hMS).1 hWP
  have hMc := (commute_miyamotoPull_iff h L η hMS).1 hcomm
  have hxC : x ∈ centralizer (miyamotoPull h L η M : Set G) :=
    mem_centralizer_iff.2 fun w hw => (hxW w hw).symm
  rw [card_miyamotoPull h L η hMS]
  refine two_mul_card_lt_of_twisted h hS.two_le _ (hS.exists_ne_of_fieldFactor_ne_one hσ) p hg
    hMP hMc fun y hy => ?_
  rw [← hact ⟨y, hMS hy⟩, act_apply]
  exact congrArg Subtype.val (miyamotoAct_apply_of_mem_centralizer h L η _ hxC hy)

theorem two_mul_card_lt_of_commute_mod_A1 (hS : Setting h L η t Q T) {x : G} (hxT : x ∈ T)
    (hσ : hS.fieldFactor ⟨x, hS.T_le hxT⟩ ≠ 1) {W : Subgroup G} (hWP : W ≤ miyamotoPG h L η)
    (hxW : ∀ w ∈ W, ⁅x, w⁆ ∈ miyamotoA1G h L η) :
    2 * Nat.card W < (2 ^ f) ^ 6 := by
  have : CharP K 2 := h.charP
  obtain ⟨p, g, hg, hact⟩ := hS.exists_act_eq_twisted hxT
  obtain ⟨M, hMS, rfl⟩ := exists_eq_miyamotoPull h L η (hWP.trans (miyamotoPull_le h L η _))
  have hMP : M ≤ miyamotoP h := (miyamotoPull_le_miyamotoPull_iff h L η hMS).1 hWP
  rw [card_miyamotoPull h L η hMS]
  refine two_mul_card_lt_of_twisted_mod_A1 h hS.two_le _
    (hS.exists_ne_of_fieldFactor_ne_one hσ) p hg hMP fun y hy => ?_
  set y' : gramSU h (miyamotoJ4 K) := ⟨y, hMS hy⟩
  rw [← hact y']
  change ((hS.act ⟨x, hS.T_le hxT⟩ y' * y'⁻¹ : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈
    miyamotoA1 h
  rw [← symm_mem_miyamotoPull_iff h L η, map_mul, map_inv, L.coe_mul, L.coe_inv,
    coe_symm_act_apply]
  have hw := hxW _ ((symm_mem_miyamotoPull_iff h L η (g := y')).2 hy)
  rwa [commutatorElement_def] at hw

theorem fieldFactor_eq_one_or_bar (hS : Setting h L η t Q T) (x : centralizer ({t} : Set G))
    (hx : hS.fieldFactor x * hS.fieldFactor x = 1) :
    hS.fieldFactor x = 1 ∨ hS.fieldFactor x = miyamotoBarEquiv h := by
  rcases ringEquiv_eq_refl_or_bar h hx with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (RingEquiv.ext h1)

theorem card_le_two_mul_card_inf_ker (hS : Setting h L η t Q T) {H : Subgroup G}
    (hHC : H ≤ centralizer ({t} : Set G))
    (hsq : ∀ x (hx : x ∈ H), hS.fieldFactor ⟨x, hHC hx⟩ * hS.fieldFactor ⟨x, hHC hx⟩ = 1) :
    Nat.card H ≤ 2 * Nat.card (H ⊓ (L ⊔ (centralizer (L : Set G) ⊓
      centralizer ({t} : Set G))) : Subgroup G) := by
  classical
  set φ : G → (K ≃+* K) := fun x =>
    if hx : x ∈ centralizer ({t} : Set G) then hS.fieldFactor ⟨x, hx⟩ else 1 with hφdef
  have hφ : ∀ x (hx : x ∈ centralizer ({t} : Set G)), φ x = hS.fieldFactor ⟨x, hx⟩ :=
    fun x hx => by simp [hφdef, hx]
  have key := card_le_card_inf_mul_ncard (H := H)
    (N := L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))) φ
    (T := ({1, miyamotoBarEquiv h} : Set (K ≃+* K))) (Set.toFinite _) (fun x hx => by
      rw [hφ x (hHC hx)]
      rcases hS.fieldFactor_eq_one_or_bar _ (hsq x hx) with h1 | h1
      · rw [h1]; exact Set.mem_insert _ _
      · rw [h1]; exact Set.mem_insert_of_mem _ rfl) fun x hx y hy e => by
      rw [hφ x (hHC hx), hφ y (hHC hy)] at e
      have h1 : hS.fieldFactor ((⟨x, hHC hx⟩ : centralizer ({t} : Set G))⁻¹ * ⟨y, hHC hy⟩) = 1 := by
        rw [map_mul, map_inv, e, inv_mul_cancel]
      obtain ⟨l, hl, c, hc, e'⟩ := (hS.fieldFactor_eq_one_iff _).1 h1
      have e'' : x⁻¹ * y = l * c := e'
      rw [e'']
      exact mul_mem (mem_sup_left hl) (mem_sup_right hc)
  have h2 : ({1, miyamotoBarEquiv h} : Set (K ≃+* K)).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  calc Nat.card H ≤ _ := key
    _ ≤ _ * 2 := Nat.mul_le_mul_left _ h2
    _ = _ := mul_comm _ _

theorem comm_of_isElementaryAbelian (_hS : Setting h L η t Q T) {X : Subgroup G}
    (hX : CFSG.IsElementaryAbelian 2 X) : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val ((hX.toIsMulCommutative.is_comm).comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem mul_self_of_isElementaryAbelian (_hS : Setting h L η t Q T) {X : Subgroup G}
    (hX : CFSG.IsElementaryAbelian 2 X) : ∀ x ∈ X, x * x = 1 := fun x hx => by
  rw [← sq]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx

theorem card_le_of_le_T_of_le_ker (hS : Setting h L η t Q T) {X : Subgroup G} (hXT : X ≤ T)
    (hX : CFSG.IsElementaryAbelian 2 X)
    (hXN : X ≤ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))) :
    Nat.card X ≤ 2 * (2 ^ f) ^ 4 ∧ (Nat.card X = 2 * (2 ^ f) ^ 4 → X = miyamotoB1 h L η t) := by
  have : CharP K 2 := h.charP
  have hxx := hS.mul_self_of_isElementaryAbelian hX
  have hXP : X ≤ miyamotoPG h L η ⊔ zpowers t := fun x hx => by
    obtain ⟨l, hl, c, hc, e⟩ := exists_mul_of_mem_sup_of_commute hS.L_comm_kernel (hXN hx)
    exact hS.mem_P_sup_zpowers_of_mul (hXT hx) (hxx x hx) hl hc e
  have hte : CFSG.IsElementaryAbelian 2 (zpowers t) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← hS.t_two, pow_orderOf_eq_one])
  have htX : zpowers t ≤ centralizer (X : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.1 (hS.T_le (hXT hx))
  have hX'e : CFSG.IsElementaryAbelian 2 (X ⊔ zpowers t : Subgroup G) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer htX
  have hX'P : X ⊔ zpowers t ≤ miyamotoPG h L η ⊔ zpowers t := sup_le hXP le_sup_right
  have hc' := hS.comm_of_isElementaryAbelian hX'e
  have hW := card_le_and_eq_A1G_of_commute h L η
    (inf_le_right : (X ⊔ zpowers t) ⊓ miyamotoPG h L η ≤ _)
    fun a ha b hb => hc' a (mem_inf.1 ha).1 b (mem_inf.1 hb).1
  have h1 := hS.card_le_two_mul_card_inf_P hX'P
  have h2 : Nat.card X ≤ Nat.card (X ⊔ zpowers t : Subgroup G) := card_le_of_le le_sup_left
  refine ⟨by omega, fun hcard => ?_⟩
  have hXX' : X = X ⊔ zpowers t := eq_of_le_of_card_ge le_sup_left (by omega)
  have hWA : (X ⊔ zpowers t) ⊓ miyamotoPG h L η = miyamotoA1G h L η := hW.2 (by omega)
  have hB : miyamotoB1 h L η t ≤ X := by
    refine sup_le (hXX'.symm ▸ le_sup_right) ?_
    rw [hXX', ← hWA]
    exact inf_le_left
  exact (eq_of_le_of_card_ge hB (by rw [hcard, hS.card_B1])).symm

theorem card_le_of_le_T (hS : Setting h L η t Q T) {X : Subgroup G} (hXT : X ≤ T)
    (hX : CFSG.IsElementaryAbelian 2 X) :
    Nat.card X ≤ 2 * (2 ^ f) ^ 4 ∧ (Nat.card X = 2 * (2 ^ f) ^ 4 → X = miyamotoB1 h L η t) := by
  have : CharP K 2 := h.charP
  have hxx := hS.mul_self_of_isElementaryAbelian hX
  have hcomm := hS.comm_of_isElementaryAbelian hX
  set N := L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) with hN
  by_cases hA : X ≤ N
  · exact hS.card_le_of_le_T_of_le_ker hXT hX hA
  obtain ⟨x₀, hx₀X, hx₀N⟩ := Set.not_subset.1 hA
  have hσ₀ : hS.fieldFactor ⟨x₀, hS.T_le (hXT hx₀X)⟩ ≠ 1 := fun h1 => hx₀N (by
    obtain ⟨l, hl, c, hc, e⟩ := (hS.fieldFactor_eq_one_iff _).1 h1
    rw [show x₀ = l * c from e]
    exact mul_mem (mem_sup_left hl) (mem_sup_right hc))
  have h1 := hS.card_le_two_mul_card_inf_ker (H := X) (hXT.trans hS.T_le) fun x hx => by
    rw [← map_mul]
    have : (⟨x, hS.T_le (hXT hx)⟩ : centralizer ({t} : Set G)) * ⟨x, hS.T_le (hXT hx)⟩ = 1 :=
      Subtype.ext (hxx x hx)
    rw [this, map_one]
  rw [← hN] at h1
  have hX₀P : X ⊓ N ≤ miyamotoPG h L η ⊔ zpowers t := fun x hx => by
    obtain ⟨hxX, hxN⟩ := mem_inf.1 hx
    obtain ⟨l, hl, c, hc, e⟩ := exists_mul_of_mem_sup_of_commute hS.L_comm_kernel hxN
    exact hS.mem_P_sup_zpowers_of_mul (hXT hxX) (hxx x hxX) hl hc e
  have h2 := hS.card_le_two_mul_card_inf_P hX₀P
  have h3 := hS.two_mul_card_lt_of_commute (hXT hx₀X) hσ₀
    (inf_le_right : X ⊓ N ⊓ miyamotoPG h L η ≤ _)
    (fun a ha b hb => hcomm a (mem_inf.1 (mem_inf.1 ha).1).1 b (mem_inf.1 (mem_inf.1 hb).1).1)
    fun w hw => hcomm x₀ hx₀X w (mem_inf.1 (mem_inf.1 hw).1).1
  refine ⟨by omega, fun hcard => by omega⟩

theorem card_le_of_le_centralizer (hS : Setting h L η t Q T) {X : Subgroup G}
    (hXC : X ≤ centralizer ({t} : Set G)) (hX : CFSG.IsElementaryAbelian 2 X) :
    Nat.card X ≤ 2 * (2 ^ f) ^ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf hS.T_sylow hXC (hX.isPGroup 2 X)
  have hX'T : X.map (MulAut.conj c⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hc x hx
  have hX'e : CFSG.IsElementaryAbelian 2 (X.map (MulAut.conj c⁻¹).toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  have hcard : Nat.card (X.map (MulAut.conj c⁻¹).toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  rw [← hcard]
  exact (hS.card_le_of_le_T hX'T hX'e).1

theorem exists_conj_eq_B1 (hS : Setting h L η t Q T) {X : Subgroup G}
    (hXC : X ≤ centralizer ({t} : Set G)) (hX : CFSG.IsElementaryAbelian 2 X)
    (hcard : Nat.card X = 2 * (2 ^ f) ^ 4) :
    ∃ c ∈ centralizer ({t} : Set G), X.map (MulAut.conj c⁻¹).toMonoidHom = miyamotoB1 h L η t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_isSylowOf hS.T_sylow hXC (hX.isPGroup 2 X)
  have hX'T : X.map (MulAut.conj c⁻¹).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hc x hx
  have hX'e : CFSG.IsElementaryAbelian 2 (X.map (MulAut.conj c⁻¹).toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  have hcard' : Nat.card (X.map (MulAut.conj c⁻¹).toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  exact ⟨c, hcC, (hS.card_le_of_le_T hX'T hX'e).2 (by rw [hcard', hcard])⟩

theorem conj_mem_L_of_perfect (hS : Setting h L η t Q T) {D : Subgroup G} (hD : ⁅D, D⁆ = D)
    {k : G} (hDk : ∀ d ∈ D, d * (k⁻¹ * t * k) = (k⁻¹ * t * k) * d) {d : G} (hd : d ∈ D) :
    k * d * k⁻¹ ∈ L := by
  set D' : Subgroup G := D.map (MulAut.conj k).toMonoidHom with hD'
  have hD'perf : ⁅D', D'⁆ = D' := by rw [hD', ← Subgroup.map_commutator, hD]
  have hD'C : D' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have h1 := hDk e he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k * e * k⁻¹ * t = k * (e * (k⁻¹ * t * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * t * k) * e) * k⁻¹ := by rw [h1]
      _ = t * (k * e * k⁻¹) := by group
  exact hS.perfect_le hD'perf hD'C ⟨d, hd, rfl⟩

theorem commutator_N2G (hS : Setting h L η t Q T) :
    ⁅miyamotoN2G h L η, miyamotoN2G h L η⁆ = miyamotoN2G h L η := by
  have : CharP K 2 := h.charP
  rw [← miyamotoPull_commutator h L η (miyamotoN2_le_gramSU h) (miyamotoN2_le_gramSU h),
    le_antisymm (commutator_le_self _) (miyamotoN2_le_commutator h hS.two_le)]

theorem exists_conj_mul_of_outer (hS : Setting h L η t Q T) {g : G}
    (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hσ : hS.fieldFactor ⟨g⁻¹ * t * g, hsC⟩ ≠ 1) :
    ∃ y ∈ L, y ≠ 1 ∧ ∃ g' : G, g'⁻¹ * t * g' = t * y := by
  have : CharP K 2 := h.charP
  set s := g⁻¹ * t * g with hsdef
  have hs2 : s * s = 1 := by
    rw [hsdef]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [hS.t_mul_t]; group
  set α := hS.act ⟨s, hsC⟩ with hαdef
  have hα1 : α ≠ 1 := fun h1 => hσ (by
    change miyamotoFieldFactor h α = 1
    rw [h1, map_one])
  have hα2 : orderOf α = 2 := by
    refine orderOf_eq_prime ?_ hα1
    rw [sq, hαdef, ← map_mul]
    have : (⟨s, hsC⟩ : centralizer ({t} : Set G)) * ⟨s, hsC⟩ = 1 := Subtype.ext hs2
    rw [this, map_one]
  obtain ⟨τ, hτ⟩ := exists_conj_eq_u_or_uz1 h hα2 hσ
  set m : G := ((η.symm τ : L) : G) with hm
  have hmL : m ∈ L := (η.symm τ).2
  have hmC : m ∈ centralizer ({t} : Set G) := hS.L_le_centralizer hmL
  set s' := m * s * m⁻¹ with hs'def
  have hs'C : s' ∈ centralizer ({t} : Set G) := mul_mem (mul_mem hmC hsC) (inv_mem hmC)
  have hact' : hS.act ⟨s', hs'C⟩ = MulAut.conj τ * α * (MulAut.conj τ)⁻¹ := by
    have e : (⟨s', hs'C⟩ : centralizer ({t} : Set G)) =
        ⟨m, hmC⟩ * ⟨s, hsC⟩ * (⟨m, hmC⟩ : centralizer ({t} : Set G))⁻¹ := rfl
    have hτ' : η ⟨m, hmL⟩ = τ := by
      have : (⟨m, hmL⟩ : L) = η.symm τ := rfl
      rw [this, MulEquiv.apply_symm_apply]
    rw [e, map_mul, map_mul, map_inv, hS.act_of_mem hmL, hτ']
  obtain ⟨n₀, v₀, w₀, hn₀, hv₀, hN₂, hw₀, hne⟩ := exists_lang_data h hS.two_le hτ
  rw [← hact'] at hv₀ hN₂ hw₀
  have hfix : ∀ y : gramSU h (miyamotoJ4 K), hS.act ⟨s', hs'C⟩ y = y →
      s' * ((η.symm y : L) : G) = ((η.symm y : L) : G) * s' := by
    intro y hy
    have e := hS.coe_symm_act_apply ⟨s', hs'C⟩ y
    rw [hy] at e
    calc s' * ((η.symm y : L) : G) = s' * ((η.symm y : L) : G) * s'⁻¹ * s' := by group
      _ = ((η.symm y : L) : G) * s' := by rw [← e]
  set n : G := ((η.symm n₀ : L) : G)
  set v : G := ((η.symm v₀ : L) : G)
  set w : G := ((η.symm w₀ : L) : G)
  have hss : s' * s' = 1 := by
    rw [hs'def]
    calc m * s * m⁻¹ * (m * s * m⁻¹) = m * (s * s) * m⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hs'inv : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hss
  have hws : w⁻¹ * s' * w = s' * (n * v * n⁻¹ * v⁻¹) := by
    have e := hS.coe_symm_act_apply ⟨s', hs'C⟩ w₀⁻¹
    have e2 : s' * w⁻¹ * s'⁻¹ * w = n * v * n⁻¹ * v⁻¹ := by
      have e3 : ((η.symm (hS.act ⟨s', hs'C⟩ w₀⁻¹ * w₀) : L) : G) = n * v * n⁻¹ * v⁻¹ := by
        rw [map_inv, hw₀]
        simp only [map_mul, map_inv, L.coe_mul, L.coe_inv]
        rfl
      rw [← e3, map_mul, L.coe_mul, e, map_inv, L.coe_inv]
    rw [← e2]
    calc w⁻¹ * s' * w = (s' * s') * (w⁻¹ * s'⁻¹ * w) := by rw [hss, one_mul, hs'inv]
      _ = s' * (s' * w⁻¹ * s'⁻¹ * w) := by group
  set k := g * m⁻¹ with hk
  have hks : k⁻¹ * t * k = s' := by rw [hk, hs'def, hsdef]; group
  have hD : ∀ d ∈ miyamotoN2G h L η, d * (k⁻¹ * t * k) = (k⁻¹ * t * k) * d := by
    intro d hd
    obtain ⟨y, hy, rfl⟩ := (mem_miyamotoPull h L η).1 hd
    rw [hks]
    exact (hfix y (hN₂ y hy)).symm
  have hnL : k * n * k⁻¹ ∈ L := hS.conj_mem_L_of_perfect hS.commutator_N2G hD
    ((symm_mem_miyamotoPull_iff h L η).2 hn₀)
  have hvC : k * v * k⁻¹ ∈ centralizer ({t} : Set G) := by
    refine mem_centralizer_singleton_iff.2 ?_
    have h1 := hfix v₀ hv₀
    rw [← hks] at h1
    calc k * v * k⁻¹ * t = k * (v * (k⁻¹ * t * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * t * k) * v) * k⁻¹ := by rw [← h1]
      _ = t * (k * v * k⁻¹) := by group
  have hvN := hS.centralizer_le_normalizer hvC
  set y := k * (n * v * n⁻¹ * v⁻¹) * k⁻¹ with hy
  have hyL : y ∈ L := by
    have e : y = (k * n * k⁻¹) * ((k * v * k⁻¹) * (k * n * k⁻¹)⁻¹ * (k * v * k⁻¹)⁻¹) := by
      rw [hy]; group
    rw [e]
    exact mul_mem hnL ((mem_normalizer_iff.1 hvN _).1 (inv_mem hnL))
  have hy1 : y ≠ 1 := by
    intro e
    apply hne
    apply η.symm.injective
    apply Subtype.ext
    have e' : n * v * n⁻¹ * v⁻¹ = 1 := by
      calc n * v * n⁻¹ * v⁻¹ = k⁻¹ * y * k := by rw [hy]; group
        _ = 1 := by rw [e]; group
    simp only [map_mul, map_inv, map_one, L.coe_mul, L.coe_inv, OneMemClass.coe_one]
    exact e'
  refine ⟨y, hyL, hy1, k * w * k⁻¹, ?_⟩
  calc (k * w * k⁻¹)⁻¹ * t * (k * w * k⁻¹) = k * (w⁻¹ * (k⁻¹ * t * k) * w) * k⁻¹ := by group
    _ = k * (s' * (n * v * n⁻¹ * v⁻¹)) * k⁻¹ := by rw [hks, hws]
    _ = (k * s' * k⁻¹) * y := by rw [hy]; group
    _ = t * y := by rw [← hks]; group

theorem exists_conj_mem_A1G (_hS : Setting h L η t Q T) {l : G} (hl : l ∈ L)
    (hl2 : l * l = 1) : ∃ m ∈ L, m⁻¹ * l * m ∈ miyamotoA1G h L η := by
  have : CharP K 2 := h.charP
  by_cases hl1 : l = 1
  · exact ⟨1, one_mem _, by rw [hl1]; simp⟩
  have ho : orderOf l = 2 := orderOf_eq_prime (by rw [sq]; exact hl2) hl1
  obtain ⟨-, -, -, -, hcls, -⟩ := miyamoto_two_fourG h L η
  obtain ⟨m, hm, hmz | hmz⟩ := hcls l hl ho
  · refine ⟨m, hm, ?_⟩
    rw [hmz]
    unfold miyamotoZ1G
    rw [symm_mem_miyamotoPull_iff h L η]
    change miyamotoZ1 K ∈ miyamotoA1 h
    rw [miyamotoZ1_eq h]
    exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_one _⟩
  · refine ⟨m, hm, ?_⟩
    rw [hmz]
    unfold miyamotoZ2G
    rw [symm_mem_miyamotoPull_iff h L η]
    change LocalAnalysis.miyamotoZ2 K ∈ miyamotoA1 h
    rw [miyamotoZ2_eq h]
    exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_zero _⟩

theorem exists_conj_mem_B1_of_inner (hS : Setting h L η t Q T) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G)) (hxLC : x ∈ L ⊔ centralizer (L : Set G))
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxt : x ≠ t) :
    ∃ m ∈ L, m⁻¹ * x * m ∈ miyamotoB1 h L η t ∧ m⁻¹ * x * m ≠ t := by
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute hS.L_comm_centralizer hxLC
  have hlc : l * c = c * l := hS.L_comm_centralizer l hl c hc
  have hcT : c ∈ centralizer ({t} : Set G) := by
    have h1 : l⁻¹ * (l * c) ∈ centralizer ({t} : Set G) :=
      mul_mem (inv_mem (hS.L_le_centralizer hl)) hxC
    rwa [inv_mul_cancel_left] at h1
  have hll : l * l = 1 ∧ c * c = 1 := by
    have hsq : (l * l) * (c * c) = 1 := by
      calc (l * l) * (c * c) = l * (l * c) * c := by group
        _ = l * (c * l) * c := by rw [hlc]
        _ = (l * c) * (l * c) := by group
        _ = 1 := hx2
    have hmem : l * l ∈ L ⊓ centralizer (L : Set G) := by
      refine Subgroup.mem_inf.2 ⟨L.mul_mem hl hl, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hsq]
      exact (centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).mul_mem hc hc)
    rw [hS.inf_centralizer_eq_bot, mem_bot] at hmem
    refine ⟨hmem, ?_⟩
    rw [hmem, one_mul] at hsq
    exact hsq
  have hct : c ∈ zpowers t := by
    by_cases h1 : c = 1
    · rw [h1]; exact one_mem _
    · rw [hS.eq_t_of_mem_kernel ⟨hc, hcT⟩ (orderOf_eq_prime (by rw [sq]; exact hll.2) h1)]
      exact mem_zpowers _
  have hl1 : l ≠ 1 := by
    rintro rfl
    rw [one_mul] at hx1 hxt
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hct
    rcases hS.zpow_t_eq k with h0 | h0
    · rw [← hk, h0] at hx1
      exact hx1 rfl
    · rw [← hk, h0] at hxt
      exact hxt rfl
  obtain ⟨m, hm, hmA⟩ := hS.exists_conj_mem_A1G hl hll.1
  have hcm : m⁻¹ * c * m = c := by
    rw [mul_assoc, ← (hS.L_comm_centralizer m hm c hc), ← mul_assoc, inv_mul_cancel, one_mul]
  have heq : m⁻¹ * (l * c) * m = (m⁻¹ * l * m) * c := by
    rw [show m⁻¹ * (l * c) * m = (m⁻¹ * l * m) * (m⁻¹ * c * m) by group, hcm]
  refine ⟨m, hm, ?_, ?_⟩
  · rw [heq]
    exact mul_mem (mem_sup_right hmA) (mem_sup_left hct)
  · rw [heq]
    intro hEq
    have hmem : m⁻¹ * l * m ∈ L ⊓ centralizer (L : Set G) := by
      refine Subgroup.mem_inf.2 ⟨L.mul_mem (L.mul_mem (L.inv_mem hm) hl) hm, ?_⟩
      rw [eq_mul_inv_of_mul_eq hEq]
      exact (centralizer (L : Set G)).mul_mem hS.t_mem ((centralizer (L : Set G)).inv_mem hc)
    rw [hS.inf_centralizer_eq_bot, mem_bot] at hmem
    apply hl1
    calc l = m * (m⁻¹ * l * m) * m⁻¹ := by group
      _ = 1 := by rw [hmem]; group

theorem exists_conj_mem_B1 (hS : Setting h L η t Q T) :
    ∃ g : G, g⁻¹ * t * g ∈ miyamotoB1 h L η t ∧ g⁻¹ * t * g ≠ t := by
  have := hS.simple
  obtain ⟨g, hne, hcomm⟩ :=
    CFSG.SeitzReduction.F4Pilot.exists_conj_ne_commute_of_isSimpleGroup hS.nonabelian hS.t_two
  have key : ∀ g₀ : G, g₀⁻¹ * t * g₀ ∈ centralizer ({t} : Set G) →
      g₀⁻¹ * t * g₀ ∈ L ⊔ centralizer (L : Set G) → g₀⁻¹ * t * g₀ ≠ t →
      ∃ g : G, g⁻¹ * t * g ∈ miyamotoB1 h L η t ∧ g⁻¹ * t * g ≠ t := by
    intro g₀ hC hLC hne₀
    have h2 : g₀⁻¹ * t * g₀ * (g₀⁻¹ * t * g₀) = 1 := by
      calc g₀⁻¹ * t * g₀ * (g₀⁻¹ * t * g₀) = g₀⁻¹ * (t * t) * g₀ := by group
        _ = 1 := by rw [hS.t_mul_t]; group
    have h1 : g₀⁻¹ * t * g₀ ≠ 1 := fun h1 => hS.t_ne_one (by
      calc t = g₀ * (g₀⁻¹ * t * g₀) * g₀⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    obtain ⟨m, -, hmB, hmne⟩ := hS.exists_conj_mem_B1_of_inner hC hLC h2 h1 hne₀
    refine ⟨g₀ * m, ?_, ?_⟩
    · rw [show (g₀ * m)⁻¹ * t * (g₀ * m) = m⁻¹ * (g₀⁻¹ * t * g₀) * m by group]
      exact hmB
    · rw [show (g₀ * m)⁻¹ * t * (g₀ * m) = m⁻¹ * (g₀⁻¹ * t * g₀) * m by group]
      exact hmne
  have hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hcomm
  by_cases hin : hS.fieldFactor ⟨g⁻¹ * t * g, hsC⟩ = 1
  · obtain ⟨l, hl, c, hc, e⟩ := (hS.fieldFactor_eq_one_iff _).1 hin
    refine key g hsC ?_ hne
    rw [show g⁻¹ * t * g = l * c from e]
    exact mul_mem (mem_sup_left hl) (mem_sup_right (mem_inf.1 hc).1)
  · obtain ⟨y, hyL, hy1, g', hg'⟩ := hS.exists_conj_mul_of_outer hsC hin
    refine key g' ?_ ?_ ?_
    · rw [hg']
      refine mem_centralizer_singleton_iff.2 ?_
      rw [mul_assoc, hS.comm_t_of_mem_L hyL]
    · rw [hg']
      exact mul_mem (mem_sup_right hS.t_mem) (mem_sup_left hyL)
    · rw [hg']
      intro h1
      apply hy1
      calc y = t⁻¹ * (t * y) := by group
        _ = 1 := by rw [h1, inv_mul_cancel]

theorem B1_le_T (hS : Setting h L η t Q T) : miyamotoB1 h L η t ≤ T :=
  hS.B1_le_Q.trans hS.Q_le_T

theorem t_mem_B1 (_hS : Setting h L η t Q T) : t ∈ miyamotoB1 h L η t :=
  mem_sup_left (mem_zpowers t)

theorem B1_comm (hS : Setting h L η t Q T) :
    ∀ x ∈ miyamotoB1 h L η t, ∀ y ∈ miyamotoB1 h L η t, x * y = y * x :=
  hS.comm_of_isElementaryAbelian hS.isElementaryAbelian_B1

theorem B1_le_R (hS : Setting h L η t Q T) :
    miyamotoB1 h L η t ≤ T ⊓ centralizer (miyamotoB1 h L η t : Set G) :=
  le_inf hS.B1_le_T fun x hx => mem_centralizer_iff.2 fun y hy => hS.B1_comm y hy x hx

theorem kernel_le_R (hS : Setting h L η t Q T) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) ≤
      T ⊓ centralizer (miyamotoB1 h L η t : Set G) := by
  intro c hc
  refine mem_inf.2 ⟨hS.kernel_le_T hc, mem_centralizer_iff.2 fun b hb => ?_⟩
  have hle : miyamotoB1 h L η t ≤ centralizer ({c} : Set G) := by
    refine sup_le ?_ fun a ha => mem_centralizer_singleton_iff.2
      (hS.L_comm_kernel a (miyamotoPull_le h L η _ ha) c hc)
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2).symm
  exact mem_centralizer_singleton_iff.1 (hle hb)

theorem weakly_closed_R (hS : Setting h L η t Q T) (c : G)
    (hc : ∀ r ∈ T ⊓ centralizer (miyamotoB1 h L η t : Set G), c⁻¹ * r * c ∈ T) :
    ∀ r ∈ T ⊓ centralizer (miyamotoB1 h L η t : Set G),
      c⁻¹ * r * c ∈ T ⊓ centralizer (miyamotoB1 h L η t : Set G) := by
  set X : Subgroup G := (miyamotoB1 h L η t).map (MulAut.conj c⁻¹).toMonoidHom with hX
  have hXT : X ≤ T := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply] using hc b (hS.B1_le_R hb)
  have := hS.isElementaryAbelian_B1
  have hXe : CFSG.IsElementaryAbelian 2 X := CFSG.IsElementaryAbelian.map _
  have hXc : Nat.card X = 2 * (2 ^ f) ^ 4 := by
    rw [hX, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hS.card_B1]
  have hXB := (hS.card_le_of_le_T hXT hXe).2 hXc
  intro r hr
  refine Subgroup.mem_inf.2 ⟨hc r hr, mem_centralizer_iff.2 fun b hb => ?_⟩
  rw [← hXB] at hb
  obtain ⟨b', hb', rfl⟩ := hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hrb : b' * r = r * b' := mem_centralizer_iff.1 (mem_inf.1 hr).2 b' hb'
  calc c⁻¹ * b' * c * (c⁻¹ * r * c) = c⁻¹ * (b' * r) * c := by group
    _ = c⁻¹ * (r * b') * c := by rw [hrb]
    _ = c⁻¹ * r * c * (c⁻¹ * b' * c) := by group

theorem R_le (hS : Setting h L η t Q T) :
    T ⊓ centralizer (miyamotoB1 h L η t : Set G) ≤
      miyamotoA1G h L η ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
  have : CharP K 2 := h.charP
  intro r hr
  obtain ⟨hrT, hrB⟩ := mem_inf.1 hr
  have hrN : r ∈ normalizer (L : Set G) := hS.T_le_normalizer hrT
  have hrA : r ∈ centralizer (miyamotoA1G h L η : Set G) :=
    mem_centralizer_iff.2 fun a ha => mem_centralizer_iff.1 hrB a (mem_sup_right ha)
  obtain ⟨a, haA, ha⟩ := (fixes_miyamotoA1_iff h _).1 fun g hg =>
    miyamotoAct_apply_of_mem_centralizer h L η ⟨r, hrN⟩ hrA hg
  obtain ⟨c, hcL, hrc⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η ⟨r, hrN⟩ a ha
  have hrc' : r = ((η.symm a : L) : G) * c := hrc
  have haG : ((η.symm a : L) : G) ∈ miyamotoA1G h L η := (symm_mem_miyamotoPull_iff h L η).2 haA
  have hcC : c ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem (hS.L_le_centralizer (η.symm a).2)) (hS.T_le hrT)
    rwa [hrc', inv_mul_cancel_left] at this
  rw [hrc']
  exact mul_mem (mem_sup_left haG) (mem_sup_right (mem_inf.2 ⟨hcL, hcC⟩))

theorem kernel_eq_zpowers' (hS : Setting h L η t Q T) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := centralizer (L : Set G) ⊓ centralizer ({t} : Set G) with hSdef
  set R := T ⊓ centralizer (miyamotoB1 h L η t : Set G) with hRdef
  by_contra hne
  have hcyc := hS.isCyclic_kernel
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS.isPGroup_kernel
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    apply hne
    symm
    apply Subgroup.eq_of_le_of_card_ge hS.zpowers_le_kernel
    rw [hn, hS.card_zpowers_t]
    interval_cases n <;> norm_num
  set k := 2 ^ (n - 1) with hk
  have hk2 : Nat.card S = 2 * k := by
    rw [hn, hk, ← pow_succ']
    congr 1
    omega
  have hkeven : Even k := by
    rw [hk]
    exact (Nat.even_pow' (by omega)).2 even_two
  have hkpos : 0 < k := by positivity
  obtain ⟨⟨s₀, hs₀⟩, hgen⟩ := hcyc.exists_generator
  have hord : orderOf s₀ = 2 * k := by
    rw [← hk2, ← orderOf_eq_card_of_forall_mem_zpowers hgen, Subgroup.orderOf_mk]
  have hs₀k : s₀ ^ k = t := by
    apply hS.eq_t_of_mem_kernel (pow_mem hs₀ k)
    apply orderOf_eq_prime
    · rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
    · intro h1
      have := orderOf_le_of_pow_eq_one hkpos h1
      omega
  have hA₁ := isElementaryAbelian_miyamotoA1G h L η
  have hA₁S : ∀ x ∈ miyamotoA1G h L η, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    hS.L_comm_kernel x (miyamotoPull_le h L η _ hx) y hy
  have hpow : ∀ z ∈ miyamotoA1G h L η ⊔ S, z ^ k = 1 ∨ z ^ k = t := by
    intro z hz
    obtain ⟨a, ha, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_commute hA₁S hz
    rw [Commute.mul_pow (hA₁S a ha s hs) k]
    have hak : a ^ k = 1 := by
      obtain ⟨j, hj⟩ := hkeven
      rw [hj, ← two_mul, pow_mul, CFSG.elemPow_eq_one_of_isElementaryAbelian a ha, one_pow]
    have hsk : (s ^ k) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, ← hk2]
      exact congrArg Subtype.val (pow_card_eq_one' (G := S) (x := ⟨s, hs⟩))
    rw [hak, one_mul]
    by_cases h1 : s ^ k = 1
    · exact Or.inl h1
    · exact Or.inr (hS.eq_t_of_mem_kernel (pow_mem hs k) (orderOf_eq_prime hsk h1))
  obtain ⟨g, hgB, hgne⟩ := hS.exists_conj_mem_B1
  obtain ⟨n', hn'N, hn't⟩ := exists_normalizer_conj_eq_of_weakly_closed_in hS.T_sylow
    (inf_le_left : R ≤ T) hS.weakly_closed_R (g := g)
    (fun r hr => (mem_centralizer_iff.1 (mem_inf.1 hr).2 _ hgB).symm)
  have hconjR : n'⁻¹ * s₀ * n' ∈ R := by
    have := (mem_normalizer_iff.1 (inv_mem hn'N) s₀).1 (hS.kernel_le_R hs₀)
    rwa [inv_inv] at this
  have hconjk : (n'⁻¹ * s₀ * n') ^ k = n'⁻¹ * t * n' := by
    have := map_pow (MulAut.conj n'⁻¹) s₀ k
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [← this, hs₀k]
  rcases hpow _ (hS.R_le hconjR) with h1 | h1
  · rw [hconjk] at h1
    apply hS.t_ne_one
    calc t = n' * (n'⁻¹ * t * n') * n'⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · rw [hconjk, hn't] at h1
    exact hgne h1

theorem card_kernel (hS : Setting h L η t Q T) :
    Nat.card (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 := by
  rw [hS.kernel_eq_zpowers', hS.card_zpowers_t]

theorem T_inf_centralizer_B1 (hS : Setting h L η t Q T) :
    T ⊓ centralizer (miyamotoB1 h L η t : Set G) = miyamotoB1 h L η t := by
  refine le_antisymm ?_ hS.B1_le_R
  have := hS.R_le
  rwa [hS.kernel_eq_zpowers', sup_comm] at this

theorem Q_eq (hS : Setting h L η t Q T) : Q = miyamotoPG h L η ⊔ zpowers t := by
  refine le_antisymm (fun q hq => ?_) (sup_le hS.P_le_Q ((zpowers_le).2 hS.t_mem_Q))
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute hS.L_comm_centralizer
    (hS.Q_le hq)
  have hcC : c ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem (hS.L_le_centralizer hl)) (hS.Q_le_centralizer hq)
    rwa [inv_mul_cancel_left] at this
  have hck : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := mem_inf.2 ⟨hc, hcC⟩
  have hlP := hS.mem_P_of_mul (hS.Q_le_T hq) hl hck rfl
  rw [hS.kernel_eq_zpowers'] at hck
  exact mul_mem (mem_sup_left hlP) (mem_sup_right hck)

theorem exists_normalizer_B1_conj_eq (hS : Setting h L η t Q T) {g : G}
    (hg : g⁻¹ * t * g ∈ miyamotoB1 h L η t) :
    ∃ n ∈ normalizer (miyamotoB1 h L η t : Set G), n⁻¹ * t * n = g⁻¹ * t * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := hS.T_inf_centralizer_B1
  obtain ⟨n, hn, hnt⟩ := exists_normalizer_conj_eq_of_weakly_closed_in hS.T_sylow
    (inf_le_left : T ⊓ centralizer (miyamotoB1 h L η t : Set G) ≤ T) hS.weakly_closed_R (g := g)
    (fun r hr => (mem_centralizer_iff.1 (mem_inf.1 hr).2 _ hg).symm)
  rw [hR] at hn
  exact ⟨n, hn, hnt⟩

theorem conj_set_B1 (hS : Setting h L η t Q T) :
    {x | ∃ n ∈ normalizer (miyamotoB1 h L η t : Set G), x = n⁻¹ * t * n} =
        {x | ∃ g : G, x = g⁻¹ * t * g} ∩ (miyamotoB1 h L η t : Set G) ∧
      {x | ∃ g : G, x = g⁻¹ * t * g} ∩ (miyamotoB1 h L η t : Set G) ≠ {t} := by
  refine ⟨Set.Subset.antisymm ?_ ?_, fun e => ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    refine ⟨⟨n, rfl⟩, ?_⟩
    have := (mem_normalizer_iff.1 (inv_mem hn) t).1 hS.t_mem_B1
    rwa [inv_inv] at this
  · rintro _ ⟨⟨g, rfl⟩, hg⟩
    obtain ⟨n, hn, hnt⟩ := hS.exists_normalizer_B1_conj_eq hg
    exact ⟨n, hn, hnt.symm⟩
  · obtain ⟨g, hgB, hgne⟩ := hS.exists_conj_mem_B1
    have hmem : g⁻¹ * t * g ∈ {x | ∃ g : G, x = g⁻¹ * t * g} ∩ (miyamotoB1 h L η t : Set G) :=
      ⟨⟨g, rfl⟩, hgB⟩
    rw [e] at hmem
    exact hgne hmem

theorem conj_not_mem_L (hS : Setting h L η t Q T) (g : G) : g⁻¹ * t * g ∉ L := by
  have : CharP K 2 := h.charP
  intro hgL
  have hzo : orderOf (g⁻¹ * t * g) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    rw [MulAut.conj_apply, inv_inv] at this
    rw [this, hS.t_two]
  obtain ⟨-, -, -, -, hcls, -⟩ := miyamoto_two_fourG h L η
  obtain ⟨m, -, hz⟩ := hcls _ hgL hzo
  set k := g * m with hk
  have hkt : k⁻¹ * t * k = m⁻¹ * (g⁻¹ * t * g) * m := by rw [hk]; group
  have key : ∀ D : Subgroup G, ⁅D, D⁆ = D → k⁻¹ * t * k ∈ D →
      D ≤ centralizer ({k⁻¹ * t * k} : Set G) → False := by
    intro D hD hzD hDC
    have h1 := hS.conj_mem_L_of_perfect hD (fun d hd => mem_centralizer_singleton_iff.1 (hDC hd))
      hzD
    rw [show k * (k⁻¹ * t * k) * k⁻¹ = t by group] at h1
    exact hS.t_not_mem_L h1
  rcases hz with hz | hz
  ·
    rw [← hkt] at hz
    have hA2N2 : miyamotoUnipotent h false true ⊔ miyamotoN2 h ≤
        gramSU h (miyamotoJ4 K) ⊓ centralizer ({miyamotoZ1 K} : Set (GL (Fin 4) K)) := by
      have hz1 : miyamotoZ1 K ∈ miyamotoZ h := by
        rw [miyamotoZ1_eq h]
        exact ⟨1, map_one _, rfl⟩
      refine sup_le (le_inf (miyamotoUnipotent_le_SU h false true) fun a ha => ?_)
        (le_inf (miyamotoN2_le_gramSU h) fun n hn =>
          mem_centralizer_singleton_iff.2 (miyamotoN2_commute_Z h hn hz1))
      obtain ⟨a', c, d, -, rfl⟩ := (mem_A2 h).1 ha
      refine mem_centralizer_singleton_iff.2 ?_
      rw [miyamotoZ1_eq h]
      exact (miyamotoZ1_comm_miyamotoXGL h (map_zero _)).symm
    refine key _ (commutator_miyamotoA2G_sup_N2G h L η hS.two_le) ?_ ?_
    · rw [hz, ← miyamotoPull_sup h L η (miyamotoUnipotent_le_SU h false true)
        (miyamotoN2_le_gramSU h)]
      unfold miyamotoZ1G
      rw [symm_mem_miyamotoPull_iff h L η]
      refine mem_sup_left ?_
      change miyamotoZ1 K ∈ miyamotoA2 h
      rw [miyamotoZ1_eq h, miyamotoXGL_mem_A2 h]
      refine ⟨rfl, ?_⟩
      simp only [map_one, map_zero, mul_zero, add_zero]
      exact CharTwo.add_self_eq_zero 1
    · rw [hz, ← miyamotoPull_sup h L η (miyamotoUnipotent_le_SU h false true)
        (miyamotoN2_le_gramSU h)]
      refine (miyamotoPull_mono h L η hA2N2).trans ?_
      rw [miyamotoPull_inf_centralizer_singleton h L η (miyamotoZ1_mem_gramSU h)]
      exact inf_le_right
  ·
    rw [← hkt] at hz
    obtain ⟨hD, hperf⟩ := commutator_centralizer_miyamotoZ2G h L η hS.two_le
    refine key _ hperf ?_ ?_
    · rw [hz]
      unfold miyamotoZ2G
      rw [symm_mem_miyamotoPull_iff h L η]
      refine mem_sup_left (mem_inf.2 ⟨?_, ?_⟩)
      · change LocalAnalysis.miyamotoZ2 K ∈ miyamotoA1 h
        rw [miyamotoZ2_eq h]
        exact (miyamotoXGL_mem_A1 h).2 ⟨rfl, map_zero _, map_zero _⟩
      · change LocalAnalysis.miyamotoZ2 K ∈ miyamotoCu h
        rw [miyamotoZ2_eq h, miyamotoXGL_mem_Cu h]
        exact ⟨map_zero _, map_zero _, map_one _, map_zero _⟩
    · rw [← hD, hz]
      exact (commutator_le_self _).trans inf_le_right

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
