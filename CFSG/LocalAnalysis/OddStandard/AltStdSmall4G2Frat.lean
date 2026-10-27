module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Next

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Subgroup Matrix
open scoped Pointwise

namespace Frat

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem exists_inv_mul_mem_normalizer {H X : Subgroup G} (hXH : X ≤ H) (hX : IsPGroup 2 X)
    (hmax : ∀ S : Subgroup G, S ≤ H → IsPGroup 2 S → X ≤ S → S ≤ X) {κ : G}
    (hκ : κ ∈ normalizer (H : Set G)) : ∃ d ∈ H, d⁻¹ * κ ∈ normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := X.map (MulAut.conj κ).toMonoidHom with hY
  have hmemY : ∀ x, κ * x * κ⁻¹ ∈ Y ↔ x ∈ X := by
    intro x
    constructor
    · rintro ⟨x', hx', hxx'⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxx'
      rwa [mul_left_cancel (mul_right_cancel hxx')] at hx'
    · intro hx
      exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hYH : Y ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (mem_normalizer_iff.1 hκ x).1 (hXH hx)
  have hYc : Nat.card Y = Nat.card X :=
    card_map_of_injective (f := (MulAut.conj κ).toMonoidHom) (MulAut.conj κ).injective
  have hX' : IsPGroup 2 (X.subgroupOf H) := hX.of_equiv (subgroupOfEquivOfLe hXH).symm
  have hY' : IsPGroup 2 (Y.subgroupOf H) := (hX.map _).of_equiv (subgroupOfEquivOfLe hYH).symm
  obtain ⟨S₁, hS₁⟩ := hX'.exists_le_sylow
  obtain ⟨S₂, hS₂⟩ := hY'.exists_le_sylow
  have hS₁X : (S₁ : Subgroup H) = X.subgroupOf H := by
    refine le_antisymm (fun s hs => ?_) hS₁
    have hs' : (s : G) ∈ (S₁ : Subgroup H).map H.subtype := ⟨s, hs, rfl⟩
    exact hmax _ (map_subtype_le _) (S₁.isPGroup'.map _)
      (fun x hx => ⟨⟨x, hXH hx⟩, hS₁ hx, rfl⟩) hs'
  have hS₂Y : Y.subgroupOf H = (S₂ : Subgroup H) := by
    refine Subgroup.eq_of_le_of_card_ge hS₂ (le_of_eq ?_)
    rw [Sylow.card_eq_multiplicity S₂, ← Sylow.card_eq_multiplicity S₁, hS₁X,
      Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hYH).toEquiv, hYc]
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq H S₁ S₂
  have hmem : ∀ y : H, (y : G) ∈ Y ↔ (d : G)⁻¹ * y * d ∈ X := by
    intro y
    have h1 : y ∈ Y.subgroupOf H ↔ d⁻¹ * y * d ∈ X.subgroupOf H := by
      rw [hS₂Y, ← hS₁X, ← hd, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem,
        MulAut.smul_def, MulAut.conj_inv_apply]
    rw [mem_subgroupOf, mem_subgroupOf] at h1
    exact h1
  refine ⟨(d : G), d.2, ?_⟩
  rw [mem_normalizer_iff]
  intro x
  have e : (d : G)⁻¹ * κ * x * ((d : G)⁻¹ * κ)⁻¹ = (d : G)⁻¹ * (κ * x * κ⁻¹) * d := by group
  rw [e, ← hmemY x]
  constructor
  · intro hx
    exact (hmem ⟨_, hYH hx⟩).1 hx
  · intro hx
    have hxH : κ * x * κ⁻¹ ∈ H := by
      have : κ * x * κ⁻¹ = d * ((d : G)⁻¹ * (κ * x * κ⁻¹) * d) * (d : G)⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem d.2 (hXH hx)) (inv_mem d.2)
    exact (hmem ⟨_, hxH⟩).2 hx

end Sylow

section Basic

variable {G : Type} [Group G]

theorem conj_mem_centralizer {A : Subgroup G} {κ : G} (hκ : κ ∈ normalizer (A : Set G)) {y : G}
    (hy : y ∈ centralizer (A : Set G)) : κ * y * κ⁻¹ ∈ centralizer (A : Set G) := by
  rw [mem_centralizer_iff]
  intro a ha
  have ha' : κ⁻¹ * a * κ ∈ A := by
    have := (mem_normalizer_iff.1 (inv_mem hκ) a).1 ha
    rwa [inv_inv] at this
  have hc := mem_centralizer_iff.1 hy _ ha'
  calc a * (κ * y * κ⁻¹) = κ * ((κ⁻¹ * a * κ) * y) * κ⁻¹ := by group
    _ = κ * (y * (κ⁻¹ * a * κ)) * κ⁻¹ := by rw [hc]
    _ = κ * y * κ⁻¹ * a := by group

theorem A'_le_cstar {L : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)} {hn : 8 ≤ n}
    {z : G} {k : ℕ} {A P A' : Subgroup G} (hs : StepData θ hn z k A P A') :
    A' ≤ RA θ hn z A ⊓ centralizer (A : Set G) :=
  le_inf hs.A'_le_RA hs.A'_le_centralizer

end Basic

section Config

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {k : ℕ} {A P A' : Subgroup G}
  (c : Config G L Q n θ z)

theorem KA_mem_normalizer (h : LevelDatum θ c.hn8 z k A) {κ : G} (hκ : κ ∈ KA L z A) :
    κ ∈ normalizer ((RA θ c.hn8 z A ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  have key : ∀ κ ∈ KA L z A, ∀ y ∈ RA θ c.hn8 z A ⊓ centralizer (A : Set G),
      κ * y * κ⁻¹ ∈ RA θ c.hn8 z A ⊓ centralizer (A : Set G) := fun κ hκ y hy =>
    Subgroup.mem_inf.2 ⟨KA_conj_mem_RA c h hκ (Subgroup.mem_inf.1 hy).1,
      conj_mem_centralizer (KA_le_normalizer hκ) (Subgroup.mem_inf.1 hy).2⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key κ hκ y, fun hy => ?_⟩
  have := key κ⁻¹ (inv_mem hκ) _ hy
  rwa [show κ⁻¹ * (κ * y * κ⁻¹) * κ⁻¹⁻¹ = y by group] at this

theorem mem_E_of_two_pow (h : LevelDatum θ c.hn8 z k A) {m : G} (hmR : m ∈ RA θ c.hn8 z A)
    (hmA : m ∈ centralizer (A : Set G)) (hmz : m ∈ centralizer ({z} : Set G)) {j : ℕ}
    (hj : m ^ 2 ^ j = 1) : m ∈ E θ c.hn8 := by
  obtain ⟨i, hi | hi⟩ := (N0.mem_B0_iff c.hn8 c m).1 (mem_of_two_pow_RA c hmR hmz hj)
  · rw [hi]
    exact N0.eps_mem_E θ c.hn8 i
  · exfalso
    apply h.z_not_mem_centralizer
    have he : N0.eps θ c.hn8 i ∈ centralizer (A : Set G) :=
      mem_centralizer_iff.2 fun a ha => h.comm ha (h.E_le (N0.eps_mem_E θ c.hn8 i))
    rw [show z = m * (N0.eps θ c.hn8 i)⁻¹ by rw [hi]; group]
    exact mul_mem hmA (inv_mem he)

theorem mem_Lfree (h : LevelDatum θ c.hn8 z k A) {m : G} (hmR : m ∈ RA θ c.hn8 z A)
    (hmA : m ∈ centralizer (A : Set G)) (hmz : m ∈ centralizer ({z} : Set G)) :
    m ∈ Lfree L z := by
  have hC0 : m ∈ N0.C0 θ c.hn8 z := by
    rw [N0.mem_C0_iff c.hn8 c]
    exact ⟨(N0.mem_centralizer_E_iff θ c.hn8 m).1 (RA_le_centralizer_E c hmR),
      mem_centralizer_singleton_iff.1 hmz⟩
  obtain ⟨s, m', hm', hmm'⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  have h2 : (m ^ m') ^ 2 ^ s = 1 := by
    rw [← pow_mul, mul_comm, ← hmm', pow_orderOf_eq_one]
  have hE := mem_E_of_two_pow c h (pow_mem hmR m') (pow_mem hmA m') (pow_mem hmz m') h2
  exact mem_Lfree_of_N0 c ⟨N0.C0_le_N0 c.hn8 c hC0, hmz⟩ hm' (ModIso.E_le_L c.hn8 hE)

theorem exists_mul_eq (hs : StepData θ c.hn8 z k A P A') {d : G} (hdR : d ∈ RA θ c.hn8 z A)
    (hdA : d ∈ centralizer (A : Set G)) :
    ∃ x ∈ A', ∃ m ∈ RA θ c.hn8 z A, m ∈ centralizer (A : Set G) ∧
      m ∈ centralizer ({z} : Set G) ∧ d = x * m := by
  have h := hs.datum
  have hAC : A ≤ centralizer (A : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun b hb => h.comm hb ha
  obtain ⟨x, hx, hxd⟩ := hs.onto _ (betaHat_mem_E c h hdR)
  have hxR : x ∈ RA θ c.hn8 z A := hs.A'_le_RA hx
  have h1 : betaHat k z (x⁻¹ * d) = 1 := by
    rw [betaHat_mul c h (inv_mem hxR) hdR, betaHat_inv c h hxR, hxd, inv_mul_cancel]
  obtain ⟨a, ha, haz⟩ := (betaHat_eq_one_iff c h (mul_mem (inv_mem hxR) hdR)).1 h1
  refine ⟨x * a, mul_mem hx (hs.A_le_A' ha), a⁻¹ * (x⁻¹ * d),
    mul_mem (inv_mem (sup_le_RA c h (mem_sup_left ha))) (mul_mem (inv_mem hxR) hdR),
    mul_mem (inv_mem (hAC ha)) (mul_mem (inv_mem (hs.A'_le_centralizer hx)) hdA), haz,
    by group⟩

theorem le_A' (hs : StepData θ c.hn8 z k A P A') {S : Subgroup G}
    (hSH : S ≤ RA θ c.hn8 z A ⊓ centralizer (A : Set G)) (hSp : IsPGroup 2 S) (hA'S : A' ≤ S) :
    S ≤ A' := by
  intro s hsS
  obtain ⟨hsR, hsA⟩ := Subgroup.mem_inf.1 (hSH hsS)
  obtain ⟨x, hx, m, hmR, hmA, hmz, rfl⟩ := exists_mul_eq c hs hsR hsA
  have hmS : m ∈ S := by
    rw [show m = x⁻¹ * (x * m) by group]
    exact mul_mem (inv_mem (hA'S hx)) hsS
  obtain ⟨j, hj⟩ := hSp ⟨m, hmS⟩
  have hj' : m ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  exact mul_mem hx (hs.A_le_A' (hs.datum.E_le (mem_E_of_two_pow c hs.datum hmR hmA hmz hj')))

end Config

end Frat

section Cover

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {k : ℕ} {A P A' : Subgroup G}

theorem StepData.cover (c : Config G L Q n θ z) (hs : StepData θ c.hn8 z k A P A')
    (M : GL (Fin 3) (ZMod 2)) : ∃ g ∈ KA L z A', ∀ v : Fin 3 → ZMod 2,
      g * epsV θ c.hn8 v * g⁻¹ = epsV θ c.hn8 ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := by
  have h := hs.datum
  obtain ⟨κ, hκ, hκv⟩ := h.cover M
  obtain ⟨d, hdH, hdN⟩ := Frat.exists_inv_mul_mem_normalizer (Frat.A'_le_cstar hs)
    hs.isPGroup_A' (fun S hSH hSp hA'S => Frat.le_A' c hs hSH hSp hA'S)
    (Frat.KA_mem_normalizer c h hκ)
  obtain ⟨hdR, hdA⟩ := Subgroup.mem_inf.1 (inv_mem hdH)
  obtain ⟨x, hx, m, hmR, hmA, hmz, hdxm⟩ := Frat.exists_mul_eq c hs hdR hdA
  refine ⟨m * κ, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩, fun v => ?_⟩
  · rw [show m * κ = x⁻¹ * (d⁻¹ * κ) by rw [hdxm]; group]
    exact mul_mem (Subgroup.le_normalizer (inv_mem hx)) hdN
  · exact mul_mem hmz (KA_le_centralizer hκ)
  · exact mul_mem (Frat.mem_Lfree c h hmR hmA hmz) (KA_le_Lfree hκ)
  · have hmE := mem_centralizer_iff.1 (RA_le_centralizer_E c hmR) _
      (epsV_mem_E θ c.hn8 ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v))
    calc m * κ * epsV θ c.hn8 v * (m * κ)⁻¹ = m * (κ * epsV θ c.hn8 v * κ⁻¹) * m⁻¹ := by group
      _ = epsV θ c.hn8 ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := by
        rw [hκv, ← hmE, mul_inv_cancel_right]

end Cover

theorem stepCover_holds : StepCover := by
  intro G _ _ L Q n θ z c k A P A' hs M
  exact StepData.cover c hs M

end CFSG.OddStandard.AltStdSmall4.G2
