module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Irr
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvolutionInner

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open scoped MatrixGroups

section Bender

variable {X : Type*} [Group X] [Finite X]

theorem card_sylow_of_isBender (hX : fusionIsBenderGroup X) (T : Sylow 2 X) :
    Nat.card (Sylow 2 X) = Nat.card (T : Subgroup X) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective e e.surjective
    have hB := CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
      f hf
    obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 2 PSL(2, GaloisField 2 f)))
    obtain ⟨-, -, -, hRcard⟩ := benderBorel_sylowCenter hB R
    have h : Nat.card (Sylow 2 PSL(2, GaloisField 2 f)) =
        Nat.card (R : Subgroup PSL(2, GaloisField 2 f)) + 1 := by
      rw [CFSG.Walter.psl2_even_card_sylow (by omega), hRcard, pow_one]
    exact Asc76X.card_sylow_eq_card_add_one_of_mulEquiv e h T
  · exact Asc76X.card_sylow_of_mulEquiv_psu3 hf e T
  · exact Asc76X.card_sylow_of_mulEquiv_sz ha e T

theorem isSzOrU3_or_abelian (hX : fusionIsBenderGroup X) :
    IsSzOrU3 X ∨ ∀ T : Sylow 2 X, (T : Subgroup X) ≤ sylowCenter T := by
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · right
    intro T
    have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective e e.surjective
    have hB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
      f hf).map_mulEquiv e.symm
    obtain ⟨-, -, hZcard, hTcard⟩ := benderBorel_sylowCenter hB T
    exact le_sylowCenter_of_card (by rw [hZcard, hTcard, pow_one])
  · exact Or.inl (Or.inr ⟨f, hf, ⟨e⟩⟩)
  · exact Or.inl (Or.inl ⟨a, ha, ⟨e⟩⟩)

end Bender

variable {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]

omit [Finite Y] in
theorem conjNormal_eq_one {c : Y} (hc : c ∈ centralizer (K : Set Y)) :
    (MulAut.conjNormal c : MulAut K) = 1 := by
  ext x
  rw [MulAut.conjNormal_apply, MulAut.one_apply]
  have := mem_centralizer_iff.mp hc x x.2
  calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [← this]
    _ = x := by group

omit [Finite Y] in
theorem conj_mem_inf {P : Subgroup Y} {y : Y} (hy : y ∈ P) {t : Y} (ht : t ∈ P ⊓ K) :
    y * t * y⁻¹ ∈ P ⊓ K :=
  mem_inf.mpr ⟨P.mul_mem (P.mul_mem hy (mem_inf.mp ht).1) (P.inv_mem hy),
    (inferInstance : K.Normal).conj_mem t (mem_inf.mp ht).2 y⟩

theorem exists_sq_mem_centralizer (hK : fusionIsBenderGroup K) (P : Sylow 2 Y) {y : Y}
    (hy : y ∈ (P : Subgroup Y))
    (hy2 : y ^ 2 ∈ ((P : Subgroup Y) ⊓ K) ⊔ centralizer (K : Set Y)) :
    ∃ t ∈ (P : Subgroup Y) ⊓ K, (t⁻¹ * y) ^ 2 ∈ centralizer (K : Set Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := (P : Subgroup Y) ⊓ K with hTdef
  set C := centralizer (K : Set Y) with hCdef
  obtain ⟨T', hT'⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  have hmemT : ∀ x : K, x ∈ (T' : Subgroup K) ↔ (x : Y) ∈ T := fun x => by
    rw [hT', mem_subgroupOf]
  obtain ⟨q, k, -, hB⟩ := (BenderExt.benderData_of_isBenderGroup hK).borel
  have hSE := (hB T').1
  have hcard := card_sylow_of_isBender hK T'
  have : Nontrivial (Sylow 2 K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    have := Nat.card_pos (α := (T' : Subgroup K))
    omega
  obtain ⟨S₀, hS₀⟩ := exists_ne T'
  set α : MulAut K := MulAut.conjNormal y with hα
  have hαT : α • T' = T' := Omega.smul_eq_of_mapsTo fun s hs => by
    rw [hmemT] at hs
    refine (hmemT _).mpr ?_
    rw [hα, MulAut.conjNormal_apply]
    exact conj_mem_inf hy hs
  obtain ⟨r, hr, hrS⟩ := Omega.exists_conj_adjust hSE hcard hS₀ α hαT
  have hrT : (r : Y) ∈ T := (hmemT r).mp hr
  refine ⟨r, hrT, ?_⟩
  have hβ : (MulAut.conj r)⁻¹ * α = MulAut.conjNormal ((r : Y)⁻¹ * y) := by
    rw [map_mul, map_inv, MulAut.conjNormal_val]
  rw [hβ] at hrS
  have hsq : ((r : Y)⁻¹ * y) ^ 2 ∈ T ⊔ C := by
    have e : ((r : Y)⁻¹ * y) ^ 2 = (r : Y)⁻¹ * (y * (r : Y)⁻¹ * y⁻¹) * y ^ 2 := by
      rw [sq, sq]
      group
    rw [e]
    exact mul_mem (mul_mem (mem_sup_left (T.inv_mem hrT))
      (mem_sup_left (conj_mem_inf hy (T.inv_mem hrT)))) hy2
  obtain ⟨t₂, ht₂, c₂, hc₂, he⟩ := mem_sup_of_normal_right.mp hsq
  have ht₂K : t₂ ∈ K := (mem_inf.mp ht₂).2
  have hβ2 : MulAut.conjNormal (((r : Y)⁻¹ * y) ^ 2) = MulAut.conj (⟨t₂, ht₂K⟩ : K) := by
    rw [← he, map_mul, conjNormal_eq_one hc₂, mul_one]
    exact MulAut.conjNormal_val (h := (⟨t₂, ht₂K⟩ : K))
  have hS₀' : MulAut.conj (⟨t₂, ht₂K⟩ : K) • S₀ = S₀ := by
    rw [← hβ2, map_pow, pow_two, mul_smul, hrS, hrS]
  have hN : (⟨t₂, ht₂K⟩ : K) ∈ normalizer ((S₀ : Subgroup K) : Set K) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (by rw [Sylow.smul_def]; exact hS₀')
  have h1 := Omega.eq_one_of_mem_normalizer hSE hS₀ ((hmemT _).mpr ht₂) hN
  have ht₂1 : t₂ = 1 := congrArg Subtype.val h1
  rw [← he, ht₂1, one_mul]
  exact hc₂

theorem mem_sup_centralizer_of_sq (hK : fusionIsBenderGroup K) (P : Sylow 2 Y)
    (hKP : K ⊔ (P : Subgroup Y) = ⊤) {γ : Y} (hγ : γ ∈ (P : Subgroup Y))
    (hγ2 : γ ^ 2 ∈ centralizer (K : Set Y))
    (hfix : ∃ T₀ : Sylow 2 K, ∀ x : K, γ * x * γ⁻¹ = x →
      x ∈ normalizer ((T₀ : Subgroup K) : Set K)) :
    γ ∈ ((P : Subgroup Y) ⊓ K) ⊔ centralizer (K : Set Y) := by
  have hd := BenderExt.extData_of_benderData K (BenderExt.benderData_of_isBenderGroup hK) P hKP
  set α : MulAut K := MulAut.conjNormal γ with hα
  have hαα : α * α = 1 := by
    rw [hα, ← map_mul, ← pow_two, conjNormal_eq_one hγ2]
  obtain ⟨T₀, hT₀⟩ := hfix
  obtain ⟨k, hk⟩ := bender_involution_automorphism_inner K hK α hαα ⟨T₀, fun x hx => hT₀ x (by
    have := congrArg Subtype.val hx
    rwa [hα, MulAut.conjNormal_apply] at this)⟩
  have hc : (k : Y)⁻¹ * γ ∈ centralizer (K : Set Y) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h := congrArg Subtype.val (congrArg (fun φ : MulAut K => φ ⟨x, hx⟩) hk)
    simp only [hα, MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv] at h
    calc x * ((k : Y)⁻¹ * γ) = (k : Y)⁻¹ * ((k : Y) * x * (k : Y)⁻¹) * γ := by group
      _ = (k : Y)⁻¹ * (γ * x * γ⁻¹) * γ := by rw [h]
      _ = (k : Y)⁻¹ * γ * x := by group
  have hkP : (k : Y) ∈ (P : Subgroup Y) := by
    have : (k : Y) = γ * ((k : Y)⁻¹ * γ)⁻¹ := by group
    rw [this]
    exact mul_mem hγ (inv_mem (hd.centralizer_le hc))
  have := mul_mem_sup (mem_inf.mpr ⟨hkP, k.2⟩) hc
  rwa [mul_inv_cancel_left] at this

theorem fix_le_center (hK : fusionIsBenderGroup K) (P : Sylow 2 Y) {y : Y}
    (hy : y ∈ (P : Subgroup Y))
    (hyZ : ∀ z ∈ sylowCenter ((P : Subgroup Y) ⊓ K), y * z = z * y)
    (hyout : y ∉ ((P : Subgroup Y) ⊓ K) ⊔ centralizer (K : Set Y)) {p c : Y}
    (hp : p ∈ sylowCenter ((P : Subgroup Y) ⊓ K)) (hc : c ∈ centralizer (K : Set Y))
    (hy2 : y ^ 2 = p * c) :
    ∀ t ∈ (P : Subgroup Y) ⊓ K, y * t * y⁻¹ = t → t ∈ sylowCenter ((P : Subgroup Y) ⊓ K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := (P : Subgroup Y) ⊓ K with hTdef
  set C := centralizer (K : Set Y) with hCdef
  have hB := BenderExt.benderData_of_isBenderGroup hK
  have hTK : T ≤ K := inf_le_right
  obtain ⟨T', hT'⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  have hmemT : ∀ x : K, x ∈ (T' : Subgroup K) ↔ (x : Y) ∈ T := fun x => by
    rw [hT', mem_subgroupOf]
  have hZ : ∀ x : K, x ∈ sylowCenter (T' : Subgroup K) ↔ (x : Y) ∈ sylowCenter T := fun x => by
    rw [hT']
    exact BenderExt.Bridge.mem_sylowCenter_subgroupOf hTK x
  set α : MulAut K := MulAut.conjNormal y with hα
  have hαapp : ∀ x : K, (α x : Y) = y * x * y⁻¹ := fun x => MulAut.conjNormal_apply y x
  have hαT : ∀ s ∈ (T' : Subgroup K), α s ∈ (T' : Subgroup K) := by
    intro s hs
    rw [hmemT] at hs ⊢
    rw [hαapp]
    exact conj_mem_inf hy hs
  have hαZ : ∀ z ∈ sylowCenter (T' : Subgroup K), α z = z := by
    intro z hz
    apply Subtype.ext
    rw [hαapp, hyZ _ ((hZ z).mp hz), mul_inv_cancel_right]
  have hαpow : ∃ n : ℕ, α ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨y, hy⟩
    refine ⟨n, ?_⟩
    have hyn : y ^ (2 ^ n) = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [hα, ← map_pow, hyn, map_one]
  have hαout : ∀ s ∈ (T' : Subgroup K), α ≠ MulAut.conj s := by
    intro s hs heq
    apply hyout
    have hsC : (s : Y)⁻¹ * y ∈ C := by
      rw [mem_centralizer_iff]
      intro g hg
      have h := congrArg Subtype.val (congrArg (fun φ : MulAut K => φ ⟨g, hg⟩) heq)
      simp only [hαapp, MulAut.conj_apply, coe_mul, coe_inv] at h
      calc g * ((s : Y)⁻¹ * y) = (s : Y)⁻¹ * ((s : Y) * g * (s : Y)⁻¹) * y := by group
        _ = (s : Y)⁻¹ * (y * g * y⁻¹) * y := by rw [h]
        _ = (s : Y)⁻¹ * y * g := by group
    have := mul_mem_sup ((hmemT s).mp hs) hsC
    rwa [mul_inv_cancel_left] at this
  obtain ⟨-, hfix, -⟩ := hB.aut T' α hαT hαZ hαpow hαout
  have hpK : p ∈ K := hTK (sylowCenter_le T hp)
  have hα2 : α ^ 2 = MulAut.conj (⟨p, hpK⟩ : K) := by
    rw [hα, ← map_pow, hy2, map_mul, conjNormal_eq_one hc, mul_one]
    exact MulAut.conjNormal_val (h := (⟨p, hpK⟩ : K))
  intro t ht hyt
  have := hfix ⟨⟨p, hpK⟩, (hZ _).mpr hp, hα2⟩ ⟨t, hTK ht⟩ ((hmemT _).mpr ht)
    (Subtype.ext (by rw [hαapp]; exact hyt))
  exact (hZ _).mp this

theorem commute_center_of_sq (hK : fusionIsBenderGroup K) (hSz : IsSzOrU3 K) (P : Sylow 2 Y)
    {y : Y} (hy : y ∈ (P : Subgroup Y))
    (hy2 : y ^ 2 ∈ ((P : Subgroup Y) ⊓ K) ⊔ centralizer (K : Set Y)) :
    ∀ z ∈ sylowCenter ((P : Subgroup Y) ⊓ K), y * z = z * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := (P : Subgroup Y) ⊓ K with hTdef
  have hTK : T ≤ K := inf_le_right
  obtain ⟨t, ht, ht2⟩ := exists_sq_mem_centralizer hK P hy hy2
  obtain ⟨T', hT'⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  have hmemT : ∀ x : K, x ∈ (T' : Subgroup K) ↔ (x : Y) ∈ T := fun x => by
    rw [hT', mem_subgroupOf]
  set β : MulAut K := MulAut.conjNormal (t⁻¹ * y) with hβ
  have hββ : β * β = 1 := by
    rw [hβ, ← map_mul, ← pow_two, conjNormal_eq_one ht2]
  have htP : t ∈ (P : Subgroup Y) := (mem_inf.mp ht).1
  have hβT : ∀ x ∈ (T' : Subgroup K), β x ∈ (T' : Subgroup K) := by
    intro x hx
    rw [hmemT] at hx ⊢
    rw [hβ, MulAut.conjNormal_apply]
    exact conj_mem_inf (mul_mem (inv_mem htP) hy) hx
  intro z hz
  have hzK : z ∈ K := hTK (sylowCenter_le T hz)
  have hzT' : (⟨z, hzK⟩ : K) ∈ (T' : Subgroup K) := (hmemT _).mpr (sylowCenter_le T hz)
  have hzC : (⟨z, hzK⟩ : K) ∈ centralizer ((T' : Subgroup K) : Set K) := by
    rw [mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    exact (mem_sylowCenter.mp hz).2 x ((hmemT x).mp hx)
  have h := Asc76X.benderFacts.aut_involution_center K hSz T' β hββ hβT _ hzT' hzC
  have h' := congrArg Subtype.val h
  rw [hβ, MulAut.conjNormal_apply] at h'
  have htz : t * z = z * t := ((mem_sylowCenter.mp hz).2 t ht)
  have h'' : t⁻¹ * y * z = z * (t⁻¹ * y) := by
    calc t⁻¹ * y * z = t⁻¹ * y * z * (t⁻¹ * y)⁻¹ * (t⁻¹ * y) := by group
      _ = z * (t⁻¹ * y) := by rw [h']
  calc y * z = t * (t⁻¹ * y * z) := by group
    _ = t * (z * (t⁻¹ * y)) := by rw [h'']
    _ = (t * z) * t⁻¹ * y := by group
    _ = (z * t) * t⁻¹ * y := by rw [htz]
    _ = z * y := by group

theorem eq_of_irr (hSz : IsSzOrU3 K) (P : Sylow 2 Y) {A : Subgroup Y}
    (hZA : sylowCenter ((P : Subgroup Y) ⊓ K) ≤ A) (hAT : A ≤ (P : Subgroup Y) ⊓ K)
    (hN : ∀ n ∈ K, n ∈ normalizer (((P : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) →
      ∀ a ∈ A, n⁻¹ * a * n ∈ A)
    (hAZ : ¬ A ≤ sylowCenter ((P : Subgroup Y) ⊓ K)) : A = (P : Subgroup Y) ⊓ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := (P : Subgroup Y) ⊓ K with hTdef
  have hTK : T ≤ K := inf_le_right
  have hAK : A ≤ K := hAT.trans hTK
  obtain ⟨T', hT'⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  have hZ : ∀ x : K, x ∈ sylowCenter (T' : Subgroup K) ↔ (x : Y) ∈ sylowCenter T := fun x => by
    rw [hT']
    exact BenderExt.Bridge.mem_sylowCenter_subgroupOf hTK x
  have hirr := irrAt_of_isSzOrU3 hSz T'
  have heq := hirr (A.subgroupOf K) (fun z hz => mem_subgroupOf.mpr (hZA ((hZ z).mp hz)))
    (fun x hx => by rw [hT', mem_subgroupOf]; exact hAT (mem_subgroupOf.mp hx))
    (fun n hn a ha => by
      rw [mem_subgroupOf] at ha ⊢
      have hn' : (n : Y) ∈ normalizer (T : Set Y) := by
        rw [hT'] at hn
        exact BenderExt.Bridge.mem_normalizer_subgroupOf hTK n hn
      simpa using hN n n.2 hn' a ha)
    (fun hle => hAZ fun x hx => (hZ ⟨x, hAK hx⟩).mp (hle (mem_subgroupOf.mpr hx)))
  rw [hT'] at heq
  apply le_antisymm hAT
  intro x hx
  have : (⟨x, hTK hx⟩ : K) ∈ T.subgroupOf K := mem_subgroupOf.mpr hx
  rw [← heq, mem_subgroupOf] at this
  exact this

end CFSG.ComponentClassification.Asc76.L26
