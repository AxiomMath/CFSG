module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3
public import CFSG.GH74.GLS.Stage4.SDWLayerAbs
public import CFSG.GH74.GLS.Stage4.T2CentSL
public import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Rest.FieldU3

section Cover

variable {Γ C : Type} [Group Γ] [Group C]

theorem sdwU_card_comap [Finite Γ] (ψ : Γ →* C) (hψ : Function.Surjective ψ) (K : Subgroup C) :
    Nat.card (K.comap ψ) = Nat.card K * Nat.card ψ.ker := by
  have : Finite C := Finite.of_surjective ψ hψ
  have h1 := Subgroup.card_mul_index (K.comap ψ)
  have h2 := Subgroup.card_mul_index K
  have h3 : (K.comap ψ).index = K.index := Subgroup.index_comap_of_surjective K hψ
  have h5 := Subgroup.card_mul_index ψ.ker
  have h4 : Nat.card ψ.range = Nat.card C := by
    rw [MonoidHom.range_eq_top_of_surjective ψ hψ, Subgroup.card_top]
  rw [Subgroup.index_ker, h4] at h5
  rw [h3] at h1
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card (K.comap ψ) * K.index = Nat.card Γ := h1
    _ = Nat.card ψ.ker * Nat.card C := h5.symm
    _ = Nat.card ψ.ker * (Nat.card K * K.index) := by rw [h2]
    _ = Nat.card K * Nat.card ψ.ker * K.index := by ring

theorem sdwU_comap_perfect (ψ : Γ →* C) (hψ : Function.Surjective ψ) (K : Subgroup C)
    (hK : ⁅K, K⁆ = K) : ⁅K.comap ψ, K.comap ψ⁆ ⊔ ψ.ker = K.comap ψ := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    · intro x hx
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
      exact K.one_mem
  · intro x hx
    have hmap : (⁅K.comap ψ, K.comap ψ⁆).map ψ = K := by
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hψ, hK]
    have hψx : ψ x ∈ (⁅K.comap ψ, K.comap ψ⁆).map ψ := by
      rw [hmap]; exact hx
    obtain ⟨y, hy, hyx⟩ := hψx
    have hxy : y⁻¹ * x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hy hxy

theorem sdwU_comap_nonabelian (ψ : Γ →* C) (hψ : Function.Surjective ψ) (K : Subgroup C)
    (hKnc : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a) :
    ∃ a ∈ K.comap ψ, ∃ b ∈ K.comap ψ, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := hKnc
  obtain ⟨a', rfl⟩ := hψ a
  obtain ⟨b', rfl⟩ := hψ b
  exact ⟨a', ha, b', hb, fun h => hab (by rw [← map_mul, ← map_mul, h])⟩

theorem sdwU_card_eq_perfect [Finite Γ] (ψ : Γ →* C) (hψ : Function.Surjective ψ)
    (S : Subgroup Γ) [S.Normal] (hNS : ψ.ker ⊓ S = ⊥) (hab : ∀ x y : Γ, ⁅x, y⁆ ∈ S)
    (hperf : ⁅S, S⁆ = S)
    (hq : ∀ T : Subgroup Γ, T ≤ S → (∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T) →
      (∀ t ∈ T, ∀ s ∈ S, t * s = s * t) ∨ T = S)
    (hC : ∀ g h : Γ, (∀ s ∈ S, g * s = s * g) → (∀ s ∈ S, h * s = s * h) → g * h = h * g)
    (K : Subgroup C) [K.Normal] (hKperf : ⁅K, K⁆ = K) (hKnc : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a) :
    Nat.card K = Nat.card S := by
  obtain ⟨-, hcard⟩ := card_eq_of_perfect_normal S ψ.ker hNS hab hperf hq hC (K.comap ψ)
    (fun x hx => by rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]; exact K.one_mem)
    (sdwU_comap_perfect ψ hψ K hKperf) (sdwU_comap_nonabelian ψ hψ K hKnc)
  rw [sdwU_card_comap ψ hψ K] at hcard
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos hcard

theorem sdwU_card_le_nonperfect [Finite Γ] (ψ : Γ →* C) (hψ : Function.Surjective ψ)
    (S : Subgroup Γ) [S.Normal] (hperf : ⁅S, S⁆ = S)
    (hq : ∀ T : Subgroup Γ, T ≤ S → (∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T) →
      (∀ t ∈ T, ∀ s ∈ S, t * s = s * t) ∨ T = S)
    (hC : ∀ g h : Γ, (∀ s ∈ S, g * s = s * g) → (∀ s ∈ S, h * s = s * h) → g * h = h * g)
    (K : Subgroup C) [K.Normal] (hKnc : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a) :
    Nat.card S ≤ Nat.card K * Nat.card ψ.ker := by
  have hSM : S ≤ K.comap ψ :=
    nonabelian_normal_contains S hperf hq hC (K.comap ψ) (sdwU_comap_nonabelian ψ hψ K hKnc)
  rw [← sdwU_card_comap ψ hψ K]
  exact Subgroup.card_le_of_le hSM

end Cover

section DetKernel

variable {Γ : Type} [Group Γ]

theorem sdwU_comm_mem_ker {A : Type} [CommGroup A] (δ : Γ →* A) (x y : Γ) : ⁅x, y⁆ ∈ δ.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement]
  simp [commutatorElement_def]

theorem sdwU_centralizer_comm {A : Type} [Group A] [IsCyclic A] (δ : Γ →* A) (g h : Γ)
    (hg : ∀ s ∈ δ.ker, g * s = s * g) (hh : ∀ s ∈ δ.ker, h * s = s * h) : g * h = h * g := by
  let C₀ : Subgroup Γ := Subgroup.centralizer (δ.ker : Set Γ)
  let f : C₀ →* A := δ.comp C₀.subtype
  have hker : f.ker ≤ Subgroup.center C₀ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxs : (x : Γ) ∈ δ.ker := hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 y.2 x hxs).symm
  have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hker
  have hgC : g ∈ C₀ := Subgroup.mem_centralizer_iff.2 fun s hs => (hg s hs).symm
  have hhC : h ∈ C₀ := Subgroup.mem_centralizer_iff.2 fun s hs => (hh s hs).symm
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨g, hgC⟩ : C₀) ⟨h, hhC⟩)

theorem sdwU_hq (S : Subgroup Γ) (hperf : Group.IsPerfect ↥S)
    (hs : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S)) :
    ∀ T : Subgroup Γ, T ≤ S → (∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T) →
      (∀ t ∈ T, ∀ s ∈ S, t * s = s * t) ∨ T = S := by
  intro T hTS hTn
  have hN : (T.subgroupOf S).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hTn g g.2 n hn⟩
  rcases t2C_normal_le_center_or_top hperf hs (T.subgroupOf S) with hc | htop
  · left
    intro t ht s hs'
    have h1 : (⟨t, hTS ht⟩ : ↥S) ∈ T.subgroupOf S := ht
    have h2 := Subgroup.mem_center_iff.1 (hc h1) ⟨s, hs'⟩
    exact (congrArg Subtype.val h2).symm
  · right
    apply le_antisymm hTS
    intro s hs'
    have : (⟨s, hs'⟩ : ↥S) ∈ T.subgroupOf S := by rw [htop]; trivial
    exact this

theorem sdwU_cen_sq {S : Subgroup Γ} (h : ∀ y ∈ Subgroup.center ↥S, y ^ 2 = 1) :
    ∀ x ∈ S, (∀ s ∈ S, x * s = s * x) → x ^ 2 = 1 := by
  intro x hx hc
  have hy : (⟨x, hx⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  have := congrArg Subtype.val (h _ hy)
  simpa using this

theorem sdwU_pow_three (N : Subgroup Γ) (h : Nat.card N = 1 ∨ Nat.card N = 3) :
    ∀ x ∈ N, x ^ 3 = 1 := by
  intro x hx
  have := pow_card_eq_one' (G := ↥N) (x := ⟨x, hx⟩)
  rcases h with h | h
  · rw [h, pow_one] at this
    have hx1 : x = 1 := congrArg Subtype.val this
    rw [hx1, one_pow]
  · rw [h] at this
    exact congrArg Subtype.val this

theorem sdwU_inf_eq_bot [Finite Γ] (S N : Subgroup Γ) [N.Normal]
    (hq : ∀ T : Subgroup Γ, T ≤ S → (∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T) →
      (∀ t ∈ T, ∀ s ∈ S, t * s = s * t) ∨ T = S)
    (hS : Nat.card N < Nat.card S) (hN3 : ∀ x ∈ N, x ^ 3 = 1)
    (hcen : ∀ x ∈ S, (∀ s ∈ S, x * s = s * x) → x ^ 2 = 1) : N ⊓ S = ⊥ := by
  rcases hq (N ⊓ S) inf_le_right (fun s hs t ht =>
      ⟨Subgroup.Normal.conj_mem inferInstance t ht.1 s,
        S.mul_mem (S.mul_mem hs ht.2) (S.inv_mem hs)⟩) with hc | heq
  · rw [eq_bot_iff]
    intro x hx
    have h2 := hcen x hx.2 (fun s hs => hc x hx s hs)
    have h3 := hN3 x hx.1
    rw [Subgroup.mem_bot]
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [h2, h3]; simp
  · exfalso
    have hSN : S ≤ N := heq ▸ inf_le_left
    exact absurd (Subgroup.card_le_of_le hSN) (not_le.2 hS)

end DetKernel

section SL2Facts

theorem sdwU_negOne_sq {k : Type} [Field k] : negOne k * negOne k = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, t2B_negOne_eq, Matrix.SpecialLinearGroup.coe_one]
  simp

variable {k : Type} [Field k] {Q : Type} [Group Q]

theorem sdwU_nonabelian_of_equiv (e : Q ≃* SL2 k) : ∃ a b : Q, a * b ≠ b * a := by
  refine ⟨e.symm (sl2U 1), e.symm (sl2L 1), fun hab => ?_⟩
  have h := congrArg (fun x : SL2 k => (x : Matrix (Fin 2) (Fin 2) k) 0 0)
    (by simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hab :
      sl2U (1 : k) * sl2L 1 = sl2L 1 * sl2U 1)
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h

theorem sdwU_card_sl2 [Finite k] (e : Q ≃* SL2 k) :
    Nat.card Q = Nat.card k * (Nat.card k ^ 2 - 1) := by
  rw [Nat.card_congr e.toEquiv]
  exact t2C_card_sl2

theorem sdwU_sl2_facts [Finite k] (e : Q ≃* SL2 k) (h4 : 4 ≤ Nat.card k) :
    Group.IsPerfect Q ∧ IsSimpleGroup (Q ⧸ Subgroup.center Q) ∧ ∀ x ∈ Subgroup.center Q, x ^ 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k h4
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have hs : IsSimpleGroup (SL2 k ⧸ Subgroup.center (SL2 k)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact (QuotientGroup.congr (Subgroup.center Q) (Subgroup.center (SL2 k)) e
      (Subgroup.map_center_eq e)).isSimpleGroup
  · intro x hx
    have hx' : e x ∈ Subgroup.center (SL2 k) := by
      rw [← Subgroup.map_center_eq e]
      exact Subgroup.mem_map_of_mem _ hx
    apply e.injective
    rw [map_pow, map_one, sq]
    rcases (t2C_center_sl2 _).1 hx' with h | h
    · rw [h, one_mul]
    · rw [h, sdwU_negOne_sq]

end SL2Facts

theorem sdwU_central_involution {E : Type} [Group E] {K : Subgroup E} {z : E} (hzK : z ∈ K)
    (hz : orderOf z = 2) {F' : Type} [Field F'] (h2 : (2 : F') ≠ 0) (e : ↥K ≃* SL2 F') :
    ∀ x ∈ K, x * z = z * x := by
  have hzz : (⟨z, hzK⟩ : ↥K) * ⟨z, hzK⟩ = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one z
    rwa [hz, sq] at this
  have hz1 : (⟨z, hzK⟩ : ↥K) ≠ 1 := by
    intro h
    have : z = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hz
    omega
  have hx : e ⟨z, hzK⟩ = negOne F' :=
    eq_negOne_of_involution h2 (by rw [← map_mul, hzz, map_one])
      (fun h => hz1 (e.injective (by rw [h, map_one])))
  have hcen : e ⟨z, hzK⟩ ∈ Subgroup.center (SL2 F') := by
    rw [hx]
    exact (t2C_center_sl2 _).2 (Or.inr rfl)
  intro x hxK
  have h1 := Subgroup.mem_center_iff.1 hcen (e ⟨x, hxK⟩)
  have h' : (⟨x, hxK⟩ : ↥K) * ⟨z, hzK⟩ = ⟨z, hzK⟩ * ⟨x, hxK⟩ :=
    e.injective (by rw [map_mul, map_mul]; exact h1)
  exact congrArg Subtype.val h'

theorem sdwU_exists_noncomm {G : Type} [Group G] {H : Subgroup G} (h : ∃ a b : ↥H, a * b ≠ b * a) :
    ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩

theorem sdwU_eq_three_of_le {q : ℕ} (hodd : Odd q) (h3 : 3 ≤ q) (h : q * (q ^ 2 - 1) ≤ 96) :
    q = 3 := by
  by_contra hne
  have h5 : 5 ≤ q := by obtain ⟨m, hm⟩ := hodd; omega
  have h25 : 25 ≤ q ^ 2 := by nlinarith
  have : 5 * 24 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h5 (by omega)
  omega

theorem sdwU_eq_of_mul_sq_sub_one {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  have hb2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  zify [ha2, hb2] at h
  have h0 : ((a : ℤ) - b) * ((a : ℤ) ^ 2 + a * b + b ^ 2 - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · omega
  · exfalso
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith

section SU2

variable {F : Type} [Field F] [Finite F] {r f : ℕ} [Fact r.Prime] [CharP F r]

theorem sdwU_nonempty_sl2_mulEquiv_statedSU_two (hF : Nat.card F = (r ^ f) ^ 2) :
    Nonempty (SL2 (fixedSubfield F r f) ≃* StatedSU 2 (r ^ f) F) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 2
  exact ⟨((hypEquiv hζ0 hζ).trans (conjEquiv P hP)).trans
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hF 2))⟩

end SU2

section GU2

variable {p f : ℕ} {F : Type} [Field F]

noncomputable def sdwUDet (q : ℕ) (F : Type) [Field F] : ↥(GU2Stated q F) →* Fˣ :=
  Matrix.GeneralLinearGroup.det.comp (GU2Stated q F).subtype

theorem sdwU_mem_ker_iff (h : UnitaryFieldData p f F) (A : ↥(GU2Stated (p ^ f) F)) :
    A ∈ (sdwUDet (p ^ f) F).ker ↔ (A : GL (Fin 2) F) ∈ StatedSU 2 (p ^ f) F := by
  have hA := (Lemma41aU3.mem_GU2Stated_iff h).1 A.2
  rw [MonoidHom.mem_ker]
  change _ ↔ (A : GL (Fin 2) F) ∈ unitarySU p f F 2
  rw [mem_unitarySU_iff h]
  constructor
  · intro hd
    refine ⟨?_, hA⟩
    have := congrArg (fun u : Fˣ => (u : F)) hd
    simpa [sdwUDet, Matrix.GeneralLinearGroup.val_det_apply] using this
  · rintro ⟨hd, -⟩
    apply Units.ext
    simpa [sdwUDet, Matrix.GeneralLinearGroup.val_det_apply] using hd

theorem sdwU_statedSU_le (h : UnitaryFieldData p f F) :
    StatedSU 2 (p ^ f) F ≤ GU2Stated (p ^ f) F := fun _ hA =>
  (Lemma41aU3.mem_GU2Stated_iff h).2 ((mem_unitarySU_iff h).1 hA).2

theorem sdwU_ker_eq (h : UnitaryFieldData p f F) :
    (sdwUDet (p ^ f) F).ker = (StatedSU 2 (p ^ f) F).subgroupOf (GU2Stated (p ^ f) F) := by
  ext A
  rw [sdwU_mem_ker_iff h, Subgroup.mem_subgroupOf]

theorem sdwU_exists_ker_equiv (h : UnitaryFieldData p f F) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = p ^ f ∧
      Nonempty (↥(sdwUDet (p ^ f) F).ker ≃* SL2 k) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hF : Nat.card F = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨e⟩ := sdwU_nonempty_sl2_mulEquiv_statedSU_two (F := F) (r := p) (f := f) hF
  exact ⟨↥(fixedSubfield F p f), inferInstance, inferInstance, card_fixedSubfield hF,
    ⟨((MulEquiv.subgroupCongr (sdwU_ker_eq h)).trans
      (Subgroup.subgroupOfEquivOfLe (sdwU_statedSU_le h))).trans e.symm⟩⟩

theorem sdwU_card_range_det_le (h : UnitaryFieldData p f F) :
    Nat.card (sdwUDet (p ^ f) F).range ≤ p ^ f + 1 := by
  have := h.finite
  have hle : (sdwUDet (p ^ f) F).range ≤ rootsOfUnity (p ^ f + 1) F := by
    rintro _ ⟨A, rfl⟩
    rw [mem_rootsOfUnity]
    have hA := (Lemma41aU3.mem_GU2Stated_iff h).1 A.2
    have h1 := Lemma41aU3.bar_det_mul_det hA
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h2 : ((sdwUDet (p ^ f) F A : Fˣ) : F) =
        ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det :=
      Matrix.GeneralLinearGroup.val_det_apply _
    rw [h2, pow_succ]
    rw [h.bar_apply] at h1
    exact h1
  have : NeZero (p ^ f + 1) := ⟨by omega⟩
  exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity F (p ^ f + 1))

theorem sdwU_card_le (h : UnitaryFieldData p f F) :
    Nat.card ↥(GU2Stated (p ^ f) F) ≤ Nat.card ↥(sdwUDet (p ^ f) F).ker * (p ^ f + 1) := by
  have h1 := Subgroup.card_mul_index (sdwUDet (p ^ f) F).ker
  rw [Subgroup.index_ker] at h1
  rw [← h1]
  exact Nat.mul_le_mul_left _ (sdwU_card_range_det_le h)

end GU2

end CFSG.GH74.GLS.Stage4.Rest.FieldU3

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Rest.FieldU3

theorem field_eq_of_component_U3 {E : Type} [Group E] [Finite E] {p' f p n : ℕ}
    (hp' : p'.Prime) (hp'2 : p' ≠ 2) (hE : CFSG.GH74.GLS.IVK.IsLnEps 3 E (-1) (p' ^ f))
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup E}
    (hK : CFSG.GH74.GLS.HasSL2Model ↥K (fun q => q = p ^ n)) (h3 : 3 ≤ p ^ n)
    {z : E} (hzK : z ∈ K) (hz : orderOf z = 2)
    (hCK : ∀ c : E, c * z = z * c → ∀ k ∈ K, c * k * c⁻¹ ∈ K) : p' ^ f = p ^ n := by
  obtain ⟨F', iF', iFin', hF'card, ⟨e₀⟩⟩ := hK
  have hF'card' : Nat.card F' = p ^ n := hF'card
  let e : ↥K ≃* SL2 F' := e₀.trans (specialLinearGroupEquivStatedSL 2 F').symm
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h3
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F' p := by
    have := Fintype.ofFinite F'
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF'card'])
  have h2 : (2 : F') ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F' p]; exact hp2)
  have hKz : ∀ x ∈ K, x * z = z * x := sdwU_central_involution hzK hz h2 e
  have hKC : K ≤ Subgroup.centralizer ({z} : Set E) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hKz x hx)
  obtain ⟨F, iF, iFin, N, hN, hFcard, hNcard, ⟨φ⟩⟩ :=
    ivk_4_1a_U3 E p' f hp' hp'2 hE z hz
  have hf : 1 ≤ f := by
    by_contra hf0
    obtain rfl : f = 0 := by omega
    have h1 := Finite.one_lt_card (α := F)
    rw [hFcard] at h1
    simp at h1
  have hdata : UnitaryFieldData p' f F := ⟨hp', hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  obtain ⟨k, ik, ikFin, hkcard, ⟨eS⟩⟩ := sdwU_exists_ker_equiv hdata
  let ψ : ↥(GU2Stated (p' ^ f) F) →* ↥(Subgroup.centralizer ({z} : Set E)) :=
    φ.symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hψs : Function.Surjective ψ := φ.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  have hψk : ψ.ker = N := by
    ext x
    simp [ψ]
  let K' : Subgroup ↥(Subgroup.centralizer ({z} : Set E)) :=
    K.subgroupOf (Subgroup.centralizer ({z} : Set E))
  have hK'norm : K'.Normal := ⟨fun x hx c => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hCK c (Subgroup.mem_centralizer_singleton_iff.1 c.2) x hx⟩
  let eK : ↥K' ≃* SL2 F' := (Subgroup.subgroupOfEquivOfLe hKC).trans e
  have hKcard : Nat.card K' = p ^ n * ((p ^ n) ^ 2 - 1) := by
    rw [sdwU_card_sl2 eK, hF'card']
  have hKnc : ∃ a ∈ K', ∃ b ∈ K', a * b ≠ b * a :=
    sdwU_exists_noncomm (sdwU_nonabelian_of_equiv eK)
  have hSk : Nat.card ↥(sdwUDet (p' ^ f) F).ker = p' ^ f * ((p' ^ f) ^ 2 - 1) := by
    rw [sdwU_card_sl2 eS, hkcard]
  have hp'3 : 3 ≤ p' := by have := hp'.two_le; omega
  have hq'3 : 3 ≤ p' ^ f := le_trans hp'3 (Nat.le_self_pow (by omega) p')
  have hq'odd : Odd (p' ^ f) := (hp'.odd_of_ne_two hp'2).pow
  have hqodd : Odd (p ^ n) := (hp.odd_of_ne_two hp2).pow
  by_cases hq'eq3 : p' ^ f = 3
  ·
    have h1 : Nat.card K' ≤ Nat.card ↥(Subgroup.centralizer ({z} : Set E)) :=
      Subgroup.card_le_card_group K'
    have h2' : Nat.card ↥(Subgroup.centralizer ({z} : Set E)) ≤ Nat.card ↥(GU2Stated (p' ^ f) F) :=
      Nat.card_le_card_of_surjective ψ hψs
    have h4 : Nat.card ↥(GU2Stated (p' ^ f) F) ≤ 96 := by
      refine (sdwU_card_le hdata).trans ?_
      rw [hSk, hq'eq3]
      norm_num
    have h5 : p ^ n * ((p ^ n) ^ 2 - 1) ≤ 96 := by
      rw [← hKcard]
      exact h1.trans (h2'.trans h4)
    have := sdwU_eq_three_of_le hqodd h3 h5
    omega
  · have h5 : 5 ≤ p' ^ f := by obtain ⟨m, hm⟩ := hq'odd; omega
    have h4k : 4 ≤ Nat.card k := by rw [hkcard]; omega
    obtain ⟨hperfS, hsimpS, hcenS⟩ := sdwU_sl2_facts eS h4k
    have hperf : ⁅(sdwUDet (p' ^ f) F).ker, (sdwUDet (p' ^ f) F).ker⁆ =
        (sdwUDet (p' ^ f) F).ker := Subgroup.isPerfect_iff.1 hperfS
    have hq := sdwU_hq _ hperfS hsimpS
    have hC : ∀ g h : ↥(GU2Stated (p' ^ f) F), (∀ s ∈ (sdwUDet (p' ^ f) F).ker, g * s = s * g) →
        (∀ s ∈ (sdwUDet (p' ^ f) F).ker, h * s = s * h) → g * h = h * g :=
      fun g h hg hh => sdwU_centralizer_comm (sdwUDet (p' ^ f) F) g h hg hh
    have hab := sdwU_comm_mem_ker (sdwUDet (p' ^ f) F)
    have hNle : Nat.card N ≤ 3 := by rcases hNcard with h | h <;> omega
    have hS24 : 120 ≤ p' ^ f * ((p' ^ f) ^ 2 - 1) := by
      have h25 : 25 ≤ (p' ^ f) ^ 2 := by nlinarith
      have : 5 * 24 ≤ p' ^ f * ((p' ^ f) ^ 2 - 1) := Nat.mul_le_mul h5 (by omega)
      omega
    have hNS : ψ.ker ⊓ (sdwUDet (p' ^ f) F).ker = ⊥ := by
      rw [hψk]
      refine sdwU_inf_eq_bot _ N hq ?_ (sdwU_pow_three N hNcard) (sdwU_cen_sq hcenS)
      rw [hSk]
      omega
    by_cases hq3 : p ^ n = 3
    · exfalso
      have h6 := sdwU_card_le_nonperfect ψ hψs _ hperf hq hC K' hKnc
      rw [hKcard, hψk, hSk, hq3] at h6
      have h7 : 3 * (3 ^ 2 - 1) * Nat.card N ≤ 72 := by
        calc 3 * (3 ^ 2 - 1) * Nat.card N ≤ 3 * (3 ^ 2 - 1) * 3 := Nat.mul_le_mul_left _ hNle
          _ = 72 := by norm_num
      omega
    · have h5q : 5 ≤ p ^ n := by obtain ⟨m, hm⟩ := hqodd; omega
      have h4F' : 4 ≤ Nat.card F' := by rw [hF'card']; omega
      have hKperf : ⁅K', K'⁆ = K' := by
        have : Group.IsPerfect ↥K' := by
          have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F' h4F'
          exact Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
        exact Subgroup.isPerfect_iff.1 this
      have hcard := sdwU_card_eq_perfect ψ hψs _ hNS hab hperf hq hC K' hKperf hKnc
      rw [hKcard, hSk] at hcard
      exact sdwU_eq_of_mul_sq_sub_one (by omega) (by omega) hcard.symm

end CFSG.GH74.GLS.Stage4.Rest
