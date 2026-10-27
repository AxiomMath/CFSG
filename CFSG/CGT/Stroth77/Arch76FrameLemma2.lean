module

public import CFSG.CGT.Stroth77.Arch76Frame
public import CFSG.CGT.Stroth77.Arch76Quotient
public import CFSG.CGT.Stroth77.StrothFrame

public section

namespace CFSG.CGT.Stroth77

open Arch76

namespace StrothFrame

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

@[expose] def configN : Config (Subgroup.normalizer (F.A : Set G)) :=
  F.dA.toConfig.restrict _ Subgroup.le_normalizer F.dA.uv_mem F.dA.t_mem F.dA.u_mem F.dA.ρ_mem

instance configN_normal : F.configN.A.Normal := Subgroup.normal_in_normalizer

@[simp] theorem coe_configN_w : (F.configN.w : G) = (F.dA.c : G) := rfl
@[simp] theorem coe_configN_x : (F.configN.x : G) = (F.dA.a : G)⁻¹ := rfl
@[simp] theorem coe_configN_y : (F.configN.y : G) = (F.dA.b : G)⁻¹ := rfl
@[simp] theorem coe_configN_uv : (F.configN.uv : G) = F.dA.uv := rfl
@[simp] theorem coe_configN_t : (F.configN.t : G) = F.dA.t := rfl
@[simp] theorem coe_configN_u : (F.configN.u : G) = F.dA.u := rfl
@[simp] theorem coe_configN_ρ : (F.configN.ρ : G) = F.dA.ρ := rfl

theorem configN_A_map : F.configN.A.map (Subgroup.normalizer (F.A : Set G)).subtype = F.A := by
  rw [show F.configN.A = F.A.subgroupOf (Subgroup.normalizer (F.A : Set G)) from rfl,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr Subgroup.le_normalizer]

theorem T_le_normalizer : F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} ≤
    Subgroup.normalizer (F.A : Set G) := by
  refine sup_le Subgroup.le_normalizer ?_
  rw [Subgroup.closure_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  exacts [F.dA.uv_mem, F.dA.t_mem, F.dA.u_mem]

theorem T_map : (F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u}).map
    (Subgroup.normalizer (F.A : Set G)).subtype =
      F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} := by
  rw [Subgroup.map_sup, F.configN_A_map, MonoidHom.map_closure, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton]
  rfl

end StrothFrame

namespace Arch76.Config

variable {Y : Type*} [Group Y] (C : Config Y) [C.A.Normal]

theorem mat_ev_mul (v : Co) (g : Y) : C.mat (C.ev v * g) = C.mat g := by
  rw [mat_mul]
  have h : C.mat (C.ev v) = ((1, 0, 0), (0, 1, 0), (0, 0, 1)) := by
    show (C.act (C.ev v) (1, 0, 0), C.act (C.ev v) X0, C.act (C.ev v) Y0) = _
    rw [C.act_of_mem_A (C.ev_mem v), C.act_of_mem_A (C.ev_mem v), C.act_of_mem_A (C.ev_mem v)]
    rfl
  rw [h]
  simp only [matMul, matAct, lin, show (1 : ZMod 2).val = 1 from rfl,
    show (1 : ZMod 4).val = 1 from rfl, ZMod.val_zero, one_smul, zero_smul, add_zero, zero_add]

@[expose] def dword (i : Fin 8) : Y :=
  match i.val with
  | 0 => 1
  | 1 => C.uv
  | 2 => C.t
  | 3 => C.uv * C.t
  | 4 => C.u
  | 5 => C.u * C.uv
  | 6 => C.u * C.t
  | _ => C.u * C.uv * C.t

@[expose] def mUV : Mat := (fuv (1, 0, 0), fuv (0, 1, 0), fuv (0, 0, 1))
@[expose] def mT : Mat := (ft (1, 0, 0), ft (0, 1, 0), ft (0, 0, 1))
@[expose] def mU : Mat := (fu (1, 0, 0), fu (0, 1, 0), fu (0, 0, 1))

@[expose] def dmat (i : Fin 8) : Mat :=
  match i.val with
  | 0 => ((1, 0, 0), (0, 1, 0), (0, 0, 1))
  | 1 => mUV
  | 2 => mT
  | 3 => matMul mUV mT
  | 4 => mU
  | 5 => matMul mU mUV
  | 6 => matMul mU mT
  | _ => matMul (matMul mU mUV) mT

theorem dmat_injective : Function.Injective dmat := by decide +kernel

theorem mat_uv_eq : C.mat C.uv = mUV := by
  show (C.act C.uv (1, 0, 0), C.act C.uv X0, C.act C.uv Y0) = _
  rw [act_uv, act_uv, act_uv]; rfl

theorem mat_t_eq : C.mat C.t = mT := by
  show (C.act C.t (1, 0, 0), C.act C.t X0, C.act C.t Y0) = _
  rw [act_t, act_t, act_t]; rfl

theorem mat_u_eq : C.mat C.u = mU := by
  show (C.act C.u (1, 0, 0), C.act C.u X0, C.act C.u Y0) = _
  rw [act_u, act_u, act_u]; rfl

theorem mat_one_eq : C.mat 1 = ((1, 0, 0), (0, 1, 0), (0, 0, 1)) := by
  show (C.act 1 (1, 0, 0), C.act 1 X0, C.act 1 Y0) = _
  rw [act_one, act_one, act_one]; rfl

theorem mat_dword (i : Fin 8) : C.mat (C.dword i) = dmat i := by
  fin_cases i
  · exact C.mat_one_eq
  · exact C.mat_uv_eq
  · exact C.mat_t_eq
  · show C.mat (C.uv * C.t) = matMul mUV mT
    rw [mat_mul, C.mat_uv_eq, C.mat_t_eq]
  · exact C.mat_u_eq
  · show C.mat (C.u * C.uv) = matMul mU mUV
    rw [mat_mul, C.mat_u_eq, C.mat_uv_eq]
  · show C.mat (C.u * C.t) = matMul mU mT
    rw [mat_mul, C.mat_u_eq, C.mat_t_eq]
  · show C.mat (C.u * C.uv * C.t) = matMul (matMul mU mUV) mT
    rw [mat_mul, mat_mul, C.mat_u_eq, C.mat_uv_eq, C.mat_t_eq]

theorem dword_mem (i : Fin 8) : C.dword i ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} := by
  have huv := C.uv_mem_T
  have ht := C.t_mem_T
  have hu := C.u_mem_T
  fin_cases i
  · exact one_mem _
  · exact huv
  · exact ht
  · exact mul_mem huv ht
  · exact hu
  · exact mul_mem hu huv
  · exact mul_mem hu ht
  · exact mul_mem (mul_mem hu huv) ht

theorem card_T_ge [Finite Y] :
    256 ≤ Nat.card (C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} : Subgroup Y) := by
  let f : Co × Fin 8 → ↥(C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} : Subgroup Y) := fun p =>
    ⟨C.ev p.1 * C.dword p.2, mul_mem (Subgroup.mem_sup_left (C.ev_mem p.1)) (C.dword_mem p.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨v, i⟩ ⟨v', i'⟩ h
    have h' : C.ev v * C.dword i = C.ev v' * C.dword i' := congrArg Subtype.val h
    have hi : i = i' := by
      apply dmat_injective
      have hm := congrArg C.mat h'
      rwa [C.mat_ev_mul, C.mat_ev_mul, C.mat_dword, C.mat_dword] at hm
    subst hi
    have hv : v = v' := C.ev_injective (mul_right_cancel h')
    rw [hv]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this

end Arch76.Config

namespace StrothFrame

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem card_T_ge : 256 ≤ Nat.card (F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} :
    Subgroup G) := by
  rw [← F.T_map, Subgroup.card_map_of_injective Subtype.val_injective]
  exact F.configN.card_T_ge

theorem card_le_of_le_centralizer_E {K : Subgroup G} (hK : K ≤ Subgroup.centralizer (F.E : Set G))
    (hK2 : IsPGroup 2 K) : Nat.card K ≤ 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hEC, -, hodd⟩ := F.E_syl
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hK2)
  have hE16 : Nat.card F.E = 2 ^ 4 := F.E_isE.2
  have hCE : Nat.card (Subgroup.centralizer (F.E : Set G)) =
      2 ^ 4 * F.E.relIndex (Subgroup.centralizer (F.E : Set G)) := by
    rw [← hE16, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, Subgroup.relIndex,
      Subgroup.card_mul_index]
  have hdvd : 2 ^ n ∣ 2 ^ 4 * F.E.relIndex (Subgroup.centralizer (F.E : Set G)) := by
    rw [← hn, ← hCE]; exact Subgroup.card_dvd_of_le hK
  have hcop : Nat.Coprime (2 ^ n) (F.E.relIndex (Subgroup.centralizer (F.E : Set G))) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h16 : 2 ^ n ∣ 2 ^ 4 := hcop.dvd_of_dvd_mul_right hdvd
  rw [hn]
  exact Nat.le_of_dvd (by norm_num) h16

theorem card_le_of_perm_six {K : Subgroup (Equiv.Perm (Fin 6))} (hK2 : IsPGroup 2 K) :
    Nat.card K ≤ 16 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hK2)
  have hdvd : 2 ^ n ∣ 720 := by
    rw [← hn, show (720 : ℕ) = Nat.card (Equiv.Perm (Fin 6)) by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl]
    exact Subgroup.card_subgroup_dvd_card K
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ∣ 720 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
    _ = 16 := by norm_num

theorem card_le_of_le_normalizer_E {H : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (F.E : Set G)) (hH2 : IsPGroup 2 H) : Nat.card H ≤ 256 := by
  set NE := Subgroup.normalizer (F.E : Set G)
  obtain ⟨φ, -, hker⟩ := F.E_quot
  set H' := H.subgroupOf NE
  have hH' : Nat.card H' = Nat.card H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have hH'2 : IsPGroup 2 H' := hH2.comap_of_injective NE.subtype Subtype.val_injective
  have hsplit : Nat.card H' = Nat.card (φ.ker.subgroupOf H') * Nat.card (H'.map φ) := by
    rw [← Subgroup.relIndex_ker, Subgroup.relIndex, Subgroup.card_mul_index]
  have hker' : Nat.card (φ.ker.subgroupOf H') ≤ 16 := by
    have hle : (φ.ker.subgroupOf H').map (NE.subtype.comp H'.subtype) ≤
        Subgroup.centralizer (F.E : Set G) := by
      rintro _ ⟨k, hk, rfl⟩
      have hk' : (k : NE) ∈ φ.ker := hk
      rw [hker] at hk'
      exact hk'
    have h2 : IsPGroup 2 ((φ.ker.subgroupOf H').map (NE.subtype.comp H'.subtype)) :=
      (hH'2.to_subgroup _).map _
    have hcard := F.card_le_of_le_centralizer_E (by simpa [MonoidHom.comp_apply] using hle) h2
    rwa [Subgroup.card_map_of_injective
      ((Subtype.val_injective).comp Subtype.val_injective)] at hcard
  have hmap : Nat.card (H'.map φ) ≤ 16 := card_le_of_perm_six (hH'2.map φ)
  rw [← hH', hsplit]
  calc Nat.card (φ.ker.subgroupOf H') * Nat.card (H'.map φ) ≤ 16 * 16 :=
        Nat.mul_le_mul hker' hmap
    _ = 256 := by norm_num

theorem T_le_normalizer_E : F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} ≤
    Subgroup.normalizer (F.E : Set G) := by
  refine sup_le F.A_le ?_
  rw [Subgroup.closure_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  exacts [F.L_le F.dA.uv_mem_L, F.L_le F.dA.t_mem_L, F.L_le F.dA.u_mem_L]

theorem T_le_S : F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} ≤ (F.S : Subgroup G) := by
  refine sup_le F.A_le_S ?_
  rw [Subgroup.closure_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  exacts [F.uv_mem_S, F.t_mem_S, F.u_mem_S]

theorem mem_T_of_normalizer_E {g : G} (hgS : g ∈ (F.S : Subgroup G))
    (hgE : g ∈ Subgroup.normalizer (F.E : Set G)) :
    g ∈ F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} := by
  set T := F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u}
  set H := T ⊔ Subgroup.closure {g}
  have hgH : g ∈ H := Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
  have hHS : H ≤ (F.S : Subgroup G) :=
    sup_le F.T_le_S ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hgS))
  have hHE : H ≤ Subgroup.normalizer (F.E : Set G) :=
    sup_le F.T_le_normalizer_E ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hgE))
  have hH2 : IsPGroup 2 H := (F.S.isPGroup').to_le hHS
  have hTH : T = H := Subgroup.eq_of_le_of_card_ge le_sup_left
    ((F.card_le_of_le_normalizer_E hHE hH2).trans F.card_T_ge)
  rw [hTH]
  exact hgH

theorem a_inv_sq : ((F.dA.a : G)⁻¹) ^ 2 = (F.dA.a : G) ^ 2 := by
  have h4 : (F.dA.a : G) ^ 4 = 1 := by
    have h := F.dA.pow_four_a_inv
    rwa [inv_pow, inv_eq_one] at h
  rw [inv_pow]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact h4)

theorem b_inv_sq : ((F.dA.b : G)⁻¹) ^ 2 = (F.dA.b : G) ^ 2 := by
  have h4 : (F.dA.b : G) ^ 4 = 1 := by
    have h := F.dA.pow_four_b_inv
    rwa [inv_pow, inv_eq_one] at h
  rw [inv_pow]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact h4)

theorem E_map : (Subgroup.closure {F.configN.x ^ 2, F.configN.y ^ 2, F.configN.uv,
    F.configN.t}).map (Subgroup.normalizer (F.A : Set G)).subtype = F.E := by
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton, F.E_eq, ← F.a_inv_sq, ← F.b_inv_sq]
  rfl

theorem T_s_map (s : Subgroup.normalizer (F.A : Set G)) :
    (F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u, s}).map
      (Subgroup.normalizer (F.A : Set G)).subtype =
        F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u, (s : G)} := by
  rw [Subgroup.map_sup, F.configN_A_map, MonoidHom.map_closure, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  rfl

end StrothFrame

theorem coe_mem_normalizer_map {G : Type*} [Group G] {N : Subgroup G} {K : Subgroup N} {g : N}
    (hg : g ∈ Subgroup.normalizer (K : Set N)) :
    (g : G) ∈ Subgroup.normalizer ((K.map N.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨g * k * g⁻¹, (hg k).mp hk, by simp⟩
  · rintro ⟨k', hk', hk'eq⟩
    refine ⟨g⁻¹ * k' * g, (hg (g⁻¹ * k' * g)).mpr (by
      rwa [show g * (g⁻¹ * k' * g) * g⁻¹ = k' by group]), ?_⟩
    simp only [map_mul, map_inv, Subgroup.coe_subtype] at hk'eq ⊢
    rw [hk'eq]; group

namespace StrothFrame

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem arch76Lemma2_normalizer
    (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G) =
        F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} ∨
      ∃ s ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (F.A : Set G) =
          F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u, s} ∧ s * s = 1 ∧
        s⁻¹ * (F.dA.c : G) * s = F.dA.c ∧ s⁻¹ * (F.dA.a : G) * s = (F.dA.a : G)⁻¹ ∧
        s⁻¹ * (F.dA.b : G) * s = (F.dA.b : G)⁻¹ ∧
        ((s⁻¹ * F.dA.uv * s = (F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ * F.dA.uv ∧
            s⁻¹ * F.dA.t * s = (F.dA.a : G) * F.dA.t ∧ s⁻¹ * F.dA.u * s = F.dA.u) ∨
          (s⁻¹ * F.dA.uv * s = (F.dA.a : G) * (F.dA.b : G)⁻¹ * F.dA.uv ∧
            s⁻¹ * F.dA.t * s = (F.dA.a : G) * (F.dA.b : G) ^ 2 * F.dA.t ∧
            s⁻¹ * F.dA.u * s = (F.dA.c : G) * F.dA.u)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (F.A : Set G) with hN
  set Q := (F.S : Subgroup G) ⊓ N with hQ
  obtain ⟨-, hQ2, hQidx⟩ := F.nsylowA
  have hP2 : IsPGroup 2 (Q.subgroupOf N) :=
    hQ2.comap_of_injective N.subtype Subtype.val_injective
  let P : Sylow 2 N := hP2.toSylow hQidx
  have hPc : (P : Subgroup N) = Q.subgroupOf N := rfl
  have hPmap : (P : Subgroup N).map N.subtype = Q := by
    rw [hPc, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hinj : Function.Injective N.subtype := Subtype.val_injective
  have hρodd : Odd (orderOf F.configN.ρ) := by
    rw [show orderOf F.configN.ρ = orderOf F.dA.ρ from Subgroup.orderOf_mk _ _]
    exact F.dA.rho_odd
  have hTP : F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u} ≤ P := by
    rw [← Subgroup.map_le_map_iff_of_injective hinj, F.T_map, hPmap]
    exact le_inf F.T_le_S F.T_le_normalizer
  have hE : ∀ g ∈ (P : Subgroup N),
      g ∈ Subgroup.normalizer (Subgroup.closure
        {F.configN.x ^ 2, F.configN.y ^ 2, F.configN.uv, F.configN.t} : Set N) →
        g ∈ F.configN.A ⊔ Subgroup.closure {F.configN.uv, F.configN.t, F.configN.u} := by
    intro g hg hgE
    have hgS : (g : G) ∈ (F.S : Subgroup G) := (Subgroup.mem_subgroupOf.mp hg).1
    have hgE' := coe_mem_normalizer_map hgE
    rw [F.E_map] at hgE'
    have hT := F.mem_T_of_normalizer_E hgS hgE'
    rw [← F.T_map] at hT
    exact (Subgroup.mem_map_iff_mem hinj).mp hT
  have hcen : ∀ y : N, y ∈ Subgroup.centralizer (F.configN.A : Set N) ↔
      (y : G) ∈ Subgroup.centralizer (F.A : Set G) := by
    intro y
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro h a ha
      have := congrArg Subtype.val (h ⟨a, Subgroup.le_normalizer ha⟩
        (Subgroup.mem_subgroupOf.mpr ha))
      simpa using this
    · intro h a ha
      exact Subtype.ext (by simpa using h a (Subgroup.mem_subgroupOf.mp ha))
  have hCP : Subgroup.centralizer (F.configN.A : Set N) ⊓ P = F.configN.A := by
    ext y
    rw [Subgroup.mem_inf, hcen, hPc, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show _ ↔ (y : G) ∈ F.A
    constructor
    · rintro ⟨h1, h2, -⟩
      have h3 : (y : G) ∈ Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) := ⟨h1, h2⟩
      rwa [hCA] at h3
    · intro h
      rw [← hCA] at h
      exact ⟨h.1, h.2, y.2⟩
  rcases F.configN.lemma2_of_centralizer_inf hρodd P hTP hE hCP with
    h | ⟨s, hs, hPeq, hs2, hsw, hsx, hsy, hrel⟩
  · left
    rw [← hPmap, h, F.T_map]
  · right
    have hsQ : (s : G) ∈ Q := by
      rw [← hPmap]; exact Subgroup.mem_map_of_mem _ hs
    have hval : ∀ {a b : N}, a = b → (a : G) = (b : G) := fun h => congrArg Subtype.val h
    have hinv : ∀ {g z : G}, g⁻¹ * z⁻¹ * g = z → g⁻¹ * z * g = z⁻¹ := fun {g z} h => by
      calc g⁻¹ * z * g = (g⁻¹ * z⁻¹ * g)⁻¹ := by group
        _ = z⁻¹ := by rw [h]
    refine ⟨s, hsQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hPmap, hPeq, F.T_s_map]
    · simpa [pow_two] using hval hs2
    · simpa using hval hsw
    · exact hinv (by simpa using hval hsx)
    · exact hinv (by simpa using hval hsy)
    · rcases hrel with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · left
        exact ⟨by simpa using hval h1, by simpa using hval h2, by simpa using hval h3⟩
      · right
        refine ⟨by simpa using hval h1, ?_, by simpa using hval h3⟩
        have := hval h2
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at this
        rw [coe_configN_t, coe_configN_x, coe_configN_y, inv_inv, F.b_inv_sq] at this
        exact this

end StrothFrame

end CFSG.CGT.Stroth77
