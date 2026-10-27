module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1Desc

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split
open scoped commutatorElement

theorem V_fix4 : ∀ σ ∈ Vset, σ 4 = 4 := by decide +kernel

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by revert c; decide

theorem mem_zpowers_two {G : Type*} [Group G] {g : G} (hg : g * g = 1) (x : G) :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  have h2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, h2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_one, h2, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

theorem exists_split_w (w : evenWeight 5) :
    ∃ w₁ w₂ : evenWeight 5, w = w₁ + w₂ ∧ w₁.1 4 = 0 ∧
      (w₂ = 0 ∨ w₂ = ⟨w04, w04_even⟩) := by
  rcases zmod2_cases (w.1 4) with h | h
  · exact ⟨w, 0, by simp, h, Or.inl rfl⟩
  · refine ⟨w + ⟨w04, w04_even⟩, ⟨w04, w04_even⟩, ?_, ?_, Or.inr rfl⟩
    · rw [add_assoc, Delta_add_self, add_zero]
    · show w.1 4 + w04 4 = 0
      rw [h]
      decide

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

@[expose] def Sinc (C : StdCfg T M H S L) : ↥S →* ↥H := Subgroup.inclusion C.hcs.sylow.le

theorem iV_mem_S (C : StdCfg T M H S L) (u : evenWeight 5) : ((C.iV u : ↥H) : G) ∈ S :=
  blockU_le_S C.hcs C.hj (C.iV_mem_U u)

theorem zU_eq_iV (C : StdCfg T M H S L) : C.zU = ((C.iV StdCfg.z0V : ↥H) : G) := rfl

theorem zU_comm (C : StdCfg T M H S L) (y : ↥H) (hy : C.D.π y 4 = 4) :
    (y : G) * C.zU = C.zU * (y : G) := by
  have h := (C.conj_zU_iff y).mpr (z0_fixed _ hy)
  calc (y : G) * C.zU = ((y : G) * C.zU * (y : G)⁻¹) * (y : G) := by group
    _ = C.zU * (y : G) := by rw [h]

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

@[expose] def Psub : Subgroup G where
  carrier := {x | ∃ (w : evenWeight 5) (σ : Equiv.Perm (Fin 5)),
    σ ∈ Vstd ∧ w.1 4 = 0 ∧ x = ((X.emb w σ : ↥H) : G)}
  mul_mem' := by
    rintro _ _ ⟨w, σ, hσ, hw, rfl⟩ ⟨w', σ', hσ', hw', rfl⟩
    have h4 : σ 4 = 4 := V_fix4 σ hσ
    refine ⟨w + vact σ w', σ * σ', mul_mem hσ hσ', ?_, ?_⟩
    · show w.1 4 + pact σ w'.1 4 = 0
      rw [pact_four h4, hw, hw', add_zero]
    · exact congrArg Subtype.val (X.emb_mul w w' σ σ')
  one_mem' := ⟨0, 1, one_mem _, rfl, congrArg Subtype.val X.emb_zero_one.symm⟩
  inv_mem' := by
    rintro _ ⟨w, σ, hσ, hw, rfl⟩
    have h4 : σ 4 = 4 := V_fix4 σ hσ
    refine ⟨vact σ⁻¹ w, σ⁻¹, inv_mem hσ, ?_, ?_⟩
    · show pact σ⁻¹ w.1 4 = 0
      have : σ⁻¹ 4 = 4 := Equiv.Perm.inv_eq_iff_eq.mpr h4.symm
      rw [pact_four this, hw]
    · exact congrArg Subtype.val (X.emb_inv w σ)

theorem mem_Psub_iff (x : G) : x ∈ X.Psub ↔
    x ∈ X.Ksub ∧ ∃ h : ↥H, (h : G) = x ∧ C.D.π h ∈ Vstd := by
  constructor
  · rintro ⟨w, σ, hσ, hw, rfl⟩
    refine ⟨⟨w, σ, (mem_A4std σ).mpr (Vset_sub_A4 σ hσ), hw, rfl⟩, X.emb w σ, rfl, ?_⟩
    rw [X.pi_emb]
    exact hσ
  · rintro ⟨⟨w, σ, hσ, hw, rfl⟩, h, hh, hπ⟩
    have : h = X.emb w σ := Subtype.ext hh
    rw [this, X.pi_emb] at hπ
    exact ⟨w, σ, hπ, hw, rfl⟩

theorem Psub_le_Ksub : X.Psub ≤ X.Ksub := fun _ hx => ((X.mem_Psub_iff _).mp hx).1

theorem Ksub_normalizes_Psub : X.Ksub ≤ Subgroup.normalizer (X.Psub : Set G) := by
  have key : ∀ k ∈ X.Ksub, ∀ p ∈ X.Psub, k * p * k⁻¹ ∈ X.Psub := by
    intro k hk p hp
    rw [X.mem_Psub_iff] at hp ⊢
    obtain ⟨hpK, h, hh, hπ⟩ := hp
    obtain ⟨w, σ, hσ, hw, rfl⟩ := hk
    refine ⟨mul_mem (mul_mem ⟨w, σ, hσ, hw, rfl⟩ hpK) (inv_mem ⟨w, σ, hσ, hw, rfl⟩),
      X.emb w σ * h * (X.emb w σ)⁻¹, ?_, ?_⟩
    · rw [← hh]
      rfl
    · rw [map_mul, map_mul, map_inv, X.pi_emb]
      exact A4_conj_V σ hσ _ hπ
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => key k hk p hp, fun hp => ?_⟩
  have := key k⁻¹ (inv_mem hk) _ hp
  have e : k⁻¹ * (k * p * k⁻¹) * k⁻¹⁻¹ = p := by group
  rwa [e] at this

theorem emb_pow4 {w : evenWeight 5} {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ Vset) :
    (X.emb w σ) ^ 4 = 1 := by
  have h2 : X.emb w σ * X.emb w σ = X.emb (w + vact σ w) 1 := by
    rw [X.emb_mul, Vset_sq σ hσ]
  have h4 : X.emb (w + vact σ w) 1 * X.emb (w + vact σ w) 1 = 1 := by
    rw [X.emb_mul, vact_one, mul_one, Delta_add_self, X.emb_zero_one]
  rw [pow_four', h2, h4]

theorem Psub_isPGroup : IsPGroup 2 ↥X.Psub := by
  rintro ⟨x, hx⟩
  obtain ⟨w, σ, hσ, hw, rfl⟩ := hx
  refine ⟨2, ?_⟩
  apply Subtype.ext
  have h := congrArg Subtype.val (X.emb_pow4 (w := w) hσ)
  rw [Subgroup.coe_pow] at h
  exact h

theorem borelP_eq : borelP M L = X.Psub := by
  rw [borelP, X.borelK_eq]
  apply le_antisymm
  · intro x hx
    have hxK : x ∈ X.Ksub := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hx
    obtain ⟨n, hn⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X.Ksub) ⟨x, hx⟩
    have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨w, σ, hσ, hw, rfl⟩ := hxK
    have h1 : (X.emb w σ) ^ 2 ^ n = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hxn)
    have h2 : σ ^ 2 ^ n = 1 := by
      have := congrArg C.D.π h1
      rwa [map_pow, X.pi_emb, map_one] at this
    have hV : σ ∈ Vset := by
      by_contra hnV
      obtain ⟨h3, h1'⟩ := A4_not_V σ hσ hnV
      have h5 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
      have hg : Nat.gcd (2 ^ n) 3 = 1 := Nat.Coprime.pow_left n (by decide)
      rw [hg, pow_one] at h5
      exact h1' h5
    exact ⟨w, σ, hV, hw, rfl⟩
  · exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 X.Psub X.Ksub
      X.Psub_le_Ksub
      ((Subgroup.normal_subgroupOf_iff_le_normalizer X.Psub_le_Ksub).mpr X.Ksub_normalizes_Psub)
      X.Psub_isPGroup

theorem P_le_S : borelP M L ≤ S := by
  rw [X.borelP_eq]
  rintro _ ⟨w, σ, hσ, hw, rfl⟩
  refine (X.mem_S_iff (X.emb w σ)).mpr ?_
  rw [X.pi_emb]
  exact (mem_Dstd _).mpr (Vset_sub_Dset σ hσ)

theorem S_eq : S = borelP M L ⊔ baum S := by
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ H := C.hcs.sylow.le hx
    set h : ↥H := ⟨x, hxH⟩ with hh
    have hπ : C.D.π h ∈ Dstd := (X.mem_S_iff h).mp hx
    obtain ⟨v, hv, e, he, hve⟩ := D_eq_VE (C.D.π h) ((mem_Dstd _).mp hπ)
    obtain ⟨w₁, w₂, hw, hw₁, -⟩ := exists_split_w (X.cw h)
    have hspec : h = X.emb (X.cw h) (v * e) := by
      rw [← hve]
      exact X.cw_spec h
    have hdecomp : h = X.emb w₁ v * X.emb (vact v⁻¹ w₂) e := by
      rw [X.emb_mul, ← vact_mul, mul_inv_cancel, vact_one, ← hw, ← hspec]
    have hxe : x = ((X.emb w₁ v : ↥H) : G) * ((X.emb (vact v⁻¹ w₂) e : ↥H) : G) :=
      congrArg Subtype.val hdecomp
    have hp : ((X.emb w₁ v : ↥H) : G) ∈ borelP M L := by
      rw [X.borelP_eq]
      exact ⟨w₁, v, hv, hw₁, rfl⟩
    have hr : ((X.emb (vact v⁻¹ w₂) e : ↥H) : G) ∈ baum S := by
      refine (X.mem_R_iff _).mpr ?_
      rw [X.pi_emb]
      exact (mem_Estd e).mpr he
    rw [hxe]
    exact mul_mem (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hr)
  · exact sup_le X.P_le_S baum_le_S

@[expose] noncomputable def c4S : ↥S →* Multiplicative (ZMod 2) where
  toFun y := Multiplicative.ofAdd ((X.cw (C.Sinc y)).1 4)
  map_one' := by
    show Multiplicative.ofAdd ((X.cw (C.Sinc 1)).1 4) = 1
    rw [map_one, X.cw4_one]
    rfl
  map_mul' y y' := by
    show Multiplicative.ofAdd ((X.cw (C.Sinc (y * y'))).1 4) =
      Multiplicative.ofAdd ((X.cw (C.Sinc y)).1 4) *
        Multiplicative.ofAdd ((X.cw (C.Sinc y')).1 4)
    have hh : C.D.π (C.Sinc y) 4 = 4 := by
      have := (X.mem_S_iff (C.Sinc y)).mp y.2
      exact D_fix4 _ ((mem_Dstd _).mp this)
    rw [map_mul, X.cw4_mul _ _ hh, ofAdd_add]

theorem pi_Sinc_mem (y : ↥S) : C.D.π (C.Sinc y) ∈ Dstd :=
  (X.mem_S_iff (C.Sinc y)).mp y.2

theorem mem_Psub_of_S (y : ↥S) (h1 : C.D.π (C.Sinc y) ∈ Vstd) (h2 : X.c4S y = 1) :
    (y : G) ∈ X.Psub := by
  have h4 : (X.cw (C.Sinc y)).1 4 = 0 :=
    Multiplicative.ofAdd.injective (h2.trans ofAdd_zero.symm)
  refine ⟨X.cw (C.Sinc y), C.D.π (C.Sinc y), h1, h4, ?_⟩
  exact congrArg Subtype.val (X.cw_spec (C.Sinc y))

theorem frattini_le : (frattini ↥S).map S.subtype ≤ borelP M L := by
  have : Fact (IsPGroup 2 ↥S) := ⟨C.hcs.sylow.2.1⟩
  rw [X.borelP_eq]
  rw [Subgroup.map_le_iff_le_comap, CFSG.frattini_eq_closure_commutator_union_powers (p := 2),
    Subgroup.closure_le]
  have hcomm : _root_.commutator ↥S ≤ X.Psub.comap S.subtype := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    show ((⁅g₁, g₂⁆ : ↥S) : G) ∈ X.Psub
    apply X.mem_Psub_of_S
    · rw [map_commutatorElement, map_commutatorElement]
      have h1 := D_comm_V _ (X.pi_Sinc_mem g₁) _ (X.pi_Sinc_mem g₂)
      exact h1
    · rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rintro y (hy | ⟨z, rfl⟩)
  · exact hcomm hy
  · show ((z ^ 2 : ↥S) : G) ∈ X.Psub
    apply X.mem_Psub_of_S
    · rw [map_pow, map_pow, pow_two]
      exact D_sq_V _ (X.pi_Sinc_mem z)
    · rw [map_pow, pow_two]
      show Multiplicative.ofAdd _ * Multiplicative.ofAdd _ = 1
      rw [← ofAdd_add, zmod2_add_self]
      rfl

theorem s_mem_S {τ : Equiv.Perm (Fin 5)} (hτ : τ ∈ Dset) : ((X.s τ : ↥H) : G) ∈ S := by
  refine (X.mem_S_iff _).mpr ?_
  rw [X.hs]
  exact (mem_Dstd _).mpr hτ

theorem vact_fixed_of_comm (h : ↥H) (u : evenWeight 5) (hc : h * C.iV u = C.iV u * h) :
    vact (C.D.π h) u = u := by
  have h1 := C.conj_iV X.hTC h u
  have h2 : h * C.iV u * h⁻¹ = C.iV u := by rw [hc]; group
  rw [h2] at h1
  exact (C.iV_inj X.hTC h1.symm)

theorem centerOf_S_iff (x : G) : x ∈ centerOf S ↔ x = 1 ∨ x = C.zU := by
  constructor
  · intro hx
    obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.mp hx
    have hcomm : ∀ s ∈ S, s * x = x * s := fun s hs => Subgroup.mem_centralizer_iff.mp hxc s hs
    have hxH : x ∈ H := C.hcs.sylow.le hxS
    set h : ↥H := ⟨x, hxH⟩ with hh
    have hσ1 : C.D.π h = 1 := by
      apply vact_faithful
      intro u
      have hc : h * C.iV u = C.iV u * h := Subtype.ext (hcomm _ (C.iV_mem_S u)).symm
      exact X.vact_fixed_of_comm h u hc
    have hspec : h = C.iV (X.cw h) := by
      have h1 := X.cw_spec h
      rw [hσ1] at h1
      calc h = X.emb (X.cw h) 1 := h1
        _ = C.iV (X.cw h) := by rw [Sec.emb, map_one, mul_one]
    have hfix : ∀ τ ∈ Dset, vact τ (X.cw h) = X.cw h := by
      intro τ hτ
      have hc : X.s τ * C.iV (X.cw h) = C.iV (X.cw h) * X.s τ := by
        rw [← hspec]
        exact Subtype.ext (hcomm _ (X.s_mem_S hτ))
      have := C.conj_iV X.hTC (X.s τ) (X.cw h)
      rw [X.hs] at this
      have h2 : X.s τ * C.iV (X.cw h) * (X.s τ)⁻¹ = C.iV (X.cw h) := by rw [hc]; group
      rw [h2] at this
      exact C.iV_inj X.hTC this.symm
    rcases fixed_Dset (X.cw h).1 (X.cw h).2 (fun σ hσ => congrArg Subtype.val (hfix σ hσ)) with
      h0 | h0
    · left
      have : X.cw h = 0 := Subtype.ext h0
      rw [this, C.iV_zero] at hspec
      exact congrArg Subtype.val hspec
    · right
      have : X.cw h = StdCfg.z0V := Subtype.ext h0
      rw [this] at hspec
      exact congrArg Subtype.val hspec
  · rintro (rfl | rfl)
    · exact one_mem _
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact blockU_le_S C.hcs C.hj C.zU_mem
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyH : y ∈ H := C.hcs.sylow.le hy
        have := (C.conj_zU_iff ⟨y, hyH⟩).mpr (z0_fixed _ (D_fix4 _ ((mem_Dstd _).mp
          ((X.mem_S_iff ⟨y, hyH⟩).mp hy))))
        calc y * C.zU = (y * C.zU * y⁻¹) * y := by group
          _ = C.zU * y := by rw [show y * C.zU * y⁻¹ = C.zU from this]

end Sec

end CFSG.QuasithinUnique.A5
