module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44DataCent
public import CFSG.Models.PGLOrders

public section

open Matrix CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44Data

abbrev G44 : Type := ↥(unitarySU 2 2 F16 4)

noncomputable abbrev T44 : Subgroup G44 := (torusSU 5 4 F16).subgroupOf (unitarySU 2 2 F16 4)

theorem torus_le : torusSU 5 4 F16 ≤ unitarySU 2 2 F16 4 :=
  torusSU_le_unitarySU unitaryFieldData (by norm_num)

theorem card_T44 : Nat.card T44 = 5 ^ 3 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe torus_le).toEquiv, card_torus]

theorem mem_T44 {g : G44} : g ∈ T44 ↔ (g : GL (Fin 4) F16) ∈ torusSU 5 4 F16 := Iff.rfl

@[expose] noncomputable def toSU (K : Type) [Group K] (e : K ≃* CFSG.PGLModel.projSU 4 2 2) :
    G44 ≃* K :=
  have hodd : Nat.gcd 4 (2 ^ 2 + 1) = 1 := by norm_num
  (projEquivOfBot (scalars_subgroupOf_eq_bot (K := F16) card_F16 (by norm_num) hodd)).symm.trans
    ((CFSG.PGLModel.projSUEquivStatedProj 4 2 2).symm.trans e.symm)

theorem card_G44 : Nat.card G44 = 1018368000 := by
  let ψ : G44 ≃* CFSG.PGLModel.projSU 4 2 2 := toSU _ (MulEquiv.refl _)
  rw [Nat.card_congr ψ.toEquiv, CFSG.PGLModel.card_projSU_four_four]

structure TorusModel (K : Type) [Group K] (Q : Subgroup K) where
  ψ : G44 ≃* K
  hψ : ∀ g : G44, ψ g ∈ Q ↔ (g : GL (Fin 4) F16) ∈ torusSU 5 4 F16

theorem exists_torusModel {K : Type} [Group K] [Finite K] (e : K ≃* CFSG.PGLModel.projSU 4 2 2)
    (Q : Sylow 5 K) : Nonempty (TorusModel K (Q : Subgroup K)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let ψ₀ := toSU K e
  let P : Subgroup K := T44.map ψ₀.toMonoidHom
  have hPcard : Nat.card P = 5 ^ 3 := by
    rw [Subgroup.card_map_of_injective ψ₀.injective, card_T44]
  have hPg : IsPGroup 5 P := IsPGroup.of_card hPcard
  have hKcard : Nat.card K = 1018368000 := by
    rw [← Nat.card_congr ψ₀.toEquiv, card_G44]
  have hidx : ¬ 5 ∣ P.index := by
    have h := Subgroup.card_mul_index P
    rw [hPcard, hKcard] at h
    have : P.index = 8146944 := by omega
    rw [this]
    norm_num
  let PS : Sylow 5 K := hPg.toSylow hidx
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K PS Q
  have hQ : (Q : Subgroup K) = P.map (MulAut.conj k).toMonoidHom := by
    rw [← hk, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨⟨ψ₀.trans (MulAut.conj k), fun g => ?_⟩⟩
  rw [hQ]
  show (MulAut.conj k) (ψ₀ g) ∈ P.map (MulAut.conj k).toMonoidHom ↔ _
  rw [show (MulAut.conj k) (ψ₀ g) = (MulAut.conj k).toMonoidHom (ψ₀ g) from rfl,
    Subgroup.mem_map_iff_mem (MulAut.conj k).injective]
  show ψ₀.toMonoidHom g ∈ T44.map ψ₀.toMonoidHom ↔ _
  rw [Subgroup.mem_map_iff_mem ψ₀.injective]
  exact mem_T44

theorem card_centralizer_singleton_mulEquiv {G K : Type*} [Group G] [Group K] (ψ : G ≃* K) (g : G) :
    Nat.card ↥(Subgroup.centralizer ({ψ g} : Set K)) =
      Nat.card ↥(Subgroup.centralizer ({g} : Set G)) := by
  refine Nat.card_congr ⟨fun z => ⟨ψ.symm z.1, ?_⟩, fun w => ⟨ψ w.1, ?_⟩, fun z => ?_, fun w => ?_⟩
  · have := Subgroup.mem_centralizer_singleton_iff.mp z.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact this
  · have := Subgroup.mem_centralizer_singleton_iff.mp w.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, ← map_mul, this]
  · exact Subtype.ext (by simp)
  · exact Subtype.ext (by simp)

namespace TorusModel

variable {K : Type} [Group K] {Q : Subgroup K} (M : TorusModel K Q)

@[expose] noncomputable def tk (n : Fin 4 → ZMod 5) (h : ∑ i, n i = 0) : K :=
  M.ψ ⟨ldg n, ldg_mem_unitarySU h⟩

theorem tk_mem (n : Fin 4 → ZMod 5) (h : ∑ i, n i = 0) : M.tk n h ∈ Q :=
  (M.hψ _).mpr (ldg_mem_torus h)

theorem exists_tk {y : K} (hy : y ∈ Q) :
    ∃ (n : Fin 4 → ZMod 5) (h : ∑ i, n i = 0), y = M.tk n h := by
  have hg : ((M.ψ.symm y : G44) : GL (Fin 4) F16) ∈ torusSU 5 4 F16 :=
    (M.hψ _).mp (by rwa [MulEquiv.apply_symm_apply])
  obtain ⟨n, hn, hng⟩ := exists_ldg_of_mem_torus hg
  refine ⟨n, hn, ?_⟩
  unfold tk
  have : (⟨ldg n, ldg_mem_unitarySU hn⟩ : G44) = M.ψ.symm y := Subtype.ext hng
  rw [this, MulEquiv.apply_symm_apply]

theorem tk_zero : M.tk 0 (by simp) = 1 := by
  unfold tk
  have : (⟨ldg 0, ldg_mem_unitarySU (by simp)⟩ : G44) = 1 := Subtype.ext ldg_zero
  rw [this, map_one]

theorem tk_eq_one_iff {n : Fin 4 → ZMod 5} (h : ∑ i, n i = 0) : M.tk n h = 1 ↔ n = 0 := by
  constructor
  · intro h1
    unfold tk at h1
    have h2 : (⟨ldg n, ldg_mem_unitarySU h⟩ : G44) = 1 := M.ψ.injective (by rw [h1, map_one])
    have h3 : ldg n = ldg 0 := (congrArg Subtype.val h2).trans ldg_zero.symm
    exact ldg_injective h3
  · rintro rfl
    exact M.tk_zero

include M in
theorem pow_five_of_mem {y : K} (hy : y ∈ Q) : y ^ 5 = 1 := by
  obtain ⟨n, h, rfl⟩ := M.exists_tk hy
  unfold tk
  rw [← map_pow]
  have : (⟨ldg n, ldg_mem_unitarySU h⟩ : G44) ^ 5 = 1 :=
    Subtype.ext (torus_pow_five (ldg_mem_torus h))
  rw [this, map_one]

include M in
theorem card_Q [Finite K] : Nat.card Q = 5 ^ 3 := by
  have h : Q = T44.map M.ψ.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro hy
      exact (M.hψ (M.ψ.symm y)).mp (by rwa [MulEquiv.apply_symm_apply])
    · intro hy
      have := (M.hψ (M.ψ.symm y)).mpr hy
      rwa [MulEquiv.apply_symm_apply] at this
  rw [h, Subgroup.card_map_of_injective M.ψ.injective, card_T44]

theorem ψ_mem_zpowers_iff (g g' : G44) :
    M.ψ g' ∈ Subgroup.zpowers (M.ψ g) ↔
      (g' : GL (Fin 4) F16) ∈ Subgroup.zpowers (g : GL (Fin 4) F16) := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [← map_zpow] at hk
    have := congrArg Subtype.val (M.ψ.injective hk)
    exact ⟨k, by simpa using this⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hk)

theorem mem_zpowers_tk_iff {n m : Fin 4 → ZMod 5} (hn : ∑ i, n i = 0) (hm : ∑ i, m i = 0) :
    M.tk m hm ∈ Subgroup.zpowers (M.tk n hn) ↔ ∃ c : ZMod 5, ∀ i, m i = c * n i := by
  unfold tk
  rw [M.ψ_mem_zpowers_iff]
  exact ldg_mem_Ln_iff

theorem zpowers_tk_eq_of_smul {n m : Fin 4 → ZMod 5} (hn : ∑ i, n i = 0) (hm : ∑ i, m i = 0)
    {c : ZMod 5} (hc : c ≠ 0) (h : ∀ i, m i = c * n i) :
    Subgroup.zpowers (M.tk m hm) = Subgroup.zpowers (M.tk n hn) := by
  obtain ⟨d, hd, -⟩ := exists_inv_zmod5 c hc
  refine le_antisymm (Subgroup.zpowers_le.mpr ((M.mem_zpowers_tk_iff hn hm).mpr ⟨c, h⟩))
    (Subgroup.zpowers_le.mpr ((M.mem_zpowers_tk_iff hm hn).mpr ⟨d, fun i => ?_⟩))
  rw [h i, ← mul_assoc, mul_comm d c, hd, one_mul]

theorem conj_perm_tk (τ : Equiv.Perm (Fin 4)) {n : Fin 4 → ZMod 5} (hn : ∑ i, n i = 0)
    (hw : ∑ i, (n ∘ τ.symm) i = 0) :
    M.ψ ⟨permGL τ, permGL_mem_unitarySU unitaryFieldData τ⟩ * M.tk n hn *
        (M.ψ ⟨permGL τ, permGL_mem_unitarySU unitaryFieldData τ⟩)⁻¹ = M.tk (n ∘ τ.symm) hw := by
  unfold tk
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show (permGL τ : GL (Fin 4) F16) * ldg n * (permGL τ : GL (Fin 4) F16)⁻¹ = _
  exact permGL_conj_ldg τ n

theorem fusion_tk (g : K) {n m : Fin 4 → ZMod 5} (hn : ∑ i, n i = 0) (hm : ∑ i, m i = 0)
    (h : g * M.tk n hn * g⁻¹ = M.tk m hm) : ∃ π : Equiv.Perm (Fin 4), ∀ i, m (π i) = n i := by
  unfold tk at h
  set γ : G44 := M.ψ.symm g with hγ
  have hg : g = M.ψ γ := by rw [hγ, MulEquiv.apply_symm_apply]
  rw [hg, ← map_inv, ← map_mul, ← map_mul] at h
  have h2 := M.ψ.injective h
  have h3 : (γ : GL (Fin 4) F16) * diagU (dv n) * (γ : GL (Fin 4) F16)⁻¹ = diagU (dv m) := by
    have := congrArg Subtype.val h2
    simpa [ldg] using this
  obtain ⟨π, hπ⟩ := exists_perm_of_conj_diagU (dv n) (dv m) (γ : GL (Fin 4) F16) h3
  exact ⟨π, fun i => pw_injective (hπ i)⟩

theorem exists_cls_of_nine_dvd [Finite K] {x : K} (hx : x ∈ Q) (hx1 : x ≠ 1)
    (h9 : 9 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set K))) :
    ∃ (n : Fin 4 → ZMod 5) (h : ∑ i, n i = 0), x = M.tk n h ∧ n ≠ 0 ∧ NoSingle n := by
  obtain ⟨n, hn, rfl⟩ := M.exists_tk hx
  refine ⟨n, hn, rfl, fun h0 => hx1 ((M.tk_eq_one_iff hn).mpr h0), ?_⟩
  by_contra hns
  obtain ⟨i₀, hs⟩ := (noSingle_or n).mp hns
  refine not_nine_dvd_card_centralizer hn hs ?_
  rw [← card_centralizer_singleton_mulEquiv M.ψ ⟨ldg n, ldg_mem_unitarySU hn⟩]
  exact h9

include M in
theorem ncard_conj_lines [Finite K] {x : K} (hx : x ∈ Q) (hx1 : x ≠ 1)
    (h9 : 9 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set K))) :
    Set.ncard {A : Subgroup K | ∃ g : K,
      A = (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ Q} = 3 := by
  obtain ⟨n, hn, rfl, hn0, hns⟩ := M.exists_cls_of_nine_dvd hx hx1 h9
  obtain ⟨σ, s, hs0, hσ⟩ := cls n hn hn0 hns
  have hmap : ∀ g : K, (Subgroup.zpowers (M.tk n hn)).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * M.tk n hn * g⁻¹) := by
    intro g
    rw [MonoidHom.map_zpowers]
    rfl
  have hA : ∀ (w : Fin 4 → ZMod 5) (hw : ∑ i, w i = 0) (ρ : Equiv.Perm (Fin 4)),
      (∀ i, w i = v1 (ρ i)) → Subgroup.zpowers (M.tk w hw) ∈ {A : Subgroup K | ∃ g : K,
        A = (Subgroup.zpowers (M.tk n hn)).map (MulAut.conj g).toMonoidHom ∧ A ≤ Q} := by
    intro w hw ρ hρ
    set τ : Equiv.Perm (Fin 4) := (ρ.trans σ.symm).symm with hτ
    have hnτ : ∀ i, (n ∘ τ.symm) i = s * w i := by
      intro i
      simp only [Function.comp_apply, hτ, Equiv.symm_symm, Equiv.trans_apply]
      rw [hσ, Equiv.apply_symm_apply, hρ]
    have hsum : ∑ i, (n ∘ τ.symm) i = 0 := (Equiv.sum_comp τ.symm n).trans hn
    refine ⟨M.ψ ⟨permGL τ, permGL_mem_unitarySU unitaryFieldData τ⟩, ?_,
      Subgroup.zpowers_le.mpr (M.tk_mem _ _)⟩
    rw [hmap, M.conj_perm_tk τ hn hsum]
    exact (M.zpowers_tk_eq_of_smul hw hsum hs0 hnτ).symm
  have hS : {A : Subgroup K | ∃ g : K,
      A = (Subgroup.zpowers (M.tk n hn)).map (MulAut.conj g).toMonoidHom ∧ A ≤ Q} =
      {Subgroup.zpowers (M.tk v1 sum_v1), Subgroup.zpowers (M.tk v2 sum_v2),
        Subgroup.zpowers (M.tk v3 sum_v3)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, rfl, hle⟩
      rw [hmap] at hle ⊢
      have hyQ : g * M.tk n hn * g⁻¹ ∈ Q := hle (Subgroup.mem_zpowers _)
      obtain ⟨m, hm, hym⟩ := M.exists_tk hyQ
      obtain ⟨π, hπ⟩ := M.fusion_tk g hn hm hym
      have hmj : ∀ j, m j = s * v1 ((π.symm.trans σ) j) := by
        intro j
        have := hπ (π.symm j)
        rw [Equiv.apply_symm_apply] at this
        rw [this, hσ]
        rfl
      obtain ⟨c, hc0, hc⟩ := lines_cases (π.symm.trans σ)
      have hsc : s * c ≠ 0 := mul_ne_zero_zmod5 s c hs0 hc0
      rw [hym]
      rcases hc with hc | hc | hc
      · left
        exact M.zpowers_tk_eq_of_smul sum_v1 hm hsc (fun j => by rw [hmj, hc, mul_assoc])
      · right; left
        exact M.zpowers_tk_eq_of_smul sum_v2 hm hsc (fun j => by rw [hmj, hc, mul_assoc])
      · right; right
        exact M.zpowers_tk_eq_of_smul sum_v3 hm hsc (fun j => by rw [hmj, hc, mul_assoc])
    · rintro (rfl | rfl | rfl)
      · exact hA v1 sum_v1 1 (fun i => rfl)
      · exact hA v2 sum_v2 (Equiv.swap 1 2) v2_eq
      · exact hA v3 sum_v3 (Equiv.swap 1 3) v3_eq
  rw [hS]
  refine Set.ncard_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
  · intro h
    have : M.tk v2 sum_v2 ∈ Subgroup.zpowers (M.tk v1 sum_v1) := h ▸ Subgroup.mem_zpowers _
    obtain ⟨c, hc⟩ := (M.mem_zpowers_tk_iff sum_v1 sum_v2).mp this
    exact (lines_ne c).1 hc
  · intro h
    have : M.tk v3 sum_v3 ∈ Subgroup.zpowers (M.tk v1 sum_v1) := h ▸ Subgroup.mem_zpowers _
    obtain ⟨c, hc⟩ := (M.mem_zpowers_tk_iff sum_v1 sum_v3).mp this
    exact (lines_ne c).2.1 hc
  · intro h
    have : M.tk v3 sum_v3 ∈ Subgroup.zpowers (M.tk v2 sum_v2) := h ▸ Subgroup.mem_zpowers _
    obtain ⟨c, hc⟩ := (M.mem_zpowers_tk_iff sum_v2 sum_v3).mp this
    exact (lines_ne c).2.2 hc

include M in
theorem inf_centralizer_le [Finite K] {x a : K} (hx : x ∈ Q) (ha : a ∈ Q) (hx1 : x ≠ 1)
    (ha1 : a ≠ 1) (hx9 : 9 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set K)))
    (ha9 : 9 ∣ Nat.card ↥(Subgroup.centralizer ({a} : Set K)))
    (hne : Subgroup.zpowers x ≠ Subgroup.zpowers a) :
    Subgroup.centralizer ({x} : Set K) ⊓ Subgroup.centralizer ({a} : Set K) ≤ Q := by
  obtain ⟨n, hn, rfl, hn0, hns⟩ := M.exists_cls_of_nine_dvd hx hx1 hx9
  obtain ⟨m, hm, rfl, hm0, hms⟩ := M.exists_cls_of_nine_dvd ha ha1 ha9
  have hsep : ∀ i j, i ≠ j → n i ≠ n j ∨ m i ≠ m j := by
    intro i j hij
    by_contra hcon
    push Not at hcon
    obtain ⟨σ, s, hs0, hσ⟩ := cls n hn hn0 hns
    obtain ⟨τ, t, ht0, hτ⟩ := cls m hm hm0 hms
    have hσij : v1 (σ i) = v1 (σ j) :=
      cancel_zmod5 s _ _ hs0 (by rw [← hσ, ← hσ]; exact hcon.1)
    have hτij : v1 (τ i) = v1 (τ j) :=
      cancel_zmod5 t _ _ ht0 (by rw [← hτ, ← hτ]; exact hcon.2)
    obtain ⟨c, hc0, hc⟩ := pairing_perm σ τ ⟨i, j, hij, hσij, hτij⟩
    obtain ⟨s', hs', hs'0⟩ := exists_inv_zmod5 s hs0
    have hd : t * c * s' ≠ 0 := mul_ne_zero_zmod5 _ _ (mul_ne_zero_zmod5 _ _ ht0 hc0) hs'0
    apply hne
    exact (M.zpowers_tk_eq_of_smul hn hm hd (fun k => by
      rw [hτ k, hc k, hσ k]
      calc t * (c * v1 (σ k)) = t * c * (s' * s) * v1 (σ k) := by rw [mul_comm s' s, hs']; ring
        _ = _ := by ring)).symm
  intro g hg
  obtain ⟨hgx, hga⟩ := hg
  have hcx := Subgroup.mem_centralizer_singleton_iff.mp hgx
  have hca := Subgroup.mem_centralizer_singleton_iff.mp hga
  set γ : G44 := M.ψ.symm g with hγ
  have hg' : g = M.ψ γ := by rw [hγ, MulEquiv.apply_symm_apply]
  have hcomm : ∀ (k : Fin 4 → ZMod 5) (hk : ∑ i, k i = 0), g * M.tk k hk = M.tk k hk * g →
      (γ : GL (Fin 4) F16) * ldg k = ldg k * (γ : GL (Fin 4) F16) := by
    intro k hk h
    unfold tk at h
    rw [hg', ← map_mul, ← map_mul] at h
    have := congrArg Subtype.val (M.ψ.injective h)
    simpa using this
  have := mem_torus_of_commute hsep γ.2 (hcomm n hn hcx) (hcomm m hm hca)
  rw [hg']
  exact (M.hψ γ).mpr this

end TorusModel

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44Data
