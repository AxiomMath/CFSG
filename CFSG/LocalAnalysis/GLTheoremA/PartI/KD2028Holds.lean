module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD2028
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MM22
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCard
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Mathieu
public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB

private theorem kdh_transport {L M : Type} [Group L] [Group M] (e : L ≃* M)
    (h : ∃ x : M, orderOf x = 3 ∧ x ∉ Subgroup.center M ∧ ∃ T : Subgroup M, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set M)) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set L) := by
  obtain ⟨x, hx3, hxZ, T, hT, hT2, hxN⟩ := h
  have hmem : ∀ z : L, z ∈ T.map e.symm.toMonoidHom ↔ e z ∈ T := fun z => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  refine ⟨e.symm x, ?_, ?_, T.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hx3
  · intro hc
    apply hxZ
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    have h1 := congrArg e (hc (e.symm g))
    simpa using h1
  · intro h0
    apply hT
    apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
    rw [h0, Subgroup.map_bot]
  · intro g
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨k, hk⟩ := hT2 ⟨y, hy⟩
    have hk' : y ^ 2 ^ k = 1 := by
      have h1 := congrArg Subtype.val hk
      simpa using h1
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hyg, ← map_pow, hk', map_one]
  · rw [Subgroup.mem_set_normalizer_iff]
    intro y
    have hN := Subgroup.mem_set_normalizer_iff.mp hxN (e y)
    simp only [SetLike.mem_coe, hmem, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hN

private theorem kdh_exp_center {L : Type} [Group L] [Finite L]
    (hZ : Nat.card (Subgroup.center L) = 3) : ∀ z ∈ Subgroup.center L, z ^ 3 = 1 := by
  intro z hz
  have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥(Subgroup.center L)) (x := ⟨z, hz⟩))
  rw [hZ] at h
  simpa using h

private theorem kdh_hexp_of_sylow {L : Type} [Group L] [Finite L]
    (hS : ∀ R : Sylow 3 L, ∀ r ∈ (R : Subgroup L), r ^ 3 = 1) :
    ∀ x : L, IsPGroup 3 (Subgroup.zpowers x) → x ^ 3 = 1 := by
  intro x hx
  obtain ⟨R, hR⟩ := IsPGroup.exists_le_sylow hx
  exact hS R x (hR (Subgroup.mem_zpowers x))

private theorem kdh_sign_emb {n : ℕ} (hn : 4 ≤ n) (σ : Equiv.Perm (Fin 4)) :
    Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn) σ) = Equiv.Perm.sign σ := by
  classical
  rw [Equiv.Perm.viaEmbeddingHom_apply]
  unfold Equiv.Perm.viaEmbedding
  convert Equiv.Perm.sign_extendDomain σ (Equiv.ofInjective _ (Fin.castLEEmb hn).injective)

private noncomputable def kdh_emb {n : ℕ} (hn : 4 ≤ n) : alternatingGroup (Fin 4) →* alternatingGroup (Fin n) :=
  ((Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn)).comp
    (alternatingGroup (Fin 4)).subtype).codRestrict (alternatingGroup (Fin n))
    (fun σ => Equiv.Perm.mem_alternatingGroup.mpr
      ((kdh_sign_emb hn σ.1).trans (Equiv.Perm.mem_alternatingGroup.mp σ.2)))

private theorem kdh_emb_injective {n : ℕ} (hn : 4 ≤ n) : Function.Injective (kdh_emb hn) := by
  intro a b hab
  apply Subtype.ext
  apply Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb hn)
  exact congrArg Subtype.val hab

private theorem kdh_hat_alt {L : Type} [Group L] [Finite L]
    (hZ : Nat.card (Subgroup.center L) = 3) {n : ℕ} (hn : 4 ≤ n)
    (e : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n))
    (hexp : ∀ x : L, IsPGroup 3 (Subgroup.zpowers x) → x ^ 3 = 1) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set L) :=
  kd2028_hat L hZ (e.symm.toMonoidHom.comp (kdh_emb hn))
    (e.symm.injective.comp (kdh_emb_injective hn)) hexp

private theorem kdh_isPGroup_two {G : Type*} [Group G] (T : Subgroup G) (h : ∀ g ∈ T, g ^ 2 = 1) :
    IsPGroup 2 T := by
  intro g
  refine ⟨1, ?_⟩
  show g ^ 2 = 1
  exact Subtype.ext (by simpa using h g.1 g.2)


private theorem kdh_comm_of_sq {L : Type} [Group L] (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1)
    {g h : L} (hg : g ^ 2 = 1) (hh : h ^ 2 = 1)
    (hm : (g : L ⧸ Subgroup.center L) * (h : L ⧸ Subgroup.center L) =
      (h : L ⧸ Subgroup.center L) * (g : L ⧸ Subgroup.center L)) : g * h = h * g := by
  have hgg : g * g = 1 := by rw [← sq]; exact hg
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hh' : h⁻¹ = h := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hh)
  have hcz : g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hm]
    group
  set c := g * h * g⁻¹ * h⁻¹ with hc_def
  have hcen : ∀ y : L, y * c = c * y := fun y => Subgroup.mem_center_iff.mp hcz y
  have hc3 : c ^ 3 = 1 := hZ3 c hcz
  have e1 : g * c * g⁻¹ = c := by rw [hcen g, mul_assoc, mul_inv_cancel, mul_one]
  have e2 : g * c * g⁻¹ = h * g * h * g := by
    have : g * c * g⁻¹ = g * g * (h * g⁻¹ * h⁻¹ * g⁻¹) := by rw [hc_def]; group
    rw [this, hgg, one_mul, hg', hh']
  have e3 : c⁻¹ = h * g * h * g := by
    have : c⁻¹ = h * g * h⁻¹ * g⁻¹ := by rw [hc_def]; group
    rw [this, hg', hh']
  have hcc : c * c = 1 := mul_eq_one_iff_inv_eq.mpr (by rw [e3, ← e2, e1])
  have hc1 : c = 1 := by
    rw [pow_three, hcc, mul_one] at hc3
    exact hc3
  calc g * h = c * (h * g) := by rw [hc_def]; group
    _ = h * g := by rw [hc1, one_mul]

private def kdh_hatT {L : Type} [Group L] (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1)
    (W : Subgroup (L ⧸ Subgroup.center L)) (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) :
    Subgroup L where
  carrier := {g | g ^ 2 = 1 ∧ (g : L ⧸ Subgroup.center L) ∈ W}
  one_mem' := ⟨by rw [one_pow], by rw [QuotientGroup.mk_one]; exact W.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha2, ha⟩ ⟨hb2, hb⟩
    have hab : Commute a b := kdh_comm_of_sq hZ3 ha2 hb2 (hWc _ ha _ hb)
    refine ⟨?_, ?_⟩
    · rw [hab.mul_pow, ha2, hb2, one_mul]
    · rw [QuotientGroup.mk_mul]
      exact W.mul_mem ha hb
  inv_mem' := by
    rintro a ⟨ha2, ha⟩
    refine ⟨?_, ?_⟩
    · rw [inv_pow, ha2, inv_one]
    · rw [QuotientGroup.mk_inv]
      exact W.inv_mem ha

private theorem kdh_conj_mem {L : Type} [Group L] (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1)
    (W : Subgroup (L ⧸ Subgroup.center L)) (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w)
    {x : L} {c : L ⧸ Subgroup.center L} (hxc : (x : L ⧸ Subgroup.center L) = c)
    (hcW : ∀ w ∈ W, c * w * c⁻¹ ∈ W) {g : L} (hg : g ∈ kdh_hatT hZ3 W hWc) :
    x * g * x⁻¹ ∈ kdh_hatT hZ3 W hWc := by
  obtain ⟨hg2, hgW⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [show (x * g * x⁻¹) ^ 2 = x * g ^ 2 * x⁻¹ by rw [sq, sq]; group, hg2, mul_one,
      mul_inv_cancel]
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxc]
    exact hcW _ hgW

private theorem kdh_hat_core {L : Type} [Group L] (hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1)
    (hexp : ∀ x : L, IsPGroup 3 (Subgroup.zpowers x) → x ^ 3 = 1)
    (W : Subgroup (L ⧸ Subgroup.center L)) (hWc : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w)
    (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hWne : W ≠ ⊥) (c : L ⧸ Subgroup.center L) (hc1 : c ≠ 1)
    (hc3 : c ^ 3 = 1) (hcW : ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hcW' : ∀ w ∈ W, c⁻¹ * w * c ∈ W) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set L) := by
  obtain ⟨x, hxc⟩ := QuotientGroup.mk_surjective c
  have hx3c : x ^ 3 ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hxc, hc3]
  have hx9 : x ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hZ3 _ hx3c]
  have hp3 : IsPGroup 3 (Subgroup.zpowers x) := by
    intro g
    refine ⟨2, Subtype.ext ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hn]
    show (x ^ n) ^ 9 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx9, one_zpow]
  have hxpow : x ^ 3 = 1 := hexp x hp3
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hc1 (by rw [← hxc, QuotientGroup.mk_one])
  have hxZ : x ∉ Subgroup.center L := fun h =>
    hc1 (by rw [← hxc]; exact (QuotientGroup.eq_one_iff x).mpr h)
  have hT : kdh_hatT hZ3 W hWc ≠ ⊥ := by
    obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
    have hw1' : (w : L ⧸ Subgroup.center L) ≠ 1 := fun h => hw1 (Subtype.ext h)
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective w
    have hg2 : g₀ ^ 2 ∈ Subgroup.center L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hW2 _ hwW]
    have ht2 : (g₀ ^ 3) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact hZ3 _ hg2
    have h3w : ((g₀ : L) : L ⧸ Subgroup.center L) ^ 3 = (g₀ : L ⧸ Subgroup.center L) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hW2 _ hwW, one_mul]
    have htW : ((g₀ ^ 3 : L) : L ⧸ Subgroup.center L) ∈ W := by
      rw [QuotientGroup.mk_pow, h3w]
      exact hwW
    have htne : g₀ ^ 3 ≠ 1 := by
      intro h
      apply hw1'
      have h' : ((g₀ ^ 3 : L) : L ⧸ Subgroup.center L) = 1 := by
        rw [h, QuotientGroup.mk_one]
      rw [QuotientGroup.mk_pow, h3w] at h'
      exact h'
    intro hbot
    have hmem : g₀ ^ 3 ∈ kdh_hatT hZ3 W hWc := ⟨ht2, htW⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact htne hmem
  refine ⟨x, orderOf_eq_prime hxpow hx1, hxZ, kdh_hatT hZ3 W hWc, hT, ?_, ?_⟩
  · exact kdh_isPGroup_two _ (fun g hg => hg.1)
  · rw [Subgroup.mem_set_normalizer_iff]
    intro g
    simp only [SetLike.mem_coe]
    constructor
    · intro hg
      exact kdh_conj_mem hZ3 W hWc hxc hcW hg
    · intro hg
      have hcW'' : ∀ w ∈ W, c⁻¹ * w * c⁻¹⁻¹ ∈ W := fun w hw => by rw [inv_inv]; exact hcW' w hw
      have h' := kdh_conj_mem hZ3 W hWc (x := x⁻¹) (c := c⁻¹)
        (by rw [QuotientGroup.mk_inv, hxc]) hcW'' hg
      have e : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
      rwa [e] at h'


theorem kd2028_hat' (L : Type) [Group L] [Finite L] (hZ : Nat.card (Subgroup.center L) = 3)
    (s t : L ⧸ Subgroup.center L) (hs : orderOf s = 3) (ht : orderOf t = 2) (hst : s * t = t * s)
    (hexp : ∀ x : L, IsPGroup 3 (Subgroup.zpowers x) → x ^ 3 = 1) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      x ∈ Subgroup.normalizer (T : Set L) := by
  have hZ3 : ∀ z ∈ Subgroup.center L, z ^ 3 = 1 := kdh_exp_center hZ
  have hcomm : Commute s t := hst
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hWc : ∀ w ∈ Subgroup.zpowers t, ∀ w' ∈ Subgroup.zpowers t, w * w' = w' * w := by
    intro w hw w' hw'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
    exact (Commute.zpow_zpow_self t m n).eq
  have hW2 : ∀ w ∈ Subgroup.zpowers t, w ^ 2 = 1 := by
    intro w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hWne : Subgroup.zpowers t ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h
    rw [h, orderOf_one] at ht
    norm_num at ht
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    norm_num at hs
  have hs3 : s ^ 3 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one s
  have hcW : ∀ w ∈ Subgroup.zpowers t, s * w * s⁻¹ ∈ Subgroup.zpowers t := by
    intro w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have e : s * t ^ m * s⁻¹ = t ^ m := by
      rw [(hcomm.zpow_right m).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩
  have hcW' : ∀ w ∈ Subgroup.zpowers t, s⁻¹ * w * s ∈ Subgroup.zpowers t := by
    intro w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have e : s⁻¹ * t ^ m * s = t ^ m := by
      rw [((hcomm.inv_left).zpow_right m).eq, mul_assoc, inv_mul_cancel, mul_one]
    rw [e]
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩
  exact kdh_hat_core hZ3 hexp (Subgroup.zpowers t) hWc hW2 hWne s hs1 hs3 hcW hcW'

private theorem kdh_m22_centralizer
    (s : ↥CFSG.Blueprint.NativeSporadic.M22) (hs : orderOf s = 3) :
    Nat.card ↥(Subgroup.centralizer ({s} : Set ↥CFSG.Blueprint.NativeSporadic.M22)) = 36 := by
  have hx : (s : Equiv.Perm (Fin 22)) ∈ CFSG.Blueprint.NativeSporadic.M22 := s.2
  have hx3 : orderOf (s : Equiv.Perm (Fin 22)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hs
  obtain ⟨c, hc, hcard⟩ := CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_sound
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data
    CFSG.HardMathSupport.Solomon.Coordinator.rep_m22A
    CFSG.HardMathSupport.Solomon.Coordinator.rep_m22B
    Certificates.certificate13511.2.2.1 (s : Equiv.Perm (Fin 22)) hx hx3
  have h36 : ∀ c < CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data.cases.size,
      CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data.cases[c]!.card = 36 := by
    decide +kernel
  have key : Nat.card ↥((Subgroup.centralizer ({s} : Set ↥CFSG.Blueprint.NativeSporadic.M22)).map
      CFSG.Blueprint.NativeSporadic.M22.subtype) =
      Nat.card ↥(Subgroup.centralizer ({s} : Set ↥CFSG.Blueprint.NativeSporadic.M22)) :=
    Subgroup.card_map_of_injective CFSG.Blueprint.NativeSporadic.M22.subtype_injective
  rw [← key, CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype]
  exact hcard.trans (h36 c hc)

private theorem kdh_m22_comm :
    ∃ s t : ↥CFSG.Blueprint.NativeSporadic.M22, orderOf s = 3 ∧ orderOf t = 2 ∧ s * t = t * s := by
  obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have h3 : 3 ∣ Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.HardMathSupport.Solomon.Coordinator.t112m_natCard_m22]
    norm_num
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have h2 : 2 ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set ↥CFSG.Blueprint.NativeSporadic.M22)) := by
    rw [kdh_m22_centralizer s hs]
    norm_num
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨s, (t : ↥CFSG.Blueprint.NativeSporadic.M22), hs, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact ht
  · exact Subgroup.mem_centralizer_iff.mp t.2 s (Set.mem_singleton s)

private theorem kdh_m22_transport {X : Type} [Group X]
    (e : X ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group) :
    ∃ s t : X, orderOf s = 3 ∧ orderOf t = 2 ∧ s * t = t * s := by
  obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  obtain ⟨s, t, hs, ht, hst⟩ := kdh_m22_comm
  refine ⟨(ψ.trans e.symm) s, (ψ.trans e.symm) t, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hs
  · rw [MulEquiv.orderOf_eq]
    exact ht
  · rw [← map_mul, ← map_mul, hst]

private theorem kdh_hatSix {L : Type} [Group L] [Finite L] (h : IsHatSix L) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set L) := by
  have hexp := kdh_hexp_of_sylow (fun R => (CFSG.HardMathSupport.Solomon.Coordinator.t112m_sylow_hatSix h R).2.2)
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  exact kdh_hat_alt hZ (n := 6) (by norm_num) e hexp

private theorem kdh_hatSeven {L : Type} [Group L] [Finite L] (h : IsHatSeven L) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set L) := by
  have hexp := kdh_hexp_of_sylow (fun R => (CFSG.HardMathSupport.Solomon.Coordinator.t112m_sylow_hatSeven h R).2.2)
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  exact kdh_hat_alt hZ (n := 7) (by norm_num) e hexp

private theorem kdh_hatMTwentyTwo {L : Type} [Group L] [Finite L]
    (h : IsHatMTwentyTwo L) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set L) := by
  have hexp := kdh_hexp_of_sylow (fun R => (CFSG.HardMathSupport.Solomon.Coordinator.t112m_sylow_hatM22 h R).2.2)
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  obtain ⟨s, t, hs, ht, hst⟩ := kdh_m22_transport e
  exact kd2028_hat' L hZ s t hs ht hst hexp

private theorem kdh_slThree {L : Type} [Group L] (h : IsSLThreeExc L) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set L) := by
  obtain ⟨K, hK, hfin, h9, ⟨e⟩⟩ := h
  exact kdh_transport e (kd2028_slThree K (by omega))

private theorem kdh_two_pow_mod_nine {i : ℕ} (h : 2 ^ i % 9 = 2 ∨ 2 ^ i % 9 = 5) :
    i % 2 = 1 ∧ i % 3 ≠ 0 := by
  have h6 : 2 ^ i % 9 = 2 ^ (i % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod i 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [h6] at h
  have hcases : i % 6 = 0 ∨ i % 6 = 1 ∨ i % 6 = 2 ∨ i % 6 = 3 ∨ i % 6 = 4 ∨ i % 6 = 5 := by
    omega
  rcases hcases with h0 | h0 | h0 | h0 | h0 | h0 <;> rw [h0] at h <;> (try norm_num at h) <;>
    omega

private theorem kdh_suThree {L : Type} [Group L] (hQ : CFSG.Open.IsQuasisimple L)
    (h : IsSUThreeExc L) (hnot : ¬ IsSUThreeTwoPow L) :
    ∃ x : L, orderOf x = 3 ∧ x ∉ Subgroup.center L ∧ ∃ T : Subgroup L, T ≠ ⊥ ∧
      IsPGroup 2 T ∧ x ∈ Subgroup.normalizer (T : Set L) := by
  obtain ⟨K, hK, hfin, q, hcard, hq9, ⟨e⟩⟩ := h
  have hq3 : q % 3 = 2 := by omega
  by_cases hodd : q % 2 = 1
  · exact kdh_transport e (kd2028_suThree K q hcard hq3 hodd)
  · exfalso
    have hq2 : 2 ∣ q := by omega
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨m, hp, hm⟩ := FiniteField.card K (ringChar K)
    have hKc : q ^ 2 = ringChar K ^ (m : ℕ) := by
      rw [← hcard, Nat.card_eq_fintype_card, hm]
    have h2 : 2 ∣ ringChar K ^ (m : ℕ) := by
      rw [← hKc]
      exact dvd_pow hq2 (by norm_num)
    have hp2 : ringChar K = 2 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm
    rw [hp2] at hKc
    have hdq : q ∣ 2 ^ (m : ℕ) := ⟨q, by rw [← hKc, sq]⟩
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdq
    obtain ⟨hi2, hi3⟩ := kdh_two_pow_mod_nine hq9
    have hi0 : i ≠ 0 := by
      rintro rfl
      norm_num at hodd
    by_cases hi1 : i = 1
    · subst hi1
      have hs : Group.IsSolvable (StatedSU 3 (2 ^ 1) K) :=
        CFSG.Quasithin.isSolvable_statedSU_one hcard
      exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hQ
        (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
    · exact hnot ⟨K, hK, hfin, i, hi2, by omega, hi3, hcard, ⟨e⟩⟩

theorem kd2028_holds : KD2028 := by
  intro L _ _ hQ hcase
  rcases hcase with h | h | h | h | ⟨h, hnot⟩
  · exact kdh_hatSix h
  · exact kdh_hatSeven h
  · exact kdh_hatMTwentyTwo h
  · exact kdh_slThree h
  · exact kdh_suThree hQ h hnot

end CFSG.LocalAnalysis.GLTheoremA
