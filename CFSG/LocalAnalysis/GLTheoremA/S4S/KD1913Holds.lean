module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M22
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinM12
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Mathieu
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCard

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator


@[expose]
def kdPermTransport {α γ : Type} (e : α ≃ γ) : Equiv.Perm α →* Equiv.Perm γ where
  toFun σ := e.permCongr σ
  map_one' := by ext x; simp
  map_mul' σ τ := by ext x; simp

@[simp]
theorem kdPermTransport_apply {α γ : Type} (e : α ≃ γ) (σ : Equiv.Perm α) :
    kdPermTransport e σ = e.permCongr σ :=
  rfl

@[expose]
def kdCyc3 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

theorem kd_fin4_odd_pow_ne_one :
    ∀ t : Equiv.Perm (Fin 4), Equiv.Perm.sign t = -1 →
      (t⁻¹ * (kdCyc3 * t * kdCyc3⁻¹)) ^ 4 ≠ 1 := by
  decide +kernel

theorem perm_centralizes_alt_eq_one {β : Type} [Fintype β] [DecidableEq β]
    (hβ : 4 ≤ Fintype.card β)
    (q : Equiv.Perm β) (hq : ∀ g ∈ alternatingGroup β, g * q = q * g) : q = 1 := by
  by_contra hq1
  obtain ⟨x, hx⟩ : ∃ x, q x ≠ x := by
    by_contra h
    push Not at h
    exact hq1 (Equiv.ext h)
  obtain ⟨y, hyx, hyw⟩ : ∃ y : β, y ≠ x ∧ y ≠ q x := by
    have hc : ({x, q x} : Finset β).card < (Finset.univ : Finset β).card := by
      rw [Finset.card_univ]
      have h2 : ({x, q x} : Finset β).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    exact ⟨y, hy.1, hy.2⟩
  obtain ⟨z, hzx, hzy, hzw⟩ : ∃ z : β, z ≠ x ∧ z ≠ y ∧ z ≠ q x := by
    have hc : ({x, y, q x} : Finset β).card < (Finset.univ : Finset β).card := by
      rw [Finset.card_univ]
      have h3 : ({x, y, q x} : Finset β).card ≤ 3 := Finset.card_le_three
      omega
    obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    exact ⟨z, hz.1, hz.2.1, hz.2.2⟩
  have hsign : Equiv.Perm.sign (Equiv.swap x y * Equiv.swap y z) = 1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hyx.symm, Equiv.Perm.sign_swap hzy.symm]
    exact Int.units_mul_self _
  have hcA : Equiv.swap x y * Equiv.swap y z ∈ alternatingGroup β :=
    Equiv.Perm.mem_alternatingGroup.mpr hsign
  have hcomm := hq _ hcA
  have key : (Equiv.swap x y * Equiv.swap y z) (q x)
      = q ((Equiv.swap x y * Equiv.swap y z) x) := by
    have h := congrArg (fun σ : Equiv.Perm β => σ x) hcomm
    simpa only [Equiv.Perm.mul_apply] using h
  have hcx : (Equiv.swap x y * Equiv.swap y z) x = y := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hyx.symm hzx.symm,
      Equiv.swap_apply_left]
  have hcw : (Equiv.swap x y * Equiv.swap y z) (q x) = q x := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hyw.symm hzw.symm,
      Equiv.swap_apply_of_ne_of_ne hx hyw.symm]
  rw [hcw, hcx] at key
  exact hyx (q.injective key.symm)

theorem s4_no_eight {β : Type} [Fintype β] [DecidableEq β] (hβ : Fintype.card β = 4)
    (Q : Subgroup (Equiv.Perm β)) (hQ : Nat.card Q = 8)
    (hn : ∀ g ∈ alternatingGroup β, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) : False := by
  have hnat : Nat.card β = 4 := by rw [Nat.card_eq_fintype_card, hβ]
  haveI : Nontrivial β := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hA : Nat.card (alternatingGroup β) = 12 := by
    have h1 := two_mul_nat_card_alternatingGroup (α := β)
    have h2 : Nat.card (Equiv.Perm β) = 24 := by
      rw [Nat.card_perm, hnat]
      rfl
    omega
  obtain ⟨t, htQ, htA⟩ : ∃ t ∈ Q, t ∉ alternatingGroup β := by
    by_contra h
    push Not at h
    have hle : Q ≤ alternatingGroup β := fun u hu => h u hu
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hQ, hA] at hdvd
    norm_num at hdvd
  have hsignt : Equiv.Perm.sign t = -1 := by
    rw [Equiv.Perm.mem_alternatingGroup] at htA
    rcases Int.units_eq_one_or (Equiv.Perm.sign t) with h | h
    · exact absurd h htA
    · exact h
  obtain ⟨e⟩ : Nonempty (β ≃ Fin 4) := ⟨Fintype.equivFinOfCardEq hβ⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : Equiv.Perm β, c0 = e.symm.permCongr kdCyc3 := ⟨_, rfl⟩
  have hsigncyc : Equiv.Perm.sign kdCyc3 = 1 := by
    unfold kdCyc3
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1),
      Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2)]
    exact Int.units_mul_self _
  have hc0A : c0 ∈ alternatingGroup β := by
    rw [Equiv.Perm.mem_alternatingGroup, hc0, Equiv.Perm.sign_permCongr]
    exact hsigncyc
  have hc0s : Equiv.Perm.sign c0 = 1 := Equiv.Perm.mem_alternatingGroup.mp hc0A
  have hφc0 : kdPermTransport e c0 = kdCyc3 := by
    rw [kdPermTransport_apply, hc0]
    ext x
    simp
  obtain ⟨d, hd⟩ : ∃ d : Equiv.Perm β, d = t⁻¹ * (c0 * t * c0⁻¹) := ⟨_, rfl⟩
  have hdQ : d ∈ Q := by
    rw [hd]
    exact Q.mul_mem (Q.inv_mem htQ) (hn c0 hc0A t htQ)
  have hdA : d ∈ alternatingGroup β := by
    rw [Equiv.Perm.mem_alternatingGroup, hd]
    simp [map_mul, map_inv, hc0s]
  have hd8 : d ^ 8 = 1 := by
    have h : (⟨d, hdQ⟩ : Q) ^ Nat.card Q = 1 := pow_card_eq_one'
    rw [hQ] at h
    simpa using congrArg Subtype.val h
  have hd12 : d ^ 12 = 1 := by
    have h : (⟨d, hdA⟩ : alternatingGroup β) ^ Nat.card (alternatingGroup β) = 1 :=
      pow_card_eq_one'
    rw [hA] at h
    simpa using congrArg Subtype.val h
  have hd4 : d ^ 4 = 1 := by
    have h : d ^ Nat.gcd 8 12 = 1 := pow_gcd_eq_one.mpr ⟨hd8, hd12⟩
    have hg : Nat.gcd 8 12 = 4 := by norm_num
    rwa [hg] at h
  have hφd : kdPermTransport e d
      = (kdPermTransport e t)⁻¹ * (kdCyc3 * kdPermTransport e t * kdCyc3⁻¹) := by
    simp only [hd, map_mul, map_inv, hφc0]
  have hsφt : Equiv.Perm.sign (kdPermTransport e t) = -1 := by
    rw [kdPermTransport_apply, Equiv.Perm.sign_permCongr]
    exact hsignt
  have h4 := congrArg (kdPermTransport e) hd4
  rw [map_pow, map_one, hφd] at h4
  exact kd_fin4_odd_pow_ne_one _ hsφt h4

theorem seven_norm_card_eq_one {β : Type} [Fintype β] [DecidableEq β]
    (hβ : Fintype.card β = 7)
    (Q : Subgroup (Equiv.Perm β)) (h3 : Nat.Coprime 3 (Nat.card Q))
    (hn : ∀ g ∈ alternatingGroup β, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) : Nat.card Q = 1 := by
  have hnat : Nat.card β = 7 := by rw [Nat.card_eq_fintype_card, hβ]
  haveI : Nontrivial β := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hA : Nat.card (alternatingGroup β) = 2520 := by
    have h1 := two_mul_nat_card_alternatingGroup (α := β)
    have h2 : Nat.card (Equiv.Perm β) = 5040 := by
      rw [Nat.card_perm, hnat]
      rfl
    omega
  have hsimple : IsSimpleGroup (alternatingGroup β) :=
    alternatingGroup.isSimpleGroup (by omega)
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup (alternatingGroup β),
      K = Q.subgroupOf (alternatingGroup β) := ⟨_, rfl⟩
  haveI hKn : K.Normal := by
    refine ⟨fun n hnK g => ?_⟩
    rw [hKdef, Subgroup.mem_subgroupOf] at hnK ⊢
    have h := hn (g : Equiv.Perm β) g.2 (n : Equiv.Perm β) hnK
    simpa using h
  rcases hsimple.eq_bot_or_eq_top_of_normal K with hK | hK
  ·
    have hQbot : Q = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro q hq
      have hcomm : ∀ g ∈ alternatingGroup β, g * q = q * g := by
        intro g hg
        have hk : g * q * g⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hn g hg q hq) (Q.inv_mem hq)
        have hkA : g * q * g⁻¹ * q⁻¹ ∈ alternatingGroup β := by
          rw [Equiv.Perm.mem_alternatingGroup] at hg ⊢
          simp [map_mul, map_inv, hg]
        have hk1 : (⟨g * q * g⁻¹ * q⁻¹, hkA⟩ : alternatingGroup β) ∈ K := by
          rw [hKdef, Subgroup.mem_subgroupOf]
          exact hk
        rw [hK, Subgroup.mem_bot] at hk1
        have h1 : g * q * g⁻¹ * q⁻¹ = 1 := congrArg Subtype.val hk1
        rw [mul_inv_eq_one] at h1
        exact mul_inv_eq_iff_eq_mul.mp h1
      exact perm_centralizes_alt_eq_one (by omega) q hcomm
    rw [hQbot, Subgroup.card_bot]
  ·
    exfalso
    have hAQ : alternatingGroup β ≤ Q := by
      intro g hg
      have hgK : (⟨g, hg⟩ : alternatingGroup β) ∈ K := by
        rw [hK]
        exact Subgroup.mem_top _
      rw [hKdef, Subgroup.mem_subgroupOf] at hgK
      exact hgK
    have hdvd := Subgroup.card_dvd_of_le hAQ
    rw [hA] at hdvd
    have h3dvd : 3 ∣ Nat.card Q := dvd_trans (by norm_num) hdvd
    have hg : Nat.gcd 3 (Nat.card Q) = 1 := h3
    rw [Nat.gcd_eq_left h3dvd] at hg
    omega


@[expose] def isM22 : TauCeti.CFSGIndex → Prop
  | .sporadic s => s = .M22
  | _ => False

private theorem kd1913NonemptyM12 {S : Type} [Group S] (h : catalogIs S isM12) :
    Nonempty (S ≃* ↥CFSG.Blueprint.NativeSporadic.M12) := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | cyclic p hp => exact (hi : False).elim
  | alternating n hn => exact (hi : False).elim
  | lie j => exact (hi : False).elim
  | sporadic s =>
    have hs : s = TauCeti.SporadicName.M12 := hi
    subst hs
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
    exact ⟨f.trans b.symm⟩

private theorem kd1913NonemptyM22 {S : Type} [Group S] (h : catalogIs S isM22) :
    Nonempty (S ≃* ↥CFSG.Blueprint.NativeSporadic.M22) := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | cyclic p hp => exact (hi : False).elim
  | alternating n hn => exact (hi : False).elim
  | lie j => exact (hi : False).elim
  | sporadic s =>
    have hs : s = TauCeti.SporadicName.M22 := hi
    subst hs
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    exact ⟨f.trans b.symm⟩

private theorem kd1913M12Centralizer
    (t : ↥CFSG.Blueprint.NativeSporadic.M12)
    (ht : orderOf t = 3) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M12)) = 36 ∨
      Nat.card ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M12)) = 54 := by
  have ho : orderOf (t : Equiv.Perm (Fin 12)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact ht
  obtain ⟨r, hr, hcard⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinM12.card_centralizerIn Nat.prime_three
      (by norm_num) t.2 ho
  have hc := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinM22.card_centralizer_subtype
    CFSG.Blueprint.NativeSporadic.M12 t
  have h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M12)) := by
    have hmem : t ∈ Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M12) :=
      Subgroup.mem_centralizer_singleton_iff.2 rfl
    have hd := orderOf_dvd_natCard
      (⟨t, hmem⟩ : ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M12)))
    rw [Subgroup.orderOf_mk, ht] at hd
    exact hd
  rw [hc.trans hcard] at h3 ⊢
  rcases CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinM12.rows_ord r hr with h | h | h | h <;>
    rw [h] at h3 ⊢ <;> omega

private theorem kd1913M22Centralizer
    (t : ↥CFSG.Blueprint.NativeSporadic.M22) (ht : orderOf t = 3) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M22)) = 36 := by
  have hx : (t : Equiv.Perm (Fin 22)) ∈ CFSG.Blueprint.NativeSporadic.M22 := t.2
  have hx3 : orderOf (t : Equiv.Perm (Fin 22)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact ht
  obtain ⟨c, hc, hcard⟩ := CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_sound
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data
    CFSG.HardMathSupport.Solomon.Coordinator.rep_m22A
    CFSG.HardMathSupport.Solomon.Coordinator.rep_m22B
    Certificates.certificate13511.2.2.1 (t : Equiv.Perm (Fin 22)) hx hx3
  have h36 : ∀ c < CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data.cases.size,
      CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data.cases[c]!.card = 36 := by
    decide +kernel
  have key : Nat.card ↥((Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M22)).map
      CFSG.Blueprint.NativeSporadic.M22.subtype) =
      Nat.card ↥(Subgroup.centralizer ({t} : Set ↥CFSG.Blueprint.NativeSporadic.M22)) :=
    Subgroup.card_map_of_injective CFSG.Blueprint.NativeSporadic.M22.subtype_injective
  rw [← key, CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype]
  exact hcard.trans (h36 c hc)

private theorem kd1913ConjInjective {S M : Type} [Group S] [Group M] [IsSimpleGroup M]
    (e : S ≃* M) (hM : ∃ u : M, Nat.card ↥(Subgroup.centralizer ({u} : Set M)) < Nat.card M) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  have hcen : Subgroup.center M = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h | h
    · exact h
    · exfalso
      obtain ⟨u, hu⟩ := hM
      have hu' : u ∈ Subgroup.center M := by
        rw [h]
        exact Subgroup.mem_top u
      have hc : Subgroup.centralizer ({u} : Set M) = ⊤ := by
        rw [eq_top_iff]
        intro y _
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_center_iff.1 hu' y
      rw [hc, Subgroup.card_top] at hu
      exact lt_irrefl _ hu
  rw [injective_iff_map_eq_one]
  intro g hg
  have hconj : ∀ h : S, g * h * g⁻¹ = h := by
    intro h
    have h1 := congrArg (fun φ : MulAut S => φ h) hg
    simpa [MulAut.conj_apply] using h1
  have hz : e g ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro m
    have h2 : g * e.symm m = e.symm m * g := mul_inv_eq_iff_eq_mul.1 (hconj (e.symm m))
    have h3 := congrArg e h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    exact h3.symm
  rw [hcen, Subgroup.mem_bot] at hz
  exact e.injective (hz.trans (map_one e).symm)

private theorem kd1913CardTransfer {S M : Type} [Group S] [Group M] (e : S ≃* M) (s : S) :
    Nat.card ↥(Subgroup.centralizer ({s} : Set S)) =
      Nat.card ↥(Subgroup.centralizer ({e s} : Set M)) := by
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv e s]
  exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm

private theorem kd1913InnBound {S M : Type} [Group S] [Finite S] [Group M] [IsSimpleGroup M]
    (e : S ≃* M) (hM : ∃ u : M, Nat.card ↥(Subgroup.centralizer ({u} : Set M)) < Nat.card M)
    (hcent : ∀ s : S, orderOf s = 3 →
      Nat.card ↥(Subgroup.centralizer ({s} : Set S)) = 36 ∨
        Nat.card ↥(Subgroup.centralizer ({s} : Set S)) = 54)
    (x : MulAut S) (hx : x ∈ innerAut S) (hord : orderOf x = 3) :
    Nat.card (GLAPPrimeCoreOf 3 (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))) ≤ 4 := by
  have hinj := kd1913ConjInjective e hM
  have : Finite (MulAut S) := MulEquiv.finite_left
  obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 (show x ∈ (MulAut.conj : S →* MulAut S).range from hx)
  have hs3 : orderOf s = 3 :=
    (orderOf_injective (MulAut.conj : S →* MulAut S) hinj s).symm.trans hord
  have hid : innerAut S ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S)) =
      (Subgroup.centralizer ({s} : Set S)).map (MulAut.conj : S →* MulAut S) := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hy, hc⟩
      obtain ⟨t, rfl⟩ :=
        MonoidHom.mem_range.1 (show y ∈ (MulAut.conj : S →* MulAut S).range from hy)
      refine ⟨t, ?_, rfl⟩
      apply hinj
      rw [map_mul, map_mul]
      exact hc
    · rintro ⟨t, ht, rfl⟩
      refine ⟨MonoidHom.mem_range.2 ⟨t, rfl⟩, ?_⟩
      rw [← map_mul, ← map_mul, ht]
  have hcard : Nat.card ↥(innerAut S ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S))) =
      Nat.card ↥(Subgroup.centralizer ({s} : Set S)) := by
    rw [hid]
    exact Subgroup.card_map_of_injective hinj
  have hX : Nat.card ↥(innerAut S ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S))) = 36 ∨
      Nat.card ↥(innerAut S ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S))) = 54 := by
    rw [hcard]
    exact hcent s hs3
  have hle : GLAPPrimeCoreOf 3 (innerAut S ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S)))
      ≤ innerAut S ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S)) :=
    Subgroup.map_subtype_le
      (GLAPPrimeCore 3 ↥(innerAut S ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S))))
  have hdvd := Subgroup.card_dvd_of_le hle
  have hnd := not_dvd_card_glaPPrimeCoreOf Nat.prime_three
    (innerAut S ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S)))
  generalize Nat.card ↥(GLAPPrimeCoreOf 3
    (innerAut S ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut S)))) = n at hdvd hnd ⊢
  rcases hX with h | h
  · rw [h] at hdvd
    have hle36 : n ≤ 36 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n <;> omega
  · rw [h] at hdvd
    have hle54 : n ≤ 54 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n <;> omega

private theorem kd1913InnBoundM12
    {S : Type} [Group S] [Finite S]
    (e : S ≃* ↥CFSG.Blueprint.NativeSporadic.M12) (x : MulAut S) (hx : x ∈ innerAut S)
    (hord : orderOf x = 3) :
    Nat.card (GLAPPrimeCoreOf 3 (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))) ≤ 4 := by
  obtain ⟨hfin, -, hsimp⟩ := CFSG.Sporadic.Mathieu.fam_m12_simplicity
  haveI := hfin
  haveI : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M12 := hsimp
  have hM : ∃ u : ↥CFSG.Blueprint.NativeSporadic.M12,
      Nat.card ↥(Subgroup.centralizer ({u} : Set ↥CFSG.Blueprint.NativeSporadic.M12)) <
        Nat.card ↥CFSG.Blueprint.NativeSporadic.M12 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hdvd : 3 ∣ Nat.card ↥CFSG.Blueprint.NativeSporadic.M12 := by
      rw [CFSG.Sporadic.Schreier.m12_card]
      norm_num
    obtain ⟨u, hu⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥CFSG.Blueprint.NativeSporadic.M12) 3 hdvd
    refine ⟨u, ?_⟩
    have hcu := kd1913M12Centralizer u hu
    rw [CFSG.Sporadic.Schreier.m12_card]
    omega
  refine kd1913InnBound e hM ?_ x hx hord
  intro s hs
  rw [kd1913CardTransfer e s]
  exact kd1913M12Centralizer (e s) ((orderOf_injective e.toMonoidHom e.injective s).trans hs)

private theorem kd1913InnBoundM22
    {S : Type} [Group S] [Finite S]
    (e : S ≃* ↥CFSG.Blueprint.NativeSporadic.M22) (x : MulAut S) (hx : x ∈ innerAut S)
    (hord : orderOf x = 3) :
    Nat.card (GLAPPrimeCoreOf 3 (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))) ≤ 4 := by
  obtain ⟨hfin, -, hsimp⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  haveI := hfin
  haveI : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M22 := hsimp
  have hM : ∃ u : ↥CFSG.Blueprint.NativeSporadic.M22,
      Nat.card ↥(Subgroup.centralizer ({u} : Set ↥CFSG.Blueprint.NativeSporadic.M22)) <
        Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hdvd : 3 ∣ Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 := by
      rw [CFSG.Sporadic.Schreier.m22_card]
      norm_num
    obtain ⟨u, hu⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥CFSG.Blueprint.NativeSporadic.M22) 3 hdvd
    refine ⟨u, ?_⟩
    have hcu := kd1913M22Centralizer u hu
    rw [CFSG.Sporadic.Schreier.m22_card]
    omega
  refine kd1913InnBound e hM ?_ x hx hord
  intro s hs
  rw [kd1913CardTransfer e s]
  exact Or.inl
    (kd1913M22Centralizer (e s) ((orderOf_injective e.toMonoidHom e.injective s).trans hs))

theorem mathieu_inn_bound {S : Type} [Group S] [Finite S]
    (hS : catalogIs S isM12 ∨ catalogIs S isM22) (x : MulAut S) (hx : x ∈ innerAut S)
    (hord : orderOf x = 3) :
    Nat.card (GLAPPrimeCoreOf 3 (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))) ≤ 4 := by
  rcases hS with h12 | h22
  · obtain ⟨e⟩ := kd1913NonemptyM12 h12
    exact kd1913InnBoundM12 e x hx hord
  · obtain ⟨e⟩ := kd1913NonemptyM22 h22
    exact kd1913InnBoundM22 e x hx hord


section CycleFacts

variable {α : Type} [Fintype α] [DecidableEq α]

theorem apply_zpow_comm {f a : Equiv.Perm α} (ha : Commute a f) (i : ℤ) (x : α) :
    a ((f ^ i) x) = (f ^ i) (a x) := by
  have h := congrArg (fun g : Equiv.Perm α => g x) ((ha.zpow_right i).eq)
  simpa [Equiv.Perm.mul_apply] using h

theorem sameCycle_conj_iff {f a : Equiv.Perm α} (ha : Commute a f) (x y : α) :
    f.SameCycle (a x) (a y) ↔ f.SameCycle x y := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have h1 := apply_zpow_comm ha i x
    exact a.injective (h1.trans hi)
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← apply_zpow_comm ha i x, hi]⟩

theorem cycleOf_conj_apply {f a : Equiv.Perm α} (ha : Commute a f) (x y : α) :
    a (f.cycleOf x y) = f.cycleOf (a x) (a y) := by
  have hc : ∀ z, a (f z) = f (a z) := fun z => by
    have h := congrArg (fun g : Equiv.Perm α => g z) ha.eq
    simpa [Equiv.Perm.mul_apply] using h
  rw [Equiv.Perm.cycleOf_apply, Equiv.Perm.cycleOf_apply]
  by_cases h : f.SameCycle x y
  · have h' : f.SameCycle (a x) (a y) := (sameCycle_conj_iff ha x y).2 h
    rw [if_pos h, if_pos h']
    exact hc y
  · have h' : ¬ f.SameCycle (a x) (a y) := fun h'' => h ((sameCycle_conj_iff ha x y).1 h'')
    rw [if_neg h, if_neg h']

theorem cycleOf_conj_of_commute {f a : Equiv.Perm α} (ha : Commute a f) (x : α) :
    a * f.cycleOf x * a⁻¹ = f.cycleOf (a x) := by
  ext y
  have h := cycleOf_conj_apply ha x (a⁻¹ y)
  have hay : a (a⁻¹ y) = y := by simp
  rw [hay] at h
  simpa [Equiv.Perm.mul_apply] using h

theorem commute_self_cycleOf (f : Equiv.Perm α) (x : α) : Commute f (f.cycleOf x) := by
  have h := cycleOf_conj_of_commute (Commute.refl f) x
  have hs : f.SameCycle x (f x) := ⟨1, by simp⟩
  have hx : f.cycleOf (f x) = f.cycleOf x := hs.cycleOf_eq.symm
  rw [hx] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem commute_cycleOf_cycleOf (f : Equiv.Perm α) (x y : α) :
    Commute (f.cycleOf x) (f.cycleOf y) := by
  by_cases hx : f x = x
  · rw [(Equiv.Perm.cycleOf_eq_one_iff f).2 hx]
    exact Commute.one_left _
  by_cases hy : f y = y
  · rw [(Equiv.Perm.cycleOf_eq_one_iff f).2 hy]
    exact Commute.one_right _
  have hmx : f.cycleOf x ∈ (f.cycleFactorsFinset : Set (Equiv.Perm α)) :=
    Finset.mem_coe.2 (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.2 (Equiv.Perm.mem_support.2 hx))
  have hmy : f.cycleOf y ∈ (f.cycleFactorsFinset : Set (Equiv.Perm α)) :=
    Finset.mem_coe.2 (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.2 (Equiv.Perm.mem_support.2 hy))
  by_cases hxy : f.cycleOf x = f.cycleOf y
  · rw [hxy]
  · exact Equiv.Perm.cycleFactorsFinset_mem_commute f hmx hmy hxy

theorem pow_three_cycleOf {f : Equiv.Perm α} (hf : f ^ 3 = 1) (x : α) :
    (f.cycleOf x) ^ 3 = 1 := by
  have h1 : orderOf f ∣ 3 := orderOf_dvd_of_pow_eq_one hf
  have h2 : orderOf (f.cycleOf x) ∣ 3 := (Equiv.Perm.orderOf_cycleOf_dvd_orderOf f x).trans h1
  exact orderOf_dvd_iff_pow_eq_one.1 h2

theorem cycleOf_mem_alternating {f : Equiv.Perm α} (hf : f ^ 3 = 1) (x : α) :
    f.cycleOf x ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h := congrArg Equiv.Perm.sign (pow_three_cycleOf hf x)
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign (f.cycleOf x)) with h1 | h1
  · exact h1
  · rw [h1] at h
    norm_num at h

theorem zpow_apply_eq_iff {σ : Equiv.Perm α} (hσ : σ ^ 3 = 1) {x : α} (hx : σ x ≠ x) (t : ℤ) :
    (σ ^ t) x = x ↔ (3 : ℤ) ∣ t := by
  have hσ' : σ ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hσ
  have hsplit : σ ^ t = σ ^ (t % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod t 3, zpow_add, zpow_mul, hσ', one_zpow, one_mul]
  rw [hsplit]
  have hr : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  have hdvd : (3 : ℤ) ∣ t ↔ t % 3 = 0 := by omega
  rw [hdvd]
  have h3 : σ * (σ * σ) = 1 := by
    rw [← pow_three]
    exact hσ
  rcases hr with h | h | h
  · rw [h, zpow_zero]
    simp
  · rw [h, zpow_one]
    simp [hx]
  · rw [h]
    constructor
    · intro hfix
      exfalso
      rw [zpow_two] at hfix
      have h2 : σ (σ x) = x := by simpa [Equiv.Perm.mul_apply] using hfix
      have h4 : σ (σ (σ x)) = x := by
        have := congrArg (fun g : Equiv.Perm α => g x) h3
        simpa [Equiv.Perm.mul_apply] using this
      rw [h2] at h4
      exact hx h4
    · intro h'
      norm_num at h'

end CycleFacts

section Core

variable {α : Type} [Fintype α] [DecidableEq α]

theorem three_free_aux {O : Subgroup (Equiv.Perm α)} (hcop : Nat.Coprime 3 (Nat.card O))
    (hord : ∀ g ∈ O, orderOf g ∣ Nat.card O) (g : Equiv.Perm α) (hg : g ∈ O)
    (h3 : g ^ 3 = 1) : g = 1 := by
  have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hc : Nat.Coprime 3 (orderOf g) := Nat.Coprime.coprime_dvd_right (hord g hg) hcop
  have h1 : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd hc.symm hd
  exact orderOf_eq_one_iff.1 h1

theorem core_fix_eq_one {H₀ : Subgroup (Equiv.Perm α)} (hA : alternatingGroup α ≤ H₀)
    {σ : Equiv.Perm α} (hσ : σ ^ 3 = 1) {a : Equiv.Perm α}
    (ha : a ∈ GLAPPrimeCoreOf 3 (H₀ ⊓ Subgroup.centralizer ({σ} : Set (Equiv.Perm α))))
    (hfix : ∀ x, σ x = x → a x = x) : a = 1 := by
  set X := H₀ ⊓ Subgroup.centralizer ({σ} : Set (Equiv.Perm α)) with hXdef
  set O := GLAPPrimeCoreOf 3 X with hOdef
  have hOX : O ≤ X := by
    intro g hg
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hg
    exact y.2
  have hnorm : ∀ g ∈ X, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 X hg) o).1 ho
  have hcop : Nat.Coprime 3 (Nat.card O) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_three X)
  have hord_dvd : ∀ g ∈ O, orderOf g ∣ Nat.card O := by
    intro g hg
    have h1 : orderOf g = orderOf (⟨g, hg⟩ : O) := Subgroup.orderOf_coe ⟨g, hg⟩
    rw [h1]
    exact orderOf_dvd_natCard _
  have hXcent : ∀ g ∈ X, g * σ = σ * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2
  have hOcent : ∀ g ∈ O, Commute g σ := fun g hg => hXcent g (hOX hg)
  ext x
  rw [Equiv.Perm.one_apply]
  by_cases hσx : σ x = x
  · exact hfix x hσx
  set c := σ.cycleOf x with hc
  have hcX : c ∈ X := by
    refine Subgroup.mem_inf.2 ⟨hA (cycleOf_mem_alternating hσ x), ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (commute_self_cycleOf σ x).symm.eq
  have haC : Commute a σ := hOcent a ha
  have hacomm : a * c * a⁻¹ = σ.cycleOf (a x) := cycleOf_conj_of_commute haC x
  have hd : a * (c * a⁻¹ * c⁻¹) ∈ O :=
    O.mul_mem ha (hnorm c hcX a⁻¹ (O.inv_mem ha))
  have hdeq : a * (c * a⁻¹ * c⁻¹) = σ.cycleOf (a x) * c⁻¹ := by
    rw [← hacomm]
    group
  have hcube : (a * (c * a⁻¹ * c⁻¹)) ^ 3 = 1 := by
    have hc3 : c ^ 3 = 1 := pow_three_cycleOf hσ x
    have hc'3 : (σ.cycleOf (a x)) ^ 3 = 1 := pow_three_cycleOf hσ (a x)
    have hcm : Commute (σ.cycleOf (a x)) c⁻¹ :=
      (commute_cycleOf_cycleOf σ (a x) x).inv_right
    rw [hdeq, hcm.mul_pow, hc'3, inv_pow, hc3, inv_one, one_mul]
  have hd1 : a * (c * a⁻¹ * c⁻¹) = 1 :=
    three_free_aux hcop hord_dvd _ hd hcube
  have hac : a * c = c * a := by
    have h2 : a * c * a⁻¹ * c⁻¹ = 1 := by
      rw [← hd1]
      group
    calc a * c = (a * c * a⁻¹ * c⁻¹) * c * a := by group
      _ = c * a := by rw [h2]; group
  have hsc : σ.SameCycle x (a x) := by
    by_contra hns
    have h1 : c (a x) = a x := Equiv.Perm.cycleOf_apply_of_not_sameCycle hns
    have h2 : c (a x) = a (σ x) := by
      have h := congrArg (fun g : Equiv.Perm α => g x) hac
      simp only [Equiv.Perm.mul_apply] at h
      have hcx : c x = σ x := Equiv.Perm.cycleOf_apply_self σ x
      rw [hcx] at h
      exact h.symm
    rw [h1] at h2
    exact hσx (a.injective h2.symm)
  obtain ⟨j, hj⟩ := hsc
  have hpow : ∀ m : ℕ, (a ^ m) x = (σ ^ ((m : ℤ) * j)) x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hexp : ((m + 1 : ℕ) : ℤ) * j = (m : ℤ) * j + j := by push_cast; ring
      rw [pow_succ', Equiv.Perm.mul_apply, ih, apply_zpow_comm haC, ← hj,
        ← Equiv.Perm.mul_apply, ← zpow_add, hexp]
  have hMj : (σ ^ ((orderOf a : ℤ) * j)) x = x := by
    rw [← hpow (orderOf a), pow_orderOf_eq_one, Equiv.Perm.one_apply]
  have h3dvd : (3 : ℤ) ∣ (orderOf a : ℤ) * j := (zpow_apply_eq_iff hσ hσx _).1 hMj
  have hMcop : Nat.Coprime 3 (orderOf a) := Nat.Coprime.coprime_dvd_right (hord_dvd a ha) hcop
  have hnd : ¬ (3 : ℤ) ∣ (orderOf a : ℤ) := by
    intro h
    have h' : 3 ∣ orderOf a := by exact_mod_cast h
    have := Nat.Coprime.eq_one_of_dvd hMcop h'
    norm_num at this
  have hj3 : (3 : ℤ) ∣ j := by
    rcases Int.prime_three.dvd_or_dvd h3dvd with h | h
    · exact absurd h hnd
    · exact h
  have hjx : (σ ^ j) x = x := (zpow_apply_eq_iff hσ hσx j).2 hj3
  exact hj.symm.trans hjx

end Core

section Restrict

variable {α : Type} [Fintype α] [DecidableEq α]

theorem fix_iff_of_commute {σ g : Equiv.Perm α} (hg : Commute g σ) (x : α) :
    σ (g x) = g x ↔ σ x = x := by
  have h : g (σ x) = σ (g x) := by
    have := congrArg (fun k : Equiv.Perm α => k x) hg.eq
    simpa [Equiv.Perm.mul_apply] using this
  constructor
  · intro hx
    apply g.injective
    rw [h, hx]
  · intro hx
    rw [← h, hx]

def restrictFix (σ : Equiv.Perm α) (X : Subgroup (Equiv.Perm α)) (hX : ∀ g ∈ X, Commute g σ) :
    X →* Equiv.Perm {x : α // σ x = x} where
  toFun g := Equiv.Perm.subtypePerm (g : Equiv.Perm α) (fun x => fix_iff_of_commute (hX g g.2) x)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem restrictFix_eq_one_iff {σ : Equiv.Perm α} {X : Subgroup (Equiv.Perm α)}
    (hX : ∀ g ∈ X, Commute g σ) (g : X) :
    restrictFix σ X hX g = 1 ↔ ∀ x, σ x = x → (g : Equiv.Perm α) x = x := by
  constructor
  · intro h x hx
    have := congrArg (fun q : Equiv.Perm {x : α // σ x = x} => ((q ⟨x, hx⟩ : {x : α // σ x = x}) : α)) h
    exact this
  · intro h
    ext ⟨y, hy⟩
    exact h y hy

theorem ofSubtype_commute_fix (σ : Equiv.Perm α) (π : Equiv.Perm {x : α // σ x = x}) :
    Commute (Equiv.Perm.ofSubtype π) σ := by
  show Equiv.Perm.ofSubtype π * σ = σ * Equiv.Perm.ofSubtype π
  ext x
  simp only [Equiv.Perm.mul_apply]
  by_cases hx : σ x = x
  · rw [hx, Equiv.Perm.ofSubtype_apply_of_mem π hx]
    exact ((π ⟨x, hx⟩).2).symm
  · have hx' : ¬ σ (σ x) = σ x := fun h => hx (σ.injective h)
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem π hx', Equiv.Perm.ofSubtype_apply_of_not_mem π hx]

theorem ofSubtype_alt_mem {σ : Equiv.Perm α} {π : Equiv.Perm {x : α // σ x = x}}
    (hπ : π ∈ alternatingGroup {x : α // σ x = x}) :
    Equiv.Perm.ofSubtype π ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup] at hπ ⊢
  rw [Equiv.Perm.sign_ofSubtype]
  exact hπ

end Restrict

section CoreCard

variable {α : Type} [Fintype α] [DecidableEq α]

theorem core_card_le_four {H₀ : Subgroup (Equiv.Perm α)} (hA : alternatingGroup α ≤ H₀)
    {σ : Equiv.Perm α} (hσ : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hcard : Fintype.card α = 7 ∨ Fintype.card α = 10) :
    Nat.card (GLAPPrimeCoreOf 3 (H₀ ⊓ Subgroup.centralizer ({σ} : Set (Equiv.Perm α)))) ≤ 4 := by
  set X := H₀ ⊓ Subgroup.centralizer ({σ} : Set (Equiv.Perm α)) with hXdef
  set O := GLAPPrimeCoreOf 3 X with hOdef
  have hX : ∀ g ∈ X, Commute g σ := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2
  have hOX : O ≤ X := by
    intro g hg
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hg
    exact y.2
  have hOnorm : ∀ g ∈ X, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 X hg) o).1 ho
  have hcop : Nat.Coprime 3 (Nat.card O) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_three X)
  set N : Subgroup X := O.subgroupOf X with hNdef
  set rho := restrictFix σ X hX with hrhodef
  have hinj : Function.Injective (rho.comp N.subtype) := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have hfix := (restrictFix_eq_one_iff hX (N.subtype n)).1 hn
    have hmem : ((N.subtype n : X) : Equiv.Perm α) ∈ O := Subgroup.mem_subgroupOf.1 n.2
    have hone := core_fix_eq_one hA hσ (a := ((N.subtype n : X) : Equiv.Perm α)) hmem hfix
    apply Subtype.ext
    apply Subtype.ext
    exact hone
  set Q := (rho.comp N.subtype).range with hQdef
  have hQcard : Nat.card Q = Nat.card O := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOX).toEquiv
  have hQnorm : ∀ π ∈ alternatingGroup {x : α // σ x = x}, ∀ q ∈ Q, π * q * π⁻¹ ∈ Q := by
    intro π hπ q hq
    obtain ⟨n, rfl⟩ := MonoidHom.mem_range.1 hq
    let g : X := ⟨Equiv.Perm.ofSubtype π, Subgroup.mem_inf.2
      ⟨hA (ofSubtype_alt_mem hπ), Subgroup.mem_centralizer_singleton_iff.2
        (ofSubtype_commute_fix σ π).eq⟩⟩
    have hgπ : rho g = π := by
      ext ⟨y, hy⟩
      exact Equiv.Perm.ofSubtype_apply_of_mem π hy
    have hnN : g * (N.subtype n) * g⁻¹ ∈ N := by
      refine Subgroup.mem_subgroupOf.2 ?_
      have := hOnorm (g : Equiv.Perm α) g.2 ((N.subtype n : X) : Equiv.Perm α)
        (Subgroup.mem_subgroupOf.1 n.2)
      simpa using this
    refine MonoidHom.mem_range.2 ⟨⟨g * (N.subtype n) * g⁻¹, hnN⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv, hgπ]
  have h3Q : Nat.Coprime 3 (Nat.card Q) := by
    rw [hQcard]
    exact hcop
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod : Fintype.card α % 3 = Fintype.card {x : α // σ x = x} % 3 := by
    have hσ' : σ ^ 3 ^ 1 = 1 := by rw [pow_one]; exact hσ
    have h := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) hσ'
    have hc : Fintype.card {x : α // σ x = x} = σ.supportᶜ.card := by
      rw [Fintype.card_subtype]
      congr 1
      ext x
      simp
    rw [hc]
    exact h.symm
  obtain ⟨x0, hx0⟩ : ∃ x0, σ x0 ≠ x0 := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (Equiv.ext fun x => hcon x)
  have hlt : Fintype.card {x : α // σ x = x} < Fintype.card α :=
    Fintype.card_subtype_lt (p := fun x => σ x = x) hx0
  have hf : Fintype.card {x : α // σ x = x} = 1 ∨ Fintype.card {x : α // σ x = x} = 4 ∨
      Fintype.card {x : α // σ x = x} = 7 := by
    rcases hcard with h | h <;> rw [h] at hmod hlt <;> omega
  have hdvd : Nat.card Q ∣ Nat.factorial (Fintype.card {x : α // σ x = x}) := by
    have h1 := Subgroup.card_subgroup_dvd_card Q
    have h2 : Nat.card (Equiv.Perm {x : α // σ x = x}) = Nat.factorial (Fintype.card {x : α // σ x = x}) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rw [h2] at h1
    exact h1
  rw [← hQcard]
  rcases hf with h1 | h4 | h7
  · rw [h1, Nat.factorial_one] at hdvd
    have : Nat.card Q = 1 := Nat.dvd_one.1 hdvd
    omega
  · rw [h4] at hdvd
    have h24 : Nat.factorial 4 = 24 := by decide
    rw [h24] at hdvd
    have h8 : Nat.card Q ∣ 8 := by
      have : Nat.card Q ∣ 8 * 3 := by norm_num; exact hdvd
      exact Nat.Coprime.dvd_of_dvd_mul_right h3Q.symm this
    by_contra hgt
    push Not at hgt
    have hle : Nat.card Q ≤ 8 := Nat.le_of_dvd (by norm_num) h8
    have heq : Nat.card Q = 8 := by
      obtain ⟨m, hm⟩ : ∃ m, Nat.card Q = m := ⟨_, rfl⟩
      rw [hm] at hgt hle h8 ⊢
      interval_cases m <;> simp_all <;> norm_num at h8
    exact s4_no_eight h4 Q heq hQnorm
  · exact le_of_eq_of_le (seven_norm_card_eq_one h7 Q h3Q hQnorm) (by norm_num)

end CoreCard

section Transfer

open CFSG.HardMathSupport.Solomon.LocalBalance

theorem gla_map_primeCoreOf {G G' : Type*} [Group G] [Group G'] (p : ℕ)
    (f : G →* G') (hf : Function.Injective f) (X : Subgroup G) :
    GLAPPrimeCoreOf p (X.map f) = (GLAPPrimeCoreOf p X).map f := by
  have h1 : GLAPPrimeCore p ↥(X.map f) =
      (GLAPPrimeCore p ↥X).map (Subgroup.equivMapOfInjective X f hf).toMonoidHom :=
    (CFSG.pPrimeCore_map_iso p (Subgroup.equivMapOfInjective X f hf)).symm
  have h2 : (X.map f).subtype.comp (Subgroup.equivMapOfInjective X f hf).toMonoidHom =
      f.comp X.subtype := by
    ext x
    rfl
  unfold GLAPPrimeCoreOf
  rw [h1, Subgroup.map_map, h2, Subgroup.map_map]

theorem map_centralizer_singleton_equiv {G H : Type*} [Group G] [Group H] (θ : G ≃* H) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map θ.toMonoidHom =
      Subgroup.centralizer ({θ x} : Set H) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.1 hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, ← map_mul, hz']
  · intro hy
    have hy' : y * θ x = θ x * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    refine ⟨θ.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply θ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hy'

theorem alt_transfer {S : Type} [Group S] [Finite S] {n : ℕ} (hn : n = 7 ∨ n = 10)
    (e : S ≃* alternatingGroup (Fin n)) (H : Subgroup (MulAut S)) (hH : innerAut S ≤ H)
    (x : MulAut S) (hx : x ∈ H) (hord : orderOf x = 3) :
    Nat.card (GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))) ≤ 4 := by
  have hn5 : 5 ≤ n := by omega
  have hn6 : n ≠ 6 := by omega
  have hbij : Function.Bijective
      (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  let ψ : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective _ hbij
  let Φ : MulAut S ≃* MulAut (alternatingGroup (Fin n)) := MulAut.congr e
  let θ : MulAut S ≃* Equiv.Perm (Fin n) := Φ.trans ψ.symm
  have hA : alternatingGroup (Fin n) ≤ H.map θ.toMonoidHom := by
    intro a ha
    have hconj : MulAut.conj (e.symm ⟨a, ha⟩) ∈ H :=
      hH (MonoidHom.mem_range.2 ⟨e.symm ⟨a, ha⟩, rfl⟩)
    refine Subgroup.mem_map.2 ⟨MulAut.conj (e.symm ⟨a, ha⟩), hconj, ?_⟩
    show ψ.symm (Φ (MulAut.conj (e.symm ⟨a, ha⟩))) = a
    have h1 : Φ (MulAut.conj (e.symm ⟨a, ha⟩)) = ψ a := by
      ext c
      simp [Φ, ψ, MulAut.congr_apply, MulAut.conj_apply]
    rw [h1, MulEquiv.symm_apply_apply]
  have hxH₀ : θ x ∈ H.map θ.toMonoidHom := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  have hord₀ : orderOf (θ x) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact hord
  have hσ : (θ x) ^ 3 = 1 := by
    rw [← hord₀]
    exact pow_orderOf_eq_one _
  have hσ1 : θ x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord₀
    norm_num at hord₀
  have hcentr : (H.map θ.toMonoidHom) ⊓ Subgroup.centralizer ({θ x} : Set (Equiv.Perm (Fin n))) =
      (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))).map θ.toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ θ.toMonoidHom θ.injective, map_centralizer_singleton_equiv]
  have hcard : Nat.card (GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))) =
      Nat.card (GLAPPrimeCoreOf 3 ((H.map θ.toMonoidHom) ⊓
        Subgroup.centralizer ({θ x} : Set (Equiv.Perm (Fin n))))) := by
    rw [hcentr, gla_map_primeCoreOf 3 θ.toMonoidHom θ.injective, Subgroup.card_map_of_injective θ.injective]
  rw [hcard]
  exact core_card_le_four hA hσ hσ1 (by rcases hn with h | h <;> simp [h])

end Transfer



@[expose] def KD1913MathieuAut : Prop :=
  ∀ (S : Type) [Group S] [Finite S], (catalogIs S isM12 ∨ catalogIs S isM22) →
    ∀ H : Subgroup (MulAut S), innerAut S < H → ∀ x ∈ H, orderOf x = 3 →
      Nat.card (GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))) ≤ 4

section Main

open CFSG.HardMathSupport.Solomon.LocalBalance


theorem kd1913_of (h : KD1913MathieuAut) :
    KD1913 := by
  intro S _ _ hcat H hH x hx hord
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact alt_transfer hi e H hH x hx hord
  | lie j => exact hi.elim
  | sporadic s =>
    have hMathieu : catalogIs S isM12 ∨ catalogIs S isM22 := by
      rcases hi with hs | hs
      · exact Or.inl ⟨TauCeti.CFSGIndex.sporadic s, hs, ⟨e⟩⟩
      · exact Or.inr ⟨TauCeti.CFSGIndex.sporadic s, hs, ⟨e⟩⟩
    by_cases hlt : innerAut S < H
    · exact h S hMathieu H hlt x hx hord
    · have heq : innerAut S = H := by
        by_contra hne
        exact hlt (lt_of_le_of_ne hH hne)
      subst heq
      exact mathieu_inn_bound hMathieu x hx hord

end Main


end CFSG.LocalAnalysis.GLTheoremA
