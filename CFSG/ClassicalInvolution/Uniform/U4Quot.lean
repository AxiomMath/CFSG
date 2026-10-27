module

public import CFSG.ClassicalInvolution.Uniform.U4Basic
public import CFSG.ClassicalInvolution.AschTight.S1916F1
public import CFSG.ClassicalInvolution.Asc77.AscFusionS4
public import CFSG.ClassicalInvolution.Uniform.USylow

public section

namespace CFSG.ClassicalInvolution.Uniform.U4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
open scoped commutatorElement MatrixGroups

variable {F : Type} [Group F] [Finite F] {K J : Subgroup F} {z t : F}

namespace Mem3

noncomputable def equiv (h : Mem3 K z) : OddQuot K ≃* SL(2, ZMod 3) :=
  (h.member.nonempty_equiv_sl2Three solvableType_three).some

omit [Finite F] in
theorem mk_mem_center (h : Mem3 K z) :
    (QuotientGroup.mk (⟨z, h.mem⟩ : ↥K) : OddQuot K) ∈ Subgroup.center (OddQuot K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (h.mul_comm_of_mem x.2)

theorem mk_ne_one (h : Mem3 K z) : (QuotientGroup.mk (⟨z, h.mem⟩ : ↥K) : OddQuot K) ≠ 1 := by
  intro h1
  rw [QuotientGroup.eq_one_iff] at h1
  exact h.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K)
    (mem_oddCoreOf_iff.mpr ⟨h.mem, h1⟩)
    (isPGroup_zpowers_of_mul_self_eq_one h.mul_self h.ne_one))

theorem mem_center_oddQuot_iff (h : Mem3 K z) (w : OddQuot K) :
    w ∈ Subgroup.center (OddQuot K) ↔
      w = 1 ∨ w = (QuotientGroup.mk (⟨z, h.mem⟩ : ↥K) : OddQuot K) := by
  have hc := h.member.natCard_center_eq_two
  obtain ⟨z', hz'1, hzu⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center (OddQuot K))).mp hc
  have hzz : (⟨_, h.mk_mem_center⟩ : Subgroup.center (OddQuot K)) = z' :=
    hzu _ (fun h1 => h.mk_ne_one (congrArg Subtype.val h1))
  constructor
  · intro hw
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · right
      have h2 := hzu ⟨w, hw⟩ (fun h1 => hw1 (congrArg Subtype.val h1))
      rw [← hzz] at h2
      exact congrArg Subtype.val h2
  · rintro (h1 | h1)
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact h.mk_mem_center

end Mem3

@[expose] def sl23i : SL(2, ZMod 3) := ⟨!![0, -1; 1, 0], by decide⟩

@[expose] def sl23j : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩

theorem sl23_center_gens :
    ∀ g : SL(2, ZMod 3), g * sl23i = sl23i * g → g * sl23j = sl23j * g → g = 1 ∨ g = -1 := by
  decide

theorem sl23_center_cases (g : SL(2, ZMod 3)) (h : ∀ x : SL(2, ZMod 3), g * x = x * g) :
    g = 1 ∨ g = -1 :=
  sl23_center_gens g (h sl23i) (h sl23j)

theorem sl23_sq_one_cases : ∀ x : SL(2, ZMod 3), x * x = 1 → x = 1 ∨ x = -1 := by decide

theorem sl23_conj_sl23i :
    ∀ x : SL(2, ZMod 3), x * x = -1 → ∃ g : SL(2, ZMod 3), g * sl23i * g⁻¹ = x := by decide

namespace Mem3

theorem equiv_mk_z (h : Mem3 K z) :
    h.equiv (QuotientGroup.mk (⟨z, h.mem⟩ : ↥K) : OddQuot K) = -1 := by
  have hc : h.equiv (QuotientGroup.mk (⟨z, h.mem⟩ : ↥K) : OddQuot K) ∈
      Subgroup.center SL(2, ZMod 3) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h1 := Subgroup.mem_center_iff.mp h.mk_mem_center (h.equiv.symm x)
    have := congrArg h.equiv h1
    simpa using this
  have hz := sl23_center_cases _ (fun x => (Subgroup.mem_center_iff.mp hc x).symm)
  rcases hz with h1 | h1
  · exact absurd (h.equiv.injective (h1.trans h.equiv.map_one.symm)) h.mk_ne_one
  · exact h1

theorem oddQuot_eq_one_or_eq (h : Mem3 K z) {w : OddQuot K} (hw : w * w = 1) :
    w = 1 ∨ w = (QuotientGroup.mk (⟨z, h.mem⟩ : ↥K) : OddQuot K) := by
  have h1 : h.equiv w * h.equiv w = 1 := by rw [← map_mul, hw, map_one]
  rcases sl23_sq_one_cases _ h1 with h2 | h2
  · left
    exact h.equiv.injective (h2.trans h.equiv.map_one.symm)
  · right
    exact h.equiv.injective (h2.trans h.equiv_mk_z.symm)

theorem eq_one_or_eq_of_forall_comm (h : Mem3 K z) {a : F} (haK : a ∈ K)
    (ha2 : IsPGroup 2 (Subgroup.zpowers a)) (hc : ∀ u ∈ K, ⁅a, u⁆ ∈ oddCoreOf K) :
    a = 1 ∨ a = z := by
  rcases (h.mem_center_oddQuot_iff _).mp (mk_mem_center_of_forall haK hc) with h1 | h1
  · left
    rw [QuotientGroup.eq_one_iff] at h1
    exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K)
      (mem_oddCoreOf_iff.mpr ⟨haK, h1⟩) ha2
  · right
    rw [QuotientGroup.eq] at h1
    have hza : a * z = z * a := h.mul_comm_of_mem haK
    have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
      isPGroup_zpowers_of_mul_self_eq_one h.mul_self h.ne_one
    have hainv : IsPGroup 2 (Subgroup.zpowers a⁻¹) := by rwa [Subgroup.zpowers_inv]
    have hcomm : Commute a⁻¹ z := (Commute.inv_left (show Commute a z from hza))
    have hmem : a⁻¹ * z ∈ oddCoreOf K :=
      mem_oddCoreOf_iff.mpr ⟨K.mul_mem (K.inv_mem haK) h.mem, h1⟩
    have h2 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hmem
      (isPGroup_zpowers_mul hcomm hainv hz2)
    exact (inv_mul_eq_one.mp h2)

theorem not_forall_comm_of_sq_eq (h : Mem3 K z) {a : F} (haK : a ∈ K) (ha2 : a * a = z) :
    ¬ ∀ u ∈ K, ⁅a, u⁆ ∈ oddCoreOf K := by
  intro hc
  rcases h.eq_one_or_eq_of_forall_comm haK
      (AscFusion.isPGroup_zpowers_of_sq_eq h.mul_self ha2) hc with h1 | h1
  · rw [h1, one_mul] at ha2
    exact h.ne_one ha2.symm
  · rw [h1, h.mul_self] at ha2
    exact h.ne_one ha2.symm

theorem exists_conj_oddQuot (h : Mem3 K z) {x y : OddQuot K}
    (hx : x * x = (QuotientGroup.mk (⟨z, h.mem⟩ : ↥K) : OddQuot K))
    (hy : y * y = (QuotientGroup.mk (⟨z, h.mem⟩ : ↥K) : OddQuot K)) :
    ∃ g : OddQuot K, g * x * g⁻¹ = y := by
  have hx' : h.equiv x * h.equiv x = -1 := by rw [← map_mul, hx, h.equiv_mk_z]
  have hy' : h.equiv y * h.equiv y = -1 := by rw [← map_mul, hy, h.equiv_mk_z]
  obtain ⟨gx, hgx⟩ := sl23_conj_sl23i _ hx'
  obtain ⟨gy, hgy⟩ := sl23_conj_sl23i _ hy'
  refine ⟨h.equiv.symm (gy * gx⁻¹), h.equiv.injective ?_⟩
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [← hgx, ← hgy]
  group

theorem exists_conj_in_member (h : Mem3 K z) {k₁ k₂ : F} (hk₁K : k₁ ∈ K) (hk₂K : k₂ ∈ K)
    (hk₁ : k₁ * k₁ = z) (hk₂ : k₂ * k₂ = z) : ∃ g ∈ K, g * k₁ * g⁻¹ = k₂ := by
  have hsq : ∀ (k : F) (hk : k ∈ K), k * k = z →
      (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : OddQuot K) * QuotientGroup.mk (⟨k, hk⟩ : ↥K) =
        (QuotientGroup.mk (⟨z, h.mem⟩ : ↥K) : OddQuot K) := by
    intro k hk hkk
    rw [← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hkk
  obtain ⟨e, he⟩ := h.exists_conj_oddQuot (hsq k₁ hk₁K hk₁) (hsq k₂ hk₂K hk₂)
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective e
  set x : F := (g₀ : F) * k₁ * (g₀ : F)⁻¹ with hx
  have hxK : x ∈ K := K.mul_mem (K.mul_mem g₀.2 hk₁K) (K.inv_mem g₀.2)
  have hmk : (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : OddQuot K) = QuotientGroup.mk ⟨k₂, hk₂K⟩ := by
    rw [← he, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  rw [QuotientGroup.eq] at hmk
  have hxy : x⁻¹ * k₂ ∈ oddCoreOf K :=
    mem_oddCoreOf_iff.mpr ⟨K.mul_mem (K.inv_mem hxK) hk₂K, hmk⟩
  have hxx : x * x = z := by
    calc x * x = (g₀ : F) * (k₁ * k₁) * (g₀ : F)⁻¹ := by rw [hx]; group
      _ = z := by rw [hk₁, h.mul_comm_of_mem g₀.2]; group
  obtain ⟨h', hh, hhx⟩ := AscFusion.exists_conj_of_odd_coset (oddCoreOf_odd_natCard K)
    (AscFusion.isPGroup_zpowers_of_sq_eq h.mul_self hxx)
    (AscFusion.isPGroup_zpowers_of_sq_eq h.mul_self hk₂)
    (AscFusion.mem_normalizer_oddCoreOf_of_mem_normalizer' (Subgroup.le_normalizer hxK)) hxy
  have hle : oddCoreOf K ⊔ Subgroup.zpowers x ≤ K :=
    sup_le (oddCoreOf_le_self K) (Subgroup.zpowers_le.mpr hxK)
  refine ⟨h' * g₀, K.mul_mem (hle hh) g₀.2, ?_⟩
  calc h' * g₀ * k₁ * (h' * g₀)⁻¹ = h' * x * h'⁻¹ := by rw [hx]; group
    _ = k₂ := hhx

theorem isQuatSub_of_isSylow2In (h : Mem3 K z) {V : Subgroup F} (hV : IsSylow2In V K) :
    IsQuatSub V := by
  set ψ : ↥K →* SL(2, ZMod 3) :=
    h.equiv.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) with hψ
  set S : Subgroup ↥K := V.subgroupOf K with hS
  have hS2 : IsPGroup 2 S := hV.2.1.comap_subtype
  have hinj : Function.Injective (ψ.comp S.subtype) :=
    h.equiv.injective.comp (injective_mk_oddCore_of_isPGroup K hS2)
  have hcardV : Nat.card V = 8 := by
    rw [natCard_isSylow2In_eq hV, Nat.card_congr h.equiv.toEquiv, natCard_sl2Three]
    have : (Nat.factorization 24) 2 = 3 := by decide +kernel
    rw [this]
    norm_num
  have hcardS : Nat.card S = 8 := by
    rw [← hcardV]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV.1).toEquiv
  have hle : S.map ψ ≤ sl2ThreeQ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_sl2ThreeQ_iff]
    obtain ⟨k, hk⟩ := hS2 ⟨x, hx⟩
    exact sl23_pow_four_of_two_pow (k := k) (by
      have := congrArg (fun y : S => ψ (y : ↥K)) hk
      simpa [map_pow] using this)
  have hcardI : Nat.card (S.map ψ) = 8 := by
    have h1 : S.map ψ = (ψ.comp S.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcardS]
  have heq : S.map ψ = sl2ThreeQ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_sl2ThreeQ, hcardI])
  obtain ⟨e₀⟩ := nonempty_mulEquiv_sl2ThreeQ
  have hrange : (ψ.comp S.subtype).range = sl2ThreeQ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact heq
  refine ⟨1, le_rfl, ⟨?_⟩⟩
  exact ((Subgroup.subgroupOfEquivOfLe hV.1).symm.trans
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))).trans e₀.symm

omit [Finite F] in
theorem forall_comm_of_oddQuotAut_eq_one {g : F} (hg : g ∈ Subgroup.normalizer (K : Set F))
    (h : oddQuotAut K (conjOn K g hg) = 1) : ∀ k ∈ K, ⁅g, k⁆ ∈ oddCoreOf K := by
  intro k hk
  have h1 : oddQuotAut K (conjOn K g hg) ((⟨k, hk⟩ : ↥K) : OddQuot K) =
      ((⟨k, hk⟩ : ↥K) : OddQuot K) := by
    rw [h]
    rfl
  rw [oddQuotAut_mk] at h1
  have h2 : conjOn K g hg ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹ ∈ classicalInvolutionOddCore ↥K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
      mul_inv_cancel]
  have hmem : ⁅g, k⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp hg k).mp hk) (K.inv_mem hk)
  refine mem_oddCoreOf_iff.mpr ⟨hmem, ?_⟩
  convert h2 using 1
  apply Subtype.ext
  simp [conjOn_apply, commutatorElement_def]

theorem oddQuotAut_conjOn_eq_one (h : Mem3 K z) {V : Subgroup F} (hV : IsSylow2In V K) {g : F}
    (hg : g ∈ Subgroup.normalizer (K : Set F)) (hc : ∀ q ∈ V, g * q = q * g) :
    oddQuotAut K (conjOn K g hg) = 1 := by
  set e := h.equiv with he
  let α : SL(2, ZMod 3) →* SL(2, ZMod 3) :=
    (e.toMonoidHom.comp (oddQuotAut K (conjOn K g hg)).toMonoidHom).comp e.symm.toMonoidHom
  let P0 : Sylow 2 ↥K := sylowOfIsSylow2In hV
  let P1 : Sylow 2 (OddQuot K) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' (classicalInvolutionOddCore ↥K))
      (QuotientGroup.mk'_surjective _) P0
  let P2 : Sylow 2 SL(2, ZMod 3) := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P1
  have hα : ∀ p : SL(2, ZMod 3), p ^ 4 = 1 → α p = p := by
    intro p hp
    have hp2 : p ∈ P2 := mem_sylow_sl23 P2 hp
    have hp2' : p ∈ (P1 : Subgroup (OddQuot K)).map e.toMonoidHom := by
      rw [← Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective P1]
      exact hp2
    obtain ⟨x, hx, rfl⟩ := hp2'
    have hx' : x ∈ (P0 : Subgroup ↥K).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) := by
      rw [← Sylow.coe_mapSurjective (f := QuotientGroup.mk' (classicalInvolutionOddCore ↥K))
        (QuotientGroup.mk'_surjective _) P0]
      exact hx
    obtain ⟨y, hy, rfl⟩ := hx'
    have hyV : (y : F) ∈ V := hy
    show e (oddQuotAut K (conjOn K g hg) (e.symm (e ((QuotientGroup.mk' _) y)))) =
      e ((QuotientGroup.mk' _) y)
    rw [MulEquiv.symm_apply_apply]
    congr 1
    show oddQuotAut K (conjOn K g hg) (y : OddQuot K) = (y : OddQuot K)
    rw [oddQuotAut_mk]
    congr 1
    apply Subtype.ext
    show g * (y : F) * g⁻¹ = y
    rw [hc y hyV]
    group
  ext x
  have h1 := sl23_hom_eq_of_fixes α hα (e x)
  have h2 : e (oddQuotAut K (conjOn K g hg) x) = e x := by
    have : α (e x) = e (oddQuotAut K (conjOn K g hg) (e.symm (e x))) := rfl
    rw [MulEquiv.symm_apply_apply] at this
    rw [← this]
    exact h1
  exact e.injective h2

theorem forall_comm_of_centralizes (h : Mem3 K z) {V : Subgroup F} (hV : IsSylow2In V K) {g : F}
    (hg : g ∈ Subgroup.normalizer (K : Set F)) (hc : ∀ q ∈ V, g * q = q * g) :
    ∀ k ∈ K, ⁅g, k⁆ ∈ oddCoreOf K :=
  forall_comm_of_oddQuotAut_eq_one hg (h.oddQuotAut_conjOn_eq_one hV hg hc)

theorem mem_of_isSylow2In (h : Mem3 K z) {V : Subgroup F} (hV : IsSylow2In V K) : z ∈ V := by
  have hQcard : 2 ≤ Nat.card V := by
    have := (h.isQuatSub_of_isSylow2In hV).eight_le
    omega
  exact AscL62.mem_of_uniqueInvolution_of_pGroup h.isUniqueInvolution hV.1 hV.2.1 hQcard

theorem pow_four_of_isPGroup (h : Mem3 K z) {x : F} (hxK : x ∈ K)
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) : x ^ 4 = 1 := by
  obtain ⟨n, hn⟩ := hx2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have h1 : h.equiv (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : OddQuot K) ^ 4 = 1 := by
    apply sl23_pow_four_of_two_pow (k := n)
    rw [← map_pow, ← QuotientGroup.mk_pow, ← hn]
    have : (⟨x, hxK⟩ : ↥K) ^ orderOf x = 1 := by
      apply Subtype.ext
      simp
    rw [this]
    simp
  have h2 : (QuotientGroup.mk ((⟨x, hxK⟩ : ↥K) ^ 4) : OddQuot K) = 1 := by
    rw [QuotientGroup.mk_pow]
    exact h.equiv.injective (by rw [map_pow, h1, map_one])
  rw [QuotientGroup.eq_one_iff] at h2
  have h3 : x ^ 4 ∈ oddCoreOf K := mem_oddCoreOf_iff.mpr ⟨K.pow_mem hxK 4, by
    simpa using h2⟩
  exact eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h3
    (hx2.to_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 4)))

theorem exists_inverted (h : Mem3 K z) {R : Subgroup F} {w : F} (hR2 : IsPGroup 2 R)
    (hRK : IsSylow2In (R ⊓ K) K) (hwR : w ∈ R) (hw2 : w * w = 1)
    (hwN : w ∈ Subgroup.normalizer (K : Set F)) (hnt : ¬ ∀ k ∈ K, ⁅w, k⁆ ∈ oddCoreOf K) :
    ∃ κ ∈ R ⊓ K, κ * κ = z ∧ w⁻¹ * κ * w = κ⁻¹ := by
  classical
  have hKz : IsUniqueInvolution K z := h.isUniqueInvolution
  set Qs : Subgroup F := R ⊓ K with hQs
  have hQsK : Qs ≤ K := inf_le_right
  have hQs2 : IsPGroup 2 Qs := hR2.to_le inf_le_left
  have hQuat : IsQuatSub Qs := h.isQuatSub_of_isSylow2In hRK
  obtain ⟨k₁, hk₁, ⟨eQ⟩⟩ := id hQuat
  have hzQ : z ∈ Qs := h.mem_of_isSylow2In hRK
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hconjQ : ∀ x : F, x ∈ Qs → w⁻¹ * x * w ∈ Qs := by
    intro x hx
    refine ⟨R.mul_mem (R.mul_mem (R.inv_mem hwR) hx.1) hwR, ?_⟩
    exact (mem_conj_iff_of_mem_normalizer hwN x).mpr hx.2
  let τ : ↥Qs ≃* ↥Qs :=
    { toFun := fun x => ⟨w⁻¹ * x * w, hconjQ x x.2⟩
      invFun := fun x => ⟨w * x * w⁻¹, by
        have h1 := hconjQ x x.2
        rw [hwi] at h1
        simpa [hwi] using h1⟩
      left_inv := fun x => by
        apply Subtype.ext
        show w * (w⁻¹ * (x : F) * w) * w⁻¹ = x
        group
      right_inv := fun x => by
        apply Subtype.ext
        show w⁻¹ * (w * (x : F) * w⁻¹) * w = x
        group
      map_mul' := fun x y => by
        apply Subtype.ext
        show w⁻¹ * ((x : F) * y) * w = (w⁻¹ * x * w) * (w⁻¹ * y * w)
        group }
  have hτ2 : ∀ x, τ (τ x) = x := by
    intro x
    apply Subtype.ext
    show w⁻¹ * (w⁻¹ * (x : F) * w) * w = x
    rw [hwi]
    calc w * (w * (x : F) * w) * w = (w * w) * x * (w * w) := by group
      _ = x := by rw [hw2]; group
  have hτ1 : ∃ x, τ x ≠ x := by
    by_contra hcon
    push Not at hcon
    apply hnt
    refine h.forall_comm_of_centralizes hRK hwN (fun q hq => ?_)
    have hr1 : w⁻¹ * q * w = q := congrArg Subtype.val (hcon ⟨q, hq⟩)
    calc w * q = w * (w⁻¹ * q * w) := by rw [hr1]
      _ = q * w := by group
  have hgen : ∀ H : Subgroup ↥Qs, (∀ x : ↥Qs, orderOf x = 4 → x ∈ H) → H = ⊤ := by
    intro H hH
    have : NeZero (2 ^ k₁) := ⟨by positivity⟩
    exact AscFusion.quaternion_generated_by_order_four eQ H hH
  have hzu : ∀ x : ↥Qs, x * x = 1 → x = 1 ∨ x = ⟨z, hzQ⟩ := by
    intro x hx
    have hxG : (x : F) * (x : F) = 1 := congrArg Subtype.val hx
    rcases hKz.unique (x : F) (hQsK x.2) hxG with h' | h'
    · exact Or.inl (Subtype.ext h')
    · exact Or.inr (Subtype.ext h')
  have hz2 : (⟨z, hzQ⟩ : ↥Qs) * ⟨z, hzQ⟩ = 1 := Subtype.ext hKz.sq
  obtain ⟨κ', hκ'4, hκ'⟩ := AscFusion.exists_inverted_order_four ⟨z, hzQ⟩ hz2
    (fun x => hQs2 x) hzu hgen τ hτ2 hτ1
  set κ : F := (κ' : F) with hκ
  have hκK : κ ∈ K := hQsK κ'.2
  have hκ4 : orderOf κ = 4 := by rw [hκ, Subgroup.orderOf_coe]; exact hκ'4
  refine ⟨κ, κ'.2, ?_, ?_⟩
  · have h1 : (κ * κ) * (κ * κ) = 1 := by
      have : κ ^ 4 = 1 := by rw [← hκ4]; exact pow_orderOf_eq_one κ
      calc (κ * κ) * (κ * κ) = κ ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := this
    rcases hKz.unique (κ * κ) (K.mul_mem hκK hκK) h1 with h' | h'
    · exfalso
      have : orderOf κ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h')
      rw [hκ4] at this
      omega
    · exact h'
  · have := congrArg Subtype.val hκ'
    simpa [τ, hκ] using this

end Mem3

end CFSG.ClassicalInvolution.Uniform.U4
