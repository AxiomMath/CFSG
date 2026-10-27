module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TR18
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TKPump
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TYb
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10THNInner
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TFix

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

private theorem exists_involution_inf_center {B : Type*} [Group B] [Finite B]
    (hB : IsPGroup 2 B) {N : Subgroup B} [N.Normal] (hN : N ≠ ⊥) :
    ∃ b ∈ N, b ∈ center B ∧ orderOf b = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent B := hB.isNilpotent
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hN
  rcases (hB.to_subgroup (N ⊓ center B)).card_eq_or_dvd with h | h
  · exact absurd (eq_bot_of_card_eq _ h) hne
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h
    exact ⟨x, (mem_inf.mp x.2).1, (mem_inf.mp x.2).2, by rw [orderOf_coe, hx]⟩

private theorem mul_self_of_mem_zpowers {G : Type*} [Group G] {σ : G} (hσ : σ * σ = 1) :
    ∀ q ∈ zpowers σ, q * q = 1 := by
  intro q hq
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hq
  rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hσ, one_zpow]

private theorem card_zpowers_le_two {G : Type*} [Group G] {σ : G} (hσ : σ * σ = 1) :
    Nat.card (zpowers σ) ≤ 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hσ)

private theorem mem_autFixed_zpowers {L : Type*} [Group L] {σ : MulAut L} {x : L} :
    x ∈ EvenPump.autFixed (zpowers σ) ↔ σ x = x := by
  rw [EvenPump.mem_autFixed]
  refine ⟨fun h => h σ (mem_zpowers σ), fun h q hq => ?_⟩
  have hle : zpowers σ ≤ MulAction.stabilizer (MulAut L) x :=
    zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)
  exact MulAction.mem_stabilizer_iff.mp (hle hq)

private theorem actZ_zpowers {M : Subgroup X} {b : X} (hbN : b ∈ normalizer (M : Set X)) :
    actZ M (zpowers b) = zpowers (zStarAct M ⟨b, hbN⟩) := by
  have h : (zpowers b).subgroupOf (normalizer (M : Set X)) = zpowers ⟨b, hbN⟩ := by
    ext x
    rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
    refine ⟨fun ⟨k, hk⟩ => ⟨k, Subtype.ext ?_⟩, fun ⟨k, hk⟩ => ⟨k, ?_⟩⟩
    · rw [SubgroupClass.coe_zpow]
      exact hk
    · rw [← hk, SubgroupClass.coe_zpow]
  show ((zpowers b).subgroupOf (normalizer (M : Set X))).map (zStarAct M) = _
  rw [h, MonoidHom.map_zpowers]

private theorem conj_injective_of_center_eq_bot {S : Type*} [Group S] (hZ : center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [← hZ, mem_center_iff]
  intro x
  have h := congrArg (fun φ : MulAut S => φ x) (MonoidHom.mem_ker.mp hg)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc x * g = g * x * g⁻¹ * g := by rw [h]
    _ = g * x := by group

private theorem center_quot_fusionZStar_eq_bot {H M : Subgroup X} (hMH : M ≤ H)
    (hM : IsPComponent 2 (M.subgroupOf H)) : center (↥M ⧸ Open.fusionZStar ↥M) = ⊥ := by
  obtain ⟨hs, a, b, hab⟩ := FooteLit.zStarQuotient_simple hM
  let f := Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hMH)
  have : IsSimpleGroup (↥M ⧸ Open.fusionZStar ↥M) := f.symm.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥M ⧸ Open.fusionZStar ↥M)) with h | h
  · exact h
  · refine absurd (f.injective ?_) hab
    rw [map_mul, map_mul]
    exact mem_center_iff.mp (h ▸ mem_top (f b)) (f a)

private theorem factorial_div_two_ne {s : ℕ} (hs : Even s) : s.factorial / 2 ≠ 44352000 := by
  intro h
  rcases Nat.lt_or_ge s 11 with h11 | h11
  · have h1 := Nat.factorial_le (show s ≤ 10 by omega)
    have h2 : Nat.factorial 10 = 3628800 := by decide
    omega
  · have hs12 : 12 ≤ s := by
      obtain ⟨k, hk⟩ := hs
      omega
    have h1 := Nat.factorial_le hs12
    have h2 : Nat.factorial 12 = 479001600 := by decide
    omega

private theorem one_lt_card_secB0 (c : Ctx X) : 1 < Nat.card (c.s.h.secB0 c.s.y) := by
  have hb1 : c.b ≠ 1 := by
    intro h
    have h1 := c.hzb
    rw [h, mul_one] at h1
    apply not_conj_a_z c.Z c.s.S_sylow c.hN c.s.t⁻¹
    rw [inv_inv, ← h1]
    group
  rw [Finite.one_lt_card_iff_nontrivial]
  exact nontrivial_of_ne ⟨c.b, c.hbB⟩ 1 fun h => hb1 (congrArg Subtype.val h)

namespace Ctx.CaseIIIp

variable {c : Ctx X} (e : c.CaseIIIp)

private theorem exists_imgZ_Yb (hcore : EvenPump.EvenAltPumpInput)
    (hHN : EvenPump.HNPumpInput) (hHNfix : HNFixedComponents) {b : X}
    (hbB : b ∈ c.s.h.secB0 c.s.y) (hb : orderOf b = 2)
    (hbZ : ∀ u ∈ c.s.h.secB0 c.s.y, u * b = b * u) :
    ∃ s : ℕ, Even s ∧ 8 ≤ s ∧ (Nat.card (c.s.h.secB0 c.s.y) = 2 → s = 8) ∧
      ∃ T : Subgroup (↥e.K ⧸ Open.fusionZStar ↥e.K),
        T ≤ EvenPump.autFixed (actZ e.K (zpowers b)) ∧
        IsPComponent 2 (T.subgroupOf (EvenPump.autFixed (actZ e.K (zpowers b)))) ∧
        Nat.card (↥T ⧸ Open.fusionZStar ↥T) = s.factorial / 2 := by
  obtain ⟨Y, hYK, hY, -, s, hs, hs8, ⟨eY⟩, -, hs2⟩ := e.exists_Yb hcore hHN hHNfix hbB hb hbZ
  have hbP2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  have hEH : zpowers b ≤ centralizer ({e.w} : Set X) :=
    zpowers_le.mpr (e.secB0_le_centralizer_w hbB)
  have hEN : zpowers b ≤ normalizer (e.K : Set X) := zpowers_le.mpr (e.secB0_le_normalizer_K hbB)
  have hTE : Y ≤ centralizer ((zpowers b : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq]
    exact hYK.trans inf_le_right
  have hT : IsPComponent 2 (Y.subgroupOf
      (centralizer ({e.w} : Set X) ⊓ centralizer ((zpowers b : Subgroup X) : Set X))) := by
    rw [centralizer_zpowers_eq]
    exact hY
  let eZ : ↥Y ⧸ Open.fusionZStar ↥Y ≃* alternatingGroup (Fin s) :=
    (QuotientGroup.quotientMulEquivOfEq (EvenPump.fusionZStar_eq_of_alt (by omega) eY)).trans eY
  have : IsSimpleGroup (alternatingGroup (Fin s)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨hTF, hTpc⟩ := isPComponent_imgZ e.K_le e.isPComponent_K hEH hEN hbP2
    (hYK.trans inf_le_left) hTE hT
  refine ⟨s, hs, hs8, hs2, imgZ e.K Y, hTF, hTpc, ?_⟩
  rw [card_imgZ_eq e.K_le e.isPComponent_K hEH hEN hbP2 (hYK.trans inf_le_left) hTE hT
    eZ.isSimpleGroup, Nat.card_congr eZ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin]

theorem false_of_HN (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    (hHNfix : HNFixedComponents) (hHNinner : HNInnerFixedComponents) (hHNidx : HNOuterIndex)
    (hB01 : c.s.h.secB0 c.s.y ⊓ coreActionKernel e.K = ⊥)
    (hK : Nonempty (↥e.K ⧸ Open.fusionZStar ↥e.K ≃* Blueprint.NativeSporadic.Carrier .HN)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eHN⟩ := hK
  have hB2 : IsPGroup 2 ↥(c.s.h.secB0 c.s.y) := c.s.h.isPGroup_secB0 c.s.y
  have hBN := e.secB0_le_normalizer_K
  set ρ : ↥(c.s.h.secB0 c.s.y) →* MulAut (↥e.K ⧸ Open.fusionZStar ↥e.K) :=
    (zStarAct e.K).comp (inclusion hBN)
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    have h1 : (b : X) ∈ c.s.h.secB0 c.s.y ⊓ coreActionKernel e.K := mem_inf.mpr ⟨b.2,
      (zStarAct_eq_one_iff e.K_le e.isPComponent_K (inclusion hBN b)).mp (MonoidHom.mem_ker.mp hb)⟩
    rw [hB01, mem_bot] at h1
    exact mem_bot.mpr (Subtype.ext h1)
  have hZ : ∀ b : ↥(c.s.h.secB0 c.s.y), b ∈ center _ →
      ∀ u ∈ c.s.h.secB0 c.s.y, u * (b : X) = b * u :=
    fun b hb u hu => congrArg Subtype.val (mem_center_iff.mp hb ⟨u, hu⟩)
  have h1 := one_lt_card_secB0 c
  obtain ⟨n, hn⟩ := hB2.exists_card_eq
  rcases n with _ | _ | n
  · rw [pow_zero] at hn
    omega
  ·
    have : Nontrivial ↥(c.s.h.secB0 c.s.y) := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨b, -, hbZ, hb⟩ := exists_involution_inf_center hB2 (N := ⊤) top_ne_bot
    have hb' : orderOf (b : X) = 2 := (orderOf_coe b).trans hb
    obtain ⟨s, -, -, hs2, T, hTF, hTpc, hTc⟩ := e.exists_imgZ_Yb hcore hHN hHNfix b.2 hb' (hZ b hbZ)
    obtain rfl := hs2 (by rw [hn]; norm_num)
    have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
    have hσ : ρ b * ρ b = 1 := by rw [← map_mul, hbb, map_one]
    rw [actZ_zpowers (hBN b.2)] at hTF hTpc
    rcases hHNfix _ ⟨eHN⟩ _ (mul_self_of_mem_zpowers hσ) (card_zpowers_le_two hσ) T hTF hTpc
      with h | h | h <;> rw [hTc] at h <;> exact absurd h (by decide)
  ·
    have h4 : 4 ≤ Nat.card ↥(c.s.h.secB0 c.s.y) := by
      have : 0 < 2 ^ n := pow_pos (by norm_num) n
      rw [hn, pow_succ, pow_succ]
      omega
    have hS := center_quot_fusionZStar_eq_bot e.K_le e.isPComponent_K
    have : Finite (MulAut (↥e.K ⧸ Open.fusionZStar ↥e.K)) :=
      inferInstanceAs (Finite ((↥e.K ⧸ Open.fusionZStar ↥e.K) ≃* (↥e.K ⧸ Open.fusionZStar ↥e.K)))
    have hInn := GH74.Uniqueness.Bender.normal_range_conj (↥e.K ⧸ Open.fusionZStar ↥e.K)
    set I := ((MulAut.conj : (↥e.K ⧸ Open.fusionZStar ↥e.K) →* MulAut _).range).comap ρ with hI
    have : I.Normal := hInn.comap ρ
    have hIidx : I.index ≤ 2 := by
      refine le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite) ?_)
        (hHNidx _ ⟨eHN⟩)
      rw [hI, index_comap]
      exact relIndex_dvd_index_of_normal _ _
    have hIne : I ≠ ⊥ := by
      intro h
      rw [h, index_bot] at hIidx
      omega
    obtain ⟨b, hbI, hbZ, hb⟩ := exists_involution_inf_center hB2 hIne
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (mem_comap.mp hbI)
    have hb' : orderOf (b : X) = 2 := (orderOf_coe b).trans hb
    have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
    have hconj := conj_injective_of_center_eq_bot hS
    have hu1 : u ≠ 1 := by
      rintro rfl
      have hb1 : b = 1 := hρinj (by rw [← hu, map_one, map_one])
      rw [hb1, orderOf_one] at hb
      exact absurd hb (by norm_num)
    have hu2 : orderOf u = 2 := by
      refine orderOf_eq_prime (hconj ?_) hu1
      rw [pow_two, map_mul, hu, ← map_mul, hbb, map_one, map_one]
    have hF : EvenPump.autFixed (actZ e.K (zpowers (b : X))) = centralizer ({u} : Set _) := by
      rw [actZ_zpowers (hBN b.2)]
      ext x
      rw [mem_autFixed_zpowers, mem_centralizer_singleton_iff]
      change ρ b x = x ↔ _
      rw [← hu, MulAut.conj_apply]
      constructor
      · intro h
        calc x * u = u * x * u⁻¹ * u := by rw [h]
          _ = u * x := by group
      · intro h
        rw [← h, mul_inv_cancel_right]
    obtain ⟨s, hs, -, -, T, hTF, hTpc, hTc⟩ := e.exists_imgZ_Yb hcore hHN hHNfix b.2 hb' (hZ b hbZ)
    rw [hF] at hTF hTpc
    have h2 := hHNinner _ ⟨eHN⟩ u hu2 T hTF hTpc
    rw [hTc] at h2
    exact factorial_div_two_ne hs h2

theorem exists_alt (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    (hA8 : EvenPump.A8PumpInput) (hHNfix : HNFixedComponents)
    (hHNinner : HNInnerFixedComponents) (hHNidx : HNOuterIndex) (hR18 : GS82R18Input) :
    ∃ m : ℕ, 8 ≤ m ∧ Nonempty (↥e.K ⧸ pPrimeCore 2 ↥e.K ≃* alternatingGroup (Fin m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 ↥(c.s.h.secB0 c.s.y) := c.s.h.isPGroup_secB0 c.s.y
  have hBN := e.secB0_le_normalizer_K
  have hBw := e.secB0_le_centralizer_w
  have : Nontrivial ↥(c.s.h.secB0 c.s.y) :=
    Finite.one_lt_card_iff_nontrivial.mp (one_lt_card_secB0 c)
  have hZ : ∀ b : ↥(c.s.h.secB0 c.s.y), b ∈ center _ →
      ∀ u ∈ c.s.h.secB0 c.s.y, u * (b : X) = b * u :=
    fun b hb u hu => congrArg Subtype.val (mem_center_iff.mp hb ⟨u, hu⟩)
  by_cases hB01 : c.s.h.secB0 c.s.y ⊓ coreActionKernel e.K = ⊥
  ·
    obtain ⟨b, -, hbZ, hb⟩ := exists_involution_inf_center hB2 (N := ⊤) top_ne_bot
    have hb' : orderOf (b : X) = 2 := (orderOf_coe b).trans hb
    have hbK : (b : X) ∉ coreActionKernel e.K := fun h => by
      have h1 : (b : X) ∈ c.s.h.secB0 c.s.y ⊓ coreActionKernel e.K := mem_inf.mpr ⟨b.2, h⟩
      rw [hB01, mem_bot] at h1
      rw [h1, orderOf_one] at hb'
      exact absurd hb' (by norm_num)
    obtain ⟨Y, hYK, hY, -, s, hs, hs8, ⟨eY⟩, hY8, -⟩ :=
      e.exists_Yb hcore hHN hHNfix b.2 hb' (hZ b hbZ)
    rcases e.pump hcore hHN hA8 (hBw b.2) hb' (hBN b.2) hbK hYK hY hs hs8 eY with
      ⟨m, -, hm, ⟨eK⟩⟩ | ⟨-, hK⟩ | ⟨rfl, hK⟩
    · exact ⟨m, hm, e.nonempty_pPrimeCore_equiv_of_fusionZStar hm eK⟩
    · exact (e.false_of_HN hcore hHN hHNfix hHNinner hHNidx hB01 hK).elim
    · exact (e.false_of_L44_HS hR18 hB01 b.2 hb' hYK hY (hY8 rfl) hK).elim
  ·
    set ρ : ↥(c.s.h.secB0 c.s.y) →* MulAut (↥e.K ⧸ Open.fusionZStar ↥e.K) :=
      (zStarAct e.K).comp (inclusion hBN)
    have hker : ρ.ker ≠ ⊥ := by
      intro h
      apply hB01
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxB, hxK⟩ := mem_inf.mp hx
      have h1 : (⟨x, hxB⟩ : ↥(c.s.h.secB0 c.s.y)) ∈ ρ.ker := MonoidHom.mem_ker.mpr
        ((zStarAct_eq_one_iff e.K_le e.isPComponent_K (inclusion hBN ⟨x, hxB⟩)).mpr hxK)
      rw [h, mem_bot] at h1
      exact mem_bot.mpr (congrArg Subtype.val h1)
    obtain ⟨b, hbk, hbZ, hb⟩ := exists_involution_inf_center hB2 hker
    have hb' : orderOf (b : X) = 2 := (orderOf_coe b).trans hb
    have hbK : (b : X) ∈ coreActionKernel e.K :=
      (zStarAct_eq_one_iff e.K_le e.isPComponent_K (inclusion hBN b)).mp (MonoidHom.mem_ker.mp hbk)
    obtain ⟨Y, hYK, hY, -, s, -, hs8, ⟨eY⟩, -, -⟩ := e.exists_Yb hcore hHN hHNfix b.2 hb' (hZ b hbZ)
    obtain ⟨eKY⟩ := e.nonempty_equiv_of_mem_kernel hbK hYK hY hb' (hBw b.2)
    exact ⟨s, hs8, ⟨eKY.trans eY⟩⟩

end Ctx.CaseIIIp

namespace Ctx.PropBData

variable {c : Ctx X} (d : c.PropBData)

theorem false_of_case_iii'
    (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    (hA8 : EvenPump.A8PumpInput) (hHNfix : HNFixedComponents)
    (hHNinner : HNInnerFixedComponents) (hHNidx : HNOuterIndex) (hR18 : GS82R18Input)
    (hw : c.φ ⟨d.z', d.z'_mem_secSub⟩ = r0)
    (ha : c.φ ⟨d.a', d.a'_mem_secSub⟩ = sigmaTwo * z0 * r0) : False := by
  obtain ⟨e, -⟩ := d.exists_caseIIIp hw ha
  obtain ⟨m, hm, ⟨eK⟩⟩ := e.exists_alt hcore hHN hA8 hHNfix hHNinner hHNidx hR18
  obtain ⟨j⟩ := e.jstarData (by omega) eK
  exact j.false

end Ctx.PropBData

end CFSG.ComponentClassification.GSThmB.A10T
