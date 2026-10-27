module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Lift
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {Y : Type} [Group Y] [Finite Y]

theorem thq_lift {p : ℕ} (hp : p.Prime) {K P : Subgroup Y} [K.Normal] (hP : IsPGroup p P)
    (hK : p.Coprime (Nat.card K)) {x : Y ⧸ K}
    (hx : ∀ g ∈ P, QuotientGroup.mk' K g * x = x * QuotientGroup.mk' K g) :
    ∃ y : Y, QuotientGroup.mk' K y = x ∧ ∀ g ∈ P, g * y = y * g := by
  classical
  let π : Y →* Y ⧸ K := QuotientGroup.mk' K
  let actY : P →* MulAut Y := (MulAut.conj : Y →* MulAut Y).comp P.subtype
  let actQ : P →* MulAut (Y ⧸ K) :=
    (MulAut.conj : (Y ⧸ K) →* MulAut (Y ⧸ K)).comp (π.comp P.subtype)
  let : MulDistribMulAction P Y := multiplicativeActionOfMulAutHom actY
  let : MulDistribMulAction P (Y ⧸ K) := multiplicativeActionOfMulAutHom actQ
  obtain ⟨y, hy, hyfix⟩ := coprime_pGroup_fixed_lift p hp hP π (QuotientGroup.mk'_surjective K)
    (fun a s => by
      change π ((a : Y) * s * (a : Y)⁻¹) = π a * π s * (π a)⁻¹
      simp [map_mul, map_inv])
    (by rw [QuotientGroup.ker_mk']; exact hK) x
    (fun a => by
      change π a * x * (π a)⁻¹ = x
      rw [mul_inv_eq_iff_eq_mul]
      exact hx a a.2)
  refine ⟨y, hy, fun g hg => ?_⟩
  have := hyfix ⟨g, hg⟩
  change g * y * g⁻¹ = y at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem thq_centralizer_map {p : ℕ} (hp : p.Prime) {K P : Subgroup Y} [K.Normal]
    (hP : IsPGroup p P) (hK : p.Coprime (Nat.card K)) :
    centralizer ((P.map (QuotientGroup.mk' K) : Subgroup (Y ⧸ K)) : Set (Y ⧸ K)) =
      (centralizer (P : Set Y)).map (QuotientGroup.mk' K) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyc⟩ := thq_lift hp hP hK (x := x) (fun g hg =>
      (mem_centralizer_iff.mp hx _ ⟨g, hg, rfl⟩))
    exact ⟨y, mem_centralizer_iff.mpr hyc, hy⟩
  · rintro ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hc g hg]

theorem thq_sylow {p : ℕ} (hp : p.Prime) {K D : Subgroup Y} [K.Normal]
    (hK : p.Coprime (Nat.card K))
    (hD : IsPGroup p D) (hsyl : IsSylowOf p D (centralizer (D : Set Y))) :
    IsSylowOf p (D.map (QuotientGroup.mk' K))
      (centralizer ((D.map (QuotientGroup.mk' K) : Subgroup (Y ⧸ K)) : Set (Y ⧸ K))) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [thq_centralizer_map hp hD hK]
  exact isSylowOf_map_hom _ hsyl

omit [Finite Y] in
theorem thq_isPGroup {p : ℕ} {E : Subgroup Y} (hE : IsElemAbelian p E) : IsPGroup p E :=
  CFSG.Open.IsElemAbelian.isPGroup hE

omit [Finite Y] in
theorem thq_mem_normalizer_map {K V : Subgroup Y} [K.Normal] {g : Y}
    (hg : g ∈ normalizer (V : Set Y)) :
    QuotientGroup.mk' K g ∈
      normalizer ((V.map (QuotientGroup.mk' K) : Subgroup (Y ⧸ K)) : Set (Y ⧸ K)) := by
  rw [mem_normalizer_iff]
  intro h
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk'_surjective K h
  have hg' := mem_normalizer_iff.mp hg
  constructor
  · rintro ⟨v, hv, hvh⟩
    refine ⟨g * v * g⁻¹, (hg' v).mp hv, ?_⟩
    simp [map_mul, map_inv, hvh]
  · rintro ⟨v, hv, hvh⟩
    refine ⟨g⁻¹ * v * g, ?_, ?_⟩
    · exact (hg' (g⁻¹ * v * g)).mpr (by simpa [mul_assoc] using hv)
    · have : QuotientGroup.mk' K v = QuotientGroup.mk' K g * QuotientGroup.mk' K h₀ *
          (QuotientGroup.mk' K g)⁻¹ := hvh
      simp only [map_mul, map_inv, this]
      group

omit [Finite Y] in
theorem thq_conj_centralizer {g d y : Y} (hgd : g * d = d * g) (hy : y * d = d * y) :
    g * y * g⁻¹ * d = d * (g * y * g⁻¹) := by
  have h1 : g⁻¹ * d = d * g⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgd]
    group
  calc g * y * g⁻¹ * d = g * y * (g⁻¹ * d) := by group
    _ = g * y * (d * g⁻¹) := by rw [h1]
    _ = g * (y * d) * g⁻¹ := by group
    _ = g * (d * y) * g⁻¹ := by rw [hy]
    _ = (g * d) * y * g⁻¹ := by group
    _ = (d * g) * y * g⁻¹ := by rw [hgd]
    _ = d * (g * y * g⁻¹) := by group

theorem thq_signalizer {p : ℕ} (hp : p.Prime) {K D : Subgroup Y} [K.Normal]
    (hD : IsPGroup p D) (hDab : IsMulCommutative D) (hK : p.Coprime (Nat.card K)) {d : Y}
    (hdD : d ∈ D) {O : Subgroup Y} (hO : IsPSignalizer p D d O) :
    IsPSignalizer p (D.map (QuotientGroup.mk' K)) (QuotientGroup.mk' K d)
      (O.map (QuotientGroup.mk' K)) := by
  classical
  have hz : IsPGroup p (zpowers d) := hD.to_le (zpowers_le.mpr hdD)
  have hlift : ∀ x : Y ⧸ K, x * QuotientGroup.mk' K d = QuotientGroup.mk' K d * x →
      ∃ y : Y, QuotientGroup.mk' K y = x ∧ y * d = d * y := by
    intro x hx
    obtain ⟨y, hy, hyc⟩ := thq_lift hp hz hK (x := x) (fun g hg => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      rw [map_zpow]
      exact (Commute.zpow_left (show Commute (QuotientGroup.mk' K d) x from hx.symm) k))
    exact ⟨y, hy, (hyc d (mem_zpowers d)).symm⟩
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hDab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨o, ho, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (hO.le_centralizer ho)]
  · intro x hx
    obtain ⟨y, rfl, hy⟩ := hlift x (mem_centralizer_singleton_iff.mp hx)
    exact thq_mem_normalizer_map (hO.normal (mem_centralizer_singleton_iff.mpr hy))
  · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd O _) hO.coprime
  · intro W hWC hWc hWN
    have hπs : Function.Surjective (QuotientGroup.mk' K) := QuotientGroup.mk'_surjective K
    set U : Subgroup Y := (W.comap (QuotientGroup.mk' K)) ⊓ centralizer ({d} : Set Y) with hU
    have hUc : p.Coprime (Nat.card U) := by
      have h1 : Nat.card U ∣ Nat.card (W.comap (QuotientGroup.mk' K)) :=
        Subgroup.card_dvd_of_le inf_le_left
      rw [card_comap_eq_card_ker_mul _ hπs W, QuotientGroup.ker_mk'] at h1
      exact Nat.Coprime.coprime_dvd_right h1 (hK.mul_right hWc)
    have key : ∀ g ∈ D, ∀ y : Y, y ∈ U → g * y * g⁻¹ ∈ U := by
      intro g hg y hy
      obtain ⟨hy1, hy2⟩ := hy
      have hgW := mem_normalizer_iff.mp (hWN ⟨g, hg, rfl⟩)
      refine ⟨?_, ?_⟩
      · show QuotientGroup.mk' K (g * y * g⁻¹) ∈ W
        have h1 : QuotientGroup.mk' K y ∈ W := hy1
        have := (hgW _).mp h1
        simpa [map_mul, map_inv] using this
      · show g * y * g⁻¹ ∈ centralizer ({d} : Set Y)
        rw [mem_centralizer_singleton_iff]
        exact thq_conj_centralizer (hcomm g hg d hdD) (mem_centralizer_singleton_iff.mp hy2)
    have hUN : D ≤ normalizer (U : Set Y) := by
      intro g hg
      rw [mem_normalizer_iff]
      intro y
      exact ⟨fun hy => key g hg y hy, fun hy => by
        have := key g⁻¹ (inv_mem hg) _ hy
        simpa [mul_assoc] using this⟩
    have hUO : U ≤ O := hO.le U inf_le_right hUc hUN
    intro w hw
    obtain ⟨y, rfl, hy⟩ := hlift w (mem_centralizer_singleton_iff.mp (hWC hw))
    exact ⟨y, hUO ⟨hw, mem_centralizer_singleton_iff.mpr hy⟩, rfl⟩

omit [Finite Y] in
theorem thq_map_join_le {K D : Subgroup Y} [K.Normal] :
    (invariantTwoJoinIn D (⊤ : Subgroup Y)).map (QuotientGroup.mk' K) ≤
      invariantTwoJoinIn (D.map (QuotientGroup.mk' K)) (⊤ : Subgroup (Y ⧸ K)) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine invariantTwoJoinIn_le_of_forall fun V _ hV2 hDV => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_invariantTwoJoinIn le_top (hV2.map _) ?_
  rintro _ ⟨g, hg, rfl⟩
  exact thq_mem_normalizer_map (hDV hg)

omit [Finite Y] in
theorem thq_join {p : ℕ} (hp : p.Prime) {K D : Subgroup Y} [K.Normal]
    (hK : p.Coprime (Nat.card K))
    (hj : p ∣ Nat.card (invariantTwoJoinIn D (⊤ : Subgroup Y))) :
    p ∣ Nat.card (invariantTwoJoinIn (D.map (QuotientGroup.mk' K)) (⊤ : Subgroup (Y ⧸ K))) := by
  set J := invariantTwoJoinIn D (⊤ : Subgroup Y) with hJ
  have h1 := card_eq_card_map_mul_card_inf_ker (QuotientGroup.mk' K) J
  rw [QuotientGroup.ker_mk'] at h1
  have h2 : ¬ p ∣ Nat.card (J ⊓ K : Subgroup Y) := by
    rw [← hp.coprime_iff_not_dvd]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hK
  rw [h1] at hj
  have h3 : p ∣ Nat.card (J.map (QuotientGroup.mk' K)) := (hp.dvd_mul.mp hj).resolve_right h2
  exact h3.trans (Subgroup.card_dvd_of_le thq_map_join_le)

theorem ThompsonPreFrame.quotient {p : ℕ} {K D : Subgroup Y} [K.Normal]
    (h : ThompsonPreFrame p K D) : ThompsonFrame p (D.map (QuotientGroup.mk' K)) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  set π : Y →* Y ⧸ K := QuotientGroup.mk' K with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hker : π.ker = K := QuotientGroup.ker_mk' K
  have hkerc : p.Coprime (Nat.card π.ker) := by rw [hker]; exact h.coprime
  have hDp : IsPGroup p D := thq_isPGroup h.elem
  have hinfD : D ⊓ π.ker = ⊥ := inf_eq_bot_of_isPGroup_of_coprime h.prime hDp hkerc
  refine
    { prime := h.prime
      odd := h.odd
      elem := ?_
      card := ?_
      pCore_eq_bot := h.pCore_quot
      pPrimeCore_eq_bot := ?_
      rank_le := ?_
      sylow := thq_sylow h.prime h.coprime hDp h.sylow
      signalizer := ?_
      join := thq_join h.prime h.coprime h.join }
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      show (a : Y ⧸ K) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg π (congrArg Subtype.val (h.elem.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, h.elem.2 x hx, map_one]
  · have := card_eq_card_map_mul_card_inf_ker π D
    rw [hinfD, Subgroup.card_bot, mul_one, h.card] at this
    exact this.symm
  · rw [CFSG.pPrimeCore_eq_bot_iff]
    intro N hN hNc
    have hNt : (N.comap π).Normal := hN.comap π
    have hcop : p.Coprime (Nat.card (N.comap π)) := by
      rw [card_comap_eq_card_ker_mul π hπs N]
      exact hkerc.mul_right hNc
    have hle : N.comap π ≤ K := h.max _ hNt hcop
    rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective hπs N]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff x).mpr (hle hx)
  · intro E hE
    obtain ⟨E', hE', hcard⟩ := exists_isElemAbelian_card_eq_of_map h.prime π hπs hkerc hE
    rw [← hcard]
    exact h.rank_le E' hE'
  · intro d' hd' hd'1
    obtain ⟨d, hdD, rfl⟩ := Subgroup.mem_map.mp hd'
    have hd1 : d ≠ 1 := fun e => hd'1 (by rw [e, map_one])
    obtain ⟨O, hO⟩ := h.signalizer d hdD hd1
    exact ⟨O.map π, thq_signalizer h.prime hDp h.elem.1 h.coprime hdD hO⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
