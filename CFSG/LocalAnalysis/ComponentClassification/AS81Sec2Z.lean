module

public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.GH74.KGroups.Cover
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

namespace Sec2

section General

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers {z x : G} (hz : orderOf z = 2) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have hk : z ^ k = z ^ (k % 2) := by
    have := (zpow_mod_orderOf z k).symm
    rwa [hz, Nat.cast_ofNat] at this
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zpow_zero]
  · right
    rw [hk, h, zpow_one]

theorem conj_eq_of_mem_normalizer_zpowers {z n : G} (hz : orderOf z = 2)
    (hn : n ∈ normalizer ((zpowers z : Subgroup G) : Set G)) : n * z * n⁻¹ = z := by
  rcases eq_one_or_eq_of_mem_zpowers hz ((mem_normalizer_iff.mp hn z).mp (mem_zpowers z)) with
    h | h
  · exfalso
    have hz1 : z = 1 := by
      have := congrArg (fun w => n⁻¹ * w * n) h
      simpa [mul_assoc] using this
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · exact h

theorem mem_normalizer_centerIn {H : Subgroup G} {n : G} (hn : n ∈ normalizer (H : Set G)) :
    n ∈ normalizer (centerIn H : Set G) := by
  have hconj : ∀ {m x : G}, m ∈ normalizer (H : Set G) → x ∈ centerIn H →
      m * x * m⁻¹ ∈ centerIn H := by
    intro m x hm hx
    refine ⟨(mem_normalizer_iff.mp hm x).mp hx.1, mem_centralizer_iff.mpr fun h hh => ?_⟩
    have hh' : m⁻¹ * h * m ∈ H := by
      have := (mem_normalizer_iff.mp (inv_mem hm) h).mp hh
      simpa using this
    have := mem_centralizer_iff.mp hx.2 _ hh'
    calc h * (m * x * m⁻¹) = m * ((m⁻¹ * h * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * h * m)) * m⁻¹ := by rw [this]
      _ = m * x * m⁻¹ * h := by group
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hconj hn, fun hx => ?_⟩
  have h := hconj (inv_mem hn) hx
  have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
  rwa [e] at h

theorem mem_normalizer_sup {H K : Subgroup G} {n : G} (hH : n ∈ normalizer (H : Set G))
    (hK : n ∈ normalizer (K : Set G)) : n ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem normalizer_le_normalizer_centralizer (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (centralizer (H : Set G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  have key : ∀ {m : G}, m ∈ normalizer (H : Set G) → ∀ c ∈ centralizer (H : Set G),
      m * c * m⁻¹ ∈ centralizer (H : Set G) := by
    intro m hm c hc
    refine mem_centralizer_iff.mpr fun h hh => ?_
    have hh' : m⁻¹ * h * m ∈ H := by
      have := (mem_normalizer_iff.mp (inv_mem hm) h).mp hh
      simpa using this
    have := mem_centralizer_iff.mp hc _ hh'
    calc h * (m * c * m⁻¹) = m * ((m⁻¹ * h * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * h * m)) * m⁻¹ := by rw [this]
      _ = m * c * m⁻¹ * h := by group
  intro c
  refine ⟨key hn c, fun hc => ?_⟩
  have h := key (inv_mem hn) _ hc
  have e : n⁻¹ * (n * c * n⁻¹) * n⁻¹⁻¹ = c := by group
  rwa [e] at h

variable [Finite G]

theorem inf_centerIn_ne_bot {T Q : Subgroup G} (hT : IsPGroup 2 T) (hQT : Q ≤ T)
    (hTQ : T ≤ normalizer (Q : Set G)) (hQ : Q ≠ ⊥) : Q ⊓ centerIn T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hn : (Q.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hQT).mpr hTQ
  have hne : Q.subgroupOf T ≠ ⊥ := by
    intro h
    apply hQ
    rw [eq_bot_iff]
    intro q hq
    have : (⟨q, hQT hq⟩ : T) ∈ Q.subgroupOf T := hq
    rw [h, mem_bot] at this
    exact congrArg Subtype.val this
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  intro hbot
  apply h
  rw [eq_bot_iff]
  rintro t ⟨htQ, htc⟩
  have hmem : (t : G) ∈ Q ⊓ centerIn T :=
    ⟨htQ, t.2, mem_centralizer_iff.mpr fun x hx => congrArg Subtype.val
      (mem_center_iff.mp htc ⟨x, hx⟩)⟩
  rw [hbot, mem_bot] at hmem
  exact Subtype.ext hmem

omit [Finite G] in
theorem mem_of_mem_sup_of_odd {Q O : Subgroup G} (hQ : IsPGroup 2 Q) (hO : Odd (Nat.card O))
    (hOQ : O ≤ centralizer (Q : Set G)) {w : G} (hw : w ∈ Q ⊔ O) (k : ℕ)
    (hk : w ^ 2 ^ k = 1) : w ∈ Q := by
  have hle : Q ≤ normalizer (O : Set G) := fun q hq => by
    rw [mem_normalizer_iff]
    intro o
    have hc : ∀ o' ∈ O, q * o' * q⁻¹ = o' := fun o' ho' => by
      rw [mem_centralizer_iff.mp (hOQ ho') q hq, mul_inv_cancel_right]
    constructor
    · intro ho
      rw [hc o ho]
      exact ho
    · intro ho
      have := hc _ ho
      have h' : o = q * o * q⁻¹ := by
        have h2 := hc (q * o * q⁻¹) ho
        calc o = q⁻¹ * (q * o * q⁻¹) * q := by group
          _ = q⁻¹ * (q * (q * o * q⁻¹) * q⁻¹) * q := by rw [h2]
          _ = q * o * q⁻¹ := by group
      rw [h']
      exact ho
  have hset : ((Q ⊔ O : Subgroup G) : Set G) = (Q : Set G) * (O : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Q O hle ▸ rfl
  have hw' : w ∈ (Q : Set G) * (O : Set G) := by
    rw [← hset]
    exact hw
  obtain ⟨q, hq, o, ho, rfl⟩ := hw'
  have hqo : q * o = o * q := mem_centralizer_iff.mp (hOQ ho) q hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hQ ⟨q, hq⟩
  have hj' : q ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hn : (q * o) ^ 2 ^ (k + j) = 1 := by
    rw [pow_add, pow_mul, hk, one_pow]
  have hcomm : Commute q o := hqo
  rw [hcomm.mul_pow] at hn
  have hq' : q ^ 2 ^ (k + j) = 1 := by
    rw [pow_add, mul_comm, pow_mul, hj', one_pow]
  rw [hq', one_mul] at hn
  have ho1 : o = 1 := by
    have h1 : orderOf o ∣ 2 ^ (k + j) := orderOf_dvd_of_pow_eq_one hn
    have h2 : orderOf o ∣ Nat.card O := by
      have := Subgroup.orderOf_dvd_natCard O ho
      exact this
    have h3 : Nat.Coprime (2 ^ (k + j)) (Nat.card O) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        hO.not_two_dvd_nat)
    have h4 : orderOf o ∣ Nat.gcd (2 ^ (k + j)) (Nat.card O) := Nat.dvd_gcd h1 h2
    rw [h3] at h4
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  simp only [ho1, mul_one]
  exact hq

omit [Finite G] in
theorem isElemAbelian_map {U : Subgroup G} (hU : IsElemAbelian 2 U) (f : G →* G) :
    IsElemAbelian 2 (U.map f) := CFSG.SectionRank.isElemAbelian_map hU _

omit [Finite G] in
theorem centerIn_eq_map (H : Subgroup G) : centerIn H = (center H).map H.subtype := by
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.mpr fun h => Subtype.ext (mem_centralizer_iff.mp hxc h h.2),
      rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hh ⟨y, hy⟩)⟩

omit [Finite G] in
theorem mem_normalizer_oUpperTwo {X : Subgroup G} {n : G} (hn : n ∈ X) :
    n ∈ normalizer (oUpperTwo X : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, oUpperTwo, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨w, ⟨hwX, hw⟩, rfl⟩
    refine ⟨X.mul_mem (X.mul_mem hn hwX) (X.inv_mem hn), ?_⟩
    have h := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective w
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    change Odd (orderOf (n * w * n⁻¹))
    rwa [h]
  · rintro ⟨hxX, hx⟩
    refine ⟨n⁻¹ * x * n, ⟨by simpa [mul_assoc] using X.mul_mem (X.mul_mem (X.inv_mem hn) hxX) hn,
      ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    have : orderOf (n⁻¹ * x * n) = orderOf x := by
      have h := orderOf_injective (MulAut.conj n⁻¹).toMonoidHom (MulAut.conj n⁻¹).injective x
      simpa [MulAut.conj_apply] using h
    rwa [this]

omit [Finite G] in
theorem mem_normalizer_inf {H K : Subgroup G} {n : G} (hH : n ∈ normalizer (H : Set G))
    (hK : n ∈ normalizer (K : Set G)) : n ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hH hK ⊢
  intro x
  exact ⟨fun hx => ⟨(hH x).mp hx.1, (hK x).mp hx.2⟩, fun hx => ⟨(hH x).mpr hx.1, (hK x).mpr hx.2⟩⟩

omit [Finite G] in
theorem le_sec2M (Q T : Subgroup G) : T ≤ sec2M Q T := by
  have h := le_iSup (fun n : normalizer (Q : Set G) => rightConjugate T n) 1
  rwa [OneMemClass.coe_one, rightConjugate_one] at h

omit [Finite G] in
theorem conj_mem_sec2M {Q T : Subgroup G} {d : G} (hd : d ∈ normalizer (Q : Set G)) {m : G}
    (hm : m ∈ sec2M Q T) : d⁻¹ * m * d ∈ sec2M Q T := by
  have hle : (sec2M Q T).map (MulAut.conj d⁻¹).toMonoidHom ≤ sec2M Q T := by
    rw [sec2M, Subgroup.map_iSup]
    refine iSup_le fun n => ?_
    have e : (rightConjugate T n).map (MulAut.conj d⁻¹).toMonoidHom =
        rightConjugate T (n * ⟨d, hd⟩ : normalizer (Q : Set G)) := by
      rw [coe_mul, ← rightConjugate_mul]
      rfl
    rw [e]
    exact le_iSup (fun n : normalizer (Q : Set G) => rightConjugate T n) _
  have := hle ⟨m, hm, rfl⟩
  simpa [MulAut.conj_apply] using this

omit [Finite G] in
theorem sec2M_le_normalizer {Q T : Subgroup G} (hT : T ≤ normalizer (Q : Set G)) :
    sec2M Q T ≤ normalizer (Q : Set G) := by
  refine iSup_le fun n => ?_
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have h := mul_mem (mul_mem (inv_mem n.2) (hT hx)) n.2
  simpa [mul_assoc] using h

omit [Finite G] in
theorem sec2M_le_of_normal {Q T X : Subgroup G} (hX : X.Normal) (hT : T ≤ X) :
    sec2M Q T ≤ X := by
  refine iSup_le fun n => ?_
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have h := hX.conj_mem _ (hT hx) (n : G)⁻¹
  simpa [mul_assoc] using h

theorem card_eq_card_inf_ker_mul_card_map' {H K : Type*} [Group H] [Group K] [Finite H]
    (φ : H →* K) (W : Subgroup H) :
    Nat.card W = Nat.card (W ⊓ φ.ker : Subgroup H) * Nat.card (W.map φ) := by
  let f : W →* K := φ.comp W.subtype
  have hrange : f.range = W.map φ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_map, ← MonoidHom.range_eq_map, range_subtype]
  have hker : Nat.card f.ker = Nat.card (W ⊓ φ.ker : Subgroup H) := by
    have h1 : f.ker = φ.ker.subgroupOf W := (MonoidHom.comap_ker φ W.subtype).symm
    rw [h1, ← inf_subgroupOf_left]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker, mul_comm]

theorem le_of_two_pow_dvd {k : ℕ} (h : 2 ^ k ∣ 241920) : 2 ^ k ≤ 2 ^ 8 := by
  refine Nat.pow_le_pow_right (by norm_num) ?_
  by_contra hk
  have h9 : 2 ^ 9 ∣ 241920 := (pow_dvd_pow 2 (by omega)).trans h
  norm_num at h9

theorem card_le_of_le_normalizer {A R U : Subgroup G}
    (hA : commutator A = ⊤) (hL : TypeL34 (rankTwoQuot A))
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hR4 : Nat.card R = 4) (hU : IsPGroup 2 U)
    (hUN : U ≤ normalizer (A : Set G)) : Nat.card U ≤ 2 ^ 10 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect A := ⟨hA⟩
  obtain ⟨e₀⟩ := PSL3Four.nonempty_equiv_of_stated (rankTwoQuot A) hL
  obtain ⟨eR, -, -⟩ := PSL3Four.full_automorphism_action
  let φ : normalizer (A : Set G) →* MulAut PSL3Four.S :=
    (MulAut.congr e₀).toMonoidHom.comp (GH74.KGroups.inducedHom.comp A.normalizerMonoidHom)
  have hker : φ.ker ≤ (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G)) := by
    intro n hn
    have h1 : GH74.KGroups.inducedHom (A.normalizerMonoidHom n) = 1 :=
      (MulAut.congr e₀).injective (by rw [map_one]; exact hn)
    have h2 : A.normalizerMonoidHom n = 1 :=
      GH74.KGroups.inducedHom_injective hperf (by rw [h1, map_one])
    have h3 : n ∈ A.normalizerMonoidHom.ker := h2
    rwa [Subgroup.normalizerMonoidHom_ker] at h3
  set U' := U.subgroupOf (normalizer (A : Set G)) with hU'
  have hcardU : Nat.card U' = Nat.card U := Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv
  have hsplit := card_eq_card_inf_ker_mul_card_map' φ U'
  have h1 : Nat.card (U' ⊓ φ.ker : Subgroup _) ≤ 4 := by
    have hle : Nat.card (U' ⊓ φ.ker : Subgroup _) ≤ Nat.card (U ⊓ centralizer (A : Set G) :
        Subgroup G) := by
      have hinj : Function.Injective (fun x : ↥(U' ⊓ φ.ker) =>
          (⟨(x : normalizer (A : Set G)), x.2.1, hker x.2.2⟩ : ↥(U ⊓ centralizer (A : Set G)))) :=
        fun a b h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h')
      exact Nat.card_le_card_of_injective _ hinj
    obtain ⟨k, hk⟩ := (hU.to_le (inf_le_left : U ⊓ centralizer (A : Set G) ≤ U)).exists_card_eq
    have hdvd : 2 ^ k ∣ Nat.card (centralizer (A : Set G)) :=
      hk ▸ Subgroup.card_dvd_of_le inf_le_right
    have := Nat.le_of_dvd (by norm_num) (hR4 ▸ AS76b.pow_dvd_card_of_isSylowOf hR hdvd)
    omega
  have h2 : Nat.card (U'.map φ) ≤ 2 ^ 8 := by
    have hU'2 : IsPGroup 2 U' := hU.of_equiv (subgroupOfEquivOfLe hUN).symm
    obtain ⟨k, hk⟩ := (hU'2.map φ).exists_card_eq
    have hdvd : Nat.card (U'.map φ) ∣ 241920 := by
      rw [← PSL3Four.card_R, Nat.card_congr eR.toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rw [hk] at hdvd ⊢
    exact le_of_two_pow_dvd hdvd
  rw [← hcardU, hsplit]
  calc Nat.card (U' ⊓ φ.ker : Subgroup _) * Nat.card (U'.map φ) ≤ 4 * 2 ^ 8 :=
        Nat.mul_le_mul h1 h2
    _ = 2 ^ 10 := by norm_num

end General

end Sec2

namespace Sec2Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ Q : Subgroup G}
  {u y z : G}

theorem T_le_normalizer (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    sec2T E T₀ ≤ normalizer (Q : Set G) :=
  le_sup_right.trans hQ.HT_le

theorem z_mem_T (hQ : Sec2Q G A R g E F T₀ Q u y z) : z ∈ sec2T E T₀ := by
  have : z ∈ centerIn (sec2T E T₀) := by rw [hQ.center]; exact mem_zpowers z
  exact this.1

theorem T_le_T₀ (_hQ : Sec2Q G A R g E F T₀ Q u y z) : sec2T E T₀ ≤ T₀ := inf_le_left

theorem isPGroup_T₀ (hQ : Sec2Q G A R g E F T₀ Q u y z) : IsPGroup 2 T₀ :=
  hQ.data.sylow.isPGroup

theorem z_mem_Q (hQ : Sec2Q G A R g E F T₀ Q u y z) : z ∈ Q := by
  have hT : IsPGroup 2 (sec2T E T₀) := hQ.isPGroup_T₀.to_le hQ.T_le_T₀
  have hQ1 : Q ≠ ⊥ := by
    intro h
    have := hQ.q8.2.1
    rw [h, card_bot] at this
    norm_num at this
  have h := Sec2.inf_centerIn_ne_bot hT hQ.le hQ.T_le_normalizer hQ1
  rw [hQ.center] at h
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
  rcases Sec2.eq_one_or_eq_of_mem_zpowers hQ.order hx.2 with h' | h'
  · exact absurd h' hx1'
  · exact h' ▸ hx.1

theorem z_mem_centralizer_Q (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    z ∈ centralizer (Q : Set G) := by
  have : z ∈ centerIn (sec2T E T₀) := by rw [hQ.center]; exact mem_zpowers z
  exact mem_centralizer_iff.mpr fun q hq => (mem_centralizer_iff.mp this.2 q (hQ.le hq))

theorem centerIn_Q (hQ : Sec2Q G A R g E F T₀ Q u y z) : centerIn Q = zpowers z := by
  have hzc : z ∈ centerIn Q := ⟨hQ.z_mem_Q, hQ.z_mem_centralizer_Q⟩
  have hcard : Nat.card (centerIn Q) = 2 := by
    rw [Sec2.centerIn_eq_map, card_map_of_injective Q.subtype_injective]
    exact hQ.q8.1.2.2.2
  refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzc) ?_).symm
  rw [hcard, Nat.card_zpowers, hQ.order]

theorem isQ8Cube_map {Q' : Subgroup G} (hQ' : IsQ8Cube Q') (t : G) :
    IsQ8Cube (Q'.map (MulAut.conj t).toMonoidHom) := by
  refine ⟨CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (Q'.equivMapOfInjective _ (MulAut.conj t).injective) hQ'.1, ?_, ?_⟩
  · rw [card_map_of_injective (MulAut.conj t).injective]
    exact hQ'.2.1
  · rintro ⟨U, hUQ, hU, hU16⟩
    apply hQ'.2.2
    refine ⟨U.map (MulAut.conj t⁻¹).toMonoidHom, ?_, Sec2.isElemAbelian_map hU _, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨q, hq, rfl⟩ := hUQ hx
      simpa [MulAut.conj_apply, mul_assoc] using hq
    · rw [card_map_of_injective (MulAut.conj t⁻¹).injective, hU16]

theorem T₀_le_normalizer_T (h212 : Step212) (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    T₀ ≤ normalizer (sec2T E T₀ : Set G) := by
  intro t ht
  have hP := ((h212 G A R g E F hQ.data.setting).2 T₀ hQ.data.le hQ.data.sylow).2.2.2.2.2
  exact Sec2.mem_normalizer_inf (le_normalizer ht) (Sec2.mem_normalizer_oUpperTwo (hP ht))

theorem T₀_le_normalizer_Q (h26 : Step26) (h212 : Step212) (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    T₀ ≤ normalizer (Q : Set G) := by
  intro t ht
  have hS := hQ.data.setting
  obtain ⟨-, -, -, -, -, -, -, -, hNH⟩ := h26 G A R g E F hS
  have htH : t ∈ normalizer (sec2H E F : Set G) := hNH (hQ.data.sylow.le ht)
  have htT : t ∈ normalizer (sec2T E T₀ : Set G) := hQ.T₀_le_normalizer_T h212 ht
  have htHT := Sec2.mem_normalizer_sup htH htT
  have hyH : y ∈ sec2H E F := hQ.data.uy.2.2.2.1.1.1
  rw [mem_normalizer_iff_map_conj_eq]
  refine hQ.unique _ (isQ8Cube_map hQ.q8 t) ?_ ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact (mem_normalizer_iff.mp htT q).mp (hQ.le hq)
  ·
    have hy' : t⁻¹ * y * t ∈ sec2H E F ⊔ sec2T E T₀ := by
      have := (mem_normalizer_iff.mp (inv_mem htHT) y).mp (mem_sup_left hyH)
      simpa using this
    have hyQ := hQ.HT_le hy'
    rw [mem_normalizer_iff_map_conj_eq] at hyQ ⊢
    calc (Q.map (MulAut.conj t).toMonoidHom).map (MulAut.conj y).toMonoidHom
        = (Q.map (MulAut.conj (t⁻¹ * y * t)).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
          rw [map_map, map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply, mul_assoc]
      _ = Q.map (MulAut.conj t).toMonoidHom := by
          rw [show Q.map (MulAut.conj (t⁻¹ * y * t)).toMonoidHom = Q from hyQ]

theorem T₀_le_centralizer (h212 : Step212) (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    T₀ ≤ centralizer ({z} : Set G) := by
  intro t ht
  have h := Sec2.mem_normalizer_centerIn (hQ.T₀_le_normalizer_T h212 ht)
  rw [hQ.center] at h
  exact mem_centralizer_singleton_iff.mpr (by
    have := Sec2.conj_eq_of_mem_normalizer_zpowers hQ.order h
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [this])

theorem sylow_T₀ (h212 : Step212) (hQ : Sec2Q G A R g E F T₀ Q u y z) : IsSylowOf 2 T₀ ⊤ :=
  ((h212 G A R g E F hQ.data.setting).2 T₀ hQ.data.le hQ.data.sylow).1

theorem sylow_T₀_centralizer (h212 : Step212) (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    IsSylowOf 2 T₀ (centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (hQ.sylow_T₀ h212).of_le (hQ.T₀_le_centralizer h212) le_top

theorem z_mem_Z (h212 : Step212) (hQ : Sec2Q G A R g E F T₀ Q u y z) : z ∈ sec2Z A E F := by
  have hZ := ((h212 G A R g E F hQ.data.setting).2 T₀ hQ.data.le hQ.data.sylow).2.2.2.1
  rw [← hZ]
  have hz : z ∈ centerIn (sec2T E T₀) := by rw [hQ.center]; exact mem_zpowers z
  rw [Sec2.centerIn_eq_map] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨t, ?_, rfl⟩
  have h1 : t ∈ Subgroup.upperCentralSeries (sec2T E T₀) 1 := by
    rwa [Subgroup.upperCentralSeries_one]
  exact Subgroup.upperCentralSeries_mono _ (by norm_num) h1

omit [Finite G] in
theorem rho_eq_one_of_mem_centralizer {ψ : G → (Fin 6 → ZMod 2)}
    {ρ : ↥(sec2M Q (sec2T E T₀)) →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))}
    (hψ : ∀ v : Fin 6 → ZMod 2, ∃ a ∈ Q, ψ a = v)
    (hρ : ∀ m : ↥(sec2M Q (sec2T E T₀)), ∀ a ∈ Q, ψ ((m : G) * a * (m : G)⁻¹) = ρ m (ψ a))
    {m : ↥(sec2M Q (sec2T E T₀))} (hm : (m : G) ∈ centralizer (Q : Set G)) : ρ m = 1 := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨a, ha, rfl⟩ := hψ v
  rw [← hρ m a ha]
  change ψ ((m : G) * a * (m : G)⁻¹) = ψ a
  rw [← mem_centralizer_iff.mp hm a ha, mul_inv_cancel_right]

theorem sylow_zpowers_centralizer (h24 : Step24) (h26 : Step26) (h212 : Step212)
    (h216 : Step216) (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    IsSylowOf 2 (zpowers z) (centralizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hQ.data.setting
  obtain ⟨-, hZS, hSS, -⟩ := h24 G A R g E F hS
  obtain ⟨-, -, -, -, -, hSsyl, -, -, -⟩ := h26 G A R g E F hS
  obtain ⟨ψ, ρ, -, hψ, -, -, hρ, -, hρker⟩ := h216 G A R g E F T₀ Q u y z hQ
  have hzQ : {z} ⊆ (Q : Set G) := Set.singleton_subset_iff.mpr hQ.z_mem_Q
  have hCz : centralizer (Q : Set G) ≤ centralizer ({z} : Set G) := Subgroup.centralizer_le hzQ
  have hCN : centralizer (Q : Set G) ≤ normalizer (Q : Set G) := fun c hc => by
    rw [mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have e : c * q * c⁻¹ = q := by
        rw [← mem_centralizer_iff.mp hc q hq, mul_inv_cancel_right]
      rw [e]
      exact hq
    · intro hq
      have hq' := hc
      have h2 := mem_centralizer_iff.mp hc (c * q * c⁻¹) hq
      have e : c * q * c⁻¹ = q := by
        have h3 : c * q * c⁻¹ * c = c * (c * q * c⁻¹) := h2
        have h4 : c * q = c * (c * q * c⁻¹) := by simpa [mul_assoc] using h3
        exact (mul_left_cancel h4).symm
      rwa [e] at hq
  have hT₀N : T₀ ≤ normalizer (Q : Set G) := hQ.T₀_le_normalizer_Q h26 h212
  have hT₀2 := hQ.isPGroup_T₀
  have hTM : sec2T E T₀ ≤ sec2M Q (sec2T E T₀) := Sec2.le_sec2M Q _
  have hST : sec2S A R E F ≤ sec2T E T₀ :=
    le_sup_right.trans ((h212 G A R g E F hS).2 T₀ hQ.data.le hQ.data.sylow).2.1
  have hSN : sec2S A R E F ≤ normalizer (Q : Set G) := hST.trans hQ.T_le_normalizer
  have hQ2 : IsPGroup 2 Q := hQ.q8.1.1
  have hO'Q : AS76b.oddCoreIn (sec2M Q (sec2T E T₀) ⊓ centralizer (Q : Set G)) ≤
      centralizer (Q : Set G) :=
    (AS76b.oddCoreIn_le _).trans inf_le_right
  have hST₀ : sec2S A R E F ≤ T₀ := le_sup_right.trans hQ.data.le
  have key : ∀ w ∈ sec2M Q (sec2T E T₀), w ∈ centralizer (Q : Set G) → w ∈ T₀ →
      w ∈ zpowers z := by
    intro w hwM hwC hwT
    have h1 : ρ ⟨w, hwM⟩ = 1 := rho_eq_one_of_mem_centralizer hψ hρ hwC
    have h2 : (⟨w, hwM⟩ : sec2M Q (sec2T E T₀)) ∈ ρ.ker := h1
    rw [hρker] at h2
    obtain ⟨k, hk⟩ := hT₀2 ⟨w, hwT⟩
    have hwQ := Sec2.mem_of_mem_sup_of_odd hQ2 (AS76b.odd_card_oddCoreIn _) hO'Q h2 k
      (congrArg Subtype.val hk)
    rw [← hQ.centerIn_Q]
    exact ⟨hwQ, hwC⟩
  have hzZ := hQ.z_mem_Z h212
  have hD : T₀ ⊓ centralizer (Q : Set G) ≤
      centralizerMod (normalizer (sec2S A R E F : Set G)) (sec2S A R E F) (sec2Z A E F) := by
    rintro d ⟨hdT, hdC⟩
    have hdN : d ∈ normalizer (sec2S A R E F : Set G) := hQ.data.sylow.le hdT
    refine ⟨hdN, hZS ▸ Sec2.mem_normalizer_centerIn hdN, fun s hs => ?_⟩
    have hsM : s ∈ sec2M Q (sec2T E T₀) := hTM (hST hs)
    have hw : s⁻¹ * d⁻¹ * s * d ∈ zpowers z := by
      refine key _ ?_ ?_ ?_
      · have := mul_mem (inv_mem hsM) (Sec2.conj_mem_sec2M (hCN hdC) hsM)
        simpa [mul_assoc] using this
      · have h1 : s⁻¹ * d⁻¹ * s ∈ centralizer (Q : Set G) := by
          have := (mem_normalizer_iff.mp (Sec2.normalizer_le_normalizer_centralizer Q
            (inv_mem (hSN hs))) d⁻¹).mp (inv_mem hdC)
          simpa using this
        exact mul_mem h1 hdC
      · have hsT : s ∈ T₀ := hST₀ hs
        exact mul_mem (mul_mem (mul_mem (inv_mem hsT) (inv_mem hdT)) hsT) hdT
    exact (zpowers_le.mpr hzZ) hw
  have hScm : sec2S A R E F ≤ centralizerMod (normalizer (sec2S A R E F : Set G))
      (sec2S A R E F) (sec2Z A E F) := by
    intro s hs
    refine ⟨le_normalizer hs, hZS ▸ Sec2.mem_normalizer_centerIn (le_normalizer hs),
      fun y hy => ?_⟩
    rw [← hSS]
    have := Subgroup.commutator_mem_commutator (inv_mem hy) (inv_mem hs)
    simpa [commutatorElement_def] using this
  have hDS : T₀ ⊓ centralizer (Q : Set G) ≤ sec2S A R E F := by
    have heq := hSsyl.eq_of_le
      (le_sup_left : sec2S A R E F ≤ sec2S A R E F ⊔ (T₀ ⊓ centralizer (Q : Set G)))
      (sup_le hScm hD) (hT₀2.to_le (sup_le hST₀ inf_le_left))
    rw [← heq]
    exact le_sup_right
  have hDz : T₀ ⊓ centralizer (Q : Set G) = zpowers z := by
    refine le_antisymm (fun d hd => key d (hTM (hST (hDS hd))) hd.2 hd.1) ?_
    rw [zpowers_le]
    exact ⟨hQ.T_le_T₀ hQ.z_mem_T, hQ.z_mem_centralizer_Q⟩
  have h1 : IsSylowOf 2 T₀ (centralizer ({z} : Set G) ⊓ normalizer (Q : Set G)) :=
    (hQ.sylow_T₀_centralizer h212).of_le (le_inf (hQ.T₀_le_centralizer h212) hT₀N) inf_le_left
  have h2 := h1.inf_of_le_normalizer (le_inf hCz hCN)
    (inf_le_right.trans (Sec2.normalizer_le_normalizer_centralizer Q))
  rwa [hDz] at h2

theorem two_pow_ten_lt_card_T₀ (h21 : Step21) (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    2 ^ 10 < Nat.card T₀ := by
  have hS := hQ.data.setting
  obtain ⟨-, ⟨hEP, hEP16, -⟩, -, -, -, -, -, -, ⟨hESP, hESP4, -⟩, ⟨hES, hES16, -⟩⟩ :=
    h21 G A R g E F hS
  have hE := hS.frame.cardE
  have hcard : ∀ {X : Subgroup G}, E ≤ X → Nat.card X = E.relIndex X * 64 := by
    intro X hX
    have := Subgroup.relIndex_mul_card E X
    rw [inf_eq_left.mpr hX, hE] at this
    exact this.symm
  have hP := hcard hEP
  rw [hEP16] at hP
  have hSP := hcard hESP
  rw [hESP4] at hSP
  have hSc := hcard hES
  rw [hES16] at hSc
  have hlt : sec2P E < sec2P E ⊔ sec2S A R E F := by
    refine lt_of_le_of_ne le_sup_left fun h => ?_
    have hle : sec2S A R E F ≤ sec2P E := h ▸ le_sup_right
    rw [inf_eq_left.mpr hle] at hSP
    omega
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 := Subgroup.card_le_of_le hQ.data.le
  omega

theorem not_mem_rightConjugate (h21 : Step21) (h212 : Step212)
    (hQ : Sec2Q G A R g E F T₀ Q u y z) (x : G) : z ∉ rightConjugate R x := by
  intro hzx
  rw [mem_rightConjugate_iff] at hzx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hQ.data.setting
  have hF := hS.frame
  obtain ⟨hAq, -, htight, hNC, -⟩ := hF.base.hyp.standard
  have hz1 : z ≠ 1 := by
    rintro rfl
    have := hQ.order
    rw [orderOf_one] at this
    exact absurd this (by norm_num)
  have hr2 : orderOf (x * z * x⁻¹) = 2 := by
    rw [← hQ.order]
    have h := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective z
    simpa [MulAut.conj_apply] using h
  have hCr : centralizer ({x * z * x⁻¹} : Set G) ≤ normalizer (A : Set G) := by
    intro c hc
    rw [← hNC]
    by_contra hcN
    have hodd := htight c hcN
    have hmem : x * z * x⁻¹ ∈ (centralizer (A : Set G) ⊓
        (centralizer (A : Set G)).map (MulAut.conj c).toMonoidHom : Subgroup G) := by
      refine ⟨hF.sylowR.le hzx, ⟨x * z * x⁻¹, hF.sylowR.le hzx, ?_⟩⟩
      have hc' := mem_centralizer_singleton_iff.mp hc
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hc', mul_inv_cancel_right]
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hr2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hT₀c : T₀.map (MulAut.conj x).toMonoidHom ≤ centralizer ({x * z * x⁻¹} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    have htz := mem_centralizer_singleton_iff.mp (hQ.T₀_le_centralizer h212 ht)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc x * t * x⁻¹ * (x * z * x⁻¹) = x * (t * z) * x⁻¹ := by group
      _ = x * (z * t) * x⁻¹ := by rw [htz]
      _ = x * z * x⁻¹ * (x * t * x⁻¹) := by group
  have hcard := Sec2.card_le_of_le_normalizer hAq.1 hS.type hF.sylowR hF.cardR
    (hQ.isPGroup_T₀.map _) (hT₀c.trans hCr)
  rw [card_map_of_injective (MulAut.conj x).injective] at hcard
  exact absurd hcard (not_le.mpr (hQ.two_pow_ten_lt_card_T₀ h21))

end Sec2Q

end CFSG.ComponentClassification.AS81
