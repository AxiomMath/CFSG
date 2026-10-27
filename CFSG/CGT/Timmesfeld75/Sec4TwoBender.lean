module

public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.BenderInputs4
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.Models.BenderSuzuki
public import CFSG.CGT.Timmesfeld75.Sec25
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups
open CFSG.BenderSuzuki (IsBenderGroup PSL2Model SzModel PSU3Model)

section Lemma25

theorem lemma25_top_of_not_normal {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hAsc : AschbacherNoPolarInput) (hT : StrongWC T)
    (hK : Subgroup.normalClosure (T : Set G) = ⊤) (hnT : ¬ ∀ g : G, conjSubgroup g T = T)
    (h4 : 4 ≤ Nat.card T) : IsBenderGroup (G ⧸ Subgroup.center G) := by
  have hTbot : T ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h4
    omega
  have hcentral : ∀ (P : Subgroup G) (p : ℕ), p.Prime → P.Normal → IsPGroup p P →
      ∀ n ∈ P, ∀ k : G, n * k = k * n := by
    intro P p hp hPn hPp n hn k
    have hNn : ∀ k ∈ Subgroup.normalClosure (T : Set G), ∀ n ∈ P, k * n * k⁻¹ ∈ P :=
      fun k _ n hn => hPn.conj_mem n hn k
    have hkK : k ∈ Subgroup.normalClosure (T : Set G) := by rw [hK]; trivial
    have hPK : P ≤ Subgroup.normalClosure (T : Set G) := by rw [hK]; exact le_top
    by_cases hp2 : p = 2
    · subst hp2
      exact twoCore_le_center hT hnT P hPK hNn hPp n hn k hkK
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨m, hm⟩ := hPp.exists_card_eq
      have hodd : Odd (Nat.card P) := by
        rw [hm]
        exact (hp.odd_of_ne_two hp2).pow
      exact oddCore_le_center hT.isWC h4 P hPK hNn hodd n hn k hkK
  refine isBenderGroup_quotient_center hAsc hT hK hnT hTbot ?_ ?_ ?_
  · intro t ht ht1
    obtain ⟨k, -, hk⟩ := not_central_of_mem_T hT hnT ht ht1
    exact ⟨k, hk⟩
  · intro x hx y hy hz
    exact commute_of_comm_central hT hnT hx hy fun k _ => hz k
  · exact solvable_normal_bot_of_pSubgroups_central fun p hp P hPn hPp =>
      fun n hn => Subgroup.mem_center_iff.2 fun k => (hcentral P p hp hPn hPp n hn k).symm

end Lemma25

section Center

variable {K : Type*} [Group K]

theorem StrongWC.map_center {T : Subgroup K} (hT : StrongWC T)
    (hTZ : T ⊓ Subgroup.center K = ⊥) :
    StrongWC (T.map (QuotientGroup.mk' (Subgroup.center K))) := by
  refine ⟨isElemAbelian_map_of_hom hT.1 _, ?_⟩
  intro tb htb htb1 ab hab gb hgb
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 htb
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hab
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact htb1 (map_one _)
  set c : K := g⁻¹ * a * g with hc
  have hcomm : (QuotientGroup.mk c : K ⧸ Subgroup.center K) * QuotientGroup.mk t =
      QuotientGroup.mk t * QuotientGroup.mk c := Subgroup.mem_centralizer_singleton_iff.1 hgb
  have hz : (c * t)⁻¹ * (t * c) ∈ Subgroup.center K :=
    QuotientGroup.eq.1 (hcomm : (QuotientGroup.mk (c * t) : K ⧸ Subgroup.center K) =
      QuotientGroup.mk (t * c))
  set z : K := (c * t)⁻¹ * (t * c) with hzdef
  have h1 : c⁻¹ * t * c = t * z := by
    rw [hzdef]
    group
  have hzt : z * t = t * z := (Subgroup.mem_center_iff.1 hz t).symm
  have h2 : c⁻¹ * t * c ∈ T := hT.2 t ht ht1 t ht c (by
    rw [Subgroup.mem_centralizer_singleton_iff, h1]
    calc t * z * t = t * (z * t) := mul_assoc _ _ _
      _ = t * (t * z) := by rw [hzt])
  have hzT : z ∈ T := by
    rw [h1] at h2
    have := T.mul_mem (T.inv_mem ht) h2
    simpa using this
  have hz1 : z = 1 := by
    have : z ∈ T ⊓ Subgroup.center K := ⟨hzT, hz⟩
    rw [hTZ, Subgroup.mem_bot] at this
    exact this
  have h3 : t * c = c * t := by
    have h4 : c * (c⁻¹ * t * c) = c * t := by rw [h1, hz1, mul_one]
    rw [← h4]
    group
  have hcT : c ∈ T := hT.2 t ht ht1 a ha g
    (Subgroup.mem_centralizer_singleton_iff.2 h3.symm)
  exact Subgroup.mem_map_of_mem _ hcT

theorem card_map_mk_center_of_inf_eq_bot {T : Subgroup K} (hTZ : T ⊓ Subgroup.center K = ⊥) :
    Nat.card (T.map (QuotientGroup.mk' (Subgroup.center K))) = Nat.card T := by
  let φ := (QuotientGroup.mk' (Subgroup.center K)).domRestrict T
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have : (t : K) ∈ T ⊓ Subgroup.center K := ⟨t.2, (QuotientGroup.eq_one_iff (t : K)).1 ht⟩
    rw [hTZ, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hr : φ.range = T.map (QuotientGroup.mk' (Subgroup.center K)) :=
    MonoidHom.domRestrict_range _ _
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Center

section Parameters

theorem isBenderGroup_center_sylow_card {K : Type} [Group K] [Finite K] (hK : IsBenderGroup K)
    (Q : Sylow 2 K) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (K ≃* PSL2Model n) ∧
        Nat.card (Subgroup.center (Q : Subgroup K)) = 2 ^ n ∧
        Nat.card (Q : Subgroup K) = 2 ^ n) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Nonempty (K ≃* SzModel n)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (K ≃* PSU3Model n) ∧
        Nat.card (Subgroup.center (Q : Subgroup K)) = 2 ^ n) := by
  rcases hK with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · left
    have : Finite (PSL2Model n) := Finite.of_surjective e e.surjective
    obtain ⟨-, -, -, h1, h2⟩ := ((bender_psl2_borel_full n hn).map_mulEquiv e.symm) Q
    exact ⟨n, hn, ⟨e⟩, h1, by simpa using h2⟩
  · right
    left
    exact ⟨n, hn, ⟨e⟩⟩
  · right
    right
    have hmodel : PSU3Model n = PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
    let e' : K ≃* PSU3 2 n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (PSU3 2 n) := Finite.of_surjective e' e'.surjective
    obtain ⟨-, -, -, h1, -⟩ := ((bender_psu3_borel_full n hn).map_mulEquiv e'.symm) Q
    exact ⟨n, hn, ⟨e⟩, h1⟩

theorem card_eq_center_sylow_of_strongWC {B : Type*} [Group B] [Finite B] (hB : IsBenderGroup B)
    {T' : Subgroup B} (hT' : StrongWC T') (hbot : T' ≠ ⊥) {Q : Sylow 2 B}
    (hTQ : T' ≤ (Q : Subgroup B)) :
    Nat.card T' = Nat.card (Subgroup.center (Q : Subgroup B)) := by
  obtain ⟨⟨x, hxT⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hcomm : ∀ t ∈ T', ∀ q ∈ (Q : Subgroup B), Commute t q := fun t ht q hq =>
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hB Q (hTQ ht)
      (by rw [← pow_two]; exact hT'.1.2 t ht) q hq
  have hZ : T' = (Subgroup.center (Q : Subgroup B)).map (Q : Subgroup B).subtype := by
    apply le_antisymm
    · intro t ht
      refine ⟨⟨t, hTQ ht⟩, Subgroup.mem_center_iff.2 fun q => ?_, rfl⟩
      exact Subtype.ext (hcomm t ht q q.2).symm.eq
    · rintro _ ⟨z, hz, rfl⟩
      refine mem_of_commute_sylow_of_strongWC hB hT' hxT hx1' Q hTQ z.2 fun q hq => ?_
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨q, hq⟩)
  rw [hZ]
  exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)

end Parameters

section Orders

theorem not_three_dvd_card_szModel
    {n : ℕ} : ¬ 3 ∣ Nat.card (SzModel n) := by
  have hmodel : CFSG.Theory.Comparator.SzModel n = Sz n := CFSG.Models.benderSzModel_eq_sz n
  have hq : 2 ^ (2 * n + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq2 : (2 ^ (2 * n + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have hq1 : 1 ≤ 2 ^ (2 * n + 1) := Nat.one_le_two_pow
  rw [show SzModel n = Sz n from hmodel,
    CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz n,
    Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mul_mod ((2 ^ (2 * n + 1)) ^ 2), hq2,
    show ((2 ^ (2 * n + 1)) ^ 2 + 1) % 3 = 2 by omega,
    show (2 ^ (2 * n + 1) - 1) % 3 = 1 by omega]
  norm_num

end Orders

section Identification

theorem bender_identification
    (hAsc : AschbacherNoPolarInput) {K : Type} [Group K] [Finite K]
    {T : Subgroup K} (hT : StrongWC T) (hnn : ¬ ∀ g : K, conjSubgroup g T = T)
    (hcl : Subgroup.normalClosure (T : Set K) = ⊤) (hTZ : T ⊓ Subgroup.center K = ⊥)
    {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card T = 2 ^ f)
    {X : Type} [Group X] (hX : IsSimpleGroup X) {S : Subgroup X} (hS : IsL2Pair X S (2 ^ f))
    (ι : X →* K) (hTS : T = S.map ι) :
    ι.range = ⊤ ∨ Nonempty (K ⧸ Subgroup.center K ≃* PSU3Model f) := by
  have h4 : 4 ≤ Nat.card T := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hTbot : T ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h4
    omega
  have hB : IsBenderGroup (K ⧸ Subgroup.center K) :=
    lemma25_top_of_not_normal hAsc hT hcl hnn h4
  have hXfin : Finite X := hS.finite
  set π : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hπ
  let ψ : X →* K ⧸ Subgroup.center K := π.comp ι
  have hψinj : Function.Injective ψ := by
    have := hX
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      apply hTbot
      rw [← hTZ, eq_comm, inf_eq_left]
      rintro _ hx
      rw [hTS] at hx
      obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.1 hx
      have : s ∈ ψ.ker := by rw [h]; trivial
      exact (QuotientGroup.eq_one_iff (ι s)).1 this
  have hT' : StrongWC (T.map π) := hT.map_center hTZ
  have hT'card : Nat.card (T.map π) = 2 ^ f := by
    rw [hπ, card_map_mk_center_of_inf_eq_bot hTZ, hcard]
  have hT'bot : T.map π ≠ ⊥ := by
    intro h
    have : Nat.card (T.map π) = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hT'card] at this
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨Q, hTQ⟩ := (isPGroup_two_of_isElemAbelian hT'.1).exists_le_sylow
  have hZcard := card_eq_center_sylow_of_strongWC hB hT' hT'bot hTQ
  rw [hT'card] at hZcard
  rcases isBenderGroup_center_sylow_card hB Q with
    ⟨n, hn, ⟨e⟩, hn1, -⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩, hn1⟩
  ·
    left
    have hnf : n = f := (Nat.pow_right_injective (le_refl 2) (hZcard.trans hn1)).symm
    subst hnf
    have hcardB : Nat.card (K ⧸ Subgroup.center K) = Nat.card X := by
      rw [Nat.card_congr e.toEquiv, hS.card_eq_mul,
        CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psl2_even (by omega)]
    have hsurj : Function.Surjective ψ :=
      (hψinj.bijective_of_nat_card_le hcardB.le).2
    have hnormal : (ι.range).Normal := by
      refine ⟨fun y hy k => ?_⟩
      obtain ⟨y', rfl⟩ := hy
      obtain ⟨x, hx⟩ := hsurj (QuotientGroup.mk k)
      obtain ⟨z, hzdef⟩ : ∃ z : K, z = (ι x)⁻¹ * k := ⟨_, rfl⟩
      have hz : z ∈ Subgroup.center K := hzdef ▸ QuotientGroup.eq.1 hx
      have hk : k = ι x * z := by rw [hzdef]; group
      have hc := Subgroup.mem_center_iff.1 hz (ι y')
      refine ⟨x * y' * x⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv, hk]
      have e1 : ι x * z * ι y' * (ι x * z)⁻¹ = ι x * (z * ι y' * z⁻¹) * (ι x)⁻¹ := by group
      have e2 : z * ι y' * z⁻¹ = ι y' := by rw [← hc]; group
      rw [e1, e2]
    have hTle : (T : Set K) ⊆ ι.range := fun t ht => by
      rw [hTS] at ht
      obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.1 ht
      exact ⟨s, rfl⟩
    have hle := Subgroup.normalClosure_le_normal hTle
    rw [hcl] at hle
    exact eq_top_iff.2 hle
  · exfalso
    have hdvd : Nat.card X ∣ Nat.card (K ⧸ Subgroup.center K) :=
      Subgroup.card_dvd_of_injective ψ hψinj
    have h3 : 3 ∣ Nat.card X := by
      rw [hS.card_eq_mul]
      refine Dvd.dvd.mul_left ?_ _
      have : (2 ^ f) ^ 2 - 1 = 4 ^ f - 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [this]
      have h41 : 4 ^ f ≡ 1 ^ f [MOD 3] := Nat.ModEq.pow f (by decide)
      rw [one_pow] at h41
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 h41.symm
    rw [Nat.card_congr e.toEquiv] at hdvd
    exact not_three_dvd_card_szModel (h3.trans hdvd)
  · right
    have hnf : n = f := (Nat.pow_right_injective (le_refl 2) (hZcard.trans hn1)).symm
    subst hnf
    exact ⟨e⟩

theorem isSimpleGroup_of_psl2 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSL(2, GaloisField 2 f)) : IsSimpleGroup X :=
  CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup
    (CFSG.BenderSuzuki.IsBenderGroup.isPSL2 f hf e)

end Identification

end CFSG.CGT.Timmesfeld75
