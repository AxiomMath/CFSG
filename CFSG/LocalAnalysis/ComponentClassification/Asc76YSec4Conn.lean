module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Induction
import CFSG.LocalAnalysis.ComponentClassification.Asc76YFischer

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem exists_pow_mem_oddCoreIn_of_mem_o22In {X : Subgroup G} {x : G} (hx : x ∈ o22In X) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ oddCoreIn X := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : QuotientGroup.mk' (CFSG.Assembly.oddCore X) y ∈
      CFSG.pCore 2 (X ⧸ CFSG.Assembly.oddCore X) := hy
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X ⧸ CFSG.Assembly.oddCore X)) ⟨_, hy'⟩
  have h1 : QuotientGroup.mk' (CFSG.Assembly.oddCore X) (y ^ 2 ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨k, ⟨_, h1, by simp⟩⟩

theorem conj_mem_o22In {X : Subgroup G} {g x : G} (hg : g ∈ normalizer (X : Set G))
    (hx : x ∈ o22In X) : g * x * g⁻¹ ∈ o22In X := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hxg : g * (y : G) * g⁻¹ ∈ X := (mem_normalizer_iff.mp hg _).mp y.2
  exact ⟨⟨_, hxg⟩, mk_conj_mem_pCore hg y.2 hxg hy, rfl⟩

theorem normalizer_le_normalizer_o22In (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (o22In X : Set G) := fun g hg =>
  mem_normalizer_of_map_conj_le (by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_o22In hg hx)

omit [Finite G] in
theorem inf_o22In_le_oddCoreIn {X A : Subgroup G} (hA : Odd (Nat.card A)) :
    A ⊓ o22In X ≤ oddCoreIn X := by
  intro x hx
  obtain ⟨k, hk⟩ := exists_pow_mem_oddCoreIn_of_mem_o22In (mem_inf.mp hx).2
  have hodd : Odd (orderOf x) := hA.of_dvd_nat (Subgroup.orderOf_dvd_natCard A (mem_inf.mp hx).1)
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem hk m

omit [Finite G] in
theorem isPGroup_o22In {X : Subgroup G} (h : oddCoreIn X = ⊥) : IsPGroup 2 (o22In X) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := exists_pow_mem_oddCoreIn_of_mem_o22In hx
  rw [h, mem_bot] at hk
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem oddCoreIn_le_oddCoreIn_of_le {X Y : Subgroup G} (hXY : X ≤ Y)
    (hYX : Y ≤ normalizer (X : Set G)) : oddCoreIn X ≤ oddCoreIn Y :=
  le_oddCoreIn_of_le_normalizer ((oddCoreIn_le X).trans hXY)
    (hYX.trans (normalizer_le_normalizer_oddCoreIn X)) (odd_card_oddCoreIn X)

theorem o22In_subgroupOf_le {X Y : Subgroup G} (hXY : X ≤ Y)
    (hYX : Y ≤ normalizer (X : Set G)) :
    (o22In X).subgroupOf Y ≤ (CFSG.pCore 2 (Y ⧸ CFSG.Assembly.oddCore Y)).comap
      (QuotientGroup.mk' (CFSG.Assembly.oddCore Y)) := by
  have hPY : o22In X ≤ Y := (map_subtype_le _).trans hXY
  have hPn : (((o22In X).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.Assembly.oddCore Y))).Normal := by
    have : ((o22In X).subgroupOf Y).Normal :=
      (normal_subgroupOf_iff_le_normalizer hPY).mpr
        (hYX.trans (normalizer_le_normalizer_o22In X))
    exact this.map _ (QuotientGroup.mk'_surjective _)
  have hP2 : IsPGroup 2 (((o22In X).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.Assembly.oddCore Y))) := by
    rintro ⟨_, y, hy, rfl⟩
    obtain ⟨k, hk⟩ := exists_pow_mem_oddCoreIn_of_mem_o22In (show (y : G) ∈ o22In X from hy)
    obtain ⟨o, ho, hoy⟩ := oddCoreIn_le_oddCoreIn_of_le hXY hYX hk
    have hoy' : o = y ^ 2 ^ k := Subtype.ext (by simpa using hoy)
    refine ⟨k, Subtype.ext ?_⟩
    change (QuotientGroup.mk' (CFSG.Assembly.oddCore Y) y) ^ 2 ^ k = 1
    rw [← map_pow, ← hoy', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ho
  intro y hy
  exact le_sSup (show _ ∈ {K : Subgroup (Y ⧸ CFSG.Assembly.oddCore Y) | K.Normal ∧ IsPGroup 2 K}
    from ⟨hPn, hP2⟩) ⟨y, hy, rfl⟩

omit [Finite G] in
theorem exists_mul_centralizer_of_commutator_mem {T X N : Subgroup G} (hT : IsPGroup 2 T)
    (hN : Odd (Nat.card N)) (hNX : N ≤ X) (hXN : X ≤ normalizer (N : Set G))
    (hTN : T ≤ normalizer (N : Set G)) (hc : ∀ t ∈ T, ∀ k ∈ X, k⁻¹ * t * k * t⁻¹ ∈ N)
    {k : G} (hk : k ∈ X) : ∃ n ∈ N, ∃ c ∈ X, c ∈ centralizer (T : Set G) ∧ k = n * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : ∀ t ∈ T, ∀ x : G, k⁻¹ * x ∈ N → k⁻¹ * (t * x * t⁻¹) ∈ N := by
    intro t ht x hx
    have h2 : t * (k⁻¹ * x) * t⁻¹ ∈ N := (mem_normalizer_iff.mp (hTN ht) _).mp hx
    have : k⁻¹ * (t * x * t⁻¹) = (k⁻¹ * t * k * t⁻¹) * (t * (k⁻¹ * x) * t⁻¹) := by group
    rw [this]
    exact N.mul_mem (hc t ht k hk) h2
  let Y := {x : G // k⁻¹ * x ∈ N}
  let act : MulAction T Y :=
    { smul := fun t x => ⟨t * x.1 * t⁻¹, hX t t.2 x.1 x.2⟩
      one_smul := fun x => Subtype.ext (by change 1 * x.1 * 1⁻¹ = x.1; group)
      mul_smul := fun s t x => Subtype.ext (by
        change ((s * t : T) : G) * x.1 * ((s * t : T) : G)⁻¹ =
          (s : G) * ((t : G) * x.1 * (t : G)⁻¹) * (s : G)⁻¹
        rw [Subgroup.coe_mul]
        group) }
  have hcard : Nat.card Y = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun x => ⟨k⁻¹ * x.1, x.2⟩
        invFun := fun o => ⟨k * o.1, by simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun o => Subtype.ext (by simp) }
  have hodd : ¬ 2 ∣ Nat.card Y := by
    rw [hcard]
    exact Nat.not_even_iff_odd.mpr hN ∘ even_iff_two_dvd.mpr
  obtain ⟨x, hx⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card Y hodd
  have hfix : ∀ t ∈ T, t * x.1 * t⁻¹ = x.1 := fun t ht =>
    congrArg Subtype.val (MulAction.mem_fixedPoints.mp hx ⟨t, ht⟩)
  have hxX : x.1 ∈ X := by
    have : x.1 = k * (k⁻¹ * x.1) := by group
    rw [this]
    exact X.mul_mem hk (hNX x.2)
  refine ⟨k * x.1⁻¹, ?_, x.1, hxX, ?_, by group⟩
  · have : k * x.1⁻¹ = x.1 * (k⁻¹ * x.1)⁻¹ * x.1⁻¹ := by group
    rw [this]
    exact (mem_normalizer_iff.mp (hXN hxX) _).mp (N.inv_mem x.2)
  · rw [mem_centralizer_iff]
    intro t ht
    calc t * x.1 = t * x.1 * t⁻¹ * t := by group
      _ = x.1 * t := by rw [hfix t ht]

omit [Finite G] in
theorem le_normalizer_sSup {Ω' : Set (Subgroup G)} {Y : Subgroup G}
    (hinv : ∀ J ∈ Ω', ∀ y ∈ Y, rightConjugate J y ∈ Ω') :
    Y ≤ normalizer ((sSup Ω' : Subgroup G) : Set G) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  have key : ∀ g ∈ Y, ∀ x ∈ sSup Ω', g * x * g⁻¹ ∈ sSup Ω' := by
    intro g hg x hx
    have h1 : rightConjugate (sSup Ω') g⁻¹ ≤ sSup Ω' := by
      rw [rightConjugate_le_iff]
      refine sSup_le fun J hJ => ?_
      rw [← rightConjugate_le_iff]
      exact le_sSup (hinv J hJ g⁻¹ (inv_mem hg))
    exact h1 (by rw [mem_rightConjugate_iff, inv_inv]; simpa [mul_assoc] using hx)
  constructor
  · exact key y hy x
  · intro hx
    have := key y⁻¹ (inv_mem hy) _ hx
    simpa [mul_assoc] using this

@[expose] def perp (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ Ω ∧ J ≤ normalizer (K : Set G)}

@[expose] def xPerp (Ω : Set (Subgroup G)) (K : Subgroup G) : Subgroup G :=
  sSup (perp Ω K)

omit [Finite G] in
theorem xPerp_le_normalizer (K : Subgroup G) : xPerp Ω K ≤ normalizer (K : Set G) :=
  sSup_le fun _ hJ => hJ.2

omit [Finite G] in
theorem perp_inv (hΩ : Assumption41 Ω) (K : Subgroup G) :
    ∀ J ∈ perp Ω K, ∀ x ∈ normalizer (K : Set G), rightConjugate J x ∈ perp Ω K := by
  rintro J ⟨hJ, hJK⟩ x hx
  refine ⟨hΩ.conj_mem J hJ x, (rightConjugate_le_rightConjugate hJK x).trans ?_⟩
  rw [← normalizer_rightConjugate, (rightConjugate_eq_self_iff K x).mpr hx]

omit [Finite G] in
theorem normalizer_le_normalizer_xPerp (hΩ : Assumption41 Ω) (K : Subgroup G) :
    normalizer (K : Set G) ≤ normalizer (xPerp Ω K : Set G) :=
  le_normalizer_sSup (perp_inv hΩ K)

theorem MinCounter.not_normal_member {S : Subgroup G} (hM : MinCounter Ω S) {J : Subgroup G}
    (hJ : J ∈ Ω) : ¬ J.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hJn
  have hΩ := hM.assumption
  obtain ⟨K₀, -, hall⟩ := hM.single
  have hall' : ∀ L ∈ Ω, L = J := by
    intro L hL
    obtain ⟨g, rfl⟩ := hall J hJ
    obtain ⟨h, rfl⟩ := hall L hL
    rw [← rightConjugate_eq_of_normal hJn (g⁻¹ * h), rightConjugate_mul]
    group
  have hJtop : J = ⊤ := by
    rw [← hΩ.generates]
    exact le_antisymm (le_sSup hJ) (sSup_le fun L hL => (hall' L hL).le)
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 J
  have hTtop : T = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨o, ho, r, hr, rfl⟩ := hM.twoNil J hJ T hT x (hJtop ▸ mem_top x)
    rw [hJtop, oddCoreIn_top_eq_bot hΩ.oddCore, mem_bot] at ho
    rw [ho, one_mul]
    exact hr
  have hStop : S = ⊤ := (hM.sylow.eq_of_le le_top le_top (hTtop ▸ hT.isPGroup)).symm
  apply hM.not_normal
  rw [hStop]
  exact sec4W_normal_of_rot_le hΩ fun _ _ _ _ _ _ => le_top

theorem MinCounter.xPerp_ne_top {S : Subgroup G} (hM : MinCounter Ω S) {J : Subgroup G}
    (hJ : J ∈ Ω) : xPerp Ω J ≠ ⊤ := fun h =>
  hM.not_normal_member hJ (normalizer_eq_top_iff.mp (eq_top_iff.mpr (h ▸ xPerp_le_normalizer J)))

theorem MinCounter.rot_le_o22In_xPerp {S : Subgroup G} (hM : MinCounter Ω S) {J K T U : Subgroup G}
    (hJ : J ∈ Ω) (hK : K ∈ perp Ω J) (hT : IsSylowOf 2 T K) (hU : IsDihedralRot U T) :
    U ≤ o22In (xPerp Ω J) :=
  hM.rot_le_o22In (hM.xPerp_ne_top hJ) (fun _ hL => hL.1)
    (fun L hL x hx => perp_inv hM.assumption J L hL x (xPerp_le_normalizer J hx)) rfl hK hT hU

omit [Finite G] in
theorem mem_normalizer_centralizer_of_mem_normalizer {U : Subgroup G} {y : G}
    (hy : y ∈ normalizer (U : Set G)) : y ∈ normalizer (centralizer (U : Set G) : Set G) := by
  rw [mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hc u hu
    have hu' : y⁻¹ * u * y ∈ U := by
      have := (mem_normalizer_iff.mp (inv_mem hy) u).mp hu
      simpa using this
    have h := hc _ hu'
    calc u * (y * c * y⁻¹) = y * ((y⁻¹ * u * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * u * y)) * y⁻¹ := by rw [h]
      _ = y * c * y⁻¹ * u := by group
  · intro hc u hu
    have hu' : y * u * y⁻¹ ∈ U := (mem_normalizer_iff.mp hy u).mp hu
    have h := hc _ hu'
    calc u * c = y⁻¹ * ((y * u * y⁻¹) * (y * c * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * c * y⁻¹) * (y * u * y⁻¹)) * y := by rw [h]
      _ = c * u := by group

theorem normalizer_rot_le (hΩ : Assumption41 Ω) {K R U : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylowOf 2 R K) (hU : IsDihedralRot U R) :
    normalizer (U : Set G) ≤ normalizer (K : Set G) := by
  obtain ⟨z, hzU, hz1, hzz, hzu, -⟩ := hU.exists_involution
  intro y hy
  apply Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hK) (hR.le (hU.le hzU))
    hz1 hzz
  rw [mem_centralizer_singleton_iff]
  have h1 : y * z * y⁻¹ ∈ U := (mem_normalizer_iff.mp hy z).mp hzU
  have h2 : y * z * y⁻¹ * (y * z * y⁻¹) = 1 := by
    calc y * z * y⁻¹ * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  rcases hzu _ h1 h2 with h | h
  · exact absurd (by simpa using h) hz1
  · calc y * z = y * z * y⁻¹ * y := by group
      _ = z * y := by rw [h]

theorem MinCounter.oddCoreIn_normalizer_le {S : Subgroup G} (hM : MinCounter Ω S)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hJK : J ≤ normalizer (K : Set G))
    (hKJ : K ≤ normalizer (J : Set G)) :
    oddCoreIn (normalizer (K : Set G)) ≤ oddCoreIn (normalizer (J : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hAodd := odd_card_oddCoreIn (normalizer (K : Set G))
  have hNA := le_normalizer_oddCoreIn (normalizer (K : Set G))
  have hNB := le_normalizer_oddCoreIn (normalizer (J : Set G))
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 J
  obtain ⟨E, hET, hE2, hE4⟩ := Assumption41.exists_fourGroup hΩ hJ hT
  have hAJ : oddCoreIn (normalizer (K : Set G)) ≤ normalizer (J : Set G) :=
    le_of_fourGroup hE2 hE4 hAodd ((hET.trans (hT.le.trans hJK)).trans hNA) fun e he he1 =>
      inf_le_right.trans (Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ)
        (hT.le (hET he)) he1 (hE2 e he))
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  have hUK : U ≤ K := hU.le.trans hR.le
  have hUo : U ≤ o22In (xPerp Ω J) := hM.rot_le_o22In_xPerp hJ ⟨hK, hKJ⟩ hR hU
  have hXJ := xPerp_le_normalizer (Ω := Ω) J
  have hNX := normalizer_le_normalizer_xPerp hΩ J
  have hC : oddCoreIn (normalizer (K : Set G)) ⊓ centralizer (U : Set G) ≤
      oddCoreIn (normalizer (J : Set G)) := by
    refine le_trans ?_ (CFSG.ComponentClassification.Asc76.L26.lemma29_subgroup (hUK.trans hKJ)
      (hU.isPGroup.to_le hU.le) fun x hx =>
      o22In_subgroupOf_le hXJ hNX (show (x : G) ∈ o22In (xPerp Ω J) from hUo hx))
    apply le_oddCoreIn_of_le_normalizer (inf_le_inf hAJ (Subgroup.centralizer_le_normalizer _))
    · intro y hy
      exact inf_le_normalizer_inf ⟨hNA (normalizer_rot_le hΩ hK hR hU (mem_inf.mp hy).2),
        mem_normalizer_centralizer_of_mem_normalizer (mem_inf.mp hy).2⟩
    · exact hAodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hc : ∀ u ∈ U, ∀ k ∈ oddCoreIn (normalizer (K : Set G)), k⁻¹ * u * k * u⁻¹ ∈
      oddCoreIn (normalizer (K : Set G)) ⊓ oddCoreIn (normalizer (J : Set G)) := by
    intro u hu k hk
    have hkA : k⁻¹ * u * k * u⁻¹ ∈ oddCoreIn (normalizer (K : Set G)) := by
      have h1 : u * k * u⁻¹ ∈ oddCoreIn (normalizer (K : Set G)) :=
        (mem_normalizer_iff.mp (hNA (le_normalizer (hUK hu))) k).mp hk
      have : k⁻¹ * u * k * u⁻¹ = k⁻¹ * (u * k * u⁻¹) := by group
      rw [this]
      exact mul_mem (inv_mem hk) h1
    have hko : k⁻¹ * u * k * u⁻¹ ∈ o22In (xPerp Ω J) := by
      have h1 : k⁻¹ * u * k⁻¹⁻¹ ∈ o22In (xPerp Ω J) :=
        conj_mem_o22In (hNX (hAJ (inv_mem hk))) (hUo hu)
      rw [inv_inv] at h1
      exact mul_mem h1 (inv_mem (hUo hu))
    exact ⟨hkA, oddCoreIn_le_oddCoreIn_of_le hXJ hNX (inf_o22In_le_oddCoreIn hAodd ⟨hkA, hko⟩)⟩
  intro a ha
  obtain ⟨n, hn, c, hcA, hcU, rfl⟩ := exists_mul_centralizer_of_commutator_mem
    (T := U) (X := oddCoreIn (normalizer (K : Set G)))
    (N := oddCoreIn (normalizer (K : Set G)) ⊓ oddCoreIn (normalizer (J : Set G)))
    (hU.isPGroup.to_le hU.le) (hAodd.of_dvd_nat (card_dvd_of_le inf_le_left)) inf_le_left
    (fun x hx => inf_le_normalizer_inf ⟨le_normalizer hx, hNB (hAJ hx)⟩)
    (fun u hu => inf_le_normalizer_inf ⟨hNA (le_normalizer (hUK hu)),
      hNB (hKJ (hUK hu))⟩) hc ha
  exact mul_mem (mem_inf.mp hn).2 (hC ⟨hcA, hcU⟩)

theorem oddCoreIn_rightConjugate_eq (X : Subgroup G) (g : G) :
    oddCoreIn (rightConjugate X g) = rightConjugate (oddCoreIn X) g := by
  set e := X.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  rw [rightConjugate, rightConjugate, oddCoreIn, oddCoreIn,
    ← CFSG.ComponentClassification.Asc76.L26.oddCore_map_mulEquiv e, Subgroup.map_map,
    Subgroup.map_map]
  rfl

theorem oddCoreIn_normalizer_rightConjugate (K : Subgroup G) (g : G) :
    oddCoreIn (normalizer (rightConjugate K g : Set G)) =
      rightConjugate (oddCoreIn (normalizer (K : Set G))) g := by
  rw [normalizer_rightConjugate, oddCoreIn_rightConjugate_eq]

omit [Finite G] in
theorem normal_of_forall_rightConjugate {H : Subgroup G} (h : ∀ g : G, rightConjugate H g = H) :
    H.Normal :=
  ⟨fun n hn g => by
    have : n ∈ rightConjugate H g := (h g).symm ▸ hn
    rwa [mem_rightConjugate_iff] at this⟩

@[expose] def DAdj (Ω : Set (Subgroup G)) (K J : Subgroup G) : Prop :=
  K ∈ Ω ∧ J ∈ Ω ∧ J ≤ normalizer (K : Set G) ∧ K ≤ normalizer (J : Set G)

omit [Finite G] in
theorem DAdj.symm {K J : Subgroup G} (h : DAdj Ω K J) : DAdj Ω J K :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

@[expose] def DConnected (Ω : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Ω, ∀ J ∈ Ω, Relation.ReflTransGen (DAdj Ω) K J

theorem MinCounter.oddCoreIn_normalizer_eq {S : Subgroup G} (hM : MinCounter Ω S)
    {K J : Subgroup G} (h : Relation.ReflTransGen (DAdj Ω) K J) :
    oddCoreIn (normalizer (K : Set G)) = oddCoreIn (normalizer (J : Set G)) := by
  induction h with
  | refl => rfl
  | tail _ hab ih =>
    exact ih.trans (le_antisymm
      (hM.oddCoreIn_normalizer_le hab.1 hab.2.1 hab.2.2.1 hab.2.2.2)
      (hM.oddCoreIn_normalizer_le hab.2.1 hab.1 hab.2.2.2 hab.2.2.1))

theorem MinCounter.oddCoreIn_normalizer_eq_bot {S : Subgroup G} (hM : MinCounter Ω S)
    (hconn : DConnected Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    oddCoreIn (normalizer (K : Set G)) = ⊥ := by
  have hΩ := hM.assumption
  have hn : (oddCoreIn (normalizer (K : Set G))).Normal := normal_of_forall_rightConjugate
    fun g => by
      rw [← oddCoreIn_normalizer_rightConjugate]
      exact (hM.oddCoreIn_normalizer_eq (hconn K hK _ (hΩ.conj_mem K hK g))).symm
  apply le_bot_iff.mp
  rw [← oddCoreIn_top_eq_bot hΩ.oddCore]
  exact le_oddCoreIn_of_le_normalizer le_top (normalizer_eq_top_iff.mpr hn).ge
    (odd_card_oddCoreIn _)

theorem IsRot.rightConjugate (hΩ : Assumption41 Ω) {U : Subgroup G} (hU : IsRot Ω U) (g : G) :
    IsRot Ω (AschbacherTightEmbedding.rightConjugate U g) := by
  obtain ⟨K, hK, R, hR, hUR, hUc, hUi⟩ := hU
  refine ⟨AschbacherTightEmbedding.rightConjugate K g, hΩ.conj_mem K hK g,
    AschbacherTightEmbedding.rightConjugate R g, ?_,
    rightConjugate_le_rightConjugate hUR g, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isSylowOf_rightConjugate hR g
  · obtain ⟨ρ, hρ⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top U).mp hUc
    rw [← hρ, AschbacherTightEmbedding.rightConjugate, MonoidHom.map_zpowers]
    infer_instance
  · rw [relIndex_rightConjugate, hUi]

omit [Finite G] in
theorem isPGroup_closure_of_commute {X : Set G} (hX : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : IsPGroup 2 (closure X) := by
  have hcomm := isMulCommutative_closure (k := X) (fun x hx y hy _ => hc x hx y hy)
  have key : ∀ x ∈ closure X, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx => exact hX x hx
    | one => exact ⟨0, by simp⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨k, hk⟩ := ihx
      obtain ⟨l, hl⟩ := ihy
      have hxy : Commute x y := congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      refine ⟨k + l, ?_⟩
      rw [hxy.mul_pow, pow_add, pow_mul, hk, one_pow, one_mul, mul_comm (2 ^ k), pow_mul, hl,
        one_pow]
    | inv x hx ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k, by rw [inv_pow, hk, inv_one]⟩
  rintro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := key x hx
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem sec4W_normal_of_commute (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (h : ∀ U U' : Subgroup G, IsRot Ω U → IsRot Ω U' → ∀ u ∈ U, ∀ u' ∈ U', u * u' = u' * u) :
    (sec4W Ω S).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Set G := {x | ∃ U : Subgroup G, IsRot Ω U ∧ x ∈ U} with hXdef
  have hX2 : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    rintro x ⟨U, ⟨K, -, R, hR, hUR, -, -⟩, hx⟩
    obtain ⟨k, hk⟩ := hR.isPGroup ⟨x, hUR hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    rintro x ⟨U, hU, hx⟩ y ⟨U', hU', hy⟩
    exact h U U' hU hU' x hx y hy
  have hXn : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X := by
    rintro x ⟨U, hU, hx⟩ g
    refine ⟨AschbacherTightEmbedding.rightConjugate U g⁻¹, hU.rightConjugate hΩ g⁻¹, ?_⟩
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hx
  have hQ2 := isPGroup_closure_of_commute hX2 hXc
  have hQn := closure_normal_of_conj hXn
  have hQS : closure X ≤ S := by
    have h1 := hS.eq_of_le (le_sup_left : S ≤ S ⊔ closure X) le_top
      (IsPGroup.to_sup_of_normal_right hS.isPGroup hQ2)
    exact h1 ▸ le_sup_right
  exact sec4W_normal_of_rot_le hΩ fun J hJ T U hT hU u hu =>
    hQS (subset_closure ⟨U, isRot_of hJ hT hU, hu⟩)

theorem MinCounter.commute_rot_of_reflTransGen {S : Subgroup G} (hM : MinCounter Ω S)
    (hO : ∀ K ∈ Ω, oddCoreIn (normalizer (K : Set G)) = ⊥) {a c : Subgroup G}
    (h : Relation.ReflTransGen (DAdj Ω) a c) (hc : c ∈ Ω) :
    a ∈ Ω → ∀ T U T' U' : Subgroup G, IsSylowOf 2 T a → IsDihedralRot U T → IsSylowOf 2 T' c →
      IsDihedralRot U' T' → ∀ u ∈ U, ∀ u' ∈ U', u * u' = u' * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hP : ∀ b ∈ Ω, IsPGroup 2 (o22In (xPerp Ω b)) := fun b hb =>
    isPGroup_o22In (le_bot_iff.mp ((oddCoreIn_le_oddCoreIn_of_le (xPerp_le_normalizer b)
      (normalizer_le_normalizer_xPerp hΩ b)).trans (hO b hb).le))
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ T U T' U' hT hU hT' hU' u hu u' hu'
    exact commute_of_rot hΩ (hP c hc) (isRot_of hc hT hU) (isRot_of hc hT' hU')
      (hM.rot_le_o22In_xPerp hc ⟨hc, le_normalizer⟩ hT hU)
      (hM.rot_le_o22In_xPerp hc ⟨hc, le_normalizer⟩ hT' hU') hu hu'
  | head hab hbc ih =>
    rename_i a' b'
    intro ha T U T' U' hT hU hT' hU' u hu u' hu'
    obtain ⟨Tb, hTb⟩ := exists_isSylowOf 2 b'
    obtain ⟨Ub, hUb⟩ := Assumption41.exists_rot hΩ hab.2.1 hTb
    have hU'b : U' ≤ normalizer (b' : Set G) := by
      refine le_trans ?_ (normalizer_rot_le hΩ hab.2.1 hTb hUb)
      intro x hx
      apply Subgroup.centralizer_le_normalizer
      rw [mem_centralizer_iff]
      intro y hy
      exact ih hab.2.1 Tb Ub T' U' hTb hUb hT' hU' y hy x hx
    have hUP : U ≤ o22In (xPerp Ω b') :=
      hM.rot_le_o22In_xPerp hab.2.1 ⟨ha, hab.2.2.2⟩ hT hU
    have hU'P : U' ≤ normalizer (o22In (xPerp Ω b') : Set G) :=
      hU'b.trans ((normalizer_le_normalizer_xPerp hΩ b').trans
        (normalizer_le_normalizer_o22In _))
    have h2 : IsPGroup 2 (U' ⊔ o22In (xPerp Ω b') : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' (hT'.isPGroup.to_le hU'.le) (hP b' hab.2.1) hU'P
    exact commute_of_rot hΩ h2 (isRot_of ha hT hU) (isRot_of hc hT' hU')
      (hUP.trans le_sup_right) le_sup_left hu hu'

theorem MinCounter.not_dConnected {S : Subgroup G} (hM : MinCounter Ω S) : ¬ DConnected Ω := by
  intro hconn
  have hΩ := hM.assumption
  have hO : ∀ K ∈ Ω, oddCoreIn (normalizer (K : Set G)) = ⊥ := fun K hK =>
    hM.oddCoreIn_normalizer_eq_bot hconn hK
  apply hM.not_normal
  apply sec4W_normal_of_commute hΩ hM.sylow
  intro U U' hU hU'
  obtain ⟨K, hK, R, hR, hUR⟩ := hU.exists_isDihedralRot hΩ
  obtain ⟨K', hK', R', hR', hUR'⟩ := hU'.exists_isDihedralRot hΩ
  exact hM.commute_rot_of_reflTransGen hO (hconn K hK K' hK') hK' hK R U R' U' hR hUR hR' hUR'

end CFSG.ComponentClassification.Asc76.Sec4
