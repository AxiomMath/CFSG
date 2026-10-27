module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Census
public import CFSG.Sporadic.Co1.Cover.Final
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Endgame
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

theorem exists_index_two {Z : Type*} [Group Z] [Finite Z] (hcomm : ∀ a b : Z, a * b = b * a)
    (h : 2 ∣ Nat.card Z) : ∃ O : Subgroup Z, O.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup Z := { ‹Group Z› with mul_comm := hcomm }
  set k := (Nat.card Z).factorization 2 with hk
  let P : Subgroup Z := (powMonoidHom (2 ^ k) : Z →* Z).range
  have hQ : IsPGroup 2 (Z ⧸ P) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H z =>
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨z, rfl⟩
  obtain ⟨z₂, hz₂⟩ := exists_prime_orderOf_dvd_card' 2 h
  have hz₂P : z₂ ∉ P := by
    rintro ⟨y, hy⟩
    have hN0 : Nat.card Z ≠ 0 := Nat.card_pos.ne'
    have hpow : (y ^ (2 ^ k)) ^ (ordCompl[2] (Nat.card Z)) = 1 := by
      rw [← pow_mul, Nat.ordProj_mul_ordCompl_eq_self, pow_card_eq_one']
    have hodd : Odd (ordCompl[2] (Nat.card Z)) :=
      Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hN0))
    have h1 := hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
    rw [show y ^ (2 ^ k) = z₂ from hy, hz₂] at h1
    exact absurd h1 (by decide)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hQ
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hz₂P
    have h1 : Nat.card (Z ⧸ P) = 1 := by rw [hn, pow_zero]
    have h2 : (z₂ : Z ⧸ P) = 1 := (Nat.card_eq_one_iff_unique.mp h1).1.elim _ _
    exact (QuotientGroup.eq_one_iff z₂).mp h2
  obtain ⟨M, hM⟩ := Sylow.exists_subgroup_card_pow_prime (G := Z ⧸ P) 2 (n := n - 1)
    (by rw [hn]; exact pow_dvd_pow 2 (Nat.sub_le n 1))
  refine ⟨M.comap (QuotientGroup.mk' P), ?_⟩
  rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective P)]
  have h1 := M.card_mul_index
  rw [hM, hn] at h1
  have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)]
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h1

theorem odd_card_center_of_lift' (h32 : AS76b.Lemma32) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (hA : AS76b.Hyp31 A) {W : Type*} [Group W]
    {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A ⊤ ψ)
    (hZbar : center (↥A ⧸ center ↥A) = ⊥) {Q : W → Prop}
    (hlift : ∀ (L : Type) [Group L] [Finite L], commutator L = ⊤ → ∀ ζ : L, orderOf ζ = 2 →
      ζ ∈ center L → ∀ π : L →* W, Function.Surjective π → π.ker = zpowers ζ → ∀ v : L,
        orderOf (π v) = 2 → Q (π v) → v ^ 2 = ζ)
    (hQ1 : ¬ Q 1) {t : normalizer (A : Set G)} (ht2 : (t : G) ^ 2 = 1) (hQ : Q (ψ t)) :
    Odd (Nat.card (center ↥A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hZ
  have hZ2 : 2 ∣ Nat.card (center ↥A) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hZ)
  obtain ⟨O₀, hO₀⟩ := exists_index_two (fun a b : center ↥A => Subtype.ext
    (mem_center_iff.mp b.2 a)) hZ2
  set O : Subgroup ↥A := O₀.map (center ↥A).subtype with hO
  have hOZ : O ≤ center ↥A := map_subtype_le O₀
  have hOn : O.Normal := ⟨fun x hx g => by
    have hc := mem_center_iff.mp (hOZ hx) g
    rwa [hc, mul_inv_cancel_right]⟩
  have hmemO : ∀ z : center ↥A, (z : ↥A) ∈ O ↔ z ∈ O₀ := fun z =>
    ⟨fun ⟨y, hy, hyz⟩ => by rwa [← Subtype.ext hyz], fun h => ⟨z, h, rfl⟩⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z : center ↥A, z ∉ O₀ := by
    by_contra hall
    push Not at hall
    have htop : O₀ = ⊤ := eq_top_iff.mpr fun z _ => hall z
    rw [htop, index_top] at hO₀
    exact absurd hO₀ (by decide)
  have hz₂O : (z₂ : ↥A) ∉ O := fun h => hz₂ ((hmemO z₂).mp h)
  have hcoset : ∀ z : center ↥A, z ∉ O₀ → z₂⁻¹ * z ∈ O₀ := fun z hz =>
    (mul_mem_iff_of_index_two hO₀).mpr (by rw [inv_mem_iff]; tauto)
  have hcL : center (↥A ⧸ O) = (center ↥A).map (QuotientGroup.mk' O) :=
    center_quot_eq_map hZbar hOZ
  have hperf : commutator (↥A ⧸ O) = ⊤ := by
    have hAp : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hA.standard.1.1
    exact (Group.isPerfect_def).1
      (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O))
  set ζ : ↥A ⧸ O := QuotientGroup.mk' O (z₂ : ↥A) with hζ
  have hζC : ζ ∈ center (↥A ⧸ O) := by
    rw [hcL]
    exact ⟨z₂, z₂.2, rfl⟩
  have hζ1 : ζ ≠ 1 := by
    rw [hζ, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hz₂O
  have hζ2 : orderOf ζ = 2 := by
    refine orderOf_eq_prime ?_ hζ1
    rw [hζ, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← SubgroupClass.coe_pow]
    exact (hmemO _).mpr (sq_mem_of_index_two hO₀ z₂)
  let ψA : ↥A →* W := ψ.comp (inclusion le_normalizer)
  have hψA : ∀ a : ↥A, ψA a = ψ ⟨a, le_normalizer a.2⟩ := fun _ => rfl
  have hkerA : ψA.ker = center ↥A := by
    ext a
    rw [MonoidHom.mem_ker, hψA, hψ.eq_one_iff, mem_center_iff, mem_centralizer_iff]
    constructor
    · intro h g
      exact Subtype.ext (h g g.2)
    · intro h g hg
      exact congrArg Subtype.val (h ⟨g, hg⟩)
  have hOker : O ≤ ψA.ker := hkerA ▸ hOZ
  let π : ↥A ⧸ O →* W := QuotientGroup.lift O ψA hOker
  have hπ : ∀ a : ↥A, π (QuotientGroup.mk' O a) = ψ ⟨a, le_normalizer a.2⟩ := fun _ => rfl
  have hπs : Function.Surjective π := by
    intro x
    obtain ⟨a, ha, hae⟩ := hψ.exists_eq x (mem_top _)
    exact ⟨QuotientGroup.mk' O ⟨a, ha⟩, by rw [hπ]; exact hae⟩
  have hπk : π.ker = zpowers ζ := by
    rw [QuotientGroup.ker_lift, hkerA]
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      by_cases hzO : (⟨z, hz⟩ : center ↥A) ∈ O₀
      · have : QuotientGroup.mk' O z = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact (hmemO ⟨z, hz⟩).mpr hzO
        rw [this]
        exact one_mem _
      · have h1 := hcoset _ hzO
        have : QuotientGroup.mk' O z = ζ := by
          rw [hζ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
          have := inv_mem ((hmemO _).mpr h1)
          simpa using this
        rw [this]
        exact mem_zpowers ζ
    · rw [zpowers_le]
      exact ⟨z₂, z₂.2, rfl⟩
  obtain ⟨a, ha, hat⟩ := hψ.exists_eq (ψ t) (mem_top _)
  have hψt2 : ψ t ^ 2 = 1 := by
    rw [← map_pow, show t ^ 2 = 1 from Subtype.ext (by simpa using ht2), map_one]
  have hψt1 : ψ t ≠ 1 := fun h1 => hQ1 (h1 ▸ hQ)
  have hord : orderOf (ψ t) = 2 := orderOf_eq_prime hψt2 hψt1
  set v : ↥A ⧸ O := QuotientGroup.mk' O ⟨a, ha⟩ with hv
  have hπv : π v = ψ t := by rw [hv, hπ]; exact hat
  have hv2 : v ^ 2 = ζ := hlift _ hperf ζ hζ2 hζC π hπs hπk v (hπv ▸ hord) (hπv ▸ hQ)
  have ha2O : (⟨a, ha⟩ : ↥A) ^ 2 ∉ O := by
    intro h
    apply hζ1
    rw [← hv2, hv, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h
  have ha2Z : (⟨a, ha⟩ : ↥A) ^ 2 ∈ center ↥A := by
    rw [← hkerA, MonoidHom.mem_ker, map_pow, hψA]
    show ψ ⟨a, le_normalizer ha⟩ ^ 2 = 1
    rw [hat, hψt2]
  have ha2 : Even (orderOf ((⟨a, ha⟩ : ↥A) ^ 2)) := by
    by_contra hodd
    obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hodd
    apply ha2O
    set z : center ↥A := ⟨_, ha2Z⟩ with hz
    have hzo : orderOf z = 2 * j + 1 := by rw [Subgroup.orderOf_mk]; exact hj
    have hzz : z = (z ^ (j + 1)) ^ 2 := by
      rw [← pow_mul, show (j + 1) * 2 = 2 * j + 1 + 1 by ring, pow_succ, ← hzo,
        pow_orderOf_eq_one, one_mul]
    have h1 : z ∈ O₀ := by
      rw [hzz]
      exact sq_mem_of_index_two hO₀ _
    exact (hmemO z).mpr h1
  set c : G := a⁻¹ * t with hc
  have hcK : c ∈ centralizer (A : Set G) := by
    have h1 : ψ ((⟨a, le_normalizer ha⟩ : normalizer (A : Set G))⁻¹ * t) = 1 := by
      rw [map_mul, map_inv, hat, inv_mul_cancel]
    simpa using (hψ.eq_one_iff _).mp h1
  have hac : Commute a c := mem_centralizer_iff.mp hcK a ha
  have hc2 : c ^ 2 = (a ^ 2)⁻¹ := by
    have h1 : (a * c) ^ 2 = 1 := by rw [hc, mul_inv_cancel_left]; exact ht2
    rw [hac.mul_pow] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hc4 : 4 ∣ orderOf c := by
    apply four_dvd_orderOf_of_even
    rw [hc2, orderOf_inv]
    have := ha2
    rwa [← Subgroup.orderOf_coe, SubgroupClass.coe_pow] at this
  set x := c ^ (orderOf c / 4) with hx
  have hx4 : orderOf x = 4 := orderOf_pow_orderOf_div (orderOf_pos c).ne' hc4
  have hxK : x ∈ centralizer (A : Set G) := pow_mem hcK _
  have hxP : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  have hsq := sq_eq_one_of_isPGroup_zpowers (h32 G A hA) hxK hxP
  have := orderOf_dvd_of_pow_eq_one hsq
  rw [hx4] at this
  exact absurd this (by norm_num)

theorem isCo1TwoB_of_isConj
    {s t : Blueprint.NativeSporadic.Co1} (hs : CFSG.Monster.GMS.IsCo1TwoB s) (h : IsConj s t) :
    CFSG.Monster.GMS.IsCo1TwoB t := by
  obtain ⟨hord, hcard, hq⟩ := hs
  obtain ⟨h1, h2, -⟩ := CFSG.Monster.GMS.co1Inv_isConj_invariants h
  have hempty : {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act s v = v ∧
      CFSG.Sporadic.Co1.Module.q₀ v = 1} = ∅ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hv hq1
    have := hq v hv
    rw [hq1] at this
    exact absurd this (by decide)
  refine ⟨?_, h1 ▸ hcard, fun v hv => ?_⟩
  · obtain ⟨c, hc⟩ := h
    rw [← SemiconjBy.orderOf_eq _ hc]
    exact hord
  · by_contra hne
    have hv1 : CFSG.Sporadic.Co1.Module.q₀ v = 1 := by
      have key : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
      exact key _ hne
    have hmem : v ∈ {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act t v = v ∧
        CFSG.Sporadic.Co1.Module.q₀ v = 1} := ⟨hv, hv1⟩
    rw [hempty, Set.ncard_empty] at h2
    rw [(Set.ncard_eq_zero (Set.toFinite _)).mp h2.symm] at hmem
    exact hmem

theorem isCo1TwoB_co1E1 :
    CFSG.Monster.GMS.IsCo1TwoB co1E1 := by
  have h1 : conjB * A₁ * conjB⁻¹ =
      ((co1MatEquiv CFSG.Sporadic.Co1.Module.TwoB.sBc : GA) : GL24) := by
    rw [conjB_conj, mul_inv_cancel_right]
  have hconj : co1MatEquiv.symm ⟨conjB, conjB_mem⟩ * co1E1 *
      (co1MatEquiv.symm ⟨conjB, conjB_mem⟩)⁻¹ = CFSG.Sporadic.Co1.Module.TwoB.sBc := by
    apply co1ι_injective
    rw [map_mul, map_mul, map_inv, co1ι_symm, co1ι_co1E1, co1ι_apply]
    exact h1
  have hc : IsConj co1E1 CFSG.Sporadic.Co1.Module.TwoB.sBc := isConj_iff.mpr ⟨_, hconj⟩
  exact isCo1TwoB_of_isConj CFSG.Monster.GMS.isCo1TwoB_sBc hc.symm

theorem co1_twoB_lift
    (L : Type) [Group L] [Finite L] (hL : commutator L = ⊤)
    (ζ : L) (hζ : orderOf ζ = 2) (hζc : ζ ∈ center L) (π : L →* Blueprint.NativeSporadic.Co1)
    (hπ : Function.Surjective π) (hk : π.ker = zpowers ζ) (v : L) (hv : orderOf (π v) = 2)
    (hQ : CFSG.Monster.GMS.IsCo1TwoB (π v)) : v ^ 2 = ζ := by
  classical
  have hv2 : v ^ 2 ∈ zpowers ζ := by
    rw [← hk, MonoidHom.mem_ker, map_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hv)
  obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hv2)
  rw [hζ, Finset.mem_range] at hi
  interval_cases i
  ·
    exfalso
    rw [pow_zero] at hie
    have hvv : v * v = 1 := by rw [← pow_two, ← hie]
    obtain ⟨K, hK⟩ := CFSG.Sporadic.Co1.Cover.co1DoubleCoverTwoB L π ζ hπ hk hζc hζ ⟨v, hvv, hQ⟩
    have hKc : Nat.card K = Nat.card Blueprint.NativeSporadic.Co1 := Nat.card_eq_of_bijective _ hK
    have hLc : Nat.card L = Nat.card Blueprint.NativeSporadic.Co1 * 2 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, hk,
        Nat.card_zpowers, hζ]
    have hK2 : K.index = 2 := by
      have h1 := K.card_mul_index
      rw [hKc, hLc] at h1
      have hpos : 0 < Nat.card Blueprint.NativeSporadic.Co1 := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos h1
    have htop : K = ⊤ := by
      have h1 : commutator L ≤ K := Cert.commutator_le_of_index_two hK2
      rw [hL] at h1
      exact eq_top_iff.mpr h1
    rw [htop, index_top] at hK2
    exact absurd hK2 (by decide)
  · rw [pow_one] at hie
    exact hie.symm

theorem co1_odd_card_center
    (h32 : AS76b.Lemma32) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (hA : AS76b.Hyp31 A)
    (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .Co1)
    {ψ : normalizer (A : Set G) →* Blueprint.NativeSporadic.Co1} (hψ : IsActionHom A ⊤ ψ)
    {t : normalizer (A : Set G)} (ht2 : (t : G) ^ 2 = 1)
    (hQ : CFSG.Monster.GMS.IsCo1TwoB (ψ t)) : Odd (Nat.card (center ↥A)) := by
  let e' : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Co1 := e
  have hZbar : center (↥A ⧸ center ↥A) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e' x ∈ center Blueprint.NativeSporadic.Co1 := by
      rw [mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := e'.surjective y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hx z)]
    rw [center_co1, mem_bot] at h1
    rw [mem_bot]
    exact e'.injective (h1.trans (map_one e').symm)
  refine odd_card_center_of_lift' h32 hA hψ hZbar co1_twoB_lift ?_ ht2 hQ
  intro h1
  have := h1.1
  rw [orderOf_one] at this
  exact absurd this (by decide)

end CFSG.ComponentClassification.RankTwoSporadic.Co1
