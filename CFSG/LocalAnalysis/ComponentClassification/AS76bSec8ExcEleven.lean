module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcEight
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcRoot

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3 JData)
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)

section Eleven

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}

theorem sec3_of_conj_ne (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G))) {y : G}
    (hQ : rightConjugate R y ≤ centralizer (R : Set G)) (hne : rightConjugate R y ≠ R) :
    Sec3 A R (rightConjugate R y) y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hA, hR, fun hyN => hne ?_, AschbacherTheorem3.isSylowOf_rightConjugate hR y, hQ⟩
  have hKy : rightConjugate (centralizer (A : Set G)) y = centralizer (A : Set G) := by
    rw [← centralizer_rightConjugate, (rightConjugate_eq_self_iff A y).2 hyN]
  have hQK : rightConjugate R y ≤ centralizer (A : Set G) := by
    rw [← hKy]
    exact map_mono hR.le
  have hQN : rightConjugate R y ≤ normalizer (R : Set G) := fun q hq =>
    centralizer_le_normalizer _ (hQ hq)
  have hRp : IsPGroup 2 R := hR.isPGroup
  have hQp : IsPGroup 2 (rightConjugate R y) := hRp.map (MulAut.conj y⁻¹).toMonoidHom
  have hp : IsPGroup 2 ↥(R ⊔ rightConjugate R y) :=
    IsPGroup.to_sup_of_normal_left' (H := R) (K := rightConjugate R y) hRp hQp hQN
  have h1 : R ⊔ rightConjugate R y = R := hR.eq_of_le le_sup_left (sup_le hR.le hQK) hp
  have h2 : rightConjugate R y ≤ R := le_sup_right.trans h1.le
  exact Subgroup.eq_of_le_of_card_ge h2 (rightConjugate_card R y).ge

variable {C : Type} [Group C] {ψ : normalizer (A : Set G) →* MulAut C}
  (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

theorem exists_sec3_otherClass (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {reps : List C} (hcover : ClassesCover reps)
    (hJ : ∀ y ∈ reps, ∃ Z u, CentreData y Z ∧ Regular Z u ∧ SylowData y Z)
    (hres : ∀ y ∈ reps, ResidualMem y) (hchar : ∀ y ∈ reps, CharTwo y)
    {x₀ : C} (hT : ActsIn ψ T (zx x₀)) {a : C} (hfus : FusionData (zx x₀) a) {P : Set C}
    (hP : OtherClass (zx x₀) a P) :
    ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ ∃ s ∈ T', s ≠ 1 ∧
      ∃ (hsN : s ∈ normalizer (A : Set G)) (w : C), w ∈ P ∧ ψ ⟨s, hsN⟩ = MulAut.conj w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  set Z := zx x₀ with hZdef
  have hTel := hc.elemT h32
  have hact : ∀ (R' T' : Subgroup G) (g' : G), Sec3 A R' T' g' → ∀ t ∈ T', t ≠ 1 →
      ∀ (htN : t ∈ normalizer (A : Set G)) (x : C), ψ ⟨t, htN⟩ = MulAut.conj x →
        ActsIn ψ T' (zx x) := fun R' T' g' hc' t ht ht1 htN x hx =>
    actsIn_zx_of_reps hZC hψ h4 h32 h34 hc' hOut hZA hcover hres hchar ht ht1 htN hx
  have himg : ∀ t ∈ T, ∃ (htN : t ∈ normalizer (A : Set G)) (z : C), z ∈ Z ∧
      ψ ⟨t, htN⟩ = MulAut.conj z ∧ (t ≠ 1 → z ≠ 1) := by
    intro t ht
    have htN := hc.le_normalizer ht
    obtain ⟨z, hz⟩ := exists_conj_of_mem hψ hc h32 h4 h34 ht htN
    exact ⟨htN, z, (actsIn_iff.1 hT) t ht htN z hz, hz,
      (involution_of_conj hZC hψ hc h32 ht htN hz).2⟩
  have hpart : ∀ t ∈ T, ∃ p ∈ A, t⁻¹ * p ∈ R := fun t ht => hc.exists_aPart h32 h4 h34 ht
  obtain ⟨â, hâ, hâψ⟩ := hψ.exists_eq (MulAut.conj a) ⟨a, rfl⟩
  have hâN := le_normalizer hâ
  set T₂ := rightConjugate T â⁻¹ with hT₂def
  have hmemT₂ : ∀ u, u ∈ T₂ ↔ â⁻¹ * u * â ∈ T := by
    intro u
    rw [hT₂def, mem_rightConjugate_iff, inv_inv]
  have himg₂ : ∀ u ∈ T₂, ∃ (huN : u ∈ normalizer (A : Set G)) (z : C), z ∈ Z ∧
      ψ ⟨u, huN⟩ = MulAut.conj (a * z * a⁻¹) ∧ (u ≠ 1 → z ≠ 1) := by
    intro u hu
    have hu' := (hmemT₂ u).1 hu
    obtain ⟨htN, z, hzZ, hz, hz1⟩ := himg _ hu'
    have huN : u ∈ normalizer (A : Set G) := by
      have h1 := mul_mem (mul_mem hâN htN) (inv_mem hâN)
      rwa [show â * (â⁻¹ * u * â) * â⁻¹ = u by group] at h1
    refine ⟨huN, z, hzZ, ?_, fun hu1 hz' => ?_⟩
    · have e : (⟨u, huN⟩ : normalizer (A : Set G)) =
          ⟨â, hâN⟩ * ⟨â⁻¹ * u * â, htN⟩ * ⟨â, hâN⟩⁻¹ := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group)
      rw [e, map_mul, map_mul, map_inv, hâψ, hz]
      simp only [map_mul, map_inv]
    · refine hz1 (fun h1 => hu1 ?_) hz'
      calc u = â * (â⁻¹ * u * â) * â⁻¹ := by group
        _ = 1 := by rw [h1]; group
  have hRA : ∀ r ∈ R, ∀ b ∈ A, r * b = b * r := fun r hr b hb =>
    (mem_centralizer_iff.1 (hc.sylowR.le hr) b hb).symm
  have hRR : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := fun r hr r' hr' =>
    congrArg Subtype.val ((hc.elemR h32).1.is_comm.comm ⟨r, hr⟩ ⟨r', hr'⟩)
  have hTT₂ : ∀ t ∈ T, ∀ u ∈ T₂, t * u = u * t := by
    intro t ht u hu
    have hu' := (hmemT₂ u).1 hu
    obtain ⟨p, hpA, hp⟩ := hpart t ht
    obtain ⟨p', hp'A, hp'⟩ := hpart _ hu'
    obtain ⟨htN, z, hzZ, hz, -⟩ := himg t ht
    obtain ⟨htN', z', hz'Z, hz', -⟩ := himg _ hu'
    have hpψ : ψ ⟨p, le_normalizer hpA⟩ = MulAut.conj z := by
      have h1 : ψ ⟨t⁻¹ * p, mul_mem (inv_mem htN) (le_normalizer hpA)⟩ = 1 :=
        (hψ.eq_one_iff _).2 (hc.sylowR.le hp)
      rw [psi_mul (inv_mem htN) (le_normalizer hpA), psi_inv htN, inv_mul_eq_one] at h1
      rw [← h1, hz]
    have hp'ψ : ψ ⟨p', le_normalizer hp'A⟩ = MulAut.conj z' := by
      have h1 : ψ ⟨(â⁻¹ * u * â)⁻¹ * p', mul_mem (inv_mem htN') (le_normalizer hp'A)⟩ = 1 :=
        (hψ.eq_one_iff _).2 (hc.sylowR.le hp')
      rw [psi_mul (inv_mem htN') (le_normalizer hp'A), psi_inv htN', inv_mul_eq_one] at h1
      rw [← h1, hz']
    set q := â * p' * â⁻¹ with hq
    have hqA : q ∈ A := mul_mem (mul_mem hâ hp'A) (inv_mem hâ)
    have hqψ : ψ ⟨q, le_normalizer hqA⟩ = MulAut.conj (a * z' * a⁻¹) := by
      have e : (⟨q, le_normalizer hqA⟩ : normalizer (A : Set G)) =
          ⟨â, hâN⟩ * ⟨p', le_normalizer hp'A⟩ * ⟨â, hâN⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hâψ, hp'ψ]
      simp only [map_mul, map_inv]
    have hp2 : p ^ 2 = 1 := by
      have hcomm : Commute t (t⁻¹ * p) := hc.commute_T_R ht hp
      have e : p = t * (t⁻¹ * p) := by group
      rw [e, hcomm.mul_pow, hTel.2 t ht, (hc.elemR h32).2 _ hp, one_mul]
    have hpq : p * q = q * p :=
      (commute_of_conj_commute hψ hZ hqA hpA hp2 hqψ hpψ (hfus.commute z hzZ z' hz'Z).symm).symm
    set r₁ := (t⁻¹ * p)⁻¹ with hr₁
    set r₂ := ((â⁻¹ * u * â)⁻¹ * p')⁻¹ with hr₂
    have hr₁R : r₁ ∈ R := inv_mem hp
    have hr₂R : r₂ ∈ R := inv_mem hp'
    have ht' : t = p * r₁ := by rw [hr₁]; group
    have hâr₂ : â * r₂ * â⁻¹ = r₂ := by rw [← hRA r₂ hr₂R â hâ, mul_inv_cancel_right]
    have hu'' : u = q * r₂ := by
      have h1 : u = â * (p' * r₂) * â⁻¹ := by rw [hr₂]; group
      rw [h1, hq]
      calc â * (p' * r₂) * â⁻¹ = â * p' * â⁻¹ * (â * r₂ * â⁻¹) := by group
        _ = â * p' * â⁻¹ * r₂ := by rw [hâr₂]
    rw [ht', hu'']
    have c1 : Commute p r₂ := (hRA r₂ hr₂R p hpA).symm
    have c2 : Commute r₁ q := hRA r₁ hr₁R q hqA
    have c3 : Commute r₁ r₂ := hRR r₁ hr₁R r₂ hr₂R
    exact ((Commute.mul_right hpq c1).mul_left (c2.mul_right c3)).eq
  have hTinf : ∀ t ∈ T, t ∈ T₂ → t = 1 := by
    intro t ht ht₂
    by_contra ht1
    obtain ⟨htN, z, hzZ, hz, hz1⟩ := himg t ht
    obtain ⟨htN', z', hz'Z, hz', -⟩ := himg₂ t ht₂
    have h1 : z = a * z' * a⁻¹ := hinj (hz.symm.trans hz')
    exact hz1 ht1 (hfus.inf_eq z hzZ z' hz'Z h1)
  have hTAg : ∀ t ∈ T, t ∈ rightConjugate A g → t = 1 := by
    intro t ht htAg
    have htK : t ∈ rightConjugate (centralizer (A : Set G)) g := hc.sylowT.le ht
    rw [mem_rightConjugate_iff] at htAg htK
    have hodd : Odd (orderOf (g * t * g⁻¹)) :=
      RankTwoL3Even.odd_orderOf_of_mem hZ (mem_inf.2 ⟨htAg, htK⟩)
    have h1 : g * t * g⁻¹ = 1 := RankTwoL3Even.eq_one_of_odd_of_pow_two hodd (k := 1)
      (by rw [pow_one, conj_pow, hTel.2 t ht, mul_one, mul_inv_cancel])
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨⟨t₁, ht₁⟩, ht₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc.T_ne_bot
  have ht₁1' : t₁ ≠ 1 := fun h => ht₁1 (Subtype.ext h)
  obtain ⟨t₂, ht₂, ht₂1, ht₂₁⟩ : ∃ t₂ ∈ T, t₂ ≠ 1 ∧ t₂ ≠ t₁ := by
    by_contra hcon
    push Not at hcon
    have hsub : (T : Set G) ⊆ {1, t₁} := fun s hs => by
      by_cases hs1 : s = 1
      · exact Or.inl hs1
      · exact Or.inr (hcon s hs hs1)
    have hcard : Nat.card T ≤ 2 := by
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
    have h4T : 4 ≤ Nat.card T := by rw [hc.card_eq]; exact hc.four_le
    omega
  have hT₂ne : T₂ ≠ ⊥ := by
    intro h
    apply hc.T_ne_bot
    have h1 := rightConjugate_card T â⁻¹
    rw [← hT₂def, h, card_bot] at h1
    exact card_eq_one.1 h1.symm
  obtain ⟨⟨u₀, hu₀⟩, hu₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hT₂ne
  have hu₀1' : u₀ ≠ 1 := fun h => hu₀1 (Subtype.ext h)
  obtain ⟨t, ht, ht1, hsAg⟩ : ∃ t ∈ T, t ≠ 1 ∧ t * u₀ ∉ rightConjugate A g := by
    by_contra hcon
    push Not at hcon
    have h1 := mul_mem (hcon t₁ ht₁ ht₁1') (inv_mem (hcon t₂ ht₂ ht₂1))
    rw [show t₁ * u₀ * (t₂ * u₀)⁻¹ = t₁ * t₂⁻¹ by group] at h1
    have h2 := hTAg _ (mul_mem ht₁ (inv_mem ht₂)) h1
    exact ht₂₁ (by rw [mul_inv_eq_one] at h2; exact h2.symm)
  set s := t * u₀ with hsdef
  obtain ⟨htN, z, hzZ, hz, hz1⟩ := himg t ht
  obtain ⟨hu₀N, z', hz'Z, hz', hz'1⟩ := himg₂ u₀ hu₀
  have hsN : s ∈ normalizer (A : Set G) := mul_mem htN hu₀N
  have hsψ : ψ ⟨s, hsN⟩ = MulAut.conj (z * (a * z' * a⁻¹)) := by
    show ψ ⟨t * u₀, mul_mem htN hu₀N⟩ = _
    rw [psi_mul htN hu₀N, hz, hz', ← map_mul]
  have hwP : z * (a * z' * a⁻¹) ∈ P := hP z hzZ (hz1 ht1) z' hz'Z (hz'1 hu₀1')
  have hw1 : z * (a * z' * a⁻¹) ≠ 1 := by
    intro h
    have hz'2 : z' * z' = 1 := hz'Z.2.2
    have h1 : z = a * z' * a⁻¹ := by
      have h2 : z = (a * z' * a⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [h2]
      have hz'i : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
      simp only [mul_inv_rev, inv_inv, hz'i, mul_assoc]
    exact hz1 ht1 (hfus.inf_eq z hzZ z' hz'Z h1)
  set R'' := rightConjugate T g⁻¹ with hR''
  set T'' := rightConjugate T₂ g⁻¹ with hT''
  set h := g * â⁻¹ * g⁻¹ with hh
  have hsw := hc.swap
  have hT''eq : T'' = rightConjugate T (â⁻¹ * g⁻¹) := by
    rw [hT'', hT₂def, rightConjugate_mul]
  have hKh : rightConjugate (centralizer (A : Set G)) h =
      rightConjugate (rightConjugate (centralizer (A : Set G)) g) (â⁻¹ * g⁻¹) := by
    rw [rightConjugate_mul, hh, mul_assoc]
  have hT''R'' : T'' ≤ centralizer (R'' : Set G) := by
    rw [hT'', hR'', centralizer_rightConjugate]
    refine map_mono fun u hu => ?_
    rw [mem_centralizer_iff]
    intro t' ht'
    exact (hTT₂ t' ht' u hu)
  have hT''inf : R'' ⊓ T'' = ⊥ := by
    rw [hR'', hT'', ← RankTwoClassical.rightConjugate_inf, eq_bot_iff]
    intro v hv
    rw [mem_rightConjugate_iff] at hv
    rw [mem_bot]
    have h1 := hTinf _ (mem_inf.1 hv).1 (mem_inf.1 hv).2
    calc v = g * (g⁻¹ * v * g⁻¹⁻¹) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hc'' : Sec3 A R'' T'' h := by
    have hsylT : IsSylowOf 2 T'' (rightConjugate (centralizer (A : Set G)) h) := by
      rw [hT''eq, hKh]
      exact AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowT _
    have hne : T'' ≠ R'' := by
      intro he
      have hT''ne : T'' ≠ ⊥ := by
        intro h0
        apply hT₂ne
        have h1 := rightConjugate_card T₂ g⁻¹
        rw [← hT'', h0, card_bot] at h1
        exact card_eq_one.1 h1.symm
      apply hT''ne
      rw [eq_bot_iff, ← hT''inf]
      exact le_inf (he ▸ le_rfl) le_rfl
    refine ⟨hc.hyp, hsw.sylowR, fun hhN => hne ?_, hsylT, hT''R''⟩
    have hKh' : rightConjugate (centralizer (A : Set G)) h = centralizer (A : Set G) := by
      rw [← centralizer_rightConjugate, (rightConjugate_eq_self_iff A h).2 hhN]
    have hT''K : T'' ≤ centralizer (A : Set G) := hKh' ▸ hsylT.le
    have hT''N : T'' ≤ normalizer (R'' : Set G) := fun q hq =>
      centralizer_le_normalizer _ (hT''R'' hq)
    have hp : IsPGroup 2 ↥(R'' ⊔ T'') :=
      IsPGroup.to_sup_of_normal_left' (H := R'') (K := T'') hsw.sylowR.isPGroup
        hsylT.isPGroup hT''N
    have h1 : R'' ⊔ T'' = R'' :=
      hsw.sylowR.eq_of_le le_sup_left (sup_le hsw.sylowR.le hT''K) hp
    have h2 : T'' ≤ R'' := le_sup_right.trans h1.le
    exact Subgroup.eq_of_le_of_card_ge h2
      (by simp only [hT''eq, hR'', rightConjugate_card, le_refl])
  have hT''A := inf_eq_bot_of_reps hZC hψ h4 h32 h34 hc'' hOut hZA hcover hres
  have hmain := main_of_reps hZC hψ h4 h32 h34 hc'' hZA hcover hJ hact
  obtain ⟨xT, hxT, -⟩ := Lemma36.exists_conj_eq hc''.sylowR hc''.sylowT
  have hV'' := le_sec3V_of (R := R'') (T := T'') ⟨xT, hxT⟩
  set v := g * s * g⁻¹ with hvdef
  have hvV : v ∈ sec3V R'' T'' := by
    have hv2 : v = (g * t * g⁻¹) * (g * u₀ * g⁻¹) := by rw [hvdef, hsdef]; group
    rw [hv2]
    refine hV'' (mul_mem_sup ?_ ?_)
    · rw [hR'', mem_rightConjugate_iff, inv_inv]
      simpa [mul_assoc] using ht
    · rw [hT'', mem_rightConjugate_iff, inv_inv]
      simpa [mul_assoc] using hu₀
  have hv' : g⁻¹ * v * g⁻¹⁻¹ = s := by rw [hvdef, inv_inv]; group
  have hvA : v ∉ A := by
    intro hvA
    apply hsAg
    rw [mem_rightConjugate_iff]
    exact hvA
  obtain ⟨x, hxV, hvx⟩ : ∃ x : G, rightConjugate R'' x ≤ sec3V R'' T'' ∧
      v ∈ rightConjugate R'' x := by
    rcases hmain with ⟨h1, -⟩ | ⟨-, h2, -⟩
    · exfalso
      have hT''le : T'' ≤ A := fun u hu => (mem_inf.1 (h1 ▸ hu)).2
      apply hc''.T_ne_bot
      rw [eq_bot_iff, ← hT''A]
      exact le_inf le_rfl hT''le
    · obtain ⟨x, hxV, hvx, -⟩ := (h2 v hvV).1 hvA
      exact ⟨x, hxV, hvx⟩
  obtain ⟨w, hw, -⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  have hR''w : R'' = rightConjugate R (w * g⁻¹) := by rw [hR'', hw, rightConjugate_mul]
  have hT₂R : T₂ ≤ centralizer (R : Set G) := by
    intro u hu
    rw [mem_centralizer_iff]
    intro r hr
    have h1 : r * (â⁻¹ * u * â) = (â⁻¹ * u * â) * r :=
      mem_centralizer_iff.1 (hc.le_centralizer ((hmemT₂ u).1 hu)) r hr
    have h2 : â * r = r * â := (hRA r hr â hâ).symm
    have h3 : â⁻¹ * r * â = r := by rw [mul_assoc, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
    have hra : Commute r â := h2.symm
    have hb : Commute r (â⁻¹ * u * â) := h1
    have hu : u = â * (â⁻¹ * u * â) * â⁻¹ := by group
    rw [hu]
    exact ((hra.mul_right hb).mul_right hra.inv_right).eq
  have hR₁ : rightConjugate R g⁻¹ = rightConjugate R'' (g * w⁻¹ * g⁻¹) := by
    rw [hR''w, rightConjugate_mul]
    congr 1
    group
  have hR₁C : rightConjugate R g⁻¹ ≤ centralizer ((R'' ⊔ T'' : Subgroup G) : Set G) := by
    refine AS76b.le_centralizer_sup ?_ ?_
    · rw [hR'', centralizer_rightConjugate]
      exact map_mono (le_centralizer_iff.1 hc.le_centralizer)
    · rw [hT'', centralizer_rightConjugate]
      exact map_mono (le_centralizer_iff.1 hT₂R)
  have hR₁W : rightConjugate R g⁻¹ ≤ sec3W R'' T'' := by
    rw [hR₁] at hR₁C ⊢
    exact le_sec3W hR₁C
  have hQC : rightConjugate R'' x ≤ centralizer (rightConjugate R g⁻¹ : Set G) :=
    hxV.trans ((sec3V_le_centralizer R'' T'').trans (centralizer_le hR₁W))
  set y₃ := w * g⁻¹ * x * g with hy₃
  have hQ₃ : rightConjugate (rightConjugate R'' x) g = rightConjugate R y₃ := by
    rw [hR''w, rightConjugate_mul, rightConjugate_mul, hy₃, mul_assoc (w * g⁻¹) x g]
  have hsQ₃ : s ∈ rightConjugate R y₃ := by
    rw [← hQ₃, mem_rightConjugate_iff]
    exact hvx
  have hQ₃C : rightConjugate R y₃ ≤ centralizer (R : Set G) := by
    rw [← hQ₃]
    have h1 := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hQC
    change rightConjugate (rightConjugate R'' x) g ≤
      rightConjugate (centralizer (rightConjugate R g⁻¹ : Set G)) g at h1
    rwa [← centralizer_rightConjugate, RankTwoClassical.rightConjugate_inv_rightConjugate] at h1
  have hsK : s ∉ centralizer (A : Set G) := by
    intro hsK
    apply hw1
    apply hinj
    rw [map_one, ← hsψ]
    exact (hψ.eq_one_iff _).2 hsK
  have hne : rightConjugate R y₃ ≠ R := by
    intro he
    rw [he] at hsQ₃
    exact hsK (hc.sylowR.le hsQ₃)
  refine ⟨rightConjugate R y₃, y₃, sec3_of_conj_ne hc.hyp hc.sylowR hQ₃C hne, s, hsQ₃,
    fun h1 => hsK (by rw [h1]; exact one_mem _), hsN, _, hwP, hsψ⟩

end Eleven

section Assembly

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem exists_config814_of_otherClass (h32 : Lemma32) (h33 : Lemma33Three)
    (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (D : ExcModel A) (hA : Hyp31 A)
    (hZA : Odd (Nat.card (center A))) {C : Type} [Group C] [Finite C] (hZC : center C = ⊥)
    (e : rankTwoQuot A ≃* C) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (q : ℕ) (hq : D.q = q) {reps lreps : List C} (hcover : ClassesCover reps)
    (hcls : ∀ x ∈ reps, ∃ Z, ClassData q x Z ∧ ResidualMem x)
    (hJ : ∀ y ∈ reps, ∃ Z u, CentreData y Z ∧ Regular Z u ∧ SylowData y Z)
    (hD0 : 2 < q → ∀ y ∈ reps, D0Data y (zx y))
    (hlevi : 2 < q → ∀ y ∈ lreps, ∃ Dl Ql Hl Ll : Subgroup C,
      LeviClassData D (zx y) Dl Ql Hl Ll)
    (hother : 2 < q → ∀ y ∈ reps, y ∉ lreps → ∃ a : C, FusionData (zx y) a ∧
      OtherClass (zx y) a {w | ∃ y' ∈ lreps, IsConj y' w})
    (h3 : D.IsTrialityFour → Nat.Coprime 3 (Nat.card (center ↥A))) :
    ∃ (g : G) (R T Q : Subgroup G), Config814 D g R T Q := by
  classical
  have hAp : commutator ↥A = ⊤ := hA.standard.1.1
  obtain ⟨ψ, hψ⟩ := exists_isActionHom (RankTwoHypIIY.autModel_mulAut hZC) hAp e
  have hres : ∀ y ∈ reps, ResidualMem y := fun y hy => (hcls y hy).choose_spec.2
  have hchar : ∀ y ∈ reps, CharTwo y := fun y hy => (hcls y hy).choose_spec.1.charTwo
  have hcard : ∀ y ∈ reps, Nat.card (zx y) = q := fun y hy => by
    obtain ⟨Z, hZ, -⟩ := hcls y hy
    rw [zx_eq_of_centreData hZ.centre, hZ.card]
  obtain ⟨g₀, hg₀, R, T₀, hR, hT₀, -, -, hTR, -, -⟩ := section3Config_of h32 h33 h4 h34 G A hA
  have hc₀ : Sec3 A R T₀ g₀ := ⟨hA, hR, hg₀, hT₀, commutator_eq_bot_iff_le_centralizer.mp hTR⟩
  obtain ⟨T, g, hc, y₀, hy₀, t₁, ht₁T, ht₁1, ht₁N, hψt₁⟩ :=
    exists_pinned hZC hψ h4 h32 h34 hc₀ hcover
  have hT : ActsIn ψ T (zx y₀) :=
    actsIn_zx_of_reps hZC hψ h4 h32 h34 hc hOut hZA hcover hres hchar ht₁T ht₁1 ht₁N hψt₁
  have hq2 : 2 < q := by
    have h1 := card_le_of_actsIn hZC hψ h4 h32 h34 hc hT
    rw [hcard y₀ hy₀] at h1
    have h2 : 4 ≤ Nat.card T := by rw [hc.card_eq]; exact hc.four_le
    omega
  have hqD : 2 < D.q := by rw [hq]; exact hq2
  obtain ⟨T', g', hc', y', hy', hT'⟩ : ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧
      ∃ y' ∈ lreps, ActsIn ψ T' (zx y') := by
    by_cases hy₀l : y₀ ∈ lreps
    · exact ⟨T, g, hc, y₀, hy₀l, hT⟩
    · obtain ⟨a, hfus, hP⟩ := hother hq2 y₀ hy₀ hy₀l
      obtain ⟨T₁, g₁, hc₁, s, hs, hs1, hsN, w, ⟨y', hy', hy'w⟩, hsw⟩ :=
        exists_sec3_otherClass hZC hψ h4 h32 h34 hc hOut hZA hcover hJ hres hchar hT hfus hP
      obtain ⟨b, hb, hc₂, hsT₂, hsN₂, hψs₂⟩ := exists_pin hψ hc₁ hs hsN hsw hy'w
      have hs1' : b * s * b⁻¹ ≠ 1 := by
        intro h
        apply hs1
        calc s = b⁻¹ * (b * s * b⁻¹) * b := by group
          _ = 1 := by rw [h]; group
      exact ⟨_, _, hc₂, y', hy', actsIn_zx_of_reps hZC hψ h4 h32 h34 hc₂ hOut hZA hcover hres hchar
        hsT₂ hs1' hsN₂ hψs₂⟩
  obtain ⟨Dl, Ql, Hl, Ll, hLC⟩ := hlevi hq2 y' hy'
  exact ⟨g', R, T', _, config814_of_pinned hZC hψ h4 h32 h34 D hc' hZA hOut hqD hcover hres hchar
    (hD0 hq2) hT' hLC h3⟩

end Assembly



end CFSG.ComponentClassification.RankTwoExceptional.Exc
