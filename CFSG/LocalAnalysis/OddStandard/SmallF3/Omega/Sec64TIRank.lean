module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64TI
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Quot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem relIndex_eq_card_of_quotEquivTo [Finite G] {R H : Subgroup G} {F : Type} [Group F]
    (hQ : QuotEquivTo R (R ⊓ H) F) : H.relIndex R = Nat.card F := by
  obtain ⟨φ, hsurj, hker⟩ := hQ
  have hcardφ : Nat.card ↥R = Nat.card ↥((R ⊓ H).subgroupOf R) * Nat.card F := by
    rw [← Subgroup.card_ker_mul_card_range φ, hker, MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.card_top]
  have hsub : Nat.card ↥((R ⊓ H).subgroupOf R) = Nat.card ↥(R ⊓ H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hsub] at hcardφ
  have hlag := sec64_card_eq R H
  have hmul : Nat.card ↥(R ⊓ H) * Nat.card F = Nat.card ↥(R ⊓ H) * H.relIndex R := by
    rw [← hcardφ, hlag]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul.symm

private theorem eq_one_or_eq_of_sq_eq_one [Finite G] {U : Subgroup G} (hU : IsCyclic ↥U)
    {y u : G} (hyU : y ∈ U) (hy : orderOf y = 2) (huU : u ∈ U) (hu : u ^ 2 = 1) :
    u = 1 ∨ u = y := by
  rcases eq_or_ne u 1 with h | h
  · exact Or.inl h
  · refine Or.inr (sec64_unique_inv hU huU hyU ?_ hy)
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) h
    · exact h2

private theorem sq_conj (a y : G) : (a * y * a⁻¹) ^ 2 = a * y ^ 2 * a⁻¹ := by
  simp only [pow_two]
  group

private theorem natCard_le_three_of_injective {α G : Type*} [Group G] {f : α → G}
    {a b c : G} (h : ∀ z, f z = a ∨ f z = b ∨ f z = c) (hf : Function.Injective f) :
    Nat.card α ≤ 3 := by
  classical
  let g : α → ({a, b, c} : Finset G) := fun z => ⟨f z, by
    rcases h z with h1 | h1 | h1 <;> simp [h1]⟩
  have hg : Function.Injective g := fun z w hzw => hf (congrArg Subtype.val hzw)
  calc Nat.card α ≤ Nat.card ({a, b, c} : Finset G) := Nat.card_le_card_of_injective g hg
    _ = ({a, b, c} : Finset G).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 3 := Finset.card_le_three

private theorem exists_mul_eq_of_mem [Finite G] {U V R : Subgroup G}
    (hUR : U ≤ R) (hVR : V ≤ R) (hdisj : U ⊓ V = ⊥)
    (hcardU : Nat.card ↥U = 4) (hcardV : Nat.card ↥V = 4) (hcardR : Nat.card ↥R = 16) :
    ∀ r ∈ R, ∃ u ∈ U, ∃ v ∈ V, u * v = r := by
  let φ : ↥U × ↥V → ↥R := fun p => ⟨p.1 * p.2, mul_mem (hUR p.1.2) (hVR p.2.2)⟩
  have hφ : Function.Injective φ := fun p q hp =>
    Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hdisj) (congrArg Subtype.val hp)
  have hcardUV : Nat.card (↥U × ↥V) = Nat.card ↥R := by
    rw [Nat.card_prod, hcardU, hcardV, hcardR]
  haveI : Fintype (↥U × ↥V) := Fintype.ofFinite _
  haveI : Fintype ↥R := Fintype.ofFinite _
  have hcard' : Fintype.card (↥U × ↥V) = Fintype.card ↥R := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardUV
  have hsurj : Function.Surjective φ :=
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard')).mp hφ
  intro r hr
  obtain ⟨p, hp⟩ := hsurj ⟨r, hr⟩
  exact ⟨p.1, p.1.2, p.2, p.2.2, congrArg Subtype.val hp⟩

private theorem ti_elemAbelian_card_le [Finite G] (hout : Asc82Outside) {T H : Subgroup G}
    {x y : G} (c : Sec64Cfg T H x y)
    (hcard : 4 ≤ Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H))
    (hTR : ¬ T ≤ centralizer ({y} : Set G))
    (hQ : QuotEquivTo (T ⊓ centralizer ({y} : Set G)) (T ⊓ centralizer ({y} : Set G) ⊓ H)
      (Multiplicative (ZMod 4))) :
    ∀ E : Subgroup G, E ≤ T → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4 := by
  intro E hET hE
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := T ⊓ centralizer ({y} : Set G) with hR
  set U : Subgroup G := R ⊓ H with hU
  have hrel : H.relIndex R = 4 := by
    rw [relIndex_eq_card_of_quotEquivTo hQ, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hUle : Nat.card ↥U ≤ H.relIndex R := sec64_ti_index hout c hcard hTR
  have hUcard : Nat.card ↥U = 4 := le_antisymm (by rw [hrel] at hUle; exact hUle) hcard
  have hRcard : Nat.card ↥R = 16 := by
    rw [sec64_card_eq R H, hUcard, hrel]
  obtain ⟨s, hsT, hsy⟩ := Set.not_subset.mp hTR
  obtain ⟨hdisj, hVle, hcomm⟩ := sec64_ti_conj hout c hcard hsT hsy
  set V : Subgroup G := CFSG.conjugate U s with hV
  have hVcard : Nat.card ↥V = 4 := by
    rw [hV, CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj s⁻¹).injective, hUcard]
  have hsurj := exists_mul_eq_of_mem (U := U) (V := V) (R := R) inf_le_left hVle hdisj
    hUcard hVcard hRcard
  set y' : G := s⁻¹ * y * s with hy'
  have hy'V : y' ∈ V := by
    rw [hV, CFSG.conjugate]
    exact Subgroup.mem_map.mpr ⟨y, c.mem_U, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hy'.symm⟩
  have hy'2 : orderOf y' = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hy']
      have hy2 : y ^ 2 = 1 := by simpa [c.hy] using pow_orderOf_eq_one y
      have hconj : (s⁻¹ * y * s) ^ 2 = s⁻¹ * y ^ 2 * s := by simpa using sq_conj s⁻¹ y
      rw [hconj, hy2]
      group
    · intro h1
      have hy1 : y = s * y' * s⁻¹ := by rw [hy']; group
      rw [h1, mul_one, mul_inv_cancel] at hy1
      have : orderOf y = 1 := orderOf_eq_one_iff.mpr hy1
      rw [c.hy] at this
      norm_num at this
  have hv_cases : ∀ v ∈ V, v ^ 2 = 1 → v = 1 ∨ v = y' := by
    intro v hVv hv2
    rw [hV, CFSG.conjugate] at hVv
    obtain ⟨u₀, hu₀U, hu₀eq⟩ := Subgroup.mem_map.mp hVv
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hu₀eq
    have hu₀2 : u₀ ^ 2 = 1 := by
      have hconj : (s⁻¹ * u₀ * s) ^ 2 = s⁻¹ * u₀ ^ 2 * s := by simpa using sq_conj s⁻¹ u₀
      rw [hu₀eq, hv2] at hconj
      calc u₀ ^ 2 = s * (s⁻¹ * u₀ ^ 2 * s) * s⁻¹ := by group
        _ = s * 1 * s⁻¹ := by rw [← hconj]
        _ = 1 := by rw [mul_one, mul_inv_cancel]
    rcases eq_one_or_eq_of_sq_eq_one c.hU c.mem_U c.hy hu₀U hu₀2 with h | h
    · left; rw [← hu₀eq, h]; group
    · right; rw [← hu₀eq, h]
  have hchar : ∀ z : G, z ∈ R → z ≠ 1 → z ^ 2 = 1 → z = y ∨ z = y' ∨ z = y * y' := by
    intro z hzR hz1 hz2
    obtain ⟨u, huU, v, hVv, huv⟩ := hsurj z hzR
    have hsq : (u * v) ^ 2 = u ^ 2 * v ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      calc u * v * (u * v) = u * (v * u) * v := by group
        _ = u * (u * v) * v := by rw [hcomm u huU v hVv]
        _ = u * u * (v * v) := by group
    have h1 : u ^ 2 * v ^ 2 = 1 := by rw [← hsq, huv]; exact hz2
    have hu2 : u ^ 2 = 1 := by
      have heq : u ^ 2 = (v ^ 2)⁻¹ := by
        calc u ^ 2 = u ^ 2 * v ^ 2 * (v ^ 2)⁻¹ := by group
          _ = 1 * (v ^ 2)⁻¹ := by rw [h1]
          _ = (v ^ 2)⁻¹ := one_mul _
      exact Subgroup.mem_bot.mp (by
        rw [← hdisj]
        exact Subgroup.mem_inf.mpr ⟨pow_mem huU 2, heq ▸ V.inv_mem (pow_mem hVv 2)⟩)
    have hv2 : v ^ 2 = 1 := by
      have heq : v ^ 2 = (u ^ 2)⁻¹ := by
        calc v ^ 2 = (u ^ 2)⁻¹ * (u ^ 2 * v ^ 2) := by group
          _ = (u ^ 2)⁻¹ * 1 := by rw [h1]
          _ = (u ^ 2)⁻¹ := mul_one _
      exact Subgroup.mem_bot.mp (by
        rw [← hdisj]
        exact Subgroup.mem_inf.mpr ⟨heq ▸ U.inv_mem (pow_mem huU 2), pow_mem hVv 2⟩)
    rcases eq_one_or_eq_of_sq_eq_one c.hU c.mem_U c.hy huU hu2 with hu1 | hu1
    · rcases hv_cases v hVv hv2 with hv1 | hv1
      · exact absurd (by rw [← huv, hu1, hv1, one_mul] : z = 1) hz1
      · exact Or.inr (Or.inl (by rw [← huv, hu1, hv1, one_mul]))
    · rcases hv_cases v hVv hv2 with hv1 | hv1
      · exact Or.inl (by rw [← huv, hu1, hv1, mul_one])
      · exact Or.inr (Or.inr (by rw [← huv, hu1, hv1]))
  have hEp : IsPGroup 2 ↥E := c.isPGroup.to_le hET
  by_cases hER : E ≤ R
  · exact sec63_elem_le_of_quot_z4 c.hU hQ E hER hE
  · have hyC_false : y ∉ E ⊓ centralizer ({y} : Set G) := by
      intro hyC
      apply hER
      intro e he
      refine Subgroup.mem_inf.mpr ⟨hET he, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hyE : y ∈ E := (Subgroup.mem_inf.mp hyC).1
      haveI : IsMulCommutative ↥E := hE.1
      have hc := mul_comm' (⟨e, he⟩ : ↥E) (⟨y, hyE⟩ : ↥E)
      exact congrArg Subtype.val hc
    have hCea : CFSG.Open.IsElemAbelian 2 (E ⊓ centralizer ({y} : Set G)) :=
      CFSG.Open.IsElemAbelian.mono hE inf_le_left
    have hCcard3 : Nat.card ↥(E ⊓ centralizer ({y} : Set G)) ≤ 3 := by
      refine natCard_le_three_of_injective (a := (1 : G)) (b := y') (c := y * y')
        (f := fun z : ↥(E ⊓ centralizer ({y} : Set G)) => (z : G)) (fun z => ?_)
        Subtype.val_injective
      rcases eq_or_ne (z : G) 1 with h1 | h1
      · exact Or.inl h1
      · rcases hchar z.1 (Subgroup.mem_inf.mpr ⟨hET (Subgroup.mem_inf.mp z.2).1,
            (Subgroup.mem_inf.mp z.2).2⟩) h1 (hE.2 z.1 (Subgroup.mem_inf.mp z.2).1) with h | h | h
        · exfalso
          exact hyC_false (by simpa [h] using z.2)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    have hCcard2 : Nat.card ↥(E ⊓ centralizer ({y} : Set G)) ≤ 2 := by
      have hCp : IsPGroup 2 ↥(E ⊓ centralizer ({y} : Set G)) :=
        hEp.to_le inf_le_left
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hCp
      rw [hj] at hCcard3
      have hjle1 : j ≤ 1 := by
        by_contra h
        have h2 : 2 ≤ j := by omega
        have h4 : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h2
        norm_num at h4
        omega
      rw [hj]
      calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hjle1
        _ = 2 := by norm_num
    have hθ_mem : ∀ e : ↥E, (e : G) * y * (e : G)⁻¹ ∈ R := by
      intro e
      by_cases heR : (e : G) ∈ R
      · have hcomm_ey : (e : G) * y = y * (e : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp heR).2
        have heqy : (e : G) * y * (e : G)⁻¹ = y := by rw [hcomm_ey]; group
        rw [heqy]
        exact Subgroup.mem_inf.mpr ⟨c.hyT, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      · have hse : (e : G)⁻¹ ∈ T := T.inv_mem (hET e.2)
        have hsy' : (e : G)⁻¹ ∉ centralizer ({y} : Set G) := by
          intro h
          exact heR (Subgroup.mem_inf.mpr ⟨hET e.2,
            (Subgroup.centralizer ({y} : Set G)).inv_mem_iff.mp h⟩)
        have hle := (sec64_ti_conj hout c hcard hse hsy').2.1
        exact hle (Subgroup.mem_map.mpr ⟨y, c.mem_U, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩)
    have hθ_ne : ∀ e : ↥E, (e : G) * y * (e : G)⁻¹ ≠ 1 := by
      intro e h1
      have hy1 : y = 1 := by
        calc y = (e : G)⁻¹ * ((e : G) * y * (e : G)⁻¹) * (e : G) := by group
          _ = (e : G)⁻¹ * 1 * (e : G) := by rw [h1]
          _ = 1 := by group
      have : orderOf y = 1 := orderOf_eq_one_iff.mpr hy1
      rw [c.hy] at this
      norm_num at this
    have hθ_sq : ∀ e : ↥E, ((e : G) * y * (e : G)⁻¹) ^ 2 = 1 := by
      intro e
      have hy2 : y ^ 2 = 1 := by simpa [c.hy] using pow_orderOf_eq_one y
      have hconj : ((e : G) * y * (e : G)⁻¹) ^ 2 = (e : G) * y ^ 2 * (e : G)⁻¹ :=
        sq_conj (e : G) y
      rw [hconj, hy2]
      group
    let θ : ↥E → {z : G // z ∈ R ∧ z ≠ 1 ∧ z ^ 2 = 1} :=
      fun e => ⟨(e : G) * y * (e : G)⁻¹, hθ_mem e, hθ_ne e, hθ_sq e⟩
    have hθwell : ∀ a b : ↥E, QuotientGroup.leftRel
        ((E ⊓ centralizer ({y} : Set G)).subgroupOf E) a b → θ a = θ b := by
      intro a b hab
      have hmem : a⁻¹ * b ∈ (E ⊓ centralizer ({y} : Set G)).subgroupOf E :=
        QuotientGroup.leftRel_apply.mp hab
      have hCmem : ((a⁻¹ * b : ↥E) : G) ∈ E ⊓ centralizer ({y} : Set G) :=
        Subgroup.mem_subgroupOf.mp hmem
      have hcomm_aby : (((a⁻¹ * b : ↥E) : G)) * y = y * (((a⁻¹ * b : ↥E) : G)) :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hCmem).2
      apply Subtype.ext
      have hcoe : ((a⁻¹ * b : ↥E) : G) = (a : G)⁻¹ * (b : G) := by simp
      rw [hcoe] at hcomm_aby
      have hb : (b : G) = (a : G) * ((a : G)⁻¹ * (b : G)) := by group
      have key : (b : G) * y * (b : G)⁻¹ = (a : G) * y * (a : G)⁻¹ := by
        have hwy : ((a : G)⁻¹ * (b : G)) * y = y * ((a : G)⁻¹ * (b : G)) := hcomm_aby
        rw [hb]
        calc (a : G) * ((a : G)⁻¹ * (b : G)) * y * ((a : G) * ((a : G)⁻¹ * (b : G)))⁻¹
            = (a : G) * (((a : G)⁻¹ * (b : G)) * y) * ((a : G)⁻¹ * (b : G))⁻¹
                * (a : G)⁻¹ := by group
          _ = (a : G) * y * (a : G)⁻¹ := by rw [hwy]; group
      exact key.symm
    let g : (↥E ⧸ (E ⊓ centralizer ({y} : Set G)).subgroupOf E) →
        {z : G // z ∈ R ∧ z ≠ 1 ∧ z ^ 2 = 1} := Quotient.lift θ hθwell
    have hginj : Function.Injective g := by
      intro q₁ q₂
      refine Quotient.inductionOn₂ q₁ q₂ (fun a b hq => ?_)
      have hval : (a : G) * y * (a : G)⁻¹ = (b : G) * y * (b : G)⁻¹ :=
        congrArg Subtype.val hq
      have hw : ((a : G)⁻¹ * (b : G)) * y = y * ((a : G)⁻¹ * (b : G)) := by
        have h2 := congrArg (fun t => (a : G)⁻¹ * t * (b : G)) hval
        have h2' : y * ((a : G)⁻¹ * (b : G)) = ((a : G)⁻¹ * (b : G)) * y := by
          calc y * ((a : G)⁻¹ * (b : G))
              = (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * (b : G) := by group
            _ = (a : G)⁻¹ * ((b : G) * y * (b : G)⁻¹) * (b : G) := h2
            _ = ((a : G)⁻¹ * (b : G)) * y := by group
        exact h2'.symm
      have hcoe : ((a⁻¹ * b : ↥E) : G) = (a : G)⁻¹ * (b : G) := by simp
      refine QuotientGroup.eq.mpr ?_
      refine Subgroup.mem_subgroupOf.mpr ?_
      refine Subgroup.mem_inf.mpr ⟨(a⁻¹ * b).2, ?_⟩
      rw [hcoe]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hw
    have hquot : (E ⊓ centralizer ({y} : Set G)).relIndex E ≤ 3 :=
      natCard_le_three_of_injective (f := fun q => (g q : G))
        (fun q => hchar (g q).1 (g q).2.1 (g q).2.2.1 (g q).2.2.2)
        (fun q₁ q₂ h => hginj (Subtype.ext h))
    have hEcard : Nat.card ↥E = (E ⊓ centralizer ({y} : Set G)).relIndex E
        * Nat.card ↥(E ⊓ centralizer ({y} : Set G)) := by
      have h := Subgroup.relIndex_mul_card (H := E ⊓ centralizer ({y} : Set G)) (K := E)
      rw [inf_eq_left.mpr inf_le_left] at h
      exact h.symm
    have hle6 : Nat.card ↥E ≤ 6 := by
      rw [hEcard]
      calc (E ⊓ centralizer ({y} : Set G)).relIndex E
            * Nat.card ↥(E ⊓ centralizer ({y} : Set G)) ≤ 3 * 2 :=
            Nat.mul_le_mul hquot hCcard2
        _ = 6 := by norm_num
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
    rw [hk] at hle6
    have hk2 : k ≤ 2 := by
      by_contra h
      have h3 : 3 ≤ k := by omega
      have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h3
      norm_num at h8
      omega
    calc Nat.card ↥E = 2 ^ k := hk
      _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num

theorem sec64_ti_rank [Finite G] (hout : Asc82Outside) {T H : Subgroup G} {x y : G}
    (c : Sec64Cfg T H x y) (hcard : 4 ≤ Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H))
    (hTR : ¬ T ≤ centralizer ({y} : Set G))
    (hQ : QuotEquivTo (T ⊓ centralizer ({y} : Set G)) (T ⊓ centralizer ({y} : Set G) ⊓ H)
      (Multiplicative (ZMod 4))) : CFSG.Open.pRank 2 T = 2 := by
  have hne : x ≠ y := by
    intro h
    exact c.hxH (h ▸ c.hyH)
  refine le_antisymm ?_ (sec64_two_le_pRank c.hx c.hy c.hxy hne c.hxT c.hyT)
  refine CFSG.SectionRank.pRank_le (p := 2) (k := 2) (by norm_num) ?_
  intro E hET hE
  simpa using ti_elemAbelian_card_le hout c hcard hTR hQ E hET hE

theorem sec64_case_ti [Finite G] (hout : Asc82Outside) {T H : Subgroup G} {x y : G}
    (c : Sec64Cfg T H x y) (halt : Sec64Tri T H y)
    (hcard : 4 ≤ Nat.card ↥(T ⊓ centralizer ({y} : Set G) ⊓ H))
    (hTR : ¬ T ≤ centralizer ({y} : Set G)) : Sec64Out T H y := by
  unfold Sec64Tri at halt
  unfold Sec64Out
  left
  rcases halt with h | ⟨-, hQ⟩ | hQ
  · exfalso
    have h1 := sec64_ti_index hout c hcard hTR
    omega
  · exact (sec64_ti_not_e4 hout c hcard hTR hQ).elim
  · exact sec64_ti_rank hout c hcard hTR hQ

end CFSG.OddStandard.SmallF3.Omega
