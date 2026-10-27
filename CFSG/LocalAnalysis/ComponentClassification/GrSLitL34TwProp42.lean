module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWBadA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwBounds
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwCentA
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwConjB
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwQ8
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwSmall
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwTrans

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {a x : G} {J S' W K T : Subgroup G} {t : G}
  {ρ : ↥(normalizer (W : Set G)) →* WrE}

private theorem mem_conjugate_iff_p42 {H : Subgroup G} {g x : G} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite G] in
private theorem oddIn_conjugate_p42 (K : Subgroup G) (c : G) :
    oddIn (conjugate K c) = conjugate (oddIn K) c := by
  have h := pPrimeCore_map_iso 2 (K.equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective)
  unfold conjugate oddIn
  rw [← h, map_map, map_map]
  rfl

omit [Finite G] in
private theorem zStarIn_conjugate_p42 (K : Subgroup G) (c : G) :
    zStarIn (conjugate K c) = conjugate (zStarIn K) c := by
  have h := CFSG.ComponentClassification.FooteLit.fusionZStar_map_mulEquiv
    (K.equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective)
  unfold conjugate zStarIn
  rw [← h, map_map, map_map]
  rfl

omit [Finite G] in
private theorem isL34Type_conjugate_p42 {K : Subgroup G} (g : G)
    (h : IsL34Type (↥K ⧸ Open.fusionZStar ↥K)) :
    IsL34Type (↥(conjugate K g) ⧸ Open.fusionZStar ↥(conjugate K g)) := by
  let e : ↥K ≃* ↥(conjugate K g) :=
    K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    (CFSG.ComponentClassification.FooteLit.nonempty_quotient_fusionZStar_equiv e).some h

private theorem isPGroup_zpowers_of_pow_p42 {u : G} {n : ℕ} (hu : u ^ 2 ^ n = 1) :
    IsPGroup 2 (zpowers u) :=
  IsPGroup.of_card_dvd_pow (n := n) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hu)

private theorem mem_normalizer_zpowers_of_comm_p42 (u v : G) (huv : u * v = v * u) :
    u ∈ normalizer ((zpowers v : Subgroup G) : Set G) := by
  have h1 : Commute u v := huv
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have h2 : u * v ^ k * u⁻¹ = v ^ k := by
      rw [(h1.zpow_right k).eq]; group
    rw [h2]; exact zpow_mem (mem_zpowers v) k
  · intro hz
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz
    have h2 : u⁻¹ * v ^ k * u = v ^ k := by
      rw [((h1.inv_left).zpow_right k).eq]; group
    have : z = v ^ k := by
      calc z = u⁻¹ * (u * z * u⁻¹) * u := by group
        _ = u⁻¹ * (v ^ k) * u := by rw [hk]
        _ = v ^ k := h2
    rw [this]; exact zpow_mem (mem_zpowers v) k

private theorem isPGroup_sup_three_p42 {u a y : G} (hu : u ^ 2 ^ 2 = 1) (ha : a ^ 2 ^ 1 = 1)
    (hy : y ^ 2 ^ 1 = 1) (hua : u * a = a * u) (huy : u * y = y * u) (hay : a * y = y * a) :
    IsPGroup 2 ↥(zpowers u ⊔ zpowers a ⊔ zpowers y) := by
  have h1 : IsPGroup 2 ↥(zpowers u ⊔ zpowers a) :=
    (isPGroup_zpowers_of_pow_p42 hu).to_sup_of_normal_right' (isPGroup_zpowers_of_pow_p42 ha)
      (zpowers_le.mpr (mem_normalizer_zpowers_of_comm_p42 u a hua))
  refine h1.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_p42 hy) ?_
  have hle : zpowers u ⊔ zpowers a ≤ centralizer ({y} : Set G) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr huy
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr hay
  intro w hw
  exact mem_normalizer_zpowers_of_comm_p42 w y (mem_centralizer_singleton_iff.mp (hle hw))

private theorem eq_one_of_mem_oddIn_p42 {M : Subgroup G} {o : G} (ho : o ∈ oddIn M)
    (h2 : o * o = 1) : o = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card ↥(oddIn M)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hP : IsPGroup 2 (zpowers o) :=
    isPGroup_zpowers_of_pow_p42 (n := 1) (by rw [pow_one, pow_two]; exact h2)
  have hbot : zpowers o = ⊥ :=
    eq_bot_of_le_two_group_of_le_odd hP hodd le_rfl (zpowers_le.mpr ho)
  have := mem_zpowers o
  rwa [hbot, mem_bot] at this

private theorem conj_comm_p42 {H : Type*} [Group H] (c : H) {p q : H} (h : p * q = q * p) :
    c⁻¹ * p * c * (c⁻¹ * q * c) = c⁻¹ * q * c * (c⁻¹ * p * c) := by
  calc c⁻¹ * p * c * (c⁻¹ * q * c) = c⁻¹ * (p * q) * c := by group
    _ = c⁻¹ * (q * p) * c := by rw [h]
    _ = c⁻¹ * q * c * (c⁻¹ * p * c) := by group

theorem prop42
    (hMax : MaximalTwoComponentInput)
    (h : TwHyp G a x J S' W K T t) (hρ : TwModel (normalizer (W : Set G)) K t ρ)
    (hC : ConcX (imgT T (normalizer (W : Set G)) ρ)) {y : ↥(normalizer (W : Set G))}
    (hy2 : y * y = 1) (hyU : IsUU (ρ y)) (hya : (y : G) * a = a * (y : G)) (g : G) :
    g⁻¹ * a * g ≠ (y : G) := by
  intro hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haord : orderOf a = 2 := h.hset.2.1.1
  have ha2 : a * a = 1 := by
    have h2 : a ^ 2 = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
    rwa [pow_two] at h2
  have hy2' : (y : G) * (y : G) = 1 := congrArg Subtype.val hy2
  have hga : a = g * (y : G) * g⁻¹ := by rw [← hg]; group
  have hCa : centralizer ({a} : Set G) ≤ normalizer (J : Set G) :=
    GrS5S.centralizer_le_normalizer_of_sec4 hMax h.hset
  have hCM : centralizer ({a} : Set G) ≤ normalizer (W : Set G) := hCa.trans h.hNJ
  have hJa : J ≤ centralizer ({a} : Set G) := (gsUnbalancingTriple_iff.mp h.hset.2.1).2.2.2.1
  have hJyy : conjugate J g ≤ centralizer ({(y : G)} : Set G) := by
    intro k hk
    rw [mem_centralizer_singleton_iff]
    have hk' : g * k * g⁻¹ ∈ J := mem_conjugate_iff_p42.mp hk
    have hka : g * k * g⁻¹ * a = a * (g * k * g⁻¹) := mem_centralizer_singleton_iff.mp (hJa hk')
    have h1 : g * (k * (y : G)) * g⁻¹ = g * ((y : G) * k) * g⁻¹ := by
      calc g * (k * (y : G)) * g⁻¹ = g * k * g⁻¹ * (g * (y : G) * g⁻¹) := by group
        _ = g * (y : G) * g⁻¹ * (g * k * g⁻¹) := by rw [← hga]; exact hka
        _ = g * ((y : G) * k) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  have haNJy : a ∈ normalizer ((conjugate J g : Subgroup G) : Set G) := by
    have ha₁ : g * a * g⁻¹ ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * a * g⁻¹ * a = g * a * g⁻¹ * (g * (y : G) * g⁻¹) := by rw [← hga]
        _ = g * (a * (y : G)) * g⁻¹ := by group
        _ = g * ((y : G) * a) * g⁻¹ := by rw [hya]
        _ = g * (y : G) * g⁻¹ * (g * a * g⁻¹) := by group
        _ = a * (g * a * g⁻¹) := by rw [← hga]
    have ha₁N : g * a * g⁻¹ ∈ normalizer (J : Set G) := hCa ha₁
    rw [mem_normalizer_iff]
    intro k
    rw [mem_conjugate_iff_p42, mem_conjugate_iff_p42]
    have h1 := mem_normalizer_iff.mp ha₁N (g * k * g⁻¹)
    have h2 : g * a * g⁻¹ * (g * k * g⁻¹) * (g * a * g⁻¹)⁻¹ = g * (a * k * a⁻¹) * g⁻¹ := by group
    rw [h2] at h1
    exact h1
  have hperfJy : ⁅conjugate J g, conjugate J g⁆ = conjugate J g := by
    unfold conjugate
    rw [← Subgroup.map_commutator, perfect_J h]
  have hLJy : IsL34Type (↥(conjugate J g) ⧸ Open.fusionZStar ↥(conjugate J g)) :=
    isL34Type_conjugate_p42 g h.hset.2.2.1
  have hZJy : zStarIn (conjugate J g) = oddIn (conjugate J g) := by
    rw [zStarIn_conjugate_p42, oddIn_conjugate_p42, zStarIn_eq_oddIn_J h]
  obtain ⟨-, hrank, hperf⟩ := cent_bounds hMax h hρ hC hy2 hyU hya
  obtain ⟨haJy, z, hzJy, q, -, u, huJy, hz2, hz1, huz, hza, hqa⟩ :=
    exists_q8_step (J' := conjugate J g) (a := a) hperfJy hLJy hZJy haNJy ha2
      (fun E hE hEel => hrank E (fun e he => mem_inf.mpr
        ⟨(mem_inf.mp (hE he)).2, hJyy (mem_inf.mp (hE he)).1⟩) hEel)
      (fun H Q _ π hH hπ hQ => hperf H Q π (fun e he => mem_inf.mpr
        ⟨(mem_inf.mp (hH he)).2, hJyy (mem_inf.mp (hH he)).1⟩) hπ hQ)
  have hzC : z ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hza
  have huC : u ∈ centralizer ({a} : Set G) := (mem_inf.mp huJy).2
  have huJ : u ∈ conjugate J g := (mem_inf.mp huJy).1
  have hzM : z ∈ normalizer (W : Set G) := hCM hzC
  have huM : u ∈ normalizer (W : Set G) := hCM huC
  obtain ⟨haM, haA⟩ := isA_a h hρ
  have hua : u * a = a * u := mem_centralizer_singleton_iff.mp huC
  have huy : u * (y : G) = (y : G) * u := mem_centralizer_singleton_iff.mp (hJyy huJ)
  have hay : a * (y : G) = (y : G) * a := hya.symm
  have hjJ : g * z * g⁻¹ ∈ J := mem_conjugate_iff_p42.mp hzJy
  have hjM : g * z * g⁻¹ ∈ normalizer (W : Set G) := h.hNJ (le_normalizer hjJ)
  set aM : ↥(normalizer (W : Set G)) := ⟨a, haM⟩ with haMdef
  set zM : ↥(normalizer (W : Set G)) := ⟨z, hzM⟩ with hzMdef
  set uM : ↥(normalizer (W : Set G)) := ⟨u, huM⟩ with huMdef
  set jM : ↥(normalizer (W : Set G)) := ⟨g * z * g⁻¹, hjM⟩ with hjMdef
  have haM2 : aM * aM = 1 := Subtype.ext ha2
  have hzM2 : zM * zM = 1 := Subtype.ext hz2
  have huz' : uM * uM = zM := Subtype.ext huz
  have hjM2 : jM * jM = 1 := Subtype.ext (by
    show g * z * g⁻¹ * (g * z * g⁻¹) = 1
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group)
  have hjM1 : jM ≠ 1 := by
    intro h1
    have h2 : g * z * g⁻¹ = 1 := congrArg Subtype.val h1
    apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  have hjA : IsA (ρ jM) := isA_of_mem_J h hρ hjJ hjM2 hjM1
  obtain ⟨k, hk⟩ := invol_conj_of_type h hρ haM2 hjM2 (Or.inl ⟨haA, hjA⟩)
  have hk' : (k : G)⁻¹ * a * k = g * z * g⁻¹ := congrArg Subtype.val hk
  have hzconj : ((k : G) * g)⁻¹ * a * ((k : G) * g) = z := by
    calc ((k : G) * g)⁻¹ * a * ((k : G) * g) = g⁻¹ * ((k : G)⁻¹ * a * k) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hk']
      _ = z := by group
  have haz2 : a * z * (a * z) = 1 := by
    calc a * z * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [hza]
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [ha2, hz2, mul_one]
  have hu4 : u ^ 2 ^ 2 = 1 := by
    have h1 : u ^ 2 ^ 2 = (u * u) * (u * u) := by
      rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, pow_two]
    rw [h1, huz, hz2]
  set P0 : Subgroup G := zpowers u ⊔ zpowers a ⊔ zpowers (y : G) with hP0def
  have hP0 : IsPGroup 2 ↥P0 :=
    isPGroup_sup_three_p42 hu4 (by simpa [pow_two] using ha2) (by simpa [pow_two] using hy2')
      hua huy hay
  have hP0M : P0 ≤ normalizer (W : Set G) :=
    sup_le (sup_le (zpowers_le.mpr huM) (zpowers_le.mpr haM)) (zpowers_le.mpr y.2)
  have hP0M2 : IsPGroup 2 ↥(P0.subgroupOf (normalizer (W : Set G))) :=
    hP0.of_equiv (Subgroup.subgroupOfEquivOfLe hP0M).symm
  set Q : Subgroup WrE := (P0.subgroupOf (normalizer (W : Set G))).map ρ with hQ
  have hQ2 : IsPGroup 2 ↥Q := hP0M2.map ρ
  have hQr : Q ≤ ρ.range := Subgroup.map_le_range ρ _
  obtain ⟨m, hm⟩ := exists_conj_le_imgT h hρ hQ2 hQr
  set c : WrE := ρ m with hc
  have hcw : c ∈ wrR := hρ.mem_wrR m
  have hc' : c⁻¹ ∈ wrR := wrR.inv_mem hcw
  have hconj : ∀ w : ↥(normalizer (W : Set G)), (w : G) ∈ P0 →
      c⁻¹ * ρ w * c ∈ imgT T (normalizer (W : Set G)) ρ := fun w hw =>
    hm _ (Subgroup.mem_map.mpr ⟨w, mem_subgroupOf.mpr hw, rfl⟩)
  have haP : a ∈ P0 := mem_sup_left (mem_sup_right (mem_zpowers a))
  have huP : u ∈ P0 := mem_sup_left (mem_sup_left (mem_zpowers u))
  have hyP : (y : G) ∈ P0 := mem_sup_right (mem_zpowers _)
  have ha'X : c⁻¹ * ρ aM * c ∈ imgT T (normalizer (W : Set G)) ρ := hconj aM haP
  have hy'X : c⁻¹ * ρ y * c ∈ imgT T (normalizer (W : Set G)) ρ := hconj y hyP
  have hx'X : c⁻¹ * ρ uM * c ∈ imgT T (normalizer (W : Set G)) ρ := hconj uM huP
  have hA' : IsA (c⁻¹ * ρ aM * c) := by
    have := isA_conj hc' haA
    rwa [inv_inv] at this
  have hU' : IsUU (c⁻¹ * ρ y * c) := by
    have := isUU_conj hc' hyU
    rwa [inv_inv] at this
  have hρay : ρ aM * ρ y = ρ y * ρ aM := by
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext hay)
  have hρua : ρ uM * ρ aM = ρ aM * ρ uM := by
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext hua)
  have hρuy : ρ uM * ρ y = ρ y * ρ uM := by
    rw [← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext huy)
  have hcomm : c⁻¹ * ρ aM * c * (c⁻¹ * ρ y * c) = c⁻¹ * ρ y * c * (c⁻¹ * ρ aM * c) :=
    conj_comm_p42 c hρay
  have hx'mem : c⁻¹ * ρ uM * c ∈ imgT T (normalizer (W : Set G)) ρ ⊓
      centralizer ({c⁻¹ * ρ aM * c} : Set WrE) ⊓ centralizer ({c⁻¹ * ρ y * c} : Set WrE) := by
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨hx'X, ?_⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      exact conj_comm_p42 c hρua
    · rw [mem_centralizer_singleton_iff]
      exact conj_comm_p42 c hρuy
  have hxx : c⁻¹ * ρ uM * c * (c⁻¹ * ρ uM * c) = c⁻¹ * ρ zM * c := by
    calc c⁻¹ * ρ uM * c * (c⁻¹ * ρ uM * c) = c⁻¹ * (ρ uM * ρ uM) * c := by group
      _ = c⁻¹ * ρ (uM * uM) * c := by rw [map_mul]
      _ = c⁻¹ * ρ zM * c := by rw [huz']
  have hρz1 : ρ zM ≠ 1 := fun h1 => hz1 (eq_one_of_mem_oddIn_p42 ((hρ.ker_iff zM).mp h1) hz2)
  have hxx1 : c⁻¹ * ρ uM * c * (c⁻¹ * ρ uM * c) ≠ 1 := by
    rw [hxx]
    intro h1
    apply hρz1
    calc ρ zM = c * (c⁻¹ * ρ zM * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hsq := hC.pair_sq _ ha'X _ hy'X hA' hU' hcomm _ hx'mem hxx1
  rw [hxx] at hsq
  rcases hsq with h1 | ⟨-, h1⟩ | ⟨h1, -⟩
  ·
    have h2 : ρ zM = ρ aM := mul_left_cancel (mul_right_cancel h1)
    have h3 : ρ (aM * zM) = 1 := by
      rw [map_mul, h2, ← map_mul, haM2, map_one]
    have h4 : ((aM * zM : ↥(normalizer (W : Set G))) : G) ∈ oddIn (normalizer (W : Set G)) :=
      (hρ.ker_iff _).mp h3
    have h6 : a * z = 1 := eq_one_of_mem_oddIn_p42 h4 haz2
    apply haJy
    have h7 : a = z⁻¹ := eq_inv_of_mul_eq_one_left h6
    rw [h7]
    exact inv_mem hzJy
  ·
    have h2 : c⁻¹ * ρ aM * c * (c⁻¹ * ρ zM * c) = c⁻¹ * ρ (aM * zM) * c := by
      calc c⁻¹ * ρ aM * c * (c⁻¹ * ρ zM * c) = c⁻¹ * (ρ aM * ρ zM) * c := by group
        _ = c⁻¹ * ρ (aM * zM) * c := by rw [map_mul]
    rw [h2] at h1
    have h3 : IsD (ρ (aM * zM)) := by
      have h4 := isD_conj hcw h1
      have e : c * (c⁻¹ * ρ (aM * zM) * c) * c⁻¹ = ρ (aM * zM) := by group
      rwa [e] at h4
    have h4 : aM * zM * (aM * zM) = 1 := Subtype.ext haz2
    exact a_not_conj_d hMax h hρ hC h4 h3 q hqa
  ·
    have h3 : IsD (ρ zM) := by
      have h4 := isD_conj hcw h1
      have e : c * (c⁻¹ * ρ zM * c) * c⁻¹ = ρ zM := by group
      rwa [e] at h4
    exact a_not_conj_d hMax h hρ hC hzM2 h3 ((k : G) * g) hzconj

end CFSG.ComponentClassification.GrSLit.L34Tw
