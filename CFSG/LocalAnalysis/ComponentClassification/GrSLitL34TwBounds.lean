module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWBadA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwConjB
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwGen
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRLev
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwSmall
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwTrans

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {a x : G} {J S' W K T : Subgroup G} {t : G}
  {ρ : ↥(normalizer (W : Set G)) →* WrE}

private theorem isPGroup_zpowers_of_mul_self {a : G} (ha2 : a * a = 1) :
    IsPGroup 2 (zpowers a) := by
  rintro ⟨h, n, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, ha2, one_zpow]

private theorem mem_normalizer_zpowers_of_comm (u v : G) (huv : u * v = v * u) :
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

private theorem isPGroup_sup_two {P : Subgroup G} {a y : G} (hP : IsPGroup 2 P)
    (ha2 : a * a = 1) (hy2 : y * y = 1) (hPa : P ≤ centralizer ({a} : Set G))
    (hPy : P ≤ centralizer ({y} : Set G)) (hay : a * y = y * a) :
    IsPGroup 2 ↥(P ⊔ zpowers a ⊔ zpowers y) := by
  have hza := isPGroup_zpowers_of_mul_self ha2
  have hzy := isPGroup_zpowers_of_mul_self hy2
  have h1 : IsPGroup 2 ↥(P ⊔ zpowers a) :=
    hP.to_sup_of_normal_right' hza (fun u hu =>
      mem_normalizer_zpowers_of_comm u a (mem_centralizer_singleton_iff.mp (hPa hu)))
  refine h1.to_sup_of_normal_right' hzy (fun u hu => ?_)
  have hPle : P ⊔ zpowers a ≤ centralizer ({y} : Set G) := by
    refine sup_le hPy ?_
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr hay
  exact mem_normalizer_zpowers_of_comm u y (mem_centralizer_singleton_iff.mp (hPle hu))

private theorem core (hMax : MaximalTwoComponentInput)
    (h : TwHyp G a x J S' W K T t) (hρ : TwModel (normalizer (W : Set G)) K t ρ)
    {y : ↥(normalizer (W : Set G))} (hy2 : y * y = 1) (hyU : IsUU (ρ y))
    (hya : (y : G) * a = a * (y : G)) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPle : P ≤ centralizer ({a} : Set G) ⊓ centralizer ({(y : G)} : Set G)) :
    ∃ (a' y' : WrE) (φ : ↥P →* WrE), a' ∈ imgT T (normalizer (W : Set G)) ρ ∧
      y' ∈ imgT T (normalizer (W : Set G)) ρ ∧ IsA a' ∧ IsUU y' ∧ a' * y' = y' * a' ∧
      Function.Injective φ ∧
      ∀ p : ↥P, φ p ∈ imgT T (normalizer (W : Set G)) ρ ⊓ centralizer ({a'} : Set WrE) ⊓
        centralizer ({y'} : Set WrE) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCM : centralizer ({a} : Set G) ≤ normalizer (W : Set G) :=
    (GrS5S.centralizer_le_normalizer_of_sec4 hMax h.hset).trans h.hNJ
  have haord : orderOf a = 2 := h.hset.2.1.1
  have ha2 : a * a = 1 := by
    have h2 : a ^ 2 = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
    rwa [pow_two] at h2
  obtain ⟨haM, haA⟩ := isA_a h hρ
  have hPa : P ≤ centralizer ({a} : Set G) := hPle.trans inf_le_left
  have hPy : P ≤ centralizer ({(y : G)} : Set G) := hPle.trans inf_le_right
  have hPM : P ≤ normalizer (W : Set G) := hPa.trans hCM
  have hay : a * (y : G) = (y : G) * a := hya.symm
  have hy2' : (y : G) * (y : G) = 1 := congrArg Subtype.val hy2
  set P' : Subgroup G := P ⊔ zpowers a ⊔ zpowers (y : G) with hP'
  have hP'2 : IsPGroup 2 ↥P' := isPGroup_sup_two hP2 ha2 hy2' hPa hPy hay
  have hP'M : P' ≤ normalizer (W : Set G) :=
    sup_le (sup_le hPM (zpowers_le.mpr haM)) (zpowers_le.mpr y.2)
  have hP'2M : IsPGroup 2 ↥(P'.subgroupOf (normalizer (W : Set G))) :=
    hP'2.of_equiv (Subgroup.subgroupOfEquivOfLe hP'M).symm
  set Q : Subgroup WrE := (P'.subgroupOf (normalizer (W : Set G))).map ρ with hQ
  have hQ2 : IsPGroup 2 ↥Q := hP'2M.map ρ
  have hQr : Q ≤ ρ.range := Subgroup.map_le_range ρ _
  obtain ⟨m, hm⟩ := exists_conj_le_imgT h hρ hQ2 hQr
  set c : WrE := ρ m with hc
  have hc' : c⁻¹ ∈ wrR := wrR.inv_mem (hρ.mem_wrR m)
  have hmemQ : ∀ (z : ↥(normalizer (W : Set G))), (z : G) ∈ P' → ρ z ∈ Q := fun z hz =>
    Subgroup.mem_map.mpr ⟨z, mem_subgroupOf.mpr hz, rfl⟩
  have haP' : a ∈ P' := mem_sup_left (mem_sup_right (mem_zpowers a))
  have hyP' : (y : G) ∈ P' := mem_sup_right (mem_zpowers _)
  have hconj : ∀ z : ↥(normalizer (W : Set G)), (z : G) ∈ P' →
      c⁻¹ * ρ z * c ∈ imgT T (normalizer (W : Set G)) ρ := fun z hz => hm _ (hmemQ z hz)
  refine ⟨c⁻¹ * ρ ⟨a, haM⟩ * c, c⁻¹ * ρ y * c,
    (MulAut.conj c⁻¹).toMonoidHom.comp (ρ.comp (Subgroup.inclusion hPM)),
    hconj ⟨a, haM⟩ haP', hconj y hyP', ?_, ?_, ?_, ?_, ?_⟩
  · have := isA_conj hc' haA
    rwa [inv_inv] at this
  · have := isUU_conj hc' hyU
    rwa [inv_inv] at this
  · have h1 : ρ ⟨a, haM⟩ * ρ y = ρ y * ρ ⟨a, haM⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext hay)
    calc c⁻¹ * ρ ⟨a, haM⟩ * c * (c⁻¹ * ρ y * c) = c⁻¹ * (ρ ⟨a, haM⟩ * ρ y) * c := by group
      _ = c⁻¹ * (ρ y * ρ ⟨a, haM⟩) * c := by rw [h1]
      _ = c⁻¹ * ρ y * c * (c⁻¹ * ρ ⟨a, haM⟩ * c) := by group
  · rw [injective_iff_map_eq_one]
    intro p hp
    have hp1 : ρ (Subgroup.inclusion hPM p) = 1 := by
      have h1 : c⁻¹ * ρ (Subgroup.inclusion hPM p) * c = 1 := by
        have : (MulAut.conj c⁻¹) (ρ (Subgroup.inclusion hPM p)) = 1 := hp
        simpa [MulAut.conj_apply] using this
      calc ρ (Subgroup.inclusion hPM p) = c * (c⁻¹ * ρ (Subgroup.inclusion hPM p) * c) * c⁻¹ := by
            group
        _ = 1 := by rw [h1]; group
    have hodd := (hρ.ker_iff _).mp hp1
    have hbot : (zpowers (p : G)) = ⊥ := by
      refine eq_bot_of_le_two_group_of_le_odd (P := P) (O := oddIn (normalizer (W : Set G)))
        hP2 ?_ ?_ ?_
      · rw [oddIn, card_map_of_injective (subtype_injective _)]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      · rw [zpowers_le]; exact p.2
      · rw [zpowers_le]; exact hodd
    have : (p : G) = 1 := by
      have := mem_zpowers (p : G)
      rw [hbot, mem_bot] at this
      exact this
    exact Subtype.ext this
  · intro p
    have hpP' : (p : G) ∈ P' := mem_sup_left (mem_sup_left p.2)
    have hpM : (p : G) ∈ normalizer (W : Set G) := hPM p.2
    have hphi : ((MulAut.conj c⁻¹).toMonoidHom.comp (ρ.comp (Subgroup.inclusion hPM))) p =
        c⁻¹ * ρ ⟨p, hpM⟩ * c := by
      simp [MulAut.conj_apply]
      rfl
    rw [hphi]
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨hconj ⟨p, hpM⟩ hpP', ?_⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      have h1 : ρ ⟨p, hpM⟩ * ρ ⟨a, haM⟩ = ρ ⟨a, haM⟩ * ρ ⟨p, hpM⟩ := by
        rw [← map_mul, ← map_mul]
        exact congrArg ρ (Subtype.ext (mem_centralizer_singleton_iff.mp (hPa p.2)))
      calc c⁻¹ * ρ ⟨p, hpM⟩ * c * (c⁻¹ * ρ ⟨a, haM⟩ * c) = c⁻¹ * (ρ ⟨p, hpM⟩ * ρ ⟨a, haM⟩) * c := by
            group
        _ = c⁻¹ * (ρ ⟨a, haM⟩ * ρ ⟨p, hpM⟩) * c := by rw [h1]
        _ = c⁻¹ * ρ ⟨a, haM⟩ * c * (c⁻¹ * ρ ⟨p, hpM⟩ * c) := by group
    · rw [mem_centralizer_singleton_iff]
      have h1 : ρ ⟨p, hpM⟩ * ρ y = ρ y * ρ ⟨p, hpM⟩ := by
        rw [← map_mul, ← map_mul]
        exact congrArg ρ (Subtype.ext (mem_centralizer_singleton_iff.mp (hPy p.2)))
      calc c⁻¹ * ρ ⟨p, hpM⟩ * c * (c⁻¹ * ρ y * c) = c⁻¹ * (ρ ⟨p, hpM⟩ * ρ y) * c := by group
        _ = c⁻¹ * (ρ y * ρ ⟨p, hpM⟩) * c := by rw [h1]
        _ = c⁻¹ * ρ y * c * (c⁻¹ * ρ ⟨p, hpM⟩ * c) := by group

theorem cent_bounds
    (hMax : MaximalTwoComponentInput)
    (h : TwHyp G a x J S' W K T t) (hρ : TwModel (normalizer (W : Set G)) K t ρ)
    (hC : ConcX (imgT T (normalizer (W : Set G)) ρ)) {y : ↥(normalizer (W : Set G))}
    (hy2 : y * y = 1) (hyU : IsUU (ρ y)) (hya : (y : G) * a = a * (y : G)) :
    (∀ P : Subgroup G, IsPGroup 2 P →
        P ≤ centralizer ({a} : Set G) ⊓ centralizer ({(y : G)} : Set G) → Nat.card P ≤ 2 ^ 7) ∧
    (∀ E : Subgroup G, E ≤ centralizer ({a} : Set G) ⊓ centralizer ({(y : G)} : Set G) →
        IsElemTwo E → Nat.card E ≠ 16) ∧
    (∀ (H : Subgroup G) (Q : Type) [Group Q] (π : ↥H →* Q),
        H ≤ centralizer ({a} : Set G) ⊓ centralizer ({(y : G)} : Set G) →
        Function.Surjective π → Group.IsPerfect Q → Odd (Nat.card Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCM : centralizer ({a} : Set G) ≤ normalizer (W : Set G) :=
    (GrS5S.centralizer_le_normalizer_of_sec4 hMax h.hset).trans h.hNJ
  refine ⟨?_, ?_, ?_⟩
  · intro P hP2 hPle
    obtain ⟨a', y', φ, ha'X, hy'X, hA, hU, hc, hinj, hφ⟩ :=
      core hMax h hρ hy2 hyU hya hP2 hPle
    have hle := hC.pair_card a' ha'X y' hy'X hA hU hc
    exact le_trans (Nat.card_le_card_of_injective
      (fun p : ↥P => (⟨φ p, hφ p⟩ : ↥(imgT T (normalizer (W : Set G)) ρ ⊓
        centralizer ({a'} : Set WrE) ⊓ centralizer ({y'} : Set WrE))))
      (fun p q hpq => hinj (congrArg Subtype.val hpq))) hle
  · intro E hEle hE hE16
    have hE2 : IsPGroup 2 E := fun g => ⟨1, by
      rw [pow_one, pow_two]; exact Subtype.ext (by simpa using hE.2 (g : G) g.2)⟩
    obtain ⟨a', y', φ, ha'X, hy'X, hA, hU, hc, hinj, hφ⟩ :=
      core hMax h hρ hy2 hyU hya hE2 hEle
    refine hC.pair_rank a' ha'X y' hy'X hA hU hc ⟨φ.range, ?_, ?_, ?_⟩
    · rintro _ ⟨p, rfl⟩
      exact hφ p
    · refine ⟨?_, ?_⟩
      · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hE.1 _ p.2 _ q.2)
      · rintro _ ⟨p, rfl⟩
        rw [← map_mul]
        have : p * p = 1 := Subtype.ext (hE.2 _ p.2)
        rw [this, map_one]
    · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, hE16]
  · intro H Q _ π hHle hπ hQ
    have hHM : H ≤ normalizer (W : Set G) := hHle.trans (inf_le_left.trans hCM)
    obtain ⟨haM, haA⟩ := isA_a h hρ
    set C₀ : Subgroup WrE := centralizer ({ρ ⟨a, haM⟩} : Set WrE) ⊓
      centralizer ({ρ y} : Set WrE) ⊓ wrR with hC₀
    have hcomm : ρ ⟨a, haM⟩ * ρ y = ρ y * ρ ⟨a, haM⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext hya.symm)
    haveI : Group.IsSolvable ↥C₀ := solvable_centralizer_pair haA hyU
      (hρ.mem_wrR _) (hρ.mem_wrR _) hcomm
    let f₀ : ↥H →* WrE := ρ.comp (Subgroup.inclusion hHM)
    have hf₀ : ∀ z, f₀ z ∈ C₀ := by
      intro z
      have hz := hHle z.2
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨?_, ?_⟩, hρ.mem_wrR _⟩
      · rw [mem_centralizer_singleton_iff]
        show ρ _ * ρ _ = ρ _ * ρ _
        rw [← map_mul, ← map_mul]
        exact congrArg ρ (Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp hz).1))
      · rw [mem_centralizer_singleton_iff]
        show ρ _ * ρ _ = ρ _ * ρ _
        rw [← map_mul, ← map_mul]
        exact congrArg ρ (Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp hz).2))
    let f : ↥H →* ↥C₀ := f₀.codRestrict C₀ hf₀
    have hker : Odd (Nat.card f.ker) := by
      have hsub : (f.ker.map H.subtype) ≤ oddIn (normalizer (W : Set G)) := by
        rintro _ ⟨z, hz, rfl⟩
        have h1 : ρ (Subgroup.inclusion hHM z) = 1 := by
          have := congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
          exact this
        exact (hρ.ker_iff _).mp h1
      have hodd : Odd (Nat.card (oddIn (normalizer (W : Set G)))) := by
        rw [oddIn, card_map_of_injective (subtype_injective _)]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      have hcard : Nat.card (f.ker.map H.subtype) = Nat.card f.ker :=
        Subgroup.card_map_of_injective (subtype_injective H)
      rw [← hcard]
      exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le hsub)
    exact odd_card_of_perfect_quotient f hker π hπ hQ

end CFSG.ComponentClassification.GrSLit.L34Tw
