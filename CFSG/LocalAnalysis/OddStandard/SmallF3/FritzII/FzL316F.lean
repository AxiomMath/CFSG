module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316F1

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

variable {G : Type} [Group G] [Finite G]

private def fzlSq (H : Subgroup G) (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : ↥H →* ↥H where
  toFun x := x ^ 2
  map_one' := by simp
  map_mul' x y := by
    have h : x * y = y * x := Subtype.ext (hcomm x x.2 y y.2)
    rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc y x y, ← h, mul_assoc, mul_assoc]

private lemma fzlSq_apply {H : Subgroup G} (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (x : ↥H) : fzlSq H hcomm x = x ^ 2 := rfl

private lemma fzlSq_ker_eq {H K : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hKH : K ≤ H)
    (hKmem : ∀ x ∈ K, x ^ 2 = 1) (hKiff : ∀ x ∈ H, x ^ 2 = 1 → x ∈ K) :
    (fzlSq H hcomm).ker = K.subgroupOf H := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have h2 : ((x : ↥H) ^ 2 : ↥H) = 1 := by
      simpa only [fzlSq_apply] using hx
    exact hKiff x.1 x.2 (by simpa using congrArg Subtype.val h2)
  · intro hx
    have h2 : ((x : ↥H) ^ 2 : ↥H) = 1 := Subtype.ext (by simpa using hKmem x.1 hx)
    simpa only [fzlSq_apply] using h2

private lemma fzlSq_ker_card {H K : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hKH : K ≤ H)
    (hKmem : ∀ x ∈ K, x ^ 2 = 1) (hKiff : ∀ x ∈ H, x ^ 2 = 1 → x ∈ K) :
    Nat.card (fzlSq H hcomm).ker = Nat.card K := by
  rw [fzlSq_ker_eq hcomm hKH hKmem hKiff]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv

private def fzlOmega (P : Subgroup G)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) : Subgroup G where
  carrier := {p | p ∈ P ∧ p ^ 2 = 1}
  mul_mem' := by
    rintro a b ⟨haP, ha2⟩ ⟨hbP, hb2⟩
    exact ⟨P.mul_mem haP hbP, by
      have hc : Commute a b := hcomm a haP b hbP
      rw [hc.mul_pow 2, ha2, hb2, one_mul]⟩
  one_mem' := ⟨P.one_mem, one_pow 2⟩
  inv_mem' := by
    rintro a ⟨haP, ha2⟩
    exact ⟨P.inv_mem haP, by rw [inv_pow, ha2, inv_one]⟩

private lemma fzlOmega_mem (P : Subgroup G)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {x : G} :
    x ∈ fzlOmega P hcomm ↔ x ∈ P ∧ x ^ 2 = 1 := Iff.rfl

private lemma fzlOmega_card (P : Subgroup G)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    Nat.card (fzlOmega P hcomm) = Nat.card {p : G // p ∈ P ∧ p ^ 2 = 1} :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1, (fzlOmega_mem P hcomm).mp x.2⟩
      invFun := fun x => ⟨x.1, (fzlOmega_mem P hcomm).mpr x.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

private lemma fzl_num_cases {n : ℕ} (h1 : n ∣ 64) (h2 : 4 ∣ n) (h3 : n % 3 = 1) :
    n = 4 ∨ n = 16 ∨ n = 64 := by
  have h1' : n ∣ 2 ^ 6 := by simpa using h1
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1'
  interval_cases j
  · norm_num at h2
  · norm_num at h2
  · left; norm_num
  · norm_num at h3
  · right; left; norm_num
  · norm_num at h3
  · right; right; norm_num

theorem fzl_abelian_dichotomy {P E Z : Subgroup G} {rho : G}
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hcard : Nat.card P = 64)
    (hrho3 : rho ^ 3 = 1) (hrP : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P)
    (hfpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1) (hZE : Z ≤ E) (hEP : E ≤ P)
    (hcE : Nat.card E = 16) (hcZ : Nat.card Z = 4) (hE4 : ∀ e ∈ E, e ^ 4 = 1)
    (hEsq : ∀ e ∈ E, e ^ 2 ∈ Z) (hEZ : ∀ e ∈ E, e ^ 2 = 1 → e ∈ Z) (hZ2 : ∀ z ∈ Z, z ^ 2 = 1)
    (hrE : ∀ e ∈ E, rho * e * rho⁻¹ ∈ E) (hPsq : ∀ p ∈ P, p ^ 2 ∈ E)
    (hEeq : Nonempty (↥E ≃* Z4Z4)) :
    Nonempty (↥P ≃* FzZ4422) ∨
      ((∀ p ∈ P, p ^ 2 = 1 → p ∈ Z) ∧ (∀ p ∈ P, p ^ 4 = 1 → p ∈ E) ∧
        ∀ e ∈ E, ∃ p ∈ P, p ^ 2 = e) := by
  classical
  let Ω : Subgroup G := fzlOmega P hcomm
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a :=
    fun a ha b hb => hcomm a (hEP ha) b (hEP hb)
  have hΩP : Ω ≤ P := fun x hx => ((fzlOmega_mem P hcomm).mp hx).1
  have hZΩ : Z ≤ Ω := fun z hz =>
    (fzlOmega_mem P hcomm).mpr ⟨hEP (hZE hz), hZ2 z hz⟩
  have hΩrho : ∀ p ∈ Ω, rho * p * rho⁻¹ ∈ Ω := by
    intro p hp
    obtain ⟨hpP, hp2⟩ := (fzlOmega_mem P hcomm).mp hp
    refine (fzlOmega_mem P hcomm).mpr ⟨hrP p hpP, ?_⟩
    rw [conj_pow, hp2]
    group
  have hΩfix : ∀ p ∈ Ω, rho * p * rho⁻¹ = p → p = 1 := fun p hp h =>
    hfpf p ((fzlOmega_mem P hcomm).mp hp).1 h
  have hΩmod : Nat.card Ω % 3 = 1 := fzl_card_mod3_of_fpf hrho3 hΩrho hΩfix
  have hΩdvd : Nat.card Ω ∣ 64 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hΩP
  have h4Ω : 4 ∣ Nat.card Ω := by
    rw [← hcZ]
    exact Subgroup.card_dvd_of_le hZΩ
  have hΩcases : Nat.card Ω = 4 ∨ Nat.card Ω = 16 ∨ Nat.card Ω = 64 :=
    fzl_num_cases hΩdvd h4Ω hΩmod
  have hEΩ_eq : E ⊓ Ω = Z := by
    refine le_antisymm ?_ (le_inf hZE hZΩ)
    intro x hx
    exact hEZ x hx.1 (by simpa using ((fzlOmega_mem P hcomm).mp hx.2).2)
  have hΩne64 : Nat.card Ω ≠ 64 := by
    intro h64
    have hΩP_eq : Ω = P := Subgroup.eq_of_le_of_card_ge hΩP (by rw [hcard, h64])
    have hEΩ : E ≤ Ω := by rw [hΩP_eq]; exact hEP
    have hEΩeq : E = E ⊓ Ω := le_antisymm (le_inf le_rfl hEΩ) inf_le_left
    have hEZ_eq : E = Z := hEΩeq.trans hEΩ_eq
    rw [hEZ_eq, hcZ] at hcE
    norm_num at hcE
  rcases hΩcases with h4 | h16 | h64
  · right
    have hΩZ : Ω = Z :=
      (Subgroup.eq_of_le_of_card_ge hZΩ (by rw [h4, hcZ])).symm
    have hΩP_mem : ∀ p ∈ P, p ^ 2 = 1 → p ∈ Z := by
      intro p hp hp2
      have hmem : p ∈ Ω := (fzlOmega_mem P hcomm).mpr ⟨hp, hp2⟩
      rwa [hΩZ] at hmem
    have hKmemP : ∀ x ∈ Ω, x ^ 2 = 1 := fun x hx => ((fzlOmega_mem P hcomm).mp hx).2
    have hKiffP : ∀ x ∈ P, x ^ 2 = 1 → x ∈ Ω :=
      fun x hxP hx2 => (fzlOmega_mem P hcomm).mpr ⟨hxP, hx2⟩
    have hKerP : Nat.card (fzlSq P hcomm).ker = 4 := by
      rw [fzlSq_ker_card hcomm hΩP hKmemP hKiffP]
      simpa [Ω] using h4
    have hRangeP : Nat.card (fzlSq P hcomm).range = 16 := by
      have h := Subgroup.card_ker_mul_card_range (fzlSq P hcomm)
      rw [hKerP] at h
      have hP : Nat.card ↥P = 64 := hcard
      rw [hP] at h
      omega
    let SqP : Subgroup G := (fzlSq P hcomm).range.map P.subtype
    have hSqPcard : Nat.card SqP = 16 := by
      show Nat.card (Subgroup.map P.subtype (fzlSq P hcomm).range) = 16
      rw [Subgroup.card_subtype P (fzlSq P hcomm).range, hRangeP]
    have hSqP_le_E : SqP ≤ E := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, rfl⟩ := hy
      exact hPsq z.1 z.2
    have hSqP_eq_E : SqP = E :=
      Subgroup.eq_of_le_of_card_ge hSqP_le_E (by rw [hSqPcard, hcE])
    have hEsqP : ∀ e ∈ E, ∃ p ∈ P, p ^ 2 = e := by
      intro e he
      have heSq : e ∈ SqP := by rw [hSqP_eq_E]; exact he
      obtain ⟨y, hy, hxy⟩ := heSq
      obtain ⟨z, rfl⟩ := hy
      exact ⟨z.1, z.2, by simpa [fzlSq] using hxy⟩
    have hKerE : Nat.card (fzlSq E hcommE).ker = 4 := by
      rw [fzlSq_ker_card hcommE hZE hZ2 hEZ]
      exact hcZ
    have hRangeE : Nat.card (fzlSq E hcommE).range = 4 := by
      have h := Subgroup.card_ker_mul_card_range (fzlSq E hcommE)
      rw [hKerE] at h
      have hE : Nat.card ↥E = 16 := hcE
      rw [hE] at h
      omega
    let SqE : Subgroup G := (fzlSq E hcommE).range.map E.subtype
    have hSqEcard : Nat.card SqE = 4 := by
      show Nat.card (Subgroup.map E.subtype (fzlSq E hcommE).range) = 4
      rw [Subgroup.card_subtype E (fzlSq E hcommE).range, hRangeE]
    have hSqE_le_Z : SqE ≤ Z := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, rfl⟩ := hy
      exact hEsq z.1 z.2
    have hSqE_eq_Z : SqE = Z :=
      Subgroup.eq_of_le_of_card_ge hSqE_le_Z (by rw [hSqEcard, hcZ])
    have hZE_sq : ∀ z ∈ Z, ∃ e ∈ E, e ^ 2 = z := by
      intro z hz
      have hzSq : z ∈ SqE := by rw [hSqE_eq_Z]; exact hz
      obtain ⟨y, hy, hxy⟩ := hzSq
      obtain ⟨e, rfl⟩ := hy
      exact ⟨e.1, e.2, by simpa [fzlSq] using hxy⟩
    have hfour : ∀ p ∈ P, p ^ 4 = 1 → p ∈ E := by
      intro p hp hp4
      have hp2Ω : p ^ 2 ∈ Ω := by
        refine (fzlOmega_mem P hcomm).mpr ⟨?_, ?_⟩
        · simpa [pow_two] using P.mul_mem hp hp
        · rw [← pow_mul]
          simpa using hp4
      have hp2Z : p ^ 2 ∈ Z := by
        rw [← hΩZ]
        exact hp2Ω
      obtain ⟨e, heE, he2⟩ := hZE_sq (p ^ 2) hp2Z
      have hsq1 : (p * e⁻¹) ^ 2 = 1 := by
        have hc : Commute p e := hcomm p hp e (hEP heE)
        have hci : Commute p e⁻¹ := hc.inv_right
        rw [hci.mul_pow 2, inv_pow, he2]
        group
      have hmemZ : (p * e⁻¹) ∈ Z := by
        have hΩmem : p * e⁻¹ ∈ Ω :=
          (fzlOmega_mem P hcomm).mpr ⟨P.mul_mem hp (P.inv_mem (hEP heE)), hsq1⟩
        rwa [hΩZ] at hΩmem
      have hpEq : (p * e⁻¹) * e = p := by group
      rw [← hpEq]
      exact E.mul_mem (hZE hmemZ) heE
    exact ⟨hΩP_mem, hfour, hEsqP⟩
  · left
    refine fzl_equiv_Z4422 hcomm hcard hZE hEP hcE hcZ hEZ hZ2 hEeq ?_
    rw [← fzlOmega_card P hcomm]
    simpa [Ω] using h16
  · exact absurd h64 hΩne64

end CFSG.OddStandard.SmallF3.FritzII
