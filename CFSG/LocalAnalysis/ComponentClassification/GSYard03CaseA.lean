module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard03Defs

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard03

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

private theorem gsy03_comm_of_sq_eq_one {Q : Type} [Group Q] {A : Subgroup Q}
    (hA2 : ∀ a ∈ A, a * a = 1) {a b : Q} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have hinv : ∀ y ∈ A, y⁻¹ = y := fun y hy => inv_eq_of_mul_eq_one_right (hA2 y hy)
  calc a * b = (a * b)⁻¹ := (hinv _ (mul_mem ha hb)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hinv a ha, hinv b hb]

private theorem gsy03_exists_isKleinFour_le {Q : Type} [Group Q] [Finite Q] {A : Subgroup Q}
    (hA2 : ∀ a ∈ A, a * a = 1) {K : Subgroup ↥A} (hK : 3 ≤ Nat.card K) :
    ∃ V : Subgroup Q, IsKleinFour V ∧ V ≤ K.map A.subtype := by
  have hsq : ∀ g : ↥A, g ^ 2 = 1 := fun g => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, sq]
    exact hA2 _ g.2)
  have hAp : IsPGroup 2 ↥A := fun g => ⟨1, by rw [pow_one]; exact hsq g⟩
  obtain ⟨m, hm⟩ := (hAp.to_subgroup K).exists_card_eq
  have h4 : 2 ^ 2 ≤ Nat.card K := by
    rw [hm] at hK ⊢
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m <;> norm_num at hK
    · exact Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨H', hH'K, hH'⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card Nat.prime_two hAp h4
  refine ⟨H'.map A.subtype, ?_, Subgroup.map_mono hH'K⟩
  refine FooteLit.isKleinFour_of_card_eq_four ?_ ?_
  · rw [Subgroup.card_subtype]
    norm_num [hH']
  · rintro _ ⟨h, -, rfl⟩
    rw [sq]
    exact hA2 _ h.2

private theorem gsy03_exists_isKleinFour_centralizer {Q : Type} [Group Q] [Finite Q]
    {A : Subgroup Q} (hA2 : ∀ a ∈ A, a * a = 1) (hA8 : 8 ≤ Nat.card A) {x : Q}
    (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A) (hz : x * x ∈ center Q) :
    ∃ V : Subgroup Q, IsKleinFour V ∧ V ≤ centralizer ({x} : Set Q) := by
  have hcen : ∀ g : Q, g * (x * x) = (x * x) * g := fun g => Subgroup.mem_center_iff.mp hz g
  have hback : ∀ a : Q, x * (x * a * x⁻¹) * x⁻¹ = a := by
    intro a
    calc x * (x * a * x⁻¹) * x⁻¹ = (x * x) * a * (x * x)⁻¹ := by group
      _ = a := by rw [← hcen a]; group
  have hfix : ∀ a ∈ A, x * (a * (x * a * x⁻¹)) * x⁻¹ = a * (x * a * x⁻¹) := by
    intro a ha
    calc x * (a * (x * a * x⁻¹)) * x⁻¹
        = (x * a * x⁻¹) * (x * (x * a * x⁻¹) * x⁻¹) := by group
      _ = (x * a * x⁻¹) * a := by rw [hback a]
      _ = a * (x * a * x⁻¹) := gsy03_comm_of_sq_eq_one hA2 (hxA a ha) ha
  let ψ : ↥A →* ↥A := MonoidHom.mk' (fun a => a * ⟨x * (a : Q) * x⁻¹, hxA (a : Q) a.2⟩)
    (fun a b => by
      apply Subtype.ext
      show (a : Q) * b * (x * ((a : Q) * b) * x⁻¹) =
        (a : Q) * (x * (a : Q) * x⁻¹) * ((b : Q) * (x * (b : Q) * x⁻¹))
      have hc : (x * (a : Q) * x⁻¹) * (b : Q) = (b : Q) * (x * (a : Q) * x⁻¹) :=
        gsy03_comm_of_sq_eq_one hA2 (hxA (a : Q) a.2) b.2
      calc (a : Q) * b * (x * ((a : Q) * b) * x⁻¹)
          = (a : Q) * ((b : Q) * (x * (a : Q) * x⁻¹)) * (x * (b : Q) * x⁻¹) := by group
        _ = (a : Q) * ((x * (a : Q) * x⁻¹) * (b : Q)) * (x * (b : Q) * x⁻¹) := by rw [hc]
        _ = (a : Q) * (x * (a : Q) * x⁻¹) * ((b : Q) * (x * (b : Q) * x⁻¹)) := by group)
  have hrk : ψ.range ≤ ψ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show (a : Q) * (x * (a : Q) * x⁻¹) * (x * ((a : Q) * (x * (a : Q) * x⁻¹)) * x⁻¹) = 1
    rw [hfix (a : Q) a.2]
    exact hA2 _ (mul_mem a.2 (hxA (a : Q) a.2))
  have hker : ∀ h ∈ ψ.ker, (h : Q) * x = x * (h : Q) := by
    intro h hh
    have h0 : (h : Q) * (x * (h : Q) * x⁻¹) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hh)
    have hhh : (h : Q) * (h : Q) = 1 := hA2 _ h.2
    have hc : x * (h : Q) * x⁻¹ = (h : Q) := by
      calc x * (h : Q) * x⁻¹ = (h : Q)⁻¹ := eq_inv_of_mul_eq_one_right h0
        _ = (h : Q) := inv_eq_of_mul_eq_one_right hhh
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  have hcard : Nat.card A = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have h1 : Nat.card ψ.range ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hrk
  have hK3 : 3 ≤ Nat.card ψ.ker := by
    by_contra hlt
    have hle2 : Nat.card ψ.ker ≤ 2 := by omega
    have hprod : Nat.card ψ.range * Nat.card ψ.ker ≤ 2 * 2 :=
      Nat.mul_le_mul (le_trans h1 hle2) hle2
    omega
  obtain ⟨V, hV, hVK⟩ := gsy03_exists_isKleinFour_le hA2 hK3
  refine ⟨V, hV, ?_⟩
  intro v hv
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp (hVK hv)
  exact mem_centralizer_singleton_iff.mpr (hker h hh)

theorem centralSquareFour_of_normal_elemAbelian {Q : Type} [Group Q] [Finite Q]
    (hZ : IsPGroup 2 (center Q))
    (h8 : ∀ S : Sylow 2 Q, ∃ A : Subgroup Q, (S : Subgroup Q) ≤ normalizer (A : Set Q) ∧
      (∀ a ∈ A, a * a = 1) ∧ 8 ≤ Nat.card A) :
    CentralSquareFour Q := by
  intro x hx
  have hxz : IsPGroup 2 (zpowers x) := by
    obtain ⟨k, hk⟩ := hZ ⟨x * x, hx⟩
    have hk' : (x * x) ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val hk
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    have hpow : x ^ 2 ^ (k + 1) = 1 := by
      have e : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [e, pow_mul, sq, hk']
    exact IsPGroup.of_card_dvd_pow (p := 2) (n := k + 1)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hpow)
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hxz
  obtain ⟨A, hSA, hA2, hA8⟩ := h8 S
  have hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A := fun a ha =>
    (mem_set_normalizer_iff.mp (hSA (hS (mem_zpowers x))) a).mp ha
  exact gsy03_exists_isKleinFour_centralizer hA2 hA8 hxA hx

theorem centralSquareFour_of_exists_normal_elemAbelian {Q : Type} [Group Q] [Finite Q]
    (hZ : IsPGroup 2 (center Q))
    (h8 : ∃ S : Sylow 2 Q, ∃ A : Subgroup Q, (S : Subgroup Q) ≤ normalizer (A : Set Q) ∧
      (∀ a ∈ A, a * a = 1) ∧ 8 ≤ Nat.card A) :
    CentralSquareFour Q := by
  obtain ⟨S₀, A₀, hS₀, hA₀, hA₀8⟩ := h8
  refine centralSquareFour_of_normal_elemAbelian hZ fun S => ?_
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Q S₀ S
  have hgS : ((g • S₀ : Sylow 2 Q) : Subgroup Q) =
      (S₀ : Subgroup Q).map (MulAut.conj g).toMonoidHom := rfl
  have hbij : Function.Bijective (MulAut.conj g).toMonoidHom := (MulAut.conj g).bijective
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨A₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · rw [hgS]
    calc (S₀ : Subgroup Q).map (MulAut.conj g).toMonoidHom
        ≤ (normalizer (A₀ : Set Q)).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hS₀
      _ = normalizer ((A₀.map (MulAut.conj g).toMonoidHom : Subgroup Q) : Set Q) :=
          Subgroup.map_normalizer_eq_of_bijective A₀ hbij
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hA₀ a ha, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact hA₀8

end CFSG.ComponentClassification.Sol76.Sig.GSYard03
