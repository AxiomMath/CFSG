module

public import CFSG.GH74.GLS.TwoThin.OddOrbit
public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.GroupTheory.NonabelianSimpleOrderSixty
public import CFSG.Timmesfeld.Final.Simple
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank
open scoped commutatorElement

theorem exists_involution_lift {I K₀ : Type*} [Group I] [Finite I] [Group K₀] (φ : I →* K₀)
    (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker)) {zb : K₀} (hz : orderOf zb = 2) :
    ∃ z : I, orderOf z = 2 ∧ φ z = zb := by
  obtain ⟨g, hg⟩ := hφ zb
  have hzb2 : zb ^ 2 = 1 := by
    have := pow_orderOf_eq_one zb
    rwa [hz] at this
  have hg2 : g ^ 2 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hg, hzb2]
  set n := Nat.card φ.ker with hn
  have hpow : (g ^ 2) ^ n = 1 := by
    have h1 : orderOf (⟨g ^ 2, hg2⟩ : φ.ker) ∣ n := orderOf_dvd_natCard _
    have h2 : (⟨g ^ 2, hg2⟩ : φ.ker) ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
    exact congrArg Subtype.val h2
  have hz2 : (g ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact hpow
  obtain ⟨k, hk⟩ := hodd
  have hφz : φ (g ^ n) = zb := by
    rw [map_pow, hg, hk, pow_succ, pow_mul, hzb2, one_pow, one_mul]
  have hz1 : g ^ n ≠ 1 := by
    intro h1
    rw [h1, map_one] at hφz
    rw [← hφz, orderOf_one] at hz
    omega
  refine ⟨g ^ n, orderOf_eq_prime hz2 hz1, hφz⟩

theorem exists_involution_centralizer_surjective {I K₀ : Type*} [Group I] [Finite I] [Group K₀]
    (φ : I →* K₀) (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker)) {z : I}
    (hz2 : z * z = 1) (hzc : φ z ∈ center K₀) (k : K₀) :
    ∃ c : I, z * c = c * z ∧ φ c = k := by
  obtain ⟨x, rfl⟩ := hφ k
  have hcomm : ∀ y ∈ (⊤ : Subgroup I), ⁅y, z⁆ ∈ φ.ker := by
    intro y _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hzc) (φ y))
  obtain ⟨c, -, hcz, o, ho, hxco⟩ := exists_commute_mul_mem_of_odd (G := I) (K := ⊤) (O := φ.ker)
    (t := z) hodd le_top hz2 (fun o ho => (MonoidHom.normal_ker φ).conj_mem o ho z) hcomm x
    (Subgroup.mem_top x)
  refine ⟨c, hcz, ?_⟩
  rw [hxco, map_mul, (MonoidHom.mem_ker.mp ho), mul_one]

theorem inB2_cases
    {K : Type} [Group K] (h : InB2 K) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ Nonempty (K ≃* StatedSL 2 F)) ∨
      (∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧ IsDoubleCoverOfAlt K n) ∨
      (IsL34Quotient K ∧ Monoid.exponent ↥(center K) = 4) := by
  obtain ⟨⟨hq, hc⟩, hne⟩ := h
  have hsimple : IsSimpleGroup K → False := by
    intro hs
    rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with h1 | h1
    · exact hne h1
    · obtain ⟨a, b, hab⟩ := hq.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have h2 := Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top a') b'
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h2]
  rcases hc with ⟨p, f, hp, hf, hP, hL⟩ | hSL | hA7 | hA | hL34
  · exact absurd (CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL) hsimple
  · exact Or.inl hSL
  · obtain ⟨e⟩ := hA7
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact absurd e.isSimpleGroup hsimple
  · exact Or.inr (Or.inl hA)
  · exact Or.inr (Or.inr hL34)

theorem exists_central_involution_statedSL_two (F : Type) [Field F] [Finite F]
    (h : Odd (Nat.card F)) :
    ∃ z : StatedSL 2 F, z ∈ center (StatedSL 2 F) ∧ orderOf z = 2 := by
  let m : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ)
  have hmat : (m : Matrix (Fin 2) (Fin 2) F) = -1 := by
    ext i j
    simp [m, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hdet : (m : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [hmat, Matrix.det_neg]
    simp
  have hm : m ∈ StatedSL 2 F := Subgroup.subset_closure hdet
  have hmc : m ∈ center (GL (Fin 2) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have hm2 : m ^ 2 = 1 := by
    show (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ)) ^ 2 = 1
    rw [← map_pow, neg_one_sq, map_one]
  have hm1 : m ≠ 1 := by
    intro h1
    have h2 : (m : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [h1]; rfl
    rw [hmat] at h2
    have h0 := congrFun (congrFun h2 0) 0
    simp at h0
    exact neg_one_ne_one_of_odd_card F h h0
  refine ⟨⟨m, hm⟩, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hmc g)
  · refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext hm2
    · intro h1
      exact hm1 (congrArg Subtype.val h1)

theorem exists_central_involution_of_inB2
    {K : Type} [Group K] [Finite K] (h : InB2 K) :
    ∃ z : K, z ∈ center K ∧ orderOf z = 2 := by
  rcases inB2_cases h with ⟨F, _, _, hodd, ⟨e⟩⟩ | ⟨n, -, -, hq, hc2, -⟩ | ⟨-, hexp⟩
  · obtain ⟨z, hzc, hz2⟩ := exists_central_involution_statedSL_two F hodd
    refine ⟨e.symm z, ?_, ?_⟩
    · have := Subgroup.map_center_eq e.symm
      rw [← this]
      exact ⟨z, hzc, rfl⟩
    · rw [MulEquiv.orderOf_eq]
      exact hz2
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center K)) 2 (by rw [hc2])
    exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩
  · have h4 : 4 ∣ Nat.card ↥(center K) := by
      rw [← hexp]
      exact Group.exponent_dvd_nat_card
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center K)) 2
      (dvd_trans (by norm_num) h4)
    exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩

theorem exists_involution_section
    {L : Type} [Group L] [Finite L] {I : Subgroup L} {K₀ : Type}
    [Group K₀] (hK₀ : InB2 K₀) (φ : ↥I →* K₀) (hφs : Function.Surjective φ)
    (hφo : Odd (Nat.card φ.ker)) :
    ∃ z : L, orderOf z = 2 ∧ ∃ (H : Subgroup L) (hz : z ∈ H) (ψ : ↥H →* K₀),
      H ≤ centralizer ({z} : Set L) ∧ Function.Surjective ψ ∧ ψ ⟨z, hz⟩ ∈ center K₀ ∧
        orderOf (ψ ⟨z, hz⟩) = 2 := by
  have : Finite K₀ := Finite.of_surjective φ hφs
  obtain ⟨zb, hzbc, hzb2⟩ := exists_central_involution_of_inB2 hK₀
  obtain ⟨z₀, hz₀, hφz₀⟩ := exists_involution_lift φ hφs hφo hzb2
  have hz₀sq : z₀ * z₀ = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hz₀)
  have hcen : φ z₀ ∈ center K₀ := hφz₀ ▸ hzbc
  set z : L := (z₀ : L) with hzdef
  have hz2 : orderOf z = 2 := by
    rw [hzdef, Subgroup.orderOf_coe]
    exact hz₀
  have hzI : z ∈ I := z₀.2
  have hzH : z ∈ I ⊓ centralizer ({z} : Set L) :=
    ⟨hzI, Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]⟩
  refine ⟨z, hz2, I ⊓ centralizer ({z} : Set L), hzH, φ.comp (Subgroup.inclusion inf_le_left),
    inf_le_right, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨c, hcz, hck⟩ := exists_involution_centralizer_surjective φ hφs hφo hz₀sq hcen k
    have hcL : (c : L) ∈ I ⊓ centralizer ({z} : Set L) := by
      refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      rw [Set.mem_singleton_iff.mp hh]
      exact congrArg Subtype.val hcz
    exact ⟨⟨(c : L), hcL⟩, hck⟩
  · simpa using hφz₀ ▸ hzbc
  · simpa using hφz₀ ▸ hzb2

theorem false_of_solvable_centralizers
    {L : Type} [Group L] [Finite L] {I : Subgroup L}
    {K₀ : Type} [Group K₀] (hK₀ : InB2 K₀) (φ : ↥I →* K₀) (hφs : Function.Surjective φ)
    (hφo : Odd (Nat.card φ.ker))
    (hsolv : ∀ z : L, orderOf z = 2 → Group.IsSolvable ↥(centralizer ({z} : Set L))) : False := by
  obtain ⟨z, hz2, H, hzH, ψ, hHle, hψs, -, -⟩ := exists_involution_section hK₀ φ hφs hφo
  have hs := hsolv z hz2
  have hsH : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHle)
  have hsK : Group.IsSolvable K₀ := Group.isSolvable_of_surjective hψs
  have : Nontrivial K₀ := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK₀.2
    exact ⟨⟨x, 1, fun h => hx1 (Subtype.ext h)⟩⟩
  have : Group.IsPerfect K₀ := hK₀.1.1.1
  exact Group.IsPerfect.not_isSolvable K₀ hsK

theorem card_ge_of_inB2 {K : Type} [Group K] [Finite K] (h : InB2 K) : 120 ≤ Nat.card K := by
  obtain ⟨⟨hq, -⟩, hne⟩ := h
  have h60 : 60 ≤ Nat.card (K ⧸ center K) :=
    CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty hq.2.1 hq.2.2
  have h2 : 2 ≤ Nat.card ↥(center K) := by
    have := (Subgroup.one_lt_card_iff_ne_bot (center K)).2 hne
    omega
  have hcard : Nat.card K = Nat.card (K ⧸ center K) * Nat.card ↥(center K) := by
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rw [hcard]
  calc 120 = 60 * 2 := by norm_num
    _ ≤ _ := Nat.mul_le_mul h60 h2

theorem false_of_card_centralizers
    {L : Type} [Group L] [Finite L] {I : Subgroup L}
    {K₀ : Type} [Group K₀] (hK₀ : InB2 K₀) (φ : ↥I →* K₀) (hφs : Function.Surjective φ)
    (hφo : Odd (Nat.card φ.ker))
    (hcard : ∀ z : L, orderOf z = 2 → Nat.card ↥(centralizer ({z} : Set L)) < 120) : False := by
  obtain ⟨z, hz2, H, hzH, ψ, hHle, hψs, -, -⟩ := exists_involution_section hK₀ φ hφs hφo
  have : Finite K₀ := Finite.of_surjective φ hφs
  have h1 : Nat.card K₀ ≤ Nat.card ↥H := Nat.card_le_card_of_surjective ψ hψs
  have h2 : Nat.card ↥H ≤ Nat.card ↥(centralizer ({z} : Set L)) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hHle) (Subgroup.inclusion_injective hHle)
  have h3 := hcard z hz2
  have h4 := card_ge_of_inB2 hK₀
  omega

end CFSG.GH74.GLS.TwoThin
