module

public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.IVK.L2.F1

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement Pointwise

section Generic13g

variable {G : Type*} [Group G]

theorem mem_mul_iff_of_index_two' {P P₀ : Subgroup G} (h : (P₀.subgroupOf P).index = 2) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) : x * y ∈ P₀ ↔ (x ∈ P₀ ↔ y ∈ P₀) := by
  have := Subgroup.mul_mem_iff_of_index_two h (a := (⟨x, hx⟩ : P)) (b := ⟨y, hy⟩)
  simpa [Subgroup.mem_subgroupOf] using this

theorem mul_self_mem_of_index_two {P P₀ : Subgroup G} (h : (P₀.subgroupOf P).index = 2) {x : G}
    (hx : x ∈ P) : x * x ∈ P₀ :=
  (mem_mul_iff_of_index_two' h hx hx).mpr Iff.rfl

theorem zpow_odd_mem_iff {P P₀ : Subgroup G} (h : (P₀.subgroupOf P).index = 2) {c : G} (hc : c ∈ P)
    {u : ℤ} (hu : Odd u) : c ^ u ∈ P₀ ↔ c ∈ P₀ := by
  obtain ⟨j, rfl⟩ := hu
  have hc2 : c * c ∈ P₀ := mul_self_mem_of_index_two h hc
  have hpow : c ^ (2 * j) ∈ P₀ := by
    rw [zpow_mul]
    have : c ^ (2 : ℤ) = c * c := by rw [zpow_two]
    rw [this]
    exact P₀.zpow_mem hc2 j
  have hcj : c ^ (2 * j) ∈ P := P.zpow_mem hc _
  rw [zpow_add, zpow_one, mem_mul_iff_of_index_two' h hcj hc]
  simp [hpow]

theorem conj_mem_iff_of_gen {P P₀ : Subgroup G} (h : (P₀.subgroupOf P).index = 2) {c a ρ : G}
    (hgen : Subgroup.closure ({c, a} : Set G) = P) (hρ : ∀ x ∈ P, ρ * x * ρ⁻¹ ∈ P)
    (hc : c ∈ P₀ ↔ ρ * c * ρ⁻¹ ∈ P₀) (ha : a ∈ P₀ ↔ ρ * a * ρ⁻¹ ∈ P₀) :
    ∀ x ∈ P, (x ∈ P₀ ↔ ρ * x * ρ⁻¹ ∈ P₀) := by
  intro x hx
  have hx' : x ∈ Subgroup.closure ({c, a} : Set G) := hgen ▸ hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact hc
    · simpa using ha
  | one => simp
  | mul y z hy hz ihy ihz =>
    have hyP : y ∈ P := hgen ▸ hy
    have hzP : z ∈ P := hgen ▸ hz
    have h1 := mem_mul_iff_of_index_two' h hyP hzP
    have h2 := mem_mul_iff_of_index_two' h (hρ y hyP) (hρ z hzP)
    have h3 : ρ * (y * z) * ρ⁻¹ = (ρ * y * ρ⁻¹) * (ρ * z * ρ⁻¹) := by group
    have ihy' : y ∈ P₀ ↔ ρ * y * ρ⁻¹ ∈ P₀ := ihy hyP
    have ihz' : z ∈ P₀ ↔ ρ * z * ρ⁻¹ ∈ P₀ := ihz hzP
    rw [h1, h3, h2, ihy', ihz']
  | inv y hy ihy =>
    have hyP : y ∈ P := hgen ▸ hy
    have h3 : ρ * y⁻¹ * ρ⁻¹ = (ρ * y * ρ⁻¹)⁻¹ := by group
    have ihy' : y ∈ P₀ ↔ ρ * y * ρ⁻¹ ∈ P₀ := ihy hyP
    rw [inv_mem_iff, h3, inv_mem_iff, ihy']

end Generic13g

theorem not_isCyclic_dihedral {k : ℕ} (hk : 2 ≤ k) : ¬ IsCyclic (DihedralGroup k) := by
  intro hcyc
  have : NeZero k := ⟨by omega⟩
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hcard : Nat.card (DihedralGroup k) = 2 * k := DihedralGroup.nat_card
  have hord : orderOf g = 2 * k := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  rcases g with i | i
  · rw [DihedralGroup.orderOf_r] at hord
    have : k / Nat.gcd k i.val ≤ k := Nat.div_le_self _ _
    omega
  · rw [DihedralGroup.orderOf_sr] at hord
    omega

section Lemma13g

theorem not_le_zpowers_of_isFourSubgroup {G : Type} [Group G] {U : Subgroup G} (hU : IsFourSubgroup U)
    (c : G) : ¬ U ≤ Subgroup.zpowers c := by
  intro hle
  have hcyc : IsCyclic ↥(U.subgroupOf (Subgroup.zpowers c)) := inferInstance
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hcardU : Nat.card ↥(U.subgroupOf (Subgroup.zpowers c)) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hU.2
  have hord : orderOf g = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
  have hgU : (((g : Subgroup.zpowers c) : G)) ∈ U := g.2
  have hel : IsElementaryAbelian 2 ↥U := hU.1
  have hsq : (((g : Subgroup.zpowers c) : G)) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) _ hgU
  have h2 : g ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using hsq
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at this
  omega

theorem exists_r_of_two_lt_orderOf {n : ℕ} {g : DihedralGroup n} (h : 2 < orderOf g) :
    ∃ i, g = DihedralGroup.r i := by
  rcases g with i | i
  · exact ⟨i, rfl⟩
  · rw [DihedralGroup.orderOf_sr] at h
    omega

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] (X Q : Subgroup G)
    (h : ∀ x ∈ X, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q) : X ≤ Subgroup.normalizer (Q : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h x hx y hy, fun hy => ?_⟩
  have := h x⁻¹ (X.inv_mem hx) _ hy
  simpa [mul_assoc] using this

end Lemma13g

section Lemma13gMain

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem ivk_1_3g : IVK_1_3g := by
  intro F _ _ hF K _ _ e N P₀ hP₀P hidx hdih
  have hPT : N.P ≤ (N.T : Subgroup (MulAut K)) := inf_le_left
  have hPinn : N.P ≤ innAut K := inf_le_right
  have hRT : N.R ≤ (N.T : Subgroup (MulAut K)) := inf_le_left
  have hRF : N.R ≤ fieldAutSub e := inf_le_right
  have htT : N.t ∈ (N.T : Subgroup (MulAut K)) := N.t_mem
  have htPt : N.t ∈ N.Pt := ⟨N.t_mem, N.t_mem_diag⟩
  have htP : N.t ∉ N.P := fun h => N.t_not_mem_inn (hPinn h)
  have ht2 : N.t * N.t = 1 := mul_self_eq_one_of_orderOf_eq_two N.t_order
  have hPnorm : ∀ ρ ∈ (N.T : Subgroup (MulAut K)), ∀ x ∈ N.P, ρ * x * ρ⁻¹ ∈ N.P := by
    intro ρ hρ x hx
    exact ⟨(N.T : Subgroup (MulAut K)).mul_mem ((N.T : Subgroup (MulAut K)).mul_mem hρ (hPT hx))
      ((N.T : Subgroup (MulAut K)).inv_mem hρ), innAut_normal.conj_mem x (hPinn hx) ρ⟩
  obtain ⟨n', hn'2, k₀, hk₀, hk₀2, ⟨e₀⟩⟩ := hdih
  have hP₀card : Nat.card P₀ = 2 ^ n' := by
    rw [Nat.card_congr e₀.toEquiv, DihedralGroup.nat_card, ← hk₀]
  have hPcard : Nat.card N.P = 2 ^ (n' + 1) := by
    have h1 := Subgroup.card_mul_index (P₀.subgroupOf N.P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀P).toEquiv, hP₀card, hidx] at h1
    rw [← h1]
    ring
  have hP₀nc : ¬ IsCyclic ↥P₀ := fun hc => not_isCyclic_dihedral hk₀2 (e₀.isCyclic.mp hc)
  obtain ⟨M, hM, hM2, ⟨φP⟩⟩ := P_dihedral_model hF N (n' + 1) hPcard
  obtain ⟨φt⟩ := Pt_dihedral_model hF N (n' + 1) hPcard
  have hMeq : M = 2 ^ n' := by
    rw [pow_succ] at hM
    omega
  have hM4 : 4 ≤ M := by
    rw [hMeq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) hn'2
  have hM2d : 2 ∣ M := by
    rw [hMeq]
    exact dvd_pow_self 2 (by omega)
  have : NeZero M := ⟨by omega⟩
  have hP₀P' : ∀ p ∈ N.P, ∀ y ∈ P₀, p * y * p⁻¹ ∈ P₀ := by
    intro p hp y hy
    have : (P₀.subgroupOf N.P).Normal := Subgroup.normal_of_index_eq_two hidx
    have h1 : (⟨y, hP₀P hy⟩ : N.P) ∈ P₀.subgroupOf N.P := by simpa [Subgroup.mem_subgroupOf] using hy
    have := this.conj_mem _ h1 ⟨p, hp⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hRinv : ∀ ρ ∈ N.R, ∀ y ∈ P₀, ρ * y * ρ⁻¹ ∈ P₀ := by
    intro ρ hρ y hy
    have hρT := hRT hρ
    have hρF := hRF hρ
    obtain ⟨U, hUP, hU4, hUcomm⟩ := N.four_cent
    have hUP' : U ≤ N.P := hUP
    have hρU : ∀ u ∈ U, ρ * u * ρ⁻¹ = u := by
      intro u hu
      rw [hUcomm ρ hρF u hu]
      group
    let cP : ↥N.P := φP.symm (DihedralGroup.r 1)
    let c : MulAut K := (cP : MulAut K)
    have hcord : orderOf c = M := by
      show orderOf (cP : MulAut K) = M
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hcP : c ∈ N.P := cP.2
    have hρc : ρ * c * ρ⁻¹ ∈ N.P := hPnorm ρ hρT c hcP
    have hρcord : orderOf (ρ * c * ρ⁻¹) = M := by
      have := MulEquiv.orderOf_eq (MulAut.conj ρ) c
      rw [MulAut.conj_apply] at this
      rw [this, hcord]
    obtain ⟨u, hu⟩ : ∃ u : ℕ, ρ * c * ρ⁻¹ = c ^ u := by
      have hdord : orderOf (φP ⟨ρ * c * ρ⁻¹, hρc⟩) = M := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hρcord]
      obtain ⟨i, hi⟩ := exists_r_of_two_lt_orderOf (by omega : 2 < orderOf (φP ⟨ρ * c * ρ⁻¹, hρc⟩))
      refine ⟨i.val, ?_⟩
      have h1 : (⟨ρ * c * ρ⁻¹, hρc⟩ : ↥N.P) = cP ^ i.val := by
        apply φP.injective
        rw [hi, map_pow, MulEquiv.apply_symm_apply, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
      have := congrArg Subtype.val h1
      simpa using this
    have hcM : c ^ M = 1 := by
      rw [← hcord]
      exact pow_orderOf_eq_one c
    have hu_odd : Odd u := by
      by_contra hne
      rw [Nat.not_odd_iff_even] at hne
      obtain ⟨j, hj⟩ := hne
      obtain ⟨M', hM'⟩ := hM2d
      have h1 : (ρ * c * ρ⁻¹) ^ M' = 1 := by
        rw [hu, ← pow_mul, hj]
        have : (j + j) * M' = M * j := by rw [hM']; ring
        rw [this, pow_mul, hcM, one_pow]
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hρcord, hM'] at h2
      have := Nat.le_of_dvd (by omega) h2
      omega
    have hUZ := not_le_zpowers_of_isFourSubgroup hU4 c
    obtain ⟨a, haU, haZ⟩ := IsConcreteLE.not_le_iff_exists.mp hUZ
    have hρa : ρ * a * ρ⁻¹ = a := hρU a haU
    have haP : a ∈ N.P := hUP' haU
    have hZP : Subgroup.zpowers c ≤ N.P := (Subgroup.zpowers_le).mpr hcP
    have hZidx : ((Subgroup.zpowers c).subgroupOf N.P).index = 2 := by
      have h1 := Subgroup.card_mul_index ((Subgroup.zpowers c).subgroupOf N.P)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, Nat.card_zpowers, hcord,
        hPcard] at h1
      have h2 : 2 ^ (n' + 1) = M * 2 := by rw [hMeq, pow_succ]
      rw [h2] at h1
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < M) h1
    have hgen : Subgroup.closure ({c, a} : Set (MulAut K)) = N.P := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        intro x hx
        rcases hx with rfl | hx
        · exact hcP
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact haP
      · intro x hx
        have hcl : c ∈ Subgroup.closure ({c, a} : Set (MulAut K)) :=
          Subgroup.subset_closure (Set.mem_insert _ _)
        have hal : a ∈ Subgroup.closure ({c, a} : Set (MulAut K)) :=
          Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        by_cases hxZ : x ∈ Subgroup.zpowers c
        · exact (Subgroup.zpowers_le).mpr hcl hxZ
        · have h1 : x * a⁻¹ ∈ Subgroup.zpowers c := by
            rw [mem_mul_iff_of_index_two' hZidx hx (N.P.inv_mem haP)]
            exact iff_of_false hxZ (fun h => haZ (by simpa using (Subgroup.zpowers c).inv_mem h))
          have h2 : x = (x * a⁻¹) * a := by group
          rw [h2]
          exact Subgroup.mul_mem _ ((Subgroup.zpowers_le).mpr hcl h1) hal
    have hc : c ∈ P₀ ↔ ρ * c * ρ⁻¹ ∈ P₀ := by
      rw [hu, ← zpow_natCast]
      exact (zpow_odd_mem_iff hidx hcP ((Int.odd_coe_nat u).mpr hu_odd)).symm
    have ha : a ∈ P₀ ↔ ρ * a * ρ⁻¹ ∈ P₀ := by rw [hρa]
    exact ((conj_mem_iff_of_gen hidx hgen (hPnorm ρ hρT) hc ha) y (hP₀P hy)).mp hy
  have htN : N.t ∉ Subgroup.normalizer (P₀ : Set (MulAut K)) := by
    intro htN
    have htN' : ∀ y, y ∈ P₀ ↔ N.t * y * N.t⁻¹ ∈ P₀ := fun y => Subgroup.mem_normalizer_iff.mp htN y
    have hidxPt := P_index_two hF N
    have hsq : ∀ g ∈ N.Pt, g * g ∈ P₀ := by
      intro g hg
      by_cases hgP : g ∈ N.P
      · exact mul_self_mem_of_index_two hidx hgP
      · have hgt : g * N.t⁻¹ ∈ N.P := by
          rw [mem_mul_iff_of_index_two' hidxPt hg (N.Pt.inv_mem htPt)]
          have : N.t⁻¹ ∉ N.P := fun h => htP (by simpa using N.P.inv_mem h)
          exact iff_of_false hgP this
        have hg_eq : g = (g * N.t⁻¹) * N.t := by group
        have htpP : N.t * (g * N.t⁻¹) * N.t⁻¹ ∈ N.P := hPnorm N.t htT _ hgt
        have hgg : g * g = (g * N.t⁻¹) * (N.t * (g * N.t⁻¹) * N.t⁻¹) := by
          calc g * g = (g * N.t⁻¹) * N.t * ((g * N.t⁻¹) * N.t) := by rw [← hg_eq]
            _ = (g * N.t⁻¹) * (N.t * (g * N.t⁻¹) * N.t⁻¹) * (N.t * N.t) := by group
            _ = (g * N.t⁻¹) * (N.t * (g * N.t⁻¹) * N.t⁻¹) := by rw [ht2, mul_one]
        rw [hgg, mem_mul_iff_of_index_two' hidx hgt htpP]
        exact htN' _
    have : NeZero (2 ^ (n' + 1)) := ⟨by positivity⟩
    let c'P : ↥N.Pt := φt.symm (DihedralGroup.r 1)
    let c' : MulAut K := (c'P : MulAut K)
    have hc'ord : orderOf c' = 2 ^ (n' + 1) := by
      show orderOf (c'P : MulAut K) = _
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hc'sq : c' * c' ∈ P₀ := hsq c' c'P.2
    have hc'sqord : orderOf (c' * c') = 2 ^ n' := by
      rw [← sq, orderOf_pow' _ (by norm_num), hc'ord]
      have : Nat.gcd (2 ^ (n' + 1)) 2 = 2 := Nat.gcd_eq_right (dvd_pow_self 2 (by omega))
      rw [this, pow_succ]
      omega
    have hzle : Subgroup.zpowers (c' * c') ≤ P₀ := (Subgroup.zpowers_le).mpr hc'sq
    have hzcard : Nat.card P₀ ≤ Nat.card (Subgroup.zpowers (c' * c')) := by
      rw [Nat.card_zpowers, hc'sqord, hP₀card]
    have heq := Subgroup.eq_of_le_of_card_ge hzle hzcard
    exact hP₀nc (heq ▸ inferInstance)
  have hzex : ∃ z ∈ N.P, orderOf z = 2 ∧ ∀ x ∈ N.P, x * z = z * x := by
    obtain ⟨M', hM'⟩ := hM2d
    have hM'pos : 0 < M' := by omega
    have haa : ((M' : ℕ) : ZMod M) + (M' : ℕ) = 0 := by
      rw [← Nat.cast_add, ← two_mul, ← hM', ZMod.natCast_self]
    have ha0 : ((M' : ℕ) : ZMod M) ≠ 0 := by
      intro h
      have := (ZMod.natCast_eq_zero_iff M' M).mp h
      have := Nat.le_of_dvd hM'pos this
      omega
    let zD : DihedralGroup M := DihedralGroup.r ((M' : ℕ) : ZMod M)
    have hzD2 : zD ^ 2 = 1 := by
      show DihedralGroup.r ((M' : ℕ) : ZMod M) ^ 2 = 1
      rw [sq, DihedralGroup.r_mul_r, haa]
      rfl
    have hzD1 : zD ≠ 1 := by
      intro h
      have : (DihedralGroup.r ((M' : ℕ) : ZMod M) : DihedralGroup M) = DihedralGroup.r 0 := h
      exact ha0 (DihedralGroup.r.inj this)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hzD : orderOf zD = 2 := orderOf_eq_prime hzD2 hzD1
    have hcent : ∀ g : DihedralGroup M, g * zD = zD * g := by
      intro g
      rcases g with i | i
      · show DihedralGroup.r i * DihedralGroup.r _ = DihedralGroup.r _ * DihedralGroup.r i
        rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
      · show DihedralGroup.sr i * DihedralGroup.r _ = DihedralGroup.r _ * DihedralGroup.sr i
        rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
        congr 1
        have : (M' : ZMod M) = -(M' : ZMod M) := by
          rw [eq_neg_iff_add_eq_zero]
          exact haa
        rw [sub_eq_add_neg, ← this]
    refine ⟨(φP.symm zD : MulAut K), (φP.symm zD).2, ?_, fun x hx => ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hzD]
    · have h1 : (⟨x, hx⟩ : ↥N.P) * φP.symm zD = φP.symm zD * ⟨x, hx⟩ := by
        apply φP.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hcent _
      exact congrArg Subtype.val h1
  have hK1 : ∀ τ ∈ (N.T : Subgroup (MulAut K)), τ ∈ N.P ⊔ N.R ∨ τ * N.t ∈ N.P ⊔ N.R := by
    intro τ hτ
    obtain ⟨d, hd, r, hr, rfl⟩ := T_decomp N τ hτ
    have hidxPt := P_index_two hF N
    by_cases hdP : d ∈ N.P
    · left
      exact Subgroup.mul_mem_sup hdP hr
    · right
      have hdt : d * N.t ∈ N.P := by
        rw [mem_mul_iff_of_index_two' hidxPt hd htPt]
        exact iff_of_false hdP htP
      have hcommP : ⁅r, N.t⁆ ∈ N.P := by
        have hTT : ⁅r, N.t⁆ ∈ (N.T : Subgroup (MulAut K)) := by
          rw [commutatorElement_def]
          exact (N.T : Subgroup (MulAut K)).mul_mem ((N.T : Subgroup (MulAut K)).mul_mem
            ((N.T : Subgroup (MulAut K)).mul_mem (hRT hr) htT) ((N.T : Subgroup (MulAut K)).inv_mem (hRT hr)))
            ((N.T : Subgroup (MulAut K)).inv_mem htT)
        have hII : ⁅r, N.t⁆ ∈ innAut K :=
          (ivk_1_2a_struct F hF K e N).2.2.2 r (hRF hr) N.t
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        exact ⟨hTT, hII⟩
      have hrt : r * N.t = ⁅r, N.t⁆ * N.t * r := by rw [commutatorElement_def]; group
      have h1 : d * r * N.t = (d * N.t) * (N.t⁻¹ * ⁅r, N.t⁆ * N.t) * r := by
        calc d * r * N.t = d * (r * N.t) := by group
          _ = d * (⁅r, N.t⁆ * N.t * r) := by rw [hrt]
          _ = (d * N.t) * (N.t⁻¹ * ⁅r, N.t⁆ * N.t) * r := by group
      rw [h1]
      have hp4 : N.t⁻¹ * ⁅r, N.t⁆ * N.t ∈ N.P := by
        have := hPnorm N.t⁻¹ ((N.T : Subgroup (MulAut K)).inv_mem htT) _ hcommP
        simpa using this
      exact Subgroup.mul_mem_sup (N.P.mul_mem hdt hp4) hr
  have hSN : N.P ⊔ N.R ≤ Subgroup.normalizer (P₀ : Set (MulAut K)) :=
    sup_le (le_normalizer_of_conj_mem _ _ hP₀P') (le_normalizer_of_conj_mem _ _ hRinv)
  have hST : N.P ⊔ N.R ≤ (N.T : Subgroup (MulAut K)) := sup_le hPT hRT
  have hmain : ∀ H : Subgroup (MulAut K), N.P ⊔ N.R ≤ H → H ≤ (N.T : Subgroup (MulAut K)) →
      N.t ∉ H → H = N.P ⊔ N.R := by
    intro H hSH hHT htH
    apply le_antisymm _ hSH
    intro τ hτ
    rcases hK1 τ (hHT hτ) with h | h
    · exact h
    · exfalso
      apply htH
      have h2 : τ * N.t ∈ H := hSH h
      have h3 := H.mul_mem (H.inv_mem hτ) h2
      simpa using h3
  have h1 : Subgroup.normalizer (P₀ : Set (MulAut K)) ⊓ (N.T : Subgroup (MulAut K)) = N.P ⊔ N.R :=
    hmain _ (le_inf hSN hST) inf_le_right (fun h => htN h.1)
  refine ⟨h1, fun f hf hf2 => ?_⟩
  have hfT := hRT hf
  have hfF := hRF hf
  have hSC : N.P ⊔ N.R ≤ Subgroup.centralizer ({f} : Set (MulAut K)) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact N.R_cent f ⟨hfT, hfF⟩ hf2 x ⟨hPT hx, hPinn hx⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val ((R_isCyclic N).commGroup.mul_comm ⟨x, hx⟩ ⟨f, hf⟩)
  have htC : N.t ∉ Subgroup.centralizer ({f} : Set (MulAut K)) := by
    intro h
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    obtain ⟨z, hzP, hz2, hzc⟩ := hzex
    have hcomm := ivk_1_2i_a F hF K e N f hf hf2 z hzP hz2 hzc
    have h1' : ⁅N.t, f⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h
    rw [h1'] at hcomm
    rw [← hcomm, orderOf_one] at hz2
    omega
  have h2 : Subgroup.centralizer ({f} : Set (MulAut K)) ⊓ (N.T : Subgroup (MulAut K)) =
      N.P ⊔ N.R := hmain _ (le_inf hSC hST) inf_le_right (fun h => htC h.1)
  rw [h1, h2]

end Lemma13gMain

end CFSG.GH74.GLS.IVK.Proofs2
