module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinPGL
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6

public section

namespace CFSG.QuasithinUnique.Out21

open CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter
open scoped MatrixGroups

section Arith

theorem twoPart_eq_pow {G : Type*} [Group G] {X : Subgroup G} {k b : ℕ} (hb : ¬ 2 ∣ b)
    (hX : Nat.card X = 2 ^ k * b) : twoPart X = 2 ^ k := by
  unfold twoPart
  rw [hX, Unc25K1.factorization_two_pow_mul hb]

theorem eight_le_two_pow {n : ℕ} (hn : n ≠ 0) (h8 : 8 ∣ n) : 8 ≤ 2 ^ n.factorization 2 := by
  have hv : 3 ≤ n.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).mp (by simpa using h8)
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by norm_num) hv

theorem twoPart_double {G G' : Type*} [Group G] [Finite G] [Group G'] {A : Subgroup G}
    {B : Subgroup G'}
    (h : Nat.card B = 2 * Nat.card A) : twoPart B = 2 * twoPart A := by
  unfold twoPart
  have hn : Nat.card A ≠ 0 := Nat.card_pos.ne'
  rw [h, Nat.factorization_mul (by norm_num) hn]
  simp [Nat.Prime.factorization_self Nat.prime_two, pow_add, pow_succ]

theorem not_dvd_720 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : ¬ p ∣ 720 := by
  intro h
  have h' : p ∣ 2 ^ 4 * 3 ^ 2 * 5 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
  · have := Nat.le_of_dvd (by norm_num) h1
    omega

end Arith

section Model

theorem model_of_isL2pType {X : Type} [Group X] (hX : IsL2pType X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (p : ℕ) (_ : Fact p.Prime),
      7 ≤ p ∧ Nat.card F = p ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧ Nonempty (X ≃* PSL2 F) := by
  rcases hX with ⟨p, hFM, h7, hmodel⟩ | hL32
  · have hp : p.Prime := hFM.1
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨K, hK, hKfin, -, e, hcard, -, -⟩ := K1.psl2_model_data (by omega) hmodel
    have hKp : Nat.card K = p := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
    have hmod : p % 8 = 1 ∨ p % 8 = 7 := by
      rcases Unc25K1.fermat_or_mersenne_pow hFM h7 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    exact ⟨K, hK, inferInstance, p, ⟨hp⟩, by omega, hKp, hmod, ⟨e⟩⟩
  · obtain ⟨F, hF, hFfin, -, e, hq7, -, -⟩ := Unc25K1.exists_psl2_seven hL32
    have hK : Nat.card F = 7 := by rw [Nat.card_eq_fintype_card, hq7]
    exact ⟨F, hF, inferInstance, 7, ⟨Nat.prime_seven⟩, le_rfl, hK, Or.inr rfl, ⟨e⟩⟩

end Model

section Transport

variable {X : Type} [Group X] {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

theorem card_mulAut_of_equiv (hp7 : 7 ≤ p) (hF : Nat.card F = p) (e : X ≃* PSL2 F) :
    Nat.card (MulAut X) = 2 * Nat.card X := by
  rw [Nat.card_congr (MulAut.congr e).toEquiv, card_aut hp7 hF, Nat.card_congr e.toEquiv]

theorem exists_injective_dihedral_of_equiv (hp7 : 7 ≤ p) (hF : Nat.card F = p) (e : X ≃* PSL2 F)
    (P : Subgroup (MulAut X)) (hP : IsPGroup 2 P) :
    ∃ (m : ℕ) (f : ↥P →* DihedralGroup (2 ^ m)), Function.Injective f := by
  set c := MulAut.congr e with hc
  let ι : ↥P ≃* ↥(P.map c.toMonoidHom) :=
    Subgroup.equivMapOfInjective P c.toMonoidHom c.injective
  have hP' : IsPGroup 2 ↥(P.map c.toMonoidHom) := hP.of_equiv ι
  obtain ⟨m, f, hf⟩ := exists_injective_dihedral hp7 hF _ hP'
  exact ⟨m, f.comp ι.toMonoidHom, hf.comp ι.injective⟩

theorem congr_apply' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (α : MulAut X) (y : Y) :
    (MulAut.congr e α) y = e (α (e.symm y)) := rfl

theorem oddNormalFix_of_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {α : MulAut X}
    (h : OddNormalFix (MulAut.congr e α)) : OddNormalFix α := by
  obtain ⟨N, hN1, hNodd, hNle, hNnorm⟩ := h
  refine ⟨N.comap e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hN1
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have h1 : e.symm y ∈ N.comap e.toMonoidHom := by simpa using hy
    rw [hbot, Subgroup.mem_bot] at h1
    simpa using congrArg e h1
  · have hc : N.comap e.toMonoidHom = N.map e.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm e N
    rw [hc, Subgroup.card_map_of_injective e.symm.injective]
    exact hNodd
  · intro x hx
    have h1 : (MulAut.congr e α) (e x) = e x := hNle hx
    rw [congr_apply', MulEquiv.symm_apply_apply] at h1
    exact e.injective h1
  · intro x hx
    have hx' : α x = x := hx
    have hex : e x ∈ fixSub (MulAut.congr e α) := by
      show (MulAut.congr e α) (e x) = e x
      rw [congr_apply', MulEquiv.symm_apply_apply, hx']
    have hn := Subgroup.mem_normalizer_iff.mp (hNnorm hex)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have := hn (e g)
    simpa using this

theorem oddNormalFix_of_outer_involution_of_equiv (hp7 : 7 ≤ p) (hF : Nat.card F = p)
    (e : X ≃* PSL2 F) {α : MulAut X} (hα2 : α * α = 1) (hαi : α ∉ innerAut X) :
    OddNormalFix α := by
  refine oddNormalFix_of_congr e (oddNormalFix_of_outer_involution hp7 hF ?_ ?_)
  · rw [← map_mul, hα2, map_one]
  · rintro ⟨y, hy⟩
    apply hαi
    refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
    rw [← hy]
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem exists_klein_of_sylow [Finite X] (hp7 : 7 ≤ p) (hF : Nat.card F = p) (e : X ≃* PSL2 F)
    {Q : Subgroup X} (hQ : IsSylowTwoOf Q ⊤) :
    ∃ a b : X, a ∈ Q ∧ b ∈ Q ∧ a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have : Finite (PSL2 F) := Finite.of_equiv X e.toEquiv
  obtain ⟨Sy, hSy⟩ :=
    Unc25K1.exists_sylow_of_isSylowTwoOf_top (Unc25K1.isSylowTwoOf_top_map e hQ)
  obtain ⟨t, s, ht, hs, ht2, hs2, ht1, hs1, hts, -⟩ :=
    Unc25K1.exists_commuting_involutions_of_sylow (hodd_of hp7 hF) Sy
  rw [hSy] at ht hs
  obtain ⟨a, haQ, rfl⟩ := Subgroup.mem_map.mp ht
  obtain ⟨b, hbQ, rfl⟩ := Subgroup.mem_map.mp hs
  refine ⟨a, b, haQ, hbQ, ?_, ?_, ?_, ?_, ?_⟩
  · apply e.injective
    rw [map_mul, map_one]
    exact ht2
  · apply e.injective
    rw [map_mul, map_one]
    exact hs2
  · intro h
    apply ht1
    rw [h]
    exact map_one e.toMonoidHom
  · intro h
    apply hs1
    rw [h]
    exact map_one e.toMonoidHom
  · intro h
    apply hts
    rw [h]

omit [Fact p.Prime] in
theorem eight_dvd_card_of_equiv [Fact p.Prime] (hp7 : 7 ≤ p) (hF : Nat.card F = p)
    (hmod : p % 8 = 1 ∨ p % 8 = 7) (e : X ≃* PSL2 F) : 8 ∣ Nat.card X := by
  rw [Nat.card_congr e.toEquiv]
  exact Unc25K1.eight_dvd_card_psl2 hp7 hF hmod

theorem prime_dvd_card_of_equiv (hp7 : 7 ≤ p) (hF : Nat.card F = p) (e : X ≃* PSL2 F) :
    p ∣ Nat.card X := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [Nat.card_congr e.toEquiv, psl2_card_formula F (hodd_of hp7 hF), hF]
  obtain ⟨k, hk⟩ := hpodd
  have h1 : p ^ 2 - 1 = 2 * (2 * k ^ 2 + 2 * k) := by
    have : p ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by rw [hk]; ring
    omega
  have h2 : p * (p ^ 2 - 1) = 2 * (p * (2 * k ^ 2 + 2 * k)) := by rw [h1]; ring
  rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  exact Dvd.intro _ rfl

end Transport

section Family1

variable {G : Type} [Group G] [Finite G] {K H S : Subgroup G}

theorem finite_mulAut (K : Subgroup G) : Finite (MulAut ↥K) :=
  Finite.of_injective (fun σ : MulAut ↥K => (σ : ↥K → ↥K)) DFunLike.coe_injective

theorem conj_mem_autOn (h : OutSetting K H S) {x : ↥K} (hx : (x : G) ∈ S) :
    (MulAut.conj x : MulAut ↥K) ∈ autOn S K := by
  rw [← Setup.range_rho (S_le_normalizer h)]
  refine ⟨⟨x, hx⟩, ?_⟩
  ext v
  rw [Setup.rho_apply_coe]
  simp [MulAut.conj_apply]

theorem card_inf_le_card_autOn
    (h : OutSetting K H S) :
    Nat.card ↥(S ⊓ K) ≤ Nat.card ↥(autOn S K) := by
  have := finite_mulAut K
  refine Nat.card_le_card_of_injective
    (fun x : ↥(S ⊓ K) => (⟨MulAut.conj (⟨(x : G), x.2.2⟩ : ↥K), conj_mem_autOn h x.2.1⟩ :
      ↥(autOn S K))) ?_
  intro a b hab
  have h1 := conj_injective h (congrArg Subtype.val hab)
  exact Subtype.ext (by simpa using congrArg Subtype.val h1)

theorem card_S_le (h : OutSetting K H S)
    (hle : Nat.card ↥(autOn S K) ≤ 2 * Nat.card ↥(S ⊓ K)) :
    Nat.card ↥S ≤ 2 * (Nat.card ↥(S ⊓ K) * Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set G))) := by
  rw [card_S h]
  calc Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set G)) * Nat.card ↥(autOn S K)
      ≤ Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set G)) * (2 * Nat.card ↥(S ⊓ K)) :=
        Nat.mul_le_mul_left _ hle
    _ = 2 * (Nat.card ↥(S ⊓ K) * Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set G))) := by ring

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

theorem card_autOn_le_of_equiv (h : OutSetting K H S) (hp7 : 7 ≤ p) (hF : Nat.card F = p)
    (e : ↥K ≃* PSL2 F) : Nat.card ↥(autOn S K) ≤ 2 * Nat.card ↥(S ⊓ K) := by
  have := finite_mulAut K
  have h1 := card_le_twoPart (le_top : autOn S K ≤ ⊤) (isSylowTwoOf_autOn h).isPGroup
  have h2 : twoPart (⊤ : Subgroup (MulAut ↥K)) = 2 * twoPart K :=
    twoPart_double (by rw [Subgroup.card_top]; exact card_mulAut_of_equiv hp7 hF e)
  have h3 : Nat.card ↥(S ⊓ K) = twoPart K := (isSylowTwoOf_inf h).card_eq
  rw [h2] at h1
  omega

theorem hasDS_of_equiv
    (h : OutSetting K H S) (hp7 : 7 ≤ p) (hF : Nat.card F = p)
    (hmod : p % 8 = 1 ∨ p % 8 = 7) (e : ↥K ≃* PSL2 F) :
    ∃ R : Subgroup ↥(autOn S K), DS.DSData R := by
  obtain ⟨m, f, hf⟩ := exists_injective_dihedral_of_equiv hp7 hF e (autOn S K)
    (isSylowTwoOf_autOn h).isPGroup
  have hQ : IsSylowTwoOf ((S ⊓ K).subgroupOf K) (⊤ : Subgroup ↥K) :=
    (Unc25Small.isSylowTwoOf_subgroupOf_top_iff inf_le_right).mp (isSylowTwoOf_inf h)
  refine hasDS_of_injective_dihedral f hf ?_ ?_
  · have h8K : 8 ∣ Nat.card ↥K := eight_dvd_card_of_equiv hp7 hF hmod e
    have h1 : 8 ≤ twoPart K := eight_le_two_pow Nat.card_pos.ne' h8K
    calc 8 ≤ twoPart K := h1
      _ = Nat.card ↥(S ⊓ K) := ((isSylowTwoOf_inf h).card_eq).symm
      _ ≤ Nat.card ↥(autOn S K) := card_inf_le_card_autOn h
  · obtain ⟨a, b, haQ, hbQ, ha2, hb2, ha1, hb1, hab⟩ := exists_klein_of_sylow hp7 hF e hQ
    have ha := conj_mem_autOn h (Subgroup.mem_subgroupOf.mp haQ).1
    have hb := conj_mem_autOn h (Subgroup.mem_subgroupOf.mp hbQ).1
    refine not_isCyclic_of_klein (a := (⟨MulAut.conj a, ha⟩ : ↥(autOn S K)))
      (b := (⟨MulAut.conj b, hb⟩ : ↥(autOn S K))) ?_ ?_ ?_ ?_ ?_
    · intro hAB
      exact hab (conj_injective h (congrArg Subtype.val hAB))
    · intro hA
      have h1 : (MulAut.conj a : MulAut ↥K) = 1 := congrArg Subtype.val hA
      apply ha1
      apply conj_injective h
      rw [map_one]
      exact h1
    · intro hB
      have h1 : (MulAut.conj b : MulAut ↥K) = 1 := congrArg Subtype.val hB
      apply hb1
      apply conj_injective h
      rw [map_one]
      exact h1
    · apply Subtype.ext
      show MulAut.conj a * MulAut.conj a = 1
      rw [← map_mul, ha2, map_one]
    · apply Subtype.ext
      show MulAut.conj b * MulAut.conj b = 1
      rw [← map_mul, hb2, map_one]

theorem oneClass_of_l2p
    (hX : IsL2pType ↥K) {i j : G} (hi : i ∈ K) (hj : j ∈ K) (hi2 : i * i = 1)
    (hj2 : j * j = 1) (hi1 : i ≠ 1) (hj1 : j ≠ 1) : ∃ k ∈ K, k * i * k⁻¹ = j := by
  have hd := l2pFacts ↥K hX
  have ho : ∀ x : ↥K, x * x = 1 → x ≠ 1 → orderOf x = 2 := fun x hx2 hx1 =>
    orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  obtain ⟨k, hk⟩ := hd.single_class ⟨i, hi⟩ ⟨j, hj⟩
    (ho _ (Subtype.ext (by simpa using hi2)) (fun h => hi1 (congrArg Subtype.val h)))
    (ho _ (Subtype.ext (by simpa using hj2)) (fun h => hj1 (congrArg Subtype.val h)))
  exact ⟨k, k.2, by simpa using congrArg Subtype.val hk⟩

theorem outer_of_l2p
    (h : OutSetting K H S) (hp7 : 7 ≤ p) (hF : Nat.card F = p)
    (e : ↥K ≃* PSL2 F) {u : G} (hu : u ∈ H) (hu2 : u * u = 1)
    (hout : u ∉ K ⊔ (H ⊓ Subgroup.centralizer (K : Set G))) :
    ¬ Nonempty (↥(autOn H K) ≃* ↥A6Models.m10) ∧
      oddCoreIn (K ⊓ Subgroup.centralizer ({u} : Set G)) ≠ ⊥ := by
  refine ⟨?_, oddCoreIn_ne_bot_of_oddNormalFix h hu
    (oddNormalFix_of_outer_involution_of_equiv hp7 hF e (actOf_mul_self h hu hu2)
      (actOf_not_mem_innerAut h hu hout))⟩
  rintro ⟨φ⟩
  have h720 : Nat.card ↥(autOn H K) = 720 := by
    rw [Nat.card_congr φ.toEquiv]
    exact A6.card_m10
  have hdvd : Nat.card ↥K ∣ 720 := by
    rw [← h720, ← card_innerAut h]
    exact Subgroup.card_dvd_of_le (innerAut_le_autOn h)
  exact not_dvd_720 (Fact.out : p.Prime) hp7
    ((prime_dvd_card_of_equiv hp7 hF e).trans hdvd)

end Family1

end CFSG.QuasithinUnique.Out21
