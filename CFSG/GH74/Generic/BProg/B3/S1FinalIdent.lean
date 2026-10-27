module

public import CFSG.GH74.Generic.BProg.B3.S1IdentRank
public import CFSG.GH74.Generic.BProg.B3.S1IdentTable
public import CFSG.GH74.Generic.BProg.B1.Stage3aRank
public import CFSG.GH74.Generic.S1.QuatRank
public import CFSG.GH74.Generic.S3.Front
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorQuaternion
public import CFSG.GH74.Generic.BProg.B3.S1FinalSl2
public import CFSG.ClassicalInvolution.Q3.M11Exact
public import CFSG.Holt.NotStar.Lemma216DihedralA7Facts

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1FinalIdent

open S1FinalSl2
open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification Subgroup
open scoped MatrixGroups

section LiftQ8

variable {H S : Type} [Group H] [Finite H] [Group S]

theorem exists_lift_q8 (ψ : H →* S) (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker))
    (τ₀ : QuaternionGroup 2 →* S) (hτ₀ : Function.Injective τ₀) :
    ∃ τ : QuaternionGroup 2 →* H, Function.Injective τ ∧ ∀ g, ψ (τ g) = τ₀ g := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup S := τ₀.range with hR
  set H' : Subgroup H := R.comap ψ with hH'
  let ψ' : ↥H' →* ↥R := (ψ.comp H'.subtype).codRestrict R (fun h => h.2)
  have hψ's : Function.Surjective ψ' := by
    rintro ⟨r, hr⟩
    obtain ⟨h, rfl⟩ := hψ r
    exact ⟨⟨h, hr⟩, rfl⟩
  have hψ'val : ∀ h : ↥H', ((ψ' h : ↥R) : S) = ψ (h : H) := fun h => rfl
  have hkerψ' : ∀ h : ↥H', h ∈ ψ'.ker ↔ ψ (h : H) = 1 := by
    intro h
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      have := congrArg Subtype.val h1
      rwa [hψ'val] at this
    · intro h1
      apply Subtype.ext
      rw [hψ'val, h1]
      rfl
  let g1 : ↥ψ'.ker →* ↥ψ.ker :=
    (H'.subtype.comp ψ'.ker.subtype).codRestrict ψ.ker (fun h => (hkerψ' h.1).1 h.2)
  have hg1 : Function.Injective g1 := fun x y hxy => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥ψ.ker => (z : H)) hxy
  have hkerodd : Odd (Nat.card ψ'.ker) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective g1 hg1)
  have hR8 : Nat.card ↥R = 8 := by
    have : Nat.card ↥R = Nat.card (QuaternionGroup 2) :=
      (Nat.card_congr (MonoidHom.ofInjective hτ₀).toEquiv).symm
    rw [this, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hH'card : Nat.card ↥H' = Nat.card ↥R * Nat.card ψ'.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ'.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ's).toEquiv
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥H') 2 (n := 3) (by
    rw [hH'card, hR8]
    exact Dvd.intro _ rfl)
  have hP8 : Nat.card ↥P = 8 := by rw [hP]; norm_num
  let f : ↥P →* ↥R := ψ'.comp P.subtype
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxk : (x : ↥H') ∈ ψ'.ker := hx
    have h1 : orderOf (⟨(x : ↥H'), hxk⟩ : ↥ψ'.ker) ∣ Nat.card ↥ψ'.ker := orderOf_dvd_natCard _
    have h2 : orderOf x ∣ Nat.card ↥P := orderOf_dvd_natCard _
    have h3 : orderOf (⟨(x : ↥H'), hxk⟩ : ↥ψ'.ker) = orderOf x := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    rw [h3] at h1
    rw [hP8] at h2
    have h4 : orderOf x ∣ Nat.gcd (Nat.card ↥ψ'.ker) 8 := Nat.dvd_gcd h1 h2
    have h5 : Nat.Coprime (Nat.card ↥ψ'.ker) 8 := by
      have := hkerodd.coprime_two_right
      exact Nat.Coprime.pow_right 3 this
    rw [Nat.Coprime.gcd_eq_one h5] at h4
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  have hfbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).2 ⟨hfinj, by rw [hP8, hR8]⟩
  let e : ↥P ≃* ↥R := MulEquiv.ofBijective f hfbij
  refine ⟨H'.subtype.comp (P.subtype.comp (e.symm.toMonoidHom.comp τ₀.rangeRestrict)), ?_, ?_⟩
  · intro x y hxy
    have h1 : Function.Injective τ₀.rangeRestrict :=
      MonoidHom.rangeRestrict_injective_iff.2 hτ₀
    apply h1
    apply e.symm.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  · intro g
    have h1 : f (e.symm (τ₀.rangeRestrict g)) = τ₀.rangeRestrict g := e.apply_symm_apply _
    have h2 := congrArg (fun z : ↥R => (z : S)) h1
    simpa [f, hψ'val] using h2

end LiftQ8

section Data

structure SL2Data (L : Type) [Group L] (q : ℕ) : Prop where
  q8 : ∃ τ : QuaternionGroup 2 →* L, Function.Injective τ
  inv : ∃ t : L, orderOf t = 2 ∧ q * (q ^ 2 - 1) ≤ Nat.card ↥(centralizer ({t} : Set L))
  dvd : q * (q ^ 2 - 1) ∣ Nat.card L

variable {H L : Type} [Group H] [Finite H] [Group L] [Finite L] {F : Type} [Field F] [Fintype F]

theorem sl2Data_of_quotient (hodd : Odd (Fintype.card F)) (hF : 5 ≤ Fintype.card F)
    (σ : H →* L) (ψ : H →* SL(2, F)) (hψ : Function.Surjective ψ)
    (hker : Odd (Nat.card ψ.ker)) {b : H} (hb2 : b * b = 1) (hbc : ∀ h : H, h * b = b * h)
    (hσb : σ b ≠ 1) : SL2Data L (Fintype.card F) := by
  classical
  have hk : ringChar F ≠ 2 := S1IdentSl2.ringChar_ne_two hodd
  have hsq : ∀ A : SL(2, F), A * A = 1 → A = 1 ∨ A = -1 := fun A hA =>
    (CFSG.LocalAnalysis.ComponentInitial.sl2_sq_eq_one_iff hk A).1 (by rw [pow_two]; exact hA)
  have hψb : ψ b = -1 := by
    rcases hsq (ψ b) (by rw [← map_mul, hb2, map_one]) with h | h
    · exfalso
      have hb : b ∈ ψ.ker := h
      have := eq_one_of_sq_of_mem_odd ψ.ker hker hb hb2
      exact hσb (by rw [this, map_one])
    · exact h
  have hnoinv : ∀ z ∈ σ.ker, z * z = 1 → z = 1 := by
    intro z hz hz2
    rcases hsq (ψ z) (by rw [← map_mul, hz2, map_one]) with h | h
    · exact eq_one_of_sq_of_mem_odd ψ.ker hker h hz2
    · exfalso
      have hzb : z * b ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, h, hψb]
        simp
      have hzb2 : (z * b) * (z * b) = 1 := by
        calc (z * b) * (z * b) = z * (b * z) * b := by group
          _ = z * (z * b) * b := by rw [← hbc z]
          _ = (z * z) * (b * b) := by group
          _ = 1 := by rw [hz2, hb2, one_mul]
      have hzb1 := eq_one_of_sq_of_mem_odd ψ.ker hker hzb hzb2
      have hzinv : z = b⁻¹ := eq_inv_of_mul_eq_one_left hzb1
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
      apply hσb
      have hz1 : σ z = 1 := hz
      rwa [hzinv, hbinv] at hz1
  have hσodd : Odd (Nat.card σ.ker) := odd_card_of_no_involution σ.ker hnoinv
  have hle : σ.ker ≤ ψ.ker := normal_odd_le_ker hodd hF ψ hψ σ.ker hσodd
  have hcardH1 : Nat.card H = Nat.card σ.ker * Nat.card σ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker, mul_comm]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange σ).toEquiv
  have hcardH2 : Nat.card H = Nat.card ψ.ker * Nat.card SL(2, F) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, mul_comm]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv
  obtain ⟨r, hr⟩ : Nat.card σ.ker ∣ Nat.card ψ.ker := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card σ.ker := Nat.card_pos
  have hrange : Nat.card σ.range = r * Nat.card SL(2, F) := by
    have : Nat.card σ.ker * Nat.card σ.range = Nat.card σ.ker * (r * Nat.card SL(2, F)) := by
      rw [← hcardH1, hcardH2, hr]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hdvd1 : Nat.card SL(2, F) ∣ Nat.card σ.range := ⟨r, by rw [hrange]; ring⟩
  have hcardSL : Nat.card SL(2, F) = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
    rw [S1IdentSl2.card_sl2, Nat.card_eq_fintype_card]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨τ₀, hτ₀⟩ := S1IdentSl2.exists_quaternion_hom hk (MonoidHom.id SL(2, F))
      Function.injective_id
    obtain ⟨τ, hτ, hτψ⟩ := exists_lift_q8 ψ hψ hker τ₀ hτ₀
    refine ⟨σ.comp τ, ?_⟩
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : τ g ∈ σ.ker := hg
    have h1 : orderOf (τ g) ∣ Nat.card σ.ker := by
      have := orderOf_dvd_natCard (⟨τ g, hmem⟩ : ↥σ.ker)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf (τ g) ∣ 8 := by
      refine (orderOf_map_dvd τ g).trans ?_
      have := orderOf_dvd_natCard g
      rwa [Nat.card_eq_fintype_card, QuaternionGroup.card] at this
    have h3 := Nat.dvd_gcd h1 h2
    have h5 : Nat.Coprime (Nat.card σ.ker) 8 := Nat.Coprime.pow_right 3 hσodd.coprime_two_right
    rw [Nat.Coprime.gcd_eq_one h5] at h3
    have h6 : τ g = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
    exact hτ (by rw [h6, map_one])
  · refine ⟨σ b, orderOf_eq_prime (by rw [sq, ← map_mul, hb2, map_one]) hσb, ?_⟩
    have hsub : σ.range ≤ centralizer ({σ b} : Set L) := by
      rintro _ ⟨h, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hbc h]
    have h1 := Subgroup.card_le_of_le hsub
    have h2 : Nat.card SL(2, F) ≤ Nat.card σ.range := Nat.le_of_dvd Nat.card_pos hdvd1
    rw [hcardSL] at h2
    exact h2.trans h1
  · rw [← hcardSL]
    exact hdvd1.trans (Subgroup.card_subgroup_dvd_card _)

end Data

section Leaves

theorem card_centralizer_le_of_injective {M N : Type} [Group M] [Group N] [Finite N]
    (f : M →* N) (hf : Function.Injective f) (t : M) :
    Nat.card ↥(centralizer ({t} : Set M)) ≤ Nat.card ↥(centralizer ({f t} : Set N)) := by
  refine Nat.card_le_card_of_injective
    (fun g => (⟨f g, ?_⟩ : ↥(centralizer ({f t} : Set N)))) ?_
  · have h := g.2
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    rw [← map_mul, ← map_mul, h]
  · intro g1 g2 h
    exact Subtype.ext (hf (congrArg Subtype.val h))

variable {L : Type} [Group L] {q : ℕ}

theorem false_of_alt7 (hq : 5 ≤ q) (h : SL2Data L q) (e : L ≃* alternatingGroup (Fin 7)) :
    False := by
  obtain ⟨t, ht2, htc⟩ := h.inv
  let f : L →* Equiv.Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := (Subgroup.subtype_injective _).comp e.injective
  have hord : orderOf (f t) = 2 := by rw [orderOf_injective f hf t]; exact ht2
  have h2 : f t ^ 2 = 1 := by
    have := pow_orderOf_eq_one (f t)
    rwa [hord] at this
  have hne : f t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hord; omega
  have hs : Equiv.Perm.sign (f t) = 1 := Equiv.Perm.mem_alternatingGroup.1 (e t).2
  have h48 := CFSG.Holt.NotStar216.card_centralizer_of_involution h2 hne hs
  have hc := card_centralizer_le_of_injective f hf t
  rw [h48] at hc
  have := S1IdentSl2.le_card_sl2 hq
  omega

theorem false_of_m11 (hq : 5 ≤ q) (h : SL2Data L q) (e : L ≃* StatedM11) : False := by
  obtain ⟨t, ht2, htc⟩ := h.inv
  let e' : L ≃* ↥CFSG.Blueprint.NativeSporadic.M11 :=
    e.trans (MulEquiv.subgroupCongr
      CFSG.Semidihedral.GL2Recognition.lowTwoRankStatedM11_eq_nativeM11)
  have hord : orderOf (e' t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht2
  have h48 := CFSG.ClassicalInvolution.Q3.card_centralizer_le_of_orderOf_eq_two hord
  have hc := card_centralizer_le_of_injective e'.toMonoidHom e'.injective t
  have := S1IdentSl2.le_card_sl2 hq
  have hc' : Nat.card ↥(centralizer ({t} : Set L)) ≤
      Nat.card ↥(centralizer ({e' t} : Set ↥CFSG.Blueprint.NativeSporadic.M11)) := hc
  omega

theorem false_of_psl3_three [Finite L] {p f : ℕ} (hq : 5 ≤ q) (h : SL2Data L q)
    (hL : LieModel L .PSL 3 p f) (h3 : p ^ f = 3) : False := by
  have hc := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hL
  rw [h3] at hc
  have h5616 : Nat.card L = 5616 := by rw [hc]; decide
  have hdvd := h.dvd
  rw [h5616] at hdvd
  exact S1IdentSl2.not_sl2_dvd_5616 q hq hdvd

end Leaves

theorem J_L3_of_sl2_data
    {X : Type} [Group X] [Finite X] (hX : Gen4 X) {M : Subgroup X} (hM : IsQuasisimple ↥M)
    (φ : QuaternionGroup 2 →* X) (hφ : Function.Injective φ)
    (hcent : ∀ g : QuaternionGroup 2, ∀ m ∈ M, φ g * m = m * φ g) {q : ℕ} (hq : 5 ≤ q)
    (hd : SL2Data (↥M ⧸ center ↥M) q) : B1.QShape3SD (↥M ⧸ center ↥M) := by
  have : IsSimpleGroup (↥M ⧸ center ↥M) := hM.2.1
  have hnonab : ∃ a b : ↥M ⧸ center ↥M, a * b ≠ b * a := hM.2.2
  have heven := even_card_of_nonabelian_simple hnonab
  have hlow : 2 ≤ CFSG.Open.twoRank (↥M ⧸ center ↥M) :=
    CFSG.Milestones.lr_nonabelian_simple_two_rank_lower_bound (↥M ⧸ center ↥M) hnonab heven
  have hup := CFSG.GH74.Generic.S1.twoRank_le_two_of_quaternion_centralizer hX φ hφ hcent
  have hrank : CFSG.Open.twoRank (↥M ⧸ center ↥M) = 2 := le_antisymm hup hlow
  rcases CFSG.Milestones.lr_rank_two_isomorphism_types (↥M ⧸ center ↥M) hnonab hrank with
    ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | h | h | h
  ·
    obtain ⟨τ, hτ⟩ := hd.q8
    exact (OddSelector.not_psl_two_odd_of_quaternion τ hτ hp2 h).elim
  ·
    have hL : LieModel (↥M ⧸ center ↥M) .PSL 3 p f :=
      lieModel_of_statedClassicalModel (by decide) h
    have hodd' : p ^ f % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h4 | h4
    · exact (S1IdentRank.false_of_rankCertified_quaternion_centralizer hX φ hφ hcent (r := 2)
        le_rfl (CFSG.GH74.Generic.S3.rankCertified_two_of_eps ⟨p, f, Or.inl ⟨hL, h4⟩⟩)).elim
    · by_cases h3 : 3 < p ^ f
      · exact ⟨p, f, hp, hp2, h3, Or.inl ⟨hL, h4⟩⟩
      · exact (false_of_psl3_three hq hd hL (by omega)).elim
  ·
    have hL : LieModel (↥M ⧸ center ↥M) .PSU 3 p f :=
      lieModel_of_statedClassicalModel (by decide) h
    have hodd' : p ^ f % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h4 | h4
    · exact ⟨p, f, hp, hp2, by omega, Or.inr ⟨hL, h4⟩⟩
    · exact (S1IdentRank.false_of_rankCertified_quaternion_centralizer hX φ hφ hcent (r := 2)
        le_rfl (CFSG.GH74.Generic.S3.rankCertified_two_of_eps ⟨p, f, Or.inr ⟨hL, h4⟩⟩)).elim
  ·
    exact (S1IdentRank.false_of_rankCertified_quaternion_centralizer hX φ hφ hcent (r := 3)
      (by norm_num) (S1IdentTable.rankCertified_u34
        (lieModel_of_statedClassicalModel (by decide) h))).elim
  ·
    obtain ⟨e7⟩ := h
    exact (false_of_alt7 hq hd e7).elim
  ·
    obtain ⟨e11⟩ := h
    exact (false_of_m11 hq hd e11).elim

end S1FinalIdent

end CFSG.GH74.Generic.BProg.B3
