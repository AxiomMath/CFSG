module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79B

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem e16_mul_self (u : E16) : u * u = 1 := by
  funext i
  have h : ∀ x : Multiplicative (ZMod 2), x * x = 1 := by decide
  exact h (u i)

theorem sec7E_A_elem [Finite G] (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    CFSG.Open.IsElemAbelian 2 (ASub S B) := by
  rw [h78 G t L S z g B hc]
  have ht2 : t ^ 2 = 1 := by rw [← hc.ctx.involution]; exact pow_orderOf_eq_one t
  have hzt : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers t) :=
    CFSG.Open.isElemAbelian_zpowers (p := 2) ht2
  have hB : CFSG.Open.IsElemAbelian 2 B := hc.normalE16.2.1.1
  have hcomm : ∀ a ∈ Subgroup.zpowers t, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have htb : t * b = b * t :=
      (Subgroup.mem_centralizer_singleton_iff.mp
        (hc.ctx.sylow.1 (hc.normalE16.1 hb).1)).symm
    exact ((show Commute t b from htb).zpow_left k).eq
  exact CFSG.Open.IsElemAbelian.sup_of_commute hzt hB hcomm

theorem sec7E_A_le_K [Finite G] (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    ASub S B ≤ MSub S B ⊓ centralizer (B : Set G) := by
  haveI : IsMulCommutative (ASub S B) := (sec7E_A_elem h78 hc).1
  refine le_inf Subgroup.le_normalizer ?_
  intro a ha
  exact Subgroup.mem_centralizer_iff.mpr fun b hb => setLike_mul_comm (sec79_B_le_A hc hb) ha

theorem sec7E_cent_A_le_K [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) :
    centralizer (ASub S B : Set G) ≤ MSub S B ⊓ centralizer (B : Set G) := by
  refine le_inf (Subgroup.centralizer_le_normalizer (ASub S B : Set G)) ?_
  exact Subgroup.centralizer_le (sec79_B_le_A hc)

theorem sec7E_A_sylow [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    IsSylow2Of (ASub S B) (centralizer (ASub S B : Set G)) := by
  have hnoalt : S ⊓ centralizer (B : Set G) ≤ ASub S B :=
    sec79_no_alt2 h36 h76 hP h77b h78 hc
  have hAle : ASub S B ≤ S ⊓ centralizer (B : Set G) := by
    rw [ASub, omega1]
    exact (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hAeq : ASub S B = S ⊓ centralizer (B : Set G) := le_antisymm hAle hnoalt
  have hY : IsSylow2Of (S ⊓ centralizer (B : Set G)) (centralizer (ASub S B : Set G)) :=
    sec79_Y_sylow h36 h76 hP h78 hc
  exact hAeq.symm ▸ hY

theorem sec7E_exists_sylow [Finite G] (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    ∃ E : Subgroup G, IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G)) ∧ ASub S B ≤ E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAK : ASub S B ≤ MSub S B ⊓ centralizer (B : Set G) := sec7E_A_le_K h78 hc
  have hAleS : ASub S B ≤ S := by
    change omega1 (S ⊓ centralizer (B : Set G)) ≤ S
    rw [omega1]
    exact (Subgroup.closure_le S).mpr fun x hx => hx.1.1
  have hA2 : IsPGroup 2 (ASub S B) := hc.ctx.sylow.2.1.to_le hAleS
  have hA2' : IsPGroup 2 ((ASub S B).subgroupOf (MSub S B ⊓ centralizer (B : Set G))) :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
  obtain ⟨Q, hQ⟩ := hA2'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥(MSub S B ⊓ centralizer (B : Set G))).map
    (MSub S B ⊓ centralizer (B : Set G)).subtype, isSylow2Of_map_sylow Q, ?_⟩
  intro a ha
  exact Subgroup.mem_map_of_mem _
    (hQ ((Subgroup.mem_subgroupOf (h := ⟨a, hAK ha⟩)).mpr ha))

theorem sec7E_inf_cent [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) {E : Subgroup G}
    (hE : IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G))) (hAE : ASub S B ≤ E) :
    E ⊓ centralizer (ASub S B : Set G) = ASub S B := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsMulCommutative (ASub S B) := (sec7E_A_elem h78 hc).1
  have hAC : ASub S B ≤ centralizer (ASub S B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun a' ha' => setLike_mul_comm ha' ha
  have hA := sec7E_A_sylow h36 h76 hP h77b h78 hc
  set P : Subgroup G := ASub S B with hPdef
  set C : Subgroup G := centralizer (ASub S B : Set G) with hCdef
  set Q : Subgroup G := E ⊓ C with hQdef
  have hPQ : P ≤ Q := le_inf hAE hAC
  have hQC : Q ≤ C := inf_le_right
  have hodd : ¬ 2 ∣ P.relIndex C := hA.2.2
  have h2Q : IsPGroup 2 Q := hE.2.1.to_le inf_le_left
  obtain ⟨n, hn⟩ := h2Q.index (P.subgroupOf Q)
  have hdvd : P.relIndex Q ∣ P.relIndex C := by
    rw [← Subgroup.relIndex_mul_relIndex (H := P) (K := Q) (L := C) hPQ hQC]
    exact ⟨Q.relIndex C, rfl⟩
  have hrel : P.relIndex Q = 2 ^ n := hn
  have hn0 : n = 0 := by
    by_contra hne
    have h2 : 2 ∣ P.relIndex Q := by
      rw [hrel]
      exact dvd_pow_self 2 hne
    exact hodd (dvd_trans h2 hdvd)
  have hQleP : Q ≤ P := relIndex_eq_one.mp (by rw [hrel, hn0, pow_zero])
  exact le_antisymm hQleP hPQ

theorem sec7E_exists_mul [Finite G] (h710d : Asc82Lemma710d) {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) {E : Subgroup G}
    (hE : IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G))) :
    ∀ k ∈ MSub S B ⊓ centralizer (B : Set G),
      ∃ e ∈ E, ∃ c ∈ centralizer (ASub S B : Set G), k = e * c := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := MSub S B ⊓ centralizer (B : Set G) with hKdef
  obtain ⟨φ, hφs, hφk⟩ := (h710d G t L S z g B hc).2.2.1
  have hcard : Nat.card E16 = 2 ^ 4 := by simp [E16, Nat.card_eq_fintype_card]
  intro k hk
  set k' : ↥K := ⟨k, hk⟩ with hk'def
  have hQtop : (E.subgroupOf K).map φ = ⊤ := by
    have hodd : ¬ 2 ∣ ((E.subgroupOf K).map φ).index := fun h2 =>
      hE.2.2 (dvd_trans h2 (Subgroup.index_map_dvd (E.subgroupOf K) hφs))
    have hdvd : ((E.subgroupOf K).map φ).index ∣ 2 ^ 4 := by
      rw [← hcard]
      exact Subgroup.index_dvd_card (H := (E.subgroupOf K).map φ)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj0 : j = 0 := by
      by_contra hne
      exact hodd (by rw [hj]; exact dvd_pow_self 2 hne)
    exact Subgroup.index_eq_one.mp (by rw [hj, hj0, pow_zero])
  have hmem : φ k' ∈ (E.subgroupOf K).map φ := by
    rw [hQtop]
    exact Subgroup.mem_top _
  obtain ⟨e', he'E, he'eq⟩ := Subgroup.mem_map.mp hmem
  have heE : (e' : G) ∈ E := Subgroup.mem_subgroupOf.mp he'E
  refine ⟨(e' : G), heE, (e' : G)⁻¹ * k, ?_, ?_⟩
  · have hcK : (e' : G)⁻¹ * k ∈ K := K.mul_mem (K.inv_mem e'.2) hk
    have hker : (⟨(e' : G)⁻¹ * k, hcK⟩ : ↥K) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have h1 : (⟨(e' : G)⁻¹ * k, hcK⟩ : ↥K) = e'⁻¹ * k' := rfl
      rw [h1, map_mul, map_inv, he'eq, inv_mul_cancel]
    rw [hφk] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  · group

theorem sec7E_quot [Finite G] (h36 : Asc82Lemma36) (h76 : Asc82Lemma76) (hP : Asc82Tab6P)
    (h77b : Asc82Lemma77b) (h78 : Asc82Lemma78) (h710d : Asc82Lemma710d) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B)
    {E : Subgroup G} (hE : IsSylow2Of E (MSub S B ⊓ centralizer (B : Set G)))
    (hAE : ASub S B ≤ E) : QuotEquivTo E (ASub S B) E16 := by
  classical
  set K : Subgroup G := MSub S B ⊓ centralizer (B : Set G) with hKdef
  set C : Subgroup G := centralizer (ASub S B : Set G) with hCdef
  obtain ⟨φ₀, hφs, hφk⟩ := (h710d G t L S z g B hc).2.2.1
  have hEK : E ≤ K := hE.1
  let φ : ↥E →* E16 := φ₀.comp (Subgroup.inclusion hEK)
  haveI : IsMulCommutative (ASub S B) := (sec7E_A_elem h78 hc).1
  have hAC : ASub S B ≤ C := by
    rw [hCdef]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun a' ha' => setLike_mul_comm ha' ha
  refine ⟨φ, ?_, ?_⟩
  · intro u
    obtain ⟨k, hk⟩ := hφs u
    obtain ⟨e, he, c, hcC, hkec⟩ := sec7E_exists_mul h710d hc hE k k.2
    have hcK : c ∈ K := sec7E_cent_A_le_K hc hcC
    have hc1 : φ₀ ⟨c, hcK⟩ = 1 := by
      have hm : (⟨c, hcK⟩ : ↥K) ∈ φ₀.ker := by
        rw [hφk]
        exact Subgroup.mem_subgroupOf.mpr hcC
      simpa [MonoidHom.mem_ker] using hm
    have heq : φ₀ k = φ₀ ⟨e, hEK he⟩ * φ₀ ⟨c, hcK⟩ := by
      rw [← map_mul]
      exact congrArg φ₀ (Subtype.ext hkec)
    refine ⟨⟨e, he⟩, ?_⟩
    change φ₀ ⟨e, hEK he⟩ = u
    rw [← hk, heq, hc1, mul_one]
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hxE : (x : G) ∈ E := x.2
    constructor
    · intro hx
      have hxC : (x : G) ∈ C := by
        have hm : (⟨x, hEK x.2⟩ : ↥K) ∈ φ₀.ker := by
          rw [MonoidHom.mem_ker]
          change φ x = 1
          exact hx
        rw [hφk] at hm
        exact Subgroup.mem_subgroupOf.mp hm
      have hxEC : (x : G) ∈ E ⊓ C := ⟨hxE, hxC⟩
      rw [sec7E_inf_cent h36 h76 hP h77b h78 hc hE hAE] at hxEC
      exact hxEC
    · intro hx
      have hxC : (x : G) ∈ C := hAC hx
      have hm : (⟨x, hEK x.2⟩ : ↥K) ∈ φ₀.ker := by
        rw [hφk]
        exact Subgroup.mem_subgroupOf.mpr hxC
      rw [MonoidHom.mem_ker] at hm
      change φ x = 1
      exact hm

end CFSG.OddStandard.SmallF3.Omega
