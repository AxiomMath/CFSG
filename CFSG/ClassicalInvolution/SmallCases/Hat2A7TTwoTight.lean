module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TZStar

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section TwoGroup

variable {F : Type} [Group F] [Finite F]

theorem le_centralizer_of_two_group_normalizes {J : Subgroup F} {t : F}
    (hJ : IsClassical2A7 ⊤ J t) (P1 : classicalInvolutionOddCore ↥J ≤ Subgroup.center ↥J)
    {R : Subgroup F} (hRN : R ≤ Subgroup.normalizer (J : Set F)) (hR2 : IsPGroup 2 R)
    (hcard : 4 < Nat.card R) {z : F} (hzR : z ∈ R)
    (huniq : ∀ x ∈ R, orderOf x = 2 → x = z) : J ≤ Subgroup.centralizer ({z} : Set F) := by
  have htriv := oddQuotAut_conjOn_eq_one_of_card hJ.witness hRN hR2 hzR huniq hcard
  have hzc := centralizes_of_oddQuotAut_eq_one hJ.perfect P1 (hRN hzR) htriv
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hzc k hk

theorem two_subgroup_unique_involution {N : Subgroup F} {z : F} (hN : IsClassical2A7 ⊤ N z)
    {R : Subgroup F} (hRN : R ≤ N) (hR2 : IsPGroup 2 R) (hcard : 4 < Nat.card R) :
    z ∈ R ∧ ∀ x ∈ R, orderOf x = 2 → x = z := by
  have huniq : ∀ x ∈ R, orderOf x = 2 → x = z := fun x hx hx2 =>
    hN.eq_of_orderOf_eq_two (hRN hx) hx2
  refine ⟨?_, huniq⟩
  have hdvd : 2 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk] at hcard ⊢
    have : k ≠ 0 := by
      rintro rfl
      simp at hcard
    exact dvd_pow_self 2 this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxz : (x : F) = z := huniq x x.2 (by rw [Subgroup.orderOf_coe]; exact hx)
  rw [← hxz]
  exact x.2

end TwoGroup

section TwoTight

variable {F : Type} [Group F] [Finite F]

@[expose] def TwoTightClass (K : Subgroup F) : Prop :=
  ∀ (w : F) (L : Subgroup F), IsClassical2A7 ⊤ L w →
    (∃ g : F, L = K.map (MulAut.conj g).toMonoidHom) →
    ∀ R : Subgroup F, R ≤ Subgroup.centralizer ({w} : Set F) → IsPGroup 2 R →
      ∃ L' : Subgroup F, IsClassical2A7 ⊤ L' w ∧
        (∃ h : F, L' = K.map (MulAut.conj h).toMonoidHom) ∧ R ≤ Subgroup.normalizer (L' : Set F)

omit [Finite F] in
theorem isPGroup_zpowers_of_orderOf_eq_two {u : F} (hu : orderOf u = 2) :
    IsPGroup 2 (Subgroup.zpowers u) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; simp)

theorem commOrEq_of_twoTight (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F)
    (P1 : ClassicalQuasisimple F) {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hT : TwoTightClass K) {g : F} (hg : (g * z * g⁻¹) * z = z * (g * z * g⁻¹)) :
    CommOrEq K (K.map (MulAut.conj g).toMonoidHom) := by
  by_contra hbad
  set u : F := g * z * g⁻¹ with hudef
  set J : Subgroup F := K.map (MulAut.conj g).toMonoidHom with hJdef
  have hJ : IsClassical2A7 ⊤ J u := isClassical2A7_map_conj hK g
  have hu2 : orderOf u = 2 := hJ.orderOf_eq_two
  have hz2 : orderOf z = 2 := hK.orderOf_eq_two
  have huC : u ∈ Subgroup.centralizer ({z} : Set F) := Subgroup.mem_centralizer_singleton_iff.mpr hg
  obtain ⟨N, hN, -, hNu⟩ := hT z K hK ⟨1, by ext x; simp⟩ (Subgroup.zpowers u)
    (Subgroup.zpowers_le.mpr huC) (isPGroup_zpowers_of_orderOf_eq_two hu2)
  have huN : u ∈ Subgroup.normalizer (N : Set F) := hNu (Subgroup.mem_zpowers u)
  have hKN : CommOrEq K N :=
    commOrEq_of_le_centralizer hZ IH hz2 ⟨z, hK⟩ ⟨z, hN⟩ hK.le_centralizer hN.le_centralizer
  have hu1 : u * u = 1 := hJ.mul_self
  obtain ⟨R, hRN, hR2, hR8, hRu⟩ := exists_two_subgroup_centralizing hN.witness huN hu1
  have hRC : R ≤ Subgroup.centralizer ({u} : Set F) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hRu r hr).symm
  obtain ⟨hzR, huniq⟩ := two_subgroup_unique_involution hN hRN hR2 (by omega)
  obtain ⟨J', hJ', -, hRJ'⟩ := hT u J hJ ⟨g, rfl⟩ R hRC hR2
  have hJ'z : J' ≤ Subgroup.centralizer ({z} : Set F) :=
    le_centralizer_of_two_group_normalizes hJ' (P1 J' u hJ') hRJ' hR2 (by omega) hzR huniq
  have hJ'N : CommOrEq J' N :=
    commOrEq_of_le_centralizer hZ IH hz2 ⟨u, hJ'⟩ ⟨z, hN⟩ hJ'z hN.le_centralizer
  have hKJ' : CommOrEq K J' := commOrEq_trans hZ IH ⟨z, hK⟩ ⟨z, hN⟩ ⟨u, hJ'⟩ hKN hJ'N.symm
  have hJJ' : CommOrEq J J' :=
    commOrEq_of_le_centralizer hZ IH hu2 ⟨u, hJ⟩ ⟨u, hJ'⟩ hJ.le_centralizer hJ'.le_centralizer
  exact hbad (commOrEq_trans hZ IH ⟨z, hK⟩ ⟨u, hJ'⟩ ⟨u, hJ⟩ hKJ' hJJ'.symm)

end TwoTight

end CFSG.ClassicalInvolution.Hat2A7T
