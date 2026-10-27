module

public import CFSG.ClassicalInvolution.RouteD.TypeUThreeChart
public import CFSG.ClassicalInvolution.RouteD.TypeUPatternPartner

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

section Sign

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem conjSign_blockEmb2_of_eq (hK : Nat.card K = (p ^ f) ^ 2) {m : ℕ} (v : Fin (m + 1) → ZMod 2)
    (a : Fin m) (h : v a.castSucc = v a.succ) (A : Su K p f 2) :
    conjSign hK v (blockEmb2 K p f m a A) = blockEmb2 K p f m a A := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  rw [coe_coe_conjSign_apply]
  have hs : ∀ b : ZMod 2, (signVal K b)⁻¹ = signVal K b := fun b =>
    inv_eq_of_mul_eq_one_right (signVal_mul_self _)
  have hd0 : ∀ i, signVal K (v i) ≠ 0 := fun i h0 => by
    have := signVal_mul_self (K := K) (v i)
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have := diag_conj_blockEmb2 (K := K) (p := p) (f := f) a (fun i => signVal K (v i)) hd0
    (by simp only [h]) A i j
  rw [hs] at this
  exact this

end Sign

section Middle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem UCtx.exists_middle_three (c : UCtx p f 3 Ω K z) (nd : UNodes c) (hMFZ : FundNoncentral p)
    (hshape : LocalShapeU p f 3 Ω z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember p f β t)
    (hnK : ¬ Commutes K β)
    (hpair : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W K β)
    (hfirst : ¬ Commutes β (nd.j 0)) (hlast : Commutes β (nd.j 2)) :
    ∃ N : Subgroup G, N ∈ centralizingMembers Ω {z} ∧ N ≠ K ∧ Commutes β N ∧
      (∃ W : Subgroup G,
        UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (nd.j 0) N) ∧
      (∃ W : Subgroup G,
        UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W N (nd.j 2)) := by
  classical
  have h2 := c.h2
  obtain ⟨htz, hσ2, hstab, -, hfixiff⟩ := c.partner_setup nd hMFZ hshape hsingle hβ hwβ hnK hpair
  have himg : ∀ a (ha : a < 3), locImg Ω z (nd.j a) =
      (blockEmb2 (GaloisField p (2 * f)) p f 3 ⟨a, ha⟩).range.map c.d.ψ := fun a ha => by
    rw [nd.img a ha, range_blockEmb2_eq_LcU_nodePair h2 ha]
  have hfix : ∀ A : Su (GaloisField p (2 * f)) p f 2,
      locAut c.hΩ.conjInvariant htz
          (c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f 3 ⟨2, by omega⟩ A)) =
        c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f 3 ⟨2, by omega⟩ A) := by
    intro A
    refine (hfixiff (nd.j 2) (nd.mem 2 (by omega)) (commutes_symm (nd.commK 2 (by omega)))).mpr
      (commutes_symm hlast) _ ?_
    rw [himg 2 (by omega)]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩
  have hmove : ∃ A : Su (GaloisField p (2 * f)) p f 2,
      locAut c.hΩ.conjInvariant htz
          (c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f 3 ⟨0, by omega⟩ A)) ≠
        c.d.ψ (blockEmb2 (GaloisField p (2 * f)) p f 3 ⟨0, by omega⟩ A) := by
    by_contra hcon
    push Not at hcon
    have hfx : ∀ a ∈ locImg Ω z (nd.j 0), locAut c.hΩ.conjInvariant htz a = a := by
      intro a ha
      rw [himg 0 (by omega)] at ha
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
      exact hcon A
    exact hfirst (commutes_symm ((hfixiff (nd.j 0) (nd.mem 0 (by omega))
      (commutes_symm (nd.commK 0 (by omega)))).mp hfx))
  obtain ⟨h, hh0, hh2, hhσ⟩ := unitary_partner_chart_three c.card_eq c.hp2 c.hq c.d.ψ c.d.ker_le
    (locAut c.hΩ.conjInvariant htz) hσ2 hstab hfix hmove
  have hcinj : Function.Injective (MulAut.conj h).toMonoidHom := (MulAut.conj h).injective
  have hroot : ∀ T : Pair (3 + 1),
      IsLongRootSU2 (GaloisField p (2 * f)) p f c.hn
        ((LcU (GaloisField p (2 * f)) p f T).map (MulAut.conj h).toMonoidHom)
        (h * zEltU (GaloisField p (2 * f)) p f T * h⁻¹) := fun T =>
    (isLongRootSU2_LcU h2 c.hn T).conj h
  have hα0 : (LcU (GaloisField p (2 * f)) p f (nodePair 3 0 (by omega))).map
      (MulAut.conj h).toMonoidHom = LcU (GaloisField p (2 * f)) p f (nodePair 3 0 (by omega)) := by
    have := hh0
    rwa [range_blockEmb2_eq_LcU_nodePair h2 (by omega : 0 < 3)] at this
  have hα2 : (LcU (GaloisField p (2 * f)) p f (nodePair 3 2 (by omega))).map
      (MulAut.conj h).toMonoidHom = LcU (GaloisField p (2 * f)) p f (nodePair 3 2 (by omega)) := by
    rw [← range_blockEmb2_eq_LcU_nodePair h2 (by omega : 2 < 3)]
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨x, ⟨A, rfl⟩, rfl⟩
      exact ⟨A, (hh2 A).symm⟩
    · rintro ⟨A, rfl⟩
      exact ⟨_, ⟨A, rfl⟩, hh2 A⟩
  obtain ⟨N, hN, hNK, hNR⟩ := typeU_exists_member_of_root c.hp2 c.hq c.hm c.hΩ c.hK c.hz c.hP1 c.d
    (R := (LcU (GaloisField p (2 * f)) p f (nodePair 3 1 (by omega))).map
      (MulAut.conj h).toMonoidHom) ⟨_, hroot _⟩
  have hfixN : ∀ a ∈ locImg Ω z N, locAut c.hΩ.conjInvariant htz a = a := by
    intro a ha
    rw [hNR] at ha
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := ha
    have hx' : x ∈ (blockEmb2 (GaloisField p (2 * f)) p f 3 ⟨1, by omega⟩).range := by
      rw [range_blockEmb2_eq_LcU_nodePair h2 (by omega : 1 < 3)]
      exact hx
    obtain ⟨A, rfl⟩ := hx'
    have := hhσ (blockEmb2 (GaloisField p (2 * f)) p f 3 ⟨1, by omega⟩ A)
    rw [conjSign_blockEmb2_of_eq c.card_eq (partnerSigns 3 0) ⟨1, by omega⟩
      (by simp [partnerSigns]) A] at this
    exact this
  have hNK' : Commutes N K :=
    (typeU_commutes_K_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.d hN hNK).symm
  have hcβ : Commutes β N := commutes_symm ((hfixiff N hN hNK').mp hfixN)
  have hcomm : ∀ T T' : Pair (3 + 1), Commute (h * zEltU (GaloisField p (2 * f)) p f T * h⁻¹)
      (h * zEltU (GaloisField p (2 * f)) p f T' * h⁻¹) := fun T T' =>
    commute_conj (signGroupU_comm (zEltU_mem_signGroupU T) (zEltU_mem_signGroupU T')) h
  have hne : ∀ a b : ℕ, (ha : a < 3) → (hb : b < 3) → a ≠ b →
      h * zEltU (GaloisField p (2 * f)) p f (nodePair 3 a ha) * h⁻¹ ≠
        h * zEltU (GaloisField p (2 * f)) p f (nodePair 3 b hb) * h⁻¹ := by
    intro a b ha hb hab hh
    exact hab ((nodePair_eq_iff ha hb).mp
      (typeU_zEltU_injective h2 (mul_left_cancel (mul_right_cancel hh))))
  have hnc : ∀ a : ℕ, (ha : a + 2 < 3 + 1) →
      ¬ Commutes ((LcU (GaloisField p (2 * f)) p f (nodePair 3 a (by omega))).map
          (MulAut.conj h).toMonoidHom)
        ((LcU (GaloisField p (2 * f)) p f (nodePair 3 (a + 1) (by omega))).map
          (MulAut.conj h).toMonoidHom) := by
    intro a ha hc'
    exact not_commutes_LcU_overlap c.card_eq c.hp2 c.hn3 (i := ⟨a, by omega⟩)
      (j := ⟨a + 1, by omega⟩) (k := ⟨a + 2, by omega⟩) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) ((commutes_map_iff _ hcinj).mp hc')
  obtain ⟨W₁, hW₁⟩ := c.stdpair_of_root (nd.mem 0 (by omega)) hN (hroot (nodePair 3 0 (by omega)))
    (hroot (nodePair 3 1 (by omega))) (by rw [hα0, nd.img 0 (by omega)]) hNR (hcomm _ _)
    (hne 0 1 (by omega) (by omega) (by omega)) (hnc 0 (by omega))
  obtain ⟨W₂, hW₂⟩ := c.stdpair_of_root hN (nd.mem 2 (by omega)) (hroot (nodePair 3 1 (by omega)))
    (hroot (nodePair 3 2 (by omega))) hNR (by rw [hα2, nd.img 2 (by omega)]) (hcomm _ _)
    (hne 1 2 (by omega) (by omega) (by omega)) (hnc 1 (by omega))
  exact ⟨N, hN, hNK, hcβ, ⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩⟩

end Middle

end CFSG.ClassicalInvolution.RouteD
