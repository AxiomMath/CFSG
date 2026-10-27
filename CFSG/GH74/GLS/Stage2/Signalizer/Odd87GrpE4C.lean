module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4CGlue
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Par

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

section

variable {G : Type} [Group G] {z : G} {k : Kind}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X J : Subgroup A}

theorem C43c_of_eq {K : Subgroup A} (hK : ncl X = K) (n : ℕ) (hn : 1 ≤ n)
    (h1 : LieModel (↥K ⧸ center ↥K) .PSL 3 p n) (h2 : X ⊔ zpowers a ≤ K)
    (h3 : IsMaxParabolicP p K (X ⊔ K ⊓ centralizer ({a} : Set A)))
    (h4 : X = Op p (X ⊔ K ⊓ centralizer ({a} : Set A))) (h5 : IsElementaryAbelian p ↥X)
    (h6 : Nat.card ↥X = p ^ (2 * n)) : C43c a p X := by
  subst hK
  exact ⟨n, hn, h1, h2, h3, h4, h5, h6⟩

theorem case_c (F : E4Hyp G z k) {c : E4Ctx G z A a p X} (d : SubData c J)
    (hc : C42c p (secZ a X J) (secX a X J) (secJ a X J)) : C43c a p X := by
  have : Fact p.Prime := ⟨c.A4.prime⟩
  obtain ⟨n, hn1, hLie, hzK, hEA, hcard, P', hP', hXOp, hPeq⟩ := hc
  have hLieHat : LieModel (Hat J) .PSL 3 p n :=
    Transport.lieModel_of_mulEquiv (secJ_equiv d.hyp).some hLie
  have hodd : Odd (p ^ n) := (c.A4.prime.odd_of_ne_two c.A4.odd).pow
  have hf : ∀ c' : A, orderOf c' = 2 → c' ∈ centralizer (J : Set A) → False :=
    fun c' h1 h2 => F.f3 A a c.sec J d.comp p n c.A4.prime hn1 (Or.inl hodd) hLieHat c' h1 h2
  have hcomp1 : ∀ J' : Subgroup A, IsComponent J' → J' = J := fun J' hJ' =>
    comp_eq_of_no_invol d.comp hf hJ'
  have hcomp : ∀ J' : Subgroup A, IsComponent J' → J' ≤ ncl X → J' = J := fun J' hJ' _ => hcomp1 J' hJ'
  have hJn : J.Normal := normal_of_unique d.comp hcomp1
  have hR2 : pCore 2 A = ⊥ := pCore_two_eq_bot_of_no_invol d.comp hf
  have hF : ∀ q : ℕ, q.Prime → X ≤ centralizer ((pCore q A : Subgroup A) : Set A) := by
    intro q hq
    by_cases hq2 : q = 2
    · subst hq2
      rw [hR2]
      intro x _ y hy
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      subst hy
      simp
    · exact c.a41 q hq hq2
  have hXK : secX a X J ≤ secJ a X J := by
    rw [hXOp]
    exact (Subgroup.map_subtype_le _).trans hP'.1.1
  have hXJC : X ≤ J ⊔ centralizer (J : Set A) := d.X_le_sup_of_le hXK
  have hJK : J ≤ ncl X := comp_le_ncl d.comp d.JX
  have hncl : ncl X = J :=
    ncl_eq_of_single_comp c.A4.prime c.A4.pgroup c.op d.comp hJn hJK hXJC hcomp hF
  have hXJ : X ≤ J := hncl ▸ (Subgroup.le_normalClosure : X ≤ ncl X)
  have haJ : a ∈ J :=
    mem_of_mem_sup_centralizer c.z2 (d.mem_sup_centralizer_of_B hzK) hf
  have hcop : Nat.Coprime p (Nat.card (secPsi a X J).ker) := secPsi_ker_coprime d.hyp hJn c.op
  obtain ⟨hMP, hOp, hcardX, hEAX⟩ := central_quotient_parabolic (p := p) (secPsi a X J)
    secPsi_surjective (secPsi_ker_central d.hyp) (secPsi_ker_odd d.hyp) hcop c.z2 haJ hXJ
    c.A4.pgroup (secPsi_map_X hXJ).symm hP' hXOp hPeq
  exact C43c_of_eq hncl n hn1
    (lieModel_quotient_center (secPsi a X J) secPsi_surjective (secPsi_ker_central d.hyp)
      d.comp.1.1 hLie)
    (sup_le hXJ (Subgroup.zpowers_le.mpr haJ)) hMP hOp (hEAX hEA) (by rw [hcardX]; exact hcard)

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
