module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.E2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.F2
public import CFSG.ClassicalInvolution.Q3.TL3S8BCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Core

variable {r : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem exists_conj_eq_t_of_BPrime :
    ∃ g : G, (∀ b ∈ S19B.sec19BPrime K S W L, g * b = b * g) ∧ g * z * g⁻¹ = t :=
  Q3T6.exists_conj_eq_t_of_subgroup3 hd.tight.hypGen hd.tight.edgeless
    hd.tight.isUniqueInvolution hd.tight.centralizer_le_normalizer hd.hW hd.hWS hd.mem_W_z
    hd.isSylow2In_inf hd.memL hd.invL hd.mem_W hd.ne (fun _ hb => hb.1.1.1)
    (fun _ hb => hb.1.1.2) (fun _ hb => hb.1.2) (fun _ hb => hb.2)

theorem false_of_F1_endgame
    (hF1 : ∀ x ∈ S19B.sec19BPrime K S W L, x ≠ 1 → ∀ g : G,
      g * z * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) →
        ∃ c ∈ Subgroup.centralizer ({x} : Set G), c * z * c⁻¹ = g * z * g⁻¹)
    (hEnd : ∀ B : Subgroup G, B ≤ (S : Subgroup G) → B ≠ ⊥ →
      fusionStronglyClosed (B : Set G) (S : Subgroup G) → B ≤ centralizerModOdd ⊤ K →
      z ∈ Subgroup.centralizer (B : Set G) →
      (∃ g ∈ Subgroup.centralizer (B : Set G),
        g * z * g⁻¹ ≠ z ∧ g * z * g⁻¹ * z = z * (g * z * g⁻¹)) → False)
    (hne : S19B.sec19BPrime K S W L ≠ ⊥) : False := by
  have hd0 := hd.toTightSylowDataR
  have hBS : S19B.sec19BPrime K S W L ≤ (S : Subgroup G) := fun x hx => hx.1.1.1
  have hBK : S19B.sec19BPrime K S W L ≤ centralizerModOdd ⊤ K := fun x hx =>
    (hd.mem_sec19BPrime_iff.mp hx).2.1
  have hsc : fusionStronglyClosed (S19B.sec19BPrime K S W L : Set G) (S : Subgroup G) := by
    intro x hx g hg
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    obtain ⟨d, hdz, hdx⟩ := tight_exists_mem_centralizer_conj_eq_of_F1
      (fun {g'} hg' => hF1 x hx hx1 g' hg') (hd0.hSz hg)
    rw [← hdx] at hg ⊢
    have hdz' : d⁻¹ * z = z * d⁻¹ := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.inv_mem _ hdz)
      exact h
    have h := hd.conj_mem_sec19BPrime hx hdz' (by rwa [inv_inv])
    rwa [inv_inv] at h
  obtain ⟨g, hgB, hgz⟩ := hd.exists_conj_eq_t_of_BPrime
  have hzB : z ∈ Subgroup.centralizer (S19B.sec19BPrime K S W L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp hb.1.2 z hd.mem_W_z).symm
  refine hEnd _ hBS hne hsc hBK hzB ⟨g, Subgroup.mem_centralizer_iff.mpr fun b hb =>
    (hgB b hb).symm, ?_, ?_⟩
  · rw [hgz]
    exact hd.ne
  · rw [hgz]
    exact hd.comm_of_mem t hd.mem_W z hd.mem_W_z

end TightSylowDataTR

end Core

theorem tightC19_11bSR_of_F1_endgame {r : ℕ} (hF1 : TightF1SR r) (hEnd : TightEndGameSR r) :
    TightC19_11bSR r := by
  intro G _ _ _ hnab R S t T W L t' V h hd
  by_contra hne
  exact hd.false_of_F1_endgame (hF1 G hnab R S t T W L t' V h hd)
    (hEnd G hnab R S t T h) hne

section E2

variable {r : ℕ} {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
  {T : Sylow 2 G}

theorem StdR.tightE2Prime_of_coreS [IsSimpleGroup (genFittingFStar G)]
    (h11b : TightC19_11bSR r) (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (h : StdR r R S t T) (hmu : ¬ AllTypeTwo (tightCore R) t) :
    TightE2Prime (tightCore R) T := by
  obtain ⟨W₀, hW₀, hW₀S, -⟩ := h.tightMemStd.exists_wSet_le_normal T
  exact (h.sylowData hmu hW₀ hW₀S).tightE2Prime fun W₁ L t' V hdT =>
    h11b G hnab R S t T W₁ L t' V h hdT

end E2

end CFSG.CGT.PushingUpLit.SolKNA.R4
