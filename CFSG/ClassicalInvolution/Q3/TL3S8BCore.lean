module

public import CFSG.ClassicalInvolution.Q3.TL3S8BF2
public import CFSG.ClassicalInvolution.Q3.TL3S8BE2
public import CFSG.ClassicalInvolution.Q3.TL3S8FStar
public import CFSG.ClassicalInvolution.Q3.Q3T6FusConj

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def TightC19_11b (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IH (Nat.card G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G) (W L : Subgroup G) (t' : G)
      (V : Subgroup G), TightFStarOK G t → TightSylowStd R S t T →
    TightSylowDataT (tightCore R) t T W L t' V →
      (T : Subgroup G) ⊓
          Subgroup.centralizer (((T : Subgroup G) ⊓ tightCore R : Subgroup G) : Set G) ⊓
          Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L = ⊥

section E2

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G}

theorem TightSylowStd.tightE2Prime_of_core {IH : ℕ → Prop} (hF : TightFStarOK G t)
    (h11b : TightC19_11b IH) (hbelow : IH (Nat.card G)) (h : TightSylowStd R S t T)
    (hmu : ¬ AllTypeTwo (tightCore R) t) : TightE2Prime (tightCore R) T := by
  obtain ⟨W₀, hW₀, hW₀S, -⟩ := h.tightMemStd.exists_wSet_le_normal T
  exact (h.sylowData hmu hW₀ hW₀S).tightE2Prime fun W₁ L t' V hdT =>
    h11b G hbelow R S t T W₁ L t' V hF h hdT

end E2

section Core

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataT

variable (hd : TightSylowDataT K z S W L t V)
include hd

theorem exists_conj_eq_t_of_BPrime :
    ∃ g : G, (∀ b ∈ S19B.sec19BPrime K S W L, g * b = b * g) ∧ g * z * g⁻¹ = t :=
  Q3T6.exists_conj_eq_t_of_subgroup3 hd.tight.hypGen hd.tight.edgeless
    hd.tight.isUniqueInvolution hd.tight.centralizer_le_normalizer hd.hW hd.hWS hd.mem_W_z
    hd.isSylow2In_inf hd.memL hd.invL hd.mem_W hd.ne (fun _ hb => hb.1.1.1)
    (fun _ hb => hb.1.1.2) (fun _ hb => hb.1.2) (fun _ hb => hb.2)

end TightSylowDataT

omit [Finite G] in
theorem tight_exists_mem_centralizer_conj_eq_of_F1 {x : G}
    (hF1 : ∀ {g : G}, g * z * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) →
      ∃ c ∈ Subgroup.centralizer ({x} : Set G), c * z * c⁻¹ = g * z * g⁻¹) {g : G}
    (hgx : g⁻¹ * x * g ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ d ∈ Subgroup.centralizer ({z} : Set G), d⁻¹ * x * d = g⁻¹ * x * g := by
  have hgx' := Subgroup.mem_centralizer_singleton_iff.mp hgx
  have h1 : g * z * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [← hgx']
      _ = x * (g * z * g⁻¹) := by group
  obtain ⟨c, hc, hcz⟩ := hF1 h1
  have hcx := Subgroup.mem_centralizer_singleton_iff.mp hc
  refine ⟨c⁻¹ * g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc c⁻¹ * g * z = c⁻¹ * (g * z * g⁻¹) * g := by group
      _ = c⁻¹ * (c * z * c⁻¹) * g := by rw [hcz]
      _ = z * (c⁻¹ * g) := by group
  · calc (c⁻¹ * g)⁻¹ * x * (c⁻¹ * g) = g⁻¹ * (c * x * c⁻¹) * g := by group
      _ = g⁻¹ * x * g := by rw [hcx]; group

namespace TightSylowDataT

variable (hd : TightSylowDataT K z S W L t V)
include hd

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
  have hd0 := hd.toTightSylowData
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

end TightSylowDataT

end Core

@[expose] def TightF1 (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IH (Nat.card G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G) (W L : Subgroup G) (t' : G)
      (V : Subgroup G), TightFStarOK G t → TightSylowStd R S t T →
    TightSylowDataT (tightCore R) t T W L t' V →
      ∀ x ∈ S19B.sec19BPrime (tightCore R) T W L, x ≠ 1 → ∀ g : G,
        g * t * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) →
          ∃ c ∈ Subgroup.centralizer ({x} : Set G), c * t * c⁻¹ = g * t * g⁻¹

@[expose] def TightEndGame (IH : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IH (Nat.card G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G) (T : Sylow 2 G), TightFStarOK G t →
    TightSylowStd R S t T →
    ∀ B : Subgroup G, B ≤ (T : Subgroup G) → B ≠ ⊥ →
      fusionStronglyClosed (B : Set G) (T : Subgroup G) → B ≤ centralizerModOdd ⊤ (tightCore R) →
      t ∈ Subgroup.centralizer (B : Set G) →
      (∃ g ∈ Subgroup.centralizer (B : Set G),
        g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ * t = t * (g * t * g⁻¹)) → False

theorem tightC19_11b_of_F1_endgame {IH : ℕ → Prop} (hF1 : TightF1 IH)
    (hEnd : TightEndGame IH) : TightC19_11b IH := by
  intro G _ _ hIH R S t T W L t' V hF h hd
  by_contra hne
  exact hd.false_of_F1_endgame (hF1 G hIH R S t T W L t' V hF h hd)
    (hEnd G hIH R S t T hF h) hne

end CFSG.ClassicalInvolution.Q3
