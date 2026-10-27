module

public import CFSG.ClassicalInvolution.Q3.TL4D1Red
public import CFSG.ClassicalInvolution.Q3.TL4D1Basic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem T4Hyp.commutes_conj_of_not_mem_normalizer (h : T4Hyp r G Δ) {J : Subgroup G}
    (hJ : J ∈ Δ) (hJ2 : IsPGroup 2 J) {P : Subgroup G} (hPn : P.Normal) (hP2 : IsPGroup 2 P)
    {v : G} (hvP : v ∈ P) (hvJ : v ∉ Subgroup.normalizer (J : Set G)) :
    Commutes J (conjSub v J) := by
  have hJR := mem_RSet_self hJ hJ2
  have hJv : conjSub v J ∈ Δ := h.hyp.conjInvariant v J hJ
  have hJvR := mem_RSet_self hJv (hJ2.map _)
  have hne : J ≠ conjSub v J := fun e => hvJ (mem_normalizer_of_conjSub_eq e.symm)
  have : P.Normal := hPn
  obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_right hJ2 hP2).exists_le_sylow
  have hJvS : conjSub v J ≤ (S : Subgroup G) := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    have e1 : y = v * ((v⁻¹ * y * v) * v⁻¹ * (v⁻¹ * y * v)⁻¹) * (v⁻¹ * y * v) := by group
    rw [e1]
    exact hS (Subgroup.mul_mem _ (Subgroup.mem_sup_right (P.mul_mem hvP
      (hPn.conj_mem _ (P.inv_mem hvP) _))) (Subgroup.mem_sup_left hy))
  exact Q3CP.l67Gen G Δ h.hyp S J hJR _ hJvR (le_sup_left.trans hS) hJvS hne

@[expose] def D1Core3 (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ThmD1RBelow 3 (Nat.card G) →
    TC.Thin.ThmDAbsBelow 3 (Nat.card G + 1) → ∀ Δ : Set (Subgroup G), T4Hyp 3 G Δ →
    (∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → TightInO2 z) →
    ∀ J ∈ Δ, ∀ L ∈ Δ, (¬ ∃ g : G, conjSub g J = L) →
    ∀ u v : G, IsUniqueInvolution J u → IsUniqueInvolution L v →
    v ∉ Subgroup.normalizer (J : Set G) → u ∉ Subgroup.normalizer (L : Set G) →
    J ⊔ L = ⊤ → (u * v) ^ 2 ∈ Subgroup.center G →
    Commutes J (conjSub v J) → Commutes L (conjSub u L) → False

theorem T4Hyp.commutes_of_core3 (hD : ThmD1RBelow 3 (Nat.card G))
    (hD2 : TC.Thin.ThmDAbsBelow 3 (Nat.card G + 1)) (hcore : D1Core3 (Nat.card G + 1))
    (h : T4Hyp 3 G Δ)
    (hall : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → TightInO2 z) {J L : Subgroup G}
    (hJ : J ∈ Δ) (hL : L ∈ Δ) (hnc : ¬ ∃ g : G, conjSub g J = L) : Commutes J L := by
  by_contra hcomm
  obtain ⟨u, hu⟩ := (h.hyp.omega1 J hJ).1
  obtain ⟨v, hv⟩ := (h.hyp.omega1 L hL).1
  have hinu := hall J hJ u hu
  have hinv := hall L hL v hv
  have hnc' : ¬ ∃ g : G, conjSub g L = J := by
    rintro ⟨g, hg⟩
    exact hnc ⟨g⁻¹, by rw [← hg, conjSub_inv_conjSub]⟩
  have hvJ : v ∉ Subgroup.normalizer (J : Set G) := fun hvJ =>
    hcomm (h.commutes_of_mem_normalizer hJ hL hnc hu hv hinu hinv hvJ)
  have huL : u ∉ Subgroup.normalizer (L : Set G) := fun huL =>
    hcomm (h.commutes_of_mem_normalizer hL hJ hnc' hv hu hinv hinu huL).symm
  obtain ⟨Pu, hPun, hPu2, huP⟩ := hinu
  obtain ⟨Pv, hPvn, hPv2, hvP⟩ := hinv
  have : Pv.Normal := hPvn
  have : Pu.Normal := hPun
  have hQn : (Pu ⊔ Pv).Normal := Subgroup.sup_normal Pu Pv
  have hQ2 : IsPGroup 2 ↥(Pu ⊔ Pv) := IsPGroup.to_sup_of_normal_right hPu2 hPv2
  have huQ : u ∈ Pu ⊔ Pv := Subgroup.mem_sup_left huP
  have hvQ : v ∈ Pu ⊔ Pv := Subgroup.mem_sup_right hvP
  have hJ2 := h.isPGroup_of_inO2 hJ hu ⟨_, hQn, hQ2, huQ⟩
  have hL2 := h.isPGroup_of_inO2 hL hv ⟨_, hQn, hQ2, hvQ⟩
  have htop : J ⊔ L = ⊤ := by
    by_contra hne
    exact hcomm (h.commutes_of_le_proper hD hJ hL hnc hu hv hQn hQ2 huQ hvQ hne le_sup_left
      le_sup_right)
  have hcJ := h.commutes_conj_of_not_mem_normalizer hJ hJ2 hQn hQ2 hvQ hvJ
  have hcL := h.commutes_conj_of_not_mem_normalizer hL hL2 hQn hQ2 huQ huL
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu.sq
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv.sq
  have he1 : (u * v) ^ 2 = u * (v * u * v⁻¹) := by
    rw [pow_two, hvinv]
    group
  have hab : Commute u (v * u * v⁻¹) := hcJ u hu.mem _ (conj_mem_conjSub hu.mem)
  have hee : (u * v) ^ 2 * (u * v) ^ 2 = 1 := by
    rw [he1]
    calc u * (v * u * v⁻¹) * (u * (v * u * v⁻¹))
        = u * ((v * u * v⁻¹) * u) * (v * u * v⁻¹) := by group
      _ = u * (u * (v * u * v⁻¹)) * (v * u * v⁻¹) := by rw [← hab.eq]
      _ = (u * u) * ((v * u * v⁻¹) * (v * u * v⁻¹)) := by group
      _ = 1 := by
          rw [hu.sq, one_mul]
          calc v * u * v⁻¹ * (v * u * v⁻¹) = v * (u * u) * v⁻¹ := by group
            _ = 1 := by rw [hu.sq, mul_one, mul_inv_cancel]
  have he2 : (u * v) ^ 2 = v * (u * v * u⁻¹) := by
    have hself : (u * v) ^ 2 = ((u * v) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hee
    rw [hself, pow_two, mul_inv_rev, mul_inv_rev, hvinv, huinv]
    group
  have hJe : J ≤ Subgroup.centralizer ({(u * v) ^ 2} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff, he1]
    have h1 : Commute x u := (hu.commute_of_mem hx).symm
    have h2 : Commute x (v * u * v⁻¹) := hcJ x hx _ (conj_mem_conjSub hu.mem)
    exact (h1.mul_right h2).eq
  have hLe : L ≤ Subgroup.centralizer ({(u * v) ^ 2} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff, he2]
    have h1 : Commute y v := (hv.commute_of_mem hy).symm
    have h2 : Commute y (u * v * u⁻¹) := hcL y hy _ (conj_mem_conjSub hv.mem)
    exact (h1.mul_right h2).eq
  have hcen : (u * v) ^ 2 ∈ Subgroup.center G := by
    by_contra hne
    have hCne : Subgroup.centralizer ({(u * v) ^ 2} : Set G) ≠ ⊤ := by
      intro hC
      refine hne (Subgroup.mem_center_iff.mpr fun g => ?_)
      have hg : g ∈ Subgroup.centralizer ({(u * v) ^ 2} : Set G) := hC ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    exact hcomm (h.commutes_of_le_proper hD hJ hL hnc hu hv hQn hQ2 huQ hvQ hCne hJe hLe)
  exact hcore G (Nat.lt_succ_self _) hD hD2 Δ h hall J hJ L hL hnc u v hu hv hvJ huL htop hcen hcJ
    hcL

theorem thmD1RBelow_succ_of_core {n : ℕ} (hD : ThmD1RBelow 3 n)
    (hD2 : TC.Thin.ThmDAbsBelow 3 (n + 1)) (hcore : D1Core3 (n + 1)) :
    ThmD1RBelow 3 (n + 1) := by
  intro G _ _ hG Δ h hall J hJ L hL hnc
  rcases (Nat.lt_succ_iff.mp hG).lt_or_eq with hlt | heq
  · exact hD G hlt Δ h hall J hJ L hL hnc
  · subst heq
    exact h.commutes_of_core3 hD hD2 hcore hall hJ hL hnc

section Cit3

theorem thmD1_step {n : ℕ} (hcore : D1Core3 (n + 1)) :
    CIT3Below n → TightBelowRPlus 3 n → TC.Thin.ThmDAbsBelow 3 (n + 1) →
      ThmD1RBelow 3 (n + 1) :=
  fun _ hP hD2 => thmD1RBelow_succ_of_core hP.thmD.d1 hD2 hcore

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
