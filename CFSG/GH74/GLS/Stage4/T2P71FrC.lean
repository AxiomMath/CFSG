module

public import CFSG.GH74.GLS.Stage4.T2P71FrB

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6.P71

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

omit [Finite G] in
theorem card_mul_inf_of_frattini [Finite G] {A B M : Subgroup G} (hAB : A ≤ B) (hMB : M ≤ B)
    (hAn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (hfr : ∀ g ∈ B, ∃ c ∈ A, ∃ n ∈ M, g = c * n) :
    Nat.card ↥B * Nat.card ↥(A ⊓ M) = Nat.card ↥A * Nat.card ↥M := by
  set A' : Subgroup ↥B := A.subgroupOf B with hA'
  set M' : Subgroup ↥B := M.subgroupOf B with hM'
  have hAn' : A'.Normal := ⟨fun a ha b => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hAn b b.2 a ha⟩
  have hsup : M' ⊔ A' = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨c, hc, n, hn, hgcn⟩ := hfr g g.2
    have hcB : c ∈ B := hAB hc
    have hnB : n ∈ B := hMB hn
    have hg : g = ⟨c, hcB⟩ * ⟨n, hnB⟩ := Subtype.ext hgcn
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hc))
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hn))
  have h1 := Subgroup.relIndex_sup_right (H := M') (K := A')
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have h2 : A'.index * Nat.card ↥A' = Nat.card ↥B := Subgroup.index_mul_card A'
  have h3 : A'.relIndex M' * Nat.card ↥(A' ⊓ M') = Nat.card ↥M' := Subgroup.relIndex_mul_card A' M'
  have cA : Nat.card ↥A' = Nat.card ↥A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  have cM : Nat.card ↥M' = Nat.card ↥M := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMB).toEquiv
  have cAM : Nat.card ↥(A' ⊓ M') = Nat.card ↥(A ⊓ M) := by
    have hle : A ⊓ M ≤ B := inf_le_left.trans hAB
    have hAM' : A' ⊓ M' = (A ⊓ M).subgroupOf B := by
      ext x; simp [hA', hM', Subgroup.mem_subgroupOf]
    rw [hAM']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [cA] at h2
  rw [cM, cAM] at h3
  rw [← h2, ← h3, h1]
  ring

theorem Z_lt_sylow (h : T6Ctx N u p) (h' : T6Ctx N.swap u p) {P : Subgroup G}
    (hPC : P ≤ Subgroup.centralizer ({N.z} : Set G)) (hPp : IsPGroup p ↥P) (hXP : N.X₁ ⊔ N.X₂ ≤ P)
    (hmax : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({N.z} : Set G) → IsPGroup p ↥E →
      Nat.card ↥E ≤ Nat.card ↥P)
    (hnotsyl : ¬ ∃ S : Sylow p G, (S : Subgroup G) ≤ Subgroup.centralizer ({N.z} : Set G)) :
    Nat.card ↥(P ⊓ Subgroup.centralizer (P : Set G)) <
      p ^ (Nat.card ↥(Subgroup.centralizer (P : Set G))).factorization p := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hp := h.prime
  set C : Subgroup G := Subgroup.centralizer ({N.z} : Set G) with hC
  set A : Subgroup G := Subgroup.centralizer (P : Set G) with hA
  set B : Subgroup G := Subgroup.normalizer (P : Set G) with hB
  set M : Subgroup G := B ⊓ C with hM
  by_contra hge
  push Not at hge
  have hZp : IsPGroup p ↥(P ⊓ A) := hPp.to_le inf_le_left
  have hZle : Nat.card ↥(P ⊓ A) ≤ p ^ (Nat.card ↥A).factorization p :=
    card_pSub_le_vp hp (inf_le_right : P ⊓ A ≤ A) hZp
  have hZc : Nat.card ↥(P ⊓ A) = p ^ (Nat.card ↥A).factorization p := le_antisymm hZle hge
  have hzP : ∀ x ∈ P, N.z * x = x * N.z := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hPC hx)).symm
  have hzo : orderOf N.z = 2 := h.sec5.loc.z_ord
  have hzA : N.z ∈ A := Subgroup.mem_centralizer_iff.2 (fun x hx => (hzP x hx).symm)
  have hA2 := A_card2 h h' hXP hzA
  have hfr := frattini hzP hzo hA2
  have hAB : A ≤ B := Subgroup.centralizer_le_normalizer (P : Set G)
  have hMB : M ≤ B := inf_le_left
  have hAn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A := by
    intro b hb a ha
    refine Subgroup.mem_centralizer_iff.2 fun s hs => ?_
    have hs' : b⁻¹ * s * b ∈ P := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hb) s).1 hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 ha _ hs'
    calc s * (b * a * b⁻¹) = b * ((b⁻¹ * s * b) * a) * b⁻¹ := by group
      _ = b * (a * (b⁻¹ * s * b)) * b⁻¹ := by rw [h1]
      _ = (b * a * b⁻¹) * s := by group
  have hfr' : ∀ g ∈ B, ∃ c ∈ A, ∃ n ∈ M, g = c * n := by
    intro g hg
    obtain ⟨c, hc, n, hn, hnz, hgcn⟩ := hfr g hg
    exact ⟨c, hc, n, ⟨hn, Subgroup.mem_centralizer_singleton_iff.2 (by
      calc n * N.z = (n * N.z * n⁻¹) * n := by group
        _ = N.z * n := by rw [hnz])⟩, hgcn⟩
  have hcount := card_mul_inf_of_frattini hAB hMB hAn hfr'
  obtain ⟨s, hs⟩ := hPp.exists_card_eq
  have hPB : P ≤ B := Subgroup.le_normalizer
  have hPM : P ≤ M := le_inf hPB hPC
  have hZAM : P ⊓ A ≤ A ⊓ M := le_inf inf_le_right (inf_le_left.trans hPM)
  have hv1 : (Nat.card ↥A).factorization p ≤ (Nat.card ↥(A ⊓ M)).factorization p := by
    have hdvd : p ^ (Nat.card ↥A).factorization p ∣ Nat.card ↥(A ⊓ M) := by
      rw [← hZc]; exact Subgroup.card_dvd_of_le hZAM
    exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  have hv2 : (Nat.card ↥M).factorization p ≤ s := by
    obtain ⟨SM⟩ : Nonempty (Sylow p ↥M) := inferInstance
    have hE : Nat.card ↥((SM : Subgroup ↥M).map M.subtype) = p ^ (Nat.card ↥M).factorization p := by
      rw [Subgroup.card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity SM]
    have hEC : (SM : Subgroup ↥M).map M.subtype ≤ C := (Subgroup.map_subtype_le _).trans inf_le_right
    have := hmax _ hEC (SM.isPGroup'.map _)
    rw [hE, hs] at this
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
  have hfac : (Nat.card ↥B * Nat.card ↥(A ⊓ M)).factorization p =
      (Nat.card ↥A * Nat.card ↥M).factorization p := by rw [hcount]
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, Finsupp.add_apply] at hfac
  have hvB : (Nat.card ↥B).factorization p ≤ s := by omega
  have hrel : P.relIndex B * Nat.card ↥P = Nat.card ↥B := by
    have := Subgroup.relIndex_mul_card P B
    rwa [inf_eq_left.2 hPB] at this
  have hN : ¬ p ∣ P.relIndex B := by
    intro hd
    have h1 : p ^ (s + 1) ∣ Nat.card ↥B := by
      rw [← hrel, hs, pow_succ']
      exact Nat.mul_dvd_mul_right hd _
    have h2 := (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h1
    omega
  have hidx := t6_sylow_of_normalizer hp hPp hN
  exact hnotsyl ⟨hPp.toSylow hidx, hPC⟩

end CFSG.GH74.GLS.Stage4.Rest.T6.P71
