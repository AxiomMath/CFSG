module

public import CFSG.GH74.GLS.Stage4.T6SylP

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

omit [Finite G] in
theorem card_K_of_coord {F : Type} [Field F] [Finite F] {φ : SL2 F →* G}
    (hinj : Function.Injective φ) {K : Subgroup G} (hrange : φ.range = K) :
    Nat.card ↥K = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have e : Nat.card ↥φ.range = Nat.card (SL2 F) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [hrange] at e
  rw [e]
  exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F

omit [Finite G] in
theorem factorization_q_mul {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) :
    (p ^ m * ((p ^ m) ^ 2 - 1)).factorization p = m := by
  have hq : 2 ≤ p ^ m := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have h1 : ¬ p ∣ (p ^ m) ^ 2 - 1 := by
    intro hd
    have hpm : p ∣ (p ^ m) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
    have h2 : p ∣ (p ^ m) ^ 2 - ((p ^ m) ^ 2 - 1) := Nat.dvd_sub hpm hd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have h2 : (p ^ m) ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ (p ^ m) ^ 2 := by nlinarith
    omega
  rw [Nat.factorization_mul (by positivity) h2, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h1, hp.factorization_pow]
  simp

theorem vp_K_le (h : T6Ctx N u p) {m n : ℕ} (hm : N.q₁ = p ^ m) (hn : N.q₂ = p ^ n) :
    (Nat.card ↥(N.K₁ ⊔ N.K₂)).factorization p ≤ m + n := by
  have hloc := h.sec5.loc
  obtain ⟨F₁, i₁, f₁, φ₁, hc₁, hi₁, hr₁, -⟩ := h.coord.coord₁
  obtain ⟨F₂, i₂, f₂, φ₂, hc₂, hi₂, hr₂, -⟩ := h.coord.coord₂
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have := hloc.q₁_ge; rw [hm, h0] at this; simp at this
    · exact h0
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have := hloc.q₂_ge; rw [hn, h0] at this; simp at this
    · exact h0
  have hK₁ : Nat.card ↥N.K₁ = p ^ m * ((p ^ m) ^ 2 - 1) := by
    rw [card_K_of_coord hi₁ hr₁, hc₁, hm]
  have hK₂ : Nat.card ↥N.K₂ = p ^ n * ((p ^ n) ^ 2 - 1) := by
    rw [card_K_of_coord hi₂ hr₂, hc₂, hn]
  let ψ : ↥N.K₁ × ↥N.K₂ →* G := MonoidHom.noncommCoprod N.K₁.subtype N.K₂.subtype
    (fun a b => hloc.K_comm a a.2 b b.2)
  have hψ : ∀ a b, ψ (a, b) = (a : G) * b := fun _ _ => rfl
  have hrange : ψ.range = N.K₁ ⊔ N.K₂ := by
    apply le_antisymm
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      rw [hψ]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right b.2)
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hloc.K_comm x).1 hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), by rw [hψ]⟩
  have hdvd : Nat.card ↥(N.K₁ ⊔ N.K₂) ∣ Nat.card ↥N.K₁ * Nat.card ↥N.K₂ := by
    rw [← hrange]
    have h1 : Nat.card (↥N.K₁ × ↥N.K₂) = Nat.card ↥N.K₁ * Nat.card ↥N.K₂ := Nat.card_prod _ _
    rw [← h1]
    have h2 : Nat.card ((↥N.K₁ × ↥N.K₂) ⧸ ψ.ker) = Nat.card ↥ψ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    rw [← h2]
    exact Subgroup.card_quotient_dvd_card _
  have hne : Nat.card ↥N.K₁ * Nat.card ↥N.K₂ ≠ 0 :=
    (Nat.mul_pos (Nat.card_pos (α := ↥N.K₁)) (Nat.card_pos (α := ↥N.K₂))).ne'
  calc (Nat.card ↥(N.K₁ ⊔ N.K₂)).factorization p
      ≤ (Nat.card ↥N.K₁ * Nat.card ↥N.K₂).factorization p :=
        (Nat.factorization_le_iff_dvd (Nat.card_pos).ne' hne).2 hdvd p
    _ = m + n := by
        rw [Nat.factorization_mul (Nat.card_pos (α := ↥N.K₁)).ne' (Nat.card_pos (α := ↥N.K₂)).ne',
          Finsupp.add_apply, hK₁, hK₂, factorization_q_mul h.prime hm1, factorization_q_mul h.prime hn1]

theorem vp_C₁_le (h : T6Ctx N u p) {m n : ℕ} (hm : N.q₁ = p ^ m) (hn : N.q₂ = p ^ n) :
    (Nat.card ↥(N.K₁ ⊔ N.K₂ ⊔ N.S)).factorization p ≤ m + n := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥(N.K₁ ⊔ N.K₂ ⊔ N.S)) := inferInstance
  set Q' : Subgroup G := (Q : Subgroup ↥(N.K₁ ⊔ N.K₂ ⊔ N.S)).map (N.K₁ ⊔ N.K₂ ⊔ N.S).subtype with hQ'
  have hQ'p : IsPGroup p ↥Q' := Q.isPGroup'.map _
  have hQ'K : Q' ≤ N.K₁ ⊔ N.K₂ := by
    rintro x ⟨c, hc, rfl⟩
    have hodd := t6_odd_of_pGroup h.prime h.p_ne_two hQ'p ⟨c, hc, rfl⟩
    exact h.oddK _ c.2 hodd
  have hdvd : Nat.card ↥Q' ∣ Nat.card ↥(N.K₁ ⊔ N.K₂) := Subgroup.card_dvd_of_le hQ'K
  have hcard : Nat.card ↥Q' = p ^ (Nat.card ↥(N.K₁ ⊔ N.K₂ ⊔ N.S)).factorization p := by
    rw [hQ', Subgroup.card_map_of_injective (N.K₁ ⊔ N.K₂ ⊔ N.S).subtype_injective]
    exact Sylow.card_eq_multiplicity Q
  rw [hcard] at hdvd
  exact ((Nat.Prime.pow_dvd_iff_le_factorization h.prime (Nat.card_pos).ne').1 hdvd).trans
    (vp_K_le h hm hn)

theorem cent_z_eq (h : T6Ctx N u p) :
    Subgroup.centralizer ({N.z} : Set G) = N.K₁ ⊔ N.K₂ ⊔ N.S ⊔ N.F := by
  apply le_antisymm h.sec5.F5.C_le
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.2 (h.zK k (Subgroup.mem_sup_left hk))
  · intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.2 (h.zK k (Subgroup.mem_sup_right hk))
  · intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.2 (h.sec5.loc.z_cent_S s hs)
  · intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.2 (F_cent_z h hf)

theorem card_C (h : T6Ctx N u p) :
    Nat.card ↥(Subgroup.centralizer ({N.z} : Set G)) =
      Nat.card ↥(N.K₁ ⊔ N.K₂ ⊔ N.S) * Nat.card ↥N.F := by
  have hnorm : N.F ≤ Subgroup.normalizer ((N.K₁ ⊔ N.K₂ ⊔ N.S : Subgroup G) : Set G) :=
    t2P53_F_normC₁ h.ctx (fun f hf => F_cent_z h hf)
  have hdisj : Disjoint (N.K₁ ⊔ N.K₂ ⊔ N.S) N.F := by
    rw [disjoint_iff, eq_bot_iff]
    intro f ⟨hf₁, hf₂⟩
    have hK : f ∈ N.K₁ ⊔ N.K₂ := h.oddK f hf₁ (h.sec5.F5.F_odd f hf₂)
    have : f ∈ N.F ⊓ (N.K₁ ⊔ N.K₂) := ⟨hf₂, hK⟩
    rw [h.sec5.F5.F_inter_K] at this
    exact this
  rw [cent_z_eq h]
  exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj

theorem card_pSub_C_le (h : T6Ctx N u p) {m n : ℕ} (hm : N.q₁ = p ^ m) (hn : N.q₂ = p ^ n)
    {P₀ : Subgroup G} (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p)
    {E : Subgroup G} (hE : E ≤ Subgroup.centralizer ({N.z} : Set G)) (hEp : IsPGroup p ↥E) :
    Nat.card ↥E ≤ N.q₁ * N.q₂ * Nat.card ↥P₀ := by
  have : Fact p.Prime := ⟨h.prime⟩
  set C : Subgroup G := Subgroup.centralizer ({N.z} : Set G) with hC
  have hEp' : IsPGroup p ↥(E.subgroupOf C) := hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
  obtain ⟨Q, hQ⟩ := hEp'.exists_le_sylow
  have h1 : Nat.card ↥(E.subgroupOf C) ≤ Nat.card ↥(Q : Subgroup ↥C) := Subgroup.card_le_of_le hQ
  have h2 : Nat.card ↥(E.subgroupOf C) = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  rw [h2, Sylow.card_eq_multiplicity Q] at h1
  refine h1.trans ?_
  have hCcard := card_C h
  have hfac : (Nat.card ↥C).factorization p ≤ m + n + (Nat.card ↥N.F).factorization p := by
    rw [hC, hCcard, Nat.factorization_mul (Nat.card_pos).ne' (Nat.card_pos).ne', Finsupp.add_apply]
    exact Nat.add_le_add_right (vp_C₁_le h hm hn) _
  calc p ^ (Nat.card ↥C).factorization p ≤ p ^ (m + n + (Nat.card ↥N.F).factorization p) :=
        Nat.pow_le_pow_right h.prime.pos hfac
    _ = N.q₁ * N.q₂ * Nat.card ↥P₀ := by
        rw [hP₀c, hm, hn, pow_add, pow_add]

theorem card_pSub_Cv_le (h : T6Ctx N u p) {m n : ℕ} (hm : N.q₁ = p ^ m) (hn : N.q₂ = p ^ n)
    {P₀ : Subgroup G} (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p) {v : G}
    (hv : v = N.z ∨ v = u ∨ v = N.z * u) {E : Subgroup G}
    (hE : E ≤ Subgroup.centralizer ({v} : Set G)) (hEp : IsPGroup p ↥E) :
    Nat.card ↥E ≤ N.q₁ * N.q₂ * Nat.card ↥P₀ := by
  have key : ∀ g : G, v = g * N.z * g⁻¹ → Nat.card ↥E ≤ N.q₁ * N.q₂ * Nat.card ↥P₀ := by
    intro g hg
    set E' : Subgroup G := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
    have hE'C : E' ≤ Subgroup.centralizer ({N.z} : Set G) := by
      rintro _ ⟨e, he, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hE he)
      rw [hg] at h1
      show (g⁻¹ * e * g⁻¹⁻¹) * N.z = N.z * (g⁻¹ * e * g⁻¹⁻¹)
      calc (g⁻¹ * e * g⁻¹⁻¹) * N.z = g⁻¹ * (e * (g * N.z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * N.z * g⁻¹) * e) * g := by rw [h1]
        _ = N.z * (g⁻¹ * e * g⁻¹⁻¹) := by group
    have hE'p : IsPGroup p ↥E' := hEp.map _
    have := card_pSub_C_le h hm hn hP₀c hE'C hE'p
    rwa [hE', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at this
  obtain ⟨ha1, ha2⟩ := a_conj_facts h
  rcases hv with rfl | rfl | rfl
  · exact key 1 (by simp)
  · refine key N.a⁻¹ ?_
    calc v = N.a⁻¹ * (N.a * v * N.a⁻¹) * N.a := by group
      _ = N.a⁻¹ * N.z * N.a⁻¹⁻¹ := by rw [ha1, inv_inv]
  · refine key N.a ?_
    rw [ha2]

end CFSG.GH74.GLS.Stage4.Rest.T6
