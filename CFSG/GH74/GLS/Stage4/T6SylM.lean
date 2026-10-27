module

public import CFSG.GH74.GLS.Stage4.T6SylD
public import CFSG.GH74.GLS.Stage4.T6SylE
public import CFSG.GH74.GLS.Stage4.T6SylF

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem U_card_decomp (h : T6Ctx N u p) {K : Subgroup G} (hKodd : Odd (Nat.card ↥K))
    (hKU : ∀ g ∈ t2U N.z u, ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    Nat.card ↥K * Nat.card ↥(K ⊓ Subgroup.centralizer ((t2U N.z u : Subgroup G) : Set G)) ^ 2 =
      Nat.card ↥(K ⊓ Subgroup.centralizer {N.z}) * Nat.card ↥(K ⊓ Subgroup.centralizer {u}) *
        Nat.card ↥(K ⊓ Subgroup.centralizer {N.z * u}) := by
  obtain ⟨hz2, hu2, hzu, hz1, hu1, hne⟩ := zu_facts h
  have := t6_isKleinFour hz2 hu2 hzu hz1 hu1 hne
  have hTK : t2U N.z u ≤ Subgroup.normalizer (K : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype (fun n hn => hKU g hg n hn)
  have hz : N.z ∈ t2U N.z u := Subgroup.subset_closure (by simp)
  have hu : u ∈ t2U N.z u := Subgroup.subset_closure (by simp)
  exact CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq hKodd hTK hz hu hz1 hu1 hne

theorem Pst_max_U (h : T6Ctx N u p) (hR : T6RFacts N p) {m n : ℕ} (hm : N.q₁ = p ^ m)
    (hn : N.q₂ = p ^ n) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) (hP₀p : IsPGroup p ↥P₀)
    (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p) {Q : Subgroup G}
    (hQp : IsPGroup p ↥Q)
    (hQM : Q ≤ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G))
    (hQU : ∀ g ∈ t2U N.z u, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) : Q ≤ R₂ N p ⊔ N.X₁ ⊔ P₀ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hPp := Pst_pGroup h hR hP₀F hP₀p
  have hQ'p : IsPGroup p ↥(Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) := hQp.to_sup_of_normal_right' hPp hQM
  have hodd : ∀ K : Subgroup G, IsPGroup p ↥K → Odd (Nat.card ↥K) := by
    intro K hK
    obtain ⟨k, hk⟩ := hK.exists_card_eq
    rw [hk]
    exact (h.prime.odd_of_ne_two h.p_ne_two).pow
  have hQ'U : ∀ g ∈ t2U N.z u, ∀ k ∈ Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀),
      g * k * g⁻¹ ∈ Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀) := fun g hg =>
    t6_norm_sup (hQU g hg) (Pst_normU h hP₀F hg)
  have hPU : ∀ g ∈ t2U N.z u, ∀ k ∈ R₂ N p ⊔ N.X₁ ⊔ P₀, g * k * g⁻¹ ∈ R₂ N p ⊔ N.X₁ ⊔ P₀ :=
    fun g hg => Pst_normU h hP₀F hg
  have hle : R₂ N p ⊔ N.X₁ ⊔ P₀ ≤ Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀) := le_sup_right
  have hcent : ∀ v : G, (v = N.z ∨ v = u ∨ v = N.z * u) →
      (Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) ⊓ Subgroup.centralizer ({v} : Set G) =
        (R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ({v} : Set G) := by
    intro v hv
    have h1 := card_Cv_Pst h hR hm hn hP₀F hP₀p hP₀c hv
    have h2 := card_pSub_Cv_le h hm hn hP₀c hv (inf_le_right :
      (Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) ⊓ Subgroup.centralizer ({v} : Set G) ≤ _)
      (hQ'p.to_le inf_le_left)
    refine (Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hle) ?_).symm
    rw [h1]
    exact h2
  have hcentU : (Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) ⊓
      Subgroup.centralizer ((t2U N.z u : Subgroup G) : Set G) =
      (R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ((t2U N.z u : Subgroup G) : Set G) := by
    apply le_antisymm
    · intro x ⟨hxQ', hxC⟩
      have hz : N.z ∈ t2U N.z u := by
        obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
        exact (t2U_mem hz2 hu2 hzu).2 (Or.inr (Or.inl rfl))
      have hxz : x ∈ (Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) ⊓ Subgroup.centralizer ({N.z} : Set G) :=
        ⟨hxQ', Subgroup.mem_centralizer_singleton_iff.2 (by
          have := Subgroup.mem_centralizer_iff.1 hxC N.z hz
          exact this.symm)⟩
      rw [hcent N.z (Or.inl rfl)] at hxz
      exact ⟨hxz.1, hxC⟩
    · exact inf_le_inf_right _ hle
  have hBW₁ := U_card_decomp h (hodd _ hQ'p) hQ'U
  have hBW₂ := U_card_decomp h (hodd _ hPp) hPU
  rw [hcentU, hcent N.z (Or.inl rfl), hcent u (Or.inr (Or.inl rfl)),
    hcent (N.z * u) (Or.inr (Or.inr rfl))] at hBW₁
  have hpos : 0 < Nat.card ↥((R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓
      Subgroup.centralizer ((t2U N.z u : Subgroup G) : Set G)) ^ 2 := by
    have := Nat.card_pos (α := ↥((R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓
      Subgroup.centralizer ((t2U N.z u : Subgroup G) : Set G)))
    positivity
  have hcard : Nat.card ↥(Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) = Nat.card ↥(R₂ N p ⊔ N.X₁ ⊔ P₀) :=
    Nat.eq_of_mul_eq_mul_right hpos (hBW₁.trans hBW₂.symm)
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard.le
  exact le_sup_left.trans heq.symm.le

theorem no_cycle (h : T6Ctx N u p) (hR : T6RFacts N p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) {x : G}
    (hxP : x ∈ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G))
    (hxU : x ∈ Subgroup.normalizer ((t2U N.z u : Subgroup G) : Set G)) :
    x * N.z * x⁻¹ = N.z := by
  obtain ⟨hz2, hu2, hzu, hz1, hu1, hne⟩ := zu_facts h
  have hX := norm_X₂_of h hR hP₀F hxP hxU
  have hz : N.z ∈ t2U N.z u := (t2U_mem hz2 hu2 hzu).2 (Or.inr (Or.inl rfl))
  have hxz : x * N.z * x⁻¹ ∈ t2U N.z u := (Subgroup.mem_normalizer_iff.1 hxU _).1 hz
  obtain ⟨w, hwX, hw1⟩ : ∃ w ∈ N.X₂, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hb : N.X₂ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      exact hcon y hy
    have h1 := h.sec5.loc.card_X₂
    rw [hb] at h1
    simp at h1
    have := h.sec5.loc.q₂_ge
    omega
  obtain ⟨w', hw'X, hw'def⟩ : ∃ w' ∈ N.X₂, w' = x * w * x⁻¹ := ⟨_, hX w hwX, rfl⟩
  have key : ∀ v : G, x * N.z * x⁻¹ = v → (v = u ∨ v = N.z * u) → False := by
    intro v hv hvu
    have hzw : N.z * w = w * N.z := (z_cent_X₂ h hwX).symm
    have hcomm : v * w' = w' * v := by
      rw [← hv, hw'def]
      calc x * N.z * x⁻¹ * (x * w * x⁻¹) = x * (N.z * w) * x⁻¹ := by group
        _ = x * (w * N.z) * x⁻¹ := by rw [hzw]
        _ = (x * w * x⁻¹) * (x * N.z * x⁻¹) := by group
    have hu' : u * w' = w' * u := by
      rcases hvu with hv' | hv'
      · rw [hv'] at hcomm; exact hcomm
      · rw [hv'] at hcomm
        have hzw' : N.z * w' = w' * N.z := (z_cent_X₂ h hw'X).symm
        calc u * w' = N.z⁻¹ * (N.z * u * w') := by group
          _ = N.z⁻¹ * (w' * (N.z * u)) := by rw [hcomm]
          _ = N.z⁻¹ * (w' * N.z) * u := by group
          _ = N.z⁻¹ * (N.z * w') * u := by rw [← hzw']
          _ = w' * u := by group
    have := X₂_u_fix h hw'X hu'.symm
    apply hw1
    have e : w = x⁻¹ * w' * x := by rw [hw'def]; group
    rw [e, this]; group
  rcases U_cases h hxz with h1 | h1 | h1 | h1
  · exfalso
    apply hz1
    have : N.z = x⁻¹ * (x * N.z * x⁻¹) * x := by group
    rw [this, h1]; group
  · exact h1
  · exact (key _ h1 (Or.inl rfl)).elim
  · exact (key _ h1 (Or.inr rfl)).elim

theorem Y_le_cent_z (h : T6Ctx N u p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) :
    N.X₁ ⊔ N.X₂ ⊔ P₀ ≤ Subgroup.centralizer ({N.z} : Set G) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.2 (z_cent_X₁ h hx)
  · intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.2 (z_cent_X₂ h hx)
  · intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.2 (F_cent_z h (hP₀F hf))

theorem Y_pGroup (h : T6Ctx N u p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) (hP₀p : IsPGroup p ↥P₀) :
    IsPGroup p ↥(N.X₁ ⊔ N.X₂ ⊔ P₀) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨k, hk⟩ := hP₀p.exists_card_eq
  obtain ⟨m, hm⟩ := h.q₁_pow
  obtain ⟨n, hn⟩ := h.q₂_pow
  refine IsPGroup.of_card (n := m + n + k) ?_
  rw [card_Y h hP₀F, hk, hm, hn]
  ring

theorem exists_conj_to_z (h : T6Ctx N u p) {v : G} (hv : v = N.z ∨ v = u ∨ v = N.z * u) :
    ∃ g : G, g * v * g⁻¹ = N.z := by
  obtain ⟨ha1, ha2⟩ := a_conj_facts h
  rcases hv with hv | hv | hv
  · exact ⟨1, by rw [hv]; group⟩
  · exact ⟨N.a, by rw [hv]; exact ha1⟩
  · refine ⟨N.a⁻¹, ?_⟩
    rw [hv]
    calc N.a⁻¹ * (N.z * u) * N.a⁻¹⁻¹ = N.a⁻¹ * (N.a * N.z * N.a⁻¹) * N.a := by rw [ha2]; group
      _ = N.z := by group

theorem card_two_sub_Cv_le (h : T6Ctx N u p) (hR : T6RFacts N p) {m n : ℕ} (hm : N.q₁ = p ^ m)
    (hn : N.q₂ = p ^ n) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) (hP₀p : IsPGroup p ↥P₀)
    (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p) {v : G}
    (hv : v = N.z ∨ v = u ∨ v = N.z * u) {E : Subgroup G}
    (hEC : E ≤ Subgroup.centralizer ({v} : Set G))
    (hEM : E ≤ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G))
    (hE2 : IsPGroup 2 ↥E) :
    Nat.card ↥E ≤ 2 ^ ((N.q₁ - 1).factorization 2 + (N.q₂ - 1).factorization 2) := by
  set Q : Subgroup G := (R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ({v} : Set G) with hQ
  have hQc : Nat.card ↥Q = N.q₁ * N.q₂ * Nat.card ↥P₀ :=
    card_Cv_Pst h hR hm hn hP₀F hP₀p hP₀c hv
  have hQp : IsPGroup p ↥Q := (Pst_pGroup h hR hP₀F hP₀p).to_le inf_le_left
  have hYc : Nat.card ↥(N.X₁ ⊔ N.X₂ ⊔ P₀) = N.q₁ * N.q₂ * Nat.card ↥P₀ := card_Y h hP₀F
  have hYp := Y_pGroup h hP₀F hP₀p
  obtain ⟨g, hg⟩ := exists_conj_to_z h hv
  set Q₁ : Subgroup G := Q.map (MulAut.conj g).toMonoidHom with hQ₁
  have hQ₁C : Q₁ ≤ Subgroup.centralizer ({N.z} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hq.2
    show g * q * g⁻¹ * N.z = N.z * (g * q * g⁻¹)
    rw [← hg]
    calc g * q * g⁻¹ * (g * v * g⁻¹) = g * (q * v) * g⁻¹ := by group
      _ = g * (v * q) * g⁻¹ := by rw [h1]
      _ = g * v * g⁻¹ * (g * q * g⁻¹) := by group
  have hQ₁p : IsPGroup p ↥Q₁ := hQp.map _
  have hQ₁c : Nat.card ↥Q₁ = N.q₁ * N.q₂ * Nat.card ↥P₀ := by
    rw [hQ₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hQc]
  have hmax : ∀ E' : Subgroup G, E' ≤ Subgroup.centralizer ({N.z} : Set G) → IsPGroup p ↥E' →
      Nat.card ↥E' ≤ N.q₁ * N.q₂ * Nat.card ↥P₀ := fun E' hE'C hE'p =>
    card_pSub_C_le h hm hn hP₀c hE'C hE'p
  obtain ⟨c, hcC, hc⟩ := t6_sylow_conj_of_max h.prime hQ₁C (Y_le_cent_z h hP₀F) hQ₁p hYp
    (fun E' h1 h2 => by rw [hQ₁c]; exact hmax E' h1 h2)
    (fun E' h1 h2 => by rw [hYc]; exact hmax E' h1 h2)
  have hcz : c * N.z = N.z * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  have hk1 : ∀ q ∈ Q, c * g * q * (c * g)⁻¹ ∈ N.X₁ ⊔ N.X₂ ⊔ P₀ := by
    intro q hq
    have h1 : g * q * g⁻¹ ∈ Q₁ := ⟨q, hq, rfl⟩
    have := (hc _).1 h1
    have e : c * g * q * (c * g)⁻¹ = c * (g * q * g⁻¹) * c⁻¹ := by group
    rw [e]; exact this
  have hk2 : ∀ y ∈ N.X₁ ⊔ N.X₂ ⊔ P₀, (c * g)⁻¹ * y * (c * g) ∈ Q := by
    intro y hy
    have h1 : c⁻¹ * y * c ∈ Q₁ := by
      rw [hc]
      have e : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
      rw [e]; exact hy
    obtain ⟨q, hq, hqe⟩ := h1
    have : (c * g)⁻¹ * y * (c * g) = q := by
      have hqe' : g * q * g⁻¹ = c⁻¹ * y * c := hqe
      calc (c * g)⁻¹ * y * (c * g) = g⁻¹ * (c⁻¹ * y * c) * g := by group
        _ = g⁻¹ * (g * q * g⁻¹) * g := by rw [hqe']
        _ = q := by group
    rw [this]; exact hq
  have hEQ : ∀ e ∈ E, ∀ q ∈ Q, e * q * e⁻¹ ∈ Q := by
    intro e he q hq
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hEM he) q).1 hq.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hEC he) hq.2) (Subgroup.inv_mem _ (hEC he))⟩
  set E' : Subgroup G := E.map (MulAut.conj (c * g)).toMonoidHom with hE'
  have hE'z : ∀ e ∈ E, (c * g) * e * (c * g)⁻¹ * N.z = N.z * ((c * g) * e * (c * g)⁻¹) := by
    intro e he
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hEC he)
    have hz' : (c * g) * v * (c * g)⁻¹ = N.z := by
      calc (c * g) * v * (c * g)⁻¹ = c * (g * v * g⁻¹) * c⁻¹ := by group
        _ = N.z := by rw [hg, hcz]; group
    rw [← hz']
    calc (c * g) * e * (c * g)⁻¹ * ((c * g) * v * (c * g)⁻¹) = (c * g) * (e * v) * (c * g)⁻¹ := by group
      _ = (c * g) * (v * e) * (c * g)⁻¹ := by rw [h1]
      _ = (c * g) * v * (c * g)⁻¹ * ((c * g) * e * (c * g)⁻¹) := by group
  have hE'C : E' ≤ Subgroup.centralizer ({N.z} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hE'z e he)
  have hE'N : ∀ e' ∈ E', ∀ y ∈ N.X₁ ⊔ N.X₂ ⊔ P₀, e' * y * e'⁻¹ ∈ N.X₁ ⊔ N.X₂ ⊔ P₀ := by
    rintro _ ⟨e, he, rfl⟩ y hy
    have hq := hk2 y hy
    have hq' := hEQ e he _ hq
    have h1 := hk1 _ hq'
    have e1 : (c * g) * ((e * ((c * g)⁻¹ * y * (c * g)) * e⁻¹)) * (c * g)⁻¹ =
        ((c * g) * e * (c * g)⁻¹) * y * ((c * g) * e * (c * g)⁻¹)⁻¹ := by group
    rw [e1] at h1
    exact h1
  have hcard := card_two_sub_le h hP₀F hE'C (hE2.map _) hE'N
  rwa [hE', Subgroup.card_map_of_injective (MulAut.conj (c * g)).injective] at hcard

theorem card_twoPart_ge' (h : T6Ctx N u p) :
    2 ^ ((N.q₁ - 1).factorization 2 + (N.q₂ - 1).factorization 2) ≤
      Nat.card ↥(twoPart N.H h.sec5.loc.H_comm) := by
  have h1 := card_twoPart_ge N.H h.sec5.loc.H_comm
  have hq₁ := h.sec5.loc.q₁_ge
  have hq₂ := h.sec5.loc.q₂_ge
  rw [H_card h, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply] at h1
  exact h1

theorem twoPart_le_cent (h : T6Ctx N u p) {v : G} (hv : v = N.z ∨ v = u ∨ v = N.z * u) :
    twoPart N.H h.sec5.loc.H_comm ≤ Subgroup.centralizer ({v} : Set G) := by
  have hvH : v ∈ N.H := by
    rcases hv with hv | hv | hv
    · rw [hv]; exact h.sec5.loc.z_mem_H
    · rw [hv]; exact h.sec5.loc.u_mem_H
    · rw [hv]; exact N.H.mul_mem h.sec5.loc.z_mem_H h.sec5.loc.u_mem_H
  intro t ht
  exact Subgroup.mem_centralizer_singleton_iff.2 (h.sec5.loc.H_comm t ht.1 v hvH)

theorem norm_U_of_norm_T (h : T6Ctx N u p) (hΩ : T6Omega1 N u) {n : G}
    (hnT : ∀ t ∈ twoPart N.H h.sec5.loc.H_comm, n * t * n⁻¹ ∈ twoPart N.H h.sec5.loc.H_comm) :
    ∀ g ∈ t2U N.z u, n * g * n⁻¹ ∈ t2U N.z u := by
  obtain ⟨hz2, hu2, hzu, hz1, hu1, hne⟩ := zu_facts h
  intro g hg
  have hgT := U_le_twoPart h hg
  have hg2 : g * g = 1 := by
    rcases U_cases h hg with rfl | rfl | rfl | rfl
    · simp
    · exact hz2
    · exact hu2
    · calc N.z * u * (N.z * u) = N.z * (u * N.z) * u := by group
        _ = N.z * (N.z * u) * u := by rw [← hzu]
        _ = (N.z * N.z) * (u * u) := by group
        _ = 1 := by rw [hz2, hu2, one_mul]
  have h1 := hnT g hgT
  have h2 : (n * g * n⁻¹) * (n * g * n⁻¹) = 1 := by
    calc (n * g * n⁻¹) * (n * g * n⁻¹) = n * (g * g) * n⁻¹ := by group
      _ = 1 := by rw [hg2]; group
  exact (t2U_mem hz2 hu2 hzu).2 (hΩ _ h1.1 h2)

theorem T_relIndex_odd (h : T6Ctx N u p) (hR : T6RFacts N p) (hΩ : T6Omega1 N u) {m n : ℕ}
    (hm : N.q₁ = p ^ m) (hn : N.q₂ = p ^ n) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F)
    (hP₀p : IsPGroup p ↥P₀) (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p) :
    ¬ 2 ∣ (twoPart N.H h.sec5.loc.H_comm).relIndex
      (Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hz2, hu2, hzu, hz1, hu1, hne⟩ := zu_facts h
  set T : Subgroup G := twoPart N.H h.sec5.loc.H_comm with hT
  set M : Subgroup G := Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G) with hM
  have hTM : T ≤ M := fun t ht => twoPart_norm_Pst h hΩ hP₀F ht
  have hTp : IsPGroup 2 ↥T := twoPart_isPGroup _ _
  obtain ⟨S₂, hS₂⟩ := (hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm).exists_le_sylow
  set T'' : Subgroup G := (S₂ : Subgroup ↥M).map M.subtype with hT''
  have hT''p : IsPGroup 2 ↥T'' := S₂.isPGroup'.map _
  have hT''M : T'' ≤ M := Subgroup.map_subtype_le _
  have hTT'' : T ≤ T'' := fun t ht => ⟨⟨t, hTM ht⟩, hS₂ (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hT''T : T'' ≤ T := by
    by_contra hcon
    have hne' : T ≠ T'' := fun e => hcon (e ▸ le_rfl)
    obtain ⟨x, hxT'', hxT, hxN⟩ := t6_exists_normalizer_elt hT''p hTT'' hne'
    have hx2 : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hT''p ⟨x, hxT''⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hxU := norm_U_of_norm_T h hΩ hxN
    have hfix := t6_fixed_pt_klein hz2 hu2 hzu hz1 hu1 hne (fun g hg => by
      have hgU : g ∈ t2U N.z u := (t2U_mem hz2 hu2 hzu).2 hg
      exact (t2U_mem hz2 hu2 hzu).1 (hxU g hgU)) hx2
    have hE : ∀ v : G, (v = N.z ∨ v = u ∨ v = N.z * u) → x * v * x⁻¹ = v → False := by
      intro v hv hxv
      set E : Subgroup G := T ⊔ Subgroup.zpowers x with hE
      have hEle : E ≤ T'' := sup_le hTT'' (Subgroup.zpowers_le.2 hxT'')
      have hEC : E ≤ Subgroup.centralizer ({v} : Set G) := by
        refine sup_le (twoPart_le_cent h hv) ?_
        rw [Subgroup.zpowers_le]
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        calc x * v = (x * v * x⁻¹) * x := by group
          _ = v * x := by rw [hxv]
      have hcard := card_two_sub_Cv_le h hR hm hn hP₀F hP₀p hP₀c hv hEC (hEle.trans hT''M)
        (hT''p.to_le hEle)
      have hge := card_twoPart_ge' h
      have hTE : T ≤ E := le_sup_left
      have heq : T = E := Subgroup.eq_of_le_of_card_ge hTE (hcard.trans hge)
      exact hxT (heq ▸ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x) : x ∈ E))
    rcases hfix with hf | hf | hf
    · exact hE _ (Or.inl rfl) hf
    · exact hE _ (Or.inr (Or.inl rfl)) hf
    · exact hE _ (Or.inr (Or.inr rfl)) hf
  have hsub : T.subgroupOf M = (S₂ : Subgroup ↥M) := by
    apply le_antisymm hS₂
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hT''T ⟨x, hx, rfl⟩
  show ¬ 2 ∣ (T.subgroupOf M).index
  rw [hsub]
  exact S₂.not_dvd_index

omit [Finite G] in
theorem t6_odd_swap_false {x z u : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hxz : x * z * x⁻¹ = z)
    (hxu : x * u * x⁻¹ = z * u) (hodd : Odd (orderOf x)) : False := by
  obtain ⟨j, hj⟩ := hodd
  have h1 : x ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one x
  have hx2 : x * (x * u * x⁻¹) * x⁻¹ = u := by
    rw [hxu]
    calc x * (z * u) * x⁻¹ = (x * z * x⁻¹) * (x * u * x⁻¹) := by group
      _ = z * (z * u) := by rw [hxz, hxu]
      _ = u := by rw [← mul_assoc, hz2, one_mul]
  have hA : ∀ i : ℕ, x ^ (2 * i) * u * (x ^ (2 * i))⁻¹ = u := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : x ^ (2 * (i + 1)) = x ^ (2 * i) * (x * x) := by
        rw [mul_add, mul_one, pow_add, pow_two]
      rw [e]
      calc x ^ (2 * i) * (x * x) * u * (x ^ (2 * i) * (x * x))⁻¹
          = x ^ (2 * i) * (x * (x * u * x⁻¹) * x⁻¹) * (x ^ (2 * i))⁻¹ := by group
        _ = x ^ (2 * i) * u * (x ^ (2 * i))⁻¹ := by rw [hx2]
        _ = u := ih
  have h2 : x ^ (2 * j + 1) * u * (x ^ (2 * j + 1))⁻¹ = z * u := by
    have e : x ^ (2 * j + 1) = x * x ^ (2 * j) := pow_succ' x (2 * j)
    rw [e]
    calc x * x ^ (2 * j) * u * (x * x ^ (2 * j))⁻¹
        = x * (x ^ (2 * j) * u * (x ^ (2 * j))⁻¹) * x⁻¹ := by group
      _ = z * u := by rw [hA j, hxu]
  rw [h1] at h2
  apply hz1
  have h3 : u = z * u := by simpa using h2
  calc z = z * u * u⁻¹ := by group
    _ = u * u⁻¹ := by rw [← h3]
    _ = 1 := by group

theorem odd_normalizer_cent_T (h : T6Ctx N u p) (hR : T6RFacts N p) (hΩ : T6Omega1 N u)
    {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) {x : G}
    (hxM : x ∈ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G))
    (hxT : ∀ t ∈ twoPart N.H h.sec5.loc.H_comm, x * t * x⁻¹ ∈ twoPart N.H h.sec5.loc.H_comm)
    (hodd : Odd (orderOf x)) : ∀ t ∈ twoPart N.H h.sec5.loc.H_comm, x * t = t * x := by
  obtain ⟨hz2, hu2, hzu, hz1, hu1, hne⟩ := zu_facts h
  have hxU := norm_U_of_norm_T h hΩ hxT
  have hxUn : x ∈ Subgroup.normalizer ((t2U N.z u : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype hxU
  have hxz := no_cycle h hR hP₀F hxM hxUn
  have hxu : x * u * x⁻¹ = u := by
    have hu' : u ∈ t2U N.z u := (t2U_mem hz2 hu2 hzu).2 (Or.inr (Or.inr (Or.inl rfl)))
    rcases U_cases h (hxU u hu') with h1 | h1 | h1 | h1
    · exfalso
      apply hu1
      calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      apply hne
      calc N.z = x⁻¹ * (x * N.z * x⁻¹) * x := by group
        _ = x⁻¹ * (x * u * x⁻¹) * x := by rw [hxz, h1]
        _ = u := by group
    · exact h1
    · exact (t6_odd_swap_false hz2 hz1 hxz h1 hodd).elim
  have hinv : ∀ t ∈ twoPart N.H h.sec5.loc.H_comm, t * t = 1 → x * t * x⁻¹ = t := by
    intro t ht ht2
    rcases hΩ t ht.1 ht2 with rfl | rfl | rfl | rfl
    · group
    · exact hxz
    · exact hxu
    · calc x * (N.z * u) * x⁻¹ = (x * N.z * x⁻¹) * (x * u * x⁻¹) := by group
        _ = N.z * u := by rw [hxz, hxu]
  have hcent := t6_cent_of_cent_invols (T := twoPart N.H h.sec5.loc.H_comm)
    (fun a ha b hb => h.sec5.loc.H_comm a ha.1 b hb.1) (fun t ht => ht.2) hxT hodd hinv
  intro t ht
  calc x * t = (x * t * x⁻¹) * x := by group
    _ = t * x := by rw [hcent t ht]

theorem card_pSub_le_vp {p : ℕ} (hp : p.Prime) {K E : Subgroup G} (hEK : E ≤ K) (hE : IsPGroup p ↥E) :
    Nat.card ↥E ≤ p ^ (Nat.card ↥K).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := (hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEK).symm).exists_le_sylow
  have h1 := Subgroup.card_le_of_le hS
  rw [Sylow.card_eq_multiplicity S] at h1
  have h2 : Nat.card ↥(E.subgroupOf K) = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  omega

theorem Pst_sylow (h : T6Ctx N u p) (hR : T6RFacts N p) (hΩ : T6Omega1 N u) {m n : ℕ}
    (hm : N.q₁ = p ^ m) (hn : N.q₂ = p ^ n) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F)
    (hP₀p : IsPGroup p ↥P₀) (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p) :
    ∃ S : Sylow p G, (S : Subgroup G) = R₂ N p ⊔ N.X₁ ⊔ P₀ := by
  have : Fact p.Prime := ⟨h.prime⟩
  set T : Subgroup G := twoPart N.H h.sec5.loc.H_comm with hT
  set Ps : Subgroup G := R₂ N p ⊔ N.X₁ ⊔ P₀ with hPs
  set M : Subgroup G := Subgroup.normalizer (Ps : Set G) with hM
  have hPp : IsPGroup p ↥Ps := Pst_pGroup h hR hP₀F hP₀p
  have hTM : T ≤ M := fun t ht => twoPart_norm_Pst h hΩ hP₀F ht
  have hTp : IsPGroup 2 ↥T := twoPart_isPGroup _ _
  have hTidx : ¬ 2 ∣ T.relIndex M := T_relIndex_odd h hR hΩ hm hn hP₀F hP₀p hP₀c
  have hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => h.sec5.loc.H_comm a ha.1 b hb.1
  obtain ⟨K, hKM, hKn, hKodd, hKcard⟩ := t6_two_complement M T hTM hTp hTidx hab
    (fun x hx hxT hodd => odd_normalizer_cent_T h hR hΩ hP₀F hx hxT hodd)
  have hPsM : Ps ≤ M := Subgroup.le_normalizer
  have hKn' : (K.subgroupOf M).Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hKn g g.2 k hk⟩
  have hTcard : Nat.card ↥T = 2 ^ (Nat.card ↥T).factorization 2 := by
    obtain ⟨b, hb⟩ := hTp.exists_card_eq
    rw [hb, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hrelK : K.relIndex M = Nat.card ↥T := by
    have := Subgroup.relIndex_mul_card K M
    rw [inf_eq_left.2 hKM] at this
    have hpos := Nat.card_pos (α := ↥K)
    exact Nat.eq_of_mul_eq_mul_right hpos (this.trans (hKcard.trans (mul_comm _ _)))
  have hPsK : Ps ≤ K := by
    intro x hx
    have hxM : x ∈ M := hPsM hx
    have h1 : (⟨x, hxM⟩ : ↥M) ^ (K.subgroupOf M).index ∈ K.subgroupOf M :=
      Subgroup.pow_index_mem (K.subgroupOf M) _
    have h2 : x ^ Nat.card ↥T ∈ K := by
      rw [← hrelK]
      have := (Subgroup.mem_subgroupOf).1 h1
      simpa [Subgroup.relIndex] using this
    have hord : ∃ j : ℕ, orderOf x = p ^ j := by
      have := (IsPGroup.iff_orderOf (p := p)).1 hPp ⟨x, hx⟩
      obtain ⟨j, hj⟩ := this
      exact ⟨j, by simpa [Subgroup.orderOf_coe] using hj⟩
    have hcop : Nat.Coprime p (Nat.card ↥T) := by
      obtain ⟨b, hb⟩ := hTp.exists_card_eq
      rw [hb]
      exact Nat.Coprime.pow_right b ((Nat.coprime_primes h.prime Nat.prime_two).2 h.p_ne_two)
    exact t6_mem_of_pow hord hcop h2
  have hUM : ∀ g ∈ t2U N.z u, g ∈ M := fun g hg => hTM (U_le_twoPart h hg)
  have hKodd' : Odd (Nat.card ↥K) := Nat.odd_iff.2 (by omega)
  obtain ⟨Q, hQK, hQp, hQc, hQU⟩ := t6_exists_invariant_sylow (hTp.to_le (U_le_twoPart h)) hKodd'
    (fun g hg k hk => hKn g (hUM g hg) k hk) h.prime
  have hQPs : Q ≤ Ps := Pst_max_U h hR hm hn hP₀F hP₀p hP₀c hQp (hQK.trans hKM) hQU
  have hcardPs : Nat.card ↥Ps = p ^ (Nat.card ↥K).factorization p :=
    le_antisymm (card_pSub_le_vp h.prime hPsK hPp) (hQc ▸ Subgroup.card_le_of_le hQPs)
  have hrel : Ps.relIndex M * Nat.card ↥Ps = Nat.card ↥M := by
    have := Subgroup.relIndex_mul_card Ps M
    rwa [inf_eq_left.2 hPsM] at this
  have hN : ¬ p ∣ Ps.relIndex M := by
    intro hd
    have hKpos : Nat.card ↥K ≠ 0 := (Nat.card_pos).ne'
    have h1 : p ^ ((Nat.card ↥K).factorization p + 1) ∣ Nat.card ↥K * Nat.card ↥T := by
      rw [← hKcard, ← hrel, hcardPs, pow_succ']
      exact Nat.mul_dvd_mul_right hd _
    have hcop : Nat.Coprime (p ^ ((Nat.card ↥K).factorization p + 1)) (Nat.card ↥T) := by
      obtain ⟨b, hb⟩ := hTp.exists_card_eq
      rw [hb]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes h.prime Nat.prime_two).2 h.p_ne_two)
    have h2 := hcop.dvd_of_dvd_mul_right h1
    have h3 := (Nat.Prime.pow_dvd_iff_le_factorization h.prime hKpos).1 h2
    omega
  have hidx := t6_sylow_of_normalizer h.prime hPp hN
  exact ⟨hPp.toSylow hidx, rfl⟩

end CFSG.GH74.GLS.Stage4.Rest.T6
