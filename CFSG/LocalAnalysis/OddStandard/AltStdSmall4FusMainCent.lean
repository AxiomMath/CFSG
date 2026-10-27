module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusMainX

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.Main

open Subgroup Equiv AltStdCycTwo

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G}

theorem mem_V0_of_two_pow (c : Config G L Q n θ z) {s : G}
    (hsC : s ∈ centralizer ({z} : Set G)) (hsE : s ∈ centralizer (E θ c.hn8 : Set G)) {k : ℕ}
    (hk : s ^ 2 ^ k = 1) : s ∈ E θ c.hn8 ⊔ zpowers z := by
  have hcomm : ∀ e ∈ eBar c.hn8,
      rhoC c ⟨s, hsC⟩ * (e : Perm (Fin n)) = e * rhoC c ⟨s, hsC⟩ := by
    intro e he
    have heE : ((θ.symm e : L) : G) ∈ E θ c.hn8 := mem_E_of_mem_eBar θ c.hn8 he
    have heC : ((θ.symm e : L) : G) ∈ centralizer ({z} : Set G) := L_le_cent c (θ.symm e).2
    have h1 : (⟨s, hsC⟩ : centralizer ({z} : Set G)) * ⟨_, heC⟩ = ⟨_, heC⟩ * ⟨s, hsC⟩ :=
      Subtype.ext (mem_centralizer_iff.1 hsE _ heE).symm
    have h2 := congrArg (rhoC c) h1
    rwa [map_mul, map_mul, rhoC_symm] at h2
  have hk' : rhoC c ⟨s, hsC⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨s, hsC⟩ : centralizer ({z} : Set G)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hev : n ≤ 9 ∨ rhoC c ⟨s, hsC⟩ ∈ alternatingGroup (Fin n) := by
    rcases c.shape with hsh | ⟨h9, -⟩
    · exact Or.inr ((mem_evenAct_iff θ c.hn8 (cent_le_normalizer c.ot.std c.ot.cyc hsC)).1
        (sup_le_evenAct θ c.hn8 (hsh hsC)))
    · exact Or.inl h9
  obtain ⟨e, he, hσe⟩ := exists_eBar_eq_of_comm c.hn8 c.small hcomm hk' hev
  have heE : ((θ.symm e : L) : G) ∈ E θ c.hn8 := mem_E_of_mem_eBar θ c.hn8 he
  have heC : ((θ.symm e : L) : G) ∈ centralizer ({z} : Set G) := L_le_cent c (θ.symm e).2
  have hker : (⟨s, hsC⟩ : centralizer ({z} : Set G)) * (⟨_, heC⟩)⁻¹ ∈ (rhoC c).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, rhoC_symm, hσe, mul_inv_cancel]
  have hK : s * ((θ.symm e : L) : G)⁻¹ ∈ centralizer (L : Set G) := (mem_ker_rhoC_iff c _).1 hker
  have hC : s * ((θ.symm e : L) : G)⁻¹ ∈ centralizer ({z} : Set G) := mul_mem hsC (inv_mem heC)
  have hse : Commute s ((θ.symm e : L) : G)⁻¹ :=
    Commute.inv_right (mem_centralizer_iff.1 hsE _ heE).symm
  have he2 : ((θ.symm e : L) : G) ^ 2 = 1 := by
    rw [sq]
    exact mul_self_of_mem_V0 c (mem_sup_left heE)
  have hpow : (s * ((θ.symm e : L) : G)⁻¹) ^ 2 ^ (k + 1) = 1 := by
    rw [hse.mul_pow]
    have h1 : s ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
    have h2 : (((θ.symm e : L) : G)⁻¹) ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ', pow_mul, inv_pow, he2, inv_one, one_pow]
    rw [h1, h2, one_mul]
  have hz := mem_zpowers_of_two_pow c.ot.cyc c.ot.card ⟨hK, hC⟩ hpow
  have : s = (s * ((θ.symm e : L) : G)⁻¹) * ((θ.symm e : L) : G) := by group
  rw [this]
  exact mul_mem (mem_sup_right hz) (mem_sup_left heE)

section LemmaC

variable {c : Config G L Q n θ z} {H : Subgroup G} {Nbar Rbar : Subgroup (Perm (Fin n))} {x : G}

theorem IsHStar.mem_xSub_of_comm (hH : IsHStar c H Nbar) (htr : ∀ v : Fin 8, tr c.hn8 v ∈ Rbar)
    (hxN : x ∈ normalizer (sSyl c H Rbar : Set G)) (hxz : x⁻¹ * z * x = z * w θ c.hn8)
    (hxw : x⁻¹ * w θ c.hn8 * x = w θ c.hn8) {t : G} (htH : t ∈ H) {k : ℕ}
    (htk : t ^ 2 ^ k = 1) (htX : ∀ y ∈ xSub θ c.hn8 z x H, t * y = y * t) :
    t ∈ xSub θ c.hn8 z x H := by
  have htz : t * z = z * t := mem_centralizer_singleton_iff.1 (hH.le htH)
  have htV : ∀ v ∈ vOne θ c.hn8 z x, t * v = v * t := by
    intro v hv
    rcases (hH.mem_vOne_iff_xSub htr hxN hxz hxw).1 hv with h | h
    · exact htX v h
    · have h1 := htX _ h
      apply mul_right_cancel (b := z)
      calc t * v * z = t * (v * z) := by group
        _ = v * z * t := h1
        _ = v * t * z := by rw [mul_assoc, ← htz, ← mul_assoc]
  have hsV : ∀ v ∈ E θ c.hn8 ⊔ zpowers z, x * t * x⁻¹ * v = v * (x * t * x⁻¹) := by
    intro v hv
    have hv' : x⁻¹ * v * x ∈ vOne θ c.hn8 z x := by
      rw [mem_vOne_iff]
      simpa [mul_assoc] using hv
    have h1 := htV _ hv'
    calc x * t * x⁻¹ * v = x * (t * (x⁻¹ * v * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * v * x) * t) * x⁻¹ := by rw [h1]
      _ = v * (x * t * x⁻¹) := by group
  have hsC : x * t * x⁻¹ ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 (hsV z (mem_sup_right (mem_zpowers z)))
  have hsE : x * t * x⁻¹ ∈ centralizer (E θ c.hn8 : Set G) :=
    mem_centralizer_iff.2 fun e he => (hsV e (mem_sup_left he)).symm
  have hsk : (x * t * x⁻¹) ^ 2 ^ k = 1 := by rw [conj_pow, htk]; group
  exact ⟨mem_vOne_iff.2 (mem_V0_of_two_pow c hsC hsE hsk), htH⟩

end LemmaC

theorem N0_le_cent (c : Config G L Q n θ z)
    (hneg : ∀ g ∈ N0 θ c.hn8 z, g * z * g⁻¹ ≠ z * w θ c.hn8) :
    N0 θ c.hn8 z ≤ centralizer ({z} : Set G) := by
  intro g hg
  obtain ⟨i, hi⟩ := N0.conj_z_eq c.hn8 c hg
  by_cases h0 : i = 0
  · rw [h0, N0.eps_zero, mul_one] at hi
    rw [mem_centralizer_singleton_iff]
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hi]
  · exfalso
    obtain ⟨k, hk⟩ := N0.exists_mPerm_pow_eq i 1 h0 (by decide)
    apply hneg (N0.sg θ c.hn8 ^ k * g) (mul_mem (pow_mem (N0.sg_mem_N0 c.hn8 c) k) hg)
    have hcomm : N0.sg θ c.hn8 ^ k * z = z * N0.sg θ c.hn8 ^ k :=
      (Commute.pow_left (N0.sg_comm_z c.hn8 c) k).eq
    calc N0.sg θ c.hn8 ^ k * g * z * (N0.sg θ c.hn8 ^ k * g)⁻¹
        = N0.sg θ c.hn8 ^ k * (g * z * g⁻¹) * (N0.sg θ c.hn8 ^ k)⁻¹ := by group
      _ = N0.sg θ c.hn8 ^ k * z * N0.eps θ c.hn8 i * (N0.sg θ c.hn8 ^ k)⁻¹ := by rw [hi]; group
      _ = z * (N0.sg θ c.hn8 ^ k * N0.eps θ c.hn8 i * (N0.sg θ c.hn8 ^ k)⁻¹) := by
          rw [hcomm]; group
      _ = z * w θ c.hn8 := by
          rw [N0.pow_conj_eps θ c.hn8 (N0.sg_conj_eps θ c.hn8), hk, N0.w_eq_eps]

section Norm

variable {c : Config G L Q n θ z} {H : Subgroup G} {Nbar Rbar : Subgroup (Perm (Fin n))} {x : G}

theorem IsHStar.comm_w_of_normalizes (hH : IsHStar c H Nbar)
    (htr : ∀ v : Fin 8, tr c.hn8 v ∈ Rbar) (hxN : x ∈ normalizer (sSyl c H Rbar : Set G))
    (hxz : x⁻¹ * z * x = z * w θ c.hn8) (hxw : x⁻¹ * w θ c.hn8 * x = w θ c.hn8)
    (hneg : ∀ g ∈ N0 θ c.hn8 z, g * z * g⁻¹ ≠ z * w θ c.hn8) {h : G} (hhH : h ∈ H)
    (hhX : ∀ y ∈ xSub θ c.hn8 z x H, h * y * h⁻¹ ∈ xSub θ c.hn8 z x H) :
    h * w θ c.hn8 = w θ c.hn8 * h := by
  have hhz : h * z = z * h := mem_centralizer_singleton_iff.1 (hH.le hhH)
  have hiz : h⁻¹ * z = z * h⁻¹ := (Commute.inv_left hhz).eq
  have hV1 : ∀ v ∈ vOne θ c.hn8 z x, h * v * h⁻¹ ∈ vOne θ c.hn8 z x := by
    intro v hv
    rcases (hH.mem_vOne_iff_xSub htr hxN hxz hxw).1 hv with h1 | h1
    · exact xSub_le_vOne (hhX v h1)
    · have h2 := xSub_le_vOne (hhX _ h1)
      have e : h * v * h⁻¹ = h * (v * z) * h⁻¹ * z := by
        calc h * v * h⁻¹ = h * v * (z * z) * h⁻¹ := by rw [z_mul_self c, mul_one]
          _ = h * (v * z) * (z * h⁻¹) := by group
          _ = h * (v * z) * h⁻¹ * z := by rw [← hiz]; group
      rw [e]
      exact mul_mem h2 (z_mem_vOne c hxz hxw)
  have hN0 : x * h * x⁻¹ ∈ N0 θ c.hn8 z := by
    apply mem_normalizer_fintype
    intro v hv
    have hv' : x⁻¹ * v * x ∈ vOne θ c.hn8 z x := by
      rw [mem_vOne_iff]
      simpa [mul_assoc] using hv
    have h1 := mem_vOne_iff.1 (hV1 _ hv')
    have e : x * h * x⁻¹ * v * (x * h * x⁻¹)⁻¹ = x * (h * (x⁻¹ * v * x) * h⁻¹) * x⁻¹ := by
      group
    rw [e]
    exact h1
  have h1 := mem_centralizer_singleton_iff.1 (N0_le_cent c hneg hN0)
  have h2 : h * (z * w θ c.hn8) = z * w θ c.hn8 * h := by
    rw [← hxz]
    calc h * (x⁻¹ * z * x) = x⁻¹ * (x * h * x⁻¹ * z) * x := by group
      _ = x⁻¹ * (z * (x * h * x⁻¹)) * x := by rw [h1]
      _ = x⁻¹ * z * x * h := by group
  apply mul_left_cancel (a := z)
  calc z * (h * w θ c.hn8) = h * z * w θ c.hn8 := by rw [hhz]; group
    _ = h * (z * w θ c.hn8) := by group
    _ = z * w θ c.hn8 * h := h2
    _ = z * (w θ c.hn8 * h) := by group

end Norm

end CFSG.OddStandard.AltStdSmall4.Fus.Main
