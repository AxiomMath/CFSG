module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ParaB
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ParaA

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

namespace Out12

variable {x : G} {T V : Subgroup G} (h : Out12 G x T V)
include h

theorem EV_sylow_cent [Finite G] {Q : Subgroup G} (hEQ : EV x V ≤ Q)
    (hQC : Q ≤ centralizer (V : Set G)) :
    SylowIn 2 (EV x V) (Q ⊓ centralizer ({x} : Set G)) := by
  have hE : EV x V ≤ Q ⊓ centralizer ({x} : Set G) := by
    intro e he
    refine ⟨hEQ he, ?_⟩
    show e ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact h.EV_comm x_mem_EV he
  obtain ⟨P, hP, hEP⟩ := SylowIn.exists_ge (p := 2) hE h.EV_isPGroup
  have hPE : P ≤ EV x V := by
    apply h.cent_E_le hP.isPGroup
    intro g hg
    have hg' := hP.le hg
    exact h.centralizes_EV (hQC hg'.1) hg'.2
  have hP' : P = EV x V := le_antisymm hPE hEP
  rw [hP'] at hP
  exact hP

theorem card_cent_of [Finite G] {Q : Subgroup G} (hEQ : EV x V ≤ Q)
    (hQC : Q ≤ centralizer (V : Set G)) :
    ∃ o : ℕ, ¬ 2 ∣ o ∧ Nat.card ↥(Q ⊓ centralizer ({x} : Set G)) = 8 * o := by
  have hS := h.EV_sylow_cent hEQ hQC
  have hE : EV x V ≤ Q ⊓ centralizer ({x} : Set G) := hS.le
  have hrel := relIndex_mul_card (EV x V) (Q ⊓ centralizer ({x} : Set G))
  rw [inf_of_le_left hE, h.card_EV] at hrel
  exact ⟨_, hS.2.2, by rw [← hrel]; ring⟩

theorem T_le_normalizer {t : G} (ht : t ∈ T) : t ∈ normalizer (V : Set G) := by
  rw [mem_normalizer_iff]
  intro v
  refine ⟨fun hv => h.V_norm t ht v hv, fun hv => ?_⟩
  have := h.V_norm t⁻¹ (T.inv_mem ht) _ hv
  have e : t⁻¹ * (t * v * t⁻¹) * t⁻¹⁻¹ = v := by group
  rwa [e] at this

end Out12

theorem odd_index_ZK [Finite G] {x : G} {T V H : Subgroup G} (h : Out12 G x T V)
    (hEH : EV x V ≤ H) (hHC : H ≤ centralizer (V : Set G))
    (hsyl : Sylow2In H (centralizer (V : Set G)))
    (hcov : ∀ b ∈ Bb V H, ∃ h ∈ H, b * x * b⁻¹ = h * x * h⁻¹) :
    ¬ 2 ∣ (Bb V H ⊓ centralizer ({x} : Set G)).relIndex
      (normalizer (V : Set G) ⊓ centralizer ({x} : Set G)) := by
  have hKZ : Bb V H ⊓ centralizer ({x} : Set G) ≤ normalizer (V : Set G) ⊓ centralizer ({x} : Set G) :=
    inf_le_inf_right _ (fun b hb => hb.1)
  have hZN : normalizer (V : Set G) ⊓ centralizer ({x} : Set G) ≤ normalizer (V : Set G) :=
    inf_le_left
  have hHB : H ≤ Bb V H := fun g hg =>
    ⟨centralizer_le_normalizer _ (hHC hg), le_normalizer hg⟩
  have hrel : (centralizer (V : Set G) ⊓ (Bb V H ⊓ centralizer ({x} : Set G))).relIndex
      (Bb V H ⊓ centralizer ({x} : Set G)) =
      (centralizer (V : Set G) ⊓ (normalizer (V : Set G) ⊓ centralizer ({x} : Set G))).relIndex
        (normalizer (V : Set G) ⊓ centralizer ({x} : Set G)) := by
    apply relIndex_eq_of_mul V hKZ hZN
    intro z hz
    obtain ⟨c, hc, hcz⟩ := frattini_N hsyl (hZN hz)
    have hcN : c⁻¹ ∈ normalizer (V : Set G) :=
      centralizer_le_normalizer _ ((centralizer (V : Set G)).inv_mem hc)
    have hbB : c⁻¹ * z ∈ Bb V H := ⟨(normalizer (V : Set G)).mul_mem hcN (hZN hz), hcz⟩
    obtain ⟨hh, hhH, hbx⟩ := hcov _ hbB
    have hκB : hh⁻¹ * (c⁻¹ * z) ∈ Bb V H := (Bb V H).mul_mem ((Bb V H).inv_mem (hHB hhH)) hbB
    have hκx : x * (hh⁻¹ * (c⁻¹ * z)) = (hh⁻¹ * (c⁻¹ * z)) * x := by
      have e : (hh⁻¹ * (c⁻¹ * z)) * x * (hh⁻¹ * (c⁻¹ * z))⁻¹ = x := by
        calc (hh⁻¹ * (c⁻¹ * z)) * x * (hh⁻¹ * (c⁻¹ * z))⁻¹
            = hh⁻¹ * ((c⁻¹ * z) * x * (c⁻¹ * z)⁻¹) * hh := by group
          _ = hh⁻¹ * (hh * x * hh⁻¹) * hh := by rw [hbx]
          _ = x := by group
      exact (mul_inv_eq_iff_eq_mul.1 e).symm
    refine ⟨c * hh, (centralizer (V : Set G)).mul_mem hc (hHC hhH), hh⁻¹ * (c⁻¹ * z),
      ⟨hκB, ?_⟩, by group⟩
    show hh⁻¹ * (c⁻¹ * z) ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hκx
  have hCZ : centralizer (V : Set G) ⊓ (normalizer (V : Set G) ⊓ centralizer ({x} : Set G)) =
      centralizer (V : Set G) ⊓ centralizer ({x} : Set G) := by
    ext m
    constructor
    · intro hm; exact ⟨hm.1, hm.2.2⟩
    · intro hm; exact ⟨hm.1, centralizer_le_normalizer _ hm.1, hm.2⟩
  have hCK : centralizer (V : Set G) ⊓ (Bb V H ⊓ centralizer ({x} : Set G)) =
      Mm V H ⊓ centralizer ({x} : Set G) := by
    ext m
    constructor
    · intro hm; exact ⟨⟨hm.1, hm.2.1.2⟩, hm.2.2⟩
    · intro hm; exact ⟨hm.1.1, ⟨centralizer_le_normalizer _ hm.1.1, hm.1.2⟩, hm.2⟩
  have N1 := relIndex_mul_card (centralizer (V : Set G) ⊓ (Bb V H ⊓ centralizer ({x} : Set G)))
    (Bb V H ⊓ centralizer ({x} : Set G))
  rw [inf_of_le_left inf_le_right] at N1
  have N2 := relIndex_mul_card
    (centralizer (V : Set G) ⊓ (normalizer (V : Set G) ⊓ centralizer ({x} : Set G)))
    (normalizer (V : Set G) ⊓ centralizer ({x} : Set G))
  rw [inf_of_le_left inf_le_right] at N2
  have N3 := relIndex_mul_card (Bb V H ⊓ centralizer ({x} : Set G))
    (normalizer (V : Set G) ⊓ centralizer ({x} : Set G))
  rw [inf_of_le_left hKZ] at N3
  rw [hrel] at N1
  obtain ⟨o₁, ho₁, hc₁⟩ := h.card_cent_of (Q := centralizer (V : Set G)) h.E_le_C le_rfl
  obtain ⟨o₂, ho₂, hc₂⟩ := h.card_cent_of (Q := Mm V H)
    (fun e he => ⟨h.E_le_C he, le_normalizer (hEH he)⟩) (fun m hm => hm.1)
  have hcardCZ : Nat.card ↥(centralizer (V : Set G) ⊓
      (normalizer (V : Set G) ⊓ centralizer ({x} : Set G))) = 8 * o₁ := by
    rw [hCZ]; exact hc₁
  have hcardCK : Nat.card ↥(centralizer (V : Set G) ⊓
      (Bb V H ⊓ centralizer ({x} : Set G))) = 8 * o₂ := by
    rw [hCK]; exact hc₂
  rw [hcardCZ] at N2
  rw [hcardCK] at N1
  set k := (centralizer (V : Set G) ⊓
    (normalizer (V : Set G) ⊓ centralizer ({x} : Set G))).relIndex
    (normalizer (V : Set G) ⊓ centralizer ({x} : Set G)) with hkdef
  set q := (Bb V H ⊓ centralizer ({x} : Set G)).relIndex
    (normalizer (V : Set G) ⊓ centralizer ({x} : Set G)) with hqdef
  set nK := Nat.card ↥(Bb V H ⊓ centralizer ({x} : Set G)) with hnK
  set nZ := Nat.card ↥(normalizer (V : Set G) ⊓ centralizer ({x} : Set G)) with hnZ
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      have hpos : 0 < nZ := Nat.card_pos
      rw [h0, zero_mul] at N2
      omega
    · exact h0
  have e1 : k * (q * (8 * o₂)) = k * (8 * o₁) := by
    calc k * (q * (8 * o₂)) = q * (k * (8 * o₂)) := by ring
      _ = q * nK := by rw [N1]
      _ = nZ := N3
      _ = k * (8 * o₁) := N2.symm
  have e2 := Nat.eq_of_mul_eq_mul_left hk0 e1
  have e3 : q * o₂ = o₁ := by
    have : 8 * (q * o₂) = 8 * o₁ := by rw [← e2]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  intro hq2
  apply ho₁
  rw [← e3]
  exact Dvd.dvd.mul_right hq2 _

theorem exists_conj_T [Finite G] {x : G} {T V H : Subgroup G} (h : Out12 G x T V)
    (hEH : EV x V ≤ H) (hHC : H ≤ centralizer (V : Set G))
    (hsyl : Sylow2In H (centralizer (V : Set G)))
    (hcov : ∀ b ∈ Bb V H, ∃ h ∈ H, b * x * b⁻¹ = h * x * h⁻¹) :
    ∃ c ∈ normalizer (V : Set G) ⊓ centralizer ({x} : Set G),
      ∀ t ∈ T, c * t * c⁻¹ ∈ Bb V H := by
  have hodd := odd_index_ZK h hEH hHC hsyl hcov
  have hKZ : Bb V H ⊓ centralizer ({x} : Set G) ≤
      normalizer (V : Set G) ⊓ centralizer ({x} : Set G) :=
    inf_le_inf_right _ (fun b hb => hb.1)
  have hZC : normalizer (V : Set G) ⊓ centralizer ({x} : Set G) ≤ centralizer ({x} : Set G) :=
    inf_le_right
  have hTZ : T ≤ normalizer (V : Set G) ⊓ centralizer ({x} : Set G) :=
    fun t ht => ⟨h.T_le_normalizer ht, h.T_sylow.1 ht⟩
  have hTsyl : SylowIn 2 T (normalizer (V : Set G) ⊓ centralizer ({x} : Set G)) := by
    refine ⟨hTZ, h.T_sylow.2.1, ?_⟩
    have hmul := relIndex_mul_relIndex T (normalizer (V : Set G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)) hTZ hZC
    intro hd
    apply h.T_sylow.2.2
    rw [← hmul]
    exact Dvd.dvd.mul_right hd _
  have hbot : IsPGroup 2 ↥(⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨TK, hTK, -⟩ := SylowIn.exists_ge (p := 2)
    (bot_le : (⊥ : Subgroup G) ≤ Bb V H ⊓ centralizer ({x} : Set G)) hbot
  have hTKZ : SylowIn 2 TK (normalizer (V : Set G) ⊓ centralizer ({x} : Set G)) := by
    refine ⟨hTK.le.trans hKZ, hTK.isPGroup, ?_⟩
    have hmul := relIndex_mul_relIndex TK (Bb V H ⊓ centralizer ({x} : Set G))
      (normalizer (V : Set G) ⊓ centralizer ({x} : Set G)) hTK.le hKZ
    intro hd
    rw [← hmul] at hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h1 | h1
    · exact hTK.2.2 h1
    · exact hodd h1
  obtain ⟨c, hcZ, hc⟩ := SylowIn.conj (p := 2) hTsyl hTKZ
  refine ⟨c, hcZ, fun t ht => ?_⟩
  have e : c⁻¹ * (c * t * c⁻¹) * c = t := by group
  have : c * t * c⁻¹ ∈ TK := (hc _).2 (by rw [e]; exact ht)
  exact (hTK.le this).1

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
