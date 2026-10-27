module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46Cl

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

theorem not_comm_field_odd : ∀ (u : (ZMod 8)ˣ) (b : ZMod 8) (u' : (ZMod 8)ˣ) (b' : ZMod 8),
    dbit8 b = 0 → fbit8 u = 1 → dbit8 b' = 1 → aff8 u b ^ 2 = 1 →
    aff8 u' b' * aff8 u b ≠ aff8 u b * aff8 u' b' := by
  intro u b u' b'
  simp only [pow_two, aff8_mul, aff8_eq_one_iff]
  revert u b u' b'
  decide

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {A : L2Data t L}

@[expose] noncomputable def tauX (A : L2Data t L) (g : X) : Multiplicative (ZMod 2 × ZMod 2) :=
  open Classical in if h : g ∈ centralizer ({t} : Set X) then A.τ ⟨g, h⟩ else 1

theorem tauX_of_mem {g : X} (hg : g ∈ centralizer ({t} : Set X)) : tauX A g = A.τ ⟨g, hg⟩ := by
  simp [tauX, hg]

theorem tauX_conj {c g : X} (hc : c ∈ centralizer ({t} : Set X))
    (hg : g ∈ centralizer ({t} : Set X)) : tauX A (c * g * c⁻¹) = tauX A g := by
  rw [tauX_of_mem (mul_mem (mul_mem hc hg) (inv_mem hc)), tauX_of_mem hg]
  have : (⟨c * g * c⁻¹, mul_mem (mul_mem hc hg) (inv_mem hc)⟩ : centralizer ({t} : Set X)) =
      ⟨c, hc⟩ * ⟨g, hg⟩ * (⟨c, hc⟩)⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, mul_comm (A.τ ⟨c, hc⟩)]
  exact mul_inv_cancel_right _ _

theorem tauX_of_mem_T {g : X} (hg : g ∈ A.T) {u : (ZMod 8)ˣ} {b : ZMod 8}
    (hψ : ψX A g = aff8 u b) : tauX A g = Multiplicative.ofAdd (dbit8 b, fbit8 u) := by
  rw [tauX_of_mem (A.T_le_centralizer hg)]
  have h := A.τ_eq ⟨g, hg⟩
  have e : (⟨A.ψ ⟨g, hg⟩, A.ψ_mem_H8 ⟨g, hg⟩⟩ : H8) = ⟨aff8 u b, aff8_mem_H8 u b⟩ := by
    apply Subtype.ext
    show A.ψ ⟨g, hg⟩ = aff8 u b
    rw [← ψX_of_mem hg, hψ]
  rw [e, type8_aff8] at h
  exact h

variable [Finite X] {C : A.CaseKD} (S : KDBase A C)

theorem R_le_TE : A.R ≤ S.TE := fun _ hr => by
  rw [mem_TE_iff]
  refine ⟨hr.1, ?_⟩
  obtain ⟨v, c, -, hψ⟩ := ψX_mem_R8 hr
  rw [← hψ, mem_PTE]
  exact dbit8_two_mul c

theorem comm_mem_R_of_mem_TE {g h : X} (hg : g ∈ S.TE) (hh : h ∈ S.TE) :
    g * h * g⁻¹ * h⁻¹ ∈ A.R := by
  have hdec : ∀ {g : X}, g ∈ S.TE → ∃ r ∈ A.R, ∃ c ∈ S.B, g = r * c := by
    intro g hg
    obtain ⟨hgT, ⟨u, b, hub, hb⟩⟩ := (mem_TE_iff S).mp hg
    obtain ⟨r, hr, a, e, -, -, rfl, -⟩ := exists_eq_of_mem_T C hgT hub.symm hb
    exact ⟨r, hr, t ^ a * C.k ^ e, mul_mem (pow_mem (mem_B_t S) _) (pow_mem (mem_B_k S) _),
      by rw [mul_assoc]⟩
  obtain ⟨r₁, hr₁, c₁, hc₁, rfl⟩ := hdec hg
  obtain ⟨r₂, hr₂, c₂, hc₂, rfl⟩ := hdec hh
  have h1 : c₁ * (r₂ * c₂) = r₂ * c₂ * c₁ := comm_B_TE S hc₁ hh
  have h2 : c₂ * r₁ = r₁ * c₂ := comm_B_TE S hc₂ (R_le_TE S hr₁)
  have e : r₁ * c₁ * (r₂ * c₂) * (r₁ * c₁)⁻¹ * (r₂ * c₂)⁻¹ = r₁ * r₂ * r₁⁻¹ * r₂⁻¹ := by
    calc r₁ * c₁ * (r₂ * c₂) * (r₁ * c₁)⁻¹ * (r₂ * c₂)⁻¹
        = r₁ * (c₁ * (r₂ * c₂)) * c₁⁻¹ * r₁⁻¹ * c₂⁻¹ * r₂⁻¹ := by group
      _ = r₁ * r₂ * (c₂ * r₁⁻¹) * c₂⁻¹ * r₂⁻¹ := by rw [h1]; group
      _ = r₁ * r₂ * r₁⁻¹ * r₂⁻¹ := by
          have h3 : c₂ * r₁⁻¹ = r₁⁻¹ * c₂ := by
            calc c₂ * r₁⁻¹ = r₁⁻¹ * (r₁ * c₂) * r₁⁻¹ := by group
              _ = r₁⁻¹ * (c₂ * r₁) * r₁⁻¹ := by rw [h2]
              _ = r₁⁻¹ * c₂ := by group
          rw [h3]
          group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hr₁ hr₂) (inv_mem hr₁)) (inv_mem hr₂)

theorem eq_T_of_le {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hTQ : A.T ≤ Q)
    (hQC : Q ≤ centralizer ({t} : Set X)) : Q = A.T := by
  have h1 := card_T_eq_of_le (A := A) hTQ hQC
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have h2 : (Nat.card Q).factorization 2 = n := by
    rw [hn, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  refine (eq_of_le_of_card_ge hTQ ?_).symm
  rw [h1, h2, hn]

theorem k_ne_t : S.k ≠ t := by
  intro h
  have := ψ_k S
  rw [h, ψX_t] at this
  exact absurd this.symm (by decide)

theorem not_conj_k_tk {g : X} (hgC : g ∈ centralizer ({t} : Set X)) :
    g * S.k * g⁻¹ ≠ t * S.k := by
  intro hgk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({t} : Set X) with hH
  set V : Subgroup X := zpowers t ⊔ zpowers S.k with hV
  set M : Subgroup X := H ⊓ normalizer (V : Set X) with hM
  set Ck : Subgroup X := H ⊓ centralizer ({S.k} : Set X) with hCk
  have hkC : S.k ∈ H := A.T_le_centralizer (k_mem_T S)
  have hct : ∀ {c : X}, c ∈ H → c * t * c⁻¹ = t := fun hc => by
    rw [mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have hVmem : ∀ v ∈ V, v = 1 ∨ v = t ∨ v = S.k ∨ v = t * S.k := by
    intro v hv
    obtain ⟨e, he, hve⟩ := exists_pow_mem_of_mem_sup (k_sq S)
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (k_comm_t S).symm)) hv
    have hv' : v = v * S.k ^ e * S.k ^ e := by
      rw [mul_assoc, ← pow_add, ← two_mul, pow_mul, k_sq S, one_pow, mul_one]
    rcases eq_one_or_eq_of_mem_zpowers (t_sq' (A := A)) hve with h' | h' <;> rw [h'] at hv' <;>
      rcases pow_lt_two_eq (g := S.k) he with h | h <;> rw [h] at hv'
    · left; rw [hv', one_mul]
    · right; right; left; rw [hv', one_mul]
    · right; left; rw [hv', mul_one]
    · right; right; right; exact hv'
  have hkt : t * S.k ≠ S.k := fun h => t_ne_one' (A := A) (by
    calc t = t * S.k * S.k⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  have hMk : ∀ h ∈ M, h * S.k * h⁻¹ = S.k ∨ h * S.k * h⁻¹ = t * S.k := by
    intro h hh
    obtain ⟨hhH, hhN⟩ := mem_inf.mp hh
    have hv : h * S.k * h⁻¹ ∈ V := (mem_normalizer_iff.mp hhN _).mp (mem_sup_right (mem_zpowers _))
    rcases hVmem _ hv with h1 | h1 | h1 | h1
    · exfalso
      apply (k_ne_t S)
      have : S.k = 1 := by
        calc S.k = h⁻¹ * (h * S.k * h⁻¹) * h := by group
          _ = 1 := by rw [h1]; group
      exact absurd this (by
        intro h0; have := ψ_k S; rw [h0, ψX_one] at this; exact absurd this.symm (by decide))
    · exfalso
      apply k_ne_t S
      calc S.k = h⁻¹ * (h * S.k * h⁻¹) * h := by group
        _ = h⁻¹ * t * h := by rw [h1]
        _ = t := by
          have := hct (inv_mem hhH)
          rwa [inv_inv] at this
    · exact Or.inl h1
    · exact Or.inr h1
  have hNV : ∀ {h : X}, h ∈ H → (h * S.k * h⁻¹ = S.k ∨ h * S.k * h⁻¹ = t * S.k) →
      h ∈ normalizer (V : Set X) := by
    intro h hh hk
    refine mem_normalizer_of_conj_mem fun v hv => ?_
    have hle : V.map (MulAut.conj h).toMonoidHom ≤ V := by
      rw [hV, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hct hh]
      refine sup_le le_sup_left ?_
      rw [zpowers_le]
      rcases hk with h1 | h1 <;> rw [h1]
      · exact mem_sup_right (mem_zpowers _)
      · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
    exact hle ⟨v, hv, rfl⟩
  have hCkM : Ck ≤ M := fun h hh => by
    obtain ⟨hhH, hhk⟩ := mem_inf.mp hh
    refine mem_inf.mpr ⟨hhH, hNV hhH (Or.inl ?_)⟩
    rw [mem_centralizer_singleton_iff.mp hhk, mul_inv_cancel_right]
  have hgM : g ∈ M := mem_inf.mpr ⟨hgC, hNV hgC (Or.inr hgk)⟩
  have hMCk : M ⊓ centralizer ({S.k} : Set X) = Ck := by
    apply le_antisymm
    · exact le_inf ((inf_le_left).trans inf_le_left) inf_le_right
    · exact le_inf hCkM inf_le_right
  have horb : {y | ∃ h ∈ M, h * S.k * h⁻¹ = y} = ({S.k, t * S.k} : Set X) := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      rcases hMk h hh with h1 | h1 <;> simp [h1]
    · intro hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨1, one_mem _, by group⟩
      · exact ⟨g, hgM, hgk⟩
  have hidx1 : Ck.relIndex M = 2 := by
    rw [← hMCk, relIndex_inf_centralizer_eq_ncard, horb, Set.ncard_pair hkt.symm]
  have hidx2 : Ck.relIndex H ≡ 2 [MOD 4] := by
    rw [hCk, relIndex_inf_centralizer_eq_ncard]
    exact S.card_conj_k
  have hMH : M ≤ H := inf_le_left
  have hmul := relIndex_mul_relIndex Ck M H hCkM hMH
  rw [hidx1] at hmul
  have hodd : ¬ 2 ∣ M.relIndex H := by
    rintro ⟨m, hm⟩
    rw [hm] at hmul
    have := hidx2
    rw [← hmul] at this
    have h4 : 2 * (2 * m) = 4 * m := by ring
    rw [h4] at this
    exact absurd (Nat.ModEq.trans this.symm (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 4 m)))
      (by decide)
  have hMcard : (Nat.card M).factorization 2 = (Nat.card H).factorization 2 := by
    have h1 := relIndex_mul_card M H
    rw [inf_of_le_left hMH] at h1
    have hpos1 : M.relIndex H ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h1
      exact Nat.card_pos.ne' h1.symm
    rw [← h1, Nat.factorization_mul hpos1 Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd, zero_add]
  obtain ⟨P⟩ : Nonempty (Sylow 2 M) := inferInstance
  set Pm : Subgroup X := (P : Subgroup M).map M.subtype with hPm
  have hPmM : Pm ≤ M := map_subtype_le _
  have hPcard : Nat.card Pm = 2 ^ (Nat.card H).factorization 2 := by
    rw [hPm, card_map_of_injective (subtype_injective _), Sylow.card_eq_multiplicity, hMcard]
  obtain ⟨c, hcH, hcT⟩ := exists_conj_eq_of_card_eq (A.T_le_centralizer) (hPmM.trans hMH)
    (card_T_eq_two_pow (A := A)) hPcard
  set k' := c⁻¹ * S.k * c with hk'
  have hk'C : k' ∈ H := mul_mem (mul_mem (inv_mem hcH) hkC) hcH
  have hTk' : ∀ h ∈ A.T, h * k' * h⁻¹ = k' ∨ h * k' * h⁻¹ = t * k' := by
    intro h hh
    have hm : c * h * c⁻¹ ∈ M := hPmM (by rw [← hcT]; exact ⟨h, hh, rfl⟩)
    have hct' : c⁻¹ * t * c = t := by
      have := hct (inv_mem hcH)
      rwa [inv_inv] at this
    rcases hMk _ hm with h1 | h1
    · left
      calc h * k' * h⁻¹ = c⁻¹ * (c * h * c⁻¹ * S.k * (c * h * c⁻¹)⁻¹) * c := by rw [hk']; group
        _ = k' := by rw [h1]
    · right
      calc h * k' * h⁻¹ = c⁻¹ * (c * h * c⁻¹ * S.k * (c * h * c⁻¹)⁻¹) * c := by rw [hk']; group
        _ = c⁻¹ * t * c * k' := by rw [h1, hk']; group
        _ = t * k' := by rw [hct']
  have hk'2 : k' ^ 2 = 1 := by
    calc k' ^ 2 = c⁻¹ * S.k ^ 2 * c := by rw [hk', pow_two, pow_two]; group
      _ = 1 := by rw [k_sq S]; group
  have hk't : k' * t = t * k' := mem_centralizer_singleton_iff.mp hk'C
  have hk'T : k' ∈ A.T := by
    set V' : Subgroup X := zpowers k' ⊔ zpowers t with hV'
    have hV'p : IsPGroup 2 V' := by
      refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_sq hk'2)
        (isPGroup_zpowers_of_sq (t_sq' (A := A))) ?_
      rw [zpowers_le]
      exact centralizer_le_normalizer _ (by
        rw [mem_centralizer_iff]
        intro a ha
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
        exact (Commute.zpow_left hk't.symm n).eq)
    have hTN : A.T ≤ normalizer (V' : Set X) := by
      intro h hh
      refine mem_normalizer_of_conj_mem fun v hv => ?_
      have hle : V'.map (MulAut.conj h).toMonoidHom ≤ V' := by
        rw [hV', Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hct (A.T_le_centralizer hh)]
        refine sup_le ?_ le_sup_right
        rw [zpowers_le]
        rcases hTk' h hh with h1 | h1 <;> rw [h1]
        · exact mem_sup_left (mem_zpowers _)
        · exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (mem_zpowers _))
      exact hle ⟨v, hv, rfl⟩
    have hp := IsPGroup.to_sup_of_normal_right' A.isPGroup_T hV'p hTN
    have hle : A.T ⊔ V' ≤ H := sup_le A.T_le_centralizer (sup_le (zpowers_le.mpr hk'C)
      (zpowers_le.mpr (t_mem_C)))
    have heq := eq_T_of_le hp le_sup_left hle
    rw [← heq]
    exact mem_sup_right (mem_sup_left (mem_zpowers _))
  have hcls : cls t k' = cls t S.k := cls_eq_of_mem ⟨c⁻¹, inv_mem hcH, by rw [hk', inv_inv]⟩
  obtain ⟨h, hh, hhk⟩ : ∃ h ∈ A.T, h * k' * h⁻¹ = t * k' := by
    by_contra hne
    push Not at hne
    have hTC : A.T ≤ centralizer ({k'} : Set X) := by
      intro h hh
      rw [mem_centralizer_singleton_iff]
      rcases hTk' h hh with h1 | h1
      · calc h * k' = h * k' * h⁻¹ * h := by group
          _ = k' * h := by rw [h1]
      · exact absurd h1 (hne h hh)
    have hodd' := odd_ncard_cls hTC
    rw [hcls] at hodd'
    have h2 := S.card_conj_k
    obtain ⟨m, hm⟩ := hodd'
    change (cls t S.k).ncard ≡ 2 [MOD 4] at h2
    rw [hm] at h2
    have : (2 * m + 1) % 2 = 2 % 2 := by
      have := Nat.ModEq.of_mul_left 2 (show (2 * m + 1) ≡ 2 [MOD 2 * 2] from h2)
      exact this
    omega
  obtain ⟨u, b, hub⟩ := ψX_mem_H8' hk'T
  have hτ : tauX A k' = tauX A S.k := by
    have := tauX_conj (A := A) (inv_mem hcH) hkC
    rwa [inv_inv] at this
  rw [tauX_of_mem_T hk'T hub.symm, tauX_of_mem_T (k_mem_T S) (ψ_k S)] at hτ
  have hbits := congrArg Multiplicative.toAdd hτ
  simp only [toAdd_ofAdd, Prod.mk.injEq] at hbits
  obtain ⟨hb, hu⟩ := hbits
  have hb0 : dbit8 b = 0 := by rw [hb]; rfl
  have hu1 : fbit8 u = 1 := by rw [hu]; rfl
  obtain ⟨u', b', hub'⟩ := ψX_mem_H8' hh
  rcases dbit8_eq b' with hb' | hb'
  · have hhE : h ∈ S.TE := (mem_TE_iff S).mpr ⟨hh, by rw [← hub']; exact mem_PTE.mpr hb'⟩
    have hk'E : k' ∈ S.TE := (mem_TE_iff S).mpr ⟨hk'T, by rw [← hub]; exact mem_PTE.mpr hb0⟩
    have hR := comm_mem_R_of_mem_TE S hhE hk'E
    rw [hhk, mul_inv_cancel_right] at hR
    exact A.config.not_mem hR.2
  · have h2 : aff8 u b ^ 2 = 1 := by rw [hub, ← ψX_pow hk'T, hk'2, ψX_one]
    apply not_comm_field_odd u b u' b' hb0 hu1 hb' h2
    have hc := congrArg (ψX A) hhk
    rw [ψX_conj hh hk'T, ψX_mul A.t_mem_T hk'T, ψX_t, one_mul, ← hub, ← hub'] at hc
    calc aff8 u' b' * aff8 u b = aff8 u' b' * aff8 u b * (aff8 u' b')⁻¹ * aff8 u' b' := by group
      _ = aff8 u b * aff8 u' b' := by rw [hc]

end CFSG.ComponentClassification.HSFLit.KD46
