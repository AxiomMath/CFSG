module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Loc
public import Certificates.Certificate17029

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5.Kc3J
  CFSG.QuasithinUnique.A5.Kc3NSC

section Hyp

variable {K : Type} [Group K]

@[expose] def LocHypD (E : Subgroup K) : Prop :=
  Subgroup.centralizer (E : Set K) ≤ E ∧ 3840 ∣ Nat.card (Subgroup.normalizer (E : Set K))

@[expose] def LocHypV (E : Subgroup K) : Prop :=
  ∃ ω ∈ Subgroup.normalizer (E : Set K), (∃ v ∈ E, ω * v ≠ v * ω) ∧
    (∀ v ∈ E, ω ^ 3 * v = v * ω ^ 3) ∧ ∀ n ∈ Subgroup.normalizer (E : Set K),
      (∀ v ∈ E, n * ω * v * ω⁻¹ * n⁻¹ = ω * n * v * n⁻¹ * ω⁻¹) ∨
      (∀ v ∈ E, n * ω * v * ω⁻¹ * n⁻¹ = ω * ω * n * v * n⁻¹ * ω⁻¹ * ω⁻¹)

end Hyp

section Transport

variable {K K' : Type} [Group K] [Group K'] (φ : K ≃* K')

theorem LocHypD.map {E : Subgroup K} (h : LocHypD E) : LocHypD (E.map φ.toMonoidHom) := by
  obtain ⟨hC, h3840⟩ := h
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := φ.surjective y
    have hx : x ∈ Subgroup.centralizer (E : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have := Subgroup.mem_centralizer_iff.1 hy (φ e) ⟨e, he, rfl⟩
      apply φ.injective
      simpa [map_mul] using this
    exact ⟨x, hC hx, rfl⟩
  · rw [card_normalizer_map φ E]
    exact h3840

theorem LocHypV.map {E : Subgroup K} (h : LocHypV E) : LocHypV (E.map φ.toMonoidHom) := by
  obtain ⟨ω, hωN, ⟨v, hv, hne⟩, h3, hnorm⟩ := h
  refine ⟨φ ω, (mem_normalizer_map φ ω).2 hωN, ⟨φ v, ⟨v, hv, rfl⟩, ?_⟩, ?_, ?_⟩
  · intro h
    apply hne
    apply φ.injective
    simpa [map_mul] using h
  · rintro _ ⟨v, hv, rfl⟩
    show φ ω ^ 3 * φ v = φ v * φ ω ^ 3
    rw [← map_pow, ← map_mul, ← map_mul, h3 v hv]
  · intro n' hn'
    obtain ⟨n, rfl⟩ := φ.surjective n'
    rcases hnorm n ((mem_normalizer_map φ n).1 hn') with h1 | h1
    · left
      rintro _ ⟨v, hv, rfl⟩
      have := congrArg φ (h1 v hv)
      simpa [map_mul, map_inv] using this
    · right
      rintro _ ⟨v, hv, rfl⟩
      have := congrArg φ (h1 v hv)
      simpa [map_mul, map_inv] using this

end Transport

section Lemmas

variable {K : Type} [Group K] {E : Subgroup K}
  (β : ↥E ≃* Multiplicative ↥(evenWeight 5))

theorem localAt_of_hypD [Finite K] (hD : LocHypD E) :
    2 ∣ (S5Stab E β).relIndex (Subgroup.normalizer (E : Set K)) := by
  obtain ⟨hC, h3840⟩ := hD
  set N := Subgroup.normalizer (E : Set K) with hN
  have hS : (S5Stab E β).subgroupOf N =
      (permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range.comap (psi β) := by
    ext n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, mem_S5Stab_iff_psi]
    constructor
    · rintro ⟨hn, h⟩
      exact h
    · intro h
      exact ⟨n.2, h⟩
  have hidx : (S5Stab E β).relIndex N =
      (permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range.relIndex (psi β).range := by
    rw [Subgroup.relIndex, hS, Subgroup.index_comap]
  have hdvd : Nat.card
      ↥((permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range ⊓ (psi β).range) ∣ 120 := by
    rw [← card_permHom_range]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hker : Nat.card (psi β).ker = 16 := by
    rw [psi_ker β hC,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := E))).toEquiv,
      Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.toAdd]
    exact CFSG.QuasithinUnique.AppC.card_evenWeight
  have hNcard := Subgroup.card_ker_mul_card_range (psi β)
  have hrel := Subgroup.relIndex_mul_card
    (permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range (psi β).range
  rw [hker] at hNcard
  rw [hidx]
  obtain ⟨c, hc⟩ := hdvd
  have h3840' : 3840 ∣ Nat.card ↥(Subgroup.normalizer (E : Set K)) := h3840
  obtain ⟨d, hd⟩ := h3840'
  set r := (permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range.relIndex (psi β).range with hr
  set h := Nat.card ↥((permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range ⊓ (psi β).range) with hh
  have e1 : r * h = 240 * d := by omega
  have e2 : 120 * r = 240 * (d * c) := by
    calc 120 * r = (h * c) * r := by rw [hc]
      _ = (r * h) * c := by ring
      _ = 240 * d * c := by rw [e1]
      _ = 240 * (d * c) := by ring
  omega

theorem psi_comm_of (g h : ↥(Subgroup.normalizer (E : Set K)))
    (H : ∀ v ∈ E, (g : K) * h * v * (h : K)⁻¹ * (g : K)⁻¹ =
      (h : K) * g * v * (g : K)⁻¹ * (h : K)⁻¹) : psi β g * psi β h = psi β h * psi β g := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply]
  apply β.symm.injective
  apply Subtype.ext
  rw [psi_spec, psi_spec, psi_spec, psi_spec]
  have := H _ (β.symm x).2
  calc (g : K) * ((h : K) * ((β.symm x : ↥E) : K) * (h : K)⁻¹) * (g : K)⁻¹ =
      (g : K) * h * ((β.symm x : ↥E) : K) * (h : K)⁻¹ * (g : K)⁻¹ := by group
    _ = (h : K) * g * ((β.symm x : ↥E) : K) * (g : K)⁻¹ * (h : K)⁻¹ := this
    _ = (h : K) * ((g : K) * ((β.symm x : ↥E) : K) * (g : K)⁻¹) * (h : K)⁻¹ := by group

theorem psi_comm2_of (g h : ↥(Subgroup.normalizer (E : Set K)))
    (H : ∀ v ∈ E, (g : K) * h * v * (h : K)⁻¹ * (g : K)⁻¹ =
      (h : K) * h * g * v * (g : K)⁻¹ * (h : K)⁻¹ * (h : K)⁻¹) :
    psi β g * psi β h = psi β h * psi β h * psi β g := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply]
  apply β.symm.injective
  apply Subtype.ext
  rw [psi_spec, psi_spec, psi_spec, psi_spec, psi_spec]
  have := H _ (β.symm x).2
  calc (g : K) * ((h : K) * ((β.symm x : ↥E) : K) * (h : K)⁻¹) * (g : K)⁻¹ =
      (g : K) * h * ((β.symm x : ↥E) : K) * (h : K)⁻¹ * (g : K)⁻¹ := by group
    _ = (h : K) * h * g * ((β.symm x : ↥E) : K) * (g : K)⁻¹ * (h : K)⁻¹ * (h : K)⁻¹ := this
    _ = (h : K) * ((h : K) * ((g : K) * ((β.symm x : ↥E) : K) * (g : K)⁻¹) * (h : K)⁻¹) *
        (h : K)⁻¹ := by group

theorem comm_of_conj_pm {G : Type*} [Group G] {z p : G} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    {m : ℕ} (hm : Odd m) (hpm : p ^ m = 1) (h : p * z * p⁻¹ = z ∨ p * z * p⁻¹ = z⁻¹) :
    p * z = z * p := by
  rcases h with h | h
  · calc p * z = (p * z * p⁻¹) * p := by group
      _ = z * p := by rw [h]
  · exfalso
    obtain ⟨k, rfl⟩ := hm
    have h2 : p ^ 2 * z * (p ^ 2)⁻¹ = z := by
      have h' : p * z⁻¹ * p⁻¹ = z := by
        have := congrArg (fun x => x⁻¹) h
        simpa [mul_assoc] using this
      calc p ^ 2 * z * (p ^ 2)⁻¹ = p * (p * z * p⁻¹) * p⁻¹ := by
            rw [pow_two, mul_inv_rev]; simp only [mul_assoc]
        _ = z := by rw [h]; exact h'
    have hc : Commute z (p ^ 2) := by
      have : p ^ 2 * z = z * p ^ 2 := by
        calc p ^ 2 * z = (p ^ 2 * z * (p ^ 2)⁻¹) * p ^ 2 := by group
          _ = z * p ^ 2 := by rw [h2]
      exact this.symm
    have hp : p = (p ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      have : p ^ (2 * (k + 1)) = p ^ (2 * k + 1) * p := by
        rw [← pow_succ]; congr 1
      rw [this, hpm, one_mul]
    have hcp : Commute z p := by
      rw [hp]
      exact hc.pow_right (k + 1)
    have h3 : p * z * p⁻¹ = z := by
      have := hcp.eq
      calc p * z * p⁻¹ = (z * p) * p⁻¹ := by rw [← this]
        _ = z := by group
    rw [h3] at h
    have hz2 : z ^ 2 = 1 := by
      have : z * z = 1 := by
        calc z * z = z * z⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel z
      simpa [pow_two] using this
    apply hz1
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2]; simp

theorem a0_pow : Delta5.a0 ^ 5 = 1 :=
  Certificates.certificate17029.1

theorem b0_pow : Delta5.b0 ^ 3 = 1 :=
  Certificates.certificate17029.2

theorem not_delta5Norm_of_hypV
    (hact : Delta5Norm E β) (h : LocHypV E) : False := by
  obtain ⟨ω, hωN, ⟨v₀, hv₀, hne⟩, hω3, hnorm⟩ := h
  set z : MulAut Dm := psi β ⟨ω, hωN⟩ with hz
  have hz1 : z ≠ 1 := fun h1 => hne ((psi_eq_one_iff β ⟨ω, hωN⟩).1 h1 v₀ hv₀)
  have hz3 : z ^ 3 = 1 := by
    have h1 : psi β (⟨ω, hωN⟩ ^ 3) = 1 := by
      rw [psi_eq_one_iff]
      intro v hv
      simpa using hω3 v hv
    rw [map_pow] at h1
    exact h1
  have hzinv : z⁻¹ = z * z := by
    apply inv_eq_of_mul_eq_one_right
    have : z * (z * z) = z ^ 3 := (pow_three z).symm
    rw [this, hz3]
  have hconj : ∀ n : ↥(Subgroup.normalizer (E : Set K)),
      psi β n * z * (psi β n)⁻¹ = z ∨ psi β n * z * (psi β n)⁻¹ = z⁻¹ := by
    intro n
    rcases hnorm n n.2 with h1 | h1
    · left
      have h3 : psi β n * z = z * psi β n := psi_comm_of β n ⟨ω, hωN⟩ h1
      rw [h3, mul_assoc, mul_inv_cancel, mul_one]
    · right
      have h3 : psi β n * z = z * z * psi β n := psi_comm2_of β n ⟨ω, hωN⟩ h1
      rw [h3, mul_assoc, mul_inv_cancel, mul_one, hzinv]
  have ha := Equiv.Perm.mem_alternatingGroup.1 Delta5.a0_alt
  have hb := Equiv.Perm.mem_alternatingGroup.1 Delta5.b0_alt
  obtain ⟨la, hlaN, hla⟩ := hact _ ha
  obtain ⟨lb, hlbN, hlb⟩ := hact _ hb
  have hψa := psi_eq_permHom β hlaN hla
  have hψb := psi_eq_permHom β hlbN hlb
  have hpa : permHom Delta5.a0 * z = z * permHom Delta5.a0 := by
    refine comm_of_conj_pm hz3 hz1 (m := 5) (by decide) ?_ ?_
    · rw [← map_pow, a0_pow, map_one]
    · rw [← hψa]
      exact hconj _
  have hpb : permHom Delta5.b0 * z = z * permHom Delta5.b0 := by
    refine comm_of_conj_pm hz3 hz1 (m := 3) (by decide) ?_ ?_
    · rw [← map_pow, b0_pow, map_one]
    · rw [← hψb]
      exact hconj _
  set f : ↥(alternatingGroup (Fin 5)) →* MulAut Dm :=
    permHom.comp (alternatingGroup (Fin 5)).subtype with hf
  set H : Subgroup ↥(alternatingGroup (Fin 5)) :=
    (Subgroup.centralizer ({z} : Set (MulAut Dm))).comap f with hH
  have ha' : Delta5.a0' ∈ H := by
    rw [hH, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hpa.symm
  have hb' : Delta5.b0' ∈ H := by
    rw [hH, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hpb.symm
  have htop : H = ⊤ := by
    rw [eq_top_iff, ← Delta5.closure_a5, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact ha'
    · rw [Set.mem_singleton_iff.1 hg]
      exact hb'
  apply hz1
  apply altImg_cent z
  rintro _ ⟨σ, hσ, rfl⟩
  have hσH : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin 5))) ∈ H := by rw [htop]; trivial
  rw [hH, Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hσH
  exact hσH z rfl

end Lemmas

section Class2

@[expose] def LocClass2 (K : Type) [Group K] : Prop :=
  ∀ (E : Subgroup K) (β : ↥E ≃* Multiplicative ↥(evenWeight 5)), Delta5Norm E β →
    ∃ (E₀ : Subgroup K) (g : K), (LocHypA E₀ ∨ LocHypD E₀ ∨ LocHypV E₀) ∧
      E = E₀.map (MulAut.conj g).toMonoidHom

theorem kc3LocalData_of_locClass2
    {K : Type} [Group K] [Finite K] (h : LocClass2 K) :
    Kc3LocalData K := by
  intro E β hact
  obtain ⟨E₀, g, hE₀, rfl⟩ := h E β hact
  rcases hE₀ with h1 | h2 | h3
  · exact localAt_of_hypA β hact (h1.map (MulAut.conj g))
  · exact ⟨(h2.map (MulAut.conj g)).1, localAt_of_hypD β (h2.map (MulAut.conj g))⟩
  · exact (not_delta5Norm_of_hypV β hact (h3.map (MulAut.conj g))).elim

theorem Delta5Norm.map {K K' : Type} [Group K] [Group K'] (φ : K ≃* K') {E : Subgroup K}
    {β : ↥E ≃* Multiplicative ↥(evenWeight 5)} (h : Delta5Norm E β) :
    Delta5Norm (E.map φ.toMonoidHom) ((φ.subgroupMap E).symm.trans β) := by
  intro σ hσ
  obtain ⟨l, hl, hact⟩ := h σ hσ
  refine ⟨φ l, (mem_normalizer_map φ l).2 hl, ?_⟩
  intro v' w' hw'
  set v : ↥E := (φ.subgroupMap E).symm v' with hv
  set w : ↥E := (φ.subgroupMap E).symm w' with hw
  have hvv : (v' : K') = φ (v : K) := by
    have := congrArg Subtype.val ((φ.subgroupMap E).apply_symm_apply v')
    simpa using this.symm
  have hww : (w' : K') = φ (w : K) := by
    have := congrArg Subtype.val ((φ.subgroupMap E).apply_symm_apply w')
    simpa using this.symm
  have h1 : (w : K) = l * (v : K) * l⁻¹ := by
    apply φ.injective
    rw [← hww, hw', hvv, map_mul, map_mul, map_inv]
  exact hact v w h1

theorem LocClass2.of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : LocClass2 Y) :
    LocClass2 X := by
  intro E β hact
  obtain ⟨E₀, g, hE₀, hEE⟩ := h (E.map e.toMonoidHom) ((e.subgroupMap E).symm.trans β)
    (Delta5Norm.map e hact)
  refine ⟨E₀.map e.symm.toMonoidHom, e.symm g, ?_, ?_⟩
  · rcases hE₀ with h1 | h2 | h3
    · exact Or.inl (h1.map e.symm)
    · exact Or.inr (Or.inl (h2.map e.symm))
    · exact Or.inr (Or.inr (h3.map e.symm))
  · have h1 : E = (E.map e.toMonoidHom).map e.symm.toMonoidHom := by
      rw [Subgroup.map_map]
      have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by
        ext x; simp
      rw [this, Subgroup.map_id]
    rw [h1, hEE, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]

end Class2

end CFSG.QuasithinUnique.A5
