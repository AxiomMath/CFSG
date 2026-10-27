module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3NSBig

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5.Kc3J
  CFSG.QuasithinUnique.A5.Kc3NSC

section Hyp

variable {K : Type} [Group K]

@[expose] def IsTransvec (E : Subgroup K) (n : K) : Prop :=
  ∃ u ∈ E, n * u ≠ u * n ∧ ∀ x ∈ E, n * x = x * n ∨ n * (u * x) = (u * x) * n

@[expose] def LocHypA (E : Subgroup K) : Prop :=
  Subgroup.centralizer (E : Set K) ≤ E ∧ 1920 ∣ Nat.card (Subgroup.normalizer (E : Set K)) ∧
    ∀ n ∈ Subgroup.normalizer (E : Set K), ¬ IsTransvec E n

theorem comm_of_beta {E : Subgroup K} (β : ↥E ≃* Multiplicative ↥(evenWeight 5)) (x y : ↥E) :
    x * y = y * x := β.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)

end Hyp

section Transport

variable {K K' : Type} [Group K] [Group K'] (φ : K ≃* K')

theorem mem_normalizer_map {E : Subgroup K} (n : K) :
    φ n ∈ Subgroup.normalizer ((E.map φ.toMonoidHom : Subgroup K') : Set K') ↔
      n ∈ Subgroup.normalizer (E : Set K) := by
  rw [← Subgroup.map_equiv_normalizer_eq E φ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem card_normalizer_map (E : Subgroup K) :
    Nat.card (Subgroup.normalizer ((E.map φ.toMonoidHom : Subgroup K') : Set K')) =
      Nat.card (Subgroup.normalizer (E : Set K)) := by
  rw [← Subgroup.map_equiv_normalizer_eq E φ]
  exact Subgroup.card_map_of_injective φ.injective

theorem IsTransvec.map {E : Subgroup K} {n : K} (h : IsTransvec E n) :
    IsTransvec (E.map φ.toMonoidHom) (φ n) := by
  obtain ⟨u, hu, hne, hx⟩ := h
  refine ⟨φ u, ⟨u, hu, rfl⟩, ?_, ?_⟩
  · intro h
    apply hne
    apply φ.injective
    simpa [map_mul] using h
  · rintro _ ⟨x, hxE, rfl⟩
    show φ n * φ x = φ x * φ n ∨ φ n * (φ u * φ x) = φ u * φ x * φ n
    rcases hx x hxE with h | h
    · left
      rw [← map_mul, ← map_mul, h]
    · right
      rw [← map_mul, ← map_mul, ← map_mul, h]

theorem IsTransvec.of_map {E : Subgroup K} {n : K} (h : IsTransvec (E.map φ.toMonoidHom) (φ n)) :
    IsTransvec E n := by
  obtain ⟨u', hu', hne, hx⟩ := h
  obtain ⟨u, hu, rfl⟩ := hu'
  refine ⟨u, hu, ?_, ?_⟩
  · intro h
    apply hne
    show φ n * φ u = φ u * φ n
    rw [← map_mul, ← map_mul, h]
  · intro x hxE
    rcases hx (φ x) ⟨x, hxE, rfl⟩ with h | h
    · left
      apply φ.injective
      simpa [map_mul] using h
    · right
      apply φ.injective
      simpa [map_mul] using h

theorem LocHypA.map {E : Subgroup K} (h : LocHypA E) : LocHypA (E.map φ.toMonoidHom) := by
  obtain ⟨hC, h1920, hnt⟩ := h
  refine ⟨?_, ?_, ?_⟩
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
    exact h1920
  · intro n' hn'
    obtain ⟨n, rfl⟩ := φ.surjective n'
    exact fun h => hnt n ((mem_normalizer_map φ n).1 hn') (IsTransvec.of_map φ h)

end Transport

section LemmaA

variable {K : Type} [Group K] {E : Subgroup K}
  (β : ↥E ≃* Multiplicative ↥(evenWeight 5))

@[expose] noncomputable def psi : ↥(Subgroup.normalizer (E : Set K)) →* MulAut Dm :=
  rhoY E (Subgroup.normalizer (E : Set K)) le_rfl β

theorem psi_spec (n : ↥(Subgroup.normalizer (E : Set K))) (x : Dm) :
    ((β.symm (psi β n x) : ↥E) : K) = (n : K) * ((β.symm x : ↥E) : K) * (n : K)⁻¹ :=
  rhoY_spec E _ le_rfl β n x

theorem psi_eq_one_iff (n : ↥(Subgroup.normalizer (E : Set K))) :
    psi β n = 1 ↔ ∀ v ∈ E, (n : K) * v = v * n := by
  constructor
  · intro h v hv
    have h2 : v = (n : K) * v * (n : K)⁻¹ := by
      have := psi_spec β n (β ⟨v, hv⟩)
      rw [h, MulAut.one_apply, MulEquiv.symm_apply_apply] at this
      exact this
    calc (n : K) * v = ((n : K) * v * (n : K)⁻¹) * (n : K) := by group
      _ = v * n := by rw [← h2]
  · intro h
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.one_apply]
    apply β.symm.injective
    apply Subtype.ext
    rw [psi_spec]
    calc (n : K) * ((β.symm x : ↥E) : K) * (n : K)⁻¹ =
        (((β.symm x : ↥E) : K) * n) * (n : K)⁻¹ := by rw [h _ (β.symm x).2]
      _ = ((β.symm x : ↥E) : K) := by group

theorem psi_ker (hC : Subgroup.centralizer (E : Set K) ≤ E) :
    (psi β).ker = E.subgroupOf (Subgroup.normalizer (E : Set K)) := by
  ext n
  rw [MonoidHom.mem_ker, psi_eq_one_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    apply hC
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (h v hv).symm
  · intro hn v hv
    have := comm_of_beta β ⟨(n : K), hn⟩ ⟨v, hv⟩
    exact congrArg Subtype.val this

theorem mem_S5Stab_iff_psi (n : K) :
    n ∈ S5Stab E β ↔ ∃ hn : n ∈ Subgroup.normalizer (E : Set K),
      psi β ⟨n, hn⟩ ∈ (permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range := by
  constructor
  · rintro ⟨hn, σ, hσ⟩
    refine ⟨hn, σ, ?_⟩
    refine MulEquiv.ext fun x => ?_
    have hw := psi_spec β ⟨n, hn⟩ x
    have h := hσ (β.symm x) (β.symm (psi β ⟨n, hn⟩ x)) (by simpa using hw)
    simp only [MulEquiv.apply_symm_apply] at h
    rw [permHom_apply, ← h, ofAdd_toAdd]
  · rintro ⟨hn, σ, hσ⟩
    refine ⟨hn, σ, fun v w hw => ?_⟩
    have h1 := psi_spec β ⟨n, hn⟩ (β v)
    rw [MulEquiv.symm_apply_apply] at h1
    have h2 : β.symm (psi β ⟨n, hn⟩ (β v)) = w := Subtype.ext (by rw [h1]; exact hw.symm)
    have h3 : psi β ⟨n, hn⟩ (β v) = β w := by rw [← h2]; simp
    rw [← h3, ← hσ, permHom_apply, toAdd_ofAdd]

theorem psi_eq_permHom {l : K} (hlN : l ∈ Subgroup.normalizer (E : Set K))
    {σ : Equiv.Perm (Fin 5)}
    (hl : ∀ v w : ↥E, (w : K) = l * v * l⁻¹ →
      Multiplicative.toAdd (β w) = Delta5.vact σ (Multiplicative.toAdd (β v))) :
    psi β ⟨l, hlN⟩ = permHom σ := by
  refine MulEquiv.ext fun x => ?_
  have hw := psi_spec β ⟨l, hlN⟩ x
  have h' := hl (β.symm x) (β.symm (psi β ⟨l, hlN⟩ x)) (by simpa using hw)
  simp only [MulEquiv.apply_symm_apply] at h'
  rw [permHom_apply, ← h', ofAdd_toAdd]

theorem card_altImg : Nat.card altImg = 60 := by
  unfold altImg
  rw [Subgroup.card_map_of_injective permHom_injective]
  exact Delta5.a5_card

theorem altImg_le_range : altImg ≤ (permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range := by
  rintro _ ⟨σ, -, rfl⟩
  exact ⟨σ, rfl⟩

@[expose] def wu : ↥(evenWeight 5) := ⟨Pi.single 0 1 + Pi.single 2 1, Delta5.pair_mem 0 2⟩

theorem transvec_fix : ∀ w : Fin 5 → ZMod 2, ∑ i, w i = 0 →
    Delta5.pact (Equiv.swap 0 1) w = w ∨
      Delta5.pact (Equiv.swap 0 1) (Pi.single 0 1 + Pi.single 2 1 + w) =
        Pi.single 0 1 + Pi.single 2 1 + w := by
  decide +kernel

theorem transvec_move : Delta5.pact (Equiv.swap 0 1)
    (Pi.single 0 1 + Pi.single 2 1 : Fin 5 → ZMod 2) ≠ Pi.single 0 1 + Pi.single 2 1 := by
  decide +kernel

theorem comm_iff_psi_fix (n : ↥(Subgroup.normalizer (E : Set K))) (x : ↥E) :
    (n : K) * (x : K) = (x : K) * n ↔ psi β n (β x) = β x := by
  have h := psi_spec β n (β x)
  rw [MulEquiv.symm_apply_apply] at h
  constructor
  · intro hc
    have h1 : ((β.symm (psi β n (β x)) : ↥E) : K) = (x : K) := by
      rw [h]
      calc (n : K) * (x : K) * (n : K)⁻¹ = ((x : K) * n) * (n : K)⁻¹ := by rw [hc]
        _ = (x : K) := by group
    have h2 : β.symm (psi β n (β x)) = x := Subtype.ext h1
    have := congrArg β h2
    simpa using this
  · intro hψ
    rw [hψ, MulEquiv.symm_apply_apply] at h
    calc (n : K) * (x : K) = ((n : K) * (x : K) * (n : K)⁻¹) * n := by group
      _ = (x : K) * n := by rw [← h]

theorem vact_eq_iff (σ : Equiv.Perm (Fin 5)) (w : ↥(evenWeight 5)) :
    Delta5.vact σ w = w ↔ Delta5.pact σ w.1 = w.1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem isTransvec_of_psi_swap (n : ↥(Subgroup.normalizer (E : Set K)))
    (hn : psi β n = permHom (Equiv.swap 0 1)) : IsTransvec E (n : K) := by
  set u₀ : ↥E := β.symm (Multiplicative.ofAdd wu) with hu₀
  have hβu : β u₀ = Multiplicative.ofAdd wu := by simp [hu₀]
  have hfix : ∀ x : ↥E, (n : K) * (x : K) = (x : K) * n ↔
      Delta5.vact (Equiv.swap 0 1) (Multiplicative.toAdd (β x)) = Multiplicative.toAdd (β x) := by
    intro x
    rw [comm_iff_psi_fix β n x, hn, permHom_apply]
    constructor
    · intro h
      have := congrArg Multiplicative.toAdd h
      simpa using this
    · intro h
      rw [h]
      simp
  refine ⟨(u₀ : K), u₀.2, ?_, ?_⟩
  · intro h
    have := (hfix u₀).1 h
    rw [hβu, toAdd_ofAdd, vact_eq_iff] at this
    exact transvec_move this
  · intro x hx
    have hsplit := transvec_fix (Multiplicative.toAdd (β ⟨x, hx⟩)).1
      (Multiplicative.toAdd (β ⟨x, hx⟩)).2
    rcases hsplit with h | h
    · left
      exact (hfix ⟨x, hx⟩).2 ((vact_eq_iff _ _).2 h)
    · right
      have hux : (u₀ : K) * x = ((u₀ * ⟨x, hx⟩ : ↥E) : K) := rfl
      rw [hux]
      refine (hfix (u₀ * ⟨x, hx⟩)).2 ?_
      rw [vact_eq_iff, map_mul, hβu, toAdd_mul, toAdd_ofAdd]
      exact h

theorem localAt_of_hypA [Finite K] (hact : Delta5Norm E β) (h : LocHypA E) :
    Subgroup.centralizer (E : Set K) ≤ E ∧
      2 ∣ (S5Stab E β).relIndex (Subgroup.normalizer (E : Set K)) := by
  obtain ⟨hC, h1920, hnt⟩ := h
  refine ⟨hC, ?_⟩
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
  have hA : altImg ≤ (permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range ⊓ (psi β).range := by
    refine le_inf altImg_le_range ?_
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨l, hlN, hl⟩ := hact σ (Equiv.Perm.mem_alternatingGroup.1 hσ)
    exact ⟨⟨l, hlN⟩, psi_eq_permHom β hlN hl⟩
  have hdvd1 : 60 ∣ Nat.card
      ↥((permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range ⊓ (psi β).range) := by
    rw [← card_altImg]
    exact Subgroup.card_dvd_of_le hA
  have hdvd2 : Nat.card
      ↥((permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range ⊓ (psi β).range) ∣ 120 := by
    rw [← card_permHom_range]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h60 : Nat.card
      ↥((permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range ⊓ (psi β).range) = 60 := by
    have hpos : 0 < Nat.card
        ↥((permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range ⊓ (psi β).range) :=
      Nat.pos_of_dvd_of_pos hdvd2 (by norm_num)
    obtain ⟨c, hc⟩ := hdvd1
    have hc2 : c ∣ 2 := by
      rw [hc] at hdvd2
      have : 60 * c ∣ 60 * 2 := hdvd2
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have hcle : c ≤ 2 := Nat.le_of_dvd (by norm_num) hc2
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0, mul_zero] at hc
        omega
      · exact h0
    interval_cases c
    · simpa using hc
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge
        (inf_le_left : (permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range ⊓ (psi β).range ≤
          (permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range)
        (by rw [hc, card_permHom_range])
      have hmem : permHom (Equiv.swap (0 : Fin 5) 1) ∈
          (permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range ⊓ (psi β).range := by
        rw [heq]
        exact ⟨_, rfl⟩
      obtain ⟨n, hn⟩ := hmem.2
      exact hnt (n : K) n.2 (isTransvec_of_psi_swap β n hn)
  have hker : Nat.card (psi β).ker = 16 := by
    rw [psi_ker β hC,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := E))).toEquiv,
      Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.toAdd]
    exact CFSG.QuasithinUnique.AppC.card_evenWeight
  have hNcard := Subgroup.card_ker_mul_card_range (psi β)
  have hrel := Subgroup.relIndex_mul_card
    (permHom : Equiv.Perm (Fin 5) →* MulAut Dm).range (psi β).range
  rw [h60] at hrel
  rw [hker] at hNcard
  have h1920' : 1920 ∣ Nat.card ↥(Subgroup.normalizer (E : Set K)) := h1920
  rw [hidx]
  omega

end LemmaA

end CFSG.QuasithinUnique.A5
