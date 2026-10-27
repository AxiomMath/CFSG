module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FoursInputs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open Subgroup CFSG CFSG.EvenSporadicStandard.HSStd CFSG.Blueprint

@[expose] def CatE16 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Catalog K → IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ τ : MulAut K, τ * τ = 1 → τ ∉ (MulAut.conj : K →* MulAut K).range →
    Nonempty (↥(autCentralizer τ) ≃* alternatingGroup (Fin 5)) →
    ∀ κ ∈ autCentralizer τ, orderOf κ = 2 → Nat.card (centralizer ({κ} : Set K)) ≤ 16 →
      Nat.card (centralizer ({κ} : Set K)) = 16 ∧
        ∀ a ∈ centralizer ({κ} : Set K), ∀ b ∈ centralizer ({κ} : Set K), a * b = b * a ∧ a * a = 1

section Generic

variable {X : Type*} [Group X]

theorem aut_inv_of_fixed_point_free (φ : MulAut X) (N : Subgroup X) [Finite N]
    (hN : ∀ n ∈ N, φ n ∈ N) (hφ : φ * φ = 1)
    (hfix : ∀ n ∈ N, φ n = n → n = 1) : ∀ n ∈ N, φ n = n⁻¹ := by
  have hφφ : ∀ x : X, φ (φ x) = x := fun x => by
    have := congrArg (fun ψ : MulAut X => ψ x) hφ
    simpa using this
  let f : N → N := fun x => ⟨(x : X)⁻¹ * φ x, N.mul_mem (N.inv_mem x.2) (hN _ x.2)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h : (x : X)⁻¹ * φ x = (y : X)⁻¹ * φ y := congrArg Subtype.val hxy
    have hz : φ ((y : X) * (x : X)⁻¹) = (y : X) * (x : X)⁻¹ := by
      have h1 : φ y = (y : X) * (x : X)⁻¹ * φ x := by
        calc φ y = (y : X) * ((y : X)⁻¹ * φ y) := by group
          _ = (y : X) * ((x : X)⁻¹ * φ x) := by rw [h]
          _ = _ := by group
      rw [map_mul, map_inv, h1]
      group
    have := hfix _ (N.mul_mem y.2 (N.inv_mem x.2)) hz
    exact Subtype.ext (mul_inv_eq_one.1 this).symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hinj
  intro n hn
  obtain ⟨x, hx⟩ := hsurj ⟨n, hn⟩
  have hx' : (x : X)⁻¹ * φ x = n := congrArg Subtype.val hx
  rw [← hx', map_mul, map_inv, hφφ]
  group

theorem commute_of_aut_inv {φ : MulAut X} {N : Subgroup X}
    (h : ∀ n ∈ N, φ n = n⁻¹) : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  intro a ha b hb
  have h1 := h _ (N.mul_mem ha hb)
  rw [map_mul, h a ha, h b hb, mul_inv_rev] at h1
  have := congrArg (·⁻¹) h1
  simpa using this.symm

theorem inf_eq_bot_or_le_of_simple (A N : Subgroup X) (hA : IsSimpleGroup A)
    (hN : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) : N ⊓ A = ⊥ ∨ A ≤ N := by
  have : (N.subgroupOf A).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hN g g.2 n hn⟩
  rcases hA.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.2⟩ : A) ∈ N.subgroupOf A := hx.1
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  · right
    intro a ha
    have : (⟨a, ha⟩ : A) ∈ N.subgroupOf A := by rw [h]; exact Subgroup.mem_top _
    exact this

theorem eq_one_of_commutes_simple (A : Subgroup X) (hA : IsSimpleGroup A)
    (hna : ∃ a b : A, a * b ≠ b * a) (u : X) (huA : u ∈ A) (h : ∀ a ∈ A, a * u = u * a) :
    u = 1 := by
  have hn : (center A).Normal := inferInstance
  have hu : (⟨u, huA⟩ : A) ∈ center A := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (h g g.2)
  rcases hA.eq_bot_or_eq_top_of_normal (center A) with h0 | h0
  · rw [h0, Subgroup.mem_bot] at hu
    simpa using congrArg Subtype.val hu
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    exact hab ((mem_center_iff.1 (h0 ▸ Subgroup.mem_top b)) a)

theorem commutator_mem_centralizer_of_inverts (R : Subgroup X) [R.Normal] {u : X} (hu : u * u = 1)
    (hinv : ∀ r ∈ R, u * r * u⁻¹ = r⁻¹) (a : X) :
    a * u * a⁻¹ * u⁻¹ ∈ centralizer (R : Set X) := by
  have hti : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hg : ∀ r ∈ R, (a * u * a⁻¹) * r * (a * u * a⁻¹)⁻¹ = r⁻¹ := by
    intro r hr
    have hr' : a⁻¹ * r * a ∈ R := by
      simpa using Normal.conj_mem ‹R.Normal› r hr a⁻¹
    have := hinv _ hr'
    calc (a * u * a⁻¹) * r * (a * u * a⁻¹)⁻¹ = a * (u * (a⁻¹ * r * a) * u⁻¹) * a⁻¹ := by group
      _ = r⁻¹ := by rw [this]; group
  rw [mem_centralizer_iff]
  intro r hr
  have h1 := hg r hr
  have h2 : u⁻¹ * r * u = r⁻¹ := by
    have := hinv r hr
    rw [hti] at this ⊢
    exact this
  have h3 : (a * u * a⁻¹ * u⁻¹) * r * (a * u * a⁻¹ * u⁻¹)⁻¹ = r := by
    calc (a * u * a⁻¹ * u⁻¹) * r * (a * u * a⁻¹ * u⁻¹)⁻¹
        = (a * u * a⁻¹) * (u⁻¹ * r * u) * (a * u * a⁻¹)⁻¹ := by group
      _ = (a * u * a⁻¹) * r⁻¹ * (a * u * a⁻¹)⁻¹ := by rw [h2]
      _ = ((a * u * a⁻¹) * r * (a * u * a⁻¹)⁻¹)⁻¹ := by group
      _ = r := by rw [h1]; group
  generalize a * u * a⁻¹ * u⁻¹ = c at h3 ⊢
  calc r * c = (c * r * c⁻¹) * c := by rw [h3]
    _ = c * r := by group

theorem conj_mul_self_eq_one {u : X} (hu : u * u = 1) : MulAut.conj u * MulAut.conj u = 1 := by
  rw [← map_mul, hu, map_one]

theorem eq_bot_of_normal_odd [Finite X] (A R : Subgroup X) [R.Normal] (hAs : IsSimpleGroup A)
    (hAna : ∃ a b : A, a * b ≠ b * a) (u : X) (hu : u * u = 1) (hu1 : u ≠ 1) (huA : u ∈ A)
    (hT : Nat.card (centralizer ({u} : Set X)) = 16) (hR : Odd (Nat.card R)) : R = ⊥ := by
  by_contra hRne
  have hcop : Nat.Coprime (Nat.card R) (Nat.card (centralizer ({u} : Set X))) := by
    rw [hT]
    exact Nat.Coprime.pow_right 4 (Nat.Coprime.symm (Nat.coprime_two_left.2 hR) : Nat.Coprime _ 2)
  have hRT : R ⊓ centralizer ({u} : Set X) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h1 : Nat.card (R ⊓ centralizer ({u} : Set X) : Subgroup X) ∣ Nat.card R :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (R ⊓ centralizer ({u} : Set X) : Subgroup X) ∣
        Nat.card (centralizer ({u} : Set X)) := Subgroup.card_dvd_of_le inf_le_right
    exact Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd h1 h2)
  have hfix : ∀ n ∈ R, MulAut.conj u n = n → n = 1 := by
    intro n hn h
    have : n ∈ R ⊓ centralizer ({u} : Set X) := by
      refine ⟨hn, ?_⟩
      show n ∈ centralizer ({u} : Set X)
      rw [mem_centralizer_singleton_iff]
      rw [MulAut.conj_apply] at h
      calc n * u = u * n * u⁻¹ * u := by rw [h]
        _ = u * n := by group
    rw [hRT, Subgroup.mem_bot] at this
    exact this
  have hinv : ∀ r ∈ R, u * r * u⁻¹ = r⁻¹ := by
    intro r hr
    have := aut_inv_of_fixed_point_free (MulAut.conj u) R
      (fun n hn => by simpa [MulAut.conj_apply] using Normal.conj_mem ‹R.Normal› n hn u)
      (conj_mul_self_eq_one hu) hfix r hr
    simpa [MulAut.conj_apply] using this
  have hN : ∀ a ∈ A, ∀ n ∈ centralizer (R : Set X), a * n * a⁻¹ ∈ centralizer (R : Set X) := by
    intro a _ n hn
    rw [mem_centralizer_iff] at hn ⊢
    intro r hr
    have hr' : a⁻¹ * r * a ∈ R := by simpa using Normal.conj_mem ‹R.Normal› r hr a⁻¹
    have := hn _ hr'
    calc r * (a * n * a⁻¹) = a * ((a⁻¹ * r * a) * n) * a⁻¹ := by group
      _ = a * (n * (a⁻¹ * r * a)) * a⁻¹ := by rw [this]
      _ = a * n * a⁻¹ * r := by group
  rcases inf_eq_bot_or_le_of_simple A (centralizer (R : Set X)) hAs hN with h | h
  · apply hu1
    refine eq_one_of_commutes_simple A hAs hAna u huA fun a ha => ?_
    have hc := commutator_mem_centralizer_of_inverts R hu hinv a
    have hcA : a * u * a⁻¹ * u⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem (A.mul_mem ha huA) (A.inv_mem ha)) (A.inv_mem huA)
    have : a * u * a⁻¹ * u⁻¹ ∈ centralizer (R : Set X) ⊓ A := ⟨hc, hcA⟩
    rw [h, Subgroup.mem_bot] at this
    calc a * u = a * u * a⁻¹ * u⁻¹ * u * a := by group
      _ = u * a := by rw [this]; group
  · apply hRne
    rw [eq_bot_iff]
    intro r hr
    have hu' := h huA
    rw [mem_centralizer_iff] at hu'
    have h1 : r * u = u * r := hu' r hr
    have h2 := hinv r hr
    have h3 : r = r⁻¹ := by
      rw [← h2]; calc r = u * r * u⁻¹ := by rw [← h1]; group
        _ = u * r * u⁻¹ := rfl
    have h4 : (⟨r, hr⟩ : R) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
      calc r * r = r * r⁻¹ := by rw [← h3]
        _ = 1 := by group
    have h5 : orderOf (⟨r, hr⟩ : R) ∣ 2 := orderOf_dvd_of_pow_eq_one h4
    have h6 : orderOf (⟨r, hr⟩ : R) ∣ Nat.card R := orderOf_dvd_natCard _
    have h7 : orderOf (⟨r, hr⟩ : R) = 1 := by
      have := Nat.dvd_gcd h5 h6
      rw [(Nat.coprime_two_left.2 hR : Nat.Coprime 2 (Nat.card R))] at this
      exact Nat.dvd_one.1 this
    have := orderOf_eq_one_iff.1 h7
    simpa using congrArg Subtype.val this

theorem eq_bot_of_normal_two [Finite X] (A Q : Subgroup X) [Q.Normal] (hAs : IsSimpleGroup A)
    (hA60 : Nat.card A = 60) (τ : MulAut X) (hτ : τ * τ = 1) (hAτ : ∀ a : X, τ a = a → a ∈ A)
    (hQτ : ∀ q ∈ Q, τ q ∈ Q) (hQ : IsPGroup 2 Q) : Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  rcases inf_eq_bot_or_le_of_simple A Q hAs
      (fun a _ n hn => Normal.conj_mem ‹Q.Normal› n hn a) with h | h
  · have hfix : ∀ n ∈ Q, τ n = n → n = 1 := by
      intro n hn hτn
      have : n ∈ Q ⊓ A := ⟨hn, hAτ n hτn⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    have hinv := aut_inv_of_fixed_point_free τ Q hQτ hτ hfix
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hne
      apply Subgroup.eq_bot_of_card_eq
      simpa using hk
    have h2 : 2 ∣ Nat.card Q := by
      rw [hk]; exact dvd_pow_self 2 hk0
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hq2 : (q : X) * q = 1 := by
      have : q ^ 2 = 1 := by rw [← hq]; exact pow_orderOf_eq_one q
      have := congrArg Subtype.val this
      simpa [pow_two] using this
    have hq1 : q = 1 := by
      have h1 := hinv q q.2
      have h3 : (q : X)⁻¹ = q := inv_eq_of_mul_eq_one_right hq2
      have : (q : X) ∈ Q ⊓ A := ⟨q.2, hAτ _ (by rw [h1, h3])⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subtype.ext this
    rw [hq1, orderOf_one] at hq
    omega
  · have hdvd : Nat.card A ∣ Nat.card Q := Subgroup.card_dvd_of_le h
    rw [hA60, hk] at hdvd
    have h3 : 3 ∣ 2 ^ k := (Dvd.dvd.trans (by norm_num) hdvd)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

end Generic

section Alt5

theorem a5_isSimpleGroup : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem a5_nonabelian : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by decide +kernel

theorem a5_card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]; decide +kernel

theorem a5_involution_centralizer_sq :
    ∀ κ : alternatingGroup (Fin 5), κ ≠ 1 → κ * κ = 1 →
      ∀ a : alternatingGroup (Fin 5), a * κ = κ * a → a * a = 1 := by decide +kernel

theorem a5_involution_centralizer_card :
    ∀ κ : alternatingGroup (Fin 5), κ ≠ 1 → κ * κ = 1 →
      (Finset.univ.filter (fun a : alternatingGroup (Fin 5) => a * κ = κ * a)).card = 4 := by
  decide +kernel

theorem centralizer_involution_of_equiv_a5 {K : Type*} [Group K]
    (ψ : K ≃* alternatingGroup (Fin 5)) (k : K) (hk1 : k ≠ 1) (hk : k * k = 1) :
    Nat.card (centralizer ({k} : Set K)) = 4 ∧
      ∀ a ∈ centralizer ({k} : Set K), ∀ b ∈ centralizer ({k} : Set K),
        a * b = b * a ∧ a * a = 1 := by
  have hψk1 : ψ k ≠ 1 := fun h => hk1 (ψ.injective (by simpa using h))
  have hψk : ψ k * ψ k = 1 := by rw [← map_mul, hk, map_one]
  have hsq : ∀ a ∈ centralizer ({k} : Set K), a * a = 1 := by
    intro a ha
    rw [mem_centralizer_singleton_iff] at ha
    apply ψ.injective
    rw [map_mul, map_one]
    exact a5_involution_centralizer_sq (ψ k) hψk1 hψk (ψ a) (by rw [← map_mul, ← map_mul, ha])
  refine ⟨?_, fun a ha b hb => ⟨?_, hsq a ha⟩⟩
  · have e : (centralizer ({k} : Set K)) ≃ {b : alternatingGroup (Fin 5) // b * ψ k = ψ k * b} :=
      ψ.toEquiv.subtypeEquiv (fun a => by
        rw [mem_centralizer_singleton_iff]
        constructor
        · intro h; show ψ a * ψ k = ψ k * ψ a; rw [← map_mul, ← map_mul, h]
        · intro h; apply ψ.injective; rw [map_mul, map_mul]; exact h)
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact a5_involution_centralizer_card (ψ k) hψk1 hψk
  · have hab : a * b ∈ centralizer ({k} : Set K) := (centralizer ({k} : Set K)).mul_mem ha hb
    have h1 := hsq _ hab
    have ha1 := hsq a ha
    have hb1 := hsq b hb
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha1
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb1
    have : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
    rw [mul_inv_rev, hai, hbi] at this
    exact this.symm

end Alt5

section Setup

structure X5Hyp (X : Type) [Group X] (τ : MulAut X) (u : X) : Prop where
  hτ : τ * τ = 1
  hA : Nonempty (↥(autCentralizer τ) ≃* alternatingGroup (Fin 5))
  hu : u * u = 1
  hu1 : u ≠ 1
  huA : u ∈ autCentralizer τ
  hT : Nat.card (centralizer ({u} : Set X)) = 16

variable {X : Type} [Group X] {τ : MulAut X} {u : X}

theorem X5Hyp.simple (H : X5Hyp X τ u) : IsSimpleGroup (autCentralizer τ) := by
  obtain ⟨e⟩ := H.hA
  have := a5_isSimpleGroup
  exact e.isSimpleGroup

theorem X5Hyp.nonabelian (H : X5Hyp X τ u) : ∃ a b : autCentralizer τ, a * b ≠ b * a := by
  obtain ⟨e⟩ := H.hA
  obtain ⟨a, b, hab⟩ := a5_nonabelian
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem X5Hyp.card (H : X5Hyp X τ u) : Nat.card (autCentralizer τ) = 60 := by
  obtain ⟨e⟩ := H.hA
  rw [Nat.card_congr e.toEquiv, a5_card]

theorem characteristic_map_mem {Y : Type*} [Group Y] (N : Subgroup Y) [hN : N.Characteristic]
    (φ : MulAut Y) {n : Y} (hn : n ∈ N) : φ n ∈ N := by
  have h := hN.fixed (φ : Y ≃* Y)
  have hmem : n ∈ N.comap (φ : Y ≃* Y).toMonoidHom := by rw [h]; exact hn
  exact hmem

theorem X5Hyp.fitting_eq_bot [Finite X] (H : X5Hyp X τ u) : fittingSubgroup X = ⊥ := by
  rw [fitting_eq_sup_pCore, iSup_eq_bot]
  intro p
  have hp : Fact p.1.1.Prime := ⟨Nat.prime_of_mem_primeFactors p.1.2⟩
  by_cases h2 : p.1.1 = 2
  · rw [h2]
    exact eq_bot_of_normal_two (autCentralizer τ) (pCore 2 X) H.simple H.card τ H.hτ
      (fun a ha => ha) (fun q hq => characteristic_map_mem _ τ hq) pCore_isPGroup
  · have hodd : Odd p.1.1 := hp.out.eq_two_or_odd'.resolve_left h2
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := p.1.1) (G := X)).exists_card_eq
    exact eq_bot_of_normal_odd (autCentralizer τ) (pCore p.1.1 X) H.simple H.nonabelian u H.hu
      H.hu1 H.huA H.hT (by rw [hk]; exact hodd.pow)

theorem X5Hyp.le_of_perfect [Finite X] (H : X5Hyp X τ u) (N : Subgroup X)
    (hNτ : ∀ n ∈ N, τ n ∈ N) (hNA : ∀ a ∈ autCentralizer τ, ∀ n ∈ N, a * n * a⁻¹ ∈ N)
    (hperf : ⁅N, N⁆ = N) (hne : N ≠ ⊥) : autCentralizer τ ≤ N := by
  rcases inf_eq_bot_or_le_of_simple (autCentralizer τ) N H.simple hNA with h | h
  · exfalso
    apply hne
    have hfix : ∀ n ∈ N, τ n = n → n = 1 := by
      intro n hn hτn
      have : n ∈ N ⊓ autCentralizer τ := ⟨hn, hτn⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    have hcomm := commute_of_aut_inv (aut_inv_of_fixed_point_free τ N hNτ H.hτ hfix)
    rw [← hperf, eq_bot_iff]
    refine (Subgroup.commutator_le.2 fun a ha b hb => ?_)
    rw [commutatorElement_def, hcomm a ha b hb]
    simp
  · exact h

theorem layer_normal_of_characteristic : (layer X).Normal := by
  have : (layer X).Characteristic := LocalCores.layer_characteristic
  infer_instance

theorem X5Hyp.generalizedFitting_eq_layer [Finite X] (H : X5Hyp X τ u) :
    generalizedFitting X = layer X := by
  rw [generalizedFitting, H.fitting_eq_bot, bot_sup_eq]

theorem X5Hyp.centralizer_layer_eq_bot [Finite X] (H : X5Hyp X τ u) :
    centralizer (layer X : Set X) = ⊥ := by
  have hE : (layer X).Normal := layer_normal_of_characteristic
  have hZn : (centralizer (layer X : Set X)).Normal := inferInstance
  have hle : centralizer (layer X : Set X) ≤ layer X := by
    rw [← H.generalizedFitting_eq_layer]
    exact centralizer_generalizedFitting_le X
  have hab : IsMulCommutative (centralizer (layer X : Set X)) :=
    ⟨⟨fun a b => Subtype.ext (by
      have := mem_centralizer_iff.1 a.2 b (hle b.2)
      exact this.symm)⟩⟩
  have hnil : Group.IsNilpotent (centralizer (layer X : Set X)) := inferInstance
  have : centralizer (layer X : Set X) ≤ fittingSubgroup X :=
    le_sSup ⟨hZn, hnil⟩
  rw [H.fitting_eq_bot] at this
  exact le_bot_iff.1 this

theorem X5Hyp.layer_ne_bot [Finite X] (H : X5Hyp X τ u) : layer X ≠ ⊥ := by
  intro h
  have h1 := H.centralizer_layer_eq_bot
  have hsub : Subsingleton X := by
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : X, z ∈ centralizer (layer X : Set X) := fun z => by
      rw [mem_centralizer_iff]
      intro g hg
      have : g ∈ layer X := hg
      rw [h, Subgroup.mem_bot] at this
      rw [this]; simp
    have hx' := hx x
    have hy' := hx y
    rw [h1, Subgroup.mem_bot] at hx' hy'
    rw [hx', hy']
  have hle : Nat.card (autCentralizer τ) ≤ Nat.card X := Subgroup.card_le_card_group _
  have : Nat.card X = 1 := Nat.card_unique
  rw [H.card, this] at hle
  omega

theorem X5Hyp.A_le_layer [Finite X] (H : X5Hyp X τ u) : autCentralizer τ ≤ layer X := by
  have : (layer X).Characteristic := LocalCores.layer_characteristic
  have hE : (layer X).Normal := layer_normal_of_characteristic
  exact H.le_of_perfect (layer X) (fun n hn => characteristic_map_mem _ τ hn)
    (fun a _ n hn => hE.conj_mem n hn a) LocalCores.layer_perfect H.layer_ne_bot

end Setup

section Components

variable {X : Type} [Group X]

theorem sSup_components_perfect (S : Set (Subgroup X)) (hS : ∀ C ∈ S, IsComponent C) :
    ⁅sSup S, sSup S⁆ = sSup S := by
  refine le_antisymm (commutator_le_self _) (sSup_le fun K hK => ?_)
  calc K = ⁅K, K⁆ := (Subgroup.isPerfect_iff.mp (hS K hK).1.1).symm
    _ ≤ ⁅sSup S, sSup S⁆ := Subgroup.commutator_mono (le_sSup hK) (le_sSup hK)

theorem map_mem_sSup_of_forall (S : Set (Subgroup X)) (f : X →* X)
    (hf : ∀ C ∈ S, ∀ c ∈ C, f c ∈ sSup S) : ∀ n ∈ sSup S, f n ∈ sSup S := by
  intro n hn
  have : sSup S ≤ (sSup S).comap f := sSup_le fun C hC c hc => hf C hC c hc
  exact this hn

theorem isComponent_ne_bot {K : Subgroup X} (hK : IsComponent K) : K ≠ ⊥ := by
  intro h
  have := LocalCores.isQuasisimple_nontrivial hK.1
  rw [h] at this
  exact not_nontrivial (↥(⊥ : Subgroup X)) this

@[expose] def autImage (τ : MulAut X) (K : Subgroup X) : Subgroup X := K.map (τ : X ≃* X).toMonoidHom

theorem mem_autImage {τ : MulAut X} {K : Subgroup X} {x : X} :
    x ∈ autImage τ K ↔ ∃ y ∈ K, τ y = x := Iff.rfl

theorem autImage_autImage {τ : MulAut X} (hτ : τ * τ = 1) (K : Subgroup X) :
    autImage τ (autImage τ K) = K := by
  ext x
  simp only [mem_autImage]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have : τ (τ y) = y := by
      have := congrArg (fun ψ : MulAut X => ψ y) hτ
      simpa using this
    rw [this]; exact hy
  · intro hx
    refine ⟨τ x, ⟨x, hx, rfl⟩, ?_⟩
    have := congrArg (fun ψ : MulAut X => ψ x) hτ
    simpa using this

theorem autImage_injective (τ : MulAut X) : Function.Injective (autImage τ) :=
  fun _ _ h => Subgroup.map_injective (τ : X ≃* X).injective h

theorem isComponent_autImage {τ : MulAut X} {K : Subgroup X} (hK : IsComponent K) :
    IsComponent (autImage τ K) :=
  LocalCores.isComponent_map_mulEquiv (τ : X ≃* X) hK

theorem X5Hyp.exists_component_cover [Finite X] {τ : MulAut X} {u : X} (H : X5Hyp X τ u) :
    ∃ K : Subgroup X, IsComponent K ∧ ∀ C : Subgroup X, IsComponent C → C = K ∨ C = autImage τ K := by
  have hE : (layer X).Normal := layer_normal_of_characteristic
  obtain ⟨K, hK⟩ : ∃ K : Subgroup X, IsComponent K := by
    by_contra hno
    push Not at hno
    exact H.layer_ne_bot (LocalCores.layer_eq_bot_of_forall hno)
  refine ⟨K, hK, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hC, hCK, hCτK⟩ := hcon
  set S₁ : Set (Subgroup X) := {K, autImage τ K} with hS₁
  set S₂ : Set (Subgroup X) := {D | IsComponent D ∧ D ≠ K ∧ D ≠ autImage τ K} with hS₂
  have hS₁c : ∀ D ∈ S₁, IsComponent D := by
    rintro D (rfl | rfl)
    · exact hK
    · exact isComponent_autImage hK
  have hS₂c : ∀ D ∈ S₂, IsComponent D := fun D hD => hD.1
  have hnorm : ∀ (S : Set (Subgroup X)), (∀ D ∈ S, IsComponent D) →
      ∀ a ∈ layer X, ∀ n ∈ sSup S, a * n * a⁻¹ ∈ sSup S := by
    intro S hS a ha n hn
    have := map_mem_sSup_of_forall S (MulAut.conj a).toMonoidHom (fun D hD d hd => by
      have hmem := LocalCores.layer_le_normalizer (hS D hD) ha
      rw [Subgroup.mem_normalizer_iff] at hmem
      exact le_sSup hD (by simpa using (hmem d).1 hd)) n hn
    simpa using this
  have hAE := H.A_le_layer
  have hτ : ∀ x : X, τ (τ x) = x := fun x => by
    have := congrArg (fun ψ : MulAut X => ψ x) H.hτ
    simpa using this
  have hτS₁ : ∀ n ∈ sSup S₁, τ n ∈ sSup S₁ := by
    refine map_mem_sSup_of_forall S₁ (τ : X ≃* X).toMonoidHom ?_
    rintro D (rfl | rfl) c hc
    · exact le_sSup (show autImage τ D ∈ S₁ from Or.inr rfl) ⟨c, hc, rfl⟩
    · rw [mem_autImage] at hc
      obtain ⟨y, hy, rfl⟩ := hc
      exact le_sSup (show K ∈ S₁ from Or.inl rfl) (by simpa [hτ] using hy)
  have hS₂τ : ∀ D ∈ S₂, autImage τ D ∈ S₂ := by
    rintro D ⟨hD, hDK, hDτK⟩
    refine ⟨isComponent_autImage hD, fun h => hDτK ?_, fun h => hDK ?_⟩
    · rw [← autImage_autImage H.hτ D, h]
    · exact autImage_injective τ h
  have hτS₂ : ∀ n ∈ sSup S₂, τ n ∈ sSup S₂ := by
    refine map_mem_sSup_of_forall S₂ (τ : X ≃* X).toMonoidHom ?_
    intro D hD c hc
    exact le_sSup (hS₂τ D hD) ⟨c, hc, rfl⟩
  have hM : autCentralizer τ ≤ sSup S₁ := by
    refine H.le_of_perfect _ hτS₁ (fun a ha n hn => hnorm S₁ hS₁c a (hAE ha) n hn)
      (sSup_components_perfect S₁ hS₁c) ?_
    intro h
    apply isComponent_ne_bot hK
    rw [eq_bot_iff, ← h]
    exact le_sSup (show K ∈ S₁ from Or.inl rfl)
  have hC2 : C ∈ S₂ := ⟨hC, hCK, hCτK⟩
  have hM' : autCentralizer τ ≤ sSup S₂ := by
    refine H.le_of_perfect _ hτS₂ (fun a ha n hn => hnorm S₂ hS₂c a (hAE ha) n hn)
      (sSup_components_perfect S₂ hS₂c) ?_
    intro h
    apply isComponent_ne_bot hC
    rw [eq_bot_iff, ← h]
    exact le_sSup hC2
  have hcomm : sSup S₁ ≤ centralizer ((sSup S₂ : Subgroup X) : Set X) := by
    refine sSup_le fun D hD => ?_
    rw [Subgroup.le_centralizer_iff]
    refine sSup_le fun D' hD' => ?_
    rcases LocalCores.distinct_components_commute (hS₂c D' hD') (hS₁c D hD) with h | h
    · exfalso
      obtain ⟨-, h1, h2⟩ := hD'
      rcases hD with rfl | rfl
      · exact h1 h
      · exact h2 h
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  obtain ⟨a, b, hab⟩ := H.nonabelian
  apply hab
  apply Subtype.ext
  have := mem_centralizer_iff.1 (hcomm (hM a.2)) b (hM' b.2)
  simpa using this.symm

end Components

section Single

variable {X : Type} [Group X] {τ : MulAut X} {u : X}

theorem X5Hyp.tau_tau (H : X5Hyp X τ u) (x : X) : τ (τ x) = x := by
  have := congrArg (fun ψ : MulAut X => ψ x) H.hτ
  simpa using this

theorem X5Hyp.orderOf_u (H : X5Hyp X τ u) : orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact H.hu) H.hu1

@[expose] def restrictAut (τ : MulAut X) (hτ : τ * τ = 1) (K : Subgroup X) (hK : ∀ k ∈ K, τ k ∈ K) :
    MulAut K where
  toFun k := ⟨τ k, hK k k.2⟩
  invFun k := ⟨τ k, hK k k.2⟩
  left_inv k := Subtype.ext (by
    have := congrArg (fun ψ : MulAut X => ψ k) hτ
    simpa using this)
  right_inv k := Subtype.ext (by
    have := congrArg (fun ψ : MulAut X => ψ k) hτ
    simpa using this)
  map_mul' a b := Subtype.ext (map_mul τ (a : X) (b : X))

theorem X5Hyp.single_case [Finite X] (H : X5Hyp X τ u) (hC : CatE16) (hτ1 : τ ≠ 1)
    (K : Subgroup X) [K.Normal] (hKτ : ∀ k ∈ K, τ k ∈ K) (hKs : IsSimpleGroup K)
    (hKna : ∃ a b : K, a * b ≠ b * a) (hKcat : Catalog K)
    (hKc : centralizer (K : Set X) = ⊥) (hAK : autCentralizer τ ≤ K) :
    ∀ a ∈ centralizer ({u} : Set X), ∀ b ∈ centralizer ({u} : Set X),
      a * b = b * a ∧ a * a = 1 := by
  set τ' := restrictAut τ H.hτ K hKτ with hτ'def
  have hτ'τ' : τ' * τ' = 1 := by
    ext k
    show τ (τ (k : X)) = (k : X)
    exact H.tau_tau k
  have hfix : ∀ k : K, τ' k = k ↔ τ (k : X) = k := fun k =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  let eA : autCentralizer τ' ≃* autCentralizer τ :=
    { toFun := fun x => ⟨(x.1 : X), (hfix x.1).1 x.2⟩
      invFun := fun a => ⟨⟨a.1, hAK a.2⟩, (hfix _).2 a.2⟩
      left_inv := fun x => rfl
      right_inv := fun a => rfl
      map_mul' := fun x y => rfl }
  have hout : τ' ∉ (MulAut.conj : K →* MulAut K).range := by
    rintro ⟨k, hk⟩
    have hkfix : τ (k : X) = k := by
      have h1 : τ' k = k := by
        rw [← hk, MulAut.conj_apply]; group
      exact (hfix k).1 h1
    have hcomm : ∀ a ∈ autCentralizer τ, a * (k : X) = k * a := by
      intro a ha
      have haK := hAK ha
      have h1 : τ' ⟨a, haK⟩ = ⟨a, haK⟩ := (hfix _).2 ha
      rw [← hk, MulAut.conj_apply] at h1
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h2
      calc a * (k : X) = (k * a * (k : X)⁻¹) * k := by rw [h2]
        _ = k * a := by group
    have hk1 : (k : X) = 1 :=
      eq_one_of_commutes_simple (autCentralizer τ) H.simple H.nonabelian k hkfix hcomm
    have hk1' : k = 1 := Subtype.ext hk1
    apply hτ1
    ext x
    have hKfix : ∀ k' ∈ K, τ k' = k' := by
      intro k' hk'
      have h1 : τ' ⟨k', hk'⟩ = ⟨k', hk'⟩ := by rw [← hk, hk1']; simp
      exact (hfix _).1 h1
    have hmem : x⁻¹ * τ x ∈ centralizer (K : Set X) := by
      rw [mem_centralizer_iff]
      intro k' hk'
      have h1 : x * k' * x⁻¹ ∈ K := Normal.conj_mem ‹K.Normal› k' hk' x
      have h2 := hKfix _ h1
      rw [map_mul, map_mul, hKfix k' hk', map_inv] at h2
      calc k' * (x⁻¹ * τ x) = x⁻¹ * ((x * k' * x⁻¹) * τ x) := by group
        _ = x⁻¹ * ((τ x * k' * (τ x)⁻¹) * τ x) := by rw [h2]
        _ = (x⁻¹ * τ x) * k' := by group
    rw [hKc, Subgroup.mem_bot] at hmem
    have := mul_eq_one_iff_eq_inv.1 hmem
    simpa using (inv_inj.1 this).symm
  have huK : u ∈ K := hAK H.huA
  set κ : K := ⟨u, huK⟩ with hκdef
  have hκ : κ ∈ autCentralizer τ' := (hfix κ).2 H.huA
  have hκord : orderOf κ = 2 := by
    rw [hκdef, Subgroup.orderOf_mk]; exact H.orderOf_u
  let g : centralizer ({κ} : Set K) → centralizer ({u} : Set X) := fun x =>
    ⟨(x.1 : X), by
      have h := mem_centralizer_singleton_iff.1 x.2
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val h⟩
  have hg : Function.Injective g := fun x y h => by
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  have hle : Nat.card (centralizer ({κ} : Set K)) ≤ 16 := by
    rw [← H.hT]
    exact Nat.card_le_card_of_injective g hg
  obtain ⟨hcard, habel⟩ := hC K hKcat hKs hKna τ' hτ'τ' hout
    ⟨eA.trans (Classical.choice H.hA)⟩ κ hκ hκord hle
  have hbij : Function.Bijective g :=
    (Nat.bijective_iff_injective_and_card g).2 ⟨hg, by rw [hcard, H.hT]⟩
  intro a ha b hb
  obtain ⟨x, hx⟩ := hbij.2 ⟨a, ha⟩
  obtain ⟨y, hy⟩ := hbij.2 ⟨b, hb⟩
  have hxa : ((x : K) : X) = a := congrArg Subtype.val hx
  have hyb : ((y : K) : X) = b := congrArg Subtype.val hy
  rw [← hxa, ← hyb]
  have h := habel x x.2 y y.2
  refine ⟨?_, ?_⟩
  · exact congrArg (fun z : K => (z : X)) h.1
  · exact congrArg (fun z : K => (z : X)) h.2

end Single

section Pair

variable {X : Type} [Group X] {τ : MulAut X} {u : X}

theorem mem_sup_of_commute {K L : Subgroup X} (h : ∀ x ∈ K, ∀ y ∈ L, x * y = y * x) {e : X}
    (he : e ∈ K ⊔ L) : ∃ k ∈ K, ∃ l ∈ L, k * l = e := by
  rw [Subgroup.sup_eq_closure] at he
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ he
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, L.one_mem, by simp⟩
    · exact ⟨1, K.one_mem, x, hx, by simp⟩
  · exact ⟨1, K.one_mem, 1, L.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * y₂, K.mul_mem hy₁ hy₂, z₁ * z₂, L.mul_mem hz₁ hz₂, ?_⟩
    calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
      _ = y₁ * (z₁ * y₂) * z₂ := by rw [h y₂ hy₂ z₁ hz₁]
      _ = y₁ * z₁ * (y₂ * z₂) := by group
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨y⁻¹, K.inv_mem hy, z⁻¹, L.inv_mem hz, ?_⟩
    calc y⁻¹ * z⁻¹ = (z * y)⁻¹ := by group
      _ = (y * z)⁻¹ := by rw [← h y hy z hz]

theorem X5Hyp.pair_case [Finite X] (H : X5Hyp X τ u) (K : Subgroup X)
    (hKL : ∀ x ∈ K, ∀ y ∈ autImage τ K, x * y = y * x)
    (hmeet : ∀ x ∈ K, x ∈ autImage τ K → x = 1)
    (hcover : autCentralizer τ ≤ K ⊔ autImage τ K) :
    ∀ a ∈ centralizer ({u} : Set X), ∀ b ∈ centralizer ({u} : Set X),
      a * b = b * a ∧ a * a = 1 := by
  set L := autImage τ K with hLdef
  have hτK : ∀ k ∈ K, τ k ∈ L := fun k hk => ⟨k, hk, rfl⟩
  have hτL : ∀ l ∈ L, τ l ∈ K := by
    rintro l ⟨y, hy, rfl⟩
    show τ (τ y) ∈ K
    rw [H.tau_tau]; exact hy
  have hLK : ∀ y ∈ L, ∀ x ∈ K, y * x = x * y := fun y hy x hx => (hKL x hx y hy).symm
  have uniq : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ l₁ ∈ L, ∀ l₂ ∈ L, k₁ * l₁ = k₂ * l₂ → k₁ = k₂ ∧ l₁ = l₂ := by
    intro k₁ hk₁ k₂ hk₂ l₁ hl₁ l₂ hl₂ h
    have h1 : k₂⁻¹ * k₁ = l₂ * l₁⁻¹ := by
      calc k₂⁻¹ * k₁ = k₂⁻¹ * (k₁ * l₁) * l₁⁻¹ := by group
        _ = k₂⁻¹ * (k₂ * l₂) * l₁⁻¹ := by rw [h]
        _ = l₂ * l₁⁻¹ := by group
    have h2 : k₂⁻¹ * k₁ = 1 :=
      hmeet _ (K.mul_mem (K.inv_mem hk₂) hk₁) (h1 ▸ L.mul_mem hl₂ (L.inv_mem hl₁))
    have h3 : k₁ = k₂ := by
      calc k₁ = k₂ * (k₂⁻¹ * k₁) := by group
        _ = k₂ := by rw [h2, mul_one]
    refine ⟨h3, ?_⟩
    rw [h3] at h
    exact mul_left_cancel h
  have decomp : ∀ a : X, τ a = a → a ∈ K ⊔ L → ∃ k ∈ K, a = k * τ k := by
    intro a ha hmem
    obtain ⟨k, hk, l, hl, rfl⟩ := mem_sup_of_commute hKL hmem
    rw [map_mul] at ha
    have h1 : τ l * τ k = k * l := by
      rw [← ha]
      exact hKL (τ l) (hτL l hl) (τ k) (hτK k hk)
    obtain ⟨-, h3⟩ := uniq _ (hτL l hl) k hk _ (hτK k hk) l hl h1
    exact ⟨k, hk, by rw [← h3]⟩
  have hfixed : ∀ k ∈ K, τ (k * τ k) = k * τ k := by
    intro k hk
    rw [map_mul, H.tau_tau]
    exact (hKL k hk (τ k) (hτK k hk)).symm
  let φ : K →* autCentralizer τ :=
    MonoidHom.mk' (fun k => ⟨(k : X) * τ k, hfixed k k.2⟩) (fun a b => by
      apply Subtype.ext
      show (a * b : K).1 * τ (a * b : K).1 = ((a : X) * τ a) * ((b : X) * τ b)
      rw [Subgroup.coe_mul, map_mul]
      calc (a : X) * b * (τ a * τ b) = a * (b * τ a) * τ b := by group
        _ = a * (τ a * b) * τ b := by rw [hLK _ (hτK a a.2) b b.2]
        _ = _ := by group)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : (k : X) * τ k = 1 := congrArg Subtype.val hk
    have h2 : (k : X) = (τ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (k : X) ∈ L := by
      rw [h2]; exact L.inv_mem (hτK k k.2)
    exact Subtype.ext (hmeet k k.2 h3)
  have hφsurj : Function.Surjective φ := by
    intro a
    obtain ⟨k, hk, hak⟩ := decomp a a.2 (hcover a.2)
    exact ⟨⟨k, hk⟩, Subtype.ext hak.symm⟩
  let ψ : K ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).trans (Classical.choice H.hA)
  obtain ⟨k, hk, hu⟩ := decomp u H.huA (hcover H.huA)
  have hkk : k * k = 1 := by
    have h1 : (k * τ k) * (k * τ k) = 1 := by rw [← hu]; exact H.hu
    have h2 : k * k * (τ k * τ k) = 1 := by
      calc k * k * (τ k * τ k) = k * (k * τ k) * τ k := by group
        _ = k * (τ k * k) * τ k := by rw [hKL k hk (τ k) (hτK k hk)]
        _ = 1 := by rw [← h1]; group
    have h3 : k * k = (τ k * τ k)⁻¹ := eq_inv_of_mul_eq_one_left h2
    exact hmeet _ (K.mul_mem hk hk) (by rw [h3]; exact L.inv_mem (L.mul_mem (hτK k hk) (hτK k hk)))
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply H.hu1
    rw [hu]; simp
  set κ : K := ⟨k, hk⟩ with hκdef
  have hκ1 : κ ≠ 1 := fun h => hk1 (congrArg Subtype.val h)
  have hκ2 : κ * κ = 1 := Subtype.ext hkk
  obtain ⟨hcard4, helem⟩ := centralizer_involution_of_equiv_a5 ψ κ hκ1 hκ2
  set D : Subgroup X := (centralizer ({κ} : Set K)).map K.subtype with hDdef
  set D' : Subgroup X := autImage τ D with hD'def
  have hDK : ∀ d ∈ D, d ∈ K := by
    rintro _ ⟨y, _, rfl⟩; exact y.2
  have hDk : ∀ d ∈ D, d * k = k * d := by
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)
  have hD'L : ∀ d ∈ D', d ∈ L := by
    rintro _ ⟨y, hy, rfl⟩; exact hτK y (hDK y hy)
  have hDel : ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ * d₂ = d₂ * d₁ ∧ d₁ * d₁ = 1 := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    have := helem y₁ hy₁ y₂ hy₂
    exact ⟨congrArg Subtype.val this.1, congrArg Subtype.val this.2⟩
  have hD'el : ∀ d₁ ∈ D', ∀ d₂ ∈ D', d₁ * d₂ = d₂ * d₁ ∧ d₁ * d₁ = 1 := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    have := hDel y₁ hy₁ y₂ hy₂
    refine ⟨?_, ?_⟩
    · show τ y₁ * τ y₂ = τ y₂ * τ y₁
      rw [← map_mul, ← map_mul, this.1]
    · show τ y₁ * τ y₁ = 1
      rw [← map_mul, this.2, map_one]
  have hcommDD' : ∀ d ∈ D, ∀ d' ∈ D', d * d' = d' * d := fun d hd d' hd' =>
    hKL d (hDK d hd) d' (hD'L d' hd')
  let f : D × D' →* X := D.subtype.noncommCoprod D'.subtype (fun d d' => hcommDD' d d.2 d' d'.2)
  have hf : ∀ d d', f (d, d') = (d : X) * d' := fun d d' => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨d, d'⟩ h
    rw [hf] at h
    have h2 : (d : X) = (d' : X)⁻¹ := eq_inv_of_mul_eq_one_left h
    have h3 : (d : X) ∈ L := by rw [h2]; exact L.inv_mem (hD'L d' d'.2)
    have h4 : (d : X) = 1 := hmeet _ (hDK d d.2) h3
    have h5 : (d' : X) = 1 := by rw [h4, one_mul] at h; exact h
    exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
  have hrange : f.range ≤ centralizer ({u} : Set X) := by
    rintro _ ⟨⟨d, d'⟩, rfl⟩
    rw [mem_centralizer_singleton_iff, hf]
    obtain ⟨d₁, hd₁, hd₁'⟩ := d'.2
    have hd'k : (d' : X) * k = k * d' := (hD'L d' d'.2 |> fun h => (hKL k hk d' h).symm)
    have hd'τk : (d' : X) * τ k = τ k * d' := by
      rw [← hd₁']
      show τ d₁ * τ k = τ k * τ d₁
      rw [← map_mul, ← map_mul, hDk d₁ hd₁]
    have hdτk : (d : X) * τ k = τ k * d := hKL d (hDK d d.2) (τ k) (hτK k hk)
    have hdk : (d : X) * k = k * d := hDk d d.2
    rw [hu]
    calc (d * d' : X) * (k * τ k) = d * (d' * k) * τ k := by group
      _ = d * (k * d') * τ k := by rw [hd'k]
      _ = (d * k) * (d' * τ k) := by group
      _ = (k * d) * (τ k * d') := by rw [hdk, hd'τk]
      _ = k * (d * τ k) * d' := by group
      _ = k * (τ k * d) * d' := by rw [hdτk]
      _ = (k * τ k) * (d * d') := by group
  have hcardD : Nat.card D = 4 := by
    rw [hDdef, Subgroup.card_map_of_injective K.subtype_injective, hcard4]
  have hcardD' : Nat.card D' = 4 := by
    rw [hD'def, autImage, Subgroup.card_map_of_injective (τ : X ≃* X).injective, hcardD]
  have hcardR : Nat.card f.range = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, Nat.card_prod, hcardD, hcardD']
  have hreq : f.range = centralizer ({u} : Set X) :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [H.hT, hcardR])
  intro a ha b hb
  rw [← hreq] at ha hb
  obtain ⟨⟨d₁, d₁'⟩, rfl⟩ := ha
  obtain ⟨⟨d₂, d₂'⟩, rfl⟩ := hb
  rw [hf, hf]
  have c12 := (hDel d₁ d₁.2 d₂ d₂.2)
  have c12' := (hD'el d₁' d₁'.2 d₂' d₂'.2)
  have c11' := hcommDD' d₁ d₁.2 d₁' d₁'.2
  have c12x := hcommDD' d₁ d₁.2 d₂' d₂'.2
  have c21x := hcommDD' d₂ d₂.2 d₁' d₁'.2
  refine ⟨?_, ?_⟩
  · calc (d₁ : X) * d₁' * (d₂ * d₂') = (d₁ * d₂) * (d₁' * d₂') := by
          calc (d₁ : X) * d₁' * (d₂ * d₂') = d₁ * (d₁' * d₂) * d₂' := by group
            _ = d₁ * (d₂ * d₁') * d₂' := by rw [← c21x]
            _ = _ := by group
      _ = (d₂ * d₁) * (d₂' * d₁') := by rw [c12.1, c12'.1]
      _ = d₂ * d₂' * (d₁ * d₁') := by
          calc (d₂ : X) * d₁ * (d₂' * d₁') = d₂ * (d₁ * d₂') * d₁' := by group
            _ = d₂ * (d₂' * d₁) * d₁' := by rw [c12x]
            _ = _ := by group
  · calc (d₁ : X) * d₁' * (d₁ * d₁') = d₁ * (d₁' * d₁) * d₁' := by group
      _ = d₁ * (d₁ * d₁') * d₁' := by rw [← c11']
      _ = (d₁ * d₁) * (d₁' * d₁') := by group
      _ = 1 := by rw [(hDel d₁ d₁.2 d₁ d₁.2).2, (hD'el d₁' d₁'.2 d₁' d₁'.2).2, one_mul]

end Pair

section Main

variable {X : Type} [Group X] {τ : MulAut X} {u : X}

theorem X5Hyp.component_simple [Finite X] (H : X5Hyp X τ u) {C : Subgroup X} (hC : IsComponent C) :
    IsSimpleGroup C ∧ ∃ a b : C, a * b ≠ b * a := by
  have hcenter : center ↥C = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : (z : X) ∈ (center ↥C).map C.subtype := ⟨z, hz, rfl⟩
    have h2 := LocalCores.center_component_le_centralizer_layer hC h1
    rw [H.centralizer_layer_eq_bot, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.2 (Subtype.ext h2)
  let e0 : ↥C ⧸ center ↥C ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  obtain ⟨-, hs, a, b, hab⟩ := hC.1
  refine ⟨e0.symm.isSimpleGroup, e0 a, e0 b, fun h => hab ?_⟩
  apply e0.injective
  rw [map_mul, map_mul]
  exact h

end Main

theorem elemAbelian_centralizer_of_X5 (hC : CatE16) {X : Type} [Group X] [Finite X]
    (hKP : ∀ H : Subgroup X, IsSimpleGroup H → (∃ a b : H, a * b ≠ b * a) → Catalog H)
    (τ : MulAut X) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hA : Nonempty (↥(autCentralizer τ) ≃* alternatingGroup (Fin 5)))
    (u : X) (hu : orderOf u = 2) (huA : u ∈ autCentralizer τ)
    (hT : Nat.card (centralizer ({u} : Set X)) = 16) :
    ∀ a ∈ centralizer ({u} : Set X), ∀ b ∈ centralizer ({u} : Set X),
      a * b = b * a ∧ a * a = 1 := by
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu, pow_two] at this
  have hu1 : u ≠ 1 := by
    rintro rfl
    simp at hu
  have H : X5Hyp X τ u := ⟨hτ, hA, hu2, hu1, huA, hT⟩
  obtain ⟨K, hK, hcov⟩ := H.exists_component_cover
  have hKc := H.component_simple hK
  have hLc : IsComponent (autImage τ K) := isComponent_autImage hK
  have hlayer : layer X = K ⊔ autImage τ K := by
    refine le_antisymm (sSup_le fun C hC' => ?_)
      (sup_le (LocalCores.component_le_layer hK) (LocalCores.component_le_layer hLc))
    rcases hcov C hC' with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hAE := H.A_le_layer
  by_cases hKτ : autImage τ K = K
  · rw [hKτ, sup_idem] at hlayer
    have hKn : K.Normal := hlayer ▸ layer_normal_of_characteristic
    refine H.single_case hC hτ1 K (fun k hk => ?_) hKc.1 hKc.2 (hKP K hKc.1 hKc.2)
      (by rw [← hlayer]; exact H.centralizer_layer_eq_bot) (hlayer ▸ hAE)
    have h : τ k ∈ autImage τ K := ⟨k, hk, rfl⟩
    rwa [hKτ] at h
  · have hKL : ∀ x ∈ K, ∀ y ∈ autImage τ K, x * y = y * x := by
      rcases LocalCores.distinct_components_commute hK hLc with h | h
      · exact absurd h.symm hKτ
      · intro x hx y hy
        exact (mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx) y hy).symm
    refine H.pair_case K hKL (fun x hx hxL => ?_) (hlayer ▸ hAE)
    exact eq_one_of_commutes_simple K hKc.1 hKc.2 x hx fun a ha => hKL a ha x hxL

theorem elemAbelian_centralizer_of_X5_of_kGroup (hC : CatE16) {X : Type} [Group X] [Finite X]
    (hX : CFSG.SectionRank.IsKGroupCat X)
    (τ : MulAut X) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hA : Nonempty (↥(autCentralizer τ) ≃* alternatingGroup (Fin 5)))
    (u : X) (hu : orderOf u = 2) (huA : u ∈ autCentralizer τ)
    (hT : Nat.card (centralizer ({u} : Set X)) = 16) :
    ∀ a ∈ centralizer ({u} : Set X), ∀ b ∈ centralizer ({u} : Set X),
      a * b = b * a ∧ a * a = 1 :=
  elemAbelian_centralizer_of_X5 hC
    (fun H hs _ => by
      have := hs
      exact CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hX H (MonoidHom.id H)
        Function.surjective_id)
    τ hτ hτ1 hA u hu huA hT

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
