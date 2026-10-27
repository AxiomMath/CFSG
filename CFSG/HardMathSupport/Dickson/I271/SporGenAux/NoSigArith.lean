module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Coprime
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

theorem card_modEq_one_of_fpf {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {g : G}
    (hgp : g ^ p = 1) {V : Subgroup G} (hVinv : ∀ y ∈ V, g * y * g⁻¹ ∈ V)
    (hVinv' : ∀ y ∈ V, g⁻¹ * y * g ∈ V) (hfix : ∀ y ∈ V, g * y * g⁻¹ = y → y = 1) :
    Nat.card V ≡ 1 [MOD p] := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype ↥V := Fintype.ofFinite _
  let f : Equiv.Perm G := MulAut.toPerm G (MulAut.conj g)
  have hf : ∀ x : G, f x = g * x * g⁻¹ := fun x => rfl
  have hiff : ∀ x : G, f x ∈ V ↔ x ∈ V := by
    intro x
    constructor
    · intro hx
      have := hVinv' _ hx
      simpa [hf, mul_assoc] using this
    · intro hx
      rw [hf]
      exact hVinv x hx
  let σ : Equiv.Perm ↥V := Equiv.Perm.subtypePerm f hiff
  have hσp' : σ ^ p ^ 1 = 1 := by
    ext x
    rw [pow_one, Equiv.Perm.subtypePerm_pow]
    have hfp : f ^ p = 1 := by
      show (MulAut.toPerm G (MulAut.conj g)) ^ p = 1
      rw [← map_pow, ← map_pow, hgp, map_one, map_one]
    simp [hfp]
  have hfixed : σ.supportᶜ = {(⟨1, V.one_mem⟩ : ↥V)} := by
    ext x
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro hx
      have h1 : g * (x : G) * g⁻¹ = x := by
        have := congrArg Subtype.val hx
        simpa [σ, hf] using this
      exact Subtype.ext (hfix x x.2 h1)
    · intro hx
      subst hx
      apply Subtype.ext
      simp [σ, hf]
  have hmod := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) hσp'
  rw [hfixed, Finset.card_singleton, ← Nat.card_eq_fintype_card] at hmod
  exact hmod.symm

theorem noSig_of_rank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hE2 : Nat.card E = p ^ 2)
    (hA : ∀ u : G, Nat.Coprime (orderOf u) p → (∀ f ∈ E, u * f = f * u) → u = 1)
    (hB : ∀ e ∈ E, e ≠ 1 → ∀ q : ℕ, q.Prime → q ≠ p → ∀ V : Subgroup G,
      V ≤ Subgroup.centralizer ({e} : Set G) → IsElemAbelian q V → V ≠ ⊥ →
        Nat.card V % p ≠ 1) :
    ∀ T : Subgroup G, Nat.Coprime p (Nat.card T) →
      E ≤ Subgroup.normalizer (T : Set G) → T = ⊥ := by
  classical
  intro T hTcop hET
  by_contra hTne
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CFSG.IsElementaryAbelian p E := hE.isElementaryAbelian
  have hTp : ¬ p ∣ Nat.card T := (Nat.Prime.coprime_iff_not_dvd hp).1 hTcop
  have hgen := le_iSup_centralizer_of_coprime (p := p) (A := E) (U := T) (by rw [hE2]) hTp hET
  obtain ⟨e, he, he1, hRne⟩ : ∃ e ∈ E, e ≠ 1 ∧
      T ⊓ Subgroup.centralizer ({e} : Set G) ≠ ⊥ := by
    by_contra hall
    push Not at hall
    apply hTne
    rw [eq_bot_iff]
    refine hgen.trans (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
    rw [hall a ha ha1]
  set R : Subgroup G := T ⊓ Subgroup.centralizer ({e} : Set G) with hR
  have he_ord : orderOf e = p := orderOf_eq_prime (hE.2 e he) he1
  obtain ⟨g, hgE, hgnot⟩ : ∃ g ∈ E, g ∉ Subgroup.zpowers e := by
    by_contra hall
    push Not at hall
    have hle : E ≤ Subgroup.zpowers e := fun x hx => hall x hx
    have := Subgroup.card_le_of_le hle
    rw [hE2, Nat.card_zpowers, he_ord] at this
    nlinarith [hp.two_le]
  have hge : g * e = e * g := congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hgE⟩ ⟨e, he⟩)
  have hgp : g ^ p = 1 := hE.2 g hgE
  have hgR : ∀ h ∈ E, ∀ x ∈ R, h * x * h⁻¹ ∈ R := by
    intro h hh x hx
    have hxT : x ∈ T := hx.1
    have hxC : x ∈ Subgroup.centralizer ({e} : Set G) := hx.2
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hET hh) x).1 hxT, ?_⟩
    · show h * x * h⁻¹ ∈ Subgroup.centralizer ({e} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
      have heh : h * e = e * h := congrArg Subtype.val (hE.1.is_comm.comm ⟨h, hh⟩ ⟨e, he⟩)
      have hheinv : h⁻¹ * e = e * h⁻¹ := by
        calc h⁻¹ * e = h⁻¹ * (e * h) * h⁻¹ := by group
          _ = h⁻¹ * (h * e) * h⁻¹ := by rw [heh]
          _ = e * h⁻¹ := by group
      calc h * x * h⁻¹ * e = h * x * (h⁻¹ * e) := by group
        _ = h * x * (e * h⁻¹) := by rw [hheinv]
        _ = h * (x * e) * h⁻¹ := by group
        _ = h * (e * x) * h⁻¹ := by rw [hxC]
        _ = (h * e) * x * h⁻¹ := by group
        _ = (e * h) * x * h⁻¹ := by rw [heh]
        _ = e * (h * x * h⁻¹) := by group
  have hgN : g ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hgR g hgE x hx, fun hx => ?_⟩
    have := hgR g⁻¹ (E.inv_mem hgE) _ hx
    simpa [mul_assoc] using this
  have hRcard : Nat.card R ≠ 1 := by
    intro h
    exact hRne (Subgroup.eq_bot_of_card_eq R h)
  obtain ⟨q, hq, hqR⟩ := Nat.exists_prime_and_dvd hRcard
  have hRT : Nat.card R ∣ Nat.card T := Subgroup.card_dvd_of_le inf_le_left
  have hqp : q ≠ p := by
    rintro rfl
    exact hTp (hqR.trans hRT)
  haveI : Fact q.Prime := ⟨hq⟩
  set ψ : MulAut ↥R := R.normalizerMonoidHom ⟨g, hgN⟩ with hψ
  have hψp : ψ ^ p = 1 := by
    rw [hψ, ← map_pow]
    have : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (R : Set G))) ^ p = 1 := Subtype.ext hgp
    rw [this, map_one]
  haveI : Fintype (Sylow q ↥R) := Fintype.ofFinite _
  let ρ : MulAut ↥R →* Equiv.Perm (Sylow q ↥R) := MulAction.toPermHom (MulAut ↥R) (Sylow q ↥R)
  have hσ : (ρ ψ) ^ p ^ 1 = 1 := by rw [pow_one, ← map_pow, hψp, map_one]
  have hcardSyl : ¬ p ∣ Fintype.card (Sylow q ↥R) := by
    intro hd
    obtain ⟨Q0⟩ : Nonempty (Sylow q ↥R) := inferInstance
    have h1 : Nat.card (Sylow q ↥R) ∣ Q0.index := Q0.card_dvd_index
    have h2 : Q0.index ∣ Nat.card R := Subgroup.index_dvd_card _
    rw [Nat.card_eq_fintype_card] at h1
    exact hTp ((hd.trans h1).trans (h2.trans hRT))
  obtain ⟨Q, hQ⟩ := Equiv.Perm.exists_fixed_point_of_prime hcardSyl hσ
  have hQfix : ψ • Q = Q := hQ
  have hQinv : ∀ x : ↥R, x ∈ (Q : Subgroup ↥R) → ψ x ∈ (Q : Subgroup ↥R) := by
    intro x hx
    have h1 : ψ x ∈ ((ψ • Q : Sylow q ↥R) : Subgroup ↥R) := by
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul x ψ _ hx
    rw [hQfix] at h1
    exact h1
  set Q' : Subgroup G := (Q : Subgroup ↥R).map R.subtype with hQ'def
  have hQ'R : Q' ≤ R := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hQ'inv : ∀ y ∈ Q', g * y * g⁻¹ ∈ Q' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨ψ x, hQinv x hx, rfl⟩
  have hRne0 : Nat.card R ≠ 0 := Nat.card_pos.ne'
  have hQ'card : Nat.card Q' = q ^ (Nat.card R).factorization q := by
    rw [hQ'def, Subgroup.card_map_of_injective R.subtype_injective]
    exact Q.card_eq_multiplicity
  have hk : 0 < (Nat.card R).factorization q :=
    (Nat.Prime.dvd_iff_one_le_factorization hq hRne0).1 hqR
  set k := (Nat.card R).factorization q with hkdef
  have hQ'pow : ∀ n : ℕ, ∀ y ∈ Q', g ^ n * y * (g ^ n)⁻¹ ∈ Q' := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      have := hQ'inv _ (ih y hy)
      convert this using 1
      group
  have hQ'inv' : ∀ y ∈ Q', g⁻¹ * y * g ∈ Q' := by
    intro y hy
    have hginv : g ^ (p - 1) = g⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hgp]
    have := hQ'pow (p - 1) y hy
    rwa [hginv, inv_inv] at this
  have hQ'fix : ∀ y ∈ Q', g * y * g⁻¹ = y → y = 1 := by
    intro y hy hyg
    have hyR : y ∈ R := hQ'R hy
    have hye : y * e = e * y := Subgroup.mem_centralizer_singleton_iff.1 hyR.2
    have hyg' : y * g = g * y := by
      calc y * g = (g * y * g⁻¹) * g := by rw [hyg]
        _ = g * y := by group
    have hord : orderOf y ∣ q ^ k := by
      rw [← hQ'card]
      exact Subgroup.orderOf_dvd_natCard Q' hy
    have hcop : Nat.Coprime (orderOf y) p :=
      Nat.Coprime.coprime_dvd_left hord
        (Nat.Coprime.pow_left k ((Nat.coprime_primes hq hp).2 hqp))
    have hCE : Subgroup.closure ({e, g} : Set G) ≤ E := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl) <;> assumption
    have hz : Subgroup.zpowers e ≤ Subgroup.closure ({e, g} : Set G) :=
      (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
    have hg' : g ∈ Subgroup.closure ({e, g} : Set G) := Subgroup.subset_closure (by simp)
    have hltp : p < Nat.card (Subgroup.closure ({e, g} : Set G)) := by
      have h1 : Nat.card (Subgroup.zpowers e) < Nat.card (Subgroup.closure ({e, g} : Set G)) := by
        refine lt_of_le_of_ne (Subgroup.card_le_of_le hz) fun heq => hgnot ?_
        have := Subgroup.eq_of_le_of_card_ge hz heq.ge
        rw [this]
        exact hg'
      rwa [Nat.card_zpowers, he_ord] at h1
    have hdvd : Nat.card (Subgroup.closure ({e, g} : Set G)) ∣ p ^ 2 := by
      rw [← hE2]
      exact Subgroup.card_dvd_of_le hCE
    have hcard : Nat.card (Subgroup.closure ({e, g} : Set G)) = p ^ 2 := by
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      by_contra hne
      have hj1 : j ≤ 1 := by
        by_contra h2
        have : j = 2 := by omega
        subst this
        exact hne hj'
      have : p ^ j ≤ p := by
        calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hj1
          _ = p := pow_one p
      omega
    have hEC : Subgroup.closure ({e, g} : Set G) = E :=
      Subgroup.eq_of_le_of_card_ge hCE (by rw [hcard, hE2])
    refine hA y hcop fun f hf => ?_
    have hfc : f ∈ Subgroup.closure ({e, g} : Set G) := hEC ▸ hf
    have hcl : Subgroup.closure ({e, g} : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 hye.symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 hyg'.symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hcl hfc)).symm
  let V : Subgroup G :=
    { carrier := {x | x ∈ Q' ∧ x ^ q = 1 ∧ ∀ y ∈ Q', x * y = y * x}
      one_mem' := ⟨Q'.one_mem, one_pow _, fun y _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haQ, haq, hac⟩ ⟨hbQ, hbq, hbc⟩
        refine ⟨Q'.mul_mem haQ hbQ, ?_, fun y hy => ?_⟩
        · have hab : Commute a b := hac b hbQ
          rw [hab.mul_pow, haq, hbq, one_mul]
        · calc a * b * y = a * (b * y) := mul_assoc _ _ _
            _ = a * (y * b) := by rw [hbc y hy]
            _ = (a * y) * b := (mul_assoc _ _ _).symm
            _ = (y * a) * b := by rw [hac y hy]
            _ = y * (a * b) := mul_assoc _ _ _
      inv_mem' := by
        rintro a ⟨haQ, haq, hac⟩
        refine ⟨Q'.inv_mem haQ, by rw [inv_pow, haq, inv_one], fun y hy => ?_⟩
        have := hac y hy
        calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * y) * a⁻¹ := by rw [this]
          _ = y * a⁻¹ := by group }
  have hVmem : ∀ x, x ∈ V ↔ x ∈ Q' ∧ x ^ q = 1 ∧ ∀ y ∈ Q', x * y = y * x := fun x => Iff.rfl
  have hVQ' : V ≤ Q' := fun x hx => ((hVmem x).1 hx).1
  have hVinv : ∀ y ∈ V, g * y * g⁻¹ ∈ V := by
    intro y hy
    obtain ⟨hyQ, hyq, hyc⟩ := (hVmem y).1 hy
    refine (hVmem _).2 ⟨hQ'inv y hyQ, ?_, fun w hw => ?_⟩
    · rw [conj_pow, hyq]
      group
    · have hw' : g⁻¹ * w * g ∈ Q' := hQ'inv' w hw
      have := hyc _ hw'
      calc g * y * g⁻¹ * w = g * (y * (g⁻¹ * w * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * w * g) * y) * g⁻¹ := by rw [this]
        _ = w * (g * y * g⁻¹) := by group
  have hVinv' : ∀ y ∈ V, g⁻¹ * y * g ∈ V := by
    intro y hy
    have hginv : g ^ (p - 1) = g⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hgp]
    have hVpow : ∀ n : ℕ, ∀ y ∈ V, g ^ n * y * (g ^ n)⁻¹ ∈ V := by
      intro n
      induction n with
      | zero => intro y hy; simpa using hy
      | succ n ih =>
        intro y hy
        have := hVinv _ (ih y hy)
        convert this using 1
        group
    have := hVpow (p - 1) y hy
    rwa [hginv, inv_inv] at this
  have hVfix : ∀ y ∈ V, g * y * g⁻¹ = y → y = 1 := fun y hy => hQ'fix y (hVQ' hy)
  have hmod := card_modEq_one_of_fpf hp hgp hVinv hVinv' hVfix
  have hVC : V ≤ Subgroup.centralizer ({e} : Set G) := hVQ'.trans (hQ'R.trans inf_le_right)
  have hVel : IsElemAbelian q V := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ((hVmem x).1 hx).2.1⟩
    exact ((hVmem a).1 a.2).2.2 b (hVQ' b.2)
  have hVne : V ≠ ⊥ := by
    have hQpg : IsPGroup q ↥Q' := IsPGroup.of_card hQ'card
    haveI : Nontrivial ↥Q' :=
      Finite.one_lt_card_iff_nontrivial.1 (by
        rw [hQ'card]
        exact Nat.one_lt_pow hk.ne' hq.one_lt)
    haveI : Nontrivial (Subgroup.center ↥Q') := hQpg.center_nontrivial
    have hcpg : IsPGroup q (Subgroup.center ↥Q') := hQpg.to_subgroup _
    obtain ⟨j, hj⟩ := hcpg.nontrivial_iff_card.1 inferInstance
    have hqdvd : q ∣ Nat.card (Subgroup.center ↥Q') := by
      rw [hj.2]
      exact dvd_pow_self q hj.1.ne'
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' q hqdvd
    intro hbot
    have hcV : ((c : ↥Q') : G) ∈ V := by
      refine (hVmem _).2 ⟨(c : ↥Q').2, ?_, fun y hy => ?_⟩
      · have : (c : ↥Q') ^ q = 1 := by
          have h2 : c ^ q = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
          exact congrArg Subtype.val h2
        exact congrArg Subtype.val this
      · exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 c.2) ⟨y, hy⟩).symm
    rw [hbot, Subgroup.mem_bot] at hcV
    have : c = 1 := Subtype.ext (Subtype.ext hcV)
    rw [this, orderOf_one] at hc
    exact hq.one_lt.ne hc
  have h1 : Nat.card V % p = 1 := by
    have := hmod
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt hp.one_lt] at this
    exact this
  exact hB e he he1 q hq hqp V hVC hVel hVne h1

end CFSG.HardMathSupport.Dickson.I271
