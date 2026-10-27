module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem not_dvd_card_center_of_perfect {R : Type*} [Group R] [Finite R] {p : ℕ}
    [hp : Fact p.Prime] (hR : commutator R = ⊤) (hp2 : ¬ p ^ 2 ∣ Nat.card R) :
    ¬ p ∣ Nat.card (Subgroup.center R) := by
  intro hpZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R) p hpZ
  set C : Subgroup R := Subgroup.zpowers (z : R)
  have hzo : orderOf (z : R) = p := by rw [Subgroup.orderOf_coe, hz]
  have hCcard : Nat.card C = p := by rw [Nat.card_zpowers, hzo]
  have hC : IsPGroup p C := IsPGroup.of_card (n := 1) (by rw [hCcard, pow_one])
  obtain ⟨P, hCP⟩ := hC.exists_le_sylow
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hk1 : k ≤ 1 := by
    by_contra h
    exact hp2 (dvd_trans (pow_dvd_pow p (by omega))
      (hk ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup R)))
  have hPC : (P : Subgroup R) = C := by
    refine (Subgroup.eq_of_le_of_card_ge hCP ?_).symm
    rw [hk, hCcard]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos hk1
      _ = p := pow_one p
  have hPZ : (P : Subgroup R) ≤ Subgroup.center R := by
    rw [hPC, Subgroup.zpowers_le]
    exact z.2
  have hPn : Subgroup.normalizer (P : Subgroup R) ≤ Subgroup.centralizer (P : Set R) :=
    fun g _ x hx => ((Subgroup.mem_center_iff.mp (hPZ hx)) g).symm
  have hker : (MonoidHom.transferSylow P hPn).ker = ⊤ := by
    rw [eq_top_iff, ← hR, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    apply Subtype.ext
    have hab : ((MonoidHom.transferSylow P hPn a : P) : R) *
        ((MonoidHom.transferSylow P hPn b : P) : R) =
        ((MonoidHom.transferSylow P hPn b : P) : R) *
        ((MonoidHom.transferSylow P hPn a : P) : R) :=
      (Subgroup.mem_center_iff.mp (hPZ (MonoidHom.transferSylow P hPn b).2) _)
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [hab]; group
  have := MonoidHom.not_dvd_card_ker_transferSylow P hPn
  rw [hker, Subgroup.card_top] at this
  exact this (hpZ.trans (Subgroup.card_subgroup_dvd_card _))

theorem not_sq_dvd_card_alternatingGroup_prime {p : ℕ} (hp : p.Prime) :
    ¬ p ^ 2 ∣ Nat.card (alternatingGroup (Fin p)) := by
  intro h
  have : Nontrivial (Fin p) := Fin.nontrivial_iff_two_le.mpr hp.two_le
  have hAc := two_mul_nat_card_alternatingGroup (α := Fin p)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at hAc
  have h1 : p ^ 2 ∣ p.factorial := hAc ▸ dvd_mul_of_dvd_right h 2
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  rw [hm, Nat.factorial_succ, ← hm, sq] at h1
  have h2 : p ∣ (p - 1).factorial := by
    have := Nat.dvd_of_mul_dvd_mul_left hp.pos h1
    simpa [hm] using this
  rw [hp.dvd_factorial] at h2
  have := hp.two_le
  omega

theorem false_of_central_of_hom_alternating {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hX : commutator X = ⊤) (g : X →* alternatingGroup (Fin p)) {k : X}
    (hk : k ∈ Subgroup.center X) (hgk : g k ≠ 1) (hgkp : g k ^ p = 1) : False := by
  have hR : commutator ↥g.range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨_, ⟨x, rfl⟩⟩ _
    have hx : x ∈ commutator X := hX ▸ Subgroup.mem_top x
    have hle : (commutator X).map g.rangeRestrict ≤ commutator ↥g.range := by
      rw [commutator_def, commutator_def (G := ↥g.range), Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact hle (Subgroup.mem_map_of_mem _ hx)
  have hp2 : ¬ p ^ 2 ∣ Nat.card g.range := fun h =>
    not_sq_dvd_card_alternatingGroup_prime hp.out (h.trans (Subgroup.card_subgroup_dvd_card _))
  apply not_dvd_card_center_of_perfect hR hp2
  have hc : (⟨g k, k, rfl⟩ : ↥g.range) ∈ Subgroup.center ↥g.range := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, ⟨x, rfl⟩⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hk x)]
  have hord : orderOf (⟨g k, k, rfl⟩ : ↥g.range) = p := by
    apply orderOf_eq_prime
    · exact Subtype.ext (by simpa using hgkp)
    · intro h
      exact hgk (congrArg Subtype.val h)
  have h1 := orderOf_dvd_natCard (⟨_, hc⟩ : Subgroup.center ↥g.range)
  rwa [← Subgroup.orderOf_coe, hord] at h1

theorem not_sq_dvd_mul_of {p a b : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (hb : ¬ p ^ 2 ∣ b) :
    ¬ p ^ 2 ∣ b * a := fun h =>
  hb (Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha)) h)

theorem commutator_eq_self_of_open_isQuasisimple {Y : Type*} [Group Y] {X : Subgroup Y}
    (h : Open.IsQuasisimple ↥X) : ⁅X, X⁆ = X := by
  have h1 : (commutator ↥X).map X.subtype = ⁅X, X⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← h1, h.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem not_sq_dvd_card_of_quasisimple_of_altSqC {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) {J : Subgroup Y} (hJ : PerfectSectionsAltSqC p J) {X : Subgroup Y}
    (hXJ : X ≤ J) (hX : Open.IsQuasisimple ↥X) : ¬ p ^ 2 ∣ Nat.card X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨N, hN, hNi, f, hf⟩ := hJ X hXJ (commutator_eq_self_of_open_isQuasisimple hX)
  have hcen : ∀ k ∈ Subgroup.center ↥X, k ^ p = 1 → f k ≠ 1 → False := by
    intro k hk hkp hfk
    by_cases h1 : (f k).1 = 1
    · have h2 : (f k).2 ≠ 1 := fun h2 => hfk (Prod.ext h1 h2)
      exact false_of_central_of_hom_alternating hX.1 ((MonoidHom.snd _ _).comp f) hk h2
        (by rw [← map_pow, hkp, map_one])
    · exact false_of_central_of_hom_alternating hX.1 ((MonoidHom.fst _ _).comp f) hk h1
        (by rw [← map_pow, hkp, map_one])
  have hkerN : ∀ k : ↥X, k ∈ f.ker ⊓ N → orderOf k = p → False := by
    intro k hk hko
    have h1 := orderOf_dvd_natCard (⟨k, hk⟩ : ↥(f.ker ⊓ N))
    rw [Subgroup.orderOf_mk, hko] at h1
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hf h1)
  have hcentral : ∀ K : Subgroup ↥X, K ≤ Subgroup.center ↥X → (K ≤ N ∨ N = ⊤) →
      ¬ p ∣ Nat.card K := by
    intro K hKZ hKN hd
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) p hd
    have hko : orderOf (k : ↥X) = p := by rw [Subgroup.orderOf_coe, hk]
    have hkp : (k : ↥X) ^ p = 1 := by rw [← hko, pow_orderOf_eq_one]
    by_cases hfk : f k = 1
    · refine hkerN k ⟨hfk, ?_⟩ hko
      rcases hKN with hKN | hNt
      · exact hKN k.2
      · rw [hNt]; exact Subgroup.mem_top _
    · exact hcen k (hKZ k.2) hkp hfk
  rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hX N with hNZ | hNt
  · rw [← Subgroup.index_mul_card N]
    exact not_sq_dvd_mul_of hp (hcentral N hNZ (Or.inl le_rfl)) hNi
  · set g := (MonoidHom.fst _ _).comp f
    rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hX g.ker with hK | hK
    · rw [← Subgroup.index_mul_card g.ker, Subgroup.index_ker]
      exact not_sq_dvd_mul_of hp (hcentral g.ker hK (Or.inr hNt))
        (fun h2 => not_sq_dvd_card_alternatingGroup_prime hp
          (h2.trans (Subgroup.card_subgroup_dvd_card _)))
    · set h := (MonoidHom.snd _ _).comp f
      have hfh : f.ker = h.ker := by
        ext x
        simp only [MonoidHom.mem_ker]
        have hx1 : (f x).1 = 1 := by
          have : x ∈ g.ker := hK ▸ Subgroup.mem_top x
          exact this
        constructor
        · intro hx; rw [show h x = (f x).2 from rfl, hx]; rfl
        · intro hx; exact Prod.ext hx1 hx
      rw [← Subgroup.index_mul_card h.ker, Subgroup.index_ker, ← hfh]
      refine not_sq_dvd_mul_of hp ?_ (fun h2 => not_sq_dvd_card_alternatingGroup_prime hp
        (h2.trans (Subgroup.card_subgroup_dvd_card _)))
      intro hd
      have h1 := hf
      rw [hNt, inf_top_eq] at h1
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h1 hd)

theorem exists_hom_alternating_of_altSq {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    {J : Subgroup Y} (hJ : PerfectSectionsAltSq p J) {X : Subgroup Y} (hXJ : X ≤ J)
    (hX : Open.IsQuasisimple ↥X) (hpX : p ∣ Nat.card X) (hp : p.Prime) :
    ∃ φ : ↥X →* alternatingGroup (Fin p), φ.ker ≤ Subgroup.center ↥X := by
  obtain ⟨V₀, hV₀X, -, hV₀p, f, hf⟩ := hJ X hXJ (commutator_eq_self_of_open_isQuasisimple hX)
  have hfZ : f.ker ≤ Subgroup.center ↥X := by
    rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hX f.ker with h | h
    · exact h
    · exfalso
      have hXV : X ≤ V₀ := by
        intro x hx
        have : (⟨x, hx⟩ : ↥X) ∈ f.ker := h ▸ Subgroup.mem_top _
        rw [hf] at this
        exact this
      have := Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXV) hV₀p
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hpX)
  set g₁ := (MonoidHom.fst _ _).comp f
  rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hX g₁.ker with h | h
  · exact ⟨g₁, h⟩
  · refine ⟨(MonoidHom.snd _ _).comp f, fun x hx => hfZ ?_⟩
    have h1 : (f x).1 = 1 := by
      have : x ∈ g₁.ker := h ▸ Subgroup.mem_top x
      exact this
    exact Prod.ext h1 hx

theorem pow_three_dvd_card_quotient_pCore {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup Y} (hEJ : E ≤ J)
    (hE : Nat.card E = p ^ 3) : p ^ 3 ∣ Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) := by
  have h1 : p ^ 3 ∣ Nat.card J := hE ▸ Subgroup.card_dvd_of_le hEJ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥J)] at h1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥J))
  rw [hk] at h1
  exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow 3 k
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)) h1

end CFSG.AGLEmbedding
