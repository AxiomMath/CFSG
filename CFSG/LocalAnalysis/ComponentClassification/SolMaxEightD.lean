module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36V

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem odd_orderOf_of_rho_eq_one [Finite X] {M : Subgroup X}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) {m : X} (hm : m ∈ M)
    (h1 : ρ ⟨m, le_normalizer hm⟩ = 1) : Odd (orderOf m) := by
  have h2 := hρ.apply_of_mem (by norm_num) ⟨m, hm⟩
  rw [h1] at h2
  have h3 : θ ((⟨m, hm⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := Subtype.ext h2.symm
  rw [map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff] at h3
  have h4 : orderOf (⟨⟨m, hm⟩, h3⟩ : ↥(pPrimeCore 2 ↥M)) ∣ Nat.card (pPrimeCore 2 ↥M) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h4
  rcases Nat.even_or_odd (orderOf m) with he | ho
  · exact absurd ((even_iff_two_dvd.mp he).trans h4)
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mp pPrimeCore_coprime_card)
  · exact ho

theorem odd_card_of_forall_mem_odd_orderOf [Finite X] {N : Subgroup X}
    (h : ∀ n ∈ N, Odd (orderOf n)) : Odd (Nat.card N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.even_or_odd (Nat.card N) with he | ho
  · obtain ⟨⟨n, hn⟩, hn2⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp he)
    rw [Subgroup.orderOf_mk] at hn2
    have := h n hn
    rw [hn2] at this
    exact absurd this (by decide)
  · exact ho

theorem zmodTwo_eq_one_or_eq_ofAdd_one (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  revert x
  decide

theorem exists_surjective_alt_prod_two [Finite X] {M H : Subgroup X}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ)
    (hMH : M ≤ H) (hHN : H ≤ normalizer (M : Set X))
    (hev : ∀ (h : X) (hh : h ∈ H), ρ ⟨h, hHN hh⟩ ∈ alternatingGroup (Fin 9))
    {t : X} (htH : t ∈ H) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htK : t ∈ UnbalancedLayer.coreActionKernel M)
    (hK2 : ∀ P : Subgroup X, P ≤ H ⊓ UnbalancedLayer.coreActionKernel M → IsPGroup 2 P →
      Nat.card P ≤ 2) :
    ∃ φ : ↥H →* alternatingGroup (Fin 9) × Multiplicative (ZMod 2), Function.Surjective φ ∧
      Odd (Nat.card φ.ker) ∧ φ ⟨t, htH⟩ = (1, Multiplicative.ofAdd 1) ∧
      ∀ (x : X) (hx : x ∈ H), ((φ ⟨x, hx⟩).1 : Perm (Fin 9)) = ρ ⟨x, hHN hx⟩ := by
  classical
  set K := H ⊓ UnbalancedLayer.coreActionKernel M with hKdef
  obtain ⟨N, hNK, hNodd, hNt⟩ := exists_oddPart_of_card_le_two (K := K) ⟨htH, htK⟩ ht2 ht1 hK2
  have ht2o : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have hsurjM : ∀ a : alternatingGroup (Fin 9), ∃ (m : X) (hm : m ∈ M),
      ρ ⟨m, hHN (hMH hm)⟩ = (a : Perm (Fin 9)) := by
    intro a
    obtain ⟨q, rfl⟩ := θ.surjective a
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨m, hm, hρ.apply_of_mem (by norm_num) ⟨m, hm⟩⟩
  have hρK : ∀ k ∈ K, ∀ hk : k ∈ normalizer (M : Set X), ρ ⟨k, hk⟩ = 1 := fun k hk _ =>
    hρ.eq_one_of_mem_coreActionKernel (by norm_num) hk.2
  have hKmem : ∀ (k : X) (hk : k ∈ H), ρ ⟨k, hHN hk⟩ = 1 → k ∈ K := fun k hk h1 =>
    ⟨hk, hρ.mem_coreActionKernel (hHN hk) h1⟩
  have hMN : ∀ m ∈ M, m ∈ K → m ∈ N := fun m hm hmK =>
    (hNodd m hmK).mpr (odd_orderOf_of_rho_eq_one hρ hm (hρK m hmK _))
  have hNconj : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    have hnK := hNK hn
    have hcK : h * n * h⁻¹ ∈ K := Subgroup.mem_inf.mpr
      ⟨H.mul_mem (H.mul_mem hh (Subgroup.mem_inf.mp hnK).1) (H.inv_mem hh),
        hρ.conj_mem_coreActionKernel (by norm_num) (hHN hh) (Subgroup.mem_inf.mp hnK).2⟩
    refine (hNodd _ hcK).mpr ?_
    have h1 : orderOf (h * n * h⁻¹) = orderOf n := by
      have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective n
      simpa using this
    rw [h1]
    exact (hNodd n hnK).mp hn
  set N' : Subgroup ↥H := N.subgroupOf H with hN'def
  set M' : Subgroup ↥H := M.subgroupOf H with hM'def
  have hN'n : N'.Normal := ⟨fun n hn h => by
    change ((h * n * h⁻¹ : ↥H) : X) ∈ N
    exact hNconj h h.2 n hn⟩
  have hM'n : M'.Normal := ⟨fun m hm h => by
    change ((h * m * h⁻¹ : ↥H) : X) ∈ M
    exact (mem_normalizer_iff.mp (hHN h.2) m).mp hm⟩
  set L : Subgroup ↥H := M' ⊔ N' with hLdef
  have hLmul : ∀ x : ↥H, x ∈ L ↔ ∃ m ∈ M', ∃ n ∈ N', m * n = x := by
    intro x
    rw [← SetLike.mem_coe, hLdef, Subgroup.mul_normal M' N']
    exact Set.mem_mul
  set t' : ↥H := ⟨t, htH⟩ with ht'def
  have hL : ∀ h : ↥H, h ∈ L ∨ h * t' ∈ L := by
    intro h
    obtain ⟨m, hm, hmh⟩ := hsurjM ⟨ρ ⟨h, hHN h.2⟩, hev h h.2⟩
    set k : X := m⁻¹ * h with hkdef
    have hkH : k ∈ H := mul_mem (inv_mem (hMH hm)) h.2
    have hkK : k ∈ K := by
      refine hKmem k hkH ?_
      have h1 : (⟨k, hHN hkH⟩ : ↥(normalizer (M : Set X))) =
          (⟨m, hHN (hMH hm)⟩)⁻¹ * ⟨h, hHN h.2⟩ := rfl
      rw [h1, map_mul, map_inv, hmh, inv_mul_cancel]
    have hmM' : (⟨m, hMH hm⟩ : ↥H) ∈ M' := hm
    rcases hNt k hkK with hkN | hktN
    · left
      refine (hLmul h).mpr ⟨⟨m, hMH hm⟩, hmM', ⟨k, hkH⟩, hkN, Subtype.ext ?_⟩
      change m * (m⁻¹ * h) = h
      group
    · right
      refine (hLmul _).mpr ⟨⟨m, hMH hm⟩, hmM', ⟨k * t, mul_mem hkH htH⟩, hktN, Subtype.ext ?_⟩
      change m * (m⁻¹ * h * t) = h * t
      group
  have ht'L : t' ∉ L := by
    intro htL
    obtain ⟨⟨m, hmH⟩, hm, ⟨n, hnH⟩, hn, hmn⟩ := (hLmul t').mp htL
    have hmn' : m * n = t := congrArg Subtype.val hmn
    have hm' : m ∈ M := hm
    have hn' : n ∈ N := hn
    have hmK : m ∈ K := by
      have h1 : m = t * n⁻¹ := by rw [← hmn']; group
      rw [h1]
      exact mul_mem ⟨htH, htK⟩ (inv_mem (hNK hn'))
    have htN : t ∈ N := by rw [← hmn']; exact mul_mem (hMN m hm' hmK) hn'
    have := (hNodd t ⟨htH, htK⟩).mp htN
    rw [ht2o] at this
    exact absurd this (by decide)
  have hLidx : L.index = 2 := by
    refine Subgroup.index_eq_two_iff.mpr ⟨t', fun b => ?_⟩
    rcases hL b with hb | hb
    · refine Or.inr ⟨hb, fun hbt => ht'L ?_⟩
      have h1 := mul_mem (inv_mem hb) hbt
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1
    · refine Or.inl ⟨hb, fun hb' => ht'L ?_⟩
      have h1 := mul_mem (inv_mem hb') hb
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1
  have hcardQ : Nat.card (↥H ⧸ L) = 2 := by rw [← Subgroup.index]; exact hLidx
  have hcard2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]; rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ε : ↥H ⧸ L ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hcardQ hcard2
  let φ₂ : ↥H →* Multiplicative (ZMod 2) := ε.toMonoidHom.comp (QuotientGroup.mk' L)
  have hφ₂ : ∀ h : ↥H, φ₂ h = 1 ↔ h ∈ L := by
    intro h
    change ε (h : ↥H ⧸ L) = 1 ↔ h ∈ L
    rw [map_eq_one_iff _ ε.injective, QuotientGroup.eq_one_iff]
  have hz2 := zmodTwo_eq_one_or_eq_ofAdd_one
  have hφ₂t : φ₂ t' = Multiplicative.ofAdd 1 :=
    (hz2 _).resolve_left fun h => ht'L ((hφ₂ t').mp h)
  let φ₁ : ↥H →* alternatingGroup (Fin 9) :=
    (ρ.comp (Subgroup.inclusion hHN)).codRestrict (alternatingGroup (Fin 9))
      fun h => hev h h.2
  have hφ₁ : ∀ h : ↥H, ((φ₁ h : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
      ρ ⟨h, hHN h.2⟩ := fun _ => rfl
  have hφ₁t : φ₁ t' = 1 := Subtype.ext (by rw [hφ₁]; exact hρK t ⟨htH, htK⟩ _)
  refine ⟨φ₁.prod φ₂, ?_, ?_, ?_, fun x hx => rfl⟩
  ·
    rintro ⟨a, z⟩
    obtain ⟨m, hm, hma⟩ := hsurjM a
    have hm1 : φ₁ ⟨m, hMH hm⟩ = a := Subtype.ext (by rw [hφ₁]; exact hma)
    have hm2 : φ₂ ⟨m, hMH hm⟩ = 1 := (hφ₂ _).mpr (mem_sup_left (show _ ∈ M' from hm))
    rcases hz2 z with rfl | rfl
    · exact ⟨⟨m, hMH hm⟩, Prod.ext hm1 hm2⟩
    · refine ⟨⟨m, hMH hm⟩ * t', Prod.ext ?_ ?_⟩
      · change φ₁ (⟨m, hMH hm⟩ * t') = a
        rw [map_mul, hm1, hφ₁t, mul_one]
      · change φ₂ (⟨m, hMH hm⟩ * t') = Multiplicative.ofAdd 1
        rw [map_mul, hm2, hφ₂t, one_mul]
  ·
    have hker : (φ₁.prod φ₂).ker ≤ N' := by
      intro h hh
      have hh' : φ₁ h = 1 ∧ φ₂ h = 1 := Prod.ext_iff.mp hh
      obtain ⟨⟨m, hmH⟩, hm, ⟨n, hnH⟩, hn, hmn⟩ := (hLmul h).mp ((hφ₂ h).mp hh'.2)
      have hmn' : m * n = (h : X) := congrArg Subtype.val hmn
      have hm' : m ∈ M := hm
      have hn' : n ∈ N := hn
      have hρh : ρ ⟨h, hHN h.2⟩ = 1 := by
        have := congrArg Subtype.val hh'.1
        rwa [hφ₁] at this
      have hmK : m ∈ K := by
        refine hKmem m hmH ?_
        have h1 : (⟨m, hHN hmH⟩ : ↥(normalizer (M : Set X))) =
            ⟨h, hHN h.2⟩ * (⟨n, hHN hnH⟩)⁻¹ := Subtype.ext (by
              change m = (h : X) * n⁻¹
              rw [← hmn']; group)
        rw [h1, map_mul, map_inv, hρh, hρK n (hNK hn') _, inv_one, one_mul]
      change (h : X) ∈ N
      rw [← hmn']
      exact mul_mem (hMN m hm' hmK) hn'
    have hN'odd : Odd (Nat.card N') := by
      have h2 : Odd (Nat.card N) := odd_card_of_forall_mem_odd_orderOf fun n hn =>
        (hNodd n (hNK hn)).mp hn
      have h3 : Nat.card N' = Nat.card N := by
        rw [hN'def]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNK.trans inf_le_left)).toEquiv
      rw [h3]
      exact h2
    have hdvd : Nat.card (φ₁.prod φ₂).ker ∣ Nat.card N' := Subgroup.card_dvd_of_le hker
    exact Odd.of_dvd_nat hN'odd hdvd
  · exact Prod.ext hφ₁t hφ₂t

end CFSG.ComponentClassification.SolMax
