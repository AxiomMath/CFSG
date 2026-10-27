module

public import CFSG.Adapters.Involutions

public section

open Subgroup

namespace CFSG.GH74.GLS.LU.Local.Five

section Zstar

variable {M : Type} [Group M] [Finite M]

theorem exists_mem_normalizer_of_lt {p : ℕ} [Fact p.Prime] {S T : Subgroup M} (hS : IsPGroup p ↥S)
    (hTS : T ≤ S) (hne : T ≠ S) : ∃ n ∈ S, n ∉ T ∧ n ∈ normalizer (T : Set M) := by
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  have hlt : T.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hne
    apply le_antisymm hTS
    intro x hx
    have : (⟨x, hx⟩ : ↥S) ∈ T.subgroupOf S := by rw [h]; trivial
    exact this
  have hnc : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent
  have hss := hnc _ hlt
  obtain ⟨⟨n, hnS⟩, hn1, hn2⟩ := Set.exists_of_ssubset hss
  refine ⟨n, hnS, hn2, ?_⟩
  have hn1' := Subgroup.mem_normalizer_iff.mp hn1
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hyS : y ∈ S := hTS hy
    have := (hn1' ⟨y, hyS⟩).mp (by simpa [Subgroup.mem_subgroupOf] using hy)
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hy
    have hyS : y ∈ S := by
      have h1 : n * y * n⁻¹ ∈ S := hTS hy
      have h2 : n⁻¹ * (n * y * n⁻¹) * n ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hnS) h1) hnS
      simpa [mul_assoc] using h2
    have := (hn1' ⟨y, hyS⟩).mpr (by simpa [Subgroup.mem_subgroupOf] using hy)
    simpa [Subgroup.mem_subgroupOf] using this

theorem zStar_iso {z : M} (hz2 : z * z = 1) (hz1 : z ≠ 1) {T : Subgroup M} (hT : IsPGroup 2 ↥T)
    (hzT : z ∈ T) (hTc : T ≤ centralizer ({z} : Set M))
    (hTmax : ∀ P : Subgroup M, IsPGroup 2 ↥P → P ≤ centralizer ({z} : Set M) → T ≤ P → P = T)
    (hiso : ∀ g : M, g⁻¹ * z * g ∈ T → g⁻¹ * z * g = z) :
    ∀ g : M, ∃ c ∈ centralizer ({z} : Set M), ∃ k ∈ CFSG.oddCore M, g = c * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hTS⟩ := hT.exists_le_sylow
  have hST : (S : Subgroup M) ≤ T := by
    by_contra hnot
    have hne : T ≠ (S : Subgroup M) := fun h => hnot (h ▸ le_rfl)
    obtain ⟨n, hnS, hnT, hnN⟩ := exists_mem_normalizer_of_lt (p := 2) S.isPGroup' hTS hne
    have hz' : n⁻¹ * z * n ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hnN) z).mp hzT
      simpa using this
    have hcomm : n⁻¹ * z * n = z := hiso n hz'
    have hnC : n ∈ centralizer ({z} : Set M) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n * z = n * (n⁻¹ * z * n) := by rw [hcomm]
        _ = z * n := by group
    have hPS : T ⊔ zpowers n ≤ (S : Subgroup M) :=
      sup_le hTS (Subgroup.zpowers_le.mpr hnS)
    have hP2 : IsPGroup 2 ↥(T ⊔ zpowers n) := S.isPGroup'.to_le hPS
    have hPC : T ⊔ zpowers n ≤ centralizer ({z} : Set M) :=
      sup_le hTc (Subgroup.zpowers_le.mpr hnC)
    have hPT := hTmax _ hP2 hPC le_sup_left
    exact hnT (hPT ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
  have hSeq : (S : Subgroup M) = T := le_antisymm hST hTS
  have hzS : z ∈ (S : Subgroup M) := by rw [hSeq]; exact hzT
  have hz1' : (⟨z, hzS⟩ : ↥(S : Subgroup M)) ≠ 1 := by
    intro h
    exact hz1 (congrArg Subtype.val h)
  have hord : orderOf (⟨z, hzS⟩ : ↥(S : Subgroup M)) = 2 := by
    apply orderOf_eq_prime _ hz1'
    apply Subtype.ext
    simpa [pow_two] using hz2
  have hcent : (⟨z, hzS⟩ : ↥(S : Subgroup M)) ∈ Subgroup.center ↥(S : Subgroup M) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have : (s : M) ∈ centralizer ({z} : Set M) := hTc (hSeq ▸ s.2)
    exact (Subgroup.mem_centralizer_singleton_iff.mp this)
  have := (CFSG.Adapters.glauberman_zStar S ⟨z, hzS⟩ hcent hord (fun g hg => by
    exact hiso g (hSeq ▸ hg))).1
  exact this

theorem exists_max_two_subgroup (D : Subgroup M) {z : M} (hzD : z ∈ D) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) :
    ∃ T : Subgroup M, T ≤ D ∧ IsPGroup 2 ↥T ∧ z ∈ T ∧
      ∀ P : Subgroup M, P ≤ D → IsPGroup 2 ↥P → T ≤ P → P = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let zD : ↥D := ⟨z, hzD⟩
  have h2 : zD ^ 2 = 1 := by
    apply Subtype.ext; simpa [pow_two] using hz2
  have h1 : zD ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hzp : IsPGroup 2 ↥(zpowers zD) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime h2 h1]; simp
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  refine ⟨(S : Subgroup ↥D).map D.subtype, Subgroup.map_subtype_le _, S.isPGroup'.map D.subtype,
    ⟨zD, hS (Subgroup.mem_zpowers zD), rfl⟩, ?_⟩
  intro P hPD hP hTP
  have hP' : IsPGroup 2 ↥(P.subgroupOf D) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  have hSP : (S : Subgroup ↥D) ≤ P.subgroupOf D := by
    intro s hs
    rw [Subgroup.mem_subgroupOf]
    exact hTP ⟨s, hs, rfl⟩
  obtain ⟨S', hS'⟩ := hP'.exists_le_sylow
  have hcard : Nat.card ↥(S' : Subgroup ↥D) ≤ Nat.card ↥(S : Subgroup ↥D) := by
    rw [S'.card_eq_multiplicity, S.card_eq_multiplicity]
  have hSS' : (S : Subgroup ↥D) = S' :=
    Subgroup.eq_of_le_of_card_ge (hSP.trans hS') hcard
  have hPS : P.subgroupOf D = (S : Subgroup ↥D) :=
    le_antisymm (hS'.trans hSS'.symm.le) hSP
  rw [← Subgroup.map_subgroupOf_eq_of_le hPD, hPS]

theorem zStar_iso_sub {M₀ : Subgroup M} {z : M} (hzM : z ∈ M₀) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    {T : Subgroup M} (hTM : T ≤ M₀) (hT : IsPGroup 2 ↥T) (hzT : z ∈ T)
    (hTc : T ≤ centralizer ({z} : Set M))
    (hTmax : ∀ P : Subgroup M, P ≤ M₀ → IsPGroup 2 ↥P → P ≤ centralizer ({z} : Set M) →
      T ≤ P → P = T)
    (hiso : ∀ g ∈ M₀, g⁻¹ * z * g ∈ T → g⁻¹ * z * g = z) :
    ∀ m ∈ M₀, ∃ c ∈ M₀ ⊓ centralizer ({z} : Set M),
      ∃ k ∈ (CFSG.oddCore ↥M₀).map M₀.subtype, m = c * k := by
  let zM : ↥M₀ := ⟨z, hzM⟩
  have hzM2 : zM * zM = 1 := Subtype.ext hz2
  have hzM1 : zM ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have key := zStar_iso (M := ↥M₀) (z := zM) hzM2 hzM1 (T := T.subgroupOf M₀)
    (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm) (by
      rw [Subgroup.mem_subgroupOf]; exact hzT) (by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have := hTc (Subgroup.mem_subgroupOf.mp hx)
      exact Subgroup.mem_centralizer_singleton_iff.mp this) (by
      intro P' hP' hP'c hTP'
      have hPle : P'.map M₀.subtype ≤ M₀ := Subgroup.map_subtype_le _
      have hPT : P'.map M₀.subtype = T := by
        apply hTmax _ hPle (hP'.map M₀.subtype)
        · rintro _ ⟨y, hy, rfl⟩
          have := Subgroup.mem_centralizer_singleton_iff.mp (hP'c hy)
          exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
        · intro x hx
          exact ⟨⟨x, hTM hx⟩, hTP' (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
      calc P' = (P'.map M₀.subtype).comap M₀.subtype :=
            (Subgroup.comap_map_eq_self_of_injective M₀.subtype_injective P').symm
        _ = T.subgroupOf M₀ := by rw [hPT]; rfl) (by
      intro g hg
      apply Subtype.ext
      exact hiso g.1 g.2 (Subgroup.mem_subgroupOf.mp hg))
  intro m hm
  obtain ⟨c, hc, k, hk, hmck⟩ := key ⟨m, hm⟩
  have hcz := Subgroup.mem_centralizer_singleton_iff.mp hc
  exact ⟨c.1, ⟨c.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcz)⟩, k.1,
    ⟨k, hk, rfl⟩, congrArg Subtype.val hmck⟩

theorem odd_card_oddCore' (M : Type) [Group M] [Finite M] : Odd (Nat.card (CFSG.oddCore M)) := by
  have hle : CFSG.oddCore M ≤ CFSG.pPrimeCore 2 M :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  have hdvd : Nat.card (CFSG.oddCore M) ∣ Nat.card (CFSG.pPrimeCore 2 M) :=
    Subgroup.card_dvd_of_le hle
  exact Nat.coprime_two_left.mp
    (Nat.Coprime.of_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := 2) (G := M)))

end Zstar

end CFSG.GH74.GLS.LU.Local.Five
