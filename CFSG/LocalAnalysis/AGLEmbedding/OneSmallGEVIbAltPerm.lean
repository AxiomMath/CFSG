module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbAltDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltBasic
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalCoprimePreimages

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem false_of_simple_section {X Y : Type*} [Group X] [Finite X] [Group Y] {p : ℕ}
    (hp : p.Prime) {J : Subgroup X} (hJ : PerfectSectionsAltSqC p J) (ψ : ↥J →* Y)
    (hψ : Function.Surjective ψ) (B : Subgroup Y) [IsSimpleGroup B] (hBp : ⁅B, B⁆ = B)
    (hp2 : p ^ 2 ∣ Nat.card B)
    (hbig : Nat.card (alternatingGroup (Fin p) × alternatingGroup (Fin p)) < Nat.card B) :
    False := by
  set R₀ := perfectResidualOf (B.comap ψ)
  have hR₀ : R₀.map ψ = B :=
    finite_canonical_perfect_preimage_image_eq ψ hψ B (Subgroup.isPerfect_iff.mpr hBp)
  have hR₀p : ⁅R₀, R₀⁆ = R₀ :=
    Subgroup.isPerfect_iff.mp (finite_perfectResidualOf_isPerfect (B.comap ψ))
  set V := R₀.map J.subtype
  have hVJ : V ≤ J := Subgroup.map_subtype_le _
  have hVp : ⁅V, V⁆ = V := by rw [← Subgroup.map_commutator, hR₀p]
  obtain ⟨N, hN, hNi, f, hf⟩ := hJ V hVJ hVp
  have hVR : ∀ v : ↥V, ∃ r ∈ R₀, J.subtype r = v := fun v => v.2
  set ι : ↥R₀ →* ↥V := (J.subtype.comp R₀.subtype).codRestrict V fun r => ⟨r, r.2, rfl⟩
  have hι : Function.Bijective ι := by
    refine ⟨fun a b hab => ?_, ?_⟩
    · have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    · rintro ⟨_, r, hr, rfl⟩
      exact ⟨⟨r, hr⟩, rfl⟩
  let eι : ↥R₀ ≃* ↥V := MulEquiv.ofBijective ι hι
  have hψB : ∀ r : ↥R₀, ψ r ∈ B := fun r => hR₀ ▸ ⟨r, r.2, rfl⟩
  set φ₀ : ↥R₀ →* ↥B := (ψ.comp R₀.subtype).codRestrict B hψB
  set φ : ↥V →* ↥B := φ₀.comp eι.symm.toMonoidHom
  have hφ : Function.Surjective φ := by
    intro b
    have hb : (b : Y) ∈ R₀.map ψ := by rw [hR₀]; exact b.2
    obtain ⟨r, hr, hrb⟩ := hb
    refine ⟨eι ⟨r, hr⟩, ?_⟩
    change φ₀ (eι.symm (eι ⟨r, hr⟩)) = b
    rw [MulEquiv.symm_apply_apply]
    exact Subtype.ext hrb
  have hp1 : 1 < p := hp.one_lt
  have hNB : (N.map φ).Normal := Subgroup.Normal.map hN φ hφ
  rcases hNB.eq_bot_or_eq_top with hbot | htop
  ·
    have hNk : N ≤ φ.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    have h1 : φ.ker.index ∣ N.index := Subgroup.index_dvd_of_le hNk
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top] at h1
    exact hNi (hp2.trans h1)
  ·
    have hDn : (f.ker ⊓ N).Normal := Subgroup.normal_inf_normal _ _
    have hDB : ((f.ker ⊓ N).map φ).Normal := Subgroup.Normal.map hDn φ hφ
    rcases hDB.eq_bot_or_eq_top with hDbot | hDtop
    ·
      have hDk : f.ker ⊓ N ≤ φ.ker := (Subgroup.map_eq_bot_iff _).mp hDbot
      set φN := φ.comp N.subtype
      set fN := f.comp N.subtype
      have hφN : φN.range = ⊤ := by
        rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype, htop]
      have hker : fN.ker ≤ φN.ker := by
        intro n hn
        exact hDk ⟨hn, n.2⟩
      have h1 : φN.ker.index ∣ fN.ker.index := Subgroup.index_dvd_of_le hker
      rw [Subgroup.index_ker, Subgroup.index_ker, hφN, Subgroup.card_top] at h1
      have h2 := Nat.le_of_dvd Nat.card_pos h1
      have h3 : Nat.card fN.range ≤
          Nat.card (alternatingGroup (Fin p) × alternatingGroup (Fin p)) :=
        Subgroup.card_le_card_group _
      omega
    ·
      have h1 : Nat.card B ∣ Nat.card ↥(f.ker ⊓ N) := by
        have := Subgroup.card_map_dvd (f.ker ⊓ N) φ
        rwa [hDtop, Subgroup.card_top] at this
      have h2 : p ∣ Nat.card ↥(f.ker ⊓ N) :=
        ((dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hp2).trans h1
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp hf h2

theorem card_alt_prod_lt {p k : ℕ} (hp : p = 5 ∨ p = 7) (hk : 2 * p ≤ k) :
    Nat.card (alternatingGroup (Fin p) × alternatingGroup (Fin p)) <
      Nat.card (alternatingGroup (Fin k)) := by
  rw [Nat.card_prod]
  have hpk := two_mul_card_alternatingGroup_fin (n := k) (by omega)
  have hf := Nat.factorial_le hk
  rcases hp with rfl | rfl
  · have h5 := two_mul_card_alternatingGroup_fin (n := 5) (by norm_num)
    have : Nat.factorial 5 = 120 := rfl
    have : Nat.factorial (2 * 5) = 3628800 := rfl
    nlinarith
  · have h7 := two_mul_card_alternatingGroup_fin (n := 7) (by norm_num)
    have : Nat.factorial 7 = 5040 := rfl
    have : Nat.factorial (2 * 7) = 87178291200 := by decide
    nlinarith

theorem sq_dvd_card_alt {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 * p ≤ k) :
    p ^ 2 ∣ Nat.card (alternatingGroup (Fin k)) := by
  have h1 : p ^ 2 ∣ (2 * p).factorial := by
    have hpos := hp.pos
    have e : (2 * p).factorial = 2 * p * (2 * p - 1).factorial := by
      rw [show 2 * p = (2 * p - 1) + 1 by omega, Nat.factorial_succ]
      congr 1
    rw [e, pow_two]
    exact mul_dvd_mul (dvd_mul_left p 2) (Nat.dvd_factorial hpos (by omega))
  have h2 := h1.trans (Nat.factorial_dvd_factorial hk)
  have := hp.two_le
  rw [← two_mul_card_alternatingGroup_fin (by omega : 2 ≤ k)] at h2
  exact Nat.Coprime.dvd_of_dvd_mul_left
    (((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_left 2) h2

theorem not_cube_dvd_factorial {p n : ℕ} (hp : p = 5 ∨ p = 7) (hn : n < 2 * p) :
    ¬ p ^ 3 ∣ n.factorial := by
  rcases hp with rfl | rfl <;> interval_cases n <;> decide

theorem not_cube_dvd_factorial_mul {p r m : ℕ} (hp : p = 5 ∨ p = 7) (hr : r < 2 * p)
    (hm : m < 2 * p) : ¬ p ^ 3 ∣ r.factorial * m.factorial := by
  rcases hp with rfl | rfl <;> interval_cases r <;> interval_cases m <;> decide

theorem false_of_quotient_perm_C {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y} {p n : ℕ}
    (hp : p.Prime) (hp57 : p = 5 ∨ p = 7) (hJ : PerfectSectionsAltSqC p J)
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n)) (hdvd : p ^ 3 ∣ Nat.card J) : False := by
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have h1 := pow_dvd_card_quotient_pCore_two hp hp2 hdvd
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin] at h1
  have hn : 2 * p ≤ n := by
    by_contra h
    exact not_cube_dvd_factorial hp57 (by omega) h1
  have h5 : 5 ≤ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    rcases hp57 with rfl | rfl <;> omega
  have : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup h5
  exact false_of_simple_section hp hJ (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (alternatingGroup (Fin n))
    (commutator_alternatingGroup_eq_self h5) (sq_dvd_card_alt hp hp2 hn)
    (card_alt_prod_lt hp57 hn)

theorem false_of_quotient_perm_prod_C {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y}
    {p r m : ℕ} (hp : p.Prime) (hp57 : p = 5 ∨ p = 7) (hJ : PerfectSectionsAltSqC p J)
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* (Equiv.Perm (Fin r) × Equiv.Perm (Fin m)))
    (hdvd : p ^ 3 ∣ Nat.card J) : False := by
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have h1 := pow_dvd_card_quotient_pCore_two hp hp2 hdvd
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_perm,
    Nat.card_eq_fintype_card (α := Fin r), Nat.card_eq_fintype_card (α := Fin m),
    Fintype.card_fin, Fintype.card_fin] at h1
  set ψ := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
  have hs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  by_cases hr : 2 * p ≤ r
  · have h5 : 5 ≤ Nat.card (Fin r) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      rcases hp57 with rfl | rfl <;> omega
    have : IsSimpleGroup (alternatingGroup (Fin r)) := alternatingGroup.isSimpleGroup h5
    exact false_of_simple_section hp hJ ((MonoidHom.fst _ _).comp ψ)
      (Prod.fst_surjective.comp hs) (alternatingGroup (Fin r))
      (commutator_alternatingGroup_eq_self h5) (sq_dvd_card_alt hp hp2 hr)
      (card_alt_prod_lt hp57 hr)
  by_cases hm : 2 * p ≤ m
  · have h5 : 5 ≤ Nat.card (Fin m) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      rcases hp57 with rfl | rfl <;> omega
    have : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup h5
    exact false_of_simple_section hp hJ ((MonoidHom.snd _ _).comp ψ)
      (Prod.snd_surjective.comp hs) (alternatingGroup (Fin m))
      (commutator_alternatingGroup_eq_self h5) (sq_dvd_card_alt hp hp2 hm)
      (card_alt_prod_lt hp57 hm)
  exact not_cube_dvd_factorial_mul hp57 (by omega) (by omega) h1

end CFSG.AGLEmbedding
