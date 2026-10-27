module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb9
public import Certificates.Certificate22607

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem SCert.SE.ut_sq_of_a : ∀ u : UT3 F4c, u.a = 0 → u * u = 1 := by decide +kernel

theorem SCert.SE.ut_comm_of_a : ∀ u v : UT3 F4c, u.a = 0 → v.a = 0 → u * v = v * u := by
  decide +kernel

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

theorem eq_one_of_odd_of_mem_sylowXt (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) {w : D.Xt} (hodd : Odd (orderOf w))
    (hwT : w ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt)) : w = 1 := by
  obtain ⟨k, hk⟩ := (D.sylowXt hO hz).isPGroup' ⟨w, hwT⟩
  have hk' : w ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  rcases b with _ | b
  · rwa [pow_zero, orderOf_eq_one_iff] at hb
  · rw [hb] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, b.succ_ne_zero⟩))

noncomputable abbrev imX (s₀ : SE) (hs : s₀.d.val < 4) : D.Xt :=
  D.piX ⟨D.toG s₀, D.S1_le_Y1 (D.toG_mem_S1 hs)⟩

omit [Finite Y] in
theorem imX_mul (s₀ t₀ : SE) (hs : s₀.d.val < 4) (ht : t₀.d.val < 4)
    (hst : (s₀ * t₀).d.val < 4) :
    D.imX s₀ hs * D.imX t₀ ht = D.imX (s₀ * t₀) hst := by
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  show D.toG s₀ * D.toG t₀ = D.toG (s₀ * t₀)
  rw [map_mul]

omit [Finite Y] in
theorem imX_inv (s₀ : SE) (hs : s₀.d.val < 4) (hs' : (s₀⁻¹).d.val < 4) :
    (D.imX s₀ hs)⁻¹ = D.imX s₀⁻¹ hs' := by
  rw [← map_inv]
  congr 1
  apply Subtype.ext
  show (D.toG s₀)⁻¹ = D.toG s₀⁻¹
  rw [map_inv]

theorem imX_mem_Et_iff (s₀ : SE) (hs : s₀.d.val < 4) : D.imX s₀ hs ∈ D.Et ↔ SE.predE s₀ :=
  (D.piX_mem_Et_iff _).trans D.toG_mem_E_iff

theorem Ft_sq (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    ∀ f ∈ D.Ft, f * f = 1 := by
  intro f hf
  have hfT := D.Ft_le hO hz hf
  have h := (D.mem_Ft_iff_tUT hO hz hfT).mp hf
  have h2 : D.tUT hO hz (⟨f, hfT⟩ * ⟨f, hfT⟩) = 1 := by
    rw [map_mul]
    exact SE.ut_sq_of_a _ h
  have := (D.tUT hO hz).injective (h2.trans (map_one _).symm)
  exact congrArg Subtype.val this

theorem Ft_comm (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    ∀ f ∈ D.Ft, ∀ g ∈ D.Ft, f * g = g * f := by
  intro f hf g hg
  have hfT := D.Ft_le hO hz hf
  have hgT := D.Ft_le hO hz hg
  have h1 := (D.mem_Ft_iff_tUT hO hz hfT).mp hf
  have h2 := (D.mem_Ft_iff_tUT hO hz hgT).mp hg
  have h3 : D.tUT hO hz (⟨f, hfT⟩ * ⟨g, hgT⟩) = D.tUT hO hz (⟨g, hgT⟩ * ⟨f, hfT⟩) := by
    rw [map_mul, map_mul]
    exact SE.ut_comm_of_a _ _ h1 h2
  have := (D.tUT hO hz).injective h3
  exact congrArg Subtype.val this

theorem not_iso_Z3A5
    (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y)
    (hEt : pCore 2 D.Xt = D.Et) (hC0 : centralizer (pCore 2 D.Xt : Set D.Xt) ≤ pCore 2 D.Xt) :
    letI : (pCore 2 D.Xt).Normal := pCore_normal
    IsEmpty (D.Xt ⧸ pCore 2 D.Xt ≃* K3A5.K) := by
  let _ : (pCore 2 D.Xt).Normal := pCore_normal
  refine ⟨fun e => ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T := ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) with hT
  set φ : D.Xt →* K3A5.K := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D.Xt)) with hφ
  have hker : ∀ w, φ w = 1 ↔ w ∈ D.Et := by
    intro w
    rw [← hEt, ← QuotientGroup.eq_one_iff (N := pCore 2 D.Xt)]
    exact ⟨fun h => e.injective (by rw [map_one]; exact h), fun h => by
      change e (QuotientGroup.mk' _ w) = 1
      rw [QuotientGroup.mk'_apply, h, map_one]⟩
  have hsurj : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hEtn : D.Et.Normal := hEt ▸ (pCore_normal : (pCore 2 D.Xt).Normal)
  have hφeq : ∀ v w : D.Xt, φ v = φ w ↔ v⁻¹ * w ∈ D.Et := by
    intro v w
    rw [← hker, map_mul, map_inv]
    exact inv_mul_eq_one.symm
  have h6 : (SE.gen 6).d.val < 4 := by decide
  have h7 : (SE.gen 7).d.val < 4 := by decide
  set a := φ (D.imX (SE.gen 6) h6) with ha
  set b := φ (D.imX (SE.gen 7) h7) with hb
  have hFP : K3A5.FourPair a b := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha, ← map_mul φ, D.imX_mul _ _ _ _ (by decide)]
      exact (hker _).mpr ((D.imX_mem_Et_iff _ _).mpr (by decide))
    · rw [hb, ← map_mul φ, D.imX_mul _ _ _ _ (by decide)]
      exact (hker _).mpr ((D.imX_mem_Et_iff _ _).mpr (by decide))
    · intro h
      exact absurd ((D.imX_mem_Et_iff _ _).mp ((hker _).mp h)) (by decide)
    · intro h
      exact absurd ((D.imX_mem_Et_iff _ _).mp ((hker _).mp h)) (by decide)
    · intro h
      have h' := (hφeq _ _).mp h
      rw [D.imX_inv _ _ (by decide), D.imX_mul _ _ _ _ (by decide)] at h'
      exact absurd ((D.imX_mem_Et_iff _ _).mp h') (by decide)
    · rw [ha, hb, ← map_mul φ, ← map_mul φ, hφeq, D.imX_mul _ _ _ _ (by decide),
        D.imX_mul _ _ _ _ (by decide), D.imX_inv _ _ (by decide), D.imX_mul _ _ _ _ (by decide)]
      exact (D.imX_mem_Et_iff _ _).mpr (by decide)
  have h36 := Certificates.certificate22607 a b hFP
  set V := T.map φ with hV
  have hxT : D.imX (SE.gen 6) h6 ∈ T :=
    D.mem_sylowXt hO hz ⟨_, mem_subgroupOf.mpr (D.toG_mem_S1 h6)⟩
  have hyT : D.imX (SE.gen 7) h7 ∈ T :=
    D.mem_sylowXt hO hz ⟨_, mem_subgroupOf.mpr (D.toG_mem_S1 h7)⟩
  have hVmem : ∀ k, k ∈ V ↔ k = 1 ∨ k = a ∨ k = b ∨ k = a * b := by
    intro k
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      rcases D.image_T_cases hO hz hτ with h | h | h | h
      · left; exact (hker τ).mpr h
      · right; left
        have h' := (hker _).mpr h
        rw [map_mul, map_inv] at h'
        exact mul_inv_eq_one.mp h'
      · right; right; left
        have h' := (hker _).mpr h
        rw [map_mul, map_inv] at h'
        exact mul_inv_eq_one.mp h'
      · right; right; right
        have h' := (hker _).mpr h
        rw [map_mul, map_inv] at h'
        rw [← map_mul]
        exact mul_inv_eq_one.mp h'
    · rintro (rfl | rfl | rfl | rfl)
      · exact one_mem _
      · exact ⟨_, hxT, rfl⟩
      · exact ⟨_, hyT, rfl⟩
      · exact ⟨_, mul_mem hxT hyT, map_mul _ _ _⟩
  set NV := normalizer (V : Set K3A5.K) with hNV
  have hconjV : ∀ k : K3A5.K, k * a * k⁻¹ ∈ V → k * b * k⁻¹ ∈ V → ∀ h ∈ V, k * h * k⁻¹ ∈ V := by
    intro k hka hkb h hh
    rcases (hVmem h).mp hh with rfl | rfl | rfl | rfl
    · simp
    · exact hka
    · exact hkb
    · rw [show k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) by group]
      exact mul_mem hka hkb
  have hNVmem : ∀ k, k ∈ NV ↔ (k * a * k⁻¹ ∈ V ∧ k * b * k⁻¹ ∈ V) := by
    intro k
    constructor
    · intro hk
      exact ⟨(mem_normalizer_iff.mp hk a).mp ((hVmem a).mpr (Or.inr (Or.inl rfl))),
        (mem_normalizer_iff.mp hk b).mp ((hVmem b).mpr (Or.inr (Or.inr (Or.inl rfl))))⟩
    · rintro ⟨hka, hkb⟩
      rw [mem_normalizer_iff]
      intro h
      refine ⟨hconjV k hka hkb h, fun hh => ?_⟩
      obtain ⟨x, hx, hxh⟩ := GHSylow.exists_conj_eq_of_maps (H := V) (k := k⁻¹)
        (fun x hx => by rw [inv_inv]; exact hconjV k hka hkb x hx) _ hh
      rw [inv_inv] at hxh
      have : x = h := by simpa using hxh
      rwa [← this]
  have hcardNV : Nat.card NV = 36 := by
    rw [← h36, K3A5.nCard, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [← hVmem, ← hVmem]
    exact hNVmem k
  set Q := NV.comap φ with hQ
  have hQ36 : 36 ∣ Nat.card Q := by
    rw [← hcardNV, ← map_comap_eq_self_of_surjective hsurj NV]
    exact card_map_dvd _ _
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 3 Q))
  set P := (P₀ : Subgroup Q).map Q.subtype with hP
  have hP9 : 9 ∣ Nat.card P := by
    rw [hP, card_map_of_injective Q.subtype_injective]
    exact Sylow.pow_dvd_card_of_pow_dvd_card (n := 2) P₀ (dvd_trans (by norm_num) hQ36)
  have hPQ : P ≤ Q := map_subtype_le _
  have hPT : ∀ w ∈ P, ∀ τ ∈ T, w * τ * w⁻¹ ∈ T := by
    intro w hw τ hτ
    have hwN : φ w ∈ NV := hPQ hw
    have h1 : φ (w * τ * w⁻¹) ∈ V := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hwN (φ τ)).mp ⟨τ, hτ, rfl⟩
    obtain ⟨τ', hτ', hτ'e⟩ := h1
    have h2 : τ'⁻¹ * (w * τ * w⁻¹) ∈ T := D.Et_le hO hz ((hφeq _ _).mp hτ'e)
    have := mul_mem hτ' h2
    rwa [mul_inv_cancel_left] at this
  have hPE : ∀ w ∈ P, ∀ e ∈ D.Et, w * e * w⁻¹ ∈ D.Et := fun w _ e he => hEtn.conj_mem e he w
  have hPF : ∀ w ∈ P, ∀ f ∈ D.Ft, w * f * w⁻¹ ∈ D.Ft := by
    intro w hw f hf
    set B := D.Ft.map (MulAut.conj w).toMonoidHom with hB
    have hBT : B ≤ T := by
      rintro _ ⟨g, hg, rfl⟩
      exact hPT w hw g (D.Ft_le hO hz hg)
    have hB2 : ∀ c ∈ B, c * c = 1 := by
      rintro _ ⟨g, hg, rfl⟩
      rw [← map_mul, D.Ft_sq hO hz g hg, map_one]
    have hBc : ∀ c ∈ B, ∀ d ∈ B, c * d = d * c := by
      rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      rw [← map_mul, ← map_mul, D.Ft_comm hO hz g hg g' hg']
    have hB16 : Nat.card B = 16 := by
      rw [hB, card_map_of_injective (MulAut.conj w).injective, (D.card_Et_Ft hO hz).2]
    have hxE : D.xX ∉ D.Et := fun h =>
      absurd (D.toG_mem_E_iff.mp ((D.piX_mem_Et_iff _).mp h)) (by decide)
    rcases D.eq_Et_or_Ft hO hz hBT hB2 hBc hB16 with h | h
    · exfalso
      have h1 : w * D.xX * w⁻¹ ∈ D.Et := h ▸ ⟨D.xX, D.xX_mem_Ft, rfl⟩
      have h2 := hEtn.conj_mem _ h1 w⁻¹
      rw [show w⁻¹ * (w * D.xX * w⁻¹) * w⁻¹⁻¹ = D.xX by group] at h2
      exact hxE h2
    · exact h ▸ ⟨f, hf, rfl⟩
  obtain ⟨w, hwP, hw1, hwZ⟩ := D.exists_centralizes_ZT hO hz hP9 hPE hPF
  have hodd : Odd (orderOf w) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (P₀.isPGroup'.map Q.subtype)) ⟨w, hwP⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    exact Odd.pow (by decide)
  have hwE := D.centralizes_Et hodd hwZ (fun e he => hEtn.conj_mem e he w)
  have hwC : w ∈ pCore 2 D.Xt := hC0 (mem_centralizer_iff.mpr fun h hh => by
    rw [hEt] at hh
    exact (hwE h hh).symm)
  rw [hEt] at hwC
  exact hw1 (D.eq_one_of_odd_of_mem_sylowXt hO hz hodd (D.Et_le hO hz hwC))

end GHSylow

end CFSG.ComponentClassification.GHarris
