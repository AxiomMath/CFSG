module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxA
public import Certificates.Certificate22300

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace FixL34

open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem tabRep_sqT {t : Tab} {g : Equiv.Perm (Fin 42)} (ht : TabRep t g) :
    TabRep (sqT t) (g ^ 2) := by
  rw [pow_two]
  exact ht.comp ht

theorem tabRep_pow256T {t : Tab} {g : Equiv.Perm (Fin 42)} (ht : TabRep t g) :
    TabRep (pow256T t) (g ^ 256) := by
  have h : g ^ 256 = ((((((((g ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) := by
    simp only [← pow_mul]
  rw [h]
  exact tabRep_sqT (tabRep_sqT (tabRep_sqT (tabRep_sqT (tabRep_sqT (tabRep_sqT (tabRep_sqT
    (tabRep_sqT ht)))))))

theorem commT_iff {t s : Tab} {g h : Equiv.Perm (Fin 42)} (ht : TabRep t g) (hs : TabRep s h) :
    commT t s = true ↔ g * h = h * g :=
  (ht.comp hs).beq_iff (hs.comp ht)

theorem eq_of_fixCheck {r : Equiv.Perm (Fin 42)} {rT : Tab}
    (hr : TabRep rT r) (hchk : fixCheck enumR.tabs (centS rT) rT = true)
    {y : Equiv.Perm (Fin 42)} (hy : y ∈ R) (hyr : y * r = r * y)
    (hyC : ∀ c ∈ centralizer {r} ⊓ S, y * c = c * y) (hy2 : y ^ 256 = 1) : y = 1 ∨ y = r := by
  obtain ⟨t, ht, hty⟩ := enumerates_R.complete y hy
  obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem ht
  unfold fixCheck at hchk
  have h := (allBelow_eq_true.mp hchk) k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with (((h1 | h2) | h3) | h4) | h5
  · exfalso
    have := (commT_iff hty hr).mpr hyr
    rw [this] at h1
    exact Bool.noConfusion h1
  · exfalso
    have : ((centS rT).all fun c => commT enumR.tabs[k]! c) = true := by
      rw [Array.all_eq_true']
      intro c hc
      obtain ⟨g, hg, hcg⟩ := (enumerates_cent hr).sound c (Array.mem_toList_iff.mpr hc)
      exact (commT_iff hty hcg).mpr (hyC g hg)
    rw [this] at h2
    exact Bool.noConfusion h2
  · exfalso
    have := ((tabRep_pow256T hty).beq_iff TabRep.idTab).mpr hy2
    rw [this] at h3
    exact Bool.noConfusion h3
  · exact Or.inl ((hty.beq_iff TabRep.idTab).mp h4)
  · exact Or.inr ((hty.beq_iff hr).mp h5)

theorem pow_256_eq_one {y : R} {k : ℕ} (hk : y ^ 2 ^ k = 1) :
    y ^ 256 = 1 := by
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf y ∣ 241920 := card_R ▸ orderOf_dvd_natCard y
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hj8 : j ≤ 8 := by
    rw [hj'] at h2
    by_contra hlt
    have : 2 ^ 9 ∣ 241920 := (Nat.pow_dvd_pow 2 (by omega : 9 ≤ j)).trans h2
    norm_num at this
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hj']
  exact (Nat.pow_dvd_pow 2 hj8).trans (by norm_num)

theorem fixCat_S {n : ℕ}
    (hn : n = 60 ∨ n = 168) : Idx.FixCat ↥S n := by
  intro α τ hα2 hα1 hτα hτ2 X hXp hXd hXα hXτ
  obtain ⟨eR, heR, -⟩ := full_automorphism_action
  obtain ⟨-, -, -, -, -, hcls, -, -, -, -, -, -, -, hC1, hC2, hC3, hC4, -⟩ :=
    involution_enumeration
  set r : R := eR.symm α with hr
  set y : R := eR.symm τ with hy
  have hαr : α = eR r := by rw [hr, MulEquiv.apply_symm_apply]
  have hτy : τ = eR y := by rw [hy, MulEquiv.apply_symm_apply]
  have hr2 : orderOf r = 2 := by
    have hrr : r * r = 1 := eR.injective (by rw [map_mul, ← hαr, hα2, map_one])
    have hr1 : r ≠ 1 := fun h => hα1 (by rw [hαr, h, map_one])
    exact orderOf_eq_prime (by rw [pow_two]; exact hrr) hr1
  have hyr : y * r = r * y := eR.injective (by rw [map_mul, map_mul, ← hαr, ← hτy, hτα])
  obtain ⟨k, hk⟩ := hτ2
  have hy256 : y ^ 256 = 1 :=
    pow_256_eq_one (k := k) (eR.injective (by rw [map_pow, ← hτy, hk, map_one]))
  have hfix : ∀ (z : R) (x : ↥S), eR z x = x → (z : Equiv.Perm (Fin 42)) * x = x * z := by
    intro z x hzx
    have h1 := congrArg Subtype.val hzx
    rw [heR, Subgroup.coe_inv] at h1
    calc (z : Equiv.Perm (Fin 42)) * x = z * x * (z : Equiv.Perm (Fin 42))⁻¹ * z := by group
      _ = x * z := by rw [h1]
  have key : ∀ (ri : R) (riT : Tab), TabRep riT (ri : Equiv.Perm (Fin 42)) → IsConj r ri →
      (fixCheck enumR.tabs (centS riT) riT = true ∨
        ¬ n ∣ Nat.card ↥(centralizer {(ri : Equiv.Perm (Fin 42))} ⊓ S)) →
      (n ∣ Nat.card ↥(centralizer {(ri : Equiv.Perm (Fin 42))} ⊓ S) →
        Nat.card ↥(centralizer {(ri : Equiv.Perm (Fin 42))} ⊓ S) ≤ n) →
      τ = 1 ∨ τ = α := by
    intro ri riT hri hconj hchk hle
    obtain ⟨c, hc, hrc⟩ := eq_conj_of_isConj hconj
    set C := centralizer {(ri : Equiv.Perm (Fin 42))} ⊓ S with hC
    set X₁ : Subgroup (Equiv.Perm (Fin 42)) :=
      (X.map S.subtype).map (MulAut.conj c⁻¹).toMonoidHom with hX₁
    have hX₁C : X₁ ≤ C := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, subtype_apply]
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_centralizer_singleton_iff]
        have hxr := hfix r x (by rw [← hαr]; exact hXα x hx)
        have hri : (ri : Equiv.Perm (Fin 42)) = c⁻¹ * r * c := by rw [hrc]; group
        rw [hri]
        calc c⁻¹ * (x : Equiv.Perm (Fin 42)) * c * (c⁻¹ * r * c) = c⁻¹ * (x * r) * c := by group
          _ = c⁻¹ * (r * x) * c := by rw [hxr]
          _ = c⁻¹ * r * c * (c⁻¹ * x * c) := by group
      · have := conj_mem_S (inv_mem hc) x.2
        rwa [inv_inv] at this
    have hX₁card : Nat.card X₁ = Nat.card X := by
      rw [hX₁, card_map_of_injective (MulAut.conj c⁻¹).injective,
        card_map_of_injective (subtype_injective _)]
    have hXd₁ : n ∣ Nat.card X₁ := by rw [hX₁card]; exact hXd
    have hdvd : n ∣ Nat.card C := hXd₁.trans (card_dvd_of_le hX₁C)
    rcases hchk with hchk | hchk
    swap
    · exact absurd hdvd hchk
    have hX₁eq : X₁ = C := eq_of_le_of_card_ge hX₁C (by
      rw [hX₁card]
      exact (hle hdvd).trans (Nat.le_of_dvd Nat.card_pos hXd))
    set y₁ : Equiv.Perm (Fin 42) := c⁻¹ * y * c with hy₁
    have hy₁R : y₁ ∈ R := mul_mem (mul_mem (inv_mem hc) y.2) hc
    have hy₁r : y₁ * ri = ri * y₁ := by
      have hri : (ri : Equiv.Perm (Fin 42)) = c⁻¹ * r * c := by rw [hrc]; group
      have hyr' : (y : Equiv.Perm (Fin 42)) * r = r * y := congrArg Subtype.val hyr
      rw [hri, hy₁]
      calc c⁻¹ * (y : Equiv.Perm (Fin 42)) * c * (c⁻¹ * r * c) = c⁻¹ * (y * r) * c := by group
        _ = c⁻¹ * (r * y) * c := by rw [hyr']
        _ = c⁻¹ * r * c * (c⁻¹ * y * c) := by group
    have hy₁C : ∀ g ∈ C, y₁ * g = g * y₁ := by
      intro g hg
      rw [← hX₁eq] at hg
      obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hg
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, subtype_apply]
      have hxy := hfix y x (by rw [← hτy]; exact hXτ x hx)
      rw [hy₁]
      calc c⁻¹ * (y : Equiv.Perm (Fin 42)) * c * (c⁻¹ * x * c) = c⁻¹ * (y * x) * c := by group
        _ = c⁻¹ * (x * y) * c := by rw [hxy]
        _ = c⁻¹ * x * c * (c⁻¹ * y * c) := by group
    have hy₁2 : y₁ ^ 256 = 1 := by
      have hyv : (y : Equiv.Perm (Fin 42)) ^ 256 = 1 := by
        rw [← Subgroup.coe_pow, hy256, Subgroup.coe_one]
      have e : c⁻¹ * (y : Equiv.Perm (Fin 42)) * c = c⁻¹ * y * c⁻¹⁻¹ := by rw [inv_inv]
      rw [hy₁, e, conj_pow, hyv, mul_one, mul_inv_cancel]
    rcases eq_of_fixCheck hri hchk hy₁R hy₁r hy₁C hy₁2 with h | h
    · left
      have hy1 : y = 1 := by
        apply Subtype.ext
        have : (y : Equiv.Perm (Fin 42)) = c * y₁ * c⁻¹ := by rw [hy₁]; group
        rw [this, h]
        simp
      rw [hτy, hy1, map_one]
    · right
      have hyr1 : y = r := by
        apply Subtype.ext
        have : (y : Equiv.Perm (Fin 42)) = c * y₁ * c⁻¹ := by rw [hy₁]; group
        rw [this, h, ← hrc]
      rw [hτy, hyr1, ← hαr]
  rcases (hcls r).mp hr2 with h | h | h | h
  · refine key r₁R r₁T tabRep_r₁ h (Or.inr ?_) (fun hd => ?_)
    · change ¬ n ∣ Nat.card C₁
      rw [hC1]
      rcases hn with rfl | rfl <;> norm_num
    · change n ∣ Nat.card C₁ at hd
      rw [hC1] at hd
      rcases hn with rfl | rfl <;> norm_num at hd
  · refine key r₂R r₂T tabRep_r₂ h ?_ (fun hd => ?_)
    · rcases hn with rfl | rfl
      · right
        change ¬ 60 ∣ Nat.card C₂
        rw [hC2]
        norm_num
      · exact Or.inl Certificates.certificate22300.1
    · change n ∣ Nat.card C₂ at hd
      change Nat.card C₂ ≤ n
      rw [hC2] at hd ⊢
      rcases hn with rfl | rfl <;> omega
  · refine key r₃R r₃T tabRep_r₃ h ?_ (fun hd => ?_)
    · rcases hn with rfl | rfl
      · exact Or.inl Certificates.certificate22300.2
      · right
        change ¬ 168 ∣ Nat.card C₃
        rw [hC3]
        norm_num
    · change n ∣ Nat.card C₃ at hd
      change Nat.card C₃ ≤ n
      rw [hC3] at hd ⊢
      rcases hn with rfl | rfl <;> omega
  · refine key r₄R r₄T tabRep_r₄ h (Or.inr ?_) (fun hd => ?_)
    · change ¬ n ∣ Nat.card C₄
      rw [hC4]
      rcases hn with rfl | rfl <;> norm_num
    · change n ∣ Nat.card C₄ at hd
      rw [hC4] at hd
      rcases hn with rfl | rfl <;> norm_num at hd

end FixL34

end CFSG.ComponentClassification.CatFactsL4U4
