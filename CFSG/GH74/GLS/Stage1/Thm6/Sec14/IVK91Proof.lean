module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1W16Components
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.IVK91
public import CFSG.GroupTheory.ABGLocalTools.PStabilityRelative
public import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

open Subgroup CFSG CFSG.ABGLocalTools
open CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14.IVK91Proof

section Abstract

variable {Γ : Type*} [Group Γ]

theorem conj_cent_mul {S₀ : Subgroup Γ} {u w a : Γ} (hu : u ∈ centralizer (S₀ : Set Γ))
    (hw : w ∈ normalizer (S₀ : Set Γ)) (ha : a ∈ S₀) :
    (u * w) * a * (u * w)⁻¹ = w * a * w⁻¹ := by
  have ht : w * a * w⁻¹ ∈ S₀ := (mem_normalizer_iff.mp hw a).mp ha
  have h1 : u * (w * a * w⁻¹) = (w * a * w⁻¹) * u := (mem_centralizer_iff.mp hu _ ht).symm
  calc (u * w) * a * (u * w)⁻¹ = u * (w * a * w⁻¹) * u⁻¹ := by group
    _ = (w * a * w⁻¹) * u * u⁻¹ := by rw [h1]
    _ = w * a * w⁻¹ := by group

def ActCases (S₀ : Subgroup Γ) : Prop :=
  (∀ n ∈ normalizer (S₀ : Set Γ), n ∈ centralizer (S₀ : Set Γ)) ∨
    ∃ x ∈ normalizer (S₀ : Set Γ), ∃ p : ℕ, (p = 3 ∨ p = 5) ∧ x ^ p ∈ centralizer (S₀ : Set Γ) ∧
      (∀ s ∈ S₀, s ≠ 1 → x * s * x⁻¹ ≠ s) ∧
      ∀ n ∈ normalizer (S₀ : Set Γ), ∃ c ∈ centralizer (S₀ : Set Γ), ∃ k : ℕ, n = c * x ^ k

theorem ActCases.fpf {S₀ : Subgroup Γ} (h : ActCases S₀) {n : Γ}
    (hn : n ∈ normalizer (S₀ : Set Γ)) (hnC : n ∉ centralizer (S₀ : Set Γ)) {s : Γ} (hs : s ∈ S₀)
    (hfix : n * s * n⁻¹ = s) : s = 1 := by
  rcases h with h1 | ⟨x, hx, p, hp, hxp, hfpf, hall⟩
  · exact absurd (h1 n hn) hnC
  · obtain ⟨c, hc, k, rfl⟩ := hall n hn
    have hxk : x ^ k ∈ normalizer (S₀ : Set Γ) := pow_mem hx k
    have hact : x ^ k * s * (x ^ k)⁻¹ = s := by
      rw [← conj_cent_mul hc hxk hs]; exact hfix
    have hpk : ¬ p ∣ k := by
      rintro ⟨j, rfl⟩
      apply hnC
      refine mul_mem hc ?_
      rw [pow_mul]; exact pow_mem hxp j
    by_contra hs1
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k * m % p = 1 := by
      rcases hp with rfl | rfl
      · have : k % 3 = 1 ∨ k % 3 = 2 := by omega
        rcases this with h | h
        · exact ⟨1, by omega⟩
        · exact ⟨2, by omega⟩
      · have : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
        rcases this with h | h | h | h
        · exact ⟨1, by omega⟩
        · exact ⟨3, by omega⟩
        · exact ⟨2, by omega⟩
        · exact ⟨4, by omega⟩
    have hp0 : 0 < p := by rcases hp with rfl | rfl <;> norm_num
    have hcom : Commute (x ^ k) s := mul_inv_eq_iff_eq_mul.mp hact
    have hcom2 : Commute ((x ^ k) ^ m) s := hcom.pow_left m
    obtain ⟨j, hkm⟩ : ∃ j : ℕ, k * m = p * j + 1 :=
      ⟨k * m / p, by have := Nat.div_add_mod (k * m) p; omega⟩
    have hpow : (x ^ k) ^ m = (x ^ p) ^ j * x := by
      rw [← pow_mul, hkm, pow_add, pow_mul, pow_one]
    have hcent : Commute ((x ^ p) ^ j) s := by
      have hc' : (x ^ p) ^ j ∈ centralizer (S₀ : Set Γ) := pow_mem hxp _
      exact (mem_centralizer_iff.mp hc' s hs).symm
    rw [hpow] at hcom2
    have hxs : Commute x s := by
      have := (hcent.inv_left).mul_left hcom2
      simpa [mul_assoc] using this
    exact hfpf s hs hs1 (by rw [hxs.eq]; group)

theorem ActCases.orbit {S₀ : Subgroup Γ} (h : ActCases S₀) {a : Γ} (ha : a ∈ S₀) :
    ∃ T : Finset Γ, T.card ≤ 5 ∧ ∀ n ∈ normalizer (S₀ : Set Γ), n * a * n⁻¹ ∈ T := by
  classical
  rcases h with h1 | ⟨x, hx, p, hp, hxp, hfpf, hall⟩
  · refine ⟨{a}, by simp, fun n hn => ?_⟩
    have h2 : n * a = a * n := (mem_centralizer_iff.mp (h1 n hn) a ha).symm
    exact Finset.mem_singleton.mpr (by rw [h2]; group)
  · have hp0 : 0 < p := by rcases hp with rfl | rfl <;> norm_num
    have hp5 : p ≤ 5 := by rcases hp with rfl | rfl <;> norm_num
    refine ⟨(Finset.range p).image (fun k => x ^ k * a * (x ^ k)⁻¹), ?_, fun n hn => ?_⟩
    · exact (Finset.card_image_le.trans (by simpa using hp5))
    · obtain ⟨c, hc, k, rfl⟩ := hall n hn
      have hxk : x ^ k ∈ normalizer (S₀ : Set Γ) := pow_mem hx k
      have h1 : (c * x ^ k) * a * (c * x ^ k)⁻¹ = x ^ k * a * (x ^ k)⁻¹ := conj_cent_mul hc hxk ha
      have hk : x ^ k = (x ^ p) ^ (k / p) * x ^ (k % p) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      have hu : (x ^ p) ^ (k / p) ∈ centralizer (S₀ : Set Γ) := pow_mem hxp _
      have hw : x ^ (k % p) ∈ normalizer (S₀ : Set Γ) := pow_mem hx _
      have h2 : x ^ k * a * (x ^ k)⁻¹ = x ^ (k % p) * a * (x ^ (k % p))⁻¹ := by
        rw [hk]; exact conj_cent_mul hu hw ha
      rw [h1, h2]
      exact Finset.mem_image.mpr ⟨k % p, Finset.mem_range.mpr (Nat.mod_lt _ hp0), rfl⟩

end Abstract

section Quotient

variable {Γ : Type*} [Group Γ]

theorem comap_mk_map (S₀ : Subgroup Γ) :
    (S₀.map (QuotientGroup.mk' (oddCore Γ))).comap (QuotientGroup.mk' (oddCore Γ)) =
      S₀ ⊔ oddCore Γ := by
  rw [comap_map_eq, QuotientGroup.ker_mk']

variable [Finite Γ]

theorem exists_norm_lift {S₀ : Subgroup Γ} (hP : IsPGroup 2 S₀)
    (hab : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a) (n : Γ)
    (hnb : QuotientGroup.mk' (oddCore Γ) n ∈
      normalizer ((S₀.map (QuotientGroup.mk' (oddCore Γ)) : Subgroup (Γ ⧸ oddCore Γ)) :
        Set (Γ ⧸ oddCore Γ))) :
    ∃ n' ∈ normalizer (S₀ : Set Γ), ∀ s ∈ S₀,
      QuotientGroup.mk' (oddCore Γ) (n' * s * n'⁻¹) =
        QuotientGroup.mk' (oddCore Γ) n * QuotientGroup.mk' (oddCore Γ) s *
          (QuotientGroup.mk' (oddCore Γ) n)⁻¹ := by
  classical
  have hmem1 : ∀ y, y ∈ S₀ ↔ n * y * n⁻¹ ∈ S₀.map (MulAut.conj n).toMonoidHom := by
    intro y
    constructor
    · intro hy
      exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
    · rintro ⟨y', hy', h⟩
      have h' : n * y' * n⁻¹ = n * y * n⁻¹ := by simpa [MulAut.conj_apply] using h
      have : y' = y := by simpa using h'
      rw [← this]; exact hy'
  have hRabel : ∀ r₁ ∈ S₀.map (QuotientGroup.mk' (oddCore Γ)),
      ∀ r₂ ∈ S₀.map (QuotientGroup.mk' (oddCore Γ)), r₁ * r₂ = r₂ * r₁ := by
    rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩
    rw [← map_mul, ← map_mul, hab s₁ hs₁ s₂ hs₂]
  have hS₁R : (S₀.map (MulAut.conj n).toMonoidHom).map (QuotientGroup.mk' (oddCore Γ)) =
      S₀.map (QuotientGroup.mk' (oddCore Γ)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have h1 : QuotientGroup.mk' (oddCore Γ) ((MulAut.conj n).toMonoidHom y) =
          QuotientGroup.mk' (oddCore Γ) n * QuotientGroup.mk' (oddCore Γ) y *
            (QuotientGroup.mk' (oddCore Γ) n)⁻¹ := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]
      have h2 : QuotientGroup.mk' (oddCore Γ) y ∈ S₀.map (QuotientGroup.mk' (oddCore Γ)) :=
        ⟨y, hy, rfl⟩
      have h3 := (mem_normalizer_iff.mp hnb (QuotientGroup.mk' (oddCore Γ) y)).mp h2
      rw [h1]; exact h3
    · intro hx
      have h3 := (mem_normalizer_iff.mp (inv_mem hnb) x).mp hx
      obtain ⟨y, hy, hyx⟩ := h3
      refine ⟨n * y * n⁻¹, ⟨y, hy, by simp [MulAut.conj_apply]⟩, ?_⟩
      have : QuotientGroup.mk' (oddCore Γ) (n * y * n⁻¹) =
          QuotientGroup.mk' (oddCore Γ) n * QuotientGroup.mk' (oddCore Γ) y *
            (QuotientGroup.mk' (oddCore Γ) n)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [this, hyx]
      group
  have hOc : Nat.Coprime 2 (Nat.card (oddCore Γ)) := Nat.coprime_two_left.mpr odd_card_oddCore
  have hsyl0 : IsSylowOf 2 S₀ (oddCore Γ ⊔ S₀) := isSylowOf_sup_of_coprime hOc hP
  have hP1 : IsPGroup 2 (S₀.map (MulAut.conj n).toMonoidHom) := hP.map _
  have hsyl1 : IsSylowOf 2 (S₀.map (MulAut.conj n).toMonoidHom)
      (oddCore Γ ⊔ S₀.map (MulAut.conj n).toMonoidHom) := isSylowOf_sup_of_coprime hOc hP1
  have hOS : oddCore Γ ⊔ S₀.map (MulAut.conj n).toMonoidHom = oddCore Γ ⊔ S₀ := by
    have h0 := comap_mk_map S₀
    have h1 := comap_mk_map (S₀.map (MulAut.conj n).toMonoidHom)
    rw [hS₁R] at h1
    rw [sup_comm (oddCore Γ), sup_comm (oddCore Γ), ← h0, ← h1]
  rw [hOS] at hsyl1
  obtain ⟨k, hkK, hk⟩ := IsSylowOf.exists_mem_conj hsyl0 hsyl1
  have hkR : QuotientGroup.mk' (oddCore Γ) k ∈ S₀.map (QuotientGroup.mk' (oddCore Γ)) := by
    have : k ∈ (S₀.map (QuotientGroup.mk' (oddCore Γ))).comap (QuotientGroup.mk' (oddCore Γ)) := by
      rw [comap_mk_map, sup_comm]; exact hkK
    exact this
  refine ⟨k⁻¹ * n, ?_, fun s hs => ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    have e : (k⁻¹ * n) * y * (k⁻¹ * n)⁻¹ = k⁻¹ * (n * y * n⁻¹) * k := by group
    rw [e, ← hk, ← hmem1]
  · have e : (k⁻¹ * n) * s * (k⁻¹ * n)⁻¹ = k⁻¹ * (n * s * n⁻¹) * k := by group
    have hy : QuotientGroup.mk' (oddCore Γ) n * QuotientGroup.mk' (oddCore Γ) s *
        (QuotientGroup.mk' (oddCore Γ) n)⁻¹ ∈ S₀.map (QuotientGroup.mk' (oddCore Γ)) :=
      (mem_normalizer_iff.mp hnb (QuotientGroup.mk' (oddCore Γ) s)).mp ⟨s, hs, rfl⟩
    have hc := hRabel _ hkR _ hy
    rw [e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    rw [mul_assoc, ← hc]
    group


theorem normal_sup_of_E16
    {S₀ : Subgroup Γ} (hP : IsPGroup 2 S₀) (hidx : ¬ 2 ∣ S₀.index)
    (hel : ∀ a ∈ S₀, a * a = 1) (hab : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a)
    (hcard : Nat.card S₀ = 16) (hact : ActCases S₀) :
    (S₀ ⊔ oddCore Γ).Normal := by
  classical
  have hodd : Odd (Nat.card (oddCore Γ)) := odd_card_oddCore
  have hbot : oddCore Γ ⊓ S₀ = ⊥ := by
    apply disjoint_iff.mp
    apply disjoint_of_coprime_natCard
    rw [hcard]
    have h2 : Nat.Coprime (Nat.card (oddCore Γ)) 2 := Nat.coprime_two_right.mpr hodd
    simpa using h2.pow_right 4
  have hinj : ∀ a ∈ S₀, ∀ b ∈ S₀, QuotientGroup.mk' (oddCore Γ) a = QuotientGroup.mk' (oddCore Γ) b →
      a = b := by
    intro a ha b hb hab'
    have h1 : a⁻¹ * b ∈ oddCore Γ := QuotientGroup.eq.mp hab'
    have h2 : a⁻¹ * b ∈ S₀ := mul_mem (inv_mem ha) hb
    have h3 : a⁻¹ * b ∈ oddCore Γ ⊓ S₀ := ⟨h1, h2⟩
    rw [hbot, mem_bot] at h3
    exact (inv_mul_eq_one.mp h3)
  have hRp : IsPGroup 2 (S₀.map (QuotientGroup.mk' (oddCore Γ))) := hP.map _
  have hRidx : ¬ 2 ∣ (S₀.map (QuotientGroup.mk' (oddCore Γ))).index := fun h =>
    hidx (h.trans (index_map_dvd S₀ (QuotientGroup.mk'_surjective _)))
  let R : Sylow 2 (Γ ⧸ oddCore Γ) := hRp.toSylow hRidx
  have hRcoe : (R : Subgroup (Γ ⧸ oddCore Γ)) = S₀.map (QuotientGroup.mk' (oddCore Γ)) :=
    IsPGroup.toSylow_coe hRp hRidx
  have hRabel : ∀ r₁ ∈ S₀.map (QuotientGroup.mk' (oddCore Γ)),
      ∀ r₂ ∈ S₀.map (QuotientGroup.mk' (oddCore Γ)), r₁ * r₂ = r₂ * r₁ := by
    rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩
    rw [← map_mul, ← map_mul, hab s₁ hs₁ s₂ hs₂]
  have hne : S₀ ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcard
    norm_num at hcard
  obtain ⟨⟨a, haS⟩, ha1⟩ := ne_bot_iff_exists_ne_one.mp hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  obtain ⟨T, hTcard, hT⟩ := hact.orbit haS
  obtain ⟨b, hbS, hb1, hbT⟩ : ∃ b ∈ S₀, b ≠ 1 ∧ b ∉ T := by
    by_contra hcon
    push Not at hcon
    have hsub : (S₀ : Set Γ) ⊆ insert 1 (T : Set Γ) := by
      intro x hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (by exact_mod_cast hcon x hx hx1)
    have h16 : 16 ≤ 1 + 5 := by
      calc 16 = (S₀ : Set Γ).ncard := by rw [← Nat.card_coe_set_eq]; exact hcard.symm
        _ ≤ (insert 1 (T : Set Γ)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ (T : Set Γ).ncard + 1 := Set.ncard_insert_le _ _
        _ ≤ 5 + 1 := by rw [Set.ncard_coe_finset]; exact Nat.add_le_add_right hTcard 1
        _ = 1 + 5 := by norm_num
    omega
  have hmk1 : ∀ x ∈ S₀, x ≠ 1 → QuotientGroup.mk' (oddCore Γ) x ≠ 1 := by
    intro x hx hx1 h
    exact hx1 (hinj x hx 1 (one_mem _) (by rw [h, map_one]))
  have hord : ∀ x ∈ S₀, x ≠ 1 → orderOf (QuotientGroup.mk' (oddCore Γ) x) = 2 := by
    intro x hx hx1
    refine orderOf_eq_prime ?_ (hmk1 x hx hx1)
    rw [pow_two, ← map_mul, hel x hx, map_one]
  have hnorm : ∀ nb : Γ ⧸ oddCore Γ, nb ∈ normalizer (R : Set (Γ ⧸ oddCore Γ)) →
      ∃ n' ∈ normalizer (S₀ : Set Γ), ∀ s ∈ S₀,
        QuotientGroup.mk' (oddCore Γ) (n' * s * n'⁻¹) = nb * QuotientGroup.mk' (oddCore Γ) s * nb⁻¹ := by
    intro nb hnb
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective nb
    have hnb' : (n : Γ ⧸ oddCore Γ) ∈
        normalizer (((R : Subgroup (Γ ⧸ oddCore Γ)) : Set (Γ ⧸ oddCore Γ))) := hnb
    rw [hRcoe] at hnb'
    exact exists_norm_lift hP hab n hnb'
  have hRn : (R : Subgroup (Γ ⧸ oddCore Γ)).Normal := by
    refine sylow_normal_of_fpf_of_not_conj_of_oddCore oddCore_quotient_oddCore_eq_bot R
      ⟨⟨fun x y => Subtype.ext (by
        have := hRabel x (by rw [← hRcoe]; exact x.2) y (by rw [← hRcoe]; exact y.2)
        exact this)⟩⟩ ?_ (a := QuotientGroup.mk' (oddCore Γ) a) (b := QuotientGroup.mk' (oddCore Γ) b)
      (by rw [hRcoe]; exact ⟨a, haS, rfl⟩) (by rw [hRcoe]; exact ⟨b, hbS, rfl⟩)
      (hord a haS ha1') (hord b hbS hb1) ?_
    · intro nb hnb hnC r hr hfix
      obtain ⟨n', hn'N, hn'act⟩ := hnorm nb hnb
      have hr' : r ∈ (R : Subgroup (Γ ⧸ oddCore Γ)) := hr
      rw [hRcoe] at hr'
      obtain ⟨s, hs, rfl⟩ := hr'
      have hfix' : QuotientGroup.mk' (oddCore Γ) (n' * s * n'⁻¹) = QuotientGroup.mk' (oddCore Γ) s := by
        rw [hn'act s hs]; exact hfix
      have hn's : n' * s * n'⁻¹ ∈ S₀ := (mem_normalizer_iff.mp hn'N s).mp hs
      have hsfix : n' * s * n'⁻¹ = s := hinj _ hn's s hs hfix'
      have hn'C : n' ∉ centralizer (S₀ : Set Γ) := by
        intro hC
        apply hnC
        show nb ∈ centralizer (((R : Subgroup (Γ ⧸ oddCore Γ)) : Set (Γ ⧸ oddCore Γ)))
        rw [hRcoe, mem_centralizer_iff]
        rintro _ ⟨t, ht, rfl⟩
        have h1 := hn'act t ht
        have h2 : n' * t * n'⁻¹ = t := by
          have := mem_centralizer_iff.mp hC t ht
          rw [← this]; group
        rw [h2] at h1
        have h3 : QuotientGroup.mk' (oddCore Γ) t * nb = nb * QuotientGroup.mk' (oddCore Γ) t := by
          calc QuotientGroup.mk' (oddCore Γ) t * nb
              = (nb * QuotientGroup.mk' (oddCore Γ) t * nb⁻¹) * nb := by rw [← h1]
            _ = nb * QuotientGroup.mk' (oddCore Γ) t := by group
        exact h3
      have := hact.fpf hn'N hn'C hs hsfix
      rw [this, map_one]
    · intro nb hnb hcon
      obtain ⟨n', hn'N, hn'act⟩ := hnorm nb hnb
      have h1 := hn'act a haS
      rw [hcon] at h1
      have hn'a : n' * a * n'⁻¹ ∈ S₀ := (mem_normalizer_iff.mp hn'N a).mp haS
      have := hinj _ hn'a b hbS h1
      exact hbT (this ▸ hT n' hn'N)
  have hRn' : (S₀.map (QuotientGroup.mk' (oddCore Γ))).Normal := by
    rw [← hRcoe]; exact hRn
  have := hRn'.comap (QuotientGroup.mk' (oddCore Γ))
  rwa [comap_mk_map] at this

end Quotient

end CFSG.GH74.GLS.Stage1.Thm6.Sec14.IVK91Proof


namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14.IVK91Proof

section Final

open CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec14

variable {Y : Type} [Group Y]

theorem mem_normalizer_subgroupOf_iff {H S : Subgroup Y} (hSH : S ≤ H) (n : ↥H) :
    n ∈ normalizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (n : Y) ∈ normalizer (S : Set Y) := by
  constructor
  · intro hn
    rw [mem_normalizer_iff] at hn ⊢
    intro y
    by_cases hy : y ∈ H
    · exact hn ⟨y, hy⟩
    · constructor
      · intro hyS; exact absurd (hSH hyS) hy
      · intro h2
        exfalso
        apply hy
        have h3 : (n : Y)⁻¹ * ((n : Y) * y * (n : Y)⁻¹) * (n : Y) ∈ H :=
          mul_mem (mul_mem (inv_mem n.2) (hSH h2)) n.2
        have e : (n : Y)⁻¹ * ((n : Y) * y * (n : Y)⁻¹) * (n : Y) = y := by group
        rwa [e] at h3
  · intro hn
    rw [mem_normalizer_iff] at hn ⊢
    intro h
    exact hn (h : Y)

theorem mem_centralizer_subgroupOf_iff {H S : Subgroup Y} (hSH : S ≤ H) (n : ↥H) :
    n ∈ centralizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (n : Y) ∈ centralizer (S : Set Y) := by
  constructor
  · intro hn
    rw [mem_centralizer_iff] at hn ⊢
    intro y hy
    have := hn ⟨y, hSH hy⟩ hy
    exact congrArg Subtype.val this
  · intro hn
    rw [mem_centralizer_iff] at hn ⊢
    intro h hh
    exact Subtype.ext (hn (h : Y) hh)

theorem ivk_9_1_proved :
    IVK_9_1 := by
  intro Y _ _ H S _hK hsyl hel hcard hact
  obtain ⟨hSH, hSp, hSidx⟩ := hsyl
  have hP : IsPGroup 2 (S.subgroupOf H) := hSp.comap_subtype
  have hidx : ¬ 2 ∣ (S.subgroupOf H).index := hSidx
  have hel' : ∀ a ∈ S.subgroupOf H, a * a = 1 := fun a ha =>
    Subtype.ext (by simpa using (hel (a : Y) ha).1)
  have hab' : ∀ a ∈ S.subgroupOf H, ∀ b ∈ S.subgroupOf H, a * b = b * a := fun a ha b hb =>
    Subtype.ext (by simpa using (hel (a : Y) ha).2 (b : Y) hb)
  have hcard' : Nat.card (S.subgroupOf H) = 16 := by
    rw [← hcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  have hact' : ActCases (S.subgroupOf H) := by
    rcases hact with h1 | ⟨x, hx, p, hp, hxp, hfpf, hall⟩
    · left
      intro n hn
      have hn' : (n : Y) ∈ normalizer (S : Set Y) := (mem_normalizer_subgroupOf_iff hSH n).mp hn
      exact (mem_centralizer_subgroupOf_iff hSH n).mpr (h1 n ⟨n.2, hn'⟩)
    · right
      refine ⟨⟨x, hx.1⟩, (mem_normalizer_subgroupOf_iff hSH _).mpr hx.2, p, hp, ?_, ?_, ?_⟩
      · rw [mem_centralizer_subgroupOf_iff hSH]; simpa using hxp
      · intro s hs hs1 h
        have hs1' : (s : Y) ≠ 1 := fun h => hs1 (Subtype.ext h)
        exact hfpf (s : Y) hs hs1' (by simpa using congrArg Subtype.val h)
      · intro n hn
        have hn' : (n : Y) ∈ normalizer (S : Set Y) := (mem_normalizer_subgroupOf_iff hSH n).mp hn
        obtain ⟨c, hc, k, hk⟩ := hall (n : Y) ⟨n.2, hn'⟩
        refine ⟨⟨c, hc.1⟩, (mem_centralizer_subgroupOf_iff hSH _).mpr hc.2, k, Subtype.ext ?_⟩
        simpa using hk
  have hnorm := normal_sup_of_E16 hP hidx hel' hab' hcard' hact'
  have hpp : pPrimeCore 2 ↥H = oddCore ↥H :=
    (pPrimeCore_eq_piCore ↥H 2).trans (oddCore_eq_piCore ↥H).symm
  have e0 : (pPrimeCoreOf 2 H).subgroupOf H = oddCore ↥H := by
    unfold pPrimeCoreOf
    rw [hpp]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hle : pPrimeCoreOf 2 H ≤ H := Subgroup.map_subtype_le _
  have e1 : (pPrimeCoreOf 2 H ⊔ S).subgroupOf H = S.subgroupOf H ⊔ oddCore ↥H := by
    rw [subgroupOf_sup hle hSH, e0, sup_comm]
  rw [e1]
  exact hnorm

end Final

end CFSG.GH74.GLS.Stage1.Thm6.Sec14.IVK91Proof
