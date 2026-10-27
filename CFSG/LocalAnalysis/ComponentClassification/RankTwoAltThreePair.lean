module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltThreeSyl
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixCoords

public section

namespace CFSG.ComponentClassification.RankTwoAlt.Three

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergCB

section Klein

variable {n : ℕ}

@[expose] def vList (h : 4 ≤ n) : Fin 4 → Perm (Fin n) :=
  ![1, swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩,
    swap ⟨0, by omega⟩ ⟨2, by omega⟩ * swap ⟨1, by omega⟩ ⟨3, by omega⟩,
    swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩ *
      (swap ⟨0, by omega⟩ ⟨2, by omega⟩ * swap ⟨1, by omega⟩ ⟨3, by omega⟩)]

theorem viaEmbeddingHom_kOf (h : 4 ≤ n) (i : Fin 4) :
    viaEmbeddingHom (fourEmb h) (kOf i) = vList h i := by
  fin_cases i <;> simp [kOf, vList, viaEmbeddingHom_swap] <;> rfl

theorem mem_rootVP_iff (h : 4 ≤ n) (x : Perm (Fin n)) :
    x ∈ rootVP n ↔ ∃ i : Fin 4, x = vList h i := by
  rw [rootVP_eq h]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨i, rfl⟩ := exists_kOf_of_mem_kleinFour hk
    exact ⟨i, viaEmbeddingHom_kOf h i⟩
  · rintro ⟨i, rfl⟩
    exact ⟨kOf i, kOf_mem i, viaEmbeddingHom_kOf h i⟩

theorem mem_rootV_iff_coe (u : alternatingGroup (Fin n)) :
    u ∈ rootV n ↔ (u : Perm (Fin n)) ∈ rootVP n :=
  (Subgroup.mem_map_iff_mem (alternatingGroup (Fin n)).subtype_injective).symm

@[expose] def d0145 (hn : 6 ≤ n) : alternatingGroup (Fin n) :=
  ⟨swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨4, by omega⟩ ⟨5, by omega⟩, by
    simp [mem_alternatingGroup, sign_swap', Fin.ext_iff]⟩

theorem d0145_facts (hn : n = 6 ∨ n = 7) :
    d0145 (six_le_of hn) * d0145 (six_le_of hn) = 1 ∧
      (∀ i : Fin 4, ∃ j : Fin 4, (d0145 (six_le_of hn) : Perm (Fin n)) * vList (by omega) i *
        (d0145 (six_le_of hn) : Perm (Fin n))⁻¹ = vList (by omega) j) ∧
      ∀ i : Fin 4, (d0145 (six_le_of hn) : Perm (Fin n)) ≠ vList (by omega) i := by
  rcases hn with rfl | rfl <;> decide

theorem d0145_normalizes (hn : n = 6 ∨ n = 7) {u : alternatingGroup (Fin n)} (hu : u ∈ rootV n) :
    d0145 (six_le_of hn) * u * (d0145 (six_le_of hn))⁻¹ ∈ rootV n := by
  have h4 : 4 ≤ n := by omega
  rw [mem_rootV_iff_coe, mem_rootVP_iff h4] at hu ⊢
  obtain ⟨i, hi⟩ := hu
  obtain ⟨j, hj⟩ := (d0145_facts hn).2.1 i
  refine ⟨j, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, hi, hj]

theorem d0145_not_mem (hn : n = 6 ∨ n = 7) : d0145 (six_le_of hn) ∉ rootV n := by
  have h4 : 4 ≤ n := by omega
  rw [mem_rootV_iff_coe, mem_rootVP_iff h4]
  rintro ⟨i, hi⟩
  exact (d0145_facts hn).2.2 i hi

theorem d0145_pow_odd (hn : n = 6 ∨ n = 7) {m : ℕ} (hm : Odd m) :
    d0145 (six_le_of hn) ^ m = d0145 (six_le_of hn) := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, (d0145_facts hn).1, one_pow, one_mul]

end Klein

section Cov

variable {G : Type} [Group G] {n : ℕ}

structure Cov (A : Subgroup G) (n : ℕ) where
  π : ↥A →* alternatingGroup (Fin n)
  surjective : Function.Surjective π
  ker_eq : π.ker = center ↥A
  θ : normalizer (A : Set G) →* MulAut (alternatingGroup (Fin n))
  θ_apply : ∀ (y : normalizer (A : Set G)) (a : ↥A),
    θ y (π a) = π ⟨(y : G) * a * (y : G)⁻¹, (mem_normalizer_iff.mp y.2 a).mp a.2⟩
  θ_eq_one_iff : ∀ y : normalizer (A : Set G), θ y = 1 ↔ (y : G) ∈ centralizer (A : Set G)

structure Side (A T : Subgroup G) (n : ℕ) extends Cov A n where
  le : T ≤ A
  map_eq : (T.subgroupOf A).map π = rootV n

namespace Cov

variable {A : Subgroup G} (c : Cov A n)
include c

theorem θ_mem (a : ↥A) : c.θ ⟨a, le_normalizer a.2⟩ = MulAut.conj (c.π a) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨b, rfl⟩ := c.surjective x
  rw [c.θ_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem eq_of_π_eq (hodd : Odd (Nat.card (center ↥A))) {a b : ↥A} (ha : a * a = 1)
    (hb : b * b = 1) (hab : c.π a = c.π b) : a = b := by
  have hz : a⁻¹ * b ∈ center ↥A := by
    rw [← c.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  have hz2 : (a⁻¹ * b) * (a⁻¹ * b) = 1 := by
    have hc := mem_center_iff.mp hz
    calc (a⁻¹ * b) * (a⁻¹ * b) = a⁻¹ * (b * (a⁻¹ * b)) := by group
      _ = a⁻¹ * (a⁻¹ * b * b) := by rw [hc b]
      _ = 1 := by rw [mul_assoc, hb, mul_one, ← mul_inv_rev, ha, inv_one]
  have hord : orderOf (a⁻¹ * b) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz2)
  have hord' : orderOf (a⁻¹ * b) ∣ Nat.card (center ↥A) := Subgroup.orderOf_dvd_natCard _ hz
  have h1 : orderOf (a⁻¹ * b) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact h
    · rw [h] at hord'
      exact absurd (even_iff_two_dvd.mpr hord') (Nat.not_even_iff_odd.mpr hodd)
  rw [orderOf_eq_one_iff, inv_mul_eq_one] at h1
  exact h1

@[expose] def relabel (α : MulAut (alternatingGroup (Fin n))) : Cov A n where
  π := α.toMonoidHom.comp c.π
  surjective := α.surjective.comp c.surjective
  ker_eq := by
    rw [← c.ker_eq]
    ext a
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  θ := (MulAut.conj α).toMonoidHom.comp c.θ
  θ_apply y a := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MulAut.mul_apply, MulAut.inv_apply_self]
    rw [c.θ_apply]
  θ_eq_one_iff y := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact c.θ_eq_one_iff y

end Cov

@[expose] noncomputable def Cov.ofPerm {A : Subgroup G} {ψ : normalizer (A : Set G) →* Perm (Fin n)}
    (hψ : RankTwoSporadic.IsActionHom A (alternatingGroup (Fin n)) ψ) (hn : 4 ≤ n) : Cov A n where
  π := restrictA hψ
  surjective := restrictA_surjective hψ
  ker_eq := ker_restrictA hψ
  θ := (conjPerm n).comp ψ
  θ_apply y a := by
    apply Subtype.ext
    rw [MonoidHom.comp_apply, conjPerm_apply, restrictA_coe, restrictA_coe, ← map_inv, ← map_mul,
      ← map_mul]
    rfl
  θ_eq_one_iff y := by
    rw [MonoidHom.comp_apply, ← hψ.eq_one_iff, ← map_one (conjPerm n)]
    exact (conjPerm_injective hn).eq_iff

@[expose] noncomputable def Cov.ofMulAut {A : Subgroup G}
    {ψ : normalizer (A : Set G) →* MulAut (alternatingGroup (Fin n))}
    (hψ : RankTwoSporadic.IsActionHom A
      (MulAut.conj : alternatingGroup (Fin n) →* MulAut (alternatingGroup (Fin n))).range ψ)
    (hZ : center (alternatingGroup (Fin n)) = ⊥) : Cov A n where
  π := (MonoidHom.ofInjective
    (RankTwoHypIIY.conj_injective_of_center_eq_bot hZ)).symm.toMonoidHom.comp (restrictA hψ)
  surjective x := by
    obtain ⟨b, hb⟩ := restrictA_surjective hψ
      (MonoidHom.ofInjective (RankTwoHypIIY.conj_injective_of_center_eq_bot hZ) x)
    refine ⟨b, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hb, MulEquiv.symm_apply_apply]
  ker_eq := by
    rw [← ker_restrictA hψ]
    ext a
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  θ := ψ
  θ_apply y a := by
    have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZ
    have key : ∀ b : ↥A, MulAut.conj ((MonoidHom.ofInjective hinj).symm (restrictA hψ b)) =
        ψ ⟨b, le_normalizer b.2⟩ := by
      intro b
      have h := MonoidHom.apply_ofInjective_symm hinj (restrictA hψ b)
      rw [h, restrictA_coe]
    apply hinj
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [RankTwoHypIIY.conj_apply_eq_mul_conj_mul_inv, key, key, ← map_inv, ← map_mul, ← map_mul]
    rfl
  θ_eq_one_iff y := hψ.eq_one_iff y

namespace Side

variable {A T : Subgroup G} (s : Side A T n)
include s

theorem mem_of_mem {t : G} (ht : t ∈ T) : s.π ⟨t, s.le ht⟩ ∈ rootV n := by
  rw [← s.map_eq]
  exact ⟨⟨t, s.le ht⟩, mem_subgroupOf.mpr ht, rfl⟩

theorem exists_of_mem {u : alternatingGroup (Fin n)} (hu : u ∈ rootV n) :
    ∃ (t : G) (ht : t ∈ T), s.π ⟨t, s.le ht⟩ = u := by
  rw [← s.map_eq] at hu
  obtain ⟨a, ha, rfl⟩ := hu
  exact ⟨a, mem_subgroupOf.mp ha, rfl⟩

theorem θ_fix {y : normalizer (A : Set G)} (hy : ∀ t ∈ T, (y : G) * t = t * y) :
    ∀ u ∈ rootV n, s.θ y u = u := by
  intro u hu
  obtain ⟨t, ht, rfl⟩ := s.exists_of_mem hu
  rw [s.θ_apply]
  congr 1
  apply Subtype.ext
  change (y : G) * t * (y : G)⁻¹ = t
  rw [hy t ht, mul_inv_cancel_right]

end Side

end Cov

section Config

variable {G : Type} [Group G] [Finite G] {n : ℕ} {A B R T : Subgroup G}

omit [Finite G] in
theorem eq_one_of_mul_self_of_odd {H : Subgroup G} (hodd : Odd (Nat.card H)) {x : G}
    (hx : x ∈ H) (h2 : x * x = 1) : x = 1 := by
  have hord : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
  have hord' : orderOf x ∣ Nat.card H := Subgroup.orderOf_dvd_natCard _ hx
  rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hord'
    exact absurd (even_iff_two_dvd.mpr hord') (Nat.not_even_iff_odd.mpr hodd)

omit [Finite G] in
theorem mem_center_of_mem_centralizer {x : G} (hxB : x ∈ B)
    (hx : x ∈ centralizer (B : Set G)) : (⟨x, hxB⟩ : ↥B) ∈ center ↥B := by
  rw [mem_center_iff]
  intro b
  exact Subtype.ext (mem_centralizer_iff.mp hx b b.2)

omit [Finite G] in
theorem eq_one_of_mem_inf_centralizer (hoddB : Odd (Nat.card (center ↥B))) {x : G} (hxB : x ∈ B)
    (hx : x ∈ centralizer (B : Set G)) (h2 : x * x = 1) : x = 1 := by
  have h := eq_one_of_mul_self_of_odd hoddB (mem_center_of_mem_centralizer hxB hx)
    (Subtype.ext h2)
  exact congrArg Subtype.val h

theorem exists_conjPerm_of_side (sA : Side A T n)
    (sB : Side B R n) (hn : n = 6 ∨ n = 7) (hR2 : ∀ r ∈ R, r * r = 1)
    (hT2 : ∀ t ∈ T, t * t = 1) (hRsyl : IsSylowOf 2 R (centralizer (A : Set G)))
    (hTB : T ≤ centralizer (B : Set G)) (hTR : T ≤ centralizer (R : Set G))
    (hNR : normalizer (R : Set G) ≤ normalizer (A : Set G))
    (hoddB : Odd (Nat.card (center ↥B))) :
    ∃ y ∈ B, ∃ hy : y ∈ normalizer (A : Set G), ∃ σ : Perm (Fin n),
      sA.θ ⟨y, hy⟩ = conjPerm n σ ∧ Commute σ (vA (by omega)) ∧ Commute σ (vB (by omega)) ∧
        σ * σ = 1 ∧ σ ∉ rootVP n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ n := by omega
  set d := d0145 (six_le_of hn) with hd
  obtain ⟨b₀, hb₀⟩ := sB.surjective d
  set m := Nat.card (center ↥B) with hm
  set y₀ : ↥B := b₀ ^ m with hy₀
  have hy₀π : sB.π y₀ = d := by rw [hy₀, map_pow, hb₀, hd, d0145_pow_odd hn hoddB]
  have hy₀2 : y₀ * y₀ = 1 := by
    have hz : b₀ ^ 2 ∈ center ↥B := by
      rw [← sB.ker_eq, MonoidHom.mem_ker, map_pow, hb₀, sq, hd, (d0145_facts hn).1]
    have h1 : (b₀ ^ 2) ^ m = 1 := by
      have := pow_card_eq_one' (G := center ↥B) (x := ⟨b₀ ^ 2, hz⟩)
      exact congrArg Subtype.val this
    rw [hy₀, ← pow_add, ← two_mul, pow_mul, h1]
  set yG : G := (y₀ : G) with hyG
  have hyB : yG ∈ B := y₀.2
  have hyG2 : yG * yG = 1 := congrArg Subtype.val hy₀2
  have hconjR : ∀ r ∈ R, yG * r * yG⁻¹ ∈ R := by
    intro r hr
    have hu := sB.mem_of_mem hr
    have hu' := d0145_normalizes hn hu
    obtain ⟨r', hr', hr'π⟩ := sB.exists_of_mem hu'
    have hsq1 : (y₀ * ⟨r, sB.le hr⟩ * y₀⁻¹) * (y₀ * ⟨r, sB.le hr⟩ * y₀⁻¹) = 1 := by
      have h := hR2 r hr
      apply Subtype.ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one]
      calc (y₀ : G) * r * (y₀ : G)⁻¹ * ((y₀ : G) * r * (y₀ : G)⁻¹) =
          (y₀ : G) * (r * r) * (y₀ : G)⁻¹ := by group
        _ = 1 := by rw [h, mul_one, mul_inv_cancel]
    have hsq2 : (⟨r', sB.le hr'⟩ : ↥B) * ⟨r', sB.le hr'⟩ = 1 := Subtype.ext (hR2 r' hr')
    have heq := sB.eq_of_π_eq hoddB hsq1 hsq2 (by
      rw [hr'π, map_mul, map_mul, map_inv, hy₀π])
    have heq' : yG * r * yG⁻¹ = r' := congrArg Subtype.val heq
    rw [heq']
    exact hr'
  have hyR : yG ∈ normalizer (R : Set G) := by
    rw [mem_normalizer_iff]
    intro r
    refine ⟨hconjR r, fun h => ?_⟩
    have hinv : yG⁻¹ = yG := inv_eq_of_mul_eq_one_right hyG2
    have := hconjR _ h
    rwa [hinv, show yG * (yG * r * yG) * yG = (yG * yG) * r * (yG * yG) by group, hyG2,
      one_mul, mul_one] at this
  have hyA : yG ∈ normalizer (A : Set G) := hNR hyR
  have hfix := sA.θ_fix (y := ⟨yG, hyA⟩) fun t ht => mem_centralizer_iff.mp (hTB ht) yG hyB
  obtain ⟨σ, hσ, hc1, hc2⟩ := exists_conjPerm hn _ hfix
  refine ⟨yG, hyB, hyA, σ, hσ, hc1, hc2, ?_, ?_⟩
  ·
    apply conjPerm_injective h4
    rw [map_mul, ← hσ, ← map_mul, map_one]
    have : (⟨yG, hyA⟩ : normalizer (A : Set G)) * ⟨yG, hyA⟩ = 1 := Subtype.ext hyG2
    rw [this, map_one]
  ·
    intro hσV
    obtain ⟨u, hu, hσu⟩ := hσV
    obtain ⟨t₀, ht₀, ht₀π⟩ := sA.exists_of_mem hu
    have ht₀A := sA.le ht₀
    have hθt : sA.θ ⟨t₀, le_normalizer ht₀A⟩ = conjPerm n σ := by
      rw [sA.θ_mem ⟨t₀, ht₀A⟩, ht₀π, RankTwoAlt.conj_eq_conjPerm, ← hσu]
      rfl
    have hkC : yG * t₀⁻¹ ∈ centralizer (A : Set G) := by
      have h1 : sA.θ (⟨yG, hyA⟩ * (⟨t₀, le_normalizer ht₀A⟩ : normalizer (A : Set G))⁻¹) = 1 := by
        rw [map_mul, map_inv, hσ, hθt, mul_inv_cancel]
      exact (sA.θ_eq_one_iff _).mp h1
    have hyt : yG * t₀ = t₀ * yG := mem_centralizer_iff.mp (hTB ht₀) yG hyB
    have hk2 : (yG * t₀⁻¹) * (yG * t₀⁻¹) = 1 := by
      have ht2 := hT2 t₀ ht₀
      have hyt' : yG * t₀⁻¹ = t₀⁻¹ * yG := by
        calc yG * t₀⁻¹ = t₀⁻¹ * (t₀ * yG) * t₀⁻¹ := by group
          _ = t₀⁻¹ * (yG * t₀) * t₀⁻¹ := by rw [hyt]
          _ = t₀⁻¹ * yG := by group
      calc (yG * t₀⁻¹) * (yG * t₀⁻¹) = yG * (t₀⁻¹ * yG) * t₀⁻¹ := by group
        _ = yG * (yG * t₀⁻¹) * t₀⁻¹ := by rw [hyt']
        _ = (yG * yG) * (t₀ * t₀)⁻¹ := by group
        _ = 1 := by rw [hyG2, ht2, inv_one, one_mul]
    have hkN : yG * t₀⁻¹ ∈ normalizer (R : Set G) :=
      mul_mem hyR (inv_mem ((centralizer_le_normalizer _) (hTR ht₀)))
    have hkp : IsPGroup 2 (zpowers (yG * t₀⁻¹)) := by
      have hdvd : orderOf (yG * t₀⁻¹) ∣ 2 ^ 1 :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq, hk2])
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hsup : IsPGroup 2 ↥(R ⊔ zpowers (yG * t₀⁻¹)) :=
      IsPGroup.to_sup_of_normal_left' hRsyl.isPGroup hkp (zpowers_le.mpr hkN)
    have heq := hRsyl.eq_of_le le_sup_left (sup_le hRsyl.le (zpowers_le.mpr hkC)) hsup
    have hkR : yG * t₀⁻¹ ∈ R := heq ▸ (le_sup_right (a := R) (mem_zpowers _))
    have ht₀B : t₀ ∈ B := by
      have : t₀ = (yG * t₀⁻¹)⁻¹ * yG := by group
      rw [this]
      exact mul_mem (inv_mem (sB.le hkR)) hyB
    have ht₀1 := eq_one_of_mem_inf_centralizer hoddB ht₀B (hTB ht₀) (hT2 t₀ ht₀)
    rw [ht₀1, inv_one, mul_one] at hkR
    have h := sB.mem_of_mem hkR
    have : (⟨yG, sB.le hkR⟩ : ↥B) = y₀ := rfl
    rw [this, hy₀π] at h
    exact d0145_not_mem hn h

theorem center_le_centralizer (sA : Side A T n)
    (sB : Side B R n) (hn : n = 6 ∨ n = 7) (hR2 : ∀ r ∈ R, r * r = 1)
    (hT2 : ∀ t ∈ T, t * t = 1) (hTsyl : IsSylowOf 2 T (centralizer (B : Set G)))
    (hRA : R ≤ centralizer (A : Set G)) (hRT : R ≤ centralizer (T : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (B : Set G))
    (hoddA : Odd (Nat.card (center ↥A))) {z : ↥A} (hz : z ∈ center ↥A) :
    (z : G) ∈ centralizer (B : Set G) := by
  have h4 : 4 ≤ n := by omega
  obtain ⟨x₀, hx₀A, hx₀N, σ₀, hσ₀, hc1, hc2, hσ₀2, hσ₀V⟩ :=
    exists_conjPerm_of_side sB sA hn hT2 hR2 hTsyl hRA hRT hNT hoddA
  have hzT : (z : G) ∈ normalizer (T : Set G) := by
    refine (centralizer_le_normalizer _) (mem_centralizer_iff.mpr fun t ht => ?_)
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨t, sA.le ht⟩)
  have hzB := hNT hzT
  have hfix := sB.θ_fix (y := ⟨z, hzB⟩) fun r hr => mem_centralizer_iff.mp (hRA hr) z z.2
  obtain ⟨σ', hσ', hc1', hc2'⟩ := exists_conjPerm hn _ hfix
  have hσ'm : σ' ^ Nat.card (center ↥A) = 1 := by
    apply conjPerm_injective h4
    rw [map_pow, ← hσ', ← map_pow, map_one]
    have hzm : z ^ Nat.card (center ↥A) = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (G := center ↥A) (x := ⟨z, hz⟩))
    have h1 : (⟨z, hzB⟩ : normalizer (B : Set G)) ^ Nat.card (center ↥A) = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      change (z : G) ^ Nat.card (center ↥A) = 1
      rw [← SubgroupClass.coe_pow, hzm, OneMemClass.coe_one]
    rw [h1, map_one]
  have hcomm : Commute σ' σ₀ := by
    have hzx : (z : G) * x₀ = x₀ * z :=
      congrArg Subtype.val (mem_center_iff.mp hz ⟨x₀, hx₀A⟩).symm
    have h1 : (⟨z, hzB⟩ : normalizer (B : Set G)) * ⟨x₀, hx₀N⟩ = ⟨x₀, hx₀N⟩ * ⟨z, hzB⟩ :=
      Subtype.ext hzx
    have h2 := congrArg sB.θ h1
    rw [map_mul, map_mul, hσ', hσ₀, ← map_mul, ← map_mul] at h2
    exact conjPerm_injective h4 h2
  have h1 := eq_one_of_commute_of_odd hn hc1 hc2 hσ₀2 hσ₀V hc1' hc2' hoddA hσ'm hcomm
  exact (sB.θ_eq_one_iff ⟨z, hzB⟩).mp (by rw [hσ', h1, map_one])

theorem center_eq_bot
    (sA : Side A T n) (sB : Side B R n) (hn : n = 6 ∨ n = 7) (hR2 : ∀ r ∈ R, r * r = 1)
    (hT2 : ∀ t ∈ T, t * t = 1) (hRsyl : IsSylowOf 2 R (centralizer (A : Set G)))
    (hTsyl : IsSylowOf 2 T (centralizer (B : Set G))) (hTR : T ≤ centralizer (R : Set G))
    (hNR : normalizer (R : Set G) ≤ normalizer (A : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (B : Set G))
    (hoddA : Odd (Nat.card (center ↥A))) (hoddB : Odd (Nat.card (center ↥B)))
    (hP : commutator ↥A = ⊤) : center ↥A = ⊥ := by
  have hRT : R ≤ centralizer (T : Set G) := le_centralizer_iff.mp hTR
  obtain ⟨y₀, hy₀B, hy₀N, σ, hσ, hc1, hc2, hσ2, hσV⟩ :=
    exists_conjPerm_of_side sA sB hn hR2 hT2 hRsyl hTsyl.le hTR hNR hoddB
  obtain ⟨v, hv, ρ, hρ, hρσ⟩ := exists_conj_s45 hn hc1 hc2 hσ2 hσV
  obtain ⟨u, -, rfl⟩ := hv
  obtain ⟨a, ha⟩ := sA.surjective u
  obtain ⟨a', ha'⟩ := sA.surjective ⟨ρ, hρ⟩
  have haN : (a : G) ∈ normalizer (A : Set G) := le_normalizer a.2
  have ha'N : (a' : G) ∈ normalizer (A : Set G) := le_normalizer a'.2
  have hyGN : (a' : G) * (y₀ * a) * (a' : G)⁻¹ ∈ normalizer (A : Set G) :=
    mul_mem (mul_mem ha'N (mul_mem hy₀N haN)) (inv_mem ha'N)
  set yN : normalizer (A : Set G) := ⟨(a' : G) * (y₀ * a) * (a' : G)⁻¹, hyGN⟩ with hyN
  have hyN' : yN = ⟨a', ha'N⟩ * (⟨y₀, hy₀N⟩ * ⟨a, haN⟩) *
      (⟨a', ha'N⟩ : normalizer (A : Set G))⁻¹ := rfl
  have hθy : sA.θ yN = conjPerm n (s45 (six_le_of hn)) := by
    rw [hyN', map_mul, map_mul, map_mul, map_inv, hσ, sA.θ_mem a, sA.θ_mem a', ha, ha',
      RankTwoAlt.conj_eq_conjPerm, RankTwoAlt.conj_eq_conjPerm, ← map_mul, ← map_mul, ← map_inv,
      ← map_mul, ← hρσ]
    rfl
  have hZB := fun (z : ↥A) (hz : z ∈ center ↥A) =>
    center_le_centralizer sA sB hn hR2 hT2 hTsyl hRsyl.le hRT hNT hoddA hz
  have hyz : ∀ z ∈ center ↥A, (yN : G) * z * (yN : G)⁻¹ = z := by
    intro z hz
    have hza : ∀ b : ↥A, Commute (z : G) b := fun b =>
      congrArg Subtype.val (mem_center_iff.mp hz b).symm
    have hzy : Commute (z : G) y₀ := (mem_centralizer_iff.mp (hZB z hz) y₀ hy₀B).symm
    have hzc : (yN : G) * z = z * yN :=
      (((hza a').mul_right (hzy.mul_right (hza a))).mul_right (hza a').inv_right).symm.eq
    rw [hzc, mul_inv_cancel_right]
  let α : ↥A →* ↥A :=
    { toFun := fun x => ⟨(yN : G) * x * (yN : G)⁻¹, (mem_normalizer_iff.mp yN.2 x).mp x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x x' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hαK : ∀ z ∈ sA.π.ker, α z = z := by
    intro z hz
    rw [sA.ker_eq] at hz
    exact Subtype.ext (hyz z hz)
  have hα : ∀ x : ↥A, ((sA.π (α x) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      s45 (six_le_of hn) * (sA.π x : Perm (Fin n)) * s45 (six_le_of hn) := by
    intro x
    have h := sA.θ_apply yN x
    rw [hθy] at h
    have h' := congrArg (fun w : alternatingGroup (Fin n) => (w : Perm (Fin n))) h
    simp only [conjPerm_apply] at h'
    rw [show (s45 (six_le_of hn))⁻¹ = s45 (six_le_of hn) from swap_inv _ _] at h'
    exact h'.symm
  have h1 := card_ker_eq_one_of_swap45 hP hn sA.surjective sA.ker_eq.le
    (by rw [sA.ker_eq]; exact hoddA) α hαK hα
  rw [← sA.ker_eq]
  exact Subgroup.eq_bot_of_card_eq _ h1

end Config

end CFSG.ComponentClassification.RankTwoAlt.Three
