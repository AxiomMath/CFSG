module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4Blk
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Fix

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

namespace Q3L4

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

omit [Finite G] in
theorem mem_oddCoreImg_of_pow_three (hD : TightDatum R S t) {x : G} (hx : x ∈ R)
    (h3 : x ^ 3 = 1) : x ∈ oddCoreImg R := by
  set y : R := ⟨x, hx⟩ with hy
  have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa [hy] using h3)
  obtain ⟨k, hk⟩ := hD.twoGroup (QuotientGroup.mk y)
  have hd3 : orderOf (QuotientGroup.mk y : R ⧸ classicalInvolutionOddCore R) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hy3, QuotientGroup.mk_one])
  have hd2 : orderOf (QuotientGroup.mk y : R ⧸ classicalInvolutionOddCore R) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hk
  have h1 : (QuotientGroup.mk y : R ⧸ classicalInvolutionOddCore R) = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)) hd3 hd2)
  rw [QuotientGroup.eq_one_iff] at h1
  exact ⟨y, h1, rfl⟩

theorem false_of_block (hD : TightDatum R S t) {N : Subgroup G} [N.Normal]
    (hC : Subgroup.centralizer (N : Set G) = ⊥) {P : Type} [Group P] (e : ↥N ≃* P)
    (htN : t ∈ N) {u : P} (hu : e ⟨t, htN⟩ = u)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 3) (β : SL(2, F) × SL(2, F) →* P)
    (hker : ∀ a b, β (a, b) = 1 ↔ (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1))
    (hβu : β (-1, 1) = u) {w : P} (hwu : w * u = u * w)
    (hw : ∀ a b, w * β (a, b) * w⁻¹ = β (b, a))
    (hnorm : ∀ g : P, g * u = u * g → ∀ x ∈ β.range, g * x * g⁻¹ ∈ β.range)
    (hcent : ∀ g : P, (∀ x ∈ β.range, g * x = x * g) → g = 1 ∨ g = u)
    (hodd : NoOddNormal β.range) (hA : NoQ8Fix P β.range) : False := by
  classical
  set ι : P →* G := N.subtype.comp e.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
  have hιu : ι u = t := by
    rw [hιdef, MonoidHom.comp_apply, ← hu]
    simp
  have hιN : ∀ p, ι p ∈ N := fun p => (e.symm p).2
  have hιs : ∀ n ∈ N, ∃ p, ι p = n := fun n hn => ⟨e ⟨n, hn⟩, by simp [hιdef]⟩
  have hCt : ∀ p : P, p * u = u * p → ι p ∈ Subgroup.centralizer ({t} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff, ← hιu, ← map_mul, ← map_mul, hp]
  set R' : Subgroup P := R.comap ι with hR'
  have hRu : ∀ x ∈ R', x * u = u * x := by
    intro x hx
    apply hι
    rw [map_mul, map_mul, hιu]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hD.cent hx)
  have hRn : ∀ g : P, g * u = u * g → ∀ x ∈ R', g * x * g⁻¹ ∈ R' := by
    intro g hg x hx
    show ι (g * x * g⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer (hCt g hg)) (ι x)).mp hx
  have hinv : ∀ x ∈ R', x * x = 1 → x = 1 ∨ x = u := by
    intro x hx hxx
    by_cases h1 : x = 1
    · exact Or.inl h1
    · right
      apply hι
      rw [hιu]
      refine hD.eq_of_orderOf_eq_two hx ?_
      rw [orderOf_injective ι hι]
      exact orderOf_eq_prime (by rw [sq]; exact hxx) h1
  have hHt : β.range.map ι ≤ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hCt x (u_comm β hβu hx)
  have hodd' : NoOddNormal (β.range.map ι) := hodd.map ι hι
  have h3 : ∀ x ∈ R', x ∈ β.range → x ^ 3 = 1 → x = 1 := by
    intro x hx hxH hx3
    set M₀ : Subgroup G := β.range.map ι ⊓ oddCoreImg R with hM₀def
    have hM₀n : (M₀.subgroupOf (β.range.map ι)).Normal := by
      refine ⟨fun m hm g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      obtain ⟨hmH, hmO⟩ := Subgroup.mem_inf.mp hm
      refine Subgroup.mem_inf.mpr ⟨?_, datum_conj_mem_oddCoreImg hD (hHt g.2) hmO⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hmH) (Subgroup.inv_mem _ g.2)
    have hM₀odd : Odd (Nat.card M₀) :=
      (odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    have hM₀ : M₀ = ⊥ := hodd' M₀ inf_le_left hM₀n hM₀odd
    have hxM : ι x ∈ M₀ := Subgroup.mem_inf.mpr ⟨⟨x, hxH, rfl⟩,
      mem_oddCoreImg_of_pow_three hD hx (by rw [← map_pow, hx3, map_one])⟩
    rw [hM₀, Subgroup.mem_bot] at hxM
    exact hι (by rw [hxM, map_one])
  have hR'p := le_pair_of_normal hF β hker hβu hw hwu hnorm hcent hRu hRn hinv h3
  have hRN : ∀ g ∈ R, g ∈ N → g = 1 ∨ g = t := by
    intro g hg hgN
    obtain ⟨p, rfl⟩ := hιs g hgN
    rcases hR'p p hg with h | h
    · left
      rw [h, map_one]
    · right
      rw [h, hιu]
  have htt : t * t = 1 := by rw [← sq, ← hD.order, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h1
    have := hD.order
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hRH : R ≤ Subgroup.centralizer ((β.range.map ι : Subgroup G) : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcl : β.range.map ι ≤
        Subgroup.closure (ι '' {x : P | x ∈ β.range ∧ x ^ 3 = 1}) := by
      rw [← MonoidHom.map_closure]
      exact Subgroup.map_mono (range_le_closure hF β)
    refine (commute_of_commutator_mem (m := r) (X := ι '' {x : P | x ∈ β.range ∧ x ^ 3 = 1})
      (Z := Subgroup.zpowers t) (n := 3) ?_ ?_ ?_ ?_ y (hcl hy)).symm
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hx.2, map_one]
    · intro z hz hz3
      rcases eq_one_or_eq_of_mem_zpowers htt hz with rfl | rfl
      · rfl
      · exfalso
        apply ht1
        rw [pow_succ, sq, htt, one_mul] at hz3
        exact hz3
    · intro z hz y hy
      rcases eq_one_or_eq_of_mem_zpowers htt hz with rfl | rfl
      · rw [one_mul, mul_one]
      · obtain ⟨x, hx, rfl⟩ := hy
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hHt ⟨x, hx.1, rfl⟩)).symm
    · rintro _ ⟨x, hx, rfl⟩
      have hxt : ι x ∈ Subgroup.centralizer ({t} : Set G) := hHt ⟨x, hx.1, rfl⟩
      have hcR : r * ι x * r⁻¹ * (ι x)⁻¹ ∈ R := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hxt) r⁻¹).mp (inv_mem hr)
        have h2 := mul_mem hr h1
        rwa [show r * (ι x * r⁻¹ * (ι x)⁻¹) = r * ι x * r⁻¹ * (ι x)⁻¹ by group] at h2
      have hcN : r * ι x * r⁻¹ * (ι x)⁻¹ ∈ N :=
        mul_mem ((inferInstance : N.Normal).conj_mem _ (hιN x) r) (inv_mem (hιN x))
      rcases hRN _ hcR hcN with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers t
  obtain ⟨φ, hφi, hφR, -⟩ := datum_exists_q8 hD
  let ψ : QuaternionGroup 2 →* MulAut ↥N := MulAut.conjNormal.comp φ
  have hψ : ∀ q (n : ↥N), ((ψ q n : ↥N) : G) = φ q * n * (φ q)⁻¹ := fun _ _ => rfl
  refine hA.map e.symm ψ ?_ fun q h hh => Subtype.ext ?_
  · rw [injective_iff_map_eq_one]
    intro q hq
    have h1 : φ q ∈ Subgroup.centralizer (N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have := congrArg Subtype.val (DFunLike.congr_fun hq ⟨n, hn⟩)
      rw [hψ] at this
      calc n * φ q = φ q * n * (φ q)⁻¹ * φ q := by rw [this]; rfl
        _ = φ q * n := by group
    rw [hC, Subgroup.mem_bot] at h1
    exact hφi (h1.trans (map_one φ).symm)
  · rw [hψ]
    obtain ⟨x, hx, rfl⟩ := hh
    have := Subgroup.mem_centralizer_iff.mp (hRH (hφR q)) (ι x) ⟨x, hx, rfl⟩
    change φ q * ι x * (φ q)⁻¹ = ι x
    rw [← this, mul_assoc, mul_inv_cancel, mul_one]

end Q3L4

end CFSG.ClassicalInvolution.Q3.TA3
