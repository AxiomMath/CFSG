module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainSylow
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainFactors
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainInner

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}
  {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem isPGroup_zpowers_two {y : G} {k : ℕ} (hy : y ^ (2 ^ k) = 1) :
    IsPGroup 2 (Subgroup.zpowers y) := by
  rintro ⟨z, hz⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨k, Subtype.ext ?_⟩
  change (y ^ n) ^ (2 ^ k) = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]

theorem IsSylowOf.card_le_of_le {p : ℕ} [Fact p.Prime] {P Q K : Subgroup G}
    (hP : IsSylowOf p P K) (hQK : Q ≤ K) (hQ : IsPGroup p Q) : Nat.card Q ≤ Nat.card P := by
  obtain ⟨P', hP', hQP'⟩ := exists_isSylowOf_le hQK hQ
  rw [hP.card_eq, ← hP'.card_eq]
  exact Subgroup.card_le_of_le hQP'

omit [Finite G] in
theorem mem_normalizer_inf {A K : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hK : x ∈ K) :
    x ∈ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨hyA, hyK⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hA y).mp hyA,
      K.mul_mem (K.mul_mem hK hyK) (K.inv_mem hK)⟩
  · rintro ⟨hyA, hyK⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hA y).mpr hyA, ?_⟩
    have h1 := K.mul_mem (K.mul_mem (K.inv_mem hK) hyK) hK
    simpa [mul_assoc] using h1

namespace FieldHyps

variable {t g : G}

theorem isSylowOf_inf_normalizer (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i') {j m : Fin 2} (hjm : j ≠ m)
    (hnd' : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (conjFactors D Abar g m))
    (htm : t ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m))
    {R : Subgroup G} (hR : IsSylowOf 2 R (aschbacherThm5Preimage D (Abar i) ⊓
      Subgroup.centralizer ({t} : Set G))) :
    IsSylowOf 2 R (aschbacherThm5Preimage D (Abar i) ⊓
      Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  set B := rightConjugate D g with hBdef
  set K := Subgroup.normalizer ((B : Subgroup G) : Set G) with hKdef
  set Lm := aschbacherThm5Preimage B (conjFactors D Abar g m) with hLm
  set Lj := aschbacherThm5Preimage B (conjFactors D Abar g j) with hLj
  have hC' := hC.conj g
  have hN' := normalizer_rightConjugate D g
  have hcK : ∀ x : G, x * t = t * x → x ∈ K := by
    intro x hx
    change x ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)
    rw [hN']
    exact (hF.hyp71 hC).centralizer_le (Subgroup.mem_centralizer_singleton_iff.mpr hx)
  have htK : t ∈ K := hcK t rfl
  have ht2 : t * t = 1 := by rw [← sq, ← hF.two]; exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  have htA : t ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hF.norm i)
  have hRX : R ≤ A ⊓ K := fun x hx =>
    ⟨(hR.le hx).1, hcK x (Subgroup.mem_centralizer_singleton_iff.mp (hR.le hx).2)⟩
  have htX : t ∈ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := mem_normalizer_inf htA htK
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) :=
    isPGroup_zpowers_two (k := 1) (by rw [pow_one, sq]; exact ht2)
  have hRt : R ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro x hx
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp (hR.le hx).2
    exact ((hc.zpow_right n).eq).symm
  have hRt2 : IsPGroup 2 (R ⊔ Subgroup.zpowers t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hR.isPGroup hT2 hRt
  have hRtY : R ⊔ Subgroup.zpowers t ≤ (A ⊓ K) ⊔ Subgroup.zpowers t :=
    sup_le_sup_right hRX _
  obtain ⟨S₀, hS₀, hRS₀⟩ := exists_isSylowOf_le hRtY hRt2
  have hYN : (A ⊓ K) ⊔ Subgroup.zpowers t ≤
      Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr htX)
  have hP : IsSylowOf 2 (S₀ ⊓ (A ⊓ K)) (A ⊓ K) := hS₀.inf_of_le_normalizer le_sup_left hYN
  set P := S₀ ⊓ (A ⊓ K) with hPdef
  have hRP : R ≤ P := le_inf (le_sup_left.trans hRS₀) hRX
  have htS₀ : t ∈ S₀ := hRS₀ (le_sup_right (a := R) (Subgroup.mem_zpowers t))
  have htP : t ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyS, hyX⟩
      exact ⟨S₀.mul_mem (S₀.mul_mem htS₀ hyS) (S₀.inv_mem htS₀),
        (Subgroup.mem_normalizer_iff.mp htX y).mp hyX⟩
    · rintro ⟨hyS, hyX⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp htX y).mpr hyX⟩
      have h1 := S₀.mul_mem (S₀.mul_mem (S₀.inv_mem htS₀) hyS) htS₀
      simpa [mul_assoc] using h1
  have hPC : P ⊓ Subgroup.centralizer ({t} : Set G) = R :=
    hR.eq_of_le (le_inf hRP fun x hx => (hR.le hx).2)
      (inf_le_inf_right _ (inf_le_right.trans inf_le_left)) hP.isPGroup.to_inf_left
  by_cases hlt : P ⊓ Subgroup.centralizer ({t} : Set G) < P
  swap
  · have hPR : P = R := by
      rw [← hPC]
      by_contra hne
      exact hlt (lt_of_le_of_ne inf_le_left (Ne.symm hne))
    rw [← hPR]
    exact hP
  exfalso
  obtain ⟨w, hwP, hwt, hcR⟩ := exists_mul_fixed_of_lt hP.isPGroup ht2 htP hlt
  rw [hPC] at hcR
  set c := w⁻¹ * (t * w * t⁻¹) with hcdef
  have hcA : c ∈ A := (hR.le hcR).1
  have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp (hR.le hcR).2
  have hcw : c * t = w⁻¹ * t * w := by rw [hcdef]; group
  have hc1 : c ≠ 1 := by
    intro h1
    apply hwt
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : t = w⁻¹ * t * w := by rw [← hcw, h1, one_mul]
    calc w * t = w * (w⁻¹ * t * w) := by rw [← h2]
      _ = t * w := by group
  have hc2 : c * c = 1 := by
    have h1 : (c * t) * (c * t) = 1 := by
      rw [hcw]
      calc w⁻¹ * t * w * (w⁻¹ * t * w) = w⁻¹ * (t * t) * w := by group
        _ = 1 := by rw [ht2, mul_one, inv_mul_cancel]
    have h3 : (c * t) * (c * t) = c * c := by
      calc (c * t) * (c * t) = c * (t * c) * t := by group
        _ = c * (c * t) * t := by rw [← hct]
        _ = c * c * (t * t) := by group
        _ = c * c := by rw [ht2, mul_one]
    rw [← h3, h1]
  have hcord : orderOf c = 2 := orderOf_eq_prime (by rw [sq]; exact hc2) hc1
  have hctwo : ∃ n : ℕ, c ^ (2 ^ n) = 1 := two_power_of_orderOf hcord
  have hwK : w ∈ K := ((hP.le hwP).2)
  obtain ⟨k, hk⟩ := hC'.hyp.hperm w⁻¹ (K.inv_mem hwK) m
  have hctk : c * t ∈ aschbacherThm5Preimage B (conjFactors D Abar g k) := by
    rw [← hk, hcw]
    refine ⟨t, htm, ?_⟩
    simp
  rcases fin_two_cases hjm k with hkj | hkm
  ·
    rw [hkj] at hctk
    have hctc : aschbacherThm5Centralizes (aschbacherThm5Core B) Lm (c * t) :=
      cross_factor_centralizes B (conjFactors D Abar g) hC'.hyp.hcomm m j hjm.symm _ hctk
    have hcN : c ∈ K := hcK c hct
    have hcLm : Lm.map (MulAut.conj c).toMonoidHom = Lm := by
      have h1 := mem_normalizer_of_centralizes (core_le_preimage _ _) hctc
      have h2 : t ∈ Subgroup.normalizer (Lm : Set G) := Subgroup.le_normalizer htm
      have h3 : c = (c * t) * t⁻¹ := by group
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
      rw [h3]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    have hcnorm : ∀ k' : Fin 2, (aschbacherThm5Preimage B (conjFactors D Abar g k')).map
        (MulAut.conj c).toMonoidHom = aschbacherThm5Preimage B (conjFactors D Abar g k') := by
      intro k'
      rcases fin_two_cases hjm k' with h | h
      · rw [h]
        exact map_other_of_map hC'.hyp hcN hjm.symm hcLm
      · rw [h]
        exact hcLm
    have hF' := hF.mirror hC hii' hcA hcord hct hcnorm
    apply hF'.false_of_centralizes_inv_mul hin hC' hjm.symm hnd' htm
    have he : t⁻¹ * c = c * t := by rw [htinv, hct]
    rw [he]
    exact hctc
  ·
    rw [hkm] at hctk
    have hcLm : c ∈ Lm := by
      have h1 := Lm.mul_mem hctk (Lm.inv_mem htm)
      rwa [mul_inv_cancel_right] at h1
    exact hF.not_centralizes_conj hin hC (l := j) hcA hctwo hc1
      (cross_factor_centralizes B (conjFactors D Abar g) hC'.hyp.hcomm j m hjm _ hcLm)

theorem inf_normalizer_le_normalizer (hC : Counterexample G D 2 Abar) {i j m : Fin 2}
    (hjm : j ≠ m) {R : Subgroup G}
    (hR : IsSylowOf 2 R (aschbacherThm5Preimage D (Abar i) ⊓
      Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)))
    (hRL : R ≤ Subgroup.normalizer
      ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
        Set G)) :
    aschbacherThm5Preimage D (Abar i) ⊓
        Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) ≤
      Subgroup.normalizer
        ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
          Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := rightConjugate D g with hBdef
  set K := Subgroup.normalizer ((B : Subgroup G) : Set G) with hKdef
  set Lm := aschbacherThm5Preimage B (conjFactors D Abar g m) with hLm
  set X := aschbacherThm5Preimage D (Abar i) ⊓ K with hXdef
  have hC' := hC.conj g
  have hother : ∀ y ∈ K, y ∈ Subgroup.normalizer
      ((aschbacherThm5Preimage B (conjFactors D Abar g j) : Subgroup G) : Set G) →
      y ∈ Subgroup.normalizer (Lm : Set G) := fun y hy hyj =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_other_of_map hC'.hyp hy hjm
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hyj))
  have htwo : ∀ y ∈ X, ∀ n : ℕ, y ^ (2 ^ n) = 1 → y ∈ Subgroup.normalizer (Lm : Set G) := by
    intro y hy n hyn
    have hQ : Subgroup.zpowers y ≤ X := Subgroup.zpowers_le.mpr hy
    obtain ⟨P', hP', hyP'⟩ := exists_isSylowOf_le hQ (isPGroup_zpowers_two hyn)
    obtain ⟨k, hkX, hk⟩ := IsSylowOf.exists_conj hR hP'
    have hρR : k⁻¹ * y * k ∈ R := by
      have h1 : y ∈ R.map (MulAut.conj k).toMonoidHom := hk ▸ hyP' (Subgroup.mem_zpowers y)
      obtain ⟨ρ, hρ, hρy⟩ := h1
      have h2 : ρ = k⁻¹ * y * k := by
        rw [← hρy]
        simp [MulAut.conj_apply, mul_assoc]
      rw [← h2]
      exact hρ
    have hkK : k ∈ K := hkX.2
    have hρN : Lm.map (MulAut.conj (k⁻¹ * y * k)).toMonoidHom = Lm :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRL hρR)
    obtain ⟨l, hl⟩ := hC'.hyp.hperm k hkK m
    have hmap : (Lm.map (MulAut.conj k).toMonoidHom).map (MulAut.conj y).toMonoidHom =
        Lm.map (MulAut.conj k).toMonoidHom := by
      rw [← map_conj_mul, show y * k = k * (k⁻¹ * y * k) by group, map_conj_mul, hρN]
    rw [hl] at hmap
    rcases fin_two_cases hjm l with h | h
    · rw [h] at hmap
      exact hother _ hy.2 (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap)
    · rw [h] at hmap
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  intro x hx
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hxb : x ^ b ∈ Subgroup.normalizer (Lm : Set G) := by
    apply htwo _ (X.pow_mem hx b) a
    rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  have hxx : x * x ∈ Subgroup.normalizer (Lm : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (sq_map_factor hC'.hyp hx.2 m)
  obtain ⟨c, rfl⟩ := hb
  have hx1 : x = ((x * x) ^ c)⁻¹ * x ^ (2 * c + 1) := by
    rw [pow_succ, pow_mul, sq, inv_mul_cancel_left]
  rw [hx1]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hxx c)) hxb

end FieldHyps

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
