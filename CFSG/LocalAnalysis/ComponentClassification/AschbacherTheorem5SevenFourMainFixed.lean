module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainKL

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}
  {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem not_dihedral_factor (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar) {i : Fin 2}
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar i)) (k : Fin 2) :
    ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k) := by
  have : Finite (D ⧸ aschbacherThm5OddCore D) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨h, hh, hik⟩ := hin.lemma_6_3 hC i k
  have hmap := map_onQuotient_factor (Abar := Abar) ⟨h, hh⟩ hik
  let e : Abar i ≃* Abar k := ((Abar i).equivMapOfInjective _
    (onQuotient D ⟨h, hh⟩).injective).trans (MulEquiv.subgroupCongr hmap)
  exact fun hk => hnd (hasDihedralSylowTwo_of_mulEquiv e.symm hk)

theorem not_dihedral_conjFactor {k : Fin 2}
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k)) (g : G) :
    ¬ AschbacherKnownGroup.HasDihedralSylowTwo (conjFactors D Abar g k) := by
  have : Finite (D ⧸ aschbacherThm5OddCore D) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have : Finite (conjFactors D Abar g k) :=
    Finite.of_injective _ (conjFactorsEquiv g k).symm.injective
  exact fun hk => hnd (hasDihedralSylowTwo_of_mulEquiv (conjFactorsEquiv g k).symm hk)

namespace FieldHyps

variable {t g : G}

theorem exists_lift_fixed (hF : FieldHyps D Abar t g) (k : Fin 2) {p : Abar k}
    (hp : hF.alpha k p = p) {n : ℕ} (hpn : p ^ (2 ^ n) = 1) :
    ∃ w : D, (w : G) ∈ aschbacherThm5Preimage D (Abar k) ∧ (w : G) * t = t * w ∧
      (∃ e : ℕ, (w : G) ^ (2 ^ e) = 1) ∧
      QuotientGroup.mk' (aschbacherThm5OddCore D) w = (p : D ⧸ aschbacherThm5OddCore D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G)
  set t' : H := ⟨t, hF.mem⟩
  have ht' : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe]; exact hF.two
  obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D)
    (p : D ⧸ aschbacherThm5OddCore D)
  have hdA : (d : G) ∈ aschbacherThm5Preimage D (Abar k) := by
    rw [mem_preimage_iff, hd]
    exact p.2
  set h₀ : H := Subgroup.inclusion Subgroup.le_normalizer d
  have hqE : quotientEmbedding D (p : D ⧸ aschbacherThm5OddCore D) = toBar D h₀ := by
    rw [← hd, quotientEmbedding_mk]
    rfl
  have hcomm : toBar D h₀ ∈ Subgroup.centralizer ({toBar D t'} : Set (Bar D)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hqE]
    have h1 := quotientEmbedding_onQuotient (D := D) t' (p : D ⧸ aschbacherThm5OddCore D)
    rw [← hF.alpha_apply k p, hp] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1.symm).symm
  rw [centralizer_toBar_eq t' ht'] at hcomm
  obtain ⟨h, hh, hhe⟩ := hcomm
  have hhA : (h : G) ∈ aschbacherThm5Preimage D (Abar k) := by
    have hker : h₀⁻¹ * h ∈ coreIn D := by
      rw [← ker_toBar, MonoidHom.mem_ker, map_mul, map_inv, hhe, inv_mul_cancel]
    have hmem := Subgroup.mem_subgroupOf.mp hker
    have hcore := core_le_preimage D (Abar k) hmem
    have h2 : (h : G) = (h₀ : G) * ((h₀⁻¹ * h : H) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [h2]
    exact Subgroup.mul_mem _ hdA hcore
  set C : Subgroup H := Subgroup.centralizer ({t'} : Set H) ⊓
    (aschbacherThm5Preimage D (Abar k)).subgroupOf H
  have hhC : h ∈ C := ⟨hh, Subgroup.mem_subgroupOf.mpr hhA⟩
  set V := Subgroup.zpowers (toBar D h)
  have hV2 : IsPGroup 2 V := by
    apply isPGroup_zpowers_two (k := n)
    rw [hhe, ← hqE, ← map_pow]
    have h1 : (p : D ⧸ aschbacherThm5OddCore D) ^ (2 ^ n) = 1 := by
      rw [← Subgroup.coe_pow, hpn, Subgroup.coe_one]
    rw [h1, map_one]
  have hVC : V ≤ C.map (QuotientGroup.mk' (coreIn D)) :=
    Subgroup.zpowers_le.mpr ⟨h, hhC, rfl⟩
  obtain ⟨W, hWC, hW2, -, hWmap⟩ := exists_isPGroup_lift (coreIn D) (coreIn_odd D) hV2 hVC
  have hmemV : toBar D h ∈ W.map (QuotientGroup.mk' (coreIn D)) := by
    rw [hWmap]
    exact Subgroup.mem_zpowers _
  obtain ⟨w, hwW, hwh⟩ := hmemV
  obtain ⟨hwt, hwA⟩ := hWC hwW
  have hwA' : (w : G) ∈ aschbacherThm5Preimage D (Abar k) := Subgroup.mem_subgroupOf.mp hwA
  have hwD : (w : G) ∈ D := preimage_le D (Abar k) hwA'
  refine ⟨⟨w, hwD⟩, hwA', ?_, ?_, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hwt)
  · obtain ⟨e, he⟩ := hW2 ⟨w, hwW⟩
    exact ⟨e, by
      have := congrArg (fun x : W => ((x : H) : G)) he
      simpa using this⟩
  · apply quotientEmbedding_injective D
    rw [quotientEmbedding_mk, hqE, ← hhe]
    exact hwh

theorem false_of_le_other (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    {R : Subgroup G} (hR : IsSylowOf 2 R (aschbacherThm5Preimage D (Abar i) ⊓
      Subgroup.centralizer ({t} : Set G)))
    (hRA' : R ≤ aschbacherThm5Preimage D (Abar i')) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := hF.alpha i with hαdef
  have hα : α ^ 2 = 1 := hF.alpha_sq i
  have hXp : Group.IsPerfect (Abar i) := semisimple_perfect _ (hC.hyp.hsemisimple i)
  obtain ⟨P, hPα⟩ := exists_invariant_sylow_two α hα
  set Z : Subgroup (Abar i) := ((R.subgroupOf D).map
    (QuotientGroup.mk' (aschbacherThm5OddCore D))).subgroupOf (Abar i) with hZdef
  have hmemZ : ∀ x : Abar i, x ∈ Z ↔ ∃ d : D, (d : G) ∈ R ∧
      QuotientGroup.mk' (aschbacherThm5OddCore D) d = (x : D ⧸ aschbacherThm5OddCore D) := by
    intro x
    rw [hZdef, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    simp only [Subgroup.mem_subgroupOf]
  have hZA' : ∀ x ∈ Z, (x : D ⧸ aschbacherThm5OddCore D) ∈ Abar i' := by
    intro x hx
    obtain ⟨d, hdR, hdx⟩ := (hmemZ x).mp hx
    rw [← hdx]
    exact (mem_preimage_iff D (Abar i') d).mp (hRA' hdR)
  have hZc : Z ≤ Subgroup.center (Abar i) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (hC.hyp.hcomm i' i hii'.symm _ (hZA' x hx) _ y.2).symm
  have hZ2 : IsPGroup 2 Z := by
    rintro ⟨x, hx⟩
    obtain ⟨d, hdR, hdx⟩ := (hmemZ x).mp hx
    obtain ⟨e, he⟩ := hR.isPGroup ⟨d, hdR⟩
    refine ⟨e, Subtype.ext (Subtype.ext ?_)⟩
    have he' : (d : G) ^ (2 ^ e) = 1 := congrArg Subtype.val he
    have hd' : d ^ (2 ^ e) = 1 := Subtype.ext (by simpa using he')
    change (x : D ⧸ aschbacherThm5OddCore D) ^ (2 ^ e) = 1
    rw [← hdx, ← map_pow, hd', map_one]
  have : Z.Normal := Subgroup.normal_of_le_center hZc
  have hZP : Z ≤ (P : Subgroup (Abar i)) := hZ2.le_sylow_of_normal P
  have hfixZ : ∀ x ∈ Z, α x = x := by
    intro x hx
    obtain ⟨d, hdR, hdx⟩ := (hmemZ x).mp hx
    apply Subtype.ext
    rw [hF.alpha_apply, ← hdx, onQuotient_mk]
    congr 1
    apply Subtype.ext
    rw [onD_apply]
    have hdt : (d : G) * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp (hR.le hdR).2
    change t * (d : G) * t⁻¹ = d
    rw [← hdt, mul_inv_cancel_right]
  have hZα : Z.map (α : Abar i →* Abar i) = Z := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change α x ∈ Z
      rw [hfixZ x hx]
      exact hx
    · intro x hx
      exact ⟨x, hx, hfixZ x hx⟩
  have hZrank : CFSG.Open.pRank 2 Z ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hsZ, u, huZ, hs, hu, hsu⟩ := exists_two_involutions (E := Z) (by omega)
    apply hsu
    have hcomm : s * u = u * s := ((Subgroup.mem_center_iff.mp (hZc huZ)) s)
    exact hF.fixed_involution_eq hin hC hii' hs hu hcomm (hfixZ s hsZ) (hfixZ u huZ)
  have hZcyc : IsCyclic Z := by
    rcases cyclic_or_quaternion_of_pRank_le_one hZ2 hZrank with hcyc | ⟨n, hn, ⟨e⟩⟩
    · exact hcyc
    · exfalso
      have hm : 2 ≤ 2 ^ (n - 2) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have htop : Subgroup.center (QuaternionGroup (2 ^ (n - 2))) = ⊤ := by
        rw [eq_top_iff]
        intro q _
        rw [Subgroup.mem_center_iff]
        intro q'
        obtain ⟨z, rfl⟩ := e.surjective q
        obtain ⟨z', rfl⟩ := e.surjective q'
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp (hZc z.2) z'
      have h1 := CFSG.Semidihedral.QuaternionAutomorphismLifting.center_card _ hm
      rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, QuaternionGroup.card] at h1
      omega
  have hfix : ∀ p ∈ (P : Subgroup (Abar i)), α p = p → p ∈ Z := by
    intro p hpP hαp
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨p, hpP⟩
    have hpn : p ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    obtain ⟨w, hwA, hwt, ⟨e, he⟩, hwp⟩ := hF.exists_lift_fixed i hαp hpn
    have hwY : (w : G) ∈ aschbacherThm5Preimage D (Abar i) ⊓
        Subgroup.centralizer ({t} : Set G) :=
      ⟨hwA, Subgroup.mem_centralizer_singleton_iff.mpr hwt⟩
    obtain ⟨P', hP', hwP'⟩ := exists_isSylowOf_le (Subgroup.zpowers_le.mpr hwY)
      (isPGroup_zpowers_two he)
    obtain ⟨c, hcY, hc⟩ := IsSylowOf.exists_conj hR hP'
    have hwR : (w : G) ∈ R.map (MulAut.conj c).toMonoidHom :=
      hc ▸ hwP' (Subgroup.mem_zpowers _)
    obtain ⟨ρ, hρR, hρw⟩ := hwR
    have hcD : c ∈ D := preimage_le D (Abar i) hcY.1
    have hρD : ρ ∈ D := preimage_le D (Abar i) (hR.le hρR).1
    rw [hmemZ]
    refine ⟨⟨ρ, hρD⟩, hρR, ?_⟩
    rw [← hwp]
    have hwprod : w = ⟨c, hcD⟩ * ⟨ρ, hρD⟩ * (⟨c, hcD⟩ : D)⁻¹ := by
      apply Subtype.ext
      rw [← hρw]
      simp [MulAut.conj_apply]
    rw [hwprod, map_mul, map_mul, map_inv]
    have hρ' : QuotientGroup.mk' (aschbacherThm5OddCore D) (⟨ρ, hρD⟩ : D) ∈ Abar i' :=
      (mem_preimage_iff D (Abar i') ⟨ρ, hρD⟩).mp (hRA' hρR)
    have hc' : QuotientGroup.mk' (aschbacherThm5OddCore D) (⟨c, hcD⟩ : D) ∈ Abar i :=
      (mem_preimage_iff D (Abar i) ⟨c, hcD⟩).mp hcY.1
    rw [← hC.hyp.hcomm i' i hii'.symm _ hρ' _ hc', mul_inv_cancel_right]
  have hPnt : Nontrivial (P : Subgroup (Abar i)) := by
    have hrankP : 2 ≤ CFSG.Open.pRank 2 (P : Subgroup (Abar i)) := by
      rw [(CFSG.SectionRank.pRank_sylow P).1]
      exact hF.two_le_pRank_top hin hC i
    obtain ⟨s, hsP, -, -, hs, -, -⟩ := exists_two_involutions hrankP
    refine ⟨⟨⟨s, hsP⟩, 1, fun h => ?_⟩⟩
    have h1 : s = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hs
    omega
  set β := restrictAut α (P : Subgroup (Abar i)) hPα
  have hβ : β ^ 2 = 1 := restrictAut_sq α hα _ hPα
  obtain ⟨q, hq1, hβq⟩ := exists_fixed_ne_one P.isPGroup' β hβ
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have hqZ : (q : Abar i) ∈ Z := hfix q q.2 (congrArg Subtype.val hβq)
    rw [hbot, Subgroup.mem_bot] at hqZ
    exact hq1 (Subtype.ext hqZ)
  have hrankP : 2 ≤ CFSG.Open.pRank 2 (P : Subgroup (Abar i)) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1]
    exact hF.two_le_pRank_top hin hC i
  obtain ⟨s, hsP, u, huP, hs, hu, hsu⟩ := exists_two_involutions hrankP
  exact false_of_fixed_central hXp α hα P hPα Z hZc hZP hZα hZcyc hZne hfix hsP huP hs hu hsu

end FieldHyps

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
