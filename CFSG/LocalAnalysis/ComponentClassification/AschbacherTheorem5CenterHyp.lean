module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5CenterQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Conjugation
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Hyp
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Semisimple

public noncomputable section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace CenterQuotient

theorem centralizes_map {G H : Type*} [Group G] [Group H] (f : G →* H) {O A : Subgroup G}
    {y : G} (hy : aschbacherThm5Centralizes O A y) :
    aschbacherThm5Centralizes (O.map f) (A.map f) (f y) := by
  rintro _ ⟨a, ha, rfl⟩
  have hmem := Subgroup.mem_map_of_mem f (hy a ha)
  simpa only [map_mul, map_inv] using hmem

theorem centralizes_mul_central {G : Type*} [Group G] {O A : Subgroup G} {y z : G}
    (hy : aschbacherThm5Centralizes O A y) (hz : z ∈ Subgroup.center G) :
    aschbacherThm5Centralizes O A (y * z) := by
  intro a ha
  have hcomm := Subgroup.mem_center_iff.mp hz
  have hyz : y * z = z * y := hcomm y
  have haz : z⁻¹ * a⁻¹ * z = a⁻¹ := by rw [mul_assoc, hcomm a⁻¹, inv_mul_cancel_left]
  have heq : (y * z)⁻¹ * a⁻¹ * (y * z) * a = y⁻¹ * (z⁻¹ * a⁻¹ * z) * y * a := by
    rw [hyz]
    group
  rw [heq, haz]
  exact hy a ha

theorem conj_centralizes_of_central_image {G : Type*} [Group G] {O A : Subgroup G} {a : G}
    (ha : aschbacherThm5Centralizes O A a)
    (hcentral : QuotientGroup.mk' (Subgroup.center G) a ∈
      Subgroup.center (G ⧸ Subgroup.center G)) (g : G) :
    aschbacherThm5Centralizes O A (g⁻¹ * a * g) := by
  have hz : a⁻¹ * (g⁻¹ * a * g) ∈ Subgroup.center G := by
    have hcomm := Subgroup.mem_center_iff.mp hcentral (QuotientGroup.mk' (Subgroup.center G) g)
    have hone : QuotientGroup.mk' (Subgroup.center G) (a⁻¹ * (g⁻¹ * a * g)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ _ (QuotientGroup.mk' _ g),
        ← hcomm]
      group
    exact (QuotientGroup.eq_one_iff _).mp hone
  have heq : g⁻¹ * a * g = a * (a⁻¹ * (g⁻¹ * a * g)) := by group
  rw [heq]
  exact centralizes_mul_central ha hz

theorem fixed_of_central_displacement {Q : Type*} [Group Q] (σ : Q →* Q) (L : Subgroup Q)
    [Group.IsPerfect L] (hcentral : ∀ x ∈ L, (σ x)⁻¹ * x ∈ Subgroup.center Q) :
    ∀ x ∈ L, σ x = x := by
  let displacement : L →* Subgroup.center Q :=
    { toFun := fun x => ⟨(σ x)⁻¹ * x, hcentral x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have hx := Subgroup.mem_center_iff.mp (hcentral x x.2) (σ y)⁻¹
        change (σ (x * y))⁻¹ * (x * y : Q) = (σ x)⁻¹ * x * ((σ y)⁻¹ * y)
        rw [map_mul, mul_inv_rev,
          show (σ y)⁻¹ * (σ x)⁻¹ * ((x : Q) * y) = (σ y)⁻¹ * ((σ x)⁻¹ * x) * y by group, hx]
        group) }
  have hker : commutator L ≤ displacement.ker := Abelianization.commutator_subset_ker _
  rw [Group.IsPerfect.commutator_eq_top] at hker
  intro x hx
  have hone : displacement ⟨x, hx⟩ = 1 := hker (Subgroup.mem_top _)
  have hval : (σ x)⁻¹ * x = 1 := congrArg Subtype.val hone
  exact inv_mul_eq_one.mp hval

theorem exists_two_element_lift {G H : Type*} [Group G] [Finite G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) {y : H} {k : ℕ} (hy : y ^ (2 ^ k) = 1) :
    ∃ x : G, f x = y ∧ ∃ m : ℕ, x ^ (2 ^ m) = 1 := by
  obtain ⟨s, rfl⟩ := hf y
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos s).ne'
  have hcop : b.Coprime (orderOf (f s)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hy)
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hb))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(s ^ b) ^ m, by rw [map_pow, map_pow, hm], a, ?_⟩
  calc ((s ^ b) ^ m) ^ (2 ^ a) = (s ^ (2 ^ a * b)) ^ m := by
        simp only [← pow_mul]
        congr 1
        ring
    _ = 1 := by rw [← hab, pow_orderOf_eq_one, one_pow]

theorem semisimple_map {Q R : Type*} [Group Q] [Group R] (φ : Q →* R)
    (hker : φ.ker ≤ Subgroup.center Q) (X : Subgroup Q) (hX : aschbacherThm5IsSemisimple X) :
    aschbacherThm5IsSemisimple (X.map φ) := by
  obtain ⟨k, K, hk, hK, hcomm, hgen⟩ := hX
  refine ⟨k, fun l => (K l).map φ, hk, fun l => ⟨Subgroup.map_mono (hK l).1, ?_⟩, ?_, ?_⟩
  · have hquasisimple := Quasisimple.range_quasisimple_of_ker_ne_top (hK l).2
      (φ.comp (K l).subtype) ?_
    · rwa [MonoidHom.range_comp, Subgroup.range_subtype] at hquasisimple
    · intro htop
      have hcentral : K l ≤ Subgroup.center Q := by
        intro x hx
        apply hker
        have hmem : (⟨x, hx⟩ : K l) ∈ (φ.comp (K l).subtype).ker := htop ▸ Subgroup.mem_top _
        exact hmem
      have : Group.IsPerfect (K l) := ⟨(hK l).2.1⟩
      have hbot := Quasisimple.perfect_le_center_eq_bot (K l) hcentral
      exact ((K l).nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial (hK l).2)) hbot
  · rintro l m hlm _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm l m hlm x hx y hy]
  · rw [← Subgroup.map_iSup, hgen]

theorem injective_of_semisimple {Q : Type*} [Group Q] {r : ℕ} (Abar : Fin r → Subgroup Q)
    (hsemisimple : ∀ i, aschbacherThm5IsSemisimple (Abar i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x) :
    Function.Injective Abar := by
  intro i j heq
  by_contra hij
  have hcentral : Abar i ≤ Subgroup.centralizer (Abar i : Set Q) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm i j hij x hx y (heq ▸ hy)).symm
  have : Group.IsPerfect (Abar i) := semisimple_perfect (Abar i) (hsemisimple i)
  have hbot := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
  rw [Subgroup.commutator_eq_self] at hbot
  exact semisimple_ne_bot (Abar i) (hsemisimple i) hbot

variable {G : Type*} [Group G] [Finite G]

theorem centralizes_of_quotient (D : Subgroup G) (r : ℕ)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hsemisimple : ∀ i, aschbacherThm5IsSemisimple (Abar i))
    (hii : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) → g ∈ Subgroup.normalizer (D : Set G))
    (i : Fin r) (s : G)
    (hs : aschbacherThm5Centralizes (aschbacherThm5Core (quotientSubgroup D))
      (aschbacherThm5Preimage (quotientSubgroup D) (quotientFactors D Abar i))
      (QuotientGroup.mk' (Subgroup.center G) s)) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) s := by
  rw [quotientFactors_apply, preimage_center_quotient, core_center_quotient] at hs
  have hstep : ∀ a ∈ aschbacherThm5Preimage D (Abar i),
      s⁻¹ * a⁻¹ * s * a ∈ aschbacherThm5Core D ⊔ Subgroup.center G := by
    intro a ha
    have hmem := hs _ (Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center G)) ha)
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at hmem
    have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center G))
      (aschbacherThm5Core D)
    rw [QuotientGroup.ker_mk'] at hcomap
    rw [← hcomap]
    exact hmem
  have hnormalizer : s ∈ Subgroup.normalizer (D : Set G) := by
    have hsinv := enters_normalizer_of_preimage_le D r Abar hii i s⁻¹ (by
      intro a ha
      refine ⟨a * (s⁻¹ * a⁻¹ * s * a)⁻¹, ?_, ?_⟩
      · apply Subgroup.mul_mem _ (Subgroup.le_normalizer (preimage_le D _ ha))
        apply Subgroup.inv_mem
        exact sup_le ((core_le D).trans Subgroup.le_normalizer)
          (Subgroup.center_le_normalizer _) (hstep a ha)
      · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
        group)
    simpa only [inv_inv] using (Subgroup.normalizer (D : Set G)).inv_mem hsinv
  have : Group.IsPerfect (Abar i) := semisimple_perfect (Abar i) (hsemisimple i)
  have hfixed := fixed_of_central_displacement
    (onQuotient D ⟨s⁻¹, Subgroup.inv_mem _ hnormalizer⟩).toMonoidHom (Abar i) ?_
  · intro a ha
    have hd : a ∈ D := preimage_le D (Abar i) ha
    have hx := hfixed (QuotientGroup.mk' (aschbacherThm5OddCore D) ⟨a, hd⟩)
      ((mem_preimage_iff D (Abar i) ⟨a, hd⟩).mp ha)
    rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, onQuotient_mk, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq] at hx
    have hcore := (mem_core_iff D _).mpr hx
    convert hcore using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, onD_apply, inv_inv]
    group
  · intro x hx
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hda : d.val ∈ aschbacherThm5Preimage D (Abar i) := (mem_preimage_iff D (Abar i) d).mpr hx
    rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, onQuotient_mk, ← map_inv, ← map_mul]
    apply mk_mem_center_of_mem_core_sup_center
    convert hstep d.val hda using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, onD_apply, inv_inv]
    group

end CenterQuotient

open CenterQuotient

theorem hyp61_center_quotient {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)} (hyp : Hyp61 G D r Abar) :
    Hyp61 (G ⧸ Subgroup.center G) (quotientSubgroup D) r (quotientFactors D Abar) := by
  have hcomapN := comap_normalizer_center_quotient D r hyp.hr Abar hyp.hii
  have hsemisimple : ∀ i, aschbacherThm5IsSemisimple (quotientFactors D Abar i) := fun i =>
    semisimple_map (factorMap D) (ker_factorMap_le_center D) (Abar i) (hyp.hsemisimple i)
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ quotientFactors D Abar i,
      ∀ y ∈ quotientFactors D Abar j, x * y = y * x := by
    rintro i j hij _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hyp.hcomm i j hij x hx y hy]
  refine ⟨hyp.hr, injective_of_semisimple _ hsemisimple hcomm, hsemisimple, hcomm, ?_, ?_, ?_, ?_⟩
  ·
    change ⨆ i, (Abar i).map (factorMap D) = ⊤
    rw [← Subgroup.map_iSup, hyp.hgen, Subgroup.map_top_of_surjective _ (factorMap_surjective D)]
  ·
    intro h' hh' i
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ h'
    have hh : h ∈ Subgroup.normalizer (D : Set G) := by rw [← hcomapN]; exact hh'
    obtain ⟨j, hj⟩ := hyp.hperm h hh i
    refine ⟨j, ?_⟩
    rw [quotientFactors_apply, quotientFactors_apply, preimage_center_quotient,
      preimage_center_quotient, ← hj, Subgroup.map_map, Subgroup.map_map]
    congr 1
  ·
    intro i j t' g' ht' hnoncentral hti htj
    obtain ⟨k, hk⟩ := ht'
    obtain ⟨t, rfl, ht⟩ := exists_two_element_lift (QuotientGroup.mk' (Subgroup.center G))
      (QuotientGroup.mk'_surjective _) hk
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g'
    have htc : t ∉ Subgroup.center G := by
      intro htc
      apply hnoncentral
      have hone : QuotientGroup.mk' (Subgroup.center G) t = 1 :=
        (QuotientGroup.eq_one_iff t).mpr htc
      rw [hone]
      exact Subgroup.one_mem _
    have hti' := centralizes_of_quotient D r Abar hyp.hsemisimple hyp.hii i t hti
    have htj' := centralizes_of_quotient D r Abar hyp.hsemisimple hyp.hii j (g⁻¹ * t * g) (by
      rw [map_mul, map_mul, map_inv]
      exact htj)
    have hg := hyp.hi i j t g ht htc hti' htj'
    rw [← hcomapN] at hg
    exact hg
  ·
    intro i g' X' hX' hcover
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g'
    have hg : g ∈ Subgroup.normalizer (D : Set G) := by
      apply hyp.hii i g (X'.comap (QuotientGroup.mk' (Subgroup.center G)))
      · intro x hx
        obtain ⟨y', hy', hxy⟩ := Subgroup.mem_map.mp (hX' hx)
        refine Subgroup.mem_map.mpr ⟨g * x * g⁻¹, ?_, ?_⟩
        · rw [← hcomapN, Subgroup.mem_comap]
          have himage : QuotientGroup.mk' (Subgroup.center G) (g * x * g⁻¹) = y' := by
            rw [map_mul, map_mul, map_inv, ← hxy]
            simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
              inv_inv]
            group
          rw [himage]
          exact hy'
        · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
          group
      · intro a ha
        obtain ⟨x', hx', o', ho', hao⟩ := hcover (QuotientGroup.mk' (Subgroup.center G) a) (by
          rw [quotientFactors_apply, preimage_center_quotient]
          exact Subgroup.mem_map_of_mem _ ha)
        rw [core_center_quotient] at ho'
        obtain ⟨o, ho, rfl⟩ := Subgroup.mem_map.mp ho'
        refine ⟨a * o⁻¹, ?_, o, ho, by group⟩
        change QuotientGroup.mk' (Subgroup.center G) (a * o⁻¹) ∈ X'
        rw [map_mul, map_inv, hao, mul_inv_cancel_right]
        exact hx'
    rw [← hcomapN] at hg
    exact hg

theorem normalizer_center_quotient_ne_top {G : Type} [Group G] [Finite G] {D : Subgroup G}
    {r : ℕ} {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)} (hyp : Hyp61 G D r Abar)
    (hH : Subgroup.normalizer (D : Set G) ≠ ⊤) :
    Subgroup.normalizer (quotientSubgroup D : Set (G ⧸ Subgroup.center G)) ≠ ⊤ := by
  intro htop
  apply hH
  rw [← comap_normalizer_center_quotient D r hyp.hr Abar hyp.hii, htop, Subgroup.comap_top]

end CFSG.ComponentClassification.AschbacherTheorem5
