module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section General

variable {X : Type*} [Group X]

theorem isSolvable_of_perfect_eq_bot [Finite X] (h : ∀ Q : Subgroup X, ⁅Q, Q⁆ = Q → Q = ⊥) :
    Group.IsSolvable X := by
  classical
  obtain ⟨_, ⟨m, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup X))
    (Set.range (derivedSeries X)) ⟨derivedSeries X 0, 0, rfl⟩
  have hperf : ⁅derivedSeries X m, derivedSeries X m⁆ = derivedSeries X m := by
    have hle : derivedSeries X (m + 1) ≤ derivedSeries X m := by
      rw [derivedSeries_succ]
      exact Subgroup.commutator_le_self _
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact absurd hlt (hmin _ ⟨m + 1, rfl⟩)
    · rw [← derivedSeries_succ]
      exact heq
  exact (Group.isSolvable_def X).2 ⟨m, h _ hperf⟩

theorem apply_eq_of_perfect_of_mem_center (α : MulAut X) {W : Subgroup X} (hW : ⁅W, W⁆ = W)
    (h : ∀ w ∈ W, w⁻¹ * α w ∈ Subgroup.center X) {w : X} (hw : w ∈ W) : α w = w := by
  let ψ : ↥W →* ↥(Subgroup.center X) :=
    { toFun := fun v => ⟨(v : X)⁻¹ * α v, h v v.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        have hc := Subgroup.mem_center_iff.mp (h a a.2) ((b : X)⁻¹)
        simp only [Subgroup.coe_mul, mul_inv_rev, map_mul]
        calc (b : X)⁻¹ * (a : X)⁻¹ * (α a * α b)
            = (b : X)⁻¹ * ((a : X)⁻¹ * α a) * α b := by group
          _ = (a : X)⁻¹ * α a * (b : X)⁻¹ * α b := by rw [hc]
          _ = (a : X)⁻¹ * α a * ((b : X)⁻¹ * α b) := by group }
  have hker : commutator ↥W ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  have hmem : w ∈ (commutator ↥W).map W.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hW]
    exact hw
  obtain ⟨v, hv, rfl⟩ := hmem
  have h1 := congrArg Subtype.val (hker hv)
  change (v : X)⁻¹ * α v = 1 at h1
  exact (inv_mul_eq_one.mp h1).symm

theorem mulAut_conj_map_eq (σ : MulAut X) (g : X) :
    MulAut.conj (σ g) = σ * MulAut.conj g * σ⁻¹ := by
  ext y
  simp [MulAut.mul_apply]

theorem exists_conj_eq_of_pow_eq_one_of_coprime {σ : MulAut X} {n : ℕ} (hσ : σ ^ n = 1)
    (hn : n.Coprime (Nat.card (Outer X))) : ∃ a : X, MulAut.conj a = σ := by
  have hψ : QuotientGroup.mk' (inner X) σ = 1 :=
    (pow_eq_one_iff_of_coprime hn).mp ⟨by rw [← map_pow, hσ, map_one], pow_card_eq_one'⟩
  exact (QuotientGroup.eq_one_iff _).mp hψ

theorem mem_center_of_mulAut_conj_eq_one {z : X} (h : MulAut.conj z = 1) :
    z ∈ Subgroup.center X := by
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  have h1 := DFunLike.congr_fun h y
  rw [MulAut.conj_apply, MulAut.one_apply] at h1
  calc y * z = z * y * z⁻¹ * z := by rw [h1]
    _ = z * y := by group

theorem apply_mem_center_of_mulEquiv {X' : Type*} [Group X'] (e : X ≃* X') {y : X}
    (hy : y ∈ Subgroup.center X) : e y ∈ Subgroup.center X' := by
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  obtain ⟨g, rfl⟩ := e.surjective g
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy g]

theorem ThreeAutFixedTwoThree.of_mulEquiv {X' : Type*} [Group X'] (e : X ≃* X')
    (h : ThreeAutFixedTwoThree X') : ThreeAutFixedTwoThree X := by
  intro α hα3 hfree x hx n hn hxn
  set α' : MulAut X' := MulAut.congr e α
  have happ : ∀ y : X, α' (e y) = e (α y) := fun y => by simp [α', MulAut.congr_apply]
  have hZ : ∀ y : X, y ∈ Subgroup.center X → e y ∈ Subgroup.center X' := fun y hy =>
    apply_mem_center_of_mulEquiv e hy
  have hα'3 : α' ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hfree' : ∀ Q : Subgroup X', ⁅Q, Q⁆ = Q → (∀ y ∈ Q, α' y = y) → Q = ⊥ := by
    intro Q hQ hfix
    have h1 := hfree (Q.map e.symm.toMonoidHom) (by rw [← Subgroup.map_commutator, hQ])
      (fun y hy => by
        obtain ⟨q, hq, rfl⟩ := hy
        apply e.injective
        change e (α (e.symm q)) = e (e.symm q)
        rw [← happ, e.apply_symm_apply, hfix q hq])
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).mp h1
  have key := h α' hα'3 hfree' (e x) (by rw [happ, ← map_inv, ← map_mul]; exact hZ _ hx) n hn
    (by rw [← map_pow]; exact hZ _ hxn)
  simpa using apply_mem_center_of_mulEquiv e.symm key

theorem threeAutFixedTwoThree_of_centerQuotient [Group.IsPerfect X]
    (h : ThreeAutFixedTwoThree (X ⧸ Subgroup.center X)) : ThreeAutFixedTwoThree X := by
  intro α hα3 hfree x hx n hn hxn
  set π := QuotientGroup.mk' (Subgroup.center X)
  set β := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X α
  have hβ : ∀ y : X, β (π y) = π (α y) := fun y =>
    CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk α y
  have hβ3 : β ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hfree' : ∀ Q : Subgroup (X ⧸ Subgroup.center X), ⁅Q, Q⁆ = Q →
      (∀ y ∈ Q, β y = y) → Q = ⊥ := by
    intro Q hQ hfix
    obtain ⟨W, hW, hWQ, hWm⟩ := ParabPrime.exists_perfect_map_eq π
      (by rw [QuotientGroup.ker_mk']) hQ
      (by rw [QuotientGroup.range_mk']; exact le_top)
    have hWfix : ∀ w ∈ W, α w = w := fun w hw =>
      apply_eq_of_perfect_of_mem_center α hW (fun v hv => by
        have h1 := hfix (π v) (hWQ hv)
        rw [hβ] at h1
        exact (QuotientGroup.eq (s := Subgroup.center X)).mp h1.symm) hw
    rw [← hWm, hfree W hW hWfix, Subgroup.map_bot]
  have h1 : π (x⁻¹ * α x) = 1 := (QuotientGroup.eq_one_iff _).mpr hx
  have h2 : π (x ^ n) = 1 := (QuotientGroup.eq_one_iff _).mpr hxn
  have key := h β hβ3 hfree' (π x)
    (by
      rw [hβ, ← map_inv, ← map_mul, h1]
      exact Subgroup.one_mem _) n hn
    (by
      rw [← map_pow, h2]
      exact Subgroup.one_mem _)
  rw [Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.mem_bot] at key
  exact (QuotientGroup.eq_one_iff x).mp key

end General

section Component

variable {Y : Type*} [Group Y]

theorem mem_centralizer_of_threeAutFixedTwoThree {L : Subgroup Y}
    (hOut : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (Outer ↥L))
    (hP : ThreeAutFixedTwoThree ↥L) {u t : Y} (hu : u ∈ Subgroup.normalizer (L : Set Y))
    (hu3 : u ^ 3 = 1)
    (hfree : ∀ D : Subgroup Y, D ≤ L → ⁅D, D⁆ = D →
      D ≤ Subgroup.centralizer ({u} : Set Y) → D = ⊥)
    (ht : t ∈ Subgroup.normalizer (L : Set Y)) (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht6 : Nat.Coprime 6 (orderOf t)) : t ∈ Subgroup.centralizer (L : Set Y) := by
  set φ := L.normalizerMonoidHom
  set U : Subgroup.normalizer (L : Set Y) := ⟨u, hu⟩
  set T : Subgroup.normalizer (L : Set Y) := ⟨t, ht⟩
  have hφ : ∀ (g : Subgroup.normalizer (L : Set Y)) (x : ↥L), ((φ g x : ↥L) : Y) =
      g * x * (g : Y)⁻¹ := fun g x => rfl
  have hTn : φ T ^ orderOf t = 1 := by
    rw [← map_pow]
    have : T ^ orderOf t = 1 := Subtype.ext (by simp [T, pow_orderOf_eq_one])
    rw [this, map_one]
  have hcop : (orderOf t).Coprime (Nat.card (Outer ↥L)) := by
    refine Nat.coprime_of_dvd fun p hp hpn hpo => ?_
    by_cases hp5 : 5 ≤ p
    · exact hOut p hp hp5 hpo
    · have h6 : p ∣ 6 := by
        interval_cases p <;> first | decide | (exfalso; norm_num at hp)
      have h1 := Nat.eq_one_of_dvd_coprimes ht6 h6 hpn
      exact hp.one_lt.ne' h1
  obtain ⟨l, hl⟩ := exists_conj_eq_of_pow_eq_one_of_coprime hTn hcop
  have hlt : ∀ x : ↥L, t * x * t⁻¹ = (l : Y) * x * (l : Y)⁻¹ := fun x =>
    ((hφ T x).symm.trans (congrArg Subtype.val (DFunLike.congr_fun hl x)).symm)
  have hUT : U * T = T * U := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp htu).symm
  have hcomm : φ U * φ T = φ T * φ U := by rw [← map_mul, hUT, map_mul]
  have hcen : l⁻¹ * φ U l ∈ Subgroup.center ↥L := by
    refine mem_center_of_mulAut_conj_eq_one ?_
    rw [map_mul, mulAut_conj_map_eq, hl, map_inv, hl, hcomm, mul_inv_cancel_right, inv_mul_cancel]
  have hpow : l ^ orderOf t ∈ Subgroup.center ↥L :=
    mem_center_of_mulAut_conj_eq_one (by rw [map_pow, hl, hTn])
  have hU3 : φ U ^ 3 = 1 := by
    rw [← map_pow]
    have : U ^ 3 = 1 := Subtype.ext (by simp [U, hu3])
    rw [this, map_one]
  have hfree' : ∀ Q : Subgroup ↥L, ⁅Q, Q⁆ = Q → (∀ y ∈ Q, φ U y = y) → Q = ⊥ := by
    intro Q hQ hfix
    have h1 := hfree (Q.map L.subtype) (by
        rintro _ ⟨y, -, rfl⟩
        exact y.2) (by rw [← Subgroup.map_commutator, hQ]) (by
        rintro _ ⟨y, hy, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 := congrArg Subtype.val (hfix y hy)
        rw [hφ] at h2
        change (y : Y) * u = u * y
        calc (y : Y) * u = u * y * u⁻¹ * u := by rw [h2]
          _ = u * y := by group)
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h1
  have hlZ := hP (φ U) hU3 hfree' l hcen (orderOf t) ht6 hpow
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := hlt ⟨y, hy⟩
  have h2 : (l : Y) * y = y * l :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hlZ ⟨y, hy⟩).symm
  change t * y * t⁻¹ = (l : Y) * y * (l : Y)⁻¹ at h1
  rw [h2, mul_inv_cancel_right] at h1
  calc y * t = t * y * t⁻¹ * t := by rw [h1]
    _ = t * y := by group

end Component

end CFSG.AGLEmbedding
