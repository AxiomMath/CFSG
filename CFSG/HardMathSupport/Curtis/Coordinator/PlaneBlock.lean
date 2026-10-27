module

public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneLift

public section

open CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.Open

namespace CFSG.HardMathSupport.Curtis.Coordinator.Plane

variable {Y : Type*} [Group Y] {L : Subgroup Y}

@[expose] def conjL (y : Y) (hy : y ∈ Subgroup.normalizer (L : Set Y)) : MulAut ↥L where
  toFun l := ⟨y * l * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy l).mp l.2⟩
  invFun l := ⟨y⁻¹ * l * y, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) l).mp l.2
    simpa using this⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[simp] theorem conjL_apply (y : Y) (hy : y ∈ Subgroup.normalizer (L : Set Y)) (l : ↥L) :
    ((conjL y hy l : ↥L) : Y) = y * l * y⁻¹ := rfl

@[expose] def conjHom (L : Subgroup Y) : ↥(Subgroup.normalizer (L : Set Y)) →* MulAut ↥L where
  toFun n := conjL n n.2
  map_one' := MulEquiv.ext fun l => Subtype.ext (by simp)
  map_mul' a b := MulEquiv.ext fun l => Subtype.ext (by simp [mul_assoc])

theorem map_center_eq {G : Type*} [Group G] (a : MulAut G) :
    (Subgroup.center G).map a.toMonoidHom = Subgroup.center G := by
  have key : ∀ b : MulAut G, ∀ z ∈ Subgroup.center G, b z ∈ Subgroup.center G := by
    intro b z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨g', rfl⟩ := b.surjective g
    rw [← map_mul, ← map_mul, hz g']
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact key a w hw
  · intro hz
    exact ⟨a.symm z, key a.symm z hz, by simp⟩

@[expose] def quotAut (a : MulAut ↥L) : MulAut (↥L ⧸ Subgroup.center ↥L) :=
  QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) a (map_center_eq a)

@[simp] theorem quotAut_mk (a : MulAut ↥L) (l : ↥L) :
    quotAut a (l : ↥L ⧸ Subgroup.center ↥L) = ((a l : ↥L) : ↥L ⧸ Subgroup.center ↥L) :=
  QuotientGroup.congr_mk _ _ _ _ _

@[expose] def quotAutHom (L : Subgroup Y) : MulAut ↥L →* MulAut (↥L ⧸ Subgroup.center ↥L) where
  toFun := quotAut
  map_one' := MulEquiv.ext fun q => by
    induction q using QuotientGroup.induction_on with
    | H l => simp
  map_mul' a b := MulEquiv.ext fun q => by
    induction q using QuotientGroup.induction_on with
    | H l => simp

@[expose] def planeAut {K : Type*} [Field K] (φ : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 K) :
    ↥(Subgroup.normalizer (L : Set Y)) →* MulAut (projectiveSL 3 K) :=
  (MulAut.congr φ).toMonoidHom.comp ((quotAutHom L).comp (conjHom L))

theorem planeAut_apply {K : Type*} [Field K] (φ : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 K)
    (n : ↥(Subgroup.normalizer (L : Set Y))) (l : ↥L) :
    planeAut φ n (φ (l : ↥L ⧸ Subgroup.center ↥L)) =
      φ ((⟨n * l * (n : Y)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 l).mp l.2⟩ : ↥L) :
        ↥L ⧸ Subgroup.center ↥L) := by
  simp only [planeAut, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact congrArg φ (quotAut_mk (conjL (n : Y) n.2) l)

theorem plane_core [Finite Y] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {e : ℕ}
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 (GaloisField 2 e))
    {E : Subgroup Y} (hEL : E ≤ L) (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    {y : Y} (hyL : y ∈ Subgroup.normalizer (L : Set Y))
    (hyE : y ∈ Subgroup.normalizer (E : Set Y)) (hyp : ∃ k : ℕ, y ^ p ^ k = 1) :
    ∀ x ∈ E, y * x * y⁻¹ = x := by
  obtain ⟨k, hk⟩ := hyp
  have hpK : (p : GaloisField 2 e) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (GaloisField 2 e) 2]
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
    omega
  let f : ↥E →* projectiveSL 3 (GaloisField 2 e) :=
    φ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center ↥L)).comp (Subgroup.inclusion hEL))
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center ↥L) (Subgroup.inclusion hEL x) = 1 :=
      φ.injective (by rw [map_one]; exact hx)
    have hz : Subgroup.inclusion hEL x ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).mp h1
    have hzp : (⟨_, hz⟩ : Subgroup.center ↥L) ^ p = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hEel.2 x x.2
    have hdZ : orderOf (⟨_, hz⟩ : Subgroup.center ↥L) ∣ Nat.card (Subgroup.center ↥L) :=
      orderOf_dvd_natCard _
    have hz1 : orderOf (⟨_, hz⟩ : Subgroup.center ↥L) = 1 := by
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hzp) with h | h
      · exact h
      · exact absurd (h ▸ hdZ) hZ
    have := congrArg (fun z : Subgroup.center ↥L => ((z : ↥L) : Y)) (orderOf_eq_one_iff.mp hz1)
    exact Subtype.ext (by simpa using this)
  have hEb : Nat.card f.range = p ^ 2 := by
    rw [← hEc]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hc : ∀ x ∈ f.range, ∀ y ∈ f.range, x * y = y * x := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, hEel.1.is_comm.comm x y]
  have hexp : ∀ x ∈ f.range, x ^ p = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow, show x ^ p = 1 from Subtype.ext (by simpa using hEel.2 x x.2), map_one]
  set n : ↥(Subgroup.normalizer (L : Set Y)) := ⟨y, hyL⟩ with hn
  have hαp : planeAut φ n ^ p ^ k = 1 := by
    rw [← map_pow]
    have : n ^ p ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hαf : ∀ x : ↥E, planeAut φ n (f x) =
      f ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyE x).mp x.2⟩ := by
    intro x
    exact planeAut_apply φ n (Subgroup.inclusion hEL x)
  have hαE : ∀ e ∈ f.range, planeAut φ n e ∈ f.range := by
    rintro _ ⟨x, rfl⟩
    rw [hαf]
    exact ⟨_, rfl⟩
  have hfix := plane_automizer hp hp5 hpK hc hexp hEb (planeAut φ n) hαp hαE
  intro x hx
  have h1 := hfix (f ⟨x, hx⟩) ⟨_, rfl⟩
  rw [hαf] at h1
  exact congrArg Subtype.val (hf h1)

end CFSG.HardMathSupport.Curtis.Coordinator.Plane
