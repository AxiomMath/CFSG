module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerReduce

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup

section Pullback

variable {p : ℕ} {G H : Type*} [Group G] [Group H]

theorem OddPCoreInClosure.of_injective_normal_range [Finite H] (hp : p.Prime) (f : G →* H)
    (hf : Function.Injective f) [f.range.Normal] (h : OddPCoreInClosure p H) :
    OddPCoreInClosure p G :=
  OddPCoreInClosure.of_mulEquiv (MonoidHom.ofInjective hf).symm
    (OddPCoreInClosure.of_normal hp f.range h)

end Pullback

section Product

variable {p : ℕ} {G : Type*} [Group G]

theorem OddPCoreInClosure.of_noncommPiCoprod [Finite G] (hp : p.Prime) {ι : Type*} [Finite ι]
    (A : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ A i → y ∈ A j → Commute x y)
    (hind : iSupIndep A) (h : ∀ i, OddPCoreInClosure p ↥(A i)) :
    OddPCoreInClosure p ↥(⨆ i, A i) := by
  classical
  haveI := Fintype.ofFinite ι
  let φ : (∀ i, ↥(A i)) →* G := Subgroup.noncommPiCoprod hcomm
  have hφinj : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : φ.range = ⨆ i, A i := Subgroup.noncommPiCoprod_range
  have hπ : OddPCoreInClosure p (∀ i, ↥(A i)) := OddPCoreInClosure.pi hp h
  exact OddPCoreInClosure.of_mulEquiv
    ((MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hrange)) hπ

end Product

section Quotient

variable {p : ℕ} {X : Type*} [Group X]

theorem exists_lift_pow_eq_one_of_central [Finite X] (hp : p.Prime) (Z : Subgroup X) [Z.Normal]
    (hZc : Z ≤ Subgroup.center X) (hZ : ∀ z ∈ Z, z ^ p = 1 → z = 1) {d : X ⧸ Z} (hdp : d ^ p = 1) :
    ∃ x : X, (x : X ⧸ Z) = d ∧ x ^ p = 1 := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective d
  have hmem : b ^ p ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hdp
  have hcop : Nat.Coprime (Nat.card Z) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) p hdvd
    have hz1 : (z : X) ^ p = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this
    have hz2 : z = 1 := Subtype.ext (hZ z z.2 hz1)
    rw [hz2, orderOf_one] at hz
    exact hp.one_lt.ne hz
  obtain ⟨w, hw⟩ := (powCoprime hcop).surjective ⟨(b ^ p)⁻¹, Z.inv_mem hmem⟩
  have hw' : w ^ p = ⟨(b ^ p)⁻¹, Z.inv_mem hmem⟩ := hw
  have hwp : (w : X) ^ p = (b ^ p)⁻¹ := congrArg Subtype.val hw'
  have hc : Commute b (w : X) := Subgroup.mem_center_iff.1 (hZc w.2) b
  refine ⟨b * w, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (w : X)).2 w.2, mul_one]
  · rw [hc.mul_pow, hwp, mul_inv_cancel]

theorem pClosureOdd_quotient_of_central [Finite X] (hp : p.Prime) (Z : Subgroup X) [Z.Normal]
    (hZc : Z ≤ Subgroup.center X) (hZ : ∀ z ∈ Z, z ^ p = 1 → z = 1)
    (h : ∀ x : X, x ^ p = 1 → OddPCoreInClosure p ↥(Subgroup.centralizer ({x} : Set X))) :
    PClosureOdd p (X ⧸ Z) := by
  intro d hd1 hdp
  obtain ⟨x, rfl, hxp⟩ := exists_lift_pow_eq_one_of_central hp Z hZc hZ hdp
  have hOC := h x hxp
  let φ : ↥(Subgroup.centralizer ({x} : Set X)) →*
      ↥(Subgroup.centralizer ({(x : X ⧸ Z)} : Set (X ⧸ Z))) :=
    ((QuotientGroup.mk' Z).comp (Subgroup.centralizer ({x} : Set X)).subtype).codRestrict _
      (fun g => by
        have hg : (g : X) * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 g.2
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        change ((g : X) : X ⧸ Z) * (x : X ⧸ Z) = (x : X ⧸ Z) * ((g : X) : X ⧸ Z)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hg])
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (y : X ⧸ Z)
    have hy : (y : X ⧸ Z) * (x : X ⧸ Z) = (x : X ⧸ Z) * (y : X ⧸ Z) :=
      Subgroup.mem_centralizer_singleton_iff.1 y.2
    have h1 : ((g * x * g⁻¹ : X) : X ⧸ Z) = (x : X ⧸ Z) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hg]
      calc (y : X ⧸ Z) * (x : X ⧸ Z) * (y : X ⧸ Z)⁻¹
          = ((x : X ⧸ Z) * (y : X ⧸ Z)) * (y : X ⧸ Z)⁻¹ := by rw [hy]
        _ = (x : X ⧸ Z) := by group
    have hz : x⁻¹ * (g * x * g⁻¹) ∈ Z := QuotientGroup.eq.1 h1.symm
    set z := x⁻¹ * (g * x * g⁻¹) with hzdef
    have hgx : g * x * g⁻¹ = x * z := by simp [hzdef]
    have hcz : Commute x z := Subgroup.mem_center_iff.1 (hZc hz) x
    have hzp : z ^ p = 1 := by
      have h2 : (g * x * g⁻¹) ^ p = 1 := by rw [conj_pow, hxp]; group
      rw [hgx, hcz.mul_pow, hxp, one_mul] at h2
      exact h2
    have hz1 : z = 1 := hZ z hz hzp
    have h3 : g * x * g⁻¹ = x := by rw [hgx, hz1, mul_one]
    have hgx' : g * x = x * g := by
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h3]
    exact ⟨⟨g, Subgroup.mem_centralizer_singleton_iff.2 hgx'⟩, Subtype.ext hg⟩
  have hker : φ.ker ≤ Subgroup.center ↥(Subgroup.centralizer ({x} : Set X)) := by
    intro g hg
    have h1 : ((g : X) : X ⧸ Z) = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hg)
    have hs : (g : X) ∈ Z := (QuotientGroup.eq_one_iff (g : X)).1 h1
    rw [Subgroup.mem_center_iff]
    intro h'
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZc hs) h'.1)
  exact OddPCoreInClosure.of_surjective_ker_le_center hp φ hsurj hker hOC

end Quotient

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
