module

public import CFSG.ClassicalInvolution.Asc77.AscT3WInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]


theorem c20_10a_of_res' (hI : Res10aInv' p f) (hY : Res10aY' p f) : C20_10a p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8
  classical
  obtain ⟨a, hab⟩ := hI G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8
  have haS := hab.mem
  have haa := hab.sq
  have haX := hab.not_mem_X
  obtain ⟨hC, hF⟩ := hY G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 a hab
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  have hnc : ∃ x y : G, x * y ≠ y * x := by
    obtain ⟨b, -, hbK⟩ := d.late_exists_swap
    by_contra hcon
    push Not at hcon
    apply d.ne
    have h3 : conjSub b K = K := by
      ext x
      rw [mem_conjSub_iff]
      have : b⁻¹ * x * b = x := by
        rw [mul_assoc, hcon x b, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this]
    exact hbK.symm.trans h3
  have hnoconj : ∀ g : G, g⁻¹ * a * g ∉ X := by
    intro g ha'
    have hCz : g⁻¹ * a * g ∈ Subgroup.centralizer ({z} : Set G) := d.r10a_X_le_C ha'
    have hcomm : z * (g⁻¹ * a * g) = (g⁻¹ * a * g) * z :=
      (Subgroup.mem_centralizer_singleton_iff.mp hCz).symm
    obtain ⟨c, hca, hcz⟩ := hF g (by
      have : (g * z * g⁻¹) * a = a * (g * z * g⁻¹) := by
        calc (g * z * g⁻¹) * a = g * (z * (g⁻¹ * a * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * a * g) * z) * g⁻¹ := by rw [hcomm]
          _ = a * (g * z * g⁻¹) := by group
      exact this)
    have hd₀ : g⁻¹ * c ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : (g⁻¹ * c) * z * (g⁻¹ * c)⁻¹ = z := by
        calc (g⁻¹ * c) * z * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * z * c⁻¹) * g := by group
          _ = z := by rw [hcz]; group
      calc (g⁻¹ * c) * z = ((g⁻¹ * c) * z * (g⁻¹ * c)⁻¹) * (g⁻¹ * c) := by group
        _ = z * (g⁻¹ * c) := by rw [this]
    have hnorm := le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins hd₀
    have hinv : (g⁻¹ * c)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hd₀
    have hnorm' := le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins hinv
    have h5 : (g⁻¹ * c)⁻¹ * (g⁻¹ * a * g) * ((g⁻¹ * c)⁻¹)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hnorm' _).mp ha'
    apply haX
    have h6 : (g⁻¹ * c)⁻¹ * (g⁻¹ * a * g) * ((g⁻¹ * c)⁻¹)⁻¹ = a := by
      calc (g⁻¹ * c)⁻¹ * (g⁻¹ * a * g) * ((g⁻¹ * c)⁻¹)⁻¹ = c⁻¹ * a * c := by group
        _ = a := by rw [mul_assoc, ← hca, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h6] at h5
    exact h5
  have hSnormX : ∀ s ∈ (S : Subgroup G), ∀ x ∈ X, s * x * s⁻¹ ∈ X := fun s hs x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins
      (d.hSz hs)) x).mp hx
  set Sg : Subgroup G := (S : Subgroup G) with hSg
  let N : Subgroup ↥Sg := X.subgroupOf Sg
  have hNn : N.Normal := ⟨fun n hn s => by
    have h1 : (n : G) ∈ X := hn
    exact hSnormX s s.2 n h1⟩
  let _inst : CommGroup (↥Sg ⧸ N) :=
    { (inferInstance : Group (↥Sg ⧸ N)) with
      mul_comm := fun x y => by
        induction x using QuotientGroup.induction_on with | _ x => ?_
        induction y using QuotientGroup.induction_on with | _ y => ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have h1 := hC (y⁻¹ : ↥Sg) (y⁻¹).2 (x⁻¹ : ↥Sg) (x⁻¹).2
        have h2 : (((x * y)⁻¹ * (y * x) : ↥Sg) : G) = ⁅((y⁻¹ : ↥Sg) : G), ((x⁻¹ : ↥Sg) : G)⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
          group
        show (((x * y)⁻¹ * (y * x) : ↥Sg) : G) ∈ X
        rw [h2]
        exact h1 }
  let ϕ : ↥Sg →* ↥Sg ⧸ N := QuotientGroup.mk' N
  have hϕmem : ∀ x : ↥Sg, ϕ x = 1 ↔ (x : G) ∈ X := fun x => QuotientGroup.eq_one_iff x
  have hodd : Odd Sg.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp S.not_dvd_index)
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr haS)
  have hϕa : ϕ ⟨a, haS⟩ ≠ 1 := fun h => haX ((hϕmem ⟨a, haS⟩).mp h)
  have hϕa2 : ϕ ⟨a, haS⟩ * ϕ ⟨a, haS⟩ = 1 := by
    rw [← map_mul]
    have : (⟨a, haS⟩ : ↥Sg) * ⟨a, haS⟩ = 1 := Subtype.ext haa
    rw [this, map_one]
  obtain ⟨g, n, hg, hne⟩ := exists_fusion_of_isSimpleGroup hnc hodd ϕ haS ha2 hϕa
  rcases Nat.even_or_odd n with hn | hn
  ·
    have h1 : a ^ n = 1 := by
      obtain ⟨k, rfl⟩ := hn
      rw [← two_mul, pow_mul, pow_two, haa, one_pow]
    have h2 : (⟨g⁻¹ * a ^ n * g, hg⟩ : ↥Sg) = 1 := Subtype.ext (by simp [h1])
    apply hne
    have h3 : ϕ ⟨a, haS⟩ ^ n = 1 := by
      obtain ⟨k, rfl⟩ := hn
      rw [← two_mul, pow_mul, pow_two, hϕa2, one_pow]
    rw [h2, map_one, h3]
  · have h1 : a ^ n = a := by
      obtain ⟨k, rfl⟩ := hn
      rw [pow_succ, pow_mul, pow_two, haa, one_pow, one_mul]
    have ha'S : g⁻¹ * a * g ∈ Sg := by
      have := hg
      rwa [h1] at this
    have h3 : ϕ ⟨a, haS⟩ ^ n = ϕ ⟨a, haS⟩ := by
      obtain ⟨k, rfl⟩ := hn
      rw [pow_succ, pow_mul, pow_two, hϕa2, one_pow, one_mul]
    have hne' : ϕ ⟨g⁻¹ * a * g, ha'S⟩ ≠ ϕ ⟨a, haS⟩ := by
      intro h
      apply hne
      have e : (⟨g⁻¹ * a ^ n * g, hg⟩ : ↥Sg) = ⟨g⁻¹ * a * g, ha'S⟩ := Subtype.ext (by simp [h1])
      rw [e, h3]
      exact h
    have ha'a' : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
      calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
        _ = 1 := by rw [haa]; group
    have hc9 := (c9 h8).1.2
    rcases hc9 a haS (g⁻¹ * a * g) ha'S (by rw [haa]; exact X.one_mem)
      (by rw [ha'a']; exact X.one_mem) (hC a haS _ ha'S) with h | h | h
    · exact haX h
    · exact hnoconj g h
    · apply hne'
      have h4 : ϕ ⟨a * (g⁻¹ * a * g), Sg.mul_mem haS ha'S⟩ = 1 := (hϕmem _).mpr h
      have e : (⟨a * (g⁻¹ * a * g), Sg.mul_mem haS ha'S⟩ : ↥Sg) =
          ⟨a, haS⟩ * ⟨g⁻¹ * a * g, ha'S⟩ := rfl
      rw [e, map_mul] at h4
      exact mul_left_cancel (h4.trans hϕa2.symm)


theorem c20_10a_of_Y' (hY : Res10aY' p f) : C20_10a p f :=
  c20_10a_of_res' p f (res10aInv'_proved p f) hY

end CFSG.ClassicalInvolution.Asc77.T3CII
