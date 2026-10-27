module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S2Odd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.FullnessCount

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Split

variable {Γ : Type*} [Group Γ]

open Classical in
@[expose] noncomputable def retraction {z : Γ} (hz : ∀ g : Γ, g * z = z * g) (hz2 : z * z = 1)
    (B : Subgroup Γ) (hcov : ∀ g : Γ, g ∈ B ∨ z * g ∈ B) : Γ →* B where
  toFun g := if h : g ∈ B then ⟨g, h⟩ else ⟨z * g, (hcov g).resolve_left h⟩
  map_one' := by
    simp
  map_mul' g h := by
    by_cases hg : g ∈ B <;> by_cases hh : h ∈ B
    · have hgh : g * h ∈ B := B.mul_mem hg hh
      simp only [hg, hh, hgh, dite_true]
      rfl
    · have hgh : g * h ∉ B := fun hgh => hh (by
        have := B.mul_mem (B.inv_mem hg) hgh
        simpa using this)
      simp only [hg, hh, hgh, dite_true, dite_false]
      refine Subtype.ext ?_
      change z * (g * h) = g * (z * h)
      rw [← mul_assoc, ← mul_assoc, ← hz g]
    · have hgh : g * h ∉ B := fun hgh => hg (by
        have := B.mul_mem hgh (B.inv_mem hh)
        simpa using this)
      simp only [hg, hh, hgh, dite_true, dite_false]
      refine Subtype.ext ?_
      change z * (g * h) = z * g * h
      rw [mul_assoc]
    · have hzg : z * g ∈ B := (hcov g).resolve_left hg
      have hzh : z * h ∈ B := (hcov h).resolve_left hh
      have hgh : g * h ∈ B := by
        have := B.mul_mem hzg hzh
        have e : z * g * (z * h) = g * h := by
          calc z * g * (z * h) = z * (g * z) * h := by simp only [mul_assoc]
            _ = z * (z * g) * h := by rw [hz g]
            _ = (z * z) * g * h := by simp only [mul_assoc]
            _ = g * h := by rw [hz2, one_mul]
        rwa [e] at this
      simp only [hg, hh, hgh, dite_true, dite_false]
      refine Subtype.ext ?_
      change g * h = z * g * (z * h)
      calc g * h = z * g * (z * h) := by
            calc g * h = (z * z) * g * h := by rw [hz2, one_mul]
              _ = z * (z * g) * h := by simp only [mul_assoc]
              _ = z * (g * z) * h := by rw [hz g]
              _ = z * g * (z * h) := by simp only [mul_assoc]

theorem retraction_of_mem {z : Γ} (hz : ∀ g : Γ, g * z = z * g) (hz2 : z * z = 1)
    (B : Subgroup Γ) (hcov : ∀ g : Γ, g ∈ B ∨ z * g ∈ B) {g : Γ} (hg : g ∈ B) :
    (retraction hz hz2 B hcov g : Γ) = g := by
  simp [retraction, hg]

theorem retraction_of_not_mem {z : Γ} (hz : ∀ g : Γ, g * z = z * g) (hz2 : z * z = 1)
    (B : Subgroup Γ) (hcov : ∀ g : Γ, g ∈ B ∨ z * g ∈ B) {g : Γ} (hg : g ∉ B) :
    (retraction hz hz2 B hcov g : Γ) = z * g := by
  simp [retraction, hg]

theorem retraction_eq_one_iff {z : Γ} (hz : ∀ g : Γ, g * z = z * g) (hz2 : z * z = 1)
    (B : Subgroup Γ) (hzB : z ∉ B) (hcov : ∀ g : Γ, g ∈ B ∨ z * g ∈ B) {g : Γ} :
    retraction hz hz2 B hcov g = 1 ↔ g = 1 ∨ g = z := by
  by_cases hg : g ∈ B
  · have h := retraction_of_mem hz hz2 B hcov hg
    constructor
    · intro h1
      rw [h1] at h
      left
      simpa using h.symm
    · rintro (rfl | rfl)
      · exact map_one _
      · exact absurd hg hzB
  · have h := retraction_of_not_mem hz hz2 B hcov hg
    constructor
    · intro h1
      rw [h1] at h
      right
      have : z * g = 1 := by simpa using h.symm
      calc g = z * (z * g) := by rw [← mul_assoc, hz2, one_mul]
        _ = z := by rw [this, mul_one]
    · rintro (rfl | rfl)
      · exact absurd B.one_mem hg
      · refine Subtype.ext ?_
        rw [h, hz2]
        rfl

theorem retraction_apply_of_mem {z : Γ} (hz : ∀ g : Γ, g * z = z * g) (hz2 : z * z = 1)
    (B : Subgroup Γ) (hcov : ∀ g : Γ, g ∈ B ∨ z * g ∈ B) (b : B) :
    retraction hz hz2 B hcov b = b :=
  Subtype.ext (retraction_of_mem hz hz2 B hcov b.2)

theorem exists_mulEquiv_prod {z : Γ} (hz : ∀ g : Γ, g * z = z * g) (hz2 : z * z = 1)
    (B : Subgroup Γ) (hzB : z ∉ B) (hcov : ∀ g : Γ, g ∈ B ∨ z * g ∈ B) {A : Type*} [Group A]
    (e : B ≃* A) : Nonempty (Γ ≃* Multiplicative (ZMod 2) × A) := by
  classical
  have hz1 : z ≠ 1 := fun h => hzB (h ▸ B.one_mem)
  let ε : Γ →* Multiplicative (ZMod 2) :=
    { toFun := fun g => if g ∈ B then 1 else Multiplicative.ofAdd 1
      map_one' := by simp
      map_mul' := fun g h => by
        by_cases hg : g ∈ B <;> by_cases hh : h ∈ B
        · simp [hg, hh, B.mul_mem hg hh]
        · have : g * h ∉ B := fun hgh => hh (by
            have := B.mul_mem (B.inv_mem hg) hgh
            simpa using this)
          simp [hg, hh, this]
        · have : g * h ∉ B := fun hgh => hg (by
            have := B.mul_mem hgh (B.inv_mem hh)
            simpa using this)
          simp [hg, hh, this]
        · have hzg : z * g ∈ B := (hcov g).resolve_left hg
          have hzh : z * h ∈ B := (hcov h).resolve_left hh
          have hgh : g * h ∈ B := by
            have := B.mul_mem hzg hzh
            have e : z * g * (z * h) = g * h := by
              calc z * g * (z * h) = z * (g * z) * h := by simp only [mul_assoc]
                _ = z * (z * g) * h := by rw [hz g]
                _ = (z * z) * g * h := by simp only [mul_assoc]
                _ = g * h := by rw [hz2, one_mul]
            rwa [e] at this
          simp only [hg, hh, hgh, ite_true, ite_false]
          decide }
  let Ψ : Γ →* Multiplicative (ZMod 2) × B := ε.prod (retraction hz hz2 B hcov)
  have hΨ : Function.Bijective Ψ := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      have h1 : ε g = 1 := congrArg Prod.fst hg
      have h2 : retraction hz hz2 B hcov g = 1 := congrArg Prod.snd hg
      have hgB : g ∈ B := by
        by_contra hgB
        have : ε g = Multiplicative.ofAdd 1 := by simp [ε, hgB]
        rw [this] at h1
        exact absurd h1 (by decide)
      rw [mem_bot]
      rcases (retraction_eq_one_iff hz hz2 B hzB hcov).1 h2 with h | h
      · exact h
      · exact absurd (h ▸ hgB) hzB
    · rintro ⟨x, b⟩
      obtain ⟨a, rfl⟩ : ∃ a : ZMod 2, Multiplicative.ofAdd a = x := ⟨x.toAdd, rfl⟩
      fin_cases a
      · refine ⟨b, ?_⟩
        refine Prod.ext ?_ (retraction_apply_of_mem hz hz2 B hcov b)
        simp [Ψ, ε]
        rfl
      · have hzb : z * (b : Γ) ∉ B := fun h => hzB (by
          have := B.mul_mem h (B.inv_mem b.2)
          simpa using this)
        refine ⟨z * b, Prod.ext ?_ (Subtype.ext ?_)⟩
        · simp [Ψ, ε, hzb]
          rfl
        · show (retraction hz hz2 B hcov (z * b) : Γ) = b
          rw [retraction_of_not_mem hz hz2 B hcov hzb, ← mul_assoc, hz2, one_mul]
  exact ⟨(MulEquiv.ofBijective Ψ hΨ).trans (MulEquiv.prodCongr (MulEquiv.refl _) e)⟩

end Split


section Quot

theorem nonempty_mulEquiv_quotient_oddCore {Y : Type*} [Group Y] [Finite Y]
    (lam : Y →* Equiv.Perm (Fin 5)) (hs : Function.Surjective lam)
    (hodd : Odd (Nat.card lam.ker)) :
    Nonempty ((Y ⧸ Open.fusionOddCore Y) ≃* Equiv.Perm (Fin 5)) := by
  have hker : lam.ker = Open.fusionOddCore Y := by
    apply le_antisymm
    · exact le_fusionOddCore_of_odd' hodd
    · have hn : ((Open.fusionOddCore Y).map lam).Normal :=
        Subgroup.Normal.map inferInstance lam hs
      have hdvd : Nat.card ((Open.fusionOddCore Y).map lam) ∣ Nat.card (Open.fusionOddCore Y) :=
        Subgroup.card_map_dvd _ _
      have hoddm : Odd (Nat.card ((Open.fusionOddCore Y).map lam)) :=
        Odd.of_dvd_nat (natCard_fusionOddCore_odd' Y) hdvd
      have := perm5_odd_normal _ hoddm
      rw [Subgroup.map_eq_bot_iff] at this
      exact this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective lam hs)⟩

end Quot

section Count

open Wreath

variable {G : Type*} [Group G] [Finite G] {A : Type*} [Group A] [Finite A]

theorem fibre_class_count {P : Subgroup G} (ρ : ↥P →* Wr2 A) (a c z : ↥P)
    (hzc : ∀ p : ↥P, p * z = z * p) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hker : ∀ p : ↥P, ρ p = 1 → p = 1 ∨ p = z) (hρz : ρ z = 1)
    (haτ : ρ a = tau) (hac : IsConj (a : G) (c : G)) (hacz : IsConj (a : G) ((c * z : ↥P) : G))
    (hw : ∀ p : ↥P, ρ p * tau * (ρ p)⁻¹ ≠ ρ c) {m m₁ : ℕ}
    (hm : Nat.card (centralizer ({ρ c} : Set (Wr2 A))) ≤ m)
    (hm₁ : Nat.card (centralizer ({a} : Set ↥P)) ≤ m₁) :
    ∃ n₁ n₂ : ℕ, n₁ + n₂ ≤ {g : G | IsConj (a : G) g ∧ g ∈ P}.ncard ∧
      Nat.card P ≤ n₁ * m₁ ∧ Nat.card P ≤ n₂ * m := by
  have hP : 0 < Nat.card P := Nat.card_pos
  have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have key : ∀ d : ↥P, ρ d = ρ c → ∀ x : ↥P, IsConj a x → IsConj d x → False := by
    intro d hd x hx hdx
    obtain ⟨p, hp⟩ := isConj_iff.1 hx
    obtain ⟨q, hq⟩ := isConj_iff.1 hdx
    apply hw (q⁻¹ * p)
    have h1 : ρ x = ρ p * tau * (ρ p)⁻¹ := by rw [← hp, map_mul, map_mul, map_inv, haτ]
    have h2 : ρ x = ρ q * ρ d * (ρ q)⁻¹ := by rw [← hq, map_mul, map_mul, map_inv]
    rw [map_mul, map_inv, ← hd]
    calc (ρ q)⁻¹ * ρ p * tau * ((ρ q)⁻¹ * ρ p)⁻¹ = (ρ q)⁻¹ * (ρ p * tau * (ρ p)⁻¹) * ρ q := by
          group
      _ = (ρ q)⁻¹ * (ρ q * ρ d * (ρ q)⁻¹) * ρ q := by rw [← h1, h2]
      _ = ρ d := by group
  have hρcz : ρ (c * z) = ρ c := by rw [map_mul, hρz, mul_one]
  have hdisj : Disjoint (subgroupConjClass P a)
      (subgroupConjClass P c ∪ subgroupConjClass P (c * z)) := by
    rw [Set.disjoint_left]
    rintro g ⟨x, hx, rfl⟩ (⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩)
    · have : y = x := Subtype.val_injective hyx
      subst this
      exact key c rfl y hx hy
    · have : y = x := Subtype.val_injective hyx
      subst this
      exact key (c * z) hρcz y hx hy
  have hsub : subgroupConjClass P a ∪ (subgroupConjClass P c ∪ subgroupConjClass P (c * z)) ⊆
      {g : G | IsConj (a : G) g ∧ g ∈ P} := by
    rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨MonoidHom.map_isConj P.subtype hy, y.2⟩
    · exact ⟨hac.trans (MonoidHom.map_isConj P.subtype hy), y.2⟩
    · exact ⟨hacz.trans (MonoidHom.map_isConj P.subtype hy), y.2⟩
  refine ⟨(subgroupConjClass P a).ncard,
    (subgroupConjClass P c ∪ subgroupConjClass P (c * z)).ncard, ?_, ?_, ?_⟩
  · rw [← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  · rw [← ncard_subgroupConjClass_mul_card_centralizer P a]
    exact Nat.mul_le_mul_left _ hm₁
  ·
    set C : Subgroup ↥P := centralizer ({c} : Set ↥P) with hC
    have hzC : z ∈ C := by
      rw [hC, mem_centralizer_singleton_iff]
      exact (hzc c).symm
    let g₀ : ↥C →* Wr2 A := ρ.comp C.subtype
    have hg₀ : ∀ x : ↥C, g₀ x = ρ x := fun x => rfl
    have hR : g₀.range ≤ (centralizer ({ρ c} : Set (Wr2 A)) ⊓ ρ.range : Subgroup (Wr2 A)) := by
      rintro _ ⟨x, rfl⟩
      refine ⟨?_, ⟨x, rfl⟩⟩
      show ρ x ∈ centralizer ({ρ c} : Set (Wr2 A))
      rw [mem_centralizer_singleton_iff]
      have hx : (x : ↥P) * c = c * x := mem_centralizer_singleton_iff.1 x.2
      rw [← map_mul, ← map_mul, hx]
    have hRm : Nat.card (centralizer ({ρ c} : Set (Wr2 A)) ⊓ ρ.range : Subgroup (Wr2 A)) ≤ m :=
      (Subgroup.card_le_of_le inf_le_left).trans hm
    have hkerle : Nat.card g₀.ker ≤ 2 := by
      classical
      have : Nat.card g₀.ker ≤ Nat.card Bool := by
        refine Nat.card_le_card_of_injective (fun x => decide (((x.1 : ↥C) : ↥P) = 1)) ?_
        intro x y hxy
        have hxk : g₀ x.1 = 1 := x.2
        have hyk : g₀ y.1 = 1 := y.2
        have hx1 := hker ((x.1 : ↥C) : ↥P) hxk
        have hy1 := hker ((y.1 : ↥C) : ↥P) hyk
        refine Subtype.ext (Subtype.ext ?_)
        by_cases hxe : ((x.1 : ↥C) : ↥P) = 1
        · have : ((y.1 : ↥C) : ↥P) = 1 := by
            by_contra hye
            simp [hxe, hye] at hxy
          rw [hxe, this]
        · have hye : ((y.1 : ↥C) : ↥P) ≠ 1 := by
            intro hye
            simp [hxe, hye] at hxy
          rw [hx1.resolve_left hxe, hy1.resolve_left hye]
      rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    have hcard := Subgroup.card_ker_mul_card_range g₀
    have hCle : Nat.card C ≤ 2 * Nat.card g₀.range := by
      rw [← hcard]
      exact Nat.mul_le_mul_right _ hkerle
    have hrange_le : Nat.card g₀.range ≤ m :=
      (Subgroup.card_le_of_le hR).trans hRm
    have hcls : ∀ d : ↥P, (subgroupConjClass P d).ncard * Nat.card (centralizer ({d} : Set ↥P)) =
        Nat.card P := fun d => ncard_subgroupConjClass_mul_card_centralizer P d
    by_cases hcz' : IsConj c (c * z)
    ·
      have hset : subgroupConjClass P (c * z) = subgroupConjClass P c := by
        unfold subgroupConjClass
        congr 1
        ext x
        exact ⟨fun h => hcz'.trans h, fun h => hcz'.symm.trans h⟩
      rw [hset, Set.union_self]
      obtain ⟨p₀, hp₀⟩ := isConj_iff.1 hcz'
      have hp₀R : ρ p₀ ∈ (centralizer ({ρ c} : Set (Wr2 A)) ⊓ ρ.range : Subgroup (Wr2 A)) := by
        refine ⟨?_, ⟨p₀, rfl⟩⟩
        show ρ p₀ ∈ centralizer ({ρ c} : Set (Wr2 A))
        rw [mem_centralizer_singleton_iff]
        have : ρ (p₀ * c * p₀⁻¹) = ρ (c * z) := by rw [hp₀]
        rw [map_mul, map_mul, map_inv, hρcz] at this
        calc ρ p₀ * ρ c = ρ p₀ * ρ c * (ρ p₀)⁻¹ * ρ p₀ := by group
          _ = ρ c * ρ p₀ := by rw [this]
      have hnot : ρ p₀ ∉ g₀.range := by
        rintro ⟨q, hq⟩
        set qq : ↥P := (q : ↥P) with hqq
        have h1 : ρ (qq⁻¹ * p₀) = 1 := by
          rw [map_mul, map_inv]
          have : ρ qq = ρ p₀ := hq
          rw [this, inv_mul_cancel]
        have hqc : qq * c = c * qq := mem_centralizer_singleton_iff.1 q.2
        have hc' : qq * c * qq⁻¹ = c := by rw [hqc]; group
        rcases hker _ h1 with h | h
        · have hp : p₀ = qq := by
            rw [inv_mul_eq_one] at h
            exact h.symm
          rw [hp, hc'] at hp₀
          have : z = 1 := by
            have := congrArg (fun x => c⁻¹ * x) hp₀
            simpa using this.symm
          exact hz1 this
        · have hp : p₀ = qq * z := by
            rw [inv_mul_eq_iff_eq_mul] at h
            exact h
          have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
          rw [hp] at hp₀
          have e : qq * z * c * (qq * z)⁻¹ = qq * c * qq⁻¹ := by
            have hzc' : z * c = c * z := (hzc c).symm
            calc qq * z * c * (qq * z)⁻¹ = qq * (z * c) * z⁻¹ * qq⁻¹ := by group
              _ = qq * (c * z) * z⁻¹ * qq⁻¹ := by rw [hzc']
              _ = qq * c * qq⁻¹ := by group
          rw [e, hc'] at hp₀
          have : z = 1 := by
            have := congrArg (fun x => c⁻¹ * x) hp₀
            simpa using this.symm
          exact hz1 this
      have h2 := two_mul_card_le_of_exists (K := g₀.range)
        (C := (centralizer ({ρ c} : Set (Wr2 A)) ⊓ ρ.range : Subgroup (Wr2 A))) hR
        ⟨ρ p₀, hp₀R, hnot⟩
      have hCm : Nat.card (centralizer ({c} : Set ↥P)) ≤ m := by
        have : Nat.card C ≤ m := by omega
        exact this
      calc Nat.card P = (subgroupConjClass P c).ncard * Nat.card (centralizer ({c} : Set ↥P)) :=
            (hcls c).symm
        _ ≤ (subgroupConjClass P c).ncard * m := Nat.mul_le_mul_left _ hCm
    · have hd := disjoint_subgroupConjClass P hcz'
      rw [Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)]
      have hcen : centralizer ({c * z} : Set ↥P) = centralizer ({c} : Set ↥P) := by
        ext x
        rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
        constructor
        · intro h
          have : x * c * z = c * x * z := by
            calc x * c * z = x * (c * z) := mul_assoc _ _ _
              _ = c * z * x := h
              _ = c * (z * x) := mul_assoc _ _ _
              _ = c * (x * z) := by rw [← hzc x]
              _ = c * x * z := (mul_assoc _ _ _).symm
          exact mul_right_cancel this
        · intro h
          calc x * (c * z) = (x * c) * z := (mul_assoc _ _ _).symm
            _ = (c * x) * z := by rw [h]
            _ = c * (x * z) := mul_assoc _ _ _
            _ = c * (z * x) := by rw [hzc x]
            _ = c * z * x := (mul_assoc _ _ _).symm
      have e1 := hcls c
      have e2 := hcls (c * z)
      rw [hcen] at e2
      have hCm2 : Nat.card (centralizer ({c} : Set ↥P)) ≤ 2 * m := by
        have : Nat.card C ≤ 2 * m := by omega
        exact this
      have f1 : Nat.card P ≤ (subgroupConjClass P c).ncard * (2 * m) := by
        rw [← e1]; exact Nat.mul_le_mul_left _ hCm2
      have f2 : Nat.card P ≤ (subgroupConjClass P (c * z)).ncard * (2 * m) := by
        rw [← e2]; exact Nat.mul_le_mul_left _ hCm2
      nlinarith

end Count

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
