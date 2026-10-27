module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Glue

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS04Lift

open CFSG.Open
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient_apply_mk)
open scoped commutatorElement

theorem commutator_mul_central {K : Type*} [Group K] (a b : K) {z₁ z₂ : K}
    (h₁ : z₁ ∈ Subgroup.center K) (h₂ : z₂ ∈ Subgroup.center K) :
    ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  have e1 : ∀ c : K, ⁅z₁, c⁆ = 1 := fun c =>
    commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.1 h₁ c).symm
  have e2 : ∀ c : K, ⁅c, z₂⁆ = 1 := fun c =>
    commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.1 h₂ c)
  rw [commutatorElement_mul_left_eq_conj_mul, e1, commutatorElement_mul_right_eq_mul_conj, e2]
  group

theorem commutator_eq_top_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G)).resolve_left fun hb => ?_
  obtain ⟨a, b, hab⟩ := hna
  apply hab
  have h1 : ⁅a, b⁆ ∈ commutator G := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [hb, Subgroup.mem_bot] at h1
  exact (commutatorElement_eq_one_iff_commute.1 h1).eq

theorem commutator_subgroup_eq_self_of_simple {S : Type*} [Group S] {Lb : Subgroup S}
    (hs : IsSimpleGroup ↥Lb) (hna : ∃ a b : ↥Lb, a * b ≠ b * a) : ⁅Lb, Lb⁆ = Lb := by
  have h := commutator_eq_top_of_simple hna
  have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥Lb) ⊤ Lb.subtype
  rw [← commutator_def, h, Subgroup.map_top, Subgroup.range_subtype] at h2
  exact h2.symm

theorem isQuasisimple_of_perfect_cover {C X : Type*} [Group C] [Group X]
    (hC : Group.IsPerfect C) (ρ : C →* X) (hρ : Function.Surjective ρ) (hX : IsSimpleGroup X)
    (hXn : ∃ a b : X, a * b ≠ b * a) (hker : ρ.ker ≤ Subgroup.center C) :
    CFSG.IsQuasisimple C := by
  have hZX : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hXn
      exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab
  have hcen : Subgroup.center C ≤ ρ.ker := by
    intro x hx
    have : ρ x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨c, rfl⟩ := hρ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx c]
    rw [hZX, Subgroup.mem_bot] at this
    exact this
  have heq : Subgroup.center C = ρ.ker := le_antisymm hcen hker
  let e : (C ⧸ Subgroup.center C) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq heq).trans (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
  refine ⟨hC, e.isSimpleGroup_congr.2 hX, ?_⟩
  obtain ⟨a, b, hab⟩ := hXn
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem glaPLayer_ne_bot_of_fixed_block {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {y : MulAut K} {Lb : Subgroup (K ⧸ Subgroup.center K)} (hLs : IsSimpleGroup ↥Lb)
    (hLna : ∃ a b : ↥Lb, a * b ≠ b * a) (hfix : ∀ x ∈ Lb, centerQuotientHom K y x = x)
    (hpL : p ∣ Nat.card Lb)
    (hnorm : ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.fixSub y, ∀ x ∈ Lb,
      QuotientGroup.mk' (Subgroup.center K) g * x * (QuotientGroup.mk' (Subgroup.center K) g)⁻¹ ∈
        Lb) :
    GLAPLayer p (CFSG.LocalAnalysis.GLTheoremA.fixSub y) ≠ ⊥ := by
  classical
  set Z := Subgroup.center K with hZ
  set π : K →* K ⧸ Z := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  set P : Subgroup K := Lb.comap π with hP
  have hmemP : ∀ x : K, x ∈ P ↔ π x ∈ Lb := fun x => Iff.rfl
  have hc : ∀ x ∈ P, x⁻¹ * y x ∈ Z := by
    intro x hx
    have h1 : π (y x) = π x := by
      have := hfix _ ((hmemP x).1 hx)
      rw [show centerQuotientHom K y (π x) = π (y x) from onCenterQuotient_apply_mk y x] at this
      exact this
    apply (QuotientGroup.eq_one_iff _).1
    change π (x⁻¹ * y x) = 1
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  set L : Subgroup K := ⁅P, P⁆ with hL
  have hmapP : P.map π = Lb := Subgroup.map_comap_eq_self_of_surjective hπs Lb
  have hLb : ⁅Lb, Lb⁆ = Lb := commutator_subgroup_eq_self_of_simple hLs hLna
  have hmapL : L.map π = Lb := by
    rw [hL, Subgroup.map_commutator, hmapP, hLb]
  have hfixL : L ≤ CFSG.LocalAnalysis.GLTheoremA.fixSub y := by
    rw [hL, Subgroup.commutator_le]
    intro a ha b hb
    have ea : y a = a * (a⁻¹ * y a) := by group
    have eb : y b = b * (b⁻¹ * y b) := by group
    show y ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, ea, eb, commutator_mul_central a b (hc a ha) (hc b hb)]
  have hLP : L ≤ P := by
    rw [hL, Subgroup.commutator_le]
    intro a ha b hb
    rw [hmemP, commutatorElement_def]
    simp only [map_mul, map_inv]
    exact Lb.mul_mem (Lb.mul_mem (Lb.mul_mem ((hmemP a).1 ha) ((hmemP b).1 hb))
      (Lb.inv_mem ((hmemP a).1 ha))) (Lb.inv_mem ((hmemP b).1 hb))
  have hsplit : ∀ a ∈ P, ∃ l ∈ L, ∃ z ∈ Z, a = l * z := by
    intro a ha
    have : π a ∈ L.map π := by rw [hmapL]; exact (hmemP a).1 ha
    obtain ⟨l, hl, hla⟩ := Subgroup.mem_map.1 this
    refine ⟨l, hl, l⁻¹ * a, ?_, by group⟩
    apply (QuotientGroup.eq_one_iff _).1
    change π (l⁻¹ * a) = 1
    rw [map_mul, map_inv, hla, inv_mul_cancel]
  have hLperf : ⁅L, L⁆ = L := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
    · rw [hL, Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨l₁, hl₁, z₁, hz₁, rfl⟩ := hsplit a ha
      obtain ⟨l₂, hl₂, z₂, hz₂, rfl⟩ := hsplit b hb
      rw [commutator_mul_central l₁ l₂ hz₁ hz₂]
      exact Subgroup.commutator_mem_commutator hl₁ hl₂
  have hnormP : ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.fixSub y, ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g hg x hx
    rw [hmemP]
    simp only [map_mul, map_inv]
    exact hnorm g hg _ ((hmemP x).1 hx)
  have hnormL : ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.fixSub y, ∀ f ∈ L, g * f * g⁻¹ ∈ L := by
    intro g hg f hf
    have hmap : ∀ g' ∈ CFSG.LocalAnalysis.GLTheoremA.fixSub y,
        L.map (MulAut.conj g').toMonoidHom ≤ L := by
      intro g' hg'
      have hPP : P.map (MulAut.conj g').toMonoidHom ≤ P := by
        rintro _ ⟨x, hx, rfl⟩
        exact hnormP g' hg' x hx
      rw [hL, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hPP hPP
    exact hmap g hg ⟨f, hf, rfl⟩
  have hLq : CFSG.IsQuasisimple ↥L := by
    let ρ : ↥L →* ↥Lb := (π.comp L.subtype).codRestrict Lb (fun x => (hmemP x).1 (hLP x.2))
    have hρs : Function.Surjective ρ := by
      intro x
      have : (x : K ⧸ Z) ∈ L.map π := by rw [hmapL]; exact x.2
      obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.1 this
      exact ⟨⟨l, hl⟩, Subtype.ext hlx⟩
    have hker : ρ.ker ≤ Subgroup.center ↥L := by
      intro x hx
      have h1 : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      have h2 : (x : K) ∈ Z := (QuotientGroup.eq_one_iff _).1 h1
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 h2 g
    have hcommL : commutator ↥L = ⊤ := by
      apply Subgroup.map_injective L.subtype_injective
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      exact hLperf
    exact isQuasisimple_of_perfect_cover (Group.isPerfect_def.2 hcommL) ρ hρs hLs hLna hker
  have hpLL : p ∣ Nat.card L := by
    have hρs : Function.Surjective ((π.comp L.subtype).codRestrict Lb
        (fun x => (hmemP x).1 (hLP x.2))) := by
      intro x
      have : (x : K ⧸ Z) ∈ L.map π := by rw [hmapL]; exact x.2
      obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.1 this
      exact ⟨⟨l, hl⟩, Subtype.ext hlx⟩
    have h1 := Subgroup.card_ker_mul_card_range
      ((π.comp L.subtype).codRestrict Lb (fun x => (hmemP x).1 (hLP x.2)))
    rw [MonoidHom.range_eq_top.2 hρs, Subgroup.card_top] at h1
    exact hpL.trans ⟨_, by rw [← h1, mul_comm]⟩
  exact CFSG.LocalAnalysis.GLTheoremA.glaPLayer_ne_bot_of_block hp hfixL hLq hnormL hpLL

end CFSG.LocalAnalysis.GLTheoremA.YS04Lift
