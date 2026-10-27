module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

private lemma mem_normalizer_of_forall_conj_mem [Finite G] {H : Subgroup G} {x : G}
    (h : ∀ w ∈ H, x * w * x⁻¹ ∈ H) :
    x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply] using h w hw
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

private lemma exists_mul_of_mem_sup_of_le_centralizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) {z : G} (hz : z ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = z := by
  have hnorm : A ≤ Subgroup.normalizer (B : Set G) :=
    hAB.trans (Subgroup.centralizer_le_normalizer _)
  have hcoe : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B hnorm
  have hz' : z ∈ (A : Set G) * (B : Set G) := by
    rwa [← hcoe]
  simpa only [Set.mem_mul, SetLike.mem_coe] using hz'

theorem centralizer_sup_eq_inf_centralizer {A B : Subgroup G} :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext z
  constructor
  · intro hz
    exact ⟨fun a ha => hz a (Or.inl ha), fun b hb => hz b (Or.inr hb)⟩
  · rintro ⟨hA, hB⟩ x (hx | hx)
    · exact hA x hx
    · exact hB x hx

theorem inf_centralizer_sup_eq_sup_inf_centralizer {A B Y : Subgroup G}
    (hAB : A ≤ Subgroup.centralizer (B : Set G))
    (hdisj : A ⊓ B = ⊥)
    (hYA : ∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    (hYB : ∀ y ∈ Y, ∀ b ∈ B, y * b * y⁻¹ ∈ B) :
    (A ⊔ B) ⊓ Subgroup.centralizer (Y : Set G) =
      (A ⊓ Subgroup.centralizer (Y : Set G)) ⊔
        (B ⊓ Subgroup.centralizer (Y : Set G)) := by
  classical
  have hdisj' : Disjoint A B := disjoint_iff.mpr hdisj
  have hinj := Subgroup.mul_injective_of_disjoint hdisj'
  apply le_antisymm
  · intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hAB hz.1
    have hzC : a * b ∈ Subgroup.centralizer (Y : Set G) := hz.2
    have haC : a ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hfix : y * (a * b) * y⁻¹ = a * b := by
        have h := Subgroup.mem_centralizer_iff.mp hzC y hy
        calc y * (a * b) * y⁻¹ = ((a * b) * y) * y⁻¹ := by rw [h]
          _ = a * b := by group
      have hpair :
          (((⟨y * a * y⁻¹, hYA y hy a ha⟩ : A),
            ⟨y * b * y⁻¹, hYB y hy b hb⟩) : A × B) = ((⟨a, ha⟩, ⟨b, hb⟩) : A × B) := by
        apply hinj
        simpa [mul_assoc] using hfix
      have hya : y * a * y⁻¹ = a := congrArg (fun p : A × B => (p.1 : G)) hpair
      calc y * a = (y * a * y⁻¹) * y := by group
        _ = a * y := by rw [hya]
    have hbC : b ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hfix : y * (a * b) * y⁻¹ = a * b := by
        have h := Subgroup.mem_centralizer_iff.mp hzC y hy
        calc y * (a * b) * y⁻¹ = ((a * b) * y) * y⁻¹ := by rw [h]
          _ = a * b := by group
      have hpair :
          (((⟨y * a * y⁻¹, hYA y hy a ha⟩ : A),
            ⟨y * b * y⁻¹, hYB y hy b hb⟩) : A × B) = ((⟨a, ha⟩, ⟨b, hb⟩) : A × B) := by
        apply hinj
        simpa [mul_assoc] using hfix
      have hyb : y * b * y⁻¹ = b := congrArg (fun p : A × B => (p.2 : G)) hpair
      calc y * b = (y * b * y⁻¹) * y := by group
        _ = b * y := by rw [hyb]
    exact Subgroup.mul_mem_sup ⟨ha, haC⟩ ⟨hb, hbC⟩
  · intro z hz
    have hAB' : A ⊓ Subgroup.centralizer (Y : Set G) ≤
        Subgroup.centralizer ((B ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_iff.mp (hAB ha.1) b hb.1
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer hAB' hz
    exact ⟨Subgroup.mul_mem_sup ha.1 hb.1,
      (Subgroup.centralizer (Y : Set G)).mul_mem ha.2 hb.2⟩

theorem card_inf_centralizer_sup_eq_mul {A B Y : Subgroup G}
    (hAB : A ≤ Subgroup.centralizer (B : Set G))
    (hdisj : A ⊓ B = ⊥)
    (hYA : ∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    (hYB : ∀ y ∈ Y, ∀ b ∈ B, y * b * y⁻¹ ∈ B) :
    Nat.card ↥((A ⊔ B) ⊓ Subgroup.centralizer (Y : Set G)) =
      Nat.card ↥(A ⊓ Subgroup.centralizer (Y : Set G)) *
        Nat.card ↥(B ⊓ Subgroup.centralizer (Y : Set G)) := by
  rw [inf_centralizer_sup_eq_sup_inf_centralizer hAB hdisj hYA hYB]
  have hnorm : A ⊓ Subgroup.centralizer (Y : Set G) ≤
      Subgroup.normalizer ((B ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
    refine (show A ⊓ Subgroup.centralizer (Y : Set G) ≤
        Subgroup.centralizer ((B ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G)
        from ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_iff.mp (hAB ha.1) b hb.1
  have hdisj' : (A ⊓ Subgroup.centralizer (Y : Set G)) ⊓
      (B ⊓ Subgroup.centralizer (Y : Set G)) = ⊥ := by
    apply le_antisymm
    · intro z hz
      have hzA : z ∈ A := hz.1.1
      have hzB : z ∈ B := hz.2.1
      have hzAB : z ∈ A ⊓ B := ⟨hzA, hzB⟩
      simpa [hdisj] using hzAB
    · exact bot_le
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (B ⊓ Subgroup.centralizer (Y : Set G)) (A ⊓ Subgroup.centralizer (Y : Set G))
    hnorm (disjoint_iff.mpr (by rw [inf_comm]; exact hdisj'))
  rw [sup_comm, Nat.mul_comm] at hcard
  exact hcard

private lemma card_inf_centralizer_singleton_eq_of_conj_swap {A B : Subgroup G} {x : G}
    (hx2 : x ^ 2 = 1)
    (hAB : A ≤ Subgroup.centralizer (B : Set G))
    (hdisj : A ⊓ B = ⊥)
    (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ B)
    (hxB : ∀ b ∈ B, x * b * x⁻¹ ∈ A) :
    Nat.card ↥((A ⊔ B) ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card A := by
  classical
  let φ : A → ↥((A ⊔ B) ⊓ Subgroup.centralizer ({x} : Set G)) := fun a =>
    ⟨(a : G) * (x * (a : G) * x⁻¹), by
      refine ⟨Subgroup.mul_mem_sup a.2 (hxA a a.2), ?_⟩
      change (a : G) * (x * (a : G) * x⁻¹) ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hab : (a : G) * (x * (a : G) * x⁻¹) =
          (x * (a : G) * x⁻¹) * (a : G) :=
        ((Subgroup.mem_centralizer_iff.mp (hAB a.2)) _ (hxA a a.2)).symm
      have hx2' : x * x = 1 := by simpa [pow_two] using hx2
      have hxinv : x⁻¹ * x⁻¹ = 1 := by
        calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
          _ = 1 := by rw [hx2']; simp
      have hxx : x * (x * (a : G) * x⁻¹) * x⁻¹ = (a : G) := by
        calc x * (x * (a : G) * x⁻¹) * x⁻¹
            = (x * x) * (a : G) * (x⁻¹ * x⁻¹) := by group
          _ = (a : G) := by rw [hx2', hxinv]; group
      have hfix : x * ((a : G) * (x * (a : G) * x⁻¹)) * x⁻¹ =
          (a : G) * (x * (a : G) * x⁻¹) := by
        calc x * ((a : G) * (x * (a : G) * x⁻¹)) * x⁻¹
            = (x * (a : G) * x⁻¹) * (x * (x * (a : G) * x⁻¹) * x⁻¹) := by group
          _ = (x * (a : G) * x⁻¹) * (a : G) := by rw [hxx]
          _ = (a : G) * (x * (a : G) * x⁻¹) := hab.symm
      have hcomm : ((a : G) * (x * (a : G) * x⁻¹)) * x =
          x * ((a : G) * (x * (a : G) * x⁻¹)) := by
        have h := congrArg (· * x) hfix
        simpa [mul_assoc] using h.symm
      exact hcomm⟩
  have hφ_inj : Function.Injective φ := by
    intro a a' h
    have hval : (a : G) * (x * (a : G) * x⁻¹) =
        (a' : G) * (x * (a' : G) * x⁻¹) := by
      simpa [φ] using congrArg Subtype.val h
    have hpair : ((a, ⟨x * (a : G) * x⁻¹, hxA a a.2⟩) : A × B) =
        (a', ⟨x * (a' : G) * x⁻¹, hxA a' a'.2⟩) := by
      apply Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hdisj)
      simpa using hval
    exact congrArg (fun p : A × B => p.1) hpair
  have hφ_surj : Function.Surjective φ := by
    intro z
    obtain ⟨a, ha, b, hb, hab⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer hAB z.2.1
    have hzx : (z : G) * x = x * (z : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp z.2.2
    have hzx' : (a : G) * b * x = x * ((a : G) * b) := by
      simpa [hab] using hzx
    have hfix : x * ((a : G) * b) * x⁻¹ = (a : G) * b := by
      calc x * ((a : G) * b) * x⁻¹ = ((a : G) * b) * x * x⁻¹ := by rw [hzx']
        _ = (a : G) * b := by group
    have hpair : (((⟨x * (b : G) * x⁻¹, hxB b hb⟩ : A),
        ⟨x * (a : G) * x⁻¹, hxA a ha⟩) : A × B) = ((⟨a, ha⟩, ⟨b, hb⟩) : A × B) := by
      apply Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hdisj)
      calc (x * (b : G) * x⁻¹) * (x * (a : G) * x⁻¹)
          = (x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹) := by
              exact ((Subgroup.mem_centralizer_iff.mp (hAB (hxB b hb)))
                (x * (a : G) * x⁻¹) (hxA a ha)).symm
        _ = x * ((a : G) * b) * x⁻¹ := by group
        _ = (a : G) * b := hfix
    have hxb_eq : x * (a : G) * x⁻¹ = (b : G) :=
      congrArg (fun p : A × B => ((p.2 : B) : G)) hpair
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    change (a : G) * (x * (a : G) * x⁻¹) = (z : G)
    rw [hxb_eq]
    exact hab
  have hbij : Function.Bijective φ := ⟨hφ_inj, hφ_surj⟩
  exact (Nat.card_congr (Equiv.ofBijective φ hbij)).symm

theorem eq_of_isElementaryAbelian_of_noOffenders [Finite G] {n : ℕ}
    (hn : 2 ≤ n) {W W₁ W₂ P : Subgroup G} (hW : IsElementaryAbelian 2 W)
    (hW₁₂ : W₁ ⊔ W₂ = W) (hdisj : W₁ ⊓ W₂ = ⊥)
    (hcard₁ : Nat.card W₁ = 2 ^ n) (hcard₂ : Nat.card W₂ = 2 ^ n)
    (hWP : W ≤ P) (hCP : P ⊓ centralizer (W : Set G) ≤ W)
    (hperm : ∀ x ∈ P,
      ((∀ w ∈ W₁, x * w * x⁻¹ ∈ W₁) ∧ (∀ w ∈ W₂, x * w * x⁻¹ ∈ W₂)) ∨
      ((∀ w ∈ W₁, x * w * x⁻¹ ∈ W₂) ∧ (∀ w ∈ W₂, x * w * x⁻¹ ∈ W₁)))
    (hoff₁ : ∀ Y : Subgroup G, Y ≤ P →
      (∀ y ∈ Y, (∀ w ∈ W₁, y * w * y⁻¹ ∈ W₁) ∧ (∀ w ∈ W₂, y * w * y⁻¹ ∈ W₂)) →
      IsElementaryAbelian 2 Y → ¬ Y ≤ centralizer (W₁ : Set G) →
      (centralizer (W₁ : Set G)).relIndex Y *
        Nat.card ↥(W₁ ⊓ centralizer (Y : Set G)) < 2 ^ n)
    (hoff₂ : ∀ Y : Subgroup G, Y ≤ P →
      (∀ y ∈ Y, (∀ w ∈ W₁, y * w * y⁻¹ ∈ W₁) ∧ (∀ w ∈ W₂, y * w * y⁻¹ ∈ W₂)) →
      IsElementaryAbelian 2 Y → ¬ Y ≤ centralizer (W₂ : Set G) →
      (centralizer (W₂ : Set G)).relIndex Y *
        Nat.card ↥(W₂ ⊓ centralizer (Y : Set G)) < 2 ^ n)
    {Y : Subgroup G} (hYP : Y ≤ P) (hY : IsElementaryAbelian 2 Y)
    (hYcard : 2 ^ (2 * n) ≤ Nat.card Y) : Y = W := by
  classical
  letI : IsElementaryAbelian 2 W := hW
  letI : IsElementaryAbelian 2 Y := hY
  let C : Subgroup G := Subgroup.centralizer (W : Set G)
  let C₁ : Subgroup G := Subgroup.centralizer (W₁ : Set G)
  let C₂ : Subgroup G := Subgroup.centralizer (W₂ : Set G)
  let P₀ : Subgroup G := P ⊓ Subgroup.normalizer (W₁ : Set G) ⊓
    Subgroup.normalizer (W₂ : Set G)
  have hW₁_le : W₁ ≤ W := by rw [← hW₁₂]; exact le_sup_left
  have hW₂_le : W₂ ≤ W := by rw [← hW₁₂]; exact le_sup_right
  have hW₁e : IsElementaryAbelian 2 W₁ := IsElementaryAbelian.of_le hW hW₁_le
  have hW₂e : IsElementaryAbelian 2 W₂ := IsElementaryAbelian.of_le hW hW₂_le
  letI : IsElementaryAbelian 2 W₁ := hW₁e
  letI : IsElementaryAbelian 2 W₂ := hW₂e
  have hcomm₁₂ : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, hW₁_le ha⟩ : W) (⟨b, hW₂_le hb⟩ : W))
  have hW₁_cent_W₂ : W₁ ≤ C₂ := by
    rw [Subgroup.le_centralizer_iff]
    intro b hb a ha
    exact hcomm₁₂ a ha b hb
  have hW₂_cent_W₁ : W₂ ≤ C₁ := by
    rw [Subgroup.le_centralizer_iff]
    intro a ha b hb
    exact (hcomm₁₂ a ha b hb).symm
  have hC_eq : C = C₁ ⊓ C₂ := by
    rw [show C = Subgroup.centralizer (W : Set G) from rfl, ← hW₁₂,
      centralizer_sup_eq_inf_centralizer]
  have hdisjD : Disjoint W₁ W₂ := disjoint_iff.mpr hdisj
  have hWcard : Nat.card W = 2 ^ (2 * n) := by
    rw [← hW₁₂,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer W₁ W₂
        (hW₂_cent_W₁.trans (Subgroup.centralizer_le_normalizer _)) hdisjD,
      hcard₁, hcard₂, show 2 * n = n + n by omega, pow_add]
  have hW₁_card_gt_one : 1 < Nat.card W₁ := by
    rw [hcard₁]
    exact Nat.one_lt_pow (by omega : n ≠ 0) (by norm_num)
  have hW₁_ne_bot : W₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hW₁_card_gt_one
    omega
  have hCY_eq_W : Y ⊓ C = Y ⊓ W := by
    apply le_antisymm
    · intro z hz
      refine ⟨hz.1, ?_⟩
      exact hCP ⟨hYP hz.1, hz.2⟩
    · rintro z ⟨hzY, hzW⟩
      exact ⟨hzY, (Subgroup.le_centralizer (H := W)) hzW⟩
  have hYcard_le : Nat.card Y ≤
      C.relIndex Y * Nat.card ↥(W ⊓ Subgroup.centralizer (Y : Set G)) := by
    have hrel := Subgroup.relIndex_mul_card (H := C) (K := Y)
    rw [inf_comm C Y, hCY_eq_W] at hrel
    calc Nat.card Y = C.relIndex Y * Nat.card ↥(Y ⊓ W) := hrel.symm
      _ ≤ C.relIndex Y * Nat.card ↥(W ⊓ Subgroup.centralizer (Y : Set G)) := by
          refine Nat.mul_le_mul_left _ ?_
          exact Subgroup.card_le_of_le (by
            intro z hz
            refine ⟨hz.2, ?_⟩
            change z ∈ Subgroup.centralizer (Y : Set G)
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : Y) (⟨z, hz.1⟩ : Y)))
  have hYcard_pos : 0 < Nat.card Y := lt_of_lt_of_le (by positivity) hYcard
  have hYleW_or_contra : Y ≤ W := by
    by_contra hYnotW
    have hYnotC : ¬ Y ≤ C := by
      intro hYC
      apply hYnotW
      intro y hy
      exact hCP ⟨hYP hy, hYC hy⟩
    have hYnotC_both : ¬ (Y ≤ C₁ ∧ Y ≤ C₂) := by
      intro hboth
      apply hYnotC
      rw [hC_eq]
      intro y hy
      exact ⟨hboth.1 hy, hboth.2 hy⟩
    by_cases hYleP₀ : Y ≤ P₀
    ·
      have hYnorm₁ : ∀ y ∈ Y, ∀ w ∈ W₁, y * w * y⁻¹ ∈ W₁ := by
        intro y hy w hw
        exact (Subgroup.mem_normalizer_iff.mp (hYleP₀ hy).1.2 w).1 hw
      have hYnorm₂ : ∀ y ∈ Y, ∀ w ∈ W₂, y * w * y⁻¹ ∈ W₂ := by
        intro y hy w hw
        exact (Subgroup.mem_normalizer_iff.mp (hYleP₀ hy).2 w).1 hw
      have hYnorm_pair : ∀ y ∈ Y, (∀ w ∈ W₁, y * w * y⁻¹ ∈ W₁) ∧
          (∀ w ∈ W₂, y * w * y⁻¹ ∈ W₂) := fun y hy => ⟨hYnorm₁ y hy, hYnorm₂ y hy⟩
      have hcard_CW : Nat.card ↥(W ⊓ Subgroup.centralizer (Y : Set G)) =
          Nat.card ↥(W₁ ⊓ Subgroup.centralizer (Y : Set G)) *
            Nat.card ↥(W₂ ⊓ Subgroup.centralizer (Y : Set G)) := by
        have h := card_inf_centralizer_sup_eq_mul (A := W₁) (B := W₂) (Y := Y)
          hW₁_cent_W₂ hdisj hYnorm₁ hYnorm₂
        simpa [hW₁₂] using h
      have hCY_eq : Y ⊓ C = (Y ⊓ C₁) ⊓ (Y ⊓ C₂) := by
        rw [hC_eq]
        ext z
        simp [and_assoc, and_left_comm, and_comm]
      have hidx_le : C.relIndex Y ≤ C₁.relIndex Y * C₂.relIndex Y := by
        calc C.relIndex Y = (Y ⊓ C).relIndex Y := by
              rw [inf_comm, Subgroup.inf_relIndex_right]
          _ = ((Y ⊓ C₁) ⊓ (Y ⊓ C₂)).relIndex Y := by rw [hCY_eq]
          _ ≤ (Y ⊓ C₁).relIndex Y * (Y ⊓ C₂).relIndex Y := Subgroup.relIndex_inf_le
          _ = C₁.relIndex Y * C₂.relIndex Y := by
              rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left]
      let f₁ : ℕ := C₁.relIndex Y * Nat.card ↥(W₁ ⊓ Subgroup.centralizer (Y : Set G))
      let f₂ : ℕ := C₂.relIndex Y * Nat.card ↥(W₂ ⊓ Subgroup.centralizer (Y : Set G))
      have hf₁_le : f₁ ≤ 2 ^ n := by
        by_cases h : Y ≤ C₁
        · have hri : C₁.relIndex Y = 1 := Subgroup.relIndex_eq_one.mpr h
          dsimp [f₁]
          rw [hri, one_mul]
          calc Nat.card ↥(W₁ ⊓ Subgroup.centralizer (Y : Set G)) ≤ Nat.card W₁ :=
                Subgroup.card_le_of_le inf_le_left
            _ = 2 ^ n := hcard₁
        · exact le_of_lt (hoff₁ Y hYP hYnorm_pair hY h)
      have hf₂_le : f₂ ≤ 2 ^ n := by
        by_cases h : Y ≤ C₂
        · have hri : C₂.relIndex Y = 1 := Subgroup.relIndex_eq_one.mpr h
          dsimp [f₂]
          rw [hri, one_mul]
          calc Nat.card ↥(W₂ ⊓ Subgroup.centralizer (Y : Set G)) ≤ Nat.card W₂ :=
                Subgroup.card_le_of_le inf_le_left
            _ = 2 ^ n := hcard₂
        · exact le_of_lt (hoff₂ Y hYP hYnorm_pair hY h)
      have hf₁_pos : 0 < f₁ := by
        dsimp [f₁]
        have hri : C₁.relIndex Y ≠ 0 := by
          rw [Subgroup.relIndex]
          exact Subgroup.index_ne_zero_of_finite
        exact Nat.mul_pos (Nat.pos_of_ne_zero hri) Nat.card_pos
      have hf₂_pos : 0 < f₂ := by
        dsimp [f₂]
        have hri : C₂.relIndex Y ≠ 0 := by
          rw [Subgroup.relIndex]
          exact Subgroup.index_ne_zero_of_finite
        exact Nat.mul_pos (Nat.pos_of_ne_zero hri) Nat.card_pos
      have hf_lt : f₁ * f₂ < 2 ^ (2 * n) := by
        have h2n : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by
          rw [show 2 * n = n + n by omega, pow_add]
        rw [h2n]
        by_cases h : Y ≤ C₁
        · have h₂ : ¬ Y ≤ C₂ := fun h₂ => hYnotC_both ⟨h, h₂⟩
          have hf₂_lt : f₂ < 2 ^ n := hoff₂ Y hYP hYnorm_pair hY h₂
          calc f₁ * f₂ < f₁ * 2 ^ n := Nat.mul_lt_mul_of_pos_left hf₂_lt hf₁_pos
            _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_right _ hf₁_le
        · have hf₁_lt : f₁ < 2 ^ n := hoff₁ Y hYP hYnorm_pair hY h
          calc f₁ * f₂ < 2 ^ n * f₂ := Nat.mul_lt_mul_of_pos_right hf₁_lt hf₂_pos
            _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_left _ hf₂_le
      have hYle_f : Nat.card Y ≤ f₁ * f₂ := by
        calc Nat.card Y ≤ C.relIndex Y * Nat.card ↥(W ⊓ Subgroup.centralizer (Y : Set G)) :=
              hYcard_le
          _ = C.relIndex Y *
                (Nat.card ↥(W₁ ⊓ Subgroup.centralizer (Y : Set G)) *
                  Nat.card ↥(W₂ ⊓ Subgroup.centralizer (Y : Set G))) := by rw [hcard_CW]
          _ ≤ (C₁.relIndex Y * C₂.relIndex Y) *
                (Nat.card ↥(W₁ ⊓ Subgroup.centralizer (Y : Set G)) *
                  Nat.card ↥(W₂ ⊓ Subgroup.centralizer (Y : Set G))) := by
              gcongr
          _ = f₁ * f₂ := by
              dsimp [f₁, f₂]
              ring
      have hYlt : Nat.card Y < 2 ^ (2 * n) := lt_of_le_of_lt hYle_f hf_lt
      exact absurd hYcard (not_le_of_gt hYlt)
    ·
      have hx_exists : ∃ x ∈ Y, x ∉ P₀ := by
        by_contra h
        apply hYleP₀
        intro y hy
        by_contra hyP₀
        exact h ⟨y, hy, hyP₀⟩
      obtain ⟨x, hxY, hxP₀⟩ := hx_exists
      have hxP : x ∈ P := hYP hxY
      have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hxY
      have hx2' : x * x = 1 := by simpa [pow_two] using hx2
      have hxswap : (∀ w ∈ W₁, x * w * x⁻¹ ∈ W₂) ∧
          (∀ w ∈ W₂, x * w * x⁻¹ ∈ W₁) := by
        rcases hperm x hxP with hfirst | hsecond
        · exfalso
          apply hxP₀
          exact ⟨⟨hxP, mem_normalizer_of_forall_conj_mem hfirst.1⟩,
            mem_normalizer_of_forall_conj_mem hfirst.2⟩
        · exact hsecond
      have hxmap₁ : W₁.map (MulAut.conj x) = W₂ := by
        apply Subgroup.eq_of_le_of_card_ge
        · rintro _ ⟨w, hw, rfl⟩
          simpa [MulAut.conj_apply] using hxswap.1 w hw
        · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hcard₁, hcard₂]
      have hxmap₂ : W₂.map (MulAut.conj x) = W₁ := by
        apply Subgroup.eq_of_le_of_card_ge
        · rintro _ ⟨w, hw, rfl⟩
          simpa [MulAut.conj_apply] using hxswap.2 w hw
        · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hcard₂, hcard₁]
      have hx_not_C : x ∉ C := by
        intro hxC
        obtain ⟨w, hwW₁, hw1⟩ :=
          (Subgroup.bot_or_exists_ne_one W₁).resolve_left hW₁_ne_bot
        have hfix : x * w * x⁻¹ = w := by
          have h := Subgroup.mem_centralizer_iff.mp hxC w (hW₁_le hwW₁)
          calc x * w * x⁻¹ = (w * x) * x⁻¹ := by rw [h.symm]
            _ = w := by group
        have hwW₂ : w ∈ W₂ := by
          rw [← hfix]
          exact hxswap.1 w hwW₁
        have : w ∈ W₁ ⊓ W₂ := ⟨hwW₁, hwW₂⟩
        rw [hdisj] at this
        exact hw1 (Subgroup.mem_bot.mp this)
      let Y₀ : Subgroup G := Y ⊓ P₀
      have hY₀_le_Y : Y₀ ≤ Y := inf_le_left
      have hY₀_le_P : Y₀ ≤ P := (inf_le_right : Y₀ ≤ P₀).trans (by
        exact inf_le_left.trans inf_le_left)
      have hY₀_norm_pair : ∀ y ∈ Y₀,
          (∀ w ∈ W₁, y * w * y⁻¹ ∈ W₁) ∧ (∀ w ∈ W₂, y * w * y⁻¹ ∈ W₂) := by
        intro y hy
        exact ⟨fun w hw => (Subgroup.mem_normalizer_iff.mp hy.2.1.2 w).1 hw,
          fun w hw => (Subgroup.mem_normalizer_iff.mp hy.2.2 w).1 hw⟩
      have hY₀e : IsElementaryAbelian 2 Y₀ := IsElementaryAbelian.of_le hY hY₀_le_Y
      have hx_not_Y₀ : x ∉ Y₀ := by
        intro hx
        exact hxP₀ hx.2
      have hswap_of_not_mem : ∀ y ∈ Y, y ∉ P₀ →
          (∀ w ∈ W₁, y * w * y⁻¹ ∈ W₂) ∧ (∀ w ∈ W₂, y * w * y⁻¹ ∈ W₁) := by
        intro y hyY hyP
        rcases hperm y (hYP hyY) with hfirst | hsecond
        · exfalso
          apply hyP
          exact ⟨⟨hYP hyY, mem_normalizer_of_forall_conj_mem hfirst.1⟩,
            mem_normalizer_of_forall_conj_mem hfirst.2⟩
        · exact hsecond
      have hmul_mem : ∀ y ∈ Y, y ∉ P₀ →
          y * x ∈ P ⊓ Subgroup.normalizer (W₁ : Set G) ⊓
            Subgroup.normalizer (W₂ : Set G) := by
        intro y hyY hyP
        have hySwap := hswap_of_not_mem y hyY hyP
        refine ⟨⟨P.mul_mem (hYP hyY) hxP, ?_⟩, ?_⟩
        · apply mem_normalizer_of_forall_conj_mem
          intro w hw
          have hcalc : (y * x) * w * (y * x)⁻¹ = y * (x * w * x⁻¹) * y⁻¹ := by group
          rw [hcalc]
          exact hySwap.2 _ (hxswap.1 w hw)
        · apply mem_normalizer_of_forall_conj_mem
          intro w hw
          have hcalc : (y * x) * w * (y * x)⁻¹ = y * (x * w * x⁻¹) * y⁻¹ := by group
          rw [hcalc]
          exact hySwap.1 _ (hxswap.2 w hw)
      have hrelY₀ : Y₀.relIndex Y = 2 := by
        rw [Subgroup.relIndex_eq_two_iff]
        refine ⟨x, hxY, ?_⟩
        intro b hb
        by_cases hb₀ : b ∈ Y₀
        · have hbP : b ∈ P₀ := hb₀.2
          have hnot : b * x ∉ Y₀ := by
            intro hbx
            have hxP' : x ∈ P₀ := by
              have hb_inv : b⁻¹ ∈ P₀ := P₀.inv_mem hbP
              simpa [mul_assoc] using P₀.mul_mem hb_inv hbx.2
            exact hxP₀ hxP'
          simp [Xor, hb₀, hnot]
        · have hbP : b ∉ P₀ := fun h => hb₀ ⟨hb, h⟩
          have hbxP : b * x ∈ P₀ := hmul_mem b hb hbP
          have hbx₀ : b * x ∈ Y₀ := ⟨Y.mul_mem hb hxY, hbxP⟩
          simp [Xor, hb₀, hbx₀]
      have hCY_eq : Y ⊓ C = Y₀ ⊓ C := by
        apply le_antisymm
        · intro z hz
          refine ⟨?_, hz.2⟩
          refine ⟨hz.1, ?_⟩
          refine ⟨⟨hYP hz.1, ?_⟩, ?_⟩
          · apply mem_normalizer_of_forall_conj_mem
            intro w hw
            have h := Subgroup.mem_centralizer_iff.mp hz.2 w (hW₁_le hw)
            have hcalc : z * w * z⁻¹ = w := by
              calc z * w * z⁻¹ = (w * z) * z⁻¹ := by rw [h.symm]
                _ = w := by group
            rw [hcalc]
            exact hw
          · apply mem_normalizer_of_forall_conj_mem
            intro w hw
            have h := Subgroup.mem_centralizer_iff.mp hz.2 w (hW₂_le hw)
            have hcalc : z * w * z⁻¹ = w := by
              calc z * w * z⁻¹ = (w * z) * z⁻¹ := by rw [h.symm]
                _ = w := by group
            rw [hcalc]
            exact hw
        · exact inf_le_inf_right C hY₀_le_Y
      have hrel_C : C.relIndex Y = 2 * C.relIndex Y₀ := by
        calc C.relIndex Y = (Y ⊓ C).relIndex Y := by
              rw [inf_comm, Subgroup.inf_relIndex_right]
          _ = (Y₀ ⊓ C).relIndex Y := by rw [hCY_eq]
          _ = (Y₀ ⊓ C).relIndex Y₀ * Y₀.relIndex Y :=
              (Subgroup.relIndex_mul_relIndex (H := Y₀ ⊓ C) (K := Y₀) (L := Y)
                inf_le_left inf_le_left).symm
          _ = 2 * C.relIndex Y₀ := by
              rw [Subgroup.inf_relIndex_left, hrelY₀]
              ring
      have hCY0_eq : Y₀ ⊓ C = Y₀ ⊓ C₁ := by
        apply le_antisymm
        · exact inf_le_inf_left Y₀ (Subgroup.centralizer_le hW₁_le)
        · intro z hz
          refine ⟨hz.1, ?_⟩
          rw [hC_eq]
          refine ⟨hz.2, ?_⟩
          change z ∈ Subgroup.centralizer (W₂ : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro w₂ hw₂
          have hw₂' : w₂ ∈ W₁.map (MulAut.conj x) := by rw [hxmap₁]; exact hw₂
          obtain ⟨w₁, hw₁, hw₁eq⟩ := Subgroup.mem_map.mp hw₂'
          have hw₂eq : x * w₁ * x⁻¹ = w₂ := by simpa [MulAut.conj_apply] using hw₁eq
          have hzx : z * x = x * z :=
            congrArg Subtype.val (mul_comm' (⟨z, hY₀_le_Y hz.1⟩ : Y) (⟨x, hxY⟩ : Y))
          have hzx_inv : z * x⁻¹ = x⁻¹ * z := by
            calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
              _ = x⁻¹ * (z * x) * x⁻¹ := by rw [← hzx]
              _ = x⁻¹ * z := by group
          have hzw : w₁ * z = z * w₁ :=
            Subgroup.mem_centralizer_iff.mp hz.2 w₁ hw₁
          calc w₂ * z = (x * w₁ * x⁻¹) * z := by rw [hw₂eq]
            _ = x * w₁ * (x⁻¹ * z) := by group
            _ = x * w₁ * (z * x⁻¹) := by rw [← hzx_inv]
            _ = x * (w₁ * z) * x⁻¹ := by group
            _ = x * (z * w₁) * x⁻¹ := by rw [hzw]
            _ = (x * z) * w₁ * x⁻¹ := by group
            _ = (z * x) * w₁ * x⁻¹ := by rw [← hzx]
            _ = z * (x * w₁ * x⁻¹) := by group
            _ = z * w₂ := by rw [hw₂eq]
      have hrel_C_C₁ : C.relIndex Y₀ = C₁.relIndex Y₀ := by
        calc C.relIndex Y₀ = (C ⊓ Y₀).relIndex Y₀ := by rw [Subgroup.inf_relIndex_right]
          _ = (Y₀ ⊓ C).relIndex Y₀ := by rw [inf_comm]
          _ = (Y₀ ⊓ C₁).relIndex Y₀ := by rw [hCY0_eq]
          _ = C₁.relIndex Y₀ := by rw [Subgroup.inf_relIndex_left]
      have hY₀_bound : C₁.relIndex Y₀ *
          Nat.card ↥(W₁ ⊓ Subgroup.centralizer (Y₀ : Set G)) ≤ 2 ^ n := by
        by_cases h : Y₀ ≤ C₁
        · have hri : C₁.relIndex Y₀ = 1 := Subgroup.relIndex_eq_one.mpr h
          rw [hri, one_mul]
          calc Nat.card ↥(W₁ ⊓ Subgroup.centralizer (Y₀ : Set G)) ≤ Nat.card W₁ :=
                Subgroup.card_le_of_le inf_le_left
            _ = 2 ^ n := hcard₁
        · exact le_of_lt (hoff₁ Y₀ hY₀_le_P hY₀_norm_pair hY₀e h)
      have hY_eq_sup : Y = Y₀ ⊔ Subgroup.zpowers x := by
        apply le_antisymm
        · intro y hyY
          by_cases hy₀ : y ∈ Y₀
          · exact Subgroup.mem_sup_left hy₀
          · have hyP : y ∉ P₀ := fun h => hy₀ ⟨hyY, h⟩
            have hyxP : y * x ∈ P₀ := hmul_mem y hyY hyP
            have hyx₀ : y * x ∈ Y₀ := ⟨Y.mul_mem hyY hxY, hyxP⟩
            have hy_eq : y = (y * x) * x := by
              calc y = y * (x * x) := by rw [hx2', mul_one]
                _ = (y * x) * x := by group
            rw [hy_eq]
            exact Subgroup.mul_mem_sup hyx₀
              (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
        · exact sup_le hY₀_le_Y (Subgroup.zpowers_le.mpr hxY)
      have hCY_sup : Subgroup.centralizer (Y : Set G) =
          Subgroup.centralizer (Y₀ : Set G) ⊓
            Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
        rw [hY_eq_sup, centralizer_sup_eq_inf_centralizer]
      have hCx : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
          Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have hWY0 : W ⊓ Subgroup.centralizer (Y₀ : Set G) =
          (W₁ ⊓ Subgroup.centralizer (Y₀ : Set G)) ⊔
            (W₂ ⊓ Subgroup.centralizer (Y₀ : Set G)) := by
        have h := inf_centralizer_sup_eq_sup_inf_centralizer (A := W₁) (B := W₂) (Y := Y₀)
          hW₁_cent_W₂ hdisj (fun y hy => (hY₀_norm_pair y hy).1)
          (fun y hy => (hY₀_norm_pair y hy).2)
        simpa [hW₁₂] using h
      have hCWY : W ⊓ Subgroup.centralizer (Y : Set G) =
          ((W₁ ⊓ Subgroup.centralizer (Y₀ : Set G)) ⊔
            (W₂ ⊓ Subgroup.centralizer (Y₀ : Set G))) ⊓
            Subgroup.centralizer ({x} : Set G) := by
        rw [hCY_sup, hCx]
        calc W ⊓ (Subgroup.centralizer (Y₀ : Set G) ⊓ Subgroup.centralizer ({x} : Set G))
            = (W ⊓ Subgroup.centralizer (Y₀ : Set G)) ⊓ Subgroup.centralizer ({x} : Set G) := by
                rw [inf_assoc]
          _ = ((W₁ ⊓ Subgroup.centralizer (Y₀ : Set G)) ⊔
                (W₂ ⊓ Subgroup.centralizer (Y₀ : Set G))) ⊓
                Subgroup.centralizer ({x} : Set G) := by rw [hWY0]
      have hA_disj_B :
          (W₁ ⊓ Subgroup.centralizer (Y₀ : Set G)) ⊓
            (W₂ ⊓ Subgroup.centralizer (Y₀ : Set G)) = ⊥ := by
        apply le_antisymm
        · intro z hz
          have hzW₁ : z ∈ W₁ := hz.1.1
          have hzW₂ : z ∈ W₂ := hz.2.1
          have hzW : z ∈ W₁ ⊓ W₂ := ⟨hzW₁, hzW₂⟩
          simpa [hdisj] using hzW
        · exact bot_le
      have hAB_comm : (W₁ ⊓ Subgroup.centralizer (Y₀ : Set G)) ≤
          Subgroup.centralizer
            (((W₂ ⊓ Subgroup.centralizer (Y₀ : Set G)) : Subgroup G) : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact Subgroup.mem_centralizer_iff.mp (hW₁_cent_W₂ ha.1) b hb.1
      have hxAB : ∀ a ∈ W₁ ⊓ Subgroup.centralizer (Y₀ : Set G),
          x * a * x⁻¹ ∈ W₂ ⊓ Subgroup.centralizer (Y₀ : Set G) := by
        intro a ha
        refine ⟨hxswap.1 a ha.1, ?_⟩
        change x * a * x⁻¹ ∈ Subgroup.centralizer (Y₀ : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hya : y * a = a * y := Subgroup.mem_centralizer_iff.mp ha.2 y hy
        have hyx : y * x = x * y :=
          congrArg Subtype.val (mul_comm' (⟨y, hY₀_le_Y hy⟩ : Y) (⟨x, hxY⟩ : Y))
        have hyx_inv : y * x⁻¹ = x⁻¹ * y := by
          calc y * x⁻¹ = x⁻¹ * (x * y) * x⁻¹ := by group
            _ = x⁻¹ * (y * x) * x⁻¹ := by rw [← hyx]
            _ = x⁻¹ * y := by group
        calc y * (x * a * x⁻¹) = (y * x) * a * x⁻¹ := by group
          _ = (x * y) * a * x⁻¹ := by rw [hyx]
          _ = x * (y * a) * x⁻¹ := by group
          _ = x * (a * y) * x⁻¹ := by rw [hya]
          _ = x * a * (y * x⁻¹) := by group
          _ = x * a * (x⁻¹ * y) := by rw [hyx_inv]
          _ = (x * a * x⁻¹) * y := by group
      have hxBA : ∀ b ∈ W₂ ⊓ Subgroup.centralizer (Y₀ : Set G),
          x * b * x⁻¹ ∈ W₁ ⊓ Subgroup.centralizer (Y₀ : Set G) := by
        intro b hb
        refine ⟨hxswap.2 b hb.1, ?_⟩
        change x * b * x⁻¹ ∈ Subgroup.centralizer (Y₀ : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyb : y * b = b * y := Subgroup.mem_centralizer_iff.mp hb.2 y hy
        have hyx : y * x = x * y :=
          congrArg Subtype.val (mul_comm' (⟨y, hY₀_le_Y hy⟩ : Y) (⟨x, hxY⟩ : Y))
        have hyx_inv : y * x⁻¹ = x⁻¹ * y := by
          calc y * x⁻¹ = x⁻¹ * (x * y) * x⁻¹ := by group
            _ = x⁻¹ * (y * x) * x⁻¹ := by rw [← hyx]
            _ = x⁻¹ * y := by group
        calc y * (x * b * x⁻¹) = (y * x) * b * x⁻¹ := by group
          _ = (x * y) * b * x⁻¹ := by rw [hyx]
          _ = x * (y * b) * x⁻¹ := by group
          _ = x * (b * y) * x⁻¹ := by rw [hyb]
          _ = x * b * (y * x⁻¹) := by group
          _ = x * b * (x⁻¹ * y) := by rw [hyx_inv]
          _ = (x * b * x⁻¹) * y := by group
      have hCWY_card :
          Nat.card ↥(W ⊓ Subgroup.centralizer (Y : Set G)) =
            Nat.card ↥(W₁ ⊓ Subgroup.centralizer (Y₀ : Set G)) := by
        rw [hCWY]
        exact card_inf_centralizer_singleton_eq_of_conj_swap hx2 hAB_comm hA_disj_B hxAB hxBA
      have hY_bound_lt :
          C.relIndex Y * Nat.card ↥(W ⊓ Subgroup.centralizer (Y : Set G)) <
            2 ^ (2 * n) := by
        rw [hrel_C, hCWY_card]
        have hprod : (2 * C.relIndex Y₀) *
            Nat.card ↥(W₁ ⊓ Subgroup.centralizer (Y₀ : Set G)) = 2 * (C.relIndex Y₀ *
              Nat.card ↥(W₁ ⊓ Subgroup.centralizer (Y₀ : Set G))) := by ring
        rw [hprod]
        have hle : 2 * (C.relIndex Y₀ *
            Nat.card ↥(W₁ ⊓ Subgroup.centralizer (Y₀ : Set G))) ≤ 2 * 2 ^ n :=
          Nat.mul_le_mul_left 2 (by simpa [hrel_C_C₁] using hY₀_bound)
        have hlt : 2 * 2 ^ n < 2 ^ (2 * n) := by
          have h2lt : 2 < 2 ^ n := by
            calc 2 = 2 ^ 1 := by norm_num
              _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
          have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
          have hineq : 2 * 2 ^ n < 2 ^ n * 2 ^ n := by
            calc 2 * 2 ^ n = 2 ^ n * 2 := by ring
              _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_left h2lt hpos
          simpa [show 2 * n = n + n by omega, pow_add] using hineq
        exact lt_of_le_of_lt hle hlt
      have hYlt : Nat.card Y < 2 ^ (2 * n) := lt_of_le_of_lt hYcard_le hY_bound_lt
      exact absurd hYcard (not_le_of_gt hYlt)
  exact Subgroup.eq_of_le_of_card_ge hYleW_or_contra (by rw [hWcard]; exact hYcard)

end CFSG.GroupTheory

end
