module

public import CFSG.LocalAnalysis.GH72.MaxInvariant
public import CFSG.LocalAnalysis.GH72.Sec5E4b
public import CFSG.LocalAnalysis.GH72.Sec5Roles
public import CFSG.LocalAnalysis.GH72.Sec5BarType
import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups
public import CFSG.LocalAnalysis.GH72.Sec4CStruct
public import CFSG.LocalAnalysis.GH72.Sec5DTools

public section

namespace CFSG.GH72

open Subgroup
open scoped Pointwise

namespace G5d

open CFSG.ABGLocalTools (IsSylowOf)

section Commutator

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_sup_le {K₁ K₂ Z R : Subgroup G}
    (hR : K₁ ⊔ K₂ ≤ normalizer (R : Set G))
    (h₁ : ∀ g ∈ K₁, ∀ z ∈ Z, g * z * g⁻¹ * z⁻¹ ∈ R)
    (h₂ : ∀ g ∈ K₂, ∀ z ∈ Z, g * z * g⁻¹ * z⁻¹ ∈ R) :
    ∀ g ∈ K₁ ⊔ K₂, ∀ z ∈ Z, g * z * g⁻¹ * z⁻¹ ∈ R := by
  intro g hg
  let S : Subgroup G :=
    { carrier := {g | g ∈ K₁ ⊔ K₂ ∧ ∀ z ∈ Z, g * z * g⁻¹ * z⁻¹ ∈ R}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(K₁ ⊔ K₂).mul_mem ha hb, fun z hz => ?_⟩
        have h1 : a * b * z * (a * b)⁻¹ * z⁻¹ =
            (a * (b * z * b⁻¹ * z⁻¹) * a⁻¹) * (a * z * a⁻¹ * z⁻¹) := by group
        rw [h1]
        exact R.mul_mem ((mem_normalizer_iff.mp (hR ha) _).mp (hb' z hz)) (ha' z hz)
      one_mem' := ⟨(K₁ ⊔ K₂).one_mem, fun z _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(K₁ ⊔ K₂).inv_mem ha, fun z hz => ?_⟩
        have h1 : a⁻¹ * z * a⁻¹⁻¹ * z⁻¹ = a⁻¹ * (a * z * a⁻¹ * z⁻¹)⁻¹ * a := by group
        rw [h1]
        have := (mem_normalizer_iff.mp (hR ((K₁ ⊔ K₂).inv_mem ha)) _).mp (R.inv_mem (ha' z hz))
        simpa [mul_assoc] using this }
  have hle : K₁ ⊔ K₂ ≤ S := sup_le (fun g hg => ⟨mem_sup_left hg, h₁ g hg⟩)
    (fun g hg => ⟨mem_sup_right hg, h₂ g hg⟩)
  exact (hle hg).2

omit [Finite G] in
theorem mem_O_of_commutator_mem_of_isL2OrA7 {G : Type*} [Group G] {H W : Subgroup G} {q : ℕ}
    (hWH : W ≤ H) (hWs : IsL2OrA7 (bar H W) q) {w : G} (hw : w ∈ W)
    (h : ∀ w' ∈ W, w * w' * w⁻¹ * w'⁻¹ ∈ O H) : w ∈ O H := by
  set π := QuotientGroup.mk' (CFSG.oddCore H) with hπ
  have hwb : π ⟨w, hWH hw⟩ ∈ bar H W :=
    mem_map_of_mem _ (show (⟨w, hWH hw⟩ : H) ∈ W.subgroupOf H from hw)
  have hcen : (⟨π ⟨w, hWH hw⟩, hwb⟩ : bar H W) ∈ center (bar H W) := by
    rw [mem_center_iff]
    rintro ⟨_, ⟨w', hw', rfl⟩⟩
    apply Subtype.ext
    change π w' * π ⟨w, hWH hw⟩ = π ⟨w, hWH hw⟩ * π w'
    have h1 : π (⟨w, hWH hw⟩ * w' * ⟨w, hWH hw⟩⁻¹ * w'⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨y, hy, hyx⟩ := h w' hw'
      have : y = ⟨w, hWH hw⟩ * w' * ⟨w, hWH hw⟩⁻¹ * w'⁻¹ := Subtype.ext hyx
      rwa [← this]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 := congrArg (· * (π w' * π ⟨w, hWH hw⟩)) h1
    simp only [one_mul] at h2
    rw [← h2]
    group
  rw [CFSG.GH72.center_eq_bot_of_isL2OrA7 hWs, mem_bot] at hcen
  have hw1 : π ⟨w, hWH hw⟩ = 1 := congrArg Subtype.val hcen
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw1
  exact ⟨_, hw1, rfl⟩

omit [Finite G] in
theorem conj_commutator_mem {H₀ N Om : Subgroup G} (hH₀N : H₀ ≤ normalizer (N : Set G))
    (hH₀Om : H₀ ≤ normalizer (Om : Set G)) {g h : G} (hh : h ∈ H₀)
    (hgc : ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ Om) :
    ∀ n ∈ N, h * g * h⁻¹ * n * (h * g * h⁻¹)⁻¹ * n⁻¹ ∈ Om := by
  intro n hn
  have hn' : h⁻¹ * n * h ∈ N := by
    have := (mem_normalizer_iff.mp (hH₀N (H₀.inv_mem hh)) n).mp hn
    simpa using this
  have h1 : h * g * h⁻¹ * n * (h * g * h⁻¹)⁻¹ * n⁻¹ =
      h * (g * (h⁻¹ * n * h) * g⁻¹ * (h⁻¹ * n * h)⁻¹) * h⁻¹ := by group
  rw [h1]
  exact (mem_normalizer_iff.mp (hH₀Om hh) _).mp (hgc _ hn')

theorem mem_O_of_centralizes_mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {H₀ L₀ P Om : Subgroup G} (hOmH₀ : Om ≤ H₀) (hH₀Om : H₀ ≤ normalizer (Om : Set G))
    (hOm : Odd (Nat.card Om)) (hL₀H₀ : L₀ ≤ H₀) (hPH₀ : P ≤ H₀)
    (hH₀N : H₀ ≤ normalizer ((L₀ ⊔ Om : Subgroup G) : Set G))
    (hcen : ∀ w ∈ L₀, (∀ w' ∈ L₀, w * w' * w⁻¹ * w'⁻¹ ∈ Om) → w ∈ Om)
    (hP : IsPGroup p P) (hH₀K : H₀ ≤ normalizer ((P ⊔ (L₀ ⊔ Om) : Subgroup G) : Set G))
    {g : G} (hg : g ∈ P ⊔ (L₀ ⊔ Om)) (hgc : ∀ n ∈ L₀ ⊔ Om, g * n * g⁻¹ * n⁻¹ ∈ Om) :
    g ∈ O H₀ := by
  set N : Subgroup G := L₀ ⊔ Om with hN
  set K : Subgroup G := P ⊔ N with hK
  have hNH₀ : N ≤ H₀ := sup_le hL₀H₀ hOmH₀
  have hKH₀ : K ≤ H₀ := sup_le hPH₀ hNH₀
  let C : Subgroup G :=
    { carrier := {g | g ∈ H₀ ∧ ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ Om}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨H₀.mul_mem ha hb, fun n hn => ?_⟩
        have h1 : a * b * n * (a * b)⁻¹ * n⁻¹ =
            (a * (b * n * b⁻¹ * n⁻¹) * a⁻¹) * (a * n * a⁻¹ * n⁻¹) := by group
        rw [h1]
        exact Om.mul_mem ((mem_normalizer_iff.mp (hH₀Om ha) _).mp (hb' n hn)) (ha' n hn)
      one_mem' := ⟨H₀.one_mem, fun n _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨H₀.inv_mem ha, fun n hn => ?_⟩
        have hn' : a⁻¹ * n * a ∈ N := by
          have := (mem_normalizer_iff.mp (hH₀N (H₀.inv_mem ha)) n).mp hn
          simpa using this
        have h1 : a⁻¹ * n * a⁻¹⁻¹ * n⁻¹ =
            (a * (a⁻¹ * n * a) * a⁻¹ * (a⁻¹ * n * a)⁻¹)⁻¹ := by group
        rw [h1]
        exact Om.inv_mem (ha' _ hn') }
  have hH₀C : H₀ ≤ normalizer (C : Set G) := by
    intro h hh
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨c, ⟨hc, hc'⟩, rfl⟩
    exact ⟨H₀.mul_mem (H₀.mul_mem hh hc) (H₀.inv_mem hh), conj_commutator_mem hH₀N hH₀Om hh hc'⟩
  set R : Subgroup G := C ⊓ K with hR
  have hRH₀ : R ≤ H₀ := inf_le_right.trans hKH₀
  have hH₀R : H₀ ≤ normalizer (R : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨hH₀C hg, hH₀K hg⟩
  have hL₀Om : L₀ ≤ normalizer (Om : Set G) := hL₀H₀.trans hH₀Om
  have hRN : R ⊓ N ≤ Om := by
    rintro x ⟨⟨⟨-, hxC⟩, -⟩, hxN⟩
    obtain ⟨w, hw, o, ho, rfl⟩ := mem_sup_of_le_normalizer' hL₀Om hxN
    refine Om.mul_mem (hcen w hw fun w' hw' => ?_) ho
    have ha : o * w' * o⁻¹ * w'⁻¹ ∈ Om := by
      have h1 : o * w' * o⁻¹ * w'⁻¹ = o * (w' * o⁻¹ * w'⁻¹) := by group
      rw [h1]
      exact Om.mul_mem ho ((mem_normalizer_iff.mp (hL₀Om hw') _).mp (Om.inv_mem ho))
    have hx := hxC w' (mem_sup_left hw')
    have h2 : w * w' * w⁻¹ * w'⁻¹ =
        (w * (o * w' * o⁻¹ * w'⁻¹) * w⁻¹)⁻¹ * (w * o * w' * (w * o)⁻¹ * w'⁻¹) := by group
    rw [h2]
    exact Om.mul_mem (Om.inv_mem ((mem_normalizer_iff.mp (hL₀Om hw) _).mp ha)) hx
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hPN : P ≤ normalizer (N : Set G) := hPH₀.trans hH₀N
  have hRodd : Odd (Nat.card R) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2
    have hr' : orderOf (r : G) = 2 := by rw [Subgroup.orderOf_coe, hr]
    have hrK : (r : G) ∈ N ⊔ P := by
      rw [sup_comm]
      exact r.2.2
    obtain ⟨n, hn, q, hq, hnq⟩ := mem_sup_of_le_normalizer hPN hrK
    have h2r : IsPGroup 2 (zpowers (n * q)) := by
      rw [hnq]
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr', pow_one])
    have hrN : (r : G) ∈ N := hnq ▸ mem_of_mul_mem_of_isPGroup_two hPN hPodd hn hq h2r
    have hrO : (r : G) ∈ Om := hRN ⟨r.2, hrN⟩
    have hdvd : orderOf (r : G) ∣ Nat.card Om := Subgroup.orderOf_dvd_natCard _ hrO
    rw [hr'] at hdvd
    exact (Nat.not_even_iff_odd.mpr hOm) (even_iff_two_dvd.mpr hdvd)
  exact le_O_of_le_normalizer hRH₀ hH₀R hRodd ⟨⟨hKH₀ hg, hgc⟩, hg⟩

theorem commutator_le_O_of_eq_sup {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {H W P A Z H₀ : Subgroup G} (hWH : W ≤ H) (hPH : P ≤ H) (hAH : A ≤ H)
    (hWn : ((W ⊔ O H).subgroupOf H).Normal)
    (hcen : ∀ w ∈ W, (∀ w' ∈ W, w * w' * w⁻¹ * w'⁻¹ ∈ O H) → w ∈ O H)
    (hP : IsPGroup p P) (hAP : A ≤ normalizer (P : Set G))
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hZA : Z ≤ A)
    (hZW : Z ≤ centralizer (W : Set G)) (hH₀ : H₀ = W ⊔ P ⊔ A ⊔ O H) :
    ⁅H₀, Z⁆ ≤ O H₀ := by
  have hOH : O H ≤ H := map_subtype_le _
  set N : Subgroup G := W ⊔ O H with hN
  have hNH : N ≤ H := sup_le hWH hOH
  have hHN : H ≤ normalizer (N : Set G) := (normal_subgroupOf_iff_le_normalizer hNH).mp hWn
  have hH₀H : H₀ ≤ H := by
    rw [hH₀]
    exact sup_le (sup_le (sup_le hWH hPH) hAH) hOH
  have hOHH₀ : O H ≤ H₀ := by
    rw [hH₀]
    exact le_sup_right
  have hWH₀ : W ≤ H₀ := by
    rw [hH₀]
    exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hPH₀ : P ≤ H₀ := by
    rw [hH₀]
    exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hAH₀ : A ≤ H₀ := by
    rw [hH₀]
    exact le_sup_right.trans le_sup_left
  have hH₀O : H₀ ≤ normalizer (O H : Set G) := hH₀H.trans (le_normalizer_O H)
  have hWO : W ≤ normalizer (O H : Set G) := hWH.trans (le_normalizer_O H)
  set K : Subgroup G := P ⊔ N with hK
  have hPN : P ≤ normalizer (N : Set G) := hPH.trans hHN
  have hH₀K : H₀ ≤ normalizer (K : Set G) := by
    rw [hH₀]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact (le_sup_left.trans (le_normalizer_sup_of_le_normalizer hPN))
    · exact fun x hx => mem_normalizer_sup (le_normalizer hx) (hPN hx)
    · exact fun a ha => mem_normalizer_sup (hAP ha) (hHN (hAH ha))
    · exact (le_sup_right.trans (le_normalizer_sup_of_le_normalizer hPN))
  have hZc : ∀ z ∈ Z, ∀ n ∈ N, z * n * z⁻¹ * n⁻¹ ∈ O H := by
    intro z hz n hn
    obtain ⟨w, hw, o, ho, rfl⟩ := mem_sup_of_le_normalizer' hWO hn
    have hzw : z * w = w * z := (mem_centralizer_iff.mp (hZW hz) w hw).symm
    have h1 : z * (w * o) * z⁻¹ * (w * o)⁻¹ = w * (z * o * z⁻¹ * o⁻¹) * w⁻¹ := by
      calc z * (w * o) * z⁻¹ * (w * o)⁻¹ = (z * w) * o * z⁻¹ * o⁻¹ * w⁻¹ := by group
        _ = (w * z) * o * z⁻¹ * o⁻¹ * w⁻¹ := by rw [hzw]
        _ = w * (z * o * z⁻¹ * o⁻¹) * w⁻¹ := by group
    rw [h1]
    refine (mem_normalizer_iff.mp (hWO hw) _).mp ?_
    exact (O H).mul_mem ((mem_normalizer_iff.mp (le_normalizer_O H (hAH (hZA hz))) o).mp ho)
      ((O H).inv_mem ho)
  have hcC : ∀ g ∈ H₀, ∀ z ∈ Z, ∀ n ∈ N,
      g * z * g⁻¹ * z⁻¹ * n * (g * z * g⁻¹ * z⁻¹)⁻¹ * n⁻¹ ∈ O H := by
    intro g hg z hz n hn
    have h1 := conj_commutator_mem (hH₀H.trans hHN) hH₀O hg (hZc z hz)
    have hx : g * z * g⁻¹ ∈ H₀ := H₀.mul_mem (H₀.mul_mem hg (hAH₀ (hZA hz))) (H₀.inv_mem hg)
    have h2 : g * z * g⁻¹ * z⁻¹ * n * (g * z * g⁻¹ * z⁻¹)⁻¹ * n⁻¹ =
        (g * z * g⁻¹ * (z⁻¹ * n * z⁻¹⁻¹ * n⁻¹) * (g * z * g⁻¹)⁻¹) *
          (g * z * g⁻¹ * n * (g * z * g⁻¹)⁻¹ * n⁻¹) := by group
    rw [h2]
    exact (O H).mul_mem ((mem_normalizer_iff.mp (hH₀O hx) _).mp (hZc z⁻¹ (Z.inv_mem hz) n hn))
      (h1 n hn)
  have hKZ : ∀ g ∈ K, ∀ z ∈ Z, g * z * g⁻¹ * z⁻¹ ∈ K := by
    intro g hg z hz
    have h1 : g * z * g⁻¹ * z⁻¹ = g * (z * g⁻¹ * z⁻¹) := by group
    rw [h1]
    exact K.mul_mem hg ((mem_normalizer_iff.mp (hH₀K (hAH₀ (hZA hz))) _).mp (K.inv_mem hg))
  have hAZ : ∀ g ∈ A, ∀ z ∈ Z, g * z * g⁻¹ * z⁻¹ ∈ K := by
    intro g hg z hz
    rw [hAc g hg z (hZA hz)]
    simp
  have hH₀eq : H₀ = K ⊔ A := by
    rw [hH₀, hK, hN]
    apply le_antisymm
    · refine sup_le (sup_le (sup_le ?_ ?_) le_sup_right) ?_
      · exact (le_sup_left.trans le_sup_right).trans le_sup_left
      · exact le_sup_left.trans le_sup_left
      · exact (le_sup_right.trans le_sup_right).trans le_sup_left
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
      · exact sup_le ((le_sup_left.trans le_sup_left).trans le_sup_left) le_sup_right
      · exact le_sup_right.trans le_sup_left
  have hcK : ∀ g ∈ H₀, ∀ z ∈ Z, g * z * g⁻¹ * z⁻¹ ∈ K := by
    rw [hH₀eq]
    exact commutator_sup_le (hH₀eq ▸ hH₀K) hKZ hAZ
  rw [commutator_le]
  intro g hg z hz
  rw [commutatorElement_def]
  exact mem_O_of_centralizes_mod hp2 hOHH₀ hH₀O (card_O_odd H) hWH₀ hPH₀ (hH₀H.trans hHN) hcen hP
    hH₀K (hcK g hg z hz) (hcC g hg z hz)

end Commutator

section EndOf54'

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_ne_of_covers {H M₀ OM Y : Subgroup G} {qmin : ℕ} (hq : 5 ≤ qmin)
    (hOM : OM ≤ M₀) (hM₀OM : M₀ ≤ normalizer (OM : Set G)) (hOModd : Odd (Nat.card OM))
    (h47 : QuotIs M₀ OM (fun L _ => IsL2OrA7 L qmin)) (hcov : Covers H M₀ OM)
    (hY : IsKleinFour Y) (hYH : Y ≤ H) (hYM₀ : Y ≤ M₀) :
    ∃ u ∈ H ⊓ M₀, u ∈ normalizer (Y : Set G) ∧ ∀ y ∈ Y, y ≠ 1 → u * y * u⁻¹ ≠ y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  obtain ⟨L, _, f, hf, hker, hL⟩ := h47
  have : Finite L := Finite.of_surjective f hf
  have hYOM : Y ⊓ OM = ⊥ := by
    rw [inf_comm]
    exact G4c.inf_eq_bot_of_odd_of_isPGroup hOModd hY2
  have hmemker : ∀ m : M₀, f m = 1 ↔ (m : G) ∈ OM := by
    intro m
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
  have hYker : ∀ m : M₀, (m : G) ∈ Y → f m = 1 → m = 1 := by
    intro m hmY hm1
    have h4 : (m : G) ∈ Y ⊓ OM := ⟨hmY, (hmemker m).mp hm1⟩
    rw [hYOM, mem_bot] at h4
    exact Subtype.ext h4
  set V : Subgroup L := (Y.subgroupOf M₀).map f with hV
  set g : ↥(Y.subgroupOf M₀) →* L := f.comp (Y.subgroupOf M₀).subtype with hg
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 : f ((a : M₀)⁻¹ * b) = 1 := by
      rw [map_mul, map_inv]
      change (f a)⁻¹ * f b = 1
      rw [show f a = g a from rfl, show f b = g b from rfl, hab, inv_mul_cancel]
    have h2 := hYker _ (Y.mul_mem (Y.inv_mem a.2) b.2) h1
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  have hgrange : g.range = V := by
    rw [hg, MonoidHom.range_comp, range_subtype]
  have hVK : IsKleinFour V := by
    have e' : ↥Y ≃* ↥V := ((subgroupOfEquivOfLe hYM₀).symm.trans
      (MonoidHom.ofInjective hginj)).trans (MulEquiv.subgroupCongr hgrange)
    exact ⟨by rw [← Nat.card_congr e'.toEquiv]; exact IsKleinFour.card_four,
      by rw [← Monoid.exponent_eq_of_mulEquiv e']; exact IsKleinFour.exponent_two⟩
  have hLtop : IsL2OrA7 (⊤ : Subgroup L) 5 := by
    have h5 : IsL2OrA7 L 5 := by
      rcases hL with h | ⟨r, k, hr, hr2, hqk, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨r, k, hr, hr2, hq.trans hqk, he⟩
    exact CFSG.GH72.isL2OrA7_of_mulEquiv Subgroup.topEquiv h5
  obtain ⟨ub, ⟨-, hubN⟩, -, hubfix⟩ :=
    exists_three_element_mem_normalizer_kleinFour hLtop hVK le_top
  obtain ⟨⟨m, hm⟩, hmub⟩ := hf ub
  have hHM₀OM : H ⊓ M₀ ≤ normalizer (OM : Set G) := inf_le_right.trans hM₀OM
  obtain ⟨h, ⟨hhH, hhM₀⟩, o, ho, rfl⟩ := mem_sup_of_le_normalizer' hHM₀OM (hcov hm)
  have hfh : f ⟨h, hhM₀⟩ = ub := by
    rw [← hmub]
    have : (⟨h * o, hm⟩ : M₀) = ⟨h, hhM₀⟩ * ⟨o, hOM ho⟩ := rfl
    rw [this, map_mul, (hmemker ⟨o, hOM ho⟩).mpr ho, mul_one]
  set D : Subgroup G := H ⊓ OM with hD
  have hYD : Y ≤ normalizer (D : Set G) := fun y hy =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer (hYH hy), hM₀OM (hYM₀ hy)⟩
  have hDodd : Odd (Nat.card D) := hOModd.of_dvd_nat (card_dvd_of_le inf_le_right)
  have hhY : Y.map (MulAut.conj h).toMonoidHom ≤ Y ⊔ D := by
    rintro _ ⟨y, hy, rfl⟩
    change h * y * h⁻¹ ∈ Y ⊔ D
    have hyM₀ := hYM₀ hy
    have hconj : h * y * h⁻¹ ∈ M₀ := M₀.mul_mem (M₀.mul_mem hhM₀ hyM₀) (M₀.inv_mem hhM₀)
    have hfv : f ⟨h * y * h⁻¹, hconj⟩ ∈ V := by
      have hyV : f ⟨y, hyM₀⟩ ∈ V := mem_map_of_mem f (show (⟨y, hyM₀⟩ : M₀) ∈ Y.subgroupOf M₀
        from hy)
      have : (⟨h * y * h⁻¹, hconj⟩ : M₀) = ⟨h, hhM₀⟩ * ⟨y, hyM₀⟩ * ⟨h, hhM₀⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hfh]
      exact (mem_normalizer_iff.mp hubN _).mp hyV
    obtain ⟨⟨y', hy'M₀⟩, hy', hy'e⟩ := hfv
    have hy'Y : y' ∈ Y := hy'
    have hdO : y'⁻¹ * (h * y * h⁻¹) ∈ OM := by
      have : (⟨y'⁻¹ * (h * y * h⁻¹), M₀.mul_mem (M₀.inv_mem hy'M₀) hconj⟩ : M₀) =
          (⟨y', hy'M₀⟩ : M₀)⁻¹ * ⟨h * y * h⁻¹, hconj⟩ := rfl
      refine (hmemker ⟨_, M₀.mul_mem (M₀.inv_mem hy'M₀) hconj⟩).mp ?_
      rw [this, map_mul, map_inv, ← hy'e, inv_mul_cancel]
    have hdH : y'⁻¹ * (h * y * h⁻¹) ∈ H :=
      H.mul_mem (H.inv_mem (hYH hy'Y)) (H.mul_mem (H.mul_mem hhH (hYH hy)) (H.inv_mem hhH))
    have : h * y * h⁻¹ = y' * (y'⁻¹ * (h * y * h⁻¹)) := by group
    rw [this]
    exact mul_mem_sup hy'Y ⟨hdH, hdO⟩
  have hYDinf : D ⊓ Y = ⊥ := by
    rw [inf_comm]
    exact eq_bot_iff.mpr fun x hx => by
      have : x ∈ Y ⊓ OM := ⟨hx.1, hx.2.2⟩
      rwa [hYOM] at this
  have hsylY : IsSylowOf 2 Y (Y ⊔ D) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_left, hY2, fun h2 => ?_⟩
    have hcard : Nat.card (Y ⊔ D : Subgroup G) = Nat.card D * Nat.card Y := by
      rw [sup_comm]
      exact CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hYD hYDinf
    have h1 := Subgroup.relIndex_mul_card Y (Y ⊔ D)
    rw [inf_eq_left.mpr (le_sup_left : Y ≤ Y ⊔ D), hcard] at h1
    have h3 : Y.relIndex (Y ⊔ D) = Nat.card D := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    rw [h3] at h2
    exact (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr h2)
  obtain ⟨c, hc, hcY⟩ := exists_mem_map_conj_le_of_isSylowOf hsylY hhY (hY2.map _)
  obtain ⟨y'', hy'', d, hd, rfl⟩ := mem_sup_of_le_normalizer' hYD hc
  have hdY : (Y.map (MulAut.conj h).toMonoidHom).map (MulAut.conj d).toMonoidHom ≤ Y := by
    have h1 := map_mono (f := (MulAut.conj y''⁻¹).toMonoidHom) hcY
    rw [G4b.map_conj_map_conj, show y''⁻¹ * (y'' * d) = d by group,
      G4b.mem_normalizer_iff_map_conj_eq'.mp (le_normalizer (Y.inv_mem hy''))] at h1
    exact h1
  rw [G4b.map_conj_map_conj] at hdY
  have hdYeq : Y.map (MulAut.conj (d * h)).toMonoidHom = Y :=
    eq_of_le_of_card_ge hdY (by rw [card_map_of_injective (MulAut.conj (d * h)).injective])
  refine ⟨d * h, ⟨H.mul_mem hd.1 hhH, M₀.mul_mem (hOM hd.2) hhM₀⟩,
    G4b.mem_normalizer_iff_map_conj_eq'.mpr hdYeq, fun y hy hy1 hyfix => ?_⟩
  have hfd : f ⟨d, hOM hd.2⟩ = 1 := (hmemker ⟨d, hOM hd.2⟩).mpr hd.2
  have hyM₀ := hYM₀ hy
  have hfy : f ⟨y, hyM₀⟩ ∈ V := mem_map_of_mem f (show (⟨y, hyM₀⟩ : M₀) ∈ Y.subgroupOf M₀
    from hy)
  have hfy1 : f ⟨y, hyM₀⟩ ≠ 1 := fun h1 =>
    hy1 (congrArg Subtype.val (hYker ⟨y, hyM₀⟩ hy h1))
  refine hubfix _ hfy hfy1 ?_
  have hdh : (⟨d * h, M₀.mul_mem (hOM hd.2) hhM₀⟩ : M₀) = ⟨d, hOM hd.2⟩ * ⟨h, hhM₀⟩ := rfl
  have : (⟨(d * h) * y * (d * h)⁻¹, M₀.mul_mem (M₀.mul_mem (M₀.mul_mem (hOM hd.2) hhM₀) hyM₀)
      (M₀.inv_mem (M₀.mul_mem (hOM hd.2) hhM₀))⟩ : M₀) =
      ⟨d * h, M₀.mul_mem (hOM hd.2) hhM₀⟩ * ⟨y, hyM₀⟩ * (⟨d * h, M₀.mul_mem (hOM hd.2) hhM₀⟩)⁻¹ :=
    rfl
  have hval := congrArg f (Subtype.ext hyfix : (⟨(d * h) * y * (d * h)⁻¹, M₀.mul_mem (M₀.mul_mem
      (M₀.mul_mem (hOM hd.2) hhM₀) hyM₀) (M₀.inv_mem (M₀.mul_mem (hOM hd.2) hhM₀))⟩ : M₀) =
      ⟨y, hyM₀⟩)
  rw [this, map_mul, map_mul, map_inv, hdh, map_mul, hfd, one_mul, hfh] at hval
  exact hval

end EndOf54'

end G5d

namespace Sec5ConfigTR

open G5d

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  {𝔠 : Sec5ConfigR ρ p} (𝔱 : Sec5ConfigTR 𝔠)

theorem exists_isCovering_of_end
    (hHns : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5)) (hYM₀ : ρ.Y ≤ ρ.M₀)
    (h1R : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y)))
    {Tt : Subgroup G} (hPJ : 𝔠.P ≤ normalizer (CFSG.ambientMaxCardZJ Tt : Set G))
    (hJ : ρ.IsCovering 𝔱.t (normalizer (CFSG.ambientMaxCardZJ Tt : Set G))) :
    ∃ H, ρ.IsCovering p H := by
  have : Fact p.Prime := ⟨𝔠.hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J : Subgroup G := normalizer (CFSG.ambientMaxCardZJ Tt : Set G) with hJdef
  obtain ⟨⟨hJloc, hAJ, -⟩, hcovM, hcovN⟩ := hJ
  have hJtop : J ≠ ⊤ := ρ.ne_top_of_isPLocal 𝔱.ht.1 𝔱.ht.2.1 hJloc
  have hA2 : IsPGroup 2 A := ρ.isPGroup_A
  have hXA : ρ.X ≤ A := ρ.X_le_A
  have hYA : ρ.Y ≤ A := ρ.Y_le_A
  have hY4 : IsKleinFour ρ.Y := ρ.isKleinFour_Y
  have hY2 : IsPGroup 2 (ρ.Y) := hA2.to_le hYA
  have hYJ : ρ.Y ≤ J := hYA.trans hAJ
  have hQP : 𝔠.Q ≤ 𝔠.P := inf_le_left
  have hQJ : 𝔠.Q ≤ J := hQP.trans hPJ
  have hAH₀ : A ≤ 𝔠.H₀ := le_sup_right.trans 𝔠.hH₀.1
  have hAQ : A ≤ normalizer (𝔠.Q : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨𝔠.hP.2.2.1 ha, le_normalizer_O _ (hAH₀ ha)⟩
  have hYQ : ρ.Y ≤ normalizer (𝔠.Q : Set G) := hYA.trans hAQ
  have hQodd : Odd (Nat.card 𝔠.Q) := by
    obtain ⟨n, hn⟩ := (𝔠.hP.2.1.to_le hQP).exists_card_eq
    rw [hn]
    exact (𝔠.hp.odd_of_ne_two 𝔠.hp2).pow
  obtain ⟨u, ⟨huH₁, -⟩, huY, humove⟩ := exists_mem_normalizer_ne_of_covers
    (H := 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) le_rfl ρ.O_M_le_M₀ ρ.M₀_le_normalizer_O_M
    (card_O_odd _) hHns 𝔠.hH₁.2.1 hY4
    (le_inf (hYA.trans hAH₀) hYQ) hYM₀
  have huQ : u ∈ normalizer (𝔠.Q : Set G) := huH₁.2
  have hQO : 𝔠.Q ⊓ O J ≠ ⊥ := by
    intro hQO
    obtain ⟨L₀, hL₀JM, hYL₀, hcovL₀, -, hL₀n, hL₀O, -, -, -⟩ := h1R J hJtop hAJ hcovM
    have hL₀J : L₀ ≤ J := hL₀JM.trans inf_le_left
    have hL₀s : IsL2OrA7 (bar J L₀) 5 := isL2OrA7_bar_of_covers hL₀J (hL₀JM.trans inf_le_right)
      ρ.M₀_le_normalizer_O_M hcovL₀ hL₀O hHns
    have hLn : (bar J L₀).Normal := by
      rw [← G4c.bar_sup_O hL₀J]
      exact hL₀n.map _ (QuotientGroup.mk'_surjective _)
    have hYL : bar J ρ.Y ≤ bar J L₀ := G4c.bar_mono hYL₀
    have hYQle : ⁅ρ.Y, 𝔠.Q⁆ ≤ 𝔠.Q := le_normalizer_iff_commutator_le_right.mp hYQ
    have hKeq : bar J ⁅ρ.Y, 𝔠.Q⁆ = ⁅bar J (ρ.Y), bar J 𝔠.Q⁆ := G4c.bar_commutator hYJ hQJ
    have hKL : ⁅bar J (ρ.Y), bar J 𝔠.Q⁆ ≤ bar J L₀ :=
      (commutator_mono hYL le_rfl).trans (commutator_le_left _ _)
    have hKodd : Odd (Nat.card (⁅bar J (ρ.Y), bar J 𝔠.Q⁆ : Subgroup (Bar J))) := by
      rw [← hKeq]
      exact G4c.odd_card_bar (hQodd.of_dvd_nat (card_dvd_of_le hYQle))
    have hL5 : IsL2PGL2OrA7OrV4 (bar J L₀) := Or.inl hL₀s
    obtain ⟨a, haY, ha1, haK⟩ := exists_le_centralizer_of_odd_of_kleinFour_le_normalizer hL5
      (G4c.isKleinFour_bar hYJ hY4) hYL hKL hKodd (normalizer_commutator_ge_left _ _)
    obtain ⟨⟨y₀, hy₀J⟩, hy₀Y, rfl⟩ := haY
    have hy₀Y' : y₀ ∈ ρ.Y := hy₀Y
    have hy₀1 : y₀ ≠ 1 := by
      rintro rfl
      exact ha1 (map_one _)
    have hy₀c : y₀ ∈ centralizer ((⁅ρ.Y, 𝔠.Q⁆ : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro k hk
      have hkQ : k ∈ 𝔠.Q := hYQle hk
      have hkJ := hQJ hkQ
      have hkb : QuotientGroup.mk' (CFSG.oddCore J) ⟨k, hkJ⟩ ∈
          ⁅bar J (ρ.Y), bar J 𝔠.Q⁆ := by
        rw [← hKeq]
        exact mem_map_of_mem _ (show (⟨k, hkJ⟩ : J) ∈ (⁅ρ.Y, 𝔠.Q⁆ : Subgroup G).subgroupOf J
          from hk)
      have hcomm := mem_centralizer_singleton_iff.mp (haK hkb)
      have hc1 : y₀ * k * y₀⁻¹ * k⁻¹ ∈ 𝔠.Q :=
        𝔠.Q.mul_mem ((mem_normalizer_iff.mp (hYQ hy₀Y') k).mp hkQ) (𝔠.Q.inv_mem hkQ)
      have hc2 : y₀ * k * y₀⁻¹ * k⁻¹ ∈ O J := by
        have h1 : QuotientGroup.mk' (CFSG.oddCore J)
            ((⟨y₀, hy₀J⟩ : J) * ⟨k, hkJ⟩ * (⟨y₀, hy₀J⟩ : J)⁻¹ * (⟨k, hkJ⟩ : J)⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
          group
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact ⟨_, h1, rfl⟩
      have hc : y₀ * k * y₀⁻¹ * k⁻¹ ∈ 𝔠.Q ⊓ O J := ⟨hc1, hc2⟩
      rw [hQO, mem_bot] at hc
      calc k * y₀ = (y₀ * k * y₀⁻¹ * k⁻¹)⁻¹ * (y₀ * k) := by group
        _ = y₀ * k := by rw [hc, inv_one, one_mul]
    have huK : u ∈ normalizer ((⁅ρ.Y, 𝔠.Q⁆ : Subgroup G) : Set G) :=
      mem_normalizer_commutator' huY huQ
    have hy₁Y : u * y₀ * u⁻¹ ∈ ρ.Y := (mem_normalizer_iff.mp huY y₀).mp hy₀Y'
    have hy₁c : u * y₀ * u⁻¹ ∈ centralizer ((⁅ρ.Y, 𝔠.Q⁆ : Subgroup G) : Set G) :=
      (mem_normalizer_iff.mp (G4b.mem_normalizer_centralizer huK) y₀).mp hy₀c
    have hYc : ρ.Y ≤ centralizer ((⁅ρ.Y, 𝔠.Q⁆ : Subgroup G) : Set G) := by
      classical
      have : IsKleinFour (ρ.Y) := hY4
      have : Fintype (ρ.Y) := Fintype.ofFinite _
      intro z hz
      have hz' : (⟨z, hz⟩ : ρ.Y) ∈ (Finset.univ : Finset (ρ.Y)) := Finset.mem_univ _
      rw [← IsKleinFour.eq_finset_univ (x := (⟨y₀, hy₀Y'⟩ : ρ.Y))
        (y := (⟨u * y₀ * u⁻¹, hy₁Y⟩ : ρ.Y))
        (fun h => hy₀1 (congrArg Subtype.val h))
        (fun h => hy₀1 (by
          have h' : u * y₀ * u⁻¹ = 1 := congrArg Subtype.val h
          calc y₀ = u⁻¹ * (u * y₀ * u⁻¹) * u := by group
            _ = 1 := by rw [h']; group))
        (fun h => humove y₀ hy₀Y' hy₀1 (congrArg Subtype.val h).symm)] at hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
      rcases hz' with h | h | h | h
      · have : z = y₀ * (u * y₀ * u⁻¹) := congrArg Subtype.val h
        rw [this]
        exact (centralizer _).mul_mem hy₀c hy₁c
      · have : z = y₀ := congrArg Subtype.val h
        rw [this]
        exact hy₀c
      · have : z = u * y₀ * u⁻¹ := congrArg Subtype.val h
        rw [this]
        exact hy₁c
      · have : z = 1 := congrArg Subtype.val h
        rw [this]
        exact (centralizer _).one_mem
    apply 𝔠.hH₁.1
    have hcop : Nat.Coprime (Nat.card (ρ.Y)) (Nat.card 𝔠.Q) := by
      rw [IsKleinFour.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hQodd)
    have hQle := CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite hYQ hcop
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd)
    rw [le_centralizer_iff]
    refine hQle.trans (sup_le ?_ inf_le_right)
    rw [commutator_comm, ← le_centralizer_iff]
    exact hYc
  have hR1 : 𝔠.P ⊓ O J ≠ ⊥ := fun h =>
    hQO (le_bot_iff.mp (h ▸ inf_le_inf_right _ hQP))
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf p (𝔠.P ⊓ O J) (O J) :=
    isSylowOf_inf_O_of_isMaxInvIn 𝔠.hp hA2 (hAJ.trans le_normalizer)
      (IsMaxInvIn.of_le 𝔠.hP hPJ le_top)
  have hAR : A ≤ normalizer ((𝔠.P ⊓ O J : Subgroup G) : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨𝔠.hP.2.2.1 ha, le_normalizer_O J (hAJ ha)⟩
  have hPR : 𝔠.P ≤ normalizer ((𝔠.P ⊓ O J : Subgroup G) : Set G) := fun g hg =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hg, le_normalizer_O J (hPJ hg)⟩
  refine ⟨normalizer ((𝔠.P ⊓ O J : Subgroup G) : Set G),
    ⟨⟨_, hR1, 𝔠.hP.2.1.to_le inf_le_left, rfl⟩, hAR, 𝔠.P, 𝔠.hP, hPR⟩, ?_, ?_⟩
  · exact E4b.covers_normalizer_of_isSylowOf_O 𝔠.hp hA2 hXA rfl ρ.M₀_le ρ.O_M_le_M₀
      (fun H hH hcov x hx hx1 hxH => (h413 H hH).1 hcov x hx hx1 hxH) 𝔱.hx₁.1 𝔱.hx₁.2.1 hJtop
      hAJ hcovM hRsyl hAR
  · exact E4b.covers_normalizer_of_isSylowOf_O 𝔠.hp hA2 hYA rfl ρ.N₀_le ρ.O_N_le_N₀
      (fun H hH hcov y hy hy1 hyH => (h413 H hH).2 hcov y hy hy1 hyH) ρ.z₂_mem_Y ρ.z₂_ne_one hJtop
      hAJ hcovN hRsyl hAR

end Sec5ConfigTR

end CFSG.GH72
