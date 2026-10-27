module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2F0
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Count
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Line

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec2

omit [Finite G] in
theorem conj_sq_eq_imp {Z : Subgroup G} (hZ : IsElemAbelian 2 Z) {t : G}
    (ht : t ∈ normalizer (Z : Set G)) (hfix : ∀ w ∈ Z, t * w * t⁻¹ = w → w = 1) :
    ∀ w ∈ Z, (t * t) * w * (t * t)⁻¹ = w → w = 1 := by
  intro w hw h
  by_contra hw1
  have hcomm : ∀ x ∈ Z, ∀ x' ∈ Z, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hZ.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have htw : t * w * t⁻¹ ∈ Z := (mem_normalizer_iff.mp ht w).mp hw
  have hne : t * w * t⁻¹ ≠ w := fun h' => hw1 (hfix w hw h')
  have hfix2 : t * (w * (t * w * t⁻¹)) * t⁻¹ = w * (t * w * t⁻¹) := by
    have h1 : t * (t * w * t⁻¹) * t⁻¹ = w := by
      calc t * (t * w * t⁻¹) * t⁻¹ = t * t * w * (t * t)⁻¹ := by group
        _ = w := h
    calc t * (w * (t * w * t⁻¹)) * t⁻¹ = (t * w * t⁻¹) * (t * (t * w * t⁻¹) * t⁻¹) := by group
      _ = (t * w * t⁻¹) * w := by rw [h1]
      _ = w * (t * w * t⁻¹) := hcomm _ htw _ hw
  have h2 := hfix _ (Z.mul_mem hw htw) hfix2
  apply hne
  have hw2 : w * w = 1 := by rw [← sq]; exact hZ.2 w hw
  calc t * w * t⁻¹ = w * (w * (t * w * t⁻¹)) := by rw [← mul_assoc, hw2, one_mul]
    _ = w := by rw [h2, mul_one]

omit [Finite G] in
theorem exists_ne_one_conj_eq_of_pow {Z : Subgroup G} (hZ : IsElemAbelian 2 Z) (hZ1 : Z ≠ ⊥)
    {t : G} (ht : t ∈ normalizer (Z : Set G)) {m : ℕ} (htm : t ^ 2 ^ m = 1) :
    ∃ w ∈ Z, w ≠ 1 ∧ t * w * t⁻¹ = w := by
  by_contra hno
  push Not at hno
  have key : ∀ n : ℕ, ∀ w ∈ Z, t ^ 2 ^ n * w * (t ^ 2 ^ n)⁻¹ = w → w = 1 := by
    intro n
    induction n with
    | zero =>
      intro w hw h
      by_contra hw1
      exact hno w hw hw1 (by simpa using h)
    | succ n ih =>
      have htn : t ^ 2 ^ n ∈ normalizer (Z : Set G) := (normalizer (Z : Set G)).pow_mem ht _
      have h := conj_sq_eq_imp hZ htn ih
      intro w hw hfix
      apply h w hw
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact hfix
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
  exact (fun h => hw1 (Subtype.ext h)) (key m w hw (by rw [htm, one_mul, inv_one, mul_one]))

theorem mem_normalizer_centralizerMod {X Y Z : Subgroup G} {n : G}
    (hX : n ∈ normalizer (X : Set G)) (hY : n ∈ normalizer (Y : Set G))
    (hZ : n ∈ normalizer (Z : Set G)) : n ∈ normalizer (centralizerMod X Y Z : Set G) := by
  refine mem_normalizer_of_forall_conj_mem fun c hc => ?_
  obtain ⟨hcX, hcZ, hcY⟩ := mem_centralizerMod.mp hc
  refine mem_centralizerMod.mpr ⟨(mem_normalizer_iff.mp hX c).mp hcX,
    (normalizer (Z : Set G)).mul_mem ((normalizer (Z : Set G)).mul_mem hZ hcZ)
      ((normalizer (Z : Set G)).inv_mem hZ), fun w hw => ?_⟩
  have hw' : n⁻¹ * w * n ∈ Y := by
    have := (mem_normalizer_iff.mp ((normalizer (Y : Set G)).inv_mem hY) w).mp hw
    simpa using this
  have h1 := (mem_normalizer_iff.mp hZ _).mp (hcY _ hw')
  have h2 : n * ((n⁻¹ * w * n)⁻¹ * c⁻¹ * (n⁻¹ * w * n) * c) * n⁻¹ =
      w⁻¹ * (n * c * n⁻¹)⁻¹ * w * (n * c * n⁻¹) := by group
  rwa [h2] at h1

end Sec2

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem not_commute_of_sec2Z (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) {y : G} (hyA : y ∈ A)
    (hyZ : y ∈ normalizer (sec2Z A E F : Set G))
    (hyfix : ∀ w ∈ sec2Z A E F, y * w * y⁻¹ = w → w = 1) {w : G} (hwA : w ∈ A)
    (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) : y * w ≠ w * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hyw
  have hq := hF.quasisimple
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hNZ := oddCore_le_center hq.1 hq.2
  obtain ⟨T, hT, hwT⟩ := exists_isSylowOf_mem_centerIn c hwA hw2 hw1
  have hwK : w ∉ centralizer (A : Set G) := fun h => by
    have h1 := inf_eq_bot_of_odd_center (zpowers_le.mpr h)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hw2 hw1, pow_one]))
      hodd
    have h2 : w ∈ zpowers w ⊓ A := ⟨mem_zpowers w, hwA⟩
    rw [h1, mem_bot] at h2
    exact hw1 h2
  have hy := mem_sup_centralizer_of_commute c hNZ hT hwT hwK hyA hyw
  have hKT : centralizer (A : Set G) ≤ normalizer (T : Set G) := fun k hk =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht =>
      (mem_centralizer_iff.mp hk t (hT.le ht)))
  have hy' : y ∈ ((T ⊔ centralizer (A : Set G) : Subgroup G) : Set G) := hy
  rw [coe_mul_of_right_le_normalizer_left T _ hKT] at hy'
  obtain ⟨t, htT, k, hk, rfl⟩ := hy'
  have hZA : sec2Z A E F ≤ A := inf_le_left
  have hconj : ∀ z ∈ sec2Z A E F, t * z * t⁻¹ = t * k * z * (t * k)⁻¹ := fun z hz => by
    have hkz : k * z = z * k := (mem_centralizer_iff.mp hk z (hZA hz)).symm
    calc t * z * t⁻¹ = t * z * k * k⁻¹ * t⁻¹ := by group
      _ = t * k * z * k⁻¹ * t⁻¹ := by rw [mul_assoc t z k, ← hkz, ← mul_assoc]
      _ = t * k * z * (t * k)⁻¹ := by group
  have htZ : t ∈ normalizer (sec2Z A E F : Set G) := Sec2.mem_normalizer_of_forall_conj_mem
    fun z hz => by rw [hconj z hz]; exact (mem_normalizer_iff.mp hyZ z).mp hz
  obtain ⟨m, hm⟩ := hT.isPGroup ⟨t, htT⟩
  have htm : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hZe : IsElemAbelian 2 (sec2Z A E F) := by
    rw [hF.sec2Z_eq]
    exact AS76b.IsElemAbelian.mono hF.elemE (inf_le_left.trans inf_le_left)
  have hZ1 : sec2Z A E F ≠ ⊥ := fun h => by
    have := hF.card_sec2Z hodd
    rw [h, card_bot] at this
    omega
  obtain ⟨z, hz, hz1, htz⟩ := Sec2.exists_ne_one_conj_eq_of_pow hZe hZ1 htZ htm
  exact hz1 (hyfix z hz (by rw [← hconj z hz, htz]))

theorem eq_one_of_conj_eq_of_sec2Z (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) {y : G} (hyA : y ∈ A)
    (hyZ : y ∈ normalizer (sec2Z A E F : Set G))
    (hyfix : ∀ w ∈ sec2Z A E F, y * w * y⁻¹ = w → w = 1) {a : G} (ha : a ∈ E ⊓ A)
    (h : y * a * y⁻¹ = a) : a = 1 := by
  by_contra ha1
  exact not_commute_of_sec2Z hF hL hodd hyA hyZ hyfix ha.2 (hF.elemE.2 a ha.1) ha1
    (mul_inv_eq_iff_eq_mul.mp h)

theorem mem_sec2Z_of_conj_mul_inv_mem (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) {y : G} (hyA : y ∈ A)
    (hyZ : y ∈ normalizer (sec2Z A E F : Set G))
    (hyfix : ∀ w ∈ sec2Z A E F, y * w * y⁻¹ = w → w = 1) {a : G} (ha : a ∈ E ⊓ A)
    (h : y * a * y⁻¹ * a⁻¹ ∈ sec2Z A E F) : a ∈ sec2Z A E F := by
  set Z := sec2Z A E F with hZdef
  have hZEA : Z ≤ E ⊓ A := by
    rw [hZdef, hF.sec2Z_eq]
    exact fun z hz => ⟨hz.1.1, hz.2⟩
  have key : ∀ w₁ w₂ : G, y * w₁ * y⁻¹ * w₁⁻¹ = y * w₂ * y⁻¹ * w₂⁻¹ →
      y * (w₂⁻¹ * w₁) * y⁻¹ = w₂⁻¹ * w₁ := fun w₁ w₂ h12 => by
    calc y * (w₂⁻¹ * w₁) * y⁻¹ = (y * w₂ * y⁻¹)⁻¹ * (y * w₁ * y⁻¹ * w₁⁻¹) * w₁ := by group
      _ = (y * w₂ * y⁻¹)⁻¹ * (y * w₂ * y⁻¹ * w₂⁻¹) * w₁ := by rw [h12]
      _ = w₂⁻¹ * w₁ := by group
  let φ : ↥Z → ↥Z := fun w => ⟨y * w * y⁻¹ * (w : G)⁻¹,
    Z.mul_mem ((mem_normalizer_iff.mp hyZ w).mp w.2) (Z.inv_mem w.2)⟩
  have hφ : Function.Injective φ := fun w₁ w₂ h12 => by
    have h' := key w₁ w₂ (congrArg Subtype.val h12)
    have h1 := hyfix _ (Z.mul_mem (Z.inv_mem w₂.2) w₁.2) h'
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨_, h⟩
  have hw' := key a w (congrArg Subtype.val hw).symm
  have hb := eq_one_of_conj_eq_of_sec2Z hF hL hodd hyA hyZ hyfix
    ((E ⊓ A).mul_mem ((E ⊓ A).inv_mem (hZEA w.2)) ha) hw'
  rw [inv_mul_eq_one] at hb
  rw [← hb]
  exact w.2

theorem mem_normalizer_F_of_torus (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) {y : G} (hyA : y ∈ A)
    (hyE : y ∈ normalizer (E : Set G)) (hyEF : y ∈ normalizer ((E ⊓ F : Subgroup G) : Set G)) :
    y ∈ normalizer (F : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := hF.quasisimple
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hNZ := oddCore_le_center hq.1 hq.2
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  obtain ⟨-, hTsyl, -⟩ := sylow_sup_structure hRA hR.isPGroup hF.sylow
  have hyR : rightConjugate R y⁻¹ = R := (rightConjugate_eq_self_iff R y⁻¹).mpr
    (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      (mem_centralizer_iff.mp (hRA hr) _ (A.inv_mem hyA)).symm))
  have hyAR : rightConjugate (A ⊔ R) y⁻¹ = A ⊔ R := (rightConjugate_eq_self_iff _ y⁻¹).mpr
    (le_normalizer (mem_sup_left (A.inv_mem hyA)))
  set D := rightConjugate F y⁻¹ with hDdef
  have hD : IsElemAbelian 2 D := AS76b.isElemAbelian_rightConjugate hF.elemF y⁻¹
  have hD64 : Nat.card D = 64 := by rw [rightConjugate_card, hF.cardF]
  have hRD : R ≤ D := by
    rw [← hyR]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hF.R_le_F y⁻¹
  have hDAR : D ≤ A ⊔ R := by
    rw [← hyAR]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hF.F_le y⁻¹
  have hDeq := eq_inf_sup_of_le_sup hRA hRD hDAR
  have hDA16 : Nat.card (D ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hRD hDAR hRA1
    rw [hD64, hF.cardR] at this
    omega
  have hZ := centerIn_inf_eq hF
  have hyN : y⁻¹ ∈ normalizer ((E ⊓ F ⊓ A : Subgroup G) : Set G) :=
    inv_mem (inf_normalizer_le_normalizer_inf ⟨hyEF, le_normalizer hyA⟩)
  have hZD : E ⊓ F ⊓ A ≤ D := by
    rw [← (rightConjugate_eq_self_iff _ y⁻¹).mpr hyN]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate (inf_le_left.trans inf_le_right) y⁻¹
  have hZ1 : E ⊓ F ⊓ A ≠ ⊥ := fun h => by
    have := hF.card_sec2Z hodd
    rw [hF.sec2Z_eq, h, card_bot] at this
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzK : z ∉ centralizer (A : Set G) := fun h => by
    have hz2 : z ^ 2 = 1 := hF.elemE.2 z hz.1.1
    have h1 := inf_eq_bot_of_odd_center (zpowers_le.mpr h)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1', pow_one]))
      hodd
    have h2 : z ∈ zpowers z ⊓ A := ⟨mem_zpowers z, hz.2⟩
    rw [h1, mem_bot] at h2
    exact hz1' h2
  have hDT : D ⊓ A ≤ (E ⊔ F) ⊓ A := by
    refine le_of_le_sup_centralizer hTsyl inf_le_right
      ((isPGroup_two_of_isElemAbelian hD).to_le inf_le_left) fun d hd => ?_
    exact mem_sup_centralizer_of_commute c hNZ hTsyl (hZ ▸ hz) hzK hd.2
      (congrArg Subtype.val (hD.1.is_comm.comm ⟨d, hd.1⟩ ⟨z, hZD hz⟩))
  have hEeq := eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le
  have hFeq := eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le
  have hne : E ⊓ A ≠ F ⊓ A := fun h => hF.ne (by rw [hEeq, hFeq, h])
  rcases Sec2.eq_or_eq_of_card_sixteen hq hL hodd hTsyl hDT
    (AS76b.IsElemAbelian.mono hD inf_le_left) hDA16
    (inf_le_inf_right A le_sup_left) (AS76b.IsElemAbelian.mono hF.elemE inf_le_left)
    (card_inf_left hF hodd)
    (inf_le_inf_right A le_sup_right) (AS76b.IsElemAbelian.mono hF.elemF inf_le_left)
    (card_inf_left hF.symm hodd) hne with h | h
  · exfalso
    apply hF.ne
    have hDE : D = E := by rw [hDeq, h, ← hEeq]
    have h1 : rightConjugate D y = F := by
      rw [hDdef, rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
    rw [← h1, hDE, (rightConjugate_eq_self_iff E y).mpr hyE]
  · have hDF : D = F := by rw [hDeq, h, ← hFeq]
    have := (rightConjugate_eq_self_iff F y⁻¹).mp hDF
    simpa using inv_mem this

theorem sec2P_le_normalizer_sec2Z
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : sec2P E ≤ normalizer (sec2Z A E F : Set G) := by
  intro p hp
  rw [← centerIn_sec2S_eq h11 hE16 hF hL hodd]
  exact mem_normalizer_centerIn (sec2P_le_normalizer_sec2S h11 hE16 hF hL hodd hp)

theorem mem_centralizerMod_of_conj_mem
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {y : G} (hyA : y ∈ A)
    (hyE : y ∈ normalizer (E : Set G)) (hyEF : y ∈ normalizer ((E ⊓ F : Subgroup G) : Set G))
    (hyfix : ∀ w ∈ E ⊓ F ⊓ A, y * w * y⁻¹ = w → w = 1) {p : G} (hp : p ∈ sec2P E)
    (hpy : p⁻¹ * (y * p * y⁻¹) ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) :
    p ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  obtain ⟨-, -, hCEF⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hZ := hF.sec2Z_eq
  have hRZ := hF.sup_sec2Z
  have hyZ : y ∈ normalizer (sec2Z A E F : Set G) := by
    rw [hZ]
    exact inf_normalizer_le_normalizer_inf ⟨hyEF, le_normalizer hyA⟩
  have hyfix' : ∀ w ∈ sec2Z A E F, y * w * y⁻¹ = w → w = 1 := fun w hw => hyfix w (hZ ▸ hw)
  have hpN := Sec2.sec2P_le E hp
  have hpZ := sec2P_le_normalizer_sec2Z h11 hE16 hF hL hodd hp
  have hyEA : y ∈ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hyE, le_normalizer hyA⟩
  set c := p⁻¹ * (y * p * y⁻¹) with hc
  have hcEF := hCEF hpy
  set L := rightConjugate (E ⊓ F) p⁻¹ with hLdef
  have hmemL : ∀ l, l ∈ L ↔ p⁻¹ * l * p ∈ E ⊓ F := fun l => by
    rw [hLdef, mem_rightConjugate_iff, inv_inv]
  have hyL : y ∈ normalizer (L : Set G) := Sec2.mem_normalizer_of_forall_conj_mem fun l hl => by
    rw [hmemL] at hl ⊢
    have h1 : p⁻¹ * (y * l * y⁻¹) * p = c * (y * (p⁻¹ * l * p) * y⁻¹) * c⁻¹ := by
      rw [hc]
      group
    rw [h1]
    exact (mem_normalizer_iff.mp hcEF _).mp ((mem_normalizer_iff.mp hyEF _).mp hl)
  have hLE : L ≤ E := fun l hl => by
    have h1 := (mem_normalizer_iff.mp hpN _).mp ((hmemL l).mp hl).1
    simpa [mul_assoc] using h1
  have hLZ : ∀ l ∈ L, l ∈ E ⊓ A → l ∈ sec2Z A E F := by
    intro l hl hlA
    have hl' : p⁻¹ * l * p ∈ ((R ⊔ sec2Z A E F : Subgroup G) : Set G) := by
      rw [hRZ]
      exact (hmemL l).mp hl
    have hZN : sec2Z A E F ≤ normalizer (R : Set G) := fun z hz =>
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
        hD.comm r (hD.R_le hr) z (hZ ▸ hz : z ∈ E ⊓ F ⊓ A).1.1)
    rw [coe_mul_of_right_le_normalizer_left R _ hZN] at hl'
    obtain ⟨r, hr, z, hz, hrz⟩ := hl'
    have hpz : p * z * p⁻¹ ∈ sec2Z A E F := (mem_normalizer_iff.mp hpZ z).mp hz
    have hl_eq : l = (p * r * p⁻¹) * (p * z * p⁻¹) := by
      calc l = p * (p⁻¹ * l * p) * p⁻¹ := by group
        _ = (p * r * p⁻¹) * (p * z * p⁻¹) := by rw [← hrz]; group
    have hzA : p * z * p⁻¹ ∈ E ⊓ A := by
      rw [hZ] at hpz
      exact ⟨hpz.1.1, hpz.2⟩
    have hrQ : p * r * p⁻¹ ∈ rightConjugate R p⁻¹ ⊓ (E ⊓ A) := by
      refine ⟨(mem_rightConjugate_iff R p⁻¹ _).mpr (by simpa [mul_assoc] using hr), ?_⟩
      have h1 := (E ⊓ A).mul_mem hlA ((E ⊓ A).inv_mem hzA)
      rwa [hl_eq, mul_inv_cancel_right] at h1
    rw [hD.inf_H _ (rightConjugate_mem_pointsIn hD.self_mem (inv_mem hpN)), mem_bot] at hrQ
    rw [hl_eq, hrQ, one_mul]
    exact hpz
  have hLEF : L ≤ E ⊓ F := fun l hl => by
    obtain ⟨a, ha, r, hr, rfl⟩ := hD.eq_mul l (hLE hl)
    have hyr : y * r * y⁻¹ = r := by
      rw [mem_centralizer_iff.mp (hRA hr) y hyA, mul_inv_cancel_right]
    have hyl := (mem_normalizer_iff.mp hyL _).mp hl
    have h1 : y * a * y⁻¹ * a⁻¹ = y * (a * r) * y⁻¹ * (a * r)⁻¹ := by
      calc y * a * y⁻¹ * a⁻¹ = y * a * y⁻¹ * (y * r * y⁻¹) * r⁻¹ * a⁻¹ := by
            rw [hyr, mul_inv_cancel_right]
        _ = y * (a * r) * y⁻¹ * (a * r)⁻¹ := by group
    have h2 : y * a * y⁻¹ * a⁻¹ ∈ sec2Z A E F := by
      refine hLZ _ ?_ ((E ⊓ A).mul_mem ((mem_normalizer_iff.mp hyEA a).mp ha)
        ((E ⊓ A).inv_mem ha))
      rw [h1]
      exact L.mul_mem hyl (L.inv_mem hl)
    have haZ := mem_sec2Z_of_conj_mul_inv_mem hF hL hodd hyA hyZ hyfix' ha h2
    rw [← hRZ]
    exact mul_mem (mem_sup_right haZ) (mem_sup_left hr)
  have hLeq : L = E ⊓ F := eq_of_le_of_card_ge hLEF (by rw [hLdef, rightConjugate_card])
  have hpEF : p ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) := by
    have := (rightConjugate_eq_self_iff _ _).mp hLeq
    simpa using inv_mem this
  refine mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd hp ?_
  rw [← (rightConjugate_eq_self_iff _ p).mpr hpEF]
  exact AschbacherTheorem3.rightConjugate_le_rightConjugate (le_inf hF.R_le_E hF.R_le_F) p

theorem exists_torus_sec2 (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    ∃ y ∈ A, y ∈ normalizer (E : Set G) ∧ y ∈ normalizer (F : Set G) ∧
      y ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) ∧
      ∀ w ∈ E ⊓ F ⊓ A, y * w * y⁻¹ = w → w = 1 := by
  obtain ⟨y, hyA, hyE, hyEF, hfix, -⟩ := exists_torus_of_frame hF hL hodd
  exact ⟨y, hyA, hyE, mem_normalizer_F_of_torus hF hL hodd hyA hyE hyEF, hyEF, hfix⟩

theorem mem_normalizer_sec2S_of_mem (hF : Frame G A A R g E F) {y : G} (hyA : y ∈ A)
    (hyE : y ∈ normalizer (E : Set G)) (hyF : y ∈ normalizer (F : Set G)) :
    y ∈ normalizer (sec2Z A E F : Set G) ∧
      y ∈ normalizer (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) : Set G) ∧
      y ∈ normalizer (sec2S A R E F : Set G) := by
  have hyEF : y ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hyE, hyF⟩
  have hyZ : y ∈ normalizer (sec2Z A E F : Set G) := by
    rw [hF.sec2Z_eq]
    exact inf_normalizer_le_normalizer_inf ⟨hyEF, le_normalizer hyA⟩
  have hyRZ : y ∈ normalizer ((R ⊔ sec2Z A E F : Subgroup G) : Set G) := by
    rw [hF.sup_sec2Z]
    exact hyEF
  have hyC := Sec2.mem_normalizer_centralizerMod (Sec2.normalizer_le_normalizer_sec2P E hyE)
    hyRZ hyZ
  exact ⟨hyZ, hyC, mem_normalizer_sup hyF hyC⟩

theorem mem_normalizer_sec2F0_of_mem
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {y : G} (hyA : y ∈ A)
    (hyE : y ∈ normalizer (E : Set G)) (hyF : y ∈ normalizer (F : Set G)) {x : G}
    (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) :
    y ∈ normalizer (sec2F0 A E x : Set G) := by
  obtain ⟨-, -, hyS⟩ := mem_normalizer_sec2S_of_mem hF hyA hyE hyF
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hyx : y * x * y⁻¹ ∈ sec2P F :=
    (mem_normalizer_iff.mp (Sec2.normalizer_le_normalizer_sec2P F hyF) x).mp hx
  have hyxS : y * x * y⁻¹ ∉ sec2S A R E F := fun h => hxS (by
    have := (mem_normalizer_iff.mp hyS x).mpr h
    exact this)
  have hEA : rightConjugate (E ⊓ A) y⁻¹ = E ⊓ A := (rightConjugate_eq_self_iff _ _).mpr
    (inv_mem (hD.normalizer_le_normalizer hyE))
  have hP : rightConjugate (sec2P E) y⁻¹ = sec2P E := (rightConjugate_eq_self_iff _ _).mpr
    (inv_mem (Sec2.normalizer_le_normalizer_sec2P E hyE))
  have hEx : rightConjugate (rightConjugate E x) y⁻¹ = rightConjugate E (y * x * y⁻¹) := by
    have h1 : rightConjugate E (y * x * y⁻¹) = rightConjugate E (x * y⁻¹) := by
      rw [show y * x * y⁻¹ = y * (x * y⁻¹) by group, ← rightConjugate_mul,
        (rightConjugate_eq_self_iff E y).mpr hyE]
    rw [rightConjugate_mul, h1]
  have h : rightConjugate (sec2F0 A E x) y⁻¹ = sec2F0 A E x := by
    rw [sec2F0, rightConjugate_sup', hEA, AschbacherTheorem3.rightConjugate_inf, hP, hEx]
    exact sec2F0_eq_sec2F0 h11 hE16 hF hL hodd hx hxS hyx hyxS
  simpa using inv_mem ((rightConjugate_eq_self_iff _ _).mp h)

end Frame

end CFSG.ComponentClassification.AS81
