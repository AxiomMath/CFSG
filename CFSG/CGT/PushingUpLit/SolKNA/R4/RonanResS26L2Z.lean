module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26L2X
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26SylowL
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26Cosets
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26CentGen
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26CommAll
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3M

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.CGT.PushingUpLit.SolKNA.R4
open scoped commutatorElement

theorem mem_center_subtype_iff {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hLC : Subgroup.centralizer (L : Set X) = Subgroup.center X) (x : ↥L) :
    x ∈ Subgroup.center ↥L ↔ (x : X) ∈ Subgroup.center X := by
  rw [← ker_domRestrict_socle hLC, MonoidHom.mem_ker, MonoidHom.domRestrict_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

section Cit


theorem s26_l2_center_bot {r : ℕ} (hr : 4 ≤ r) {X : Type} [Group X] [Finite X]
    (hO : classicalInvolutionOddCore X = ⊥)
    {Φ : Set (Subgroup X)} (hΦ : TypeRFam r Φ) {A : Subgroup X} (hA : A ∈ Φ)
    {S : Sylow 2 ↥A} {z : X} (hd : TightDatum A S z) (hz : IsUniqueInvolution A z)
    {L : Subgroup X} [L.Normal] (hLq : CFSG.IsQuasisimple ↥L)
    (hLC : Subgroup.centralizer (L : Set X) = Subgroup.center X) (hzn : z ∉ Subgroup.center X)
    (hnt : ∀ y : X, ∀ m ∈ Subgroup.center X, y * z * y⁻¹ = z * m → m = 1)
    (hL2 : CFSG.ClassicalInvolution.Q3.TA3.SmallL2 ↥(socleOf L))
    (hTC : Subgroup.centralizer ((socleOf L : Subgroup (X ⧸ Subgroup.center X)) :
      Set (X ⧸ Subgroup.center X)) = ⊥)
    (hgen : (⨆ g : X, conjSub g A) = ⊤)
    {u b : X} (huS : u ∈ (S : Subgroup A).map A.subtype) (hbS : b ∈ (S : Subgroup A).map A.subtype)
    (hou : orderOf u = 2 ^ (r - 1)) (hbu : b * u * b⁻¹ = u⁻¹)
    (hbb : b * b = u ^ 2 ^ (r - 2)) (hzu : u ^ 2 ^ (r - 2) = z) :
    Subgroup.center X = ⊥ := by
  classical
  obtain ⟨hbT, huL, -⟩ := s26_l2_x_mem hr hO hΦ hA hd hz hzn hnt hL2 hTC huS hbS hou hbu hbb hzu
  have hzL : z ∈ L := hzu ▸ L.pow_mem huL _
  have hbn : b ∉ L ⊔ Subgroup.center X := by
    intro h
    obtain ⟨l, hl, c, hc, hlc⟩ := Subgroup.mem_sup_of_normal_right.mp h
    apply hbT
    refine ⟨l, hl, ?_⟩
    show (QuotientGroup.mk l : X ⧸ Subgroup.center X) = QuotientGroup.mk b
    rw [← hlc, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).mpr hc, mul_one]
  have hbz : b ∉ Subgroup.zpowers u := fun h =>
    hbn (Subgroup.mem_sup_left ((Subgroup.zpowers_le.mpr huL) h))
  have hcard : Nat.card ↥((S : Subgroup A).map A.subtype) = 2 * orderOf u := by
    obtain ⟨e⟩ := hΦ.quat A hA _ (isSylow2In_map_subtype A S)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card, hou]
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega, pow_succ]
    ring
  have hcos := mem_zpowers_or_coset hcard huS hbS hbz
  have hAL : ∀ k ∈ A, k ∈ L ⊔ Subgroup.center X → k ∈ L :=
    mem_of_mem_sup_center hO huS hbS huL hbn hcos
  have hcomm : ∀ x y : X, ⁅x, y⁆ ∈ L ⊔ Subgroup.center X := by
    intro x y
    obtain ⟨l, hl, hl'⟩ := l2_comm_all (socleOf L) hL2 hTC (QuotientGroup.mk x) (QuotientGroup.mk y)
    have h1 : (QuotientGroup.mk l : X ⧸ Subgroup.center X) = QuotientGroup.mk ⁅x, y⁆ := by
      have h := map_commutatorElement (QuotientGroup.mk' (Subgroup.center X)) x y
      exact hl'.trans h.symm
    have h2 : l⁻¹ * ⁅x, y⁆ ∈ Subgroup.center X := QuotientGroup.eq.mp h1
    have h3 : ⁅x, y⁆ = l * (l⁻¹ * ⁅x, y⁆) := by group
    rw [h3]
    exact Subgroup.mul_mem_sup hl h2
  have hM : A ⊔ (L ⊔ Subgroup.center X) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun g => ?_
    intro y hy
    have ha : g⁻¹ * y * g ∈ A := mem_conjSub_iff.mp hy
    have h1 : y = ⁅g, g⁻¹ * y * g⁻¹⁻¹⁆ * (g⁻¹ * y * g) := by
      simp [commutatorElement_def]
      group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcomm _ _)) (Subgroup.mem_sup_left ha)
  have hKLZ : ∀ x : X, ∃ k ∈ A, ∃ l ∈ L, ∃ c ∈ Subgroup.center X, x = k * l * c := by
    intro x
    have hx : x ∈ A ⊔ (L ⊔ Subgroup.center X) := by rw [hM]; exact Subgroup.mem_top x
    obtain ⟨k, hk, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨l, hl, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hn
    exact ⟨k, hk, l, hl, c, hc, by rw [mul_assoc]⟩
  have hcenL : ∀ c ∈ Subgroup.center X, c ∈ L := by
    intro c hc
    obtain ⟨k, hk, l, hl, hkl⟩ :=
      center_le_mul_of_gen (K := A) (L := L) (Z := Subgroup.center X) le_rfl hgen hKLZ c hc
    have hkc : k = l⁻¹ * c := by
      have h1 : l⁻¹ * c = c * l⁻¹ := Subgroup.mem_center_iff.mp hc l⁻¹
      rw [h1, hkl]
      group
    have hkLZ : k ∈ L ⊔ Subgroup.center X := by
      rw [hkc]
      exact Subgroup.mul_mem_sup (L.inv_mem hl) hc
    have hkL : k ∈ L := hAL k hk hkLZ
    rw [hkl]
    exact L.mul_mem hkL hl
  obtain ⟨p, f, hp, hp2, hf, hmodel⟩ := hL2
  have hq3 : p ^ f ≠ 3 := fun h => hmodel.1.2.2.2.2 (by rw [h])
  have hq5 : 5 ≤ p ^ f := by
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hodd' := Nat.odd_iff.mp hodd
    omega
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥L) := by
    intro g
    obtain ⟨a, ha⟩ := central_orderOf_two_pow hO
      ((mem_center_subtype_iff hLC (g : ↥L)).mp g.2)
    refine ⟨a, ?_⟩
    have h1 := pow_orderOf_eq_one (((g : ↥L)) : X)
    rw [ha] at h1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  obtain ⟨e⟩ := nonempty_socle_equiv hLC
  have hZL : Subgroup.center ↥L = ⊥ :=
    E3S3M.center_eq_bot_of_psl2 hLq e.symm
      (Or.inl ⟨by decide, hmodel⟩ : CFSG.Blueprint.LieModel ↥(socleOf L) .PSL 2 p f) hp2 hq5 hZ2
      (x := ⟨z, hzL⟩) (Subtype.ext hz.sq)
      (fun h => hzn ((mem_center_subtype_iff hLC ⟨z, hzL⟩).mp h))
  rw [eq_bot_iff]
  intro c hc
  have hcL := hcenL c hc
  have hcc : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := (mem_center_subtype_iff hLC _).mpr hc
  rw [hZL, Subgroup.mem_bot] at hcc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hcc)

end Cit

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
