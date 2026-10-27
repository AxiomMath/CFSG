module

public import CFSG.CGT.PushingUpLit.CGT6.EmbLift
import CFSG.CGT.PushingUpLit.CGT6.EmbThompson
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltEnd

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

section Group

private theorem cbl_comm_mul_central {Γ : Type*} [Group Γ] {y₁ y₂ z₁ z₂ : Γ}
    (h₁ : z₁ ∈ Subgroup.center Γ) (h₂ : z₂ ∈ Subgroup.center Γ) :
    ⁅y₁ * z₁, y₂ * z₂⁆ = ⁅y₁, y₂⁆ := by
  have c1 : ∀ g : Γ, ⁅z₁, g⁆ = 1 := fun g =>
    (show Commute z₁ g from (Subgroup.mem_center_iff.mp h₁ g).symm).commutator_eq
  have c2 : ∀ g : Γ, ⁅g, z₂⁆ = 1 := fun g =>
    (show Commute g z₂ from Subgroup.mem_center_iff.mp h₂ g).commutator_eq
  rw [commutatorElement_mul_left_eq_conj_mul, c1, commutatorElement_mul_right_eq_mul_conj, c2]
  simp

private theorem cbl_eq_top_of_central {Γ : Type*} [Group Γ] [Group.IsPerfect Γ]
    {N P : Subgroup Γ} (hP : P ≤ Subgroup.center Γ) (hNP : ∀ x : Γ, ∃ y ∈ N, y⁻¹ * x ∈ P) :
    N = ⊤ := by
  rw [eq_top_iff, ← Group.isPerfect_def.mp ‹Group.IsPerfect Γ›]
  refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
  obtain ⟨y₁, hy₁, hz₁⟩ := hNP g₁
  obtain ⟨y₂, hy₂, hz₂⟩ := hNP g₂
  have e1 : g₁ = y₁ * (y₁⁻¹ * g₁) := by simp
  have e2 : g₂ = y₂ * (y₂⁻¹ * g₂) := by simp
  rw [e1, e2, cbl_comm_mul_central (hP hz₁) (hP hz₂), commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hy₁ hy₂) (inv_mem hy₁)) (inv_mem hy₂)

private theorem cbl_exists_order_two {Γ : Type*} [Group Γ] [Finite Γ]
    (hP : CFSG.pCore 2 Γ ≠ ⊥) : ∃ q : Γ, q ∈ CFSG.pCore 2 Γ ∧ orderOf q = 2 := by
  have hp : IsPGroup 2 ↥(CFSG.pCore 2 Γ) := pCore_isPGroup
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hP (Subgroup.card_eq_one.mp (by simpa using hk))
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CFSG.pCore 2 Γ)) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  exact ⟨q, q.2, by rw [Subgroup.orderOf_coe]; exact hq⟩

end Group

section Perm

private theorem cbl_card_eq {m n : ℕ} (hm : 7 ≤ m) {F : Finset (Fin n)}
    (e : alternatingGroup (Fin m) ≃* altStabilizer n F) : m + F.card = n := by
  have hF : F.card ≤ n := by
    simpa using Finset.card_le_univ F
  have e' : alternatingGroup (Fin m) ≃* alternatingGroup (Fin (n - F.card)) :=
    e.trans (altStabilizerEquiv F)
  have hnt : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  by_cases hk : 2 ≤ n - F.card
  · have hnt' : Nontrivial (Fin (n - F.card)) := Fin.nontrivial_iff_two_le.mpr hk
    have h1 := Nat.card_congr e'.toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin] at h1
    have h2m : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h2k : 2 ∣ (n - F.card).factorial := Nat.dvd_factorial (by norm_num) hk
    have h3 : m.factorial = (n - F.card).factorial := by omega
    have := (Nat.factorial_inj (by omega)).mp h3
    omega
  · exfalso
    have hs : Subsingleton (Fin (n - F.card)) :=
      Fin.subsingleton_iff_le_one.mpr (by omega)
    have : Subsingleton (alternatingGroup (Fin (n - F.card))) := inferInstance
    have : Subsingleton (alternatingGroup (Fin m)) := e'.injective.subsingleton
    have : Nontrivial (alternatingGroup (Fin m)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
    exact not_subsingleton _ ‹_›

private theorem cbl_comm_swap {n : ℕ} {σ : Equiv.Perm (Fin n)} {a b : Fin n} (ha : σ a = a)
    (hb : σ b = b) : σ * Equiv.swap a b = Equiv.swap a b * σ := by
  have h := Equiv.swap_apply_apply σ a b
  rw [ha, hb] at h
  calc σ * Equiv.swap a b = (σ * Equiv.swap a b * σ⁻¹) * σ := by group
    _ = Equiv.swap a b * σ := by rw [← h]

private theorem cbl_sign {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  rfl

private theorem cbl_klein4 {n : ℕ} {f₁ f₂ f₃ f₄ : Fin n} (h12 : f₁ ≠ f₂) (h13 : f₁ ≠ f₃)
    (h14 : f₁ ≠ f₄) (h23 : f₂ ≠ f₃) (h24 : f₂ ≠ f₄) (h34 : f₃ ≠ f₄) :
    ∃ σ₁ σ₂ : alternatingGroup (Fin n), σ₁ ^ 2 = 1 ∧ σ₂ ^ 2 = 1 ∧ σ₁ ≠ 1 ∧ σ₂ ≠ 1 ∧
      σ₁ ≠ σ₂ ∧ σ₁ * σ₂ = σ₂ * σ₁ ∧ ∀ τ : alternatingGroup (Fin n),
        (τ : Perm (Fin n)) f₁ = f₁ → (τ : Perm (Fin n)) f₂ = f₂ → (τ : Perm (Fin n)) f₃ = f₃ →
        (τ : Perm (Fin n)) f₄ = f₄ → τ * σ₁ = σ₁ * τ ∧ τ * σ₂ = σ₂ * τ := by
  have s1 : (swap f₁ f₂ * swap f₃ f₄) * (swap f₁ f₂ * swap f₃ f₄) = 1 := by
    ext x
    simp only [Perm.mul_apply, swap_apply_def, Perm.coe_one, id_eq]
    grind
  have s2 : (swap f₁ f₃ * swap f₂ f₄) * (swap f₁ f₃ * swap f₂ f₄) = 1 := by
    ext x
    simp only [Perm.mul_apply, swap_apply_def, Perm.coe_one, id_eq]
    grind
  have s3 : (swap f₁ f₂ * swap f₃ f₄) * (swap f₁ f₃ * swap f₂ f₄) =
      (swap f₁ f₃ * swap f₂ f₄) * (swap f₁ f₂ * swap f₃ f₄) := by
    ext x
    simp only [Perm.mul_apply, swap_apply_def]
    grind
  have s4 : (swap f₁ f₂ * swap f₃ f₄) ≠ 1 := fun h => by
    have := congrArg (fun f : Perm (Fin n) => f f₁) h
    simp only [Perm.mul_apply, swap_apply_def, Perm.coe_one, id_eq] at this
    grind
  have s5 : (swap f₁ f₃ * swap f₂ f₄) ≠ 1 := fun h => by
    have := congrArg (fun f : Perm (Fin n) => f f₁) h
    simp only [Perm.mul_apply, swap_apply_def, Perm.coe_one, id_eq] at this
    grind
  have s6 : (swap f₁ f₂ * swap f₃ f₄) ≠ (swap f₁ f₃ * swap f₂ f₄) := fun h => by
    have := congrArg (fun f : Perm (Fin n) => f f₁) h
    simp only [Perm.mul_apply, swap_apply_def] at this
    grind
  refine ⟨⟨swap f₁ f₂ * swap f₃ f₄, cbl_sign h12 h34⟩, ⟨swap f₁ f₃ * swap f₂ f₄, cbl_sign h13 h24⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (by simpa [pow_two] using s1)
  · exact Subtype.ext (by simpa [pow_two] using s2)
  · exact fun h => s4 (congrArg Subtype.val h)
  · exact fun h => s5 (congrArg Subtype.val h)
  · exact fun h => s6 (congrArg Subtype.val h)
  · exact Subtype.ext s3
  · intro τ h1 h2 h3 h4
    constructor
    · apply Subtype.ext
      show (τ : Perm (Fin n)) * (swap f₁ f₂ * swap f₃ f₄) = (swap f₁ f₂ * swap f₃ f₄) * τ
      rw [← mul_assoc, cbl_comm_swap h1 h2, mul_assoc, cbl_comm_swap h3 h4, mul_assoc]
    · apply Subtype.ext
      show (τ : Perm (Fin n)) * (swap f₁ f₃ * swap f₂ f₄) = (swap f₁ f₃ * swap f₂ f₄) * τ
      rw [← mul_assoc, cbl_comm_swap h1 h3, mul_assoc, cbl_comm_swap h2 h4, mul_assoc]

private theorem cbl_klein {n : ℕ} {F : Finset (Fin n)} (hF : 4 ≤ F.card) :
    ∃ σ₁ σ₂ : alternatingGroup (Fin n), σ₁ ^ 2 = 1 ∧ σ₂ ^ 2 = 1 ∧ σ₁ ≠ 1 ∧ σ₂ ≠ 1 ∧
      σ₁ ≠ σ₂ ∧ σ₁ * σ₂ = σ₂ * σ₁ ∧
      ∀ τ ∈ altStabilizer n F, τ * σ₁ = σ₁ * τ ∧ τ * σ₂ = σ₂ * τ := by
  obtain ⟨f₁, hf₁, f₂, hf₂, f₃, hf₃, h12, h13, h23⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < F.card)
  obtain ⟨f₄, hf₄, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {f₁, f₂, f₃}) (t := F)
    (lt_of_le_of_lt Finset.card_le_three (show 3 < F.card by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  obtain ⟨σ₁, σ₂, hσ1, hσ2, hσ1n, hσ2n, hσ12, hσc, hcomm⟩ :=
    cbl_klein4 h12 h13 (Ne.symm hn.1) h23 (Ne.symm hn.2.1) (Ne.symm hn.2.2)
  refine ⟨σ₁, σ₂, hσ1, hσ2, hσ1n, hσ2n, hσ12, hσc, fun τ hτ => ?_⟩
  rw [mem_altStabilizer_iff] at hτ
  exact hcomm τ (hτ _ hf₁) (hτ _ hf₂) (hτ _ hf₃) (hτ _ hf₄)

end Perm

section Lift

private theorem cbl_pCore_eq_bot {G T Y : Subgroup (MulAut V)} (h : EndCfg4 G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (hXG : X ≤ G) (hYX : Y ≤ X)
    (hperf : ⁅X, X⁆ = X) (hshort : IsShortGroup ↥(yuHol X)) (hY2 : ¬ IsPGroup 2 ↥Y)
    (hXY : X ≠ Y) (hsimple : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X)) :
    CFSG.pCore 2 ↥X = ⊥ := by
  by_contra hP
  have hPc : CFSG.pCore 2 ↥X ≤ Subgroup.center ↥X := pCore_le_center_of_inClassX hV hperf hshort
  obtain ⟨q, hqP, hq2⟩ := cbl_exists_order_two hP
  have hqc : q ∈ Subgroup.center ↥X := hPc hqP
  have hqcomm : ∀ x ∈ X, x * (q : MulAut V) = (q : MulAut V) * x := fun x hx =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hqc ⟨x, hx⟩)
  have hq1 : (q : MulAut V) ≠ 1 := fun h1 => by
    have : q = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hq2
    omega
  have hqsq : (q : MulAut V) ^ 2 = 1 := by
    have : q ^ 2 = 1 := by rw [← hq2]; exact pow_orderOf_eq_one q
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hqY : (q : MulAut V) ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) :=
    ⟨hXG q.2, Subgroup.mem_centralizer_iff.mpr fun y hy => hqcomm y (hYX hy)⟩
  have hsubn : (Y.subgroupOf X).IsSubnormal := by
    refine CFSG.GroupTheory.isSubnormal_subgroupOf_of_le ?_ (h.cent _ hqY hq1 hqsq)
    exact le_inf hXG fun x hx => Subgroup.mem_centralizer_iff.mpr fun s hs => by
      rw [Set.mem_singleton_iff.mp hs]
      exact (hqcomm x hx).symm
  have hsub' := hsubn.map (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X))
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimple hsub' with hbot | htop
  · apply hY2
    intro y
    have hy : (⟨(y : MulAut V), hYX y.2⟩ : ↥X) ∈ Y.subgroupOf X := y.2
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨(y : MulAut V), hYX y.2⟩ ∈
        (Y.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := ⟨_, hy, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨(y : MulAut V), hYX y.2⟩ : ↥X) ∈ CFSG.pCore 2 ↥X :=
      (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := ↥X)) ⟨_, h2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥X) => ((z : ↥X) : MulAut V)) hk
    simpa using this
  · have : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hperf
    have hN := cbl_eq_top_of_central hPc (N := Y.subgroupOf X) fun x => by
      have hx : QuotientGroup.mk' (CFSG.pCore 2 ↥X) x ∈
          (Y.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := by
        rw [htop]
        trivial
      obtain ⟨y, hy, hyx⟩ := hx
      exact ⟨y, hy, (QuotientGroup.eq).mp hyx⟩
    apply hXY
    refine le_antisymm (fun x hx => ?_) hYX
    have : (⟨x, hx⟩ : ↥X) ∈ Y.subgroupOf X := by
      rw [hN]
      trivial
    exact this

omit [Finite V] in
private theorem cbl_centralizes {X Y : Subgroup (MulAut V)} {n : ℕ} (hYX : Y ≤ X)
    (ψ : ↥X ≃* alternatingGroup (Fin n)) {F : Finset (Fin n)}
    (himg : (Y.subgroupOf X).map ψ.toMonoidHom = altStabilizer n F)
    {σ : alternatingGroup (Fin n)} (hσ : ∀ τ ∈ altStabilizer n F, τ * σ = σ * τ) :
    ((ψ.symm σ : ↥X) : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hτ : ψ ⟨y, hYX hy⟩ ∈ altStabilizer n F := by
    rw [← himg]
    exact ⟨⟨y, hYX hy⟩, hy, rfl⟩
  have h3 : (⟨y, hYX hy⟩ : ↥X) * ψ.symm σ = ψ.symm σ * ⟨y, hYX hy⟩ := by
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hσ _ hτ
  exact congrArg Subtype.val h3

private theorem cbl_card_two {G T Y : Subgroup (MulAut V)} (h2 : Alt2Rank1) (h : EndCfg4 G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m)
    (ε : ↥Y ≃* alternatingGroup (Fin m)) {X : Subgroup (MulAut V)} (hXG : X ≤ G) (hYX : Y ≤ X)
    (hXY : X ≠ Y) {n : ℕ} (hn : Odd n) (ψ : ↥X ≃* alternatingGroup (Fin n))
    {F : Finset (Fin n)} (himg : (Y.subgroupOf X).map ψ.toMonoidHom = altStabilizer n F) :
    F.card = 2 ∧ n = m + 2 := by
  have e1 : ↥Y ≃* ↥(altStabilizer n F) :=
    ((Subgroup.subgroupOfEquivOfLe hYX).symm.trans
      (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective)).trans
      (MulEquiv.subgroupCongr himg)
  have hmF : m + F.card = n := cbl_card_eq hm (ε.symm.trans e1)
  have hF0 : F.card ≠ 0 := by
    intro h0
    apply hXY
    have hF : F = ∅ := Finset.card_eq_zero.mp h0
    have h1 : (Y.subgroupOf X).map ψ.toMonoidHom = ⊤ := by
      rw [himg, hF]
      ext σ
      simp [mem_altStabilizer_iff]
    refine le_antisymm (fun x hx => ?_) hYX
    have hx1 : ψ ⟨x, hx⟩ ∈ (Y.subgroupOf X).map ψ.toMonoidHom := by
      rw [h1]
      trivial
    obtain ⟨y, hy, hyx⟩ := hx1
    have : y = ⟨x, hx⟩ := ψ.injective hyx
    subst this
    exact hy
  have hF4 : F.card < 4 := by
    by_contra hF4
    obtain ⟨σ₁, σ₂, hσ1, hσ2, hσ1n, hσ2n, hσ12, hσc, hcomm⟩ := cbl_klein (not_lt.mp hF4)
    refine h2 V hV G T Y h m hm hodd ⟨ε⟩ ((ψ.symm σ₁ : ↥X) : MulAut V)
      ((ψ.symm σ₂ : ↥X) : MulAut V) (hXG (ψ.symm σ₁).2) (hXG (ψ.symm σ₂).2)
      (cbl_centralizes hYX ψ himg fun τ hτ => (hcomm τ hτ).1)
      (cbl_centralizes hYX ψ himg fun τ hτ => (hcomm τ hτ).2) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← Subgroup.coe_pow, ← map_pow, hσ1, map_one, Subgroup.coe_one]
    · rw [← Subgroup.coe_pow, ← map_pow, hσ2, map_one, Subgroup.coe_one]
    · intro h1
      have h3 : ψ.symm σ₁ = 1 := Subtype.ext h1
      exact hσ1n (by simpa using congrArg ψ h3)
    · intro h1
      have h3 : ψ.symm σ₂ = 1 := Subtype.ext h1
      exact hσ2n (by simpa using congrArg ψ h3)
    · intro h1
      exact hσ12 (ψ.symm.injective (Subtype.ext h1))
    · have := congrArg (fun z : alternatingGroup (Fin n) => ((ψ.symm z : ↥X) : MulAut V)) hσc
      simpa using this
  have hm2 := Nat.odd_iff.mp hodd
  have hn2 := Nat.odd_iff.mp hn
  omega

end Lift

theorem EndCfg4.lift_alt {G T Y : Subgroup (MulAut V)} (h2 : Alt2Rank1) (h : EndCfg4 G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m)
    {H X : Subgroup (MulAut V)} (hHG : H ≤ G) (hX : Lift4 H Y X) :
    Y ≤ X ∧ X ≤ H ∧ (X.subgroupOf H).IsSubnormal ∧
      (X = Y ∨ ∃ (θ : ↥X ≃* alternatingGroup (Fin (m + 2))) (a b : Fin (m + 2)), a ≠ b ∧
        (Y.subgroupOf X).map θ.toMonoidHom = altStabilizer (m + 2) {a, b} ∧
        IsNatSectionWith (altAct (m + 2)) θ (commV X) ⊥) := by
  classical
  have hX' := hX
  obtain ⟨hYX, hXH, hsub, hcases⟩ := hX
  refine ⟨hYX, hXH, hsub, ?_⟩
  by_cases hXY : X = Y
  · exact Or.inl hXY
  refine Or.inr ?_
  have hXG : X ≤ G := hXH.trans hHG
  have hY2 : ¬ IsPGroup 2 ↥Y := h.adm.hcls.not_isPGroup hV
  obtain ⟨ε⟩ := hY
  rcases hcases with ⟨hXcls, harr⟩ | ⟨n, hn, -, hYeq | ⟨-, ⟨eSL⟩, -⟩⟩
  ·
    have hperfX : ⁅X, X⁆ = X := Lift4.commutator_eq_self hV h.adm.hperf h.adm.hcls hX'
    have hsimTop := (arrowNat_top_simple_of_perfect hV hY2 hperfX (Ne.symm hXY) harr).1
    have hsimple : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X) := (yuTop X hV).symm.isSimpleGroup
    have h0 := cbl_pCore_eq_bot h hV hXG hYX hperfX hXcls.1 hY2 hXY hsimple
    rcases harr with heq | ⟨a, b, φ, F, -, -, -, -, -, himg⟩
    · exact absurd (yuHol_inj heq).symm hXY
    let ψ : ↥X ≃* alternatingGroup (Fin (2 * a + 1)) := (yuTop' X hV h0).symm.trans φ
    have himg' : (Y.subgroupOf X).map ψ.toMonoidHom = altStabilizer (2 * a + 1) F := by
      rw [← himg, ← yuTop'_image X hV h0 Y, Subgroup.map_map]
      congr 1
      ext x
      simp [ψ]
    obtain ⟨hF2, han⟩ := cbl_card_two h2 h hV hm hodd ε hXG hYX hXY ⟨a, rfl⟩ ψ himg'
    obtain ⟨c, rfl⟩ := hodd
    obtain rfl : a = c + 1 := by omega
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hF2
    obtain ⟨θ', hθ'⟩ := natSection_of_classX_alt hV hperfX hXcls (by omega) ⟨c + 1, by ring⟩ ⟨ψ⟩
    exact ⟨ψ, p, q, hpq, himg', isNatSectionWith_of_equiv (by omega) (by omega) θ' ψ hθ'⟩
  · exact absurd hYeq.symm hXY
  · exfalso
    have h1 : Nat.card ↥Y = 2 ^ n * (2 ^ (2 * n) - 1) := by
      rw [Nat.card_congr eSL.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        GaloisField.card 2 n (by omega), ← pow_mul, mul_comm n 2]
    exact card_alt_ne_card_sl2 hm hn ((Nat.card_congr ε.toEquiv).symm.trans h1)

end CFSG.CGT.PushingUpLit.CGT6
