module

public import CFSG.Quasithin.Background.B6Basic
import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem mem_normalizer_of_normal {B : Subgroup X} (hB : B.Normal) (g : X) :
    g ∈ Subgroup.normalizer (B : Set X) := by
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top g

private theorem mem_normalizer_thompsonJ_of_conjSub_le {T : Subgroup X} {c : X}
    (h : B6.conjSub c (thompsonJ T) ≤ T) : c ∈ Subgroup.normalizer (thompsonJ T : Set X) := by
  have hdecomp : B6.conjSub c (thompsonJ T) =
      ⨆ (A : Subgroup X) (_ : IsMaxElemAbelian T A), B6.conjSub c A := by
    unfold thompsonJ
    simp only [OrderIso.map_iSup]
  have hle : B6.conjSub c (thompsonJ T) ≤ thompsonJ T := by
    rw [hdecomp]
    refine iSup₂_le fun A₀ hA₀ => ?_
    have hcT : B6.conjSub c A₀ ≤ T := ((B6.conjSub c).monotone (B6.le_thompsonJ hA₀)).trans h
    refine B6.le_thompsonJ ⟨hcT, B6.isElemAbelian_conjSub hA₀.2.1 c, fun B hBT hB => ?_⟩
    rw [B6.card_conjSub]
    exact hA₀.2.2 B hBT hB
  have heq : B6.conjSub c (thompsonJ T) = thompsonJ T :=
    Subgroup.eq_of_le_of_card_ge hle (B6.card_conjSub _ _).ge
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

theorem eq_mul_normalizer_thompsonJ_of_commutator_le {T : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    {A B : Subgroup X} (hB : B.Normal) (hBA : B ≤ A) (hcomm : ⁅A, thompsonJ T⁆ ≤ B) :
    ∀ a ∈ A, ∃ b ∈ B, ∃ n ∈ A ⊓ Subgroup.normalizer (thompsonJ T : Set X), a = b * n := by
  intro a ha
  set J : Subgroup X := thompsonJ T
  have hJT : J ≤ T := B6.thompsonJ_le T
  have hTH : T ≤ Subgroup.normalizer ((B ⊔ J : Subgroup X) : Set X) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_sup B J
      ⟨mem_normalizer_of_normal hB t, B6.le_normalizer_thompsonJ T ht⟩
  have hBH : B ≤ Subgroup.normalizer ((B ⊔ J : Subgroup X) : Set X) :=
    le_sup_left.trans Subgroup.le_normalizer
  have hTBsyl : IsSylowTwoOf T (T ⊔ B) := B6.isSylowTwoOf_mono hT le_sup_left le_top
  have hP : IsSylowTwoOf (T ⊓ (B ⊔ J)) (B ⊔ J) :=
    B6.isSylowTwoOf_inf_normal hTBsyl (sup_le le_sup_right (hJT.trans le_sup_left))
      (sup_le hTH hBH)
  have hJa : B6.conjSub a J ≤ B ⊔ J := by
    intro x hx
    rw [B6.mem_conjSub] at hx
    have hc : ⁅a, a⁻¹ * x * a⁆ ∈ B := Subgroup.commutator_le.mp hcomm a ha _ hx
    have hxe : x = ⁅a, a⁻¹ * x * a⁆ * (a⁻¹ * x * a) := by
      rw [commutatorElement_def]
      group
    rw [hxe]
    exact Subgroup.mul_mem_sup hc hx
  have hJ2 : IsPGroup 2 (B6.conjSub a J) := (hT.2.1.to_le hJT).map (MulAut.conj a).toMonoidHom
  obtain ⟨P', hP', hJaP'⟩ := B6.exists_isSylowTwoOf_ge hJ2 hJa
  obtain ⟨g, hg, hgP⟩ := B6.isSylowTwoOf_exists_conj hP hP'
  have hc : B6.conjSub (g⁻¹ * a) J ≤ T := by
    rw [B6.conjSub_mul]
    have h1 : B6.conjSub g⁻¹ (B6.conjSub a J) ≤ B6.conjSub g⁻¹ P' :=
      (B6.conjSub g⁻¹).monotone hJaP'
    have h2 : B6.conjSub g⁻¹ P' = T ⊓ (B ⊔ J) := by
      rw [hgP, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
    rw [h2] at h1
    exact h1.trans inf_le_left
  have hcN := mem_normalizer_thompsonJ_of_conjSub_le hc
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  refine ⟨y, hy, z * (g⁻¹ * a), ⟨?_, mul_mem (Subgroup.le_normalizer hz) hcN⟩, ?_⟩
  · have : z * (g⁻¹ * a) = y⁻¹ * a := by
      rw [← hyz]
      group
    rw [this]
    exact A.mul_mem (A.inv_mem (hBA hy)) ha
  · rw [← mul_assoc, ← hyz]
    group

private theorem frattini_of_normal_ge {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) {W : Subgroup X}
    (hW : W.Normal) (hJ : thompsonJ T ≤ W) (x : X) :
    ∃ w ∈ W, ∃ n ∈ Subgroup.normalizer (thompsonJ T : Set X), x = w * n := by
  have hWn : (⊤ : Subgroup X) ≤ Subgroup.normalizer (W : Set X) := fun g _ =>
    mem_normalizer_of_normal hW g
  have hsyl : IsSylowTwoOf (T ⊓ W) W := B6.isSylowTwoOf_inf_normal hT le_top hWn
  have hfr := B6.frattini_two (H := ⊤) le_top hWn hsyl
  have hx : x ∈ W ⊔ ((⊤ : Subgroup X) ⊓ Subgroup.normalizer ((T ⊓ W : Subgroup X) : Set X)) :=
    hfr (Subgroup.mem_top x)
  obtain ⟨w, hw, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  refine ⟨w, hw, n, ?_, rfl⟩
  have hJTW : thompsonJ T ≤ T ⊓ W := le_inf (B6.thompsonJ_le T) hJ
  have hEq : thompsonJ (T ⊓ W) = thompsonJ T := B6.thompsonJ_eq_of_le hJTW inf_le_left
  have := normalizer_le_normalizer_thompsonJ (T ⊓ W) hn.2
  rwa [hEq] at this

private def centralizerSection (A B : Subgroup X) (hB : B.Normal) : Subgroup X where
  carrier := {x | ∀ a ∈ A, ⁅x, a⁆ ∈ B}
  one_mem' a _ := by simp
  mul_mem' {x y} hx hy a ha := by
    have h : ⁅x * y, a⁆ = x * ⁅y, a⁆ * x⁻¹ * ⁅x, a⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact B.mul_mem (hB.conj_mem _ (hy a ha) x) (hx a ha)
  inv_mem' {x} hx a ha := by
    have h : ⁅x⁻¹, a⁆ = x⁻¹ * ⁅x, a⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact hB.conj_mem _ (B.inv_mem (hx a ha)) x⁻¹

omit [Finite X] in
private theorem centralizerSection_normal {A B : Subgroup X} (hA : A.Normal) (hB : B.Normal) :
    (centralizerSection A B hB).Normal where
  conj_mem n hn g a ha := by
    have h : ⁅g * n * g⁻¹, a⁆ = g * ⁅n, g⁻¹ * a * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    show ⁅g * n * g⁻¹, a⁆ ∈ B
    rw [h]
    exact hB.conj_mem _ (hn (g⁻¹ * a * g) (by simpa using hA.conj_mem a ha g⁻¹)) g

private def kPart (T : Subgroup X) : Subgroup X :=
  Subgroup.normalizer (thompsonJ T : Set X) ⊓
    Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set X)

omit [Finite X] in
private theorem kPart_le_normalizer (T : Subgroup X) :
    kPart T ≤ Subgroup.normalizer (thompsonJ T : Set X) := inf_le_left

omit [Finite X] in
private theorem normalizer_le_normalizer_kPart (T : Subgroup X) :
    Subgroup.normalizer (thompsonJ T : Set X) ≤ Subgroup.normalizer (kPart T : Set X) := by
  intro n hn
  have hNE : Subgroup.normalizer (thompsonJ T : Set X) ≤
      Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set X) :=
    normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv (thompsonJ T)
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hn, B6.le_normalizer_centralizer hNE hn⟩

omit [Finite X] in
private theorem inf_kPart_eq_baum (T : Subgroup X) : T ⊓ kPart T = baum T := by
  have hTN : T ≤ Subgroup.normalizer (thompsonJ T : Set X) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  ext x
  simp only [Subgroup.mem_inf, kPart, baum]
  constructor
  · rintro ⟨hxT, -, hxc⟩
    exact ⟨hxT, hxc⟩
  · rintro ⟨hxT, hxc⟩
    exact ⟨hxT, hTN hxT, hxc⟩

private theorem isSylowTwoOf_baum_kPart {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) :
    IsSylowTwoOf (baum T) (kPart T) := by
  have hTN : T ≤ Subgroup.normalizer (thompsonJ T : Set X) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  have hTsyl : IsSylowTwoOf T (Subgroup.normalizer (thompsonJ T : Set X)) :=
    B6.isSylowTwoOf_mono hT hTN le_top
  have := B6.isSylowTwoOf_inf_normal hTsyl (kPart_le_normalizer T)
    (normalizer_le_normalizer_kPart T)
  rwa [inf_kPart_eq_baum] at this

omit [Finite X] in
private theorem baum_le_kPart (T : Subgroup X) : baum T ≤ kPart T := by
  rw [← inf_kPart_eq_baum T]
  exact inf_le_right

omit [Finite X] in
private theorem normalizer_baum_le_normalizer {T T₂ : Subgroup X} (h2 : T₂ ≤ baum T)
    (h2c : (T₂.subgroupOf (baum T)).Characteristic) :
    Subgroup.normalizer (baum T : Set X) ≤ Subgroup.normalizer (T₂ : Set X) := by
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (T₂.subgroupOf (baum T))
  rwa [Subgroup.map_subgroupOf_eq_of_le h2] at h

private theorem omegaOneCenterOf_le_thompsonJ (T : Subgroup X) :
    omegaOneCenterOf T ≤ omegaOneCenterOf (thompsonJ T) := by
  rw [← (omegaOne_centralizer_thompsonJ T).1]
  refine (Subgroup.closure_le _).2 fun z hz => Subgroup.subset_closure ⟨⟨hz.1.1, ?_⟩, hz.2⟩
  exact Subgroup.centralizer_le (B6.thompsonJ_le T) hz.1.2

omit [Finite X] in
private theorem le_centralizer_of_le_omegaOneCenterOf {T T₁ : Subgroup X}
    (h1 : T₁ ≤ omegaOneCenterOf T) : T ≤ Subgroup.centralizer (T₁ : Set X) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyc : y ∈ centerOf T := (Subgroup.closure_le (centerOf T)).mpr (fun z hz => hz.1) (h1 hy)
  exact (Subgroup.mem_centralizer_iff.mp hyc.2 t ht).symm

private theorem le_sup_of_isTwoQuotient {A B D S : Subgroup X} (hB : B.Normal) (hBD : B ≤ D)
    (hDA : D ≤ A) (hAD : A ≤ Subgroup.normalizer (D : Set X))
    (h2 : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ B) (hS : IsSylowTwoOf S A) : D ≤ B ⊔ S := by
  have hSD : IsSylowTwoOf (S ⊓ D) D := B6.isSylowTwoOf_inf_normal hS hDA hAD
  have hsup : B ⊔ (S ⊓ D) = D :=
    B6.sup_eq_of_isTwoQuotient hBD (fun d _ => mem_normalizer_of_normal hB d) h2 hSD
  calc D = B ⊔ (S ⊓ D) := hsup.symm
    _ ≤ B ⊔ S := sup_le_sup_left inf_le_left B

private theorem le_sup_inf_centralizer_of_two_group {T T₁ : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    (h1 : T₁ ≤ omegaOneCenterOf T) {A B : Subgroup X} (hA : A.Normal) (hB : B.Normal)
    (hBA : B ≤ A) (h2 : ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B) :
    A ≤ B ⊔ (A ⊓ Subgroup.centralizer (T₁ : Set X)) := by
  have hS : IsSylowTwoOf (T ⊓ A) A :=
    B6.isSylowTwoOf_inf_normal hT le_top fun g _ => mem_normalizer_of_normal hA g
  have hsup : B ⊔ (T ⊓ A) = A :=
    B6.sup_eq_of_isTwoQuotient hBA (fun d _ => mem_normalizer_of_normal hB d) h2 hS
  have hTC := le_centralizer_of_le_omegaOneCenterOf h1
  calc A = B ⊔ (T ⊓ A) := hsup.symm
    _ ≤ B ⊔ (A ⊓ Subgroup.centralizer (T₁ : Set X)) :=
        sup_le_sup_left (fun x hx => ⟨hx.2, hTC hx.1⟩) B

private theorem commutator_thompsonJ_le_of_chief {T : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    {A B : Subgroup X} (hA : A.Normal) (hB : B.Normal) (hBA : B ≤ A)
    (hchief : ∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A)
    (hAN : A ≤ B ⊔ Subgroup.normalizer (thompsonJ T : Set X))
    (h2 : ¬ ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B) : ⁅A, thompsonJ T⁆ ≤ B := by
  set J : Subgroup X := thompsonJ T
  have hJ2 : IsPGroup 2 J := hT.2.1.to_le (B6.thompsonJ_le T)
  have hAH : A ≤ Subgroup.normalizer ((B ⊔ J : Subgroup X) : Set X) := by
    refine hAN.trans (sup_le (le_sup_left.trans Subgroup.le_normalizer) ?_)
    intro n hn
    exact Subgroup.inf_normalizer_le_normalizer_sup B J ⟨mem_normalizer_of_normal hB n, hn⟩
  set Q : Subgroup X := A ⊓ (B ⊔ J)
  have hAQ : A ≤ Subgroup.normalizer (Q : Set X) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ha, hAH ha⟩
  have hBQ : B ≤ Q := le_inf hBA le_sup_left
  have hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k ∈ B := fun q hq =>
    B6.isTwoQuotient_of_sup_eq hJ2 (fun d _ => mem_normalizer_of_normal hB d)
      (rfl : J ⊔ B = J ⊔ B) q (by rw [sup_comm]; exact hq.2)
  have hS₀ : IsSylowTwoOf (T ⊓ A) A :=
    B6.isSylowTwoOf_inf_normal hT le_top fun g _ => mem_normalizer_of_normal hA g
  have hQK : ∀ q ∈ Q, ∀ g : X, g * q * g⁻¹ ∈ B ⊔ (T ⊓ A) := by
    intro q hq g
    have hT' : IsSylowTwoOf (B6.conjSub g⁻¹ T) ⊤ := by
      have := B6.isSylowTwoOf_conjSub hT g⁻¹
      rwa [(B6.conjSub g⁻¹).map_top] at this
    have hS' : IsSylowTwoOf (B6.conjSub g⁻¹ T ⊓ A) A :=
      B6.isSylowTwoOf_inf_normal hT' le_top fun g _ => mem_normalizer_of_normal hA g
    have hQS : Q ≤ B ⊔ (B6.conjSub g⁻¹ T ⊓ A) :=
      le_sup_of_isTwoQuotient hB hBQ inf_le_left hAQ hQ2 hS'
    obtain ⟨b, hb, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hQS hq)
    have hs1 : g * s * g⁻¹ ∈ T ⊓ A := by
      refine ⟨?_, hA.conj_mem s hs.2 g⟩
      simpa using (B6.mem_conjSub).mp hs.1
    have hb1 : g * b * g⁻¹ ∈ B := hB.conj_mem b hb g
    have hgq : g * (b * s) * g⁻¹ = (g * b * g⁻¹) * (g * s * g⁻¹) := by group
    rw [hgq]
    exact Subgroup.mul_mem_sup hb1 hs1
  have hC₀n : (B ⊔ (T ⊓ A)).normalCore.Normal := Subgroup.normalCore_normal _
  have hBC₀ : B ≤ (B ⊔ (T ⊓ A)).normalCore := fun x hx g =>
    Subgroup.mem_sup_left (hB.conj_mem x hx g)
  have hC₀A : (B ⊔ (T ⊓ A)).normalCore ≤ A :=
    (Subgroup.normalCore_le _).trans (sup_le hBA inf_le_right)
  rcases hchief _ hC₀n hBC₀ hC₀A with h | h
  · have hQB : Q ≤ B := by
      rw [← h]
      exact fun q hq g => hQK q hq g
    rw [Subgroup.commutator_le]
    intro a ha j hj
    apply hQB
    have hrw : ⁅a, j⁆ = a * (j * a⁻¹ * j⁻¹) := by
      rw [commutatorElement_def]
      group
    refine ⟨?_, ?_⟩
    · rw [hrw]
      exact A.mul_mem ha (hA.conj_mem _ (A.inv_mem ha) j)
    · have haj : a * j * a⁻¹ ∈ B ⊔ J :=
        (Subgroup.mem_normalizer_iff.mp (hAH ha) j).mp (Subgroup.mem_sup_right hj)
      rw [commutatorElement_def]
      exact (B ⊔ J).mul_mem haj ((B ⊔ J).inv_mem (Subgroup.mem_sup_right hj))
  · exfalso
    apply h2
    have hAK : A ≤ B ⊔ (T ⊓ A) :=
      calc A = (B ⊔ (T ⊓ A)).normalCore := h.symm
        _ ≤ B ⊔ (T ⊓ A) := Subgroup.normalCore_le _
    exact B6.isTwoQuotient_of_sup_eq hS₀.2.1 (fun d _ => mem_normalizer_of_normal hB d)
      (le_antisymm (sup_le inf_le_right hBA) (by rw [sup_comm]; exact hAK))

private theorem exists_mul_normalizer_baum {T : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    {A B : Subgroup X} (hB : B.Normal) (hBA : B ≤ A) (hA : A.Normal)
    (hK : A ⊓ kPart T ≤ B) {a : X} (haA : a ∈ A)
    (haN : a ∈ Subgroup.normalizer (thompsonJ T : Set X)) :
    ∃ b ∈ B, ∃ n ∈ A ⊓ Subgroup.normalizer (baum T : Set X), a = b * n := by
  set K : Subgroup X := kPart T
  set S : Subgroup X := baum T
  have hSK : S ≤ K := baum_le_kPart T
  have haK : a ∈ Subgroup.normalizer (K : Set X) := normalizer_le_normalizer_kPart T haN
  have hcomm : ∀ s ∈ S, ⁅a, s⁆ ∈ B ⊓ K := by
    intro s hs
    have hsK : s ∈ K := hSK hs
    have h1 : a * s * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp haK s).mp hsK
    have hKm : ⁅a, s⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem h1 (K.inv_mem hsK)
    have hrw : ⁅a, s⁆ = a * (s * a⁻¹ * s⁻¹) := by
      rw [commutatorElement_def]
      group
    have hAm : ⁅a, s⁆ ∈ A := by
      rw [hrw]
      exact A.mul_mem haA (hA.conj_mem _ (A.inv_mem haA) s)
    exact ⟨hK ⟨hAm, hKm⟩, hKm⟩
  have hconjS : B6.conjSub a S ≤ (B ⊓ K) ⊔ S := by
    intro x hx
    rw [B6.mem_conjSub] at hx
    have hxe : x = ⁅a, a⁻¹ * x * a⁆ * (a⁻¹ * x * a) := by
      rw [commutatorElement_def]
      group
    rw [hxe]
    exact Subgroup.mul_mem_sup (hcomm _ hx) hx
  have hRK : (B ⊓ K) ⊔ S ≤ K := sup_le inf_le_right hSK
  have hSsyl : IsSylowTwoOf S K := isSylowTwoOf_baum_kPart hT
  have hSR : IsSylowTwoOf S ((B ⊓ K) ⊔ S) := B6.isSylowTwoOf_mono hSsyl le_sup_right hRK
  have hSaK : IsSylowTwoOf (B6.conjSub a S) K := by
    have := B6.isSylowTwoOf_conjSub hSsyl a
    rwa [B6.conjSub_eq_self haK] at this
  have hSaR : IsSylowTwoOf (B6.conjSub a S) ((B ⊓ K) ⊔ S) :=
    B6.isSylowTwoOf_mono hSaK hconjS hRK
  obtain ⟨r, hr, hrS⟩ := B6.isSylowTwoOf_exists_conj hSR hSaR
  have hKn : S ≤ Subgroup.normalizer ((B ⊓ K : Subgroup X) : Set X) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨mem_normalizer_of_normal hB s, Subgroup.le_normalizer (hSK hs)⟩
  have hr' : r ∈ ((B ⊓ K) ⊔ S : Subgroup X) := hr
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (B ⊓ K) S hKn] at hr'
  obtain ⟨u, hu, s₀, hs₀, hur⟩ := hr'
  have hur' : u * s₀ = r := hur
  have hra : r⁻¹ * a ∈ Subgroup.normalizer (S : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show B6.conjSub (r⁻¹ * a) S = S
    rw [B6.conjSub_mul, hrS, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  refine ⟨u, hu.1, s₀ * (r⁻¹ * a), ⟨?_, mul_mem (Subgroup.le_normalizer hs₀) hra⟩, ?_⟩
  · have : s₀ * (r⁻¹ * a) = u⁻¹ * a := by
      rw [← hur']
      group
    rw [this]
    exact A.mul_mem (A.inv_mem (hBA hu.1)) haA
  · rw [← mul_assoc, hur']
    group

theorem cover_of_chief_factor_normalizer {T T₁ T₂ : Subgroup X} (hT : IsSylowTwoOf T ⊤)
    (h1 : T₁ ≤ omegaOneCenterOf T) (h2 : T₂ ≤ baum T)
    (h2c : (T₂.subgroupOf (baum T)).Characteristic) {A B : Subgroup X} (hA : A.Normal)
    (hB : B.Normal) (hBA : B ≤ A)
    (hchief : ∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A)
    (hAN : A ≤ B ⊔ Subgroup.normalizer (thompsonJ T : Set X)) :
    A ≤ B ⊔ (A ⊓ Subgroup.centralizer (T₁ : Set X)) ∨
      A ≤ B ⊔ (A ⊓ Subgroup.normalizer (T₂ : Set X)) := by
  by_cases h2grp : ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B
  · exact Or.inl (le_sup_inf_centralizer_of_two_group hT h1 hA hB hBA h2grp)
  have hcomm := commutator_thompsonJ_le_of_chief hT hA hB hBA hchief hAN h2grp
  set N : Subgroup X := Subgroup.normalizer (thompsonJ T : Set X)
  set K : Subgroup X := kPart T
  have hJW : thompsonJ T ≤ centralizerSection A B hB := fun j hj a ha => by
    have := Subgroup.commutator_le.mp hcomm a ha j hj
    rw [← commutatorElement_inv]
    exact B.inv_mem this
  have hW := centralizerSection_normal hA hB
  have hNn : N ≤ Subgroup.normalizer ((B ⊔ (A ⊓ K) : Subgroup X) : Set X) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_sup B (A ⊓ K)
      ⟨mem_normalizer_of_normal hB n, Subgroup.inf_normalizer_le_normalizer_inf
        ⟨mem_normalizer_of_normal hA n, normalizer_le_normalizer_kPart T hn⟩⟩
  have hWc : ∀ w ∈ centralizerSection A B hB, ∀ y ∈ B ⊔ (A ⊓ K), w * y * w⁻¹ ∈ B ⊔ (A ⊓ K) := by
    intro w hw y hy
    obtain ⟨b, hb, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    have hbk : w * (b * k) * w⁻¹ = ((w * b * w⁻¹) * ⁅w, k⁆) * k := by
      rw [commutatorElement_def]
      group
    rw [hbk]
    exact Subgroup.mul_mem_sup (B.mul_mem (hB.conj_mem b hb w) (hw k hk.1)) hk
  have hWn : centralizerSection A B hB ≤ Subgroup.normalizer ((B ⊔ (A ⊓ K) : Subgroup X) : Set X) :=
    fun w hw => B6.mem_normalizer_of_forall_mem (hWc w hw) fun y hy => by
      simpa using hWc w⁻¹ ((centralizerSection A B hB).inv_mem hw) y hy
  have hBKn : (B ⊔ (A ⊓ K)).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro x _
    obtain ⟨w, hw, n, hn, rfl⟩ := frattini_of_normal_ge hT hW hJW x
    exact mul_mem (hWn hw) (hNn hn)
  rcases hchief _ hBKn le_sup_left (sup_le hBA inf_le_left) with h | h
  ·
    right
    have hKB : A ⊓ K ≤ B := le_sup_right.trans h.le
    intro a ha
    obtain ⟨b, hb, a', ha', rfl⟩ :=
      eq_mul_normalizer_thompsonJ_of_commutator_le hT hB hBA hcomm a ha
    obtain ⟨u, hu, n'', hn'', rfl⟩ := exists_mul_normalizer_baum hT hB hBA hA hKB ha'.1 ha'.2
    rw [← mul_assoc]
    exact Subgroup.mul_mem_sup (B.mul_mem hb hu)
      ⟨hn''.1, normalizer_baum_le_normalizer h2 h2c hn''.2⟩
  ·
    left
    have hT₁E : (T₁ : Set X) ⊆ (omegaOneCenterOf (thompsonJ T) : Set X) :=
      fun x hx => omegaOneCenterOf_le_thompsonJ T (h1 hx)
    calc A = B ⊔ (A ⊓ K) := h.symm
      _ ≤ B ⊔ (A ⊓ Subgroup.centralizer (T₁ : Set X)) :=
          sup_le_sup_left (inf_le_inf_left A (inf_le_right.trans
            (Subgroup.centralizer_le hT₁E))) B

theorem climb_of_chief_factor_step {P : Subgroup X → Prop} {N : Subgroup X}
    (hstep : ∀ A B : Subgroup X, A.Normal → B.Normal → B ≤ A →
      (∀ D : Subgroup X, D.Normal → B ≤ D → D ≤ A → D = B ∨ D = A) → A ≤ B ⊔ N → P B → P A)
    {H : Subgroup X} (hH : H.Normal) (hPH : P H) :
    ∀ Q : Subgroup X, Q.Normal → H ≤ Q → Q ≤ H ⊔ N → P Q := by
  intro Q
  induction Q using WellFoundedLT.induction with
  | _ Q ih =>
    intro hQ hHQ hQN
    rcases eq_or_lt_of_le hHQ with h | hlt
    · exact h ▸ hPH
    · obtain ⟨D, hHD, hmax⟩ :=
        (Set.toFinite {K : Subgroup X | K.Normal ∧ H ≤ K ∧ K < Q}).exists_le_maximal
          ⟨hH, le_rfl, hlt⟩
      obtain ⟨hDn, -, hDQ⟩ := hmax.1
      have hchief : ∀ E : Subgroup X, E.Normal → D ≤ E → E ≤ Q → E = D ∨ E = Q := by
        intro E hE hDE hEQ
        by_cases hEQ' : E = Q
        · exact Or.inr hEQ'
        · exact Or.inl (le_antisymm (hmax.2 ⟨hE, hHD.trans hDE, lt_of_le_of_ne hEQ hEQ'⟩ hDE) hDE)
      have hPD : P D := ih D hDQ hDn hHD (hDQ.le.trans hQN)
      exact hstep Q D hQ hDn hDQ.le hchief (hQN.trans (sup_le_sup_right hHD N)) hPD

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
