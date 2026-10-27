module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellThompson
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAut
public import CFSG.Quasithin.Background.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG.Quasithin CFSG.Quasithin.BlueprintB2

section Elem

variable {G : Type*} [Group G]

theorem isElemAbelian_iff {A : Subgroup G} :
    CFSG.Open.IsElemAbelian 2 A ↔ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ 2 = 1 := by
  constructor
  · rintro ⟨hc, hp⟩
    exact ⟨fun a ha b hb => congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩), hp⟩
  · rintro ⟨hc, hp⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hp⟩

theorem isElemAbelian_mono {A B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 2 B) (h : A ≤ B) :
    CFSG.Open.IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono hB h

theorem isElemAbelian_bot : CFSG.Open.IsElemAbelian 2 (⊥ : Subgroup G) :=
  CFSG.Open.isElemAbelian_bot _

theorem isElemAbelian_zpowers {x : G} (hx : x ^ 2 = 1) :
    CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem isElemAbelian_sup {A B : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A)
    (hB : CFSG.Open.IsElemAbelian 2 B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    CFSG.Open.IsElemAbelian 2 (A ⊔ B : Subgroup G) := by
  have hA' : CFSG.IsElementaryAbelian 2 A := isElementaryAbelian_iff.mpr (isElemAbelian_iff.mp hA)
  have hB' : CFSG.IsElementaryAbelian 2 B := isElementaryAbelian_iff.mpr (isElemAbelian_iff.mp hB)
  have hle : B ≤ Subgroup.centralizer (A : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb
  exact isElemAbelian_iff.mpr (isElementaryAbelian_iff.mp
    (isElementaryAbelian_sup_of_le_centralizer hA' hB' hle))

theorem isElemAbelian_map {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) {H : Type*} [Group H]
    (f : G →* H) : CFSG.Open.IsElemAbelian 2 (A.map f) := CFSG.Open.IsElemAbelian.map hA _

theorem maxElem_card_le {H A B : Subgroup G} (hA : IsMaxElemAbelian H A) (hBH : B ≤ H)
    (hB : CFSG.Open.IsElemAbelian 2 B) : Nat.card B ≤ Nat.card A := hA.2.2 B hBH hB

theorem maxElem_card_eq [Finite G] {H A A' : Subgroup G} (hA : IsMaxElemAbelian H A)
    (hA' : IsMaxElemAbelian H A') : Nat.card A = Nat.card A' :=
  le_antisymm (maxElem_card_le hA' hA.1 hA.2.1) (maxElem_card_le hA hA'.1 hA'.2.1)

theorem maxElem_mem_of_centralizer [Finite G] {H A : Subgroup G}
    (hA : IsMaxElemAbelian H A) {x : G} (hxH : x ∈ H) (hxc : x ∈ Subgroup.centralizer (A : Set G))
    (hx2 : x ^ 2 = 1) : x ∈ A := by
  have hB : CFSG.Open.IsElemAbelian 2 (A ⊔ Subgroup.zpowers x : Subgroup G) :=
    isElemAbelian_sup hA.2.1 (isElemAbelian_zpowers hx2) fun a ha b hb => by
      obtain ⟨m, rfl⟩ := hb
      have h1 : Commute a x := Subgroup.mem_centralizer_iff.mp hxc a ha
      exact (h1.zpow_right m).eq
  have hle : A ⊔ Subgroup.zpowers x ≤ H := sup_le hA.1 (Subgroup.zpowers_le.mpr hxH)
  have hcard := maxElem_card_le hA hle hB
  have heq : A = A ⊔ Subgroup.zpowers x := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem card_sup_mul_card_inf [Finite G] {L R : Subgroup G} (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup G) * Nat.card (L ⊓ R : Subgroup G) = Nat.card L * Nat.card R :=
  (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L R hc).1

theorem maxElem_inf_centralizer_eq [Finite G] {H A V : Subgroup G}
    (hA : IsMaxElemAbelian H A) (hVH : V ≤ H) (hV : CFSG.Open.IsElemAbelian 2 V) :
    V ⊓ Subgroup.centralizer (A : Set G) = A ⊓ V := by
  apply le_antisymm
  · rintro c ⟨hcV, hcA⟩
    exact ⟨maxElem_mem_of_centralizer hA (hVH hcV) hcA ((isElemAbelian_iff.mp hV).2 c hcV), hcV⟩
  · rintro c ⟨hcA, hcV⟩
    exact ⟨hcV, Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (isElemAbelian_iff.mp hA.2.1).1 a ha c hcA⟩

theorem action_inequality [Finite G] {H A V : Subgroup G} (hA : IsMaxElemAbelian H A)
    (hVH : V ≤ H) (hV : CFSG.Open.IsElemAbelian 2 V) :
    V ⊓ Subgroup.centralizer (A : Set G) = A ⊓ V ∧
      Nat.card V * Nat.card (A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) ≤
        Nat.card A * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  have hVA := maxElem_inf_centralizer_eq hA hVH hV
  refine ⟨hVA, ?_⟩
  set C : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G) with hC
  have hCA : C ≤ A := inf_le_left
  have hCel : CFSG.Open.IsElemAbelian 2 C := isElemAbelian_mono hA.2.1 hCA
  have hVC : ∀ v ∈ V, ∀ c ∈ C, v * c = c * v := fun v hv c hc =>
    Subgroup.mem_centralizer_iff.mp hc.2 v hv
  have hW : CFSG.Open.IsElemAbelian 2 (V ⊔ C : Subgroup G) := isElemAbelian_sup hV hCel hVC
  have hWH : V ⊔ C ≤ H := sup_le hVH (hCA.trans hA.1)
  have hWA : Nat.card (V ⊔ C : Subgroup G) ≤ Nat.card A := maxElem_card_le hA hWH hW
  have hprod := card_sup_mul_card_inf hVC
  have h5 : V ⊓ C = A ⊓ V := by
    ext x
    constructor
    · rintro ⟨hxV, hxA, -⟩
      exact ⟨hxA, hxV⟩
    · rintro ⟨hxA, hxV⟩
      refine ⟨hxV, hxA, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      exact (isElemAbelian_iff.mp hV).1 v hv x hxV
  rw [h5] at hprod
  rw [hVA]
  calc Nat.card V * Nat.card C = Nat.card (V ⊔ C : Subgroup G) * Nat.card (A ⊓ V : Subgroup G) :=
        hprod.symm
    _ ≤ Nat.card A * Nat.card (A ⊓ V : Subgroup G) := Nat.mul_le_mul_right _ hWA

theorem isElemAbelian_cj {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) (g : G) :
    CFSG.Open.IsElemAbelian 2 (cj A g) := by
  obtain ⟨hc, hp⟩ := isElemAbelian_iff.mp hA
  refine isElemAbelian_iff.mpr ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have := hc _ (mem_cj.mp hx) _ (mem_cj.mp hy)
    have h2 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := this
        _ = g * (y * x) * g⁻¹ := by group
    simpa using h2
  · have := hp _ (mem_cj.mp hx)
    have h2 : g * x ^ 2 * g⁻¹ = 1 := by
      calc g * x ^ 2 * g⁻¹ = (g * x * g⁻¹) ^ 2 := by rw [pow_two, pow_two]; group
        _ = 1 := this
    simpa using h2

theorem isElemAbelian_aimg {S A : Subgroup G} (α : S ≃* S) (hA : CFSG.Open.IsElemAbelian 2 A) :
    CFSG.Open.IsElemAbelian 2 (aimg S α A) := by
  obtain ⟨hc, hp⟩ := isElemAbelian_iff.mp hA
  refine isElemAbelian_iff.mpr ⟨?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := mem_aimg.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_aimg.mp hy
    have h1 : a * b = b * a := Subtype.ext (hc _ ha _ hb)
    have h2 : α a * α b = α b * α a := by rw [← map_mul, ← map_mul, h1]
    exact congrArg Subtype.val h2
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_aimg.mp hx
    have h1 : a ^ 2 = 1 := Subtype.ext (by simpa using hp _ ha)
    have h2 : (α a) ^ 2 = 1 := by rw [← map_pow, h1, map_one]
    simpa using congrArg Subtype.val h2

theorem isMaxElemAbelian_aimg [Finite G] {S A : Subgroup G} (α : S ≃* S)
    (hA : IsMaxElemAbelian S A) : IsMaxElemAbelian S (aimg S α A) := by
  refine ⟨aimg_le, isElemAbelian_aimg α hA.2.1, fun B hBS hB => ?_⟩
  rw [card_aimg hA.1]
  exact maxElem_card_le hA hBS hB

theorem isMaxElemAbelian_cj [Finite G] {H A : Subgroup G} (g : G) (hA : IsMaxElemAbelian H A) :
    IsMaxElemAbelian (cj H g) (cj A g) := by
  refine ⟨cj_mono hA.1, isElemAbelian_cj hA.2.1 g, fun B hBH hB => ?_⟩
  have hB' : cj B g⁻¹ ≤ H := by
    intro y hy
    have h1 : g⁻¹ * y * g⁻¹⁻¹ ∈ B := mem_cj.mp hy
    have h2 := mem_cj.mp (hBH h1)
    simpa [mul_assoc] using h2
  have := maxElem_card_le hA hB' (isElemAbelian_cj hB g⁻¹)
  rw [card_cj] at this ⊢
  exact this

theorem maxElem_le_thompsonJ {H A : Subgroup G} (hA : IsMaxElemAbelian H A) : A ≤ thompsonJ H :=
  le_iSup₂_of_le A hA le_rfl

theorem thompsonJ_le_of_forall {H N : Subgroup G} (h : ∀ A, IsMaxElemAbelian H A → A ≤ N) :
    thompsonJ H ≤ N :=
  iSup₂_le h

theorem thompsonJ_le_self' (H : Subgroup G) : thompsonJ H ≤ H :=
  thompsonJ_le_of_forall fun _ hA => hA.1

theorem exists_maxElem [Finite G] (H : Subgroup G) : ∃ A : Subgroup G, IsMaxElemAbelian H A := by
  classical
  have hne : ({B : Subgroup G | B ≤ H ∧ CFSG.Open.IsElemAbelian 2 B} : Set (Subgroup G)).Nonempty :=
    ⟨⊥, bot_le, isElemAbelian_bot⟩
  obtain ⟨A, ⟨hAH, hA⟩, hmax⟩ := Set.exists_max_image _ (fun B : Subgroup G => Nat.card B)
    (Set.toFinite _) hne
  exact ⟨A, hAH, hA, fun B hBH hB => hmax B ⟨hBH, hB⟩⟩

theorem mem_centerTorsion_thompsonJ_iff [Finite G] {H : Subgroup G} {x : G} :
    x ∈ centerTorsion 2 (thompsonJ H) ↔ x ∈ H ∧ ∀ A : Subgroup G, IsMaxElemAbelian H A → x ∈ A := by
  constructor
  · intro hx
    obtain ⟨hxJ, hxc, hx2⟩ := mem_centerTorsion_iff.mp hx
    have hxH : x ∈ H := thompsonJ_le_self' H hxJ
    exact ⟨hxH, fun A hA => maxElem_mem_of_centralizer hA hxH
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hxc a (maxElem_le_thompsonJ hA ha)) hx2⟩
  · rintro ⟨hxH, hxA⟩
    obtain ⟨A₀, hA₀⟩ := exists_maxElem H
    have hx2 : x ^ 2 = 1 := (isElemAbelian_iff.mp hA₀.2.1).2 x (hxA A₀ hA₀)
    have hxJ : x ∈ thompsonJ H := maxElem_le_thompsonJ hA₀ (hxA A₀ hA₀)
    refine mem_centerTorsion_iff.mpr ⟨hxJ, fun k hk => ?_, hx2⟩
    have : thompsonJ H ≤ Subgroup.centralizer ({x} : Set G) := by
      refine thompsonJ_le_of_forall fun A hA a ha => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (isElemAbelian_iff.mp hA.2.1).1 x (hxA A hA) a ha
    exact (Subgroup.mem_centralizer_iff.mp (this hk) x (Set.mem_singleton x)).symm

theorem thompsonJ_conj_mem [Finite G] {Q : Subgroup G} [Q.Normal] {x : G} (hx : x ∈ thompsonJ Q)
    (g : G) : g * x * g⁻¹ ∈ thompsonJ Q := by
  have : thompsonJ Q ≤ (thompsonJ Q).comap (MulAut.conj g).toMonoidHom := by
    refine thompsonJ_le_of_forall fun A hA a ha => ?_
    show g * a * g⁻¹ ∈ thompsonJ Q
    have hA' : IsMaxElemAbelian Q (cj A g⁻¹) := by
      have := isMaxElemAbelian_cj g⁻¹ hA
      rwa [cj_eq_self_of_normal] at this
    exact maxElem_le_thompsonJ hA' (by simpa using mem_cj_of_mem (g := g⁻¹) ha)
  exact this hx

theorem centerTorsion_thompsonJ_conj_mem [Finite G] {Q : Subgroup G} [Q.Normal] {x : G}
    (hx : x ∈ centerTorsion 2 (thompsonJ Q)) (g : G) :
    g * x * g⁻¹ ∈ centerTorsion 2 (thompsonJ Q) := by
  obtain ⟨hxQ, hxA⟩ := mem_centerTorsion_thompsonJ_iff.mp hx
  refine mem_centerTorsion_thompsonJ_iff.mpr ⟨(inferInstance : Q.Normal).conj_mem x hxQ g,
    fun A hA => ?_⟩
  have hA' : IsMaxElemAbelian Q (cj A g) := by
    have := isMaxElemAbelian_cj g hA
    rwa [cj_eq_self_of_normal] at this
  exact mem_cj.mp (hxA _ hA')

end Elem

end CFSG.QuasithinUnique.Setup.Campbell
