module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Facts
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem quasisimple_of_equiv' {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

theorem catalogIs_center_quot_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (P : TauCeti.CFSGIndex → Prop) (h : catalogIs (A ⧸ Subgroup.center A) P) :
    catalogIs (B ⧸ Subgroup.center B) P := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨(QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
    (Subgroup.map_center_eq e)).symm.trans f⟩⟩

theorem isCatalogGroup_center_quot_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsCatalogGroup (A ⧸ Subgroup.center A)) : IsCatalogGroup (B ⧸ Subgroup.center B) := by
  obtain ⟨i, ⟨f⟩⟩ := h
  exact ⟨i, ⟨(QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
    (Subgroup.map_center_eq e)).symm.trans f⟩⟩

theorem card_center_eq_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center B) := by
  have h2 : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := Subgroup.map_center_eq e
  rw [← h2, Subgroup.card_map_of_injective e.injective]

theorem isTypeWithCenter_of_equiv {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
    {X : Subgroup G₁} {Y : Subgroup G₂} {P : TauCeti.CFSGIndex → Prop} {z : ℕ}
    (e : PQuot 3 X ≃* PQuot 3 Y) (h : IsTypeWithCenter 3 X P z) : IsTypeWithCenter 3 Y P z :=
  ⟨catalogIs_center_quot_of_equiv e P h.1, by rw [← card_center_eq_of_equiv e]; exact h.2⟩

theorem model_of_component {G : Type} [Group G] [Finite G] {J I : Subgroup G} {x : G}
    (hJQ : CFSG.Open.IsQuasisimple (PQuot 3 J)) (hcat : IsCatalogGroup (PSimple 3 J))
    (hx3 : x ^ 3 = 1) (hxJ : x ∈ Subgroup.normalizer (J : Set G))
    (hI : GLAPComponent 3 (J ⊓ Subgroup.centralizer ({x} : Set G)) I)
    (hIT : IsTypeWithCenter 3 I isA6 1) (hnot : ¬ J ≤ I ⊔ GLAPPrimeCoreOf 3 J) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (K I' : Subgroup Q) (y : Q) (e : ↥K ≃* PQuot 3 J),
      I1430Model K I' y ∧
        (InducesInnerMod 3 J x → ∃ g ∈ K, ∀ k ∈ K, y⁻¹ * k * y = g * k * g⁻¹) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  set H : Subgroup G := J ⊔ Subgroup.zpowers x with hH
  have hJH : J ≤ H := le_sup_left
  have hxH : x ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hIJ : I ≤ J := le_trans hI.1 inf_le_left
  have hIH : I ≤ H := hIJ.trans hJH
  have hXH : J ⊓ Subgroup.centralizer ({x} : Set G) ≤ H := inf_le_left.trans hJH
  set K₀ : Subgroup ↥H := J.subgroupOf H with hK₀
  have hHN : H ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hxJ)
  haveI hK₀n : K₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).2 hHN
  set N₀ : Subgroup ↥H := GLAPPrimeCoreOf 3 K₀ with hN₀
  haveI hN₀n : N₀.Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf 3 K₀
    rw [Subgroup.normalizer_eq_top_iff.2 hK₀n, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  have hker : (QuotientGroup.mk' N₀).ker = N₀ := QuotientGroup.ker_mk' N₀
  have hN₀K : N₀ ≤ K₀ := Subgroup.map_subtype_le _
  have hN : ¬ 3 ∣ Nat.card (QuotientGroup.mk' N₀).ker := by
    rw [hker]
    exact not_dvd_card_glaPPrimeCoreOf hp K₀
  have hkerle : (QuotientGroup.mk' N₀).ker ≤ K₀ := by
    rw [hker]
    exact hN₀K
  have hx₀p : IsPGroup 3 (Subgroup.zpowers (⟨x, hxH⟩ : ↥H)) :=
    isPGroup_zpowers_mk hxH (isPGroup_zpowers_of_pow_eq_one hx3)
  have hmapsub : N₀.map H.subtype = GLAPPrimeCoreOf 3 J :=
    map_subtype_glaPPrimeCoreOf_subgroupOf 3 hJH
  set ψ : ↥H →* ↥H ⧸ N₀ := QuotientGroup.mk' N₀ with hψ
  set x₀ : ↥H := ⟨x, hxH⟩ with hx₀
  set K' : Subgroup (↥H ⧸ N₀) := K₀.map ψ with hK'
  set I'' : Subgroup (↥H ⧸ N₀) := (I.subgroupOf H).map ψ with hI''
  have hK'n : K'.Normal := hK₀n.map _ (QuotientGroup.mk'_surjective N₀)
  have e : ↥K' ≃* PQuot 3 J :=
    (Classical.choice (nonempty_pQuot_equiv_map_self (p := 3) (ψ := ψ) (K := K₀)
      (by rw [hker, inf_eq_left.2 hN₀K]))).symm.trans
      (Classical.choice (nonempty_pQuot_equiv_subgroupOf 3 hJH))
  have hK'q : CFSG.Open.IsQuasisimple ↥K' := quasisimple_of_equiv' e.symm hJQ
  have hcat' : IsCatalogGroup (↥K' ⧸ Subgroup.center ↥K') :=
    isCatalogGroup_center_quot_of_equiv e.symm hcat
  have hK'c : ∀ z ∈ Subgroup.center ↥K', ∃ n : ℕ, z ^ 3 ^ n = 1 := by
    intro z hz
    have h2 : (Subgroup.center ↥K').map e.toMonoidHom = Subgroup.center (PQuot 3 J) :=
      Subgroup.map_center_eq e
    have hz' : e z ∈ Subgroup.center (PQuot 3 J) := by
      rw [← h2]
      exact Subgroup.mem_map_of_mem _ hz
    obtain ⟨n, hn⟩ := CFSG.LocalAnalysis.GLTheoremA.I106TGroup.center_pQuot_three_pow J (e z) hz'
    exact ⟨n, e.injective (by rw [map_pow, hn, map_one])⟩
  have hy'n : ψ x₀ ∈ Subgroup.normalizer (K' : Set (↥H ⧸ N₀)) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hK'n]
    exact Subgroup.mem_top _
  have hy'3 : (ψ x₀) ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : x₀ ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [h3, map_one]
  have hI₀ : GLAPComponent 3 (J.subgroupOf H ⊓ Subgroup.centralizer ({x₀} : Set ↥H))
      (I.subgroupOf H) := by
    have h1 := glaPComponent_subgroupOf hp hXH hI
    rw [subgroupOf_inf_centralizer hxH] at h1
    exact h1
  have hcomp : GLAPComponent 3 (K' ⊓ Subgroup.centralizer ({ψ x₀} : Set (↥H ⧸ N₀))) I'' :=
    glaPComponent_map_of_ker_le hp hN hkerle hx₀p hI₀
  have hIT'' : IsTypeWithCenter 3 I'' isA6 1 := by
    obtain ⟨eA⟩ := nonempty_pQuot_equiv_map hp hN (I.subgroupOf H)
    obtain ⟨eB⟩ := nonempty_pQuot_equiv_subgroupOf 3 hIH
    exact isTypeWithCenter_of_equiv (eB.symm.trans eA) hIT
  have hnotC : ¬ K' ≤ Subgroup.centralizer ({ψ x₀} : Set (↥H ⧸ N₀)) := by
    intro hC
    rw [inf_eq_left.2 hC] at hcomp
    have hO : GLAPPrimeCore 3 ↥K' = ⊥ := by
      have h1 := glaPPrimeCore_map_iso 3 e
      have h2 : GLAPPrimeCore 3 (PQuot 3 J) = ⊥ :=
        CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
      rw [h2] at h1
      have h3 : GLAPPrimeCore 3 ↥K' ≤ e.toMonoidHom.ker := (Subgroup.map_eq_bot_iff _).1 h1
      rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective] at h3
      exact le_bot_iff.1 h3
    have hY : CFSG.Open.IsQuasisimple (↥K' ⧸ GLAPPrimeCore 3 ↥K') :=
      quasisimple_of_equiv' (((QuotientGroup.quotientMulEquivOfEq hO).trans
        QuotientGroup.quotientBot).symm) hK'q
    have hbar : barX 3 K' I'' = ⊤ := eq_top_of_isComponentOf_of_isQuasisimple hY hcomp.2.2.1
    have hIK' : I'' ≤ K' := Subgroup.map_mono (fun a ha => Subgroup.mem_subgroupOf.2
      (hIJ (Subgroup.mem_subgroupOf.1 ha)))
    have hsup : I'' ⊔ GLAPPrimeCoreOf 3 K' = K' :=
      sup_glaPPrimeCoreOf_eq_of_barX_eq_top hIK' hbar
    have hGO : GLAPPrimeCoreOf 3 K' = ⊥ := by
      show (GLAPPrimeCore 3 ↥K').map K'.subtype = ⊥
      rw [hO, Subgroup.map_bot]
    rw [hGO, sup_bot_eq] at hsup
    refine hnot (fun j hj => ?_)
    have hj₀ : (⟨j, hJH hj⟩ : ↥H) ∈ K₀ := Subgroup.mem_subgroupOf.2 hj
    have hψj : ψ ⟨j, hJH hj⟩ ∈ I'' := by
      rw [hsup]
      exact Subgroup.mem_map_of_mem ψ hj₀
    obtain ⟨i, hi, hψi⟩ := Subgroup.mem_map.1 hψj
    have hn : i⁻¹ * ⟨j, hJH hj⟩ ∈ (QuotientGroup.mk' N₀).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, inv_mul_cancel]
    rw [hker] at hn
    have hjn : j = (i : G) * ((i⁻¹ * ⟨j, hJH hj⟩ : ↥H) : G) := by
      simp
    rw [hjn]
    refine mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hi))
      (Subgroup.mem_sup_right ?_)
    rw [← hmapsub]
    exact Subgroup.mem_map_of_mem H.subtype hn
  refine ⟨↥H ⧸ N₀, inferInstance, inferInstance, K', I'', ψ x₀, e,
    ⟨hK'n, hK'q, hK'c, hy'n, hy'3, hnotC, hcomp, hIT'', hcat'⟩, ?_⟩
  intro hInner
  obtain ⟨l, hl, hall⟩ := hInner
  have hl₀ : (⟨l, hJH hl⟩ : ↥H) ∈ K₀ := Subgroup.mem_subgroupOf.2 hl
  refine ⟨(ψ ⟨l, hJH hl⟩)⁻¹, K'.inv_mem (Subgroup.mem_map_of_mem ψ hl₀), ?_⟩
  intro k hk
  obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.1 hk
  have hj : (j₀ : G) ∈ J := Subgroup.mem_subgroupOf.1 hj₀
  have hmem := hall j₀ hj
  rw [← hmapsub] at hmem
  obtain ⟨m, hm, hmv⟩ := Subgroup.mem_map.1 hmem
  have hmn : m = (((⟨l, hJH hl⟩ : ↥H)⁻¹ * j₀ * (⟨l, hJH hl⟩ : ↥H))⁻¹ * (x₀⁻¹ * j₀ * x₀)) :=
    Subtype.ext (by simpa [hx₀] using hmv)
  rw [hmn] at hm
  have hψn : ψ (((⟨l, hJH hl⟩ : ↥H)⁻¹ * j₀ * (⟨l, hJH hl⟩ : ↥H))⁻¹ * (x₀⁻¹ * j₀ * x₀)) = 1 := by
    have h' : (((⟨l, hJH hl⟩ : ↥H)⁻¹ * j₀ * (⟨l, hJH hl⟩ : ↥H))⁻¹ * (x₀⁻¹ * j₀ * x₀)) ∈
        (QuotientGroup.mk' N₀).ker := by
      rw [hker]
      exact hm
    exact MonoidHom.mem_ker.1 h'
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv] at hψn ⊢
  rw [eq_inv_of_mul_eq_one_right hψn]
  group

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
