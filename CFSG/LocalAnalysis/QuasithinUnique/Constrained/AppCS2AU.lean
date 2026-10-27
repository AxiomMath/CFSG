module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellCommuting
public import CFSG.Quasithin.Background.C2Aux

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

omit [Finite G] in
theorem iSup_fin_two_eq' (f : Fin 2 → Subgroup G) : (⨆ i, f i) = f 0 ⊔ f 1 :=
  le_antisymm (iSup_le fun i => by fin_cases i <;> simp) (sup_le (le_iSup f 0) (le_iSup f 1))

@[expose] def U0 (L : Subgroup G) (t : G) : Subgroup G := blockU L ⊔ blockU2 L t

@[expose] def gaU0 (L : Subgroup G) (t : G) (A : Subgroup G) : Subgroup G :=
  (A ⊓ centralizer ((U0 L t : Subgroup G) : Set G)) ⊔ U0 L t

omit [Finite G] in
theorem blockU2_eq (L : Subgroup G) (t : G) : blockU2 L t = blockU (conjR L t) :=
  (blockU_conjR L t).symm

omit [Finite G] in
theorem card_U1 (P : PiData L) : Nat.card ↥(blockU L) = 16 := P.card_blockU

theorem card_U2 (P : PiData L) (t : G) : Nat.card ↥(blockU2 L t) = 16 := by
  rw [show blockU2 L t = conjSubgroup (blockU L) t from rfl, C5.card_conjSubgroup, P.card_blockU]

namespace Dbl

variable {t : G} (D : Dbl T M H S L t)
include D

theorem blockU2_le_L₂ : blockU2 L t ≤ conjR L t := by
  show conjR (blockU L) t ≤ conjR L t
  exact C5.conjSubgroup_mono D.blockU_le_L t

theorem campbell_pkg :
    IsElemAbelian 2 (U0 L t) ∧ H ≤ normalizer ((U0 L t : Subgroup G) : Set G) ∧
      H ⊓ centralizer ((U0 L t : Subgroup G) : Set G) = pCoreOf 2 H ∧
      S ⊓ centralizer ((U0 L t : Subgroup G) : Set G) = pCoreOf 2 H := by
  have hLb : IsBlock2 H L := D.hcs.block.1
  have hL : ∀ i : Fin 2, IsBlock2 H (![L, conjR L t] i) := by
    intro i
    fin_cases i
    · exact hLb
    · exact CFSG.Quasithin.IsBlock2.conjByElt_of_mem hLb (H.inv_mem (D.hcs.sylow.le D.ht))
  have hcomm : ∀ i j : Fin 2, i ≠ j → ⁅(![L, conjR L t] i), (![L, conjR L t] j)⁆ = ⊥ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact D.hcomm
    · rw [Subgroup.commutator_comm]; exact D.hcomm
    · exact absurd rfl hij
  have hperm : ∀ g ∈ S, ∀ i : Fin 2, ∃ j : Fin 2,
      conjSubgroup (![L, conjR L t] i) g = ![L, conjR L t] j := by
    intro g hg i
    fin_cases i
    · rcases D.conjR_cases hg with a | a
      · exact ⟨0, a⟩
      · exact ⟨1, a⟩
    · have hst : t * g ∈ S := S.mul_mem D.ht hg
      have e : conjSubgroup (conjR L t) g = conjR L (t * g) := conjSubgroup_conjSubgroup L t g
      rcases D.conjR_cases hst with a | a
      · exact ⟨0, by show conjSubgroup (conjR L t) g = L; rw [e]; exact a⟩
      · exact ⟨1, by show conjSubgroup (conjR L t) g = conjR L t; rw [e]; exact a⟩
  have hKT : (⨆ i : Fin 2, ![L, conjR L t] i) ⊔ S = H := by
    rw [iSup_fin_two_eq']
    show L ⊔ conjR L t ⊔ S = H
    rw [← D.hjoin, ← D.hcs.eq_join]
  have := Setup.Campbell.commuting_short_product_core_centralizer D.hcs.sylow (s := 2)
    (by norm_num) ![L, conjR L t] hL hcomm hperm hKT
  have hU : (⨆ i : Fin 2, blockU (![L, conjR L t] i)) = U0 L t := by
    rw [iSup_fin_two_eq']
    show blockU L ⊔ blockU (conjR L t) = blockU L ⊔ blockU2 L t
    rw [blockU_conjR]
    rfl
  obtain ⟨-, h2, h3, h4, -, h6, -⟩ := this
  rw [hU] at h2 h3 h4 h6
  exact ⟨h2, h3, h4, h6⟩

theorem U0_isElemAbelian : IsElemAbelian 2 (U0 L t) := D.campbell_pkg.1

theorem hQ0 : H ⊓ centralizer ((U0 L t : Subgroup G) : Set G) = pCoreOf 2 H :=
  D.campbell_pkg.2.2.1

theorem U1_le_Q : blockU L ≤ pCoreOf 2 H := C56.blockU_le_pCoreOf_general D.hcs

theorem U2_le_Q : blockU2 L t ≤ pCoreOf 2 H := by
  have hPn : t ∈ normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
      (D.hcs.sylow.le D.ht)
  have := C5.conjSubgroup_mono D.U1_le_Q t
  rwa [C5.conjSubgroup_eq_self hPn] at this

theorem U0_le_Q : U0 L t ≤ pCoreOf 2 H := sup_le D.U1_le_Q D.U2_le_Q

theorem Q_le_S : pCoreOf 2 H ≤ S := C56.pCoreOf_le_S D.hcs

theorem U0_le_S : U0 L t ≤ S := D.U0_le_Q.trans D.Q_le_S

theorem Q_comm_U0 {q u : G} (hq : q ∈ pCoreOf 2 H) (hu : u ∈ U0 L t) : q * u = u * q := by
  rw [← D.hQ0] at hq
  exact (Subgroup.mem_centralizer_iff.1 hq.2 u hu).symm

theorem U1_comm_U2 : ∀ a ∈ blockU L, ∀ b ∈ blockU2 L t, a * b = b * a := fun a ha b hb =>
  D.comm_elem a (D.blockU_le_L ha) b (D.blockU2_le_L₂ hb)

theorem blockU0_eq : blockU0 S L = U0 L t := by
  apply le_antisymm
  · refine iSup_le fun g => ?_
    have hg : (g : G)⁻¹ ∈ S := S.inv_mem g.2
    have hconj : (blockU L).map (MulAut.conj (g : G)).toMonoidHom =
        conjR (blockU L) (g : G)⁻¹ := by simp [conjR]
    rw [hconj]
    have e : conjR (blockU L) (g : G)⁻¹ = blockU (conjR L (g : G)⁻¹) := (blockU_conjR L _).symm
    rw [e]
    rcases D.conjR_cases hg with h | h
    · rw [h]; exact le_sup_left
    · rw [h]
      show blockU (conjR L t) ≤ blockU L ⊔ blockU2 L t
      rw [blockU_conjR]
      exact le_sup_right
  · refine sup_le ?_ ?_
    · calc blockU L = conjR (blockU L) 1 := (conjSubgroup_one _).symm
        _ ≤ blockU0 S L := conjR_le_conjJoin' S.one_mem
    · exact conjR_le_conjJoin' D.ht

theorem U1_inf_U2 : blockU L ⊓ blockU2 L t = ⊥ := D.blockU_inf_blockU₂

theorem exists_mul_of_mem_U0 {u : G} (hu : u ∈ U0 L t) :
    ∃ a ∈ blockU L, ∃ b ∈ blockU2 L t, a * b = u := by
  have hN : blockU L ≤ normalizer ((blockU2 L t : Subgroup G) : Set G) :=
    C5.le_normalizer_of_commute D.U1_comm_U2
  have hu' : u ∈ ((blockU L ⊔ blockU2 L t : Subgroup G) : Set G) := hu
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (blockU L) (blockU2 L t) hN] at hu'
  obtain ⟨a, ha, b, hb, hab⟩ := hu'
  exact ⟨a, ha, b, hb, hab⟩

theorem mul_unique {a a' b b' : G} (ha : a ∈ blockU L) (ha' : a' ∈ blockU L)
    (hb : b ∈ blockU2 L t) (hb' : b' ∈ blockU2 L t) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hmem : a'⁻¹ * a ∈ blockU L ⊓ blockU2 L t :=
    Subgroup.mem_inf.2 ⟨(blockU L).mul_mem ((blockU L).inv_mem ha') ha,
      by rw [h1]; exact (blockU2 L t).mul_mem hb' ((blockU2 L t).inv_mem hb)⟩
  rw [D.U1_inf_U2] at hmem
  have h2 : a'⁻¹ * a = 1 := Subgroup.mem_bot.1 hmem
  have h3 : a = a' := by
    have := congrArg (a' * ·) h2
    simpa using this
  refine ⟨h3, ?_⟩
  subst h3
  exact mul_left_cancel h

omit [Finite G] D in
theorem one_block (P : PiData L) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAN : A ≤ normalizer (L : Set G)) :
    Nat.card A * Nat.card ↥(blockU L ⊓ centralizer (A : Set G)) ≤
      16 * Nat.card ↥(A ⊓ centralizer (blockU L : Set G)) := by
  have h4 := P.card_im_mul hAN
  have h5 := P.card_fix hAN
  have h7 := card_mul_fix_le (P.im A) (P.im_elemAbelian hA).1 (P.im_elemAbelian hA).2
  rw [h5, ← h4]
  calc Nat.card (P.im A) * Nat.card ↥(A ⊓ centralizer (blockU L : Set G)) *
        Nat.card (FixΔ (P.im A))
      = Nat.card ↥(A ⊓ centralizer (blockU L : Set G)) *
          (Nat.card (P.im A) * Nat.card (FixΔ (P.im A))) := by ring
    _ ≤ Nat.card ↥(A ⊓ centralizer (blockU L : Set G)) * 16 := Nat.mul_le_mul_left _ h7
    _ = 16 * Nat.card ↥(A ⊓ centralizer (blockU L : Set G)) := by ring

theorem one_block_conj (P : PiData L) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAS₁ : A ≤ s2SI S L) :
    Nat.card A * Nat.card ↥(blockU2 L t ⊓ centralizer (A : Set G)) ≤
      16 * Nat.card ↥(A ⊓ centralizer (blockU2 L t : Set G)) := by
  set A' := conjSubgroup A t⁻¹ with hA'
  have hA'S₁ : A' ≤ s2SI S L := by
    intro x hx
    have hx' : t⁻¹ * x * t⁻¹⁻¹ ∈ A := mem_conjSubgroup_iff.1 hx
    have := D.s2SI_normal D.ht (hAS₁ hx')
    have e : t * (t⁻¹ * x * t⁻¹⁻¹) * t⁻¹ = x := by group
    rwa [e] at this
  have hA'e : IsElemAbelian 2 A' :=
    C5.isElemAbelian_two_iff.mpr ((C5.isElemAbelian_two_iff.mp hA).conjSubgroup t⁻¹)
  have hone := one_block P hA'e (hA'S₁.trans s2SI_le_normalizer)
  have e1 : Nat.card A' = Nat.card A := C5.card_conjSubgroup A t⁻¹
  have hU2 : conjSubgroup (blockU2 L t) t⁻¹ = blockU L :=
    C5.conjSubgroup_conjSubgroup_inv (blockU L) t
  have e2 : Nat.card ↥(blockU L ⊓ centralizer (A' : Set G)) =
      Nat.card ↥(blockU2 L t ⊓ centralizer (A : Set G)) := by
    rw [← C5.card_conjSubgroup (blockU2 L t ⊓ centralizer (A : Set G)) t⁻¹, C5.conjSubgroup_inf,
      C5.conjSubgroup_centralizer, hU2]
  have e3 : Nat.card ↥(A' ⊓ centralizer (blockU L : Set G)) =
      Nat.card ↥(A ⊓ centralizer (blockU2 L t : Set G)) := by
    rw [← C5.card_conjSubgroup (A ⊓ centralizer (blockU2 L t : Set G)) t⁻¹, C5.conjSubgroup_inf,
      C5.conjSubgroup_centralizer, hU2]
  rw [e1, e2, e3] at hone
  exact hone

theorem centralizer_U0 :
    centralizer ((U0 L t : Subgroup G) : Set G) =
      centralizer (blockU L : Set G) ⊓ centralizer (blockU2 L t : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun u hu => h u (Subgroup.mem_sup_left hu), fun u hu => h u (Subgroup.mem_sup_right hu)⟩
  · rintro ⟨h1, h2⟩ u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul_of_mem_U0 hu
    have e1 := h1 a ha
    have e2 := h2 b hb
    calc a * b * x = a * (b * x) := by group
      _ = a * (x * b) := by rw [e2]
      _ = (a * x) * b := by group
      _ = (x * a) * b := by rw [e1]
      _ = x * (a * b) := by group

theorem card_cent_U0_le {A : Subgroup G} (hAS₁ : A ≤ s2SI S L) :
    Nat.card ↥((U0 L t : Subgroup G) ⊓ centralizer (A : Set G)) ≤
      Nat.card ↥(blockU L ⊓ centralizer (A : Set G)) *
        Nat.card ↥(blockU2 L t ⊓ centralizer (A : Set G)) := by
  classical
  have hN1 : ∀ g ∈ A, g ∈ normalizer (blockU L : Set G) := fun g hg =>
    C1.mem_normalizer_blockU (s2SI_le_normalizer (hAS₁ hg))
  have hN2 : ∀ g ∈ A, g ∈ normalizer (blockU2 L t : Set G) := fun g hg => by
    have := C1.mem_normalizer_blockU (L := conjR L t) (D.s2SI_le_normalizer_L₂ (hAS₁ hg))
    rwa [← blockU2_eq L t] at this
  let φ : ↥(blockU L ⊓ centralizer (A : Set G)) × ↥(blockU2 L t ⊓ centralizer (A : Set G)) →
      ↥((U0 L t : Subgroup G) ⊓ centralizer (A : Set G)) := fun p =>
    ⟨p.1.1 * p.2.1, ⟨mul_mem (Subgroup.mem_sup_left p.1.2.1) (Subgroup.mem_sup_right p.2.2.1),
      Subgroup.mem_centralizer_iff.2 fun a ha => by
        have e1 := Subgroup.mem_centralizer_iff.1 p.1.2.2 a ha
        have e2 := Subgroup.mem_centralizer_iff.1 p.2.2.2 a ha
        calc a * (p.1.1 * p.2.1) = (a * p.1.1) * p.2.1 := by group
          _ = (p.1.1 * a) * p.2.1 := by rw [e1]
          _ = p.1.1 * (a * p.2.1) := by group
          _ = p.1.1 * (p.2.1 * a) := by rw [e2]
          _ = p.1.1 * p.2.1 * a := by group⟩⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, hu0, huC⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul_of_mem_U0 hu0
    have hcomp : ∀ g ∈ A, g * a = a * g ∧ g * b = b * g := by
      intro g hg
      have hc := Subgroup.mem_centralizer_iff.1 huC g hg
      have ha' : g * a * g⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.1 (hN1 g hg) a).1 ha
      have hb' : g * b * g⁻¹ ∈ blockU2 L t :=
        (Subgroup.mem_normalizer_iff.1 (hN2 g hg) b).1 hb
      have hprod : (g * a * g⁻¹) * (g * b * g⁻¹) = a * b := by
        calc (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
          _ = (a * b * g) * g⁻¹ := by rw [hc]
          _ = a * b := by group
      obtain ⟨h1, h2⟩ := D.mul_unique ha' ha hb' hb hprod
      refine ⟨?_, ?_⟩
      · calc g * a = (g * a * g⁻¹) * g := by group
          _ = a * g := by rw [h1]
      · calc g * b = (g * b * g⁻¹) * g := by group
          _ = b * g := by rw [h2]
    refine ⟨(⟨a, ha, Subgroup.mem_centralizer_iff.2 fun g hg => (hcomp g hg).1⟩,
      ⟨b, hb, Subgroup.mem_centralizer_iff.2 fun g hg => (hcomp g hg).2⟩), ?_⟩
    rfl
  calc Nat.card ↥((U0 L t : Subgroup G) ⊓ centralizer (A : Set G))
      ≤ Nat.card (↥(blockU L ⊓ centralizer (A : Set G)) ×
          ↥(blockU2 L t ⊓ centralizer (A : Set G))) := Nat.card_le_card_of_surjective φ hsurj
    _ = _ := Nat.card_prod _ _

theorem card_U0 (P : PiData L) : Nat.card ↥(U0 L t) = 256 := by
  have h := B2F.card_sup_mul_card_inf_of_commute D.U1_comm_U2
  rw [D.U1_inf_U2, Subgroup.card_bot, card_U1 P, card_U2 P t] at h
  show Nat.card ↥(blockU L ⊔ blockU2 L t) = 256
  omega

theorem offender_bound (P : PiData L) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAS₁ : A ≤ s2SI S L) :
    Nat.card A * Nat.card ↥((U0 L t : Subgroup G) ⊓ centralizer (A : Set G)) ≤
      256 * Nat.card ↥(A ⊓ centralizer ((U0 L t : Subgroup G) : Set G)) := by
  have h1 := one_block P hA (hAS₁.trans s2SI_le_normalizer)
  have h2 := D.one_block_conj P hA hAS₁
  have hf := D.card_cent_U0_le hAS₁
  set K₁ := A ⊓ centralizer (blockU L : Set G) with hK₁
  set K₂ := A ⊓ centralizer (blockU2 L t : Set G) with hK₂
  set K := A ⊓ centralizer ((U0 L t : Subgroup G) : Set G) with hK
  have hKeq : K₁ ⊓ K₂ = K := by
    rw [hK₁, hK₂, hK, D.centralizer_U0]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have hcommK : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hA ha.1 hb.1
  have h3 := B2F.card_sup_mul_card_inf_of_commute hcommK
  rw [hKeq] at h3
  have h4 : Nat.card ↥(K₁ ⊔ K₂) ≤ Nat.card A :=
    Subgroup.card_le_of_le (sup_le inf_le_left inf_le_left)
  have hk : Nat.card ↥K₁ * Nat.card ↥K₂ ≤ Nat.card A * Nat.card ↥K := by
    rw [← h3]
    exact Nat.mul_le_mul_right _ h4
  set a := Nat.card A
  set f₁ := Nat.card ↥(blockU L ⊓ centralizer (A : Set G))
  set f₂ := Nat.card ↥(blockU2 L t ⊓ centralizer (A : Set G))
  set f₀ := Nat.card ↥((U0 L t : Subgroup G) ⊓ centralizer (A : Set G))
  have hpos : 0 < a := Nat.card_pos
  have h5 : (a * f₁) * (a * f₂) ≤ (16 * Nat.card ↥K₁) * (16 * Nat.card ↥K₂) :=
    Nat.mul_le_mul h1 h2
  have h6 : a * (a * (f₁ * f₂)) ≤ a * (256 * Nat.card ↥K) := by
    calc a * (a * (f₁ * f₂)) = (a * f₁) * (a * f₂) := by ring
      _ ≤ (16 * Nat.card ↥K₁) * (16 * Nat.card ↥K₂) := h5
      _ = 256 * (Nat.card ↥K₁ * Nat.card ↥K₂) := by ring
      _ ≤ 256 * (a * Nat.card ↥K) := Nat.mul_le_mul_left _ hk
      _ = a * (256 * Nat.card ↥K) := by ring
  have h7 : a * (f₁ * f₂) ≤ 256 * Nat.card ↥K := Nat.le_of_mul_le_mul_left h6 hpos
  calc a * f₀ ≤ a * (f₁ * f₂) := Nat.mul_le_mul_left _ hf
    _ ≤ 256 * Nat.card ↥K := h7

theorem aU_spec (P : PiData L) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAS₁ : A ≤ s2SI S L) :
    IsElemAbelian 2 (gaU0 L t A) ∧ Nat.card A ≤ Nat.card ↥(gaU0 L t A) ∧
      gaU0 L t A ≤ pCoreOf 2 H ∧ U0 L t ≤ gaU0 L t A := by
  set K := A ⊓ centralizer ((U0 L t : Subgroup G) : Set G) with hK
  have hKe : IsElemAbelian 2 K := B2F.isElemAbelian_mono inf_le_left hA
  have hcomm : ∀ k ∈ K, ∀ u ∈ U0 L t, k * u = u * k := fun k hk u hu =>
    (Subgroup.mem_centralizer_iff.1 hk.2 u hu).symm
  have hB1e := B2F.isElemAbelian_sup_of_commute hKe D.U0_isElemAbelian hcomm
  have h2 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have h3 : Nat.card ↥(K ⊓ U0 L t) ≤
      Nat.card ↥((U0 L t : Subgroup G) ⊓ centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    exact B2F.isElemAbelian_comm hA ha hx.1.1
  have h4 := D.offender_bound P hA hAS₁
  have h6 := D.card_U0 P
  have hbpos : 0 < Nat.card ↥(K ⊓ U0 L t) := Nat.card_pos
  rw [h6] at h2
  set a := Nat.card ↥(K ⊔ U0 L t)
  set b := Nat.card ↥(K ⊓ U0 L t)
  set k := Nat.card ↥K
  set f := Nat.card ↥((U0 L t : Subgroup G) ⊓ centralizer (A : Set G))
  have h8 : Nat.card A ≤ a := by
    have h9 : Nat.card A * b ≤ a * b := by
      calc Nat.card A * b ≤ Nat.card A * f := Nat.mul_le_mul_left _ h3
        _ ≤ 256 * k := h4
        _ = a * b := by rw [h2]; ring
    exact Nat.le_of_mul_le_mul_right h9 hbpos
  refine ⟨hB1e, h8, sup_le ?_ D.U0_le_Q, le_sup_right⟩
  intro x hx
  rw [← D.hQ0]
  exact ⟨D.hcs.sylow.le (s2SI_le_S (hAS₁ hx.1)), hx.2⟩

theorem omegaOneCenter_le_pCoreOf (P : PiData L) :
    omegaOneCenterOf (thompsonJ S) ≤ pCoreOf 2 H := by
  obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian S
  have hA₀S₁ : A₀ ≤ s2SI S L := (GammaExtra.le_thompsonJ hA₀).trans D.thompsonJ_le_s2SI
  obtain ⟨he, hcard, hle, -⟩ := D.aU_spec P hA₀.2.1 hA₀S₁
  have hmax : IsMaxElemAbelian S (gaU0 L t A₀) :=
    ⟨sup_le (inf_le_left.trans hA₀.1) D.U0_le_S, he,
      fun B hBS hBe => (hA₀.2.2 B hBS hBe).trans hcard⟩
  rw [(omegaOne_centralizer_thompsonJ S).2]
  exact (iInf₂_le (gaU0 L t A₀) hmax).trans hle

theorem U0_le_baum (P : PiData L) : U0 L t ≤ baum S := by
  refine le_inf D.U0_le_S ?_
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact D.Q_comm_U0 (D.omegaOneCenter_le_pCoreOf P hz) hu

theorem blockU_le_baum (P : PiData L) : blockU L ≤ baum S := le_sup_left.trans (D.U0_le_baum P)

theorem blockU2_le_baum (P : PiData L) : blockU2 L t ≤ baum S := le_sup_right.trans (D.U0_le_baum P)

theorem F1_le_Z0 {u : G} (hu : u ∈ blockU L ⊓ centralizer (thompsonJ S : Set G)) :
    u ∈ omegaOneCenterOf (thompsonJ S) := by
  have hL := D.hL
  have hU := isElemAbelian_blockU hL
  have hcJ : ∀ y ∈ thompsonJ S, y * u = u * y := fun y hy =>
    Subgroup.mem_centralizer_iff.1 hu.2 y hy
  obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian S
  have huA : u ∈ A :=
    inf_centralizer_le_of_isMaxElemAbelian hU D.blockU_le_S hA
      ⟨hu.1, Subgroup.mem_centralizer_iff.2 fun a ha => hcJ a (GammaExtra.le_thompsonJ hA ha)⟩
  have huJ : u ∈ thompsonJ S := GammaExtra.le_thompsonJ hA huA
  exact Subgroup.subset_closure ⟨⟨huJ, Subgroup.mem_centralizer_iff.2 fun y hy => hcJ y hy⟩,
    C1.blockU_sq hL u hu.1⟩

theorem exists_ne_one_F1 (P : A5Pi L) (hJ : P.im (thompsonJ S) = Estd) :
    ∃ u ∈ blockU L ⊓ centralizer (thompsonJ S : Set G), u ≠ 1 := by
  have hcard : Nat.card ↥(blockU L ⊓ centralizer (thompsonJ S : Set G)) = 4 := by
    rw [P.card_fix D.thompsonJ_le_N, hJ, card_fix_Estd]
  have : Nontrivial ↥(blockU L ⊓ centralizer (thompsonJ S : Set G)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; norm_num)
  obtain ⟨u, hu⟩ := exists_ne (1 : ↥(blockU L ⊓ centralizer (thompsonJ S : Set G)))
  exact ⟨u, u.2, fun h => hu (Subtype.ext h)⟩

theorem baum_le_normalizer (P : A5Pi L) (hJ : P.im (thompsonJ S) = Estd) :
    baum S ≤ normalizer (L : Set G) := by
  intro b hb
  rcases D.conjR_cases hb.1 with h | h
  · exact mem_normalizer_iff_conjR.2 h
  · exfalso
    obtain ⟨u, hu, hu1⟩ := D.exists_ne_one_F1 P hJ
    have huZ : u ∈ omegaOneCenterOf (thompsonJ S) := D.F1_le_Z0 hu
    have hbu : u * b = b * u := Subgroup.mem_centralizer_iff.1 hb.2 u huZ
    have huU2 : u ∈ conjR (blockU L) b := by
      show u ∈ conjSubgroup (blockU L) b
      rw [mem_conjSubgroup_iff]
      have e : b * u * b⁻¹ = u := by
        calc b * u * b⁻¹ = (u * b) * b⁻¹ := by rw [hbu]
          _ = u := by group
      rw [e]; exact hu.1
    rw [← blockU_conjR, h] at huU2
    have hmem : u ∈ blockU L ⊓ blockU2 L t := ⟨hu.1, by rw [blockU2_eq L t]; exact huU2⟩
    rw [D.U1_inf_U2] at hmem
    exact hu1 (Subgroup.mem_bot.1 hmem)

end Dbl

end CFSG.QuasithinUnique.AppCS2
