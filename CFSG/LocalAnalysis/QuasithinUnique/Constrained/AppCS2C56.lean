module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Mate
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Frat

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace Cfg2

variable {t : G} (C : Cfg2 T M H S L t)
include C

theorem B_le_N_V {x : G} (hx : x ∈ normalizer (S : Set G)) :
    baum S ≤ normalizer (conjR (blockU L) x : Set G) := by
  intro b hb
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  show conjR (conjR (blockU L) x) b = conjR (blockU L) x
  have hxb : x * b * x⁻¹ ∈ baum S :=
    (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_baum S hx) b).1 hb
  have hU : conjR (blockU L) (x * b * x⁻¹) = blockU L :=
    C5.conjSubgroup_eq_self (C1.mem_normalizer_blockU (C.hBN hxb))
  rw [Dbl.conjR_conjR]
  have e : x * b = (x * b * x⁻¹) * x := by group
  rw [e, ← Dbl.conjR_conjR, hU]

theorem U_le_N_V {x : G} (hx : x ∈ normalizer (S : Set G)) :
    blockU L ≤ normalizer (conjR (blockU L) x : Set G) :=
  C.U_le_baum.trans (C.B_le_N_V hx)

theorem V_comm {x : G} {v v' : G} (hv : v ∈ conjR (blockU L) x) (hv' : v' ∈ conjR (blockU L) x) :
    v * v' = v' * v :=
  (C5.isElemAbelian_two_iff.mp (C.V_elem x)).1 v hv v' hv'

theorem cent_U_V {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    blockU L ⊓ centralizer (conjR (blockU L) x : Set G) ≤ ⁅conjR (blockU L) x, blockU L⁆ ∧
      blockU L ⊓ centralizer (conjR (blockU L) x : Set G) = blockU L ⊓ conjR (blockU L) x ∧
      blockU L ⊓ conjR (blockU L) x =
        conjR (blockU L) x ⊓ centralizer (blockU L : Set G) := by
  have hL := C.D.hL
  have hVN : conjR (blockU L) x ≤ normalizer (L : Set G) := C.V_le_N hx
  have hcard1 : Nat.card ↥(blockU L ⊓ centralizer (conjR (blockU L) x : Set G)) = 4 := by
    rw [C.P.card_fix hVN, hVE, card_fix_Estd]
  have hcard2 : Nat.card ↥(conjR (blockU L) x ⊓ centralizer (blockU L : Set G)) = 4 := by
    have h4 := C.P.card_im_mul hVN
    rw [hVE, Estd_card, C.card_V x] at h4
    omega
  have h1 : blockU L ⊓ centralizer (conjR (blockU L) x : Set G) ≤
      ⁅conjR (blockU L) x, blockU L⁆ := by
    intro u hu
    obtain ⟨huU, huC⟩ := hu
    set f : evenWeight 5 := Multiplicative.toAdd (C.P.β ⟨u, huU⟩) with hf
    have hfix : f ∈ FixΔ Estd := by
      rw [← hVE]
      intro σ hσ
      obtain ⟨y, hy, rfl⟩ := (C.P.mem_im).1 hσ
      have hc := Subgroup.mem_centralizer_iff.1 huC y hy
      have h := C.P.hcomp y ⟨u, huU⟩ ⟨u, huU⟩ (by
        show u = (y : G) * u * (y : G)⁻¹
        rw [hc]; group)
      exact h.symm
    have hfe : isEven f.1 := (mem_evenWeight_iff f.1).1 f.2
    have hfE : ∀ σ ∈ Eset, pact σ f.1 = f.1 := fun σ hσ =>
      congrArg Subtype.val (hfix σ ((mem_Estd σ).2 hσ))
    obtain ⟨t', htE, w, hwe, hw⟩ := fix_comm f.1 hfe hfE
    have htV : t' ∈ C.P.im (conjR (blockU L) x) := by
      rw [hVE]; exact (mem_Estd t').2 htE
    obtain ⟨v, hvV, hvt⟩ := (C.P.mem_im).1 htV
    have hw' : w ∈ evenWeight 5 := (mem_evenWeight_iff w).2 hwe
    set u' : ↥(blockU L) := C.P.β.symm (Multiplicative.ofAdd ⟨w, hw'⟩) with hu'
    have hu'β : Multiplicative.toAdd (C.P.β u') = ⟨w, hw'⟩ := by simp [hu']
    have hvU' : (v : G) * (u' : G) * (v : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (L := L) v.2) u').mp u'.2
    have hcomp := C.P.hcomp v u' ⟨(v : G) * (u' : G) * (v : G)⁻¹, hvU'⟩ rfl
    have heq : (⟨(v : G) * (u' : G) * (v : G)⁻¹, hvU'⟩ : ↥(blockU L)) * u'⁻¹ = ⟨u, huU⟩ := by
      apply C.P.β.injective
      apply Multiplicative.toAdd.injective
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hcomp, hvt, hu'β]
      apply Subtype.ext
      funext i
      have hi := congrFun hw i
      simp only [Pi.add_apply] at hi
      show pact t' w i + -(w i) = f.1 i
      rw [← hi]
      generalize pact t' w i = a
      generalize w i = b
      revert a b
      decide
    have hu : u = (v : G) * (u' : G) * (v : G)⁻¹ * (u' : G)⁻¹ := by
      have := congrArg Subtype.val heq
      simpa using this.symm
    rw [hu]
    exact Subgroup.commutator_mem_commutator hvV u'.2
  have h2 : blockU L ⊓ conjR (blockU L) x ≤
      conjR (blockU L) x ⊓ centralizer (blockU L : Set G) := by
    intro u hu
    refine ⟨hu.2, Subgroup.mem_centralizer_iff.2 fun u' hu' => ?_⟩
    exact blockU_comm_blockU hL hu' hu.1
  have hh1 : blockU L ⊓ centralizer (conjR (blockU L) x : Set G) ≤
      blockU L ⊓ conjR (blockU L) x := by
    intro u hu
    refine ⟨hu.1, ?_⟩
    have := h1 hu
    have hc : ⁅conjR (blockU L) x, blockU L⁆ ≤ conjR (blockU L) x := by
      rw [Subgroup.commutator_le]
      intro v hv u' hu'
      have : (v * u' * v⁻¹ * u'⁻¹) = v * (u' * v⁻¹ * u'⁻¹) := by group
      rw [commutatorElement_def, this]
      exact mul_mem hv ((Subgroup.mem_normalizer_iff.1 (C.U_le_N_V hx hu') v⁻¹).1 (inv_mem hv))
    exact hc this
  have e1 := Subgroup.eq_of_le_of_card_ge hh1
    (by rw [hcard1]; exact (Subgroup.card_le_of_le h2).trans hcard2.le)
  have e2 := Subgroup.eq_of_le_of_card_ge h2 (by
    rw [hcard2, ← e1, hcard1])
  exact ⟨h1, e1, e2⟩


theorem D1_normal {b d : G} (hb : b ∈ baum S) (hd : d ∈ s2I S L) : b * d * b⁻¹ ∈ s2I S L := by
  refine ⟨?_, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
  · exact (baum S).mul_mem ((baum S).mul_mem hb hd.1) ((baum S).inv_mem hb)
  · have hbN : b ∈ normalizer (L : Set G) := C.hBN hb
    have hl' : b⁻¹ * l * b ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hbN) l).1 hl
      simpa using this
    have h := Subgroup.mem_centralizer_iff.1 hd.2 _ hl'
    calc l * (b * d * b⁻¹) = b * ((b⁻¹ * l * b) * d) * b⁻¹ := by group
      _ = b * (d * (b⁻¹ * l * b)) * b⁻¹ := by rw [h]
      _ = (b * d * b⁻¹) * l := by group

theorem D1_le_centralizer_V {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    s2I S L ≤ centralizer (conjR (blockU L) x : Set G) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvB : v ∈ baum S := C.V_le_baum hx hv
  have hcV : d * v * d⁻¹ * v⁻¹ ∈ conjR (blockU L) x := by
    have h1 : d * v * d⁻¹ ∈ conjR (blockU L) x :=
      (Subgroup.mem_normalizer_iff.1 (C.B_le_N_V hx hd.1) v).1 hv
    exact (conjR (blockU L) x).mul_mem h1 ((conjR (blockU L) x).inv_mem hv)
  have hcD : d * v * d⁻¹ * v⁻¹ ∈ s2I S L := by
    have h1 : v * d⁻¹ * v⁻¹ ∈ s2I S L := C.D1_normal hvB ((s2I S L).inv_mem hd)
    have e : d * v * d⁻¹ * v⁻¹ = d * (v * d⁻¹ * v⁻¹) := by group
    rw [e]
    exact (s2I S L).mul_mem hd h1
  have hmem : d * v * d⁻¹ * v⁻¹ ∈ conjR (blockU L) x ⊓ centralizer (blockU L : Set G) :=
    ⟨hcV, Subgroup.mem_centralizer_iff.2 fun u hu =>
      Subgroup.mem_centralizer_iff.1 hcD.2 u (C.D.blockU_le_L hu)⟩
  rw [← (C.cent_U_V hx hVE).2.2] at hmem
  have hZ : d * v * d⁻¹ * v⁻¹ ∈ blockZ L := ⟨hmem.1, hcD.2⟩
  rw [blockZ_eq_bot_of_alt5 C.D.hL C.D.h5] at hZ
  have h1 : d * v * d⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.1 hZ
  have h2 : d * v = v * d := by
    have := mul_inv_eq_one.1 h1
    calc d * v = (d * v * d⁻¹ * v⁻¹) * (v * d) := by group
      _ = v * d := by rw [h1, one_mul]
  exact h2.symm

theorem exists_mem_V_mul_Q1 {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) {b : G} (hb : b ∈ baum S) :
    ∃ v ∈ conjR (blockU L) x, v⁻¹ * b ∈ pCoreOf 2 (L ⊔ baum S) := by
  have hbN : b ∈ normalizer (L : Set G) := C.hBN hb
  have hπ : C.P.π ⟨b, hbN⟩ ∈ C.P.im (conjR (blockU L) x) := by
    rw [hVE, ← C.hB]
    exact C.P.pi_mem_im hb
  obtain ⟨y, hy, hyπ⟩ := (C.P.mem_im).1 hπ
  refine ⟨(y : G), hy, ?_⟩
  rw [C.D.Q1_eq_inf]
  have hyB : (y : G) ∈ baum S := C.V_le_baum hx hy
  refine ⟨(baum S).mul_mem ((baum S).inv_mem hyB) hb, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
  have h1 : C.P.π (y⁻¹ * ⟨b, hbN⟩) = 1 := by
    rw [map_mul, map_inv, hyπ, inv_mul_cancel]
  have h2 := (C.P.hker (y⁻¹ * ⟨b, hbN⟩)).1 h1 u hu
  have h3 : (((y⁻¹ * ⟨b, hbN⟩ : ↥(normalizer (L : Set G))) : ↥(normalizer (L : Set G))) : G) =
      (y : G)⁻¹ * b := rfl
  rw [h3] at h2
  calc u * ((y : G)⁻¹ * b) = ((y : G)⁻¹ * b * u * ((y : G)⁻¹ * b)⁻¹) * ((y : G)⁻¹ * b) := by rw [h2]
    _ = (y : G)⁻¹ * b * u := by group


theorem baum_eq_V_sup_Q1 {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    baum S = conjR (blockU L) x ⊔ pCoreOf 2 (L ⊔ baum S) := by
  apply le_antisymm
  · intro b hb
    obtain ⟨v, hv, hq⟩ := C.exists_mem_V_mul_Q1 hx hVE hb
    have e : b = v * (v⁻¹ * b) := by group
    rw [e]
    exact mul_mem (mem_sup_left hv) (mem_sup_right hq)
  · exact sup_le (C.V_le_baum hx) (by rw [C.D.Q1_eq_inf]; exact inf_le_left)

theorem baum_eq_Q1_sup_conj {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    baum S = pCoreOf 2 (L ⊔ baum S) ⊔ conjR (pCoreOf 2 (L ⊔ baum S)) x := by
  have hQB := C.D.Q1_le_baum
  apply le_antisymm
  · calc baum S = conjR (blockU L) x ⊔ pCoreOf 2 (L ⊔ baum S) := C.baum_eq_V_sup_Q1 hx hVE
      _ ≤ conjR (pCoreOf 2 (L ⊔ baum S)) x ⊔ pCoreOf 2 (L ⊔ baum S) :=
          sup_le_sup_right (C5.conjSubgroup_mono C.D.U_le_Q1 x) _
      _ = pCoreOf 2 (L ⊔ baum S) ⊔ conjR (pCoreOf 2 (L ⊔ baum S)) x := sup_comm _ _
  · refine sup_le hQB ?_
    have h1 : conjR (pCoreOf 2 (L ⊔ baum S)) x ≤ conjR (baum S) x := C5.conjSubgroup_mono hQB x
    have h2 : conjR (baum S) x = baum S :=
      C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum S hx)
    exact h1.trans h2.le

theorem comm_U_baum_le {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    ⁅blockU L, baum S⁆ ≤ ⁅blockU L, conjR (blockU L) x⁆ := by
  rw [Subgroup.commutator_le]
  intro u hu b hb
  obtain ⟨v, hv, hq⟩ := C.exists_mem_V_mul_Q1 hx hVE hb
  have hq' : v⁻¹ * b ∈ baum S ⊓ centralizer (blockU L : Set G) := by
    rw [← C.D.Q1_eq_inf]; exact hq
  have hqC : u * (v⁻¹ * b) = (v⁻¹ * b) * u := Subgroup.mem_centralizer_iff.1 hq'.2 u hu
  have hbq : b = v * (v⁻¹ * b) := by group
  generalize v⁻¹ * b = q at hqC hbq
  have hqu : q * u⁻¹ = u⁻¹ * q := (show Commute u⁻¹ q from (show Commute u q from hqC).inv_left).eq.symm
  have e : ⁅u, b⁆ = ⁅u, v⁆ := by
    rw [commutatorElement_def, commutatorElement_def, hbq]
    calc u * (v * q) * u⁻¹ * (v * q)⁻¹ = u * v * (q * u⁻¹ * q⁻¹) * v⁻¹ := by group
      _ = u * v * (u⁻¹ * q * q⁻¹) * v⁻¹ := by rw [hqu]
      _ = u * v * u⁻¹ * v⁻¹ := by group
  rw [e]
  exact Subgroup.commutator_mem_commutator hu hv

theorem comm_U_V_le_inf {x : G} (hx : x ∈ normalizer (S : Set G)) :
    ⁅blockU L, conjR (blockU L) x⁆ ≤ blockU L ⊓ conjR (blockU L) x := by
  rw [Subgroup.commutator_le]
  intro u hu v hv
  have hvN : v ∈ normalizer (blockU L : Set G) :=
    C1.mem_normalizer_blockU (C.hBN (C.V_le_baum hx hv))
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h1 : v * u⁻¹ * v⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.1 hvN u⁻¹).1 ((blockU L).inv_mem hu)
    have e : ⁅u, v⁆ = u * (v * u⁻¹ * v⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (blockU L).mul_mem hu h1
  · have h1 : u * v * u⁻¹ ∈ conjR (blockU L) x :=
      (Subgroup.mem_normalizer_iff.1 (C.U_le_N_V hx hu) v).1 hv
    have e : ⁅u, v⁆ = (u * v * u⁻¹) * v⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact (conjR (blockU L) x).mul_mem h1 ((conjR (blockU L) x).inv_mem hv)

theorem comm_U_V_eq {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    ⁅blockU L, conjR (blockU L) x⁆ =
      blockU L ⊓ centralizer (conjR (blockU L) x : Set G) := by
  obtain ⟨h1, h2, -⟩ := C.cent_U_V hx hVE
  apply le_antisymm
  · rw [h2]; exact C.comm_U_V_le_inf hx
  · exact h1.trans (le_of_eq (Subgroup.commutator_comm _ _))

theorem comm_U_baum_eq {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    ⁅blockU L, baum S⁆ = ⁅blockU L, conjR (blockU L) x⁆ :=
  le_antisymm (C.comm_U_baum_le hx hVE) (Subgroup.commutator_mono le_rfl (C.V_le_baum hx))

theorem inf_le_centralizer_baum {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    blockU L ⊓ conjR (blockU L) x ≤ centralizer (baum S : Set G) := by
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨v, hv, hq⟩ := C.exists_mem_V_mul_Q1 hx hVE hb
  have hq' : v⁻¹ * b ∈ baum S ⊓ centralizer (blockU L : Set G) := by
    rw [← C.D.Q1_eq_inf]; exact hq
  have hbq : b = v * (v⁻¹ * b) := by group
  generalize v⁻¹ * b = q at hq' hbq
  have hqe : e * q = q * e := Subgroup.mem_centralizer_iff.1 hq'.2 e he.1
  have hve : e * v = v * e := C.V_comm he.2 hv
  rw [hbq]
  calc v * q * e = v * (q * e) := by group
    _ = v * (e * q) := by rw [hqe]
    _ = (v * e) * q := by group
    _ = (e * v) * q := by rw [hve]
    _ = e * (v * q) := by group

theorem inf_centralizer_baum_eq {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    blockU L ⊓ centralizer (baum S : Set G) = blockU L ⊓ conjR (blockU L) x := by
  apply le_antisymm
  · rw [← (C.cent_U_V hx hVE).2.1]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (C.V_le_baum hx)))
  · exact le_inf inf_le_left (C.inf_le_centralizer_baum hx hVE)

theorem conjR_inf_centralizer_baum_eq {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    conjR (blockU L) x ⊓ centralizer (baum S : Set G) = blockU L ⊓ conjR (blockU L) x := by
  apply le_antisymm
  · rw [(C.cent_U_V hx hVE).2.2]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 C.U_le_baum))
  · exact le_inf inf_le_right (C.inf_le_centralizer_baum hx hVE)

theorem conjR_comm_U_baum {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    conjR ⁅blockU L, baum S⁆ x = ⁅blockU L, baum S⁆ := by
  have hE : ⁅blockU L, baum S⁆ = blockU L ⊓ conjR (blockU L) x := by
    rw [C.comm_U_baum_eq hx hVE, C.comm_U_V_eq hx hVE]
    exact (C.cent_U_V hx hVE).2.1
  have hEC : ⁅blockU L, baum S⁆ = blockU L ⊓ centralizer (baum S : Set G) := by
    rw [hE]; exact (C.inf_centralizer_baum_eq hx hVE).symm
  have hBx : conjSubgroup (baum S) x = baum S :=
    C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum S hx)
  have h1 : conjR ⁅blockU L, baum S⁆ x = conjR (blockU L) x ⊓ centralizer (baum S : Set G) := by
    rw [hEC]
    show conjSubgroup (blockU L ⊓ centralizer (baum S : Set G)) x = _
    rw [C5.conjSubgroup_inf, C5.conjSubgroup_centralizer, hBx]
    rfl
  rw [h1, C.conjR_inf_centralizer_baum_eq hx hVE, hE]

theorem U_le_normalizer_D1 : blockU L ≤ normalizer (s2I S L : Set G) := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro d
  have hcd : ∀ d' ∈ s2I S L, u * d' * u⁻¹ = d' := fun d' hd' => by
    have := Subgroup.mem_centralizer_iff.1 hd'.2 u (C.D.blockU_le_L hu)
    rw [this]; group
  have hcd' : ∀ d' ∈ s2I S L, u⁻¹ * d' * u = d' := fun d' hd' => by
    have := Subgroup.mem_centralizer_iff.1 hd'.2 u⁻¹ ((L).inv_mem (C.D.blockU_le_L hu))
    rw [this]; group
  constructor
  · intro hd; rw [hcd d hd]; exact hd
  · intro hd
    have h2 : d = u * d * u⁻¹ := by
      calc d = u⁻¹ * (u * d * u⁻¹) * u := by group
        _ = u * d * u⁻¹ := hcd' _ hd
    rw [h2]; exact hd

theorem D1_conj_mem {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) {e : G} (he : e ∈ conjSubgroup (s2I S L) x) :
    ∃ w ∈ conjR (blockU L) x, ∃ d ∈ s2I S L, e = w * d := by
  have heB : e ∈ baum S := by
    have h1 : conjSubgroup (s2I S L) x ≤ conjSubgroup (baum S) x :=
      C5.conjSubgroup_mono inf_le_left x
    rw [C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum S hx)] at h1
    exact h1 he
  have heC : e ∈ centralizer (conjR (blockU L) x : Set G) := by
    have h0 : s2I S L ≤ centralizer (blockU L : Set G) := fun d hd =>
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 C.D.blockU_le_L) hd.2
    have h1 : conjSubgroup (s2I S L) x ≤ conjSubgroup (centralizer (blockU L : Set G)) x :=
      C5.conjSubgroup_mono h0 x
    rw [C5.conjSubgroup_centralizer] at h1
    exact h1 he
  obtain ⟨v, hv, hq⟩ := C.exists_mem_V_mul_Q1 hx hVE heB
  have hq' := hq
  rw [C.D.Q1_eq_sup, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right (blockU L) (s2I S L) C.U_le_normalizer_D1] at hq'
  obtain ⟨u, hu, d, hd, hud⟩ := hq'
  have hud' : u * d = v⁻¹ * e := hud
  have hvC : v⁻¹ ∈ centralizer (conjR (blockU L) x : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun w hw =>
      (show Commute w v⁻¹ from (show Commute w v from C.V_comm hw hv).inv_right).eq
  have hqC : v⁻¹ * e ∈ centralizer (conjR (blockU L) x : Set G) :=
    (centralizer (conjR (blockU L) x : Set G)).mul_mem hvC heC
  have hdC : d ∈ centralizer (conjR (blockU L) x : Set G) := C.D1_le_centralizer_V hx hVE hd
  have huC : u ∈ centralizer (conjR (blockU L) x : Set G) := by
    have e1 : u = (v⁻¹ * e) * d⁻¹ := by rw [← hud']; group
    rw [e1]
    exact (centralizer (conjR (blockU L) x : Set G)).mul_mem hqC
      ((centralizer (conjR (blockU L) x : Set G)).inv_mem hdC)
  have huV : u ∈ conjR (blockU L) x := by
    have h1 : u ∈ blockU L ⊓ centralizer (conjR (blockU L) x : Set G) := ⟨hu, huC⟩
    rw [(C.cent_U_V hx hVE).2.1] at h1
    exact h1.2
  refine ⟨v * u, (conjR (blockU L) x).mul_mem hv huV, d, hd, ?_⟩
  calc e = v * (v⁻¹ * e) := by group
    _ = v * (u * d) := by rw [hud']
    _ = v * u * d := by group

theorem conjR_frattini_D1 {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : C.P.im (conjR (blockU L) x) = Estd) :
    conjR (CFSG.QuasithinUnique.DoubleA3.frattiniOf (s2I S L)) x =
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (s2I S L) := by
  have hD2 : IsPGroup 2 ↥(s2I S L) := C.D.isPGroup_baum.to_le inf_le_left
  have hle : CFSG.QuasithinUnique.DoubleA3.frattiniOf (conjSubgroup (s2I S L) x) ≤
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (s2I S L) :=
    frattiniOf_le_of_mul hD2 (fun w hw w' hw' => C.V_comm hw hw')
      (fun w hw => (C5.isElemAbelian_two_iff.mp (C.V_elem x)).2 w hw)
      (fun w hw d hd => Subgroup.mem_centralizer_iff.1 (C.D1_le_centralizer_V hx hVE hd) w hw)
      (fun e he => C.D1_conj_mem hx hVE he)
  have h1 : conjSubgroup (CFSG.QuasithinUnique.DoubleA3.frattiniOf (s2I S L)) x ≤
      CFSG.QuasithinUnique.DoubleA3.frattiniOf (s2I S L) := by
    rw [conjSubgroup_frattiniOf]; exact hle
  exact Subgroup.eq_of_le_of_card_ge h1 (C5.card_conjSubgroup _ x).ge

end Cfg2

theorem lemmaC56_14_s2 : A5.LemmaC56_14_s2 := by
  intro G _ _ T M H S L hcs h5 hne x _ hxN hUV
  obtain ⟨t, ⟨D⟩⟩ := exists_dbl hcs h5 hne
  obtain ⟨C⟩ := D.nonempty_cfg
  have hVE := C.im_V_eq hxN hUV
  exact ⟨⟨C.D.Q1_eq_sup, C.D1_le_centralizer_V hxN hVE⟩,
    ⟨C.baum_eq_V_sup_Q1 hxN hVE, C.baum_eq_Q1_sup_conj hxN hVE, C.comm_U_baum_eq hxN hVE,
      C.comm_U_V_eq hxN hVE, (C.cent_U_V hxN hVE).2.1⟩,
    C.conjR_comm_U_baum hxN hVE, C.conjR_frattini_D1 hxN hVE⟩

end CFSG.QuasithinUnique.AppCS2
