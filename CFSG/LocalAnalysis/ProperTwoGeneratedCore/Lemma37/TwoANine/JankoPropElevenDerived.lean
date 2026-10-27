module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenComm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar
open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {fr : JankoFrame G z}

theorem exists_mul_of_mem_sup_right {X Y : Subgroup G} (h : Y ≤ normalizer (X : Set G)) {g : G}
    (hg : g ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, x * y = g := by
  have hg' : g ∈ ((X ⊔ Y : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X Y h] at hg'
  obtain ⟨x, hx, y, hy, rfl⟩ := hg'
  exact ⟨x, hx, y, hy, rfl⟩

theorem closure_E_union_M : closure ((fr.E : Set G) ∪ fr.M) = fr.N := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rfl

theorem commutator_N_le_S [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : ⁅fr.N, fr.N⁆ ≤ fr.S := by
  have hX : ((fr.E : Set G) ∪ fr.M) ⊆ centralizer (fr.S : Set G) := by
    rintro x (hx | hx)
    · exact mem_centralizer_S_of_mem_N (E_le_N hx)
    · exact mem_centralizer_S_of_mem_N (M_le_N hx)
  have base : ∀ x ∈ ((fr.E : Set G) ∪ fr.M), ∀ y ∈ ((fr.E : Set G) ∪ fr.M), ⁅x, y⁆ ∈ fr.S := by
    rintro x (hx | hx) y (hy | hy)
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (fr.E_comm x hx y hy)]; exact one_mem _
    · rw [← commutatorElement_inv]; exact inv_mem (commutator_mem_S p7 p10 hz hy hx)
    · exact commutator_mem_S p7 p10 hz hx hy
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (p10.M_comm x hx y hy)]; exact one_mem _
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [← closure_E_union_M] at ha hb
  exact commutator_mem_of_mem_closure hX
    (fun x hx => commutator_mem_of_mem_closure_right hX (base x hx) hb) ha

theorem S_le_commutator_N [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : fr.S ≤ ⁅fr.N, fr.N⁆ := by
  have hP3 : fr.P3bar ≤ ⁅fr.N, fr.N⁆ := fun w hw => by
    obtain ⟨a, ha, rfl⟩ := (mem_P3bar_iff p7 p10 hz).mp hw
    exact Subgroup.commutator_mem_commutator (M_le_N ha.1) (E_le_N s₂_mem_E)
  refine sup_le hP3 ?_
  rw [← map_P3bar hz]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨a, ha, rfl⟩ := (mem_P3bar_iff p7 p10 hz).mp hw
  have hℓ : fr.ℓ ^ 2 ∈ normalizer (fr.N : Set G) := pow_mem ℓ_mem_normalizer_N 2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [conjugate_commutatorElement]
  exact Subgroup.commutator_mem_commutator (conj_mem_of_mem_normalizer hℓ (M_le_N ha.1))
    (conj_mem_of_mem_normalizer hℓ (E_le_N s₂_mem_E))

theorem commutator_N [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : ⁅fr.N, fr.N⁆ = fr.S :=
  le_antisymm (commutator_N_le_S p7 p10 hz) (S_le_commutator_N p7 p10 hz)

theorem commutator_mem_S_of_mem_N [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) {n x : G} (hn : n ∈ fr.N) (hx : x ∈ fr.N) : ⁅n, x⁆ ∈ fr.S :=
  commutator_N_le_S p7 p10 hz (Subgroup.commutator_mem_commutator hn hx)

theorem N_pow_three [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : ∀ x ∈ fr.N, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨e, he, m, hm, rfl⟩ := exists_mul_of_mem_N hx
  have hc : ⁅e, m⁆ ∈ fr.S := commutator_mem_S_of_mem_N p7 p10 hz (E_le_N he) (M_le_N hm)
  have hcM : ⁅e, m⁆ ∈ fr.M := S_le_M p10 hc
  have hce : Commute e ⁅e, m⁆ := comm_of_mem_ZN (S_le_ZN hc) (E_le_N he)
  have h2 : e ^ 2 * m * (e ^ 2)⁻¹ = ⁅e, m⁆ ^ 2 * m := by
    rw [hce.commutatorElement_pow_left 2, commutatorElement_def]; group
  have h1 : e * m * e⁻¹ = ⁅e, m⁆ * m := by rw [commutatorElement_def]; group
  have he3 : e ^ 3 = 1 := fr.E_pow_three e he
  have hm3 : m ^ 3 = 1 := p10.M_pow_three m hm
  have hc3 : ⁅e, m⁆ ^ 3 = 1 := p10.M_pow_three _ hcM
  have hmc : m * ⁅e, m⁆ ^ 2 = ⁅e, m⁆ ^ 2 * m := p10.M_comm m hm _ (pow_mem hcM 2)
  have key : (e * m) ^ 3 =
      (e * m * e⁻¹) * (e ^ 2 * m * (e ^ 2)⁻¹) * (e ^ 3 * m * (e ^ 3)⁻¹) * e ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]; group
  rw [key, he3, h1, h2, one_mul, inv_one, mul_one, mul_one]
  generalize ⁅e, m⁆ = c at hc3 hmc ⊢
  calc c * m * (c ^ 2 * m) * m = c * (m * c ^ 2) * m * m := by group
    _ = c ^ 3 * m ^ 3 := by rw [hmc, show m ^ 3 = m * m * m by rw [pow_succ, pow_two]]; group
    _ = 1 := by rw [hc3, hm3, one_mul]

theorem N_inf_centralizer_z (p10 : JankoProp10 fr) :
    fr.N ⊓ centralizer ({z} : Set G) = fr.E := by
  refine le_antisymm (fun x hx => ?_) (le_inf E_le_N fr.E_le)
  obtain ⟨e, he, m, hm, rfl⟩ := exists_mul_of_mem_N hx.1
  have hez : e * z = z * e := mem_centralizer_singleton_iff.mp (fr.E_le he)
  have hx2 : e * m * z = z * (e * m) := mem_centralizer_singleton_iff.mp hx.2
  have hmz : m * z = z * m := by
    refine mul_left_cancel (a := e) ?_
    calc e * (m * z) = z * (e * m) := by rw [← mul_assoc, hx2]
      _ = e * (z * m) := by rw [← mul_assoc, ← hez, mul_assoc]
  have hmP : m ∈ fr.P₁ := by
    rw [← p10.M_inf_centralizer_z]
    exact ⟨hm, mem_centralizer_singleton_iff.mpr hmz⟩
  exact mul_mem he (P₁_le_E hmP)

theorem conj_eq_inv_of_mem_P₁ {g p : G} (hg : g * fr.s₁ * g⁻¹ = fr.s₁⁻¹) (hp : p ∈ fr.P₁) :
    g * p * g⁻¹ = p⁻¹ := by
  rw [fr.P₁_eq] at hp
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  rw [← conj_zpow, hg, inv_zpow]

theorem N_inf_centralizer_t [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr) :
    fr.N ⊓ centralizer ({fr.t} : Set G) = fr.P₂ ⊔ fr.At := by
  have hP₂t : fr.P₂ ≤ centralizer ({fr.t} : Set G) := by
    rw [← fr.E_inf_centralizer_t]; exact inf_le_right
  refine le_antisymm (fun x hx => ?_) (sup_le (le_inf (P₂_le_E.trans E_le_N) hP₂t)
    (le_inf (inf_le_left.trans M_le_N) inf_le_right))
  obtain ⟨e, he, m, hm, rfl⟩ := exists_mul_of_mem_N hx.1
  have hxt : fr.t * (e * m) * fr.t⁻¹ = e * m := mem_centralizer_singleton_iff_conj.mp hx.2
  have htM := t_mem_normalizer_M p7
  have hdE : e⁻¹ * (fr.t * e * fr.t⁻¹) ∈ fr.E :=
    mul_mem (inv_mem he) (conj_mem_of_mem_normalizer t_mem_normalizer_E he)
  have hdM : e⁻¹ * (fr.t * e * fr.t⁻¹) ∈ fr.M := by
    have h1 : fr.t * e * fr.t⁻¹ = e * m * (fr.t * m * fr.t⁻¹)⁻¹ := by
      rw [← hxt]; group
    rw [h1, show e⁻¹ * (e * m * (fr.t * m * fr.t⁻¹)⁻¹) = m * (fr.t * m * fr.t⁻¹)⁻¹ by group]
    exact mul_mem hm (inv_mem (conj_mem_of_mem_normalizer htM hm))
  generalize hd : e⁻¹ * (fr.t * e * fr.t⁻¹) = d at hdE hdM
  have hted : fr.t * e * fr.t⁻¹ = e * d := by rw [← hd]; group
  have hdP : d ∈ fr.P₁ := by rw [← E_inf_M p10]; exact ⟨hdE, hdM⟩
  have htd : fr.t * d * fr.t⁻¹ = d⁻¹ := conj_eq_inv_of_mem_P₁ fr.t_mul_s₁ hdP
  have hdinv : d⁻¹ = d * d := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, ← pow_two, ← pow_succ]
    exact fr.E_pow_three d hdE
  have he₀ : e * d * d ∈ fr.P₂ := by
    rw [← fr.E_inf_centralizer_t]
    refine ⟨mul_mem (mul_mem he hdE) hdE, mem_centralizer_singleton_iff_conj.mpr ?_⟩
    calc fr.t * (e * d * d) * fr.t⁻¹ =
          (fr.t * e * fr.t⁻¹) * (fr.t * d * fr.t⁻¹) * (fr.t * d * fr.t⁻¹) := by group
      _ = e * d⁻¹ := by rw [hted, htd]; group
      _ = e * d * d := by rw [hdinv, mul_assoc]
  have hrest : (e * d * d)⁻¹ * (e * m) ∈ fr.At := by
    refine ⟨?_, mem_centralizer_singleton_iff_conj.mpr ?_⟩
    · rw [show (e * d * d)⁻¹ * (e * m) = d⁻¹ * d⁻¹ * m by group]
      have hdM' : d⁻¹ ∈ fr.M := inv_mem hdM
      exact mul_mem (mul_mem hdM' hdM') hm
    · have h0 : fr.t * (e * d * d) * fr.t⁻¹ = e * d * d :=
        mem_centralizer_singleton_iff_conj.mp (hP₂t he₀)
      rw [conj_mul_conj, conj_inv_conj, h0, hxt]
  rw [show e * m = (e * d * d) * ((e * d * d)⁻¹ * (e * m)) by group]
  exact mul_mem_sup he₀ hrest

theorem E_le_centralizer_ZN : fr.E ≤ centralizer (fr.ZN : Set G) := fun _ he =>
  Subgroup.mem_centralizer_iff.mpr fun _ hh => (comm_of_mem_ZN hh (E_le_N he)).symm

theorem ZN_le_centralizer_ZN : fr.ZN ≤ centralizer (fr.ZN : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_iff.mpr fun _ hh => (comm_of_mem_ZN hh hx.1).symm

theorem I_le_centralizer_I : fr.I ≤ centralizer (fr.I : Set G) := by
  have hE : fr.I ≤ centralizer (fr.E : Set G) := sup_le
    (fun e he => Subgroup.mem_centralizer_iff.mpr fun e' he' => fr.E_comm e' he' e he)
    (Subgroup.le_centralizer_iff.mp E_le_centralizer_ZN)
  have hZ : fr.I ≤ centralizer (fr.ZN : Set G) := sup_le E_le_centralizer_ZN ZN_le_centralizer_ZN
  exact sup_le (Subgroup.le_centralizer_iff.mp hE) (Subgroup.le_centralizer_iff.mp hZ)

theorem I_comm : ∀ a ∈ fr.I, ∀ b ∈ fr.I, a * b = b * a := fun a ha _ hb =>
  Subgroup.mem_centralizer_iff.mp (I_le_centralizer_I hb) a ha

theorem I_le_N : fr.I ≤ fr.N := sup_le E_le_N ZN_le_N

theorem I_le_centralizer_E : fr.I ≤ centralizer (fr.E : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_iff.mpr fun _ he => Subgroup.mem_centralizer_iff.mp
    (I_le_centralizer_I hx) _ (mem_sup_left he)

theorem E_inf_ZN (p10 : JankoProp10 fr) : fr.E ⊓ fr.ZN = fr.P₁ :=
  le_antisymm ((E_inf_M p10) ▸ inf_le_inf_left _ (ZN_le_M p10)) (le_inf P₁_le_E P₁_le_ZN)

theorem card_I [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr) (hz : orderOf z = 2) :
    Nat.card fr.I = 3 ^ 5 := by
  have hle : fr.E ≤ normalizer (fr.ZN : Set G) :=
    E_le_centralizer_ZN.trans (centralizer_le_normalizer _)
  have h := card_sup_mul_card_inf hle
  rw [E_inf_ZN p10, card_P₁, fr.card_E, card_ZN p7 p10 hz] at h
  change Nat.card fr.I * 3 = 27 * 27 at h
  omega

theorem N_le_normalizer_I [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : fr.N ≤ normalizer (fr.I : Set G) := fun n hn =>
  mem_normalizer_of_conj_mem fun x hx => by
    rw [show n * x * n⁻¹ = ⁅n, x⁆ * x by rw [commutatorElement_def]; group]
    exact mul_mem (mem_sup_right (S_le_ZN (commutator_mem_S_of_mem_N p7 p10 hz hn (I_le_N hx))))
      hx

theorem L_le_normalizer_I [Finite G] (p7 : JankoProp7 fr) : fr.L ≤ normalizer (fr.I : Set G) :=
  fun _ hl => mem_normalizer_sup (L_le_normalizer_E hl) (mem_normalizer_ZN
    (L_le_normalizer_N p7 hl))

theorem commute_of_commutator_mem_centralizer_z [Finite G] (p7 : JankoProp7 fr)
    (p10 : JankoProp10 fr) (hz : orderOf z = 2) {m w : G} (hm : m ∈ fr.M)
    (hw : w ∈ centralizer (fr.P₁ : Set G)) (hwz : w * z = z * w)
    (h : ⁅m, w⁆ ∈ centralizer ({z} : Set G)) : m * w = w * m := by
  have hcM : ⁅m, w⁆ ∈ fr.M := by
    rw [show ⁅m, w⁆ = m * (w * m⁻¹ * w⁻¹) by rw [commutatorElement_def]; group]
    exact mul_mem hm (conj_mem_of_mem_normalizer (centralizer_P₁_le_normalizer_M hw)
      (inv_mem hm))
  have hcP : ⁅m, w⁆ ∈ fr.P₁ := by rw [← p10.M_inf_centralizer_z]; exact ⟨hcM, h⟩
  have hc1 : ⁅m, w⁆ ∈ fr.P₁ ⊓ fr.Mbar := ⟨hcP, commutator_mem_Mbar p7 p10 hz hm hw hwz⟩
  rw [P₁_inf_Mbar p10 hz, Subgroup.mem_bot] at hc1
  exact commutatorElement_eq_one_iff_mul_comm.mp hc1

theorem N_inf_normalizer_E [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : fr.N ⊓ normalizer (fr.E : Set G) = fr.I := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf I_le_N (I_le_centralizer_E.trans (centralizer_le_normalizer _)))
  obtain ⟨e, he, m, hm, rfl⟩ := exists_mul_of_mem_N hx.1
  have hmE : m ∈ normalizer (fr.E : Set G) := by
    rw [show m = e⁻¹ * (e * m) by group]
    exact mul_mem (centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
      fun e' he' => fr.E_comm e' he' _ (inv_mem he))) hx.2
  refine mul_mem (mem_sup_left he) (mem_sup_right (mem_ZN_of_mem_M p10 hm fun e' he' => ?_))
  have hw : e' ∈ centralizer (fr.P₁ : Set G) := E_le_centralizer_P₁ he'
  have hwz : e' * z = z * e' := mem_centralizer_singleton_iff.mp (fr.E_le he')
  have hcE : ⁅m, e'⁆ ∈ fr.E := by
    rw [commutatorElement_def]
    exact mul_mem (conj_mem_of_mem_normalizer hmE he') (inv_mem he')
  exact (commute_of_commutator_mem_centralizer_z p7 p10 hz hm hw hwz (fr.E_le hcE)).symm

theorem centralizer_E [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : centralizer (fr.E : Set G) = fr.I ⊔ zpowers z := by
  refine le_antisymm (fun c hc => ?_) (sup_le I_le_centralizer_E
    (zpowers_le.mpr z_mem_centralizer_E))
  have hcP : c ∈ centralizer (fr.P₁ : Set G) := Subgroup.centralizer_le P₁_le_E hc
  rw [p10.centralizer_P₁] at hcP
  obtain ⟨m, hm, f, hf, rfl⟩ := exists_mul_of_mem_sup_right
    (fun f hf => centralizer_P₁_le_normalizer_M (fr.F_le_centralizer hf)) hcP
  have hfz : f * z = z * f := mem_centralizer_singleton_iff.mp (fr.F_le hf)
  have hfP : f ∈ centralizer (fr.P₁ : Set G) := fr.F_le_centralizer hf
  have key : ∀ e ∈ fr.E, f * e * f⁻¹ = e ∧ m * e = e * m := fun e he => by
    have hce : m * f * e * (m * f)⁻¹ = e := by
      have := Subgroup.mem_centralizer_iff.mp hc e he
      rw [← this, mul_inv_cancel_right]
    have hw : f * e * f⁻¹ ∈ centralizer (fr.P₁ : Set G) :=
      mul_mem (mul_mem hfP (E_le_centralizer_P₁ he)) (inv_mem hfP)
    have hwz : f * e * f⁻¹ * z = z * (f * e * f⁻¹) := by
      have hez : Commute e z := mem_centralizer_singleton_iff.mp (fr.E_le he)
      have hfz' : Commute f z := hfz
      exact (Commute.mul_left (Commute.mul_left hfz' hez) hfz'.inv_left).eq
    have h0 : m * (f * e * f⁻¹) * m⁻¹ = e := by
      calc m * (f * e * f⁻¹) * m⁻¹ = m * f * e * (m * f)⁻¹ := by group
        _ = e := hce
    have hcomm : ⁅m, f * e * f⁻¹⁆ ∈ centralizer ({z} : Set G) := by
      rw [commutatorElement_def, h0]
      exact mul_mem (fr.E_le he) (inv_mem (mem_centralizer_singleton_iff.mpr hwz))
    have hmw := commute_of_commutator_mem_centralizer_z p7 p10 hz hm hw hwz hcomm
    have hfe : f * e * f⁻¹ = e := by
      calc f * e * f⁻¹ = m * (f * e * f⁻¹) * m⁻¹ := by rw [hmw, mul_inv_cancel_right]
        _ = e := h0
    rw [hfe] at hmw
    exact ⟨hfe, hmw⟩
  have hmZ : m ∈ fr.ZN := mem_ZN_of_mem_M p10 hm fun e he => (key e he).2.symm
  have hfEF : f ∈ fr.EF ⊔ zpowers z := by
    rw [← fr.centralizer_EF]
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun e he => ?_, hf⟩
    have he' : e ∈ fr.E := by rw [fr.EF_eq] at he; exact he.1
    have h := (key e he').1
    calc e * f = f * e * f⁻¹ * f := by rw [h]
      _ = f * e := by group
  have hEF : fr.EF ⊔ zpowers z ≤ fr.I ⊔ zpowers z :=
    sup_le_sup_right (fr.EF_eq ▸ inf_le_left.trans le_sup_left) _
  exact mul_mem (mem_sup_left (mem_sup_right hmZ)) (hEF hfEF)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven
