
module

public import CFSG.GH74.Uniqueness.SU.KI1r4L34ModelBase

public import CFSG.GH74.KGroups.L34TablesBase
public meta import CFSG.GH74.KGroups.L34Aut
public meta import CFSG.GH74.KGroups.L34
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.Uniqueness.SU.KI1r4L34ModelInputs
public meta import CFSG.GH74.Uniqueness.SU.KI1r4L34ModelInputs
public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSLN
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.GH74.KGroups.L34Inputs
public import CFSG.GH74.KGroups.L34
public import CFSG.GH74.KGroups.L34AutInputs
public import Certificates.Certificate5140
public import CFSG.GH74.KGroups.L34Aut

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.L34M

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.L34

theorem s0_length : s0list.length = 64 :=
  Certificates.certificate5140.1

theorem s0_nodup : s0list.Nodup :=
  Certificates.certificate5140.2.1

theorem s0_one :
    (1 : Equiv.Perm (Fin 42)) ∈ s0list :=
  Certificates.certificate5140.2.2.1

theorem s0_mul_check : (s0list.all fun a => s0list.all fun b => decide (a * b ∈ s0list)) = true :=
  Certificates.certificate5140.2.2.2.2.2.1

theorem s0_mul : ∀ a ∈ s0list, ∀ b ∈ s0list, a * b ∈ s0list := by
  have h : (s0list.all fun a => s0list.all fun b => decide (a * b ∈ s0list)) = true := s0_mul_check
  intro a ha b hb
  simpa using List.all_eq_true.1 (List.all_eq_true.1 h a ha) b hb

theorem s0_inv_check : (s0list.all fun a => decide (a⁻¹ ∈ s0list)) = true :=
  Certificates.certificate5140.2.2.2.2.2.2.1

theorem s0_inv : ∀ a ∈ s0list, a⁻¹ ∈ s0list := by
  have h : (s0list.all fun a => decide (a⁻¹ ∈ s0list)) = true := s0_inv_check
  intro a ha
  simpa using List.all_eq_true.1 h a ha

@[expose] def S0 : Subgroup (Equiv.Perm (Fin 42)) where
  carrier := {g | g ∈ s0list}
  mul_mem' := fun {a b} ha hb => s0_mul a ha b hb
  one_mem' := s0_one
  inv_mem' := fun {a} ha => s0_inv a ha

theorem mem_S0
    {g : Equiv.Perm (Fin 42)} : g ∈ S0 ↔ g ∈ s0list := Iff.rfl

theorem s0_mem_QP_check : (s0list.all fun g => QP.sift g 0) = true :=
  Certificates.certificate5140.2.2.2.2.2.2.2.1

theorem s0_mem_QP : ∀ g ∈ s0list, QP.sift g 0 = true := by
  have h : (s0list.all fun g => QP.sift g 0) = true := s0_mem_QP_check
  exact fun g hg => List.all_eq_true.1 h g hg

theorem S0_le_QP :
    S0 ≤ QP.originalSubgroup :=
  fun _ hg => (mem_iff_sift QP QP_ok _).2 (s0_mem_QP _ (mem_S0.1 hg))

theorem card_S0 : Nat.card S0 = 64 := by
  have h := card_eq_length (fun _ : S0 => True) (fun g => (g : Equiv.Perm (Fin 42)))
    Subtype.val_injective s0list s0_nodup (by
      intro b
      constructor
      · intro hb
        exact ⟨⟨b, mem_S0.2 hb⟩, trivial, rfl⟩
      · rintro ⟨a, -, rfl⟩
        exact mem_S0.1 a.2)
  rw [← s0_length, ← h]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm

theorem model_check :
    modelCheck (elemsT QA) (elemsT QP) = true :=
  Certificates.certificate5140.2.2.2.1

theorem cent_le_S0 :
    ∀ g ∈ QA.originalSubgroup, (∀ s ∈ S0, g * s = s * g) → g ∈ S0 := by
  intro g hg hc
  have h1 := (Bool.and_eq_true_iff.1
    (List.all_eq_true.1 model_check g ((mem_elemsT QA QA_ok g).2 hg))).1
  have h2 : (s0list.all fun s => decide (g * s = s * g)) = true := by
    rw [List.all_eq_true]
    intro s hs
    simpa using hc s (mem_S0.2 hs)
  rw [h2] at h1
  exact mem_S0.2 (by simpa using h1)

theorem y0_mem_check : QP.sift y0 0 = true :=
  Certificates.certificate5140.2.2.2.2.2.2.2.2.1

theorem y0_mem :
    y0 ∈ QP.originalSubgroup := (mem_iff_sift QP QP_ok y0).2 y0_mem_check

theorem y0_norm_check : (s0list.all fun s => decide (y0 * s * y0⁻¹ ∈ s0list)) = true :=
  Certificates.certificate5140.2.2.2.2.2.2.2.2.2.1

theorem y0_norm : ∀ s ∈ S0, y0 * s * y0⁻¹ ∈ S0 := by
  have h : (s0list.all fun s => decide (y0 * s * y0⁻¹ ∈ s0list)) = true := y0_norm_check
  intro s hs
  exact mem_S0.2 (by simpa using List.all_eq_true.1 h s (mem_S0.1 hs))

theorem y0_free_check : (s0list.all fun s => !decide (y0 * s = s * y0) || decide (s = 1)) = true :=
  Certificates.certificate5140.2.2.2.2.2.2.2.2.2.2

theorem y0_free : ∀ s ∈ S0, y0 * s = s * y0 → s = 1 := by
  have h : (s0list.all fun s => !decide (y0 * s = s * y0) || decide (s = 1)) = true := y0_free_check
  intro s hs hc
  have h1 := List.all_eq_true.1 h s (mem_S0.1 hs)
  simpa [hc] using h1

theorem QA_conj_QP :
    ∀ σ ∈ QA.originalSubgroup, ∀ y ∈ QP.originalSubgroup,
    σ * y * σ⁻¹ ∈ QP.originalSubgroup := by
  obtain ⟨M, hP, hA⟩ := autModel (K := QP.originalSubgroup) (MulEquiv.refl _)
  intro σ hσ y hy
  rw [← hA] at hσ
  obtain ⟨φ, hφ⟩ := M.Φ.surjective ⟨σ, hσ⟩
  have h1 : (M.Φ φ : Equiv.Perm (Fin 42)) = σ := congrArg Subtype.val hφ
  have hyM : y ∈ M.P := by rw [hP]; exact hy
  obtain ⟨x', hx'⟩ := M.e.surjective ⟨y, hyM⟩
  have h2 := M.spec φ x'
  have h3 : (M.e x' : Equiv.Perm (Fin 42)) = y := congrArg Subtype.val hx'
  rw [h1, h3] at h2
  have hmem : ∀ g : Equiv.Perm (Fin 42), g ∈ M.P → g ∈ QP.originalSubgroup := fun g hg => by
    rw [← hP]
    exact hg
  rw [← h2]
  exact hmem _ (M.e (φ x')).2

theorem central_gens :
    ∀ g ∈ QA.originalSubgroup, g ^ 2 = 1 → g ∉ QP.originalSubgroup →
    (∀ s ∈ S0, g * s * g⁻¹ ∈ S0) →
    9 ∣ Nat.card ↥(QP.originalSubgroup ⊓ Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 42)))) →
    ∀ a ∈ [PA, PB, sg0, sg1, sg2], a * g * a⁻¹ * g⁻¹ ∈ QP.originalSubgroup := by
  intro g hg hg2 hgP hnorm h9 a ha
  have h1 := (Bool.and_eq_true_iff.1
    (List.all_eq_true.1 model_check g ((mem_elemsT QA QA_ok g).2 hg))).2
  have hs : (s0list.all fun s => decide (g * s * g⁻¹ ∈ s0list)) = true := by
    rw [List.all_eq_true]
    intro s hs
    exact decide_eq_true (mem_S0.1 (hnorm s (mem_S0.2 hs)))
  have hcard : 9 ∣ ((elemsT QP).filter fun h => decide (h * g = g * h)).length := by
    rw [← card_inf_centralizer QP QP_ok g]
    exact h9
  have hP : QP.sift g 0 = false := by
    cases hb : QP.sift g 0
    · rfl
    · exact absurd ((mem_iff_sift QP QP_ok g).2 hb) hgP
  have h3 : ([PA, PB, sg0, sg1, sg2].all fun a => QP.sift (a * g * a⁻¹ * g⁻¹) 0) = true := by
    simpa [hg2, hP, hs, hcard] using h1
  exact (mem_iff_sift QP QP_ok _).2 (List.all_eq_true.1 h3 a ha)

theorem central_all :
    ∀ g ∈ QA.originalSubgroup, g ^ 2 = 1 → g ∉ QP.originalSubgroup →
    (∀ s ∈ S0, g * s * g⁻¹ ∈ S0) →
    9 ∣ Nat.card ↥(QP.originalSubgroup ⊓ Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 42)))) →
    ∀ a ∈ QA.originalSubgroup, a * g * a⁻¹ * g⁻¹ ∈ QP.originalSubgroup := by
  intro g hg hg2 hgP hnorm h9 a ha
  have hgens := central_gens g hg hg2 hgP hnorm h9
  rw [QA_closure'] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hgens x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxA : x ∈ QA.originalSubgroup := by rw [QA_closure']; exact hx
    have e : x * y * g * (x * y)⁻¹ * g⁻¹ =
        (x * (y * g * y⁻¹ * g⁻¹) * x⁻¹) * (x * g * x⁻¹ * g⁻¹) := by group
    rw [e]
    exact QP.originalSubgroup.mul_mem (QA_conj_QP x hxA _ ihy) ihx
  | inv x hx ihx =>
    have hxA : x ∈ QA.originalSubgroup := by rw [QA_closure']; exact hx
    have e : x⁻¹ * g * x⁻¹⁻¹ * g⁻¹ = x⁻¹ * (x * g * x⁻¹ * g⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact QA_conj_QP x⁻¹ (QA.originalSubgroup.inv_mem hxA) _ (QP.originalSubgroup.inv_mem ihx)

theorem exists_sylow_of_card
    (R : Subgroup (Equiv.Perm (Fin 42))) (hR : R ≤ QP.originalSubgroup)
    (hRc : Nat.card R = 64) :
    ∃ SR : Sylow 2 ↥QP.originalSubgroup, (SR : Subgroup ↥QP.originalSubgroup) =
      R.subgroupOf QP.originalSubgroup := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : Nat.card ↥QP.originalSubgroup = 20160 := by rw [card_group QP QP_ok, QP_valid.2]
  have hcard : Nat.card (R.subgroupOf QP.originalSubgroup) = 64 := by
    rw [← hRc]
    have h1 : (R.subgroupOf QP.originalSubgroup).map QP.originalSubgroup.subtype = R := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hR]
    rw [← Subgroup.card_map_of_injective QP.originalSubgroup.subtype_injective
      (K := R.subgroupOf QP.originalSubgroup), h1]
  have hpg : IsPGroup 2 (R.subgroupOf QP.originalSubgroup) :=
    IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)
  obtain ⟨SR, hSR⟩ := hpg.exists_le_sylow
  refine ⟨SR, ?_⟩
  have h1 : Nat.card (SR : Subgroup ↥QP.originalSubgroup) ∣ 20160 := by
    have := Subgroup.card_subgroup_dvd_card (SR : Subgroup ↥QP.originalSubgroup)
    rwa [hP] at this
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 SR.isPGroup'
  have h64 : 64 ≤ Nat.card (SR : Subgroup ↥QP.originalSubgroup) := by
    have := Subgroup.card_le_of_le hSR
    rwa [hcard] at this
  have hn6 : n ≤ 6 := by
    by_contra hlt
    push Not at hlt
    have h7 : 2 ^ 7 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    rw [← hn] at h7
    have := h7.trans h1
    norm_num at this
  have hn6' : 6 ≤ n := by
    by_contra hlt
    push Not at hlt
    have h5 : 2 ^ n ≤ 32 := by
      calc 2 ^ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 32 := by norm_num
    rw [hn] at h64
    omega
  have hn' : n = 6 := le_antisymm hn6 hn6'
  have hSRc : Nat.card (SR : Subgroup ↥QP.originalSubgroup) = 64 := by
    rw [hn, hn']
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hSR (by rw [hSRc, hcard])).symm

theorem exists_conj_S0
    (S : Subgroup (Equiv.Perm (Fin 42))) (hS : S ≤ QP.originalSubgroup)
    (hc : Nat.card S = 64) :
    ∃ q ∈ QP.originalSubgroup, S.map (MulAut.conj q).toMonoidHom = S0 := by
  classical
  obtain ⟨SS, hSS⟩ := exists_sylow_of_card S hS hc
  obtain ⟨TT, hTT⟩ := exists_sylow_of_card S0 S0_le_QP card_S0
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥QP.originalSubgroup) SS TT
  refine ⟨(g : Equiv.Perm (Fin 42)), g.2, ?_⟩
  have hle : S.map (MulAut.conj (g : Equiv.Perm (Fin 42))).toMonoidHom ≤ S0 := by
    rintro _ ⟨s, hs, rfl⟩
    have hsP : s ∈ QP.originalSubgroup := hS hs
    have hmem : (⟨s, hsP⟩ : ↥QP.originalSubgroup) ∈ (SS : Subgroup ↥QP.originalSubgroup) := by
      rw [hSS]
      exact hs
    have h4 : (MulAut.conj g) ⟨s, hsP⟩ ∈ ((g • SS : Sylow 2 ↥QP.originalSubgroup) :
        Subgroup ↥QP.originalSubgroup) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
    rw [hg, hTT, Subgroup.mem_subgroupOf] at h4
    exact h4
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj (g : Equiv.Perm (Fin 42))).injective,
    hc, card_S0]

end CFSG.GH74.Uniqueness.SU.K.R4.L34M
