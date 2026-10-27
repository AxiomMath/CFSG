module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Set2

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight2

variable {X : Type} [Group X] [Finite X]

theorem secQ_eq_one_of_two {h : Hyp52 X} {y : X} {w : ↥(h.secSub y)} {k : ℕ}
    (hw : (w : X) ^ 2 ^ k = 1) (h1 : h.subQ y w = 1) : (w : X) ∈ h.secB0 y :=
  Hyp52.subQ_eq_one_of_two hw h1

structure Setting3 (X : Type) [Group X] [Finite X] extends Setting2 X where
  t : X
  t_H : t ∈ h.secSub y
  t_norm : t ∈ normalizer ((h.S ⊓ h.secG0 y : Subgroup X) : Set X)
  t_lift : h.subQ y ⟨t, t_H⟩ = tb

theorem Setting3.t_G0 (s : Setting3 X) : s.t ∈ s.h.secG0 s.y :=
  s.h.secSub_le_G0 s.y s.t_H

namespace Setting0

variable (s : Setting0 X)

theorem hr_S_inf_le_secSub : s.hr.S ⊓ s.h.secG0 s.y ≤ s.h.secSub s.y :=
  (inf_le_inf_right _ (s.hsec.S_le.trans inf_le_left)).trans (s.h.secC0_le_secSub s.y)

end Setting0

namespace Setting1

variable (s : Setting1 X)

theorem Lay_le_secSub : Seven.Lay s.h s.y ≤ s.h.secSub s.y :=
  s.h.secL0_le_secSub s.y

theorem map_Lay_eq : ((Seven.Lay s.h s.y).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) =
    generalizedFitting (s.h.subQuot s.y) := by
  rw [Hyp52.subQ_map_eq s.sec (Seven.Lay_le_centralizer_secB0 s.h s.y) s.L_pc]
  exact (Hyp59.generalizedFitting_simple s.sec).1.symm

theorem secQ_mem_S_of_mem_T {x : X} (hx : x ∈ s.hr.S ⊓ s.h.secG0 s.y) :
    s.h.subQ s.y ⟨x, s.hr_S_inf_le_secSub hx⟩ ∈ s.sec.S := by
  rw [s.sec_S]
  exact mem_map_of_mem _ (mem_subgroupOf.mpr hx)

theorem mem_T_of_isPGroup {P : Subgroup X} (hP : IsPGroup 2 P)
    (hTP : s.hr.S ⊓ s.h.secG0 s.y ≤ P) {q : X} (hqP : q ∈ P) (hqH : q ∈ s.h.secSub s.y)
    (hqθ : s.h.subQ s.y ⟨q, hqH⟩ ∈ s.sec.S) : q ∈ s.hr.S ⊓ s.h.secG0 s.y := by
  rw [s.sec_S] at hqθ
  obtain ⟨σ, hσ, hσq⟩ := mem_map.mp hqθ
  have hσT : (σ : X) ∈ s.hr.S ⊓ s.h.secG0 s.y := mem_subgroupOf.mp hσ
  have hwP : (σ : X)⁻¹ * q ∈ P := mul_mem (inv_mem (hTP hσT)) hqP
  obtain ⟨k, hk⟩ := hP ⟨_, hwP⟩
  have hk' : ((σ⁻¹ * ⟨q, hqH⟩ : ↥(s.h.secSub s.y)) : X) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : s.h.subQ s.y (σ⁻¹ * ⟨q, hqH⟩) = 1 := by rw [map_mul, map_inv, hσq, inv_mul_cancel]
  have h2 := Hyp52.subQ_eq_one_of_two hk' h1
  have hB0T : s.h.secB0 s.y ≤ s.hr.S ⊓ s.h.secG0 s.y :=
    le_inf ((s.h.secB0_le_B s.y).trans s.hsec.B_le_S) le_normalizer
  have h3 := mul_mem hσT (hB0T h2)
  simpa using h3

end Setting1

namespace Setting2

variable (s : Setting2 X)

theorem conjugate_Dbar_mul {σ : s.h.subQuot s.y} (hσ : σ ∈ s.sec.S) :
    conjugate (s.sec.S ⊓ s.sec.J) (s.tb * σ) = conjugate (s.sec.S ⊓ s.sec.J) s.tb := by
  have hSN : s.sec.S ≤ normalizer ((s.sec.S ⊓ s.sec.J : Subgroup _) : Set (s.h.subQuot s.y)) :=
    fun w hw => mem_normalizer_inf (le_normalizer hw) (mem_inf.mp (s.sec.S_le hw)).2
  have hσ' : s.tb * σ * s.tb⁻¹ ∈ s.sec.S := (mem_normalizer_iff.mp s.tb_norm σ).mp hσ
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff]
  rw [show s.tb * σ * x * (s.tb * σ)⁻¹ =
    (s.tb * σ * s.tb⁻¹) * (s.tb * x * s.tb⁻¹) * (s.tb * σ * s.tb⁻¹)⁻¹ by group]
  exact (mem_normalizer_iff.mp (hSN hσ') _).symm

theorem exists_lift_LayT : ∃ τ ∈ Seven.Lay s.h s.y, ∃ hτ : τ ∈ s.h.secSub s.y,
    τ ∈ normalizer ((s.hr.S ⊓ s.h.secG0 s.y : Subgroup X) : Set X) ∧
    τ * τ ∈ s.hr.S ⊓ s.h.secG0 s.y ∧ s.tb⁻¹ * s.h.subQ s.y ⟨τ, hτ⟩ ∈ s.sec.S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : s.hr.S ⊓ s.h.secG0 s.y ≤ normalizer (Seven.Lay s.h s.y : Set X) :=
    inf_le_right.trans (Seven.secG0_le_normalizer_Lay s.h s.y)
  have hT2 : IsPGroup 2 (s.hr.S ⊓ s.h.secG0 s.y : Subgroup X) := s.hr.isPGroup_S.to_le inf_le_left
  have hTH := s.hr_S_inf_le_secSub
  have h1 : s.tb ∈ ((Seven.Lay s.h s.y).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) := by
    rw [s.map_Lay_eq]
    exact s.tb_mem
  obtain ⟨ℓ, hℓL, hℓ⟩ := mem_map.mp h1
  have hℓL' : (ℓ : X) ∈ Seven.Lay s.h s.y := mem_subgroupOf.mp hℓL
  set K : Subgroup X := ((s.sec.S).comap (s.h.subQ s.y)).map (s.h.secSub s.y).subtype with hK
  have hmemK : ∀ {x : X} (hx : x ∈ s.h.secSub s.y), s.h.subQ s.y ⟨x, hx⟩ ∈ s.sec.S → x ∈ K :=
    fun hx h => ⟨⟨_, hx⟩, mem_comap.mpr h, rfl⟩
  have hKmem : ∀ {x : X}, x ∈ K → ∃ hx : x ∈ s.h.secSub s.y, s.h.subQ s.y ⟨x, hx⟩ ∈ s.sec.S := by
    rintro x ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  set M : Subgroup X := K ⊓ ((s.hr.S ⊓ s.h.secG0 s.y) ⊔ Seven.Lay s.h s.y) with hM
  have hTK : s.hr.S ⊓ s.h.secG0 s.y ≤ K := fun x hx =>
    hmemK (hTH hx) (s.secQ_mem_S_of_mem_T hx)
  have hTM : s.hr.S ⊓ s.h.secG0 s.y ≤ M := le_inf hTK le_sup_left
  have hSyl : ∃ P : Sylow 2 ↥M, (P : Subgroup ↥M) = (s.hr.S ⊓ s.h.secG0 s.y).subgroupOf M := by
    have hS2 : IsPGroup 2 ((s.hr.S ⊓ s.h.secG0 s.y).subgroupOf M) := hT2.comap_subtype
    obtain ⟨P, hP⟩ := hS2.exists_le_sylow
    refine ⟨P, le_antisymm (fun q hq => ?_) hP⟩
    have hP2 : IsPGroup 2 ((P : Subgroup ↥M).map M.subtype) := P.isPGroup'.map _
    have hSP : s.hr.S ⊓ s.h.secG0 s.y ≤ (P : Subgroup ↥M).map M.subtype := fun x hx =>
      ⟨⟨x, hTM hx⟩, hP (show (⟨x, hTM hx⟩ : ↥M) ∈ (s.hr.S ⊓ s.h.secG0 s.y).subgroupOf M
        from hx), rfl⟩
    obtain ⟨hqH, hqθ⟩ := hKmem (mem_inf.mp q.2).1
    exact mem_subgroupOf.mpr (s.mem_T_of_isPGroup hP2 hSP ⟨q, hq, rfl⟩ hqH hqθ)
  set E : Subgroup X := conjugate (s.hr.S ⊓ s.h.secG0 s.y) (ℓ : X) with hE
  have hEM : E ≤ M := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have hσH : (ℓ : X) * x * (ℓ : X)⁻¹ ∈ s.h.secSub s.y := hTH hx
    have hxH : x ∈ s.h.secSub s.y := by
      have := mul_mem (mul_mem (inv_mem ℓ.2) hσH) ℓ.2
      rwa [show (ℓ : X)⁻¹ * ((ℓ : X) * x * (ℓ : X)⁻¹) * ℓ = x by group] at this
    refine mem_inf.mpr ⟨hmemK hxH ?_, ?_⟩
    · have h2 : (⟨x, hxH⟩ : ↥(s.h.secSub s.y)) = ℓ⁻¹ * ⟨_, hσH⟩ * ℓ := Subtype.ext (by
        show x = (ℓ : X)⁻¹ * ((ℓ : X) * x * (ℓ : X)⁻¹) * ℓ
        group)
      rw [h2, map_mul, map_mul, map_inv, hℓ]
      have h3 := s.secQ_mem_S_of_mem_T hx
      have := (mem_normalizer_iff.mp (inv_mem s.tb_norm) _).mp h3
      rwa [inv_inv] at this
    ·
      have hxeq : x = ((ℓ : X) * x * (ℓ : X)⁻¹) *
          (((ℓ : X) * x * (ℓ : X)⁻¹)⁻¹ * (ℓ : X)⁻¹ * ((ℓ : X) * x * (ℓ : X)⁻¹) * ℓ) := by
        group
      rw [hxeq]
      refine mul_mem (mem_sup_left hx) (mem_sup_right (mul_mem ?_ hℓL'))
      have := (mem_normalizer_iff.mp (inv_mem (hTL hx)) _).mp (inv_mem hℓL')
      rwa [inv_inv] at this
  have hE2 : IsPGroup 2 E := by
    intro x
    obtain ⟨k, hk⟩ := hT2 ⟨(ℓ : X) * x * (ℓ : X)⁻¹, mem_conjugate_iff.mp x.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : ((ℓ : X) * x * (ℓ : X)⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [conj_pow] at hk'
    have h3 : (x : X) ^ 2 ^ k = 1 := by
      calc (x : X) ^ 2 ^ k = (ℓ : X)⁻¹ * ((ℓ : X) * (x : X) ^ 2 ^ k * (ℓ : X)⁻¹) * ℓ := by
            group
        _ = 1 := by rw [hk']; group
    simpa using h3
  obtain ⟨m, hmM, hmE⟩ := exists_conjugate_le_of_sylow hSyl hEM hE2
  have hℓm : (ℓ : X) * m ∈ normalizer ((s.hr.S ⊓ s.h.secG0 s.y : Subgroup X) : Set X) := by
    refine inv_mem_iff.mp (mem_normalizer_of_conj_mem_fin fun x hx => ?_)
    apply hmE
    rw [mem_conjugate_iff, hE, mem_conjugate_iff]
    rw [show (ℓ : X) * (m * (((ℓ : X) * m)⁻¹ * x * ((ℓ : X) * m)⁻¹⁻¹) * m⁻¹) * (ℓ : X)⁻¹ = x by
      group]
    exact hx
  have hmSL : m ∈ (((s.hr.S ⊓ s.h.secG0 s.y) ⊔ Seven.Lay s.h s.y : Subgroup X) : Set X) :=
    (mem_inf.mp hmM).2
  rw [coe_mul_of_left_le_normalizer_right _ _ hTL] at hmSL
  obtain ⟨σ, hσ, lam, hlam, hσl⟩ := hmSL
  have hσH : (σ : X) ∈ s.h.secSub s.y := hTH hσ
  obtain ⟨hmH, hmθ⟩ := hKmem (mem_inf.mp hmM).1
  have hmσL : m * σ⁻¹ ∈ Seven.Lay s.h s.y := by
    have : m * σ⁻¹ = σ * lam * σ⁻¹ := by rw [← hσl]
    rw [this]
    exact (mem_normalizer_iff.mp (hTL hσ) lam).mp hlam
  set τ₀' : ↥(s.h.secSub s.y) := ℓ * (⟨m, hmH⟩ * ⟨σ, hσH⟩⁻¹) with hτ₀'
  set τ₀ : X := (τ₀' : X) with hτ₀
  have hτ₀e : τ₀ = (ℓ : X) * (m * σ⁻¹) := rfl
  have hτ₀L : τ₀ ∈ Seven.Lay s.h s.y := by rw [hτ₀e]; exact mul_mem hℓL' hmσL
  have hτ₀N : τ₀ ∈ normalizer ((s.hr.S ⊓ s.h.secG0 s.y : Subgroup X) : Set X) := by
    rw [hτ₀e, ← mul_assoc]
    exact mul_mem hℓm (inv_mem (le_normalizer hσ))
  have hτ₀H : τ₀ ∈ s.h.secSub s.y := τ₀'.2
  have hτ₀θ : s.tb⁻¹ * s.h.subQ s.y ⟨τ₀, hτ₀H⟩ ∈ s.sec.S := by
    have e1 : (⟨τ₀, hτ₀H⟩ : ↥(s.h.secSub s.y)) = τ₀' := rfl
    rw [e1, hτ₀', map_mul, hℓ, inv_mul_cancel_left, map_mul, map_inv]
    exact mul_mem hmθ (inv_mem (s.secQ_mem_S_of_mem_T hσ))
  obtain ⟨k, m₀, hm₀, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos τ₀).ne'
  have hτL : τ₀ ^ m₀ ∈ Seven.Lay s.h s.y := pow_mem hτ₀L m₀
  have hτH : τ₀ ^ m₀ ∈ s.h.secSub s.y := pow_mem hτ₀H m₀
  have hτN : τ₀ ^ m₀ ∈ normalizer ((s.hr.S ⊓ s.h.secG0 s.y : Subgroup X) : Set X) :=
    pow_mem hτ₀N m₀
  have hτk : (τ₀ ^ m₀) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hτ2 : IsPGroup 2 (zpowers (τ₀ ^ m₀)) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hτk)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  set u := s.h.subQ s.y ⟨τ₀, hτ₀H⟩ with hu
  have hu2 : u * u ∈ s.sec.S := by
    have : u * u = s.tb * s.tb * (s.tb⁻¹ * (s.tb⁻¹ * u) * s.tb) * (s.tb⁻¹ * u) := by group
    rw [this]
    refine mul_mem (mul_mem s.tb_sq ?_) hτ₀θ
    have := (mem_normalizer_iff.mp (inv_mem s.tb_norm) _).mp hτ₀θ
    rwa [inv_inv] at this
  have hθτ : s.h.subQ s.y ⟨τ₀ ^ m₀, hτH⟩ = u ^ m₀ := by
    rw [hu, ← map_pow]
    rfl
  obtain ⟨j, hj⟩ := hm₀
  have hτθ : s.tb⁻¹ * s.h.subQ s.y ⟨τ₀ ^ m₀, hτH⟩ ∈ s.sec.S := by
    rw [hθτ, hj, pow_succ', pow_mul, ← mul_assoc]
    exact mul_mem hτ₀θ (pow_mem (by rw [pow_two]; exact hu2) j)
  have hττθ : s.h.subQ s.y ⟨τ₀ ^ m₀ * τ₀ ^ m₀, mul_mem hτH hτH⟩ ∈ s.sec.S := by
    have e2 : s.h.subQ s.y ⟨τ₀ ^ m₀ * τ₀ ^ m₀, mul_mem hτH hτH⟩ =
        s.h.subQ s.y ⟨τ₀ ^ m₀, hτH⟩ * s.h.subQ s.y ⟨τ₀ ^ m₀, hτH⟩ := by
      rw [← map_mul]
      rfl
    rw [e2, hθτ, ← pow_add, hj,
      show 2 * j + 1 + (2 * j + 1) = 2 * (2 * j + 1) by ring, pow_mul, pow_two]
    exact pow_mem hu2 _
  have hP2 : IsPGroup 2 ((s.hr.S ⊓ s.h.secG0 s.y) ⊔ zpowers (τ₀ ^ m₀) : Subgroup X) :=
    hT2.to_sup_of_normal_left' hτ2 (zpowers_le.mpr hτN)
  have hττ : τ₀ ^ m₀ * τ₀ ^ m₀ ∈ s.hr.S ⊓ s.h.secG0 s.y :=
    s.mem_T_of_isPGroup hP2 le_sup_left
      (mem_sup_right (mul_mem (mem_zpowers _) (mem_zpowers _))) (mul_mem hτH hτH) hττθ
  exact ⟨τ₀ ^ m₀, hτL, hτH, hτN, hττ, hτθ⟩

theorem exists_lift_Lay : ∃ τ ∈ Seven.Lay s.h s.y, ∃ hτ : τ ∈ s.h.secSub s.y,
    τ ∈ normalizer ((s.h.S ⊓ s.h.secG0 s.y : Subgroup X) : Set X) ∧
    τ * τ ∈ s.h.S ⊓ s.h.secG0 s.y ∧ s.tb⁻¹ * s.h.subQ s.y ⟨τ, hτ⟩ ∈ s.sec.S := by
  obtain ⟨τ, hτL, hτH, hτN, hτ2, hτθ⟩ := s.exists_lift_LayT
  have hTL := Hyp52.inf_Lay_le_of_reChoice s.S0_le s.S0_sylow s.lemma61
    (s.hsec.S_le.trans inf_le_left) s.hr.isPGroup_S s.S0_le_hr
  exact ⟨τ, hτL, hτH, Hyp52.mem_normalizer_S0_of_reChoice s.S0_le_hr hTL hτL hτN,
    Hyp52.mul_self_mem_S0_of_reChoice hTL hτL (mem_inf.mp hτ2).1, hτθ⟩

theorem exists_setting3 : ∃ s3 : Setting3 X, s3.toSetting1 = s.toSetting1 ∧
    s3.t ∈ Seven.Lay s.h s.y ∧ s3.t * s3.t ∈ s.h.S ⊓ s.h.secG0 s.y := by
  obtain ⟨τ, hτL, hτH, hτN, hτ2, hτθ⟩ := s.exists_lift_Lay
  have htb : s.h.subQ s.y ⟨τ, hτH⟩ = s.tb * (s.tb⁻¹ * s.h.subQ s.y ⟨τ, hτH⟩) := by
    rw [mul_inv_cancel_left]
  have hc := s.conjugate_Dbar_mul hτθ
  rw [← htb] at hc
  let s2 : Setting2 X :=
    { s with
      tb := s.h.subQ s.y ⟨τ, hτH⟩
      tb_mem := by
        rw [← s.map_Lay_eq]
        exact mem_map_of_mem _ (show (⟨τ, hτH⟩ : ↥(s.h.secSub s.y)) ∈
          (Seven.Lay s.h s.y).subgroupOf _ from hτL)
      tb_norm := by
        rw [htb]
        exact mul_mem s.tb_norm (le_normalizer hτθ)
      tb_not := by
        rw [htb]
        intro h
        apply s.tb_not
        have := mul_mem h (inv_mem hτθ)
        rwa [mul_inv_cancel_right] at this
      tb_sq := by
        rw [← map_mul]
        exact s.subQ_mem_secS (mem_inf.mp hτ2).1 (mem_inf.mp hτ2).2 (mul_mem hτH hτH)
      D_inf := by rw [hc]; exact s.D_inf
      D_comm := by rw [hc]; exact s.D_comm
      D_sup := by rw [hc]; exact s.D_sup
      a_mem_Dt := by rw [hc]; exact s.a_mem_Dt
      a_central := by rw [hc]; exact s.a_central
      Dt_index_A10 := by rw [hc]; exact s.Dt_index_A10 }
  exact ⟨⟨s2, τ, hτH, hτN, rfl⟩, rfl, hτL, hτ2⟩

end Setting2

end Eight2

end CFSG.ComponentClassification.GSThmB
