module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Sylow
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Lift
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.KFacts

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue.A7

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

variable {G : Type} [Group G] [Finite G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
  {eK : ↥Kb ≃* A₇} {T : Subgroup G} {Tp : Subgroup S₇} {f : S₇}

theorem ip_P_conj (hIVK : IVKA7Facts)
    (h : Abs (Cx x) T (Pg x Kb T) (Qg x Kb T) (Rd7 x Kb T) (rho x Kb eK) Tp f) {z : G}
    (hz : HZ T (Pg x Kb T) z) : IP_P_conj x z (Pg x Kb T) := by
  intro a ha ha2 ha1
  have hzP := hz.z_mem_P
  have haC : a ∈ Cx x := ((mem_Kg x Kb).1 ha.2).1
  have hzC : z ∈ Cx x := ((mem_Kg x Kb).1 hzP.2).1
  have hρa : rho x Kb eK a ∈ A₇ := rho_mem_A_of_Kg x Kb eK ha.2
  have hρz : rho x Kb eK z ∈ A₇ := rho_mem_A_of_Kg x Kb eK hzP.2
  have hord : ∀ g ∈ Pg x Kb T, g * g = 1 → g ≠ 1 → orderOf (rho x Kb eK g) = 2 := by
    intro g hg hg2 hg1
    have hgC : g ∈ Cx x := ((mem_Kg x Kb).1 hg.2).1
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← rho_mul x Kb eK hgC hgC, hg2, rho_one]
    · intro h1
      apply hg1
      apply h.P_inj g hg 1 (Pg x Kb T).one_mem
      rw [h1, h.rho_one]
  obtain ⟨σ, hσ, hσa⟩ := hIVK.hd.1 _ _ hρa hρz (hord a ha ha2 ha1) (hord z hzP hz.z_sq hz.z_ne_one)
  obtain ⟨k, hk⟩ : ∃ k : ↥Kb, ((eK k : A₇) : S₇) = σ := ⟨eK.symm ⟨σ, hσ⟩, by simp⟩
  obtain ⟨ka, hka⟩ : ∃ ka : ↥Kb, ka = ⟨pr x a, ((mem_Kg x Kb).1 ha.2).2⟩ := ⟨_, rfl⟩
  obtain ⟨kz, hkz⟩ : ∃ kz : ↥Kb, kz = ⟨pr x z, ((mem_Kg x Kb).1 hzP.2).2⟩ := ⟨_, rfl⟩
  have e1 : ((eK ka : A₇) : S₇) = rho x Kb eK a := by rw [hka]; exact (rho_Kg x Kb eK ha.2).symm
  have e2 : ((eK kz : A₇) : S₇) = rho x Kb eK z := by rw [hkz]; exact (rho_Kg x Kb eK hzP.2).symm
  have h1 : k * ka * k⁻¹ = kz := by
    apply eK.injective
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hk, e1, e2]
    exact hσa
  have h2 : (k : CentralizerBar x) * pr x a * (k : CentralizerBar x)⁻¹ = pr x z := by
    have := congrArg Subtype.val h1
    simpa [hka, hkz] using this
  have hbar : IsConj (QuotientGroup.mk (⟨a, haC⟩ : ↥(Cx x)) : CentralizerBar x)
      (QuotientGroup.mk (⟨z, hzC⟩ : ↥(Cx x)) : CentralizerBar x) := by
    rw [isConj_iff]
    refine ⟨(k : CentralizerBar x), ?_⟩
    rw [← pr_of_mem x haC, ← pr_of_mem x hzC]
    exact h2
  obtain ⟨c, hc⟩ := exists_conj_of_conj_mk (Ox x) (Ox_odd x) (a := ⟨a, haC⟩) (z := ⟨z, hzC⟩)
    (Subtype.ext ha2) (Subtype.ext hz.z_sq) hbar
  exact ⟨c.1, c.2, congrArg Subtype.val hc⟩

theorem ip_outer (hIVK : IVKA7Facts) (hT : IsSylow2In T (Cx x))
    (h : Abs (Cx x) T (Pg x Kb T) (Qg x Kb T) (Rd7 x Kb T) (rho x Kb eK) Tp f)
    (hx : x * x = 1) (hx1 : x ≠ 1) : IP_outer x T (Rd7 x Kb T) := by
  intro u huT hu2 huRd
  have huC := hT.1 huT
  have hxT : x ∈ T := x_mem_of_sylow x hT hx hx1
  have hxQ : x ∈ Qg x Kb T :=
    (h.mem_Q x).2 ⟨hxT, (rho_eq_one_iff x Kb eK x).2 (phig_x_eq_one x Kb)⟩
  have hρu2 : rho x Kb eK u * rho x Kb eK u = 1 := by
    rw [← rho_mul x Kb eK huC huC, hu2, rho_one]
  have hρuA : rho x Kb eK u ∉ A₇ := fun hA => huRd ((h.mem_Rd u).2 ⟨huT, hA⟩)
  have hρu1 : rho x Kb eK u ≠ 1 := fun h1 => hρuA (h1 ▸ one_mem _)
  have hρuord : orderOf (rho x Kb eK u) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hρu2) hρu1
  obtain ⟨A, hA, hAcard⟩ := exists_elemAb_of_pRank_eq (hIVK.hg _ hρuord)
  let E₄ : Subgroup S₇ := A.map (centralizer ({rho x Kb eK u} : Set S₇) ⊓ A₇).subtype
  have hE₄ : Dihedral.IsEA E₄ := isEA_map_hom _ (isEA_of_isElementaryAbelian hA)
  have hc₄ : Nat.card E₄ = 4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hAcard]
    norm_num
  have hE₄mem : ∀ a ∈ E₄, a ∈ A₇ ∧ rho x Kb eK u * a = a * rho x Kb eK u := by
    rintro _ ⟨y, -, rfl⟩
    obtain ⟨hcent, hA7⟩ := y.2
    exact ⟨hA7, Subgroup.mem_centralizer_iff.1 hcent _ (Set.mem_singleton _)⟩
  have hE₄le : E₄ ≤ A₇ := fun a ha => (hE₄mem a ha).1
  let V₂ : Subgroup ↥Kb := (E₄.subgroupOf A₇).map eK.symm.toMonoidHom
  have hV₂ : Dihedral.IsEA V₂ := isEA_map_hom _ (isEA_subgroupOf' hE₄)
  have hc₂ : Nat.card V₂ = 4 := by
    rw [Subgroup.card_map_of_injective eK.symm.injective, card_subgroupOf hE₄le]
    exact hc₄
  have hmemV₂ : ∀ k ∈ V₂, ((eK k : A₇) : S₇) ∈ E₄ := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : (eK (eK.symm.toMonoidHom y) : A₇) = y := eK.apply_symm_apply y
    rw [h1]
    exact Subgroup.mem_subgroupOf.1 hy
  have hfix : ∀ k ∈ V₂, phig x Kb u k = k := by
    intro k hk
    obtain ⟨-, hcomm⟩ := hE₄mem _ (hmemV₂ k hk)
    apply eK.injective
    apply Subtype.ext
    rw [PsiA7_spec eK (phig x Kb u) k]
    show rho x Kb eK u * _ * (rho x Kb eK u)⁻¹ = _
    rw [hcomm, mul_inv_cancel_right]
  let Vb : Subgroup (CentralizerBar x) := V₂.map Kb.subtype
  have hVb : Dihedral.IsEA Vb := isEA_map_hom _ hV₂
  have hcb : Nat.card Vb = 4 := by
    rw [Subgroup.card_map_of_injective Kb.subtype_injective]; exact hc₂
  have hVbK : ∀ g ∈ Vb, g ∈ Kb := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  have hcommU : ∀ g ∈ Vb, pr x u * g = g * pr x u := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 := phig_apply x Kb u v
    rw [hfix v hv] at h1
    have h2 : pr x u * (v : CentralizerBar x) * (pr x u)⁻¹ = (v : CentralizerBar x) := h1.symm
    calc pr x u * (v : CentralizerBar x)
        = (pr x u * (v : CentralizerBar x) * (pr x u)⁻¹) * pr x u := by group
      _ = (v : CentralizerBar x) * pr x u := by rw [h2]
  have hxK : x ∉ Kg x Kb := by
    intro hxK
    have h1 := h.P_inj x ⟨hxT, hxK⟩ 1 (Pg x Kb T).one_mem (by rw [h.rho_Q hxQ, h.rho_one])
    exact hx1 h1
  have huK : u ∉ Kg x Kb := fun hK => hρuA (rho_mem_A_of_Kg x Kb eK hK)
  have huxK : u * x ∉ Kg x Kb := by
    intro hK
    apply hρuA
    have := rho_mem_A_of_Kg x Kb eK hK
    rwa [rho_mul x Kb eK huC (x_mem_Cx x), h.rho_Q hxQ, mul_one] at this
  have hux : u ≠ x := by
    intro hux
    apply huRd
    rw [hux]
    exact h.Q_le_Rd hxQ
  exact exists_E16 hx hx1 hT hxT huT hu2 hxK huK huxK hux hVb hcb hVbK hcommU

theorem ip_f3 (hIVK : IVKA7Facts) (hT : IsSylow2In T (Cx x))
    (h : Abs (Cx x) T (Pg x Kb T) (Qg x Kb T) (Rd7 x Kb T) (rho x Kb eK) Tp f) :
    IP_f3 x (Pg x Kb T) := by
  intro V hVP hV
  have hVC : ∀ g ∈ V, g ∈ Cx x := fun g hg => ((mem_Kg x Kb).1 (hVP hg).2).1
  have hVCle : V ≤ Cx x := fun g hg => hVC g hg
  have hVT : V ≤ T := fun g hg => (hVP hg).1
  have hVRd : V ≤ Rd7 x Kb T := fun g hg => h.P_le_Rd (hVP hg)
  have hEA := h.isEA_img hVCle hV.1
  have hcard : Nat.card (h.img V hVCle) = 4 := by rw [h.card_img hVP hVCle]; exact hV.2
  have hleA : h.img V hVCle ≤ A₇ := fun a ha => (h.img_le_Pbar hVCle hVRd ha).2
  obtain ⟨mY, hmY3, hmYA, hmYN, w, hw, hmw⟩ :=
    exists_three_elem_normalizing hIVK.hf hleA hEA hcard
  obtain ⟨k, hk⟩ : ∃ k : ↥Kb, ((eK k : A₇) : S₇) = mY := ⟨eK.symm ⟨mY, hmYA⟩, by simp⟩
  have hk3 : k ^ 3 = 1 := by
    apply eK.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, hk, hmY3]
    try rfl
  have hconjk : ∀ y : ↥Kb, ((eK (k * y * k⁻¹) : A₇) : S₇) = mY * (eK y : S₇) * mY⁻¹ := by
    intro y
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hk]
  have hmem : ∀ y : ↥Kb, ((eK y : A₇) : S₇) ∈ h.img V hVCle ↔
      ∃ g ∈ V, pr x g = (y : CentralizerBar x) := by
    intro y
    constructor
    · intro hy
      obtain ⟨g, hg, hgy⟩ := (h.mem_img hVCle).1 hy
      refine ⟨g, hg, ?_⟩
      rw [rho_Kg x Kb eK (hVP hg).2] at hgy
      have := eK.injective (Subtype.ext hgy)
      exact congrArg Subtype.val this
    · rintro ⟨g, hg, hgy⟩
      refine (h.mem_img hVCle).2 ⟨g, hg, ?_⟩
      have hyeq : (⟨pr x g, ((mem_Kg x Kb).1 (hVP hg).2).2⟩ : ↥Kb) = y := Subtype.ext hgy
      rw [rho_Kg x Kb eK (hVP hg).2, hyeq]
  have hmem_iff : ∀ y : ↥Kb, ((eK y : A₇) : S₇) ∈ h.img V hVCle ↔
      ((eK (k * y * k⁻¹) : A₇) : S₇) ∈ h.img V hVCle := by
    intro y
    rw [hconjk y]
    exact hmYN _
  obtain ⟨fbar, hfbar⟩ : ∃ fbar : CentralizerBar x, fbar = (k : CentralizerBar x) := ⟨_, rfl⟩
  have hfbar3 : fbar ^ 3 = 1 := by
    rw [hfbar]
    have := congrArg (fun z : ↥Kb => (z : CentralizerBar x)) hk3
    simpa using this
  have hE2 : IsPGroup 2 ↥(V.subgroupOf (Cx x)) :=
    ((hT.2.1.to_le hVT).of_equiv (Subgroup.subgroupOfEquivOfLe hVCle).symm)
  have hEab : ∀ a ∈ V.subgroupOf (Cx x), ∀ b ∈ V.subgroupOf (Cx x), a * b = b * a :=
    fun a ha b hb => Subtype.ext ((hV.1 _ ha).2 _ hb)
  have hprm : ∀ g : G, ∀ hg : g ∈ Cx x, (QuotientGroup.mk ⟨g, hg⟩ : CentralizerBar x) = pr x g :=
    fun g hg => (pr_of_mem x hg).symm
  have hf : ∀ y : CentralizerBar x, y ∈ (V.subgroupOf (Cx x)).map (QuotientGroup.mk' (Ox x)) ↔
      fbar * y * fbar⁻¹ ∈ (V.subgroupOf (Cx x)).map (QuotientGroup.mk' (Ox x)) := by
    intro y
    rw [mem_map_mk_iff, mem_map_mk_iff]
    constructor
    · rintro ⟨g, hg, hgC, hgy⟩
      have hyK : y ∈ Kb := by rw [← hgy, hprm]; exact ((mem_Kg x Kb).1 (hVP hg).2).2
      have h1 : ((eK ⟨y, hyK⟩ : A₇) : S₇) ∈ h.img V hVCle :=
        (hmem ⟨y, hyK⟩).2 ⟨g, hg, by
          show pr x g = y
          rw [← hprm g hgC]; exact hgy⟩
      obtain ⟨g', hg', hg'y⟩ := (hmem _).1 ((hmem_iff _).1 h1)
      exact ⟨g', hg', hVC g' hg', by rw [hprm]; simpa [hfbar] using hg'y⟩
    · rintro ⟨g', hg', hg'C, hg'y⟩
      have hy'K : fbar * y * fbar⁻¹ ∈ Kb := by
        rw [← hg'y, hprm]; exact ((mem_Kg x Kb).1 (hVP hg').2).2
      have hyK : y ∈ Kb := by
        have := Kb.mul_mem (Kb.mul_mem (Kb.inv_mem k.2) hy'K) k.2
        simpa [hfbar, mul_assoc] using this
      have h1 : ((eK (k * ⟨y, hyK⟩ * k⁻¹) : A₇) : S₇) ∈ h.img V hVCle :=
        (hmem _).2 ⟨g', hg', by rw [← hprm g' hg'C, hg'y]; simp [hfbar]⟩
      obtain ⟨g, hg, hgy⟩ := (hmem _).1 ((hmem_iff _).2 h1)
      exact ⟨g, hg, hVC g hg, by rw [hprm]; exact hgy⟩
  obtain ⟨n, hn1, hn2⟩ := exists_normalizing_lift (Ox x) (Ox_odd x) hE2 hEab hf
  have hpow : ∀ j : ℕ, ∀ ee ∈ V.subgroupOf (Cx x),
      (QuotientGroup.mk (n ^ j * ee * (n ^ j)⁻¹) : CentralizerBar x) =
        fbar ^ j * QuotientGroup.mk ee * (fbar ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro ee _; simp
    | succ j ih =>
      intro ee hee
      have hE' : n ^ j * ee * (n ^ j)⁻¹ ∈ V.subgroupOf (Cx x) :=
        (pow_mem_normalizer_aux hn1 j ee).1 hee
      have e1 : n ^ (j + 1) * ee * (n ^ (j + 1))⁻¹ = n * (n ^ j * ee * (n ^ j)⁻¹) * n⁻¹ := by
        rw [pow_succ']; group
      rw [e1, hn2 _ hE', ih ee hee, pow_succ']
      simp [mul_assoc]
  have hcent : ∀ ee ∈ V.subgroupOf (Cx x), n ^ (3 ^ 1) * ee = ee * n ^ (3 ^ 1) := by
    intro ee hee
    have hE' : n ^ 3 * ee * (n ^ 3)⁻¹ ∈ V.subgroupOf (Cx x) :=
      (pow_mem_normalizer_aux hn1 3 ee).1 hee
    have hd : (n ^ 3 * ee * (n ^ 3)⁻¹) * ee⁻¹ ∈ V.subgroupOf (Cx x) :=
      mul_mem hE' (inv_mem hee)
    have hmk : (QuotientGroup.mk ((n ^ 3 * ee * (n ^ 3)⁻¹) * ee⁻¹) : CentralizerBar x) = 1 := by
      rw [QuotientGroup.mk_mul, hpow 3 ee hee, hfbar3, QuotientGroup.mk_inv]
      simp
    have hd1 : (n ^ 3 * ee * (n ^ 3)⁻¹) * ee⁻¹ = 1 := by
      apply Subtype.ext
      apply eq_one_of_pr_eq_one x hT (hVT hd) (((n ^ 3 * ee * (n ^ 3)⁻¹) * ee⁻¹ : ↥(Cx x))).2
      show pr x ((((n ^ 3 * ee * (n ^ 3)⁻¹) * ee⁻¹ : ↥(Cx x))) : G) = 1
      rw [pr_of_mem x (((n ^ 3 * ee * (n ^ 3)⁻¹) * ee⁻¹ : ↥(Cx x))).2]
      exact hmk
    have : n ^ 3 * ee * (n ^ 3)⁻¹ = ee := mul_inv_eq_one.1 hd1
    calc n ^ (3 ^ 1) * ee = n ^ 3 * ee * (n ^ 3)⁻¹ * n ^ 3 := by simp
      _ = ee * n ^ 3 := by rw [this]
      _ = ee * n ^ (3 ^ 1) := by simp
  obtain ⟨m', ⟨a, ha⟩, hm'1, hm'2⟩ := exists_threeElement_acting hn1 hcent
  refine ⟨m'.1, ⟨a, by simpa using congrArg Subtype.val ha⟩, (mem_Cx x).1 m'.2, ?_, ?_⟩
  · intro v hv
    have := (hm'1 ⟨v, hVC v hv⟩).1 (Subgroup.mem_subgroupOf.2 hv)
    exact Subgroup.mem_subgroupOf.1 this
  · obtain ⟨g₀, hg₀, hg₀w⟩ := (h.mem_img hVCle).1 hw
    refine ⟨g₀, hg₀, fun hcon => hmw ?_⟩
    have hee : (⟨g₀, hVC g₀ hg₀⟩ : ↥(Cx x)) ∈ V.subgroupOf (Cx x) := Subgroup.mem_subgroupOf.2 hg₀
    have h1 : m' * ⟨g₀, hVC g₀ hg₀⟩ * m'⁻¹ = ⟨g₀, hVC g₀ hg₀⟩ := Subtype.ext hcon
    rw [hm'2 _ hee] at h1
    have h2 := hn2 _ hee
    rw [h1] at h2
    have h3 : fbar * pr x g₀ * fbar⁻¹ = pr x g₀ := by
      rw [pr_of_mem x (hVC g₀ hg₀)]; exact h2.symm
    have h4 : k * (⟨pr x g₀, ((mem_Kg x Kb).1 (hVP hg₀).2).2⟩ : ↥Kb) * k⁻¹ =
        ⟨pr x g₀, ((mem_Kg x Kb).1 (hVP hg₀).2).2⟩ := Subtype.ext (by simpa [hfbar] using h3)
    rw [← hg₀w, rho_Kg x Kb eK (hVP hg₀).2, ← hconjk, h4]

end CFSG.GH74.GLS.Stage1.Thm6.Glue.A7
